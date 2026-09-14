// FormaliaXiv viewer.
//
// - Renders the paper PDF page-by-page with pdf.js.
// - Overlays click hotspots on env headings (Theorem 1., Lemma 5., …).
// - Click → opens a resizable Lean side panel with syntax-highlighted source,
//   a (toggleable) file browser, word-wrap, clickable imports, and tooltips
//   for identifiers that match a known declaration in the link manifest.

import * as pdfjsLib from './lib/pdf.min.mjs';
pdfjsLib.GlobalWorkerOptions.workerSrc = new URL('./lib/pdf.worker.min.mjs', import.meta.url).href;
// pdf_viewer.mjs reads the core from globalThis.pdfjsLib at evaluation time, so
// it must be set BEFORE the (dynamic) import below runs.
globalThis.pdfjsLib = pdfjsLib;
const { PDFViewer, EventBus, PDFLinkService } = await import('./lib/pdf_viewer.mjs');

const LEAN_WORKSPACE_PREFIX = 'lean_workspace/';

// Site root, resolved from this module's own URL — so the same assets work
// whether the site is served at the origin root (live server) or under a
// project sub-path (GitHub Pages, e.g. https://user.github.io/FormaliaXiv/).
const ROOT = new URL('.', import.meta.url).href;
// Which paper this page is showing — derived from the URL (.../p/<id>[/]).
const PAPER_ID = decodeURIComponent((location.pathname.match(/\/p\/([^/]+)/) || [])[1] || '');
const api = (p) => `${ROOT}api/${PAPER_ID}/${p}`;
const fileUrl = (rel) => `${ROOT}files/${PAPER_ID}/` + rel.split('/').map(encodeURIComponent).join('/');

const state = {
  paper: null,
  lean: null,                 // lazy-loaded /api/<id>/lean.json
  declsByFqn: null,           // Map<fqn, decl>
  declsByName: null,          // Map<name, decl|decl[]>
  declsByFile: null,          // Map<relPath, decl[]>
  envsByLabel: null,          // Map<label, env>
  fileList: null,             // string[] of relative paths
  fileFlags: null,            // {relPath: {sorry, axiom}} for nav colouring
  navFlaggedOnly: false,      // nav filter: show only sorry/axiom files
  currentFile: null,
  currentHighlight: null,
  currentCommentKey: null,    // fqn (or file) the comment box is bound to
  hotspotsByLabel: new Map(), // label → hotspot element on the PDF
  infoByFile: new Map(),      // relPath → Map<line, goalString> | null (none)
  pdf: null,                  // loaded pdf.js document
  envsByPage: new Map(),      // page → [{env, link, sig}]
  pdfViewer: null,            // pdf.js PDFViewer instance
  eventBus: null,
  pendingFlash: null,         // env label awaiting its hotspot to flash
  envPageByLabel: new Map(),  // label → corrected PDF page
  highlightsByPage: new Map(),// page → [highlight]  (span-based, multi-line)
  highlightByFqn: new Map(),  // lean fqn → highlight (for PDF scroll-to)
  pendingHlFlash: null,       // link_id awaiting its highlight to flash
};

// ── PDF + env hotspots ──────────────────────────────────────────────────────

function labelToSignature(label) {
  if (!label) return null;
  if (label.startsWith('proof')) return null;
  const m = /^([a-z]+):(\d+)$/.exec(label);
  if (!m) return null;
  const [, kind, n] = m;
  const Kind = kind.charAt(0).toUpperCase() + kind.slice(1);
  return `${Kind} ${n}.`;
}

function bestLeanLink(env) {
  const cands = (env.links || []).filter(l => l.lean_fqn && l.lean_range);
  if (!cands.length) return null;
  return cands.reduce((a, b) => (a && a.confidence > b.confidence ? a : b), null);
}

// Build the PDF view using pdf.js's own PDFViewer (the engine behind Firefox's
// viewer): it owns rendering, lazy page virtualization, the text layer, and
// smooth quality-preserving zoom. We only attach click-hotspots to each page's
// text layer as it renders.
async function buildPdfView(pdfUrl) {
  const container = document.getElementById('viewerContainer');
  const eventBus = new EventBus();
  const linkService = new PDFLinkService({ eventBus });
  const pdfViewer = new PDFViewer({
    container,
    viewer: document.getElementById('viewer'),
    eventBus,
    linkService,
    textLayerMode: 1,        // enable the text layer (selectable + our anchor)
    annotationMode: 0,       // we don't need the annotation layer
  });
  linkService.setViewer(pdfViewer);
  state.pdfViewer = pdfViewer;
  state.eventBus = eventBus;

  eventBus.on('pagesinit', () => {
    pdfViewer.currentScaleValue = 'page-width';
    const loading = document.getElementById('loading');
    if (loading) loading.remove();
  });
  // Each page's text layer renders (and re-renders on zoom) → (re)place hotspots.
  eventBus.on('textlayerrendered', (e) => {
    placeHotspotsForPage(e.pageNumber);
    placeSpanHighlightsForPage(e.pageNumber);
  });

  const pdf = await pdfjsLib.getDocument(pdfUrl).promise;
  state.pdf = pdf;
  pdfViewer.setDocument(pdf);
  linkService.setDocument(pdf, null);

  setupPdfZoom(container);

  // Refit when the PDF column resizes (panel toggle, splitter drag) — but only
  // if the user is on a keyword scale; a manual numeric zoom is left untouched.
  let resizeTimer = null;
  const ro = new ResizeObserver(() => {
    clearTimeout(resizeTimer);
    resizeTimer = setTimeout(() => {
      const val = pdfViewer.currentScaleValue;
      if (val === 'page-width' || val === 'auto' || val === 'page-fit') {
        pdfViewer.currentScaleValue = val;
      }
    }, 150);
  });
  ro.observe(document.getElementById('pdf-col'));
}

// Ctrl/⌘ + wheel and trackpad pinch (which the browser also reports as a
// ctrl-wheel) drive pdf.js's native zoom, which re-renders crisply. This is the
// viewer's own zoom — we just forward the standard gesture to it.
function setupPdfZoom(container) {
  container.addEventListener('wheel', (e) => {
    if (!(e.ctrlKey || e.metaKey)) return;
    e.preventDefault();
    const v = state.pdfViewer;
    if (!v) return;
    const factor = e.deltaY < 0 ? 1.06 : 1 / 1.06;
    v.currentScale = Math.min(8, Math.max(0.25, v.currentScale * factor));
  }, { passive: false });
}

// Find each env heading in a page's text layer and overlay a click-hotspot.
// Re-runs on every text-layer render so hotspots track zoom automatically.
function placeHotspotsForPage(pageNumber) {
  const envs = state.envsByPage.get(pageNumber);
  if (!envs || !envs.length) return;
  const pageView = state.pdfViewer.getPageView(pageNumber - 1);
  const pageDiv = pageView && pageView.div;
  const textLayer = pageDiv && pageDiv.querySelector('.textLayer');
  if (!textLayer) return;

  for (const h of pageDiv.querySelectorAll('.lean-hotspot')) h.remove();
  for (const { env } of envs) { if (env.label) state.hotspotsByLabel.delete(env.label); }

  const spans = [...textLayer.querySelectorAll('span')].filter(s => s.textContent);
  if (!spans.length) return;
  // Build a token stream (lowercased alphanumerics) mapping each token to its
  // source span. Matching on tokens is punctuation/whitespace-insensitive, so it
  // works for both "Theorem 1." headings and raw statement-text snippets.
  const tok = [];        // token strings
  const tokSpan = [];    // parallel: span index for each token
  for (let si = 0; si < spans.length; si++) {
    const m = spans[si].textContent.toLowerCase().match(/[a-z0-9]+/g);
    if (m) for (const t of m) { tok.push(t); tokSpan.push(si); }
  }
  const findSubseq = (want) => {
    for (let i = 0; i + want.length <= tok.length; i++) {
      let ok = true;
      for (let j = 0; j < want.length; j++) { if (tok[i + j] !== want[j]) { ok = false; break; } }
      if (ok) return i;
    }
    return -1;
  };
  const normTokens = (s) => (s.toLowerCase().match(/[a-z0-9]+/g) || []);

  // Use the text layer (inset:0 of the page's padding box) as the origin so the
  // page's transparent border doesn't offset our absolutely-positioned hotspots.
  const originRect = textLayer.getBoundingClientRect();
  for (const { env, link, sigs } of envs) {
    let span0 = -1, span1 = -1;
    for (const sig of sigs) {
      const full = normTokens(sig);
      if (full.length < 2) continue;
      // Try the full token run, then shrinking prefixes down to 3 tokens — math
      // in a statement often breaks the snippet partway, but the prose prefix
      // before the first formula usually survives in the PDF text. Longest
      // prefixes are tried first and win, so this only adds fallbacks for envs
      // that would otherwise fail (e.g. a heading word the text layer lacks, or
      // a statement that hits a formula after just a few prose words).
      const cap = Math.min(full.length, 9), floor = 3;
      const tries = full.length <= floor ? [full]
        : Array.from({ length: cap - floor + 1 }, (_, k) => full.slice(0, cap - k));
      let at = -1, want = null;
      for (const w of tries) { at = findSubseq(w); if (at >= 0) { want = w; break; } }
      if (at >= 0) { span0 = tokSpan[at]; span1 = tokSpan[at + want.length - 1]; break; }
    }
    if (span0 < 0) continue;
    let x0 = Infinity, y0 = Infinity, x1 = -Infinity, y1 = -Infinity;
    for (let si = span0; si <= span1; si++) {
      const r = spans[si].getBoundingClientRect();
      x0 = Math.min(x0, r.left - originRect.left);
      y0 = Math.min(y0, r.top - originRect.top);
      x1 = Math.max(x1, r.right - originRect.left);
      y1 = Math.max(y1, r.bottom - originRect.top);
    }
    if (!isFinite(x0)) continue;
    const pad = 2;
    const hot = document.createElement('button');
    hot.type = 'button';
    hot.className = 'lean-hotspot';
    hot.style.left = (x0 - pad) + 'px';
    hot.style.top = (y0 - pad) + 'px';
    hot.style.width = (x1 - x0 + pad * 2) + 'px';
    hot.style.height = (y1 - y0 + pad * 2) + 'px';
    const extra = ((env.links || []).filter(l => l.lean_fqn).length) - 1;
    const why = link.rationale ? `\n\nWhy: ${link.rationale}` : '';
    hot.title = `${relationPhrase(link.kind)} — ${link.lean_fqn}`
      + (extra > 0 ? ` (+${extra} more)` : '') + why;
    hot.setAttribute('aria-label', hot.title);
    hot.addEventListener('click', (ev) => { ev.preventDefault(); openLeanFromLink(env, link); });
    pageDiv.appendChild(hot);
    if (env.label) {
      state.hotspotsByLabel.set(env.label, hot);
      if (state.pendingFlash === env.label) { flashHotspot(hot); state.pendingFlash = null; }
    }
  }
}

// Render span-based highlights on a page: for each linked Lean decl whose paper
// span lands on this page, match its prose in the text layer and draw one rect
// per visual line (a real multi-line text highlight), clickable to the decl.
function placeSpanHighlightsForPage(pageNumber) {
  const hls = state.highlightsByPage.get(pageNumber);
  if (!hls || !hls.length) return;
  const pageView = state.pdfViewer.getPageView(pageNumber - 1);
  const pageDiv = pageView && pageView.div;
  const textLayer = pageDiv && pageDiv.querySelector('.textLayer');
  if (!textLayer) return;

  for (const el of pageDiv.querySelectorAll('.lean-span-hl')) el.remove();
  const spans = [...textLayer.querySelectorAll('span')].filter(s => s.textContent);
  if (!spans.length) return;
  // Tokens are matched after folding Unicode compatibility forms (subscripts,
  // combining accents: "F₈" → "f8", "Ḡ" → "g") so quotes written that way still
  // find the plain "F8" / "G" of the text layer. Folding keeps string length
  // for the characters we index (NFKD only expands; offsets are taken on the
  // original text via a parallel map).
  const foldChar = (ch) => ch.toLowerCase().normalize('NFKD').replace(/[\u0300-\u036f]/g, '');
  const tok = [], tokSpan = [], tokC0 = [], tokC1 = [];   // token → span index + char offsets in it
  for (let si = 0; si < spans.length; si++) {
    const raw = spans[si].textContent;
    // per-character folding keeps a char→original-offset map
    let folded = '', map = [];
    for (let k = 0; k < raw.length; k++) { const f = foldChar(raw[k]); for (let q = 0; q < f.length; q++) map.push(k); folded += f; }
    for (const m of folded.matchAll(/[a-z0-9]+/g)) {
      tok.push(m[0]); tokSpan.push(si); tokC0.push(map[m.index]); tokC1.push(map[m.index + m[0].length - 1] + 1);
    }
  }
  const foldText = (s) => s.toLowerCase().normalize('NFKD').replace(/[\u0300-\u036f]/g, '');
  // Geometry of part of a text-layer span (from char `from` to char `to`),
  // via a DOM Range so a highlight that starts or ends mid-line is cut at the
  // word, not at the line's edge. Falls back to the whole span.
  const rectFor = (si, from, to) => {
    const sp = spans[si], tn = sp.firstChild;
    if (!tn || tn.nodeType !== 3 || (from == null && to == null)) return sp.getBoundingClientRect();
    try {
      const rg = document.createRange();
      rg.setStart(tn, Math.min(from == null ? 0 : from, tn.length));
      rg.setEnd(tn, Math.min(to == null ? tn.length : to, tn.length));
      const r = rg.getBoundingClientRect();
      if (r.width || r.height) return r;
    } catch (e) { /* fall through */ }
    return sp.getBoundingClientRect();
  };
  const W = 5;
  const findWin = (want, from = 0) => {
    for (let i = from; i + want.length <= tok.length; i++) {
      let ok = true;
      for (let j = 0; j < want.length; j++) { if (tok[i + j] !== want[j]) { ok = false; break; } }
      if (ok) return i;
    }
    return -1;
  };
  const originRect = textLayer.getBoundingClientRect();

  // Anchor a highlight's prose on the page. Every occurrence of every
  // `w`-token run of the prose (W down to MINW, widest that matches at all)
  // votes for the page position the prose would START at if that run were
  // aligned (occurrence − offset of the run in the prose). The start with the
  // most DISTINCT runs agreeing (within a small tolerance for extraction
  // noise) wins, and the highlight is bracketed around those runs — from the
  // implied start (so a leading token that extracts oddly is still covered)
  // to the last run's end. Scanning the WHOLE prose (not just its head)
  // matters because a statement may open with a formula and only have
  // anchorable prose in the middle. Voting by alignment, rather than taking a
  // dense cluster of hits, is what keeps neighbouring look-alike sentences
  // apart ("F5 is the class of all G ∈ F3 such that …", "F6 is the class of
  // all G ∈ F5 such that …"): shared phrases vote for every neighbour alike,
  // the distinctive tokens decide, and the range can never swallow a
  // neighbour since only runs consistent with ONE alignment are kept.
  const MINW = 4;
  const anchorSpan = (pt) => {
    if (pt.length < 3) return null;
    const lo = Math.min(MINW, pt.length);
    for (let w = Math.min(W, pt.length); w >= lo; w--) {
      const hits = [];                            // [impliedStart, runOffset, position]
      for (let off = 0; off + w <= pt.length; off++) {
        const want = pt.slice(off, off + w);
        for (let at = findWin(want); at >= 0; at = findWin(want, at + 1)) hits.push([at - off, off, at]);
      }
      if (!hits.length) continue;               // widen the search at a shorter width
      hits.sort((a, b) => a[0] - b[0]);
      const tol = 4 + (pt.length >> 3);
      const cnt = new Map();
      let distinct = 0, best = null, j = 0;
      for (let i = 0; i < hits.length; i++) {
        const o = hits[i][1];
        cnt.set(o, (cnt.get(o) || 0) + 1);
        if (cnt.get(o) === 1) distinct++;
        while (hits[i][0] - hits[j][0] > tol) {
          const oj = hits[j][1];
          cnt.set(oj, cnt.get(oj) - 1);
          if (cnt.get(oj) === 0) distinct--;
          j++;
        }
        if (!best || distinct > best.n) best = { n: distinct, j, i };
      }
      const cl = hits.slice(best.j, best.i + 1);
      const starts = cl.map(h => h[0]).sort((a, b) => a - b);
      const implied = starts[starts.length >> 1];
      let s0 = Infinity, s1 = -Infinity;
      for (const h of cl) { if (h[2] < s0) s0 = h[2]; if (h[2] + w - 1 > s1) s1 = h[2] + w - 1; }
      s0 = Math.max(0, Math.min(s0, implied));
      return { s0, s1 };
    }
    return null;
  };

  // 1) Locate each highlight's token range on the page.
  const matched = [];
  for (const h of hls) {
    const pt = (foldText(h.prose).match(/[a-z0-9]+/g) || []);
    const span = anchorSpan(pt);
    if (!span) continue;
    matched.push({ h, t0: span.s0, t1: Math.min(span.s1, tok.length - 1) });
  }
  if (!matched.length) return;

  // 2) Merge highlights whose TOKEN ranges overlap into ONE group, so several
  //    Lean decls formalizing the same passage become a single block instead of
  //    a stack of overlapping highlights. Merely adjacent passages (one ends
  //    where the next begins, even on the same line) stay separate blocks.
  matched.sort((a, b) => a.t0 - b.t0 || a.t1 - b.t1);
  const groups = [], refutedGroups = [];
  for (const m of matched) {
    // A refuted passage (the Lean shows the printed text is false) is its own
    // red block, never merged into the ordinary highlight of the statement it
    // sits in — and drawn after them so it stays on top.
    if (m.h.refuted || m.h.erratum) { refutedGroups.push({ t0: m.t0, t1: m.t1, members: [m.h], refuted: true }); continue; }
    const g = groups[groups.length - 1];
    if (g && m.t0 <= g.t1) { g.t1 = Math.max(g.t1, m.t1); g.members.push(m.h); }
    else groups.push({ t0: m.t0, t1: m.t1, members: [m.h] });
  }

  // 3) Render one flowing block per group, with a count badge + popover if many.
  for (const g of [...groups, ...refutedGroups]) {
    g.s0 = tokSpan[g.t0]; g.s1 = tokSpan[g.t1];
    const rows = [];
    for (let si = g.s0; si <= g.s1; si++) {
      const r = rectFor(si, si === g.s0 ? tokC0[g.t0] : null, si === g.s1 ? tokC1[g.t1] : null);
      if (r.width === 0 && r.height === 0) continue;
      const top = r.top - originRect.top, bottom = r.bottom - originRect.top;
      // A span belongs to a row when their vertical extents mostly overlap —
      // not when their tops align: a subscript/superscript span ("5" in F₅)
      // sits lower/higher than its line and used to become a stub row of its own.
      let row = rows.find(gr => {
        const ov = Math.min(gr.y1, bottom) - Math.max(gr.y0, top);
        return ov > 0.5 * Math.min(gr.y1 - gr.y0, r.height);
      });
      if (!row) { row = { top, x0: Infinity, y0: Infinity, x1: -Infinity, y1: -Infinity }; rows.push(row); }
      row.x0 = Math.min(row.x0, r.left - originRect.left);
      row.y0 = Math.min(row.y0, r.top - originRect.top);
      row.x1 = Math.max(row.x1, r.right - originRect.left);
      row.y1 = Math.max(row.y1, r.bottom - originRect.top);
    }
    const valid = rows.filter(r => isFinite(r.x0)).sort((a, b) => a.y0 - b.y0);
    if (!valid.length) continue;
    g.members.sort((a, b) => (b.confidence || 0) - (a.confidence || 0));
    const multi = g.members.length > 1;
    const refuted = !!g.refuted;
    const gid = g.members.map(m => m.link_id).join('|');
    const blockLeft = Math.min(...valid.map(r => r.x0));
    const blockRight = Math.max(...valid.map(r => r.x1));
    const title = refuted
      ? ('⚠ Error found in the paper — ' + ((g.members[0].erratum && g.members[0].erratum.title) || 'the formalization refutes this passage')
         + '\n\nClick for what is wrong and how the formalization fixes it')
      : multi
      ? (g.members.length + ' Lean declarations formalize this passage — click to choose')
      : (relationPhrase(g.members[0].kind) + ' — ' + g.members[0].lean_fqn
         + (g.members[0].rationale ? '\n\nWhy: ' + g.members[0].rationale : ''));
    const onClick = (ev) => {
      ev.preventDefault(); ev.stopPropagation();
      if (refuted) showErratumPopover(g.members[0], ev); else openHighlightGroup(g.members, ev);
    };
    // Vertical extent. A text-layer span box hugs its glyphs (ascender top to
    // descender bottom), so a row that ran from its own top to the next row's
    // top carried the whole interline gap below the text and read as sitting
    // low. Split every gap evenly between neighbouring rows instead: rows still
    // touch (one flowing block) but each is centred on its line of text.
    const n = valid.length;
    const halfGap = (i) => {
      const r = valid[i];
      const next = i + 1 < n ? Math.max(0, valid[i + 1].y0 - r.y1) : null;
      const prev = i > 0 ? Math.max(0, r.y0 - valid[i - 1].y1) : null;
      const g = next != null ? next : (prev != null ? prev : (r.y1 - r.y0) * 0.2);
      return g / 2;
    };
    const tops = valid.map((r, i) => (i === 0 ? r.y0 - halfGap(0) : (valid[i - 1].y1 + r.y0) / 2));
    const bottoms = valid.map((r, i) => (i === n - 1 ? r.y1 + halfGap(n - 1) : tops[i + 1]));
    const els = [];
    for (let i = 0; i < valid.length; i++) {
      const row = valid[i];
      const first = i === 0, last = i === valid.length - 1;
      const left = first ? row.x0 : blockLeft;
      const right = last ? row.x1 : blockRight;
      const hl = document.createElement('button');
      hl.type = 'button';
      hl.className = 'lean-span-hl' + (first ? ' lean-span-hl-first' : '') + (last ? ' lean-span-hl-last' : '')
        + (multi ? ' lean-span-hl-multi' : '') + (refuted ? ' lean-span-hl-refuted' : '');
      hl.style.left = left + 'px';
      hl.style.top = tops[i] + 'px';
      hl.style.width = Math.max(2, right - left) + 'px';
      hl.style.height = Math.max(2, bottoms[i] - tops[i]) + 'px';
      hl.title = title;
      hl.dataset.hlGroup = gid;
      hl.addEventListener('click', onClick);
      hl.addEventListener('mouseenter', () => setHlHover(gid, true));
      hl.addEventListener('mouseleave', () => setHlHover(gid, false));
      pageDiv.appendChild(hl);
      els.push(hl);
    }
    if (multi || refuted) {
      const badge = document.createElement('button');
      badge.type = 'button';
      badge.className = 'lean-hl-badge' + (refuted ? ' lean-hl-badge-refuted' : '');
      badge.textContent = refuted ? '⚠' : String(g.members.length);
      badge.title = title;
      badge.style.left = (valid[0].x0 - 16) + 'px';
      badge.style.top = tops[0] + 'px';
      badge.dataset.hlGroup = gid;
      badge.addEventListener('click', onClick);
      badge.addEventListener('mouseenter', () => setHlHover(gid, true));
      badge.addEventListener('mouseleave', () => setHlHover(gid, false));
      pageDiv.appendChild(badge);
      els.push(badge);
    }
    for (const m of g.members) {
      // Keep the page-bucket object itself (not a copy) so reveal/un-reveal
      // bookkeeping and the placed elements stay on one record.
      m._els = els; m._gid = gid;
      state.highlightByFqn.set(m.lean_fqn, m);
    }
    if (g.members.some(m => state.pendingHlFlash === m.link_id)) {
      state.pendingHlFlash = null;
      els[0].scrollIntoView({ block: 'center' });
      els.forEach(flashHotspot);
    }
    if (refuted && state.pendingErratumOpen === g.members[0].link_id) {
      // The header's "Error in the paper" button scrolled here; now that the
      // red block exists, centre it and open its note.
      state.pendingErratumOpen = null;
      const placed = state.highlightByFqn.get(g.members[0].lean_fqn);
      setTimeout(() => { els[0].scrollIntoView({ block: 'center' }); els.forEach(flashHotspot); openErratumAt(placed); }, 250);
    }
  }
}

// Click a highlight: one decl → open it; several → popover to choose.
function openHighlightGroup(members, ev) {
  if (members.length === 1) { openLeanFromHighlight(members[0]); return; }
  showHlPopover(members, ev);
}

// Floating chooser listing every Lean decl that formalizes a shared passage.
function showHlPopover(members, ev) {
  const pop = ensureHlPopover();
  pop.className = '';
  pop.innerHTML = '<div class="hlp-head">' + members.length + ' declarations formalize this passage</div>' +
    members.map((m, i) => {
      const c = m.confidence || 0, w = confWord(c);
      const name = m.lean_fqn.split('.').slice(-1)[0];
      return '<button class="hlp-item" data-i="' + i + '" title="' + escapeHtml(m.lean_fqn) + '">' +
        '<div class="hlp-line"><span class="hlp-rel">' + escapeHtml(relationPhrase(m.kind)) + '</span>' +
        '<span class="hlp-name">' + escapeHtml(name) + '</span>' +
        '<span class="lw-conf lw-' + w + '">' + w + '</span></div>' +
        (m.rationale ? '<div class="hlp-why">' + escapeHtml(m.rationale) + '</div>' : '') + '</button>';
    }).join('');
  pop.hidden = false;
  placePopover(pop, ev);
  for (const it of pop.querySelectorAll('.hlp-item')) {
    it.addEventListener('click', () => { hideHlPopover(); openLeanFromHighlight(members[+it.dataset.i]); });
  }
}

function hideHlPopover() {
  const pop = document.getElementById('hl-popover');
  if (pop) { pop.hidden = true; pop.innerHTML = ''; }
}

function ensureHlPopover() {
  let pop = document.getElementById('hl-popover');
  if (!pop) { pop = document.createElement('div'); pop.id = 'hl-popover'; document.body.appendChild(pop); }
  return pop;
}

function placePopover(pop, ev) {
  const pad = 8, vw = window.innerWidth, vh = window.innerHeight;
  pop.style.left = Math.max(pad, Math.min(ev.clientX, vw - pop.offsetWidth - pad)) + 'px';
  pop.style.top = Math.max(pad, Math.min(ev.clientY + 12, vh - pop.offsetHeight - pad)) + 'px';
}

// Curated erratum prose → paragraphs; `code` spans become <code>.
function erratumParas(text) {
  return String(text || '').split(/\n\s*\n/).map(t => t.trim()).filter(Boolean)
    .map(t => '<p>' + escapeHtml(t).replace(/`([^`]+)`/g, '<code>$1</code>') + '</p>').join('');
}

// The Lean declarations an erratum points at: the refuting decl first, then the
// curated references (the corrected statement, the printed conclusion, …).
function erratumRefs(h, e) {
  const all = [{ fqn: h.lean_fqn, label: h.refuted ? 'Lean: the refutation' : 'Lean: the corrected statement' }, ...((e && e.refs) || [])];
  return all.filter((r, i) => r && r.fqn && all.findIndex(x => x && x.fqn === r.fqn) === i);
}

// Header button "⚠ Error in the paper": jump to the refuted passage(s).
// Absolute URL of the paper's formalization report (site-relative in meta,
// resolved against the site root, or an external URL as given).
function reportUrl() {
  const r = state.report;
  if (!r || !r.url) return null;
  return /^https?:/i.test(r.url) ? r.url : new URL(r.url.replace(/^\//, ''), ROOT).href;
}

function setupErrataButton() {
  const btn = document.getElementById('btn-errata');
  if (!btn) return;
  const list = state.errata || [];
  const rep = reportUrl();
  if (!list.length && !rep) { btn.hidden = true; return; }
  btn.hidden = false;
  btn.textContent = !list.length ? '📄 Formalization report'
    : list.length === 1 ? '⚠ Error found in the paper' : `⚠ ${list.length} errors found in the paper`;
  btn.title = (list.map(h => (h.erratum && h.erratum.title) || ('PDF p. ' + h.pdf_page)).join('\n')
    + (list.length ? '\n\nJump to it in the PDF and see what is wrong and how the formalization fixed it' : '')
    + (rep ? '\n\nAlso: open the formalization report (PDF)' : '')).trim();
  btn.addEventListener('click', (e) => {
    e.stopPropagation();
    if (!list.length) { window.open(rep, '_blank', 'noopener'); return; }
    if (list.length === 1 && !rep) { goToErratum(0); return; }
    const r = btn.getBoundingClientRect();
    showErrataList(list, { clientX: r.left, clientY: r.bottom - 8 });
  });
}

function reportLinkHtml(cls, text) {
  const rep = reportUrl();
  if (!rep) return '';
  return '<a class="' + cls + '" href="' + escapeHtml(rep) + '" target="_blank" rel="noopener">' + text + '</a>';
}

// Chooser listing every erratum (title + page); pick one to jump to it.
function showErrataList(list, ev) {
  const pop = ensureHlPopover();
  pop.className = 'erratum';
  pop.innerHTML = '<div class="hlp-head erx-head">⚠ Errors found in the paper</div>' +
    list.map((h, i) => '<button class="hlp-item" data-i="' + i + '">' +
      '<div class="hlp-line"><span class="hlp-rel">' + escapeHtml((h.erratum && h.erratum.title) || h.lean_fqn) + '</span>' +
      '<span class="hlp-name">p. ' + h.pdf_page + '</span></div></button>').join('') +
    reportLinkHtml('hlp-item erx-report',
      '<div class="hlp-line"><span class="hlp-rel">📄 ' + escapeHtml((state.report && state.report.title) || 'Formalization report') + '</span>' +
      '<span class="hlp-name">PDF ↗</span></div>');
  pop.hidden = false;
  placePopover(pop, ev);
  for (const it of pop.querySelectorAll('button.hlp-item')) {
    it.addEventListener('click', () => { hideHlPopover(); goToErratum(+it.dataset.i); });
  }
  for (const a of pop.querySelectorAll('a.erx-report')) a.addEventListener('click', () => setTimeout(hideHlPopover, 0));
}

function goToErratum(i) {
  const h = (state.errata || [])[i];
  if (!h) return;
  const placed = state.highlightByFqn.get(h.lean_fqn);
  if (placed && placed._els && placed._els.length && placed._els[0].isConnected) {
    placed._els[0].scrollIntoView({ block: 'center', behavior: 'smooth' });
    placed._els.forEach(flashHotspot);
    setTimeout(() => openErratumAt(placed), 400);
    return;
  }
  if (h.pdf_page && state.pdfViewer) {
    state.pendingErratumOpen = h.link_id;   // opened once that page's highlights are placed
    state.pdfViewer.scrollPageIntoView({ pageNumber: h.pdf_page });
    setTimeout(() => placeSpanHighlightsForPage(h.pdf_page), 300);
  }
}

function openErratumAt(h) {
  const el = h && h._els && h._els[0];
  const r = el ? el.getBoundingClientRect() : null;
  showErratumPopover(h, r ? { clientX: r.left + Math.min(r.width / 2, 240), clientY: r.bottom + 2 }
                          : { clientX: 100, clientY: 60 });
}

// A refuted passage: explain what is wrong in the paper and how the
// formalization repaired it, with buttons into the Lean.
function showErratumPopover(h, ev) {
  const pop = ensureHlPopover();
  const e = h.erratum || {};
  const refs = erratumRefs(h, e);
  pop.className = 'erratum';
  pop.innerHTML = '<div class="hlp-head erx-head">⚠ Error found in the paper — ' +
    (h.refuted ? 'the formalization refutes this passage' : 'the formalization states a corrected version') + '</div>' +
    '<div class="erx-body">' +
    (e.title ? '<div class="erx-title">' + escapeHtml(e.title) + '</div>' : '') +
    (e.problem ? '<div class="erx-label">What is wrong</div>' + erratumParas(e.problem)
               : (h.rationale ? erratumParas(h.rationale) : '')) +
    (e.fix ? '<div class="erx-label">How the formalization fixes it</div>' + erratumParas(e.fix) : '') +
    '<div class="erx-refs">' + refs.map((r, i) =>
      '<button class="erx-ref" type="button" data-i="' + i + '" title="' + escapeHtml(r.fqn) + '">' +
      escapeHtml(r.label || r.fqn.split('.').slice(-1)[0]) +
      ' <span class="erx-fqn">' + escapeHtml(r.fqn.split('.').slice(-2).join('.')) + '</span></button>').join('') +
    '</div>' +
    (reportUrl() ? '<div class="erx-foot">' + reportLinkHtml('', '📄 Full account in the formalization report ↗') + '</div>' : '') +
    '</div>';
  pop.hidden = false;
  placePopover(pop, ev);
  for (const b of pop.querySelectorAll('.erx-ref')) {
    b.addEventListener('click', () => { hideHlPopover(); openLeanFromFqn(refs[+b.dataset.i].fqn); });
  }
}
document.addEventListener('click', (e) => {
  const pop = document.getElementById('hl-popover');
  if (pop && !pop.hidden && !pop.contains(e.target)) hideHlPopover();
});
document.addEventListener('keydown', (e) => { if (e.key === 'Escape') hideHlPopover(); });

// Hover any row of a multi-line highlight → light up all rows of that link.
function setHlHover(fqn, on) {
  for (const el of document.querySelectorAll(`.lean-span-hl[data-hl-group="${CSS.escape(fqn)}"], .lean-hl-badge[data-hl-group="${CSS.escape(fqn)}"]`)) {
    el.classList.toggle('hl-hover', on);
  }
}

async function openLeanFromHighlight(h) {
  openLeanPanel();
  await loadFile(h.lean_file, {
    start: h.lean_range ? h.lean_range.start_line : 1,
    end: h.lean_range ? h.lean_range.end_line : 1,
    fqn: h.lean_fqn, conf: h.confidence,
  });
}

// A link the paper's scope keeps off the PDF by default: draw it now that the
// reader asked for it from the Lean panel. Only the most recently requested
// one stays drawn, so the page never fills up with proof-step highlights.
function revealLeanOnlyHighlight(h) {
  const prev = state.revealedHl;
  if (prev && prev !== h) {
    const list = state.highlightsByPage.get(prev.pdf_page) || [];
    const i = list.indexOf(prev);
    if (i >= 0) list.splice(i, 1);
    prev._revealed = false;
    for (const el of (prev._els || [])) el.remove();
    state.highlightByFqn.set(prev.lean_fqn, prev);
  }
  h._revealed = true;
  state.revealedHl = h;
  if (!state.highlightsByPage.has(h.pdf_page)) state.highlightsByPage.set(h.pdf_page, []);
  state.highlightsByPage.get(h.pdf_page).push(h);
  placeSpanHighlightsForPage(h.pdf_page);   // no-op until the page's text layer exists
}

// Scroll the PDF to a span highlight for a Lean fqn (used from the Lean panel).
function scrollPdfToHighlight(fqn) {
  const h = state.highlightByFqn.get(fqn);
  if (!h) return false;
  if (h.show_in_pdf === false && !h._revealed) revealLeanOnlyHighlight(h);
  // The placed elements are only usable while their page is alive: pdf.js
  // destroys pages that scroll far out of view (it keeps ~10), which detaches
  // everything we appended — scrollIntoView on a detached node is a silent
  // no-op. On a long paper that is the common case, so fall back to a page
  // scroll and flash the block once it is placed again.
  if (h._els && h._els.length && h._els[0].isConnected) {
    h._els[0].scrollIntoView({ block: 'center', behavior: 'smooth' });
    h._els.forEach(flashHotspot);
    return true;
  }
  if (h.pdf_page && state.pdfViewer) {
    state.pendingHlFlash = h.link_id;
    state.pdfViewer.scrollPageIntoView({ pageNumber: h.pdf_page });
    // If the page's text layer is already rendered no textlayerrendered event
    // will fire; re-place now so the pending flash (and centring) happen.
    setTimeout(() => placeSpanHighlightsForPage(h.pdf_page), 300);
    return true;
  }
  return false;
}

// Scroll the PDF to a paper env and flash a transient highlight. Uses pdf.js's
// own scrollPageIntoView; if the heading hotspot isn't placed yet (lazy text
// layer), arm a pending flash that fires when the hotspot appears.
function scrollPdfToEnv(label, pageRange) {
  const hot = state.hotspotsByLabel.get(label);
  if (hot && hot.isConnected) {   // detached once pdf.js evicts the page
    hot.scrollIntoView({ block: 'center', behavior: 'smooth' });
    flashHotspot(hot);
    return;
  }
  // Prefer the corrected page for this env over the (possibly degenerate) link page.
  const corrected = state.envPageByLabel.get(label);
  const page = corrected || (pageRange && pageRange.start_page);
  if (!page || !state.pdfViewer) return;
  state.pendingFlash = label;
  state.pdfViewer.scrollPageIntoView({ pageNumber: page });
  // Fallback: if the heading never resolves, flash the page top once it renders.
  setTimeout(() => {
    if (state.pendingFlash !== label) return;
    state.pendingFlash = null;
    const pv = state.pdfViewer.getPageView(page - 1);
    if (pv && pv.div) flashRect(pv.div, { left: 0, top: 0, width: pv.div.clientWidth, height: 46 });
  }, 700);
}

function flashHotspot(hot) {
  flashRect(hot.parentElement, {
    left: parseFloat(hot.style.left), top: parseFloat(hot.style.top),
    width: parseFloat(hot.style.width), height: parseFloat(hot.style.height),
  });
}

function flashRect(pageDiv, rect) {
  if (!pageDiv) return;
  const f = document.createElement('div');
  f.className = 'pdf-flash';
  f.style.left = (rect.left - 4) + 'px';
  f.style.top = (rect.top - 4) + 'px';
  f.style.width = (rect.width + 8) + 'px';
  f.style.height = (rect.height + 8) + 'px';
  pageDiv.appendChild(f);
  setTimeout(() => f.remove(), 2500);
}

// ── Lean panel open/close + splitter ────────────────────────────────────────

function openLeanPanel() {
  const app = document.getElementById('app');
  app.classList.remove('lean-closed');
  document.getElementById('lean-col').hidden = false;
  document.getElementById('splitter').hidden = false;
}

// Open the Lean panel from the toolbar button: show the file browser and load
// the first source file so the pane isn't empty.
async function openLeanBrowser() {
  openLeanPanel();
  if (document.getElementById('lean-nav').hidden) await toggleNav();
  if (!state.currentFile) {
    await ensureFileList();
    const first = state.fileList.find(f => f.endsWith('.lean'));
    if (first) loadFile(first);
  }
}

function closeLeanPanel() {
  const app = document.getElementById('app');
  app.classList.add('lean-closed');
  document.getElementById('lean-col').hidden = true;
  document.getElementById('splitter').hidden = true;
}

function setupSplitter() {
  const sp = document.getElementById('splitter');
  const app = document.getElementById('app');
  // Restore last width.
  const saved = parseInt(localStorage.getItem('formaliaxiv-lean-w') || '0', 10);
  if (saved && saved > 200) app.style.setProperty('--lean-w', saved + 'px');

  let dragging = false;
  function onMove(e) {
    if (!dragging) return;
    const w = Math.min(window.innerWidth - 200, Math.max(320, window.innerWidth - e.clientX));
    app.style.setProperty('--lean-w', w + 'px');
  }
  function onUp() {
    if (!dragging) return;
    dragging = false;
    sp.classList.remove('dragging');
    document.body.style.cursor = '';
    document.body.style.userSelect = '';
    const w = parseInt(getComputedStyle(app).getPropertyValue('--lean-w'), 10);
    if (w) localStorage.setItem('formaliaxiv-lean-w', String(w));
    window.removeEventListener('pointermove', onMove);
    window.removeEventListener('pointerup', onUp);
  }
  sp.addEventListener('pointerdown', (e) => {
    e.preventDefault();
    dragging = true;
    sp.classList.add('dragging');
    document.body.style.cursor = 'col-resize';
    document.body.style.userSelect = 'none';
    window.addEventListener('pointermove', onMove);
    window.addEventListener('pointerup', onUp);
  });
}

// ── Lean data + tokenizer ───────────────────────────────────────────────────

async function ensureLeanLoaded() {
  if (state.lean) return state.lean;
  const r = await fetch(api('lean.json'));
  state.lean = await r.json();
  state.declsByFqn = new Map();
  state.declsByName = new Map();
  state.declsByFile = new Map();
  for (const d of state.lean.decls) {
    state.declsByFqn.set(d.fqn, d);
    const arr = state.declsByName.get(d.name) || [];
    arr.push(d);
    state.declsByName.set(d.name, arr);
    const farr = state.declsByFile.get(d.file) || [];
    farr.push(d);
    state.declsByFile.set(d.file, farr);
  }
  return state.lean;
}

// Does this link actually point at somewhere in the paper? Three anchorings are
// in use: an older *label* link (env hotspot), a *span* link carrying the LaTeX
// range it was cut from, and — for papers whose LaTeX source we don't hold — a
// link resolved straight to a PDF page. Any of them earns the Lean→PDF arrow.
function pointsAtPaper(l) {
  return !!(l.paper_label || l.paper_latex_range || l.paper_page_range);
}

// Best paper-side link for a Lean decl (one that actually points at a paper env).
function bestPaperLink(decl) {
  const cands = (decl.links || []).filter(pointsAtPaper);
  if (!cands.length) return null;
  const best = cands.reduce((a, b) => ((a && (a.confidence || 0) > (b.confidence || 0)) ? a : b), null);
  return {
    label: best.paper_label || null,
    page: best.paper_page_range ? best.paper_page_range.start_page : null,
    fqn: decl.fqn,
  };
}

// Human phrasing for *why* a Lean decl maps to a paper element. Links now reach
// equations / paragraphs / proof-steps (not just theorem↔theorem), so the
// relationship is no longer self-evident — we spell it out in the UI.
const RELATION_PHRASE = {
  definition: 'Formalizes the definition',
  theorem: 'Proves the theorem',
  lemma: 'Proves the lemma',
  proposition: 'Proves the proposition',
  corollary: 'Proves the corollary',
  remark: 'Formalizes the remark',
  equation: 'Establishes the displayed equation',
  paragraph: 'Realizes this step in the prose',
  proof_case: 'Handles this proof case',
  have_step: 'Carries out this proof step',
  other: 'Corresponds to this passage',
};
function relationPhrase(kind) { return RELATION_PHRASE[kind] || RELATION_PHRASE.other; }
function confWord(c) { return c >= 0.8 ? 'strong' : (c >= 0.6 ? 'likely' : 'tentative'); }
const ORPHAN_ROLE = {
  helper: 'Helper lemma — a proof step the paper does not state',
  scaffolding: 'Scaffolding — infrastructure / prior-work, no paper counterpart',
  no_counterpart: 'No paper counterpart',
};

// Render the "why this links to the paper" banner for the focused decl. Shows,
// for each paper link, the relationship + confidence + the rationale, and (for
// unlinked decls) the honest role so the absence of a link is explained too.
function renderLinkWhy(decl) {
  const el = document.getElementById('link-why');
  if (!el) return;
  // Only papers built with the new span-link model (which emit `highlights`)
  // show the "why" banner — older label-only papers don't.
  if (!(state.paper && state.paper.highlights && state.paper.highlights.length)) {
    el.hidden = true; el.innerHTML = ''; return;
  }
  const links = decl ? (decl.links || []) : [];
  const paperLinks = links.filter(pointsAtPaper);
  if (!decl || (!paperLinks.length && !links.length)) {
    el.hidden = true; el.innerHTML = ''; return;
  }
  if (!paperLinks.length) {
    // Lean-only orphan: explain why it is NOT linked (helper/scaffolding/…).
    // `paper_status` says which when the manifest carries it; older papers only
    // hint at it through the link source.
    const o = links[0];
    const role = ORPHAN_ROLE[o.paper_status]
      || ORPHAN_ROLE[o.source && o.source.includes('orphan') ? 'helper' : '']
      || 'Not linked to a paper statement';
    el.hidden = false;
    el.innerHTML = LW_CLOSE_BTN + `<div class="lw-row lw-orphan"><div class="lw-line"><span class="lw-rel">${escapeHtml(role)}</span></div>` +
      (o.rationale ? `<div class="lw-why">${escapeHtml(o.rationale)}</div>` : '') + `</div>`;
    el.querySelector('.lw-close').onclick = () => { el.hidden = true; };
    return;
  }
  paperLinks.sort((a, b) => (b.confidence || 0) - (a.confidence || 0));
  el.hidden = false;
  const fqn = decl.fqn;
  // Surface that a "formalized" result is actually assumed / incomplete / not
  // wired into the main proof (flags from the compiled dependency graph).
  const box = (t) => `<div class="lw-warn">${t}</div>`;
  const srcs = Array.isArray(decl.assumption_sources) ? decl.assumption_sources : [];
  let warn = '';
  if (decl.is_axiom) warn += box('⚠ This declaration is an <b>axiom</b> — assumed, not proven.');
  else if (decl.has_sorry) warn += box('⚠ Proof contains <code>sorry</code> — incomplete.');
  // The offending axiom/sorry decls (grouped by file, with a "Rests on …"
  // header) stand in for a summary line. Skipped when the decl IS the
  // axiom/sorry (the message above already covers it).
  if (!decl.is_axiom && !decl.has_sorry) warn += renderAssumptionSources(srcs, decl.fqn);
  if (paperLinks.some(l => l.reachable === false))
    warn += box('⚠ Formalized but <b>not on the main theorem\'s dependency path</b> (e.g. the proof bypasses it via an axiom).');
  el.innerHTML = LW_CLOSE_BTN + warn + `<div class="lw-head">Why this links to the paper</div>` + paperLinks.map(l => {
    const c = l.confidence || 0;
    const w = confWord(c);
    // Span links carry no label; offer a generic "show in PDF" that scrolls to
    // the decl's highlight. Label links keep the label chip.
    const target = l.paper_label
      ? `<a class="lw-label" href="#" data-label="${escapeHtml(l.paper_label)}" title="Show in the PDF">${escapeHtml(l.paper_label)}</a>`
      : `<a class="lw-label" href="#" data-fqn="${escapeHtml(fqn)}" title="Show in the PDF">show in PDF ↩</a>`;
    if (l.paper_status === 'refuted' || l.erratum) {
      // This decl refutes or corrects the printed passage: say so in red, with the erratum.
      const e = l.erratum || {};
      const rel = l.paper_status === 'refuted' ? 'refutes this passage' : 'corrected in this statement';
      return `<div class="lw-row lw-refuted">
        <div class="lw-line">
          <span class="lw-rel">⚠ Error found in the paper — ${rel}</span>
          ${target}
          <span class="lw-conf lw-${w}" title="confidence ${(c * 100) | 0}%">${w}</span>
        </div>
        <div class="lw-erratum">
          ${e.title ? `<div class="lw-erx-title">${escapeHtml(e.title)}</div>` : ''}
          ${e.problem ? `<div class="lw-erx-label">What is wrong</div>${erratumParas(e.problem)}` : ''}
          ${e.fix ? `<div class="lw-erx-label">How the formalization fixes it</div>${erratumParas(e.fix)}` : ''}
        </div>
        ${l.rationale ? `<div class="lw-why">${escapeHtml(l.rationale)}</div>` : ''}
      </div>`;
    }
    return `<div class="lw-row">
      <div class="lw-line">
        <span class="lw-rel">${escapeHtml(relationPhrase(l.kind))}</span>
        ${target}
        <span class="lw-conf lw-${w}" title="confidence ${(c * 100) | 0}%">${w}</span>
      </div>
      ${l.rationale ? `<div class="lw-why">${escapeHtml(l.rationale)}</div>` : ''}
    </div>`;
  }).join('');
  for (const a of el.querySelectorAll('.lw-label')) {
    a.addEventListener('click', (e) => {
      e.preventDefault();
      if (a.dataset.label) scrollPdfToEnv(a.dataset.label, null);
      else if (a.dataset.fqn) scrollPdfToHighlight(a.dataset.fqn);
    });
  }
  // Click an offending axiom/sorry decl → open its file (and jump to it if known).
  for (const a of el.querySelectorAll('.lw-src[data-path]')) {
    a.addEventListener('click', (e) => {
      e.preventDefault();
      const d = state.declsByFqn && state.declsByFqn.get(a.dataset.fqn);
      const hl = d ? { start: d.decl_range.start_line, end: d.decl_range.end_line, fqn: d.fqn } : null;
      loadFile(a.dataset.path, hl);
    });
  }
  el.querySelector('.lw-close').onclick = () => { el.hidden = true; };
}

// The exact `axiom`/`sorry` declarations a result transitively rests on, grouped
// by file so a reviewer can audit only those. Excludes the decl itself.
function renderAssumptionSources(srcs, selfFqn) {
  const items = (srcs || []).filter(s => s.fqn !== selfFqn);
  if (!items.length) return '';
  const nAx = items.filter(s => s.kind === 'axiom').length;
  const nSo = items.filter(s => s.kind === 'sorry').length;
  const summary = [nAx ? `${nAx} axiom${nAx > 1 ? 's' : ''}` : '',
                   nSo ? `${nSo} sorry` : ''].filter(Boolean).join(' + ');
  const byFile = new Map();
  for (const s of items) {
    const f = s.file || '(unknown file)';
    if (!byFile.has(f)) byFile.set(f, []);
    byFile.get(f).push(s);
  }
  let html = `<div class="lw-srcs"><div class="lw-srcs-head">Rests on ${escapeHtml(summary)}:</div>`;
  for (const [f, arr] of [...byFile.entries()].sort((a, b) => a[0].localeCompare(b[0]))) {
    const rel = f.startsWith(LEAN_WORKSPACE_PREFIX) ? f.slice(LEAN_WORKSPACE_PREFIX.length) : f;
    const decls = arr.sort((a, b) => a.name.localeCompare(b.name)).map(s => {
      const tag = `<span class="lw-tag lw-tag-${s.kind}">${s.kind}</span>`;
      const nm = escapeHtml(s.name);
      return s.file
        ? `<a class="lw-src" href="#" data-path="${escapeHtml(s.file)}" data-fqn="${escapeHtml(s.fqn)}" title="${escapeHtml(s.fqn)}">${nm}</a>${tag}`
        : `<span class="lw-src lw-src-plain" title="${escapeHtml(s.fqn)}">${nm}</span>${tag}`;
    }).join('');
    html += `<div class="lw-srcfile"><span class="lw-srcfile-name" title="${escapeHtml(f)}">${escapeHtml(rel)}</span><span class="lw-srcfile-decls">${decls}</span></div>`;
  }
  return html + '</div>';
}

const LW_CLOSE_BTN = '<button class="lw-close" type="button" title="Hide" aria-label="Hide">×</button>';

const KEYWORDS = new Set([
  'import','open','namespace','end','section','variable','variables','universe','universes',
  'structure','class','instance','inductive','coinductive','def','theorem','lemma','example',
  'abbrev','axiom','constant','noncomputable','mutual','where','if','then','else','for','in',
  'do','return','match','with','fun','λ','let','have','show','suffices','attribute','deriving',
  'extends','private','protected','partial','unsafe','macro','elab','syntax','notation','infix',
  'infixl','infixr','postfix','prefix','scoped','local','set_option','prelude','register_builtin_option',
  'initialize','builtin_initialize','syntax_cat','as','from','renaming','hiding','public','use',
]);
const TACTICS = new Set([
  'by','exact','apply','intro','intros','rintro','rcases','obtain','cases','refine','simp',
  'rw','rewrite','calc','assumption','rfl','ring','trivial','constructor','contradiction','omega',
  'linarith','nlinarith','positivity','field_simp','norm_num','push_neg','split','ext','funext',
  'change','specialize','generalize','clear','rename','rename_i','show','unfold','dsimp','done',
  'left','right','exists','admit','sorry','aesop','decide','simp_all','tauto','revert','induction',
  'fin_cases','use','first','any_goals','all_goals','try','focus','swap','case','case_eq','choose',
  'nontriviality','convert','exact?','apply?','rfl','exact_mod_cast','norm_cast','push_cast','simp_rw',
]);
const DECL_INTRO = new Set(['theorem','lemma','def','abbrev','example','axiom','constant','instance','class','structure','inductive','coinductive']);

function escapeHtml(s) {
  return s.replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;');
}

// Returns an array of tokens: { type, text, meta? }
function tokenize(src) {
  const out = [];
  let i = 0;
  const n = src.length;

  function push(type, text, meta) { out.push({ type, text, meta }); }

  while (i < n) {
    const c = src[i];

    // Block comment /- ... -/ (handles nesting)
    if (c === '/' && src[i + 1] === '-') {
      const start = i;
      i += 2;
      let depth = 1;
      while (i < n && depth > 0) {
        if (src[i] === '/' && src[i + 1] === '-') { depth++; i += 2; }
        else if (src[i] === '-' && src[i + 1] === '/') { depth--; i += 2; }
        else i++;
      }
      push('com', src.slice(start, i));
      continue;
    }
    // Line comment
    if (c === '-' && src[i + 1] === '-') {
      const start = i;
      while (i < n && src[i] !== '\n') i++;
      push('com', src.slice(start, i));
      continue;
    }
    // String
    if (c === '"') {
      const start = i;
      i++;
      while (i < n) {
        if (src[i] === '\\' && i + 1 < n) { i += 2; continue; }
        if (src[i] === '"') { i++; break; }
        i++;
      }
      push('str', src.slice(start, i));
      continue;
    }
    // Char literal — tolerate: 'a', '\n', '\\'
    if (c === "'") {
      const start = i;
      i++;
      if (src[i] === '\\') i += 2; else i += 1;
      if (src[i] === "'") i++;
      // could also be part of an identifier suffix; fall through if not closed
      push('str', src.slice(start, i));
      continue;
    }
    // Attribute @[ ... ]
    if (c === '@' && src[i + 1] === '[') {
      const start = i;
      i += 2;
      let depth = 1;
      while (i < n && depth > 0) {
        if (src[i] === '[') depth++;
        else if (src[i] === ']') depth--;
        i++;
      }
      push('attr', src.slice(start, i));
      continue;
    }
    // Number
    if (/[0-9]/.test(c)) {
      const start = i;
      while (i < n && /[0-9_]/.test(src[i])) i++;
      if (src[i] === '.' && /[0-9]/.test(src[i + 1])) {
        i++;
        while (i < n && /[0-9_]/.test(src[i])) i++;
      }
      push('num', src.slice(start, i));
      continue;
    }
    // Identifier (possibly dotted). Lean identifiers allow Unicode letters.
    if (/[\p{L}_]/u.test(c)) {
      const start = i;
      i++;
      while (i < n && /[\p{L}\p{N}_'?!]/u.test(src[i])) i++;
      let end = i;
      while (src[end] === '.' && /[\p{L}_]/u.test(src[end + 1] || '')) {
        end++;
        while (end < n && /[\p{L}\p{N}_'?!]/u.test(src[end])) end++;
      }
      const word = src.slice(start, end);
      const simple = src.slice(start, i);
      i = end;
      if (KEYWORDS.has(simple)) push('kw', word);
      else if (TACTICS.has(simple)) push('tactic', word);
      else push('id', word);
      continue;
    }
    // Whitespace
    if (/\s/.test(c)) {
      const start = i;
      while (i < n && /\s/.test(src[i])) i++;
      push('ws', src.slice(start, i));
      continue;
    }
    // Operator / punctuation / math symbols (including Unicode ∃ ∈ ≤ → …)
    {
      const start = i;
      while (i < n
             && !/[\p{L}\p{N}_\s"'@]/u.test(src[i])
             && !(src[i] === '/' && src[i + 1] === '-')
             && !(src[i] === '-' && src[i + 1] === '-')) {
        i++;
        if (i - start >= 3) break;
      }
      if (i === start) i++;             // emergency progress guard
      push('op', src.slice(start, i));
    }
  }
  // Post-process: tag the module path after `import`/`open` as a navigable
  // path (only workspace-rooted ones, which map 1:1 to files), and the
  // identifier after a decl-introducer (def/theorem/…) as a decl name.
  for (let k = 0; k < out.length; k++) {
    const t = out[k];
    if (t.type === 'kw' && (t.text === 'import' || t.text === 'open')) {
      let j = k + 1;
      while (j < out.length && out[j].type === 'ws') j++;
      if (j < out.length && out[j].type === 'id' && out[j].text.startsWith('Workspace.')) {
        out[j].type = 'import-path';
      }
    }
    if (t.type === 'kw' && DECL_INTRO.has(t.text)) {
      let j = k + 1;
      while (j < out.length && out[j].type === 'ws') j++;
      // Skip attribute lists/modifiers if any
      while (j < out.length && (out[j].type === 'attr' || out[j].type === 'ws')) j++;
      if (j < out.length && out[j].type === 'id') {
        out[j].meta = { decl: true };
      }
    }
  }
  return out;
}

// Token render → HTML for a single token, may include data attrs.
function renderToken(t) {
  const txt = escapeHtml(t.text);
  if (t.type === 'ws') return txt;
  if (t.type === 'com') return `<span class="tok-com">${txt}</span>`;
  if (t.type === 'str') return `<span class="tok-str">${txt}</span>`;
  if (t.type === 'num') return `<span class="tok-num">${txt}</span>`;
  if (t.type === 'kw')  return `<span class="${t.text === 'import' ? 'tok-imp' : 'tok-kw'}">${txt}</span>`;
  if (t.type === 'attr')return `<span class="tok-attr">${txt}</span>`;
  if (t.type === 'op')  return `<span class="tok-op">${txt}</span>`;
  if (t.type === 'tactic') return `<span class="tok-tactic">${txt}</span>`;
  if (t.type === 'import-path') {
    return `<span class="tok-id tok-import-path" data-import="${escapeHtml(t.text)}">${txt}</span>`;
  }
  if (t.type === 'id') {
    if (t.meta && t.meta.decl) return `<span class="tok-decl">${txt}</span>`;
    // Try to match against known decls. Prefer full fqn match, else last-segment unique match.
    const word = t.text;
    let decl = state.declsByFqn && state.declsByFqn.get(word);
    if (!decl) {
      const last = word.split('.').pop();
      const arr = state.declsByName && state.declsByName.get(last);
      if (arr && arr.length === 1) decl = arr[0];
    }
    if (decl) {
      // Keep the natural identifier color; just underline (same color) to signal clickable.
      return `<span class="tok-id tok-known" data-fqn="${escapeHtml(decl.fqn)}">${txt}</span>`;
    }
    return `<span class="tok-id">${txt}</span>`;
  }
  return txt;
}

// Render full text → lines of HTML with gutter.
// opts: { hl, declLinks: Map<line,{label,page,fqn}> (arrow rows),
//         linkRows: Map<line,{label,page,fqn}> (every row of a linked decl), goalLines: Set<line> }
function renderLean(text, opts = {}) {
  const { hl, declLinks, linkRows, goalLines } = opts;
  const tokens = tokenize(text);
  // Split tokens into lines by walking the text and tracking offsets.
  const lines = [];
  let curLine = [];
  for (const t of tokens) {
    if (t.text.indexOf('\n') < 0) { curLine.push(t); continue; }
    const parts = t.text.split('\n');
    for (let i = 0; i < parts.length; i++) {
      if (i > 0) { lines.push(curLine); curLine = []; }
      if (parts[i].length) curLine.push({ ...t, text: parts[i] });
    }
  }
  lines.push(curLine);

  const start = hl?.start, end = hl?.end;
  const out = lines.map((toks, idx) => {
    const ln = idx + 1;
    const inHl = start && ln >= start && ln <= end;
    const cls = ['ln'];
    if (inHl) cls.push('hl');
    if (ln === start) cls.push('hl-start');
    if (ln === end) cls.push('hl-end');
    const dl = declLinks && declLinks.get(ln);
    let arrow = '<span class="arr"></span>';
    if (dl) {
      cls.push('has-link');
      // Label link → scroll to the env hotspot; span link (no label) → scroll to
      // the fqn's PDF highlight. Carry whichever target this decl actually has.
      const attrs = dl.label
        ? `data-label="${escapeHtml(dl.label)}" data-page="${dl.page || ''}"`
        : `data-fqn="${escapeHtml(dl.fqn)}"`;
      const ttl = dl.label ? `Show in PDF: ${dl.label}` : 'Show in PDF';
      arrow = `<span class="arr" role="button" title="${escapeHtml(ttl)}" ${attrs}>←</span>`;
    }
    const lr = linkRows && linkRows.get(ln);
    let rowAttrs = '';
    if (lr) {
      cls.push('in-link');
      rowAttrs = lr.label
        ? ` data-link-label="${escapeHtml(lr.label)}" data-link-page="${lr.page || ''}"`
        : ` data-link-fqn="${escapeHtml(lr.fqn)}"`;
    }
    if (goalLines && goalLines.has(ln)) cls.push('has-goal');
    const inner = toks.map(renderToken).join('') || ' ';
    return `<div class="${cls.join(' ')}" data-line="${ln}"${rowAttrs}>${arrow}<span class="lno">${ln}</span><span class="src">${inner}</span></div>`;
  });
  return out.join('');
}

// ── File loading ────────────────────────────────────────────────────────────

function importPathToFile(path) {
  // "Workspace.Types.Foo" → "lean_workspace/Workspace/Types/Foo.lean"
  // The lakefile.lean root is `Workspace`; anything outside that is external.
  const parts = path.split('.');
  if (!parts.length) return null;
  if (parts[0] !== 'Workspace') return null;
  return LEAN_WORKSPACE_PREFIX + parts.join('/') + '.lean';
}

// Fetch precomputed goal info for a file, if it was generated. Returns
// Map<line, goalString> or null (feature not generated for this paper yet).
async function ensureInfo(relPath) {
  if (state.infoByFile.has(relPath)) return state.infoByFile.get(relPath);
  if (window.__STATIC__) { state.infoByFile.set(relPath, null); return null; }  // static site ships no goal info
  let result = null;
  try {
    const r = await fetch(api('info/' + relPath.split('/').map(encodeURIComponent).join('/')));
    if (r.ok) {
      const arr = await r.json();
      const m = new Map();
      for (const e of arr) {
        if (typeof e.line === 'number' && e.goal) m.set(e.line, e.goal);
      }
      result = m.size ? m : null;
    }
  } catch (e) { /* no info available */ }
  state.infoByFile.set(relPath, result);
  return result;
}

async function loadFile(relPath, hl = null) {
  state.currentFile = relPath;
  state.currentHighlight = hl;
  await ensureLeanLoaded();
  document.getElementById('lean-title').textContent = relPath;
  const subtitle = hl
    ? `L${hl.start}–${hl.end}${hl.fqn ? '  ·  ' + hl.fqn : ''}${hl.conf != null ? '  ·  conf ' + hl.conf.toFixed(2) : ''}`
    : '';
  document.getElementById('lean-subtitle').textContent = subtitle;

  // "Why relevant" banner for the focused decl (the one a link/arrow jumped to).
  renderLinkWhy(hl?.fqn ? state.declsByFqn.get(hl.fqn) : null);

  // Build the decl→paper arrow map for this file (arrow on the decl's first
  // line) and the row map (every line of a linked decl jumps to the PDF on click).
  const declLinks = new Map(), linkRows = new Map();
  for (const d of (state.declsByFile.get(relPath) || [])) {
    const pl = bestPaperLink(d);
    if (!pl) continue;
    declLinks.set(d.decl_range.start_line, pl);
    const last = d.decl_range.end_line || d.decl_range.start_line;
    for (let ln = d.decl_range.start_line; ln <= last; ln++) if (!linkRows.has(ln)) linkRows.set(ln, pl);
  }
  const goalMap = await ensureInfo(relPath);

  const codeEl = document.getElementById('lean-code');
  codeEl.textContent = '// loading…';
  try {
    const r = await fetch(fileUrl(relPath));
    if (!r.ok) throw new Error(`HTTP ${r.status}`);
    const text = await r.text();
    codeEl.innerHTML = renderLean(text, {
      hl, declLinks, linkRows,
      goalLines: goalMap ? new Set(goalMap.keys()) : null,
    });
    if (hl) {
      const target = codeEl.querySelector('.hl-start') || codeEl.querySelector('.hl');
      if (target) target.scrollIntoView({ block: 'center' });
    } else {
      codeEl.parentElement.scrollTop = 0;
    }
  } catch (e) {
    codeEl.textContent = '// failed to load ' + relPath + ': ' + e;
  }
  // Bind the comment box to this decl (if opened via a link) or the file.
  setCommentKey(hl?.fqn || ('file:' + relPath));
  // Update nav active state.
  for (const el of document.querySelectorAll('.nav-file')) {
    el.classList.toggle('active', el.dataset.path === relPath);
  }
}

async function openLeanFromLink(env, link) {
  openLeanPanel();
  await loadFile(link.lean_file, {
    start: link.lean_range.start_line,
    end:   link.lean_range.end_line,
    fqn:   link.lean_fqn,
    conf:  link.confidence,
  });
}

async function openLeanFromFqn(fqn) {
  await ensureLeanLoaded();
  const d = state.declsByFqn.get(fqn);
  if (!d) return;
  openLeanPanel();
  await loadFile(d.file, {
    start: d.decl_range.start_line,
    end:   d.decl_range.end_line,
    fqn:   d.fqn,
  });
}

// ── File navigator ──────────────────────────────────────────────────────────

async function ensureFileList() {
  if (state.fileList) return state.fileList;
  const r = await fetch(api('files/lean'));
  const j = await r.json();
  state.fileList = j.files;
  state.fileFlags = j.flags || {};
  return state.fileList;
}

function renderNav(filter) {
  const root = document.getElementById('nav-tree');
  const q = (filter || '').toLowerCase();
  const flags = state.fileFlags || {};
  const flagged = (p) => { const f = flags[p]; return !!(f && (f.sorry || f.axiom)); };
  const files = state.fileList.filter(p =>
    (!q || p.toLowerCase().includes(q)) && (!state.navFlaggedOnly || flagged(p)));
  // Group by top-level directory under lean_workspace/
  const groups = new Map();
  for (const p of files) {
    const rel = p.startsWith(LEAN_WORKSPACE_PREFIX) ? p.slice(LEAN_WORKSPACE_PREFIX.length) : p;
    const slash = rel.indexOf('/');
    const dir = slash < 0 ? '(root)' : rel.slice(0, slash);
    if (!groups.has(dir)) groups.set(dir, []);
    groups.get(dir).push({ rel, full: p });
  }
  const dirs = [...groups.keys()].sort();
  const html = dirs.map(dir => {
    const items = groups.get(dir).sort((a, b) => a.rel.localeCompare(b.rel));
    const links = items.map(({ rel, full }) => {
      const active = full === state.currentFile ? ' active' : '';
      const f = flags[full];
      let cls = '', marks = '';
      // Root = contains a main theorem; an entry point worth reading. Emoji only,
      // no colour change (colour is reserved for the axiom/sorry warning).
      if (f && f.root) marks += `<span class="nav-root" title="contains a main theorem — start here">⭐</span>`;
      if (f && (f.axiom || f.sorry)) {
        cls = f.axiom ? ' nav-axiom' : ' nav-sorry';
        const t = [f.axiom ? 'axiom' : '', f.sorry ? 'sorry' : ''].filter(Boolean).join(' + ');
        marks += `<span class="nav-flag" title="contains ${t}">⚠</span>`;
      }
      return `<a class="nav-file${active}${cls}" data-path="${escapeHtml(full)}" title="${escapeHtml(full)}">${marks}${escapeHtml(rel)}</a>`;
    }).join('');
    return `<div class="nav-dir">${escapeHtml(dir)}/</div>${links}`;
  }).join('');
  root.innerHTML = html;
  for (const el of root.querySelectorAll('.nav-file')) {
    el.addEventListener('click', (e) => { e.preventDefault(); loadFile(el.dataset.path); });
  }
}

async function toggleNav() {
  const nav = document.getElementById('lean-nav');
  const sp = document.getElementById('nav-splitter');
  const btn = document.getElementById('btn-nav');
  const willShow = nav.hidden;
  nav.hidden = !willShow;
  sp.hidden = !willShow;
  btn.setAttribute('aria-pressed', willShow ? 'true' : 'false');
  if (willShow) {
    if (!state.fileList) await ensureFileList();
    renderNav(document.getElementById('nav-search').value);
  }
}

function setupNavSplitter() {
  const sp = document.getElementById('nav-splitter');
  const col = document.getElementById('lean-col');
  const saved = parseInt(localStorage.getItem('formaliaxiv-nav-w') || '0', 10);
  if (saved && saved > 120) col.style.setProperty('--nav-w', saved + 'px');
  let dragging = false;
  function onMove(e) {
    if (!dragging) return;
    const rect = col.getBoundingClientRect();
    const w = Math.min(rect.width * 0.6, Math.max(120, e.clientX - rect.left));
    col.style.setProperty('--nav-w', w + 'px');
  }
  function onUp() {
    if (!dragging) return;
    dragging = false;
    sp.classList.remove('dragging');
    document.body.style.cursor = '';
    document.body.style.userSelect = '';
    const w = parseInt(getComputedStyle(col).getPropertyValue('--nav-w'), 10);
    if (w) localStorage.setItem('formaliaxiv-nav-w', String(w));
    window.removeEventListener('pointermove', onMove);
    window.removeEventListener('pointerup', onUp);
  }
  sp.addEventListener('pointerdown', (e) => {
    e.preventDefault();
    dragging = true;
    sp.classList.add('dragging');
    document.body.style.cursor = 'col-resize';
    document.body.style.userSelect = 'none';
    window.addEventListener('pointermove', onMove);
    window.addEventListener('pointerup', onUp);
  });
}

// ── Tooltip on hover ────────────────────────────────────────────────────────

function setupHover() {
  const tip = document.getElementById('hover-tip');
  let hideTimer = null;
  const code = document.getElementById('lean-code');

  code.addEventListener('click', (e) => {
    const arr = e.target.closest('.arr[data-label], .arr[data-fqn]');
    if (arr) {
      e.preventDefault();
      if (arr.dataset.label) {
        const page = arr.dataset.page ? parseInt(arr.dataset.page, 10) : null;
        scrollPdfToEnv(arr.dataset.label, page ? { start_page: page } : null);
      } else if (arr.dataset.fqn) {
        scrollPdfToHighlight(arr.dataset.fqn);
      }
      return;
    }
    const el = e.target.closest('.tok-known');
    if (el) {
      e.preventDefault();
      openLeanFromFqn(el.dataset.fqn);
      return;
    }
    const imp = e.target.closest('.tok-import-path');
    if (imp) {
      e.preventDefault();
      const path = importPathToFile(imp.dataset.import);
      if (!path) { flashTip(imp, `external module: ${imp.dataset.import}`); return; }
      ensureFileList().then((list) => {
        if (list.includes(path)) loadFile(path);
        else flashTip(imp, `no local file for ${imp.dataset.import}`);
      });
      return;
    }
    // Anywhere on a linked declaration (not only its gutter arrow) → show it in
    // the PDF. Skipped while the user is selecting text.
    const row = e.target.closest('.ln.in-link');
    if (row && !(window.getSelection && String(window.getSelection()))) {
      if (row.dataset.linkLabel) {
        const page = row.dataset.linkPage ? parseInt(row.dataset.linkPage, 10) : null;
        scrollPdfToEnv(row.dataset.linkLabel, page ? { start_page: page } : null);
      } else if (row.dataset.linkFqn) {
        scrollPdfToHighlight(row.dataset.linkFqn);
      }
    }
  });

  code.addEventListener('mouseover', async (e) => {
    // Precomputed goal state on a tactic line.
    const lno = e.target.closest('.ln.has-goal .lno');
    if (lno) {
      if (hideTimer) { clearTimeout(hideTimer); hideTimer = null; }
      const line = parseInt(lno.parentElement.dataset.line, 10);
      const m = state.infoByFile.get(state.currentFile);
      const goal = m && m.get(line);
      if (goal) showTip(lno, `<div class="h-goal">${escapeHtml(goal)}</div>`);
      return;
    }
    const el = e.target.closest('.tok-known');
    if (!el) return;
    if (hideTimer) { clearTimeout(hideTimer); hideTimer = null; }
    await ensureLeanLoaded();
    const decl = state.declsByFqn.get(el.dataset.fqn);
    if (!decl) return;
    showTip(el, renderDeclTip(decl));
  });
  code.addEventListener('mouseout', (e) => {
    if (!e.target.closest('.tok-known') && !e.target.closest('.ln.has-goal .lno')) return;
    hideTimer = setTimeout(() => { tip.hidden = true; }, 80);
  });

  function flashTip(target, text) {
    showTip(target, `<div class="h-doc">${escapeHtml(text)}</div>`);
    setTimeout(() => { tip.hidden = true; }, 1300);
  }

  function showTip(target, html) {
    tip.innerHTML = html;
    tip.hidden = false;
    const r = target.getBoundingClientRect();
    const tipW = tip.offsetWidth;
    const tipH = tip.offsetHeight;
    let left = r.left;
    let top = r.bottom + 6;
    if (left + tipW > window.innerWidth - 8) left = Math.max(8, window.innerWidth - tipW - 8);
    if (top + tipH > window.innerHeight - 8) top = r.top - tipH - 6;
    tip.style.left = left + 'px';
    tip.style.top = top + 'px';
  }
}

function renderDeclTip(decl) {
  const doc = decl.docstring ? `<div class="h-doc">${escapeHtml(decl.docstring.trim())}</div>` : '';
  const flags = [];
  if (decl.has_sorry) flags.push('has sorry');
  if (decl.is_axiom) flags.push('axiom');
  const flagsStr = flags.length ? `  ·  <span style="color:#e08866">${flags.join(', ')}</span>` : '';
  return `
    <div><span class="h-kind">${escapeHtml(decl.kind)}</span><span class="h-fqn">${escapeHtml(decl.fqn)}</span></div>
    <div class="h-loc">${escapeHtml(decl.file)}  ·  L${decl.decl_range.start_line}–${decl.decl_range.end_line}${flagsStr}</div>
    ${doc}
  `;
}

// ── Comments (server-persisted) ─────────────────────────────────────────────

async function ensureComments() {
  if (state.comments) return state.comments;
  try {
    const r = await fetch(api('comments'));
    state.comments = r.ok ? await r.json() : {};
  } catch (e) { state.comments = {}; }
  return state.comments;
}

async function setCommentKey(key) {
  state.currentCommentKey = key;
  await ensureComments();
  renderComments();
}

function renderComments() {
  const key = state.currentCommentKey;
  const list = document.getElementById('comments-list');
  const items = (state.comments && state.comments[key]) || [];
  document.getElementById('comments-title').textContent =
    `Comments — ${key.startsWith('file:') ? key.slice(5).split('/').pop() : key.split('.').pop()}`;
  if (!items.length) {
    list.innerHTML = `<div class="empty">No comments yet for <code>${escapeHtml(key)}</code>.</div>`;
    return;
  }
  list.innerHTML = items.map(c => `
    <div class="comment" data-id="${escapeHtml(c.id)}">
      <div class="c-head">
        <span class="c-author">${escapeHtml(c.author || 'anon')}</span>
        <span class="c-time">${escapeHtml(new Date(c.ts * 1000).toLocaleString())}</span>
        <button class="c-del" title="Delete" data-id="${escapeHtml(c.id)}">delete</button>
      </div>
      <div class="c-body">${escapeHtml(c.text)}</div>
    </div>`).join('');
  for (const b of list.querySelectorAll('.c-del')) {
    b.addEventListener('click', () => deleteComment(b.dataset.id));
  }
}

async function postComment(text, author) {
  const key = state.currentCommentKey;
  if (!key || !text.trim()) return;
  const body = { op: 'add', key, text: text.trim(), author: (author || '').trim() };
  const r = await fetch(api('comments'), {
    method: 'POST', headers: { 'Content-Type': 'application/json' }, body: JSON.stringify(body),
  });
  if (r.ok) {
    const j = await r.json();
    state.comments[key] = j.comments;
    renderComments();
  }
}

async function deleteComment(id) {
  const key = state.currentCommentKey;
  const r = await fetch(api('comments'), {
    method: 'POST', headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify({ op: 'delete', key, id }),
  });
  if (r.ok) {
    const j = await r.json();
    state.comments[key] = j.comments;
    renderComments();
  }
}

function toggleNotes(force) {
  const sec = document.getElementById('comments');
  const btn = document.getElementById('btn-notes');
  const show = force != null ? force : sec.hidden;
  sec.hidden = !show;
  btn.setAttribute('aria-pressed', show ? 'true' : 'false');
}

function setupComments() {
  document.getElementById('btn-notes').addEventListener('click', () => toggleNotes());
  document.getElementById('comments-collapse').addEventListener('click', () => toggleNotes(false));
  document.getElementById('comment-form').addEventListener('submit', (e) => {
    e.preventDefault();
    const ta = document.getElementById('comment-text');
    const au = document.getElementById('comment-author');
    postComment(ta.value, au.value);
    ta.value = '';
  });
}

// ── Download Lean workspace ─────────────────────────────────────────────────

// Trigger a download of the paper's whole Lean workspace as a .zip. The server
// sets Content-Disposition: attachment, so navigating to the URL downloads the
// file rather than the browser trying to render it.
function downloadLeanZip() {
  if (!PAPER_ID) return;
  const a = document.createElement('a');
  a.href = api('lean.zip');
  a.download = `${PAPER_ID}-lean.zip`;
  document.body.appendChild(a);
  a.click();
  a.remove();
}

// ── Dependency graph ────────────────────────────────────────────────────────

// Open the paper's declaration-level dependency graph in a new tab. Absolute
// path so it resolves to the same host/port the site is served from (works
// behind a reverse proxy as well as on localhost).
function openGraph() {
  if (!PAPER_ID) return;
  window.open(`${ROOT}p/${encodeURIComponent(PAPER_ID)}/graph/`, '_blank', 'noopener');
}

// ── Word wrap toggle ────────────────────────────────────────────────────────

function setupWrapToggle() {
  const btn = document.getElementById('btn-wrap');
  const code = document.getElementById('lean-code');
  // Default: wrap on
  const stored = localStorage.getItem('formaliaxiv-wrap');
  const wrap = stored == null ? true : stored === '1';
  applyWrap(wrap);
  btn.addEventListener('click', () => applyWrap(code.classList.contains('nowrap')));
  function applyWrap(on) {
    code.classList.toggle('nowrap', !on);
    btn.setAttribute('aria-pressed', on ? 'true' : 'false');
    localStorage.setItem('formaliaxiv-wrap', on ? '1' : '0');
  }
}

// ── Init ────────────────────────────────────────────────────────────────────

async function main() {
  // Static export (GitHub Pages) has no backend to persist comments — hide the
  // notes feature entirely so nothing tries to POST.
  if (window.__STATIC__) {
    for (const id of ['btn-notes', 'comment-form']) {
      const el = document.getElementById(id);
      if (el) el.style.display = 'none';
    }
  }
  document.getElementById('lean-close').addEventListener('click', closeLeanPanel);
  document.getElementById('btn-nav').addEventListener('click', toggleNav);
  document.getElementById('btn-download').addEventListener('click', downloadLeanZip);
  document.getElementById('btn-graph').addEventListener('click', openGraph);
  document.getElementById('open-lean').addEventListener('click', openLeanBrowser);
  document.getElementById('nav-search').addEventListener('input', (e) => renderNav(e.target.value));
  document.getElementById('nav-flagged-cb').addEventListener('change', (e) => {
    state.navFlaggedOnly = e.target.checked;
    renderNav(document.getElementById('nav-search').value);
  });
  document.addEventListener('keydown', (e) => {
    if (e.target.tagName === 'INPUT' || e.target.tagName === 'TEXTAREA') return;
    const leanOpen = !document.getElementById('lean-col').hidden;
    if (e.key === 'Escape') closeLeanPanel();
    if ((e.key === 'l' || e.key === 'L') && !leanOpen) openLeanBrowser();
    if ((e.key === 'b' || e.key === 'B') && leanOpen) toggleNav();
    if ((e.key === 'n' || e.key === 'N') && leanOpen) toggleNotes();
    if ((e.key === 'd' || e.key === 'D') && leanOpen) downloadLeanZip();
    if ((e.key === 'g' || e.key === 'G') && leanOpen) openGraph();
  });
  setupSplitter();
  setupNavSplitter();
  setupWrapToggle();
  setupHover();
  setupComments();

  if (!PAPER_ID) { document.getElementById('loading').textContent = 'No paper selected.'; return; }

  let paper, meta;
  try {
    [paper, meta] = await Promise.all([
      fetch(api('paper.json')).then(r => r.json()),
      fetch(api('meta')).then(r => r.json()),
    ]);
    state.paper = paper;
    if (meta.title) document.title = meta.title + ' — FormaliaXiv';
  } catch (e) {
    document.getElementById('loading').textContent = 'Failed to load paper data: ' + e;
    return;
  }

  // pdf_url is emitted as a root-relative path (/files/...); resolve it against
  // ROOT so it works under a sub-path deployment too.
  const pdfUrl = meta.pdf_url ? new URL(meta.pdf_url.replace(/^\//, ''), ROOT).href : null;
  state.report = meta.report || null;   // the paper's formalization report, if it ships one
  if (!pdfUrl) { document.getElementById('loading').textContent = 'No PDF found for this paper.'; return; }

  for (const env of paper.envs) {
    if (env.label) state.envPageByLabel.set(env.label, env.pdf_page || env.page_range?.start_page);
  }
  for (const env of paper.envs) {
    const link = bestLeanLink(env);
    if (!link || !env.page_range) continue;
    // Candidate strings to locate the env in the PDF, best first:
    //  1) a "Theorem N." style heading derived from a numeric label (precise), then
    //  2) the env's statement text (works for any label style).
    const sigs = [];
    const ls = labelToSignature(env.label);
    if (ls) sigs.push(ls);
    if (env.head_text && env.head_text.trim().split(/\s+/).length >= 3) sigs.push(env.head_text);
    if (!sigs.length) continue;
    // pdf_page (text-derived) overrides the indexer page when the latter was
    // degenerate (all page 1); otherwise it's null and we use page_range.
    const p = env.pdf_page || env.page_range.start_page;
    if (!state.envsByPage.has(p)) state.envsByPage.set(p, []);
    state.envsByPage.get(p).push({ env, link, sigs, page: p });
  }

  // Span-based highlights (new link model): bucket by page, index by Lean fqn.
  // Links outside the paper's link_scope (show_in_pdf === false) are indexed
  // for the Lean panel's jump but not drawn until the reader asks for one.
  for (const h of (paper.highlights || [])) {
    if (!h.pdf_page || !h.prose) continue;
    if (h.show_in_pdf !== false) {
      if (!state.highlightsByPage.has(h.pdf_page)) state.highlightsByPage.set(h.pdf_page, []);
      state.highlightsByPage.get(h.pdf_page).push(h);
    }
    if (h.lean_fqn) state.highlightByFqn.set(h.lean_fqn, h);
  }
  // Passages the Lean refutes (errata): the header button jumps to them.
  state.errata = (paper.highlights || []).filter(h => (h.erratum || h.refuted) && h.show_in_pdf !== false && h.pdf_page && h.prose);
  setupErrataButton();

  // Deep link: ?file=<lean path> opens the Lean panel straight on that source
  // (used by the proof-graph viewer's "open file" action). Run it alongside the
  // PDF so a slow PDF render never delays showing the requested file.
  const deepLink = openDeepLinkedFile();

  try {
    await buildPdfView(pdfUrl);
  } catch (e) {
    document.getElementById('loading').textContent = 'Failed to load PDF: ' + e;
  }
  await deepLink;
}

// Open the file named in the ?file= query param, if any, in the Lean panel.
async function openDeepLinkedFile() {
  const want = new URLSearchParams(location.search).get('file');
  if (!want) return;
  try {
    openLeanPanel();
    if (document.getElementById('lean-nav').hidden) await toggleNav();
    await ensureFileList();
    // Accept the path with or without the lean_workspace/ prefix.
    const path = state.fileList.includes(want)
      ? want
      : state.fileList.find(f => f === LEAN_WORKSPACE_PREFIX + want || f.endsWith('/' + want) || f === want);
    if (path) await loadFile(path);
  } catch (e) {
    /* deep link is best-effort; ignore failures */
  }
}

main();
