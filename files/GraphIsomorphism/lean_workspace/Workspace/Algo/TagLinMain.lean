/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 4.1.1: the running time of the tagged refinement process.  The whole program: parse
the input, run the rounds, write `X*`.
-/
import Workspace.Algo.TagLinSem
import Workspace.Machine.BridgeUp

/-!
# The tagged refinement process on the RAM

The program `tagProg` reads a raw tagged digraph `r` (colors, edges, tag), runs the rounds of
§4.1.1 until the number of colors stops growing, and writes `X* = (V, E, c*, t*)`
(`Algo.taggedOut`).

## Memory

After the bridge `up`, the input is copied to `F = 3L + 200` (`L` the input length), with
its length at `F`.  The records of the rounds (`S`, `A`, `d`: the address array of the color
strings, the sort's region, the number of colors) are at `100, 103, …`.  All other data is
allocated upward from `F + L + 1` (register `14`).

## Registers

`1` the constant `1`; `14` the free address; `15` the edge block (its length cell), `17`,
`18` the tag's encoding (start, length); `20`, `21` the string address array and `n`;
`40`, `41` the ranks and the number of colors of the last round; `42`, `43` the first edge and
the number of edges; `50` the next record, `54` the number of records, `55` the loop flag.
The sort (`Workspace/Algo/TagLinSort.lean`) and the round (`Workspace/Algo/TagLinRows.lean`)
write only registers below `50` other than these.

No axiom, no `sorry`.
-/

namespace Algo

namespace TagLin

open RAM RAM.Exact

/-! ## The layout of the input -/

theorem encode_edge (e : ℕ × ℕ) : Enc.encode e = [1, e.1, 1, e.2] := rfl

theorem length_encList_edges (es : List (ℕ × ℕ)) :
    (encList Enc.encode es).length = 5 * es.length := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    rw [encList, List.length_append, ih, encode_edge]; simp [RAM.frame]; ring

/-- The edges in a block: edge `e` is `[4, 1, a, 1, b]` at `E0 + 5e`. -/
theorem Blk.edges {m : Mem} {E0 : ℕ} {es : List (ℕ × ℕ)} (h : Blk m E0 (encList Enc.encode es))
    (e : ℕ) (he : e < es.length) :
    m (E0 + 5 * e + 2) = es[e].1 ∧ m (E0 + 5 * e + 4) = es[e].2 := by
  have h1 := h.encList_get e he
  have hl : (encList Enc.encode (es.take e)).length = 5 * e := by
    rw [length_encList_edges, List.length_take]; omega
  rw [hl, encode_edge] at h1
  have a := h1 2 (by simp [RAM.frame])
  have b := h1 4 (by simp [RAM.frame])
  simp [RAM.frame] at a b
  exact ⟨by rw [a], by rw [b]⟩

/-- The layout of a raw tagged digraph: the colors, then the edges, then the tag. -/
theorem input_layout {M : Mem} {F : ℕ} {r : RawTagged} (h : Blk M (F + 1) (Enc.encode r)) :
    let ec := encList Enc.encode r.1
    let ee := encList Enc.encode r.2.1
    let et := encList Enc.encode r.2.2
    M (F + 1) = ec.length ∧ Blk M (F + 2) ec ∧ M (F + 3 + ec.length) = ee.length ∧
      Blk M (F + 4 + ec.length) ee ∧ M (F + 4 + ec.length + ee.length) = et.length ∧
      Blk M (F + 5 + ec.length + ee.length) et ∧
      (Enc.encode r).length = ec.length + ee.length + et.length + 4 := by
  intro ec ee et
  rw [Blk.encode_pair] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  rw [Blk.encode_pair] at h4
  obtain ⟨g1, g2, g3, g4⟩ := h4
  have eec : (Enc.encode r.1).length = ec.length := rfl
  have eee : (Enc.encode r.2.1).length = ee.length := rfl
  have eet : (Enc.encode r.2.2).length = et.length := rfl
  have e2 : (Enc.encode r.2).length = ee.length + et.length + 2 := by
    change (frame (Enc.encode r.2.1) ++ frame (Enc.encode r.2.2)).length = _
    simp [RAM.frame]; rw [eee, eet]; ring
  rw [eec] at h1 h3 g1 g2 g3 g4
  rw [eee] at g1 g3 g4
  rw [eet] at g3
  refine ⟨h1, h2, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show F + 3 + ec.length = F + 1 + 1 + ec.length + 1 by ring]; exact g1
  · rwa [show F + 1 + 1 + ec.length + 1 + 1 = F + 4 + ec.length by ring] at g2
  · rwa [show F + 1 + 1 + ec.length + 1 + 1 + ee.length = F + 4 + ec.length + ee.length by ring]
      at g3
  · rwa [show F + 1 + 1 + ec.length + 1 + 1 + ee.length + 1 = F + 5 + ec.length + ee.length by
      ring] at g4
  · change (frame (Enc.encode r.1) ++ frame (Enc.encode r.2)).length = _
    simp only [List.length_append, RAM.frame, List.length_cons, e2, eec]; ring

/-! ## The programs -/

/-- Copy the input from `16` to `F = 3L + 200`, its length first. -/
def setupP : Program :=
  seq (assign 0 16) (seq (copyTo 1 16) (seq (addTo 1 1 16) (seq (addTo 1 1 16)
    (seq (assign 2 200) (seq (addTo 1 1 2) (seq (copyTo 2 16) (seq (assign 3 1)
    (seq (addTo 2 2 3) (Arrays.copyBlock 0 1 2 3)))))))))

/-- Read the layout: the colors (`30`, `31`), the edges (`15`, `42`), the tag (`17`, `18`),
the free address `F + L + 1` (`20`). -/
def parseP : Program :=
  seq (copyTo 10 1) (seq (assign 1 1) (seq (addTo 2 10 1) (seq (loadTo 3 2) (seq (addTo 30 2 1)
    (seq (addTo 31 30 3) (seq (addTo 15 31 1) (seq (loadTo 4 15) (seq (addTo 42 15 1)
    (seq (addTo 5 42 4) (seq (loadTo 18 5) (seq (addTo 17 5 1) (seq (loadTo 6 10)
    (seq (addTo 20 10 6) (seq (addTo 20 20 1) (seq (assign 21 0) (assign 43 0))))))))))))))))

/-- Count the edges: `|ee| / 5`. -/
def ecntP : Program :=
  whileNz 4 (seq (subTo 4 4 1) (seq (subTo 4 4 1) (seq (subTo 4 4 1) (seq (subTo 4 4 1)
    (seq (subTo 4 4 1) (addTo 43 43 1))))))

/-- The addresses of the color strings: `S₀[v]` at `F + L + 1 + v`. -/
def ptrP : Program :=
  framesLoop 30 31 32 33 (seq (addTo 2 20 21) (seq (storeTo 2 30) (addTo 21 21 1)))

/-- Store the record of the round just sorted and advance. -/
def recP : Program :=
  seq (storeTo 50 20) (seq (addTo 2 50 1) (seq (storeTo 2 22) (seq (addTo 2 2 1)
    (seq (storeTo 2 23) (seq (addTo 50 50 1) (seq (addTo 50 50 1) (seq (addTo 50 50 1)
    (addTo 54 54 1))))))))

/-- Round `0`: sort the input colors, record. -/
def round0P : Program :=
  seq (addTo 14 20 21) (seq (assign 50 100) (seq (assign 54 0) (seq sortProg (seq recP
    (seq (copyTo 40 24) (seq (copyTo 41 23) (assign 55 1)))))))

/-- One more round: the new colors, sort, record, compare the numbers of colors. -/
def roundP : Program :=
  seq rowsProg (seq sortProg (seq recP (seq (subTo 55 23 41) (seq (copyTo 41 23)
    (copyTo 40 24)))))

/-- The rounds, until the number of colors stops growing. -/
def roundsP : Program := whileNz 55 roundP

/-! ## The constants of an input -/

/-- The input length. -/
def Lr (r : RawTagged) : ℕ := (Enc.encode r).length

/-- The base of the copy of the input. -/
def Fr (r : RawTagged) : ℕ := 3 * Lr r + 200

/-- The lengths of the encodings of the colors, the edges and the tag. -/
def ecl (r : RawTagged) : ℕ := (encList Enc.encode r.1).length
def eel (r : RawTagged) : ℕ := (encList Enc.encode r.2.1).length
def etl (r : RawTagged) : ℕ := (encList Enc.encode r.2.2).length

/-- The length cell of the edge block, the first edge, the tag. -/
def Eblk (r : RawTagged) : ℕ := Fr r + 3 + ecl r
def E0 (r : RawTagged) : ℕ := Fr r + 4 + ecl r
def T0 (r : RawTagged) : ℕ := Fr r + 5 + ecl r + eel r

/-- The first free address after the input: the address array of round `0`. -/
def SA0 (r : RawTagged) : ℕ := Fr r + Lr r + 1

/-- The address of the color of vertex `v` in the input. -/
def cp (r : RawTagged) (v : ℕ) : ℕ := Fr r + 2 + (encList Enc.encode (r.1.take v)).length

theorem Lr_eq (r : RawTagged) : Lr r = ecl r + eel r + etl r + 4 := by
  unfold Lr ecl eel etl
  change (frame (Enc.encode r.1) ++ frame (frame (Enc.encode r.2.1) ++
    frame (Enc.encode r.2.2))).length = _
  simp only [List.length_append, RAM.frame, List.length_cons]
  change (encList Enc.encode r.1).length + 1 + ((encList Enc.encode r.2.1).length + 1 +
    ((encList Enc.encode r.2.2).length + 1) + 1) = _
  ring

theorem n_le_ecl (r : RawTagged) : r.1.length ≤ ecl r := by
  unfold ecl
  generalize r.1 = cs
  induction cs with
  | nil => simp [encList]
  | cons c cs ih => simp only [encList, List.length_append, RAM.frame, List.length_cons]; omega

theorem eel_eq (r : RawTagged) : eel r = 5 * r.2.1.length := length_encList_edges _

/-- The number of edges is at most `n²` (no repeated edge, ends are vertices). -/
theorem edges_le_sq {r : RawTagged} (hr : r.WF) : r.2.1.length ≤ r.1.length * r.1.length := by
  classical
  have hsub : r.2.1.toFinset ⊆ Finset.range r.1.length ×ˢ Finset.range r.1.length := by
    intro e he
    rw [List.mem_toFinset] at he
    have := hr.2 e he
    simp only [Finset.mem_product, Finset.mem_range]; exact ⟨this.1, this.2.1⟩
  have := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hr.1, Finset.card_product, Finset.card_range] at this
  exact this

/-! ## The record of a round -/

/-- Round `i` is recorded at `100 + 3i`: the address array `S` of its strings, the region `A`
of its sort (sorted representatives at `A`, ranks at `A + 4n`), the number of colors.  The
palette `PX r i` is read off `S` and `A`, and all these cells lie in `[lo, hi)`. -/
structure RecOK (r : RawTagged) (m : Mem) (lo hi i : ℕ) : Prop where
  d : m (100 + 3 * i + 2) = NX r i
  loS : lo ≤ m (100 + 3 * i)
  loA : lo ≤ m (100 + 3 * i + 1)
  hiS : m (100 + 3 * i) + r.1.length ≤ hi
  hiA : m (100 + 3 * i + 1) + 5 * r.1.length ≤ hi
  pal : ∀ idx < NX r i, m (m (100 + 3 * i + 1) + idx) < r.1.length ∧
    (PX r i)[idx]? = some (sX r i (m (m (100 + 3 * i + 1) + idx))) ∧
    lo ≤ m (m (100 + 3 * i) + m (m (100 + 3 * i + 1) + idx)) ∧
    m (m (100 + 3 * i) + m (m (100 + 3 * i + 1) + idx)) + 1 +
      2 * (sX r i (m (m (100 + 3 * i + 1) + idx))).length ≤ hi ∧
    StrAt m (m (m (100 + 3 * i) + m (m (100 + 3 * i + 1) + idx)))
      (sX r i (m (m (100 + 3 * i + 1) + idx)))
  rank : ∀ x < r.1.length, m (m (100 + 3 * i + 1) + 4 * r.1.length + x) = rX r i x

/-- A record survives writes outside its cells and outside `[lo, hi)`. -/
theorem RecOK.congr {r : RawTagged} {m m' : Mem} {lo hi i : ℕ} (h : RecOK r m lo hi i)
    (hrec : ∀ c < 3, m' (100 + 3 * i + c) = m (100 + 3 * i + c))
    (hm : ∀ z, lo ≤ z → z < hi → m' z = m z) :
    RecOK r m' lo hi i := by
  have e0 : m' (100 + 3 * i) = m (100 + 3 * i) := hrec 0 (by omega)
  have e1 : m' (100 + 3 * i + 1) = m (100 + 3 * i + 1) := hrec 1 (by omega)
  have e2 : m' (100 + 3 * i + 2) = m (100 + 3 * i + 2) := hrec 2 (by omega)
  obtain ⟨hd, hS, hA, hS', hA', hpal, hrk⟩ := h
  refine ⟨by rw [e2, hd], by rw [e0]; exact hS, by rw [e1]; exact hA, by rw [e0]; exact hS',
    by rw [e1]; exact hA', fun idx hidx => ?_, fun x hx => ?_⟩
  · obtain ⟨a, b, c, d, f⟩ := hpal idx hidx
    have hlt : idx < 5 * r.1.length := by
      have := NX_le r i; omega
    have g1 : m' (m (100 + 3 * i + 1) + idx) = m (m (100 + 3 * i + 1) + idx) :=
      hm _ (by omega) (by omega)
    have g2 : m' (m (100 + 3 * i) + m (m (100 + 3 * i + 1) + idx)) =
        m (m (100 + 3 * i) + m (m (100 + 3 * i + 1) + idx)) := hm _ (by omega) (by omega)
    rw [e0, e1, g1, g2]
    refine ⟨a, b, c, d, f.congr (fun z hz1 hz2 => hm z (by omega) (by omega))⟩
  · rw [e1, hm _ (by omega) (by omega), hrk x hx]

theorem RecOK.mono {r : RawTagged} {m : Mem} {lo hi hi' i : ℕ} (h : RecOK r m lo hi i)
    (hh : hi ≤ hi') : RecOK r m lo hi' i := by
  obtain ⟨hd, hS, hA, hS', hA', hpal, hrk⟩ := h
  refine ⟨hd, hS, hA, by omega, by omega, fun idx hidx => ?_, hrk⟩
  obtain ⟨a, b, c, d, f⟩ := hpal idx hidx
  exact ⟨a, b, c, by omega, f⟩

/-! ## The state between rounds -/

/-- The state after the rounds `0, …, j`. -/
structure MInv (r : RawTagged) (j : ℕ) (m : Mem) : Prop where
  one : m 1 = 1
  inp : Blk m (Fr r) (Lr r :: Enc.encode r)
  r15 : m 15 = Eblk r
  r17 : m 17 = T0 r
  r18 : m 18 = etl r
  r21 : m 21 = r.1.length
  r42 : m 42 = E0 r
  r43 : m 43 = r.2.1.length
  r50 : m 50 = 100 + 3 * (j + 1)
  r54 : m 54 = j + 1
  r14 : SA0 r + r.1.length ≤ m 14
  r40 : m 40 = m (100 + 3 * j + 1) + 4 * r.1.length
  r41 : m 41 = NX r j
  flag : m 55 = 0 ↔ (0 < j ∧ NX r j = NX r (j - 1))
  recs : ∀ i ≤ j, RecOK r m (Fr r) (m 14) i
  nostop : ∀ i, i + 1 < j → NX r (i + 1) ≠ NX r i

/-- While the number of colors grows, round `j` has at least `j` colors more than round `0`. -/
theorem le_NX_of_nostop (r : RawTagged) {j : ℕ} (h : ∀ i < j, NX r (i + 1) ≠ NX r i) :
    j ≤ NX r j := by
  induction j with
  | zero => omega
  | succ j ih =>
    have h1 := ih (fun i hi => h i (by omega))
    have h2 := h j (by omega)
    have h3 := NX_mono r j
    omega

/-! ## Setup and parsing -/

/-- **Setup**: the input, with its length first, is copied to `F`. -/
theorem runsTo_setupP (r : RawTagged) :
    RunsTo setupP (fun m => m = initMemAt 16 (Enc.encode r))
      (fun m => m 1 = Fr r ∧ Blk m (Fr r) (Lr r :: Enc.encode r)) (7 * (Lr r + 1) + 14) := by
  set l := Enc.encode r with hl
  set L := l.length with hLdef
  have eL : Lr r = L := rfl
  set M0 := initMemAt 16 l with hM0
  have e16 : M0 16 = L := by rw [hM0, initMemAt_of_ge _ (le_refl _)]; simp [initMem, hLdef]
  have eM0 : ∀ j (hj : j < L + 1), M0 (16 + j) = (L :: l)[j]'(by simp; omega) := by
    intro j hj
    rw [hM0, initMemAt_of_ge _ (by omega)]
    rcases j with _ | j
    · simp [initMem, hLdef]
    · simp only [initMem, Nat.add_sub_cancel_left, Nat.add_one_ne_zero, if_false,
        Nat.add_sub_cancel, List.getElem_cons_succ]
      rw [List.getD_eq_getElem _ _ (by omega)]
  unfold setupP
  refine RunsTo.mono (T := 1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (7 * (L + 1) + 5))))))))))
    ?_ (by rw [eL]; omega)
  refine assign_seq (copy_seq (add_seq (add_seq (assign_seq (add_seq (copy_seq (assign_seq
    (add_seq ?_))))))))
  refine ExplLinear.at_mem (fun M1 => M1 0 = 16 ∧ M1 1 = Fr r ∧ M1 2 = L + 1 ∧
      ∀ z, 4 ≤ z → M1 z = M0 z) ⟨?_, ?_, ?_, ?_⟩ (fun M1 hM1 => ?_)
  · simp (disch := omega) only [Mem.update_self, Mem.update_of_ne]
  · simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, e16]; unfold Fr; omega
  · simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, e16]
  · intro z hz; simp (disch := omega) only [Mem.update_self, Mem.update_of_ne]
  obtain ⟨h0, h1, h2, h4⟩ := hM1
  have hF : Fr r = 3 * L + 200 := rfl
  refine ((Arrays.runsTo_copyBlock 0 1 2 3 (by omega) (by omega) (by omega) M1 (by rw [h0]; omega)
    (by rw [h1]; omega) (Or.inr (by rw [h0, h2, h1]; omega))).mono (by rw [h2])).weaken
    (fun M2 ⟨hc1, hc2⟩ => ?_)
  rw [h0, h1, h2] at hc1
  rw [h1, h2] at hc2
  refine ⟨by rw [hc2 1 (by omega) (by simp), h1], fun j hj => ?_⟩
  rw [hc1 j (by simpa using hj), h4 _ (by omega), eM0 j (by simpa using hj)]
  rfl

/-- The facts `input_layout` gives at the base `F`. -/
theorem inp_layout {m : Mem} {r : RawTagged} (h : Blk m (Fr r) (Lr r :: Enc.encode r)) :
    m (Fr r) = Lr r ∧ m (Fr r + 1) = ecl r ∧ Blk m (Fr r + 2) (encList Enc.encode r.1) ∧
      m (Eblk r) = eel r ∧ Blk m (E0 r) (encList Enc.encode r.2.1) ∧
      m (T0 r - 1) = etl r ∧ Blk m (T0 r) (encList Enc.encode r.2.2) ∧
      Blk m (Eblk r) (frame (encList Enc.encode r.2.1)) := by
  rw [Blk.cons] at h
  obtain ⟨h0, h1⟩ := h
  obtain ⟨a, b, c, d, e, f, -⟩ := input_layout h1
  have hT : T0 r - 1 = Fr r + 4 + ecl r + eel r := by unfold T0; omega
  refine ⟨h0, a, b, c, d, by rw [hT]; exact e, f, ?_⟩
  rw [Blk.frame_iff]
  exact ⟨c, by rw [show Eblk r + 1 = Fr r + 4 + ecl r by unfold Eblk; ring]; exact d⟩

theorem wf_parseP : Wf parseP := by unfold parseP; wf_tac

/-- **Parsing**: the registers of the layout. -/
theorem runsTo_parseP {M : Mem} {r : RawTagged} (h1 : M 1 = Fr r)
    (hb : Blk M (Fr r) (Lr r :: Enc.encode r)) :
    RunsTo parseP (fun m => m = M) (fun m => Outside [1, 2, 3, 4, 5, 6, 10, 15, 17, 18, 20, 21,
      30, 31, 42, 43] M m ∧ m 1 = 1 ∧ m 4 = eel r ∧ m 15 = Eblk r ∧ m 17 = T0 r ∧
      m 18 = etl r ∧ m 20 = SA0 r ∧ m 21 = 0 ∧ m 30 = Fr r + 2 ∧
      m 31 = Fr r + 2 + ecl r ∧ m 42 = E0 r ∧ m 43 = 0) 17 := by
  obtain ⟨g0, g1, -, g3, -, g5, -, -⟩ := inp_layout hb
  have hF : 200 ≤ Fr r := by unfold Fr; omega
  have hT : Fr r + 4 + ecl r + eel r = T0 r - 1 := by unfold T0; omega
  have e3 : M (Fr r + 1 + 1 + 1 + ecl r) = eel r := by
    rw [show Fr r + 1 + 1 + 1 + ecl r = Eblk r by unfold Eblk; ring, g3]
  have e5 : M (Fr r + 1 + 1 + 1 + ecl r + 1 + eel r) = etl r := by
    rw [show Fr r + 1 + 1 + 1 + ecl r + 1 + eel r = T0 r - 1 by unfold T0; omega, g5]
  unfold parseP
  refine copy_seq' (assign_seq' (add_seq' (load_seq' (add_seq' ?_))))
  refine ExplLinear.at_mem (fun m => Outside [1, 2, 3, 10, 30] M m ∧ m 1 = 1 ∧ m 10 = Fr r ∧
    m 2 = Fr r + 1 ∧ m 3 = ecl r ∧ m 30 = Fr r + 2) ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ (fun M1 hM1 => ?_)
  · outside_tac (Outside.refl [1, 2, 3, 10, 30] M)
  all_goals try (simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, h1, g1]; done)
  obtain ⟨o1, f1, f10, f2, f3, f30⟩ := hM1
  have k : ∀ z, z ∉ [1, 2, 3, 10, 30] → M1 z = M z := o1
  have e3' : M1 (Fr r + 2 + ecl r + 1) = eel r := by
    rw [k _ (by simp; omega), show Fr r + 2 + ecl r + 1 = Eblk r by unfold Eblk; ring, g3]
  refine add_seq' (add_seq' (load_seq' (add_seq' (add_seq' ?_))))
  refine ExplLinear.at_mem (fun m => Outside [1, 2, 3, 4, 5, 10, 15, 30, 31, 42] M m ∧ m 1 = 1 ∧
    m 10 = Fr r ∧ m 4 = eel r ∧ m 5 = T0 r - 1 ∧ m 15 = Eblk r ∧ m 30 = Fr r + 2 ∧
    m 31 = Fr r + 2 + ecl r ∧ m 42 = E0 r) ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    (fun M2 hM2 => ?_)
  · intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
    simp (disch := omega) only [Mem.update_of_ne]
    exact k z (by simp; omega)
  all_goals
    simp (config := {failIfUnchanged := false}) (disch := omega) only [Mem.update_self,
      Mem.update_of_ne, f1, f10, f30, f3, e3']
    try (simp only [T0, Eblk, E0]; omega)
  obtain ⟨o2, f1, f10, f4, f5, f15, f30, f31, f42⟩ := hM2
  have k2 : ∀ z, z ∉ [1, 2, 3, 4, 5, 10, 15, 30, 31, 42] → M2 z = M z := o2
  have eT : M2 (T0 r - 1) = etl r := by rw [k2 _ (by simp; unfold T0; omega), g5]
  have eF : M2 (Fr r) = Lr r := by rw [k2 _ (by simp; omega), g0]
  refine load_seq' (add_seq' (load_seq' (add_seq' (add_seq' (assign_seq' (assign_last' ?_))))))
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
    simp (disch := omega) only [Mem.update_of_ne]
    exact k2 z (by simp; omega)
  all_goals simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, f1, f10, f4, f5, f15,
    f30, f31, f42, eT, eF]
  · unfold T0; omega
  · unfold SA0; ring

theorem wf_ecntBody : Wf (seq (subTo 4 4 1) (seq (subTo 4 4 1) (seq (subTo 4 4 1) (seq (subTo 4 4 1)
    (seq (subTo 4 4 1) (addTo 43 43 1)))))) := by wf_tac

/-- **Counting the edges**: `|ee| / 5` in `10 |es| + 1` steps. -/
theorem runsTo_ecntP {M : Mem} {k : ℕ} (h1 : M 1 = 1) (h4 : M 4 = 5 * k) (h43 : M 43 = 0) :
    RunsTo ecntP (fun m => m = M) (fun m => Outside [4, 43] M m ∧ m 43 = k) (10 * k + 1) := by
  have key := runsTo_whileNz_amortX (i := 4) wf_ecntBody
    (fun m => ∃ c ≤ k, m 4 = 5 * (k - c) ∧ m 43 = c ∧ Outside [4, 43] M m) (fun m => 2 * m 4)
    ?_ M ⟨0, by omega, by rw [h4]; simp, h43, Outside.refl _ _⟩
  · obtain ⟨t, ht⟩ := key
    obtain ⟨M', ⟨⟨c, hc, h4', h43', ho⟩, h0, hpot⟩, hrun⟩ := ht.exact
    have : c = k := by
      rcases Nat.lt_or_ge c k with h | h
      · rw [h4'] at h0; omega
      · omega
    subst this
    simp only [h4] at hpot
    exact (hrun.mono (by omega)).weaken (fun m hm => by subst hm; exact ⟨ho, h43'⟩)
  intro m ⟨c, hc, h4', h43', ho⟩ hne
  have e1 : m 1 = 1 := by rw [ho 1 (by simp), h1]
  have hck : c < k := by
    rcases Nat.lt_or_ge c k with h | h
    · exact h
    · rw [h4'] at hne; exfalso; apply hne; rw [show k - c = 0 by omega]
  refine ⟨6, ?_⟩
  rt
  simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, e1, h4', h43']
  refine ⟨⟨c + 1, by omega, by omega, rfl, ?_⟩, by omega⟩
  outside_tac ho

theorem wf_ptrBody : Wf (seq (addTo 2 20 21) (seq (storeTo 2 30) (addTo 21 21 1))) := by wf_tac

/-- **The addresses of the input colors**, in `11 |ec| + 2` steps. -/
theorem runsTo_ptrP {M : Mem} {r : RawTagged} (h1 : M 1 = 1)
    (hb : Blk M (Fr r) (Lr r :: Enc.encode r)) (h20 : M 20 = SA0 r) (h21 : M 21 = 0)
    (h30 : M 30 = Fr r + 2) (h31 : M 31 = Fr r + 2 + ecl r) :
    RunsTo ptrP (fun m => m = M) (fun m => Keep [2, 21, 30, 32, 33] (SA0 r)
      (SA0 r + r.1.length) M m ∧ m 21 = r.1.length ∧
      ∀ v < r.1.length, m (SA0 r + v) = cp r v) (11 * ecl r + 2) := by
  obtain ⟨-, -, hc, -⟩ := inp_layout hb
  have hS : Fr r + 2 + ecl r ≤ SA0 r := by
    have := Lr_eq r; unfold SA0; omega
  have hF : 200 ≤ Fr r := by unfold Fr; omega
  have key := runsTo_framesLoop Enc.encode r.1 (Fr r + 2) (rp := 30) (re := 31) (rc := 32)
    (rt := 33) (by decide) (by omega) wf_ptrBody
    (fun j m => m 20 = SA0 r ∧ m 21 = j ∧ Keep [2, 21, 30, 32, 33] (SA0 r) (SA0 r + j) M m ∧
      ∀ v < j, m (SA0 r + v) = cp r v) (fun _ => 0) 3 0 ?_ (fun _ _ => ⟨rfl, rfl, rfl⟩) ?_ M
    ⟨h20, h21, Keep.refl _ _ _ _, fun v hv => by omega⟩ h30 (by rw [h31]; rfl) h1 hc
  · refine (key.mono (by simp only; unfold ecl; omega)).weaken
      (fun m ⟨⟨_, e21, hk, hv⟩, _⟩ => ⟨hk, e21, hv⟩)
  · intro j m v ⟨a, b, c, d⟩
    have hS64 : 64 ≤ SA0 r := by unfold SA0; omega
    have st : ∀ z, z = 30 ∨ z = 32 ∨ z = 33 → (m.update z v) 20 = SA0 r ∧
        (m.update z v) 21 = j ∧ Keep [2, 21, 30, 32, 33] (SA0 r) (SA0 r + j) M (m.update z v) ∧
        ∀ w < j, (m.update z v) (SA0 r + w) = cp r w := by
      intro z hz
      refine ⟨by rw [Mem.update_of_ne _ _ (by omega), a], by rw [Mem.update_of_ne _ _ (by omega), b],
        c.upd (Or.inl (by simp; omega)) v, fun w hw => ?_⟩
      rw [Mem.update_of_ne _ _ (by omega), d w hw]
    exact ⟨st 30 (by omega), st 32 (by omega), st 33 (by omega)⟩
  · intro j hj m ⟨a, b, c, d⟩ hrp hre h1' hblk
    refine ⟨3, ?_⟩
    rt
    have hS64 : 64 ≤ SA0 r := by unfold SA0; omega
    have hcp : m 30 = cp r j := by rw [hrp]; rfl
    refine ⟨⟨?_, ?_, ?_, fun w hw => ?_⟩, ?_, ?_, ?_, ?_, by simp only; omega⟩
    · simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, a, b, h1', hcp]
    · simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, a, b, h1', hcp]
    · simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, a, b, h1', hcp]
      exact ((c.mono (fun z hz => hz) le_rfl (by omega)).upd (Or.inl (by simp)) _).upd
        (Or.inr ⟨by omega, by omega⟩) _ |>.upd (Or.inl (by simp)) _
    · simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, a, b, h1', hcp]
      rcases Nat.lt_succ_iff_lt_or_eq.1 hw with hw | rfl
      · simp (disch := omega) only [Mem.update_of_ne]; exact d w hw
      · simp (disch := omega) only [Mem.update_of_ne, Mem.update_self]
    · simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, a, b, h1', hcp]
    · simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, a, b, h1', hcp]
    · simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, a, b, h1', hcp]
    · simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, a, b, h1', hcp]
      have hlen := encList_take_le Enc.encode r.1 j
      refine ((hblk.update (Or.inl (by omega))).update (Or.inr ?_)).update (Or.inl (by omega))
      unfold ecl at hS; omega

/-- The state after parsing: the layout registers and the addresses of the input colors. -/
structure PState (r : RawTagged) (m : Mem) : Prop where
  one : m 1 = 1
  inp : Blk m (Fr r) (Lr r :: Enc.encode r)
  r15 : m 15 = Eblk r
  r17 : m 17 = T0 r
  r18 : m 18 = etl r
  r20 : m 20 = SA0 r
  r21 : m 21 = r.1.length
  r42 : m 42 = E0 r
  r43 : m 43 = r.2.1.length
  sa : ∀ v < r.1.length, m (SA0 r + v) = cp r v

/-- **Phase A**: copy, parse, count the edges, the addresses of the colors; `20 L + 41`
steps. -/
theorem runsTo_phaseA (r : RawTagged) :
    RunsTo (seq setupP (seq parseP (seq ecntP ptrP))) (fun m => m = initMemAt 16 (Enc.encode r))
      (PState r) (20 * Lr r + 41) := by
  have hL := Lr_eq r
  have he := eel_eq r
  refine RunsTo.mono (T := (7 * (Lr r + 1) + 14) + (17 + ((10 * r.2.1.length + 1) +
    (11 * ecl r + 2)))) ?_ (by omega)
  refine block_seq (runsTo_setupP r) (fun M1 ⟨h1, hb⟩ => ?_)
  refine block_seq (runsTo_parseP h1 hb) (fun M2 ⟨o2, f1, f4, f15, f17, f18, f20, f21, f30, f31,
    f42, f43⟩ => ?_)
  have hb2 : Blk M2 (Fr r) (Lr r :: Enc.encode r) :=
    ExplLinear.Blk.outside hb o2 (by intro z hz; simp at hz; unfold Fr; omega)
  refine block_seq (runsTo_ecntP (k := r.2.1.length) f1 (by rw [f4, he]) f43)
    (fun M3 ⟨o3, g43⟩ => ?_)
  have k3 : ∀ z, z ∉ [4, 43] → M3 z = M2 z := o3
  have hb3 : Blk M3 (Fr r) (Lr r :: Enc.encode r) :=
    ExplLinear.Blk.outside hb2 o3 (by intro z hz; simp at hz; unfold Fr; omega)
  refine (runsTo_ptrP (by rw [k3 1 (by simp), f1]) hb3 (by rw [k3 20 (by simp), f20])
    (by rw [k3 21 (by simp), f21]) (by rw [k3 30 (by simp), f30])
    (by rw [k3 31 (by simp), f31])).weaken (fun m ⟨hk, e21, hsa⟩ => ?_)
  have hS : Fr r + Lr r + 1 = SA0 r := rfl
  have hS2 : 200 ≤ SA0 r := by unfold SA0 Fr; omega
  have hLl : Lr r = (Enc.encode r).length := rfl
  have k4 : ∀ z, z ∉ [2, 21, 30, 32, 33] → z < SA0 r → m z = M3 z :=
    fun z hz hr => hk z hz (Or.inl hr)
  refine ⟨by rw [k4 1 (by simp) (by omega), k3 1 (by simp), f1],
    hb3.congr (fun z hz1 hz2 => k4 z (by simp; have : 200 ≤ Fr r := (by unfold Fr; omega); omega)
      (by simp at hz2; omega)),
    by rw [k4 15 (by simp) (by omega), k3 15 (by simp), f15],
    by rw [k4 17 (by simp) (by omega), k3 17 (by simp), f17],
    by rw [k4 18 (by simp) (by omega), k3 18 (by simp), f18],
    by rw [k4 20 (by simp) (by omega), k3 20 (by simp), f20], e21,
    by rw [k4 42 (by simp) (by omega), k3 42 (by simp), f42],
    by rw [k4 43 (by simp) (by omega), g43], hsa⟩

/-! ## From a sort to a record -/

theorem getElem?_map_getD {Dl : List ℕ} {f : ℕ → List ℕ} {i : ℕ} (hi : i < Dl.length) :
    (Dl.map f)[i]? = some (f (Dl.getD i 0)) := by
  rw [List.getElem?_map, List.getElem?_eq_getElem hi, List.getD_eq_getElem _ _ hi]; rfl

/-- The palette and the ranks of a sorted round. -/
theorem pal_of_sortOut {r : RawTagged} {j S A : ℕ} {M M2 : Mem} {Dl : List ℕ}
    (h : SortOut r.1.length S A (sX r j) M Dl M2) :
    Dl.map (sX r j) = PX r j ∧ Dl.length = NX r j ∧
      ∀ x < r.1.length, M2 (A + r.1.length + r.1.length + r.1.length + r.1.length + x) =
        rX r j x := by
  have hcov : ∀ v < r.1.length, ∃ w ∈ Dl, sX r j w = sX r j v := fun v hv => by
    obtain ⟨i, hi, -, hs⟩ := h.rank v hv
    refine ⟨Dl.getD i 0, ?_, hs⟩
    rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi
  have hP := PX_of_sorted r j Dl h.sort.sorted h.sort.dlt hcov
  have hN : Dl.length = NX r j := by rw [NX_eq_length, ← hP, List.length_map]
  refine ⟨hP, hN, fun x hx => ?_⟩
  obtain ⟨i, hi, hm, hs⟩ := h.rank x hx
  rw [hm, rX_eq r j hx]
  have hnd : (PX r j).Nodup := by rw [← hP]; exact h.sort.sorted.imp (fun h => ne_of_lt h)
  have hget : (PX r j)[i]'(by rw [← hP, List.length_map]; exact hi) = sX r j x := by
    have := getElem?_map_getD (f := sX r j) hi
    rw [hP, List.getElem?_eq_getElem (by rw [← hP, List.length_map]; exact hi)] at this
    rw [Option.some.inj this, hs]
  rw [← hget, hnd.idxOf_getElem]

/-- **A sorted round, recorded.** -/
theorem recOK_of_sortOut {r : RawTagged} {j S A lo : ℕ} {M M2 m : Mem} {Dl : List ℕ}
    (h : SortOut r.1.length S A (sX r j) M Dl M2)
    (hS : m (100 + 3 * j) = S) (hA : m (100 + 3 * j + 1) = A)
    (hd : m (100 + 3 * j + 2) = Dl.length)
    (hm : ∀ z, lo ≤ z → z < A + 5 * r.1.length → m z = M2 z)
    (hlo : lo ≤ S) (hloS : ∀ v < r.1.length, lo ≤ M2 (S + v)) :
    RecOK r m lo (A + 5 * r.1.length) j := by
  obtain ⟨hP, hN, hrk⟩ := pal_of_sortOut h
  have hE := h.sort.env
  set n := r.1.length with hn
  have hSn : S + n ≤ A := hE.hSAn
  refine ⟨by rw [hd, hN], by rw [hS]; exact hlo, by rw [hA]; omega, by rw [hS]; omega,
    by rw [hA], fun idx hidx => ?_, fun x hx => ?_⟩
  · rw [← hN] at hidx
    have hdn := h.sort.length_le
    obtain ⟨g1, g2⟩ := h.sort.getD hidx
    have e1 : m (A + idx) = Dl.getD idx 0 := by rw [hm _ (by omega) (by omega), g1]
    have e2 : m (S + Dl.getD idx 0) = M2 (S + Dl.getD idx 0) := hm _ (by omega) (by omega)
    have sp := hE.spA _ g2
    have s64 := hloS _ g2
    rw [hS, hA, e1, e2]
    refine ⟨g2, by rw [← hP]; exact getElem?_map_getD hidx, s64, by omega,
      (hE.strs _ g2).congr (fun z hz1 hz2 => hm z (by omega) (by omega))⟩
  · rw [hA, hm _ (by omega) (by omega)]
    have := hrk x hx
    rw [show A + 4 * n + x = A + n + n + n + n + x by ring]; exact this

/-! ## Round `0` -/

/-- The input color of `v` is stored at `cp r v`, inside the input. -/
theorem input_color {m : Mem} {r : RawTagged} (hb : Blk m (Fr r) (Lr r :: Enc.encode r))
    {v : ℕ} (hv : v < r.1.length) :
    StrAt m (cp r v) (sX r 0 v) ∧ Fr r + 2 ≤ cp r v ∧
      cp r v + 1 + 2 * (sX r 0 v).length ≤ Fr r + 2 + ecl r := by
  obtain ⟨-, -, hc, -⟩ := inp_layout hb
  have h1 := hc.encList_get v hv
  have h2 := encList_take_lt Enc.encode r.1 v hv
  rw [sX_zero r hv]
  have e : (Enc.encode r.1[v]).length = 2 * r.1[v].length :=
    ExplLinear.length_encode_nat_list _
  refine ⟨strAt_iff_blk.2 h1, by unfold cp; omega, ?_⟩
  unfold cp ecl; rw [e] at h2; omega

/-- The letters of the input colors. -/
theorem sum_sX_zero_le (r : RawTagged) :
    2 * ∑ y ∈ Finset.range r.1.length, (sX r 0 y).length ≤ ecl r := by
  have key : ∀ k ≤ r.1.length, 2 * ∑ y ∈ Finset.range k, (sX r 0 y).length ≤
      (encList Enc.encode (r.1.take k)).length := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      rw [Finset.sum_range_succ, encList_take_succ Enc.encode r.1 k (by omega), List.length_append,
        sX_zero r (by omega)]
      have := ih (by omega)
      have e : (Enc.encode r.1[k]).length = 2 * r.1[k].length :=
        ExplLinear.length_encode_nat_list _
      simp only [RAM.frame, List.length_cons, e]
      omega
  have := key r.1.length le_rfl
  rwa [List.take_length] at this

/-- The time of the sort of round `0`. -/
noncomputable def tSort0 (r : RawTagged) : ℕ :=
  22 * ∑ y ∈ Finset.range r.1.length, (sX r 0 y).length + 81 * r.1.length * r.1.length +
    134 * r.1.length + 16

theorem wf_recP : Wf recP := by unfold recP; wf_tac

/-- **Recording a round**: `(S, A, d)` from `20, 22, 23` into the cells `100 + 3j + (0,1,2)`;
`9` steps. -/
theorem runsTo_recP {M : Mem} {j : ℕ} (h1 : M 1 = 1) (h50 : M 50 = 100 + 3 * j)
    (h54 : M 54 = j) :
    RunsTo recP (fun m => m = M) (fun m => Keep [2, 50, 54] (100 + 3 * j) (100 + 3 * j + 3) M m ∧
      m (100 + 3 * j) = M 20 ∧ m (100 + 3 * j + 1) = M 22 ∧ m (100 + 3 * j + 2) = M 23 ∧
      m 50 = 100 + 3 * (j + 1) ∧ m 54 = j + 1) 9 := by
  unfold recP
  refine store_seq' (add_seq' (store_seq' (add_seq' (store_seq' (add_seq' (add_seq' (add_seq'
    (add_last' (T := 0) ?_))))))))
  refine ⟨fun z hz hab => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
    simp (disch := omega) only [Mem.update_of_ne, Mem.update_self, h50, h1]
  all_goals simp (disch := omega) only [Mem.update_of_ne, Mem.update_self, h50, h1, h54]
  all_goals omega

/-- **Round `0`**: sort the input colors and record them; `tSort0 + 15` steps. -/
theorem runsTo_round0 {M : Mem} {r : RawTagged} (hP : PState r M) :
    RunsTo round0P (fun m => m = M) (MInv r 0) (tSort0 r + 15) := by
  set n := r.1.length with hn
  have hF : 200 ≤ Fr r := by unfold Fr; omega
  have hS : Fr r + Lr r + 1 = SA0 r := rfl
  have hL := Lr_eq r
  set A := SA0 r + n with hA
  set M1 := ((M.update 14 A).update 50 100).update 54 0 with hM1
  have g1 : ∀ z, z ≠ 14 → z ≠ 50 → z ≠ 54 → M1 z = M z := fun z a b c => by
    rw [hM1, Mem.update_of_ne _ _ c, Mem.update_of_ne _ _ b, Mem.update_of_ne _ _ a]
  have hI : SortIn n (SA0 r) A (sX r 0) M1 := by
    refine ⟨by rw [g1 1 (by omega) (by omega) (by omega), hP.one], by rw [hM1]; simp (disch := omega) only [Mem.update_self, Mem.update_of_ne],
      by rw [g1 20 (by omega) (by omega) (by omega), hP.r20],
      by rw [g1 21 (by omega) (by omega) (by omega), hP.r21], by unfold SA0; omega, by omega,
      fun v hv => ?_, fun v hv => ?_, fun v hv => ?_⟩
    all_goals rw [g1 _ (by unfold SA0; omega) (by unfold SA0; omega) (by unfold SA0; omega),
      hP.sa v hv]
    all_goals obtain ⟨a, b, c⟩ := input_color hP.inp hv
    · omega
    · unfold SA0 at hA; omega
    · exact a.congr (fun z hz1 hz2 => g1 z (by omega) (by omega) (by omega))
  unfold round0P
  refine RunsTo.mono (T := 1 + (1 + (1 + (tSort0 r + (9 + (0 + 1 + 1 + 1)))))) ?_ (by omega)
  refine add_seq (assign_seq (assign_seq ?_))
  have eM1 : ((M.update 14 (M 20 + M 21)).update 50 100).update 54 0 = M1 := by
    rw [hP.r20, hP.r21]
  rw [eM1]
  refine block_seq (runsTo_sortProg hI) (fun M2 ⟨Dl, hO⟩ => ?_)
  have k2 : ∀ z, z ∉ Wsort → z < A → M2 z = M1 z := fun z hz hr => hO.keep z hz (Or.inl hr)
  have hE := hO.sort.env
  obtain ⟨hPX, hN, -⟩ := pal_of_sortOut hO
  have e50 : M2 50 = 100 + 3 * 0 := by rw [k2 50 (by simp) (by omega), hM1]; simp (disch := omega) only [Mem.update_self, Mem.update_of_ne]
  have e54 : M2 54 = 0 := by rw [k2 54 (by simp) (by omega), hM1]; simp (disch := omega) only [Mem.update_self, Mem.update_of_ne]
  refine block_seq (runsTo_recP hE.one e50 e54) (fun M3 ⟨k3, c0, c1, c2, c50, c54⟩ => ?_)
  refine copy_seq' (copy_seq' (assign_last' (T := 0) ?_))
  set mf := ((M3.update 40 (M3 24)).update 41 ((M3.update 40 (M3 24)) 23)).update 55 1 with hmf
  have kf : ∀ z, z ≠ 40 → z ≠ 41 → z ≠ 55 → mf z = M3 z := fun z a b c => by
    rw [hmf, Mem.update_of_ne _ _ c, Mem.update_of_ne _ _ b, Mem.update_of_ne _ _ a]
  -- a cell of the input area or a register kept by everything
  have kM : ∀ z, z ∉ Wsort → z ≠ 2 → z ≠ 14 → z ≠ 40 → z ≠ 41 → z ≠ 50 → z ≠ 54 → z ≠ 55 →
      (z < 100 ∨ 103 ≤ z) → z < A → mf z = M z := by
    intro z hW h2 h14 h40 h41 h50 h54 h55 hz hA'
    rw [kf z h40 h41 h55, k3 z (by simp; omega) (by omega), k2 z hW hA', g1 z h14 h50 h54]
  have k23 : mf 23 = Dl.length := by
    rw [kf 23 (by omega) (by omega) (by omega), k3 23 (by simp) (by omega), hO.sort.r23]
  have m14 : mf 14 = A + 5 * n := by
    rw [kf 14 (by omega) (by omega) (by omega), k3 14 (by simp) (by omega), hO.r14]; ring
  have hmM2 : ∀ z, Fr r ≤ z → z < A + 5 * n → mf z = M2 z := fun z h1 h2 => by
    rw [kf z (by omega) (by omega) (by omega), k3 z (by simp; omega) (by omega)]
  have hrec : RecOK r mf (Fr r) (A + 5 * n) 0 := by
    refine recOK_of_sortOut hO ?_ ?_ ?_ hmM2 (by unfold SA0; omega) (fun v hv => ?_)
    · rw [kf _ (by omega) (by omega) (by omega), c0, hE.r20]
    · rw [kf _ (by omega) (by omega) (by omega), c1, hE.r22]
    · rw [kf _ (by omega) (by omega) (by omega), c2, hO.sort.r23]
    · rw [k2 _ (by simp; unfold SA0; omega) (by omega),
        g1 _ (by unfold SA0; omega) (by unfold SA0; omega) (by unfold SA0; omega), hP.sa v hv]
      have := (input_color hP.inp hv).2.1; omega
  have hLl : Lr r = (Enc.encode r).length := rfl
  have hSA : 200 ≤ SA0 r := by unfold SA0; omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [kf 1 (by omega) (by omega) (by omega), k3 1 (by simp) (by omega), hE.one]
  · exact hP.inp.congr (fun z hz1 hz2 => kM z (by simp; omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega)
      (by simp at hz2; unfold SA0 at hA; omega))
  · rw [kM 15 (by simp) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega), hP.r15]
  · rw [kM 17 (by simp) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega), hP.r17]
  · rw [kM 18 (by simp) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega), hP.r18]
  · rw [kM 21 (by simp) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega), hP.r21]
  · rw [kM 42 (by simp) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega), hP.r42]
  · rw [kM 43 (by simp) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega), hP.r43]
  · rw [kf 50 (by omega) (by omega) (by omega), c50]
  · rw [kf 54 (by omega) (by omega) (by omega), c54]
  · rw [m14]; omega
  · rw [hmf]; simp (disch := omega) only [Mem.update_self, Mem.update_of_ne]
    rw [c1, k3 24 (by simp) (by omega), hE.r24, hE.r22]
    ring
  · rw [hmf]; simp (disch := omega) only [Mem.update_self, Mem.update_of_ne]
    rw [k3 23 (by simp) (by omega), hO.sort.r23, hN]
  · rw [hmf]; simp
  · intro i hi
    obtain rfl : i = 0 := by omega
    rw [m14]; exact hrec
  · intro i hi; omega

/-- While running, the round index is at most `n + 1`. -/
theorem MInv.j_le {r : RawTagged} {j : ℕ} {m : Mem} (h : MInv r j m) : j ≤ r.1.length + 1 := by
  rcases Nat.eq_zero_or_pos j with h0 | hj
  · omega
  · have := le_NX_of_nostop r (j := j - 1) (fun i hi => h.nostop i (by omega))
    have := NX_le r (j - 1)
    omega

/-- The time of round `j + 1`. -/
noncomputable def tRound (r : RawTagged) (j : ℕ) : ℕ :=
  (16 * NX r j * r.1.length + 16 * r.1.length + 42 * r.2.1.length + 15) +
    ((22 * ∑ y ∈ Finset.range r.1.length, (sX r (j + 1) y).length +
      81 * r.1.length * r.1.length + 134 * r.1.length + 16) + (9 + (0 + 1 + 1 + 1)))

/-- **Round `j + 1`**: the rows, their sort, the record, the stop test. -/
theorem runsTo_roundP {M : Mem} {r : RawTagged} {j : ℕ} (hr : r.WF) (hM : MInv r j M)
    (hf : M 55 ≠ 0) : RunsTo roundP (fun m => m = M) (MInv r (j + 1)) (tRound r j) := by
  set n := r.1.length with hn
  have hF : 200 ≤ Fr r := by unfold Fr; omega
  have hL := Lr_eq r
  have hLl : Lr r = (Enc.encode r).length := rfl
  have hjn := hM.j_le
  have hnL := n_le_ecl r
  have hee := eel_eq r
  set fr := M 14 with hfr
  have hfr0 : SA0 r + n ≤ fr := hM.r14
  have hSA : Fr r + Lr r + 1 = SA0 r := rfl
  set N := NX r j with hN
  have hNn : N ≤ n := NX_le r j
  obtain ⟨-, -, -, -, hEb, -, -, -⟩ := inp_layout hM.inp
  have hRj := hM.recs j le_rfl
  have hR := hRj.rank
  unfold roundP
  refine block_seq (T := 16 * N * n + 16 * n + 42 * r.2.1.length + 15)
    (runsTo_rowsProg (fr := fr) (R := M (100 + 3 * j + 1) + 4 * n) (rk := rX r j)
      hM.one rfl hM.r21 hM.r40 hM.r41 hM.r42 hM.r43 (fun x hx => hR x hx)
      (fun x hx => rX_lt r j hx) (fun e he => Blk.edges hEb e he) (edges_lt hr)
      (by have := hRj.loA; omega) (by have := hRj.hiA; omega) (by unfold E0; omega)
      (by unfold E0 SA0 at *; omega)) (fun M2 ⟨k2, e14, e20, hrows⟩ => ?_)
  have k2' : ∀ z, z ∉ Wrows → z < fr → M2 z = M z := fun z hz h => k2 z hz (Or.inl h)
  set A := fr + n + n * rowW N with hA
  have hWl : ∀ v < n, v * rowW N + rowW N ≤ n * rowW N := fun v hv => by
    have := Nat.mul_le_mul_right (rowW N) (show v + 1 ≤ n by omega)
    rw [Nat.add_mul, one_mul] at this
    exact this
  have hWd : rowW N = 4 * N + 3 := rfl
  have hI : SortIn n fr A (sX r (j + 1)) M2 := by
    refine ⟨by rw [k2' 1 (by simp) (by omega), hM.one], e14, e20,
      by rw [k2' 21 (by simp) (by omega), hM.r21], by unfold SA0 at hfr0; omega, by omega,
      fun v hv => ?_, fun v hv => ?_, fun v hv => ?_⟩
    · rw [(hrows v hv).1]; unfold SA0 at hfr0; omega
    · rw [(hrows v hv).1, sX_succ hr j hv, length_rowStr]
      have := hWl v hv; omega
    · rw [(hrows v hv).1, sX_succ hr j hv]; exact (hrows v hv).2
  refine block_seq (runsTo_sortProg hI) (fun M3 ⟨Dl, hO⟩ => ?_)
  have k3 : ∀ z, z ∉ Wsort → z < A → M3 z = M2 z := fun z hz hr => hO.keep z hz (Or.inl hr)
  have hE := hO.sort.env
  obtain ⟨hPX, hND, -⟩ := pal_of_sortOut hO
  have kM : ∀ z, z ∉ Wsort → z ∉ Wrows → z < fr → M3 z = M z := fun z h1 h2 h3 => by
    rw [k3 z h1 (by omega), k2' z h2 h3]
  have e50 : M3 50 = 100 + 3 * (j + 1) := by
    rw [kM 50 (by simp) (by simp) (by unfold SA0 at hfr0; omega), hM.r50]
  have e54 : M3 54 = j + 1 := by
    rw [kM 54 (by simp) (by simp) (by unfold SA0 at hfr0; omega), hM.r54]
  refine block_seq (runsTo_recP hE.one e50 e54) (fun M4 ⟨k4, c0, c1, c2, c50, c54⟩ => ?_)
  refine sub_seq' (copy_seq' (copy_last' (T := 0) ?_))
  set mf := ((M4.update 55 (M4 23 - M4 41)).update 41 ((M4.update 55 (M4 23 - M4 41)) 23)).update
    40 (((M4.update 55 (M4 23 - M4 41)).update 41 ((M4.update 55 (M4 23 - M4 41)) 23)) 24)
    with hmf
  have kf : ∀ z, z ≠ 40 → z ≠ 41 → z ≠ 55 → mf z = M4 z := fun z a b c => by
    rw [hmf, Mem.update_of_ne _ _ a, Mem.update_of_ne _ _ b, Mem.update_of_ne _ _ c]
  have hrecj : 100 + 3 * (j + 1) + 3 ≤ Fr r := by unfold Fr; omega
  have kA : ∀ z, z ∉ Wsort → z ∉ Wrows → z ≠ 2 → z ≠ 40 → z ≠ 41 → z ≠ 50 → z ≠ 54 →
      z ≠ 55 → (z < 100 + 3 * (j + 1) ∨ 100 + 3 * (j + 1) + 3 ≤ z) → z < fr → mf z = M z := by
    intro z h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
    rw [kf z h4 h5 h8, k4 z (by simp; omega) h9, kM z h1 h2 h10]
  have m23 : M4 23 = Dl.length := by rw [k4 23 (by simp) (by omega), hO.sort.r23]
  have m41 : M4 41 = N := by
    rw [k4 41 (by simp) (by omega), kM 41 (by simp) (by simp) (by unfold SA0 at hfr0; omega),
      hM.r41]
  have m14 : mf 14 = A + 5 * n := by
    rw [kf 14 (by omega) (by omega) (by omega), k4 14 (by simp) (by omega), hO.r14]; ring
  have hmM3 : ∀ z, Fr r ≤ z → z < A + 5 * n → mf z = M3 z := fun z h1 h2 => by
    rw [kf z (by omega) (by omega) (by omega), k4 z (by simp; omega) (by omega)]
  have hrec : RecOK r mf (Fr r) (A + 5 * n) (j + 1) := by
    refine recOK_of_sortOut hO ?_ ?_ ?_ hmM3 (by unfold SA0 at hfr0; omega) (fun v hv => ?_)
    · rw [kf _ (by omega) (by omega) (by omega), c0, hE.r20]
    · rw [kf _ (by omega) (by omega) (by omega), c1, hE.r22]
    · rw [kf _ (by omega) (by omega) (by omega), c2, hO.sort.r23]
    · rw [k3 _ (by simp; unfold SA0 at hfr0; omega) (by omega), (hrows v hv).1]
      unfold SA0 at hfr0; omega
  have hNj1 : Dl.length = NX r (j + 1) := hND
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [kf 1 (by omega) (by omega) (by omega), k4 1 (by simp) (by omega), hE.one]
  · exact hM.inp.congr (fun z hz1 hz2 => kA z (by simp; omega) (by simp; omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by simp at hz2; unfold SA0 at hfr0; omega))
  all_goals first
    | (rw [kA 15 (by simp) (by simp) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by unfold SA0 at hfr0; omega), hM.r15]; done)
    | (rw [kA 17 (by simp) (by simp) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by unfold SA0 at hfr0; omega), hM.r17]; done)
    | (rw [kA 18 (by simp) (by simp) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by unfold SA0 at hfr0; omega), hM.r18]; done)
    | (rw [kA 21 (by simp) (by simp) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by unfold SA0 at hfr0; omega), hM.r21]; done)
    | (rw [kA 42 (by simp) (by simp) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by unfold SA0 at hfr0; omega), hM.r42]; done)
    | (rw [kA 43 (by simp) (by simp) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by unfold SA0 at hfr0; omega), hM.r43]; done)
    | skip
  · rw [kf 50 (by omega) (by omega) (by omega), c50]
  · rw [kf 54 (by omega) (by omega) (by omega), c54]
  · rw [m14]; omega
  · rw [hmf]; simp (disch := omega) only [Mem.update_self, Mem.update_of_ne]
    rw [c1, k4 24 (by simp) (by omega), hE.r24, hE.r22]
    ring
  · rw [hmf]; simp (disch := omega) only [Mem.update_self, Mem.update_of_ne]
    rw [m23, hNj1]
  · rw [hmf]; simp (disch := omega) only [Mem.update_self, Mem.update_of_ne]
    rw [m23, m41, hNj1]
    have := NX_mono r j
    constructor
    · intro h; exact ⟨by omega, by simp only [Nat.add_sub_cancel]; omega⟩
    · rintro ⟨-, h⟩; simp only [Nat.add_sub_cancel] at h; omega
  · intro i hi
    rcases Nat.lt_or_ge i (j + 1) with hij | hij
    · have := (hM.recs i (by omega)).congr (m' := mf) (fun c hc => kA _ (by simp; omega)
        (by simp; omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by unfold SA0 at hfr0; omega))
        (fun z hz1 hz2 => kA z (by simp; omega) (by simp; omega) (by omega) (by omega) (by omega)
          (by omega) (by omega) (by omega) (by omega) hz2)
      exact this.mono (by rw [m14]; omega)
    · obtain rfl : i = j + 1 := by omega
      rw [m14]; exact hrec
  · intro i hi
    rcases Nat.lt_or_ge (i + 1) j with h | h
    · exact hM.nostop i h
    · obtain rfl : j = i + 1 := by omega
      intro he
      exact hf (hM.flag.2 ⟨by omega, by simp only [Nat.add_sub_cancel]; exact he⟩)

theorem wf_sortProg : Wf sortProg := by
  unfold sortProg sortInit posLoop rankLoop
  wf_tac

theorem wf_rowsProg : Wf rowsProg := by
  unfold rowsProg rowsInit edgesProg
  wf_tac

theorem wf_roundP : Wf roundP := by
  unfold roundP
  wf_tac

/-- The letters of the colors of round `j + 1`: `n (2 N_j + 1)`. -/
theorem sum_sX_succ {r : RawTagged} (hr : r.WF) (j : ℕ) :
    ∑ y ∈ Finset.range r.1.length, (sX r (j + 1) y).length =
      r.1.length * (2 * NX r j + 1) := by
  rw [Finset.sum_congr rfl (fun y hy => by
    rw [sX_succ hr j (Finset.mem_range.1 hy), length_rowStr]), Finset.sum_const,
    Finset.card_range, smul_eq_mul]

/-- A bound on the cost of one round, plus the loop test. -/
def Kr (r : RawTagged) : ℕ :=
  141 * r.1.length * r.1.length + 172 * r.1.length + 42 * r.2.1.length + 45

theorem tRound_le {r : RawTagged} (hr : r.WF) (j : ℕ) : tRound r j + 2 ≤ Kr r := by
  unfold tRound Kr
  rw [sum_sX_succ hr j]
  have h := NX_le r j
  have h1 : NX r j * r.1.length ≤ r.1.length * r.1.length := Nat.mul_le_mul_right _ h
  have h2 : r.1.length * NX r j ≤ r.1.length * r.1.length := Nat.mul_le_mul_left _ h
  nlinarith

/-- **The rounds**: from round `0` to the first round `k + 1` that does not add a color; at most
`Kr (n + 1) + 1` steps. -/
theorem runsTo_roundsP {M : Mem} {r : RawTagged} (hr : r.WF) (hM : MInv r 0 M) :
    ∃ t ≤ Kr r * (r.1.length + 1) + 1, RunsTo roundsP (fun m => m = M)
      (fun m => MInv r (Babai.TaggedDigraph.stopIdx (decTagged r) + 1) m) t := by
  set n := r.1.length
  have hloop := runsTo_whileNz_amortX (i := 55) wf_roundP (fun m => ∃ j, MInv r j m)
    (fun m => Kr r * (n + 2 - m 54)) (fun M' ⟨j, hj⟩ hf => by
      have hjn : j ≤ n := by
        have := le_NX_of_nostop r (j := j) (fun i hi => by
          rcases Nat.lt_or_ge (i + 1) j with h | h
          · exact hj.nostop i h
          · obtain rfl : j = i + 1 := by omega
            intro he
            exact hf (hj.flag.2 ⟨by omega, by simp only [Nat.add_sub_cancel]; exact he⟩))
        have := NX_le r j
        omega
      refine ⟨tRound r j, (runsTo_roundP hr hj hf).weaken (fun m hm => ⟨⟨j + 1, hm⟩, ?_⟩)⟩
      have := tRound_le hr j
      simp only
      rw [hm.r54, hj.r54]
      have e : n + 2 - (j + 1) = (n + 2 - (j + 1 + 1)) + 1 := by omega
      rw [e, Nat.mul_add, Nat.mul_one]
      omega) M ⟨0, hM⟩
  obtain ⟨t, ht⟩ := hloop
  obtain ⟨mf, ⟨⟨j, hj⟩, h55, hΦ⟩, hrun⟩ := ht.exact
  have ⟨hj0, hjs⟩ := hj.flag.1 h55
  have hstop : Babai.TaggedDigraph.stopIdx (decTagged r) = j - 1 := by
    refine stopIdx_eq_of r (by rw [Nat.sub_add_cancel hj0]; exact hjs) (fun i hi => ?_)
    exact hj.nostop i (by omega)
  refine ⟨t, ?_, hrun.weaken (fun m hm => ?_)⟩
  · have := hM.r54
    simp only at hΦ
    rw [this] at hΦ
    have e : n + 2 - (0 + 1) = n + 1 := by omega
    rw [e] at hΦ
    have e2 : Kr r * (n + 1) = Kr r * (r.1.length + 1) := rfl
    omega
  · rw [hm, hstop, Nat.sub_add_cancel hj0]; exact hj

end TagLin

end Algo
