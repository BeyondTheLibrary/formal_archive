/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

§5.4.2: the trivial bound `O(k²n^{2k+1})` for `k`-ary WL refinement.  How a raw `k`-ary
coloring lies in memory, and the facts about the iterates the fast program uses.
-/
import Workspace.Algo.WLFastSort

/-!
# The input layout of the fast `k`-WL program

A raw coloring `p = (dom, table)` with `|dom| = n`, `N` rows and tuples of length `k` is encoded
as

  `2n, 1, d₀, …, 1, d_{n-1}, N(2k+4), row₀, …, row_{N-1}`,

each row `(t, c)` taking the `2k + 4` cells `2k+3, 2k, 1, t₀, …, 1, t_{k-1}, 1, c`
(`Algo.WLFast.blk_rawWL_iff`).  So the entry `i` of the tuple of row `r` and the color of row
`r` are at fixed offsets, and a table with the same tuples and new colors is obtained by
rewriting the color cells only (`Algo.WLFast.blk_rawWL_recolor`).

No axiom, no `sorry`.
-/

namespace Algo

namespace WLFast

open RAM RAM.Exact
open ExplLinear (length_encode_nat_list)

/-! ## Lists of blocks of one width -/

theorem blk_encList_uniform {α : Type*} {f : α → List ℕ} {w : ℕ} {m : Mem} :
    ∀ (l : List α) (p : ℕ), (∀ a ∈ l, (f a).length + 1 = w) →
      (Blk m p (encList f l) ↔ ∀ r (hr : r < l.length), Blk m (p + r * w) (frame (f l[r])))
  | [], p, _ => by simp [encList, Blk.nil]
  | a :: l, p, hw => by
      have ha := hw a (by simp)
      have ih := blk_encList_uniform (m := m) l (p + w) (fun b hb => hw b (by simp [hb]))
      have hfl : (frame (f a)).length = w := by simp [RAM.frame, ha]
      rw [encList, Blk.append, hfl, ih]
      constructor
      · rintro ⟨h0, hs⟩ r hr
        rcases r with _ | r
        · simpa using h0
        · have := hs r (by simpa using hr)
          rw [show p + (r + 1) * w = p + w + r * w by ring]
          simpa using this
      · intro h
        refine ⟨by simpa using h 0 (by simp), fun r hr => ?_⟩
        have := h (r + 1) (by simpa using hr)
        rw [show p + (r + 1) * w = p + w + r * w by ring] at this
        simpa using this

theorem length_encList_uniform {α : Type*} {f : α → List ℕ} {w : ℕ} :
    ∀ (l : List α), (∀ a ∈ l, (f a).length + 1 = w) → (encList f l).length = l.length * w
  | [], _ => by simp [encList]
  | a :: l, hw => by
      rw [encList, List.length_append, length_encList_uniform l (fun b hb => hw b (by simp [hb]))]
      simp only [RAM.frame, List.length_cons, hw a (by simp)]
      ring

/-- An encoded list of numbers: `1, x₀, 1, x₁, …`. -/
theorem blk_natList_iff {m : Mem} {p : ℕ} {t : List ℕ} :
    Blk m p (Enc.encode t) ↔ ∀ i (hi : i < t.length), m (p + i * 2) = 1 ∧ m (p + i * 2 + 1) = t[i] := by
  change Blk m p (encList Enc.encode t) ↔ _
  rw [blk_encList_uniform (f := (Enc.encode : ℕ → List ℕ)) (w := 2) t p (fun a _ => rfl)]
  refine forall_congr' fun i => forall_congr' fun hi => ?_
  change Blk m (p + i * 2) [1, t[i]] ↔ _
  simp [Blk.cons, Blk.nil]

/-! ## Rows -/

/-- The cells of the row `(t, c)` from address `b` on. -/
def RowAt (m : Mem) (b : ℕ) (q : List ℕ × ℕ) : Prop :=
  m b = 2 * q.1.length + 3 ∧ m (b + 1) = 2 * q.1.length ∧
    (∀ i (hi : i < q.1.length), m (b + 2 + i * 2) = 1 ∧ m (b + 2 + i * 2 + 1) = q.1[i]) ∧
    m (b + 2 + 2 * q.1.length) = 1 ∧ m (b + 3 + 2 * q.1.length) = q.2

theorem length_encode_row (q : List ℕ × ℕ) : (frame (Enc.encode q)).length = 2 * q.1.length + 4 := by
  change (frame (frame (Enc.encode q.1) ++ frame (Enc.encode q.2))).length = _
  simp only [RAM.frame, List.length_cons, List.length_append, length_encode_nat_list]
  change 2 * q.1.length + 1 + ([q.2].length + 1) + 1 = _
  simp

theorem blk_row_iff {m : Mem} {b : ℕ} {q : List ℕ × ℕ} :
    Blk m b (frame (Enc.encode q)) ↔ RowAt m b q := by
  change Blk m b (frame (frame (Enc.encode q.1) ++ frame (Enc.encode q.2))) ↔ _
  rw [Blk.frame_iff, Blk.append, Blk.frame_iff, Blk.frame_iff, blk_natList_iff]
  simp only [RAM.frame, List.length_append, List.length_cons, length_encode_nat_list]
  change _ ↔ _ ∧ _ ∧ _ ∧ _ ∧ m (b + 3 + 2 * q.1.length) = q.2
  have e1 : (Enc.encode q.2).length = 1 := rfl
  have e2 : Blk m (b + 1 + (2 * q.1.length + 1) + 1) (Enc.encode q.2) ↔
      m (b + 3 + 2 * q.1.length) = q.2 := by
    rw [Blk.encode_nat, show b + 1 + (2 * q.1.length + 1) + 1 = b + 3 + 2 * q.1.length by ring]
  rw [e1, e2, show b + 1 + (2 * q.1.length + 1) = b + 2 + 2 * q.1.length by ring]
  constructor
  · rintro ⟨h0, ⟨h1, h2⟩, h3, h4⟩
    refine ⟨by omega, h1, fun i hi => ?_, h3, h4⟩
    have := h2 i hi
    rw [show b + 1 + 1 + i * 2 = b + 2 + i * 2 by ring] at this
    exact this
  · rintro ⟨h0, h1, h2, h3, h4⟩
    refine ⟨by omega, ⟨h1, fun i hi => ?_⟩, h3, h4⟩
    rw [show b + 1 + 1 + i * 2 = b + 2 + i * 2 by ring]
    exact h2 i hi

/-! ## A raw coloring -/

/-- **The layout of a raw coloring whose tuples have length `k`.** -/
theorem blk_rawWL_iff {m : Mem} {F k : ℕ} {p : RawWL} (hk : ∀ q ∈ p.2, q.1.length = k) :
    Blk m F (Enc.encode p) ↔
      m F = 2 * p.1.length ∧ Blk m (F + 1) (Enc.encode p.1) ∧
        m (F + 2 * p.1.length + 1) = p.2.length * (2 * k + 4) ∧
        ∀ r (hr : r < p.2.length), RowAt m (F + 2 * p.1.length + 2 + r * (2 * k + 4)) p.2[r] := by
  have hw : ∀ q ∈ p.2, (frame (Enc.encode q)).length = 2 * k + 4 := fun q hq => by
    rw [length_encode_row, hk q hq]
  have hl : (Enc.encode p.2).length = p.2.length * (2 * k + 4) :=
    length_encList_uniform p.2 (fun q hq => by rw [← hw q hq]; rfl)
  rw [Blk.encode_pair, length_encode_nat_list, hl]
  change _ ∧ _ ∧ _ ∧ Blk m (F + 1 + 2 * p.1.length + 1) (encList Enc.encode p.2) ↔ _
  rw [blk_encList_uniform (w := 2 * k + 4) p.2 _ (fun q hq => by rw [← hw q hq]; rfl)]
  simp only [blk_row_iff]
  rw [show F + 1 + 2 * p.1.length = F + 2 * p.1.length + 1 by ring,
    show F + 2 * p.1.length + 1 + 1 = F + 2 * p.1.length + 2 by ring]

theorem mul_add_inj {w r r' a b : ℕ} (ha : a < w) (hb : b < w) (h : r * w + a = r' * w + b) :
    r = r' ∧ a = b := by
  have hw : 0 < w := by omega
  have e1 : (r * w + a) / w = r := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hw, Nat.div_eq_of_lt ha, zero_add]
  have e2 : (r' * w + b) / w = r' := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hw, Nat.div_eq_of_lt hb, zero_add]
  have hr : r = r' := by rw [← e1, ← e2, h]
  subst hr
  exact ⟨rfl, by omega⟩

theorem length_encode_rawWL {k : ℕ} {p : RawWL} (hk : ∀ q ∈ p.2, q.1.length = k) :
    (Enc.encode p).length = 2 * p.1.length + 2 + p.2.length * (2 * k + 4) := by
  have hw : ∀ q ∈ p.2, (frame (Enc.encode q)).length = 2 * k + 4 := fun q hq => by
    rw [length_encode_row, hk q hq]
  have hl : (Enc.encode p.2).length = p.2.length * (2 * k + 4) :=
    length_encList_uniform p.2 (fun q hq => by rw [← hw q hq]; rfl)
  change (frame (Enc.encode p.1) ++ frame (Enc.encode p.2)).length = _
  simp only [RAM.frame, List.length_append, List.length_cons, length_encode_nat_list, hl]
  ring

theorem lt_mul_of_lt' {r N w j : ℕ} (hr : r < N) (hj : j < w) : r * w + j < N * w := by
  have : (r + 1) * w ≤ N * w := Nat.mul_le_mul_right _ hr
  rw [Nat.add_mul, one_mul] at this; omega

/-- The color cell of row `r`. -/
def colCell (F n k r : ℕ) : ℕ := F + 2 * n + 2 + r * (2 * k + 4) + (2 * k + 3)

/-- **Recoloring in place.**  A table with the same tuples and new colors is encoded by the
old encoding with the color cells rewritten. -/
theorem blk_rawWL_recolor {m m' : Mem} {F k : ℕ} {p p' : RawWL}
    (hk : ∀ q ∈ p.2, q.1.length = k) (h : Blk m F (Enc.encode p)) (h1 : p'.1 = p.1)
    (hlen : p'.2.length = p.2.length)
    (hkey : ∀ r (hr : r < p.2.length), p'.2[r].1 = p.2[r].1)
    (hcol : ∀ r (hr : r < p.2.length), m' (colCell F p.1.length k r) = p'.2[r].2)
    (hsame : ∀ z, F ≤ z → z < F + (Enc.encode p).length →
      (∀ r, r < p.2.length → z ≠ colCell F p.1.length k r) → m' z = m z) :
    Blk m' F (Enc.encode p') := by
  have hk' : ∀ q ∈ p'.2, q.1.length = k := by
    intro q hq
    obtain ⟨r, hr, rfl⟩ := List.getElem_of_mem hq
    rw [hkey r (by omega)]; exact hk _ (List.getElem_mem _)
  have htot : (Enc.encode p).length = 2 * p.1.length + 2 + p.2.length * (2 * k + 4) := by
    have hw : ∀ q ∈ p.2, (frame (Enc.encode q)).length = 2 * k + 4 := fun q hq => by
      rw [length_encode_row, hk q hq]
    have hl : (Enc.encode p.2).length = p.2.length * (2 * k + 4) :=
      length_encList_uniform p.2 (fun q hq => by rw [← hw q hq]; rfl)
    change (frame (Enc.encode p.1) ++ frame (Enc.encode p.2)).length = _
    simp only [RAM.frame, List.length_append, List.length_cons, length_encode_nat_list, hl]
    ring
  obtain ⟨e0, e1, e2, e3⟩ := (blk_rawWL_iff hk).1 h
  -- cells below the rows are not color cells
  have hlow : ∀ z, F ≤ z → z < F + 2 * p.1.length + 2 → m' z = m z := fun z hz1 hz2 =>
    hsame z hz1 (by rw [htot]; omega) (fun r _ => by unfold colCell; omega)
  rw [blk_rawWL_iff hk', h1]
  refine ⟨by rw [hlow F le_rfl (by omega), e0], e1.congr (fun z hz1 hz2 => ?_),
    by rw [hlow _ (by omega) (by omega), e2, hlen], fun r hr' => ?_⟩
  · rw [length_encode_nat_list] at hz2; exact hlow z (by omega) (by omega)
  · have hr : r < p.2.length := hlen ▸ hr'
    obtain ⟨f0, f1, f2, f3, f4⟩ := e3 r hr
    have hkr := hk _ (List.getElem_mem hr)
    have hq : p'.2[r] = (p.2[r].1, p'.2[r].2) := Prod.ext (hkey r hr) rfl
    rw [hq]
    have hc := hcol r hr
    rw [hq] at hc
    unfold colCell at hc
    unfold RowAt
    dsimp only
    generalize hb : F + 2 * p.1.length + 2 + r * (2 * k + 4) = b at f0 f1 f2 f3 f4 hc ⊢
    have hrk : (r + 1) * (2 * k + 4) ≤ p.2.length * (2 * k + 4) :=
      Nat.mul_le_mul_right _ (by omega)
    -- a cell of row `r` other than its color cell is kept
    have hin : ∀ a, a < 2 * k + 3 → m' (b + a) = m (b + a) := by
      intro a ha
      refine hsame _ (by omega) (by rw [htot]; nlinarith) (fun r' _ he => ?_)
      unfold colCell at he
      have := mul_add_inj (w := 2 * k + 4) (r := r) (r' := r') (a := a) (b := 2 * k + 3)
        (by omega) (by omega) (by omega)
      omega
    refine ⟨?_, ?_, fun i hi => ?_, ?_, ?_⟩
    · rw [show b = b + 0 by rfl, hin 0 (by omega)]; exact f0
    · rw [hin 1 (by omega)]; exact f1
    · have hi' : i < k := by rw [← hkr]; exact hi
      rw [show b + 2 + i * 2 = b + (2 + i * 2) by ring,
        show b + (2 + i * 2) + 1 = b + (3 + i * 2) by ring,
        hin _ (by omega), hin _ (by omega),
        show b + (2 + i * 2) = b + 2 + i * 2 by ring, show b + (3 + i * 2) = b + 2 + i * 2 + 1 by ring]
      exact f2 i hi
    · rw [hkr, show b + 2 + 2 * k = b + (2 + 2 * k) by ring, hin _ (by omega),
        ← show b + 2 + 2 * k = b + (2 + 2 * k) by ring, ← hkr]; exact f3
    · rw [hkr, show b + 3 + 2 * k = b + (2 * k + 3) by ring]
      exact hc

/-! ## Facts about well-formed colorings and their iterates -/

section Facts

variable {n k : ℕ} {p : RawWL}

theorem dom_perm (h : RawWL.WF n k p) : p.1.Perm (List.range n) :=
  (List.perm_ext_iff_of_nodup h.domNodup List.nodup_range).2 (fun a => by
    rw [h.domMem, List.mem_range])

theorem length_dom (h : RawWL.WF n k p) : p.1.length = n := by
  rw [(dom_perm h).length_eq, List.length_range]

theorem key_length (h : RawWL.WF n k p) {r : ℕ} (hr : r < p.2.length) : p.2[r].1.length = k :=
  ((h.keyMem _).1 (List.mem_map_of_mem (List.getElem_mem hr))).1

theorem key_lt (h : RawWL.WF n k p) {r : ℕ} (hr : r < p.2.length) {d : ℕ} (hd : d ∈ p.2[r].1) :
    d < n :=
  ((h.keyMem _).1 (List.mem_map_of_mem (List.getElem_mem hr))).2 d hd

theorem key_getElem_lt (h : RawWL.WF n k p) {r : ℕ} (hr : r < p.2.length) {i : ℕ}
    (hi : i < p.2[r].1.length) : p.2[r].1[i] < n :=
  key_lt h hr (List.getElem_mem hi)

theorem iter_fst (p : RawWL) : ∀ j, (rawWLStep^[j] p).1 = p.1
  | 0 => rfl
  | j + 1 => by rw [Function.iterate_succ_apply', rawWLStep_fst, iter_fst p j]

theorem iter_keys (p : RawWL) : ∀ j, (rawWLStep^[j] p).2.map Prod.fst = p.2.map Prod.fst
  | 0 => rfl
  | j + 1 => by rw [Function.iterate_succ_apply', rawWLStep_keys, iter_keys p j]

theorem iter_length (p : RawWL) (j : ℕ) : (rawWLStep^[j] p).2.length = p.2.length := by
  have := congrArg List.length (iter_keys p j)
  simpa using this

theorem iter_key (p : RawWL) (j : ℕ) {r : ℕ} (hr : r < p.2.length) :
    ((rawWLStep^[j] p).2[r]'(by rw [iter_length]; exact hr)).1 = p.2[r].1 := by
  have := congrArg (fun l => l[r]?) (iter_keys p j)
  simp only [List.getElem?_map] at this
  rw [List.getElem?_eq_getElem hr, List.getElem?_eq_getElem (by rw [iter_length]; exact hr)] at this
  simpa using this

/-- Once fixed, always fixed. -/
theorem iter_fixed {q : RawWL} (hq : rawWLStep q = q) : ∀ j, rawWLStep^[j] q = q
  | 0 => rfl
  | j + 1 => by rw [Function.iterate_succ_apply, hq, iter_fixed hq j]

/-- A round changes nothing exactly when every new color is the old one. -/
theorem step_eq_iff {q : RawWL} : rawWLStep q = q ↔
    ∀ r (hr : r < q.2.length), wlNewCol q q.2[r].1 = q.2[r].2 := by
  constructor
  · intro he r hr
    have := congrArg (fun p : RawWL => (p.2[r]?).map Prod.snd) he
    simp only [rawWLStep, List.getElem?_map, List.getElem?_eq_getElem hr, Option.map_some] at this
    exact Option.some.inj this
  · intro hc
    refine Prod.ext rfl (List.ext_getElem (by simp [rawWLStep]) (fun r h1 h2 => ?_))
    simp only [rawWLStep, List.getElem_map]
    exact Prod.ext rfl (hc r h2)

end Facts

end WLFast

end Algo
