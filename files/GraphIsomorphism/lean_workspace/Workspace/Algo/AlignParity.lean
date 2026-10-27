/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: Procedure Align (§14.1), line 2 (i) — the parity correction, for the
case `G^ϕ = A(Γ)`.
-/
import Workspace.Algo.AlignPerm
import Workspace.Algo.TopParity

/-!
# §14.1, Procedure Align, line 2 (i): the parity correction

Line 1 of Procedure Align asks whether `X(x)` and `X(y)` are **`G^ϕ`-isomorphic**, and `G^ϕ`
is the symmetric group `S(Γ)` *or* the alternating group `A(Γ)` (`Babai.IsGiantRep`).  The
test `Algo.alignColPartTest` of session 1 and the permutation `Algo.alignColPartPerm` of
`Workspace/Algo/AlignPerm.lean` answer the question for `S(Γ)`.  For `A(Γ)` an odd answer has
to be corrected, and the correction is possible exactly when `Aut(X(x))` contains an odd
permutation.  This is the same phenomenon as the corrected Eq. (70)
(`Babai.Align_G1_image`, `Babai.not_Align_G1_image_as_printed`).

## When does `Aut` of a colored partition contain an odd permutation?

`Aut(X)` is a direct product, over the keys `(color, cell size)`, of the wreath products
`S_s ≀ S_r` (`r` cells of size `s`).  Such a factor contains an odd permutation exactly when
`s ≥ 2` (a transposition inside one cell) or `r ≥ 2` and `s` is odd (the swap of two cells is
a product of `s` transpositions).  Collecting the cases, the answer is as simple as can be:

> `Aut` of a colored partition of `Γ` contains an odd permutation **exactly when two distinct
> points of `Γ` have the same color** (`Algo.exists_odd_colPartAut_iff`).

Indeed, if the coloring is injective then every automorphism fixes every point.  Conversely,
two distinct points of one color either lie in one cell (then their transposition is an
automorphism), or some cell has two points (same), or all cells are singletons (then any
color-preserving permutation is an automorphism).  `Algo.exists_odd_colPartAut_iff_cells`
gives the same condition in the shape "some cell has at least two points, or two distinct
cells have the same key and odd size".

## Main definitions

* `Algo.cpSwapOk` — the test "the transposition of these two points is an automorphism";
* `Algo.cpHasOddAut`, `Algo.cpOddAut` — the decision and the odd automorphism it produces;
* `Algo.alignColPartIso` — **line 2 (i) with the parity correction**: the isomorphism `σ̄` of
  `X(x)` and `X(y)` inside `G^ϕ`, or the report that there is none.

## Main results

* `Algo.exists_odd_colPartAut_iff` — **the exact parity condition**;
* `Algo.cpOddAut_spec` — the computed odd automorphism is one;
* `Algo.alignColPartIso_some`, `Algo.alignColPartIso_eq_none` — **the routine decides
  `Iso_K(X(x), X(y)) ≠ ∅` for `K = S(Γ)` and for `K = A(Γ)`, and returns a witness**;
* `Algo.alignColPartIso_mem_structIso`, `Algo.alignColPartIso_none_structIso` — the same
  against the `S(Γ)`-set the procedure acts on;
* `Algo.Align_line2_colPart` — **Eq. (70)** (`Babai.Align_eq70`, `Babai.Align_G1_image`) for a
  lift of the computed `σ̄`;
* `Algo.polyFun_alignColPartIso` — **the running time**.

No axiom, no `sorry`.
-/

namespace Algo

open RAM RAM.Targets
open Equiv (Perm swap)
open scoped Pointwise

/-! ## Transpositions that are automorphisms -/

/-- The transposition of two points of a colored partition is an automorphism when the two
points are distinct and either lie in one cell or are both alone in their cells. -/
def cpSwapOk (p : RawColPart × (ℕ × ℕ)) : Bool :=
  decide (p.2.1 ≠ p.2.2) &&
    (decide (cellOf p.1 p.2.1 = cellOf p.1 p.2.2) ||
      (decide (labAt p.1.1 p.2.1 = labAt p.1.1 p.2.2) &&
        (decide (cellSize (p.1, p.2.1) = 1) && decide (cellSize (p.1, p.2.2) = 1))))

/-- Two points in one cell: their transposition preserves the cell of every point. -/
theorem colPartIso_swap_of_cell {m : ℕ} {P : RawColPart} {a b : Fin m}
    (h : cellOf P (a : ℕ) = cellOf P (b : ℕ)) : ColPartIso m P P (swap a b) := by
  have hcell : ∀ u : Fin m, cellOf P ((swap a b u : Fin m) : ℕ) = cellOf P (u : ℕ) := by
    intro u
    by_cases hu : u = a
    · subst hu; rw [Equiv.swap_apply_left]; exact h.symm
    · by_cases hv : u = b
      · subst hv; rw [Equiv.swap_apply_right]; exact h
      · rw [Equiv.swap_apply_of_ne_of_ne hu hv]
  exact ⟨fun u => labAt_of_cellOf_eq (hcell u), fun u v => by rw [hcell u, hcell v]⟩

/-- A point alone in its cell is the only point of its cell. -/
theorem eq_of_cellOf_eq_of_cellSize_one {m : ℕ} {P : RawColPart} (hP : P.1.length = m)
    {a u : Fin m} (ha : cellSize (P, (a : ℕ)) = 1)
    (h : cellOf P (u : ℕ) = cellOf P (a : ℕ)) : u = a := by
  have hu : (u : ℕ) ∈ cpCellList P (a : ℕ) :=
    mem_cpCellList.2 ⟨by rw [hP]; exact u.isLt, h⟩
  have haa : (a : ℕ) ∈ cpCellList P (a : ℕ) :=
    mem_cpCellList.2 ⟨by rw [hP]; exact a.isLt, rfl⟩
  rw [cellSize_eq_length] at ha
  obtain ⟨x, hx⟩ := List.length_eq_one_iff.1 ha
  rw [hx, List.mem_singleton] at hu haa
  exact Fin.ext (hu.trans haa.symm)

/-- Two points of one color, each alone in its cell: their transposition is an
automorphism. -/
theorem colPartIso_swap_of_singletons {m : ℕ} {P : RawColPart} (hP : P.1.length = m)
    {a b : Fin m} (hab : a ≠ b) (hcol : labAt P.1 (a : ℕ) = labAt P.1 (b : ℕ))
    (ha : cellSize (P, (a : ℕ)) = 1) (hb : cellSize (P, (b : ℕ)) = 1) :
    ColPartIso m P P (swap a b) := by
  have hsa : ∀ u : Fin m, cellOf P (u : ℕ) = cellOf P (a : ℕ) → u = a :=
    fun u h => eq_of_cellOf_eq_of_cellSize_one hP ha h
  have hsb : ∀ u : Fin m, cellOf P (u : ℕ) = cellOf P (b : ℕ) → u = b :=
    fun u h => eq_of_cellOf_eq_of_cellSize_one hP hb h
  -- a point of `{a, b}` has a cell of its own
  have hkey : ∀ u v : Fin m, (u = a ∨ u = b ∨ v = a ∨ v = b) →
      (cellOf P (u : ℕ) = cellOf P (v : ℕ) ↔ u = v) := by
    intro u v hin
    constructor
    · intro h
      rcases hin with rfl | rfl | rfl | rfl
      · exact (hsa v h.symm).symm
      · exact (hsb v h.symm).symm
      · exact hsa u h
      · exact hsb u h
    · intro h; rw [h]
  refine ⟨fun u => ?_, fun u v => ?_⟩
  · by_cases hu : u = a
    · subst hu; rw [Equiv.swap_apply_left]; exact hcol.symm
    · by_cases hv : u = b
      · subst hv; rw [Equiv.swap_apply_right]; exact hcol
      · rw [Equiv.swap_apply_of_ne_of_ne hu hv]
  · by_cases hin : u = a ∨ u = b ∨ v = a ∨ v = b
    · have hin' : (swap a b u) = a ∨ (swap a b u) = b ∨ (swap a b v) = a ∨
          (swap a b v) = b := by
        rcases hin with rfl | rfl | rfl | rfl
        · exact Or.inr (Or.inl (Equiv.swap_apply_left _ _))
        · exact Or.inl (Equiv.swap_apply_right _ _)
        · exact Or.inr (Or.inr (Or.inr (Equiv.swap_apply_left _ _)))
        · exact Or.inr (Or.inr (Or.inl (Equiv.swap_apply_right _ _)))
      rw [hkey u v hin, hkey _ _ hin']
      exact ⟨fun h => by rw [h], fun h => (swap a b).injective h⟩
    · push_neg at hin
      obtain ⟨h1, h2, h3, h4⟩ := hin
      rw [Equiv.swap_apply_of_ne_of_ne h1 h2, Equiv.swap_apply_of_ne_of_ne h3 h4]

/-- The test `Algo.cpSwapOk` is sound: it only accepts transpositions that are
automorphisms. -/
theorem colPartIso_swap_of_cpSwapOk {m : ℕ} {P : RawColPart} (hP : P.1.length = m)
    {a b : Fin m} (h : cpSwapOk (P, ((a : ℕ), (b : ℕ))) = true) :
    a ≠ b ∧ ColPartIso m P P (swap a b) := by
  simp only [cpSwapOk, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true] at h
  obtain ⟨hne, hcase⟩ := h
  have hab : a ≠ b := fun hh => hne (congrArg Fin.val hh)
  refine ⟨hab, ?_⟩
  rcases hcase with hcell | hsing
  · exact colPartIso_swap_of_cell hcell
  · exact colPartIso_swap_of_singletons hP hab hsing.1 hsing.2.1 hsing.2.2

/-! ## The exact parity condition -/

/-- A cell with two points has a second point next to any given one. -/
theorem exists_mem_cell_ne {m : ℕ} {P : RawColPart} (hP : P.1.length = m) {u : Fin m}
    (h : 2 ≤ cellSize (P, (u : ℕ))) :
    ∃ w : Fin m, w ≠ u ∧ cellOf P (w : ℕ) = cellOf P (u : ℕ) := by
  have hu : (u : ℕ) < P.1.length := by rw [hP]; exact u.isLt
  set j : ℕ := if cpPos P (u : ℕ) = 0 then 1 else 0 with hj
  have hjlt : j < cellSize (P, (u : ℕ)) := by
    rw [hj]; split <;> omega
  have hjne : j ≠ cpPos P (u : ℕ) := by
    rw [hj]; split <;> omega
  obtain ⟨w, hw, hwj⟩ := cpPos_surj hu hjlt
  obtain ⟨hw1, hw2⟩ := mem_cpCellList.1 hw
  refine ⟨⟨w, by rw [← hP]; exact hw1⟩, ?_, hw2⟩
  intro hh
  exact hjne (by rw [← hwj, show w = (u : ℕ) from congrArg Fin.val hh])

/-- If two distinct points have the same color, some transposition passes the test. -/
theorem exists_cpSwapOk {m : ℕ} {P : RawColPart} (hP : P.1.length = m) {u v : Fin m}
    (huv : u ≠ v) (hcol : labAt P.1 (u : ℕ) = labAt P.1 (v : ℕ)) :
    ∃ a b : Fin m, cpSwapOk (P, ((a : ℕ), (b : ℕ))) = true := by
  have hokCell : ∀ a b : Fin m, a ≠ b → cellOf P (a : ℕ) = cellOf P (b : ℕ) →
      cpSwapOk (P, ((a : ℕ), (b : ℕ))) = true := by
    intro a b hab hcell
    simp only [cpSwapOk, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]
    exact ⟨fun hh => hab (Fin.ext hh), Or.inl hcell⟩
  by_cases hcell : cellOf P (u : ℕ) = cellOf P (v : ℕ)
  · exact ⟨u, v, hokCell u v huv hcell⟩
  · by_cases h2u : 2 ≤ cellSize (P, (u : ℕ))
    · obtain ⟨w, hw, hwc⟩ := exists_mem_cell_ne hP h2u
      exact ⟨w, u, hokCell w u hw hwc⟩
    · by_cases h2v : 2 ≤ cellSize (P, (v : ℕ))
      · obtain ⟨w, hw, hwc⟩ := exists_mem_cell_ne hP h2v
        exact ⟨w, v, hokCell w v hw hwc⟩
      · have hu1 : cellSize (P, (u : ℕ)) = 1 := by
          have := cpKey_snd_pos (P := P) (u := (u : ℕ)) (by rw [hP]; exact u.isLt)
          simp only [cpKey] at this
          omega
        have hv1 : cellSize (P, (v : ℕ)) = 1 := by
          have := cpKey_snd_pos (P := P) (u := (v : ℕ)) (by rw [hP]; exact v.isLt)
          simp only [cpKey] at this
          omega
        refine ⟨u, v, ?_⟩
        simp only [cpSwapOk, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]
        exact ⟨fun hh => huv (Fin.ext hh), Or.inr ⟨hcol, hu1, hv1⟩⟩

/-- If the coloring is injective then the only automorphism is the identity. -/
theorem colPartIso_eq_one_of_injective {m : ℕ} {P : RawColPart}
    (hinj : ∀ u v : Fin m, labAt P.1 (u : ℕ) = labAt P.1 (v : ℕ) → u = v)
    {f : Perm (Fin m)} (hf : ColPartIso m P P f) : f = 1 := by
  refine Equiv.ext (fun u => ?_)
  exact hinj (f u) u (hf.1 u)

/-- §14.1, line 2 (i).  **The exact parity condition**: the automorphism group of a colored
partition of `Γ = [0, m)` contains an odd permutation exactly when two distinct points of `Γ`
carry the same color.

(For the equivalent wording in terms of cells see
`Algo.exists_odd_colPartAut_iff_cells`.) -/
theorem exists_odd_colPartAut_iff {m : ℕ} {P : RawColPart} (hP : P.1.length = m) :
    (∃ f : Perm (Fin m), ColPartIso m P P f ∧ Equiv.Perm.sign f = -1) ↔
      ∃ u v : Fin m, u ≠ v ∧ labAt P.1 (u : ℕ) = labAt P.1 (v : ℕ) := by
  constructor
  · rintro ⟨f, hf, hsign⟩
    by_contra hcon
    push_neg at hcon
    have hinj : ∀ u v : Fin m, labAt P.1 (u : ℕ) = labAt P.1 (v : ℕ) → u = v := by
      intro u v h
      by_contra hne
      exact absurd h (hcon u v hne)
    rw [colPartIso_eq_one_of_injective hinj hf] at hsign
    rw [Equiv.Perm.sign_one] at hsign
    exact absurd hsign (by decide)
  · rintro ⟨u, v, huv, hcol⟩
    obtain ⟨a, b, hok⟩ := exists_cpSwapOk hP huv hcol
    obtain ⟨hab, hiso⟩ := colPartIso_swap_of_cpSwapOk hP hok
    exact ⟨swap a b, hiso, Equiv.Perm.sign_swap hab⟩

/-- §14.1, line 2 (i).  **The parity condition in terms of cells**: the automorphism group
contains an odd permutation exactly when some cell has at least two points, or two distinct
cells have the same key and odd size.  (A cell of even size contributes nothing: its swap
with another cell of the same key is a product of evenly many transpositions.) -/
theorem exists_odd_colPartAut_iff_cells {m : ℕ} {P : RawColPart} (hP : P.1.length = m) :
    (∃ f : Perm (Fin m), ColPartIso m P P f ∧ Equiv.Perm.sign f = -1) ↔
      ((∃ u : Fin m, 2 ≤ cellSize (P, (u : ℕ))) ∨
        ∃ u v : Fin m, cellOf P (u : ℕ) ≠ cellOf P (v : ℕ) ∧
          cpKey (P, (u : ℕ)) = cpKey (P, (v : ℕ)) ∧ Odd (cellSize (P, (u : ℕ)))) := by
  rw [exists_odd_colPartAut_iff hP]
  constructor
  · rintro ⟨u, v, huv, hcol⟩
    by_cases h2u : 2 ≤ cellSize (P, (u : ℕ))
    · exact Or.inl ⟨u, h2u⟩
    by_cases h2v : 2 ≤ cellSize (P, (v : ℕ))
    · exact Or.inl ⟨v, h2v⟩
    have hu1 : cellSize (P, (u : ℕ)) = 1 := by
      have := cpKey_snd_pos (P := P) (u := (u : ℕ)) (by rw [hP]; exact u.isLt)
      simp only [cpKey] at this
      omega
    have hv1 : cellSize (P, (v : ℕ)) = 1 := by
      have := cpKey_snd_pos (P := P) (u := (v : ℕ)) (by rw [hP]; exact v.isLt)
      simp only [cpKey] at this
      omega
    refine Or.inr ⟨u, v, ?_, ?_, by rw [hu1]; exact odd_one⟩
    · intro hh
      exact huv (eq_of_cellOf_eq_of_cellSize_one hP hv1 hh)
    · exact Prod.ext hcol (hu1.trans hv1.symm)
  · rintro (⟨u, hu⟩ | ⟨u, v, hne, hkey, -⟩)
    · obtain ⟨w, hw, hwc⟩ := exists_mem_cell_ne hP hu
      exact ⟨w, u, hw, congrArg Prod.fst hwc⟩
    · exact ⟨u, v, fun hh => hne (by rw [hh]), congrArg Prod.fst hkey⟩

/-! ## The routine -/

/-- The transpositions of two points that pass `Algo.cpSwapOk`. -/
def cpSwapList (P : RawColPart) : List (ℕ × ℕ) :=
  (cpPairs (cpDom P)).filter (fun q => cpSwapOk (P, q))

/-- §14.1, line 2 (i).  **The decision whether `Aut(X)` contains an odd permutation.** -/
def cpHasOddAut (P : RawColPart) : Bool := ! (cpSwapList P).isEmpty

/-- §14.1, line 2 (i).  **An odd automorphism of `X`**, when there is one; otherwise the
identity. -/
def cpOddAut (P : RawColPart) : RawPerm :=
  rawTopSwap (cpDom P, (cpSwapList P).getD 0 (0, 0))

theorem getD_zero_mem {α : Type*} {l : List α} (h : l ≠ []) (d : α) : l.getD 0 d ∈ l := by
  cases l with
  | nil => exact absurd rfl h
  | cons a t => simp

theorem cpHasOddAut_eq_true_iff (P : RawColPart) :
    cpHasOddAut P = true ↔ cpSwapList P ≠ [] := by
  rw [cpHasOddAut, Bool.not_eq_true', List.isEmpty_eq_false_iff]

theorem cpHasOddAut_iff {m : ℕ} {P : RawColPart} (hP : P.1.length = m) :
    cpHasOddAut P = true ↔
      ∃ f : Perm (Fin m), ColPartIso m P P f ∧ Equiv.Perm.sign f = -1 := by
  rw [exists_odd_colPartAut_iff hP, cpHasOddAut_eq_true_iff]
  constructor
  · intro hnil
    obtain ⟨q, hq⟩ := List.exists_mem_of_ne_nil _ hnil
    rw [cpSwapList, List.mem_filter] at hq
    obtain ⟨hmem, hok⟩ := hq
    rw [mem_cpPairs, cpDom, hP] at hmem
    have h1 : q.1 < m := List.mem_range.1 hmem.1
    have h2 : q.2 < m := List.mem_range.1 hmem.2
    have hok' : cpSwapOk (P, (((⟨q.1, h1⟩ : Fin m) : ℕ), ((⟨q.2, h2⟩ : Fin m) : ℕ))) = true :=
      hok
    obtain ⟨hab, hiso⟩ := colPartIso_swap_of_cpSwapOk hP hok'
    refine ⟨⟨q.1, h1⟩, ⟨q.2, h2⟩, hab, ?_⟩
    have hc := hiso.1 (⟨q.1, h1⟩ : Fin m)
    rw [Equiv.swap_apply_left] at hc
    exact hc.symm
  · rintro ⟨u, v, huv, hcol⟩
    obtain ⟨a, b, hok⟩ := exists_cpSwapOk hP huv hcol
    have hmem : ((a : ℕ), (b : ℕ)) ∈ cpSwapList P := by
      rw [cpSwapList, List.mem_filter]
      refine ⟨?_, hok⟩
      rw [mem_cpPairs, cpDom, hP]
      exact ⟨List.mem_range.2 a.isLt, List.mem_range.2 b.isLt⟩
    intro hnil
    rw [hnil] at hmem
    exact absurd hmem (by simp)

/-- §14.1, line 2 (i).  **The computed odd automorphism is one.** -/
theorem cpOddAut_spec {m : ℕ} {P : RawColPart} (hP : P.1.length = m)
    (h : cpHasOddAut P = true) :
    RawPerm.WF m (cpOddAut P) ∧ ColPartIso m P P (decPerm m (cpOddAut P)) ∧
      Equiv.Perm.sign (decPerm m (cpOddAut P)) = -1 := by
  have hne : cpSwapList P ≠ [] := (cpHasOddAut_eq_true_iff P).1 h
  set q := (cpSwapList P).getD 0 (0, 0) with hq
  have hmem : q ∈ cpSwapList P := getD_zero_mem hne _
  rw [cpSwapList, List.mem_filter] at hmem
  obtain ⟨hpair, hok⟩ := hmem
  rw [mem_cpPairs, cpDom, hP] at hpair
  have h1 : q.1 < m := List.mem_range.1 hpair.1
  have h2 : q.2 < m := List.mem_range.1 hpair.2
  set a : Fin m := ⟨q.1, h1⟩
  set b : Fin m := ⟨q.2, h2⟩
  have hdom : (cpDom P).length = m := by rw [cpDom, List.length_range, hP]
  have hraw : cpOddAut P = encPerm m (swap a b) := by
    rw [cpOddAut, ← hq]
    have : q = ((a : ℕ), (b : ℕ)) := rfl
    rw [this]
    exact rawTopSwap_spec hdom a b
  obtain ⟨hab, hiso⟩ := colPartIso_swap_of_cpSwapOk (a := a) (b := b) hP hok
  rw [hraw, decPerm_encPerm]
  exact ⟨wf_encPerm m (swap a b), hiso, Equiv.Perm.sign_swap hab⟩

/-! ## Line 2 (i) with the parity correction -/

/-- §14.1, **line 2 (i)**, in the colored-partition case.

The Boolean says which giant `G^ϕ` is: `true` for the alternating group `A(Γ)`, `false` for
the symmetric group `S(Γ)`.  The answer is a `σ̄ ∈ Iso_{G^ϕ}(X(x), X(y))`, or `none` when
there is none — which is the reject exit of line 1. -/
def alignColPartIso (p : Bool × (RawColPart × RawColPart)) : Option RawPerm :=
  if alignColPartTest p.2 then
    (if p.1 = false then some (alignColPartPerm p.2)
      else if topEven (alignColPartPerm p.2) then some (alignColPartPerm p.2)
      else if cpHasOddAut p.2.1 then some (rawMul (alignColPartPerm p.2, cpOddAut p.2.1))
      else none)
  else none

section Spec

variable {m : ℕ} {P Q : RawColPart} {g : Bool} {s : RawPerm}

theorem topEven_of_wf {l : RawPerm} (h : RawPerm.WF m l) :
    topEven l = true ↔ decPerm m l ∈ alternatingGroup (Fin m) := by
  have hh := topEven_encPerm (m := m) (decPerm m l)
  rwa [encPerm_decPerm h] at hh

/-- §14.1, **line 2 (i)**: the answer is a well-formed permutation of `Γ`, it is an
isomorphism of the two colored partitions, and in the alternating case it is even. -/
theorem alignColPartIso_some (hP : P.1.length = m) (hQ : Q.1.length = m)
    (h : alignColPartIso (g, (P, Q)) = some s) :
    RawPerm.WF m s ∧ ColPartIso m P Q (decPerm m s) ∧
      (g = true → Equiv.Perm.sign (decPerm m s) = 1) := by
  simp only [alignColPartIso] at h
  by_cases htest : alignColPartTest (P, Q) = true
  · rw [if_pos htest] at h
    obtain ⟨hwf, -⟩ := alignColPartPerm_check hP hQ htest
    have hstat : (colPartStat P).Perm (colPartStat Q) := (cpStatEq_iff _ _).1 htest
    have hiso := alignColPartPerm_colPartIso hP hQ hstat
    by_cases hg : g = false
    · rw [if_pos hg] at h
      obtain rfl : s = alignColPartPerm (P, Q) := (Option.some.inj h).symm
      exact ⟨hwf, hiso, fun hgt => absurd (hg ▸ hgt) (by simp)⟩
    · rw [if_neg hg] at h
      have hgt : g = true := by cases g <;> simp_all
      by_cases heven : topEven (alignColPartPerm (P, Q)) = true
      · rw [if_pos heven] at h
        obtain rfl : s = alignColPartPerm (P, Q) := (Option.some.inj h).symm
        refine ⟨hwf, hiso, fun _ => ?_⟩
        exact (Equiv.Perm.mem_alternatingGroup).1 ((topEven_of_wf hwf).1 heven)
      · rw [if_neg heven] at h
        by_cases hodd : cpHasOddAut P = true
        · rw [if_pos hodd] at h
          obtain ⟨hwfA, hisoA, hsignA⟩ := cpOddAut_spec hP hodd
          obtain rfl : s = rawMul (alignColPartPerm (P, Q), cpOddAut P) :=
            (Option.some.inj h).symm
          have hwfs : RawPerm.WF m (rawMul (alignColPartPerm (P, Q), cpOddAut P)) :=
            wf_rawMul hwf hwfA
          have hdec : decPerm m (rawMul (alignColPartPerm (P, Q), cpOddAut P)) =
              decPerm m (alignColPartPerm (P, Q)) * decPerm m (cpOddAut P) := by
            rw [rawMul_of_wf hwf hwfA, decPerm_encPerm]
          refine ⟨hwfs, ?_, fun _ => ?_⟩
          · rw [colPartIso_iff_smul] at hiso hisoA ⊢
            rw [hdec, mul_smul, hisoA, hiso]
          · rw [hdec, map_mul, hsignA]
            have hsignS : Equiv.Perm.sign (decPerm m (alignColPartPerm (P, Q))) = -1 := by
              rcases Int.units_eq_one_or (Equiv.Perm.sign
                (decPerm m (alignColPartPerm (P, Q)))) with hh | hh
              · exact absurd ((topEven_of_wf hwf).2
                  ((Equiv.Perm.mem_alternatingGroup).2 hh)) heven
              · exact hh
            rw [hsignS]
            decide
        · rw [if_neg hodd] at h
          exact absurd h (by simp)
  · rw [if_neg htest] at h
    exact absurd h (by simp)

/-- §14.1, **line 1 / line 2 (i)**: when the routine reports `none` there is no isomorphism
at all in the giant `G^ϕ` — every isomorphism of the two colored partitions is odd, and the
giant is the alternating group. -/
theorem alignColPartIso_eq_none (hP : P.1.length = m) (hQ : Q.1.length = m)
    (h : alignColPartIso (g, (P, Q)) = none) (f : Perm (Fin m)) (hf : ColPartIso m P Q f) :
    g = true ∧ Equiv.Perm.sign f = -1 := by
  simp only [alignColPartIso] at h
  have htest : alignColPartTest (P, Q) = true := (alignColPartTest_iff hP hQ).2 ⟨f, hf⟩
  rw [if_pos htest] at h
  have hg : ¬ (g = false) := by
    intro hg; rw [if_pos hg] at h; exact absurd h (by simp)
  have hgt : g = true := by cases g <;> simp_all
  rw [if_neg hg] at h
  have heven : ¬ (topEven (alignColPartPerm (P, Q)) = true) := by
    intro hh; rw [if_pos hh] at h; exact absurd h (by simp)
  rw [if_neg heven] at h
  have hodd : ¬ (cpHasOddAut P = true) := by
    intro hh; rw [if_pos hh] at h; exact absurd h (by simp)
  rw [if_neg hodd] at h
  refine ⟨hgt, ?_⟩
  -- the computed `σ̄` is odd; were `f` even, `f⁻¹ σ̄` would be an odd automorphism of `X(x)`
  have hstat : (colPartStat P).Perm (colPartStat Q) := (cpStatEq_iff _ _).1 htest
  obtain ⟨hwf, -⟩ := alignColPartPerm_check hP hQ htest
  have hiso := alignColPartPerm_colPartIso hP hQ hstat
  have hsignS : Equiv.Perm.sign (decPerm m (alignColPartPerm (P, Q))) = -1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign (decPerm m (alignColPartPerm (P, Q))))
      with hh | hh
    · exact absurd ((topEven_of_wf hwf).2 ((Equiv.Perm.mem_alternatingGroup).2 hh)) heven
    · exact hh
  rcases Int.units_eq_one_or (Equiv.Perm.sign f) with hh | hh
  · exfalso
    refine hodd ((cpHasOddAut_iff hP).2
      ⟨f⁻¹ * decPerm m (alignColPartPerm (P, Q)), ?_, ?_⟩)
    · rw [colPartIso_iff_smul] at hiso hf ⊢
      rw [mul_smul, hiso, ← hf, inv_smul_smul]
    · rw [map_mul, map_inv, hh, hsignS]
      decide
  · exact hh

/-! ### Against the `S(Γ)`-set the procedure acts on -/

/-- §14.1, **line 2 (i)**: the answer is a `σ̄ ∈ Iso_{G^ϕ}(X(x), X(y))`.

`Babai.IsGiantRep ϕ` (`A(Γ) ≤ G^ϕ`) is the standing hypothesis of Sec. 14, and the flag
`true` says that `G^ϕ` is the alternating group, so an even answer lies in `G^ϕ` in either
case. -/
theorem alignColPartIso_mem_structIso {Ω : Type*} {G : Subgroup (Perm Ω)}
    (ϕ : G →* Perm (Fin m)) (hϕ : Babai.IsGiantRep ϕ) (hP : P.1.length = m)
    (hQ : Q.1.length = m) (h : alignColPartIso (true, (P, Q)) = some s) :
    decPerm m s ∈
      Babai.structIso (ϕ.range : Set (Perm (Fin m))) (decColStruct m P) (decColStruct m Q) := by
  obtain ⟨hwf, hiso, hsign⟩ := alignColPartIso_some hP hQ h
  exact ⟨hϕ ((Equiv.Perm.mem_alternatingGroup).2 (hsign rfl)),
    (colPartIso_iff_smul m P Q _).1 hiso⟩

/-- §14.1, **line 2 (i)** for `G^ϕ = S(Γ)`: the answer is an isomorphism, with no condition
on the group. -/
theorem alignColPartIso_false_mem_structIso (hP : P.1.length = m) (hQ : Q.1.length = m)
    (h : alignColPartIso (false, (P, Q)) = some s) (K : Set (Perm (Fin m)))
    (hK : Set.univ ⊆ K) :
    decPerm m s ∈ Babai.structIso K (decColStruct m P) (decColStruct m Q) := by
  obtain ⟨hwf, hiso, -⟩ := alignColPartIso_some hP hQ h
  exact ⟨hK (Set.mem_univ _), (colPartIso_iff_smul m P Q _).1 hiso⟩

/-- §14.1, **line 1**, the reject exit in the alternating case: `Iso_{A(Γ)}(X(x), X(y)) = ∅`.
This is the case the printed Eq. (70) overlooks; see `Babai.Align_G1_image` and
the corrected paper. -/
theorem alignColPartIso_none_structIso (hP : P.1.length = m) (hQ : Q.1.length = m)
    (h : alignColPartIso (true, (P, Q)) = none) :
    Babai.structIso ((alternatingGroup (Fin m) : Subgroup (Perm (Fin m))) :
      Set (Perm (Fin m))) (decColStruct m P) (decColStruct m Q) = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro f ⟨hfA, hf⟩
  obtain ⟨-, hsign⟩ := alignColPartIso_eq_none hP hQ h f ((colPartIso_iff_smul m P Q f).2 hf)
  rw [(Equiv.Perm.mem_alternatingGroup).1 hfA] at hsign
  exact absurd hsign (by decide)

/-- §14.1, **line 1**, the reject exit in the symmetric case: `Iso_{S(Γ)}(X(x), X(y)) = ∅`. -/
theorem alignColPartIso_none_structIso_univ (hP : P.1.length = m) (hQ : Q.1.length = m)
    (h : alignColPartIso (false, (P, Q)) = none) :
    Babai.structIso (Set.univ : Set (Perm (Fin m))) (decColStruct m P)
      (decColStruct m Q) = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro f ⟨-, hf⟩
  obtain ⟨hgt, -⟩ := alignColPartIso_eq_none hP hQ h f ((colPartIso_iff_smul m P Q f).2 hf)
  exact absurd hgt (by simp)

end Spec

/-! ### Eq. (70) for the computed `σ̄`

Line 2 (ii) lifts `σ̄` to a `σ ∈ ϕ⁻¹(σ̄)` (`Algo.actPreimage`), and lines 2 (iii), (iv) then
give Eq. (70).  Stated here for *any* lift of the computed `σ̄`, so that the use of this
file's routine at line 2 is recorded against the mathematics of
`Workspace/Canonical/Align.lean`, not only against `Algo.ColPartIso`. -/

/-- §14.1, **Eq. (70)** for the `σ̄` computed by `Algo.alignColPartIso`: with `y' = y^{σ⁻¹}`
and `G₁ = ϕ⁻¹(Aut(X(x)))`,

* `Iso_G(x,y) = Iso_{G₁}(x,y')σ`  (`Babai.Align_eq70`), and
* `G₁^ϕ = Aut(X(x)) ∩ G^ϕ`  (`Babai.Align_G1_image`, the corrected second clause; the printed
  clause `G₁^ϕ = Aut(X(x))` is false, see `Babai.not_Align_G1_image_as_printed` and
  the corrected paper). -/
theorem Align_line2_colPart {Ω : Type*} {A : Type*} {m : ℕ} {G : Subgroup (Perm Ω)}
    {ϕ : G →* Perm (Fin m)} {X : (Ω → A) → Babai.ColStruct (Fin m) ℕ}
    (hcan : Babai.IsCanonicalStructure ϕ X) (x y : Ω → A) {P Q : RawColPart} {g : Bool}
    {s : RawPerm} (hP : P.1.length = m) (hQ : Q.1.length = m)
    (hXx : X x = decColStruct m P) (hXy : X y = decColStruct m Q)
    (h : alignColPartIso (g, (P, Q)) = some s) (σ : G) (hσ : ϕ σ = decPerm m s) :
    Babai.strIso (G : Set (Perm Ω)) x y =
      (σ : Perm Ω) • Babai.strIso
        ((Babai.preimageSubgroup ϕ (Babai.structAut (X x)) : Subgroup (Perm Ω)) :
          Set (Perm Ω)) x (Babai.strAct y (σ : Perm Ω)⁻¹) ∧
      Babai.homImage ϕ
          ((Babai.preimageSubgroup ϕ (Babai.structAut (X x)) : Subgroup (Perm Ω)) :
            Set (Perm Ω)) =
        (Babai.structAut (Γ := Fin m) (X x) : Set (Perm (Fin m))) ∩
          (ϕ.range : Set (Perm (Fin m))) := by
  obtain ⟨-, hiso, -⟩ := alignColPartIso_some hP hQ h
  have hsmul : ϕ σ • X x = X y := by
    rw [hXx, hXy, hσ]
    exact (colPartIso_iff_smul m P Q _).1 hiso
  exact ⟨Babai.Align_eq70 hcan x y σ hsmul, Babai.Align_G1_image ϕ x⟩

/-! ## The running time -/

theorem polyFun_cpSwapOk : PolyFun cpSwapOk := by
  have ha : PolyFun (fun p : RawColPart × (ℕ × ℕ) => cellOf p.1 p.2.1) :=
    (polyFun_fst.pair (polyFun_snd.comp polyFun_fst)).comp polyFun_cellOfPair
  have hb : PolyFun (fun p : RawColPart × (ℕ × ℕ) => cellOf p.1 p.2.2) :=
    (polyFun_fst.pair (polyFun_snd.comp polyFun_snd)).comp polyFun_cellOfPair
  have hne : PolyFun (fun p : RawColPart × (ℕ × ℕ) => decide (p.2.1 ≠ p.2.2)) :=
    polyFun_snd.comp polyFun_natNe
  have hcell : PolyFun (fun p : RawColPart × (ℕ × ℕ) =>
      decide (cellOf p.1 p.2.1 = cellOf p.1 p.2.2)) := (ha.pair hb).comp polyFun_pairNatEq
  have hcol : PolyFun (fun p : RawColPart × (ℕ × ℕ) =>
      decide (labAt p.1.1 p.2.1 = labAt p.1.1 p.2.2)) := by
    have h1 : PolyFun (fun p : RawColPart × (ℕ × ℕ) => labAt p.1.1 p.2.1) :=
      ((polyFun_fst.comp polyFun_fst).pair (polyFun_snd.comp polyFun_fst)).comp
        polyFun_labAtPair
    have h2 : PolyFun (fun p : RawColPart × (ℕ × ℕ) => labAt p.1.1 p.2.2) :=
      ((polyFun_fst.comp polyFun_fst).pair (polyFun_snd.comp polyFun_snd)).comp
        polyFun_labAtPair
    exact (h1.pair h2).comp polyFun_natEq
  have hs1 : PolyFun (fun p : RawColPart × (ℕ × ℕ) => decide (cellSize (p.1, p.2.1) = 1)) :=
    (((polyFun_fst.pair (polyFun_snd.comp polyFun_fst)).comp polyFun_cellSize).pair
      (polyFun_const 1)).comp polyFun_natEq
  have hs2 : PolyFun (fun p : RawColPart × (ℕ × ℕ) => decide (cellSize (p.1, p.2.2) = 1)) :=
    (((polyFun_fst.pair (polyFun_snd.comp polyFun_snd)).comp polyFun_cellSize).pair
      (polyFun_const 1)).comp polyFun_natEq
  have hor : PolyFun (fun p : RawColPart × (ℕ × ℕ) =>
      (decide (cellOf p.1 p.2.1 = cellOf p.1 p.2.2) ||
        (decide (labAt p.1.1 p.2.1 = labAt p.1.1 p.2.2) &&
          (decide (cellSize (p.1, p.2.1) = 1) && decide (cellSize (p.1, p.2.2) = 1))))) := by
    refine (PolyFun.ite hcell (polyFun_const true)
      (polyFun_and hcol (polyFun_and hs1 hs2))).of_eq (fun p => ?_)
    cases hh : decide (cellOf p.1 p.2.1 = cellOf p.1 p.2.2) <;> simp [hh]
  exact polyFun_and hne hor

theorem polyFun_cpSwapList : PolyFun cpSwapList :=
  ((polyFun_id.pair (polyFun_cpDom.comp polyFun_cpPairs)).comp
    (PolyFun.filterParam polyFun_cpSwapOk)).of_eq (fun _ => rfl)

theorem polyFun_cpHasOddAut : PolyFun cpHasOddAut := by
  refine (PolyFun.ite (polyFun_cpSwapList.comp polyFun_isEmpty) (polyFun_const false)
    (polyFun_const true)).of_eq (fun P => ?_)
  rw [cpHasOddAut]
  cases hh : (cpSwapList P).isEmpty <;> simp [hh]

theorem polyFun_cpOddAut : PolyFun cpOddAut := by
  have h : PolyFun (fun P : RawColPart => (cpSwapList P).getD 0 (0, 0)) :=
    ((polyFun_cpSwapList.pair (polyFun_const 0)).pair (polyFun_const (0, 0))).comp polyFun_getD
  exact (polyFun_cpDom.pair h).comp polyFun_rawTopSwap

/-- §14.1, line 2 (i) with the parity correction **runs in polynomial time**. -/
theorem polyFun_alignColPartIso : PolyFun alignColPartIso := by
  have hperm : PolyFun (fun p : Bool × (RawColPart × RawColPart) => alignColPartPerm p.2) :=
    polyFun_snd.comp polyFun_alignColPartPerm
  have hP : PolyFun (fun p : Bool × (RawColPart × RawColPart) => p.2.1) :=
    polyFun_snd.comp polyFun_fst
  have htest : PolyFun (fun p : Bool × (RawColPart × RawColPart) => alignColPartTest p.2) :=
    polyFun_snd.comp polyFun_alignColPartTest
  have hflag : PolyFun (fun p : Bool × (RawColPart × RawColPart) => decide (p.1 = false)) := by
    refine (PolyFun.ite polyFun_fst (polyFun_const false) (polyFun_const true)).of_eq
      (fun p => ?_)
    cases hh : p.1 <;> simp [hh]
  have heven : PolyFun (fun p : Bool × (RawColPart × RawColPart) =>
      topEven (alignColPartPerm p.2)) := hperm.comp polyFun_topEven
  have hodd : PolyFun (fun p : Bool × (RawColPart × RawColPart) => cpHasOddAut p.2.1) :=
    hP.comp polyFun_cpHasOddAut
  have hmul : PolyFun (fun p : Bool × (RawColPart × RawColPart) =>
      rawMul (alignColPartPerm p.2, cpOddAut p.2.1)) :=
    (hperm.pair (hP.comp polyFun_cpOddAut)).comp polyFun_rawMul
  refine (PolyFun.ite htest
    (PolyFun.ite hflag (hperm.comp polyFun_some)
      (PolyFun.ite heven (hperm.comp polyFun_some)
        (PolyFun.ite hodd (hmul.comp polyFun_some) polyFun_none)))
    polyFun_none).of_eq (fun p => ?_)
  rw [alignColPartIso]
  by_cases h1 : alignColPartTest p.2 = true
  · simp only [h1, if_true]
    by_cases h2 : p.1 = false
    · simp [h2]
    · simp only [h2, decide_false, Bool.false_eq_true, if_false]
      by_cases h3 : topEven (alignColPartPerm p.2) = true
      · simp [h3]
      · simp only [h3, Bool.false_eq_true, if_false]
        by_cases h4 : cpHasOddAut p.2.1 = true <;> simp [h4]
  · simp [h1]

end Algo
