/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: Procedure Align (§14.1), line 2 (iv) — generators of `Aut(X(x))`
for a colored partition `X(x)`, on the unit-cost RAM.
-/
import Workspace.Algo.AlignParity

/-!
# §14.1, Procedure Align, line 2 (iv): generators of `Aut(X(x))`

> 2. Else, let
>    ...
>    (iv) `G₁ = ϕ⁻¹(Aut(X(x)))`

Line 2 (iv) needs **generators** of `Aut(X(x))`, not the set.  This file computes them in
the colored-partition case.

## The group and the generators

`Aut` of a colored partition of `Γ = [0, m)` is the direct product, over the keys
`k = (color, cell size)`, of the wreath products `S_s ≀ S_r` (`r` cells of size `s`): an
automorphism carries cells to cells of the same key, and inside a cell it is arbitrary.  Two
families of permutations generate it:

* the transpositions of two points of one cell (`Algo.colPartIso_swap_of_cell`);
* for two distinct cells of one key, the **cell swap**: the permutation that exchanges the
  two cells position by position and fixes every other point (`Algo.cpCellSwap`).

A single transposition of two points of *different* cells is **not** an automorphism in
general (take `Γ = [0,4)` of one color with the cells `{0,1}` and `{2,3}`: `(0 2)(1 3)` is an
automorphism, `(0 2)` is not), which is why the second family is a product of `s`
transpositions and not a transposition.  This is also why the induction of
`Algo.giant_stabilizer_le` (`Workspace/Algo/TopStab.lean`) does not apply.

## The generation proof

`Algo.cpAut_mem_of_gens` is the mathematical heart, stated for an arbitrary subgroup `H`
that contains the two families.  It is two inductions:

1. an automorphism that fixes every cell setwise is a product of transpositions inside cells
   (`Algo.cpAut_mem_of_fixes_cells`): peel off `swap a (f a)`, whose two points lie in one
   cell, and the support drops (`Equiv.Perm.card_support_swap_mul`);
2. a general automorphism `f` induces a permutation of the cells; multiplying by the cell
   swap of the cell of `u` with the cell of `f u` strictly shrinks the set of points whose
   cell `f` does not preserve, and step 1 is the base case.

## Main definitions

* `Algo.cpAtPos` — the point of a cell at a given position;
* `Algo.cpCellSwap` — the swap of two cells of one key, position by position;
* `Algo.cpAutGen`, `Algo.cpAutGens` — **the generators of `Aut(X)`**, one per ordered pair of
  points of `Γ`.

## Main results

* `Algo.cpAut_mem_of_gens` — the abstract generation statement;
* `Algo.decGroup_cpAutGens` — **`Algo.cpAutGens` generates `Aut(X)`**:
  `decGroup m (cpAutGens P) = Babai.structAut (decColStruct m P)`;
* `Algo.cpAutGens_wf`, `Algo.length_cpAutGens` — well formed, and at most `m²` generators;
* `Algo.polyFun_cpAutGens` — **the running time**.

No axiom, no `sorry`.
-/

namespace Algo

open RAM RAM.Targets
open Equiv (Perm swap)

/-! ## Reading a map over the domain -/

theorem labAt_map_cpDom {P : RawColPart} (f : ℕ → ℕ) {w : ℕ} (hw : w < P.1.length) :
    labAt ((cpDom P).map f) w = f w := by
  have hlen : ((cpDom P).map f).length = P.1.length := by
    rw [List.length_map, cpDom, List.length_range]
  rw [labAt, List.getD_eq_getElem _ _ (by rw [hlen]; exact hw)]
  show ((cpDom P).map f)[w]'(by rw [hlen]; exact hw) = _
  simp [cpDom]

/-! ## The point of a cell at a given position -/

/-- The point of the cell of `v` at position `j`.  (Junk when the cell has no such
position.) -/
def cpAtPos (p : RawColPart × ℕ × ℕ) : ℕ :=
  labAt ((cpCellList p.1 p.2.1).filter (fun w => decide (cpPos p.1 w = p.2.2))) 0

theorem cpAtPos_congr {P : RawColPart} {a b j : ℕ} (h : cellOf P a = cellOf P b) :
    cpAtPos (P, a, j) = cpAtPos (P, b, j) := by
  show labAt ((cpCellList P a).filter _) 0 = labAt ((cpCellList P b).filter _) 0
  rw [cpCellList_congr h]

/-- The point of a cell at a position below the size of the cell exists, and has that
position. -/
theorem cpAtPos_spec {P : RawColPart} {v : ℕ} (hv : v < P.1.length) {j : ℕ}
    (hj : j < cellSize (P, v)) :
    cpAtPos (P, v, j) ∈ cpCellList P v ∧ cpPos P (cpAtPos (P, v, j)) = j := by
  obtain ⟨w, hw, hwj⟩ := cpPos_surj hv hj
  have hwS : w ∈ (cpCellList P v).filter (fun z => decide (cpPos P z = j)) :=
    List.mem_filter.2 ⟨hw, by simp [hwj]⟩
  have hne : (cpCellList P v).filter (fun z => decide (cpPos P z = j)) ≠ [] := by
    intro hh
    rw [hh] at hwS
    exact absurd hwS (by simp)
  have hmem : cpAtPos (P, v, j) ∈ (cpCellList P v).filter (fun z => decide (cpPos P z = j)) :=
    labAt_zero_mem hne
  obtain ⟨h1, h2⟩ := List.mem_filter.1 hmem
  exact ⟨h1, by simpa using h2⟩

/-- Reading the position of a point of a cell and then the point at that position gives the
point back. -/
theorem cpAtPos_self {P : RawColPart} {v w : ℕ} (hw : w ∈ cpCellList P v) :
    cpAtPos (P, v, cpPos P w) = w := by
  obtain ⟨hw1, hw2⟩ := mem_cpCellList.1 hw
  rw [← cpAtPos_congr (j := cpPos P w) hw2]
  obtain ⟨hm, hp⟩ := cpAtPos_spec (P := P) (v := w) hw1 (cpPos_lt_cellSize hw1)
  obtain ⟨hz1, hz2⟩ := mem_cpCellList.1 hm
  exact cpPos_inj hz1 hw1 hz2 hp

/-! ## The swap of two cells

The cell of `u` and the cell of `v` are exchanged position by position; every other point is
fixed. -/

/-- One value of the cell swap. -/
def cpCellSwapAt (z : (RawColPart × ℕ × ℕ) × ℕ) : ℕ :=
  if cellOf z.1.1 z.2 = cellOf z.1.1 z.1.2.1 then
    cpAtPos (z.1.1, z.1.2.2, cpPos z.1.1 z.2)
  else if cellOf z.1.1 z.2 = cellOf z.1.1 z.1.2.2 then
    cpAtPos (z.1.1, z.1.2.1, cpPos z.1.1 z.2)
  else z.2

/-- §14.1, line 2 (iv).  **The swap of the cell of `u` with the cell of `v`**, position by
position.  This is a product of `|cell|` transpositions, and — unlike any one of them — it is
an automorphism of the colored partition. -/
def cpCellSwap (p : RawColPart × ℕ × ℕ) : RawPerm := (cpDom p.1).map (fun w => cpCellSwapAt (p, w))

section CellSwap

variable {P : RawColPart} {u v : ℕ}

theorem cpCellSwapAt_left (hvm : v < P.1.length) (hkey : cpKey (P, u) = cpKey (P, v))
    {w : ℕ} (hwm : w < P.1.length) (hw : cellOf P w = cellOf P u) :
    cpCellSwapAt ((P, u, v), w) ∈ cpCellList P v ∧
      cpPos P (cpCellSwapAt ((P, u, v), w)) = cpPos P w := by
  have hsz : cpPos P w < cellSize (P, v) := by
    have h1 : cpPos P w < cellSize (P, w) := cpPos_lt_cellSize hwm
    have h2 : cellSize (P, w) = cellSize (P, u) := cellSize_congr hw
    have h3 : cellSize (P, u) = cellSize (P, v) := congrArg Prod.snd hkey
    omega
  have heq : cpCellSwapAt ((P, u, v), w) = cpAtPos (P, v, cpPos P w) := by
    show (if cellOf P w = cellOf P u then cpAtPos (P, v, cpPos P w) else _) = _
    rw [if_pos hw]
  rw [heq]
  exact cpAtPos_spec hvm hsz

theorem cpCellSwapAt_right (hum : u < P.1.length) (hne : cellOf P u ≠ cellOf P v)
    (hkey : cpKey (P, u) = cpKey (P, v)) {w : ℕ} (hwm : w < P.1.length)
    (hw : cellOf P w = cellOf P v) :
    cpCellSwapAt ((P, u, v), w) ∈ cpCellList P u ∧
      cpPos P (cpCellSwapAt ((P, u, v), w)) = cpPos P w := by
  have hnl : ¬ (cellOf P w = cellOf P u) := fun hh => hne (hh.symm.trans hw)
  have hsz : cpPos P w < cellSize (P, u) := by
    have h1 : cpPos P w < cellSize (P, w) := cpPos_lt_cellSize hwm
    have h2 : cellSize (P, w) = cellSize (P, v) := cellSize_congr hw
    have h3 : cellSize (P, u) = cellSize (P, v) := congrArg Prod.snd hkey
    omega
  have heq : cpCellSwapAt ((P, u, v), w) = cpAtPos (P, u, cpPos P w) := by
    show (if cellOf P w = cellOf P u then _
      else if cellOf P w = cellOf P v then cpAtPos (P, u, cpPos P w) else _) = _
    rw [if_neg hnl, if_pos hw]
  rw [heq]
  exact cpAtPos_spec hum hsz

theorem cpCellSwapAt_other {w : ℕ} (h1 : cellOf P w ≠ cellOf P u)
    (h2 : cellOf P w ≠ cellOf P v) : cpCellSwapAt ((P, u, v), w) = w := by
  show (if cellOf P w = cellOf P u then _
    else if cellOf P w = cellOf P v then _ else w) = w
  rw [if_neg h1, if_neg h2]

/-- The cell swap sends a point below the degree to a point below the degree. -/
theorem cpCellSwapAt_lt (hum : u < P.1.length) (hvm : v < P.1.length)
    (hne : cellOf P u ≠ cellOf P v) (hkey : cpKey (P, u) = cpKey (P, v)) {w : ℕ}
    (hwm : w < P.1.length) : cpCellSwapAt ((P, u, v), w) < P.1.length := by
  by_cases h1 : cellOf P w = cellOf P u
  · exact (mem_cpCellList.1 (cpCellSwapAt_left hvm hkey hwm h1).1).1
  · by_cases h2 : cellOf P w = cellOf P v
    · exact (mem_cpCellList.1 (cpCellSwapAt_right hum hne hkey hwm h2).1).1
    · rw [cpCellSwapAt_other h1 h2]; exact hwm

/-- The cell of the image, as a function of the cell of the point: the transposition of the
two cells. -/
theorem cellOf_cpCellSwapAt (hum : u < P.1.length) (hvm : v < P.1.length)
    (hne : cellOf P u ≠ cellOf P v) (hkey : cpKey (P, u) = cpKey (P, v)) {w : ℕ}
    (hwm : w < P.1.length) :
    cellOf P (cpCellSwapAt ((P, u, v), w)) =
      (if cellOf P w = cellOf P u then cellOf P v
        else if cellOf P w = cellOf P v then cellOf P u else cellOf P w) := by
  by_cases h1 : cellOf P w = cellOf P u
  · rw [if_pos h1]
    exact (mem_cpCellList.1 (cpCellSwapAt_left hvm hkey hwm h1).1).2
  · rw [if_neg h1]
    by_cases h2 : cellOf P w = cellOf P v
    · rw [if_pos h2]
      exact (mem_cpCellList.1 (cpCellSwapAt_right hum hne hkey hwm h2).1).2
    · rw [if_neg h2, cpCellSwapAt_other h1 h2]

/-- **The cell swap is an involution.** -/
theorem cpCellSwapAt_involutive (hum : u < P.1.length) (hvm : v < P.1.length)
    (hne : cellOf P u ≠ cellOf P v) (hkey : cpKey (P, u) = cpKey (P, v)) {w : ℕ}
    (hwm : w < P.1.length) :
    cpCellSwapAt ((P, u, v), cpCellSwapAt ((P, u, v), w)) = w := by
  by_cases h1 : cellOf P w = cellOf P u
  · obtain ⟨hz, hp⟩ := cpCellSwapAt_left hvm hkey hwm h1
    obtain ⟨hz1, hz2⟩ := mem_cpCellList.1 hz
    obtain ⟨hz', hp'⟩ := cpCellSwapAt_right hum hne hkey hz1 hz2
    have : cpCellSwapAt ((P, u, v), cpCellSwapAt ((P, u, v), w)) =
        cpAtPos (P, u, cpPos P w) := by
      have heq : cpCellSwapAt ((P, u, v), cpCellSwapAt ((P, u, v), w)) =
          cpAtPos (P, u, cpPos P (cpCellSwapAt ((P, u, v), w))) := by
        have hnl : ¬ (cellOf P (cpCellSwapAt ((P, u, v), w)) = cellOf P u) :=
          fun hh => hne (hh.symm.trans hz2)
        show (if cellOf P (cpCellSwapAt ((P, u, v), w)) = cellOf P u then _
          else if cellOf P (cpCellSwapAt ((P, u, v), w)) = cellOf P v then
            cpAtPos (P, u, cpPos P (cpCellSwapAt ((P, u, v), w))) else _) = _
        rw [if_neg hnl, if_pos hz2]
      rw [heq, hp]
    rw [this]
    exact cpAtPos_self (mem_cpCellList.2 ⟨hwm, h1⟩)
  · by_cases h2 : cellOf P w = cellOf P v
    · obtain ⟨hz, hp⟩ := cpCellSwapAt_right hum hne hkey hwm h2
      obtain ⟨hz1, hz2⟩ := mem_cpCellList.1 hz
      have heq : cpCellSwapAt ((P, u, v), cpCellSwapAt ((P, u, v), w)) =
          cpAtPos (P, v, cpPos P (cpCellSwapAt ((P, u, v), w))) := by
        show (if cellOf P (cpCellSwapAt ((P, u, v), w)) = cellOf P u then
          cpAtPos (P, v, cpPos P (cpCellSwapAt ((P, u, v), w))) else _) = _
        rw [if_pos hz2]
      rw [heq, hp]
      exact cpAtPos_self (mem_cpCellList.2 ⟨hwm, h2⟩)
    · rw [cpCellSwapAt_other h1 h2, cpCellSwapAt_other h1 h2]

end CellSwap

/-! ## The cell swap as a permutation of `Γ` -/

section CellSwapPerm

variable {m : ℕ} {P : RawColPart} {u v : ℕ}

theorem labAt_cpCellSwap {w : ℕ} (hw : w < P.1.length) :
    labAt (cpCellSwap (P, u, v)) w = cpCellSwapAt ((P, u, v), w) :=
  labAt_map_cpDom _ hw

theorem cpCellSwap_wf (hP : P.1.length = m) (hum : u < m) (hvm : v < m)
    (hne : cellOf P u ≠ cellOf P v) (hkey : cpKey (P, u) = cpKey (P, v)) :
    RawPerm.WF m (cpCellSwap (P, u, v)) := by
  have hum' : u < P.1.length := by rw [hP]; exact hum
  have hvm' : v < P.1.length := by rw [hP]; exact hvm
  have hdom : cpDom P = List.range m := by rw [cpDom, hP]
  refine ⟨?_, ?_, ?_⟩
  · rw [cpCellSwap, List.length_map, hdom, List.length_range]
  · intro a ha
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 ha
    rw [hdom, List.mem_range] at hw
    rw [← hP]
    exact cpCellSwapAt_lt hum' hvm' hne hkey (by rw [hP]; exact hw)
  · rw [cpCellSwap]
    show ((cpDom P).map (fun w => cpCellSwapAt ((P, u, v), w))).Nodup
    rw [hdom]
    refine List.Nodup.map_on ?_ List.nodup_range
    intro a ha b hb hab
    rw [List.mem_range] at ha hb
    have ha' : a < P.1.length := by rw [hP]; exact ha
    have hb' : b < P.1.length := by rw [hP]; exact hb
    have h1 := cpCellSwapAt_involutive hum' hvm' hne hkey ha'
    have h2 := cpCellSwapAt_involutive hum' hvm' hne hkey hb'
    rw [← h1, ← h2]
    exact congrArg (fun z => cpCellSwapAt ((P, u, v), z)) hab

theorem cpCellSwap_apply (hP : P.1.length = m) (hum : u < m) (hvm : v < m)
    (hne : cellOf P u ≠ cellOf P v) (hkey : cpKey (P, u) = cpKey (P, v)) (w : Fin m) :
    ((decPerm m (cpCellSwap (P, u, v)) w : Fin m) : ℕ) = cpCellSwapAt ((P, u, v), (w : ℕ)) := by
  rw [← labAt_eq_decPerm (cpCellSwap_wf hP hum hvm hne hkey) w.isLt,
    labAt_cpCellSwap (by rw [hP]; exact w.isLt)]

/-- **The cell swap is an automorphism of the colored partition.** -/
theorem colPartIso_cpCellSwap (hP : P.1.length = m) (hum : u < m) (hvm : v < m)
    (hne : cellOf P u ≠ cellOf P v) (hkey : cpKey (P, u) = cpKey (P, v)) :
    ColPartIso m P P (decPerm m (cpCellSwap (P, u, v))) := by
  have hum' : u < P.1.length := by rw [hP]; exact hum
  have hvm' : v < P.1.length := by rw [hP]; exact hvm
  have hap := cpCellSwap_apply hP hum hvm hne hkey
  have hcell : ∀ w : Fin m,
      cellOf P ((decPerm m (cpCellSwap (P, u, v)) w : Fin m) : ℕ) =
        (if cellOf P (w : ℕ) = cellOf P u then cellOf P v
          else if cellOf P (w : ℕ) = cellOf P v then cellOf P u else cellOf P (w : ℕ)) := by
    intro w
    rw [hap w]
    exact cellOf_cpCellSwapAt hum' hvm' hne hkey (by rw [hP]; exact w.isLt)
  have hinj : ∀ a b : ℕ × ℕ,
      (if a = cellOf P u then cellOf P v else if a = cellOf P v then cellOf P u else a) =
        (if b = cellOf P u then cellOf P v else if b = cellOf P v then cellOf P u else b) ↔
      a = b := by
    intro a b
    by_cases ha1 : a = cellOf P u <;> by_cases ha2 : a = cellOf P v <;>
      by_cases hb1 : b = cellOf P u <;> by_cases hb2 : b = cellOf P v <;>
      simp_all [eq_comm]
  refine ⟨fun w => ?_, fun w w' => ?_⟩
  · have h := hcell w
    have hcolor : (cellOf P u).1 = (cellOf P v).1 := by
      have := congrArg Prod.fst hkey
      exact this
    rw [← cellOf_fst, ← cellOf_fst, h]
    by_cases h1 : cellOf P (w : ℕ) = cellOf P u
    · rw [if_pos h1, ← hcolor, ← h1]
    · rw [if_neg h1]
      by_cases h2 : cellOf P (w : ℕ) = cellOf P v
      · rw [if_pos h2, hcolor, ← h2]
      · rw [if_neg h2]
  · rw [hcell w, hcell w']
    exact (hinj _ _).symm

end CellSwapPerm

/-! ## The abstract generation statement -/

section Generation

variable {m : ℕ} {P : RawColPart}

/-- The transposition of two points of one cell preserves the cell of every point. -/
theorem cellOf_swap_of_cell {a b : Fin m} (h : cellOf P (a : ℕ) = cellOf P (b : ℕ))
    (w : Fin m) : cellOf P ((swap a b w : Fin m) : ℕ) = cellOf P (w : ℕ) := by
  by_cases hw : w = a
  · subst hw; rw [Equiv.swap_apply_left]; exact h.symm
  · by_cases hv : w = b
    · subst hv; rw [Equiv.swap_apply_right]; exact h
    · rw [Equiv.swap_apply_of_ne_of_ne hw hv]

theorem colPartIso_mul {f g : Perm (Fin m)} (hf : ColPartIso m P P f)
    (hg : ColPartIso m P P g) : ColPartIso m P P (f * g) := by
  rw [colPartIso_iff_smul] at hf hg ⊢
  rw [mul_smul, hg, hf]

theorem colPartIso_inv {f : Perm (Fin m)} (hf : ColPartIso m P P f) :
    ColPartIso m P P f⁻¹ := by
  rw [colPartIso_iff_smul] at hf ⊢
  rw [inv_smul_eq_iff]
  exact hf.symm

/-- **Step 1**: an automorphism that fixes every cell setwise is a product of transpositions
inside cells. -/
theorem cpAut_mem_of_fixes_cells (H : Subgroup (Perm (Fin m)))
    (hswap : ∀ a b : Fin m, a ≠ b → cellOf P (a : ℕ) = cellOf P (b : ℕ) → swap a b ∈ H)
    {f : Perm (Fin m)} (hfix : ∀ w : Fin m,
      cellOf P ((f w : Fin m) : ℕ) = cellOf P (w : ℕ)) : f ∈ H := by
  suffices hmain : ∀ k (g : Perm (Fin m)), g.support.card = k →
      (∀ w : Fin m, cellOf P ((g w : Fin m) : ℕ) = cellOf P (w : ℕ)) → g ∈ H by
    exact hmain _ f rfl hfix
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro g hcard hgfix
    by_cases hg1 : g = 1
    · subst hg1; exact H.one_mem
    obtain ⟨a, ha⟩ : ∃ a : Fin m, g a ≠ a := by
      by_contra hh
      exact hg1 (Equiv.ext (fun a => not_not.1 (fun h => hh ⟨a, h⟩)))
    have hcellga : cellOf P ((a : ℕ)) = cellOf P ((g a : Fin m) : ℕ) := (hgfix a).symm
    have hsmall : (swap a (g a) * g).support.card < k := by
      rw [← hcard]
      exact Equiv.Perm.card_support_swap_mul ha
    have hfix' : ∀ w : Fin m,
        cellOf P (((swap a (g a) * g) w : Fin m) : ℕ) = cellOf P (w : ℕ) := by
      intro w
      show cellOf P ((swap a (g a) (g w) : Fin m) : ℕ) = _
      rw [cellOf_swap_of_cell hcellga (g w), hgfix w]
    have hmem := ih _ hsmall (swap a (g a) * g) rfl hfix'
    have := H.mul_mem (hswap a (g a) (Ne.symm ha) hcellga) hmem
    simpa [← mul_assoc] using this

/-- §14.1, line 2 (iv).  **The generation statement**: a subgroup of `S(Γ)` that contains the
transpositions inside the cells and one cell swap for each pair of distinct cells of one key
contains the whole automorphism group of the colored partition. -/
theorem cpAut_mem_of_gens (hP : P.1.length = m) (H : Subgroup (Perm (Fin m)))
    (hswap : ∀ a b : Fin m, a ≠ b → cellOf P (a : ℕ) = cellOf P (b : ℕ) → swap a b ∈ H)
    (hcell : ∀ a b : Fin m, cellOf P (a : ℕ) ≠ cellOf P (b : ℕ) →
      cpKey (P, (a : ℕ)) = cpKey (P, (b : ℕ)) →
      ∃ g ∈ H, ColPartIso m P P g ∧
        (∀ w : Fin m, cellOf P (w : ℕ) = cellOf P (a : ℕ) →
          cellOf P ((g w : Fin m) : ℕ) = cellOf P (b : ℕ)) ∧
        (∀ w : Fin m, cellOf P (w : ℕ) = cellOf P (b : ℕ) →
          cellOf P ((g w : Fin m) : ℕ) = cellOf P (a : ℕ)) ∧
        (∀ w : Fin m, cellOf P (w : ℕ) ≠ cellOf P (a : ℕ) →
          cellOf P (w : ℕ) ≠ cellOf P (b : ℕ) → g w = w))
    {f : Perm (Fin m)} (hf : ColPartIso m P P f) : f ∈ H := by
  classical
  set T : Perm (Fin m) → Finset (Fin m) := fun g =>
    Finset.univ.filter (fun w => cellOf P ((g w : Fin m) : ℕ) ≠ cellOf P (w : ℕ)) with hT
  suffices hmain : ∀ k (g : Perm (Fin m)), (T g).card = k → ColPartIso m P P g → g ∈ H by
    exact hmain _ f rfl hf
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro g hcard hg
    by_cases hempty : T g = ∅
    · refine cpAut_mem_of_fixes_cells H hswap (fun w => ?_)
      by_contra hh
      have : w ∈ T g := by rw [hT]; simp [hh]
      rw [hempty] at this
      exact absurd this (by simp)
    obtain ⟨a, haT⟩ := Finset.nonempty_iff_ne_empty.2 hempty
    have ha : cellOf P ((g a : Fin m) : ℕ) ≠ cellOf P ((a : ℕ)) := by
      have := Finset.mem_filter.1 haT
      exact this.2
    -- the key of a point is preserved
    have hkeyg : ∀ w : Fin m, cpKey (P, ((g w : Fin m) : ℕ)) = cpKey (P, (w : ℕ)) := by
      intro w
      have h := cpKey_cpAct hP hP hg w.isLt
      rwa [cpAct_of_lt g w.isLt, show (⟨(w : ℕ), w.isLt⟩ : Fin m) = w from rfl] at h
    obtain ⟨c, hcH, hciso, hc1, hc2, hc3⟩ :=
      hcell a (g a) (Ne.symm ha) ((hkeyg a).symm)
    have hg' : ColPartIso m P P (c * g) := colPartIso_mul hciso hg
    -- the cells that `c * g` does not preserve
    have hsub : T (c * g) ⊆ T g := by
      intro w hw
      by_contra hnot
      have hfix : cellOf P ((g w : Fin m) : ℕ) = cellOf P (w : ℕ) := by
        by_contra hh
        exact hnot (by rw [hT]; simp [hh])
      have hwa : cellOf P (w : ℕ) ≠ cellOf P (a : ℕ) := by
        intro hh
        have := (hg.2 w a).1 hh
        rw [hfix] at this
        exact ha (this.symm.trans hh)
      have hwb : cellOf P (w : ℕ) ≠ cellOf P ((g a : Fin m) : ℕ) := by
        intro hh
        have : cellOf P ((g w : Fin m) : ℕ) = cellOf P ((g a : Fin m) : ℕ) := by
          rw [hfix, hh]
        exact hwa ((hg.2 w a).2 this)
      have hcw : c (g w) = g w := hc3 (g w) (by rw [hfix]; exact hwa) (by rw [hfix]; exact hwb)
      have : cellOf P (((c * g) w : Fin m) : ℕ) = cellOf P (w : ℕ) := by
        show cellOf P ((c (g w) : Fin m) : ℕ) = _
        rw [hcw, hfix]
      have hw' := (Finset.mem_filter.1 hw).2
      exact hw' this
    have hnota : a ∉ T (c * g) := by
      rw [hT]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not]
      show cellOf P ((c (g a) : Fin m) : ℕ) = _
      exact hc2 (g a) rfl
    have hlt : (T (c * g)).card < k := by
      rw [← hcard]
      refine Finset.card_lt_card ⟨hsub, fun hh => hnota (hh haT)⟩
    have hmem := ih _ hlt (c * g) rfl hg'
    have := H.mul_mem (H.inv_mem hcH) hmem
    simpa [← mul_assoc] using this

end Generation

/-! ## The generators on raw data -/

/-- §14.1, line 2 (iv).  **One generator of `Aut(X)` per ordered pair of points**: the
transposition of the two points when they lie in one cell, the swap of their two cells when
they have the same key, and the identity otherwise. -/
def cpAutGen (p : RawColPart × ℕ × ℕ) : RawPerm :=
  if cellOf p.1 p.2.1 = cellOf p.1 p.2.2 then rawTopSwap (cpDom p.1, (p.2.1, p.2.2))
  else if cpKey (p.1, p.2.1) = cpKey (p.1, p.2.2) then cpCellSwap p
  else rawOne (cpDom p.1)

/-- §14.1, line 2 (iv).  **Generators of `Aut(X)`** for a colored partition `X`. -/
def cpAutGens (P : RawColPart) : RawGens :=
  (cpPairs (cpDom P)).map (fun q => cpAutGen (P, q.1, q.2))

section Spec

variable {m : ℕ} {P : RawColPart}

theorem mem_cpAutGens {u v : ℕ} (hu : u < P.1.length) (hv : v < P.1.length) :
    cpAutGen (P, u, v) ∈ cpAutGens P := by
  refine List.mem_map.2 ⟨(u, v), ?_, rfl⟩
  rw [mem_cpPairs]
  exact ⟨by rw [cpDom]; exact List.mem_range.2 hu, by rw [cpDom]; exact List.mem_range.2 hv⟩

/-- Each generator is an automorphism of the colored partition. -/
theorem colPartIso_cpAutGen (hP : P.1.length = m) {u v : ℕ} (hu : u < m) (hv : v < m) :
    RawPerm.WF m (cpAutGen (P, u, v)) ∧ ColPartIso m P P (decPerm m (cpAutGen (P, u, v))) := by
  have hdom : (cpDom P).length = m := by rw [cpDom, List.length_range, hP]
  by_cases h1 : cellOf P u = cellOf P v
  · have heq : cpAutGen (P, u, v) = encPerm m (swap (⟨u, hu⟩ : Fin m) ⟨v, hv⟩) := by
      show (if cellOf P u = cellOf P v then rawTopSwap (cpDom P, (u, v)) else _) = _
      rw [if_pos h1]
      exact rawTopSwap_spec hdom ⟨u, hu⟩ ⟨v, hv⟩
    rw [heq, decPerm_encPerm]
    exact ⟨wf_encPerm _ _, colPartIso_swap_of_cell h1⟩
  · by_cases h2 : cpKey (P, u) = cpKey (P, v)
    · have heq : cpAutGen (P, u, v) = cpCellSwap (P, u, v) := by
        show (if cellOf P u = cellOf P v then _
          else if cpKey (P, u) = cpKey (P, v) then cpCellSwap (P, u, v) else _) = _
        rw [if_neg h1, if_pos h2]
      rw [heq]
      exact ⟨cpCellSwap_wf hP hu hv h1 h2, colPartIso_cpCellSwap hP hu hv h1 h2⟩
    · have heq : cpAutGen (P, u, v) = encPerm m 1 := by
        show (if cellOf P u = cellOf P v then _
          else if cpKey (P, u) = cpKey (P, v) then _ else rawOne (cpDom P)) = _
        rw [if_neg h1, if_neg h2, rawOne_eq, hdom]
      rw [heq, decPerm_encPerm]
      refine ⟨wf_encPerm _ _, ⟨fun w => rfl, fun w w' => Iff.rfl⟩⟩

theorem cpAutGens_wf (hP : P.1.length = m) : RawGens.WF m (cpAutGens P) := by
  intro r hr
  obtain ⟨⟨u, v⟩, hq, rfl⟩ := List.mem_map.1 hr
  have hq' := mem_cpPairs.1 hq
  have hu : u < m := by rw [← hP]; exact List.mem_range.1 hq'.1
  have hv : v < m := by rw [← hP]; exact List.mem_range.1 hq'.2
  exact (colPartIso_cpAutGen hP hu hv).1

/-- At most `m²` generators. -/
theorem length_cpAutGens (hP : P.1.length = m) : (cpAutGens P).length = m * m := by
  rw [cpAutGens, List.length_map, cpPairs, List.length_flatMap]
  have hdom : cpDom P = List.range m := by rw [cpDom, hP]
  rw [hdom]
  simp

/-- §14.1, line 2 (iv).  **The computed list generates `Aut(X)`.** -/
theorem decGroup_cpAutGens (hP : P.1.length = m) :
    decGroup m (cpAutGens P) = Babai.structAut (decColStruct m P) := by
  have hmemgen : ∀ u v : ℕ, u < m → v < m →
      decPerm m (cpAutGen (P, u, v)) ∈ decGroup m (cpAutGens P) := by
    intro u v hu hv
    exact Subgroup.subset_closure (List.mem_map.2 ⟨cpAutGen (P, u, v),
      mem_cpAutGens (by rw [hP]; exact hu) (by rw [hP]; exact hv), rfl⟩)
  apply le_antisymm
  · refine (Subgroup.closure_le _).2 ?_
    rintro s hs
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hs
    obtain ⟨⟨u, v⟩, hq, rfl⟩ := List.mem_map.1 hr
    have hq' := mem_cpPairs.1 hq
    have hu : u < m := by rw [← hP]; exact List.mem_range.1 hq'.1
    have hv : v < m := by rw [← hP]; exact List.mem_range.1 hq'.2
    exact (colPartIso_iff_smul m P P _).1 (colPartIso_cpAutGen hP hu hv).2
  · intro f hf
    refine cpAut_mem_of_gens hP _ ?_ ?_ ((colPartIso_iff_smul m P P f).2 hf)
    · intro a b hab hcell
      have hdom : (cpDom P).length = m := by rw [cpDom, List.length_range, hP]
      have heq : cpAutGen (P, (a : ℕ), (b : ℕ)) = encPerm m (swap a b) := by
        show (if cellOf P (a : ℕ) = cellOf P (b : ℕ) then
          rawTopSwap (cpDom P, ((a : ℕ), (b : ℕ))) else _) = _
        rw [if_pos hcell]
        exact rawTopSwap_spec hdom a b
      have := hmemgen (a : ℕ) (b : ℕ) a.isLt b.isLt
      rwa [heq, decPerm_encPerm] at this
    · intro a b hcell hkey
      have heq : cpAutGen (P, (a : ℕ), (b : ℕ)) = cpCellSwap (P, (a : ℕ), (b : ℕ)) := by
        show (if cellOf P (a : ℕ) = cellOf P (b : ℕ) then _
          else if cpKey (P, (a : ℕ)) = cpKey (P, (b : ℕ)) then
            cpCellSwap (P, (a : ℕ), (b : ℕ)) else _) = _
        rw [if_neg hcell, if_pos hkey]
      have hmem := hmemgen (a : ℕ) (b : ℕ) a.isLt b.isLt
      rw [heq] at hmem
      have ham : (a : ℕ) < P.1.length := by rw [hP]; exact a.isLt
      have hbm : (b : ℕ) < P.1.length := by rw [hP]; exact b.isLt
      refine ⟨_, hmem, colPartIso_cpCellSwap hP a.isLt b.isLt hcell hkey, ?_, ?_, ?_⟩
      · intro w hw
        rw [cpCellSwap_apply hP a.isLt b.isLt hcell hkey w]
        exact (mem_cpCellList.1 (cpCellSwapAt_left hbm hkey
          (by rw [hP]; exact w.isLt) hw).1).2
      · intro w hw
        rw [cpCellSwap_apply hP a.isLt b.isLt hcell hkey w]
        exact (mem_cpCellList.1 (cpCellSwapAt_right ham hcell hkey
          (by rw [hP]; exact w.isLt) hw).1).2
      · intro w h1 h2
        apply Fin.ext
        rw [cpCellSwap_apply hP a.isLt b.isLt hcell hkey w]
        exact cpCellSwapAt_other h1 h2

/-- §14.1, line 2 (iv), in the words of `Algo.ColPartIso`. -/
theorem mem_decGroup_cpAutGens_iff (hP : P.1.length = m) (f : Perm (Fin m)) :
    f ∈ decGroup m (cpAutGens P) ↔ ColPartIso m P P f := by
  rw [decGroup_cpAutGens hP]
  exact (colPartIso_iff_smul m P P f).symm

end Spec

/-! ## The running time -/

theorem polyFun_cpAtPos : PolyFun cpAtPos := by
  have hcl : PolyFun (fun p : RawColPart × ℕ × ℕ => cpCellList p.1 p.2.1) :=
    (polyFun_fst.pair (polyFun_snd.comp polyFun_fst)).comp polyFun_cpCellList
  have hpos : PolyFun (fun z : (RawColPart × ℕ × ℕ) × ℕ => cpPos z.1.1 z.2) :=
    ((polyFun_fst.comp polyFun_fst).pair polyFun_snd).comp polyFun_cpPos
  have hj : PolyFun (fun z : (RawColPart × ℕ × ℕ) × ℕ => z.1.2.2) :=
    (polyFun_fst.comp polyFun_snd).comp polyFun_snd
  have hq : PolyFun (fun z : (RawColPart × ℕ × ℕ) × ℕ => decide (cpPos z.1.1 z.2 = z.1.2.2)) :=
    (hpos.pair hj).comp polyFun_natEq
  exact (((polyFun_id.pair hcl).comp (PolyFun.filterParam hq)).pair
    (polyFun_const 0)).comp polyFun_labAtPair

theorem polyFun_cpCellSwapAt : PolyFun cpCellSwapAt := by
  have hP : PolyFun (fun z : (RawColPart × ℕ × ℕ) × ℕ => z.1.1) :=
    polyFun_fst.comp polyFun_fst
  have hu : PolyFun (fun z : (RawColPart × ℕ × ℕ) × ℕ => z.1.2.1) :=
    (polyFun_fst.comp polyFun_snd).comp polyFun_fst
  have hv : PolyFun (fun z : (RawColPart × ℕ × ℕ) × ℕ => z.1.2.2) :=
    (polyFun_fst.comp polyFun_snd).comp polyFun_snd
  have hw : PolyFun (fun z : (RawColPart × ℕ × ℕ) × ℕ => z.2) := polyFun_snd
  have hcw : PolyFun (fun z : (RawColPart × ℕ × ℕ) × ℕ => cellOf z.1.1 z.2) :=
    (hP.pair hw).comp polyFun_cellOfPair
  have hcu : PolyFun (fun z : (RawColPart × ℕ × ℕ) × ℕ => cellOf z.1.1 z.1.2.1) :=
    (hP.pair hu).comp polyFun_cellOfPair
  have hcv : PolyFun (fun z : (RawColPart × ℕ × ℕ) × ℕ => cellOf z.1.1 z.1.2.2) :=
    (hP.pair hv).comp polyFun_cellOfPair
  have hpos : PolyFun (fun z : (RawColPart × ℕ × ℕ) × ℕ => cpPos z.1.1 z.2) :=
    (hP.pair hw).comp polyFun_cpPos
  have hav : PolyFun (fun z : (RawColPart × ℕ × ℕ) × ℕ =>
      cpAtPos (z.1.1, z.1.2.2, cpPos z.1.1 z.2)) :=
    (hP.pair (hv.pair hpos)).comp polyFun_cpAtPos
  have hau : PolyFun (fun z : (RawColPart × ℕ × ℕ) × ℕ =>
      cpAtPos (z.1.1, z.1.2.1, cpPos z.1.1 z.2)) :=
    (hP.pair (hu.pair hpos)).comp polyFun_cpAtPos
  refine (PolyFun.ite ((hcw.pair hcu).comp polyFun_pairNatEq) hav
    (PolyFun.ite ((hcw.pair hcv).comp polyFun_pairNatEq) hau hw)).of_eq (fun z => ?_)
  rw [cpCellSwapAt]
  by_cases h1 : cellOf z.1.1 z.2 = cellOf z.1.1 z.1.2.1
  · simp [h1]
  · by_cases h2 : cellOf z.1.1 z.2 = cellOf z.1.1 z.1.2.2 <;> simp [h1, h2]

theorem polyFun_cpCellSwap : PolyFun cpCellSwap :=
  ((polyFun_id.pair (polyFun_fst.comp polyFun_cpDom)).comp
    (PolyFun.mapParam polyFun_cpCellSwapAt)).of_eq (fun _ => rfl)

theorem polyFun_cpAutGen : PolyFun cpAutGen := by
  have hP : PolyFun (fun p : RawColPart × ℕ × ℕ => p.1) := polyFun_fst
  have hu : PolyFun (fun p : RawColPart × ℕ × ℕ => p.2.1) := polyFun_snd.comp polyFun_fst
  have hv : PolyFun (fun p : RawColPart × ℕ × ℕ => p.2.2) := polyFun_snd.comp polyFun_snd
  have hcu : PolyFun (fun p : RawColPart × ℕ × ℕ => cellOf p.1 p.2.1) :=
    (hP.pair hu).comp polyFun_cellOfPair
  have hcv : PolyFun (fun p : RawColPart × ℕ × ℕ => cellOf p.1 p.2.2) :=
    (hP.pair hv).comp polyFun_cellOfPair
  have hku : PolyFun (fun p : RawColPart × ℕ × ℕ => cpKey (p.1, p.2.1)) :=
    (hP.pair hu).comp polyFun_cpKey
  have hkv : PolyFun (fun p : RawColPart × ℕ × ℕ => cpKey (p.1, p.2.2)) :=
    (hP.pair hv).comp polyFun_cpKey
  have hswap : PolyFun (fun p : RawColPart × ℕ × ℕ =>
      rawTopSwap (cpDom p.1, (p.2.1, p.2.2))) :=
    ((hP.comp polyFun_cpDom).pair (hu.pair hv)).comp polyFun_rawTopSwap
  have hone : PolyFun (fun p : RawColPart × ℕ × ℕ => rawOne (cpDom p.1)) :=
    (hP.comp polyFun_cpDom).comp polyFun_rawOne
  refine (PolyFun.ite ((hcu.pair hcv).comp polyFun_pairNatEq) hswap
    (PolyFun.ite ((hku.pair hkv).comp polyFun_pairNatEq) polyFun_cpCellSwap hone)).of_eq
    (fun p => ?_)
  rw [cpAutGen]
  by_cases h1 : cellOf p.1 p.2.1 = cellOf p.1 p.2.2
  · simp [h1]
  · by_cases h2 : cpKey (p.1, p.2.1) = cpKey (p.1, p.2.2) <;> simp [h1, h2]

/-- §14.1, line 2 (iv): the generators of `Aut(X)` **are computed in polynomial time**. -/
theorem polyFun_cpAutGens : PolyFun cpAutGens := by
  have h : PolyFun (fun z : RawColPart × (ℕ × ℕ) => cpAutGen (z.1, z.2.1, z.2.2)) :=
    (polyFun_fst.pair ((polyFun_snd.comp polyFun_fst).pair
      (polyFun_snd.comp polyFun_snd))).comp polyFun_cpAutGen
  exact ((polyFun_id.pair (polyFun_cpDom.comp polyFun_cpPairs)).comp
    (PolyFun.mapParam h)).of_eq (fun _ => rfl)

end Algo
