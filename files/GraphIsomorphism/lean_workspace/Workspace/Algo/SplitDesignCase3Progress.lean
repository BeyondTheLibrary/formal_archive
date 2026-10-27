import Workspace.Algo.SplitDesignHintValidity

/-! Section 9.7 makes progress by shrinking the second part or by adding
a coherent hint. The complement shrinks because the first set is large.
When the first set is selected, its returned structure supplies the hint. -/
namespace Algo
open Babai RAM

section
variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {s : Set Ω}
    {X : BlkDesignObj s} {name₁ : ↥X.Pt₁ → ℕ} {name₂ : ↥X.blocks → ℕ}
    {r : RawUpccCase} (h : DesignNames X name₁ name₂ r) (hw : r.WF)
    (e₁ : ↥X.Pt₁ ≃ Fin r.2.1.length) (he₁ : ∀ x, r.2.1[(e₁ x).val] = name₁ x)
    (e₂ : ↥X.blocks ≃ Fin r.2.2.length) (he₂ : ∀ B, r.2.2[(e₂ B).val] = name₂ B)

include h hw he₁ he₂ in
open scoped Classical in
theorem designReadSelected_progress (o : RawDesignReadOut)
    (hnd : (designReadFirst o).Nodup) (hL : ∀ i ∈ designReadFirst o, i < r.2.2.length)
    (hquarter : r.2.2.length ≤ 4 * (designReadFirst o).length)
    (hhint : 3 * r.2.2.length < 4 * (designReadFirstSet e₂ o).ncard →
      letI : Fintype ↥s := Fintype.ofFinite _
      letI : DecidableEq ↥s := Classical.decEq _
      (X.linkGraph.restrictBlkHint (designReadFirstSet e₂ o)
        (designReadMathHint e₂ o)).HasHint) :
    letI : Fintype ↥s := Fintype.ofFinite _
    letI : DecidableEq ↥s := Classical.decEq _
    10 * (designReadSelectedSet r name₂ o).ncard ≤ 9 * X.blocks.ncard ∨
      ((designReadSelectedSet r name₂ o).ncard ≤ X.blocks.ncard ∧
        (X.linkGraph.restrictBlkHint (designReadSelectedSet r name₂ o)
          (designReadMathHint e₂ o)).HasHint) := by
  classical
  letI : Fintype ↥s := Fintype.ofFinite _
  letI : DecidableEq ↥s := Classical.decEq _
  have hn : r.2.2.length = X.blocks.ncard := designRight_length e₂
  have hcard := designReadFirstSet_ncard e₂ o hnd hL
  have hsub := designReadFirstSet_sub e₂ o
  have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
  have he := designReadSelectedSet_eq h hw e₁ he₁ e₂ he₂ o hnd hL
  rcases reducePart2ByColorBlk_mem X.linkGraph (designReadFirstSet e₂ o)
      (X.blocks \ designReadFirstSet e₂ o) with hfirst | hsecond
  · rw [hfirst] at he
    rw [he]
    by_cases hsmall : 4 * (designReadFirstSet e₂ o).ncard ≤ 3 * r.2.2.length
    · left; omega
    · exact Or.inr ⟨hle,hhint (by omega)⟩
  · rw [hsecond] at he
    rw [he]
    left
    have hc := Set.ncard_diff hsub (Set.toFinite _)
    omega

include h hw he₁ he₂ in
open scoped Classical in
theorem designReadPartition_progress (P : RawColPart)
    (hlen : P.1.length = r.2.2.length)
    (hP : (decColPartition P.1.length P).IsAlphaPartition (3 / 4))
    (hn : 4 ≤ P.1.length) :
    letI : Fintype ↥s := Fintype.ofFinite _
    letI : DecidableEq ↥s := Classical.decEq _
    let o := designReadPartitionExit P
    10 * (designReadSelectedSet r name₂ o).ncard ≤ 9 * X.blocks.ncard ∨
      ((designReadSelectedSet r name₂ o).ncard ≤ X.blocks.ncard ∧
        (X.linkGraph.restrictBlkHint (designReadSelectedSet r name₂ o)
          (designReadMathHint e₂ o)).HasHint) := by
  apply designReadSelected_progress h hw e₁ he₁ e₂ he₂ (designReadPartitionExit P)
    (rawEquipFirst_nodup P)
  · intro i hi
    rw [← hlen]
    exact rawEquipFirst_lt hi
  · rw [← hlen]
    exact rawEquipFirst_quarter P (by omega)
  · exact designReadPartition_hasHint e₂ P hlen hP hn

include h hw he₁ he₂ in
open scoped Classical in
theorem designReadUpcc_progress (l : List ℕ) (q : RawConfig)
    (hnd : l.Nodup) (hL : ∀ i ∈ l, i < r.2.2.length)
    (hbig : 3 * r.2.2.length < 4 * l.length)
    (Z : PartitionStructure (Fin l.length)) (hco : Z.IsCoherent)
    (hu : Z.IsUniprimitive)
    (hc : ∀ i j : Fin l.length, binColor (q,(i,j)) = Z.natColor i j) :
    letI : Fintype ↥s := Fintype.ofFinite _
    letI : DecidableEq ↥s := Classical.decEq _
    let o : RawDesignReadOut := (none,l,some q)
    10 * (designReadSelectedSet r name₂ o).ncard ≤ 9 * X.blocks.ncard ∨
      ((designReadSelectedSet r name₂ o).ncard ≤ X.blocks.ncard ∧
        (X.linkGraph.restrictBlkHint (designReadSelectedSet r name₂ o)
          (designReadMathHint e₂ o)).HasHint) := by
  apply designReadSelected_progress h hw e₁ he₁ e₂ he₂ (none,l,some q) hnd hL (by
    change r.2.2.length ≤ 4 * l.length
    omega)
  intro _
  exact designReadUpcc_hasHint e₂ l q hnd hL Z hco hu hc

end
end Algo
