import Workspace.Algo.SplitDesignCase3Names
import Workspace.Algo.SplitDesignReadNames

/-! Lemma 9.3.2 supplies the symmetry defect for the actual selected graph.
The selected set is read from its stored names, not supplied by the caller. -/
namespace Algo
open Babai RAM

section
variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {s : Set Ω}
    {X : BlkDesignObj s} {name₁ : ↥X.Pt₁ → ℕ} {name₂ : ↥X.blocks → ℕ}
    {r : RawUpccCase} (h : DesignNames X name₁ name₂ r) (hw : r.WF)
    (e₁ : ↥X.Pt₁ ≃ Fin r.2.1.length) (he₁ : ∀ x, r.2.1[(e₁ x).val] = name₁ x)
    (e₂ : ↥X.blocks ≃ Fin r.2.2.length) (he₂ : ∀ B, r.2.2[(e₂ B).val] = name₂ B)

def designReadSelectedSet (r : RawUpccCase) (name₂ : ↥X.blocks → ℕ) (o : RawDesignReadOut) :
    Set (Set ↥s) := Subtype.val '' {B : ↥X.blocks | name₂ B ∈ designReadSelected (r,o)}

theorem designReadSelectedSet_sub (o : RawDesignReadOut) :
    designReadSelectedSet r name₂ o ⊆ X.blocks := by
  rintro _ ⟨B,hB,rfl⟩
  exact B.property

theorem designReadSelectedSet_mem (o : RawDesignReadOut) (B : ↥X.blocks) :
    B.val ∈ designReadSelectedSet r name₂ o ↔ name₂ B ∈ designReadSelected (r,o) := by
  simp only [designReadSelectedSet,Set.mem_image,Set.mem_setOf_eq]
  exact ⟨fun ⟨C,hC,hCB⟩ => (Subtype.ext hCB : C = B) ▸ hC,fun hB => ⟨B,hB,rfl⟩⟩

include h hw he₁ he₂ in
open scoped Classical in
theorem designReadSelectedSet_eq (o : RawDesignReadOut)
    (hnd : (designReadFirst o).Nodup) (hL : ∀ i ∈ designReadFirst o, i < r.2.2.length) :
    letI : Fintype ↥s := Fintype.ofFinite _
    letI : DecidableEq ↥s := Classical.decEq _
    designReadSelectedSet r name₂ o = reducePart2ByColorBlk X.linkGraph
      (designReadFirstSet e₂ o) (X.blocks \ designReadFirstSet e₂ o) := by
  classical
  letI : Fintype ↥s := Fintype.ofFinite _
  letI : DecidableEq ↥s := Classical.decEq _
  have hsub : reducePart2ByColorBlk X.linkGraph (designReadFirstSet e₂ o)
      (X.blocks \ designReadFirstSet e₂ o) ⊆ X.blocks := by
    rcases reducePart2ByColorBlk_mem X.linkGraph (designReadFirstSet e₂ o)
      (X.blocks \ designReadFirstSet e₂ o) with he | he
    · rw [he]; exact designReadFirstSet_sub e₂ o
    · rw [he]; exact Set.diff_subset
  ext B
  by_cases hB : B ∈ X.blocks
  · exact (designReadSelectedSet_mem o ⟨B,hB⟩).trans
      (designReadSelected_mem h hw e₁ he₁ e₂ he₂ o hnd hL ⟨B,hB⟩)
  · exact iff_of_false (fun hh => hB (designReadSelectedSet_sub o hh))
      (fun hh => hB (hsub hh))

include h hw he₁ he₂ in
open scoped Classical in
theorem designReadSelectedSet_defect (o : RawDesignReadOut)
    (hnd : (designReadFirst o).Nodup) (hL : ∀ i ∈ designReadFirst o, i < r.2.2.length) :
    letI : Fintype ↥s := Fintype.ofFinite _
    letI : DecidableEq ↥s := Classical.decEq _
    ((X.n₁ : ℚ) - 1) / 2 ≤
      (X.linkGraph.restrictBlk (designReadSelectedSet r name₂ o)).symDefect₁ := by
  classical
  letI : Fintype ↥s := Fintype.ofFinite _
  letI : DecidableEq ↥s := Classical.decEq _
  rw [designReadSelectedSet_eq h hw e₁ he₁ e₂ he₂ o hnd hL]
  have hcov : X.linkGraph.blocks ⊆ designReadFirstSet e₂ o ∪ (X.blocks \ designReadFirstSet e₂ o) := by
    intro B hB
    by_cases hh : B ∈ designReadFirstSet e₂ o
    · exact Or.inl hh
    · exact Or.inr ⟨hB,hh⟩
  have he : Classical.decEq ↥s = fun a b => Subtype.instDecidableEq a b :=
    funext fun _ => funext fun _ => Subsingleton.elim _ _
  have hno : ∀ x, X.linkGraph.part₁ x → ∀ y, X.linkGraph.part₁ y →
      ¬ @IsTwin ↥s (Classical.decEq _) X.linkGraph.Aut x y := by
    rw [he]
    exact BlkCaseObj.linkGraph_noTwins X
  exact reducePart2ByColorBlk_spec X.linkGraph hno hcov

include h hw he₁ he₂ in
open scoped Classical in
theorem designCallReadSelected_defect {xs : List ℕ} {o : RawDesignReadOut}
    (ho : (xs,o) ∈ designCallReadFamily r) :
    letI : Fintype ↥s := Fintype.ofFinite _
    letI : DecidableEq ↥s := Classical.decEq _
    ((X.n₁ : ℚ) - 1) / 2 ≤
      (X.linkGraph.restrictBlk (designReadSelectedSet r name₂ o)).symDefect₁ := by
  obtain ⟨hnd,hL⟩ := designCallReadFirst_names r ho
  exact designReadSelectedSet_defect h hw e₁ he₁ e₂ he₂ o hnd hL

end
end Algo
