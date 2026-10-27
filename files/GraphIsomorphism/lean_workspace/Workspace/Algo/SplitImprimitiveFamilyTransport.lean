import Workspace.Algo.SplitImprimitiveFamily

/-! The complete implemented ImprimitiveCase family is canonical under
independent compact numberings. The paper's branch test transports first,
then every chosen partition or graph has a target representative in the
same ordered branch of the algorithm.
-/
namespace Algo
open Babai RAM
open scoped Classical
section
variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {s t : Set Ω}
    {X : BlkImprimitiveObj s} {Y : BlkImprimitiveObj t} {φ : ↥s ≃ ↥t}
    (hφ : φ ∈ (BlkImprimitiveCases Ω).Iso X Y)
include hφ

theorem impPaperOutcome_transport
    (Z : Pt (Cat.sum (ColoredPartitions Ω ℕ) (VColBlkGraphs Ω ℕ)))
    (hZ : ImpPaperOutcome X Z) :
    ∃ Z',ImpPaperOutcome Y Z' ∧ ∃ (hS : Z.car ⊆ s) (hT : Z'.car ⊆ t),
      φ ∈ (Cat.sub (Cat.sum (ColoredPartitions Ω ℕ) (VColBlkGraphs Ω ℕ))).Iso
        ⟨⟨Z.car,hS⟩,Z.obj⟩ ⟨⟨Z'.car,hT⟩,Z'.obj⟩ := by
  by_cases hs : ImprimitiveSplits X
  · rw [ImpPaperOutcome,if_pos hs] at hZ
    obtain ⟨B,rfl⟩ := hZ
    let B' : ↥Y.blocks := ⟨φ '' B.val,(hφ.2.1 B.val).2 B.property⟩
    refine ⟨⟨Subtype.val '' Y.Pt₁,
      Sum.inl (kerPartition Y.Pt₁ (fun y => Y.c {y} B'.val))⟩,?_,?_,?_,?_⟩
    · rw [ImpPaperOutcome,if_pos (imprimitiveSplits_congr (X := ⟨s,X⟩) (Y := ⟨t,Y⟩) ⟨φ,hφ⟩ hs)]
      exact ⟨B',rfl⟩
    · rintro _ ⟨x,_,rfl⟩
      exact x.property
    · rintro _ ⟨y,_,rfl⟩
      exact y.property
    · apply kerOutcomeL_mem_subIso (VColBlkGraphs Ω ℕ) φ hφ.1
      intro x
      simpa only [Set.image_singleton] using hφ.2.2 {x} B.val
  · have hs' : ¬ ImprimitiveSplits Y := fun hy => hs
      (imprimitiveSplits_congr (X := ⟨t,Y⟩) (Y := ⟨s,X⟩)
        ⟨φ.symm,(BlkImprimitiveCases Ω).symm_mem hφ⟩ hy)
    rw [ImpPaperOutcome,if_neg hs] at hZ
    obtain ⟨G,rfl,hG,hdef,hbranch⟩ := hZ
    obtain ⟨Z',hZ',hiso⟩ := step2Out_equivariant hφ
      ⟨⟨s,subset_rfl⟩,Sum.inr G⟩ ⟨G,⟨hG,hdef,hbranch⟩,rfl⟩
    obtain ⟨G',⟨hG',hdef',hbranch'⟩,rfl⟩ := hZ'
    refine ⟨⟨t,Sum.inr G'⟩,?_,subset_rfl,subset_rfl,hiso⟩
    rw [ImpPaperOutcome,if_neg hs']
    exact ⟨G',rfl,hG',hdef',hbranch'⟩

variable {r r' : RawUpccCase}
    {name₁ : ↥X.Pt₁ → ℕ} {name₂ : ↥X.blocks → ℕ}
    {name₁' : ↥Y.Pt₁ → ℕ} {name₂' : ↥Y.blocks → ℕ}
    (hn : ImpNames X name₁ name₂ r) (hn' : ImpNames Y name₁' name₂' r')
    (hl : r.2.1.Nodup) (hr : r.2.2.Nodup)
    (hl' : r'.2.1.Nodup) (hr' : r'.2.2.Nodup)
    (e₁ : ↥X.Pt₁ ≃ Fin r.2.1.length) (he₁ : ∀ x,r.2.1[(e₁ x).val] = name₁ x)
    (e₂ : ↥X.blocks ≃ Fin r.2.2.length) (he₂ : ∀ B,r.2.2[(e₂ B).val] = name₂ B)
    (e₁' : ↥Y.Pt₁ ≃ Fin r'.2.1.length) (he₁' : ∀ x,r'.2.1[(e₁' x).val] = name₁' x)
    (e₂' : ↥Y.blocks ≃ Fin r'.2.2.length) (he₂' : ∀ B,r'.2.2[(e₂' B).val] = name₂' B)
include hn hn' hl hr hl' hr' he₁ he₂ he₁' he₂'

theorem impCase_transport (q : RawImpOutcome) (hq : q ∈ impCase r) :
    ∃ q' ∈ impCase r',∃ Z Z',
      ImpOutcomeRep X name₁ name₂ r e₁ q Z ∧
      ImpOutcomeRep Y name₁' name₂' r' e₁' q' Z' ∧
      ImpPaperOutcome X Z ∧ ImpPaperOutcome Y Z' ∧
      ∃ (hS : Z.car ⊆ s) (hT : Z'.car ⊆ t),
        φ ∈ (Cat.sub (Cat.sum (ColoredPartitions Ω ℕ) (VColBlkGraphs Ω ℕ))).Iso
          ⟨⟨Z.car,hS⟩,Z.obj⟩ ⟨⟨Z'.car,hT⟩,Z'.obj⟩ := by
  obtain ⟨Z,hrep,hpaper⟩ := impCase_paper hn hl hr e₁ he₁ e₂ he₂ q hq
  obtain ⟨Z',hpaper',hS,hT,hiso⟩ := impPaperOutcome_transport hφ Z hpaper
  obtain ⟨q',hq',hrep'⟩ := impCase_complete hn' hl' hr' e₁' he₁' e₂' he₂' Z' hpaper'
  exact ⟨q',hq',Z,Z',hrep,hrep',hpaper,hpaper',hS,hT,hiso⟩

omit he₁ he₁' in
/-- The graph-only branch transports each actual selected graph, with
its complete colors and hint, along the original ambient map. -/
theorem impStep2Graphs_transport (hsplit : ¬ ImprimitiveSplits X)
    (q : RawImpGraph) (hq : q ∈ impStep2Graphs r) :
    ∃ q' ∈ impStep2Graphs r',∃ (G : VColBipBlk ↥s ℕ) (G' : VColBipBlk ↥t ℕ),
      ImpGraphRep X name₁ name₂ r q G ∧
      ImpGraphRep Y name₁' name₂' r' q' G' ∧ G.IsIsoTo G' φ ∧
      G ∈ X.step2Cands ∧
      (letI : Fintype ↥s := Fintype.ofFinite _
       letI : DecidableEq ↥s := Classical.decEq _
       1/2 ≤ G.defect₁) ∧
      G' ∈ Y.step2Cands ∧
      (letI : Fintype ↥t := Fintype.ofFinite _
       letI : DecidableEq ↥t := Classical.decEq _
       1/2 ≤ G'.defect₁) := by
  obtain ⟨G,hrep,hG,hdef,hbranch,_⟩ := impStep2Graphs_spec hn hl hr e₂ he₂ hsplit q hq
  obtain ⟨Z',hZ',hiso⟩ := step2Out_equivariant hφ
    ⟨⟨s,subset_rfl⟩,Sum.inr G⟩ ⟨G,⟨hG,hdef,hbranch⟩,rfl⟩
  obtain ⟨G',⟨hG',hdef',hbranch'⟩,rfl⟩ := hZ'
  obtain ⟨q',hq',hrep'⟩ := impStep2Graphs_covers hn' hl' hr' e₂' he₂' G' hG' hdef' hbranch'
  refine ⟨q',hq',G,G',hrep,hrep',?_,hG,hdef,hG',hdef'⟩
  obtain ⟨ψ,hψ,hiso⟩ := hiso
  have he : ψ = φ := Equiv.ext (fun x => Subtype.ext (hψ x))
  subst ψ
  exact hiso

end
end Algo
