import Workspace.Algo.SplitDesignNames

/-! # Section 9.7: the exact hypergraph and its twins

Neighborhood rows give the simple hypergraph of the paper. The proof keeps
the vertex bijection explicit, including when a transposition exchanges
hyperedges rather than fixing each edge.
-/
namespace Algo
open Babai RAM

/-- Neighborhood hypergraph on second-part positions. -/
def designHypergraph (r : RawUpccCase) : RawSplitHypergraph :=
  (r.2.2,simpleHypergraphRowsRaw (neighborhoodRowsRaw (designBip r)))

theorem polyFun_designHypergraph : PolyFun designHypergraph :=
  (polyFun_snd.comp polyFun_snd).pair
    (polyFun_designBip.comp (polyFun_neighborhoodRowsRaw.comp polyFun_simpleHypergraphRowsRaw))

theorem designHypergraph_simple (r : RawUpccCase) :
    (decSplitHypergraph r.2.2.length (designHypergraph r).2).IsSimple :=
  simpleHypergraphRowsRaw_isSimple (neighborhoodRowsRaw_wf (designBip r))

/-- Hypergraph twin labels used in Cases 1 and 2. -/
def designTwins (r : RawUpccCase) : RawLab := hypergraphTwinsRaw (designHypergraph r)

theorem polyFun_designTwins : PolyFun designTwins :=
  polyFun_designHypergraph.comp polyFun_hypergraphTwinsRaw

@[simp] theorem designTwins_length (r : RawUpccCase) :
    (designTwins r).length = r.2.2.length := length_hypergraphTwinsRaw _

section Specification
variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {s : Set Ω}
    {X : BlkDesignObj s} {name₁ : ↥X.Pt₁ → ℕ} {name₂ : ↥X.blocks → ℕ}
    {r : RawUpccCase} (h : DesignNames X name₁ name₂ r)
    (e₁ : ↥X.Pt₁ ≃ Fin r.2.1.length) (he₁ : ∀ x, r.2.1[(e₁ x).val] = name₁ x)
    (e₂ : ↥X.blocks ≃ Fin r.2.2.length) (he₂ : ∀ B, r.2.2[(e₂ B).val] = name₂ B)

/-- The paper views blocks in the ambient point set. The machine uses positions. -/
def designBlockEquiv : ↥X.blkAmb ≃ Fin r.2.2.length where
  toFun b := e₂ ⟨X.blkOf b,X.blkOf_mem b⟩
  invFun i := X.blkPt (e₂.symm i).property
  left_inv b := by simp only [Equiv.symm_apply_apply,X.blkPt_blkOf]
  right_inv i := by
    simp only [X.blkOf_blkPt]
    change e₂ (e₂.symm i) = i
    exact e₂.apply_symm_apply i

@[simp] theorem designBlockEquiv_apply (B : ↥X.blocks) :
    designBlockEquiv e₂ (X.blkPt B.property) = e₂ B := by
  simp [designBlockEquiv]

include h he₁ he₂

/-- Each row is the corresponding paper hyperedge under the displayed bijection. -/
theorem designRow_image (x : ↥X.Pt₁) :
    splitRowSet r.2.2.length (splitNeighborhoodRow (designBip r,e₁ x)) =
      (X.toBlkFinset (X.nbhd x.val)).image (designBlockEquiv e₂) := by
  classical
  apply Finset.ext
  intro i
  obtain ⟨B,rfl⟩ := e₂.surjective i
  rw [mem_splitRowSet,designRow_mem h e₁ he₁ e₂ he₂]
  constructor
  · intro hB
    exact Finset.mem_image.2 ⟨X.blkPt B.property,
      (X.mem_toBlkFinset _ _).2 (by simpa using hB),designBlockEquiv_apply e₂ B⟩
  · intro hi
    obtain ⟨b,hb,he⟩ := Finset.mem_image.1 hi
    have he' : b = X.blkPt B.property := (designBlockEquiv e₂).injective
      (he.trans (designBlockEquiv_apply e₂ B).symm)
    subst b
    simpa only [X.mem_toBlkFinset,X.blkOf_blkPt] using hb

/-- The stored hyperedges are exactly the paper's hyperedges in these coordinates. -/
theorem designHypergraph_edges (F : Finset (Fin r.2.2.length)) :
    F ∈ (decSplitHypergraph r.2.2.length (designHypergraph r).2).edgeSet ↔
      ∃ x : ↥X.Pt₁, F = (X.toBlkFinset (X.nbhd x.val)).image (designBlockEquiv e₂) := by
  classical
  change F ∈ (decSplitHypergraph _ (simpleHypergraphRowsRaw _)).edgeSet ↔ _
  rw [simpleHypergraphRowsRaw_edgeSet]
  constructor
  · rintro ⟨i,hi⟩
    let j : Fin r.2.1.length := ⟨i.val,by simpa [decSplitHypergraph] using i.isLt⟩
    refine ⟨e₁.symm j,?_⟩
    rw [← designRow_image h e₁ he₁ e₂ he₂,Equiv.apply_symm_apply]
    change F = splitRowSet r.2.2.length (splitNeighborhoodRow (designBip r,j))
    rw [← hi]
    change splitRowSet _ ((neighborhoodRowsRaw (designBip r)).getD i.val []) = _
    rw [neighborhoodRowsRaw_get (designBip r) j]
  · rintro ⟨x,rfl⟩
    refine ⟨⟨(e₁ x).val,by
      change (e₁ x).val < (neighborhoodRowsRaw (designBip r)).length
      rw [length_neighborhoodRowsRaw]
      exact (e₁ x).isLt⟩,?_⟩
    change splitRowSet _ ((neighborhoodRowsRaw (designBip r)).getD (e₁ x) []) = _
    rw [neighborhoodRowsRaw_get,designRow_image h e₁ he₁ e₂ he₂]

/-- Membership in the paper's finite edge family is preserved in both directions. -/
theorem designHypergraph_image_mem (F : Finset ↥X.blkAmb) :
    F.image (designBlockEquiv e₂) ∈
      (decSplitHypergraph r.2.2.length (designHypergraph r).2).edgeSet ↔
        F ∈ X.edgeFinsetFam := by
  rw [designHypergraph_edges h e₁ he₁ e₂ he₂,X.mem_edgeFinsetFam]
  constructor
  · rintro ⟨x,hF⟩
    exact ⟨X.nbhd x.val,⟨x.val,x.property,rfl⟩,
      Finset.image_injective (designBlockEquiv e₂).injective hF⟩
  · rintro ⟨S,⟨x,hx,rfl⟩,rfl⟩
    exact ⟨⟨x,hx⟩,rfl⟩

/-- Exchanging two raw vertices tests exactly the paper's hypergraph twin relation. -/
theorem designTwins_spec (B C : ↥X.blocks) :
    LabRel (designTwins r) (e₂ B) (e₂ C) ↔ X.IsHTwin B.val C.val := by
  classical
  rw [designTwins,hypergraphTwinsRaw_spec]
  change TwinOrEq (decSplitHypergraph r.2.2.length (designHypergraph r).2).Aut
    (e₂ B) (e₂ C) ↔ _
  have swapImage (F : Finset ↥X.blkAmb) :
      (F.image (designBlockEquiv e₂)).image (Equiv.swap (e₂ B) (e₂ C)) =
        (F.image (Equiv.swap (X.blkPt B.property) (X.blkPt C.property))).image
          (designBlockEquiv e₂) := by
    rw [Finset.image_image,Finset.image_image]
    apply Finset.image_congr
    intro a _
    dsimp only [Function.comp_def]
    rw [(designBlockEquiv e₂).injective.map_swap,designBlockEquiv_apply,designBlockEquiv_apply]
  have hs : Equiv.swap (e₂ B) (e₂ C) ∈
      (decSplitHypergraph r.2.2.length (designHypergraph r).2).Aut ↔ X.IsHTwin B.val C.val := by
    constructor
    · intro hs
      refine (X.isHTwin_iff_image B.property C.property).2 fun F hF => ?_
      have hm := (Hypergraph.mem_aut_iff_edgeSet (designHypergraph_simple r) _).1 hs
        (F.image (designBlockEquiv e₂))
      rw [swapImage,designHypergraph_image_mem h e₁ he₁ e₂ he₂,
        designHypergraph_image_mem h e₁ he₁ e₂ he₂] at hm
      exact hm.2 hF
    · intro ht
      apply Hypergraph.mem_aut_of_involutive_image (designHypergraph_simple r)
        (fun x => Equiv.swap_apply_self _ _ x)
      intro A hA
      let F := A.image (designBlockEquiv e₂).symm
      have hF : F.image (designBlockEquiv e₂) = A := by
        simp [F,Finset.image_image,Function.comp_def]
      rw [← hF,swapImage,designHypergraph_image_mem h e₁ he₁ e₂ he₂]
      apply (X.isHTwin_iff_image B.property C.property).1 ht
      rw [← designHypergraph_image_mem h e₁ he₁ e₂ he₂,hF]
      exact hA
  by_cases hBC : B = C
  · subst C
    exact iff_of_true (Or.inl rfl) (X.isHTwin_refl _)
  · have he : e₂ B ≠ e₂ C := fun hh => hBC (e₂.injective hh)
    constructor
    · rintro (hh | ⟨_,hm⟩)
      · exact (he hh).elim
      · exact hs.1 hm
    · intro hh
      exact Or.inr ⟨he,hs.2 hh⟩

end Specification
end Algo
