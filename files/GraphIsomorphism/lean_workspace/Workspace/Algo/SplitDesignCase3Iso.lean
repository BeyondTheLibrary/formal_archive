import Workspace.Algo.SplitDesignCase3Transport
import Workspace.Algo.SplitDesignTestsTransport
import Workspace.Algo.SplitDesignCase3Defect
import Workspace.Algo.SplitDesignHintValidity
import Workspace.SplitOrJohnson.BlkSymIso
import Workspace.SplitOrJohnson.BlockDesignSkel

/-! # Sec. 9.7, Case 3 at two isomorphic parents

Two objects of Sec. 9.7 (v2.5) related by a morphism `φ` name their blocks by positions in
two stored lists. The morphism moves blocks to blocks, hence positions to positions by a
permutation. This permutation is an isomorphism of the two stored relations (the relation is
the `k`-skeleton of the neighborhood hypergraph `H` in block coordinates, and `φ` carries `H`
to `H`). So the Design Lemma call of Case 3 moves along it
(`designCallReadFamily_iso`), and the selected block family and the hint of every returned
object correspond under `φ`. This is the canonicity of Case 3 that Sec. 9.7 uses.
-/
namespace Algo
open Babai RAM Equiv
open scoped Classical

section
variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {s t : Set Ω}
    {X : BlkDesignObj s} {Y : BlkDesignObj t} {φ : ↥s ≃ ↥t}
    (hφ : X.IsMorphOn Y φ)
    {n₁ : ↥X.Pt₁ → ℕ} {n₂ : ↥X.blocks → ℕ}
    {n₁' : ↥Y.Pt₁ → ℕ} {n₂' : ↥Y.blocks → ℕ} {r r' : RawUpccCase}
    (h : DesignNames X n₁ n₂ r) (h' : DesignNames Y n₁' n₂' r')
    (e₁ : ↥X.Pt₁ ≃ Fin r.2.1.length) (he₁ : ∀ x,r.2.1[(e₁ x).val] = n₁ x)
    (e₂ : ↥X.blocks ≃ Fin r.2.2.length) (he₂ : ∀ B,r.2.2[(e₂ B).val] = n₂ B)
    (e₁' : ↥Y.Pt₁ ≃ Fin r'.2.1.length) (he₁' : ∀ x,r'.2.1[(e₁' x).val] = n₁' x)
    (e₂' : ↥Y.blocks ≃ Fin r'.2.2.length) (he₂' : ∀ B,r'.2.2[(e₂' B).val] = n₂' B)

/-- The blocks of `X` go to the blocks of `Y` by `φ`. -/
def designBlockMap : ↥X.blocks ≃ ↥Y.blocks :=
  (imgEquiv φ).subtypeEquiv (fun B => (hφ.blocks B).symm)

@[simp] theorem designBlockMap_val (B : ↥X.blocks) :
    (designBlockMap hφ B).val = φ '' B.val := rfl

include hφ e₂ e₂' in
theorem designRight_length_eq : r'.2.2.length = r.2.2.length := by
  rw [designRight_length e₂',designRight_length e₂,hφ.n₂_eq]

include hφ e₁ e₁' in
theorem designLeft_length_eq : r'.2.1.length = r.2.1.length := by
  rw [designLeft_length e₁',designLeft_length e₁,hφ.n₁_eq]

/-- The action of `φ` on block positions. -/
def designBlockPos : Perm (Fin r.2.2.length) :=
  e₂.symm.trans ((designBlockMap hφ).trans (e₂'.trans (finCongr (designRight_length_eq hφ e₂ e₂'))))

theorem designBlockPos_apply (B : ↥X.blocks) :
    (designBlockPos hφ e₂ e₂' (e₂ B)).val = (e₂' (designBlockMap hφ B)).val := by
  simp [designBlockPos]

include hφ h h' he₁ he₂ he₁' he₂' in
theorem designCallWitness_length_eq :
    (designCallWitness r').length = (designCallWitness r).length := by
  rw [designCallWitness_length h' e₁' he₁' e₂' he₂',designCallWitness_length h e₁ he₁ e₂ he₂]
  by_cases hc : X.IsCase3a
  · rw [if_pos (hφ.isCase3a_iff.2 hc),if_pos hc,hφ.d'_eq]
  · rw [if_neg (fun hh => hc (hφ.isCase3a_iff.1 hh)),if_neg hc,hφ.tSkel_eq]

include h h' he₁ he₂ he₁' he₂' in
/-- **The block positions move by an isomorphism of the stored relations.** -/
theorem designBlockPos_iso (hlt : X.n₂ < X.n₁) :
    designBlockPos hφ e₂ e₂' ∈ KAryRelStruct.Iso
      (decRel r.2.2.length (designCallWitness r).length (designCallRelations r))
      (decRel r.2.2.length (designCallWitness r).length (designCallRelations r')) := by
  have hlt' : Y.n₂ < Y.n₁ := by rw [hφ.n₂_eq,hφ.n₁_eq]; exact hlt
  have hk' := designCallWitness_length_eq hφ h h' e₁ he₁ e₂ he₂ e₁' he₁' e₂' he₂'
  intro i x
  by_cases hi : i = 0
  · subst i
    let v : Fin (designCallWitness r).length → ↥X.blkAmb := fun j => (designBlockEquiv e₂).symm (x j)
    have hx : x = fun j => designBlockEquiv e₂ (v j) := by
      funext j; simp [v]
    have hmap : ∀ b : ↥X.blkAmb,((designBlockPos hφ e₂ e₂' (designBlockEquiv e₂ b)) : ℕ) =
        (designBlockEquiv e₂' (BlkCaseObj.blkAmbEquiv hφ b) : ℕ) := by
      intro b
      change (designBlockPos hφ e₂ e₂' (e₂ ⟨X.blkOf b,X.blkOf_mem b⟩)).val =
        (e₂' ⟨Y.blkOf (BlkCaseObj.blkAmbEquiv hφ b),Y.blkOf_mem _⟩).val
      rw [designBlockPos_apply]
      congr 2
      apply Subtype.ext
      simp only [designBlockMap_val,BlkCaseObj.blkAmbEquiv_apply,BlkCaseObj.blkOf_blkMap]
    have h1 := designCallRelations_skeleton h e₁ he₁ e₂ he₂ hlt _ rfl v
    have h2 := designCallRelations_skeleton h' e₁' he₁' e₂' he₂' hlt' _ hk'
      (fun j => BlkCaseObj.blkAmbEquiv hφ (v j))
    change (_ ↔ Function.Injective v ∧ Finset.univ.image v ∈ _) at h1
    change (_ ↔ Function.Injective (fun j => BlkCaseObj.blkAmbEquiv hφ (v j)) ∧
      Finset.univ.image (fun j => BlkCaseObj.blkAmbEquiv hφ (v j)) ∈ _) at h2
    simp only [mem_decRel_rel] at h1 h2 ⊢
    have ht : tupleOf (tupleMap (designBlockPos hφ e₂ e₂') x) =
        tupleOf (fun j => designBlockEquiv e₂' (BlkCaseObj.blkAmbEquiv hφ (v j))) := by
      rw [hx]
      simp only [tupleOf,tupleMap]
      congr 1
      funext j
      exact hmap (v j)
    rw [ht,h2,hx,h1]
    have himg : Finset.univ.image (fun j => BlkCaseObj.blkAmbEquiv hφ (v j)) =
        (Finset.univ.image v).image (BlkCaseObj.blkAmbEquiv hφ) := by
      rw [Finset.image_image]; rfl
    rw [himg,Hypergraph.mem_skeleton_edgeSet_image X.nbhdHg Y.nbhdHg _
      (BlkCaseObj.blkAmbEquiv hφ) (BlkCaseObj.nbhdHg_edgeSet_image hφ)]
    exact and_congr ⟨fun hv a b he => hv ((BlkCaseObj.blkAmbEquiv hφ).injective he),
      fun hv a b he => hv (congrArg _ he)⟩ Iff.rfl
  · simp only [mem_decRel_rel]
    rw [getD_of_length_le (by rw [designCallRelations_length]; omega),
      getD_of_length_le (by rw [designCallRelations_length]; omega)]
    simp

include hφ in
omit [Fintype Ω] [DecidableEq Ω] in
theorem designBlockMap_mem_iff {P : Set (Set ↥s)} {P' : Set (Set ↥t)} (hP : P ⊆ X.blocks)
    (hP' : P' ⊆ Y.blocks) (hc : ∀ B : ↥X.blocks,designBlockMap hφ B ∈ Subtype.val ⁻¹' P' ↔ B.val ∈ P)
    (B : Set ↥s) : φ '' B ∈ P' ↔ B ∈ P := by
  by_cases hB : B ∈ X.blocks
  · exact hc ⟨B,hB⟩
  · exact iff_of_false (fun hh => hB ((hφ.blocks B).1 (hP' hh))) (fun hh => hB (hP hh))

variable {xs xs' : List ℕ} {o o' : RawDesignReadOut}
    (ho : (xs,o) ∈ designCallReadFamily r) (ho' : (xs',o') ∈ designCallReadFamily r')
    (hi : DesignReadOutIso r.2.2.length (designBlockPos hφ e₂ e₂') o o')

include ho ho' hi in
theorem designReadFirstSet_iso (B : Set ↥s) :
    φ '' B ∈ designReadFirstSet e₂' o' ↔ B ∈ designReadFirstSet e₂ o := by
  have hN := designRight_length_eq hφ e₂ e₂'
  apply designBlockMap_mem_iff hφ (designReadFirstSet_sub e₂ o) (designReadFirstSet_sub e₂' o')
  intro C
  change (designBlockMap hφ C).val ∈ designReadFirstSet e₂' o' ↔ _
  rw [designReadFirstSet_mem,designReadFirstSet_mem,← designBlockPos_apply]
  refine (designReadFirst_iso hi (fun P hp => designCallRead_partition_length r ho hp)
    (fun P hp => (designCallRead_partition_length r' ho' hp).trans hN) (e₂ C)).symm

include h h' he₁ he₂ he₁' he₂' ho ho' hi in
/-- **Sec. 9.7, Case 3: the selected block family is canonical.** -/
theorem designReadSelectedSet_iso (hw : r.WF) (hw' : r'.WF) (B : Set ↥s) :
    letI : Fintype ↥s := Fintype.ofFinite _
    letI : DecidableEq ↥s := Classical.decEq _
    letI : Fintype ↥t := Fintype.ofFinite _
    letI : DecidableEq ↥t := Classical.decEq _
    φ '' B ∈ designReadSelectedSet r' n₂' o' ↔ B ∈ designReadSelectedSet r n₂ o := by
  letI : Fintype ↥s := Fintype.ofFinite _
  letI : DecidableEq ↥s := Classical.decEq _
  letI : Fintype ↥t := Fintype.ofFinite _
  letI : DecidableEq ↥t := Classical.decEq _
  obtain ⟨hnd,hL⟩ := designCallReadFirst_names r ho
  obtain ⟨hnd',hL'⟩ := designCallReadFirst_names r' ho'
  rw [designReadSelectedSet_eq h hw e₁ he₁ e₂ he₂ o hnd hL,
    designReadSelectedSet_eq h' hw' e₁' he₁' e₂' he₂' o' hnd' hL']
  have hF := designReadFirstSet_iso hφ e₂ e₂' ho ho' hi
  refine reducePart2ByColorBlk_image (BlkCaseObj.linkGraph_isIsoTo hφ) hF (fun C => ?_) B
  change φ '' C ∈ Y.blocks \ _ ↔ C ∈ X.blocks \ _
  simp only [Set.mem_diff,hφ.blocks C,hF C]

include ho ho' hi in
/-- **Sec. 9.7, Case 3: the hint on pairs of blocks is canonical.** -/
theorem designReadMathHint_iso (A B : Set ↥s) (hA : A ∈ X.blocks) (hB : B ∈ X.blocks) :
    designReadMathHint e₂' o' (φ '' A) (φ '' B) = designReadMathHint e₂ o A B := by
  have hN := designRight_length_eq hφ e₂ e₂'
  have e1 := designReadMathHint_on e₂ o ⟨A,hA⟩ ⟨B,hB⟩
  have e2 := designReadMathHint_on e₂' o' (designBlockMap hφ ⟨A,hA⟩) (designBlockMap hφ ⟨B,hB⟩)
  simp only [designBlockMap_val] at e2
  rw [e1,e2,← designBlockPos_apply,← designBlockPos_apply]
  exact designReadHintAt_iso hi (fun P hp => designCallRead_partition_length r ho hp)
    (fun P hp => (designCallRead_partition_length r' ho' hp).trans hN) _ _

end
end Algo
