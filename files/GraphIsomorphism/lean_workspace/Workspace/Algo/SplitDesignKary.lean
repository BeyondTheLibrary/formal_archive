import Workspace.Algo.SplitDesignCall
import Workspace.Master.KAryOfString

/-! # Section 9.7: transport the Design Lemma hypotheses

The single stored relation defines the same k-ary structure as the paper,
including the empty relations at all other indices. The block bijection
therefore preserves the automorphism group and its symmetry defect.
-/
namespace Algo
open Babai RAM

/-- An isomorphism of k-ary structures conjugates their automorphism groups. -/
theorem designIso_aut {V W C : Type*} {k : ℕ}
    {X : KAryRelStruct V C k} {Y : KAryRelStruct W C k}
    (e : V ≃ W) (he : e ∈ KAryRelStruct.Iso X Y) :
    Y.Aut = X.Aut.map e.permCongrHom.toMonoidHom := by
  ext p
  rw [Subgroup.mem_map_equiv]
  have hcomm (x : Str V k) :
      tupleMap e (tupleMap (e.permCongrHom.symm p) x) =
        tupleMap p (tupleMap e x) := by
    funext i
    simp [tupleMap,Equiv.permCongr_symm_apply]
  constructor
  · intro hp c x
    rw [he c x,he c (tupleMap (e.permCongrHom.symm p) x),hcomm]
    exact hp c (tupleMap e x)
  · intro hp c y
    let x : Fin k → V := fun i => e.symm (y i)
    have hh := hp c x
    rw [he c x,he c (tupleMap (e.permCongrHom.symm p) x),hcomm] at hh
    have hx : tupleMap e x = y := by funext i; simp [x,tupleMap]
    rwa [hx] at hh

/-- The one-relation table has no unintended colors beyond index zero. -/
theorem designCallRelations_length (r : RawUpccCase) :
    (designCallRelations r).length = 1 := rfl

section Specification
variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {s : Set Ω}
    {X : BlkDesignObj s} {name₁ : ↥X.Pt₁ → ℕ} {name₂ : ↥X.blocks → ℕ}
    {r : RawUpccCase} (h : DesignNames X name₁ name₂ r)
    (e₁ : ↥X.Pt₁ ≃ Fin r.2.1.length) (he₁ : ∀ x, r.2.1[(e₁ x).val] = name₁ x)
    (e₂ : ↥X.blocks ≃ Fin r.2.2.length) (he₂ : ∀ B, r.2.2[(e₂ B).val] = name₂ B)
include h he₁ he₂

/-- The complete k-ary input, with every relation index accounted for. -/
theorem designCallRelations_iso {k : ℕ} (S : RelStructure ↥X.blkAmb)
    (hnum : S.numRel = 1) (hary : S.IsKAry k)
    (hrel : ∀ v : Fin k → ↥X.blkAmb,
      (fun i => designBlockEquiv e₂ (v i)) ∈
        (decRel r.2.2.length k (designCallRelations r)).rel 0 ↔
      v ∈ (S.toKAry hary).rel 0) :
    designBlockEquiv e₂ ∈ KAryRelStruct.Iso (S.toKAry hary)
      (decRel r.2.2.length k (designCallRelations r)) := by
  intro i v
  by_cases hi : i = 0
  · subst i; exact (hrel v).symm
  · rw [RelStructure.toKAry_rel_of_ge _ _ (by rw [hnum]; omega)]
    change False ↔ tupleOf _ ∈ (designCallRelations r).getD i []
    rw [getD_of_length_le (by rw [designCallRelations_length]; omega)]
    simp

/-- The Case 3a input has the paper's symmetry defect, in its finite names. -/
theorem designCall_case3a_defect (hlt : X.n₂ < X.n₁) (hc : X.IsCase3a) :
    defect (decRel r.2.2.length X.d' (designCallRelations r)).Aut =
      structDefect (X.nbhdStruct X.d') := by
  classical
  have hi := designCallRelations_iso h e₁ he₁ e₂ he₂ (X.nbhdStruct X.d') rfl
    (X.nbhdStruct_isKAry X.d') (fun v => by
      simpa only [RelStructure.toKAry,Hypergraph.toRelStructureSimple,
        BlkCaseObj.nbhdStruct,RelStructure.reindexRel,dif_pos (show 0 < 1 by omega)] using
        designCallRelations_case3a h e₁ he₁ e₂ he₂ hlt hc v)
  rw [designIso_aut _ hi,defect_map_permCongrHom,RelStructure.toKAry_aut]
  rfl

/-- The Case 3b input has the skeleton's symmetry defect. -/
theorem designCall_case3b_defect (hlt : X.n₂ < X.n₁) (hc : ¬ X.IsCase3a) :
    defect (decRel r.2.2.length X.tSkel (designCallRelations r)).Aut =
      structDefect (X.skelStruct X.tSkel) := by
  classical
  have hi := designCallRelations_iso h e₁ he₁ e₂ he₂ (X.skelStruct X.tSkel) rfl
    (X.skelStruct_isKAry X.tSkel) (fun v => by
      simpa only [RelStructure.toKAry,Hypergraph.toRelStructureSimple,
        BlkCaseObj.skelStruct,RelStructure.reindexRel,dif_pos (show 0 < 1 by omega)] using
        designCallRelations_case3b h e₁ he₁ e₂ he₂ hlt hc v)
  rw [designIso_aut _ hi,defect_map_permCongrHom,RelStructure.toKAry_aut]
  rfl

end Specification
end Algo
