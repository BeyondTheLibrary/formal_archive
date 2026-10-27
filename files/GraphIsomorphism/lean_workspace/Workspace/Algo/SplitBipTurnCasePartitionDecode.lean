import Workspace.Algo.SplitBipTurnImpTransport

/-! Read a local case partition through its actual dictionary and first
list, then extend it on the parent first part. This equation preserves
all labels and blocks and is shared by the three case procedures.
-/
namespace Algo
open Babai RAM
open scoped Classical
namespace SbipNodeRep
variable {m : ℕ} {I : RawSbipNode} {X : Pt (BipBlockInputs (Fin m))}
    (h : SbipNodeRep m I X)
include h

theorem case_partition_named_decode {W : Set (Fin m)}
    (P : ColoredPartition ↥W ℕ) (hWV : W ⊆ BipBlockInputs.V₁ X) (q : RawColPart)
    (name : ↥W → ℕ) (eW : ↥W ≃ Fin (sbipTurnCase I.1).2.1.2.1.length)
    (heW : ∀ x,(sbipTurnCase I.1).2.1.2.1[(eW x).val] = name x)
    (hrow : ∀ x,sbipDictPoint (sbipGraphStep9Dictionary I.1.2,name x) = x.val.val)
    (hcover : ∀ a,a ∈ (sbipTurnCase I.1).2.1.2.1 ↔ ∃ x,name x = a)
    (hc : ∀ x,labAt q.1 (eW x) = P.color x)
    (hp : ∀ x y,cellOf q (eW x) = cellOf q (eW y) ↔ P.part x y) :
    sbipDecodeNamed m I.1.2.1.1.1.1
      (rawAlignPartition (sbipCasePartition (sbipTurnContext (sbipTurnCase I.1),q))) =
      some ⟨BipBlockInputs.V₁ X,Sum.inl (extendPartition (BipBlockInputs.V₁ X) W P)⟩ := by
  obtain ⟨e,he⟩ := h.point_equiv_exists
  let eV := (splitImageEquiv X.obj.1.1.V₁).trans e
  have heV (x : ↥(BipBlockInputs.V₁ X)) : I.1.2.1.1.1.1[(eV x).val] = x.val.val := he (wPt x)
  have hdec := sbipCasePartition_decode P (sbipTurnContext (sbipTurnCase I.1)) q
    Fin.val name eV heV eW heW hrow hcover
    (sbipGraphStep9Input_wf (sbipTurnGraphInput I.1)).left_nodup hWV
    (fun _ _ _ _ hh => Fin.ext hh) hc hp
  rw [h.decodeNamed_partition_graph e he]
  exact congrArg some (congrArg (fun Q : ColoredPartition ↥(BipBlockInputs.V₁ X) ℕ =>
    (⟨BipBlockInputs.V₁ X,Sum.inl Q⟩ : Pt (SplitOutcomes (Fin m)))) hdec)

end SbipNodeRep
end Algo
