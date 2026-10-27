import Workspace.Algo.SplitBipTurnEarlyTransport

/-! Connect the mathematical first-part decoder to the single named
outcome decoder. The list order is read from the stored point names,
so the equality introduces no choice of a new numbering.
-/
namespace Algo
open Babai RAM
open scoped Classical

private theorem partitionPoint_eq {Ω : Type} {S T : Set Ω}
    (e : ↥S ≃ ↥T) (h : S = T) (he : ∀ x,(e x).val = x.val)
    (P : ColoredPartition ↥S ℕ) (Q : ColoredPartition ↥T ℕ)
    (hP : P.pushforward e = Q) :
    (⟨S,Sum.inl P⟩ : Pt (SplitOutcomes Ω)) = ⟨T,Sum.inl Q⟩ := by
  subst T
  have he' : e = Equiv.refl ↥S := Equiv.ext (fun x => Subtype.ext (he x))
  subst e
  have hp : P = Q := by
    rw [← hP]
    apply ColoredPartition.ext <;> rfl
  subst Q
  rfl

namespace SbipNodeRep
variable {m : ℕ} {I : RawSbipNode} {X : Pt (BipBlockInputs (Fin m))}
    (h : SbipNodeRep m I X)
include h

theorem point_equiv_exists :
    ∃ e : ↥X.obj.1.1.V₁ ≃ Fin I.1.2.1.1.1.1.length,
      ∀ x,I.1.2.1.1.1.1[(e x).val] = x.val.val.val := by
  exact splitNameEquiv_exists (fun x : ↥X.obj.1.1.V₁ => x.val.val.val)
    (fun x y he => Subtype.ext (Subtype.ext (Fin.ext he))) _ h.left_nodup h.point_cover

theorem namedPartition_eq_graph
    (e : ↥X.obj.1.1.V₁ ≃ Fin I.1.2.1.1.1.1.length)
    (he : ∀ x,I.1.2.1.1.1.1[(e x).val] = x.val.val.val) (q : RawColPart) :
    sbipDecodeNamedPartition I.1.2.1.1.1.1 h.left_nodup h.point_lt q =
      (⟨BipBlockInputs.V₁ X,Sum.inl (sbipGraphDecodePartition X.obj.1.1 e q)⟩ :
        Pt (SplitOutcomes (Fin m))) := by
  let er := winEquiv m I.1.2.1.1.1.1 h.left_nodup h.point_lt
  let eg := ((splitImageEquiv X.obj.1.1.V₁).trans e).symm
  let f := er.symm.trans eg
  apply partitionPoint_eq f h.point_set
  · intro x
    apply Fin.ext
    have hr := winEquiv_symm_val I.1.2.1.1.1.1 h.left_nodup h.point_lt x
    rw [List.getD_eq_getElem _ _ (er.symm x).isLt] at hr
    have hg := he (e.symm (er.symm x))
    simp only [Equiv.apply_symm_apply] at hg
    exact hg.symm.trans hr
  · apply ColoredPartition.ext
    · funext x
      change labAt q.1 (er.symm (f.symm x)) = labAt q.1 (eg.symm x)
      simp [f]
    · apply Setoid.ext
      intro x y
      change cellOf q (er.symm (f.symm x)) = cellOf q (er.symm (f.symm y)) ↔
        cellOf q (eg.symm x) = cellOf q (eg.symm y)
      simp [f]

theorem decodeNamed_partition_graph
    (e : ↥X.obj.1.1.V₁ ≃ Fin I.1.2.1.1.1.1.length)
    (he : ∀ x,I.1.2.1.1.1.1[(e x).val] = x.val.val.val) (q : RawColPart) :
    sbipDecodeNamed m I.1.2.1.1.1.1 (rawAlignPartition q) =
      some ⟨BipBlockInputs.V₁ X,Sum.inl (sbipGraphDecodePartition X.obj.1.1 e q)⟩ := by
  rw [sbipDecodeNamed_partition _ h.left_nodup h.point_lt,h.namedPartition_eq_graph e he]

end SbipNodeRep
end Algo
