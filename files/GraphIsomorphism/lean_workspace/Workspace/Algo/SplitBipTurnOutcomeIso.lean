import Workspace.Algo.SplitBipTurnNamedPartition

/-! Isomorphism of actual named outcomes. The map on each returned
carrier must be the restriction of the given input isomorphism. This
also applies to Johnson carriers, which can be smaller than the first part.
-/
namespace Algo
open Babai RAM
open scoped Classical

def SbipNamedOutcomeIso {m : ℕ} (I J : RawSbipNode)
    (X Y : Pt (BipBlockInputs (Fin m))) (φ : ↥X.car ≃ ↥Y.car)
    (o o' : RawAlignOutcome) : Prop :=
  ∃ Z Z',sbipDecodeNamed m I.1.2.1.1.1.1 o = some Z ∧
    sbipDecodeNamed m J.1.2.1.1.1.1 o' = some Z' ∧
    ∃ (hZ : Z.car ⊆ X.car) (hZ' : Z'.car ⊆ Y.car),
      φ ∈ (Cat.sub (SplitOutcomes (Fin m))).Iso
        ⟨⟨Z.car,hZ⟩,Z.obj⟩ ⟨⟨Z'.car,hZ'⟩,Z'.obj⟩

namespace SbipNodeRep
variable {m : ℕ} {I J : RawSbipNode} {X Y : Pt (BipBlockInputs (Fin m))}
    (h : SbipNodeRep m I X) (h' : SbipNodeRep m J Y)
    (φ : ↥X.car ≃ ↥Y.car) (hφ : X.obj.1.1.IsIsoTo Y.obj.1.1 φ)
include h h' hφ

theorem namedOutcomeIso_partition
    (e : ↥X.obj.1.1.V₁ ≃ Fin I.1.2.1.1.1.1.length)
    (he : ∀ x,I.1.2.1.1.1.1[(e x).val] = x.val.val.val)
    (e' : ↥Y.obj.1.1.V₁ ≃ Fin J.1.2.1.1.1.1.length)
    (he' : ∀ x,J.1.2.1.1.1.1[(e' x).val] = x.val.val.val)
    (q q' : RawColPart)
    (hq : subEquiv φ (fun x => hφ.part₁ x) ∈ (ColoredPartitions (Fin m) ℕ).Iso
      (sbipGraphDecodePartition X.obj.1.1 e q)
      (sbipGraphDecodePartition Y.obj.1.1 e' q')) :
    SbipNamedOutcomeIso I J X Y φ (rawAlignPartition q) (rawAlignPartition q') := by
  refine ⟨_,_,h.decodeNamed_partition_graph e he q,
    h'.decodeNamed_partition_graph e' he' q',?_,?_,?_⟩
  · rintro _ ⟨x,_,rfl⟩
    exact x.property
  · rintro _ ⟨x,_,rfl⟩
    exact x.property
  · exact ⟨subEquiv φ (fun x => hφ.part₁ x),fun _ => rfl,hq⟩

theorem early1_named_transport {c : ℕ}
    (hα : BipBlockInputs.alpha X = BipBlockInputs.alpha Y)
    (hs : sbipGraphSmall1 c I.1.2.1.1 = true)
    (q : RawColPart) (hq : q ∈ sbipGraphEarly1 c (sbipTurnGraphInput I.1)) :
    ∃ q' ∈ sbipGraphEarly1 c (sbipTurnGraphInput J.1),
      SbipNamedOutcomeIso I J X Y φ (rawAlignPartition q) (rawAlignPartition q') := by
  obtain ⟨e,he⟩ := h.point_equiv_exists
  obtain ⟨e',he'⟩ := h'.point_equiv_exists
  obtain ⟨q',hq',hiso⟩ := sbipGraphEarly1_transport X Y (sbipTurnGraphInput I.1)
    (sbipTurnGraphInput J.1) e e' h.alpha h'.alpha φ hφ hα
    (by simpa only [sbipGraphSmall1,decide_eq_true_eq] using hs) q hq
  exact ⟨q',hq',h.namedOutcomeIso_partition h' φ hφ e he e' he' q q' hiso⟩

theorem early2_named_transport {c : ℕ}
    (hs : sbipGraphSmall2 c I.1.2.1.1 = true)
    (q : RawColPart) (hq : q ∈ sbipGraphEarly2 (c+1) I.1.2.1.1) :
    ∃ q' ∈ sbipGraphEarly2 (c+1) J.1.2.1.1,
      SbipNamedOutcomeIso I J X Y φ (rawAlignPartition q) (rawAlignPartition q') := by
  obtain ⟨name,v,hc,hd,hf,hnd,hv,hp,hr⟩ := h.names
  obtain ⟨name',v',hc',hd',hf',hnd',hv',hp',hr'⟩ := h'.names
  obtain ⟨e,he⟩ := sbipGraphEarly_point_equiv_exists X I.1.2.1.1 name hc hp h.left_nodup
  obtain ⟨eB,heB⟩ := sbipGraphEarly_block_equiv_exists X I.1.2.1.1 name hc hr h.right_nodup
  obtain ⟨e',he'⟩ := sbipGraphEarly_point_equiv_exists Y J.1.2.1.1 name' hc' hp' h'.left_nodup
  obtain ⟨eB',heB'⟩ := sbipGraphEarly_block_equiv_exists Y J.1.2.1.1 name' hc' hr' h'.right_nodup
  obtain ⟨q',hq',hiso⟩ := sbipGraphEarly2_transport X Y I.1.2.1.1 J.1.2.1.1 name name'
    hc hc' h.left_nodup h.right_nodup h'.left_nodup h'.right_nodup e eB e' eB'
    he heB he' heB' φ hφ
    (by simpa only [sbipGraphSmall2,decide_eq_true_eq] using hs) q hq
  exact ⟨q',hq',h.namedOutcomeIso_partition h' φ hφ e
    (fun x => (he x).trans (hd.point_name x.val x.property)) e'
    (fun x => (he' x).trans (hd'.point_name x.val x.property)) q q' hiso⟩

theorem early4_named_transport :
    SbipNamedOutcomeIso I J X Y φ
      (rawAlignPartition (sbipGraphEarly4 (sbipTurnGraphInput I.1)))
      (rawAlignPartition (sbipGraphEarly4 (sbipTurnGraphInput J.1))) := by
  obtain ⟨name,v,hc,hd,hf,hnd,hv,hp,hr⟩ := h.names
  obtain ⟨name',v',hc',hd',hf',hnd',hv',hp',hr'⟩ := h'.names
  obtain ⟨e,he,hq⟩ := sbipGraphEarly4_decode X (sbipTurnGraphInput I.1) name hc hnd v hv hp
    h.alpha h.left_nodup
  obtain ⟨e',he',hq'⟩ := sbipGraphEarly4_decode Y (sbipTurnGraphInput J.1) name' hc' hnd' v' hv' hp'
    h'.alpha h'.left_nodup
  apply h.namedOutcomeIso_partition h' φ hφ e
    (fun x => (he x).trans (hd.point_name x.val x.property)) e'
    (fun x => (he' x).trans (hd'.point_name x.val x.property))
  dsimp only [sbipTurnGraphInput] at hq hq' ⊢
  rw [hq,hq']
  exact kerPartition_mem_iso φ (fun x => hφ.part₁ x) (VColBipBlk.wlDiag_map hφ)

end SbipNodeRep
end Algo
