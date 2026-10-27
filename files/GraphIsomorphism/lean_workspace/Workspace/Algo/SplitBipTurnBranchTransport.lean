import Workspace.Algo.SplitBipTurnComponentDecode

/-! The early branch decisions agree on isomorphic represented nodes.
The component exit also transports the exact extended partition. All
maps are the restrictions of the supplied input isomorphism.
-/
namespace Algo
open Babai RAM
open scoped Classical
namespace SbipNodeRep
variable {m : ℕ} {I J : RawSbipNode} {X Y : Pt (BipBlockInputs (Fin m))}
    (h : SbipNodeRep m I X) (h' : SbipNodeRep m J Y)
    (φ : ↥X.car ≃ ↥Y.car) (hφ : φ ∈ (BipBlockInputs (Fin m)).IsoP X Y)
include h h' hφ

theorem small_tests_transport (c : ℕ) :
    sbipGraphSmall1 c I.1.2.1.1 = sbipGraphSmall1 c J.1.2.1.1 ∧
    sbipGraphSmall2 c I.1.2.1.1 = sbipGraphSmall2 c J.1.2.1.1 := by
  obtain ⟨e,_⟩ := h.point_equiv_exists
  obtain ⟨e',_⟩ := h'.point_equiv_exists
  have hl : I.1.2.1.1.1.1.length = J.1.2.1.1.1.1.length := by
    rw [sbipGraphEarly_first_size X _ e,sbipGraphEarly_first_size Y _ e']
    exact BipBlockInputs.n₁_congr ⟨φ,hφ⟩
  have hr : I.1.2.1.1.1.2.1.length = J.1.2.1.1.1.2.1.length := by
    change sbipNodeBlocks I = sbipNodeBlocks J
    rw [h.block_count,h'.block_count]
    exact VColBipBlk.numBlocks_eq_of_isIsoTo hφ.2
  simp only [sbipGraphSmall1,sbipGraphSmall2,hl,hr,and_self]

theorem early4_test_transport :
    (sbipGraphSteps35 (sbipTurnGraphInput I.1)).2 = none ↔
      (sbipGraphSteps35 (sbipTurnGraphInput J.1)).2 = none := by
  obtain ⟨name,e,hc,hd,hf,hnd,he,hp,hr⟩ := h.names
  obtain ⟨name',e',hc',hd',hf',hnd',he',hp',hr'⟩ := h'.names
  rw [sbipGraphSteps35_exit_iff X (sbipTurnGraphInput I.1) name hc hnd e he hp
    h.alpha h.denominator h.left_nodup,
    sbipGraphSteps35_exit_iff Y (sbipTurnGraphInput J.1) name' hc' hnd' e' he' hp'
    h'.alpha h'.denominator h'.left_nodup]
  exact ⟨allClassesSmall_congr ⟨φ,hφ⟩,
    allClassesSmall_congr ⟨φ.symm,(BipBlockInputs (Fin m)).symm_mem hφ⟩⟩

theorem component_test_transport (hd : ¬ AllClassesSmall X) :
    sbipImprimitive (sbipGraphComponentTable (sbipTurnGraphInput I.1)) =
      sbipImprimitive (sbipGraphComponentTable (sbipTurnGraphInput J.1)) := by
  have hd' : ¬ AllClassesSmall Y := fun hh => hd
    (allClassesSmall_congr ⟨φ.symm,(BipBlockInputs (Fin m)).symm_mem hφ⟩ hh)
  obtain ⟨name,e,hc,hs,hf,hnd,he,hp,hr⟩ := h.names
  obtain ⟨name',e',hc',hs',hf',hnd',he',hp',hr'⟩ := h'.names
  apply Bool.eq_iff_iff.mpr
  rw [sbipGraphComponentTable_test X (sbipTurnGraphInput I.1) name hc hnd e he hp hr
    h.alpha h.denominator h.left_nodup hd,
    sbipGraphComponentTable_test Y (sbipTurnGraphInput J.1) name' hc' hnd' e' he' hp' hr'
    h'.alpha h'.denominator h'.left_nodup hd']
  exact ⟨step6Imprimitive_congr ⟨φ,hφ⟩,
    step6Imprimitive_congr ⟨φ.symm,(BipBlockInputs (Fin m)).symm_mem hφ⟩⟩

theorem component_named_transport (hd : ¬ AllClassesSmall X) :
    SbipNamedOutcomeIso I J X Y φ
      (rawAlignPartition (sbipGraphComponentPartition (sbipTurnGraphInput I.1)))
      (rawAlignPartition (sbipGraphComponentPartition (sbipTurnGraphInput J.1))) := by
  have hd' : ¬ AllClassesSmall Y := fun hh => hd
    (allClassesSmall_congr ⟨φ.symm,(BipBlockInputs (Fin m)).symm_mem hφ⟩ hh)
  obtain ⟨name,v,hc,hs,hf,hnd,hv,hp,hr⟩ := h.names
  obtain ⟨name',v',hc',hs',hf',hnd',hv',hp',hr'⟩ := h'.names
  obtain ⟨e,he,hq⟩ := sbipGraphComponentPartition_decode X name (sbipTurnGraphInput I.1)
    hc hnd v hv hp hr h.alpha h.denominator h.left_nodup hd
  obtain ⟨e',he',hq'⟩ := sbipGraphComponentPartition_decode Y name' (sbipTurnGraphInput J.1)
    hc' hnd' v' hv' hp' hr' h'.alpha h'.denominator h'.left_nodup hd'
  apply h.namedOutcomeIso_partition h' φ hφ.2 e
    (fun x => (he x).trans (hs.point_name x.val x.property)) e'
    (fun x => (he' x).trans (hs'.point_name x.val x.property))
  dsimp only [sbipTurnGraphInput] at hq hq' ⊢
  rw [hq,hq']
  have hW : ∀ x,φ x ∈ dominantClass Y ↔ x ∈ dominantClass X := by
    intro x
    rw [dominantClass_image hφ]
    exact ⟨fun ⟨y,hy,hyx⟩ => (φ.injective hyx) ▸ hy,fun hx => ⟨x,hx,rfl⟩⟩
  exact extendPartition.mem_iso (dominantClass_image_subset_V₁ X)
    (dominantClass_image_subset_V₁ Y) (subEquiv φ (fun x => hφ.2.part₁ x))
    (subEquiv φ hW) (fun _ => rfl)
    (compPartition_mem_iso φ hW (fun u v => step6Color_map hφ u v))

end SbipNodeRep
end Algo
