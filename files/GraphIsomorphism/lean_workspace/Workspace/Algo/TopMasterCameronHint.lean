import Workspace.Algo.TopMasterCameronLift

/-! # The computed giant-action hint after Cameron descent
Every returned image is computed from a returned subgroup generator. The
specification proves the image assignment and its giant range. It does not
ask the caller to provide either the images or a matching homomorphism.
-/
namespace Algo
open RAM RAM.Targets Babai Equiv

def camLiftImage (q : (RawCameron × RawAction) × RawPerm) : RawPerm :=
  camPointPerm ((q.1.1, rawImgOf (q.1.2, q.2)), 0)

def camLiftImages (q : RawCameron × RawAction) : RawGens :=
  (camLiftGens q).map (fun g => camLiftImage (q, g))

def camLiftAction (q : RawCameron × RawAction) : RawAction :=
  ((q.2.1.1, camLiftGens q), (camPointDom q.1, camLiftImages q))

def camLiftHint (q : RawCameron × RawAction) : RawMasterHint :=
  ((camLiftAction q).2, q.1.t)

theorem polyFun_camLiftImage : PolyFun camLiftImage :=
  (((polyFun_fst.comp polyFun_fst).pair
    (((polyFun_fst.comp polyFun_snd).pair polyFun_snd).comp polyFun_rawImgOf)).pair
      (polyFun_const 0)).comp camPoly_pointPerm

theorem polyFun_camLiftImages : PolyFun camLiftImages :=
  (polyFun_id.pair polyFun_camLiftGens).comp (PolyFun.mapParam polyFun_camLiftImage)

theorem polyFun_camLiftAction : PolyFun camLiftAction :=
  (((polyFun_snd.comp polyFun_fst).comp polyFun_fst).pair polyFun_camLiftGens).pair
    ((polyFun_fst.comp camPoly_pointDom).pair polyFun_camLiftImages)

theorem polyFun_camLiftHint : PolyFun camLiftHint :=
  (polyFun_camLiftAction.comp polyFun_snd).pair (polyFun_fst.comp camPoly_t)

section Spec
variable {n m : ℕ} {p : RawAction} {c : RawCameron}
  {ϕ : decGroup n p.1.2 →* Perm (Fin m)}
  (hp : RawAction.WF n m p ϕ) (h : c.WF m)
  (hhi : (decGroup m p.2.2).map (permCongrHom (decCameron c h)).toMonoidHom ≤
    wreathProduct (JohnsonS c.k c.t) c.s)

theorem camLiftImage_spec {r : RawPerm} (hr : r ∈ camLiftGens (c, p)) :
    camLiftImage ((c, p), r) = encPerm c.k (camLiftGiantHom hp h hhi
      ⟨decPerm n r, Subgroup.subset_closure (List.mem_map_of_mem hr)⟩) := by
  have hrg : decPerm n r ∈ decGroup n p.1.2 :=
    camLiftGens_le hp h hhi (Subgroup.subset_closure (List.mem_map_of_mem hr))
  have hi := rawImgOf_spec hp.1 hp.2.1 hp.2.2.2.2 hrg
  rw [map_encPerm_decPerm hp.2.2.1, map_encPerm_decPerm hp.2.2.2.1,
    encPerm_decPerm (camLiftGens_wf hp r hr)] at hi
  change camPointPerm ((c, rawImgOf (p, r)), 0) = _
  rw [hi]
  exact camPointPerm_first_spec h (camLiftIntoNbar hp h hhi
    ⟨decPerm n r, Subgroup.subset_closure (List.mem_map_of_mem hr)⟩)

theorem camLiftAction_wf : RawAction.WF n c.k (camLiftAction (c, p))
    (camLiftGiantHom (p := p) hp h hhi) := by
  refine ⟨hp.1, by simp [camLiftAction, camPointDom_eq h], camLiftGens_wf hp, ?_, ?_, ?_⟩
  · intro r hr
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hr
    rw [camLiftImage_spec hp h hhi hg]
    exact wf_encPerm _ _
  · simp [camLiftAction, camLiftImages]
  · intro i hi hj
    have hg : i < (camLiftGens (c, p)).length := by simpa [camLiftAction] using hi
    simp only [camLiftAction, camLiftImages, List.getElem_map,
      camLiftImage_spec hp h hhi (List.getElem_mem hg), decPerm_encPerm]
    rfl

/-- One live action, including the exact subgroup and the recovered giant hint. -/
theorem camLiftAction_spec
    (hlo : basePower (JohnsonA c.k c.t) c.s ≤
      (decGroup m p.2.2).map (permCongrHom (decCameron c h)).toMonoidHom) :
    decGroup n (camLiftAction (c, p)).1.2 = camLiftSubgroup (ϕ := ϕ) h ∧
      RawAction.WF n c.k (camLiftAction (c, p)) (camLiftGiantHom (p := p) hp h hhi) ∧
      IsGiantRep (camLiftGiantHom hp h hhi) ∧
      (camLiftAction (c, p)).1.2.length ≤ n * n :=
  ⟨camLiftGens_spec hp h hhi, camLiftAction_wf hp h hhi,
    camLiftGiantHom_giant hp h hhi hlo, camLiftGens_length hp⟩
end Spec
end Algo
