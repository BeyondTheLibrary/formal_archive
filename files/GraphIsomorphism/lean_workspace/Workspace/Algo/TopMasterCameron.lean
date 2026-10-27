import Workspace.Algo.CameronNbar
import Workspace.Algo.TopMasterRoute

/-! # Recovering the giant action from the Cameron table
The proof of Theorem 11.2.1 selects the alternating base group and its
first coordinate. The existing column-comparison routine recovers the
point permutation in that coordinate. We prove that the recovered rows
are the generator images of one giant homomorphism, in their original
order. No new recognition assumption is used.
-/
namespace Algo
open RAM RAM.Targets Babai Equiv

noncomputable def camBaseAsWreath {k t s : ℕ} :
    basePower (JohnsonA k t) s →* wreathProduct (JohnsonS k t) s :=
  Subgroup.inclusion (by
    rintro g ⟨q, hq, he⟩
    exact ⟨q, 1, fun i => johnsonA_le_johnsonS k t (hq i), he⟩)

theorem camBase_parts {k t s : ℕ} (ht : 1 ≤ t) (hk : t < k)
    (g : basePower (JohnsonA k t) s) :
    camWreathCoords (camBaseAsWreath g) = 1 ∧
      ∀ i, camWreathPoints (camBaseAsWreath g) i ∈ alternatingGroup (Fin k) := by
  have h := (camWreathSign_eq_one ht hk (camBaseAsWreath g)).mpr g.property
  exact (camSignedPerm_eq_one _ _).mp h

noncomputable def camBasePointHom {k t s : ℕ} (ht : 1 ≤ t) (hk : t < k) (i : Fin s) :
    basePower (JohnsonA k t) s →* Perm (Fin k) where
  toFun g := camWreathPoints (camBaseAsWreath g) i
  map_one' := by
    have he : (camBaseAsWreath (1 : basePower (JohnsonA k t) s)).val =
        wreathPerm (fun _ => tAction t (1 : Perm (Fin k))) 1 := by
      ext f j
      simp [camBaseAsWreath]
    exact congrFun (camWreath_parts ht hk _ he).1 i
  map_mul' g h := by
    have he : (camBaseAsWreath (g * h)).val = wreathPerm
        (fun j => tAction t (camWreathPoints (camBaseAsWreath g) j *
          camWreathPoints (camBaseAsWreath h) j)) 1 := by
      change (camBaseAsWreath g).val * (camBaseAsWreath h).val = _
      rw [camWreath_decomp (camBaseAsWreath g), camWreath_decomp (camBaseAsWreath h),
        (camBase_parts ht hk g).1, (camBase_parts ht hk h).1]
      ext f j
      simp [Perm.mul_apply]
    exact congrFun (camWreath_parts ht hk _ he).1 i

theorem camBasePointHom_giant {k t s : ℕ} (ht : 1 ≤ t) (hk : t < k) (i : Fin s) :
    alternatingGroup (Fin k) ≤ (camBasePointHom ht hk i).range := by
  intro a ha
  let w : basePower (JohnsonA k t) s :=
    ⟨wreathPerm (fun _ => tAction t a) 1, ⟨fun _ => tAction t a,
      fun _ => Subgroup.mem_map_of_mem _ ha, rfl⟩⟩
  refine ⟨w, ?_⟩
  exact congrFun (camWreath_parts ht hk (camBaseAsWreath w) rfl).1 i

noncomputable def camNbarIntoBase {n : ℕ} {c : RawCameron} (h : c.WF n) :
    camNbar c h →* basePower (JohnsonA c.k c.t) c.s :=
  (((decCameron c h).permCongrHom.toMonoidHom).comp (camNbar c h).subtype).codRestrict _
    (fun g => g.property)

theorem camNbarIntoBase_surjective {n : ℕ} {c : RawCameron} (h : c.WF n) :
    Function.Surjective (camNbarIntoBase h) := by
  intro w
  let g : Perm (Fin n) := (decCameron c h).permCongrHom.symm w
  have he : (decCameron c h).permCongrHom g = w :=
    (decCameron c h).permCongrHom.apply_symm_apply w
  refine ⟨⟨g, ?_⟩, ?_⟩
  · change (decCameron c h).permCongrHom g ∈ basePower (JohnsonA c.k c.t) c.s
    rw [he]
    exact w.property
  · exact Subtype.ext he

noncomputable def camNbarPointHom {n : ℕ} {c : RawCameron} (h : c.WF n) :
    camNbar c h →* Perm (Fin c.k) :=
  (camBasePointHom h.t_pos (by have := h.k_gt; omega) ⟨0, h.s_pos⟩).comp (camNbarIntoBase h)

theorem camNbarPointHom_giant {n : ℕ} {c : RawCameron} (h : c.WF n) :
    IsGiantRep (camNbarPointHom h) := by
  intro a ha
  obtain ⟨w, hw⟩ := camBasePointHom_giant h.t_pos (by have := h.k_gt; omega) ⟨0, h.s_pos⟩ ha
  obtain ⟨g, hg⟩ := camNbarIntoBase_surjective h w
  exact ⟨g, by
    change camBasePointHom h.t_pos (by have := h.k_gt; omega) ⟨0, h.s_pos⟩
      (camNbarIntoBase h g) = a
    rw [hg]
    exact hw⟩

theorem camPointPerm_first_spec {n : ℕ} {c : RawCameron} (h : c.WF n) (g : camNbar c h) :
    camPointPerm ((c, encPerm n g), 0) = encPerm c.k (camNbarPointHom h g) := by
  let w := camNbarIntoBase h g
  have he := camWreath_decomp (camBaseAsWreath w)
  rw [(camBase_parts h.t_pos (by have := h.k_gt; omega) w).1] at he
  have hh := camPointPerm_spec h g (camWreathPoints (camBaseAsWreath w)) 1 he ⟨0, h.s_pos⟩
  simpa only [Perm.one_apply] using hh

def camGiantImages (p : RawCameron × RawGens) : RawGens :=
  p.2.map (fun g => camPointPerm ((p.1, g), 0))
def camGiantAction (p : RawCameron × RawGens) : RawAction :=
  ((camDom p.1, p.2), (camPointDom p.1, camGiantImages p))

theorem polyFun_camGiantImages : PolyFun camGiantImages :=
  (polyFun_fst.pair polyFun_snd).comp
    (PolyFun.mapParam (((polyFun_id).pair (polyFun_const 0)).comp camPoly_pointPerm))
theorem polyFun_camGiantAction : PolyFun camGiantAction :=
  ((polyFun_fst.comp camPoly_dom).pair polyFun_snd).pair
    ((polyFun_fst.comp camPoly_pointDom).pair polyFun_camGiantImages)

noncomputable def camGiantHom {n : ℕ} {c : RawCameron} (h : c.WF n) {gs : RawGens}
    (hN : decGroup n gs = camNbar c h) : decGroup n gs →* Perm (Fin c.k) :=
  (camNbarPointHom h).comp (Subgroup.inclusion hN.le)

theorem camGiantHom_giant {n : ℕ} {c : RawCameron} (h : c.WF n) {gs : RawGens}
    (hN : decGroup n gs = camNbar c h) : IsGiantRep (camGiantHom h hN) := by
  intro a ha
  obtain ⟨g, hg⟩ := camNbarPointHom_giant h ha
  exact ⟨⟨g, hN.symm ▸ g.property⟩, hg⟩

theorem camGiantImages_row {n : ℕ} {c : RawCameron} (h : c.WF n) {gs : RawGens}
    (hgs : RawGens.WF n gs) (hN : decGroup n gs = camNbar c h) {r : RawPerm} (hr : r ∈ gs) :
    camPointPerm ((c, r), 0) = encPerm c.k
      (camGiantHom h hN ⟨decPerm n r, Subgroup.subset_closure (List.mem_map.mpr ⟨r, hr, rfl⟩)⟩) := by
  have hh := camPointPerm_first_spec h
    ⟨decPerm n r, hN ▸ Subgroup.subset_closure (List.mem_map.mpr ⟨r, hr, rfl⟩)⟩
  simpa only [encPerm_decPerm (hgs r hr)] using hh

theorem camGiantAction_wf {n : ℕ} {c : RawCameron} (h : c.WF n) {gs : RawGens}
    (hgs : RawGens.WF n gs) (hN : decGroup n gs = camNbar c h) :
    RawAction.WF n c.k (camGiantAction (c, gs)) (camGiantHom h hN) := by
  refine ⟨camDom_length h, by simp [camGiantAction, camPointDom_eq h], hgs, ?_, ?_, ?_⟩
  · intro r hr
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hr
    rw [camGiantImages_row h hgs hN hq]
    exact wf_encPerm _ _
  · simp [camGiantAction, camGiantImages]
  · intro i hi hi'
    have hig : i < gs.length := by simpa [camGiantAction] using hi
    simp only [camGiantAction, camGiantImages, List.getElem_map]
    rw [camGiantImages_row h hgs hN (List.getElem_mem hig), decPerm_encPerm]
    rfl

/-- The live action produced by the alternating-base descent. -/
def camNbarGiantAction (p : RawCameron × RawGens) : RawAction :=
  camGiantAction (p.1, rawNbar p)

def camNbarMasterHint (p : RawCameron × RawGens) : RawMasterHint :=
  ((camNbarGiantAction p).2, p.1.t)

theorem polyFun_camNbarGiantAction : PolyFun camNbarGiantAction :=
  (polyFun_fst.pair camPoly_rawNbar).comp polyFun_camGiantAction

theorem polyFun_camNbarMasterHint : PolyFun camNbarMasterHint :=
  (polyFun_camNbarGiantAction.comp polyFun_snd).pair (polyFun_fst.comp camPoly_t)

theorem camNbarGiantAction_spec {n : ℕ} {c : RawCameron} (h : c.WF n) {gs : RawGens}
    (hw : RawGens.WF n gs)
    (hlo : basePower (JohnsonA c.k c.t) c.s ≤
      (decGroup n gs).map (permCongrHom (decCameron c h)).toMonoidHom)
    (hhi : (decGroup n gs).map (permCongrHom (decCameron c h)).toMonoidHom ≤
      wreathProduct (JohnsonS c.k c.t) c.s) :
    ∃ ϕ : decGroup n (rawNbar (c, gs)) →* Perm (Fin c.k),
      RawAction.WF n c.k (camNbarGiantAction (c, gs)) ϕ ∧ IsGiantRep ϕ :=
  ⟨camGiantHom h (rawNbar_spec h hw hlo hhi),
    camGiantAction_wf h (rawNbar_wf h gs) (rawNbar_spec h hw hlo hhi),
    camGiantHom_giant h (rawNbar_spec h hw hlo hhi)⟩

end Algo
