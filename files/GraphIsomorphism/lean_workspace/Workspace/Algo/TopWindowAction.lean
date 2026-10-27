import Workspace.Algo.TopFourEntry

/-! # Supplying the restricted top action to the raw top-action round
The two generator lists remain aligned when the domain action is restricted
to the invariant window. The target action is unchanged because it factors
through that restriction. This is the representation passage used in §12.
-/
set_option synthInstance.maxSize 2048
namespace Algo
open RAM RAM.Targets Babai Equiv

noncomputable def topwGroupEquiv {n : ℕ} (Δ : List ℕ) (hnd : Δ.Nodup)
    (hlt : ∀ u ∈ Δ, u < n) (G : Subgroup (Perm (Fin n))) (hinv : IsInvariant G (winSet n Δ)) :
    (winRestrictHom n Δ hnd hlt G hinv).range ≃* restrictTo G (winSet n Δ) hinv :=
  (MulEquiv.subgroupCongr (range_winRestrictHom Δ hnd hlt G hinv)).trans
    (((winEquiv n Δ hnd hlt).symm.permCongrHom).subgroupMap (restrictTo G (winSet n Δ) hinv)).symm

 theorem topwGroupEquiv_coe {n : ℕ} {Δ : List ℕ} (hnd : Δ.Nodup)
    (hlt : ∀ u ∈ Δ, u < n) {G : Subgroup (Perm (Fin n))} (hinv : IsInvariant G (winSet n Δ))
    (g : (winRestrictHom n Δ hnd hlt G hinv).range) :
    (topwGroupEquiv Δ hnd hlt G hinv g : Perm (winSet n Δ)) =
      (winEquiv n Δ hnd hlt).permCongr (g : Perm (Fin Δ.length)) := rfl

 theorem topwGroupEquiv_restrict {n : ℕ} {Δ : List ℕ} (hnd : Δ.Nodup)
    (hlt : ∀ u ∈ Δ, u < n) {G : Subgroup (Perm (Fin n))} (hinv : IsInvariant G (winSet n Δ)) (g : G) :
    topwGroupEquiv Δ hnd hlt G hinv ⟨winRestrictHom n Δ hnd hlt G hinv g, ⟨g, rfl⟩⟩ =
      ⟨restrictHom G (winSet n Δ) hinv g, ⟨g, rfl⟩⟩ := by
  apply Subtype.ext
  rw [topwGroupEquiv_coe]
  change (winEquiv n Δ hnd hlt).permCongr
    ((winEquiv n Δ hnd hlt).symm.permCongr _) = _
  rw [← Equiv.permCongr_symm, Equiv.apply_symm_apply]

noncomputable def topwInducedHom {n m : ℕ} {Δ : List ℕ} (hnd : Δ.Nodup)
    (hlt : ∀ u ∈ Δ, u < n) {G : Subgroup (Perm (Fin n))} (hinv : IsInvariant G (winSet n Δ))
    (ϕ : restrictTo G (winSet n Δ) hinv →* Perm (Fin m)) :
    (winRestrictHom n Δ hnd hlt G hinv).range →* Perm (Fin m) :=
  ϕ.comp (topwGroupEquiv Δ hnd hlt G hinv).toMonoidHom

 theorem topwInducedHom_giant {n m : ℕ} {Δ : List ℕ} (hnd : Δ.Nodup)
    (hlt : ∀ u ∈ Δ, u < n) {G : Subgroup (Perm (Fin n))} (hinv : IsInvariant G (winSet n Δ))
    (ϕ : restrictTo G (winSet n Δ) hinv →* Perm (Fin m)) (hϕ : IsGiantRep ϕ) :
    IsGiantRep (topwInducedHom hnd hlt hinv ϕ) := by
  intro σ hσ
  obtain ⟨g, hg⟩ := hϕ hσ
  exact ⟨(topwGroupEquiv Δ hnd hlt G hinv).symm g, by
    simp only [topwInducedHom, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply, hg]⟩

/-- Restrict the source permutations and keep their images in the same order. -/
def topwAction (p : RawAction × List ℕ) : RawAction :=
  ((p.2, rawRestrictGens (p.1.1, p.2)), p.1.2)

 theorem polyFun_topwAction : PolyFun topwAction :=
  (polyFun_snd.pair (((polyFun_fst.comp polyFun_fst).pair polyFun_snd).comp polyFun_rawRestrictGens)).pair
    (polyFun_fst.comp polyFun_snd)

noncomputable def topwActionHom {n m : ℕ} {dom Δ : List ℕ} {gens : List (Perm (Fin n))}
    (hnd : Δ.Nodup) (hlt : ∀ u ∈ Δ, u < n) (hinv : IsInvariant (genGroup gens) (winSet n Δ))
    (ϕ : restrictTo (genGroup gens) (winSet n Δ) hinv →* Perm (Fin m)) :
    decGroup Δ.length (rawRestrictGens ((dom, gens.map (encPerm n)), Δ)) →* Perm (Fin m) :=
  (topwInducedHom hnd hlt hinv ϕ).comp
    (Subgroup.inclusion (le_of_eq (decGroup_rawRestrictGens hnd hlt dom gens hinv)))

 theorem topwActionHom_giant {n m : ℕ} {dom Δ : List ℕ} {gens : List (Perm (Fin n))}
    (hnd : Δ.Nodup) (hlt : ∀ u ∈ Δ, u < n) (hinv : IsInvariant (genGroup gens) (winSet n Δ))
    (ϕ : restrictTo (genGroup gens) (winSet n Δ) hinv →* Perm (Fin m)) (hϕ : IsGiantRep ϕ) :
    IsGiantRep (topwActionHom (dom := dom) hnd hlt hinv ϕ) := by
  intro σ hσ
  obtain ⟨g, hg⟩ := topwInducedHom_giant hnd hlt hinv ϕ hϕ hσ
  refine ⟨⟨g, ?_⟩, hg⟩
  rw [decGroup_rawRestrictGens hnd hlt dom gens hinv]
  exact g.2

 theorem topwAction_WF {n m : ℕ} {dom gdom Δ : List ℕ} {gens : List (Perm (Fin n))}
    {imgs : List (Perm (Fin m))} {ψ : genGroup gens →* Perm (Fin m)}
    (hg : gdom.length = m) (hI : ImgsOf gens imgs ψ)
    (hnd : Δ.Nodup) (hlt : ∀ u ∈ Δ, u < n) (hinv : IsInvariant (genGroup gens) (winSet n Δ))
    (ϕ : restrictTo (genGroup gens) (winSet n Δ) hinv →* Perm (Fin m))
    (hfactor : ∀ g : genGroup gens, ψ g = ϕ ⟨restrictHom (genGroup gens) (winSet n Δ) hinv g, ⟨g, rfl⟩⟩) :
    RawAction.WF Δ.length m
      (topwAction (((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m))), Δ))
      (topwActionHom hnd hlt hinv ϕ) := by
  refine ⟨rfl, hg, ?_, wf_map_encPerm m imgs, ?_, ?_⟩
  · intro r hr
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp ha
    rw [rawRestrictPerm_spec hnd hlt hinv (Subgroup.subset_closure hg)]
    exact wf_encPerm _ _
  · simpa only [topwAction, rawRestrictGens, List.length_map] using hI.1
  · intro i hi hi'
    have higen : i < gens.length := by simpa only [topwAction, rawRestrictGens, List.length_map] using hi
    have hiimgs : i < imgs.length := by simpa only [topwAction, List.length_map] using hi'
    have hv := (hI.2 i higen hiimgs).trans (hfactor ⟨gens[i], Subgroup.subset_closure (List.getElem_mem higen)⟩)
    simp only [topwAction, rawRestrictGens, List.getElem_map, decPerm_encPerm]
    unfold topwActionHom
    change imgs[i] = topwInducedHom hnd hlt hinv ϕ ⟨decPerm Δ.length
      (rawRestrictPerm (Δ, encPerm n gens[i])), _⟩
    rw [hv]
    apply congrArg ϕ
    apply Subtype.ext
    change restrictHom (genGroup gens) (winSet n Δ) hinv _ =
      (winEquiv n Δ hnd hlt).permCongr (decPerm Δ.length (rawRestrictPerm (Δ, encPerm n gens[i])))
    rw [rawRestrictPerm_spec hnd hlt hinv (Subgroup.subset_closure (List.getElem_mem higen)), decPerm_encPerm]
    exact (congrArg Subtype.val (topwGroupEquiv_restrict hnd hlt hinv
      ⟨gens[i], Subgroup.subset_closure (List.getElem_mem higen)⟩)).symm

/-- The same bridge accepts arbitrary well-formed raw action arrays. -/
 theorem topwAction_WF_raw {n m : ℕ} {p : RawAction}
    {ψ : decGroup n p.1.2 →* Perm (Fin m)} (hp : RawAction.WF n m p ψ)
    {Δ : List ℕ} (hnd : Δ.Nodup) (hlt : ∀ u ∈ Δ, u < n)
    (hinv : IsInvariant (decGroup n p.1.2) (winSet n Δ))
    (ϕ : restrictTo (decGroup n p.1.2) (winSet n Δ) hinv →* Perm (Fin m))
    (hϕ : IsGiantRep ϕ)
    (hfactor : ∀ g : decGroup n p.1.2, ψ g = ϕ ⟨restrictHom (decGroup n p.1.2) (winSet n Δ) hinv g, ⟨g, rfl⟩⟩) :
    ∃ ρ : decGroup Δ.length (topwAction (p, Δ)).1.2 →* Perm (Fin m),
      RawAction.WF Δ.length m (topwAction (p, Δ)) ρ ∧ IsGiantRep ρ := by
  let gs := p.1.2.map (decPerm n)
  let ims := p.2.2.map (decPerm m)
  have he : ((p.1.1, gs.map (encPerm n)), (p.2.1, ims.map (encPerm m))) = p := by
    rw [map_encPerm_decPerm hp.2.2.1, map_encPerm_decPerm hp.2.2.2.1]
  have hw := topwAction_WF (dom := p.1.1) hp.2.1 hp.2.2.2.2 hnd hlt hinv ϕ hfactor
  have hg := topwActionHom_giant (dom := p.1.1) hnd hlt hinv ϕ hϕ
  have hh : ∃ ρ : decGroup Δ.length
      (topwAction (((p.1.1, gs.map (encPerm n)), (p.2.1, ims.map (encPerm m))), Δ)).1.2 →* Perm (Fin m),
      RawAction.WF Δ.length m (topwAction (((p.1.1, gs.map (encPerm n)),
        (p.2.1, ims.map (encPerm m))), Δ)) ρ ∧ IsGiantRep ρ :=
    ⟨topwActionHom hnd hlt hinv ϕ, hw, hg⟩
  have hprop := congrArg (fun q : RawAction => ∃ ρ : decGroup Δ.length (topwAction (q, Δ)).1.2 →* Perm (Fin m),
    RawAction.WF Δ.length m (topwAction (q, Δ)) ρ ∧ IsGiantRep ρ) he
  exact hprop.mp hh

end Algo
