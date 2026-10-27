import Workspace.Algo.TopMasterCameronMinimalLink
import Workspace.Algo.TopMasterHintWindowLink

/-! # The ambient Cameron subgroup has the computed numbered image
Computing the signed kernel before restricting the window yields exactly
the subgroup obtained by computing it in the numbered window. Surjectivity
of restriction proves both inclusions; no equality of generator lists is
assumed.
-/
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
namespace Algo
open RAM RAM.Targets Babai Equiv
open scoped Classical

 theorem masterAction_preim_range {Ω Λ Γ : Type*}
    {G K : Subgroup (Perm Ω)} {H : Subgroup (Perm Λ)}
    (ρ : G →* H) (hρ : Function.Surjective ρ) (φ : H →* Perm Γ)
    (N : Subgroup (Perm Γ)) (hKG : K ≤ G)
    (hK : K = preimSubgroup (φ.comp ρ) N)
    (R : K →* Perm Λ) (hR : ∀ g : K, R g = (ρ (Subgroup.inclusion hKG g)).val) :
    R.range = preimSubgroup φ N := by
  ext q
  constructor
  · rintro ⟨g, rfl⟩
    rw [hR]
    have hg := mem_preimSubgroup.mp (hK.le g.property)
    exact mem_preimSubgroup.mpr ⟨(ρ (Subgroup.inclusion hKG g)).property, hg.2⟩
  · intro hq
    obtain ⟨hqG, hqN⟩ := mem_preimSubgroup.mp hq
    obtain ⟨g, hg⟩ := hρ ⟨q, hqG⟩
    have hgK : g.val ∈ K := by
      rw [hK]
      exact mem_preimSubgroup.mpr ⟨g.property, by change φ (ρ g) ∈ N; rw [hg]; exact hqN⟩
    refine ⟨⟨g.val, hgK⟩, ?_⟩
    rw [hR]
    exact congrArg Subtype.val hg

section Window
variable {n : ℕ} {W : RawWinSI}
    (hx : W.2.2.2.1.length = n) (hw : RawGens.WF n W.2.1)
    (hnd : W.1.Nodup) (hlt : ∀ u ∈ W.1, u < n)
    (hinv : IsInvariant (decGroup n W.2.1) (winSet n W.1))
    (htr : IsTransitive (decGroup W.1.length (primitiveWindowInput W).1)) (hn : 2 ≤ W.1.length)
    {c : RawCameron} (h : c.WF (rawMinBlocks ((primitiveWindowInput W).1, W.1)).length)
    (hhi : (decGroup (rawMinBlocks ((primitiveWindowInput W).1, W.1)).length
      (masterWindowBlockAction W).2.2).map (permCongrHom (decCameron c h)).toMonoidHom ≤
        wreathProduct (JohnsonS c.k c.t) c.s)

include hx hw hnd hlt hinv htr hn h hhi in
 theorem masterCameronChild_minimal_group (j : ℕ) :
    decGroup W.1.length (masterHintTop (masterCameronChildInput ((c, masterWindowBlockInput W), j))).1.1.2 =
      decGroup W.1.length (camLiftGens (c, camMinimalAction ((primitiveWindowInput W).1, W.1))) := by
  let hr := masterRestrictionAction_wf hx hw hnd hlt hinv
  let ha := masterWindowBlockAction_wf hx hw hnd hlt hinv htr hn
  let hq := camMinimalAction_wf (dom := W.1) (rawRestrictGens_wf_of_raw (dom := W.2.2.2.1) hw hnd hlt hinv)
    rfl htr hn
  have hi := isInvariant_of_le hinv (camLiftGens_le (p := masterWindowBlockAction W) ha h hhi)
  change decGroup W.1.length
    (rawRestrictGens ((W.2.2.2.1, camLiftGens (c, masterWindowBlockAction W)), W.1)) = _
  rw [decGroup_rawRestrictGens_of_raw (camLiftGens_wf (p := masterWindowBlockAction W) ha) hnd hlt hi, camLiftGens_spec (p := camMinimalAction ((primitiveWindowInput W).1, W.1)) hq h hhi]
  exact masterAction_preim_range (camActionRange hr) (camActionRange_surjective hr)
    (camMinimalHom (dom := W.1) (rawRestrictGens_wf_of_raw (dom := W.2.2.2.1) hw hnd hlt hinv) rfl htr hn)
    (camNbar c h) (camLiftGens_le (p := masterWindowBlockAction W) ha h hhi) (camLiftGens_spec (p := masterWindowBlockAction W) ha h hhi)
    (winRestrictHom n W.1 hnd hlt _ hi) (fun _ => rfl)

noncomputable def masterCameronChildHom (j : ℕ) :
    decGroup W.1.length (masterHintTop (masterCameronChildInput ((c, masterWindowBlockInput W), j))).1.1.2 →*
      Perm (Fin c.k) :=
  (camLiftGiantHom (camMinimalAction_wf (dom := W.1) (rawRestrictGens_wf_of_raw (dom := W.2.2.2.1)
    hw hnd hlt hinv) rfl htr hn) h hhi).comp
      (MulEquiv.subgroupCongr (masterCameronChild_minimal_group hx hw hnd hlt hinv htr hn h hhi j)).toMonoidHom

noncomputable def masterCameronRestrictedGenerator (j : ℕ) (r : RawPerm)
    (hr : r ∈ camLiftGens (c, masterWindowBlockAction W)) :
    decGroup W.1.length (masterHintTop (masterCameronChildInput ((c, masterWindowBlockInput W), j))).1.1.2 := by
  refine ⟨decPerm W.1.length (rawRestrictPerm (W.1, r)), Subgroup.subset_closure ?_⟩
  exact List.mem_map_of_mem (List.mem_map_of_mem hr)

 theorem masterCameronChild_image (j : ℕ) {r : RawPerm}
    (hr : r ∈ camLiftGens (c, masterWindowBlockAction W)) :
    camLiftImage ((c, masterWindowBlockAction W), r) =
      encPerm c.k (masterCameronChildHom hx hw hnd hlt hinv htr hn h hhi j
        (masterCameronRestrictedGenerator j r hr)) := by
  let ha := masterWindowBlockAction_wf hx hw hnd hlt hinv htr hn
  let hrw := rawRestrictGens_wf_of_raw (dom := W.2.2.2.1) hw hnd hlt hinv
  rw [camLiftImage_spec (p := masterWindowBlockAction W) ha h hhi hr]
  apply congrArg (encPerm c.k)
  apply congrArg (camNbarPointHom h)
  apply Subtype.ext
  change camMinimalHom (dom := W.1) hrw rfl htr hn _ = camMinimalHom (dom := W.1) hrw rfl htr hn _
  apply congrArg (camMinimalHom (dom := W.1) hrw rfl htr hn)
  apply Subtype.ext
  change winRestrictHom n W.1 hnd hlt (decGroup n W.2.1) hinv _ =
    decPerm W.1.length (rawRestrictPerm (W.1, r))
  have hg := camLiftGens_le (p := masterWindowBlockAction W) ha h hhi (Subgroup.subset_closure (List.mem_map_of_mem hr))
  have he := rawRestrictPerm_spec hnd hlt hinv hg
  rw [encPerm_decPerm (camLiftGens_wf (p := masterWindowBlockAction W) ha r hr)] at he
  rw [he, decPerm_encPerm]
  rfl

 theorem masterCameronChild_rows_wf (j : ℕ) :
    RawAction.WF W.1.length c.k
      (masterHintTop (masterCameronChildInput ((c, masterWindowBlockInput W), j))).1
      (masterCameronChildHom hx hw hnd hlt hinv htr hn h hhi j) := by
  let ha := masterWindowBlockAction_wf hx hw hnd hlt hinv htr hn
  have hf := camLiftAction_wf (p := masterWindowBlockAction W) ha h hhi
  have hi := isInvariant_of_le hinv (camLiftGens_le (p := masterWindowBlockAction W) ha h hhi)
  refine ⟨rfl, hf.2.1, rawRestrictGens_wf_of_raw (camLiftGens_wf (p := masterWindowBlockAction W) ha) hnd hlt hi,
    hf.2.2.2.1, ?_, ?_⟩
  · simpa only [masterCameronChild_action, topwAction, rawRestrictGens, List.length_map]
      using hf.2.2.2.2.1
  · intro i hi hj
    have hig : i < (camLiftGens (c, masterWindowBlockAction W)).length := by
      simpa only [masterCameronChild_action, topwAction, rawRestrictGens, List.length_map] using hi
    simp only [masterCameronChild_action, topwAction, camLiftAction, camLiftImages,
      rawRestrictGens, List.getElem_map]
    exact (congrArg (decPerm c.k)
      (masterCameronChild_image hx hw hnd hlt hinv htr hn h hhi j (List.getElem_mem hig))).trans
      (decPerm_encPerm _ _)

end Window
end Algo
