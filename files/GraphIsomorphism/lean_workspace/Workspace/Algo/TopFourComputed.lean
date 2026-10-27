import Workspace.Algo.TopFourLabels

/-! # The live top-action record supplied by the raw computation
`Top4Source` packages the hypotheses of Corollary 12.0.10 and an encoded
action. Its derived record reads the generator pair, orbit order, odd lift,
class labels, and remaining windows computed by `top4InputContext`.
-/
set_option maxHeartbeats 2000000
set_option synthInstance.maxSize 2048
namespace Algo
open RAM RAM.Targets Babai Equiv
open scoped Classical

structure Top4Source (n m : ℕ) where
  dom : List ℕ
  gdom : List ℕ
  gens : List (Perm (Fin n))
  imgs : List (Perm (Fin m))
  hom : genGroup gens →* Perm (Fin m)
  dom_length : dom.length = n
  gdom_length : gdom.length = m
  images : ImgsOf gens imgs hom
  transitive : IsTransitive (genGroup gens)
  giant : IsGiantRep hom
  large : VeryLargeK m (maxOrbitLength (genGroup gens))
  color : List ℕ
  color_nodup : color.Nodup
  color_lt : ∀ u ∈ color, u < m
  color_large : m < 2 * (winSet m color).ncard

namespace Top4Source
variable {n m : ℕ} (F : Top4Source n m)

noncomputable def action : RawAction := ((F.dom, F.gens.map (encPerm n)), (F.gdom, F.imgs.map (encPerm m)))
noncomputable def stabilizer : RawAction := topRAction (F.action, F.color)
noncomputable def window : List ℕ := top4Omega (F.action, F.color)

theorem window_nodup : F.window.Nodup := top4Omega_nodup _
theorem window_lt : ∀ u ∈ F.window, u < n := fun u hu => by
  have h := top4Omega_lt (F.action, F.color) u hu
  change u < F.dom.length at h
  exact F.dom_length ▸ h

theorem group_eq : decGroup n F.stabilizer.1.2 = stabOn F.hom (winSet m F.color) :=
  decGroup_topRGens F.dom_length F.gdom_length F.images F.giant

theorem window_eq : winSet n F.window = omegaOf F.hom (winSet m F.color) :=
  top4Omega_spec F.dom_length F.gdom_length F.images F.giant F.large

theorem invariant : IsInvariant (decGroup n F.stabilizer.1.2) (winSet n F.window) := by
  rw [F.group_eq, F.window_eq]
  exact isInvariant_omegaOf_stabOn F.hom F.giant F.large _

noncomputable def classHom : decGroup n F.stabilizer.1.2 →* Perm (Fin (winSet m F.color).ncard) :=
  (((finCongr (ncard_winSet F.color F.color_nodup F.color_lt).symm).permCongrHom).toMonoidHom.comp
    (psiCFin F.hom F.color F.color_nodup F.color_lt)).comp (Subgroup.inclusion (le_of_eq F.group_eq))

theorem stabilizer_wf : RawAction.WF n (winSet m F.color).ncard F.stabilizer F.classHom := by
  exact (topRAction_WF F.dom_length F.gdom_length F.images F.giant F.color_nodup F.color_lt).castTarget
    (ncard_winSet F.color F.color_nodup F.color_lt).symm

noncomputable def paperHom := phiCFinWith F.transitive F.hom F.giant F.large (winSet m F.color)
  F.color_large (top4ClassLabel F.color F.color_nodup F.color_lt)

noncomputable def windowHom : restrictTo (decGroup n F.stabilizer.1.2) (winSet n F.window) F.invariant →*
    Perm (Fin (winSet m F.color).ncard) :=
  F.paperHom.comp (topwEqualGroups F.group_eq F.window_eq F.invariant
    (isInvariant_omegaOf_stabOn F.hom F.giant F.large (winSet m F.color))).toMonoidHom

theorem factor : ∀ g : decGroup n F.stabilizer.1.2, F.classHom g =
    F.windowHom ⟨restrictHom _ _ F.invariant g, ⟨g, rfl⟩⟩ :=
  top4Class_factor F.transitive F.hom F.giant F.large F.color F.color_large F.color_nodup F.color_lt
    _ F.group_eq _ F.window_eq F.invariant

theorem windowHom_giant : IsGiantRep F.windowHom := by
  have hg := isGiantRep_phiCFinWith F.transitive F.hom F.giant F.large (winSet m F.color)
    F.color_large (top4ClassLabel F.color F.color_nodup F.color_lt)
  intro σ hσ
  obtain ⟨g, hg⟩ := hg hσ
  exact ⟨(topwEqualGroups F.group_eq F.window_eq F.invariant
    (isInvariant_omegaOf_stabOn F.hom F.giant F.large _)).symm g, by
      simpa only [windowHom, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply] using hg⟩

noncomputable def innerHom := topwActionHomRaw F.stabilizer_wf.2.2.1 F.window_nodup F.window_lt
  F.invariant F.windowHom

theorem inner_wf : RawAction.WF F.window.length (winSet m F.color).ncard
    (topwAction (F.stabilizer, F.window)) F.innerHom :=
  topwAction_WF_exact F.stabilizer_wf F.window_nodup F.window_lt F.invariant F.windowHom F.factor

noncomputable def innerCompat := topwPreparedCompat F.stabilizer_wf.2.2.1 F.window_nodup F.window_lt F.invariant F.windowHom
noncomputable def outerCompat := topwCompatAs F.window_nodup F.window_lt F.group_eq F.window_eq F.invariant
  (isInvariant_omegaOf_stabOn F.hom F.giant F.large (winSet m F.color)) F.paperHom

noncomputable def data (hm3 : 3 ≤ (winSet m F.color).ncard) :
    TopAction4Data F.transitive F.hom F.giant F.large (winSet m F.color) F.color_large where
  label := top4ClassLabel F.color F.color_nodup F.color_lt
  generators := topAltGensTyped F.stabilizer.2.1 F.stabilizer_wf.2.1 hm3
  generators_length := (topAltGensTyped_spec F.stabilizer.2.1 F.stabilizer_wf.2.1 hm3).1
  generators_generate := (topAltGensTyped_spec F.stabilizer.2.1 F.stabilizer_wf.2.1 hm3).2
  odd := F.outerCompat.odd (F.innerCompat.odd (topcsOddChoice F.inner_wf))
  orbits := F.outerCompat.orbits (F.innerCompat.orbits (topcsActionOrbits F.inner_wf))
  windows := (top4Rest (F.action, F.color)).map (winSet n)
  windows_spec := by
    unfold action
    rw [top4Rest_spec F.dom_length F.gdom_length F.images F.transitive F.giant F.large F.color]

 theorem body_loop {c d e f : ℕ} (hm3 : 3 ≤ (winSet m F.color).ncard)
    (hcap : TopwpCap e f) (x y : RawStr) (α : RawPerm) (Cy : List ℕ) (solve : RawWinSI → RawCoset) :
    let C := top4InputContext (((F.action, x, y), F.color), α, Cy)
    LoopMatch (top4Round c d e f solve) (top4Decode n) (decCoset n) (C, none)
      (top4Width C) 0 (top4Init (C, none))
      (cosetTopAction4BodyWith F.transitive F.hom F.giant F.large (winSet m F.color) F.color_large
        (F.data hm3) (decStrN n x) (strAct (decStrN n y) (decPerm n α)⁻¹)) := by
  intro C
  have hpos : 0 < F.window.length := top4Omega_pos F.dom_length F.gdom_length F.images
    F.transitive F.giant F.large F.color_large
  have h := top4WindowContext_loop (c := c) (d := d) F.stabilizer_wf F.window_nodup F.window_lt
    F.invariant F.windowHom F.factor F.windowHom_giant hm3 hpos hcap x
    (top4aTarget (F.dom, α, y)) (top4Rest (F.action, F.color)) solve
  dsimp only [windowHom] at h
  rw [top4LiveBody_as F.window_nodup F.window_lt F.group_eq F.window_eq F.invariant
    (isInvariant_omegaOf_stabOn F.hom F.giant F.large (winSet m F.color)) F.paperHom] at h
  simp only [C, top4InputContext, top4aTarget_spec F.dom_length, cosetTopAction4BodyWith,
    data, action, stabilizer, window, paperHom, outerCompat, innerCompat, windowHom, innerHom] at h ⊢
  convert h using 1
  congr 1
  funext a
  cases a <;> rfl

end Top4Source
end Algo
