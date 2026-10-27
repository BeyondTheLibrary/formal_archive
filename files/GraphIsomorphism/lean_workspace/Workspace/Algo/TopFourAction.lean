import Workspace.Algo.TopWindowAction
import Workspace.Algo.AlignColorRaw

/-! # The induced giant action for top-action 4
The paper first forms the setwise stabilizer of the large color class and
then restricts its action to Ω(C). The generator images are kept aligned
through both steps. The factorization is proved from `phiC_restrictHom`.
-/
namespace Algo
open RAM RAM.Targets Babai Equiv

 theorem top4Action_factor {n m : ℕ} {gens : List (Perm (Fin n))}
    (hG : IsTransitive (genGroup gens)) (ϕ : genGroup gens →* Perm (Fin m))
    (hϕ : IsGiantRep ϕ) (hk : VeryLargeK m (maxOrbitLength (genGroup gens)))
    (C : List ℕ) (hC : m < 2 * (winSet m C).ncard) (hnd : C.Nodup) (hlt : ∀ u ∈ C, u < m)
    (H : Subgroup (Perm (Fin n))) (hH : H = stabOn ϕ (winSet m C))
    (W : Set (Fin n)) (hW : W = omegaOf ϕ (winSet m C)) (hinv : IsInvariant H W) :
    ∃ ψ : restrictTo H W hinv →* Perm (Fin C.length), IsGiantRep ψ ∧
      ∀ g : H, ((psiCFin ϕ C hnd hlt).comp (Subgroup.inclusion (le_of_eq hH))) g =
        ψ ⟨restrictHom H W hinv g, ⟨g, rfl⟩⟩ := by
  classical
  subst H
  subst W
  let ψ : restrictTo (stabOn ϕ (winSet m C)) (omegaOf ϕ (winSet m C)) hinv →* Perm (Fin C.length) :=
    ((winEquiv m C hnd hlt).symm.permCongrHom).toMonoidHom.comp
      (phiC hG ϕ hϕ hk (winSet m C) hC)
  refine ⟨ψ, ?_, ?_⟩
  · intro σ hσ
    have he : (winEquiv m C hnd hlt).permCongr σ ∈ alternatingGroup (winSet m C) := by
      rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_permCongr]
      exact hσ
    obtain ⟨g, hg⟩ := isGiantRep_phiC hG ϕ hϕ hk (winSet m C) hC he
    refine ⟨g, ?_⟩
    change (winEquiv m C hnd hlt).symm.permCongr
      (phiC hG ϕ hϕ hk (winSet m C) hC g) = σ
    rw [hg, ← Equiv.permCongr_symm, Equiv.symm_apply_apply]
  · intro g
    exact psiCFin_eq_phiC ϕ hG hϕ hk C hC hnd hlt g

/-- The two successive restriction routines used in §12. -/
def top4RestrictedAction (p : RawAction × List ℕ × List ℕ) : RawAction :=
  topwAction (topRAction (p.1, p.2.1), p.2.2)

theorem polyFun_top4RestrictedAction : PolyFun top4RestrictedAction :=
  ((((polyFun_fst.pair (polyFun_snd.comp polyFun_fst)).comp polyFun_topRAction).pair
    (polyFun_snd.comp polyFun_snd)).comp polyFun_topwAction)

 theorem top4RestrictedAction_WF {n m : ℕ} {dom gdom C Δ : List ℕ}
    {gens : List (Perm (Fin n))} {imgs : List (Perm (Fin m))} {ϕ : genGroup gens →* Perm (Fin m)}
    (hd : dom.length = n) (hg : gdom.length = m) (hI : ImgsOf gens imgs ϕ)
    (hG : IsTransitive (genGroup gens)) (hϕ : IsGiantRep ϕ)
    (hk : VeryLargeK m (maxOrbitLength (genGroup gens)))
    (hC : m < 2 * (winSet m C).ncard) (hnd : C.Nodup) (hlt : ∀ u ∈ C, u < m)
    (hΔnd : Δ.Nodup) (hΔlt : ∀ u ∈ Δ, u < n) (hΔ : winSet n Δ = omegaOf ϕ (winSet m C)) :
    let act : RawAction := ((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m)))
    ∃ ψ : decGroup Δ.length (top4RestrictedAction (act, C, Δ)).1.2 →* Perm (Fin C.length),
      RawAction.WF Δ.length C.length (top4RestrictedAction (act, C, Δ)) ψ ∧ IsGiantRep ψ := by
  intro act
  have hgroup := decGroup_topRGens (C := C) hd hg hI hϕ
  have hinv : IsInvariant (decGroup n (topRGens (act, C))) (winSet n Δ) := by
    rw [hgroup, hΔ]
    exact isInvariant_omegaOf_stabOn ϕ hϕ hk (winSet m C)
  obtain ⟨ψ, hψ, hfactor⟩ := top4Action_factor hG ϕ hϕ hk C hC hnd hlt
    (decGroup n (topRGens (act, C))) hgroup (winSet n Δ) hΔ hinv
  exact topwAction_WF_raw (topRAction_WF hd hg hI hϕ hnd hlt) hΔnd hΔlt hinv ψ hψ hfactor

/-- A two-color label for a supplied list of top-domain points. -/
def top4ClassLab (p : List ℕ × List ℕ) : RawLab :=
  (rawOne p.1).map (fun i => if i ∈ p.2 then 1 else 0)

theorem top4ClassLab_spec {m : ℕ} {dom C : List ℕ} (hd : dom.length = m) (i : Fin m) :
    labAt (top4ClassLab (dom, C)) i = 1 ↔ i.val ∈ C := by
  have hi : i.val < (rawOne dom).length := by simpa only [rawOne, List.length_range, hd] using i.isLt
  change ((rawOne dom).map (fun j => if j ∈ C then 1 else 0)).getD i.val 0 = 1 ↔ i.val ∈ C
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map] using hi)]
  simp only [List.getElem_map, rawOne, List.getElem_range]
  split <;> simp_all

theorem polyFun_top4ClassLab : PolyFun top4ClassLab := by
  have hstep : PolyFun (fun p : (List ℕ × List ℕ) × ℕ => if p.2 ∈ p.1.2 then 1 else 0) :=
    (PolyFun.ite ((polyFun_snd.pair (polyFun_fst.comp polyFun_snd)).comp polyFun_natListMem)
      (polyFun_const 1) (polyFun_const 0)).of_eq (fun _ => by simp)
  exact (polyFun_id.pair (polyFun_fst.comp polyFun_rawOne)).comp (PolyFun.mapParam hstep)

/-- The first window Ω(C), computed from the standard-block labels. -/
def top4Omega (p : RawAction × List ℕ) : List ℕ :=
  alignRDomWindow ((p.1, top4ClassLab (p.1.2.1, p.2)), 1)

theorem polyFun_top4Omega : PolyFun top4Omega :=
  (((polyFun_fst.pair ((((polyFun_fst.comp polyFun_snd).comp polyFun_fst).pair polyFun_snd).comp polyFun_top4ClassLab)).pair
    (polyFun_const 1)).comp polyFun_alignRDomWindow)

theorem top4Omega_nodup (p : RawAction × List ℕ) : (top4Omega p).Nodup := nodup_alignRDomWindow _
theorem top4Omega_lt (p : RawAction × List ℕ) : ∀ u ∈ top4Omega p, u < p.1.1.1.length :=
  fun _ hu => (mem_alignRDomWindow.mp hu).1

theorem top4Omega_spec {n m : ℕ} {dom gdom C : List ℕ}
    {gens : List (Perm (Fin n))} {imgs : List (Perm (Fin m))} {ϕ : genGroup gens →* Perm (Fin m)}
    (hd : dom.length = n) (hg : gdom.length = m) (hI : ImgsOf gens imgs ϕ)
    (hϕ : IsGiantRep ϕ) (hk : VeryLargeK m (maxOrbitLength (genGroup gens))) :
    winSet n (top4Omega (((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m))), C)) =
      omegaOf ϕ (winSet m C) := by
  rw [top4Omega, winSet_alignRDomWindow hd hg hI hϕ hk]
  congr 1
  ext i
  exact top4ClassLab_spec hg i

/-- The complete raw action preparation from the original action and class. -/
def top4InducedAction (p : RawAction × List ℕ) : RawAction :=
  top4RestrictedAction (p.1, p.2, top4Omega p)

theorem polyFun_top4InducedAction : PolyFun top4InducedAction :=
  (polyFun_fst.pair (polyFun_snd.pair polyFun_top4Omega)).comp polyFun_top4RestrictedAction

theorem top4InducedAction_WF {n m : ℕ} {dom gdom C : List ℕ}
    {gens : List (Perm (Fin n))} {imgs : List (Perm (Fin m))} {ϕ : genGroup gens →* Perm (Fin m)}
    (hd : dom.length = n) (hg : gdom.length = m) (hI : ImgsOf gens imgs ϕ)
    (hG : IsTransitive (genGroup gens)) (hϕ : IsGiantRep ϕ)
    (hk : VeryLargeK m (maxOrbitLength (genGroup gens)))
    (hC : m < 2 * (winSet m C).ncard) (hnd : C.Nodup) (hlt : ∀ u ∈ C, u < m) :
    let p : RawAction × List ℕ := (((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m))), C)
    ∃ ψ : decGroup (top4Omega p).length (top4InducedAction p).1.2 →* Perm (Fin C.length),
      RawAction.WF (top4Omega p).length C.length (top4InducedAction p) ψ ∧ IsGiantRep ψ := by
  intro p
  exact top4RestrictedAction_WF hd hg hI hG hϕ hk hC hnd hlt (top4Omega_nodup p)
    (fun u hu => by
      have hh := top4Omega_lt p u hu
      change u < dom.length at hh
      exact hd ▸ hh)
    (top4Omega_spec hd hg hI hϕ hk)

theorem top4Omega_length_le (p : RawAction × List ℕ) : (top4Omega p).length ≤ p.1.1.1.length := by
  exact (List.length_filter_le _ _).trans_eq List.length_range

theorem top4Omega_pos {n m : ℕ} {dom gdom C : List ℕ}
    {gens : List (Perm (Fin n))} {imgs : List (Perm (Fin m))} {ϕ : genGroup gens →* Perm (Fin m)}
    (hd : dom.length = n) (hg : gdom.length = m) (hI : ImgsOf gens imgs ϕ)
    (hG : IsTransitive (genGroup gens)) (hϕ : IsGiantRep ϕ)
    (hk : VeryLargeK m (maxOrbitLength (genGroup gens))) (hC : m < 2 * (winSet m C).ncard) :
    0 < (top4Omega (((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m))), C)).length := by
  obtain ⟨u, hu⟩ := nonempty_omegaOf hG ϕ hϕ hk (winSet m C) hC
  rw [← top4Omega_spec hd hg hI hϕ hk] at hu
  exact List.length_pos_of_mem hu

/-- The output-size polynomial is chosen before the original input degree. -/
theorem top4InducedAction_uniform_cap (C D : ℕ) : ∃ c d : ℕ, ∀ (n : ℕ) (p : RawAction × List ℕ),
    Enc.size p ≤ topcsContextCap C D n → Enc.size (top4InducedAction p) ≤ topcsContextCap c d n := by
  obtain ⟨F, hF, hmF, hsF⟩ := polyFun_top4InducedAction.size.exists_polyBound
  obtain ⟨c, d, hcd⟩ := hF.comp (polyBound_topcsContextCap C D)
  exact ⟨c, d, fun n p hp => (hsF p).trans ((hmF _ _ hp).trans (hcd n))⟩

end Algo
