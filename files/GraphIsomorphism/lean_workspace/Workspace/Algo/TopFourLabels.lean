import Workspace.Algo.TopFourInput

/-! # Identifying computed labels with the live top-action data
The raw target degree is the color-list length. The paper's degree is the
cardinality of the color class. Their equality transports the action, while
the displayed list equivalence supplies the label map in `TopAction4Data`.
-/
namespace Algo
open RAM RAM.Targets Babai Equiv
open scoped Classical

 theorem RawAction.WF.castTarget {n m m' : ℕ} {p : RawAction}
    {ϕ : decGroup n p.1.2 →* Perm (Fin m)} (hp : RawAction.WF n m p ϕ) (h : m = m') :
    RawAction.WF n m' p (((finCongr h).permCongrHom).toMonoidHom.comp ϕ) := by
  subst m'
  simpa using hp

noncomputable def topwEqualGroups {Ω : Type*} {H G : Subgroup (Perm Ω)}
    {W V : Set Ω} (hG : H = G) (hW : W = V)
    (hH : IsInvariant H W) (hV : IsInvariant G V) : restrictTo H W hH ≃* restrictTo G V hV := by
  subst G
  subst V
  exact MulEquiv.refl _

noncomputable def topwCompatAs {n m : ℕ} {Δ : List ℕ} (hnd : Δ.Nodup)
    (hlt : ∀ u ∈ Δ, u < n) {H G : Subgroup (Perm (Fin n))} {W : Set (Fin n)}
    (hG : H = G) (hW : winSet n Δ = W)
    (hH : IsInvariant H (winSet n Δ)) (hV : IsInvariant G W)
    (ϕ : restrictTo G W hV →* Perm (Fin m)) :
    TopdCompat ((winEquiv n Δ hnd hlt).trans (Equiv.setCongr hW))
      (topwInducedHom hnd hlt hH (ϕ.comp (topwEqualGroups hG hW hH hV).toMonoidHom)) ϕ where
  group := (topwGroupEquiv Δ hnd hlt H hH).trans (topwEqualGroups hG hW hH hV)
  coe := by
    subst G
    subst W
    intro g
    rfl
  hom := fun _ => rfl

 theorem top4LiveBody_as {n m : ℕ} {Δ : List ℕ} (hnd : Δ.Nodup)
    (hlt : ∀ u ∈ Δ, u < n) {H G : Subgroup (Perm (Fin n))} {W : Set (Fin n)}
    (hG : H = G) (hW : winSet n Δ = W)
    (hH : IsInvariant H (winSet n Δ)) (hV : IsInvariant G W)
    (ϕ : restrictTo G W hV →* Perm (Fin m)) (S : List (alternatingGroup (Fin m)))
    (O : TopActionOdd (topwInducedHom hnd hlt hH (ϕ.comp (topwEqualGroups hG hW hH hV).toMonoidHom)))
    (E : OrbitEnum (kerSubgroup (topwInducedHom hnd hlt hH (ϕ.comp (topwEqualGroups hG hW hH hV).toMonoidHom))))
    (x y : Fin n → ℕ) (rest : List (Set (Fin n))) :
    top4LiveBody hnd hlt hH (ϕ.comp (topwEqualGroups hG hW hH hV).toMonoidHom) S O E x y rest =
      (cosetWindowTopAction3With G W hV ϕ S ((topwCompatAs hnd hlt hG hW hH hV ϕ).odd O)
        ((topwCompatAs hnd hlt hG hW hH hV ϕ).orbits E) x y).bind
        (fun A => match A with | none => .done ∅ | some B => Babai.cosetChain x y rest B) := by
  subst G
  subst W
  rfl

 theorem top4Class_factor {n m : ℕ} {gens : List (Perm (Fin n))}
    (hG : IsTransitive (genGroup gens)) (ϕ : genGroup gens →* Perm (Fin m))
    (hϕ : IsGiantRep ϕ) (hk : VeryLargeK m (maxOrbitLength (genGroup gens)))
    (C : List ℕ) (hC : m < 2 * (winSet m C).ncard) (hnd : C.Nodup) (hlt : ∀ u ∈ C, u < m)
    (H : Subgroup (Perm (Fin n))) (hH : H = stabOn ϕ (winSet m C))
    (W : Set (Fin n)) (hW : W = omegaOf ϕ (winSet m C)) (hinv : IsInvariant H W) :
    let ψ := (((finCongr (ncard_winSet C hnd hlt).symm).permCongrHom).toMonoidHom.comp
      (psiCFin ϕ C hnd hlt)).comp (Subgroup.inclusion (le_of_eq hH))
    let ρ := (phiCFinWith hG ϕ hϕ hk (winSet m C) hC (top4ClassLabel C hnd hlt)).comp
      (topwEqualGroups hH hW hinv (isInvariant_omegaOf_stabOn ϕ hϕ hk (winSet m C))).toMonoidHom
    ∀ g : H, ψ g = ρ ⟨restrictHom H W hinv g, ⟨g, rfl⟩⟩ := by
  subst H
  subst W
  intro ψ ρ g
  change (finCongr (ncard_winSet C hnd hlt).symm).permCongr (psiCFin ϕ C hnd hlt g) =
    phiCFinWith hG ϕ hϕ hk (winSet m C) hC (top4ClassLabel C hnd hlt)
      ⟨restrictHom _ _ _ g, ⟨g, rfl⟩⟩
  rw [phiCFinWith_restrictHom, psiCFin_eq_psiC]
  rfl

end Algo
