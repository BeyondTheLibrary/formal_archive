import Workspace.Algo.TopFourAmbientMatch
import Workspace.Master.Sec15

/-! # The machine's window lift is the paper's window lift
Lines 4b, 4c–4d and 5–7 of Section 15 run a round on the window `Δ` and lift it to `Ω`
(`Babai.liftWindow`, the reduction of Sec. 2.2.3 to window instances). The paper's round lives
on the window as a subtype of `Ω`; the machine's lives on the positions `Fin |Δ|` of the
computed window list, and the machine lifts it by `Algo.top4wTree`. This file relabels a
round on the positions along the list equivalence `Algo.winEquiv` (`Algo.topwSubtypeRed`) and
proves that the machine's lift makes the same calls, in the same order, and returns the same
value as the paper's lift of the relabelled round (`Algo.top4wTree_calls_eq_liftWindow`,
`Algo.top4wTree_run_eq_liftWindow`).
-/
namespace Algo
open RAM RAM.Targets Babai Equiv
open scoped Pointwise

section Relabel
variable {n : ℕ} {Δ : List ℕ} (hnd : Δ.Nodup) (hlt : ∀ u ∈ Δ, u < n)

/-- Relabel a round on the window positions as a round on the window subtype. -/
noncomputable def topwSubtypeRed :
    SIReduction (Fin Δ.length) ℕ (Set (Perm (Fin Δ.length))) →
      SIReduction ↥(winSet n Δ) ℕ (Set (Perm ↥(winSet n Δ)))
  | .done b => .done ((winEquiv n Δ hnd hlt).permCongr '' b)
  | .call J k => .call (topwSubtypeInstance hnd hlt J)
      (fun a => topwSubtypeRed (k ((winEquiv n Δ hnd hlt).symm.permCongr '' a)))

/-- Relabelling a set of permutations and back gives the set. -/
theorem permCongr_symm_image (A : Set (Perm (Fin Δ.length))) :
    (winEquiv n Δ hnd hlt).symm.permCongr '' ((winEquiv n Δ hnd hlt).permCongr '' A) = A := by
  rw [Set.image_image]
  convert Set.image_id A
  ext σ i
  simp [Equiv.permCongr_apply]

/-- The relabelled instance has the relabelled answer. -/
theorem topwSubtypeInstance_answer (J : SIInstance (Fin Δ.length) ℕ) :
    (topwSubtypeInstance hnd hlt J).answer = (winEquiv n Δ hnd hlt).permCongr '' J.answer := by
  ext τ
  simp only [SIInstance.answer, wIso, topwSubtypeInstance, Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨⟨σ, hσ, rfl⟩, hw⟩
    refine ⟨σ, ⟨hσ, fun u hu => ?_⟩, rfl⟩
    have := hw (winEquiv n Δ hnd hlt u) ⟨u, hu, rfl⟩
    simpa [Equiv.permCongr_apply] using this
  · rintro ⟨σ, ⟨hσ, hw⟩, rfl⟩
    refine ⟨⟨σ, hσ, rfl⟩, ?_⟩
    rintro _ ⟨u, hu, rfl⟩
    simpa [Equiv.permCongr_apply] using hw u hu

theorem calls_topwSubtypeRed :
    ∀ T : SIReduction (Fin Δ.length) ℕ (Set (Perm (Fin Δ.length))),
      (topwSubtypeRed hnd hlt T).calls = T.calls.map (topwSubtypeInstance hnd hlt) := by
  intro T
  induction T with
  | done b => rfl
  | call J k ih =>
    rw [topwSubtypeRed, SIReduction.calls_call, SIReduction.calls_call, List.map_cons,
      topwSubtypeInstance_answer, permCongr_symm_image, ih]

theorem run_topwSubtypeRed :
    ∀ T : SIReduction (Fin Δ.length) ℕ (Set (Perm (Fin Δ.length))),
      (topwSubtypeRed hnd hlt T).run = (winEquiv n Δ hnd hlt).permCongr '' T.run := by
  intro T
  induction T with
  | done b => rfl
  | call J k ih =>
    rw [topwSubtypeRed, SIReduction.run_call, SIReduction.run_call,
      topwSubtypeInstance_answer, permCongr_symm_image, ih]
end Relabel

/-- A coset instance whose coset lies in a subgroup `H` is a coset instance for `H`. -/
theorem _root_.Babai.IsCosetInstance.of_K_subset {Ω A : Type*} {G H : Subgroup (Perm Ω)}
    {J : SIInstance Ω A} (h : IsCosetInstance G J) (hK : J.K ⊆ (H : Set (Perm Ω))) :
    IsCosetInstance H J := by
  obtain ⟨N, σ, -, -, hJK, hI⟩ := h
  have hσ : σ ∈ H := hK (hJK ▸ Set.mem_smul_set.mpr ⟨1, N.one_mem, mul_one σ⟩)
  refine ⟨N, σ, fun ν hν => ?_, hσ, hJK, hI⟩
  have : σ * ν ∈ H := hK (hJK ▸ Set.mem_smul_set.mpr ⟨ν, hν, rfl⟩)
  have h2 := H.mul_mem (H.inv_mem hσ) this
  rwa [inv_mul_cancel_left] at h2

section Link
variable {n : ℕ} {Δ : List ℕ} (hnd : Δ.Nodup) (hlt : ∀ u ∈ Δ, u < n)
    {G : Subgroup (Perm (Fin n))} (hinv : IsInvariant G (winSet n Δ)) (x : Fin n → ℕ)

/-- A call with respect to the restricted group, in position labels, is one with respect to
`G^Δ` once relabelled. -/
theorem topwSubtypeInstance_K {J : SIInstance (Fin Δ.length) ℕ}
    (hJ : J.K ⊆ ((winRestrictHom n Δ hnd hlt G hinv).range : Set (Perm (Fin Δ.length)))) :
    (topwSubtypeInstance hnd hlt J).K ⊆ (restrictTo G (winSet n Δ) hinv : Set _) := by
  rintro _ ⟨σ, hσ, rfl⟩
  have h := hJ hσ
  rw [range_winRestrictHom] at h
  obtain ⟨ρ, hρ, rfl⟩ := h
  convert hρ
  ext w
  simp [Equiv.permCongr_apply]

/-- Relabelling keeps coset instances: a coset instance for the restricted group in position
labels is a coset instance for `G^Δ` once relabelled. -/
theorem topwSubtypeInstance_isCosetInstance {J : SIInstance (Fin Δ.length) ℕ}
    (hJ : IsCosetInstance (winRestrictHom n Δ hnd hlt G hinv).range J) :
    IsCosetInstance (restrictTo G (winSet n Δ) hinv) (topwSubtypeInstance hnd hlt J) := by
  let e := winEquiv n Δ hnd hlt
  have key : ∀ τ ∈ (winRestrictHom n Δ hnd hlt G hinv).range,
      e.permCongrHom τ ∈ restrictTo G (winSet n Δ) hinv := by
    intro τ hτ
    rw [range_winRestrictHom] at hτ
    obtain ⟨ρ, hρ, rfl⟩ := hτ
    convert hρ
    ext w
    simp [e, Equiv.permCongr_apply]
  obtain ⟨N, σ, hN, hσ, hK, hI⟩ := hJ
  refine ⟨N.map e.permCongrHom.toMonoidHom, e.permCongrHom σ, ?_, key σ hσ, ?_, ?_⟩
  · rintro _ ⟨ν, hν, rfl⟩
    exact key ν (hN hν)
  · change e.permCongr '' J.K = _
    rw [hK, ← Equiv.permCongrHom_coe, Set.image_smul_distrib, Subgroup.coe_map]
    rfl
  · rintro _ ⟨ν, hν, rfl⟩
    change (e.permCongr ν) '' (e '' J.Δ) = e '' J.Δ
    rw [Set.image_image]
    have : (fun x => e.permCongr ν (e x)) = fun x => e (ν x) := by
      funext x; simp [Equiv.permCongr_apply]
    rw [this, ← Set.image_image, hI ν hν]

/-- **The machine's lift makes the paper's calls**: the lift of a round on the window
positions (`Algo.top4wTree`) makes, in order, the calls of the paper's lift of the
relabelled round (`Babai.liftWindow`). -/
theorem top4wTree_calls_eq_liftWindow
    (T : SIReduction (Fin Δ.length) ℕ (Set (Perm (Fin Δ.length))))
    (hK : ∀ J ∈ T.calls, J.K ⊆
      ((winRestrictHom n Δ hnd hlt G hinv).range : Set (Perm (Fin Δ.length)))) :
    (top4wTree Δ hnd hlt G hinv x T).calls =
      (liftWindow G (winSet n Δ) hinv x (topwSubtypeRed hnd hlt T)).calls := by
  have hK' : ∀ J ∈ (topwSubtypeRed hnd hlt T).calls,
      J.K ⊆ (restrictTo G (winSet n Δ) hinv : Set _) := by
    rw [calls_topwSubtypeRed]
    intro J hJ
    obtain ⟨J', hJ', rfl⟩ := List.mem_map.mp hJ
    exact topwSubtypeInstance_K hnd hlt hinv (hK J' hJ')
  rw [calls_liftWindow hinv x _ hK', calls_topwSubtypeRed, List.map_map]
  simp only [top4wTree, SIReduction.calls_bind, SIReduction.calls_done, List.append_nil]
  rw [calls_topwReduction hnd hlt hinv x T hK]
  exact List.map_congr_left (fun J _ => topwInstance_eq_windowInstance hnd hlt hinv x J)

/-- **The machine's lift returns the paper's value.** -/
theorem top4wTree_run_eq_liftWindow
    (T : SIReduction (Fin Δ.length) ℕ (Set (Perm (Fin Δ.length))))
    (hK : ∀ J ∈ T.calls, J.K ⊆
      ((winRestrictHom n Δ hnd hlt G hinv).range : Set (Perm (Fin Δ.length)))) :
    (top4wTree Δ hnd hlt G hinv x T).run =
      (liftWindow G (winSet n Δ) hinv x (topwSubtypeRed hnd hlt T)).run := by
  have hK' : ∀ J ∈ (topwSubtypeRed hnd hlt T).calls,
      J.K ⊆ (restrictTo G (winSet n Δ) hinv : Set _) := by
    rw [calls_topwSubtypeRed]
    intro J hJ
    obtain ⟨J', hJ', rfl⟩ := List.mem_map.mp hJ
    exact topwSubtypeInstance_K hnd hlt hinv (hK J' hJ')
  rw [liftWindow, SIReduction.run_bind, SIReduction.run_done, SIReduction.run_window hinv x _ hK',
    run_topwSubtypeRed, ← topwPreimage_eq_windowPreim hnd hlt hinv]
  simp only [top4wTree, SIReduction.run_bind, SIReduction.run_done]
  rw [run_topwReduction hnd hlt hinv x T hK]

/-- **The machine's lift keeps coset instances**: if every call of the round on the window
positions is a coset instance for the restricted group, then every call of its lift is a coset
instance for `G`. -/
theorem top4wTree_calls_isCosetInstance
    (T : SIReduction (Fin Δ.length) ℕ (Set (Perm (Fin Δ.length))))
    (hT : ∀ J ∈ T.calls, IsCosetInstance (winRestrictHom n Δ hnd hlt G hinv).range J) :
    ∀ J ∈ (top4wTree Δ hnd hlt G hinv x T).calls, IsCosetInstance G J := by
  have hK : ∀ J ∈ T.calls, J.K ⊆
      ((winRestrictHom n Δ hnd hlt G hinv).range : Set (Perm (Fin Δ.length))) :=
    fun J hJ => (hT J hJ).K_subset
  have hK' : ∀ J ∈ (topwSubtypeRed hnd hlt T).calls,
      J.K ⊆ (restrictTo G (winSet n Δ) hinv : Set _) := by
    rw [calls_topwSubtypeRed]
    intro J hJ
    obtain ⟨J', hJ', rfl⟩ := List.mem_map.mp hJ
    exact topwSubtypeInstance_K hnd hlt hinv (hK J' hJ')
  rw [top4wTree_calls_eq_liftWindow hnd hlt hinv x T hK]
  refine calls_liftWindow_isCosetInstance hinv x _ hK' ?_
  rw [calls_topwSubtypeRed]
  intro J hJ
  obtain ⟨J', hJ', rfl⟩ := List.mem_map.mp hJ
  exact topwSubtypeInstance_isCosetInstance hnd hlt hinv (hT J' hJ')
end Link

end Algo
