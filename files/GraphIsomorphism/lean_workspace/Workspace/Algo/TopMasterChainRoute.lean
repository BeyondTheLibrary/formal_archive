import Workspace.Algo.TopMasterChainChoices

/-! # The actual intransitive route supplies the line-1 case -/
namespace Algo
open RAM RAM.Targets Babai Equiv MulAction
open scoped Classical

 theorem masterTransitive_of_image {Ω Ω' : Type*} (e : Ω ≃ Ω')
    (G : Subgroup (Perm Ω)) (H : Subgroup (Perm Ω'))
    (hGH : e.permCongr '' (G : Set (Perm Ω)) = H) (hH : IsTransitive H) :
    IsTransitive G := by
  obtain ⟨u, hu⟩ := hH
  refine ⟨e.symm u, Set.eq_univ_of_forall fun v => ?_⟩
  have hh : e v ∈ orbit H (e (e.symm u)) := by rw [Equiv.apply_symm_apply, hu]; trivial
  rw [← topd_orbit e G H hGH] at hh
  obtain ⟨z, hz, he⟩ := hh
  exact e.injective he ▸ hz

section Route
variable {n B C₀ : ℕ} {W : RawWinSI}
    (hw : RawGens.WF n W.2.1) (hnd : W.1.Nodup) (hlt : ∀ u ∈ W.1, u < n)
    (hinv : IsInvariant (decGroup n W.2.1) (winSet n W.1))
    (hr : masterReduceRoute B C₀ W = 2)

include hw hnd hlt hinv hr in
theorem masterChainRoute_intransitive : ¬IsTransitive (masterChainData hw hlt hinv).windowGroup := by
  intro ht
  have hf := ((masterReduceRoute_chain B C₀ W).mp hr).2.2
  have hgs := rawRestrictGens_wf_of_raw (dom := W.2.2.2.1) hw hnd hlt hinv
  have he := decGroup_rawRestrictGens_of_raw (dom := W.2.2.2.1) hw hnd hlt hinv
  change decGroup W.1.length (primitiveWindowInput W).1 = _ at he
  have ht' : IsTransitive (decGroup W.1.length (primitiveWindowInput W).1) := by
    rw [he]
    exact masterTransitive_of_image (winEquiv n W.1 hnd hlt) _ _
      (topwCompat hnd hlt hinv (1 : restrictTo (decGroup n W.2.1) (winSet n W.1) hinv →* Perm (Fin 0))).group_image ht
  have hh := (rawIsTransitive_eq_true_iff hgs rfl).mpr ht'
  change rawIsTransitive (masterWindowGroup W) = true at hh
  rw [hf] at hh
  contradiction

include hw hnd hlt hinv hr in
theorem masterChainRoute_nonempty (hC : 1 < C₀) : (winSet n W.1).Nonempty := by
  have hn := masterReduceRoute_large_window (N := 0) hw hnd hlt hinv hC
    (by omega : masterReduceRoute B C₀ W ≠ 0) (by omega : masterReduceRoute B C₀ W ≠ 1)
  obtain ⟨u, hu⟩ := List.length_pos_iff_exists_mem.mp hn
  exact ⟨⟨u, hlt u hu⟩, hu⟩

noncomputable def masterChainCase (q : ℕ) (hC : 1 < C₀) :
    Line1Case (masterGroupInstance n W) q :=
  .chain (masterChainData hw hlt hinv) ⟨_, (masterChainRoute_nonempty hw hnd hlt hinv hr hC).choose_spec⟩
    (masterChainRoute_intransitive hw hnd hlt hinv hr)

include hw hnd hlt hinv hr in
theorem masterChainCase_loop (a b q : ℕ) (hC : 1 < C₀) (solve : RawWinSI → RawCoset)
    (hx : W.2.2.2.1.length = n) :
    LoopMatch (masterChainRound a b solve) (masterChainDecode n) (decCoset n)
      (masterChainPreparedEnter W) (winOrbits (W.2.1, W.1)).length 0
      (masterChainInit (masterChainPreparedEnter W)) (masterChainCase hw hnd hlt hinv hr q hC).cosetBranch :=
  masterChainData_loop hx hw hnd hlt hinv a b solve
    ⟨_, (masterChainRoute_nonempty hw hnd hlt hinv hr hC).choose_spec⟩

include hw hnd hlt hinv hr in
theorem masterChainCase_progress (q : ℕ) (hC : 1 < C₀) :
    (∀ J ∈ (masterChainCase hw hnd hlt hinv hr q hC).cosetBranch.calls,
      J.windowSize < (masterGroupInstance n W).windowSize) ∧
    (((masterChainCase hw hnd hlt hinv hr q hC).cosetBranch.calls).map SIInstance.windowSize).sum ≤
      (masterGroupInstance n W).windowSize := by
  let d := masterChainData hw hlt hinv
  let u : (masterGroupInstance n W).Δ :=
    ⟨_, (masterChainRoute_nonempty hw hnd hlt hinv hr hC).choose_spec⟩
  change (∀ J ∈ (chainRuleCoset d u).calls, J.windowSize < _) ∧ _
  constructor
  · intro J hJ
    obtain ⟨J', hJ', hsize⟩ := calls_liftWindow_windowSize d.invariant
      (masterGroupInstance n W).x _ (calls_chainRuleBranch_K d u) J hJ
    have hm := (Babai.calls_cosetChain _ _ _ _).2 J' hJ'
    have hs := ncard_lt_of_mem_orbitList (masterChainRoute_intransitive hw hnd hlt hinv hr)
      (d.orbits.spec.mem_iff.mp hm)
    rw [d.card_window] at hs
    exact hsize.trans_lt hs
  · change (((chainRuleCoset d u).calls).map SIInstance.windowSize).sum ≤ _
    rw [chainRuleCoset, sum_windowSize_calls_liftWindow d.invariant
      (masterGroupInstance n W).x _ (calls_chainRuleBranch_K d u)]
    refine (sum_windowSize_calls_cosetChain _ _ _ _).trans ?_
    rw [(d.orbits.spec.map Set.ncard).sum_eq, sum_ncard_orbitList, d.card_window]

end Route
end Algo
