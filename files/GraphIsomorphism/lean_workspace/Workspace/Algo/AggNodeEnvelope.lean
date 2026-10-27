import Workspace.Algo.AggNodePhaseBound
import Workspace.Algo.AggNodeCheckedWidth

/-! # A uniform cap derived from the implemented routines

The envelopes used in the state invariant exist for every raw context.
Their quasipolynomial bounds follow from the concrete table, cache, and
packing routines. The exponent is selected before the varying domain size.
-/
set_option synthInstance.maxSize 1024
set_option maxHeartbeats 1000000
namespace Algo
open RAM RAM.Targets

/-- The proof envelopes fit one quasipolynomial in the supplied context size. -/
theorem aggnEnvelope_exists_in_size (c : ℕ) : ∃ d : ℕ, ∀ C : AggnPhaseCtx,
    ∃ B : AggnStateEnvelope c C,
      aggnEnvelopeBound B (aggnPhaseWidth c C) ≤ 2 ^ ((Nat.log 2 (Enc.size C) + 2) ^ d) := by
  have hjobs := aggnQuasiFun_phaseJobs c
  have hloops := (quasiFun_id.pair hjobs).comp
    (aggnQuasiFun_mapParam aggnPolyFun_jobLoop.quasiFun)
  have hseed := (quasiFun_id.pair (hjobs.pair hloops)).pair
    (quasiFun_const ((([], []), ([], [], [])) : RawLCLoop))
  obtain ⟨L, hL, hLm, hs⟩ := hseed.size.exists_quasiPolyBound
  obtain ⟨K, hK, hKm, hk⟩ := (aggnQuasiFun_recomputeInput c).size.exists_quasiPolyBound
  obtain ⟨E, hE, hEm, he⟩ := aggnPolyFun_loopEntry.size.exists_polyBound
  obtain ⟨w, hw⟩ := aggnPhaseWidth_bound_in_size c
  let S := fun N => L N + lcStBound (L N)
  let P := fun N => 2 * L N + 2 * S N
  let Q := fun N => K (P N) + 1
  let A := fun N => 4 * Q N + chainBound (L N) + 4
  let F := fun N => E (2 * L N + 2 * P N)
  let D := fun N => 2048 * (L N + S N + Q N + A N +
    (2 + 2 * F N * L N) + 2 ^ ((Nat.log 2 N + 2) ^ w) + 1)
  have hS : QuasiPolyBound S := hL.add (polyBound_lcStBound.comp_quasiPoly hL)
  have hP : QuasiPolyBound P := ((polyBound_const 2).quasiPoly.mul hL).add
    ((polyBound_const 2).quasiPoly.mul hS)
  have hQ : QuasiPolyBound Q := (hK.comp hP).add (polyBound_const 1).quasiPoly
  have hA : QuasiPolyBound A := (((polyBound_const 4).quasiPoly.mul hQ).add
    (polyBound_chainBound.comp_quasiPoly hL)).add (polyBound_const 4).quasiPoly
  have hF : QuasiPolyBound F := hE.comp_quasiPoly
    (((polyBound_const 2).quasiPoly.mul hL).add ((polyBound_const 2).quasiPoly.mul hP))
  have hD : QuasiPolyBound D := (polyBound_const 2048).quasiPoly.mul
    ((((((hL.add hS).add hQ).add hA).add
      ((polyBound_const 2).quasiPoly.add (((polyBound_const 2).quasiPoly.mul hF).mul hL))).add
        (quasiPolyBound_witness w)).add (polyBound_const 1).quasiPoly)
  obtain ⟨d, hd⟩ := hD
  refine ⟨d, fun C => ?_⟩
  let N := Enc.size C
  let seed := ((C, aggnPhaseJobs c C, (aggnPhaseJobs c C).map (aggnJobLoop C)),
    ((([], []), ([], [], [])) : RawLCLoop))
  have hseedSize : Enc.size seed ≤ L N := hs C
  have hctx : Enc.size C ≤ L N := ((size_fst_le' seed.1).trans (size_fst_le' seed)).trans hseedSize
  have hj : Enc.size (aggnPhaseJobs c C) ≤ L N :=
    ((size_fst_le' seed.1.2).trans ((size_snd_le' seed.1).trans (size_fst_le' seed))).trans hseedSize
  have hl : Enc.size ((aggnPhaseJobs c C).map (aggnJobLoop C)) ≤ L N :=
    ((size_snd_le' seed.1.2).trans ((size_snd_le' seed.1).trans (size_fst_le' seed))).trans hseedSize
  have hempty : Enc.size ((([], []), ([], [], [])) : RawLCLoop) ≤ L N :=
    (size_snd_le' seed).trans hseedSize
  have hsLoop : ∀ p : RawLCLoop, Enc.size p ≤ L N → AggnLoopBound (L N) (S N) p := by
    intro p hp
    exact ⟨(size_fst_le' p).trans hp, ((size_snd_le' p).trans hp).trans (Nat.le_add_right _ _)⟩
  let B : AggnStateEnvelope c C := {
    base := L N
    loopState := S N
    cache := Q N
    coset := A N
    entry := F N
    context_le := hctx
    jobs_le := hj
    open_le := fun a ha => hsLoop (aggnJobLoop C a)
      ((size_mem_le (List.mem_map_of_mem (f := aggnJobLoop C) ha)).trans hl)
    empty_le := hsLoop _ hempty
    step_le := Nat.le_add_left _ _
    cache_le := fun p hp => ((hk p).trans (hKm _ _ hp.size)).trans (Nat.le_add_right _ 1)
    coset_le := le_rfl
    entry_le := fun a ha p hp => (he (a, p)).trans (hEm _ _ (by
      have hpa := Combine.size_pair_le a p
      have hsa := (size_mem_le ha).trans hj
      have hsp := hp.size
      dsimp only [P]
      omega)) }
  refine ⟨B, le_trans ?_ (hd N)⟩
  have hwC : aggnPhaseWidth c C ≤ 2 ^ ((Nat.log 2 N + 2) ^ w) := hw C
  change 2048 * (L N + S N + Q N + A N + (2 + 2 * F N * L N) + aggnPhaseWidth c C + 1) ≤ D N
  dsimp only [D]
  omega

/-- The checked context bound turns the preceding cap into a bound in the parent degree. -/
theorem aggnEnvelope_exists (c : ℕ) : ∃ d : ℕ, ∀ (n : ℕ) (I : AggnPhaseNode),
    (aggnCheckedRound c n).WF I → ∃ B : AggnStateEnvelope c I.1,
      aggnEnvelopeBound B (aggnPhaseWidth c I.1) ≤
        2 ^ ((Nat.log 2 ((aggnCheckedRound c n).ground I) + 2) ^ d) := by
  obtain ⟨e, he⟩ := aggnEnvelope_exists_in_size c
  have hcomp := (quasiPolyBound_witness e).comp_poly
    ((polyBound_const 2).mul aggnPolyBound_checkedWindow)
  obtain ⟨d, hd⟩ := hcomp
  refine ⟨d, fun n I hI => ?_⟩
  obtain ⟨B, hB⟩ := he I.1
  refine ⟨B, hB.trans ?_⟩
  have hc := quasiPolyBound_witness_mono e hI.2.1
  have hg : (aggnCheckedRound c n).ground I = n := hI.1
  rw [hg]
  exact hc.trans (hd n)

end Algo
