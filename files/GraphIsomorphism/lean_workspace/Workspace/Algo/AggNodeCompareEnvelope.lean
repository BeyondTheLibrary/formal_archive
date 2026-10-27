import Workspace.Algo.AggNodeCompareBound
import Workspace.Algo.AggNodeCompareChecked

/-! # One comparison-state cap for every input degree

Construct the invariant from the actual preparation routines. The coset
bound is chosen after the cache bound, since the latter is independent of
coset encoding size. The final exponent is chosen before the input degree.
-/
set_option synthInstance.maxSize 1024
set_option maxHeartbeats 1000000
namespace Algo
open RAM RAM.Targets

theorem aggnCompareEnvelope_exists_in_size (c : ℕ) : ∃ d : ℕ, ∀ C : AggnPhaseCtx,
    ∃ B : AggnCompareEnvelope c C,
      aggnCompareEnvelopeBound B (aggnCompareWidth c C) ≤
        2 ^ ((Nat.log 2 (Enc.size C) + 2) ^ d) := by
  have hjobs := aggnQuasiFun_compareJobs c
  have hctxs := (quasiFun_id.pair hjobs).comp
    (aggnQuasiFun_mapParam aggnPolyFun_compareCtx.quasiFun)
  let empty : AggnPairCtx := ((([], []), ([], [], [])), [], none)
  have hseed := (quasiFun_id.pair (hjobs.pair hctxs)).pair (quasiFun_const empty)
  obtain ⟨L, hL, hLm, hs⟩ := hseed.size.exists_quasiPolyBound
  obtain ⟨K, hK, hKm, hk⟩ := (aggnQuasiFun_recomputeInput c).size.exists_quasiPolyBound
  obtain ⟨w, hw⟩ := aggnCompareWidth_bound_in_size c
  let S := fun N => L N + lcStBound (L N)
  let P := fun N => 2 * L N + 2 * S N
  let U := fun N => K (P N) + L N
  let Q := fun N => K (P N) + aggnCompareCacheBound (U N)
  let A := fun N => L N + 4 * Q N + chainBound (L N) + 4
  let D := fun N => 65536 * (L N + S N + Q N + A N +
    (1 + 2 * A N * L N) + 2 ^ ((Nat.log 2 N + 2) ^ w) + 1)
  have hS : QuasiPolyBound S := hL.add (polyBound_lcStBound.comp_quasiPoly hL)
  have hP : QuasiPolyBound P := ((polyBound_const 2).quasiPoly.mul hL).add
    ((polyBound_const 2).quasiPoly.mul hS)
  have hU : QuasiPolyBound U := (hK.comp hP).add hL
  have hQ : QuasiPolyBound Q := (hK.comp hP).add (aggnPolyBound_compareCache.comp_quasiPoly hU)
  have hA : QuasiPolyBound A := ((hL.add ((polyBound_const 4).quasiPoly.mul hQ)).add
    (polyBound_chainBound.comp_quasiPoly hL)).add (polyBound_const 4).quasiPoly
  have hD : QuasiPolyBound D := (polyBound_const 65536).quasiPoly.mul
    ((((((hL.add hS).add hQ).add hA).add
      ((polyBound_const 1).quasiPoly.add (((polyBound_const 2).quasiPoly.mul hA).mul hL))).add
        (quasiPolyBound_witness w)).add (polyBound_const 1).quasiPoly)
  obtain ⟨d, hd⟩ := hD
  refine ⟨d, fun C => ?_⟩
  let N := Enc.size C
  let seed := ((C, aggnCompareJobs c C, (aggnCompareJobs c C).map (aggnCompareCtx C)), empty)
  have hseedSize : Enc.size seed ≤ L N := hs C
  have hctx : Enc.size C ≤ L N := ((size_fst_le' seed.1).trans (size_fst_le' seed)).trans hseedSize
  have hj : Enc.size (aggnCompareJobs c C) ≤ L N :=
    ((size_fst_le' seed.1.2).trans ((size_snd_le' seed.1).trans (size_fst_le' seed))).trans hseedSize
  have hl : Enc.size ((aggnCompareJobs c C).map (aggnCompareCtx C)) ≤ L N :=
    ((size_snd_le' seed.1.2).trans ((size_snd_le' seed.1).trans (size_fst_le' seed))).trans hseedSize
  have hempty : Enc.size empty ≤ L N := (size_snd_le' seed).trans hseedSize
  have hsLoop : ∀ p : RawLCLoop, Enc.size p ≤ L N → AggnLoopBound (L N) (S N) p := by
    intro p hp
    exact ⟨(size_fst_le' p).trans hp, ((size_snd_le' p).trans hp).trans (Nat.le_add_right _ _)⟩
  have hcache : ∀ p ys q mode, AggnLoopBound (L N) (S N) p → Enc.size ys ≤ L N →
      Enc.size (aggnPairInput c p ys q mode) ≤ Q N := by
    intro p ys q mode hp hy
    have hsrc : Enc.size (aggnrInputOf c p) ≤ K (P N) := (hk p).trans (hKm _ _ hp.size)
    cases mode with
    | none => exact hsrc.trans (Nat.le_add_right _ _)
    | some H =>
      have hu : Enc.size (aggnrInputOf c p) ≤ U N := hsrc.trans (Nat.le_add_right _ _)
      have hx : Enc.size p.1.1 ≤ U N :=
        ((size_fst_le' p.1).trans hp.1).trans (Nat.le_add_left _ _)
      have hy' : Enc.size ys ≤ U N := hy.trans (Nat.le_add_left _ _)
      exact (aggnCompareInput_size p ys q hu hx hy').trans (Nat.le_add_left _ _)
  let B : AggnCompareEnvelope c C := {
    base := L N
    loopState := S N
    cache := Q N
    coset := A N
    context_le := hctx
    jobs_le := hj
    open_le := by
      intro a ha
      have hc : Enc.size (aggnCompareCtx C a) ≤ L N :=
        (size_mem_le (List.mem_map_of_mem (f := aggnCompareCtx C) ha)).trans hl
      refine ⟨hsLoop _ ((size_fst_le' _).trans hc),
        ((size_fst_le' (aggnCompareCtx C a).2).trans (size_snd_le' _)).trans hc, ?_⟩
      exact (((size_snd_le' (aggnCompareCtx C a).2).trans (size_snd_le' _)).trans hc).trans
        (by dsimp only [A]; omega)
    empty_le := hsLoop _ ((size_fst_le' empty).trans hempty)
    empty_coset_le := (((size_snd_le' empty.2).trans (size_snd_le' empty)).trans hempty).trans
      (by dsimp only [A]; omega)
    step_le := Nat.le_add_left _ _
    cache_le := hcache
    coset_le := by dsimp only [A]; omega }
  refine ⟨B, le_trans ?_ (hd N)⟩
  have hwC : aggnCompareWidth c C ≤ 2 ^ ((Nat.log 2 N + 2) ^ w) := hw C
  change 65536 * (L N + S N + Q N + A N + (1 + 2 * A N * L N) + aggnCompareWidth c C + 1) ≤ D N
  dsimp only [D]
  omega

/-- A single exponent bounds every well-formed context of the uniform carrier. -/
theorem aggnCompareEnvelope_exists (c : ℕ) : ∃ d : ℕ, ∀ I : AggnPhaseNode,
    (aggnCompareCheckedRound c).WF I → ∃ B : AggnCompareEnvelope c I.1,
      aggnCompareEnvelopeBound B (aggnCompareWidth c I.1) ≤
        2 ^ ((Nat.log 2 ((aggnCompareCheckedRound c).ground I) + 2) ^ d) := by
  obtain ⟨e, he⟩ := aggnCompareEnvelope_exists_in_size c
  have hcomp := (quasiPolyBound_witness e).comp_poly
    ((polyBound_const 2).mul aggnPolyBound_checkedWindow)
  obtain ⟨d, hd⟩ := hcomp
  refine ⟨d, fun I hI => ?_⟩
  obtain ⟨B, hB⟩ := he I.1
  exact ⟨B, hB.trans ((quasiPolyBound_witness_mono e hI.2.1).trans (hd I.1.2.1.length))⟩

end Algo
