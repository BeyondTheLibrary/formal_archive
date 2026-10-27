import Workspace.Algo.TopMasterChainReturnMatch

/-! # A uniform computable termination measure for master nodes
The outer window is the first component and the stored Johnson degree is
the second. The ambient degree supplies a polynomial weight, fixed during
each recursion. This measure controls machine stack depth; the paper's
finer logarithmic rank still controls the number of mathematical calls.
-/
namespace Algo
open RAM RAM.Targets Babai

 def masterDegree (p : RawMasterSI) : ℕ := p.1.2.2.2.1.length
 def masterWindowSize (p : RawMasterSI) : ℕ := p.1.1.length
 def masterParameter (p : RawMasterSI) : ℕ :=
  p.2.elim (2 * masterWindowSize p) (fun h => h.1.1.length)
 def masterRankCap (n : ℕ) : ℕ := 16 * (n + 1) ^ 2
 def masterRankWeight (n : ℕ) : ℕ := masterRankCap n + 2 * n + 1
 def masterRawMeasure (p : RawMasterSI) : ℕ :=
  masterWindowSize p * masterRankWeight (masterDegree p) + masterParameter p + masterRankCap (masterDegree p)

 theorem polyFun_masterDegree : PolyFun masterDegree :=
  ((((polyFun_fst.comp polyFun_snd).comp polyFun_snd).comp polyFun_snd).comp polyFun_fst).comp polyFun_length
 theorem polyFun_masterWindowSize : PolyFun masterWindowSize :=
  (polyFun_fst.comp polyFun_fst).comp polyFun_length
 theorem polyFun_masterParameter : PolyFun masterParameter := by
  have hbody : PolyFun (fun q : RawMasterHint × RawMasterSI => q.1.1.1.length) :=
    ((polyFun_fst.comp polyFun_fst).comp polyFun_fst).comp polyFun_length
  exact (polyFun_snd.pair polyFun_id).comp
    (PolyFun.optionElim ((polyFun_const 2).mul polyFun_masterWindowSize) hbody)
 theorem polyFun_masterRankCap : PolyFun masterRankCap :=
  (polyFun_const 16).mul (polyFun_powConst (polyFun_id.add (polyFun_const 1)) 2)
 theorem polyFun_masterRankWeight : PolyFun masterRankWeight :=
  (polyFun_masterRankCap.add ((polyFun_const 2).mul polyFun_id)).add (polyFun_const 1)
 theorem polyFun_masterRawMeasure : PolyFun masterRawMeasure :=
  ((polyFun_masterWindowSize.mul (polyFun_masterDegree.comp polyFun_masterRankWeight)).add
    polyFun_masterParameter).add (polyFun_masterDegree.comp polyFun_masterRankCap)

 def masterMeasureBound (n : ℕ) : ℕ :=
  n * masterRankWeight n + 2 * n + masterRankCap n
 theorem polyBound_masterRankCap : PolyBound masterRankCap := by
  change PolyBound (fun n : ℕ => 16 * (n + 1) ^ 2)
  simpa only [pow_two] using
    (polyBound_const 16).mul ((polyBound_id.add (polyBound_const 1)).mul
      (polyBound_id.add (polyBound_const 1)))
 theorem polyBound_masterRankWeight : PolyBound masterRankWeight :=
  (polyBound_masterRankCap.add ((polyBound_const 2).mul polyBound_id)).add (polyBound_const 1)
 theorem polyBound_masterMeasureBound : PolyBound masterMeasureBound :=
  ((polyBound_id.mul polyBound_masterRankWeight).add ((polyBound_const 2).mul polyBound_id)).add
    polyBound_masterRankCap
 theorem mono_masterRankCap : Monotone masterRankCap := by
  intro a b h
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
 theorem mono_masterRankWeight : Monotone masterRankWeight := by
  intro a b h
  have := mono_masterRankCap h
  unfold masterRankWeight
  omega
 theorem mono_masterMeasureBound : Monotone masterMeasureBound := by
  intro a b h
  have h1 := Nat.mul_le_mul h (mono_masterRankWeight h)
  have h2 := mono_masterRankCap h
  unfold masterMeasureBound
  omega

 theorem masterRawMeasure_le {p : RawMasterSI}
    (hw : masterWindowSize p ≤ masterDegree p)
    (hm : masterParameter p ≤ 2 * masterWindowSize p) :
    masterRawMeasure p ≤ masterMeasureBound (masterDegree p) := by
  have hh := Nat.mul_le_mul_right (masterRankWeight (masterDegree p)) hw
  unfold masterRawMeasure masterMeasureBound
  omega

 theorem masterRawMeasure_lt {p q : RawMasterSI}
    (hn : masterDegree q = masterDegree p)
    (hw : masterWindowSize q ≤ masterWindowSize p)
    (hq : masterParameter q ≤ 2 * masterDegree p)
    (hp : masterWindowSize q < masterWindowSize p ∨ masterParameter q < masterParameter p) :
    masterRawMeasure q < masterRawMeasure p := by
  unfold masterRawMeasure
  rw [hn]
  rcases hp with hp | hp
  · have hstep := Nat.mul_le_mul_right (masterRankWeight (masterDegree p)) (Nat.succ_le_of_lt hp)
    rw [Nat.succ_mul] at hstep
    unfold masterRankWeight at *
    omega
  · have hstep := Nat.mul_le_mul_right (masterRankWeight (masterDegree p)) hw
    omega

/-- The executable measure bounds the paper's exact mathematical rank. -/
 theorem masterRawMeasure_dominates {Ω A ι : Type*} (M : MasterStep Ω A ι) (i : ι)
    {p : RawMasterSI} (hwin : M.win i = masterWindowSize p)
    (hw : masterWindowSize p ≤ masterDegree p) : M.rank i ≤ masterRawMeasure p := by
  have hcap : MasterStep.rankBound (M.win i) ≤ masterRankCap (masterDegree p) := by
    have hlog : Nat.log 2 (M.win i) ≤ masterDegree p := (Nat.log_le_self _ _).trans (hwin ▸ hw)
    have hpow := Nat.pow_le_pow_left (Nat.succ_le_succ hlog) 2
    change (Nat.log 2 (M.win i) + 1) ^ 2 ≤ (masterDegree p + 1) ^ 2 at hpow
    unfold MasterStep.rankBound masterRankCap
    omega
  have hJ := M.johnsonRank_le_rankBound i
  have hprod := Nat.mul_le_mul_left (M.win i) hcap
  unfold MasterStep.rank masterRawMeasure masterRankWeight
  rw [hwin] at *
  nlinarith
end Algo
