/-
An explicit running time for Theorem 1.1.1 (Babai, version 2.5): envelopes of the two phases of
Procedure AggregateCertificates (Sec. 13.2) with an explicit exponent. Not part of the faithful
formalization.
-/
import Workspace.Explicit.L57Env
import Workspace.Explicit.L57Cont
import Workspace.Explicit.CarriersRoute4State

/-!
# Envelopes of the two phases at the degree

For a context of the continuation at degree `n` (`Explicit.ContCtxOK`) of size at most
`2^{K₀ (log₂ n + 2)^5}`, the envelopes `Explicit.PhaseEnv` and `Explicit.CompEnv` exist with all
their fields, and the width of the two phases, at most `2^{K (log₂ n + 2)^5}`
(`Explicit.env_exists`). The construction is that of `Algo.aggnEnvelope_exists_in_size` and
`Algo.aggnCompareEnvelope_exists_in_size`, with the job tables and the recomputation inputs
bounded at the degree (`Explicit.TN.aggnPhaseJobs`, `Explicit.TN.aggnCompareJobs`,
`Explicit.TN.aggnrInputOf`). The width has the factor `|T|!` for the list `T` of the context,
which the guard keeps below `2^{(c+1)(log₂ n + 2)^5}` (`Explicit.factorial_guard_le`).
-/

set_option synthInstance.maxSize 1024
set_option maxHeartbeats 1000000

namespace Explicit

open RAM Algo

theorem Q5.polyB {f : ℕ → ℕ} (hf : PolyBound f) {T : ℕ → ℕ} (hT : Q5 T) :
    Q5 (fun n => f (T n)) := by
  obtain ⟨c, d, h⟩ := hf
  exact (q5_polyOf hT c d).mono (fun n => h (T n))

theorem q5_tsB5 {T : ℕ → ℕ} (hT : Q5 T) (A b : ℕ) : Q5 (fun n => tsB A 5 b n (T n)) :=
  ((q5_two_pow_lg A 5 le_rfl).mul ((hT.add (q5_const 1)).pow b)).mono (fun _ => le_rfl)

/-- **The factorial of a list within the guard**: `m ≤ (log₂ N + 1)^{c+1}` with `N ≤ n` gives
`m! ≤ m^m ≤ 2^{(c+1)(log₂ N + 1)^{c+2}} ≤ 2^{(c+1)(log₂ n + 2)^5}`. -/
theorem factorial_guard_le {c m N n : ℕ} (hc : c + 2 ≤ 5) (hN : N ≤ n)
    (hm : m ≤ guardBound (c + 1) N) : Nat.factorial m ≤ 2 ^ ((c + 1) * lg n ^ 5) := by
  have hLn : Nat.log 2 N + 2 ≤ lg n := by
    unfold lg; have := Nat.log_mono_right (b := 2) hN; omega
  set L := Nat.log 2 N
  set g := (L + 1) ^ (c + 1) with hgdef
  have hg : g ≤ 2 ^ ((c + 1) * (L + 1)) := by
    rw [mul_comm, pow_mul]; exact Nat.pow_le_pow_left (Nat.lt_two_pow_self).le _
  have hg1 : 1 ≤ g := Nat.one_le_pow _ _ (by omega)
  have hmg : m ≤ g := hm
  have hexp : (L + 1) * g ≤ lg n ^ 5 :=
    calc (L + 1) * g = (L + 1) ^ (c + 2) := by rw [hgdef, pow_succ]; ring
      _ ≤ (L + 1) ^ 5 := Nat.pow_le_pow_right (by omega) hc
      _ ≤ lg n ^ 5 := Nat.pow_le_pow_left (by omega) 5
  calc Nat.factorial m ≤ m ^ m := Nat.factorial_le_pow m
    _ ≤ g ^ g := le_trans (Nat.pow_le_pow_left hmg m) (Nat.pow_le_pow_right hg1 hmg)
    _ ≤ (2 ^ ((c + 1) * (L + 1))) ^ g := Nat.pow_le_pow_left hg g
    _ = 2 ^ ((c + 1) * ((L + 1) * g)) := by rw [← pow_mul, mul_assoc]
    _ ≤ 2 ^ ((c + 1) * lg n ^ 5) :=
      Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ hexp)

variable {c n : ℕ} {C : AggnPhaseCtx}

/-- The sum of the fields of a certificate-phase envelope. -/
def phaseEnvTot (B : PhaseEnv c n C) : ℕ := B.base + B.loopState + B.cache + B.coset + B.entry

/-- The sum of the fields of a comparison-phase envelope. -/
def compEnvTot (B : CompEnv c n C) : ℕ := B.base + B.loopState + B.cache + B.coset

/-- **The envelopes of the two phases at the degree, with an explicit exponent.** -/
theorem env_exists (c : ℕ) (hc : c + 2 ≤ 5) (K0 : ℕ) : ∃ K, ∀ n (C : AggnPhaseCtx),
    ContCtxOK c n C → Enc.size C ≤ 2 ^ (K0 * lg n ^ 5) →
    ∃ (B : PhaseEnv c n C) (B' : CompEnv c n C),
      phaseEnvTot B + compEnvTot B' + aggnAggregateWidth c C ≤ 2 ^ (K * lg n ^ 5) := by
  have hc1 : c + 1 ≤ 5 := by omega
  obtain ⟨Aj, bj, hJ⟩ := (TN.aggnPhaseJobs c).mono_k hc1
  obtain ⟨Ac, bc, hJc⟩ := (TN.aggnCompareJobs c).mono_k hc1
  obtain ⟨Ar, br, hR⟩ := (TN.aggnrInputOf c).mono_k hc1
  obtain ⟨cl, dl, hl⟩ := aggnPolyFun_jobLoop.size
  obtain ⟨cx, dx, hx⟩ := aggnPolyFun_compareCtx.size
  obtain ⟨ce, de, he⟩ := aggnPolyFun_loopEntry.size
  let X : ℕ → ℕ := fun n => 2 ^ (K0 * lg n ^ 5)
  let J1 : ℕ → ℕ := fun n => tsB Aj 5 bj n (X n)
  let J2 : ℕ → ℕ := fun n => tsB Ac 5 bc n (X n)
  let E0 : ℕ := Enc.size ((([], []), ([], [], [])) : RawLCLoop)
  let E1 : ℕ := Enc.size (none : RawCoset)
  let L : ℕ → ℕ := fun n => X n + J1 n + cl * (2 * X n + 2 * J1 n + 1) ^ dl + E0
  let S : ℕ → ℕ := fun n => L n + lcStBound (L n)
  let Q : ℕ → ℕ := fun n => tsB Ar 5 br n (2 * L n + 2 * S n) + 1
  let A : ℕ → ℕ := fun n => 4 * Q n + chainBound (L n) + 4
  let F : ℕ → ℕ := fun n => ce * (2 * L n + 2 * (2 * L n + 2 * S n) + 1) ^ de
  let L' : ℕ → ℕ := fun n => X n + J2 n + cx * (2 * X n + 2 * J2 n + 1) ^ dx + E0 + E1
  let S' : ℕ → ℕ := fun n => L' n + lcStBound (L' n)
  let R' : ℕ → ℕ := fun n => tsB Ar 5 br n (2 * L' n + 2 * S' n)
  let U : ℕ → ℕ := fun n => R' n + L' n
  let Q' : ℕ → ℕ := fun n => R' n + aggnCompareCacheBound (U n)
  let A' : ℕ → ℕ := fun n => L' n + 4 * Q' n + chainBound (L' n) + 4
  let Fct : ℕ → ℕ := fun n => 2 ^ ((c + 1) * lg n ^ 5)
  let W : ℕ → ℕ := fun n => (L n + L' n) * (2 * (n * (Fct n * n)))
  let T : ℕ → ℕ := fun n => (L n + S n + Q n + A n + F n) + (L' n + S' n + Q' n + A' n) + W n
  have qX : Q5 X := q5_two_pow_lg K0 5 le_rfl
  have qJ1 : Q5 J1 := q5_tsB5 qX Aj bj
  have qJ2 : Q5 J2 := q5_tsB5 qX Ac bc
  have qL : Q5 L := ((qX.add qJ1).add
    (q5_polyOf (((q5_const 2).mul qX).add ((q5_const 2).mul qJ1)) cl dl)).add (q5_const E0)
  have qS : Q5 S := qL.add (Q5.polyB polyBound_lcStBound qL)
  have qQ : Q5 Q := (q5_tsB5 (((q5_const 2).mul qL).add ((q5_const 2).mul qS)) Ar br).add
    (q5_const 1)
  have qA : Q5 A := (((q5_const 4).mul qQ).add (Q5.polyB polyBound_chainBound qL)).add
    (q5_const 4)
  have qF : Q5 F := q5_polyOf (((q5_const 2).mul qL).add ((q5_const 2).mul
    (((q5_const 2).mul qL).add ((q5_const 2).mul qS)))) ce de
  have qL' : Q5 L' := (((qX.add qJ2).add
    (q5_polyOf (((q5_const 2).mul qX).add ((q5_const 2).mul qJ2)) cx dx)).add
      (q5_const E0)).add (q5_const E1)
  have qS' : Q5 S' := qL'.add (Q5.polyB polyBound_lcStBound qL')
  have qR' : Q5 R' := q5_tsB5 (((q5_const 2).mul qL').add ((q5_const 2).mul qS')) Ar br
  have qU : Q5 U := qR'.add qL'
  have qQ' : Q5 Q' := qR'.add (Q5.polyB aggnPolyBound_compareCache qU)
  have qA' : Q5 A' := ((qL'.add ((q5_const 4).mul qQ')).add
    (Q5.polyB polyBound_chainBound qL')).add (q5_const 4)
  have qW : Q5 W := (qL.add qL').mul ((q5_const 2).mul
    (q5_id.mul ((q5_two_pow_lg (c + 1) 5 le_rfl).mul q5_id)))
  have qT : Q5 T := ((((qL.add qS).add qQ).add qA).add qF).add
    ((((qL'.add qS').add qQ').add qA').add qW) |>.mono (fun n => by
      show T n ≤ _; dsimp only [T]; omega)
  obtain ⟨K, hK⟩ := qT
  refine ⟨K, fun n C hC hXC => ?_⟩
  have hCtx : CtxOK n C := hC.1
  have hXC' : Enc.size C ≤ X n := hXC
  -- the certificate phase
  have hjobs : Enc.size (aggnPhaseJobs c C) ≤ J1 n :=
    (hJ.size n C hCtx).trans (tsB_mono_right _ _ _ _ hXC')
  have hsLoop : ∀ p : RawLCLoop, Enc.size p ≤ L n → AggnLoopBound (L n) (S n) p := fun p hp =>
    ⟨(size_fst_le' p).trans hp, ((size_snd_le' p).trans hp).trans (Nat.le_add_right _ _)⟩
  have hpoly : ∀ {a b : ℕ} (k d : ℕ), a ≤ b → k * (a + 1) ^ d ≤ k * (b + 1) ^ d :=
    fun k d h => Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
  let B : PhaseEnv c n C := {
    base := L n
    loopState := S n
    cache := Q n
    coset := A n
    entry := F n
    ctx_ok := hCtx
    context_le := by dsimp only [L]; omega
    jobs_le := by dsimp only [L]; omega
    open_le := by
      intro a ha
      apply hsLoop
      have h1 : Enc.size (aggnJobLoop C a) ≤ cl * (Enc.size (C, a) + 1) ^ dl := hl (C, a)
      have h2 := Combine.size_pair_le C a
      have h3 := (size_mem_le ha).trans hjobs
      have h4 := hpoly cl dl (show Enc.size (C, a) ≤ 2 * X n + 2 * J1 n by omega)
      dsimp only [L]
      omega
    empty_le := hsLoop _ (by dsimp only [L]; omega)
    step_le := Nat.le_add_left _ _
    cache_le := by
      intro p hp hb
      have h1 := hR.size n p hp
      have h2 := tsB_mono_right Ar 5 br n hb.size
      dsimp only [Q]
      omega
    coset_le := le_rfl
    entry_le := by
      intro a ha p hp
      have h1 : Enc.size (aggnLoopEntry (a, p)) ≤ ce * (Enc.size (a, p) + 1) ^ de := he (a, p)
      have h2 := Combine.size_pair_le a p
      have h3 := (size_mem_le ha).trans hjobs
      have h3' : Enc.size a ≤ L n := by dsimp only [L]; omega
      have h4 := hp.size
      have h5 := hpoly ce de (show Enc.size (a, p) ≤ 2 * L n + 2 * (2 * L n + 2 * S n) by
        omega)
      dsimp only [F]
      omega }
  -- the comparison phase
  have hcjobs : Enc.size (aggnCompareJobs c C) ≤ J2 n :=
    (hJc.size n C hCtx).trans (tsB_mono_right _ _ _ _ hXC')
  have hsLoop' : ∀ p : RawLCLoop, Enc.size p ≤ L' n → AggnLoopBound (L' n) (S' n) p :=
    fun p hp =>
      ⟨(size_fst_le' p).trans hp, ((size_snd_le' p).trans hp).trans (Nat.le_add_right _ _)⟩
  have hcache : ∀ p ys q mode, LoopOK n p → AggnLoopBound (L' n) (S' n) p →
      Enc.size ys ≤ L' n → Enc.size (aggnPairInput c p ys q mode) ≤ Q' n := by
    intro p ys q mode hlp hp hy
    have hsrc : Enc.size (aggnrInputOf c p) ≤ R' n :=
      (hR.size n p hlp).trans (tsB_mono_right _ _ _ _ hp.size)
    cases mode with
    | none => exact hsrc.trans (Nat.le_add_right _ _)
    | some H =>
      have hu : Enc.size (aggnrInputOf c p) ≤ U n := hsrc.trans (Nat.le_add_right _ _)
      have hx' : Enc.size p.1.1 ≤ U n :=
        ((size_fst_le' p.1).trans hp.1).trans (Nat.le_add_left _ _)
      have hy' : Enc.size ys ≤ U n := hy.trans (Nat.le_add_left _ _)
      exact (aggnCompareInput_size p ys q hu hx' hy').trans (Nat.le_add_left _ _)
  let B' : CompEnv c n C := {
    base := L' n
    loopState := S' n
    cache := Q' n
    coset := A' n
    ctx_ok := hCtx
    context_le := by dsimp only [L']; omega
    jobs_le := by dsimp only [L']; omega
    open_le := by
      intro a ha
      have h1 : Enc.size (aggnCompareCtx C a) ≤ cx * (Enc.size (C, a) + 1) ^ dx := hx (C, a)
      have h2 := Combine.size_pair_le C a
      have h3 := (size_mem_le ha).trans hcjobs
      have h4 := hpoly cx dx (show Enc.size (C, a) ≤ 2 * X n + 2 * J2 n by omega)
      have hc : Enc.size (aggnCompareCtx C a) ≤ L' n := by
        dsimp only [L']
        omega
      refine ⟨hsLoop' _ ((size_fst_le' _).trans hc),
        ((size_fst_le' (aggnCompareCtx C a).2).trans (size_snd_le' _)).trans hc, ?_⟩
      exact (((size_snd_le' (aggnCompareCtx C a).2).trans (size_snd_le' _)).trans hc).trans
        (by dsimp only [A']; omega)
    empty_le := hsLoop' _ (by dsimp only [L']; omega)
    empty_coset_le := by dsimp only [A', L']; omega
    step_le := Nat.le_add_left _ _
    cache_le := hcache
    coset_le := by dsimp only [A']; omega }
  -- the width
  have hxn : C.2.1.length ≤ n := hCtx.1
  have hfact : Nat.factorial C.2.2.2.length ≤ Fct n := factorial_guard_le hc hxn hC.2.2
  have hjw : aggnJobWidth C ≤ n * (Fct n * n) :=
    Nat.mul_le_mul hxn (Nat.mul_le_mul hfact hxn)
  have hpw : aggnPhaseWidth c C ≤ L n * (n * (Fct n * n)) := by
    change (aggnPhaseJobs c C).length * aggnJobWidth C ≤ _
    refine Nat.mul_le_mul ?_ hjw
    have := (length_le_size (aggnPhaseJobs c C)).trans hjobs
    dsimp only [L]; omega
  have hcw : aggnCompareWidth c C ≤ L' n * (2 * (n * (Fct n * n))) := by
    change (aggnCompareJobs c C).length * (2 * aggnJobWidth C) ≤ _
    refine Nat.mul_le_mul ?_ (Nat.mul_le_mul_left 2 hjw)
    have := (length_le_size (aggnCompareJobs c C)).trans hcjobs
    dsimp only [L']; omega
  have hW : aggnAggregateWidth c C ≤ W n := by
    change aggnPhaseWidth c C + aggnCompareWidth c C ≤ _
    have : L n * (n * (Fct n * n)) ≤ L n * (2 * (n * (Fct n * n))) :=
      Nat.mul_le_mul_left _ (by omega)
    dsimp only [W]
    rw [Nat.add_mul]
    omega
  refine ⟨B, B', le_trans ?_ (hK n)⟩
  change (L n + S n + Q n + A n + F n) + (L' n + S' n + Q' n + A' n) +
    aggnAggregateWidth c C ≤ T n
  dsimp only [T]
  omega

end Explicit
