/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: bounded iteration on the RAM with a per-input cost, and the table of
all `k`-tuples over a list, for the standalone routine of Theorem 13.2.1.
-/
import Workspace.Algo.OracleFold
import Workspace.Algo.WLGuarded

/-!
# Iteration with a per-input cost, and the tuple table

The Master Algorithm's RAM chain builds the table of all `t`-tuples only below the arity
guard `t ≤ (log n + 1)^c` (`Algo.aggTable`), which is what keeps its cost quasipolynomial.
Theorem 13.2.1 is stated for every `t` with `max{8, 2 + log₂ n} < t < m/10`, at cost
`m^{O(t)}`. This file gives the unguarded table with that cost.

* `Algo.exists_iterProg`: a set-up, `N` rounds of a step, and a read-off, all `RAM.PolyFun`,
  run within `(N + 2) · poly(size of the input + B)` steps, where `B` bounds the states.
* `Algo.exists_tuplesProg`: the list of all `k`-tuples over `dom`
  (`Algo.tuplesOf dom k`, `|dom|^k` tuples) within
  `(k + 2) · poly(size + (|dom| + 1)^k · (k + 1) · (size + 1))` steps.
-/

namespace Algo
open RAM

/-- The `j`-th state of an iteration is small: the bound used by `Algo.exists_iterProg`. -/
theorem size_iter_pair_le {σ : Type*} [Enc σ] (k : ℕ) (s : σ) :
    Enc.size ((k, s) : ℕ × σ) ≤ 2 * Enc.size k + 2 * Enc.size s := size_pair_le' _

set_option maxHeartbeats 4000000 in
/-- **Bounded iteration on the RAM, with a per-input cost.** A set-up `setup a = (N, s₀)`,
`N` rounds of `step`, and a read-off, all `RAM.PolyFun`: one program runs it within
`(N + 2) · pw c d (size a + B)` steps, where `B` bounds the states `step^[j] s₀`, `j ≤ N`. -/
theorem exists_iterProg {α σ β : Type*} [Enc α] [Enc σ] [Enc β] [Inhabited α] [Inhabited σ]
    {setup : α → ℕ × σ} {step : σ → σ} {read : σ → β}
    (h1 : PolyFun setup) (h2 : PolyFun step) (h3 : PolyFun read) :
    ∃ (P : Program) (c d : ℕ), Wf P ∧ ∀ (a : α) (B : ℕ),
      (∀ j ≤ (setup a).1, Enc.size (step^[j] (setup a).2) ≤ B) →
      RunsOn 16 P a (read (step^[(setup a).1] (setup a).2))
        (((setup a).1 + 2) * pw c d (Enc.size a + B)) := by
  obtain ⟨Pset, c1, d1, hset, hset_s⟩ := polyFun_witness h1
  obtain ⟨Pst, c2, d2, hst, -⟩ := polyFun_witness h2
  obtain ⟨Prd, c3, d3, hrd, -⟩ := polyFun_witness h3
  obtain ⟨Ppred, c4, d4, hpred, -⟩ := polyFun_witness
    ((polyFun_fst.sub (polyFun_const 1)) : PolyFun (fun p : ℕ × σ => p.1 - 1))
  obtain ⟨Psnd, c5, d5, hsnd, -⟩ := polyFun_witness
    (polyFun_snd : PolyFun (fun p : ℕ × σ => p.2))
  -- the polynomial
  obtain ⟨Z, hZ⟩ : ∃ f : ℕ → ℕ, ∀ X, f X = 2 * pw c1 d1 X + 2 * X + 4 := ⟨_, fun _ => rfl⟩
  obtain ⟨Gf, hGf⟩ : ∃ f : ℕ → ℕ, ∀ X, f X = pw c1 d1 X + 19 * Z X + 19 * pw c1 d1 X
      + 19 * X + 10 * pw c4 d4 (Z X) + 10 * pw c5 d5 (Z X) + 10 * pw c2 d2 X + 378
      + pw c3 d3 X + 1 := ⟨_, fun _ => rfl⟩
  have hGp : PolyBound Gf := by
    have pZ : PolyBound Z := by
      rw [show Z = _ from funext hZ]
      exact (((polyBound_const 2).mul (polyBound_pw c1 d1)).add
        ((polyBound_const 2).mul polyBound_id)).add (polyBound_const 4)
    rw [show Gf = _ from funext hGf]
    exact (((((((((polyBound_pw c1 d1).add ((polyBound_const 19).mul pZ)).add
      ((polyBound_const 19).mul (polyBound_pw c1 d1))).add
      ((polyBound_const 19).mul polyBound_id)).add
      ((polyBound_const 10).mul ((polyBound_pw c4 d4).comp pZ))).add
      ((polyBound_const 10).mul ((polyBound_pw c5 d5).comp pZ))).add
      ((polyBound_const 10).mul (polyBound_pw c2 d2))).add (polyBound_const 378)).add
      (polyBound_pw c3 d3)).add (polyBound_const 1)
  obtain ⟨c, d, hcd⟩ := hGp
  let Body : Program := Pairing.pairProg 16 Ppred (RAM.seq Psnd Pst)
  have hBodyWf : Wf Body := Pairing.wf_pairProg 16 (hpred.runsOn default).wf
    (wf_seq (hsnd.runsOn default).wf (hst.runsOn default).wf)
  refine ⟨RAM.seq Pset (RAM.seq (whileNz 18 Body) (RAM.seq Psnd Prd)), c, d, ?_, ?_⟩
  · exact wf_seq (hset.runsOn default).wf (wf_seq (wf_whileNz hBodyWf)
      (wf_seq (hsnd.runsOn default).wf (hrd.runsOn default).wf))
  intro a B hB
  obtain ⟨M, hM⟩ : ∃ M, M = Enc.size a := ⟨_, rfl⟩
  set N := (setup a).1 with hN
  set s₀ := (setup a).2 with hs₀
  have hZa : Enc.size (setup a) ≤ pw c1 d1 M := by
    have := hset_s a; rw [← hM] at this; exact this
  have hNs : Enc.size N ≤ pw c1 d1 M := le_trans (size_fst_le' (setup a)) hZa
  have hsize_k : ∀ k ≤ N, Enc.size k ≤ pw c1 d1 M := fun k hk =>
    le_trans (size_nat_le_of_le hk) hNs
  have hZM := hZ (M + B)
  have hGM := hcd (M + B)
  rw [hGf] at hGM
  have hmono1 : pw c1 d1 M ≤ pw c1 d1 (M + B) := pw_mono c1 d1 (by omega)
  -- one round of the loop
  have hbody : ∀ j < N, RunsOn 16 Body ((N - j, step^[j] s₀) : ℕ × σ)
      ((N - (j + 1), step^[j + 1] s₀) : ℕ × σ)
      (10 * pw c4 d4 (Z (M + B)) + 10 * pw c5 d5 (Z (M + B)) + 10 * pw c2 d2 (M + B)
        + 19 * Z (M + B) + 19 * pw c1 d1 (M + B) + 19 * (M + B) + 376) := by
    intro j hj
    set p : ℕ × σ := (N - j, step^[j] s₀) with hp
    have r := RunsOn.pair (K := 16) (by omega) (hpred.runsOn p)
      ((hsnd.runsOn p).seq (hst.runsOn p.2))
    have e : ((p.1 - 1, step p.2) : ℕ × σ) = ((N - (j + 1), step^[j + 1] s₀) : ℕ × σ) := by
      rw [Function.iterate_succ_apply']
      simp only [hp]
      congr 1
    have ep1 : p.1 - 1 = N - (j + 1) := by simp only [hp]; omega
    have ep2 : step p.2 = step^[j + 1] s₀ := by rw [Function.iterate_succ_apply']
    rw [e] at r
    refine r.mono ?_
    rw [ep1, ep2]
    have hsj : Enc.size (step^[j] s₀) ≤ B := hB j (by omega)
    have hsj1 : Enc.size (step^[j + 1] s₀) ≤ B := hB (j + 1) (by omega)
    have hk1 : Enc.size (N - j) ≤ pw c1 d1 M := hsize_k _ (by omega)
    have hk2 : Enc.size (N - (j + 1)) ≤ pw c1 d1 M := hsize_k _ (by omega)
    have hp1 : Enc.size p ≤ 2 * Enc.size (N - j) + 2 * Enc.size (step^[j] s₀) := size_pair_le' p
    have hpZ : Enc.size p ≤ Z (M + B) := by omega
    have q1 : c4 * (Enc.size p + 1) ^ d4 ≤ pw c4 d4 (Z (M + B)) := pw_mono c4 d4 hpZ
    have q2 : c5 * (Enc.size p + 1) ^ d5 ≤ pw c5 d5 (Z (M + B)) := pw_mono c5 d5 hpZ
    have q3 : c2 * (Enc.size p.2 + 1) ^ d2 ≤ pw c2 d2 (M + B) := pw_mono c2 d2 (by
      show Enc.size (step^[j] s₀) ≤ M + B; omega)
    show 19 * Enc.size p + 19 * Enc.size (N - (j + 1)) + 19 * Enc.size (step^[j + 1] s₀)
      + 10 * (c4 * (Enc.size p + 1) ^ d4)
      + 10 * (c5 * (Enc.size p + 1) ^ d5 + c2 * (Enc.size p.2 + 1) ^ d2) + 11 * 16 + 200 ≤ _
    omega
  have hloop := runsOn_iterate_sum (K := 16) (Q := Body) (step := step) hBodyWf N s₀ _ hbody
  have hs1 : RunsOn 16 Pset a ((N, s₀) : ℕ × σ) (c1 * (Enc.size a + 1) ^ d1) := hset.runsOn a
  have hs3 := (hsnd.runsOn ((0 : ℕ), step^[N] s₀)).seq (hrd.runsOn (step^[N] s₀))
  have hall := hs1.seq (hloop.seq hs3)
  refine hall.mono ?_
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul]
  have hsN : Enc.size (step^[N] s₀) ≤ B := hB N le_rfl
  have hz : Enc.size (((0 : ℕ), step^[N] s₀) : ℕ × σ) ≤ Z (M + B) := by
    have h1 := size_pair_le' (((0 : ℕ), step^[N] s₀) : ℕ × σ)
    have h2 : Enc.size (0 : ℕ) = 2 := by rw [Small.size_nat]; rfl
    simp only at h1; omega
  have q1 : c5 * (Enc.size (((0 : ℕ), step^[N] s₀) : ℕ × σ) + 1) ^ d5 ≤ pw c5 d5 (Z (M + B)) :=
    pw_mono c5 d5 hz
  have q2 : c3 * (Enc.size (step^[N] s₀) + 1) ^ d3 ≤ pw c3 d3 (M + B) := pw_mono c3 d3 (by omega)
  have q0 : c1 * (M + 1) ^ d1 ≤ pw c1 d1 (M + B) := hmono1
  set G := pw c1 d1 (M + B) + 19 * Z (M + B) + 19 * pw c1 d1 (M + B) + 19 * (M + B)
      + 10 * pw c4 d4 (Z (M + B)) + 10 * pw c5 d5 (Z (M + B)) + 10 * pw c2 d2 (M + B) + 378
      + pw c3 d3 (M + B) + 1 with hG
  have hW : N * (10 * pw c4 d4 (Z (M + B)) + 10 * pw c5 d5 (Z (M + B)) + 10 * pw c2 d2 (M + B)
      + 19 * Z (M + B) + 19 * pw c1 d1 (M + B) + 19 * (M + B) + 376 + 2) ≤ N * G :=
    Nat.mul_le_mul_left _ (by omega)
  have hNG : (N + 2) * G ≤ (N + 2) * pw c d (M + B) := Nat.mul_le_mul_left _ hGM
  have hexp : (N + 2) * G = N * G + 2 * G := by ring
  rw [← hM]
  omega

/-! ## The tuple table -/

/-- Set-up of the tuple table: `k` rounds from `(dom, [[]])`. -/
def tuplesSetup (p : List ℕ × ℕ) : ℕ × (List ℕ × List (List ℕ)) := (p.2, (p.1, [[]]))

theorem polyFun_tuplesSetup : PolyFun tuplesSetup :=
  (polyFun_snd.pair (polyFun_fst.pair (polyFun_const [[]]))).of_eq (fun _ => rfl)

/-- The size of the table of all `j`-tuples over `dom`. -/
theorem size_tuplesOf_le (dom : List ℕ) (j : ℕ) :
    Enc.size (tuplesOf dom j)
      ≤ 1 + dom.length ^ j * (2 * (1 + j * (2 * Enc.size dom + 1)) + 1) := by
  have hent : ∀ t ∈ tuplesOf dom j, Enc.size t ≤ 1 + j * (2 * Enc.size dom + 1) := by
    intro t ht
    obtain ⟨hlen, hmem⟩ := (mem_tuplesOf dom j t).1 ht
    have h := size_list_le_of_entries t (Enc.size dom) (fun x hx => size_mem_le (hmem x hx))
    rw [hlen] at h
    exact h
  have h := size_list_le_of_entries (tuplesOf dom j) _ hent
  rwa [length_tuplesOf] at h

/-- The state bound of the tuple table, for all rounds up to `k`. -/
def tuplesBound (L S k : ℕ) : ℕ :=
  2 * S + 2 * (1 + (L + 1) ^ k * (2 * (1 + k * (2 * S + 1)) + 1))

theorem size_tabState_le (dom : List ℕ) {j k : ℕ} (hj : j ≤ k) :
    Enc.size (tabStep^[j] ((dom, [[]]) : List ℕ × List (List ℕ)))
      ≤ tuplesBound dom.length (Enc.size dom) k := by
  rw [tabStep_iterate]
  have h1 := size_pair_le' ((dom, tuplesOf dom j) : List ℕ × List (List ℕ))
  have h2 := size_tuplesOf_le dom j
  have h3 : dom.length ^ j ≤ (dom.length + 1) ^ k :=
    le_trans (Nat.pow_le_pow_left (by omega) j) (Nat.pow_le_pow_right (by omega) hj)
  have h4 : 2 * (1 + j * (2 * Enc.size dom + 1)) + 1 ≤ 2 * (1 + k * (2 * Enc.size dom + 1)) + 1 := by
    have := Nat.mul_le_mul_right (2 * Enc.size dom + 1) hj
    omega
  have h5 := Nat.mul_le_mul h3 h4
  simp only at h1
  unfold tuplesBound
  omega

/-- **The table of all `k`-tuples over `dom` on the RAM**, without an arity guard: within
`(k + 2) · pw c d (size (dom, k) + tuplesBound |dom| (size dom) k)` steps. -/
theorem exists_tuplesProg :
    ∃ (P : Program) (c d : ℕ), Wf P ∧ ∀ (dom : List ℕ) (k : ℕ),
      RunsOn 16 P ((dom, k) : List ℕ × ℕ) (tuplesOf dom k)
        ((k + 2) * pw c d (Enc.size ((dom, k) : List ℕ × ℕ)
          + tuplesBound dom.length (Enc.size dom) k)) := by
  obtain ⟨P, c, d, hwf, hrun⟩ := exists_iterProg polyFun_tuplesSetup polyFun_tabStep
    (polyFun_snd : PolyFun (fun s : List ℕ × List (List ℕ) => s.2))
  refine ⟨P, c, d, hwf, fun dom k => ?_⟩
  have h := hrun (dom, k) (tuplesBound dom.length (Enc.size dom) k)
    (fun j hj => size_tabState_le dom hj)
  have e : (tabStep^[(tuplesSetup (dom, k)).1] (tuplesSetup (dom, k)).2).2 = tuplesOf dom k := by
    show (tabStep^[k] ((dom, [[]]) : List ℕ × List (List ℕ))).2 = _
    rw [tabStep_iterate]
  rw [e] at h
  exact h

end Algo
