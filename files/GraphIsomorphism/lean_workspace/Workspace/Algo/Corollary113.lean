/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

§1.1, Corollary 1.1.3 on the RAM.
-/
import Workspace.Algo.OrbitTime

/-!
# Corollary 1.1.3

> As an immediate consequence we obtain a slightly stronger result: only the length of the
> largest orbit of `G` matters.
>
> **Corollary 1.1.3.** The SI problem can be solved in time, polynomial in `n` (the length of
> the strings) and quasipolynomial in `n₀(G)`, the length of the largest orbit of `G`.

The routine of Theorem 1.1.1 is `Algo.siWorkspaceRoutine`; the reduction to the orbits and its
cost are `Algo.orbit_workspace_of` (`Workspace/Algo/OrbitTime.lean`). This file turns the
quasipolynomial of `normSIBound n₀` into a quasipolynomial of `n₀`, frames the routine by the
bridge to the top-level convention, and collects the polynomial and quasipolynomial factors into
the one-constant form `RAM.Targets.polyQuasiBound`.

## Main results

* `Algo.orbit_workspace`: Corollary 1.1.3 in the workspace convention (used again for
  Corollary 1.1.4);
* `Algo.polyQuasi_absorb`: `c (N+1)^d · 2^((log M + 2)^{c'})` is at most
  `polyQuasiBound (c + d + c') N M` when `N ≥ 1`;
* `Algo.corollary_1_1_3`: `RAM.Targets.Corollary_1_1_3_statement`.
-/

namespace Algo
open RAM RAM.Targets Babai Equiv

/-- **Corollary 1.1.3 in the workspace convention**: one program, and constants `c, d, c'`, such
that on every input of String Isomorphism the program halts with an admissible answer of size at
most `chainBound` of the input size `N`, within `c (N + 1)^d · 2^((log₂ n₀(G) + 2)^{c'})` steps. -/
theorem orbit_workspace :
    ∃ (Prog : Program) (c d c' : ℕ), ∀ (n s : ℕ) (a : SIInput n s),
      ∃ b, SIRel n s a b ∧ Enc.size b ≤ chainBound (Enc.size a) ∧
        RunsOn 16 Prog a b (pw c d (Enc.size a) *
          2 ^ ((Nat.log 2 (maxOrbitLength a.1) + 2) ^ c')) := by
  obtain ⟨P, T, S, ⟨cT, hT⟩, hSb, hSmono, hP⟩ := siWorkspaceRoutine
  obtain ⟨Prog, c, d, hrun⟩ := orbit_workspace_of (P := P) (T := T) (S := S) hP hT hSb hSmono
  obtain ⟨c', hc'⟩ := (quasiPolyBound_witness cT).comp_poly polyBound_normSIBound
  refine ⟨Prog, c, d, c', fun n s a => ?_⟩
  obtain ⟨b, hb, hsz, hr⟩ := hrun n s a
  exact ⟨b, hb, hsz, hr.mono (Nat.mul_le_mul_left _ (hc' _))⟩

/-- **Absorbing the constants.**  For `N ≥ 1`, a polynomial witness times a quasipolynomial
witness is at most the one-constant bound `polyQuasiBound`. -/
theorem polyQuasi_absorb {c d c' N M : ℕ} (hN : 1 ≤ N) :
    pw c d N * 2 ^ ((Nat.log 2 M + 2) ^ c') ≤ polyQuasiBound (c + d + c') N M := by
  unfold pw polyQuasiBound
  have h2 : 2 ≤ N + 1 := by omega
  have hc : c ≤ (N + 1) ^ c :=
    le_trans (Nat.lt_two_pow_self).le (Nat.pow_le_pow_left h2 c)
  have hpoly : c * (N + 1) ^ d ≤ (N + 1) ^ (c + d + c') := by
    calc c * (N + 1) ^ d ≤ (N + 1) ^ c * (N + 1) ^ d := Nat.mul_le_mul_right _ hc
      _ = (N + 1) ^ (c + d) := by rw [pow_add]
      _ ≤ (N + 1) ^ (c + d + c') := Nat.pow_le_pow_right (by omega) (by omega)
  have hq : (2 : ℕ) ^ ((Nat.log 2 M + 2) ^ c') ≤ 2 ^ ((Nat.log 2 M + 2) ^ (c + d + c')) :=
    Nat.pow_le_pow_right (by norm_num) (Nat.pow_le_pow_right (by omega) (by omega))
  exact Nat.mul_le_mul hpoly hq

/-- **Corollary 1.1.3** (§1.1): String Isomorphism is solvable in time polynomial in the input
size and quasipolynomial in `n₀(G)`, the length of the largest orbit of `G`, on the RAM model of
`Workspace/Machine/`. The route is the one the paper's "immediate consequence" implies: Luks's
Chain Rule over the orbits of `G` (Eqs. (63)–(64)), each orbit handled by restriction
(Obs. 11.1.11 with Eq. (59)) and one call of the routine of Theorem 1.1.1 on at most `n₀(G)`
points. -/
theorem corollary_1_1_3 : Corollary_1_1_3_statement := by
  obtain ⟨Prog, c, d, c', hrun⟩ := orbit_workspace
  have hApoly : PolyBound (fun m => 18 * m + 112 + 7 * chainBound m + pw c d m) :=
    ((((polyBound_const 18).mul polyBound_id).add (polyBound_const 112)).add
      ((polyBound_const 7).mul polyBound_chainBound)).add (polyBound_pw c d)
  obtain ⟨cA, dA, hA⟩ := hApoly
  refine ⟨RAM.seq Bridge.up (RAM.seq Prog Bridge.down), cA + dA + c', fun n s a => ?_⟩
  obtain ⟨b, hb, hsz, hr⟩ := hrun n s a
  obtain ⟨k, hk, hhalt, hout⟩ := hr.bridge
  refine ⟨b, hb, k, le_trans hk ?_, hhalt, hout⟩
  set m := Enc.size a
  set Q := 2 ^ ((Nat.log 2 (maxOrbitLength a.1) + 2) ^ c') with hQ
  have hQ1 : 1 ≤ Q := Nat.one_le_two_pow
  have hm : 1 ≤ m := one_le_size a
  have h1 : 18 * m + 78 + (pw c d m * Q + (7 * Enc.size b + 34)) ≤
      (18 * m + 112 + 7 * chainBound m + pw c d m) * Q := by
    have e1 : (18 * m + 112 + 7 * chainBound m + pw c d m) * Q =
        (18 * m + 112 + 7 * chainBound m) * Q + pw c d m * Q := by ring
    have e2 : 18 * m + 112 + 7 * chainBound m ≤ (18 * m + 112 + 7 * chainBound m) * Q :=
      Nat.le_mul_of_pos_right _ hQ1
    omega
  have h2 : (18 * m + 112 + 7 * chainBound m + pw c d m) * Q ≤ pw cA dA m * Q :=
    Nat.mul_le_mul_right _ (hA m)
  exact le_trans h1 (le_trans h2 (polyQuasi_absorb hm))

end Algo

#print axioms Algo.corollary_1_1_3
