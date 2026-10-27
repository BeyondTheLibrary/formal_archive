/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: a unary counter on the RAM.
-/
import Workspace.Algo.LocalCertRAM
import Workspace.Machine.Build
import Workspace.Machine.ListOps2
import Workspace.Machine.RunsOnLoop

/-!
# A unary counter

`Enc ℕ` measures a number by its bit length, so a bound of the form `poly(size + N)` cannot be
read off a number `N` in the input.  `Algo.exists_padProg` writes `N` zeros next to the input,
in time polynomial in `size + N`; a polynomial-time routine run on the padded input then runs in
time polynomial in `size + N`.  This is how the cost `poly(size) · |G : H|` of Prop. 11.1.6 and
the cost `poly(size) · n^{O(k)}` of Theorems 8.1.2 and 8.1.5 are stated.

No axiom and no `sorry`.
-/

namespace Algo

open RAM

/-! ## A unary counter -/

/-- One step of the padding loop: put a `0` in front. -/
def padStep {α : Type} (s : α × List ℕ) : α × List ℕ := (s.1, 0 :: s.2)

theorem padStep_iterate {α : Type} (a : α) : ∀ j, padStep^[j] ((a, []) : α × List ℕ)
    = (a, List.replicate j 0)
  | 0 => rfl
  | j + 1 => by
      rw [Function.iterate_succ_apply', padStep_iterate a j]
      rfl

theorem polyFun_padStep {α : Type} [Enc α] : PolyFun (padStep (α := α)) :=
  (polyFun_fst.pair (((polyFun_const 0).pair polyFun_snd).comp polyFun_cons)).of_eq
    (fun _ => rfl)

theorem size_replicate_zero_le (j : ℕ) : Enc.size (List.replicate j 0) ≤ 1 + 5 * j := by
  have h := size_list_le_of_entries (List.replicate j 0) 2 (fun a ha => by
    rw [List.eq_of_mem_replicate ha]
    show Enc.size (0 : ℕ) ≤ 2
    rw [Small.size_nat]; simp)
  simp only [List.length_replicate] at h
  omega

/-- **The unary counter.**  A loop of `N` rounds turns `(N, (a, []))` into
`(0, (a, [0, …, 0]))` with `N` zeros, in time polynomial in `size a + N`. -/
theorem exists_padProg (α : Type) [Enc α] [Inhabited α] :
    ∃ (P : Program) (c d : ℕ), Wf P ∧ ∀ (a : α) (N : ℕ),
      RunsOn 16 P ((N, (a, [])) : ℕ × (α × List ℕ))
        ((0, (a, List.replicate N 0)) : ℕ × (α × List ℕ)) (pw c d (Enc.size a + N)) := by
  have hbody : PolyFun (fun s : ℕ × (α × List ℕ) => (s.1 - 1, padStep s.2)) :=
    (polyFun_fst.sub (polyFun_const 1)).pair (polyFun_snd.comp polyFun_padStep)
  obtain ⟨Pb, cb, db, hPb, -⟩ := polyFun_witness hbody
  obtain ⟨G, hGd⟩ : ∃ G : ℕ → ℕ, ∀ t, G t = t * (pw cb db (22 * t + 8) + 2) + 1 :=
    ⟨_, fun _ => rfl⟩
  have hG : PolyBound G := by
    rw [show G = fun t => t * (pw cb db (22 * t + 8) + 2) + 1 from funext hGd]
    exact (polyBound_id.mul (((polyBound_pw cb db).comp (((polyBound_const 22).mul
      polyBound_id).add (polyBound_const 8))).add (polyBound_const 2))).add (polyBound_const 1)
  obtain ⟨c, d, hcd⟩ := hG
  have hwf : Wf Pb := CleanComputeAt.wf' hPb
  refine ⟨whileNz (16 + 2) Pb, c, d, wf_whileNz hwf, fun a N => ?_⟩
  have hsz : ∀ j ≤ N, Enc.size ((N - j, padStep^[j] ((a, []) : α × List ℕ)) : ℕ × (α × List ℕ))
      ≤ 22 * (Enc.size a + N) + 8 := by
    intro j hj
    rw [padStep_iterate]
    have h1 := size_pair_le' ((N - j, (a, List.replicate j 0)) : ℕ × (α × List ℕ))
    have h2 := size_pair_le' ((a, List.replicate j 0) : α × List ℕ)
    have h3 := size_replicate_zero_le j
    have h4 : Enc.size (N - j) ≤ N + 2 := by
      rw [Small.size_nat]; have := size_le_self (N - j); omega
    simp only at h1 h2
    omega
  have hloop := runsOn_iterate_sum (K := 16) (Q := Pb) (step := padStep) hwf N
    ((a, []) : α × List ℕ) (fun j => pw cb db (Enc.size
      ((N - j, padStep^[j] ((a, []) : α × List ℕ)) : ℕ × (α × List ℕ)))) (fun j hj => by
      have r := hPb.runsOn ((N - j, padStep^[j] ((a, []) : α × List ℕ)) : ℕ × (α × List ℕ))
      have e : ((N - j, padStep^[j] ((a, []) : α × List ℕ)).1 - 1,
          padStep (N - j, padStep^[j] ((a, []) : α × List ℕ)).2)
          = ((N - (j + 1), padStep^[j + 1] ((a, []) : α × List ℕ)) : ℕ × (α × List ℕ)) := by
        rw [Function.iterate_succ_apply']
        simp only
        congr 1
      rw [e] at r
      exact r)
  rw [padStep_iterate] at hloop
  refine hloop.mono ?_
  beta_reduce
  have hsum : ∑ j ∈ Finset.range N, (pw cb db (Enc.size
      ((N - j, padStep^[j] ((a, []) : α × List ℕ)) : ℕ × (α × List ℕ))) + 2)
      ≤ ∑ _j ∈ Finset.range N, (pw cb db (22 * (Enc.size a + N) + 8) + 2) :=
    Finset.sum_le_sum (fun j hj => by
      have := pw_mono cb db (hsz j (le_of_lt (Finset.mem_range.1 hj)))
      omega)
  rw [Finset.sum_const, Finset.card_range, smul_eq_mul] at hsum
  have h1 : N * (pw cb db (22 * (Enc.size a + N) + 8) + 2)
      ≤ (Enc.size a + N) * (pw cb db (22 * (Enc.size a + N) + 8) + 2) :=
    Nat.mul_le_mul_right _ (by omega)
  have h2 := hcd (Enc.size a + N)
  rw [hGd] at h2
  have e : c * (Enc.size a + N + 1) ^ d = pw c d (Enc.size a + N) := rfl
  omega

end Algo
