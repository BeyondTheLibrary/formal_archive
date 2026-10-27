/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: the pipeline `F3 ∘ F2 ∘ F1` of §5.2 with the arity `k` in the input.
-/
import Workspace.Algo.Functors
import Workspace.Algo.WLVertex

/-!
# §5.2 with the arity in the input — the debt of work package A8

`Workspace/Algo/Functors.lean` makes `F1` a `RAM.PolyFun` uniformly in `k` but `F2` only for each
*fixed* `k`, because `F2` ranges over the whole transformation monoid `𝔐_k` (Notation 5.1.5),
which has `k^k` elements, and `k^k` is not polynomial in the size of the input.

The Design Lemma needs the other reading: `k` is part of the input, bounded by
`(log₂ n + 1)^{c₀}` (`Algo.guardBound`).  Under that guard `k^k` **is** quasipolynomial, since
`k ≤ n` there, so `k^k ≤ n^k`, which is the number of rows of the table of `k`-tuples.  So the
route is the one of `Workspace/Algo/WLGuarded.lean`: build the index set `𝔐_k` by a loop of `k`
rounds under the guard (`RAM.QuasiFun.iterateSetup`), and hand it, as data, to the
index-set-parameterized routine `Algo.rawF2I`, which is a `RAM.PolyFun` with `k` nowhere in the
statement.

The other index set, the pairs `(i, j) ∈ [k]²`, is only `k²` long and needs no guard.

## Main definitions

* `Algo.pairIdxOf`, `Algo.guardedMon`, `Algo.guardedIdx` — the two index sets from the input;
* `Algo.guardedPipeline321` — `F3 ∘ F2 ∘ F1` from the domain and the relations, `k` in the input.

## Main results

* `Algo.guardedIdx_of_guard` — under the guard the index sets are `Algo.idxOf k`;
* `Algo.quasiFun_guardedMon`, `Algo.quasiFun_guardedPipeline321` — both are `RAM.QuasiFun`s;
* `Algo.guardedPipeline321_spec` — the routine computes `F3 ∘ F2 ∘ F1` of the input structure.

No axiom and no `sorry`.
-/

namespace Algo

open Babai RAM

/-- The input of §5.2 from the domain: the arity carrier `ks` (only its length is read), the
vertex list, and the list of the relations of the input structure. -/
abbrev PIn : Type := (List ℕ × List ℕ) × RawRelStruct

/-! ## The index set of the equality type

`[k]²` has `k²` elements, so it is built without a guard, by the fold of
`Workspace/Algo/TupleTable.lean` at the fixed length `2`. -/

/-- The index set of the equality type `ρ(x⃗)`, built from the arity carrier. -/
def pairIdxOf (a : PIn) : List (List ℕ) := tuplesOf (List.range a.1.1.length) 2

theorem pairIdxOf_eq (a : PIn) : pairIdxOf a = pairIdx a.1.1.length := rfl

theorem polyFun_pairIdxOf : PolyFun pairIdxOf := by
  have hrange : PolyFun (fun a : PIn => List.range a.1.1.length) :=
    (polyFun_fst.comp polyFun_fst).comp polyFun_rangeLength
  exact ((hrange.comp (polyFun_tuplesOf 2)).comp polyFun_snd).of_eq (fun a => rfl)

/-! ## The index set `𝔐_k`, under the guard

`𝔐_k` is the list of all `k`-tuples over `[0, k)`, which is the very fold of
`Workspace/Algo/WLGuarded.lean` with the vertex list replaced by `List.range k`.  The guard is
the same as there — `k ≤ (log₂ n + 1)^{c₀}` with `n` the number of vertices — because that is
what makes `k^k` quasipolynomial. -/

/-- The set-up of the loop building `𝔐_k`: `k` rounds from the empty tuple over `[0, k)`, or no
round at all when the arity exceeds the guard. -/
def monSetUp (c₀ : ℕ) (a : PIn) : ℕ × (List ℕ × List (List ℕ)) :=
  if a.1.1.length ≤ guardBound c₀ a.1.2.length then
    (a.1.1.length, (List.range a.1.1.length, [[]]))
  else (0, ([], []))

/-- **The index set `𝔐_k` of Notation 5.1.5, with `k` in the input**, guarded. -/
def guardedMon (c₀ : ℕ) (a : PIn) : List (List ℕ) :=
  (tabStep^[(monSetUp c₀ a).1] (monSetUp c₀ a).2).2

theorem guardedMon_of_guard {c₀ : ℕ} {a : PIn}
    (hg : a.1.1.length ≤ guardBound c₀ a.1.2.length) :
    guardedMon c₀ a = monIdx a.1.1.length := by
  have hset : monSetUp c₀ a = (a.1.1.length, (List.range a.1.1.length, [[]])) := if_pos hg
  rw [guardedMon, hset]
  show (tabStep^[a.1.1.length]
    ((List.range a.1.1.length, [[]]) : List ℕ × List (List ℕ))).2 = _
  rw [tabStep_iterate]
  rfl

/-- **Both index sets of `F2`, with `k` in the input.** -/
def guardedIdx (c₀ : ℕ) (a : PIn) : IdxP := (pairIdxOf a, guardedMon c₀ a)

/-- Under the guard the routine has exactly the index sets of the arity read off the input. -/
theorem guardedIdx_of_guard {c₀ : ℕ} {a : PIn}
    (hg : a.1.1.length ≤ guardBound c₀ a.1.2.length) :
    guardedIdx c₀ a = idxOf a.1.1.length := by
  rw [guardedIdx, guardedMon_of_guard hg, pairIdxOf_eq, idxOf]

/-! ## The size of the loop's state -/

/-- The quasipolynomial bound on the size of every state of the loop building `𝔐_k`. -/
def monSizeBound (c₀ N : ℕ) : ℕ :=
  2 * (1 + N * (2 * (N + 2) + 1))
    + 2 * (1 + 2 ^ ((Nat.log 2 N + 2) ^ (c₀ + 1))
        * (2 * (1 + (Nat.log 2 N + 2) ^ c₀ * (2 * (N + 2) + 1)) + 1))

theorem quasiPolyBound_monSizeBound (c₀ : ℕ) : QuasiPolyBound (monSizeBound c₀) := by
  have h1 : PolyBound (fun n : ℕ => 2 * (n + 2) + 1) :=
    ((polyBound_const 2).mul (polyBound_id.add (polyBound_const 2))).add (polyBound_const 1)
  have hG : PolyBound (fun n : ℕ => 1 + n * (2 * (n + 2) + 1)) :=
    (polyBound_const 1).add (polyBound_id.mul h1)
  have hT : PolyBound (fun n : ℕ => 1 + (Nat.log 2 n + 2) ^ c₀ * (2 * (n + 2) + 1)) :=
    (polyBound_const 1).add ((polyBound_logPow c₀).mul h1)
  exact ((polyBound_const 2).quasiPoly.mul hG.quasiPoly).add
    ((polyBound_const 2).quasiPoly.mul ((polyBound_const 1).quasiPoly.add
      ((quasiPolyBound_witness (c₀ + 1)).mul
        (((polyBound_const 2).mul hT).add (polyBound_const 1)).quasiPoly)))

theorem le_monSizeBound (c₀ N : ℕ) : 4 ≤ monSizeBound c₀ N := by
  rw [monSizeBound]
  have h1 : 1 ≤ 1 + N * (2 * (N + 2) + 1) := Nat.le_add_right 1 _
  have h2 : 1 ≤ 1 + 2 ^ ((Nat.log 2 N + 2) ^ (c₀ + 1))
      * (2 * (1 + (Nat.log 2 N + 2) ^ c₀ * (2 * (N + 2) + 1)) + 1) := Nat.le_add_right 1 _
  omega

/-- Each index is a natural below `k ≤ N`, so it occupies at most `N + 2` bits. -/
theorem size_idx_le {N i : ℕ} (h : i ≤ N) : Enc.size i ≤ N + 2 := by
  have h1 : Enc.size i ≤ Enc.size N := size_nat_le_of_le h
  have h2 : Enc.size N = Nat.size N + 2 := Small.size_nat N
  have h3 : Nat.size N ≤ N := size_le_self N
  omega

/-- **The state of the loop building `𝔐_k` is quasipolynomially large.** -/
theorem size_monState_le (c₀ : ℕ) (a : PIn) (j : ℕ) (hj : j ≤ (monSetUp c₀ a).1) :
    Enc.size (tabStep^[j] (monSetUp c₀ a).2) ≤ monSizeBound c₀ (Enc.size a) := by
  set N := Enc.size a with hN
  set T := 1 + (Nat.log 2 N + 2) ^ c₀ * (2 * (N + 2) + 1) with hT
  set R := 2 ^ ((Nat.log 2 N + 2) ^ (c₀ + 1)) with hR
  by_cases hg : a.1.1.length ≤ guardBound c₀ a.1.2.length
  · set k := a.1.1.length with hk
    have hset : monSetUp c₀ a = (k, (List.range k, [[]])) := if_pos hg
    have hj' : j ≤ k := by rw [hset] at hj; exact hj
    have hstate : tabStep^[j] (monSetUp c₀ a).2 = (List.range k, tuplesOf (List.range k) j) := by
      rw [hset]; exact tabStep_iterate (List.range k) j
    rw [hstate]
    -- the arity is at most the input size
    have hkN : k ≤ N := by
      refine le_trans (length_le_size a.1.1) ?_
      exact le_trans (size_fst_le' a.1) (size_fst_le' a)
    have hnN : a.1.2.length ≤ N :=
      le_trans (length_le_size a.1.2) (le_trans (size_snd_le' a.1) (size_fst_le' a))
    have hB : j ≤ (Nat.log 2 N + 1) ^ c₀ := by
      refine le_trans (le_trans hj' hg) ?_
      rw [guardBound]
      exact Nat.pow_le_pow_left (by
        have := Nat.log_mono_right (b := 2) hnN
        omega) c₀
    have hB2 : j ≤ (Nat.log 2 N + 2) ^ c₀ :=
      le_trans hB (Nat.pow_le_pow_left (by omega) c₀)
    -- the vertex-index list
    have hrangeent : ∀ i ∈ List.range k, Enc.size i ≤ N + 2 := by
      intro i hi
      exact size_idx_le (le_trans (le_of_lt (List.mem_range.1 hi)) hkN)
    have hrange : Enc.size (List.range k) ≤ 1 + N * (2 * (N + 2) + 1) := by
      have h := size_list_le_of_entries (List.range k) (N + 2) hrangeent
      rw [List.length_range] at h
      have h2 : k * (2 * (N + 2) + 1) ≤ N * (2 * (N + 2) + 1) := Nat.mul_le_mul_right _ hkN
      omega
    -- each tuple built so far
    have hent : ∀ t ∈ tuplesOf (List.range k) j, Enc.size t ≤ T := by
      intro t ht
      obtain ⟨hlen, hmem⟩ := (mem_tuplesOf (List.range k) j t).1 ht
      have h := size_list_le_of_entries t (N + 2) (fun x hx => hrangeent x (hmem x hx))
      rw [hlen] at h
      have h2 : j * (2 * (N + 2) + 1) ≤ (Nat.log 2 N + 2) ^ c₀ * (2 * (N + 2) + 1) :=
        Nat.mul_le_mul_right _ hB2
      omega
    have hcount : (tuplesOf (List.range k) j).length ≤ R := by
      rw [length_tuplesOf, List.length_range]
      exact pow_le_quasi hkN hB
    have hlist : Enc.size (tuplesOf (List.range k) j) ≤ 1 + R * (2 * T + 1) := by
      have h := size_list_le_of_entries (tuplesOf (List.range k) j) T hent
      have h2 : (tuplesOf (List.range k) j).length * (2 * T + 1) ≤ R * (2 * T + 1) :=
        Nat.mul_le_mul_right _ hcount
      omega
    have hpair : Enc.size ((List.range k, tuplesOf (List.range k) j) : List ℕ × List (List ℕ))
        ≤ 2 * Enc.size (List.range k) + 2 * Enc.size (tuplesOf (List.range k) j) :=
      size_pair_le' _
    rw [monSizeBound, ← hT, ← hR]
    omega
  · have hset : monSetUp c₀ a = (0, ([], [])) := if_neg hg
    have hj0 : j = 0 := by rw [hset] at hj; exact Nat.le_zero.1 hj
    subst hj0
    have hstate : tabStep^[0] (monSetUp c₀ a).2
        = (([], []) : List ℕ × List (List ℕ)) := by rw [hset]; rfl
    rw [hstate]
    have h1 : Enc.size ((([], []) : List ℕ × List (List ℕ)))
        ≤ 2 * Enc.size ([] : List ℕ) + 2 * Enc.size ([] : List (List ℕ)) := size_pair_le' _
    have h2 : Enc.size ([] : List ℕ) = 1 := rfl
    have h3 : Enc.size ([] : List (List ℕ)) = 1 := rfl
    have h4 := le_monSizeBound c₀ N
    omega

/-! ## The cost -/

theorem polyFun_monSetUp (c₀ : ℕ) : PolyFun (monSetUp c₀) := by
  have hk : PolyFun (fun a : PIn => a.1.1.length) :=
    (polyFun_fst.comp polyFun_fst).comp polyFun_length
  have hbound : PolyFun (fun a : PIn => guardBound c₀ a.1.2.length) := by
    have hn : PolyFun (fun a : PIn => Nat.log 2 a.1.2.length) :=
      ((polyFun_fst.comp polyFun_snd).comp polyFun_length).comp polyFun_log2
    exact polyFun_powConst (hn.add (polyFun_const 1)) c₀
  have hrange : PolyFun (fun a : PIn => List.range a.1.1.length) :=
    (polyFun_fst.comp polyFun_fst).comp polyFun_rangeLength
  have hyes : PolyFun (fun a : PIn =>
      ((a.1.1.length, (List.range a.1.1.length, [[]])) : ℕ × (List ℕ × List (List ℕ)))) :=
    hk.pair (hrange.pair (polyFun_const [[]]))
  have hno : PolyFun (fun _ : PIn =>
      ((0, ([], [])) : ℕ × (List ℕ × List (List ℕ)))) := polyFun_const _
  refine (PolyFun.ite (hk.le hbound) hyes hno).of_eq (fun a => ?_)
  by_cases h : a.1.1.length ≤ guardBound c₀ a.1.2.length <;> simp [monSetUp, h]

/-- **The index set `𝔐_k` is computable in quasipolynomial time with `k` in the input.**  This
is the debt of work package A8: `k^k` is quasipolynomial under the guard `k ≤ (log₂ n+1)^{c₀}`. -/
theorem quasiFun_guardedMon (c₀ : ℕ) : QuasiFun (guardedMon c₀) := by
  have hstep : QuasiFun (fun x : ℕ × (List ℕ × List (List ℕ)) => (x.1 - 1, tabStep x.2)) :=
    ((polyFun_fst.sub (polyFun_const 1)).pair (polyFun_snd.comp polyFun_tabStep)).quasiFun
  refine (QuasiFun.iterateSetup (q := fun n => n) (p := monSizeBound c₀)
    (polyFun_monSetUp c₀).quasiFun hstep polyFun_snd.quasiFun ?_ polyBound_id.quasiPoly
    (size_monState_le c₀) (quasiPolyBound_monSizeBound c₀)).of_eq (fun a => rfl)
  intro a
  by_cases hg : a.1.1.length ≤ guardBound c₀ a.1.2.length
  · have hset : monSetUp c₀ a = (a.1.1.length, (List.range a.1.1.length, [[]])) := if_pos hg
    rw [hset]
    exact le_trans (length_le_size a.1.1) (le_trans (size_fst_le' a.1) (size_fst_le' a))
  · have hset : monSetUp c₀ a = (0, ([], [])) := if_neg hg
    rw [hset]
    exact Nat.zero_le _

theorem quasiFun_guardedIdx (c₀ : ℕ) : QuasiFun (guardedIdx c₀) :=
  (polyFun_pairIdxOf.quasiFun.pair (quasiFun_guardedMon c₀)).of_eq (fun a => rfl)

/-! ## §5.2 from the domain, with the arity in the input -/

theorem fst_rawWLStep_iterate : ∀ (m : ℕ) (p : RawWL), (rawWLStep^[m] p).1 = p.1
  | 0, _ => rfl
  | m + 1, p => by
      rw [Function.iterate_succ_apply, fst_rawWLStep_iterate m (rawWLStep p), rawWLStep_fst]

/-- `k`-ary WL refinement does not touch the vertex list. -/
theorem fst_rawWLStable (p : RawWL) : (rawWLStable p).1 = p.1 := by
  rw [rawWLStable_eq_iterate]; exact fst_rawWLStep_iterate _ p

/-- **§5.2 from the domain, with the arity in the input**: build the guarded table of
`k`-tuples and the two index sets of `F2`, then run `F1`, `F2`, `F3`. -/
def guardedPipeline321 (c₀ : ℕ) (a : PIn) : RawWL :=
  rawPipelineI (guardedIdx c₀ a) (guardedTable c₀ a.1, a.2)

/-- **The guarded pipeline is a `RAM.QuasiFun`**, for every fixed `c₀`, with the arity `k` read
off the input.  The answer is the refined table, which is quasipolynomially large, so the class
is `RAM.QuasiFun` and not `RAM.QuasiPolyFun`. -/
theorem quasiFun_guardedPipeline321 (c₀ : ℕ) : QuasiFun (guardedPipeline321 c₀) := by
  have hin : QuasiFun (fun a : PIn =>
      ((guardedIdx c₀ a, (guardedTable c₀ a.1, a.2)) : IdxP × RawF1In)) :=
    (quasiFun_guardedIdx c₀).pair
      ((polyFun_fst.quasiFun.comp (quasiFun_guardedTable c₀)).pair polyFun_snd.quasiFun)
  exact (hin.comp_poly polyFun_rawPipelineI).of_eq (fun a => rfl)

theorem guardedPipeline321_of_guard {c₀ : ℕ} {a : PIn}
    (hg : a.1.1.length ≤ guardBound c₀ a.1.2.length) :
    guardedPipeline321 c₀ a = rawPipeline a.1.1.length (tupleTable a.1.2 a.1.1.length, a.2) := by
  rw [guardedPipeline321, guardedIdx_of_guard hg, guardedTable_of_guard hg, rawPipeline]

/-- **§5.2 from the domain**: under the guard, the guarded pipeline computes `F3 ∘ F2 ∘ F1` of
the given relational structure on the given vertex list. -/
theorem guardedPipeline321_spec {n c₀ : ℕ} {a : PIn} (hnd : a.1.2.Nodup)
    (hmem : ∀ b, b ∈ a.1.2 ↔ b < n) (hg : a.1.1.length ≤ guardBound c₀ a.1.2.length)
    (x x' : Str (Fin n) a.1.1.length) :
    (decWL n a.1.1.length (guardedPipeline321 c₀ a)).color x
        = (decWL n a.1.1.length (guardedPipeline321 c₀ a)).color x'
      ↔ (decRel n a.1.1.length a.2).F1.F2.F3.color x
        = (decRel n a.1.1.length a.2).F1.F2.F3.color x' := by
  rw [guardedPipeline321_of_guard hg]
  exact rawPipeline_spec (a := (tupleTable a.1.2 a.1.1.length, a.2)) (wf_tupleTable hnd hmem) x x'

/-- The answer of the guarded pipeline is a well-formed table. -/
theorem guardedPipeline321_wf {n c₀ : ℕ} {a : PIn} (hnd : a.1.2.Nodup)
    (hmem : ∀ b, b ∈ a.1.2 ↔ b < n) (hg : a.1.1.length ≤ guardBound c₀ a.1.2.length) :
    RawWL.WF n a.1.1.length (guardedPipeline321 c₀ a) := by
  rw [guardedPipeline321_of_guard hg]
  exact rawPipeline_wf (a := (tupleTable a.1.2 a.1.1.length, a.2)) (wf_tupleTable hnd hmem)

/-- **Every color the guarded pipeline computes is below the number of rows of the table of
`k`-tuples.**  `F1` and `F2` rename by the rank among the tags that occur (§4.1.1), and `k`-ary
WL refinement keeps the colors below the row count, so the whole pipeline does. -/
theorem col_guardedPipeline321_le (c₀ : ℕ) (a : PIn) :
    ∀ q ∈ (guardedPipeline321 c₀ a).2,
      q.2 ≤ 2 ^ ((Nat.log 2 (Enc.size a.1) + 2) ^ (c₀ + 1)) := by
  have hrows : (rawF2I (guardedIdx c₀ a) (rawF1 (guardedTable c₀ a.1, a.2))).2.length
      ≤ 2 ^ ((Nat.log 2 (Enc.size a.1) + 2) ^ (c₀ + 1)) := by
    rw [rawF2I_length, rawF1_length]
    exact length_guardedTable_le c₀ a.1
  have hcol : ∀ q ∈ (rawF2I (guardedIdx c₀ a) (rawF1 (guardedTable c₀ a.1, a.2))).2,
      q.2 ≤ 2 ^ ((Nat.log 2 (Enc.size a.1) + 2) ^ (c₀ + 1)) := by
    intro q hq
    obtain ⟨q', hq', rfl⟩ := List.mem_map.1 hq
    refine le_trans (le_of_lt (f2NewColI_lt hq')) ?_
    rw [rawF1_length]
    exact length_guardedTable_le c₀ a.1
  exact col_rawWLStable_le hcol hrows

/-- The guarded pipeline does not touch the vertex list. -/
@[simp] theorem fst_guardedPipeline321 (c₀ : ℕ) (a : PIn) :
    (guardedPipeline321 c₀ a).1 = a.1.2 := by
  rw [guardedPipeline321, rawPipelineI, fst_rawWLStable, rawF2I_fst, rawF1_fst]
  by_cases hg : a.1.1.length ≤ guardBound c₀ a.1.2.length
  · rw [guardedTable_of_guard hg]; rfl
  · rw [guardedTable_of_not_guard hg]

end Algo
