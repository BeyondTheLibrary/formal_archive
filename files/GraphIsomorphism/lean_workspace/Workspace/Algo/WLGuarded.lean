/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: the table of `k`-tuples with `k` in the input and `k = O(log n)` (§5.4.2).
-/
import Workspace.Algo.TupleTable
import Workspace.Machine.QuasiFun
import Workspace.Machine.Mul

/-!
# §5.4.2 — the guarded table of `k`-tuples, with `k` in the input

`Workspace/Algo/TupleTable.lean` builds the table of `k`-tuples for each *fixed* `k`, which is
the paper's "`n^{O(k)}` with `k` fixed".  The Design Lemma and Sec. 13 need the other reading:
`k` is part of the input and is bounded by `(log₂ n + 1)^{c₀}`, and the cost is then
`n^{O(log^{c₀} n)}`, a quasipolynomial.

Two things have to change for that statement to be sayable.

* **The arity may not be a machine natural.**  A routine that loops `k` times has to read `k`
  off a list of length `k`, since `Enc ℕ` measures a natural by its bit length.  So the input is
  the pair `(ks, dom)` of a list of length `k` and the list of vertices, and the table builder is
  one loop over `ks`, not a meta-level recursion on `k`: one round puts every vertex in front of
  every tuple built so far (`Algo.tabStep`).
* **The answer is quasipolynomially large.**  `RAM.QuasiPolyFun` carries a *polynomial* bound on
  the size of the answer, and the table has about `k · n^k` entries.  The class for this is
  `RAM.QuasiFun` (`Workspace/Machine/QuasiFun.lean`), and the loop is run by
  `RAM.QuasiFun.iterateSetup`, whose state bound is quasipolynomial.

The guard sits inside the routine, not in a hypothesis: a `RAM.QuasiFun` is a total function, so
the routine answers the empty table on the given vertex list when `k` exceeds the guard.

## Main definitions

* `Algo.guardBound c₀ n = (log₂ n + 1) ^ c₀` — the guard of the arity;
* `Algo.tabStep`, `Algo.tabRead`, `Algo.tabSetUp` — the loop;
* `Algo.guardedTable`, `Algo.guardedPipeline`.

## Main results

* `Algo.guardedTable_of_guard`, `Algo.guardedTable_of_not_guard` — what the routine answers;
* `Algo.quasiFun_guardedTable`, `Algo.quasiFun_guardedPipeline` — both are `RAM.QuasiFun`s, for
  every fixed `c₀`.

No axiom and no `sorry`.
-/

namespace Algo

open Babai RAM

/-! ## Counting the tuples

The size bound below needs the number of `j`-tuples, and that is `n ^ j` whether or not the
vertex list is duplicate-free. -/

theorem length_extendStep (dom : List ℕ) : ∀ L : List (List ℕ),
    (extendStep (dom, L)).length = L.length * dom.length
  | [] => by simp [extendStep]
  | t :: L => by
      have h : extendStep (dom, t :: L)
          = dom.map (fun y => y :: t) ++ extendStep (dom, L) := by
        simp [extendStep]
      rw [h, List.length_append, List.length_map, length_extendStep dom L,
        List.length_cons, add_one_mul]
      exact Nat.add_comm _ _

theorem length_tuplesOf (dom : List ℕ) : ∀ j : ℕ, (tuplesOf dom j).length = dom.length ^ j
  | 0 => rfl
  | j + 1 => by
      rw [tuplesOf_succ, length_extendStep, length_tuplesOf dom j, pow_succ]

/-! ## The loop -/

/-- The guard on the arity: `k ≤ (log₂ n + 1)^{c₀}`, the bound `k = O(log n)` of the Design
Lemma read with the exponent `c₀` the caller fixes. -/
def guardBound (c₀ n : ℕ) : ℕ := (Nat.log 2 n + 1) ^ c₀

/-- One round of the table builder: put every vertex in front of every tuple built so far,
keeping the vertex list. -/
def tabStep (s : List ℕ × List (List ℕ)) : List ℕ × List (List ℕ) := (s.1, extendStep s)

theorem tabStep_iterate (dom : List ℕ) :
    ∀ j : ℕ, tabStep^[j] ((dom, [[]]) : List ℕ × List (List ℕ)) = (dom, tuplesOf dom j)
  | 0 => rfl
  | j + 1 => by
      rw [Function.iterate_succ_apply', tabStep_iterate dom j, tuplesOf_succ]
      rfl

/-- The read-off: color every tuple `0`. -/
def tabRead (s : List ℕ × List (List ℕ)) : RawWL := (s.1, s.2.map (fun t => (t, 0)))

/-- The set-up: the number of rounds and the start state.  The arity is the length of the first
component of the input; when it exceeds the guard the loop is run zero times and the answer is
the empty table on the given vertex list. -/
def tabSetUp (c₀ : ℕ) (a : List ℕ × List ℕ) : ℕ × (List ℕ × List (List ℕ)) :=
  if a.1.length ≤ guardBound c₀ a.2.length then (a.1.length, (a.2, [[]]))
  else (0, (a.2, []))

/-- **The guarded table builder.**  On input `(ks, dom)` it builds the table of all
`ks.length`-tuples over `dom`, unless `ks.length` exceeds the guard, in which case it answers the
empty table on `dom`. -/
def guardedTable (c₀ : ℕ) (a : List ℕ × List ℕ) : RawWL :=
  tabRead (tabStep^[(tabSetUp c₀ a).1] (tabSetUp c₀ a).2)

theorem guardedTable_of_guard {c₀ : ℕ} {a : List ℕ × List ℕ}
    (hg : a.1.length ≤ guardBound c₀ a.2.length) :
    guardedTable c₀ a = tupleTable a.2 a.1.length := by
  have hset : tabSetUp c₀ a = (a.1.length, (a.2, [[]])) := if_pos hg
  rw [guardedTable, hset]
  show tabRead (tabStep^[a.1.length] ((a.2, [[]]) : List ℕ × List (List ℕ))) = _
  rw [tabStep_iterate]
  rfl

theorem guardedTable_of_not_guard {c₀ : ℕ} {a : List ℕ × List ℕ}
    (hg : ¬ a.1.length ≤ guardBound c₀ a.2.length) :
    guardedTable c₀ a = (a.2, []) := by
  have hset : tabSetUp c₀ a = (0, (a.2, [])) := if_neg hg
  rw [guardedTable, hset]
  rfl

/-! ## The size of the table

Under the guard the table has `n^k` rows of `k` entries each, with `k ≤ (log₂ N + 1)^{c₀}` and
`n ≤ N`, so its encoding is at most `2^{(log₂ N + 2)^{c₀+1}}` times a polynomial in `N`.  That
is a `RAM.QuasiPolyBound`, which is exactly what `RAM.QuasiFun.iterateSetup` asks of the state. -/

/-- The quasipolynomial bound on the size of every state the loop passes through. -/
def tabSizeBound (c₀ N : ℕ) : ℕ :=
  2 * N + 2 * (1 + 2 ^ ((Nat.log 2 N + 2) ^ (c₀ + 1))
    * (2 * (1 + (Nat.log 2 N + 2) ^ c₀ * (2 * N + 1)) + 1))

theorem quasiPolyBound_tabSizeBound (c₀ : ℕ) : QuasiPolyBound (tabSizeBound c₀) := by
  have h1 : PolyBound (fun n : ℕ => 2 * n + 1) :=
    ((polyBound_const 2).mul polyBound_id).add (polyBound_const 1)
  have h2 : PolyBound (fun n : ℕ => 1 + (Nat.log 2 n + 2) ^ c₀ * (2 * n + 1)) :=
    (polyBound_const 1).add ((polyBound_logPow c₀).mul h1)
  have h3 : PolyBound (fun n : ℕ => 2 * (1 + (Nat.log 2 n + 2) ^ c₀ * (2 * n + 1)) + 1) :=
    ((polyBound_const 2).mul h2).add (polyBound_const 1)
  have h4 : QuasiPolyBound (fun n : ℕ => 2 ^ ((Nat.log 2 n + 2) ^ (c₀ + 1))
      * (2 * (1 + (Nat.log 2 n + 2) ^ c₀ * (2 * n + 1)) + 1)) :=
    (quasiPolyBound_witness (c₀ + 1)).mul h3.quasiPoly
  have h5 : QuasiPolyBound (fun n : ℕ => 1 + 2 ^ ((Nat.log 2 n + 2) ^ (c₀ + 1))
      * (2 * (1 + (Nat.log 2 n + 2) ^ c₀ * (2 * n + 1)) + 1)) :=
    (polyBound_const 1).quasiPoly.add h4
  exact ((polyBound_const 2).mul polyBound_id).quasiPoly.add
    ((polyBound_const 2).quasiPoly.mul h5)

theorem le_tabSizeBound (c₀ N : ℕ) : 2 * N + 2 ≤ tabSizeBound c₀ N :=
  Nat.add_le_add_left (Nat.mul_le_mul_left 2 (Nat.le_add_right 1 _)) (2 * N)

/-- **The state of the loop is quasipolynomially large.**  This is the counting the ruling on
work package A8 asked for: under the guard, `n^k · k` is below a `RAM.QuasiPolyBound` of the
input size. -/
theorem size_state_le (c₀ : ℕ) (a : List ℕ × List ℕ) (j : ℕ) (hj : j ≤ (tabSetUp c₀ a).1) :
    Enc.size (tabStep^[j] (tabSetUp c₀ a).2) ≤ tabSizeBound c₀ (Enc.size a) := by
  obtain ⟨ks, dom⟩ := a
  set N := Enc.size ((ks, dom) : List ℕ × List ℕ) with hN
  have hdomN : Enc.size dom ≤ N := size_snd_le' ((ks, dom) : List ℕ × List ℕ)
  have hnN : dom.length ≤ N := le_trans (length_le_size dom) hdomN
  by_cases hg : ks.length ≤ guardBound c₀ dom.length
  · have hset : tabSetUp c₀ ((ks, dom) : List ℕ × List ℕ) = (ks.length, (dom, [[]])) := if_pos hg
    have hj' : j ≤ ks.length := by rw [hset] at hj; exact hj
    have hstate : tabStep^[j] (tabSetUp c₀ ((ks, dom) : List ℕ × List ℕ)).2
        = (dom, tuplesOf dom j) := by
      rw [hset]; exact tabStep_iterate dom j
    rw [hstate]
    -- the arity is below the guard
    have hlogmono : Nat.log 2 dom.length ≤ Nat.log 2 N := Nat.log_mono_right hnN
    have hB' : j ≤ (Nat.log 2 N + 1) ^ c₀ := by
      refine le_trans (le_trans hj' hg) ?_
      rw [guardBound]
      exact Nat.pow_le_pow_left (by omega) c₀
    have hB : j ≤ (Nat.log 2 N + 2) ^ c₀ :=
      le_trans hB' (Nat.pow_le_pow_left (by omega) c₀)
    -- the number of tuples is quasipolynomially bounded
    have hdom2 : dom.length ≤ 2 ^ (Nat.log 2 N + 1) := le_trans hnN (le_two_pow_log N)
    have hA : dom.length ^ j ≤ 2 ^ ((Nat.log 2 N + 2) ^ (c₀ + 1)) := by
      calc dom.length ^ j ≤ (2 ^ (Nat.log 2 N + 1)) ^ j := Nat.pow_le_pow_left hdom2 j
        _ = 2 ^ ((Nat.log 2 N + 1) * j) := by rw [← pow_mul]
        _ ≤ 2 ^ ((Nat.log 2 N + 1) ^ (c₀ + 1)) := by
            refine Nat.pow_le_pow_right (by norm_num) ?_
            calc (Nat.log 2 N + 1) * j
                ≤ (Nat.log 2 N + 1) * (Nat.log 2 N + 1) ^ c₀ := Nat.mul_le_mul_left _ hB'
              _ = (Nat.log 2 N + 1) ^ (c₀ + 1) := by rw [pow_succ]; ring
        _ ≤ 2 ^ ((Nat.log 2 N + 2) ^ (c₀ + 1)) :=
            Nat.pow_le_pow_right (by norm_num) (Nat.pow_le_pow_left (by omega) _)
    -- each tuple has `j` entries, each an entry of the vertex list
    have hent : ∀ t ∈ tuplesOf dom j, Enc.size t ≤ 1 + j * (2 * N + 1) := by
      intro t ht
      obtain ⟨hlen, hmem⟩ := (mem_tuplesOf dom j t).1 ht
      have h := size_list_le_of_entries t N
        (fun x hx => le_trans (size_mem_le (hmem x hx)) hdomN)
      rw [hlen] at h
      exact h
    have hlist : Enc.size (tuplesOf dom j)
        ≤ 1 + dom.length ^ j * (2 * (1 + j * (2 * N + 1)) + 1) := by
      have h := size_list_le_of_entries (tuplesOf dom j) (1 + j * (2 * N + 1)) hent
      rwa [length_tuplesOf] at h
    have hstep3 : dom.length ^ j * (2 * (1 + j * (2 * N + 1)) + 1)
        ≤ 2 ^ ((Nat.log 2 N + 2) ^ (c₀ + 1))
          * (2 * (1 + (Nat.log 2 N + 2) ^ c₀ * (2 * N + 1)) + 1) := by
      refine Nat.mul_le_mul hA ?_
      have h := Nat.mul_le_mul_right (2 * N + 1) hB
      omega
    calc Enc.size ((dom, tuplesOf dom j) : List ℕ × List (List ℕ))
        ≤ 2 * Enc.size dom + 2 * Enc.size (tuplesOf dom j) := size_pair_le' _
      _ ≤ 2 * N + 2 * (1 + dom.length ^ j * (2 * (1 + j * (2 * N + 1)) + 1)) :=
          Nat.add_le_add (Nat.mul_le_mul_left _ hdomN) (Nat.mul_le_mul_left _ hlist)
      _ ≤ tabSizeBound c₀ N :=
          Nat.add_le_add_left (Nat.mul_le_mul_left 2 (Nat.add_le_add_left hstep3 1)) (2 * N)
  · have hset : tabSetUp c₀ ((ks, dom) : List ℕ × List ℕ) = (0, (dom, [])) := if_neg hg
    have hj0 : j = 0 := by rw [hset] at hj; exact Nat.le_zero.1 hj
    subst hj0
    have hstate : tabStep^[0] (tabSetUp c₀ ((ks, dom) : List ℕ × List ℕ)).2
        = ((dom, []) : List ℕ × List (List ℕ)) := by rw [hset]; rfl
    rw [hstate]
    have h1 : Enc.size ((dom, ([] : List (List ℕ))) : List ℕ × List (List ℕ))
        ≤ 2 * Enc.size dom + 2 * Enc.size ([] : List (List ℕ)) := size_pair_le' _
    have h2 : Enc.size ([] : List (List ℕ)) = 1 := rfl
    have h3 := le_tabSizeBound c₀ N
    omega

/-! ## The cost -/

/-- A fixed power of a `RAM.PolyFun`.  The exponent is a parameter of the statement, not of the
input, so this is a meta-level recursion, as it must be: `a ↦ x ^ a` is not a `RAM.PolyFun`. -/
theorem polyFun_powConst {α : Type*} [Enc α] {f : α → ℕ} (hf : PolyFun f) (c : ℕ) :
    PolyFun (fun a => f a ^ c) := by
  induction c with
  | zero => exact (polyFun_const 1).of_eq (fun a => (pow_zero _).symm)
  | succ c ih => exact (ih.mul hf).of_eq (fun a => (pow_succ _ _).symm)

theorem polyFun_guardBound (c₀ : ℕ) :
    PolyFun (fun a : List ℕ × List ℕ => guardBound c₀ a.2.length) := by
  have hn : PolyFun (fun a : List ℕ × List ℕ => Nat.log 2 a.2.length) :=
    (polyFun_snd.comp polyFun_length).comp polyFun_log2
  exact polyFun_powConst (hn.add (polyFun_const 1)) c₀

theorem polyFun_tabSetUp (c₀ : ℕ) : PolyFun (tabSetUp c₀) := by
  have hk : PolyFun (fun a : List ℕ × List ℕ => a.1.length) := polyFun_fst.comp polyFun_length
  have hguard : PolyFun (fun a : List ℕ × List ℕ =>
      decide (a.1.length ≤ guardBound c₀ a.2.length)) := hk.le (polyFun_guardBound c₀)
  have hyes : PolyFun (fun a : List ℕ × List ℕ =>
      ((a.1.length, (a.2, [[]])) : ℕ × (List ℕ × List (List ℕ)))) :=
    hk.pair (polyFun_snd.pair (polyFun_const [[]]))
  have hno : PolyFun (fun a : List ℕ × List ℕ =>
      ((0, (a.2, [])) : ℕ × (List ℕ × List (List ℕ)))) :=
    (polyFun_const 0).pair (polyFun_snd.pair (polyFun_const []))
  refine (PolyFun.ite hguard hyes hno).of_eq (fun a => ?_)
  by_cases h : a.1.length ≤ guardBound c₀ a.2.length <;> simp [tabSetUp, h]

theorem polyFun_tabStep : PolyFun tabStep :=
  (polyFun_fst.pair polyFun_extendStep).of_eq (fun _ => rfl)

theorem polyFun_tabRead : PolyFun tabRead := by
  have hrow : PolyFun (fun t : List ℕ => ((t, 0) : List ℕ × ℕ)) :=
    polyFun_id.pair (polyFun_const 0)
  exact (polyFun_fst.pair (polyFun_snd.comp (PolyFun.map hrow))).of_eq (fun _ => rfl)

/-- **For every fixed `c₀`, the guarded table builder is a `RAM.QuasiFun`.**  This is the
statement the ruling on work package A8 asked for (point 6 of the note of session 2 in
`Workspace/Algo/DESIGN.md`): with `k` in the input and guarded by `k ≤ (log₂ n + 1)^{c₀}`,
building the table of `k`-tuples runs in quasipolynomial time.  The answer is quasipolynomially
large, which is why the class is `RAM.QuasiFun` and not `RAM.QuasiPolyFun`. -/
theorem quasiFun_guardedTable (c₀ : ℕ) : QuasiFun (guardedTable c₀) := by
  have hstep : QuasiFun (fun x : ℕ × (List ℕ × List (List ℕ)) => (x.1 - 1, tabStep x.2)) :=
    ((polyFun_fst.sub (polyFun_const 1)).pair (polyFun_snd.comp polyFun_tabStep)).quasiFun
  refine (QuasiFun.iterateSetup (q := fun n => n) (p := tabSizeBound c₀)
    (polyFun_tabSetUp c₀).quasiFun hstep polyFun_tabRead.quasiFun ?_ polyBound_id.quasiPoly
    (size_state_le c₀) (quasiPolyBound_tabSizeBound c₀)).of_eq (fun a => rfl)
  intro a
  by_cases hg : a.1.length ≤ guardBound c₀ a.2.length
  · have hset : tabSetUp c₀ a = (a.1.length, (a.2, [[]])) := if_pos hg
    rw [hset]
    exact le_trans (length_le_size a.1) (size_fst_le' a)
  · have hset : tabSetUp c₀ a = (0, (a.2, [])) := if_neg hg
    rw [hset]
    exact Nat.zero_le _

/-- §5.4.1 with the arity in the input: build the guarded table of `k`-tuples, then run `k`-ary
WL refinement to stability. -/
def guardedPipeline (c₀ : ℕ) (a : List ℕ × List ℕ) : RawWL := rawWLStable (guardedTable c₀ a)

/-- **For every fixed `c₀`, the guarded pipeline is a `RAM.QuasiFun`.** -/
theorem quasiFun_guardedPipeline (c₀ : ℕ) : QuasiFun (guardedPipeline c₀) :=
  ((quasiFun_guardedTable c₀).comp_poly polyFun_rawWLStable).of_eq (fun _ => rfl)

/-- Under the guard the pipeline is the pipeline of `Workspace/Algo/TupleTable.lean` at the
arity read off the input. -/
theorem guardedPipeline_of_guard {c₀ : ℕ} {a : List ℕ × List ℕ}
    (hg : a.1.length ≤ guardBound c₀ a.2.length) :
    guardedPipeline c₀ a = wlPipeline a.1.length a.2 := by
  rw [guardedPipeline, guardedTable_of_guard hg]
  rfl

end Algo
