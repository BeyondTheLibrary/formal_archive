/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: reading the coloring of the vertices off the `k`-ary WL refinement.
-/
import Workspace.Algo.WLGuarded

/-!
# §5.4.1 — the vertex coloring computed by `k`-ary WL refinement

`Workspace/Algo/WLGuarded.lean` runs the whole of §5.4.1 with the arity `k` in the input, and
its answer is the refined table of `k`-tuples, which has `n^k` rows: a `RAM.QuasiFun`, not a
`RAM.QuasiPolyFun`.  Every caller of `k`-ary WL refinement in Secs. 8 and 9 reads only a small
part of that table, and the machine layer's rule is to **return to the small class as soon as
the answer is small** (`RAM.QuasiFun.quasiPolyFun`).

This file does that for the simplest read-off, the one the Design Lemma needs first: the color
of the vertex `x` is the color of the diagonal tuple `(x, …, x)`.  There are `n` of them, and
each color is a natural below `n^k`, hence of `O(k log n)` bits, so the answer is polynomially
small and the composite is a `RAM.QuasiPolyFun`.

## Main definitions

* `Algo.diagOf` — the diagonal tuple `(y, …, y)`, at the arity given by the input;
* `Algo.vertexColorAt`, `Algo.vertexColors` — the read-off;
* `Algo.guardedVertexColoring` — the guarded pipeline followed by the read-off.

## Main results

* `Algo.vertexColorAt_spec` — the color read off is the color `Babai.wlStable` gives to the
  diagonal tuple;
* `Algo.sizeBound_guardedVertexColoring` — the answer is polynomially small;
* `Algo.quasiPolyFun_guardedVertexColoring` — **the read-off is a `RAM.QuasiPolyFun`**, which
  is the form Secs. 8 and 9 need.

No axiom and no `sorry`.
-/

namespace Algo

open Babai RAM

/-! ## The read-off -/

/-- The diagonal tuple `(y, …, y)`, of the arity given by the first component. -/
def diagOf (z : List ℕ × ℕ) : List ℕ := z.1.map (fun _ => z.2)

theorem diagOf_eq_tupleOf {n k : ℕ} {ks : List ℕ} (hk : ks.length = k) (y : Fin n) :
    diagOf (ks, (y : ℕ)) = tupleOf (fun _ : Fin k => y) := by
  rw [diagOf, tupleOf]
  show ks.map (fun _ => (y : ℕ)) = List.ofFn (fun _ : Fin k => (y : ℕ))
  rw [List.map_const', hk, List.ofFn_const]

/-- The color a table gives to the vertex `y`: the color of the diagonal tuple. -/
def vertexColorAt (a : List ℕ × List ℕ) (p : RawWL) (y : ℕ) : ℕ := tblGet (p.2, diagOf (a.1, y))

/-- The colors of all the vertices, in the order the input lists them. -/
def vertexColors (a : List ℕ × List ℕ) (p : RawWL) : List ℕ :=
  a.2.map (fun y => vertexColorAt a p y)

/-- §5.4.1 from the domain, read off at the vertices: run the guarded pipeline and keep the
colors of the diagonal tuples. -/
def guardedVertexColoring (c₀ : ℕ) (a : List ℕ × List ℕ) : List ℕ :=
  vertexColors a (guardedPipeline c₀ a)

/-- **What the read-off computes**: the color that the stable `k`-ary refinement gives to the
diagonal tuple `(y, …, y)`. -/
theorem vertexColorAt_spec {n c₀ k : ℕ} {a : List ℕ × List ℕ} (hnd : a.2.Nodup)
    (hmem : ∀ b, b ∈ a.2 ↔ b < n) (hg : a.1.length ≤ guardBound c₀ a.2.length)
    (hk : a.1.length = k) (y y' : Fin n) :
    vertexColorAt a (guardedPipeline c₀ a) (y : ℕ)
        = vertexColorAt a (guardedPipeline c₀ a) (y' : ℕ)
      ↔ (decWL n k (tupleTable a.2 k)).wlStable.color (fun _ : Fin k => y)
        = (decWL n k (tupleTable a.2 k)).wlStable.color (fun _ : Fin k => y') := by
  have hpipe : guardedPipeline c₀ a = wlPipeline k a.2 := by
    rw [guardedPipeline_of_guard hg, hk]
  have hread : ∀ z : Fin n, vertexColorAt a (guardedPipeline c₀ a) (z : ℕ)
      = (decWL n k (wlPipeline k a.2)).color (fun _ : Fin k => z) := by
    intro z
    rw [vertexColorAt, hpipe, diagOf_eq_tupleOf hk z, decWL_color]
  rw [hread y, hread y']
  exact wlPipeline_spec hnd hmem _ _

/-! ## The size of the answer

The colors of the refined table are ranks below the number of its rows, and the number of rows
is `n^k` with `k` below the guard, so each color has `O((log n)^{c₀+1})` bits and there are
`n` of them. -/

/-- A table answers, at every key, a value bounded by the values it lists. -/
theorem tblGet_le {B : ℕ} : ∀ (tbl : List (List ℕ × ℕ)) (t : List ℕ),
    (∀ q ∈ tbl, q.2 ≤ B) → tblGet (tbl, t) ≤ B := by
  intro tbl
  induction tbl with
  | nil => intro t _; exact Nat.zero_le _
  | cons q l ih =>
      obtain ⟨u, c⟩ := q
      intro t h
      by_cases hq : t = u
      · have hval : tblGet (((u, c) :: l), t) = c := by
          show ((((u, c) :: l)).lookup t).getD 0 = c
          simp [List.lookup, hq]
        rw [hval]
        exact h (u, c) (List.mem_cons_self ..)
      · have hb : (t == u) = false := beq_eq_false_iff_ne.2 hq
        have hstep : tblGet (((u, c) :: l), t) = tblGet (l, t) := by
          show ((((u, c) :: l)).lookup t).getD 0 = (l.lookup t).getD 0
          simp [List.lookup, hb]
        rw [hstep]
        exact ih t (fun r hr => h r (List.mem_cons_of_mem _ hr))

/-- Along the process the colors stay below a bound that the start state gives. -/
theorem col_rawWLIter_le {p : RawWL} {B : ℕ} (hB : ∀ q ∈ p.2, q.2 ≤ B) (hlen : p.2.length ≤ B) :
    ∀ (j : ℕ), ∀ q ∈ (rawWLStep^[j] p).2, q.2 ≤ B
  | 0 => hB
  | j + 1 => fun _ hq => le_of_lt (lt_of_lt_of_le (rawWLIter_colLt p j hq) hlen)

theorem col_rawWLStable_le {p : RawWL} {B : ℕ} (hB : ∀ q ∈ p.2, q.2 ≤ B)
    (hlen : p.2.length ≤ B) : ∀ q ∈ (rawWLStable p).2, q.2 ≤ B := by
  rw [rawWLStable_eq_iterate]
  exact col_rawWLIter_le hB hlen _

theorem col_guardedTable_zero (c₀ : ℕ) (a : List ℕ × List ℕ) :
    ∀ q ∈ (guardedTable c₀ a).2, q.2 = 0 := by
  by_cases hg : a.1.length ≤ guardBound c₀ a.2.length
  · rw [guardedTable_of_guard hg]
    intro q hq
    obtain ⟨t, -, rfl⟩ := List.mem_map.1 hq
    rfl
  · rw [guardedTable_of_not_guard hg]
    intro q hq
    exact absurd hq (by simp)

/-- The counting of `Algo.size_state_le`, in the form needed here: under the guard the number
of `k`-tuples is below a quasipolynomial of the input size. -/
theorem pow_le_quasi {c₀ N m j : ℕ} (hm : m ≤ N) (hj : j ≤ (Nat.log 2 N + 1) ^ c₀) :
    m ^ j ≤ 2 ^ ((Nat.log 2 N + 2) ^ (c₀ + 1)) := by
  have hm2 : m ≤ 2 ^ (Nat.log 2 N + 1) := le_trans hm (le_two_pow_log N)
  calc m ^ j ≤ (2 ^ (Nat.log 2 N + 1)) ^ j := Nat.pow_le_pow_left hm2 j
    _ = 2 ^ ((Nat.log 2 N + 1) * j) := by rw [← pow_mul]
    _ ≤ 2 ^ ((Nat.log 2 N + 1) ^ (c₀ + 1)) := by
        refine Nat.pow_le_pow_right (by norm_num) ?_
        calc (Nat.log 2 N + 1) * j
            ≤ (Nat.log 2 N + 1) * (Nat.log 2 N + 1) ^ c₀ := Nat.mul_le_mul_left _ hj
          _ = (Nat.log 2 N + 1) ^ (c₀ + 1) := by rw [pow_succ]; ring
    _ ≤ 2 ^ ((Nat.log 2 N + 2) ^ (c₀ + 1)) :=
        Nat.pow_le_pow_right (by norm_num) (Nat.pow_le_pow_left (by omega) _)

/-- **The guarded table has quasipolynomially many rows.** -/
theorem length_guardedTable_le (c₀ : ℕ) (a : List ℕ × List ℕ) :
    (guardedTable c₀ a).2.length ≤ 2 ^ ((Nat.log 2 (Enc.size a) + 2) ^ (c₀ + 1)) := by
  set N := Enc.size a with hN
  by_cases hg : a.1.length ≤ guardBound c₀ a.2.length
  · rw [guardedTable_of_guard hg]
    have hlen : (tupleTable a.2 a.1.length).2.length = a.2.length ^ a.1.length := by
      rw [tupleTable]
      rw [List.length_map, length_tuplesOf]
    rw [hlen]
    have hnN : a.2.length ≤ N := by
      have h1 : a.2.length ≤ Enc.size a.2 := length_le_size a.2
      have h2 : Enc.size a.2 ≤ N := size_snd_le' a
      omega
    refine pow_le_quasi hnN ?_
    refine le_trans hg ?_
    rw [guardBound]
    exact Nat.pow_le_pow_left (by
      have := Nat.log_mono_right (b := 2) hnN
      omega) c₀
  · rw [guardedTable_of_not_guard hg]
    exact Nat.zero_le _

/-- **Every color the guarded pipeline computes is below the number of rows.** -/
theorem col_guardedPipeline_le (c₀ : ℕ) (a : List ℕ × List ℕ) :
    ∀ q ∈ (guardedPipeline c₀ a).2, q.2 ≤ 2 ^ ((Nat.log 2 (Enc.size a) + 2) ^ (c₀ + 1)) := by
  refine col_rawWLStable_le ?_ (length_guardedTable_le c₀ a)
  intro q hq
  rw [col_guardedTable_zero c₀ a q hq]
  exact Nat.zero_le _

/-- **The answer of the read-off is polynomially small.** -/
theorem sizeBound_guardedVertexColoring (c₀ : ℕ) : SizeBound (guardedVertexColoring c₀) := by
  have hbound : ∀ a : List ℕ × List ℕ, Enc.size (guardedVertexColoring c₀ a)
      ≤ 1 + Enc.size a * (2 * ((Nat.log 2 (Enc.size a) + 2) ^ (c₀ + 1) + 3) + 1) := by
    intro a
    set N := Enc.size a with hN
    set m := (Nat.log 2 N + 2) ^ (c₀ + 1) with hm
    have hentry : ∀ b ∈ guardedVertexColoring c₀ a, Enc.size b ≤ m + 3 := by
      intro b hb
      obtain ⟨y, -, rfl⟩ := List.mem_map.1 hb
      have hle : vertexColorAt a (guardedPipeline c₀ a) y ≤ 2 ^ m :=
        tblGet_le _ _ (col_guardedPipeline_le c₀ a)
      have hsize : Nat.size (vertexColorAt a (guardedPipeline c₀ a) y) ≤ m + 1 := by
        refine Nat.size_le.2 (lt_of_le_of_lt hle ?_)
        exact Nat.pow_lt_pow_right (by norm_num) (by omega)
      have hEnc : Enc.size (vertexColorAt a (guardedPipeline c₀ a) y)
          = Nat.size (vertexColorAt a (guardedPipeline c₀ a) y) + 2 :=
        Small.size_nat _
      omega
    have hlen : (guardedVertexColoring c₀ a).length ≤ N := by
      have h1 : (guardedVertexColoring c₀ a).length = a.2.length := by
        rw [guardedVertexColoring, vertexColors, List.length_map]
      have h2 : a.2.length ≤ Enc.size a.2 := length_le_size a.2
      have h3 : Enc.size a.2 ≤ N := size_snd_le' a
      omega
    have h := size_list_le_of_entries (guardedVertexColoring c₀ a) (m + 3) hentry
    have h2 : (guardedVertexColoring c₀ a).length * (2 * (m + 3) + 1)
        ≤ N * (2 * (m + 3) + 1) := Nat.mul_le_mul_right _ hlen
    omega
  have hpb : PolyBound (fun N : ℕ => 1 + N * (2 * ((Nat.log 2 N + 2) ^ (c₀ + 1) + 3) + 1)) :=
    (polyBound_const 1).add (polyBound_id.mul
      (((polyBound_const 2).mul ((polyBound_logPow (c₀ + 1)).add (polyBound_const 3))).add
        (polyBound_const 1)))
  obtain ⟨c, d, hc⟩ := hpb
  exact ⟨c, d, fun a => le_trans (hbound a) (hc _)⟩

/-! ## The cost -/

theorem polyFun_diagOf : PolyFun diagOf :=
  (polyFun_swap.comp (PolyFun.mapParam (polyFun_fst (α := ℕ) (β := ℕ)))).of_eq (fun z => rfl)

theorem polyFun_vertexColors :
    PolyFun (fun z : (List ℕ × List ℕ) × RawWL => vertexColors z.1 z.2) := by
  have hf : PolyFun (fun w : ((List ℕ × List ℕ) × RawWL) × ℕ =>
      tblGet (w.1.2.2, diagOf (w.1.1.1, w.2))) :=
    ((((polyFun_fst.comp polyFun_snd).comp polyFun_snd)).pair
      ((((polyFun_fst.comp polyFun_fst).comp polyFun_fst).pair polyFun_snd).comp
        polyFun_diagOf)).comp polyFun_tblGet
  have hin : PolyFun (fun z : (List ℕ × List ℕ) × RawWL => (z, z.1.2)) :=
    polyFun_id.pair ((polyFun_fst.comp polyFun_snd))
  exact (hin.comp (PolyFun.mapParam hf)).of_eq (fun z => rfl)

theorem quasiFun_guardedVertexColoring (c₀ : ℕ) : QuasiFun (guardedVertexColoring c₀) := by
  have hin : QuasiFun (fun a : List ℕ × List ℕ =>
      ((a, guardedPipeline c₀ a) : (List ℕ × List ℕ) × RawWL)) :=
    quasiFun_id.pair (quasiFun_guardedPipeline c₀)
  exact (hin.comp_poly polyFun_vertexColors).of_eq (fun a => rfl)

/-- **The read-off returns to the small class.**  §5.4.1 with the arity in the input, followed
by the read-off at the vertices, is a `RAM.QuasiPolyFun`: the time is quasipolynomial and the
answer is polynomially small.  This is the form in which Secs. 8 and 9 call `k`-ary WL
refinement. -/
theorem quasiPolyFun_guardedVertexColoring (c₀ : ℕ) :
    QuasiPolyFun (guardedVertexColoring c₀) :=
  (quasiFun_guardedVertexColoring c₀).quasiPolyFun (sizeBound_guardedVertexColoring c₀)

end Algo
