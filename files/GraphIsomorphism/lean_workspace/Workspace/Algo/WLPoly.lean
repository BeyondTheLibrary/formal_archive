/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: `k`-ary WL refinement runs in time polynomial in the size of the table
of `k`-tuples (§5.4.2).
-/
import Workspace.Algo.WLRaw
import Workspace.Algo.RefinePoly

/-!
# §5.4.2 — the cost of `k`-ary WL refinement

§5.4.2 (lines 3399–3400): *"The stable refinement (`k`-ary coherent configuration) can
trivially be computed in time `O(k²n^{2k+1})` and nontrivially in time `O(k²n^{k+1} log n)`
[ImL, Sec. 4.9]."*  Row R7 of `Workspace/Algo/DESIGN.md`, item 1.2, asks for this as a
statement about the RAM of `Workspace/Machine/`.

## What "time `n^{O(k)}`" is, as a statement

`RAM.PolyFun` is a statement about one function between two fixed encodable types, in the size
of its input.  With `k` part of the input there is no time function of the input size alone
that expresses `n^{O(k)}` (see the note on A8 session 1 in `Workspace/Algo/DESIGN.md`).  The
repair, and the ruling recorded in the note on this session, is to state the bound **in the
size of the table of `k`-tuples**.  The table has `n^k` rows of length `k`, so its size is
about `k·n^k`, and `O(k²n^{2k+1})` is polynomial in it.  The statements below are therefore
uniform in `k`: `k` is read off the input, as the common length of the tuples.

Two remarks on how the bound is proved, both inherited from session 1.

* **The round count arrives as a list.**  `Algo.wlFuel` is a list of length `|table|²`, built
  from the table by a `map` and a `flatten`.
* **The accumulator bound is proved from an arbitrary start.**  `RAM.PolyFun.foldl` quantifies
  over every start state, so the bound may not use well-formedness.  It does not have to: a
  round keeps the tuples and makes every color a rank, hence a natural below the number of rows
  (`Algo.wlNewCol_lt`), whatever the input was.

## Main results

* `Algo.polyFun_tblGet`, `Algo.polyFun_substAt`, `Algo.polyFun_innerVec` — reading the table;
* `Algo.polyFun_wlTagAt` — the tag of a tuple;
* `Algo.polyFun_rawWLStep` — one round;
* `Algo.polyFun_rawWLStable` — the whole process.

No axiom and no `sorry`.
-/

namespace Algo

open RAM

/-! ## Reading the table -/

theorem polyFun_tblGet : PolyFun tblGet :=
  (((polyFun_listLookup (α := List ℕ) (β := ℕ) polyFun_listNatEq)).pair
    (polyFun_const 0)).comp polyFun_optionGetD

/-! ## Substitution -/

theorem polyFun_substAt : PolyFun substAt := by
  have hcond : PolyFun (fun z : (ℕ × ℕ) × (ℕ × ℕ) => decide (z.2.2 = z.1.1)) :=
    ((polyFun_snd.comp polyFun_snd).pair (polyFun_fst.comp polyFun_fst)).comp polyFun_natEq
  have hf : PolyFun (fun z : (ℕ × ℕ) × (ℕ × ℕ) => if z.2.2 = z.1.1 then z.1.2 else z.2.1) := by
    refine (PolyFun.ite hcond (polyFun_fst.comp polyFun_snd)
      (polyFun_snd.comp polyFun_fst)).of_eq (fun z => ?_)
    by_cases h : z.2.2 = z.1.1 <;> simp [h]
  have hin : PolyFun (fun p : (ℕ × ℕ) × List ℕ => (p.1, p.2.zipIdx)) :=
    polyFun_fst.pair (polyFun_snd.comp polyFun_zipIdx)
  exact (hin.comp (PolyFun.mapParam hf)).of_eq (fun p => rfl)

/-! ## The tuple of old colors -/

theorem polyFun_innerVec :
    PolyFun (fun z : (List (List ℕ × ℕ) × List ℕ) × ℕ => innerVec z.1.1 z.1.2 z.2) := by
  have htbl : PolyFun (fun w : ((List (List ℕ × ℕ) × List ℕ) × ℕ) × ℕ => w.1.1.1) :=
    (polyFun_fst.comp polyFun_fst).comp polyFun_fst
  have ht : PolyFun (fun w : ((List (List ℕ × ℕ) × List ℕ) × ℕ) × ℕ => w.1.1.2) :=
    (polyFun_fst.comp polyFun_fst).comp polyFun_snd
  have hy : PolyFun (fun w : ((List (List ℕ × ℕ) × List ℕ) × ℕ) × ℕ => w.1.2) :=
    polyFun_fst.comp polyFun_snd
  have hi : PolyFun (fun w : ((List (List ℕ × ℕ) × List ℕ) × ℕ) × ℕ => w.2) := polyFun_snd
  have hf : PolyFun (fun w : ((List (List ℕ × ℕ) × List ℕ) × ℕ) × ℕ =>
      tblGet (w.1.1.1, substAt ((w.2, w.1.2), w.1.1.2))) :=
    (htbl.pair (((hi.pair hy).pair ht).comp polyFun_substAt)).comp polyFun_tblGet
  have hin : PolyFun (fun z : (List (List ℕ × ℕ) × List ℕ) × ℕ =>
      (z, List.range z.1.2.length)) :=
    polyFun_id.pair ((polyFun_fst.comp polyFun_snd).comp polyFun_rangeLength)
  exact (hin.comp (PolyFun.mapParam hf)).of_eq (fun z => rfl)

/-! ## The tuples of old colors that occur -/

theorem polyFun_allVecs : PolyFun allVecs := by
  -- the inner map, over the vertices
  have hinner : PolyFun (fun u : (List (List ℕ × ℕ) × List ℕ) × List ℕ =>
      u.2.map (fun y => innerVec u.1.1 u.1.2 y)) := PolyFun.mapParam polyFun_innerVec
  have hf : PolyFun (fun w : RawWL × (List ℕ × ℕ) =>
      w.1.1.map (fun y => innerVec w.1.2 w.2.1 y)) := by
    have hin : PolyFun (fun w : RawWL × (List ℕ × ℕ) => ((w.1.2, w.2.1), w.1.1)) :=
      (((polyFun_fst.comp polyFun_snd).pair (polyFun_snd.comp polyFun_fst))).pair
        (polyFun_fst.comp polyFun_fst)
    exact (hin.comp hinner).of_eq (fun w => rfl)
  have hin : PolyFun (fun p : RawWL => (p, p.2)) := polyFun_id.pair polyFun_snd
  exact ((hin.comp (PolyFun.mapParam hf)).comp polyFun_flatten).of_eq (fun p => rfl)

theorem polyFun_vecSet : PolyFun vecSet :=
  ((polyFun_nil.pair polyFun_allVecs).comp
    (polyFun_dedupG (α := List ℕ) polyFun_listNatEq)).of_eq (fun p => rfl)

/-! ## The tag of a tuple -/

theorem polyFun_wlCount :
    PolyFun (fun z : (RawWL × List ℕ) × ℕ => wlCount z.1.1 z.1.2 z.2) := by
  have hp : PolyFun (fun w : ((RawWL × List ℕ) × ℕ) × ℕ => w.1.1.1) :=
    (polyFun_fst.comp polyFun_fst).comp polyFun_fst
  have ht : PolyFun (fun w : ((RawWL × List ℕ) × ℕ) × ℕ => w.1.1.2) :=
    (polyFun_fst.comp polyFun_fst).comp polyFun_snd
  have hj : PolyFun (fun w : ((RawWL × List ℕ) × ℕ) × ℕ => w.1.2) :=
    polyFun_fst.comp polyFun_snd
  have hy : PolyFun (fun w : ((RawWL × List ℕ) × ℕ) × ℕ => w.2) := polyFun_snd
  have hvec : PolyFun (fun w : ((RawWL × List ℕ) × ℕ) × ℕ =>
      innerVec w.1.1.1.2 w.1.1.2 w.2) :=
    (((hp.comp polyFun_snd).pair ht).pair hy).comp polyFun_innerVec
  have hrank : PolyFun (fun w : ((RawWL × List ℕ) × ℕ) × ℕ =>
      rankIn (vecSet w.1.1.1, innerVec w.1.1.1.2 w.1.1.2 w.2)) :=
    ((hp.comp polyFun_vecSet).pair hvec).comp polyFun_rankIn
  have hq : PolyFun (fun w : ((RawWL × List ℕ) × ℕ) × ℕ =>
      decide (rankIn (vecSet w.1.1.1, innerVec w.1.1.1.2 w.1.1.2 w.2) = w.1.2)) :=
    (hrank.pair hj).comp polyFun_natEq
  have hin : PolyFun (fun z : (RawWL × List ℕ) × ℕ => (z, z.1.1.1)) :=
    polyFun_id.pair ((polyFun_fst.comp polyFun_fst).comp polyFun_fst)
  exact ((hin.comp (PolyFun.filterParam hq)).comp polyFun_length).of_eq (fun z => rfl)

theorem polyFun_wlTagAt : PolyFun (fun z : RawWL × List ℕ => wlTagAt z.1 z.2) := by
  have hhead : PolyFun (fun z : RawWL × List ℕ => tblGet (z.1.2, z.2)) :=
    ((polyFun_fst.comp polyFun_snd).pair polyFun_snd).comp polyFun_tblGet
  have hin : PolyFun (fun z : RawWL × List ℕ => (z, List.range (vecSet z.1).length)) :=
    polyFun_id.pair ((polyFun_fst.comp polyFun_vecSet).comp polyFun_rangeLength)
  have htail : PolyFun (fun z : RawWL × List ℕ =>
      (List.range (vecSet z.1).length).map (fun j => wlCount z.1 z.2 j)) :=
    (hin.comp (PolyFun.mapParam polyFun_wlCount)).of_eq (fun z => rfl)
  exact ((hhead.pair htail).comp polyFun_cons).of_eq (fun z => rfl)

theorem polyFun_wlTags : PolyFun wlTags := by
  have hf : PolyFun (fun w : RawWL × (List ℕ × ℕ) => wlTagAt w.1 w.2.1) :=
    (polyFun_fst.pair (polyFun_snd.comp polyFun_fst)).comp polyFun_wlTagAt
  have hin : PolyFun (fun p : RawWL => (p, p.2)) := polyFun_id.pair polyFun_snd
  exact (hin.comp (PolyFun.mapParam hf)).of_eq (fun p => rfl)

theorem polyFun_wlTagSet : PolyFun wlTagSet :=
  ((polyFun_nil.pair polyFun_wlTags).comp
    (polyFun_dedupG (α := List ℕ) polyFun_listNatEq)).of_eq (fun p => rfl)

theorem polyFun_wlNewCol : PolyFun (fun z : RawWL × List ℕ => wlNewCol z.1 z.2) :=
  (((polyFun_fst.comp polyFun_wlTagSet).pair polyFun_wlTagAt).comp polyFun_rankIn).of_eq
    (fun z => rfl)

/-! ## One round -/

/-- **One round of `k`-ary WL refinement is a `RAM.PolyFun` of the table.** -/
theorem polyFun_rawWLStep : PolyFun rawWLStep := by
  have hf : PolyFun (fun w : RawWL × (List ℕ × ℕ) =>
      ((w.2.1, wlNewCol w.1 w.2.1) : List ℕ × ℕ)) :=
    (polyFun_snd.comp polyFun_fst).pair
      ((polyFun_fst.pair (polyFun_snd.comp polyFun_fst)).comp polyFun_wlNewCol)
  have hin : PolyFun (fun p : RawWL => (p, p.2)) := polyFun_id.pair polyFun_snd
  exact (polyFun_fst.pair (hin.comp (PolyFun.mapParam hf))).of_eq (fun p => rfl)

/-! ## The process -/

theorem polyFun_wlFuel : PolyFun wlFuel := by
  have hf : PolyFun (fun z : List (List ℕ × ℕ) × (List ℕ × ℕ) => z.1) := polyFun_fst
  have hin : PolyFun (fun tbl : List (List ℕ × ℕ) => (tbl, tbl)) := polyFun_id.pair polyFun_id
  exact ((hin.comp (PolyFun.mapParam hf)).comp polyFun_flatten).of_eq (fun tbl => rfl)

/-! ### The size of the state along the process

A round keeps the vertex list and the tuples, and makes every color a rank below the number of
rows.  So from **any** start state the state after one or more rounds is bounded by a fixed
polynomial in the size of the start state. -/

theorem rawWLIter_fst (p : RawWL) : ∀ j : ℕ, (rawWLStep^[j] p).1 = p.1
  | 0 => rfl
  | j + 1 => by rw [Function.iterate_succ_apply', rawWLStep_fst, rawWLIter_fst p j]

theorem rawWLIter_keys (p : RawWL) :
    ∀ j : ℕ, (rawWLStep^[j] p).2.map Prod.fst = p.2.map Prod.fst
  | 0 => rfl
  | j + 1 => by rw [Function.iterate_succ_apply', rawWLStep_keys, rawWLIter_keys p j]

theorem rawWLIter_length (p : RawWL) : ∀ j : ℕ, (rawWLStep^[j] p).2.length = p.2.length
  | 0 => rfl
  | j + 1 => by rw [Function.iterate_succ_apply', rawWLStep_length, rawWLIter_length p j]

theorem rawWLIter_colLt (p : RawWL) (j : ℕ) {q : List ℕ × ℕ}
    (hq : q ∈ (rawWLStep^[j + 1] p).2) : q.2 < p.2.length := by
  rw [Function.iterate_succ_apply'] at hq
  obtain ⟨q', hq', rfl⟩ := List.mem_map.1 hq
  have := wlNewCol_lt hq'
  rw [rawWLIter_length p j] at this
  exact this

theorem size_key_le {p : RawWL} {j : ℕ} {q : List ℕ × ℕ} (hq : q ∈ (rawWLStep^[j] p).2) :
    Enc.size q.1 ≤ Enc.size p.2 := by
  have hmem : q.1 ∈ p.2.map Prod.fst := by
    rw [← rawWLIter_keys p j]
    exact List.mem_map_of_mem hq
  obtain ⟨q', hq', hq'2⟩ := List.mem_map.1 hmem
  have h1 : Enc.size q' ≤ Enc.size p.2 := size_mem_le hq'
  have h2 : Enc.size q'.1 ≤ Enc.size q' := size_fst_le' q'
  rw [← hq'2]
  omega

theorem size_rawWLIter_le (p : RawWL) (N : ℕ) (hN : Enc.size p ≤ N) :
    ∀ j : ℕ, Enc.size (rawWLStep^[j] p)
      ≤ N + (2 * N + 2 * (1 + N * (2 * (4 * N + 4) + 1))) := by
  intro j
  have hsnd : Enc.size p.2 ≤ N := by
    have := size_snd_le' p
    omega
  have hfst : Enc.size p.1 ≤ N := by
    have := size_fst_le' p
    omega
  have hlenN : p.2.length ≤ N := by
    have h1 : p.2.length ≤ Enc.size p.2 := length_le_size _
    omega
  match j with
  | 0 => simpa using (by omega : Enc.size p ≤ N + (2 * N + 2 * (1 + N * (2 * (4 * N + 4) + 1))))
  | j + 1 =>
      set Y := rawWLStep^[j + 1] p with hY
      have hY1 : Y.1 = p.1 := rawWLIter_fst p (j + 1)
      have hlen : Y.2.length = p.2.length := rawWLIter_length p (j + 1)
      have hentry : ∀ q ∈ Y.2, Enc.size q ≤ 4 * N + 4 := by
        intro q hq
        have h1 : Enc.size q.1 ≤ N := by
          have := size_key_le (p := p) (j := j + 1) hq
          omega
        have h2 : q.2 < p.2.length := rawWLIter_colLt p j hq
        have h3 : Enc.size q.2 = Nat.size q.2 + 2 := Small.size_nat q.2
        have h4 : Nat.size q.2 ≤ q.2 := size_le_self q.2
        have h5 : Enc.size q ≤ 2 * Enc.size q.1 + 2 * Enc.size q.2 := size_pair_le' q
        omega
      have htbl : Enc.size Y.2 ≤ 1 + N * (2 * (4 * N + 4) + 1) := by
        have h := size_list_le_of_entries Y.2 (4 * N + 4) hentry
        have h2 : Y.2.length * (2 * (4 * N + 4) + 1) ≤ N * (2 * (4 * N + 4) + 1) :=
          Nat.mul_le_mul_right _ (by omega)
        omega
      have hdom : Enc.size Y.1 ≤ N := by rw [hY1]; omega
      have hpair : Enc.size Y ≤ 2 * Enc.size Y.1 + 2 * Enc.size Y.2 := size_pair_le' Y
      omega

/-- **The stable `k`-ary refinement is a `RAM.PolyFun` of the table.**  This is row R7 of
`Workspace/Algo/DESIGN.md`, item 1.2: the time is polynomial in the size of the table of
`k`-tuples, uniformly in `k`. -/
theorem polyFun_rawWLStable : PolyFun rawWLStable := by
  have hstep : PolyFun (fun z : RawWL × (List ℕ × ℕ) => rawWLStep z.1) :=
    polyFun_fst.comp polyFun_rawWLStep
  have hacc : ∀ (x : RawWL) (r : List (List ℕ × ℕ)) (j : ℕ),
      Enc.size (List.foldl (fun y a => (fun z : RawWL × (List ℕ × ℕ) => rawWLStep z.1) (y, a))
          x (r.take j))
        ≤ (fun m => m + (2 * m + 2 * (1 + m * (2 * (4 * m + 4) + 1))))
            (Enc.size ((x, r) : RawWL × List (List ℕ × ℕ))) := by
    intro x r j
    have hx : Enc.size x ≤ Enc.size ((x, r) : RawWL × List (List ℕ × ℕ)) :=
      Combine.size_fst_le x r
    have hfold : List.foldl (fun y a => (fun z : RawWL × (List ℕ × ℕ) => rawWLStep z.1) (y, a))
        x (r.take j) = rawWLStep^[(r.take j).length] x := foldl_const_eq_iterate_gen _ _
    rw [hfold]
    exact size_rawWLIter_le x _ hx _
  have hfold := PolyFun.foldl hstep
    (p := fun m => m + (2 * m + 2 * (1 + m * (2 * (4 * m + 4) + 1))))
    (polyBound_id.add (((polyBound_const 2).mul polyBound_id).add
      ((polyBound_const 2).mul ((polyBound_const 1).add
        (polyBound_id.mul (((polyBound_const 2).mul
          (((polyBound_const 4).mul polyBound_id).add (polyBound_const 4))).add
            (polyBound_const 1)))))))
    hacc
  have hin : PolyFun (fun p : RawWL => (p, wlFuel p.2)) :=
    polyFun_id.pair (polyFun_snd.comp polyFun_wlFuel)
  exact (hin.comp hfold).of_eq (fun p => rfl)

/-! ## The finer bounds of §5.4.2, as statements -/

/-- §5.4.2 (lines 3399–3400), first half: "The stable refinement (`k`-ary coherent
configuration) can trivially be computed in time `O(k²n^{2k+1})`."  On the RAM: one program
computes `rawWLStable` on every well-formed table of `k`-tuples over `[0, n)`, `k ≥ 1`, within
`C·(k²n^{2k+1} + 1)` steps.

Proved as `Algo.section_5_4_2_trivial` (`Workspace/Algo/WLFastCost.lean`), by a step-exact
program (`Algo.WLFast.wlFastP`) with tuple addressing in an array of size `n^k`.  The algorithm
itself uses the coarser form `n^{O(k)}` (`F3`, §5.2), proved here as `polyFun_rawWLStable`. -/
def Section_5_4_2_trivial_statement : Prop :=
  ∃ (P : Program) (C : ℕ), ∀ (n k : ℕ) (p : RawWL), 1 ≤ k → RawWL.WF n k p →
    ∃ s ≤ C * (k ^ 2 * n ^ (2 * k + 1) + 1),
      Halted P (run P (Config.init (encode p)) s) ∧
        OutputAt (run P (Config.init (encode p)) s).mem (encode (rawWLStable p))

/-- §5.4.2, second half, cited from [ImL, Sec. 4.9] (Immerman–Lander, *Describing graphs: a
first-order approach to graph canonization*, 1990): the stable refinement can "nontrivially
[be computed] in time `O(k²n^{k+1} log n)`."  The paper never uses this bound in a proof or an
algorithm, so it is recorded as a statement only (no axiom, no proof). -/
def Section_5_4_2_ImL_statement : Prop :=
  ∃ (P : Program) (C : ℕ), ∀ (n k : ℕ) (p : RawWL), 1 ≤ k → RawWL.WF n k p →
    ∃ s ≤ C * (k ^ 2 * n ^ (k + 1) * (Nat.log 2 n + 1) + 1),
      Halted P (run P (Config.init (encode p)) s) ∧
        OutputAt (run P (Config.init (encode p)) s).mem (encode (rawWLStable p))

end Algo
