/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: building the table of `k`-tuples (§5.4.2).
-/
import Workspace.Algo.WLPoly

/-!
# §5.4.2 — building the table of `k`-tuples

`Workspace/Algo/WLRaw.lean` and `Workspace/Algo/WLPoly.lean` take the table of `k`-tuples as
the input, which is what makes the running-time statement uniform in `k`.  This file builds
that table from the domain.

The table has `n^k` rows, so its size is about `k·n^k`.  A routine whose *output* is that large
is not a `RAM.PolyFun` of its input — a `RAM.PolyFun` carries a polynomial bound on the size of
the answer.  What is true, and what is proved here, is the statement **for each fixed `k`**:
`k` is then a parameter of the theorem, not of the input, and `n^k` is a polynomial.  This is
the literal reading of the paper's "`n^{O(k)}`, `k` fixed" (rows R4–R7 of item 1.2 of
`Workspace/Algo/DESIGN.md`).

The guarded statement for `k ≤ (log₂ n + 1)^{c₀}` is **not** here; see the note on this session
at the end of `Workspace/Algo/DESIGN.md` for why it cannot be a `RAM.QuasiPolyFun` of the
present `Workspace/Machine/PolyFun.lean` as long as the table itself is the answer.

## Main definitions

* `Algo.extendStep`, `Algo.tuplesOf` — all `k`-tuples over a list of vertices;
* `Algo.tupleTable` — the table with every tuple colored `0`.

## Main results

* `Algo.mem_tuplesOf`, `Algo.nodup_tuplesOf`, `Algo.wf_tupleTable` — the table is well formed;
* `Algo.decWL_tupleTable` — it decodes to the constant coloring of `Ω^k`;
* `Algo.polyFun_tupleTable`, `Algo.polyFun_wlPipeline` — for each fixed `k`, building the table
  and then refining it are `RAM.PolyFun`s.

No axiom and no `sorry`.
-/

namespace Algo

open Babai RAM

/-! ## All `k`-tuples over a list -/

/-- One round of the construction: put every vertex in front of every tuple built so far. -/
def extendStep (z : List ℕ × List (List ℕ)) : List (List ℕ) :=
  (z.2.map (fun t => z.1.map (fun y => y :: t))).flatten

theorem mem_extendStep {dom : List ℕ} {L : List (List ℕ)} {t : List ℕ} :
    t ∈ extendStep (dom, L) ↔ ∃ s ∈ L, ∃ y ∈ dom, t = y :: s := by
  rw [extendStep, List.mem_flatten]
  constructor
  · rintro ⟨l, hl, htl⟩
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hl
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 htl
    exact ⟨s, hs, y, hy, rfl⟩
  · rintro ⟨s, hs, y, hy, rfl⟩
    exact ⟨dom.map (fun y => y :: s), List.mem_map_of_mem hs, List.mem_map_of_mem hy⟩

theorem nodup_extendStep {dom : List ℕ} (hdom : dom.Nodup) {L : List (List ℕ)} (hL : L.Nodup) :
    (extendStep (dom, L)).Nodup := by
  rw [extendStep, List.nodup_flatten]
  constructor
  · intro l hl
    obtain ⟨s, -, rfl⟩ := List.mem_map.1 hl
    exact hdom.map (fun a b h => by injection h)
  · rw [List.pairwise_map]
    refine hL.imp ?_
    intro t₁ t₂ hne x h₁ h₂
    obtain ⟨y₁, -, rfl⟩ := List.mem_map.1 h₁
    obtain ⟨y₂, -, he⟩ := List.mem_map.1 h₂
    exact hne (by injection he with _ h; exact h.symm)

/-- All `j`-tuples over a list of vertices. -/
def tuplesOf (dom : List ℕ) (j : ℕ) : List (List ℕ) :=
  (fun acc => extendStep (dom, acc))^[j] [[]]

@[simp] theorem tuplesOf_zero (dom : List ℕ) : tuplesOf dom 0 = [[]] := rfl

theorem tuplesOf_succ (dom : List ℕ) (j : ℕ) :
    tuplesOf dom (j + 1) = extendStep (dom, tuplesOf dom j) := by
  rw [tuplesOf, tuplesOf, Function.iterate_succ_apply']

/-- **What the construction produces**: exactly the `j`-tuples over the list. -/
theorem mem_tuplesOf (dom : List ℕ) :
    ∀ (j : ℕ) (t : List ℕ), t ∈ tuplesOf dom j ↔ (t.length = j ∧ ∀ a ∈ t, a ∈ dom) := by
  intro j
  induction j with
  | zero =>
      intro t
      simp only [tuplesOf_zero, List.mem_singleton]
      constructor
      · rintro rfl; simp
      · rintro ⟨h1, -⟩; exact List.eq_nil_of_length_eq_zero h1
  | succ j ih =>
      intro t
      rw [tuplesOf_succ, mem_extendStep]
      constructor
      · rintro ⟨s, hs, y, hy, rfl⟩
        obtain ⟨h1, h2⟩ := (ih s).1 hs
        refine ⟨by simp [h1], fun a ha => ?_⟩
        rcases List.mem_cons.1 ha with rfl | ha'
        · exact hy
        · exact h2 a ha'
      · rintro ⟨h1, h2⟩
        match t with
        | [] => simp at h1
        | y :: s =>
            refine ⟨s, (ih s).2 ⟨by simpa using h1,
              fun a ha => h2 a (List.mem_cons_of_mem _ ha)⟩, y,
              h2 y (List.mem_cons_self ..), rfl⟩

theorem nodup_tuplesOf {dom : List ℕ} (hdom : dom.Nodup) : ∀ j : ℕ, (tuplesOf dom j).Nodup
  | 0 => by simp
  | j + 1 => by
      rw [tuplesOf_succ]
      exact nodup_extendStep hdom (nodup_tuplesOf hdom j)

/-! ## The table -/

/-- The table of all `k`-tuples over a list of vertices, every tuple colored `0`. -/
def tupleTable (dom : List ℕ) (k : ℕ) : RawWL := (dom, (tuplesOf dom k).map (fun t => (t, 0)))

@[simp] theorem tupleTable_fst (dom : List ℕ) (k : ℕ) : (tupleTable dom k).1 = dom := rfl

@[simp] theorem keys_tupleTable (dom : List ℕ) (k : ℕ) :
    (tupleTable dom k).2.map Prod.fst = tuplesOf dom k := by
  simp [tupleTable, List.map_map, Function.comp_def]

/-- **The built table is well formed.** -/
theorem wf_tupleTable {n k : ℕ} {dom : List ℕ} (hnd : dom.Nodup) (hmem : ∀ a, a ∈ dom ↔ a < n) :
    RawWL.WF n k (tupleTable dom k) where
  domNodup := hnd
  domMem := hmem
  keyNodup := by rw [keys_tupleTable]; exact nodup_tuplesOf hnd k
  keyMem := by
    intro t
    rw [keys_tupleTable, mem_tuplesOf]
    exact and_congr Iff.rfl ⟨fun h a ha => (hmem a).1 (h a ha),
      fun h a ha => (hmem a).2 (h a ha)⟩
  colLt := by
    intro q hq
    have hpos : 0 < (tupleTable dom k).2.length := List.length_pos_of_mem hq
    obtain ⟨t, -, rfl⟩ := List.mem_map.1 hq
    exact hpos

/-- Looking up in a table all of whose colors are the same. -/
theorem lookup_map_const {β : Type*} (c : β) : ∀ (L : List (List ℕ)) (t : List ℕ),
    (L.map (fun s => (s, c))).lookup t = if t ∈ L then some c else none := by
  intro L
  induction L with
  | nil => intro t; simp
  | cons s L ih =>
      intro t
      by_cases h : t = s
      · subst h; simp [List.lookup]
      · have hb : (t == s) = false := beq_eq_false_iff_ne.2 h
        have hcond : (t = s ∨ t ∈ L) = (t ∈ L) := by simp [h]
        simp only [List.map_cons, List.mem_cons, hcond]
        simp [List.lookup, hb, ih t]

/-- The built table decodes to the constant coloring of `Ω^k`, which is the `k`-ary
configuration the refinement of §5.4.1 starts from when nothing is given. -/
theorem decWL_tupleTable {n k : ℕ} (dom : List ℕ) (x : Str (Fin n) k) :
    (decWL n k (tupleTable dom k)).color x = 0 := by
  rw [decWL_color, tblGet]
  show (((tuplesOf dom k).map (fun s => (s, 0))).lookup (tupleOf x)).getD 0 = 0
  rw [lookup_map_const]
  split <;> rfl

/-! ## The cost, for a fixed arity -/

theorem polyFun_extendStep : PolyFun extendStep := by
  have hcons : PolyFun (fun w : List ℕ × ℕ => w.2 :: w.1) :=
    (polyFun_snd.pair polyFun_fst).comp polyFun_cons
  have hf : PolyFun (fun w : List ℕ × List ℕ => w.1.map (fun y => y :: w.2)) :=
    (polyFun_swap.comp (PolyFun.mapParam hcons)).of_eq (fun w => rfl)
  exact (PolyFun.flatMapParam hf).of_eq (fun z => rfl)

/-- Building the tuples, with the vertex list carried along. -/
theorem polyFun_tuplesOf : ∀ k : ℕ,
    PolyFun (fun dom : List ℕ => ((dom, tuplesOf dom k) : List ℕ × List (List ℕ)))
  | 0 => (polyFun_id.pair (polyFun_const [[]])).of_eq (fun dom => rfl)
  | k + 1 =>
      ((polyFun_tuplesOf k).comp (polyFun_fst.pair polyFun_extendStep)).of_eq
        (fun dom => by rw [Prod.mk.injEq]; exact ⟨rfl, (tuplesOf_succ dom k).symm⟩)

/-- **For each fixed arity, building the table is a `RAM.PolyFun`.** -/
theorem polyFun_tupleTable (k : ℕ) : PolyFun (fun dom : List ℕ => tupleTable dom k) := by
  have hrow : PolyFun (fun t : List ℕ => ((t, 0) : List ℕ × ℕ)) :=
    polyFun_id.pair (polyFun_const 0)
  exact ((polyFun_tuplesOf k).comp
    (polyFun_fst.pair (polyFun_snd.comp (PolyFun.map hrow)))).of_eq (fun dom => rfl)

/-- §5.4.1 from the domain: build the table of `k`-tuples, then run `k`-ary WL refinement to
stability. -/
def wlPipeline (k : ℕ) (dom : List ℕ) : RawWL := rawWLStable (tupleTable dom k)

/-- **For each fixed arity, the whole pipeline is a `RAM.PolyFun`.**  This is the reading of
rows R4–R7 of `Workspace/Algo/DESIGN.md`, item 1.2, with `k` fixed. -/
theorem polyFun_wlPipeline (k : ℕ) : PolyFun (wlPipeline k) :=
  ((polyFun_tupleTable k).comp polyFun_rawWLStable).of_eq (fun dom => rfl)

/-- **The pipeline computes the stable `k`-ary refinement** of the constant coloring. -/
theorem wlPipeline_spec {n k : ℕ} {dom : List ℕ} (hnd : dom.Nodup)
    (hmem : ∀ a, a ∈ dom ↔ a < n) (x x' : Str (Fin n) k) :
    (decWL n k (wlPipeline k dom)).color x = (decWL n k (wlPipeline k dom)).color x'
      ↔ (decWL n k (tupleTable dom k)).wlStable.color x
        = (decWL n k (tupleTable dom k)).wlStable.color x' :=
  rawWLStable_spec (wf_tupleTable hnd hmem) x x'

end Algo
