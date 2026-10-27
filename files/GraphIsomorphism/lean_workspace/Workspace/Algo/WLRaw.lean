/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: `k`-ary WL refinement (§5.4.1, §5.4.2) on raw data.
-/
import Workspace.Algo.RefineRaw
import Workspace.Higher.WL

/-!
# §5.4.1, §5.4.2 — `k`-ary WL refinement as a routine

This is the raw half of the second part of the work package **A8** of
`Workspace/Algo/DESIGN.md` (row R7 of item 1.2, and the refinement behind rows R4–R6).
`Workspace/Higher/WL.lean` has the mathematics: one round `Babai.KAryPartStruct.wlStep`, the
process `.wlIter`, the stable refinement `.wlStable`, and the functor `F3`.  All of it is
noncomputable: the colors after `j` rounds live in the type `wlColorType C k j`, and the
counts are `Set.ncard`s.  This file builds the computable copy and proves that it has the same
color classes.

## The data

§5.4.1 works with a `k`-ary configuration `X = (Ω; R₁,…,R_r)`, i.e. with a coloring of `Ω^k`.
The raw form of that datum is the **table of `k`-tuples**: the list of the vertices, and the
list of the pairs `(x⃗, c(x⃗))`.  The table has `n^k` rows, each of length `k`, so its size is
`k·n^k`; the paper's `n^{O(k)}` is polynomial in the size of that table, which is why the
running-time statements of `Workspace/Algo/WLPoly.lean` take the table as the input.

## One round

§5.4.1: *"we encode in the new color `c'(x⃗)` the following information: the old color `c(x⃗)`,
and for all `i₁,…,i_k ≤ r`, the number `|{y ∈ Ω | (∀j ≤ k)(c(x⃗ʲ(y)) = i_j)}|`."*  So the new
color of `x⃗` is the old color together with the multiset, over `y ∈ Ω`, of the `k`-tuples
`(c(x⃗ʲ(y)) | j ∈ [k])`.  The paper lists the counts by the tuple `(i₁,…,i_k)` of old colors,
which would be a list of `r^k` entries; only the tuples that actually occur can have a nonzero
count, so this file lists the counts by the tuples that occur.

The list of tuples that occur is produced by a deduplication, hence in an accidental order.
To make the tag independent of that order, the count of a tuple `v` is stored at position
`Algo.rankIn (vecSet p, v)` — the rank of `v` in the lexicographic order, which is what §4.1.1
already used to rename colors and which does not depend on the order of the deduplicated list
(`Algo.rankIn_congr_perm`).

As in §4.1.1 and in `Workspace/Algo/RefineRaw.lean`, the new name of a tag is its rank among
the tags that occur, so the colors stay naturals below the number of rows of the table.

## Main definitions

* `Algo.RawWL`, `Algo.RawWL.WF`, `Algo.decWL` — the table, its well-formedness, its decoding;
* `Algo.substAt`, `Algo.innerVec` — `x⃗ʲ(y)` and the tuple `(c(x⃗ʲ(y)) | j ∈ [k])`;
* `Algo.wlTagAt`, `Algo.wlNewCol`, `Algo.rawWLStep` — one round;
* `Algo.rawWLStable` — the process, run for `(n^k)²` rounds.

## Main results

* `Algo.wlTagAt_eq_iff` — two tuples get the same tag exactly when one round of
  `Babai.KAryPartStruct.wlStep` gives them the same color;
* `Algo.rawWLStep_spec` — one round of the routine is one round of the process;
* `Algo.rawWLIter_spec` — round by round;
* `Algo.rawWLStable_spec` — the routine and `Babai.KAryPartStruct.wlStable` have the same
  color classes;
* `Algo.wlNewCol_lt`, `Algo.rawWLStep_wf` — the colors stay below the number of rows.

The running time is `Workspace/Algo/WLPoly.lean`.  No axiom and no `sorry`.
-/

namespace Algo

open Babai

/-! ## Substitution in a raw tuple

Notation 5.2.1: `x⃗ʲ(z)` is `x⃗` with the `j`-th letter replaced by `z`.  On raw data that is
`List.set`, which is a recursion on a machine natural and therefore not a routine; the routine
form is a `map` over `List.zipIdx`, exactly as in point 5 of the note on A4 session 2. -/

/-- Notation 5.2.1 on raw tuples: replace the letter at position `i` by `y`. -/
def substAt (p : (ℕ × ℕ) × List ℕ) : List ℕ :=
  p.2.zipIdx.map (fun q => if q.2 = p.1.1 then p.1.2 else q.1)

@[simp] theorem length_substAt (i y : ℕ) (t : List ℕ) : (substAt ((i, y), t)).length = t.length := by
  simp [substAt]

theorem substAt_eq_set (i y : ℕ) (t : List ℕ) : substAt ((i, y), t) = t.set i y := by
  refine List.ext_getElem (by simp [substAt]) (fun j h1 h2 => ?_)
  simp only [substAt, List.getElem_map, List.getElem_zipIdx, Nat.zero_add, List.getElem_set]
  by_cases hij : i = j
  · simp [hij]
  · simp [hij, Ne.symm hij]

/-! ## The table of `k`-tuples -/

/-- A raw `k`-ary coloring: the list of the vertices, and the table of the pairs
`(k`-tuple, color`)`. -/
abbrev RawWL := List ℕ × List (List ℕ × ℕ)

/-- **Well-formedness of a raw `k`-ary coloring** for the domain size `n` and the arity `k`:
the vertex list lists every vertex once, every `k`-tuple over the vertices occurs once in the
table, and the colors are below the number of rows. -/
structure RawWL.WF (n k : ℕ) (p : RawWL) : Prop where
  /-- The vertex list has no repetition. -/
  domNodup : p.1.Nodup
  /-- The vertex list is the domain `[0, n)`. -/
  domMem : ∀ a, a ∈ p.1 ↔ a < n
  /-- No tuple is listed twice. -/
  keyNodup : (p.2.map Prod.fst).Nodup
  /-- The tuples listed are exactly the `k`-tuples over the domain. -/
  keyMem : ∀ t : List ℕ, t ∈ p.2.map Prod.fst ↔ (t.length = k ∧ ∀ a ∈ t, a < n)
  /-- Colors are naturals below the number of rows; the standard form of §4.1.1. -/
  colLt : ∀ q ∈ p.2, q.2 < p.2.length

/-- The raw form of a `k`-tuple of vertices. -/
def tupleOf {n k : ℕ} (x : Str (Fin n) k) : List ℕ := List.ofFn (fun i => (x i : ℕ))

@[simp] theorem length_tupleOf {n k : ℕ} (x : Str (Fin n) k) : (tupleOf x).length = k := by
  simp [tupleOf]

@[simp] theorem getElem_tupleOf {n k : ℕ} (x : Str (Fin n) k) {i : ℕ} (h : i < (tupleOf x).length) :
    (tupleOf x)[i] = (x ⟨i, by simpa using h⟩ : ℕ) := by
  simp only [tupleOf, List.getElem_ofFn]

theorem tupleOf_injective {n k : ℕ} : Function.Injective (tupleOf (n := n) (k := k)) := by
  intro x y h
  funext i
  have := congrArg (fun l => l[(i : ℕ)]?) h
  simp only [tupleOf, List.getElem?_ofFn] at this
  simp only [dif_pos i.isLt] at this
  have h2 : (x ⟨(i : ℕ), i.isLt⟩ : ℕ) = (y ⟨(i : ℕ), i.isLt⟩ : ℕ) := by
    simpa using this
  exact Fin.ext (by simpa using h2)

theorem tupleOf_lt {n k : ℕ} (x : Str (Fin n) k) {a : ℕ} (ha : a ∈ tupleOf x) : a < n := by
  rw [tupleOf, List.mem_ofFn] at ha
  obtain ⟨i, rfl⟩ := ha
  exact (x i).isLt

/-- Every `k`-tuple over `[0, n)` is the raw form of a `k`-tuple of vertices. -/
theorem exists_tupleOf {n k : ℕ} {t : List ℕ} (hl : t.length = k) (hlt : ∀ a ∈ t, a < n) :
    ∃ x : Str (Fin n) k, tupleOf x = t := by
  subst hl
  refine ⟨fun i => ⟨t[(i : ℕ)], hlt _ (List.getElem_mem i.isLt)⟩, ?_⟩
  simp [tupleOf]

/-- Substituting in a raw tuple is substituting in the tuple. -/
theorem tupleOf_subst {n k : ℕ} (x : Str (Fin n) k) (j : Fin k) (z : Fin n) :
    tupleOf (Str.subst x j z) = (tupleOf x).set (j : ℕ) (z : ℕ) := by
  refine List.ext_getElem (by simp) (fun i h1 h2 => ?_)
  rw [List.getElem_set, getElem_tupleOf]
  by_cases hij : (j : ℕ) = i
  · have : (⟨i, by simpa using h1⟩ : Fin k) = j := Fin.ext hij.symm
    simp [hij, this]
  · have : (⟨i, by simpa using h1⟩ : Fin k) ≠ j := fun hc => hij (congrArg Fin.val hc).symm
    rw [if_neg hij, getElem_tupleOf, Str.subst_of_ne _ this]

/-! ## Reading the table -/

/-- The color the table gives to a tuple, `0` if the tuple is not listed. -/
def tblGet (p : List (List ℕ × ℕ) × List ℕ) : ℕ := (p.1.lookup p.2).getD 0

/-- **The decoding**: the `k`-ary partition structure a raw table describes. -/
def decWL (n k : ℕ) (p : RawWL) : KAryPartStruct (Fin n) ℕ k :=
  ⟨fun x => tblGet (p.2, tupleOf x)⟩

@[simp] theorem decWL_color (n k : ℕ) (p : RawWL) (x : Str (Fin n) k) :
    (decWL n k p).color x = tblGet (p.2, tupleOf x) := rfl

/-- Looking up in a table whose values have been recomputed from the keys. -/
theorem lookup_map_key {β : Type*} (g : List ℕ → β) :
    ∀ (l : List (List ℕ × ℕ)) (t : List ℕ),
      (l.map (fun q => (q.1, g q.1))).lookup t
        = if t ∈ l.map Prod.fst then some (g t) else none := by
  intro l
  induction l with
  | nil => intro t; simp
  | cons q l ih =>
      intro t
      by_cases h : t = q.1
      · subst h
        simp [List.lookup]
      · have hb : (t == q.1) = false := beq_eq_false_iff_ne.2 h
        have hcond : (t = q.1 ∨ t ∈ l.map Prod.fst) = (t ∈ l.map Prod.fst) := by
          simp [h]
        simp only [List.map_cons, List.mem_cons, hcond]
        simp [List.lookup, hb, ih t]

/-! ## One round

§5.4.1.  For each `y ∈ Ω`, the `k`-tuple of old colors around `x⃗`. -/

/-- §5.4.1: the tuple `(c(x⃗ʲ(y)) | j ∈ [k])` of old colors. -/
def innerVec (tbl : List (List ℕ × ℕ)) (t : List ℕ) (y : ℕ) : List ℕ :=
  (List.range t.length).map (fun i => tblGet (tbl, substAt ((i, y), t)))

@[simp] theorem length_innerVec (tbl : List (List ℕ × ℕ)) (t : List ℕ) (y : ℕ) :
    (innerVec tbl t y).length = t.length := by simp [innerVec]

theorem getElem_innerVec {tbl : List (List ℕ × ℕ)} {t : List ℕ} {y i : ℕ}
    (h : i < (innerVec tbl t y).length) : (innerVec tbl t y)[i] = tblGet (tbl, t.set i y) := by
  simp only [innerVec, List.getElem_map, List.getElem_range, substAt_eq_set]

/-- The raw tuple of old colors is the tuple of old colors. -/
theorem innerVec_tupleOf {n k : ℕ} (p : RawWL) (x : Str (Fin n) k) (z : Fin n) :
    innerVec p.2 (tupleOf x) (z : ℕ)
      = List.ofFn (fun j : Fin k => (decWL n k p).color (Str.subst x j z)) := by
  refine List.ext_getElem (by simp) (fun i h1 h2 => ?_)
  have hik : i < k := by simpa using h1
  rw [getElem_innerVec, List.getElem_ofFn]
  rw [show ((⟨i, by simpa using h2⟩ : Fin k)) = (⟨i, hik⟩ : Fin k) from rfl]
  rw [decWL_color, tupleOf_subst]

/-- The colors around `x⃗` are the prescribed ones exactly when the raw tuple of old colors is
the raw form of the prescription. -/
theorem innerVec_eq_ofFn_iff {n k : ℕ} (p : RawWL) (x : Str (Fin n) k) (z : Fin n)
    (i : Str ℕ k) :
    innerVec p.2 (tupleOf x) (z : ℕ) = List.ofFn i
      ↔ ∀ j : Fin k, (decWL n k p).color (Str.subst x j z) = i j := by
  rw [innerVec_tupleOf]
  constructor
  · intro h j
    have := congrArg (fun l => l[(j : ℕ)]?) h
    simp only [List.getElem?_ofFn, dif_pos j.isLt] at this
    simpa using this
  · intro h
    exact congrArg List.ofFn (funext h)

/-! ### The tuples of old colors that occur -/

/-- All the tuples of old colors that occur, in the order the table lists them. -/
def allVecs (p : RawWL) : List (List ℕ) :=
  (p.2.map (fun q => p.1.map (fun y => innerVec p.2 q.1 y))).flatten

/-- The distinct tuples of old colors that occur. -/
def vecSet (p : RawWL) : List (List ℕ) := RAM.dedupG (([] : List (List ℕ)), allVecs p)

theorem mem_allVecs {p : RawWL} {q : List ℕ × ℕ} (hq : q ∈ p.2) {y : ℕ} (hy : y ∈ p.1) :
    innerVec p.2 q.1 y ∈ allVecs p := by
  rw [allVecs, List.mem_flatten]
  exact ⟨p.1.map (fun y => innerVec p.2 q.1 y), List.mem_map_of_mem hq, List.mem_map_of_mem hy⟩

theorem mem_vecSet {p : RawWL} {v : List ℕ} : v ∈ vecSet p ↔ v ∈ allVecs p :=
  RAM.mem_dedupG_nil _ _

theorem nodup_vecSet (p : RawWL) : (vecSet p).Nodup := RAM.nodup_dedupG _

theorem innerVec_mem_vecSet {p : RawWL} {q : List ℕ × ℕ} (hq : q ∈ p.2) {y : ℕ} (hy : y ∈ p.1) :
    innerVec p.2 q.1 y ∈ vecSet p :=
  mem_vecSet.2 (mem_allVecs hq hy)

theorem exists_of_mem_allVecs {p : RawWL} {v : List ℕ} (hv : v ∈ allVecs p) :
    ∃ q ∈ p.2, ∃ y ∈ p.1, innerVec p.2 q.1 y = v := by
  rw [allVecs, List.mem_flatten] at hv
  obtain ⟨l, hl, hvl⟩ := hv
  rw [List.mem_map] at hl
  obtain ⟨q, hq, rfl⟩ := hl
  rw [List.mem_map] at hvl
  obtain ⟨y, hy, rfl⟩ := hvl
  exact ⟨q, hq, y, hy, rfl⟩

/-- Every tuple of old colors that occurs has `k` entries. -/
theorem length_of_mem_vecSet {n k : ℕ} {p : RawWL} (h : RawWL.WF n k p) {v : List ℕ}
    (hv : v ∈ vecSet p) : v.length = k := by
  obtain ⟨q, hq, y, -, rfl⟩ := exists_of_mem_allVecs (mem_vecSet.1 hv)
  rw [length_innerVec]
  exact ((h.keyMem q.1).1 (List.mem_map_of_mem hq)).1

/-! ### The tag of a tuple -/

/-- How many vertices `y` give the tuple `v` of old colors around `t`: the paper's
`|{y ∈ Ω | (∀j ≤ k)(c(x⃗ʲ(y)) = i_j)}|`. -/
def countVec (p : RawWL) (t : List ℕ) (v : List ℕ) : ℕ :=
  (p.1.filter (fun y => decide (innerVec p.2 t y = v))).length

/-- The same count, listed at the rank of the tuple `v` rather than at `v` itself. -/
def wlCount (p : RawWL) (t : List ℕ) (j : ℕ) : ℕ :=
  (p.1.filter (fun y => decide (rankIn (vecSet p, innerVec p.2 t y) = j))).length

/-- §5.4.1, the new color of `x⃗` before renaming: the old color of `x⃗` followed by the counts
of the tuples of old colors, each at the rank of its tuple. -/
def wlTagAt (p : RawWL) (t : List ℕ) : List ℕ :=
  tblGet (p.2, t) :: (List.range (vecSet p).length).map (fun j => wlCount p t j)

@[simp] theorem length_wlTagAt (p : RawWL) (t : List ℕ) :
    (wlTagAt p t).length = 1 + (vecSet p).length := by
  simp [wlTagAt, Nat.add_comm]

/-- Reading the count of one tuple off the tag. -/
theorem wlCount_eq_countVec {n k : ℕ} {p : RawWL} (h : RawWL.WF n k p) {q : List ℕ × ℕ}
    (hq : q ∈ p.2) {v : List ℕ} (hv : v ∈ vecSet p) :
    wlCount p q.1 (rankIn (vecSet p, v)) = countVec p q.1 v := by
  rw [wlCount, countVec, ← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
  refine List.countP_congr (fun y hy => ?_)
  have hmem : innerVec p.2 q.1 y ∈ vecSet p := innerVec_mem_vecSet hq hy
  have hlen : ∀ u ∈ vecSet p, u.length = k := fun u hu => length_of_mem_vecSet h hu
  simp only [decide_eq_true_eq]
  constructor
  · intro hr; exact rankIn_inj hlen hmem hv hr
  · intro he; rw [he]

/-- A tuple that does not occur is counted `0` times. -/
theorem countVec_eq_zero {p : RawWL} {q : List ℕ × ℕ} (hq : q ∈ p.2) {v : List ℕ}
    (hv : v ∉ vecSet p) : countVec p q.1 v = 0 := by
  rw [countVec, List.length_eq_zero_iff, List.filter_eq_nil_iff]
  intro y hy hc
  exact hv (by rw [← of_decide_eq_true hc]; exact innerVec_mem_vecSet hq hy)

/-- A rank that no occurring tuple has is counted `0` times. -/
theorem wlCount_eq_zero {p : RawWL} {q : List ℕ × ℕ} (hq : q ∈ p.2) {j : ℕ}
    (hj : ∀ v ∈ vecSet p, rankIn (vecSet p, v) ≠ j) : wlCount p q.1 j = 0 := by
  rw [wlCount, List.length_eq_zero_iff, List.filter_eq_nil_iff]
  intro y hy hc
  exact hj _ (innerVec_mem_vecSet hq hy) (of_decide_eq_true hc)

/-- **Two tuples get the same tag exactly when they have the same old color and the same
multiset of tuples of old colors.** -/
theorem wlTagAt_eq_iff_countVec {n k : ℕ} {p : RawWL} (h : RawWL.WF n k p)
    {q q' : List ℕ × ℕ} (hq : q ∈ p.2) (hq' : q' ∈ p.2) :
    wlTagAt p q.1 = wlTagAt p q'.1
      ↔ (tblGet (p.2, q.1) = tblGet (p.2, q'.1) ∧ ∀ v, countVec p q.1 v = countVec p q'.1 v) := by
  constructor
  · intro hh
    have hhead : tblGet (p.2, q.1) = tblGet (p.2, q'.1) := by
      have := congrArg (fun l => l.headD 0) hh
      simpa [wlTagAt] using this
    have htail : ∀ j ∈ List.range (vecSet p).length, wlCount p q.1 j = wlCount p q'.1 j := by
      have h2 := congrArg List.tail hh
      simp only [wlTagAt, List.tail_cons] at h2
      exact List.map_inj_left.1 h2
    refine ⟨hhead, fun v => ?_⟩
    by_cases hv : v ∈ vecSet p
    · have hj : rankIn (vecSet p, v) ∈ List.range (vecSet p).length :=
        List.mem_range.2 (rankIn_lt_length hv)
      exact (wlCount_eq_countVec h hq hv).symm.trans
        ((htail _ hj).trans (wlCount_eq_countVec h hq' hv))
    · rw [countVec_eq_zero hq hv, countVec_eq_zero hq' hv]
  · rintro ⟨hhead, hcnt⟩
    rw [wlTagAt, wlTagAt, hhead]
    congr 1
    refine List.map_congr_left (fun j hj => ?_)
    by_cases hex : ∃ v ∈ vecSet p, rankIn (vecSet p, v) = j
    · obtain ⟨v, hv, rfl⟩ := hex
      exact (wlCount_eq_countVec h hq hv).trans
        ((hcnt v).trans (wlCount_eq_countVec h hq' hv).symm)
    · push_neg at hex
      rw [wlCount_eq_zero hq hex, wlCount_eq_zero hq' hex]

/-! ### The tag and one round of `Babai.KAryPartStruct.wlStep` -/

/-- Every vertex occurs in the vertex list. -/
theorem mem_dom {n k : ℕ} {p : RawWL} (h : RawWL.WF n k p) (z : Fin n) : (z : ℕ) ∈ p.1 :=
  (h.domMem _).2 z.isLt

/-- **The raw count is the paper's count.** -/
theorem countVec_eq_ncard {n k : ℕ} {p : RawWL} (h : RawWL.WF n k p) (x : Str (Fin n) k)
    (i : Str ℕ k) :
    countVec p (tupleOf x) (List.ofFn i)
      = {z : Fin n | ∀ j : Fin k, (decWL n k p).color (Str.subst x j z) = i j}.ncard := by
  have hset : {z : Fin n | ∀ j : Fin k, (decWL n k p).color (Str.subst x j z) = i j}
      = {z : Fin n | (z : ℕ) ∈ p.1 ∧
          (fun y => decide (innerVec p.2 (tupleOf x) y = List.ofFn i)) (z : ℕ) = true} := by
    ext z
    simp only [Set.mem_setOf_eq, decide_eq_true_eq]
    constructor
    · intro hz; exact ⟨mem_dom h z, (innerVec_eq_ofFn_iff p x z i).2 hz⟩
    · rintro ⟨-, hz⟩; exact (innerVec_eq_ofFn_iff p x z i).1 hz
  rw [countVec, hset,
    ncard_eq_length_filter (n := n) p.1 h.domNodup (fun a ha => (h.domMem a).1 ha)
      (fun y => decide (innerVec p.2 (tupleOf x) y = List.ofFn i))]

/-- A tuple of old colors that does not have `k` entries is counted `0` times. -/
theorem countVec_eq_zero_of_length {p : RawWL} {t v : List ℕ} (hv : v.length ≠ t.length) :
    countVec p t v = 0 := by
  rw [countVec, List.length_eq_zero_iff, List.filter_eq_nil_iff]
  intro y _ hc
  exact hv (by rw [← of_decide_eq_true hc, length_innerVec])

/-- **One round of the routine is one round of `k`-ary WL refinement.**  Two tuples get the
same tag exactly when `Babai.KAryPartStruct.wlStep` gives them the same color. -/
theorem wlTagAt_eq_iff {n k : ℕ} {p : RawWL} (h : RawWL.WF n k p) {q q' : List ℕ × ℕ}
    (hq : q ∈ p.2) (hq' : q' ∈ p.2) {x x' : Str (Fin n) k} (hx : tupleOf x = q.1)
    (hx' : tupleOf x' = q'.1) :
    wlTagAt p q.1 = wlTagAt p q'.1
      ↔ (decWL n k p).wlStep.color x = (decWL n k p).wlStep.color x' := by
  rw [wlTagAt_eq_iff_countVec h hq hq', KAryPartStruct.wlStep_color_eq_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨by rw [decWL_color, decWL_color, hx, hx']; exact h1, fun i => ?_⟩
    rw [← countVec_eq_ncard h x i, ← countVec_eq_ncard h x' i, hx, hx']
    exact h2 (List.ofFn i)
  · rintro ⟨h1, h2⟩
    refine ⟨by rw [← hx, ← hx']; exact h1, fun v => ?_⟩
    by_cases hlen : v.length = k
    · obtain ⟨i, rfl⟩ : ∃ i : Str ℕ k, List.ofFn i = v := by
        subst hlen
        exact ⟨fun j => v[(j : ℕ)], by simp⟩
      rw [← hx, ← hx', countVec_eq_ncard h x i, countVec_eq_ncard h x' i]
      exact h2 i
    · have hk : q.1.length = k := ((h.keyMem q.1).1 (List.mem_map_of_mem hq)).1
      have hk' : q'.1.length = k := ((h.keyMem q'.1).1 (List.mem_map_of_mem hq')).1
      rw [countVec_eq_zero_of_length (by rw [hk]; exact hlen),
        countVec_eq_zero_of_length (by rw [hk']; exact hlen)]

/-! ### Renaming and the round

§4.1.1, applied again: the new name of a tag is its rank among the tags that occur, so the
colors are again naturals below the number of rows. -/

/-- The tags of the tuples, in the order the table lists them. -/
def wlTags (p : RawWL) : List (List ℕ) := p.2.map (fun q => wlTagAt p q.1)

/-- The distinct tags that occur. -/
def wlTagSet (p : RawWL) : List (List ℕ) := RAM.dedupG (([] : List (List ℕ)), wlTags p)

theorem mem_wlTagSet {p : RawWL} {t : List ℕ} : t ∈ wlTagSet p ↔ t ∈ wlTags p :=
  RAM.mem_dedupG_nil _ _

theorem wlTagAt_mem_wlTagSet {p : RawWL} {q : List ℕ × ℕ} (hq : q ∈ p.2) :
    wlTagAt p q.1 ∈ wlTagSet p :=
  mem_wlTagSet.2 (List.mem_map_of_mem hq)

theorem length_wlTagSet_le (p : RawWL) : (wlTagSet p).length ≤ p.2.length := by
  have := RAM.length_dedupG_le (wlTags p)
  simpa [wlTags] using this

/-- §5.4.1 with the renaming of §4.1.1: the new color of a tuple. -/
def wlNewCol (p : RawWL) (t : List ℕ) : ℕ := rankIn (wlTagSet p, wlTagAt p t)

/-- **The new colors are naturals below the number of rows.** -/
theorem wlNewCol_lt {p : RawWL} {q : List ℕ × ℕ} (hq : q ∈ p.2) :
    wlNewCol p q.1 < p.2.length := by
  have h1 : rankIn (wlTagSet p, wlTagAt p q.1) < (wlTagSet p).length :=
    rankIn_lt_length (wlTagAt_mem_wlTagSet hq)
  have h2 := length_wlTagSet_le p
  exact lt_of_lt_of_le h1 h2

/-- **The renaming loses nothing**: two tuples get the same new color exactly when they get the
same tag. -/
theorem wlNewCol_eq_iff {p : RawWL} {q q' : List ℕ × ℕ} (hq : q ∈ p.2) (hq' : q' ∈ p.2) :
    wlNewCol p q.1 = wlNewCol p q'.1 ↔ wlTagAt p q.1 = wlTagAt p q'.1 := by
  constructor
  · intro hh
    refine rankIn_inj (L := 1 + (vecSet p).length) (fun u hu => ?_)
      (wlTagAt_mem_wlTagSet hq) (wlTagAt_mem_wlTagSet hq') hh
    obtain ⟨q'', hq'', rfl⟩ := List.mem_map.1 (mem_wlTagSet.1 hu)
    exact length_wlTagAt p q''.1
  · intro hh; rw [wlNewCol, wlNewCol, hh]

/-- §5.4.1: one round of `k`-ary WL refinement on raw data. -/
def rawWLStep (p : RawWL) : RawWL := (p.1, p.2.map (fun q => (q.1, wlNewCol p q.1)))

@[simp] theorem rawWLStep_fst (p : RawWL) : (rawWLStep p).1 = p.1 := rfl

@[simp] theorem rawWLStep_keys (p : RawWL) :
    (rawWLStep p).2.map Prod.fst = p.2.map Prod.fst := by
  simp [rawWLStep, List.map_map, Function.comp_def]

@[simp] theorem rawWLStep_length (p : RawWL) : (rawWLStep p).2.length = p.2.length := by
  simp [rawWLStep]

/-- The table of the new round answers the new color. -/
theorem tblGet_rawWLStep {p : RawWL} {q : List ℕ × ℕ} (hq : q ∈ p.2) :
    tblGet ((rawWLStep p).2, q.1) = wlNewCol p q.1 := by
  rw [tblGet, rawWLStep, lookup_map_key (fun t => wlNewCol p t) p.2 q.1,
    if_pos (List.mem_map_of_mem hq)]
  rfl

/-- **Well-formedness is preserved by a round.** -/
theorem rawWLStep_wf {n k : ℕ} {p : RawWL} (h : RawWL.WF n k p) :
    RawWL.WF n k (rawWLStep p) where
  domNodup := h.domNodup
  domMem := h.domMem
  keyNodup := by rw [rawWLStep_keys]; exact h.keyNodup
  keyMem := by rw [rawWLStep_keys]; exact h.keyMem
  colLt := by
    intro q hq
    obtain ⟨q', hq', rfl⟩ := List.mem_map.1 hq
    rw [rawWLStep_length]
    exact wlNewCol_lt hq'

/-- Every `k`-tuple of vertices is listed in a well-formed table. -/
theorem tupleOf_mem_keys {n k : ℕ} {p : RawWL} (h : RawWL.WF n k p) (x : Str (Fin n) k) :
    ∃ q ∈ p.2, q.1 = tupleOf x := by
  have : tupleOf x ∈ p.2.map Prod.fst :=
    (h.keyMem _).2 ⟨length_tupleOf x, fun a ha => tupleOf_lt x ha⟩
  obtain ⟨q, hq, hq'⟩ := List.mem_map.1 this
  exact ⟨q, hq, hq'⟩

/-- **One round of the routine is one round of the process.** -/
theorem rawWLStep_spec {n k : ℕ} {p : RawWL} (h : RawWL.WF n k p) (x x' : Str (Fin n) k) :
    (decWL n k (rawWLStep p)).color x = (decWL n k (rawWLStep p)).color x'
      ↔ (decWL n k p).wlStep.color x = (decWL n k p).wlStep.color x' := by
  obtain ⟨q, hq, hqx⟩ := tupleOf_mem_keys h x
  obtain ⟨q', hq', hqx'⟩ := tupleOf_mem_keys h x'
  rw [decWL_color, decWL_color, ← hqx, ← hqx', tblGet_rawWLStep hq, tblGet_rawWLStep hq',
    wlNewCol_eq_iff hq hq']
  exact wlTagAt_eq_iff h hq hq' hqx.symm hqx'.symm

/-! ## The process

§5.4.1: the rounds are repeated until the coloring is stable.  As in
`Workspace/Higher/WL.lean` the number of rounds is fixed in advance at
`|Ω^k × Ω^k| = (n^k)²`, a bound valid for every input on `n` vertices, which keeps the
procedure canonical.  The round count reaches the machine as the length of a list, for the
reason in point 1 of the note on A3 in `Workspace/Algo/DESIGN.md`. -/

theorem wf_rawWLIter {n k : ℕ} {p : RawWL} (h : RawWL.WF n k p) :
    ∀ j : ℕ, RawWL.WF n k (rawWLStep^[j] p)
  | 0 => h
  | j + 1 => by
      rw [Function.iterate_succ_apply']
      exact rawWLStep_wf (wf_rawWLIter h j)

/-- **The routine and the process have the same color classes, round by round.** -/
theorem rawWLIter_spec {n k : ℕ} {p : RawWL} (h : RawWL.WF n k p) :
    ∀ (j : ℕ) (x x' : Str (Fin n) k),
      (decWL n k (rawWLStep^[j] p)).color x = (decWL n k (rawWLStep^[j] p)).color x'
        ↔ ((decWL n k p).wlIter j).color x = ((decWL n k p).wlIter j).color x' := by
  intro j
  induction j with
  | zero => intro x x'; exact Iff.rfl
  | succ j ih =>
      intro x x'
      have hstep := rawWLStep_spec (wf_rawWLIter h j) x x'
      rw [← Function.iterate_succ_apply' rawWLStep j] at hstep
      rw [hstep, KAryPartStruct.wlIter_succ]
      exact KAryPartStruct.wlStep_congr (fun u v => ih u v) x x'

/-! ### The number of rows

A well-formed table lists every `k`-tuple over `[0, n)` once, so it has `n^k` rows.  That is
what turns the fuel `|table|²` into the paper's round count `|Ω^k × Ω^k|`. -/

theorem length_table {n k : ℕ} {p : RawWL} (h : RawWL.WF n k p) : p.2.length = n ^ k := by
  classical
  have hlen : p.2.length = (p.2.map Prod.fst).length := by simp
  have hcard : (p.2.map Prod.fst).toFinset.card = (p.2.map Prod.fst).length :=
    List.toFinset_card_of_nodup h.keyNodup
  have himg : (p.2.map Prod.fst).toFinset
      = Finset.image (fun x : Str (Fin n) k => tupleOf x) Finset.univ := by
    ext t
    simp only [List.mem_toFinset, Finset.mem_image, Finset.mem_univ, true_and]
    rw [h.keyMem t]
    constructor
    · rintro ⟨h1, h2⟩
      obtain ⟨x, hx⟩ := exists_tupleOf h1 h2
      exact ⟨x, hx⟩
    · rintro ⟨x, rfl⟩
      exact ⟨length_tupleOf x, fun a ha => tupleOf_lt x ha⟩
  have hcard2 : (Finset.image (fun x : Str (Fin n) k => tupleOf x) Finset.univ).card
      = Fintype.card (Str (Fin n) k) :=
    Finset.card_image_of_injective _ tupleOf_injective
  rw [hlen, ← hcard, himg, hcard2]
  simp [Str]

/-- A list of length `|table|²`: the fuel of the process. -/
def wlFuel (tbl : List (List ℕ × ℕ)) : List (List ℕ × ℕ) := (tbl.map (fun _ => tbl)).flatten

@[simp] theorem length_wlFuel (tbl : List (List ℕ × ℕ)) :
    (wlFuel tbl).length = tbl.length * tbl.length := by
  rw [wlFuel, List.length_flatten, List.map_map]
  have hc : (List.length ∘ fun _ : List ℕ × ℕ => tbl) = fun _ : List ℕ × ℕ => tbl.length := rfl
  rw [hc, List.map_const', List.sum_replicate, smul_eq_mul]

/-- §5.4.1: the stable `k`-ary refinement, on raw data. -/
def rawWLStable (p : RawWL) : RawWL :=
  List.foldl (fun q _ => rawWLStep q) p (wlFuel p.2)

theorem rawWLStable_eq_iterate (p : RawWL) :
    rawWLStable p = rawWLStep^[p.2.length * p.2.length] p := by
  rw [rawWLStable, foldl_const_eq_iterate_gen, length_wlFuel]

/-- **§5.4.1: the routine and `Babai.KAryPartStruct.wlStable` have the same color classes.**
This is row R7 of `Workspace/Algo/DESIGN.md`, item 1.2. -/
theorem rawWLStable_spec {n k : ℕ} {p : RawWL} (h : RawWL.WF n k p) (x x' : Str (Fin n) k) :
    (decWL n k (rawWLStable p)).color x = (decWL n k (rawWLStable p)).color x'
      ↔ (decWL n k p).wlStable.color x = (decWL n k p).wlStable.color x' := by
  have hcard : Fintype.card (Str (Fin n) k × Str (Fin n) k) = n ^ k * n ^ k := by
    simp [Str]
  rw [rawWLStable_eq_iterate, length_table h]
  show _ ↔ ((decWL n k p).wlIter (Fintype.card (Str (Fin n) k × Str (Fin n) k))).color x
    = ((decWL n k p).wlIter (Fintype.card (Str (Fin n) k × Str (Fin n) k))).color x'
  rw [hcard]
  exact rawWLIter_spec h (n ^ k * n ^ k) x x'

/-- The same statement as an equality of partitions. -/
theorem rawWLStable_kernelSet {n k : ℕ} {p : RawWL} (h : RawWL.WF n k p) :
    kernelSet (decWL n k (rawWLStable p)).color = kernelSet (decWL n k p).wlStable.color := by
  ext q
  simp only [mem_kernelSet]
  exact rawWLStable_spec h q.1 q.2

/-- §5.2, row R6 of `Workspace/Algo/DESIGN.md`, item 1.2: the routine computes the functor
`F3`, which §5.4.1 constructs as the `k`-ary WL refinement run to stability. -/
theorem rawWLStable_F3 {n k : ℕ} {p : RawWL} (h : RawWL.WF n k p) (x x' : Str (Fin n) k) :
    (decWL n k (rawWLStable p)).color x = (decWL n k (rawWLStable p)).color x'
      ↔ (decWL n k p).F3.color x = (decWL n k p).F3.color x' :=
  rawWLStable_spec h x x'

/-- The answer is again a well-formed table. -/
theorem rawWLStable_wf {n k : ℕ} {p : RawWL} (h : RawWL.WF n k p) :
    RawWL.WF n k (rawWLStable p) := by
  rw [rawWLStable_eq_iterate]
  exact wf_rawWLIter h _

end Algo
