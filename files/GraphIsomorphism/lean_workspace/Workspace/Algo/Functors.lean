/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: the functors `F1` (§5.1.3) and `F2` (§5.1.5) on raw data, and the
pipeline `F3 ∘ F2 ∘ F1` of §5.2.
-/
import Workspace.Algo.TupleTable
import Workspace.Algo.WLGuarded

/-!
# §5.1.3, §5.1.5, §5.2 — the functors `F1` and `F2` as routines

This is the second half of the work package **A8** of `Workspace/Algo/DESIGN.md`: rows **R4**
and **R5** of item 1.2.  Row R6 (`F3`) is the `k`-ary WL refinement of
`Workspace/Algo/WLRaw.lean`, and this file assembles the three into the pipeline of §5.2.

* `F1` (line 3103): *"There is a functor `F1`, computable in time `|C| · n^{O(k)}`, that
  converts `k`-ary structures into `k`-ary partition structures … We define `F1(X)` as follows.
  Assign to each `x⃗ ∈ Ω^k` the color `c(x⃗) = {i ∈ C | x⃗ ∈ Rᵢ}`."*
* `F2` (line 3168): *"There is a functor `F2`, computable in time `n^{O(k)}`, that converts
  `k`-ary partition structures into `k`-ary configurations … `F2` assigns to each partition
  structure its unique coarsest refinement that is a configuration."*  The construction is the
  one supplied in `Workspace/Higher/Configurations.lean` (the paper leaves it as
  "ADD DETAILS HERE"): the new color of `x⃗` is the equality type `ρ(x⃗)` together with the list
  of the old colors of the strings `τ(x⃗)`, `τ ∈ 𝔐_k`.

Both are `map`s over the table of `k`-tuples, with the same renaming of the colors as in
§4.1.1: the new name of a tag is its rank among the tags that occur, so the colors stay
naturals below the number of rows.

## Where the index sets come from

`F1` reads the relations, and nothing else, so its routine is uniform in `k`.

`F2` needs two index sets: the pairs `(i, j) ∈ [k]²`, for the equality type `ρ(x⃗)`, and the
whole transformation monoid `𝔐_k = [k]^{[k]}`, for the strings `τ(x⃗)`.  Both are lists of
tuples over `[0, k)`, so both are `Algo.tuplesOf (List.range k)`, and for a **fixed** `k` they
are constants.  That is the reading of row R5 of item 1.2 ("`P` for fixed `k`"): the running
time statements below carry `k` as a parameter of the theorem, not of the input.  The
transformation monoid has `k^k` elements, which is *not* bounded by the size of the table when
`k > n`, so the uniform-in-`k` statement that `Workspace/Algo/WLRaw.lean` proves for `F3` is
**not** available for `F2` in this shape; see the note on A8 session 3 in
`Workspace/Algo/DESIGN.md`.

## Main definitions

* `Algo.RawRelStruct`, `Algo.decRel` — a raw `k`-ary relational structure and its decoding;
* `Algo.membVec`, `Algo.f1NewCol`, `Algo.rawF1` — the functor `F1`;
* `Algo.pairIdx`, `Algo.monIdx`, `Algo.applyIdx`, `Algo.rhoCode`, `Algo.f2TagAt`,
  `Algo.f2NewCol`, `Algo.rawF2` — the functor `F2`;
* `Algo.rawPipeline` — `F3 ∘ F2 ∘ F1` on the table.

## Main results

* `Algo.rawF1_spec`, `Algo.rawF2_spec` — the routines have the color classes of `Babai.F1`
  and `Babai.F2`;
* `Algo.rawF1_wf`, `Algo.rawF2_wf` — the answers are well-formed tables;
* `Algo.rawPipeline_spec` — the pipeline has the color classes of `F3 ∘ F2 ∘ F1`;
* `Algo.polyFun_rawF1`, `Algo.polyFun_rawF2`, `Algo.polyFun_rawPipeline` — the running times;
* `Algo.polyFun_rawF2I`, `Algo.polyFun_rawPipelineI` — the same with the index sets of `F2`
  supplied as data, which is what makes the arity an input (`Workspace/Algo/FunctorsGuarded.lean`).

No axiom and no `sorry`.
-/

namespace Algo

open Babai RAM

/-! ## §5.1.2 — raw `k`-ary relational structures

"A `k`-ary relational structure … is a pair `X = (Ω, R)` where `R = (Rᵢ : i ∈ C)` where each
`Rᵢ` is a `k`-ary relation on `Ω`."  On raw data the colors are the naturals `0, 1, …`, a
relation is the list of the tuples it contains, and a structure is the list of its relations. -/

/-- A raw `k`-ary relation: the list of the tuples it contains. -/
abbrev RawRel := List (List ℕ)

/-- A raw `k`-ary relational structure: one relation per color, the colors being the positions
in the list. -/
abbrev RawRelStruct := List RawRel

/-- **The decoding** of a raw `k`-ary relational structure.  A color beyond the list indexes
the empty relation. -/
def decRel (n k : ℕ) (rels : RawRelStruct) : KAryRelStruct (Fin n) ℕ k :=
  ⟨fun i => {x | tupleOf x ∈ rels.getD i []}⟩

@[simp] theorem mem_decRel_rel {n k : ℕ} (rels : RawRelStruct) (i : ℕ) (x : Str (Fin n) k) :
    x ∈ (decRel n k rels).rel i ↔ tupleOf x ∈ rels.getD i [] := Iff.rfl

theorem getD_of_length_le {rels : RawRelStruct} {i : ℕ} (h : rels.length ≤ i) :
    rels.getD i [] = [] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]
  rfl

/-! ## §5.1.3 — the functor `F1`

"Assign to each `x⃗ ∈ Ω^k` the color `c(x⃗) = {i ∈ C | x⃗ ∈ Rᵢ}`."  On raw data that set is its
characteristic vector over the colors that the input lists. -/

/-- §5.1.3: the color `c(x⃗) = {i ∈ C | x⃗ ∈ Rᵢ}`, as the characteristic vector of the tuple over
the relations listed. -/
def membVec (z : RawRelStruct × List ℕ) : List ℕ :=
  z.1.map (fun R => if z.2 ∈ R then 1 else 0)

@[simp] theorem length_membVec (rels : RawRelStruct) (t : List ℕ) :
    (membVec (rels, t)).length = rels.length := by simp [membVec]

theorem membVec_eq_iff (rels : RawRelStruct) (t t' : List ℕ) :
    membVec (rels, t) = membVec (rels, t') ↔ ∀ R ∈ rels, (t ∈ R ↔ t' ∈ R) := by
  rw [membVec, membVec, List.map_inj_left]
  refine forall_congr' (fun R => forall_congr' (fun _ => ?_))
  by_cases h1 : t ∈ R <;> by_cases h2 : t' ∈ R <;> simp [h1, h2]

theorem membVec_eq_iff_index (rels : RawRelStruct) (t t' : List ℕ) :
    membVec (rels, t) = membVec (rels, t')
      ↔ ∀ i : ℕ, (t ∈ rels.getD i [] ↔ t' ∈ rels.getD i []) := by
  rw [membVec_eq_iff]
  constructor
  · intro h i
    rcases Nat.lt_or_ge i rels.length with hi | hi
    · rw [List.getD_eq_getElem _ _ hi]
      exact h _ (List.getElem_mem hi)
    · rw [getD_of_length_le hi]; simp
  · intro h R hR
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hR
    have := h i
    rwa [List.getD_eq_getElem _ _ hi] at this

/-- §5.1.3: the color `F1` gives to a tuple, read as an equality of colors. -/
theorem F1_color_eq_iff (n k : ℕ) (rels : RawRelStruct) (x x' : Str (Fin n) k) :
    (decRel n k rels).F1.color x = (decRel n k rels).F1.color x'
      ↔ ∀ i : ℕ, (tupleOf x ∈ rels.getD i [] ↔ tupleOf x' ∈ rels.getD i []) := by
  rw [KAryRelStruct.F1_color, KAryRelStruct.F1_color]
  constructor
  · intro h i
    have := Set.ext_iff.1 h i
    simpa using this
  · intro h
    ext i
    simpa using h i

/-- The input of the routine computing `F1`: the table of the `k`-tuples (whose colors are
ignored) and the relations. -/
abbrev RawF1In := RawWL × RawRelStruct

/-- The characteristic vectors that occur, in the order the table lists the tuples. -/
def f1Tags (a : RawF1In) : List (List ℕ) := a.1.2.map (fun q => membVec (a.2, q.1))

/-- The distinct characteristic vectors that occur. -/
def f1TagSet (a : RawF1In) : List (List ℕ) := RAM.dedupG (([] : List (List ℕ)), f1Tags a)

theorem mem_f1TagSet {a : RawF1In} {t : List ℕ} : t ∈ f1TagSet a ↔ t ∈ f1Tags a :=
  RAM.mem_dedupG_nil _ _

theorem nodup_f1TagSet (a : RawF1In) : (f1TagSet a).Nodup := RAM.nodup_dedupG _

theorem length_f1TagSet_le (a : RawF1In) : (f1TagSet a).length ≤ a.1.2.length := by
  have := RAM.length_dedupG_le (f1Tags a)
  simpa [f1Tags] using this

theorem membVec_mem_f1TagSet {a : RawF1In} {q : List ℕ × ℕ} (hq : q ∈ a.1.2) :
    membVec (a.2, q.1) ∈ f1TagSet a :=
  mem_f1TagSet.2 (List.mem_map_of_mem hq)

/-- §5.1.3 with the renaming of §4.1.1: the new color of a tuple is the rank of its
characteristic vector among those that occur.  §5.1.3 asks for exactly this order: *"The linear
ordering of `C` induces the lexicographic ordering of `C'`"* — the relations are listed in the
order of `C`, so the lexicographic order on the characteristic vectors is that ordering of the
subsets of `C`. -/
def f1NewCol (a : RawF1In) (t : List ℕ) : ℕ := rankIn (f1TagSet a, membVec (a.2, t))

theorem f1NewCol_lt {a : RawF1In} {q : List ℕ × ℕ} (hq : q ∈ a.1.2) :
    f1NewCol a q.1 < a.1.2.length :=
  lt_of_lt_of_le (rankIn_lt_length (membVec_mem_f1TagSet hq)) (length_f1TagSet_le a)

/-- **The renaming loses nothing.** -/
theorem f1NewCol_eq_iff {a : RawF1In} {q q' : List ℕ × ℕ} (hq : q ∈ a.1.2) (hq' : q' ∈ a.1.2) :
    f1NewCol a q.1 = f1NewCol a q'.1 ↔ membVec (a.2, q.1) = membVec (a.2, q'.1) := by
  constructor
  · intro hh
    refine rankIn_inj (L := a.2.length) (fun u hu => ?_) (membVec_mem_f1TagSet hq)
      (membVec_mem_f1TagSet hq') hh
    obtain ⟨q'', -, rfl⟩ := List.mem_map.1 (mem_f1TagSet.1 hu)
    exact length_membVec a.2 q''.1
  · intro hh; rw [f1NewCol, f1NewCol, hh]

/-- **§5.1.3, the functor `F1` as a routine**: recolor the table of `k`-tuples by the rank of
the characteristic vector of the tuple. -/
def rawF1 (a : RawF1In) : RawWL := (a.1.1, a.1.2.map (fun q => (q.1, f1NewCol a q.1)))

@[simp] theorem rawF1_fst (a : RawF1In) : (rawF1 a).1 = a.1.1 := rfl

@[simp] theorem rawF1_keys (a : RawF1In) :
    (rawF1 a).2.map Prod.fst = a.1.2.map Prod.fst := by
  simp [rawF1, List.map_map, Function.comp_def]

@[simp] theorem rawF1_length (a : RawF1In) : (rawF1 a).2.length = a.1.2.length := by
  simp [rawF1]

theorem tblGet_rawF1 {a : RawF1In} {q : List ℕ × ℕ} (hq : q ∈ a.1.2) :
    tblGet ((rawF1 a).2, q.1) = f1NewCol a q.1 := by
  rw [tblGet, rawF1, lookup_map_key (fun t => f1NewCol a t) a.1.2 q.1,
    if_pos (List.mem_map_of_mem hq)]
  rfl

/-- **The answer is a well-formed table.** -/
theorem rawF1_wf {n k : ℕ} {a : RawF1In} (h : RawWL.WF n k a.1) : RawWL.WF n k (rawF1 a) where
  domNodup := h.domNodup
  domMem := h.domMem
  keyNodup := by rw [rawF1_keys]; exact h.keyNodup
  keyMem := by rw [rawF1_keys]; exact h.keyMem
  colLt := by
    intro q hq
    obtain ⟨q', hq', rfl⟩ := List.mem_map.1 hq
    rw [rawF1_length]
    exact f1NewCol_lt hq'

/-- **§5.1.3, row R4 of `Workspace/Algo/DESIGN.md`, item 1.2: the routine computes `F1`.**  The
routine and `Babai.KAryRelStruct.F1` give the same color classes. -/
theorem rawF1_spec {n k : ℕ} {a : RawF1In} (h : RawWL.WF n k a.1) (x x' : Str (Fin n) k) :
    (decWL n k (rawF1 a)).color x = (decWL n k (rawF1 a)).color x'
      ↔ (decRel n k a.2).F1.color x = (decRel n k a.2).F1.color x' := by
  obtain ⟨q, hq, hqx⟩ := tupleOf_mem_keys h x
  obtain ⟨q', hq', hqx'⟩ := tupleOf_mem_keys h x'
  rw [decWL_color, decWL_color, ← hqx, ← hqx', tblGet_rawF1 hq, tblGet_rawF1 hq',
    f1NewCol_eq_iff hq hq', hqx, hqx', F1_color_eq_iff, membVec_eq_iff_index]

/-! ## §5.1.5 — the functor `F2`

The color of `x⃗` is the equality type `ρ(x⃗)` on `[k]` together with the old colors of all the
strings `τ(x⃗)`, `τ ∈ 𝔐_k`.  Both index sets are lists of tuples over `[0, k)`: the pairs for
`ρ`, the `k`-tuples for `𝔐_k`. -/

/-- The index set of the equality type `ρ(x⃗)`: the pairs `(i, j) ∈ [k]²`. -/
def pairIdx (k : ℕ) : List (List ℕ) := tuplesOf (List.range k) 2

/-- The index set of the strings `τ(x⃗)`: Notation 5.1.5's symmetric monoid `𝔐_k`, as the list
of all `k`-tuples over `[0, k)`. -/
def monIdx (k : ℕ) : List (List ℕ) := tuplesOf (List.range k) k

theorem mem_pairIdx {k : ℕ} {s : List ℕ} :
    s ∈ pairIdx k ↔ (s.length = 2 ∧ ∀ a ∈ s, a < k) := by
  rw [pairIdx, mem_tuplesOf]
  simp [List.mem_range]

theorem mem_monIdx {k : ℕ} {σ : List ℕ} :
    σ ∈ monIdx k ↔ (σ.length = k ∧ ∀ a ∈ σ, a < k) := by
  rw [monIdx, mem_tuplesOf]
  simp [List.mem_range]

/-- Notation 5.1.5 on raw tuples: the string `τ(x⃗)`, i.e. `x⃗ ∘ τ`. -/
def applyIdx (z : List ℕ × List ℕ) : List ℕ := z.2.map (fun i => z.1.getD i 0)

/-- The pair of index sets `F2` reads: the pairs `(i, j) ∈ [k]²` and the monoid `𝔐_k`.  They are
passed to the routine as data, so that the routine itself is uniform in `k`; see
`Workspace/Algo/FunctorsGuarded.lean`. -/
abbrev IdxP : Type := List (List ℕ) × List (List ℕ)

/-- The two index sets of `F2` at the arity `k`. -/
def idxOf (k : ℕ) : IdxP := (pairIdx k, monIdx k)

@[simp] theorem fst_idxOf (k : ℕ) : (idxOf k).1 = pairIdx k := rfl
@[simp] theorem snd_idxOf (k : ℕ) : (idxOf k).2 = monIdx k := rfl

/-- The equality type `ρ(x⃗)` over a given list of index pairs. -/
def rhoCodeI (P : List (List ℕ)) (t : List ℕ) : List ℕ :=
  P.map (fun s => if t.getD (s.getD 0 0) 0 = t.getD (s.getD 1 0) 0 then 1 else 0)

@[simp] theorem length_rhoCodeI (P : List (List ℕ)) (t : List ℕ) :
    (rhoCodeI P t).length = P.length := by simp [rhoCodeI]

/-- The equality type `ρ(x⃗)`, as the list of the indicators of `xᵢ = xⱼ`. -/
def rhoCode (k : ℕ) (t : List ℕ) : List ℕ := rhoCodeI (pairIdx k) t

@[simp] theorem length_rhoCode (k : ℕ) (t : List ℕ) :
    (rhoCode k t).length = (pairIdx k).length := by simp [rhoCode]

/-- §5.1.5 with the index sets supplied as data: the new color of `x⃗` before renaming. -/
def f2TagAtI (I : IdxP) (p : RawWL) (t : List ℕ) : List ℕ :=
  rhoCodeI I.1 t ++ I.2.map (fun σ => tblGet (p.2, applyIdx (t, σ)))

/-- §5.1.5: the new color of `x⃗` before renaming. -/
def f2TagAt (k : ℕ) (p : RawWL) (t : List ℕ) : List ℕ := f2TagAtI (idxOf k) p t

@[simp] theorem length_f2TagAtI (I : IdxP) (p : RawWL) (t : List ℕ) :
    (f2TagAtI I p t).length = I.1.length + I.2.length := by
  simp [f2TagAtI]

@[simp] theorem length_f2TagAt (k : ℕ) (p : RawWL) (t : List ℕ) :
    (f2TagAt k p t).length = (pairIdx k).length + (monIdx k).length := by
  simp [f2TagAt]

theorem f2TagAtI_eq_iff_parts (I : IdxP) (p : RawWL) (t t' : List ℕ) :
    f2TagAtI I p t = f2TagAtI I p t'
      ↔ (rhoCodeI I.1 t = rhoCodeI I.1 t' ∧
          ∀ σ ∈ I.2, tblGet (p.2, applyIdx (t, σ)) = tblGet (p.2, applyIdx (t', σ))) := by
  constructor
  · intro hh
    obtain ⟨h1, h2⟩ := List.append_inj hh (by simp)
    exact ⟨h1, List.map_inj_left.1 h2⟩
  · rintro ⟨h1, h2⟩
    rw [f2TagAtI, f2TagAtI, h1]
    congr 1
    exact List.map_congr_left h2

theorem f2TagAt_eq_iff_parts (k : ℕ) (p : RawWL) (t t' : List ℕ) :
    f2TagAt k p t = f2TagAt k p t'
      ↔ (rhoCode k t = rhoCode k t' ∧
          ∀ σ ∈ monIdx k, tblGet (p.2, applyIdx (t, σ)) = tblGet (p.2, applyIdx (t', σ))) :=
  f2TagAtI_eq_iff_parts (idxOf k) p t t'

/-! ### Reading the tag off a tuple of vertices -/

theorem getD_tupleOf {n k : ℕ} (x : Str (Fin n) k) {i : ℕ} (hi : i < k) :
    (tupleOf x).getD i 0 = (x ⟨i, hi⟩ : ℕ) := by
  have h : i < (tupleOf x).length := by rw [length_tupleOf]; exact hi
  rw [List.getD_eq_getElem _ _ h, getElem_tupleOf]

/-- The equality type of the raw tuple is the equality type of the tuple. -/
theorem rhoCode_eq_iff {n k : ℕ} (x y : Str (Fin n) k) :
    rhoCode k (tupleOf x) = rhoCode k (tupleOf y) ↔ ∀ i j : Fin k, (x i = x j ↔ y i = y j) := by
  rw [rhoCode, rhoCode, rhoCodeI, rhoCodeI, List.map_inj_left]
  constructor
  · intro h i j
    have hs : ([(i : ℕ), (j : ℕ)] : List ℕ) ∈ pairIdx k := by
      refine mem_pairIdx.2 ⟨rfl, ?_⟩
      intro a ha
      rcases List.mem_cons.1 ha with rfl | ha'
      · exact i.isLt
      · rcases List.mem_cons.1 ha' with rfl | ha''
        · exact j.isLt
        · simp at ha''
    have := h _ hs
    have hgi : ([(i : ℕ), (j : ℕ)] : List ℕ).getD 0 0 = (i : ℕ) := rfl
    have hgj : ([(i : ℕ), (j : ℕ)] : List ℕ).getD 1 0 = (j : ℕ) := rfl
    rw [hgi, hgj, getD_tupleOf x i.isLt, getD_tupleOf x j.isLt, getD_tupleOf y i.isLt,
      getD_tupleOf y j.isLt] at this
    have hx : (⟨(i : ℕ), i.isLt⟩ : Fin k) = i := Fin.ext rfl
    have hy : (⟨(j : ℕ), j.isLt⟩ : Fin k) = j := Fin.ext rfl
    rw [hx, hy] at this
    constructor
    · intro hij
      by_contra hc
      have h1 : ((x i : ℕ) = (x j : ℕ)) := by rw [hij]
      have h2 : ((y i : ℕ) ≠ (y j : ℕ)) := fun hh => hc (Fin.ext hh)
      rw [if_pos h1, if_neg h2] at this
      exact absurd this (by omega)
    · intro hij
      by_contra hc
      have h1 : ((y i : ℕ) = (y j : ℕ)) := by rw [hij]
      have h2 : ((x i : ℕ) ≠ (x j : ℕ)) := fun hh => hc (Fin.ext hh)
      rw [if_neg h2, if_pos h1] at this
      exact absurd this (by omega)
  · intro h s hs
    obtain ⟨hlen, hlt⟩ := mem_pairIdx.1 hs
    have h0 : s.getD 0 0 < k := by
      have : (0 : ℕ) < s.length := by rw [hlen]; omega
      rw [List.getD_eq_getElem _ _ this]
      exact hlt _ (List.getElem_mem this)
    have h1 : s.getD 1 0 < k := by
      have : (1 : ℕ) < s.length := by rw [hlen]; omega
      rw [List.getD_eq_getElem _ _ this]
      exact hlt _ (List.getElem_mem this)
    rw [getD_tupleOf x h0, getD_tupleOf x h1, getD_tupleOf y h0, getD_tupleOf y h1]
    have hiff := h ⟨s.getD 0 0, h0⟩ ⟨s.getD 1 0, h1⟩
    by_cases hc : (x ⟨s.getD 0 0, h0⟩ : ℕ) = (x ⟨s.getD 1 0, h1⟩ : ℕ)
    · have hc' : (y ⟨s.getD 0 0, h0⟩ : ℕ) = (y ⟨s.getD 1 0, h1⟩ : ℕ) :=
        congrArg Fin.val (hiff.1 (Fin.ext hc))
      rw [if_pos hc, if_pos hc']
    · have hc' : ¬ ((y ⟨s.getD 0 0, h0⟩ : ℕ) = (y ⟨s.getD 1 0, h1⟩ : ℕ)) := by
        intro hh
        exact hc (congrArg Fin.val (hiff.2 (Fin.ext hh)))
      rw [if_neg hc, if_neg hc']

/-- Substitution of indices in a raw tuple is `Str.idx`. -/
theorem applyIdx_tupleOf {n k : ℕ} (x : Str (Fin n) k) (τ : Mon k) :
    applyIdx (tupleOf x, List.ofFn (fun i : Fin k => (τ i : ℕ))) = tupleOf (Str.idx τ x) := by
  rw [applyIdx, List.map_ofFn, tupleOf]
  refine congrArg List.ofFn (funext (fun i => ?_))
  show (tupleOf x).getD ((τ i : ℕ)) 0 = _
  rw [getD_tupleOf x (τ i).isLt]
  have : (⟨((τ i : ℕ)), (τ i).isLt⟩ : Fin k) = τ i := Fin.ext rfl
  rw [this]
  rfl

theorem monIdx_ofFn {k : ℕ} (τ : Mon k) : List.ofFn (fun i : Fin k => (τ i : ℕ)) ∈ monIdx k := by
  refine mem_monIdx.2 ⟨by simp, ?_⟩
  intro a ha
  rw [List.mem_ofFn] at ha
  obtain ⟨i, rfl⟩ := ha
  exact (τ i).isLt

theorem exists_mon_of_mem_monIdx {k : ℕ} {σ : List ℕ} (h : σ ∈ monIdx k) :
    ∃ τ : Mon k, σ = List.ofFn (fun i : Fin k => (τ i : ℕ)) := by
  obtain ⟨hlen, hlt⟩ := mem_monIdx.1 h
  have hgd : ∀ i : Fin k, σ.getD (i : ℕ) 0 < k := by
    intro i
    have hi : (i : ℕ) < σ.length := by rw [hlen]; exact i.isLt
    rw [List.getD_eq_getElem _ _ hi]
    exact hlt _ (List.getElem_mem hi)
  refine ⟨fun i => ⟨σ.getD (i : ℕ) 0, hgd i⟩, ?_⟩
  refine List.ext_getElem (by simp [hlen]) (fun j h1 h2 => ?_)
  simp only [List.getElem_ofFn]
  show σ[j] = σ.getD j 0
  rw [List.getD_eq_getElem _ _ h1]

/-- **The tag is the color of `F2`.**  Two tuples get the same tag exactly when
`Babai.KAryPartStruct.F2` gives them the same color. -/
theorem f2TagAt_eq_iff {n k : ℕ} (p : RawWL) (x y : Str (Fin n) k) :
    f2TagAt k p (tupleOf x) = f2TagAt k p (tupleOf y)
      ↔ (decWL n k p).F2.color x = (decWL n k p).F2.color y := by
  rw [f2TagAt_eq_iff_parts, KAryPartStruct.F2_color_eq_iff, rhoCode_eq_iff]
  refine and_congr Iff.rfl ?_
  constructor
  · intro h τ
    have := h _ (monIdx_ofFn τ)
    rw [applyIdx_tupleOf x τ, applyIdx_tupleOf y τ] at this
    exact this
  · intro h σ hσ
    obtain ⟨τ, rfl⟩ := exists_mon_of_mem_monIdx hσ
    rw [applyIdx_tupleOf x τ, applyIdx_tupleOf y τ]
    exact h τ

/-! ### The renaming, and the round -/

/-- The tags of the tuples, in the order the table lists them. -/
def f2TagsI (I : IdxP) (p : RawWL) : List (List ℕ) := p.2.map (fun q => f2TagAtI I p q.1)

/-- The distinct tags that occur. -/
def f2TagSetI (I : IdxP) (p : RawWL) : List (List ℕ) :=
  RAM.dedupG (([] : List (List ℕ)), f2TagsI I p)

/-- The tags of the tuples, in the order the table lists them. -/
def f2Tags (k : ℕ) (p : RawWL) : List (List ℕ) := f2TagsI (idxOf k) p

/-- The distinct tags that occur. -/
def f2TagSet (k : ℕ) (p : RawWL) : List (List ℕ) := f2TagSetI (idxOf k) p

theorem mem_f2TagSetI {I : IdxP} {p : RawWL} {t : List ℕ} :
    t ∈ f2TagSetI I p ↔ t ∈ f2TagsI I p := RAM.mem_dedupG_nil _ _

theorem mem_f2TagSet {k : ℕ} {p : RawWL} {t : List ℕ} :
    t ∈ f2TagSet k p ↔ t ∈ f2Tags k p := RAM.mem_dedupG_nil _ _

theorem nodup_f2TagSet (k : ℕ) (p : RawWL) : (f2TagSet k p).Nodup := RAM.nodup_dedupG _

theorem length_f2TagSetI_le (I : IdxP) (p : RawWL) : (f2TagSetI I p).length ≤ p.2.length := by
  have := RAM.length_dedupG_le (f2TagsI I p)
  simpa [f2TagsI] using this

theorem length_f2TagSet_le (k : ℕ) (p : RawWL) : (f2TagSet k p).length ≤ p.2.length :=
  length_f2TagSetI_le _ p

theorem f2TagAtI_mem_f2TagSetI {I : IdxP} {p : RawWL} {q : List ℕ × ℕ} (hq : q ∈ p.2) :
    f2TagAtI I p q.1 ∈ f2TagSetI I p := mem_f2TagSetI.2 (List.mem_map_of_mem hq)

theorem f2TagAt_mem_f2TagSet {k : ℕ} {p : RawWL} {q : List ℕ × ℕ} (hq : q ∈ p.2) :
    f2TagAt k p q.1 ∈ f2TagSet k p := f2TagAtI_mem_f2TagSetI hq

/-- §5.1.5 with the renaming of §4.1.1: the new color of a tuple. -/
def f2NewColI (I : IdxP) (p : RawWL) (t : List ℕ) : ℕ :=
  rankIn (f2TagSetI I p, f2TagAtI I p t)

/-- §5.1.5 with the renaming of §4.1.1: the new color of a tuple. -/
def f2NewCol (k : ℕ) (p : RawWL) (t : List ℕ) : ℕ := f2NewColI (idxOf k) p t

theorem f2NewColI_lt {I : IdxP} {p : RawWL} {q : List ℕ × ℕ} (hq : q ∈ p.2) :
    f2NewColI I p q.1 < p.2.length :=
  lt_of_lt_of_le (rankIn_lt_length (f2TagAtI_mem_f2TagSetI hq)) (length_f2TagSetI_le I p)

theorem f2NewCol_lt {k : ℕ} {p : RawWL} {q : List ℕ × ℕ} (hq : q ∈ p.2) :
    f2NewCol k p q.1 < p.2.length := f2NewColI_lt hq

/-- **The renaming loses nothing.** -/
theorem f2NewColI_eq_iff {I : IdxP} {p : RawWL} {q q' : List ℕ × ℕ} (hq : q ∈ p.2)
    (hq' : q' ∈ p.2) :
    f2NewColI I p q.1 = f2NewColI I p q'.1 ↔ f2TagAtI I p q.1 = f2TagAtI I p q'.1 := by
  constructor
  · intro hh
    refine rankIn_inj (L := I.1.length + I.2.length) (fun u hu => ?_)
      (f2TagAtI_mem_f2TagSetI hq) (f2TagAtI_mem_f2TagSetI hq') hh
    obtain ⟨q'', -, rfl⟩ := List.mem_map.1 (mem_f2TagSetI.1 hu)
    exact length_f2TagAtI I p q''.1
  · intro hh; rw [f2NewColI, f2NewColI, hh]

/-- **The renaming loses nothing.** -/
theorem f2NewCol_eq_iff {k : ℕ} {p : RawWL} {q q' : List ℕ × ℕ} (hq : q ∈ p.2) (hq' : q' ∈ p.2) :
    f2NewCol k p q.1 = f2NewCol k p q'.1 ↔ f2TagAt k p q.1 = f2TagAt k p q'.1 :=
  f2NewColI_eq_iff hq hq'

/-- **§5.1.5, the functor `F2` as a routine**, with the index sets supplied as data. -/
def rawF2I (I : IdxP) (p : RawWL) : RawWL := (p.1, p.2.map (fun q => (q.1, f2NewColI I p q.1)))

/-- **§5.1.5, the functor `F2` as a routine**: recolor the table of `k`-tuples by the rank of
the tag. -/
def rawF2 (k : ℕ) (p : RawWL) : RawWL := rawF2I (idxOf k) p

@[simp] theorem rawF2I_fst (I : IdxP) (p : RawWL) : (rawF2I I p).1 = p.1 := rfl

@[simp] theorem rawF2_fst (k : ℕ) (p : RawWL) : (rawF2 k p).1 = p.1 := rfl

@[simp] theorem rawF2I_keys (I : IdxP) (p : RawWL) :
    (rawF2I I p).2.map Prod.fst = p.2.map Prod.fst := by
  simp [rawF2I, List.map_map, Function.comp_def]

@[simp] theorem rawF2_keys (k : ℕ) (p : RawWL) :
    (rawF2 k p).2.map Prod.fst = p.2.map Prod.fst := rawF2I_keys _ p

@[simp] theorem rawF2I_length (I : IdxP) (p : RawWL) : (rawF2I I p).2.length = p.2.length := by
  simp [rawF2I]

@[simp] theorem rawF2_length (k : ℕ) (p : RawWL) : (rawF2 k p).2.length = p.2.length :=
  rawF2I_length _ p

theorem tblGet_rawF2I {I : IdxP} {p : RawWL} {q : List ℕ × ℕ} (hq : q ∈ p.2) :
    tblGet ((rawF2I I p).2, q.1) = f2NewColI I p q.1 := by
  rw [tblGet, rawF2I, lookup_map_key (fun t => f2NewColI I p t) p.2 q.1,
    if_pos (List.mem_map_of_mem hq)]
  rfl

theorem tblGet_rawF2 {k : ℕ} {p : RawWL} {q : List ℕ × ℕ} (hq : q ∈ p.2) :
    tblGet ((rawF2 k p).2, q.1) = f2NewCol k p q.1 := tblGet_rawF2I hq

/-- **The answer is a well-formed table.** -/
theorem rawF2I_wf {n k : ℕ} {I : IdxP} {p : RawWL} (h : RawWL.WF n k p) :
    RawWL.WF n k (rawF2I I p) where
  domNodup := h.domNodup
  domMem := h.domMem
  keyNodup := by rw [rawF2I_keys]; exact h.keyNodup
  keyMem := by rw [rawF2I_keys]; exact h.keyMem
  colLt := by
    intro q hq
    obtain ⟨q', hq', rfl⟩ := List.mem_map.1 hq
    rw [rawF2I_length]
    exact f2NewColI_lt hq'

/-- **The answer is a well-formed table.** -/
theorem rawF2_wf {n k : ℕ} {p : RawWL} (h : RawWL.WF n k p) : RawWL.WF n k (rawF2 k p) :=
  rawF2I_wf h

/-- **§5.1.5, row R5 of `Workspace/Algo/DESIGN.md`, item 1.2: the routine computes `F2`.**  The
routine and `Babai.KAryPartStruct.F2` give the same color classes. -/
theorem rawF2_spec {n k : ℕ} {p : RawWL} (h : RawWL.WF n k p) (x x' : Str (Fin n) k) :
    (decWL n k (rawF2 k p)).color x = (decWL n k (rawF2 k p)).color x'
      ↔ (decWL n k p).F2.color x = (decWL n k p).F2.color x' := by
  obtain ⟨q, hq, hqx⟩ := tupleOf_mem_keys h x
  obtain ⟨q', hq', hqx'⟩ := tupleOf_mem_keys h x'
  rw [decWL_color, decWL_color, ← hqx, ← hqx', tblGet_rawF2 hq, tblGet_rawF2 hq',
    f2NewCol_eq_iff hq hq', hqx, hqx', f2TagAt_eq_iff]

/-! ## Congruences of the mathematical functors

The three routines are specified by their color *classes*, so the composite needs the
mathematical functors to depend on their input only through its classes.  For `F2` this is
`Babai.KAryPartStruct.F2_color_eq_iff`; for `F3` it is `Babai.KAryPartStruct.wlStep_congr`,
iterated. -/

/-- `F2` depends on its input only through its color classes. -/
theorem F2_classes_congr {Ω : Type*} {C D : Type*} {k : ℕ} {d : KAryPartStruct Ω C k}
    {e : KAryPartStruct Ω D k}
    (hk : ∀ u v : Str Ω k, d.color u = d.color v ↔ e.color u = e.color v) (x y : Str Ω k) :
    d.F2.color x = d.F2.color y ↔ e.F2.color x = e.F2.color y := by
  rw [KAryPartStruct.F2_color_eq_iff, KAryPartStruct.F2_color_eq_iff]
  exact and_congr Iff.rfl (forall_congr' (fun τ => hk _ _))

/-- The `k`-ary WL process depends on its input only through its color classes. -/
theorem wlIter_classes_congr {Ω : Type*} {C D : Type} {k : ℕ} {d : KAryPartStruct Ω C k}
    {e : KAryPartStruct Ω D k}
    (hk : ∀ u v : Str Ω k, d.color u = d.color v ↔ e.color u = e.color v) :
    ∀ (j : ℕ) (x y : Str Ω k),
      (d.wlIter j).color x = (d.wlIter j).color y
        ↔ (e.wlIter j).color x = (e.wlIter j).color y := by
  intro j
  induction j with
  | zero => intro x y; exact hk x y
  | succ j ih =>
      intro x y
      rw [KAryPartStruct.wlIter_succ, KAryPartStruct.wlIter_succ]
      exact KAryPartStruct.wlStep_congr (fun u v => ih u v) x y

/-- `F3` depends on its input only through its color classes. -/
theorem F3_classes_congr {Ω : Type*} [Fintype Ω] {C D : Type} {k : ℕ}
    {d : KAryPartStruct Ω C k} {e : KAryPartStruct Ω D k}
    (hk : ∀ u v : Str Ω k, d.color u = d.color v ↔ e.color u = e.color v) (x y : Str Ω k) :
    d.F3.color x = d.F3.color y ↔ e.F3.color x = e.F3.color y :=
  wlIter_classes_congr hk _ x y

/-! ## §5.2 — the pipeline `F3 ∘ F2 ∘ F1` -/

/-- §5.2 with the index sets of `F2` supplied as data: the three functors, one after the other,
on the table of `k`-tuples. -/
def rawPipelineI (I : IdxP) (a : RawF1In) : RawWL := rawWLStable (rawF2I I (rawF1 a))

/-- §5.2: the three functors, one after the other, on the table of `k`-tuples. -/
def rawPipeline (k : ℕ) (a : RawF1In) : RawWL := rawPipelineI (idxOf k) a

/-- **§5.2: the pipeline computes `F3 ∘ F2 ∘ F1`.**  This is rows R4, R5 and R6 of
`Workspace/Algo/DESIGN.md`, item 1.2, composed: the routine and the mathematical composite have
the same color classes. -/
theorem rawPipeline_spec {n k : ℕ} {a : RawF1In} (h : RawWL.WF n k a.1) (x x' : Str (Fin n) k) :
    (decWL n k (rawPipeline k a)).color x = (decWL n k (rawPipeline k a)).color x'
      ↔ (decRel n k a.2).F1.F2.F3.color x = (decRel n k a.2).F1.F2.F3.color x' := by
  have h1 : RawWL.WF n k (rawF1 a) := rawF1_wf h
  have h2 : RawWL.WF n k (rawF2 k (rawF1 a)) := rawF2_wf h1
  have hF2 : ∀ u v : Str (Fin n) k,
      (decWL n k (rawF2 k (rawF1 a))).color u = (decWL n k (rawF2 k (rawF1 a))).color v
        ↔ (decRel n k a.2).F1.F2.color u = (decRel n k a.2).F1.F2.color v := by
    intro u v
    rw [rawF2_spec h1 u v]
    exact F2_classes_congr (fun s t => rawF1_spec h s t) u v
  rw [show rawPipeline k a = rawWLStable (rawF2 k (rawF1 a)) from rfl, rawWLStable_spec h2 x x']
  exact F3_classes_congr hF2 x x'

/-- The answer of the pipeline is again a well-formed table. -/
theorem rawPipeline_wf {n k : ℕ} {a : RawF1In} (h : RawWL.WF n k a.1) :
    RawWL.WF n k (rawPipeline k a) := rawWLStable_wf (rawF2_wf (rawF1_wf h))

/-! ## The cost

As in `Workspace/Algo/WLPoly.lean`, the bound is stated **in the size of the table** of
`k`-tuples together with the relations.  `F1` is uniform in `k`; `F2` carries `k` as a
parameter of the statement, because its two index sets are lists of tuples over `[0, k)`. -/

theorem polyFun_membVec : PolyFun membVec := by
  have hf : PolyFun (fun w : List ℕ × RawRel => (if w.1 ∈ w.2 then 1 else 0 : ℕ)) := by
    refine (PolyFun.ite (polyFun_listMem (α := List ℕ) polyFun_listNatEq)
      (polyFun_const 1) (polyFun_const 0)).of_eq (fun w => ?_)
    by_cases h : w.1 ∈ w.2 <;> simp [h]
  exact (polyFun_swap.comp (PolyFun.mapParam hf)).of_eq (fun z => rfl)

theorem polyFun_f1Tags : PolyFun f1Tags := by
  have hf : PolyFun (fun w : RawF1In × (List ℕ × ℕ) => membVec (w.1.2, w.2.1)) :=
    ((polyFun_fst.comp polyFun_snd).pair (polyFun_snd.comp polyFun_fst)).comp polyFun_membVec
  have hin : PolyFun (fun a : RawF1In => (a, a.1.2)) :=
    polyFun_id.pair (polyFun_fst.comp polyFun_snd)
  exact (hin.comp (PolyFun.mapParam hf)).of_eq (fun a => rfl)

theorem polyFun_f1TagSet : PolyFun f1TagSet :=
  ((polyFun_nil.pair polyFun_f1Tags).comp
    (polyFun_dedupG (α := List ℕ) polyFun_listNatEq)).of_eq (fun a => rfl)

theorem polyFun_f1NewCol : PolyFun (fun z : RawF1In × List ℕ => f1NewCol z.1 z.2) := by
  have hmv : PolyFun (fun z : RawF1In × List ℕ => membVec (z.1.2, z.2)) :=
    (((polyFun_fst.comp polyFun_snd).pair polyFun_snd)).comp polyFun_membVec
  exact (((polyFun_fst.comp polyFun_f1TagSet).pair hmv).comp polyFun_rankIn).of_eq (fun z => rfl)

/-- **§5.1.3, row R4: the functor `F1` is a `RAM.PolyFun` of the table**, uniformly in `k`. -/
theorem polyFun_rawF1 : PolyFun rawF1 := by
  have hf : PolyFun (fun w : RawF1In × (List ℕ × ℕ) =>
      ((w.2.1, f1NewCol w.1 w.2.1) : List ℕ × ℕ)) :=
    (polyFun_snd.comp polyFun_fst).pair
      ((polyFun_fst.pair (polyFun_snd.comp polyFun_fst)).comp polyFun_f1NewCol)
  have hin : PolyFun (fun a : RawF1In => (a, a.1.2)) :=
    polyFun_id.pair (polyFun_fst.comp polyFun_snd)
  exact ((polyFun_fst.comp polyFun_fst).pair (hin.comp (PolyFun.mapParam hf))).of_eq
    (fun a => rfl)

theorem polyFun_getD0 : PolyFun (fun w : List ℕ × ℕ => w.1.getD w.2 0) :=
  ((polyFun_id.pair (polyFun_const 0)).comp polyFun_getD).of_eq (fun w => rfl)

theorem polyFun_applyIdx : PolyFun applyIdx :=
  (PolyFun.mapParam polyFun_getD0).of_eq (fun z => rfl)

/-- The equality type, with the list of index pairs read off the input: uniform in `k`. -/
theorem polyFun_rhoCodeI : PolyFun (fun w : List ℕ × List (List ℕ) => rhoCodeI w.2 w.1) := by
  have hidx : ∀ i : ℕ, PolyFun (fun w : List ℕ × List ℕ => w.1.getD (w.2.getD i 0) 0) := by
    intro i
    have h1 : PolyFun (fun w : List ℕ × List ℕ => w.2.getD i 0) :=
      (polyFun_snd.pair (polyFun_const i)).comp polyFun_getD0
    exact (polyFun_fst.pair h1).comp polyFun_getD0
  have hcond : PolyFun (fun w : List ℕ × List ℕ =>
      decide (w.1.getD (w.2.getD 0 0) 0 = w.1.getD (w.2.getD 1 0) 0)) :=
    ((hidx 0).pair (hidx 1)).comp polyFun_natEq
  have hf : PolyFun (fun w : List ℕ × List ℕ =>
      (if w.1.getD (w.2.getD 0 0) 0 = w.1.getD (w.2.getD 1 0) 0 then 1 else 0 : ℕ)) := by
    refine (PolyFun.ite hcond (polyFun_const 1) (polyFun_const 0)).of_eq (fun w => ?_)
    by_cases h : w.1.getD (w.2.getD 0 0) 0 = w.1.getD (w.2.getD 1 0) 0 <;> simp [h]
  exact (PolyFun.mapParam hf).of_eq (fun w => rfl)

theorem polyFun_rhoCode (k : ℕ) : PolyFun (rhoCode k) :=
  ((polyFun_id.pair (polyFun_const (pairIdx k))).comp polyFun_rhoCodeI).of_eq (fun t => rfl)

/-- **The tag of `F2` with the two index sets read off the input**: uniform in `k`. -/
theorem polyFun_f2TagAtI :
    PolyFun (fun z : IdxP × (RawWL × List ℕ) => f2TagAtI z.1 z.2.1 z.2.2) := by
  have hrho : PolyFun (fun z : IdxP × (RawWL × List ℕ) => rhoCodeI z.1.1 z.2.2) :=
    (((polyFun_snd.comp polyFun_snd).pair
      (polyFun_fst.comp polyFun_fst)).comp polyFun_rhoCodeI).of_eq (fun z => rfl)
  have hf : PolyFun (fun w : (IdxP × (RawWL × List ℕ)) × List ℕ =>
      tblGet (w.1.2.1.2, applyIdx (w.1.2.2, w.2))) :=
    ((polyFun_fst.comp polyFun_snd |>.comp polyFun_fst |>.comp polyFun_snd).pair
      (((polyFun_fst.comp polyFun_snd |>.comp polyFun_snd).pair polyFun_snd).comp
        polyFun_applyIdx)).comp polyFun_tblGet
  have htail : PolyFun (fun z : IdxP × (RawWL × List ℕ) =>
      z.1.2.map (fun σ => tblGet (z.2.1.2, applyIdx (z.2.2, σ)))) :=
    ((polyFun_id.pair (polyFun_fst.comp polyFun_snd)).comp (PolyFun.mapParam hf)).of_eq
      (fun z => rfl)
  exact ((hrho.pair htail).comp polyFun_append).of_eq (fun z => rfl)

theorem polyFun_f2TagAt (k : ℕ) : PolyFun (fun z : RawWL × List ℕ => f2TagAt k z.1 z.2) :=
  (((polyFun_const (idxOf k)).pair polyFun_id).comp polyFun_f2TagAtI).of_eq (fun z => rfl)

theorem polyFun_f2TagsI : PolyFun (fun z : IdxP × RawWL => f2TagsI z.1 z.2) := by
  have hf : PolyFun (fun w : (IdxP × RawWL) × (List ℕ × ℕ) =>
      f2TagAtI w.1.1 w.1.2 w.2.1) :=
    ((polyFun_fst.comp polyFun_fst).pair
      ((polyFun_fst.comp polyFun_snd).pair
        (polyFun_snd.comp polyFun_fst))).comp polyFun_f2TagAtI
  have hin : PolyFun (fun z : IdxP × RawWL => (z, z.2.2)) :=
    polyFun_id.pair (polyFun_snd.comp polyFun_snd)
  exact (hin.comp (PolyFun.mapParam hf)).of_eq (fun z => rfl)

theorem polyFun_f2Tags (k : ℕ) : PolyFun (f2Tags k) :=
  (((polyFun_const (idxOf k)).pair polyFun_id).comp polyFun_f2TagsI).of_eq (fun p => rfl)

theorem polyFun_f2TagSetI : PolyFun (fun z : IdxP × RawWL => f2TagSetI z.1 z.2) :=
  ((polyFun_nil.pair polyFun_f2TagsI).comp
    (polyFun_dedupG (α := List ℕ) polyFun_listNatEq)).of_eq (fun z => rfl)

theorem polyFun_f2TagSet (k : ℕ) : PolyFun (f2TagSet k) :=
  (((polyFun_const (idxOf k)).pair polyFun_id).comp polyFun_f2TagSetI).of_eq (fun p => rfl)

theorem polyFun_f2NewColI :
    PolyFun (fun z : IdxP × (RawWL × List ℕ) => f2NewColI z.1 z.2.1 z.2.2) :=
  ((((polyFun_fst.pair (polyFun_snd.comp polyFun_fst)).comp polyFun_f2TagSetI).pair
    polyFun_f2TagAtI).comp polyFun_rankIn).of_eq (fun z => rfl)

theorem polyFun_f2NewCol (k : ℕ) : PolyFun (fun z : RawWL × List ℕ => f2NewCol k z.1 z.2) :=
  (((polyFun_const (idxOf k)).pair polyFun_id).comp polyFun_f2NewColI).of_eq (fun z => rfl)

/-- **§5.1.5, row R5, uniformly in `k`: with the two index sets supplied as data, the functor
`F2` is a `RAM.PolyFun`.**  The arity enters only through those lists, which
`Workspace/Algo/FunctorsGuarded.lean` builds under the guard `k ≤ (log₂ n + 1)^{c₀}`. -/
theorem polyFun_rawF2I : PolyFun (fun z : IdxP × RawWL => rawF2I z.1 z.2) := by
  have hf : PolyFun (fun w : (IdxP × RawWL) × (List ℕ × ℕ) =>
      ((w.2.1, f2NewColI w.1.1 w.1.2 w.2.1) : List ℕ × ℕ)) :=
    (polyFun_snd.comp polyFun_fst).pair
      (((polyFun_fst.comp polyFun_fst).pair
        ((polyFun_fst.comp polyFun_snd).pair
          (polyFun_snd.comp polyFun_fst))).comp polyFun_f2NewColI)
  have hin : PolyFun (fun z : IdxP × RawWL => (z, z.2.2)) :=
    polyFun_id.pair (polyFun_snd.comp polyFun_snd)
  exact ((polyFun_snd.comp polyFun_fst).pair
    (hin.comp (PolyFun.mapParam hf))).of_eq (fun z => rfl)

/-- **§5.1.5, row R5: for each fixed `k`, the functor `F2` is a `RAM.PolyFun` of the table.** -/
theorem polyFun_rawF2 (k : ℕ) : PolyFun (rawF2 k) :=
  (((polyFun_const (idxOf k)).pair polyFun_id).comp polyFun_rawF2I).of_eq (fun p => rfl)

/-- **§5.2, uniformly in `k`: with the index sets of `F2` supplied as data, the pipeline
`F3 ∘ F2 ∘ F1` is a `RAM.PolyFun`.** -/
theorem polyFun_rawPipelineI : PolyFun (fun z : IdxP × RawF1In => rawPipelineI z.1 z.2) :=
  (((polyFun_fst.pair (polyFun_snd.comp polyFun_rawF1)).comp polyFun_rawF2I).comp
    polyFun_rawWLStable).of_eq (fun z => rfl)

/-- **§5.2: for each fixed `k`, the pipeline `F3 ∘ F2 ∘ F1` is a `RAM.PolyFun` of the table.** -/
theorem polyFun_rawPipeline (k : ℕ) : PolyFun (rawPipeline k) :=
  (((polyFun_const (idxOf k)).pair polyFun_id).comp polyFun_rawPipelineI).of_eq (fun a => rfl)

end Algo
