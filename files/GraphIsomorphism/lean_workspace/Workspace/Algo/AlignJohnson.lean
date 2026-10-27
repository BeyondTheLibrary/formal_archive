/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: Procedure Align (§14.1) — a Johnson scheme on a subset of `Γ` as raw
data, its well-formedness test on the unit-cost RAM, and its decoding.
-/
import Workspace.Algo.AlignStruct
import Workspace.Algo.DesignPoly
import Workspace.Machine.Pow

/-!
# §14.1, Procedure Align: a Johnson scheme as raw data

Procedure Align works with two shapes of structure on `Γ = [0, m)`: a colored partition
(`Algo.RawColPart`, `Workspace/Algo/AlignStruct.lean`) and a **Johnson scheme `J(m*, t*)`
carried by a subset `W ⊆ Γ`** (line 7 (B): *"identify `Δ_j` with `(Γ* choose t*)` where
`|Γ*| = m*`"*).  This file is the second shape.

## The raw encoding

`Algo.RawJohnson = List ℕ × ℕ × List (List ℕ)` is the triple `(W, t*, rows)`:

* `W` is the list of the points of `Γ` that carry the scheme, without repetition;
* `t*` is the parameter;
* `rows` holds one `t*`-subset of `Γ* = [0, m*)` per point of `W`, **in the same order**,
  each written as a strictly increasing list.

This is the encoding the DESIGN note "A10 session 1" §1 fixes, so that Sec. 9 (which
*produces* a Johnson scheme) and Sec. 14 (which *consumes* one) speak the same language.
The underlying set `Γ*` is not stored: it is read off the rows, `m* = |⋃ rows|`
(`Algo.rawJDeg`).  Well-formedness asks the entries of the rows to be below that number, so
`⋃ rows = [0, m*)` and the identification really is with the `t*`-subsets of `[0, m*)`.

**The point of risk R-A10-2.**  The test `Algo.rawJWFb` has to check that the rows are *all*
the `t*`-subsets of `Γ*`.  It does so by checking that they are distinct `t*`-subsets and
that there are `C(m*, t*)` of them.  That is polynomial in the **input** size, because the
rows are part of the input: `|rows| = |W| = C(m*, t*)`.  Phrased as "`W` is in bijection with
the `t*`-subsets of some set" the check would be exponential.

## Main definitions

* `Algo.RawJohnson`, `Algo.rawJDeg`, `Algo.rawJRow`, `Algo.rawJDiff` — the encoding and the
  three readers;
* `Algo.RawJohnson.WF` — well-formedness for the parameters `(m, m*, t*)`;
* `Algo.rawJWFb` — the test, a `RAM.PolyFun`;
* `Algo.rawJSet` — a row as a `t*`-subset of `Fin m*`;
* `Algo.decJohnson` — the decoding into `Babai.ColStruct (Fin m) ℕ`, the `S(Γ)`-set
  Procedure Align acts on.

## Main results

* `Algo.rawJWFb_iff` — the test decides well-formedness;
* `Algo.polyFun_rawJWFb` — **the running time**;
* `Algo.RawJohnson.WF.rowBinom_bijective` — well-formed rows are **exactly** the `t*`-subsets
  of `Fin m*`;
* `Algo.RawJohnson.WF.rawJDeg_eq` — and therefore `m*` is read correctly off the rows;
* `Algo.RawJohnson.WF.toBinom_bijective` — the identification of `W` with `(Γ* choose t*)`;
* `Algo.decJohnson_isJohnsonOn` — **the specification**: well-formed raw data decodes to a
  structure that `Babai.ColStruct.IsJohnsonOn` on `W` with the parameters `(m*, t*)`.

No axiom, no `sorry`.
-/

namespace Algo

open RAM RAM.Targets
open Equiv (Perm)

/-! ## The raw encoding -/

/-- §14.1, line 7 (B).  A **Johnson scheme on a subset of `Γ`, as raw data**: the list `W` of
the points that carry it, the parameter `t*`, and one `t*`-subset of `Γ* = [0, m*)` per point
of `W`, in the same order, each written as a strictly increasing list. -/
abbrev RawJohnson := List ℕ × ℕ × List (List ℕ)

/-- The size `m*` of the underlying set `Γ*`, read off the rows: the number of distinct
entries occurring in them. -/
def rawJDeg (r : RawJohnson) : ℕ := (dedupG (([] : List ℕ), r.2.2.flatten)).length

/-- The `t*`-subset of `Γ*` that a point of `W` is identified with, as a list.  A point
outside `W` gets the empty list. -/
def rawJRow (p : RawJohnson × ℕ) : List ℕ := ((p.1.1.zip p.1.2.2).lookup p.2).getD []

/-- The Johnson color of a pair of points of `W`, `|S ∖ T|` (Def. 3.2.13). -/
def rawJDiff (p : RawJohnson × (ℕ × ℕ)) : ℕ :=
  ((rawJRow (p.1, p.2.1)).filter (fun a => !decide (a ∈ rawJRow (p.1, p.2.2)))).length

/-! ## Well-formedness -/

/-- §14.1, line 7 (B) and Def. 3.2.9.  A raw Johnson scheme is **well formed** for the degree
`m` and the parameters `(m*, t*)` when it describes a Johnson scheme `J(m*, t*)` on a subset
of `Γ = [0, m)`.

The last two clauses — the rows are pairwise distinct and there are `C(m*, t*)` of them — are
what make the identification a *bijection* of `W` with `(Γ* choose t*)`, which is what
`Babai.ColStruct.IsJohnsonOn` asks for.  Injectivity alone would not do. -/
structure RawJohnson.WF (m ms ts : ℕ) (r : RawJohnson) : Prop where
  /-- `t* ≥ 2` (Def. 3.2.9). -/
  two_le : 2 ≤ ts
  /-- `m* ≥ 2t* + 1` (Def. 3.2.9). -/
  params : 2 * ts + 1 ≤ ms
  /-- The header carries `t*`. -/
  hdr : r.2.1 = ts
  /-- `W` lies in `Γ = [0, m)`. -/
  wLt : ∀ w ∈ r.1, w < m
  /-- `W` has no repetition. -/
  wNodup : r.1.Nodup
  /-- One row per point of `W`. -/
  rowsLen : r.2.2.length = r.1.length
  /-- Each row is strictly increasing. -/
  rowSorted : ∀ row ∈ r.2.2, row.SortedLT
  /-- Each row has `t*` entries. -/
  rowLen : ∀ row ∈ r.2.2, row.length = ts
  /-- Each row lies in `Γ* = [0, m*)`. -/
  rowLt : ∀ row ∈ r.2.2, ∀ a ∈ row, a < ms
  /-- The rows are pairwise distinct. -/
  rowsNodup : r.2.2.Nodup
  /-- There are `C(m*, t*)` of them. -/
  card : r.2.2.length = Nat.choose ms ts

/-! ## Counting: a list of distinct small naturals, as a subset of `Fin N` -/

/-- A list of distinct naturals below `N`, read as a subset of `Fin N`. -/
def rawJSet (N : ℕ) (l : List ℕ) : Finset (Fin N) :=
  Finset.univ.filter (fun i : Fin N => (i : ℕ) ∈ l)

@[simp] theorem mem_rawJSet {N : ℕ} {l : List ℕ} {i : Fin N} :
    i ∈ rawJSet N l ↔ (i : ℕ) ∈ l := by
  simp [rawJSet]

/-- **The counting lemma.**  A list without repetition whose entries are below `N` has as
many entries as the subset of `Fin N` it describes. -/
theorem card_rawJSet {N : ℕ} {l : List ℕ} (hnd : l.Nodup) (hlt : ∀ a ∈ l, a < N) :
    (rawJSet N l).card = l.length := by
  classical
  rw [← List.toFinset_card_of_nodup hnd]
  refine Finset.card_bij' (fun i _ => (i : ℕ)) (fun a ha => ⟨a, hlt a (List.mem_toFinset.1 ha)⟩)
    ?_ ?_ ?_ ?_
  · intro i hi
    exact List.mem_toFinset.2 (mem_rawJSet.1 hi)
  · intro a ha
    exact mem_rawJSet.2 (List.mem_toFinset.1 ha)
  · intro i _; rfl
  · intro a _; rfl

/-- A strictly increasing list is recovered from the subset of `Fin N` it describes. -/
theorem rawJSet_injOn {N : ℕ} {a b : List ℕ} (ha : a.SortedLT) (hb : b.SortedLT)
    (hal : ∀ x ∈ a, x < N) (hbl : ∀ x ∈ b, x < N) (h : rawJSet N a = rawJSet N b) :
    a = b := by
  refine ha.eq_of_mem_iff hb (fun x => ⟨fun hx => ?_, fun hx => ?_⟩)
  · have : (⟨x, hal x hx⟩ : Fin N) ∈ rawJSet N a := mem_rawJSet.2 hx
    rw [h] at this
    exact mem_rawJSet.1 this
  · have : (⟨x, hbl x hx⟩ : Fin N) ∈ rawJSet N b := mem_rawJSet.2 hx
    rw [← h] at this
    exact mem_rawJSet.1 this

/-! ## Reading a row -/

/-- The row of a point of `W` is the row at its position.  `Algo.rawJRow` looks the point up
in the association list `W.zip rows`, and this is what it finds. -/
theorem rawJ_lookup_zip : ∀ (W : List ℕ) (rows : List (List ℕ)) (i w : ℕ) (row : List ℕ),
    W.Nodup → W.length = rows.length → W[i]? = some w → rows[i]? = some row →
    (W.zip rows).lookup w = some row := by
  intro W
  induction W with
  | nil => intro rows i w row _ _ hw _; simp at hw
  | cons a W ih =>
    intro rows i w row hnd hlen hw hrow
    cases rows with
    | nil => simp at hlen
    | cons b rows =>
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hw hrow
        subst hw; subst hrow
        simp [List.lookup]
      | succ k =>
        simp only [List.getElem?_cons_succ] at hw hrow
        have hmem : w ∈ W := List.mem_of_getElem? hw
        have hne : ¬ (w = a) := by
          rintro rfl
          exact (List.nodup_cons.1 hnd).1 hmem
        have hb : (w == a) = false := beq_eq_false_iff_ne.2 hne
        simp only [List.zip_cons_cons, List.lookup, hb]
        exact ih rows k w row (List.nodup_cons.1 hnd).2 (by simpa using hlen) hw hrow

/-! ## Well-formed rows are exactly the `t*`-subsets of `Γ*` -/

namespace RawJohnson

variable {m ms ts : ℕ} {r : RawJohnson}

theorem WF.rowNodup (h : WF m ms ts r) {row : List ℕ} (hrow : row ∈ r.2.2) : row.Nodup :=
  (h.rowSorted row hrow).nodup

theorem WF.card_rowSet (h : WF m ms ts r) {row : List ℕ} (hrow : row ∈ r.2.2) :
    (rawJSet ms row).card = ts := by
  rw [card_rawJSet (h.rowNodup hrow) (h.rowLt row hrow)]
  exact h.rowLen row hrow

/-- The row at an index, as a `t*`-subset of `Γ* = [0, m*)`. -/
def WF.rowBinom (h : WF m ms ts r) (i : Fin r.2.2.length) : Babai.binom (Fin ms) ts :=
  ⟨rawJSet ms r.2.2[i], h.card_rowSet (List.getElem_mem i.isLt)⟩

/-- **The rows of well-formed raw data are exactly the `t*`-subsets of `Γ*`.**  They are
`C(m*, t*)` pairwise distinct `t*`-subsets of a set of size `m*`, so they are all of them.
This is the step that makes the identification a bijection, as
`Babai.ColStruct.IsJohnsonOn` asks. -/
theorem WF.rowBinom_bijective (h : WF m ms ts r) : Function.Bijective h.rowBinom := by
  classical
  have hcard : Fintype.card (Fin r.2.2.length) = Fintype.card (Babai.binom (Fin ms) ts) := by
    rw [Fintype.card_fin, h.card, Fintype.card_finset_len, Fintype.card_fin]
  refine (Fintype.bijective_iff_injective_and_card _).2 ⟨?_, hcard⟩
  intro i j hij
  have hset : rawJSet ms r.2.2[i] = rawJSet ms r.2.2[j] := congrArg Subtype.val hij
  have hrows : r.2.2[i] = r.2.2[j] :=
    rawJSet_injOn (h.rowSorted _ (List.getElem_mem i.isLt))
      (h.rowSorted _ (List.getElem_mem j.isLt))
      (h.rowLt _ (List.getElem_mem i.isLt)) (h.rowLt _ (List.getElem_mem j.isLt)) hset
  exact Fin.ext ((List.Nodup.getElem_inj_iff h.rowsNodup).1 hrows)

/-- Every point of `Γ*` occurs in some row: the rows are all the `t*`-subsets, and a
`t*`-subset containing a given point exists because `t* ≤ m*`. -/
theorem WF.mem_flatten (h : WF m ms ts r) {a : ℕ} (ha : a < ms) : a ∈ r.2.2.flatten := by
  classical
  have hts : 2 ≤ ts := h.two_le
  have hms : 2 * ts + 1 ≤ ms := h.params
  have h1 : ({⟨a, ha⟩} : Finset (Fin ms)).card ≤ ts := by
    rw [Finset.card_singleton]; omega
  have h2 : ts ≤ (Finset.univ : Finset (Fin ms)).card := by
    rw [Finset.card_univ, Fintype.card_fin]; omega
  obtain ⟨S, hSsub, -, hScard⟩ :=
    Finset.exists_subsuperset_card_eq (Finset.subset_univ _) h1 h2
  obtain ⟨i, hi⟩ := h.rowBinom_bijective.2 ⟨S, hScard⟩
  have hmemS : (⟨a, ha⟩ : Fin ms) ∈ rawJSet ms r.2.2[i] := by
    rw [show rawJSet ms r.2.2[i] = S from congrArg Subtype.val hi]
    exact hSsub (Finset.mem_singleton_self _)
  exact List.mem_flatten.2 ⟨r.2.2[i], List.getElem_mem i.isLt, mem_rawJSet.1 hmemS⟩

/-- **`m*` is read correctly off the rows.**  The entries of the rows are exactly the points
of `Γ* = [0, m*)`, so their number is `m*`. -/
theorem WF.rawJDeg_eq (h : WF m ms ts r) : rawJDeg r = ms := by
  classical
  rw [rawJDeg, length_dedupG_eq_card]
  have hset : r.2.2.flatten.toFinset = Finset.range ms := by
    ext a
    simp only [List.mem_toFinset, Finset.mem_range]
    constructor
    · intro hmem
      obtain ⟨row, hrow, ha⟩ := List.mem_flatten.1 hmem
      exact h.rowLt row hrow a ha
    · exact fun ha => h.mem_flatten ha
  rw [hset, Finset.card_range]

/-! ### The identification of `W` with `(Γ* choose t*)` -/

/-- The row of a point of `W` is the row at its position in `W`. -/
theorem WF.rawJRow_getElem (h : WF m ms ts r) {i : ℕ} (hi : i < r.1.length) :
    rawJRow (r, r.1[i]) = r.2.2[i]'(by rw [h.rowsLen]; exact hi) := by
  rw [rawJRow, rawJ_lookup_zip r.1 r.2.2 i r.1[i] _ h.wNodup (h.rowsLen.symm)
    (List.getElem?_eq_getElem hi) (List.getElem?_eq_getElem _)]
  rfl

theorem WF.rawJRow_mem (h : WF m ms ts r) {w : ℕ} (hw : w ∈ r.1) : rawJRow (r, w) ∈ r.2.2 := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hw
  rw [h.rawJRow_getElem hi]
  exact List.getElem_mem _

/-- The color class `W ⊆ Γ` that carries the scheme. -/
def carrier (m : ℕ) (r : RawJohnson) : Set (Fin m) := {u : Fin m | (u : ℕ) ∈ r.1}

/-- The identification of `W` with `(Γ* choose t*)`. -/
def WF.toBinom (h : WF m ms ts r) (u : carrier m r) : Babai.binom (Fin ms) ts :=
  ⟨rawJSet ms (rawJRow (r, (u : Fin m))), h.card_rowSet (h.rawJRow_mem u.2)⟩

theorem WF.toBinom_bijective (h : WF m ms ts r) : Function.Bijective h.toBinom := by
  classical
  have hW : Fintype.card (carrier m r) = r.1.length := by
    rw [show (carrier m r) = {u : Fin m | (u : ℕ) ∈ r.1} from rfl]
    rw [Fintype.card_subtype]
    exact card_rawJSet h.wNodup h.wLt
  have hcard : Fintype.card (carrier m r) = Fintype.card (Babai.binom (Fin ms) ts) := by
    rw [hW, ← h.rowsLen, h.card, Fintype.card_finset_len, Fintype.card_fin]
  refine (Fintype.bijective_iff_injective_and_card _).2 ⟨?_, hcard⟩
  rintro ⟨u, hu⟩ ⟨v, hv⟩ huv
  obtain ⟨i, hi, hiu⟩ := List.getElem_of_mem hu
  obtain ⟨j, hj, hjv⟩ := List.getElem_of_mem hv
  have hset : rawJSet ms (rawJRow (r, (u : ℕ))) = rawJSet ms (rawJRow (r, (v : ℕ))) :=
    congrArg Subtype.val huv
  rw [← hiu, ← hjv, h.rawJRow_getElem hi, h.rawJRow_getElem hj] at hset
  have hrows : r.2.2[i]'(by rw [h.rowsLen]; exact hi) = r.2.2[j]'(by rw [h.rowsLen]; exact hj) :=
    rawJSet_injOn (h.rowSorted _ (List.getElem_mem _)) (h.rowSorted _ (List.getElem_mem _))
      (h.rowLt _ (List.getElem_mem _)) (h.rowLt _ (List.getElem_mem _)) hset
  have : i = j := (List.Nodup.getElem_inj_iff h.rowsNodup).1 hrows
  subst this
  exact Subtype.ext (Fin.ext (by rw [← hiu, ← hjv]))

end RawJohnson

/-! ## The decoding -/

/-- §14.1, line 7 (B).  The structure on `Γ = [0, m)` that a raw Johnson scheme describes:
the underlying coloring marks the class `W` that carries the scheme, and the pair coloring is
the Johnson coloring `|S ∖ T|` of Def. 3.2.13 on `W`, and `0` outside. -/
def decJohnson (m : ℕ) (r : RawJohnson) : Babai.ColStruct (Fin m) ℕ where
  vcol u := if (u : ℕ) ∈ r.1 then 1 else 0
  ecol u v :=
    if (u : ℕ) ∈ r.1 then (if (v : ℕ) ∈ r.1 then rawJDiff (r, ((u : ℕ), (v : ℕ))) else 0) else 0

@[simp] theorem decJohnson_vcol (m : ℕ) (r : RawJohnson) (u : Fin m) :
    (decJohnson m r).vcol u = if (u : ℕ) ∈ r.1 then 1 else 0 := rfl

theorem decJohnson_ecol_mem (m : ℕ) (r : RawJohnson) {u v : Fin m} (hu : (u : ℕ) ∈ r.1)
    (hv : (v : ℕ) ∈ r.1) :
    (decJohnson m r).ecol u v = rawJDiff (r, ((u : ℕ), (v : ℕ))) := by
  simp [decJohnson, hu, hv]

/-- The Johnson color of a pair, as a cardinality: `|S ∖ T|`. -/
theorem rawJDiff_eq_card {ms : ℕ} {r : RawJohnson} {u v : ℕ}
    (hnd : (rawJRow (r, u)).Nodup) (hlt : ∀ a ∈ rawJRow (r, u), a < ms) :
    rawJDiff (r, (u, v)) =
      (rawJSet ms (rawJRow (r, u)) \ rawJSet ms (rawJRow (r, v))).card := by
  classical
  have hset : rawJSet ms (rawJRow (r, u)) \ rawJSet ms (rawJRow (r, v))
      = rawJSet ms ((rawJRow (r, u)).filter (fun a => !decide (a ∈ rawJRow (r, v)))) := by
    ext i
    simp [rawJSet, Finset.mem_sdiff, List.mem_filter]
  rw [hset, card_rawJSet (hnd.filter _) (fun a ha => hlt a (List.mem_of_mem_filter ha))]
  rfl

/-- §14.1, line 7 (B).  **The specification of the decoding**: well-formed raw data decodes to
a structure that is a Johnson scheme `J(m*, t*)` on `W`, in the sense of
`Babai.ColStruct.IsJohnsonOn`. -/
theorem decJohnson_isJohnsonOn {m ms ts : ℕ} {r : RawJohnson} (h : RawJohnson.WF m ms ts r) :
    (decJohnson m r).IsJohnsonOn (RawJohnson.carrier m r) ms ts := by
  refine ⟨h.two_le, h.params, ⟨Equiv.ofBijective _ h.toBinom_bijective, ?_⟩⟩
  intro S T
  rw [decJohnson_ecol_mem m r S.2 T.2,
    rawJDiff_eq_card (ms := ms) (h.rowNodup (h.rawJRow_mem S.2))
      (h.rowLt _ (h.rawJRow_mem S.2))]
  rfl

/-! ## The well-formedness test

Every routine of the algorithmic layer is total, so the caller has to be able to *check* that
the raw data describes a Johnson scheme.  The check is `Algo.rawJWFb`, and it is polynomial in
the input size because the rows are part of the input (risk R-A10-2). -/

/-- `RAM.dedupG` decides `List.Nodup` at any entry type.  `Algo.length_dedupG_eq_iff_nodup`
is the same statement for `ℕ`; the proof is the same. -/
theorem rawJ_dedup_nodup {α : Type*} [DecidableEq α] (l : List α) :
    (dedupG (([] : List α), l)).length = l.length ↔ l.Nodup := by
  obtain ⟨e, he, hnd, -, hmem⟩ := dedupG_struct l ([] : List α)
  have hde : dedupG (([] : List α), l) = e := by rw [dedupG, he]; simp
  have hsub : e ⊆ l := fun c hc => hmem c hc
  have hsubperm : List.Subperm e l := List.subperm_of_subset hnd hsub
  rw [hde]
  constructor
  · intro hlen
    exact (hsubperm.perm_of_length_le (le_of_eq hlen.symm)).nodup_iff.1 hnd
  · intro hl
    have hsub' : l ⊆ e := fun c hc => by
      have : c ∈ dedupG (([] : List α), l) := (mem_dedupG_nil l c).2 hc
      rwa [hde] at this
    exact le_antisymm hsubperm.length_le (List.subperm_of_subset hl hsub').length_le

/-- The rows are pairwise distinct. -/
def rawJNodupB (l : List (List ℕ)) : Bool :=
  decide ((dedupG (([] : List (List ℕ)), l)).length = l.length)

theorem rawJNodupB_iff (l : List (List ℕ)) : rawJNodupB l = true ↔ l.Nodup := by
  rw [rawJNodupB, decide_eq_true_eq]
  exact rawJ_dedup_nodup l

/-- Every entry of the list is below the bound. -/
def rawJAllLtB (p : ℕ × List ℕ) : Bool := (p.2.filter (fun a => decide (p.1 ≤ a))).isEmpty

theorem rawJAllLtB_iff (N : ℕ) (l : List ℕ) : rawJAllLtB (N, l) = true ↔ ∀ a ∈ l, a < N := by
  simp only [rawJAllLtB, List.isEmpty_iff, List.filter_eq_nil_iff, decide_eq_true_eq,
    Nat.not_le]

/-- The list is strictly increasing: every adjacent pair rises. -/
def rawJSortedB (l : List ℕ) : Bool :=
  ((l.zip l.tail).filter (fun q => decide (q.2 ≤ q.1))).isEmpty

theorem rawJSortedB_iff (l : List ℕ) : rawJSortedB l = true ↔ l.SortedLT := by
  rw [rawJSortedB, List.isEmpty_iff, List.filter_eq_nil_iff, List.sortedLT_iff_isChain]
  induction l with
  | nil => simp
  | cons a t ih =>
    cases t with
    | nil => simp
    | cons b t =>
      have hz : (a :: b :: t).zip (a :: b :: t).tail
          = (a, b) :: ((b :: t).zip (b :: t).tail) := rfl
      rw [hz, List.isChain_cons_cons, ← ih]
      simp [Nat.not_le]

/-- One row: strictly increasing, of length `t*`, inside `Γ* = [0, m*)`. -/
def rawJRowOkB (p : (ℕ × ℕ) × List ℕ) : Bool :=
  rawJSortedB p.2 && decide (p.2.length = p.1.2) && rawJAllLtB (p.1.1, p.2)

theorem rawJRowOkB_iff (ms ts : ℕ) (row : List ℕ) :
    rawJRowOkB ((ms, ts), row) = true ↔
      row.SortedLT ∧ row.length = ts ∧ ∀ a ∈ row, a < ms := by
  simp only [rawJRowOkB, Bool.and_eq_true, rawJSortedB_iff, decide_eq_true_eq,
    rawJAllLtB_iff, and_assoc]

/-- All the rows. -/
def rawJAllRowsOkB (p : (ℕ × ℕ) × List (List ℕ)) : Bool :=
  (p.2.filter (fun row => !rawJRowOkB (p.1, row))).isEmpty

theorem rawJAllRowsOkB_iff (ms ts : ℕ) (rows : List (List ℕ)) :
    rawJAllRowsOkB ((ms, ts), rows) = true ↔
      ∀ row ∈ rows, row.SortedLT ∧ row.length = ts ∧ ∀ a ∈ row, a < ms := by
  simp only [rawJAllRowsOkB, List.isEmpty_iff, List.filter_eq_nil_iff, Bool.not_eq_true',
    Bool.not_eq_false]
  exact forall₂_congr fun row _ => rawJRowOkB_iff ms ts row

/-- §14.1, line 7 (B).  **The well-formedness test for raw Johnson data.**  The parameters
`t*` and `m*` are read off the input: `t*` is the header and `m*` is `Algo.rawJDeg`, the
number of distinct entries of the rows. -/
def rawJWFb (p : ℕ × RawJohnson) : Bool :=
  decide (2 ≤ p.2.2.1) && decide (2 * p.2.2.1 + 1 ≤ rawJDeg p.2)
    && rawJAllLtB (p.1, p.2.1) && nodupB p.2.1
    && decide (p.2.2.2.length = p.2.1.length)
    && rawJAllRowsOkB ((rawJDeg p.2, p.2.2.1), p.2.2.2)
    && rawJNodupB p.2.2.2
    && decide (p.2.2.2.length = Nat.choose (rawJDeg p.2) p.2.2.1)

/-- **The test decides well-formedness.** -/
theorem rawJWFb_iff (m : ℕ) (r : RawJohnson) :
    rawJWFb (m, r) = true ↔ RawJohnson.WF m (rawJDeg r) r.2.1 r := by
  simp only [rawJWFb, Bool.and_eq_true, decide_eq_true_eq, rawJAllLtB_iff, nodupB_eq_true,
    rawJAllRowsOkB_iff, rawJNodupB_iff]
  constructor
  · rintro ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩
    exact ⟨h1, h2, rfl, h3, h4, h5, fun row hr => (h6 row hr).1,
      fun row hr => (h6 row hr).2.1, fun row hr => (h6 row hr).2.2, h7, h8⟩
  · intro h
    exact ⟨⟨⟨⟨⟨⟨⟨h.two_le, h.params⟩, h.wLt⟩, h.wNodup⟩, h.rowsLen⟩,
      fun row hr => ⟨h.rowSorted row hr, h.rowLen row hr, h.rowLt row hr⟩⟩,
      h.rowsNodup⟩, h.card⟩

/-! ## The running time -/

/-- The conjunction of two `RAM.PolyFun` tests. -/
theorem polyFun_rawJAnd {α : Type*} [Enc α] {f g : α → Bool} (hf : PolyFun f)
    (hg : PolyFun g) : PolyFun (fun a => f a && g a) :=
  (PolyFun.ite hf hg (polyFun_const false)).of_eq (fun a => by cases f a <;> simp)

/-- The negation of a `RAM.PolyFun` test. -/
theorem polyFun_rawJNot {α : Type*} [Enc α] {f : α → Bool} (hf : PolyFun f) :
    PolyFun (fun a => !f a) :=
  (PolyFun.ite hf (polyFun_const false) (polyFun_const true)).of_eq (fun a => by
    cases f a <;> simp)

theorem polyFun_rawJDeg : PolyFun rawJDeg := by
  have h1 : PolyFun (fun r : RawJohnson => r.2.2.flatten) :=
    (polyFun_snd.comp polyFun_snd).comp polyFun_flatten
  have h2 : PolyFun (fun l : List ℕ => (([] : List ℕ), l)) := polyFun_nil.pair polyFun_id
  have h3 : PolyFun (fun q : List ℕ × List ℕ => (dedupG q).length) :=
    (polyFun_dedupG polyFun_natEq).comp polyFun_length
  exact (h1.comp (h2.comp h3)).of_eq (fun _ => rfl)

theorem polyFun_rawJAllLtB : PolyFun rawJAllLtB :=
  (PolyFun.filterParam polyFun_le).comp polyFun_isEmpty

theorem polyFun_rawJSortedB : PolyFun rawJSortedB :=
  ((polyFun_id.pair polyFun_tail).comp polyFun_zip).comp
    ((PolyFun.filter polyFun_ge).comp polyFun_isEmpty)

theorem polyFun_rawJRowOkB : PolyFun rawJRowOkB := by
  have ha : PolyFun (fun p : (ℕ × ℕ) × List ℕ => rawJSortedB p.2) :=
    polyFun_snd.comp polyFun_rawJSortedB
  have hb : PolyFun (fun p : (ℕ × ℕ) × List ℕ => decide (p.2.length = p.1.2)) :=
    ((polyFun_snd.comp polyFun_length).pair (polyFun_fst.comp polyFun_snd)).comp polyFun_natEq
  have hc : PolyFun (fun p : (ℕ × ℕ) × List ℕ => rawJAllLtB (p.1.1, p.2)) :=
    ((polyFun_fst.comp polyFun_fst).pair polyFun_snd).comp polyFun_rawJAllLtB
  exact (polyFun_rawJAnd (polyFun_rawJAnd ha hb) hc).of_eq (fun _ => rfl)

theorem polyFun_rawJAllRowsOkB : PolyFun rawJAllRowsOkB :=
  (PolyFun.filterParam (polyFun_rawJNot polyFun_rawJRowOkB)).comp polyFun_isEmpty

theorem polyFun_rawJNodupB : PolyFun rawJNodupB := by
  have h2 : PolyFun (fun l : List (List ℕ) => (([] : List (List ℕ)), l)) :=
    polyFun_nil.pair polyFun_id
  have h3 : PolyFun (fun q : List (List ℕ) × List (List ℕ) => (dedupG q).length) :=
    (polyFun_dedupG polyFun_listNatEq).comp polyFun_length
  exact (((h2.comp h3).pair polyFun_length).comp polyFun_natEq).of_eq (fun _ => rfl)

/-- `m*` is at most the size of the input: it counts entries of the rows, and the rows are
part of the input.  This is the bound that makes the binomial coefficient `C(m*, t*)` of the
test a `RAM.PolyFun` (risk R-A10-2). -/
theorem rawJDeg_le_size (p : ℕ × RawJohnson) : rawJDeg p.2 ≤ Enc.size p := by
  obtain ⟨m, W, ts, rows⟩ := p
  have h1 : (dedupG (([] : List ℕ), rows.flatten)).length ≤ rows.flatten.length :=
    length_dedupG_le _
  have h2 : rows.flatten.length ≤ Enc.size rows := length_flatten_le_size _
  have h3 : Enc.size rows ≤ Enc.size ((ts, rows) : ℕ × List (List ℕ)) :=
    Combine.size_snd_le _ _
  have h4 : Enc.size ((ts, rows) : ℕ × List (List ℕ))
      ≤ Enc.size ((W, (ts, rows)) : RawJohnson) := Combine.size_snd_le _ _
  have h5 : Enc.size ((W, (ts, rows)) : RawJohnson)
      ≤ Enc.size ((m, (W, (ts, rows))) : ℕ × RawJohnson) := Combine.size_snd_le _ _
  show (dedupG (([] : List ℕ), rows.flatten)).length
      ≤ Enc.size ((m, (W, (ts, rows))) : ℕ × RawJohnson)
  exact le_trans h1 (le_trans h2 (le_trans h3 (le_trans h4 h5)))

/-- §14.1, line 7 (B).  **The well-formedness test runs in polynomial time.** -/
theorem polyFun_rawJWFb : PolyFun rawJWFb := by
  have hts : PolyFun (fun p : ℕ × RawJohnson => p.2.2.1) :=
    (polyFun_snd.comp polyFun_snd).comp polyFun_fst
  have hrows : PolyFun (fun p : ℕ × RawJohnson => p.2.2.2) :=
    (polyFun_snd.comp polyFun_snd).comp polyFun_snd
  have hW : PolyFun (fun p : ℕ × RawJohnson => p.2.1) := polyFun_snd.comp polyFun_fst
  have hms : PolyFun (fun p : ℕ × RawJohnson => rawJDeg p.2) := polyFun_snd.comp polyFun_rawJDeg
  have h1 : PolyFun (fun p : ℕ × RawJohnson => decide (2 ≤ p.2.2.1)) :=
    ((polyFun_const 2).pair hts).comp polyFun_le
  have h2 : PolyFun (fun p : ℕ × RawJohnson => decide (2 * p.2.2.1 + 1 ≤ rawJDeg p.2)) :=
    (((((polyFun_const 2).pair hts).comp polyFun_mul).pair (polyFun_const 1)).comp
      polyFun_add |>.pair hms).comp polyFun_le
  have h3 : PolyFun (fun p : ℕ × RawJohnson => rawJAllLtB (p.1, p.2.1)) :=
    (polyFun_fst.pair hW).comp polyFun_rawJAllLtB
  have h4 : PolyFun (fun p : ℕ × RawJohnson => nodupB p.2.1) := hW.comp polyFun_nodupB
  have h5 : PolyFun (fun p : ℕ × RawJohnson => decide (p.2.2.2.length = p.2.1.length)) :=
    ((hrows.comp polyFun_length).pair (hW.comp polyFun_length)).comp polyFun_natEq
  have h6 : PolyFun (fun p : ℕ × RawJohnson =>
      rawJAllRowsOkB ((rawJDeg p.2, p.2.2.1), p.2.2.2)) :=
    ((hms.pair hts).pair hrows).comp polyFun_rawJAllRowsOkB
  have h7 : PolyFun (fun p : ℕ × RawJohnson => rawJNodupB p.2.2.2) :=
    hrows.comp polyFun_rawJNodupB
  have hchoose : PolyFun (fun p : ℕ × RawJohnson => Nat.choose (rawJDeg p.2) p.2.2.1) :=
    PolyFun.choose hms hts rawJDeg_le_size polyBound_id
  have h8 : PolyFun (fun p : ℕ × RawJohnson =>
      decide (p.2.2.2.length = Nat.choose (rawJDeg p.2) p.2.2.1)) :=
    ((hrows.comp polyFun_length).pair hchoose).comp polyFun_natEq
  exact polyFun_rawJAnd (polyFun_rawJAnd (polyFun_rawJAnd (polyFun_rawJAnd
    (polyFun_rawJAnd (polyFun_rawJAnd (polyFun_rawJAnd h1 h2) h3) h4) h5) h6) h7) h8

end Algo
