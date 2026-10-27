/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: the routines behind `Workspace/Algo/Transversal.lean`.
-/
import Workspace.Algo.Transversal

/-!
# Transversals, stabilizers and short generating sets as routines

`Workspace/Algo/Transversal.lean` proves the *mathematics* of three class-D rows of
`Workspace/Algo/DESIGN.md`, item 2.  This file turns each of them into a routine on raw data,
with its specification and its `RAM.PolyFun`:

* `Algo.rawRow` — row `i` of the table, a transversal of `G^{(i+1)}` in `G^{(i)}`
  (`Algo.rowPerms_transversal`, from `Algo.entries_transversal`);
* `Algo.rawStab` — the entries of the rows from `i` on, a generating list of the pointwise
  stabilizer of `{0, …, i−1}` (`Algo.decGroup_rawStab`, from `Algo.closure_entriesFrom`);
* `Algo.rawPointStab` — the pointwise stabilizer of an arbitrary list `Δ` of points, by
  conjugating the base so that `Δ` comes first (`Algo.decGroup_rawPointStab`, from
  `Algo.pointwiseStabilizer_map_conj`);
* `Algo.rawShorten` — any generating list replaced by one of at most `n²` elements
  (`Algo.decGroup_rawShorten`, `Algo.length_rawShorten_le`).

No axiom and no `sorry`.

Two remarks on the shape of the routines.

**Rows from `i` on are read with `Algo.rowsFrom`, not with `List.drop`.**  `List.drop` recurses
on a machine natural and has no `RAM.PolyFun` in the machine layer; a `filter` over
`List.zipIdx` has one, and `Algo.mem_rowsFrom` is all the two specifications need.

**The table is read, never rebuilt with a different base.**  `Algo.rawBuildTable` takes the
domain and the generators, and its base is always `0, 1, 2, …`; it does not take a base order.
So the pointwise stabilizer of an arbitrary `Δ` conjugates, as point 5 of the note on A4
session 3 of `Workspace/Algo/DESIGN.md` says: the generators are conjugated by the permutation
that lists `Δ` first, the stabilizer of an initial segment is read off the conjugated table, and
the answer is conjugated back.  Both conjugations are a `map` of `Algo.rawMul`.
-/

namespace Algo

open RAM RAM.Targets
open Equiv (Perm)

variable {n : ℕ}

/-! ## Reading a stored row

A stored row is an association list.  Under the shape invariant its keys are pairwise distinct,
so an entry of the stored list is exactly a filled position of the row. -/

/-- **With distinct keys, a stored pair is what the lookup returns.** -/
theorem lookup_eq_some_of_mem {β : Type*} :
    ∀ (l : List (ℕ × β)), (l.map Prod.fst).Nodup → ∀ {j : ℕ} {τ : β}, (j, τ) ∈ l →
      l.lookup j = some τ := by
  intro l
  induction l with
  | nil => intro _ j τ h; exact absurd h (List.not_mem_nil)
  | cons q t ih =>
      intro hnd j τ h
      obtain ⟨k, v⟩ := q
      rw [List.map_cons, List.nodup_cons] at hnd
      rcases List.mem_cons.1 h with h1 | h1
      · rw [Prod.mk.injEq] at h1
        obtain ⟨rfl, rfl⟩ := h1
        simp [List.lookup]
      · have hjk : j ≠ k := by
          intro hj
          exact hnd.1 (List.mem_map.2 ⟨(j, τ), h1, by rw [hj]⟩)
        have hbeq : (j == k) = false := by simpa using hjk
        simp only [List.lookup, hbeq, cond_false]
        exact ih hnd.2 h1

/-- **The set of entries of row `i` is the set of second components of the stored row.** -/
theorem entries_eq_row {M : MTable n} (h : Shape n M) (i : ℕ) :
    Entries (tableOf M) i = {τ | τ ∈ (M.getD i ([] : MRow n)).map Prod.snd} := by
  ext τ
  constructor
  · rintro ⟨j, hj⟩
    exact List.mem_map.2 ⟨(j, τ), mem_of_lookup_eq_some _ _ _ hj, rfl⟩
  · intro hτ
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hτ
    rcases getD_mem_or_nil M i with hmem | hnil
    · exact ⟨q.1, lookup_eq_some_of_mem _ (h.nodup _ hmem) (by simpa using hq)⟩
    · rw [hnil] at hq; exact absurd hq (List.not_mem_nil)

/-- Membership in a flattened list of rows, by the index of the row. -/
theorem mem_flatten_iff_getD {α : Type*} (x : α) :
    ∀ l : List (List α), x ∈ l.flatten ↔ ∃ j, x ∈ l.getD j [] := by
  intro l
  induction l with
  | nil =>
      constructor
      · intro h; exact absurd h (by simpa using List.not_mem_nil)
      · rintro ⟨j, hj⟩
        rw [List.getD_eq_default _ _ (by simp)] at hj
        exact absurd hj (List.not_mem_nil)
  | cons a t ih =>
      constructor
      · intro h
        rw [List.flatten_cons, List.mem_append] at h
        rcases h with h1 | h1
        · exact ⟨0, h1⟩
        · obtain ⟨j, hj⟩ := ih.1 h1
          exact ⟨j + 1, by simpa [List.getD_eq_getElem?_getD] using hj⟩
      · rintro ⟨j, hj⟩
        rw [List.flatten_cons, List.mem_append]
        cases j with
        | zero => exact Or.inl hj
        | succ j =>
            refine Or.inr (ih.2 ⟨j, ?_⟩)
            simpa [List.getD_eq_getElem?_getD] using hj

/-- **The set of all entries of a stored table is the set of its stored permutations.** -/
theorem allEntries_eq_entriesList {M : MTable n} (h : Shape n M) :
    AllEntries (tableOf M) = {τ | τ ∈ entriesList M} := by
  ext τ
  constructor
  · intro hτ
    exact allEntries_subset_entriesList hτ
  · intro hτ
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hτ
    obtain ⟨j, hj⟩ := (mem_flatten_iff_getD q M).1 hq
    have : q.2 ∈ Entries (tableOf M) j := by
      rw [entries_eq_row h]
      exact List.mem_map.2 ⟨q, hj, rfl⟩
    obtain ⟨m, hm⟩ := this
    exact ⟨j, m, hm⟩

/-! ## (a) Row `i` of the table

Proposition 11.1.6 and Theorem 11.1.9 let "`σ` range over right coset representatives" of
`G^{(i+1)}` in `G^{(i)}`.  Row `i` of a complete table is such a list of representatives, by
`Algo.entries_transversal`. -/

/-- **Row `i` of the table, as a list of permutations.**  The mathematical side of
`Algo.rawRow`. -/
def rowPerms (n : ℕ) (gens : List (Perm (Fin n))) (i : ℕ) : List (Perm (Fin n)) :=
  ((buildTable n gens).getD i ([] : MRow n)).map Prod.snd

/-- **Row `i` of the table is a transversal of `G^{(i+1)}` in `G^{(i)}`**: every element of
`G^{(i)}` is an entry of row `i` times an element of `G^{(i+1)}`, and the two factors are
determined by the product.  Paper: Prop. 11.1.6, Thm. 11.1.9 (§11.1). -/
theorem rowPerms_transversal (n : ℕ) (gens : List (Perm (Fin n))) {i k : ℕ}
    (h : i + (k + 1) = n) {σ : Perm (Fin n)} (hσ : σ ∈ chainStab (genGroup gens) i) :
    ∃! p : Perm (Fin n) × Perm (Fin n),
      p.1 ∈ rowPerms n gens i ∧ p.2 ∈ chainStab (genGroup gens) (i + 1) ∧ σ = p.1 * p.2 := by
  have hset : ∀ τ : Perm (Fin n),
      τ ∈ Entries (tableOf (buildTable n gens)) i ↔ τ ∈ rowPerms n gens i := by
    intro τ
    rw [entries_eq_row (shape_buildTable n gens) i]
    exact Iff.rfl
  obtain ⟨p, hp, huniq⟩ :=
    entries_transversal (isTable_buildTable n gens) (complete_buildTable n gens) h hσ
  refine ⟨p, ⟨(hset p.1).1 hp.1, hp.2.1, hp.2.2⟩, ?_⟩
  rintro q ⟨hq1, hq2, hq3⟩
  exact huniq q ⟨(hset q.1).2 hq1, hq2, hq3⟩

/-- **Row `i` of the table, as a routine.**  `dom` is a domain witness (any list of length
`n`), the second component is the generator list, and the last is the level `i`. -/
def rawRow (p : (List ℕ × List RawPerm) × ℕ) : List RawPerm :=
  ((rawBuildTable p.1).getD p.2 ([] : RawRow)).map Prod.snd

/-- **The routine computes row `i`.** -/
theorem rawRow_spec {n : ℕ} (dom : List ℕ) (hdom : dom.length = n)
    (gens : List (Perm (Fin n))) (i : ℕ) :
    rawRow ((dom, gens.map (encPerm n)), i) = (rowPerms n gens i).map (encPerm n) := by
  rw [rawRow, rawBuildTable_spec dom hdom gens, encMTable, rowPerms]
  show ((((buildTable n gens).map
    (fun row => row.map (fun q => (q.1, encPerm n q.2)))).getD i []).map Prod.snd) = _
  rw [getD_map_nil _ rfl, List.map_map, List.map_map]
  rfl

theorem polyFun_rawRow : PolyFun rawRow := by
  have hg : PolyFun (fun p : (List ℕ × List RawPerm) × ℕ =>
      (rawBuildTable p.1).getD p.2 ([] : RawRow)) :=
    (((polyFun_fst.comp polyFun_rawBuildTable).pair polyFun_snd).pair
      (polyFun_const ([] : RawRow))).comp polyFun_getD
  exact (hg.comp (PolyFun.map (polyFun_snd (α := ℕ) (β := RawPerm)))).of_eq (fun _ => rfl)

/-! ## (b) The rows from `i` on

The entries of the rows from `i` on generate the pointwise stabilizer of `{0, …, i−1}`
(`Algo.closure_entriesFrom`).  `List.drop` is not a `RAM.PolyFun`, so the rows from `i` on are
selected by a `filter` over `List.zipIdx`. -/

/-- **The entries of a list from the position `i` on.**  Extensionally `p.1.drop p.2`, but
written as a `filter` over `List.zipIdx`, which is a `RAM.PolyFun`. -/
def rowsFrom {α : Type*} (p : List α × ℕ) : List α :=
  (p.1.zipIdx.filter (fun q => decide (p.2 ≤ q.2))).map Prod.fst

theorem mem_rowsFrom {α : Type*} {l : List α} {i : ℕ} {x : α} :
    x ∈ rowsFrom (l, i) ↔ ∃ j, i ≤ j ∧ l[j]? = some x := by
  rw [rowsFrom]
  constructor
  · intro h
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 h
    obtain ⟨hq1, hq2⟩ := List.mem_filter.1 hq
    exact ⟨q.2, by simpa using hq2, List.mk_mem_zipIdx_iff_getElem?.1 (by simpa using hq1)⟩
  · rintro ⟨j, hij, hj⟩
    refine List.mem_map.2 ⟨(x, j), List.mem_filter.2 ⟨?_, by simpa using hij⟩, rfl⟩
    exact List.mk_mem_zipIdx_iff_getElem?.2 hj

theorem mem_flatten_rowsFrom {α : Type*} {M : List (List α)} {i : ℕ} {x : α} :
    x ∈ (rowsFrom (M, i)).flatten ↔ ∃ j, i ≤ j ∧ x ∈ M.getD j [] := by
  constructor
  · intro h
    obtain ⟨row, hrow, hx⟩ := List.mem_flatten.1 h
    obtain ⟨j, hij, hj⟩ := mem_rowsFrom.1 hrow
    refine ⟨j, hij, ?_⟩
    rwa [List.getD_eq_getElem?_getD, hj]
  · rintro ⟨j, hij, hx⟩
    by_cases hj : j < M.length
    · refine List.mem_flatten.2 ⟨M.getD j [], mem_rowsFrom.2 ⟨j, hij, ?_⟩, hx⟩
      rw [List.getD_eq_getElem _ _ hj, List.getElem?_eq_getElem hj]
    · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hj)] at hx
      exact absurd hx (List.not_mem_nil)

/-- **The rows from `i` on commute with a map on the rows.** -/
theorem rowsFrom_map {α β : Type*} (f : List α → List β) (M : List (List α)) (i : ℕ) :
    rowsFrom (M.map f, i) = (rowsFrom (M, i)).map f := by
  rw [rowsFrom, rowsFrom, List.zipIdx_map, List.filter_map, List.map_map, List.map_map]
  rfl

/-- **The entries of the rows from `i` on, as a list of permutations.**  The mathematical side
of `Algo.rawStab`. -/
def stabGens (n : ℕ) (gens : List (Perm (Fin n))) (i : ℕ) : List (Perm (Fin n)) :=
  entriesList (rowsFrom (buildTable n gens, i))

/-- **The entries of the rows from `i` on are exactly `Algo.EntriesFrom`.** -/
theorem entriesFrom_eq_stabGens (n : ℕ) (gens : List (Perm (Fin n))) (i : ℕ) :
    EntriesFrom (tableOf (buildTable n gens)) i = {τ | τ ∈ stabGens n gens i} := by
  ext τ
  rw [stabGens, entriesList]
  constructor
  · rintro ⟨j, hij, m, hm⟩
    have hmem : τ ∈ ((buildTable n gens).getD j ([] : MRow n)).map Prod.snd :=
      (Set.ext_iff.1 (entries_eq_row (shape_buildTable n gens) j) τ).1 ⟨m, hm⟩
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hmem
    exact List.mem_map.2 ⟨q, mem_flatten_rowsFrom.2 ⟨j, hij, hq⟩, rfl⟩
  · intro hτ
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hτ
    obtain ⟨j, hij, hj⟩ := mem_flatten_rowsFrom.1 hq
    have : q.2 ∈ Entries (tableOf (buildTable n gens)) j := by
      rw [entries_eq_row (shape_buildTable n gens) j]
      exact List.mem_map.2 ⟨q, hj, rfl⟩
    obtain ⟨m, hm⟩ := this
    exact ⟨j, hij, m, hm⟩

/-- **The entries of the rows from `i` on generate the pointwise stabilizer of
`{0, …, i−1}`.**  Paper: the generating set §13.1 line 08 needs, for an initial segment. -/
theorem closure_stabGens (n : ℕ) (gens : List (Perm (Fin n))) {i : ℕ} (hi : i ≤ n) :
    Subgroup.closure {g | g ∈ stabGens n gens i} = chainStab (genGroup gens) i := by
  rw [← entriesFrom_eq_stabGens]
  exact closure_entriesFrom (isTable_buildTable n gens) (complete_buildTable n gens)
    (k := n - i) (by omega)

/-- **The generators of the chain stabilizer `G^{(i)}`, as a routine.** -/
def rawStab (p : (List ℕ × List RawPerm) × ℕ) : List RawPerm :=
  rawEntries (rowsFrom (rawBuildTable p.1, p.2))

theorem rawStab_spec {n : ℕ} (dom : List ℕ) (hdom : dom.length = n)
    (gens : List (Perm (Fin n))) (i : ℕ) :
    rawStab ((dom, gens.map (encPerm n)), i) = (stabGens n gens i).map (encPerm n) := by
  rw [rawStab, rawBuildTable_spec dom hdom gens, encMTable, rowsFrom_map, ← encMTable,
    rawEntries_encMTable, stabGens]

/-- **The routine returns a generating list of `G^{(i)}`.** -/
theorem decGroup_rawStab {n : ℕ} (dom : List ℕ) (hdom : dom.length = n)
    (gens : List (Perm (Fin n))) {i : ℕ} (hi : i ≤ n) :
    decGroup n (rawStab ((dom, gens.map (encPerm n)), i)) = chainStab (genGroup gens) i := by
  rw [rawStab_spec dom hdom gens i, decGroup_map_encPerm, genGroup]
  exact closure_stabGens n gens hi

theorem polyFun_rowsFrom {α : Type*} [Enc α] : PolyFun (rowsFrom (α := α)) := by
  have hq : PolyFun (fun z : ℕ × (α × ℕ) => decide (z.1 ≤ z.2.2)) :=
    (polyFun_fst.pair ((polyFun_snd.comp polyFun_snd))).comp polyFun_le
  have hz : PolyFun (fun p : List α × ℕ => ((p.2, p.1.zipIdx) : ℕ × List (α × ℕ))) :=
    polyFun_snd.pair (polyFun_fst.comp polyFun_zipIdx)
  exact ((hz.comp (PolyFun.filterParam hq)).comp
    (PolyFun.map (polyFun_fst (α := α) (β := ℕ)))).of_eq (fun _ => rfl)

theorem polyFun_rawStab : PolyFun rawStab := by
  have hin : PolyFun (fun p : (List ℕ × List RawPerm) × ℕ =>
      ((rawBuildTable p.1, p.2) : RawTable × ℕ)) :=
    (polyFun_fst.comp polyFun_rawBuildTable).pair polyFun_snd
  exact ((hin.comp polyFun_rowsFrom).comp polyFun_rawEntries).of_eq (fun _ => rfl)

/-! ## (c) The pointwise stabilizer of an arbitrary list of points

The chain of `Workspace/Algo/Chain.lean` is tied to the base `0, 1, 2, …`, and
`Algo.rawBuildTable` does not take a base order, so `G_{(Δ)}` for a general `Δ` is not a group
of the chain.  The routine conjugates: it builds the permutation that lists `Δ` first, conjugates
the generators by it, reads the stabilizer of the initial segment `{0, …, |Δ|−1}` off the
conjugated table, and conjugates the answer back. -/

/-- **The base reordering**: the points of `Δ` first, then the rest of the domain, in order.
`p.1` is a domain witness and `p.2` is `Δ`. -/
def rawOrd (p : List ℕ × List ℕ) : RawPerm :=
  p.2 ++ (rawOne p.1).filter (fun x => if decide (x ∈ p.2) then false else true)

theorem mem_filter_rawOrd {dom Δ : List ℕ} {x : ℕ}
    (h : x ∈ (rawOne dom).filter (fun x => if decide (x ∈ Δ) then false else true)) :
    x < dom.length ∧ x ∉ Δ := by
  rw [List.mem_filter] at h
  obtain ⟨h1, h2⟩ := h
  rw [rawOne, List.mem_range] at h1
  refine ⟨h1, fun hx => ?_⟩
  rw [if_pos (by simpa using hx)] at h2
  exact absurd h2 (by simp)

/-- **The base reordering is a permutation of the domain.** -/
theorem wf_rawOrd {n : ℕ} {dom Δ : List ℕ} (hdom : dom.length = n) (hnd : Δ.Nodup)
    (hlt : ∀ x ∈ Δ, x < n) : RawPerm.WF n (rawOrd (dom, Δ)) := by
  have hmem : ∀ x ∈ rawOrd (dom, Δ), x < n := by
    intro x hx
    rcases List.mem_append.1 hx with h1 | h1
    · exact hlt x h1
    · have h2 : x < dom.length := (mem_filter_rawOrd h1).1
      omega
  have hnd' : (rawOrd (dom, Δ)).Nodup := by
    refine List.Nodup.append hnd ?_ ?_
    · exact List.Nodup.filter _ (by rw [rawOne]; exact List.nodup_range)
    · intro x hx hx'
      exact absurd hx (mem_filter_rawOrd hx').2
  have hle : (rawOrd (dom, Δ)).length ≤ n := length_le_of_nodup_lt hnd' hmem
  have hsub : List.range n ⊆ rawOrd (dom, Δ) := by
    intro x hx
    rw [List.mem_range] at hx
    by_cases hxΔ : x ∈ Δ
    · exact List.mem_append.2 (Or.inl hxΔ)
    · refine List.mem_append.2 (Or.inr (List.mem_filter.2 ⟨?_, ?_⟩))
      · rw [rawOne, List.mem_range, hdom]; exact hx
      · rw [if_neg (by simpa using hxΔ)]
  have hge : n ≤ (rawOrd (dom, Δ)).length := by
    have := (List.Nodup.subperm List.nodup_range hsub).length_le
    simpa using this
  exact ⟨le_antisymm hle hge, hmem, hnd'⟩

theorem length_le_of_nodup {n : ℕ} {Δ : List ℕ} (hnd : Δ.Nodup) (hlt : ∀ x ∈ Δ, x < n) :
    Δ.length ≤ n := length_le_of_nodup_lt hnd hlt

/-- **The base reordering maps the initial segment onto `Δ`.** -/
theorem image_decPerm_rawOrd {n : ℕ} {dom Δ : List ℕ} (hdom : dom.length = n) (hnd : Δ.Nodup)
    (hlt : ∀ x ∈ Δ, x < n) :
    (decPerm n (rawOrd (dom, Δ))) '' {x : Fin n | (x : ℕ) < Δ.length}
      = {x : Fin n | (x : ℕ) ∈ Δ} := by
  have hwf := wf_rawOrd hdom hnd hlt
  have hval : ∀ (x : Fin n) (hx : (x : ℕ) < Δ.length),
      ((decPerm n (rawOrd (dom, Δ))) x : ℕ) = Δ[(x : ℕ)] := by
    intro x hx
    rw [decPerm_val_of_wf hwf x]
    exact List.getElem_append_left hx
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : (x : ℕ) < Δ.length := hx
    show ((decPerm n (rawOrd (dom, Δ))) x : ℕ) ∈ Δ
    rw [hval x hx']
    exact List.getElem_mem hx'
  · intro hy
    have hy' : (y : ℕ) ∈ Δ := hy
    obtain ⟨j, hj, hjy⟩ := List.getElem_of_mem hy'
    have hjn : j < n := lt_of_lt_of_le hj (length_le_of_nodup hnd hlt)
    refine ⟨⟨j, hjn⟩, hj, ?_⟩
    exact Fin.ext (by rw [hval ⟨j, hjn⟩ hj, hjy])

/-- **The chain stabilizer is the pointwise stabilizer of an initial segment.**  The bridge
between `Algo.chainStab` and the paper's `G_{(Δ)}` (§2.2.1, Eq. (12)). -/
theorem chainStab_eq_pointwiseStabilizer (H : Subgroup (Perm (Fin n))) (i : ℕ) :
    chainStab H i = Babai.pointwiseStabilizer H {x : Fin n | (x : ℕ) < i} := by
  ext σ
  rw [mem_chainStab, Babai.mem_pointwiseStabilizer]
  exact ⟨fun h => ⟨h.1, fun x hx => h.2 x hx⟩, fun h => ⟨h.1, fun x hx => h.2 x hx⟩⟩

/-- **A generating list, conjugated.**  `p.1` is the conjugating permutation `π` as a raw
permutation, and the answer lists `π⁻¹ g π` for the generators `g`. -/
def rawConj (p : RawPerm × List RawPerm) : List RawPerm :=
  p.2.map (fun g => rawMul (rawInv p.1, rawMul (g, p.1)))

theorem rawConj_spec {n : ℕ} {l : RawPerm} (hwf : RawPerm.WF n l)
    (gens : List (Perm (Fin n))) :
    rawConj (l, gens.map (encPerm n))
      = (gens.map (fun g => (MulAut.conj (decPerm n l)⁻¹) g)).map (encPerm n) := by
  have hl : encPerm n (decPerm n l) = l := encPerm_decPerm hwf
  rw [rawConj, List.map_map, List.map_map]
  refine List.map_congr_left (fun g _ => ?_)
  show rawMul (rawInv l, rawMul (encPerm n g, l)) = _
  rw [← hl, rawInv_encPerm, rawMul_encPerm, rawMul_encPerm]
  congr 1
  show (decPerm n l)⁻¹ * (g * decPerm n l) = _
  simp [MulAut.conj, mul_assoc]

/-- **Conjugating a generating list conjugates the group it generates.** -/
theorem genGroup_map_conj (gens : List (Perm (Fin n))) (π : Perm (Fin n)) :
    genGroup (gens.map (fun g => (MulAut.conj π) g))
      = (genGroup gens).map (MulAut.conj π).toMonoidHom := by
  rw [genGroup, genGroup, MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · intro hx
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hx
    exact ⟨g, hg, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact List.mem_map.2 ⟨g, hg, rfl⟩

theorem map_conj_conj_inv (π : Perm (Fin n)) (S : Subgroup (Perm (Fin n))) :
    (S.map (MulAut.conj π⁻¹).toMonoidHom).map (MulAut.conj π).toMonoidHom = S := by
  rw [Subgroup.map_map]
  have : (MulAut.conj π).toMonoidHom.comp (MulAut.conj π⁻¹).toMonoidHom
      = MonoidHom.id (Perm (Fin n)) := by
    refine MonoidHom.ext (fun x => ?_)
    show π * (π⁻¹ * x * π⁻¹⁻¹) * π⁻¹ = x
    simp [mul_assoc]
  rw [this, Subgroup.map_id]

/-- **The pointwise stabilizer of an arbitrary list of points, as a routine.**  `p.2` is the
list `Δ`. -/
def rawPointStab (p : (List ℕ × List RawPerm) × List ℕ) : List RawPerm :=
  (rawStab ((p.1.1, rawConj (rawOrd (p.1.1, p.2), p.1.2)), p.2.length)).map
    (fun h => rawMul (rawOrd (p.1.1, p.2), rawMul (h, rawInv (rawOrd (p.1.1, p.2)))))

/-- **The routine returns a generating list of `G_{(Δ)}`.**  Paper: the pointwise stabilizer
`G_{(Δ)}` of §2.2.1, Eq. (12), used in §13.1 line 08. -/
theorem decGroup_rawPointStab {n : ℕ} (dom : List ℕ) (hdom : dom.length = n)
    (gens : List (Perm (Fin n))) (Δ : List ℕ) (hnd : Δ.Nodup) (hlt : ∀ x ∈ Δ, x < n) :
    decGroup n (rawPointStab ((dom, gens.map (encPerm n)), Δ))
      = Babai.pointwiseStabilizer (genGroup gens) {x : Fin n | (x : ℕ) ∈ Δ} := by
  have hwf : RawPerm.WF n (rawOrd (dom, Δ)) := wf_rawOrd hdom hnd hlt
  set ord := rawOrd (dom, Δ) with hord
  set ρ := decPerm n ord with hρ
  have hl : encPerm n ρ = ord := encPerm_decPerm hwf
  set cg : List (Perm (Fin n)) := gens.map (fun g => (MulAut.conj ρ⁻¹) g) with hcg
  -- the conjugated generators
  have h1 : rawConj (ord, gens.map (encPerm n)) = cg.map (encPerm n) := rawConj_spec hwf gens
  -- the stabilizer of the initial segment of the conjugated group
  have h2 : rawStab ((dom, cg.map (encPerm n)), Δ.length)
      = (stabGens n cg Δ.length).map (encPerm n) := rawStab_spec dom hdom cg Δ.length
  -- conjugating back
  have h3 : rawPointStab ((dom, gens.map (encPerm n)), Δ)
      = ((stabGens n cg Δ.length).map (fun h => (MulAut.conj ρ) h)).map (encPerm n) := by
    rw [rawPointStab, ← hord, h1, h2, List.map_map, List.map_map]
    refine List.map_congr_left (fun h _ => ?_)
    show rawMul (ord, rawMul (encPerm n h, rawInv ord)) = _
    rw [← hl, rawInv_encPerm, rawMul_encPerm, rawMul_encPerm]
    congr 1
  rw [h3, decGroup_map_encPerm, genGroup_map_conj, genGroup]
  rw [closure_stabGens n cg (length_le_of_nodup hnd hlt)]
  rw [chainStab_eq_pointwiseStabilizer]
  have himg : (ρ⁻¹ : Perm (Fin n)) '' {x : Fin n | (x : ℕ) ∈ Δ}
      = {x : Fin n | (x : ℕ) < Δ.length} := by
    rw [← image_decPerm_rawOrd hdom hnd hlt, ← hρ, ← Set.image_comp]
    simp [Function.comp_def]
  have hgen : genGroup cg = (genGroup gens).map (MulAut.conj ρ⁻¹).toMonoidHom := by
    rw [hcg, genGroup_map_conj]
  rw [hgen, ← himg, ← pointwiseStabilizer_map_conj, map_conj_conj_inv]

theorem polyFun_rawOrd : PolyFun rawOrd := by
  have hq : PolyFun (fun z : List ℕ × ℕ => if decide (z.2 ∈ z.1) then false else true) :=
    PolyFun.ite ((polyFun_snd.pair polyFun_fst).comp polyFun_natListMem)
      (polyFun_const false) (polyFun_const true)
  have hpair : PolyFun (fun p : List ℕ × List ℕ => ((p.2, rawOne p.1) : List ℕ × List ℕ)) :=
    polyFun_snd.pair (polyFun_fst.comp polyFun_rawOne)
  exact ((polyFun_snd.pair (hpair.comp (PolyFun.filterParam hq))).comp polyFun_append).of_eq
    (fun _ => rfl)

theorem polyFun_rawConj : PolyFun rawConj := by
  have hf : PolyFun (fun z : RawPerm × RawPerm => rawMul (rawInv z.1, rawMul (z.2, z.1))) :=
    ((polyFun_fst.comp polyFun_rawInv).pair
      ((polyFun_snd.pair polyFun_fst).comp polyFun_rawMul)).comp polyFun_rawMul
  exact (PolyFun.mapParam hf).of_eq (fun _ => rfl)

theorem polyFun_rawPointStab : PolyFun rawPointStab := by
  have hord : PolyFun (fun p : (List ℕ × List RawPerm) × List ℕ => rawOrd (p.1.1, p.2)) :=
    ((polyFun_fst.comp polyFun_fst).pair polyFun_snd).comp polyFun_rawOrd
  have hA : PolyFun (fun p : (List ℕ × List RawPerm) × List ℕ =>
      ((rawOrd (p.1.1, p.2), p.1.2) : RawPerm × List RawPerm)) :=
    hord.pair (polyFun_fst.comp polyFun_snd)
  have hB : PolyFun (fun p : (List ℕ × List RawPerm) × List ℕ =>
      rawConj (rawOrd (p.1.1, p.2), p.1.2)) := hA.comp polyFun_rawConj
  have hC : PolyFun (fun p : (List ℕ × List RawPerm) × List ℕ =>
      ((((p.1.1, rawConj (rawOrd (p.1.1, p.2), p.1.2)) : List ℕ × List RawPerm), p.2.length) :
        (List ℕ × List RawPerm) × ℕ)) :=
    ((polyFun_fst.comp polyFun_fst).pair hB).pair (polyFun_snd.comp polyFun_length)
  have hstab : PolyFun (fun p : (List ℕ × List RawPerm) × List ℕ =>
      rawStab ((p.1.1, rawConj (rawOrd (p.1.1, p.2), p.1.2)), p.2.length)) :=
    hC.comp polyFun_rawStab
  have hback : PolyFun (fun z : RawPerm × RawPerm =>
      rawMul (z.1, rawMul (z.2, rawInv z.1))) :=
    (polyFun_fst.pair ((polyFun_snd.pair
      (polyFun_fst.comp polyFun_rawInv)).comp polyFun_rawMul)).comp polyFun_rawMul
  exact ((hord.pair hstab).comp (PolyFun.mapParam hback)).of_eq (fun _ => rfl)

/-! ## (d) Shortening a generating list

Every step of Luks's framework outputs a generating list, and the lists must not grow along the
recursion.  The entries of a complete table generate the group and there are at most `n²` of
them. -/

/-- **A generating list of at most `n²` elements, as a routine.** -/
def rawShorten (p : List ℕ × List RawPerm) : List RawPerm := rawEntries (rawBuildTable p)

/-- **The shortened list generates the same group.** -/
theorem decGroup_rawShorten {n : ℕ} (dom : List ℕ) (hdom : dom.length = n)
    (gens : List (Perm (Fin n))) :
    decGroup n (rawShorten (dom, gens.map (encPerm n))) = genGroup gens := by
  rw [rawShorten, rawBuildTable_spec dom hdom gens, rawEntries_encMTable, decGroup_map_encPerm,
    genGroup, ← allEntries_eq_entriesList (shape_buildTable n gens)]
  exact closure_allEntries_buildTable n gens

/-- **The shortened list has at most `n²` elements.** -/
theorem length_rawShorten_le {n : ℕ} (dom : List ℕ) (hdom : dom.length = n)
    (gens : List (Perm (Fin n))) :
    (rawShorten (dom, gens.map (encPerm n))).length ≤ n * n :=
  length_rawEntries_rawBuildTable_le dom hdom gens

theorem polyFun_rawShorten : PolyFun rawShorten :=
  (polyFun_rawBuildTable.comp polyFun_rawEntries).of_eq (fun _ => rfl)

end Algo
