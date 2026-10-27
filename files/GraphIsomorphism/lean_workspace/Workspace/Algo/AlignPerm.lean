/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: Procedure Align (§14.1), line 2 (i) — the aligning permutation `σ̄`
of two colored partitions of `Γ`, on the unit-cost RAM.
-/
import Workspace.Algo.AlignStruct
import Workspace.Algo.RefineRaw

/-!
# §14.1, Procedure Align, line 2 (i): the aligning permutation `σ̄`

> 2. Else, let
>    (i) `σ̄ ∈ Iso_{G^ϕ}(X(x), X(y))`          (: aligning in `Γ` :)

Session 1 of this package (`Algo/AlignStruct.lean`) decided **one half** of line 1 for
colored partitions: if the two key statistics differ then there is no isomorphism at all.
This file does the other half: if the statistics agree, an isomorphism is *computed*.

## The construction, without sorting

Every point `u` of `Γ = [0, m)` is given a **rank**

`cpRank P u = (key of u, index of the cell of u among the cells of that key, position of u
inside its cell)`,

where the key is the pair (color, size of the cell) of `Algo.cpKey`, the cell of a point is
the set of points with the same pair of labels, the cells of one key are ordered by their
least point, and the points of one cell are ordered as naturals.  Each of the three entries
is the length of one `List.filter`, so no sorting routine is needed.

The rank is injective (`Algo.cpRank_inj`), and its image is
`{(k, i, j) : i < (number of cells of key k), j < k.2}` (`Algo.cpRank_lt`,
`Algo.cpRank_surj`).  The number of points of key `k` is therefore
`(number of cells of key k) · k.2` (`Algo.count_key_eq`), so two colored partitions with the
same key statistic have the same number of cells of each key (`Algo.cpNumCells_eq`) and
hence the same set of ranks.  Matching equal ranks is the wanted `σ̄`
(`Algo.alignColPartPerm`).

## Main definitions

* `Algo.cpCellList`, `Algo.cpMin`, `Algo.cpPos`, `Algo.cpCellIdx`, `Algo.cpRank` — the rank;
* `Algo.cpMinList`, `Algo.cpNumCells` — the cells of one key and their number;
* `Algo.alignColPartPerm` — **the `σ̄` of line 2 (i)** in the colored-partition case.

## Main results

* `Algo.count_key_eq` — the points of one key are the cells of that key, `k.2` points each;
* `Algo.alignColPartPerm_wf`, `Algo.alignColPartPerm_check` — **the output is a permutation
  of `Γ` and the verifier `Algo.rawColPartIsoCheck` of session 1 accepts it**;
* `Algo.alignColPartPerm_colPartIso` — it is an isomorphism of the two colored partitions;
* `Algo.alignColPartTest_iff` — **line 1 is decided**: the test of session 1 answers `true`
  exactly when an isomorphism exists;
* `Algo.polyFun_alignColPartPerm` — **the running time**: `σ̄` is a `RAM.PolyFun`.

No axiom, no `sorry`.
-/

namespace Algo

open RAM RAM.Targets
open Equiv (Perm)

/-! ## Two list tools -/

theorem band_left {a b : Bool} (h : (a && b) = true) : a = true := by
  simp only [Bool.and_eq_true] at h; exact h.1

theorem band_right {a b : Bool} (h : (a && b) = true) : b = true := by
  simp only [Bool.and_eq_true] at h; exact h.2

theorem band_intro {a b : Bool} (ha : a = true) (hb : b = true) : (a && b) = true := by
  simp [ha, hb]


/-- A repetition-free list of naturals all of which are below its own length lists every
natural below that length.  (The pigeonhole principle in the shape this file uses.) -/
theorem perm_range_of_nodup {L : List ℕ} (hnd : L.Nodup) (hlt : ∀ a ∈ L, a < L.length) :
    L.Perm (List.range L.length) := by
  refine List.perm_of_nodup_nodup_toFinset_eq hnd List.nodup_range ?_
  refine Finset.eq_of_subset_of_card_le ?_ ?_
  · intro a ha
    simp only [List.mem_toFinset, List.mem_range] at ha ⊢
    exact hlt a ha
  · rw [List.toFinset_card_of_nodup hnd, List.toFinset_card_of_nodup List.nodup_range]
    simp

theorem mem_of_nodup_of_lt {L : List ℕ} (hnd : L.Nodup) (hlt : ∀ a ∈ L, a < L.length)
    {j : ℕ} (hj : j < L.length) : j ∈ L :=
  (perm_range_of_nodup hnd hlt).mem_iff.2 (List.mem_range.2 hj)

/-- The label at position `0` is the first entry. -/
theorem labAt_zero (l : List ℕ) : labAt l 0 = l.headD 0 := by cases l <;> rfl

/-- The first entry of a nonempty list is an entry of it. -/
theorem labAt_zero_mem {l : List ℕ} (h : l ≠ []) : labAt l 0 ∈ l := by
  cases l with
  | nil => exact absurd rfl h
  | cons a t => simp [labAt]

/-! ## The cell of a point, as a list -/

/-- The points of the cell of `u`, in increasing order. -/
def cpCellList (P : RawColPart) (u : ℕ) : List ℕ :=
  (cpDom P).filter (fun v => decide (cellOf P v = cellOf P u))

theorem cellSize_eq_length (P : RawColPart) (u : ℕ) :
    cellSize (P, u) = (cpCellList P u).length := rfl

theorem mem_cpCellList {P : RawColPart} {u w : ℕ} :
    w ∈ cpCellList P u ↔ w < P.1.length ∧ cellOf P w = cellOf P u := by
  rw [cpCellList, List.mem_filter, cpDom, List.mem_range, decide_eq_true_eq]

theorem nodup_cpCellList (P : RawColPart) (u : ℕ) : (cpCellList P u).Nodup :=
  List.Nodup.filter _ List.nodup_range

theorem pairwise_cpCellList (P : RawColPart) (u : ℕ) :
    (cpCellList P u).Pairwise (· < ·) :=
  List.Pairwise.filter _ List.pairwise_lt_range

theorem self_mem_cpCellList {P : RawColPart} {u : ℕ} (hu : u < P.1.length) :
    u ∈ cpCellList P u := mem_cpCellList.2 ⟨hu, rfl⟩

theorem cpCellList_congr {P : RawColPart} {u v : ℕ} (h : cellOf P u = cellOf P v) :
    cpCellList P u = cpCellList P v := by rw [cpCellList, cpCellList, h]

theorem cellSize_congr {P : RawColPart} {u v : ℕ} (h : cellOf P u = cellOf P v) :
    cellSize (P, u) = cellSize (P, v) := by
  rw [cellSize_eq_length, cellSize_eq_length, cpCellList_congr h]

/-- Points of one cell have one color. -/
theorem labAt_of_cellOf_eq {P : RawColPart} {u v : ℕ} (h : cellOf P u = cellOf P v) :
    labAt P.1 u = labAt P.1 v := by
  have h1 := congrArg Prod.fst h
  exact h1

theorem cpKey_congr {P : RawColPart} {u v : ℕ} (h : cellOf P u = cellOf P v) :
    cpKey (P, u) = cpKey (P, v) :=
  Prod.ext (labAt_of_cellOf_eq h) (cellSize_congr h)

/-- Points of one key have one color. -/
theorem labAt_of_cpKey_eq {P Q : RawColPart} {u v : ℕ} (h : cpKey (P, u) = cpKey (Q, v)) :
    labAt P.1 u = labAt Q.1 v := by
  have h1 := congrArg Prod.fst h
  exact h1

/-! ## The least point of a cell -/

/-- The least point of the cell of `u`. -/
def cpMin (P : RawColPart) (u : ℕ) : ℕ := labAt (cpCellList P u) 0

theorem cpMin_mem {P : RawColPart} {u : ℕ} (hu : u < P.1.length) :
    cpMin P u ∈ cpCellList P u := by
  refine labAt_zero_mem (fun hh => ?_)
  have h := self_mem_cpCellList hu
  rw [hh] at h
  exact absurd h (by simp)

theorem cpMin_le {P : RawColPart} {u w : ℕ} (hw : w ∈ cpCellList P u) : cpMin P u ≤ w := by
  rw [cpMin, labAt_zero]
  rcases hl : cpCellList P u with _ | ⟨b, t⟩
  · rw [hl] at hw; exact absurd hw (by simp)
  · have hp := pairwise_cpCellList P u
    rw [hl] at hp hw
    rw [List.headD_cons]
    rcases List.mem_cons.1 hw with rfl | hw'
    · exact le_rfl
    · exact (List.rel_of_pairwise_cons hp hw').le

theorem cellOf_cpMin {P : RawColPart} {u : ℕ} (hu : u < P.1.length) :
    cellOf P (cpMin P u) = cellOf P u := (mem_cpCellList.1 (cpMin_mem hu)).2

theorem cpMin_lt {P : RawColPart} {u : ℕ} (hu : u < P.1.length) :
    cpMin P u < P.1.length := (mem_cpCellList.1 (cpMin_mem hu)).1

theorem cpMin_congr {P : RawColPart} {u v : ℕ} (h : cellOf P u = cellOf P v) :
    cpMin P u = cpMin P v := by rw [cpMin, cpMin, cpCellList_congr h]

theorem cellOf_of_cpMin_eq {P : RawColPart} {u v : ℕ} (hu : u < P.1.length)
    (hv : v < P.1.length) (h : cpMin P u = cpMin P v) : cellOf P u = cellOf P v := by
  rw [← cellOf_cpMin hu, ← cellOf_cpMin hv, h]

theorem cpMin_idem {P : RawColPart} {u : ℕ} (hu : u < P.1.length) :
    cpMin P (cpMin P u) = cpMin P u := cpMin_congr (cellOf_cpMin hu)

/-! ## The position of a point inside its cell -/

/-- The number of points of the cell of `u` below `u`. -/
def cpPos (P : RawColPart) (u : ℕ) : ℕ :=
  ((cpDom P).filter (fun w => decide (cellOf P w = cellOf P u) && decide (w < u))).length

theorem cpPos_lt_cellSize {P : RawColPart} {u : ℕ} (hu : u < P.1.length) :
    cpPos P u < cellSize (P, u) := by
  rw [cpPos, cellSize_eq_length, cpCellList, ← List.countP_eq_length_filter,
    ← List.countP_eq_length_filter]
  refine Algo.countP_lt_countP (a := u) (cpDom P) (fun b _ hb => ?_) ?_ ?_ ?_
  · exact band_left hb
  · exact List.mem_range.2 hu
  · simp
  · simp

theorem cpPos_lt_of_lt {P : RawColPart} {u v : ℕ} (hv : v < P.1.length)
    (hcell : cellOf P u = cellOf P v) (huv : u < v) : cpPos P u < cpPos P v := by
  rw [cpPos, cpPos, ← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
  refine Algo.countP_lt_countP (a := u) (cpDom P) (fun b _ hb => ?_) ?_ ?_ ?_
  · have h1 := band_left hb
    have h2 := band_right hb
    rw [decide_eq_true_eq] at h1 h2
    exact band_intro (by rw [decide_eq_true_eq, h1, hcell])
      (by rw [decide_eq_true_eq]; omega)
  · exact List.mem_range.2 (lt_trans huv hv)
  · exact band_intro (by rw [decide_eq_true_eq]; exact hcell)
      (by rw [decide_eq_true_eq]; exact huv)
  · simp

theorem cpPos_inj {P : RawColPart} {u v : ℕ} (hu : u < P.1.length) (hv : v < P.1.length)
    (hcell : cellOf P u = cellOf P v) (h : cpPos P u = cpPos P v) : u = v := by
  rcases lt_trichotomy u v with hlt | heq | hgt
  · exact absurd h (Nat.ne_of_lt (cpPos_lt_of_lt hv hcell hlt))
  · exact heq
  · exact absurd h.symm (Nat.ne_of_lt (cpPos_lt_of_lt hu hcell.symm hgt))

/-- Every position below the size of a cell is taken. -/
theorem cpPos_surj {P : RawColPart} {u : ℕ} (hu : u < P.1.length) {j : ℕ}
    (hj : j < cellSize (P, u)) : ∃ v ∈ cpCellList P u, cpPos P v = j := by
  set L := (cpCellList P u).map (cpPos P) with hL
  have hlen : L.length = cellSize (P, u) := by
    rw [hL, List.length_map, cellSize_eq_length]
  have hnd : L.Nodup := by
    refine List.Nodup.map_on ?_ (nodup_cpCellList P u)
    intro a ha b hb hab
    obtain ⟨ha1, ha2⟩ := mem_cpCellList.1 ha
    obtain ⟨hb1, hb2⟩ := mem_cpCellList.1 hb
    exact cpPos_inj ha1 hb1 (ha2.trans hb2.symm) hab
  have hlt : ∀ a ∈ L, a < L.length := by
    intro a hA
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hA
    obtain ⟨hw1, hw2⟩ := mem_cpCellList.1 hw
    rw [hlen, ← cellSize_congr hw2]
    exact cpPos_lt_cellSize hw1
  have := mem_of_nodup_of_lt hnd hlt (by rw [hlen]; exact hj)
  obtain ⟨v, hv, hvj⟩ := List.mem_map.1 this
  exact ⟨v, hv, hvj⟩

/-! ## The cells of one key -/

/-- The least points of the cells of key `k`: one entry per cell. -/
def cpMinList (P : RawColPart) (k : ℕ × ℕ) : List ℕ :=
  (cpDom P).filter (fun w => decide (cpMin P w = w) && decide (cpKey (P, w) = k))

/-- The number of cells of key `k`. -/
def cpNumCells (P : RawColPart) (k : ℕ × ℕ) : ℕ := (cpMinList P k).length

theorem mem_cpMinList {P : RawColPart} {k : ℕ × ℕ} {w : ℕ} :
    w ∈ cpMinList P k ↔ w < P.1.length ∧ cpMin P w = w ∧ cpKey (P, w) = k := by
  rw [cpMinList, List.mem_filter, cpDom, List.mem_range, Bool.and_eq_true, decide_eq_true_eq,
    decide_eq_true_eq]

theorem nodup_cpMinList (P : RawColPart) (k : ℕ × ℕ) : (cpMinList P k).Nodup :=
  List.Nodup.filter _ List.nodup_range

/-- The index of the cell of `u` among the cells of its key: the number of cells of that key
whose least point comes first. -/
def cpCellIdx (P : RawColPart) (u : ℕ) : ℕ :=
  ((cpDom P).filter (fun w =>
    (decide (cpMin P w = w) && decide (cpKey (P, w) = cpKey (P, u))) &&
      decide (cpMin P w < cpMin P u))).length

theorem cpCellIdx_congr {P : RawColPart} {u v : ℕ} (h : cellOf P u = cellOf P v) :
    cpCellIdx P u = cpCellIdx P v := by
  rw [cpCellIdx, cpCellIdx, cpKey_congr h, cpMin_congr h]

theorem cpCellIdx_lt {P : RawColPart} {u : ℕ} (hu : u < P.1.length) :
    cpCellIdx P u < cpNumCells P (cpKey (P, u)) := by
  rw [cpCellIdx, cpNumCells, cpMinList, ← List.countP_eq_length_filter,
    ← List.countP_eq_length_filter]
  refine Algo.countP_lt_countP (a := cpMin P u) (cpDom P) (fun b _ hb => ?_) ?_ ?_ ?_
  · exact band_left hb
  · exact List.mem_range.2 (cpMin_lt hu)
  · refine band_intro (by rw [decide_eq_true_eq]; exact cpMin_idem hu) ?_
    rw [decide_eq_true_eq]; exact cpKey_congr (cellOf_cpMin hu)
  · simp [cpMin_idem hu]

theorem cpCellIdx_lt_of_min_lt {P : RawColPart} {u v : ℕ} (hu : u < P.1.length)
    (hkey : cpKey (P, u) = cpKey (P, v)) (h : cpMin P u < cpMin P v) :
    cpCellIdx P u < cpCellIdx P v := by
  rw [cpCellIdx, cpCellIdx, ← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
  refine Algo.countP_lt_countP (a := cpMin P u) (cpDom P) (fun b _ hb => ?_) ?_ ?_ ?_
  · have h1 := band_left hb
    have h2 := band_right hb
    have h3 := band_left h1
    have h4 := band_right h1
    rw [decide_eq_true_eq] at h2 h4
    refine band_intro (band_intro h3 ?_) ?_
    · rw [decide_eq_true_eq, h4, hkey]
    · rw [decide_eq_true_eq]; omega
  · exact List.mem_range.2 (cpMin_lt hu)
  · refine band_intro (band_intro ?_ ?_) ?_
    · rw [decide_eq_true_eq]; exact cpMin_idem hu
    · rw [decide_eq_true_eq]; exact (cpKey_congr (cellOf_cpMin hu)).trans hkey
    · rw [decide_eq_true_eq, cpMin_idem hu]; exact h
  · simp [cpMin_idem hu]

/-- Two points of the same key whose cells have the same index are in one cell. -/
theorem cpCellIdx_inj {P : RawColPart} {u v : ℕ} (hu : u < P.1.length) (hv : v < P.1.length)
    (hkey : cpKey (P, u) = cpKey (P, v)) (h : cpCellIdx P u = cpCellIdx P v) :
    cellOf P u = cellOf P v := by
  rcases lt_trichotomy (cpMin P u) (cpMin P v) with hlt | heq | hgt
  · exact absurd h (Nat.ne_of_lt (cpCellIdx_lt_of_min_lt hu hkey hlt))
  · exact cellOf_of_cpMin_eq hu hv heq
  · exact absurd h.symm (Nat.ne_of_lt (cpCellIdx_lt_of_min_lt hv hkey.symm hgt))

/-- Every cell index below the number of cells of a key is taken. -/
theorem cpCellIdx_surj {P : RawColPart} {k : ℕ × ℕ} {i : ℕ} (hi : i < cpNumCells P k) :
    ∃ w ∈ cpMinList P k, cpCellIdx P w = i := by
  set L := (cpMinList P k).map (cpCellIdx P) with hL
  have hlen : L.length = cpNumCells P k := by rw [hL, List.length_map, cpNumCells]
  have hnd : L.Nodup := by
    refine List.Nodup.map_on ?_ (nodup_cpMinList P k)
    intro a ha b hb hab
    obtain ⟨ha1, ha2, ha3⟩ := mem_cpMinList.1 ha
    obtain ⟨hb1, hb2, hb3⟩ := mem_cpMinList.1 hb
    have hc := cpCellIdx_inj ha1 hb1 (ha3.trans hb3.symm) hab
    rw [← ha2, ← hb2, cpMin_congr hc]
  have hlt : ∀ a ∈ L, a < L.length := by
    intro a hA
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hA
    obtain ⟨hw1, _, hw3⟩ := mem_cpMinList.1 hw
    rw [hlen, ← hw3]
    exact cpCellIdx_lt hw1
  have := mem_of_nodup_of_lt hnd hlt (by rw [hlen]; exact hi)
  obtain ⟨w, hw, hwi⟩ := List.mem_map.1 this
  exact ⟨w, hw, hwi⟩

/-! ## The rank of a point -/

/-- §14.1, line 2 (i).  The **rank** of a point of a colored partition: its key, the index of
its cell among the cells of that key, and its position inside its cell.  The rank is
injective and its image depends only on the key statistic, which is what makes it a canonical
naming of the points. -/
def cpRank (P : RawColPart) (u : ℕ) : (ℕ × ℕ) × ℕ × ℕ :=
  (cpKey (P, u), cpCellIdx P u, cpPos P u)

/-- The three entries of the rank, read off. -/
theorem cpRank_eq_iff {P Q : RawColPart} {u v : ℕ} :
    cpRank P u = cpRank Q v ↔
      (cpKey (P, u) = cpKey (Q, v) ∧ cpCellIdx P u = cpCellIdx Q v ∧
        cpPos P u = cpPos Q v) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · have h1 := congrArg Prod.fst h; exact h1
    · have h1 := congrArg (fun z => z.2.1) h; exact h1
    · have h1 := congrArg (fun z => z.2.2) h; exact h1
  · rintro ⟨h1, h2, h3⟩
    rw [cpRank, cpRank, h1, h2, h3]

theorem cpRank_inj {P : RawColPart} {u v : ℕ} (hu : u < P.1.length) (hv : v < P.1.length)
    (h : cpRank P u = cpRank P v) : u = v := by
  obtain ⟨hk, hi, hp⟩ := cpRank_eq_iff.1 h
  exact cpPos_inj hu hv (cpCellIdx_inj hu hv hk hi) hp

theorem cpRank_lt {P : RawColPart} {u : ℕ} (hu : u < P.1.length) :
    cpCellIdx P u < cpNumCells P (cpKey (P, u)) ∧ cpPos P u < (cpKey (P, u)).2 :=
  ⟨cpCellIdx_lt hu, cpPos_lt_cellSize hu⟩

/-- Every triple below the bounds is the rank of a point. -/
theorem cpRank_surj {P : RawColPart} {k : ℕ × ℕ} {i j : ℕ} (hi : i < cpNumCells P k)
    (hj : j < k.2) : ∃ u, u < P.1.length ∧ cpRank P u = (k, i, j) := by
  obtain ⟨w, hw, hwi⟩ := cpCellIdx_surj hi
  obtain ⟨hw1, _, hw3⟩ := mem_cpMinList.1 hw
  have hsize : cellSize (P, w) = k.2 := by rw [← hw3]; rfl
  obtain ⟨v, hv, hvj⟩ := cpPos_surj hw1 (by rw [hsize]; exact hj)
  obtain ⟨hv1, hv2⟩ := mem_cpCellList.1 hv
  refine ⟨v, hv1, ?_⟩
  rw [cpRank, hvj, cpKey_congr hv2, hw3, cpCellIdx_congr hv2, hwi]

/-! ## The points of one key

The points of one key are its cells, `k.2` points each.  This is the step that turns the
equality of the two key statistics (the test of line 1) into the equality of the two sets of
ranks. -/

/-- The points of key `k`. -/
def cpKeyList (P : RawColPart) (k : ℕ × ℕ) : List ℕ :=
  (cpDom P).filter (fun w => decide (cpKey (P, w) = k))

theorem mem_cpKeyList {P : RawColPart} {k : ℕ × ℕ} {w : ℕ} :
    w ∈ cpKeyList P k ↔ w < P.1.length ∧ cpKey (P, w) = k := by
  rw [cpKeyList, List.mem_filter, cpDom, List.mem_range, decide_eq_true_eq]

theorem nodup_cpKeyList (P : RawColPart) (k : ℕ × ℕ) : (cpKeyList P k).Nodup :=
  List.Nodup.filter _ List.nodup_range

/-- **The points of one key are its cells, `k.2` points each.** -/
theorem count_key_eq (P : RawColPart) (k : ℕ × ℕ) :
    (cpKeyList P k).length = cpNumCells P k * k.2 := by
  set N := cpNumCells P k * k.2 with hN
  set f : ℕ → ℕ := fun w => cpCellIdx P w * k.2 + cpPos P w with hf
  set L := (cpKeyList P k).map f with hL
  have hlen : L.length = (cpKeyList P k).length := by rw [hL, List.length_map]
  -- the values are below `N`
  have hval : ∀ a ∈ L, a < N := by
    intro a ha
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 ha
    obtain ⟨hw1, hw2⟩ := mem_cpKeyList.1 hw
    have h1 : cpCellIdx P w < cpNumCells P k := by rw [← hw2]; exact cpCellIdx_lt hw1
    have h2 : cpPos P w < k.2 := by rw [← hw2]; exact cpPos_lt_cellSize hw1
    have : cpCellIdx P w * k.2 + cpPos P w < cpCellIdx P w * k.2 + k.2 := by omega
    refine lt_of_lt_of_le this ?_
    rw [hN, ← Nat.succ_mul]
    exact Nat.mul_le_mul_right _ h1
  -- the values are distinct
  have hnd : L.Nodup := by
    refine List.Nodup.map_on ?_ (nodup_cpKeyList P k)
    intro a ha b hb hab
    obtain ⟨ha1, ha2⟩ := mem_cpKeyList.1 ha
    obtain ⟨hb1, hb2⟩ := mem_cpKeyList.1 hb
    have hpa : cpPos P a < k.2 := by rw [← ha2]; exact cpPos_lt_cellSize ha1
    have hpb : cpPos P b < k.2 := by rw [← hb2]; exact cpPos_lt_cellSize hb1
    have hidx : cpCellIdx P a = cpCellIdx P b := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with h | h
      · have h1 : cpCellIdx P a * k.2 + cpPos P a < (cpCellIdx P a + 1) * k.2 := by
          rw [Nat.succ_mul]; omega
        have h2 : (cpCellIdx P a + 1) * k.2 ≤ cpCellIdx P b * k.2 :=
          Nat.mul_le_mul_right _ h
        rw [hf] at hab; simp only at hab; omega
      · have h1 : cpCellIdx P b * k.2 + cpPos P b < (cpCellIdx P b + 1) * k.2 := by
          rw [Nat.succ_mul]; omega
        have h2 : (cpCellIdx P b + 1) * k.2 ≤ cpCellIdx P a * k.2 :=
          Nat.mul_le_mul_right _ h
        rw [hf] at hab; simp only at hab; omega
    have hpos : cpPos P a = cpPos P b := by rw [hf] at hab; simp only [hidx] at hab; omega
    exact cpPos_inj ha1 hb1 (cpCellIdx_inj ha1 hb1 (ha2.trans hb2.symm) hidx) hpos
  -- every value below `N` occurs
  have hcov : ∀ t < N, t ∈ L := by
    intro t ht
    rw [hN] at ht
    have hk2 : 0 < k.2 := by
      rcases Nat.eq_zero_or_pos k.2 with h0 | h0
      · rw [h0, Nat.mul_zero] at ht; exact absurd ht (Nat.not_lt_zero _)
      · exact h0
    have hi : t / k.2 < cpNumCells P k := by
      rw [Nat.div_lt_iff_lt_mul hk2]
      omega
    obtain ⟨u, hu, hru⟩ := cpRank_surj (P := P) (k := k) hi (Nat.mod_lt _ hk2)
    have hku : cpKey (P, u) = k := by
      have h1 := congrArg Prod.fst hru; exact h1
    have hiu : cpCellIdx P u = t / k.2 := by
      have h1 := congrArg (fun z => z.2.1) hru; exact h1
    have hpu : cpPos P u = t % k.2 := by
      have h1 := congrArg (fun z => z.2.2) hru; exact h1
    refine List.mem_map.2 ⟨u, mem_cpKeyList.2 ⟨hu, hku⟩, ?_⟩
    rw [hf]
    simp only [hiu, hpu]
    exact Nat.div_add_mod' t k.2
  have h1 : L.length ≤ N := by
    have hsub : L ⊆ List.range N := fun a ha => List.mem_range.2 (hval a ha)
    have := (List.Nodup.subperm hnd hsub).length_le
    simpa using this
  have h2 : N ≤ L.length := by
    have hsub : List.range N ⊆ L := fun a ha => hcov a (List.mem_range.1 ha)
    have := (List.Nodup.subperm List.nodup_range hsub).length_le
    simpa using this
  omega

/-! ## From equal statistics to equal ranks -/

theorem count_colPartStat (P : RawColPart) (k : ℕ × ℕ) :
    (colPartStat P).count k = (cpKeyList P k).length := by
  rw [colPartStat, List.count_eq_countP, List.countP_map, cpKeyList,
    ← List.countP_eq_length_filter]
  exact List.countP_congr (fun a _ => by simp)

/-- A key of a point has a positive second entry: a point lies in its own cell. -/
theorem cpKey_snd_pos {P : RawColPart} {u : ℕ} (hu : u < P.1.length) : 0 < (cpKey (P, u)).2 :=
  Nat.lt_of_le_of_lt (Nat.zero_le _) (cpPos_lt_cellSize hu)

theorem cpNumCells_eq_zero {P : RawColPart} {k : ℕ × ℕ} (hk : k.2 = 0) :
    cpNumCells P k = 0 := by
  rw [cpNumCells, List.length_eq_zero_iff, List.eq_nil_iff_forall_not_mem]
  intro w hw
  obtain ⟨hw1, _, hw3⟩ := mem_cpMinList.1 hw
  have := cpKey_snd_pos hw1
  rw [hw3, hk] at this
  exact Nat.lt_irrefl 0 this

/-- **Equal key statistics give equally many cells of each key.** -/
theorem cpNumCells_eq {P Q : RawColPart} (h : (colPartStat P).Perm (colPartStat Q))
    (k : ℕ × ℕ) : cpNumCells P k = cpNumCells Q k := by
  rcases Nat.eq_zero_or_pos k.2 with hk | hk
  · rw [cpNumCells_eq_zero hk, cpNumCells_eq_zero hk]
  · have hc : (cpKeyList P k).length = (cpKeyList Q k).length := by
      rw [← count_colPartStat, ← count_colPartStat]
      exact h.count_eq k
    rw [count_key_eq, count_key_eq] at hc
    exact Nat.eq_of_mul_eq_mul_right hk hc

/-! ## The aligning permutation -/

/-- The point of `Q` with the same rank as the point `u` of `P`. -/
def cpMatch (p : RawColPart × RawColPart) (u : ℕ) : ℕ :=
  labAt ((cpDom p.2).filter (fun v => decide (cpRank p.2 v = cpRank p.1 u))) 0

/-- §14.1, **line 2 (i)**, the colored-partition case: the aligning permutation `σ̄`.  Each
point of `X(x)` is sent to the point of `X(y)` with the same rank. -/
def alignColPartPerm (p : RawColPart × RawColPart) : RawPerm :=
  (cpDom p.1).map (cpMatch p)

section Spec

variable {m : ℕ} {P Q : RawColPart}

/-- The rank of a point of `P` is the rank of a point of `Q`, once the statistics agree. -/
theorem cpRank_attained (hP : P.1.length = m) (hQ : Q.1.length = m)
    (hstat : (colPartStat P).Perm (colPartStat Q)) {u : ℕ} (hu : u < m) :
    ∃ v, v < m ∧ cpRank Q v = cpRank P u := by
  have hu' : u < P.1.length := by rw [hP]; exact hu
  obtain ⟨hi, hj⟩ := cpRank_lt hu'
  rw [cpNumCells_eq hstat] at hi
  obtain ⟨v, hv, hrv⟩ := cpRank_surj (P := Q) hi hj
  exact ⟨v, by rw [← hQ]; exact hv, by rw [hrv, cpRank]⟩

theorem cpMatch_spec (hP : P.1.length = m) (hQ : Q.1.length = m)
    (hstat : (colPartStat P).Perm (colPartStat Q)) {u : ℕ} (hu : u < m) :
    cpMatch (P, Q) u < m ∧ cpRank Q (cpMatch (P, Q) u) = cpRank P u := by
  obtain ⟨v, hv, hrv⟩ := cpRank_attained hP hQ hstat hu
  set S := (cpDom Q).filter (fun w => decide (cpRank Q w = cpRank P u)) with hS
  have hmem : ∀ w ∈ S, w < m ∧ cpRank Q w = cpRank P u := by
    intro w hw
    rw [hS, List.mem_filter, cpDom, List.mem_range, hQ, decide_eq_true_eq] at hw
    exact hw
  have hvS : v ∈ S := by
    rw [hS, List.mem_filter, cpDom, List.mem_range, hQ, decide_eq_true_eq]
    exact ⟨hv, hrv⟩
  have hhead : cpMatch (P, Q) u ∈ S := by
    have hSne : S ≠ [] := fun hh => by rw [hh] at hvS; exact absurd hvS (by simp)
    have := labAt_zero_mem hSne
    exact this
  exact hmem _ hhead

/-- **The output is a permutation of `Γ`.** -/
theorem alignColPartPerm_wf (hP : P.1.length = m) (hQ : Q.1.length = m)
    (hstat : (colPartStat P).Perm (colPartStat Q)) :
    RawPerm.WF m (alignColPartPerm (P, Q)) := by
  have hdom : cpDom P = List.range m := by rw [cpDom, hP]
  refine ⟨?_, ?_, ?_⟩
  · rw [alignColPartPerm, List.length_map, hdom, List.length_range]
  · intro a ha
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 ha
    rw [hdom, List.mem_range] at hu
    exact (cpMatch_spec hP hQ hstat hu).1
  · rw [alignColPartPerm, hdom]
    refine List.Nodup.map_on ?_ List.nodup_range
    intro a ha b hb hab
    rw [List.mem_range] at ha hb
    have h1 := (cpMatch_spec hP hQ hstat ha).2
    have h2 := (cpMatch_spec hP hQ hstat hb).2
    rw [hab, h2] at h1
    exact cpRank_inj (by rw [hP]; exact ha) (by rw [hP]; exact hb) h1.symm

theorem labAt_alignColPartPerm (hP : P.1.length = m) {u : ℕ} (hu : u < m) :
    labAt (alignColPartPerm (P, Q)) u = cpMatch (P, Q) u := by
  have hdom : cpDom P = List.range m := by rw [cpDom, hP]
  have hlen : (alignColPartPerm (P, Q)).length = m := by
    rw [alignColPartPerm, List.length_map, hdom, List.length_range]
  rw [labAt, List.getD_eq_getElem _ _ (by rw [hlen]; exact hu)]
  show ((cpDom P).map (cpMatch (P, Q)))[u]'_ = _
  simp [hdom]

/-- §14.1, **line 2 (i)**: the computed `σ̄` **is an isomorphism** of the two colored
partitions, in the words of the category `Babai.ColoredPartitions` (§7.1). -/
theorem alignColPartPerm_colPartIso (hP : P.1.length = m) (hQ : Q.1.length = m)
    (hstat : (colPartStat P).Perm (colPartStat Q)) :
    ColPartIso m P Q (decPerm m (alignColPartPerm (P, Q))) := by
  have hwf := alignColPartPerm_wf hP hQ hstat
  have himg : ∀ u : Fin m,
      ((decPerm m (alignColPartPerm (P, Q)) u : Fin m) : ℕ) = cpMatch (P, Q) (u : ℕ) := by
    intro u
    rw [← labAt_eq_decPerm hwf u.isLt, labAt_alignColPartPerm hP u.isLt]
  have hrank : ∀ u : Fin m, cpRank Q (cpMatch (P, Q) (u : ℕ)) = cpRank P (u : ℕ) :=
    fun u => (cpMatch_spec hP hQ hstat u.isLt).2
  have hlt : ∀ u : Fin m, cpMatch (P, Q) (u : ℕ) < m :=
    fun u => (cpMatch_spec hP hQ hstat u.isLt).1
  have hcomp : ∀ u : Fin m, cpKey (Q, cpMatch (P, Q) (u : ℕ)) = cpKey (P, (u : ℕ)) ∧
      cpCellIdx Q (cpMatch (P, Q) (u : ℕ)) = cpCellIdx P (u : ℕ) :=
    fun u => ⟨(cpRank_eq_iff.1 (hrank u)).1, (cpRank_eq_iff.1 (hrank u)).2.1⟩
  constructor
  · intro u
    rw [himg u]
    have := labAt_of_cpKey_eq (hcomp u).1
    exact this
  · intro u v
    obtain ⟨hku, hiu⟩ := hcomp u
    obtain ⟨hkv, hiv⟩ := hcomp v
    rw [himg u, himg v]
    constructor
    · intro h
      refine cpCellIdx_inj (by rw [hQ]; exact hlt u) (by rw [hQ]; exact hlt v) ?_ ?_
      · rw [hku, hkv]; exact cpKey_congr h
      · rw [hiu, hiv]; exact cpCellIdx_congr h
    · intro h
      refine cpCellIdx_inj (by rw [hP]; exact u.isLt) (by rw [hP]; exact v.isLt) ?_ ?_
      · rw [← hku, ← hkv]; exact cpKey_congr h
      · rw [← hiu, ← hiv]; exact cpCellIdx_congr h

/-- §14.1, **line 2 (i)**: the verifier of session 1 accepts the computed `σ̄`. -/
theorem alignColPartPerm_check (hP : P.1.length = m) (hQ : Q.1.length = m)
    (h : alignColPartTest (P, Q) = true) :
    RawPerm.WF m (alignColPartPerm (P, Q)) ∧
      rawColPartIsoCheck ((P, Q), alignColPartPerm (P, Q)) = true := by
  have hstat : (colPartStat P).Perm (colPartStat Q) := (cpStatEq_iff _ _).1 h
  refine ⟨alignColPartPerm_wf hP hQ hstat, ?_⟩
  exact (rawColPartIsoCheck_iff hP (alignColPartPerm_wf hP hQ hstat)).2
    (alignColPartPerm_colPartIso hP hQ hstat)

/-- §14.1, **line 1 is decided**: the test of session 1 answers `true` exactly when the two
colored partitions are isomorphic.  (Line 1 asks for `G^ϕ`-isomorphism; this is the case
`G^ϕ = S(Γ)`.  For `G^ϕ = A(Γ)` see `Workspace/Algo/AlignParity.lean`.) -/
theorem alignColPartTest_iff (hP : P.1.length = m) (hQ : Q.1.length = m) :
    alignColPartTest (P, Q) = true ↔ ∃ f : Perm (Fin m), ColPartIso m P Q f := by
  constructor
  · intro h
    exact ⟨_, alignColPartPerm_colPartIso hP hQ ((cpStatEq_iff _ _).1 h)⟩
  · rintro ⟨f, hf⟩
    exact (cpStatEq_iff _ _).2 (colPartStat_perm hP hQ hf)

/-- §14.1, **line 1 is decided**, in the words of the `S(Γ)`-set the procedure acts on. -/
theorem alignColPartTest_iff_structIso (hP : P.1.length = m) (hQ : Q.1.length = m) :
    alignColPartTest (P, Q) = true ↔
      Babai.structIso (Set.univ : Set (Perm (Fin m))) (decColStruct m P) (decColStruct m Q)
        ≠ ∅ := by
  rw [alignColPartTest_iff hP hQ]
  constructor
  · rintro ⟨f, hf⟩ hempty
    have : f ∈ Babai.structIso (Set.univ : Set (Perm (Fin m))) (decColStruct m P)
        (decColStruct m Q) := ⟨Set.mem_univ _, (colPartIso_iff_smul m P Q f).1 hf⟩
    rw [hempty] at this
    exact this
  · intro h
    rcases Set.eq_empty_or_nonempty (Babai.structIso (Set.univ : Set (Perm (Fin m)))
      (decColStruct m P) (decColStruct m Q)) with he | ⟨f, hf⟩
    · exact absurd he h
    · exact ⟨f, (colPartIso_iff_smul m P Q f).2 hf.2⟩

end Spec

/-! ## The running time -/

theorem polyFun_and {α : Type*} [Enc α] {f g : α → Bool} (hf : PolyFun f) (hg : PolyFun g) :
    PolyFun (fun a => f a && g a) :=
  (PolyFun.ite hf hg (polyFun_const false)).of_eq (fun a => by cases hh : f a <;> simp [hh])

theorem polyFun_natLt : PolyFun (fun p : ℕ × ℕ => decide (p.1 < p.2)) :=
  ((polyFun_fst.add (polyFun_const 1)).le polyFun_snd).of_eq
    (fun _ => by rw [decide_eq_decide]; omega)

theorem polyFun_cpCellList : PolyFun (fun p : RawColPart × ℕ => cpCellList p.1 p.2) := by
  have ha : PolyFun (fun z : (RawColPart × ℕ) × ℕ => cellOf z.1.1 z.2) :=
    ((polyFun_fst.comp polyFun_fst).pair polyFun_snd).comp polyFun_cellOfPair
  have hb : PolyFun (fun z : (RawColPart × ℕ) × ℕ => cellOf z.1.1 z.1.2) :=
    polyFun_fst.comp polyFun_cellOfPair
  have hq : PolyFun (fun z : (RawColPart × ℕ) × ℕ =>
      decide (cellOf z.1.1 z.2 = cellOf z.1.1 z.1.2)) := (ha.pair hb).comp polyFun_pairNatEq
  exact ((polyFun_id.pair (polyFun_fst.comp polyFun_cpDom)).comp
    (PolyFun.filterParam hq)).of_eq (fun _ => rfl)

theorem polyFun_cpMin : PolyFun (fun p : RawColPart × ℕ => cpMin p.1 p.2) :=
  (polyFun_cpCellList.pair (polyFun_const 0)).comp polyFun_labAtPair

theorem polyFun_cpPos : PolyFun (fun p : RawColPart × ℕ => cpPos p.1 p.2) := by
  have ha : PolyFun (fun z : (RawColPart × ℕ) × ℕ => cellOf z.1.1 z.2) :=
    ((polyFun_fst.comp polyFun_fst).pair polyFun_snd).comp polyFun_cellOfPair
  have hb : PolyFun (fun z : (RawColPart × ℕ) × ℕ => cellOf z.1.1 z.1.2) :=
    polyFun_fst.comp polyFun_cellOfPair
  have h1 : PolyFun (fun z : (RawColPart × ℕ) × ℕ =>
      decide (cellOf z.1.1 z.2 = cellOf z.1.1 z.1.2)) := (ha.pair hb).comp polyFun_pairNatEq
  have h2 : PolyFun (fun z : (RawColPart × ℕ) × ℕ => decide (z.2 < z.1.2)) :=
    (polyFun_snd.pair (polyFun_fst.comp polyFun_snd)).comp polyFun_natLt
  exact ((polyFun_id.pair (polyFun_fst.comp polyFun_cpDom)).comp
    (PolyFun.filterParam (polyFun_and h1 h2))).comp polyFun_length

theorem polyFun_cpMinList : PolyFun (fun p : RawColPart × (ℕ × ℕ) => cpMinList p.1 p.2) := by
  have hm : PolyFun (fun z : (RawColPart × (ℕ × ℕ)) × ℕ => cpMin z.1.1 z.2) :=
    ((polyFun_fst.comp polyFun_fst).pair polyFun_snd).comp polyFun_cpMin
  have h1 : PolyFun (fun z : (RawColPart × (ℕ × ℕ)) × ℕ => decide (cpMin z.1.1 z.2 = z.2)) :=
    (hm.pair polyFun_snd).comp polyFun_natEq
  have hk : PolyFun (fun z : (RawColPart × (ℕ × ℕ)) × ℕ => cpKey (z.1.1, z.2)) :=
    ((polyFun_fst.comp polyFun_fst).pair polyFun_snd).comp polyFun_cpKey
  have h2 : PolyFun (fun z : (RawColPart × (ℕ × ℕ)) × ℕ =>
      decide (cpKey (z.1.1, z.2) = z.1.2)) :=
    (hk.pair (polyFun_fst.comp polyFun_snd)).comp polyFun_pairNatEq
  exact ((polyFun_id.pair ((polyFun_fst.comp polyFun_cpDom))).comp
    (PolyFun.filterParam (polyFun_and h1 h2))).of_eq (fun _ => rfl)

theorem polyFun_cpNumCells : PolyFun (fun p : RawColPart × (ℕ × ℕ) => cpNumCells p.1 p.2) :=
  polyFun_cpMinList.comp polyFun_length

theorem polyFun_cpCellIdx : PolyFun (fun p : RawColPart × ℕ => cpCellIdx p.1 p.2) := by
  have hm : PolyFun (fun z : (RawColPart × ℕ) × ℕ => cpMin z.1.1 z.2) :=
    ((polyFun_fst.comp polyFun_fst).pair polyFun_snd).comp polyFun_cpMin
  have hmu : PolyFun (fun z : (RawColPart × ℕ) × ℕ => cpMin z.1.1 z.1.2) :=
    polyFun_fst.comp polyFun_cpMin
  have h1 : PolyFun (fun z : (RawColPart × ℕ) × ℕ => decide (cpMin z.1.1 z.2 = z.2)) :=
    (hm.pair polyFun_snd).comp polyFun_natEq
  have hk : PolyFun (fun z : (RawColPart × ℕ) × ℕ => cpKey (z.1.1, z.2)) :=
    ((polyFun_fst.comp polyFun_fst).pair polyFun_snd).comp polyFun_cpKey
  have hku : PolyFun (fun z : (RawColPart × ℕ) × ℕ => cpKey (z.1.1, z.1.2)) :=
    polyFun_fst.comp polyFun_cpKey
  have h2 : PolyFun (fun z : (RawColPart × ℕ) × ℕ =>
      decide (cpKey (z.1.1, z.2) = cpKey (z.1.1, z.1.2))) :=
    (hk.pair hku).comp polyFun_pairNatEq
  have h3 : PolyFun (fun z : (RawColPart × ℕ) × ℕ =>
      decide (cpMin z.1.1 z.2 < cpMin z.1.1 z.1.2)) := (hm.pair hmu).comp polyFun_natLt
  exact ((polyFun_id.pair (polyFun_fst.comp polyFun_cpDom)).comp
    (PolyFun.filterParam (polyFun_and (polyFun_and h1 h2) h3))).comp polyFun_length

theorem polyFun_cpRank : PolyFun (fun p : RawColPart × ℕ => cpRank p.1 p.2) :=
  polyFun_cpKey.pair (polyFun_cpCellIdx.pair polyFun_cpPos)

theorem polyFun_rankEq :
    PolyFun (fun p : ((ℕ × ℕ) × ℕ × ℕ) × ((ℕ × ℕ) × ℕ × ℕ) => decide (p.1 = p.2)) := by
  have h1 : PolyFun (fun p : ((ℕ × ℕ) × ℕ × ℕ) × ((ℕ × ℕ) × ℕ × ℕ) =>
      decide (p.1.1 = p.2.1)) :=
    ((polyFun_fst.comp polyFun_fst).pair (polyFun_snd.comp polyFun_fst)).comp polyFun_pairNatEq
  have h2 : PolyFun (fun p : ((ℕ × ℕ) × ℕ × ℕ) × ((ℕ × ℕ) × ℕ × ℕ) =>
      decide (p.1.2 = p.2.2)) :=
    ((polyFun_fst.comp polyFun_snd).pair (polyFun_snd.comp polyFun_snd)).comp polyFun_pairNatEq
  refine (polyFun_and h1 h2).of_eq (fun p => ?_)
  by_cases hh : p.1.1 = p.2.1 <;> simp [hh, Prod.ext_iff]

theorem polyFun_cpMatch :
    PolyFun (fun p : (RawColPart × RawColPart) × ℕ => cpMatch p.1 p.2) := by
  have ha : PolyFun (fun z : ((RawColPart × RawColPart) × ℕ) × ℕ =>
      cpRank z.1.1.2 z.2) :=
    (((polyFun_fst.comp polyFun_fst).comp polyFun_snd).pair polyFun_snd).comp polyFun_cpRank
  have hb : PolyFun (fun z : ((RawColPart × RawColPart) × ℕ) × ℕ =>
      cpRank z.1.1.1 z.1.2) :=
    (((polyFun_fst.comp polyFun_fst).comp polyFun_fst).pair
      (polyFun_fst.comp polyFun_snd)).comp polyFun_cpRank
  have hq : PolyFun (fun z : ((RawColPart × RawColPart) × ℕ) × ℕ =>
      decide (cpRank z.1.1.2 z.2 = cpRank z.1.1.1 z.1.2)) := (ha.pair hb).comp polyFun_rankEq
  have hdom : PolyFun (fun p : (RawColPart × RawColPart) × ℕ => cpDom p.1.2) :=
    (polyFun_fst.comp polyFun_snd).comp polyFun_cpDom
  exact (((polyFun_id.pair hdom).comp (PolyFun.filterParam hq)).pair
    (polyFun_const 0)).comp polyFun_labAtPair

/-- §14.1, line 2 (i) **runs in polynomial time**. -/
theorem polyFun_alignColPartPerm : PolyFun alignColPartPerm :=
  ((polyFun_id.pair (polyFun_fst.comp polyFun_cpDom)).comp
    (PolyFun.mapParam polyFun_cpMatch)).of_eq (fun _ => rfl)

end Algo
