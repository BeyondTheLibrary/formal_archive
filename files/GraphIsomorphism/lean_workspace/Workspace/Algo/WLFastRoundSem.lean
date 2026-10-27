/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

§5.4.2: the trivial bound `O(k²n^{2k+1})` for `k`-ary WL refinement.  The lists one round of
the fast program writes, and why they give the new colors.
-/
import Workspace.Algo.WLFastBuild

/-!
# One round of the fast `k`-WL program: the lists

For the current coloring `q` (same tuples as the input `p`) the round writes, for every row `r`
and vertex `y`, the record `r :: nvec r y`, where `nvec r y = (c(t_r[i ↦ y]))_{i<k}` is the tuple
of old colors of §5.4.1 (`Algo.WLFast.nvec_eq_innerVec`).  Sorting all records sorts them by row,
and within a row by the tuple (`Algo.WLFast.sorted_eq`), so the records of row `r` come out as
`sortV r`, the sorted tuples of the row, which are `sortedVecs q t_r`
(`Algo.WLFast.sortV_eq`).  The string of row `r` written next is `strOf q t_r`
(`Algo.WLFast.strRec_eq`).

No axiom, no `sorry`.
-/

namespace Algo

namespace WLFast

open RAM RAM.Exact

/-- The tuple of old colors of row `r` at the vertex `y`. -/
def nvec (q p : RawWL) (k r y : ℕ) : List ℕ :=
  (List.range k).map (fun i => tblGet (q.2, (tup p r).set i y))

/-- The records of row `r`: `r :: nvec r y` for each vertex `y`. -/
def recRow (q p : RawWL) (n k r : ℕ) : List ℕ := (List.range n).flatMap (fun y => r :: nvec q p k r y)

/-- The addresses of the records of row `r`. -/
def addrRow (Rec n k r : ℕ) : List ℕ :=
  (List.range n).map (fun y => Rec + (r * (n * (k + 1)) + y * (k + 1)))

/-- The tuples of old colors of row `r`, sorted. -/
def sortV (q p : RawWL) (n k r : ℕ) : List (List ℕ) :=
  ((List.range n).map (nvec q p k r)).mergeSort (· ≤ ·)

/-- All records, sorted. -/
def sortedRecs (q p : RawWL) (n k N : ℕ) : List (List ℕ) :=
  (List.range N).flatMap (fun r => (sortV q p n k r).map (fun v => r :: v))

/-- The string record of row `r`: the old color, the complemented sorted tuples, a free cell. -/
def strRec (q p : RawWL) (n k r : ℕ) : List ℕ :=
  (tblGet (q.2, tup p r) :: (List.range n).flatMap (fun y => (List.range k).map
    (fun i => q.2.length - (((sortV q p n k r).getD y []).getD i 0)))) ++ [0]

section

variable {q p : RawWL} {n k r N : ℕ}

@[simp] theorem length_nvec (q p : RawWL) (k r y : ℕ) : (nvec q p k r y).length = k := by
  simp [nvec]

theorem length_recRow (q p : RawWL) (n k r : ℕ) : (recRow q p n k r).length = n * (k + 1) :=
  length_range_flatMap (fun y => by simp) n

@[simp] theorem length_addrRow (Rec n k r : ℕ) : (addrRow Rec n k r).length = n := by
  simp [addrRow]

theorem sortV_perm (q p : RawWL) (n k r : ℕ) :
    (sortV q p n k r).Perm ((List.range n).map (nvec q p k r)) := List.mergeSort_perm _ _

@[simp] theorem length_sortV (q p : RawWL) (n k r : ℕ) : (sortV q p n k r).length = n := by
  rw [(sortV_perm q p n k r).length_eq]; simp

theorem length_of_mem_sortV {v : List ℕ} (hv : v ∈ sortV q p n k r) : v.length = k := by
  obtain ⟨y, -, rfl⟩ := List.mem_map.1 ((sortV_perm q p n k r).subset hv)
  simp

theorem sortV_pairwise (q p : RawWL) (n k r : ℕ) : (sortV q p n k r).Pairwise (· ≤ ·) :=
  List.pairwise_mergeSort' (· ≤ ·) _

theorem nvec_eq_innerVec {r : ℕ} (hl : (tup p r).length = k) (y : ℕ) :
    nvec q p k r y = innerVec q.2 (tup p r) y := by
  simp only [nvec, innerVec, hl, substAt_eq_set]

/-- The sorted tuples of a row are those of §5.4.1. -/
theorem sortV_eq {r : ℕ} (hl : (tup p r).length = k) (hq1 : q.1 = p.1)
    (hdom : p.1.Perm (List.range n)) : sortV q p n k r = sortedVecs q (tup p r) := by
  refine eq_sortedVecs (sortV_pairwise q p n k r) ((sortV_perm q p n k r).trans ?_)
  rw [vecsOf, hq1]
  have e : (List.range n).map (nvec q p k r) = (List.range n).map (innerVec q.2 (tup p r)) :=
    List.map_congr_left (fun y _ => nvec_eq_innerVec hl y)
  rw [e]
  exact (hdom.map _).symm

theorem sortedRecs_pairwise (q p : RawWL) (n k N : ℕ) :
    (sortedRecs q p n k N).Pairwise (· ≤ ·) := by
  unfold sortedRecs
  rw [List.pairwise_flatMap]
  refine ⟨fun r _ => ?_, ?_⟩
  · rw [List.pairwise_map]
    exact (sortV_pairwise q p n k r).imp (fun h => cons_le_cons_iff'.2 (Or.inr ⟨rfl, h⟩))
  · refine List.pairwise_lt_range.imp (fun {a b} hab => ?_)
    intro x hx y hy
    obtain ⟨v, -, rfl⟩ := List.mem_map.1 hx
    obtain ⟨w, -, rfl⟩ := List.mem_map.1 hy
    exact cons_le_cons_iff'.2 (Or.inl hab)

theorem recs_perm (q p : RawWL) (n k N : ℕ) :
    ((List.range N).flatMap (fun r => (List.range n).map (fun y => r :: nvec q p k r y))).Perm
      (sortedRecs q p n k N) := by
  unfold sortedRecs
  refine List.Perm.flatMap_left _ (fun r _ => ?_)
  have : (List.range n).map (fun y => r :: nvec q p k r y) =
      ((List.range n).map (nvec q p k r)).map (fun v => r :: v) := by
    rw [List.map_map]; rfl
  rw [this]
  exact ((sortV_perm q p n k r).symm).map _

/-- **The sorted records.**  A sorted permutation of the records is `sortedRecs`. -/
theorem sorted_eq {L : List (List ℕ)} (hs : L.Pairwise (· ≤ ·))
    (hp : L.Perm ((List.range N).flatMap (fun r => (List.range n).map (fun y => r :: nvec q p k r y)))) :
    L = sortedRecs q p n k N :=
  List.Perm.eq_of_pairwise' hs (sortedRecs_pairwise q p n k N) (hp.trans (recs_perm q p n k N))

theorem getElem_sortedRecs {y : ℕ} (hr : r < N) (hy : y < n)
    (h : r * n + y < (sortedRecs q p n k N).length) :
    (sortedRecs q p n k N)[r * n + y] = r :: (sortV q p n k r)[y]'(by simp; exact hy) := by
  unfold sortedRecs
  rw [getElem_flatMap_range_of_length (f := fun r => (sortV q p n k r).map (fun v => r :: v))
    (fun r => by simp) N r y hr hy]
  simp

theorem length_sortedRecs (q p : RawWL) (n k N : ℕ) : (sortedRecs q p n k N).length = N * n :=
  length_range_flatMap (fun r => by simp) N

/-- Reading a list of `n` blocks of length `k` block by block. -/
theorem flatMap_getD_eq (f : ℕ → ℕ) :
    ∀ (l : List (List ℕ)), (∀ v ∈ l, v.length = k) →
      (List.range l.length).flatMap (fun y => (List.range k).map (fun i => f ((l.getD y []).getD i 0)))
        = l.flatten.map f
  | [], _ => by simp
  | v :: l, h => by
      have hv : v.length = k := h v (by simp)
      have ih := flatMap_getD_eq f l (fun w hw => h w (by simp [hw]))
      rw [List.length_cons, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map,
        List.flatten_cons, List.map_append]
      congr 1
      · simp only [List.getD_cons_zero]
        apply List.ext_getElem (by simp [hv])
        intro i h1 h2
        simp only [List.getElem_map, List.getElem_range]
        try rw [List.getD_eq_getElem _ _ (by rw [hv]; simpa using h1)]

/-- **The string record of a row** is the string of §5.4.2 (`strOf`), then a free cell. -/
theorem strRec_eq {r : ℕ} (hl : (tup p r).length = k) (hq1 : q.1 = p.1)
    (hdom : p.1.Perm (List.range n)) : strRec q p n k r = strOf q (tup p r) ++ [0] := by
  unfold strRec strOf
  have e := flatMap_getD_eq (k := k) (fun c => q.2.length - c) (sortV q p n k r)
    (fun v hv => length_of_mem_sortV hv)
  rw [length_sortV] at e
  rw [e, sortV_eq hl hq1 hdom]

/-- The strings of all rows, listed by row, are the strings of the table. -/
theorem strs_eq (hN : q.2.length = N) (hkey : ∀ r (hr : r < q.2.length), q.2[r].1 = tup p r) :
    (List.range N).map (fun r => strOf q (tup p r)) = q.2.map (fun r => strOf q r.1) := by
  subst hN
  apply List.ext_getElem (by simp)
  intro r h1 h2
  simp only [List.getElem_map, List.getElem_range]
  rw [hkey r (by simpa using h2)]

end

end WLFast

end Algo
