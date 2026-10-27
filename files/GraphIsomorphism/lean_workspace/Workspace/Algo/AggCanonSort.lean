import Workspace.Algo.RefinePoly
import Workspace.LocalCertificates.Canonical

/-! # Sorting image and representative pairs

We count the keys smaller than each key. The output scans these ranks in
increasing order. All loops run over stored lists, including on malformed data.
-/

namespace Algo

open RAM RAM.Targets

abbrev AggkRow := List ℕ × RawPerm

/-- The rank of an image key among the stored rows. -/
def aggkRowRank (p : List AggkRow × AggkRow) : ℕ :=
  rankIn (p.1.map Prod.fst, p.2.1)

def aggkAtRank (p : (List AggkRow × ℕ) × AggkRow) : Bool :=
  decide (aggkRowRank (p.1.1, p.2) = p.1.2)

def aggkRankRows (p : List AggkRow × ℕ) : List AggkRow :=
  p.1.filter (fun r => aggkAtRank (p, r))

/-- Sort the materialized rows. Equal keys retain their input order. -/
def aggkSortRows (rows : List AggkRow) : List AggkRow :=
  (List.range rows.length).flatMap (fun i => aggkRankRows (rows, i))

theorem aggkPolyFun_rowRank : PolyFun aggkRowRank :=
  ((polyFun_fst.comp (PolyFun.map polyFun_fst)).pair
    (polyFun_snd.comp polyFun_fst)).comp polyFun_rankIn

theorem aggkPolyFun_atRank : PolyFun aggkAtRank :=
  (((polyFun_fst.comp polyFun_fst).pair polyFun_snd).comp aggkPolyFun_rowRank).natEq
    (polyFun_fst.comp polyFun_snd)

theorem aggkPolyFun_rankRows : PolyFun aggkRankRows :=
  (polyFun_id.pair polyFun_fst).comp (PolyFun.filterParam aggkPolyFun_atRank)

theorem aggkPolyFun_sortRows : PolyFun aggkSortRows :=
  ((polyFun_id.pair polyFun_rangeLength).comp
    (PolyFun.flatMapParam aggkPolyFun_rankRows)).of_eq (fun _ => rfl)

theorem aggkRowRank_lt {rows : List AggkRow} {r : AggkRow} (hr : r ∈ rows) :
    aggkRowRank (rows, r) < rows.length := by
  simpa only [aggkRowRank, List.length_map] using
    rankIn_lt_length (List.mem_map_of_mem (f := Prod.fst) hr)

@[simp] theorem aggkMem_rankRows (rows : List AggkRow) (i : ℕ) (r : AggkRow) :
    r ∈ aggkRankRows (rows, i) ↔ r ∈ rows ∧ aggkRowRank (rows, r) = i := by
  simp [aggkRankRows, aggkAtRank]

@[simp] theorem aggkMem_sortRows (rows : List AggkRow) (r : AggkRow) :
    r ∈ aggkSortRows rows ↔ r ∈ rows := by
  simp only [aggkSortRows, List.mem_flatMap, List.mem_range, aggkMem_rankRows]
  exact ⟨fun ⟨_, _, h, _⟩ => h, fun h => ⟨_, aggkRowRank_lt h, h, rfl⟩⟩

/-- The numeric comparison agrees with list lexicographic order on equal lengths. -/
theorem aggkCmpRec_of_lt {u v : List ℕ} (hlen : u.length = v.length) (h : u < v) :
    cmpRec u v = 1 := by
  induction u generalizing v with
  | nil => cases v <;> simp_all
  | cons a u ih =>
    cases v with
    | nil => simp at hlen
    | cons b v =>
      rcases List.cons_lex_cons_iff.mp h with hab | ⟨rfl, huv⟩
      · simp [cmpRec_cons, hab]
      · simpa only [cmpRec_cons, lt_self_iff_false, ↓reduceIte] using
          ih (by simpa using hlen) huv

theorem aggkRank_le_key {rows : List AggkRow} {a b : AggkRow}
    (ha : a ∈ rows) (hb : b ∈ rows) (hlen : a.1.length = b.1.length)
    (hr : aggkRowRank (rows, a) ≤ aggkRowRank (rows, b)) : a.1 ≤ b.1 := by
  apply le_of_not_gt
  intro hlt
  have h := rankIn_lt_rankIn (List.mem_map_of_mem (f := Prod.fst) hb)
    (aggkCmpRec_of_lt hlen.symm hlt)
  exact Nat.not_lt_of_ge hr h

theorem aggkSortRows_sorted {rows : List AggkRow} {k : ℕ}
    (hlen : ∀ r ∈ rows, r.1.length = k) :
    ((aggkSortRows rows).map Prod.fst).SortedLE := by
  rw [List.sortedLE_iff_pairwise, List.pairwise_map, aggkSortRows, List.pairwise_flatMap]
  constructor
  · intro i hi
    apply List.pairwise_of_forall_mem_list
    intro a ha b hb
    obtain ⟨ha, hra⟩ := (aggkMem_rankRows rows i a).mp ha
    obtain ⟨hb, hrb⟩ := (aggkMem_rankRows rows i b).mp hb
    exact aggkRank_le_key ha hb ((hlen a ha).trans (hlen b hb).symm)
      (by rw [hra, hrb])
  · apply List.pairwise_lt_range.imp
    intro i j hij a ha b hb
    obtain ⟨ha, hra⟩ := (aggkMem_rankRows rows i a).mp ha
    obtain ⟨hb, hrb⟩ := (aggkMem_rankRows rows j b).mp hb
    exact aggkRank_le_key ha hb ((hlen a ha).trans (hlen b hb).symm)
      (by rw [hra, hrb]; omega)

theorem aggkSortRows_nodup {rows : List AggkRow} (h : rows.Nodup) :
    (aggkSortRows rows).Nodup := by
  rw [aggkSortRows, List.nodup_flatMap]
  constructor
  · intro i hi
    exact h.filter _
  · apply List.pairwise_lt_range.imp
    intro i j hij
    apply List.disjoint_left.mpr
    intro a hai haj
    have hi := (aggkMem_rankRows rows i a).mp hai
    have hj := (aggkMem_rankRows rows j a).mp haj
    omega

theorem aggkSortRows_perm {rows : List AggkRow} (h : rows.Nodup) :
    (aggkSortRows rows).Perm rows := by
  apply List.perm_of_nodup_nodup_toFinset_eq (aggkSortRows_nodup h) h
  ext r
  simp

end Algo
