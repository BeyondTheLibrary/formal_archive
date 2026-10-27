import Workspace.Algo.AggregateRaw
import Workspace.Algo.AggregateTable

/-! # Test sets with the guard measured in the ambient domain

The master algorithm can have `m` much smaller than `n`. The arity is bounded by a
power of `log n`, so it must not be guarded by `log m`. We build guarded tuples on
`[m]` and keep their increasing rows. The result has exactly `C(m,t)` entries.
-/
namespace Algo
open RAM RAM.Targets
open scoped Classical

/-- §13.2: all test sets, with the guard on the size of `Ω`. -/
def aggTestSetsOn (c : ℕ) (p : RawAggTestInput) : List (List ℕ) :=
  ((aggTable c (p.1, p.2.1, List.range p.2.2.length)).2.map Prod.fst).filter
    (fun row => decide (row = aggNormalizeRow (p.2.2, row)))

theorem aggQuasiFun_testSetsOn (c : ℕ) : QuasiFun (aggTestSetsOn c) := by
  have ht : QuasiFun (fun p : RawAggTestInput =>
      (aggTable c (p.1, p.2.1, List.range p.2.2.length)).2.map Prod.fst) :=
    ((polyFun_fst.pair ((polyFun_snd.comp polyFun_fst).pair
      ((polyFun_snd.comp polyFun_snd).comp polyFun_rangeLength))).comp_quasiFun
      (aggQuasiFun_table c)).comp_poly (polyFun_snd.comp (PolyFun.map polyFun_fst))
  have hf : PolyFun (fun z : List ℕ × List ℕ => decide (z.2 = aggNormalizeRow z)) :=
    (polyFun_snd.pair aggPolyFun_normalizeRow).comp polyFun_listNatEq
  exact (((polyFun_snd.comp polyFun_snd).quasiFun.pair ht).comp_poly
    (PolyFun.filterParam hf)).of_eq (fun _ => rfl)

theorem aggNormalizeRow_enlarge {dom gdom row : List ℕ} (hm : gdom.length ≤ dom.length)
    (hr : row = aggNormalizeRow (gdom, row)) : row = aggNormalizeRow (dom, row) := by
  have hs : row.Pairwise (· < ·) := by rw [hr]; exact List.pairwise_lt_range.filter _
  apply hs.eq_of_mem_iff (List.pairwise_lt_range.filter _)
  intro u
  simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
  constructor
  · intro hu
    have hu' := hu
    rw [hr] at hu'
    exact ⟨(List.mem_range.1 (List.mem_filter.1 hu').1).trans_le hm, hu⟩
  · exact And.right

theorem aggMem_testSetsOn {c : ℕ} {ks dom gdom row : List ℕ}
    (hg : ks.length ≤ guardBound c dom.length) (_hm : gdom.length ≤ dom.length) :
    row ∈ aggTestSetsOn c (ks, dom, gdom) ↔
      row.length = ks.length ∧ row = aggNormalizeRow (gdom, row) := by
  unfold aggTestSetsOn
  rw [aggTable_of_guard (a := (ks, dom, List.range gdom.length)) hg, keys_tupleTable]
  simp only [List.mem_filter, mem_tuplesOf, List.mem_range, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨hl, _⟩, he⟩; exact ⟨hl, he⟩
  · rintro ⟨hl, he⟩
    refine ⟨⟨hl, ?_⟩, he⟩
    intro u hu
    rw [he] at hu
    exact List.mem_range.1 (List.mem_filter.1 hu).1

theorem aggRowOn_wf {c : ℕ} {ks dom gdom row : List ℕ}
    (hg : ks.length ≤ guardBound c dom.length) (hm : gdom.length ≤ dom.length)
    (hr : row ∈ aggTestSetsOn c (ks, dom, gdom)) :
    row.Nodup ∧ (∀ u ∈ row, u < gdom.length) ∧ row.length = ks.length := by
  obtain ⟨hl, he⟩ := (aggMem_testSetsOn hg hm).1 hr
  refine ⟨?_, ?_, hl⟩
  · rw [he]; exact List.nodup_range.filter _
  · intro u hu; rw [he] at hu
    exact List.mem_range.1 (List.mem_filter.1 hu).1

theorem aggNameOn_inverse {c : ℕ} {ks dom gdom row : List ℕ}
    (hg : ks.length ≤ guardBound c dom.length) (hm : gdom.length ≤ dom.length)
    (hr : row ∈ aggTestSetsOn c (ks, dom, gdom)) :
    aggName (winSet gdom.length row) = row := by
  rw [(aggMem_testSetsOn hg hm).1 hr |>.2]
  apply List.filter_congr
  intro u hu
  simp only [aggNormalizeRow] at *
  simp [winSet, List.mem_range.1 hu]

theorem aggNodup_testSetsOn {c : ℕ} {ks dom gdom : List ℕ}
    (hg : ks.length ≤ guardBound c dom.length) :
    (aggTestSetsOn c (ks, dom, gdom)).Nodup := by
  unfold aggTestSetsOn
  rw [aggTable_of_guard (a := (ks, dom, List.range gdom.length)) hg, keys_tupleTable]
  exact (nodup_tuplesOf List.nodup_range _).filter _

/-- The ambient guard still enumerates exactly the paper's test sets. -/
theorem aggTestSetsOn_perm {c : ℕ} {ks dom gdom : List ℕ}
    (hg : ks.length ≤ guardBound c dom.length) (hm : gdom.length ≤ dom.length) :
    ((aggTestSetsOn c (ks, dom, gdom)).map (winSet gdom.length)).Perm
      (Babai.testSetList (Fin gdom.length) ks.length) := by
  have hnd : ((aggTestSetsOn c (ks, dom, gdom)).map (winSet gdom.length)).Nodup := by
    apply List.Nodup.map_on _ (aggNodup_testSetsOn hg)
    intro a ha b hb he
    exact (aggNameOn_inverse hg hm ha).symm.trans
      ((congrArg aggName he).trans (aggNameOn_inverse hg hm hb))
  apply List.perm_of_nodup_nodup_toFinset_eq hnd (aggPaperList_nodup _ _)
  ext T
  simp only [List.mem_toFinset, List.mem_map, aggMem_paperList]
  constructor
  · rintro ⟨row, hr, rfl⟩
    obtain ⟨hn, hb, hl⟩ := aggRowOn_wf hg hm hr
    exact (ncard_winSet row hn hb).trans hl
  · intro hT
    refine ⟨aggName T, ?_, aggName_spec T⟩
    exact (aggMem_testSetsOn hg hm).2
      ⟨(aggName_length T).trans hT, aggName_normal T gdom rfl⟩

theorem aggLength_testSetsOn {c : ℕ} {ks dom gdom : List ℕ}
    (hg : ks.length ≤ guardBound c dom.length) (hm : gdom.length ≤ dom.length) :
    (aggTestSetsOn c (ks, dom, gdom)).length = gdom.length.choose ks.length := by
  have h := (aggTestSetsOn_perm hg hm).length_eq
  simpa only [List.length_map, Babai.length_testSetList, Fintype.card_fin] using h

theorem aggSize_testSetsOn (c : ℕ) : QuasiSizeBound (aggTestSetsOn c) :=
  (aggQuasiFun_testSetsOn c).size

theorem aggSize_testSetsOn_explicit {c : ℕ} {ks dom gdom : List ℕ}
    (hg : ks.length ≤ guardBound c dom.length) (hm : gdom.length ≤ dom.length)
    (ht : ks.length ≤ dom.length) : Enc.size (aggTestSetsOn c (ks, dom, gdom)) ≤
      1 + gdom.length.choose ks.length * (2 * strBound dom.length + 1) := by
  have he : ∀ row ∈ aggTestSetsOn c (ks, dom, gdom), Enc.size row ≤ strBound dom.length := by
    intro row hr
    obtain ⟨_, hb, hl⟩ := aggRowOn_wf hg hm hr
    exact size_natList_le (hl.le.trans ht) (fun u hu => (hb u hu).trans_le hm)
  have h := size_list_le_of_entries _ _ he
  rwa [aggLength_testSetsOn hg hm] at h

/-- The specification fields, completeness and count hold together with the ambient guard. -/
theorem aggExists_completeOn {c n : ℕ} {dom gdom ks : List ℕ}
    {G : Subgroup (Equiv.Perm (Fin n))}
    (ϕ : G →* Equiv.Perm (Fin gdom.length)) (x : Fin n → ℕ)
    (hg : ks.length ≤ guardBound c dom.length) (hm : gdom.length ≤ dom.length) :
    ∃ store : RawAggStore, store.map Prod.fst = aggTestSetsOn c (ks, dom, gdom) ∧
      AggStoreFor ϕ x ks.length store ∧ AggComplete gdom.length ks.length store ∧
      store.length = gdom.length.choose ks.length := by
  obtain ⟨store, he, hs⟩ := aggExists_store ϕ x (aggTestSetsOn c (ks, dom, gdom))
    (aggNodup_testSetsOn hg) (fun _ hr => aggRowOn_wf hg hm hr)
  refine ⟨store, he, hs, ?_, ?_⟩
  · intro T hT
    have hr : aggName T ∈ aggTestSetsOn c (ks, dom, gdom) :=
      (aggMem_testSetsOn hg hm).2
        ⟨(aggName_length T).trans hT, aggName_normal T gdom rfl⟩
    rw [← he] at hr
    obtain ⟨e, he', hrow⟩ := List.mem_map.1 hr
    exact ⟨e, he', hrow ▸ aggName_spec T⟩
  · have h := congrArg List.length he
    simpa [aggLength_testSetsOn hg hm] using h

/-- A partial store that uses each scheduled name at most once has at most `C(m,t)` entries. -/
theorem aggStore_lengthOn {c n : ℕ} {ks dom gdom : List ℕ} {store : RawAggStore}
    (hg : ks.length ≤ guardBound c dom.length) (hm : gdom.length ≤ dom.length)
    (hs : AggStoreWF n gdom.length ks.length store)
    (hkeys : store.map Prod.fst ⊆ aggTestSetsOn c (ks, dom, gdom)) :
    store.length ≤ gdom.length.choose ks.length := by
  have h := (List.subperm_of_subset hs.1 hkeys).length_le
  simpa only [List.length_map, aggLength_testSetsOn hg hm] using h

end Algo
