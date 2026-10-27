import Workspace.Algo.WLGuarded
import Workspace.Algo.TestSetNaming
import Workspace.LocalCertificates.AggregateRound

/-! # The test sets of AggregateCertificates (§13.2)

The table lists each set once, by its increasing list of labels. The guard is the
same as the tuple-table guard. A fixed exponent is chosen before the input size.
The order need not equal the unspecified order of `Babai.testSetList`.
-/
namespace Algo
open RAM RAM.Targets

/-- Position in the certificate phase: test-set index and local loop counter. -/
abbrev RawAggPos := ℕ × ℕ

/-- Increasing names for the points selected by a row. -/
def aggNormalizeRow (p : List ℕ × List ℕ) : List ℕ :=
  (List.range p.1.length).filter (fun u => decide (u ∈ p.2))

theorem aggPolyFun_normalizeRow : PolyFun aggNormalizeRow :=
  (((polyFun_snd.pair (polyFun_fst.comp polyFun_rangeLength)).comp
    (PolyFun.filterParam ((polyFun_snd.pair polyFun_fst).comp polyFun_natListMem)))).of_eq
    (fun _ => rfl)

/-- §13.2: the test sets in a fixed order. The first list witnesses the arity. -/
def aggTestSets (c : ℕ) (p : List ℕ × List ℕ) : List (List ℕ) :=
  (((guardedTable c (p.1, List.range p.2.length)).2).map Prod.fst).filter
    (fun row => decide (row = aggNormalizeRow (p.2, row)))

theorem aggQuasiFun_testSets (c : ℕ) : QuasiFun (aggTestSets c) := by
  have ht : QuasiFun (fun p : List ℕ × List ℕ =>
      ((guardedTable c (p.1, List.range p.2.length)).2).map Prod.fst) :=
    ((polyFun_fst.pair (polyFun_snd.comp polyFun_rangeLength)).quasiFun.comp
      (quasiFun_guardedTable c)).comp_poly
        (polyFun_snd.comp (PolyFun.map polyFun_fst))
  have hf : PolyFun (fun z : List ℕ × List ℕ =>
      decide (z.2 = aggNormalizeRow z)) :=
    (polyFun_snd.pair aggPolyFun_normalizeRow).comp polyFun_listNatEq
  exact ((polyFun_snd.quasiFun.pair ht).comp_poly (PolyFun.filterParam hf)).of_eq
    (fun _ => rfl)

theorem aggSize_testSets (c : ℕ) : QuasiSizeBound (aggTestSets c) :=
  (aggQuasiFun_testSets c).size

/-- A row occurs exactly when it names a set of the requested size in increasing order. -/
theorem aggMem_testSets {c : ℕ} {ks dom row : List ℕ}
    (hg : ks.length ≤ guardBound c dom.length) :
    row ∈ aggTestSets c (ks, dom) ↔
      row.length = ks.length ∧ row = aggNormalizeRow (dom, row) := by
  have hg' : ks.length ≤ guardBound c (List.range dom.length).length := by simpa using hg
  unfold aggTestSets
  rw [guardedTable_of_guard (a := (ks, List.range dom.length)) hg', keys_tupleTable]
  simp only [List.mem_filter, mem_tuplesOf, List.mem_range, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨hl, _⟩, he⟩; exact ⟨hl, he⟩
  · rintro ⟨hl, he⟩
    refine ⟨⟨hl, ?_⟩, he⟩
    intro u hu
    rw [he] at hu
    exact List.mem_range.1 (List.mem_filter.1 hu).1

theorem aggNodup_testSets (c : ℕ) (ks dom : List ℕ)
    (hg : ks.length ≤ guardBound c dom.length) : (aggTestSets c (ks, dom)).Nodup := by
  have hg' : ks.length ≤ guardBound c (List.range dom.length).length := by simpa using hg
  unfold aggTestSets
  rw [guardedTable_of_guard hg', keys_tupleTable]
  exact (nodup_tuplesOf List.nodup_range _).filter _

theorem aggRow_wf {c : ℕ} {ks dom row : List ℕ}
    (hg : ks.length ≤ guardBound c dom.length) (hr : row ∈ aggTestSets c (ks, dom)) :
    row.Nodup ∧ (∀ u ∈ row, u < dom.length) ∧ row.length = ks.length := by
  obtain ⟨hl, he⟩ := (aggMem_testSets hg).1 hr
  refine ⟨?_, ?_, hl⟩
  · rw [he]; exact List.nodup_range.filter _
  · intro u hu; rw [he] at hu
    exact List.mem_range.1 (List.mem_filter.1 hu).1

open scoped Classical

/-- A mathematical set has one increasing raw name. -/
noncomputable def aggName {m : ℕ} (T : Set (Fin m)) : List ℕ :=
  (List.range m).filter (fun u => if h : u < m then decide ((⟨u, h⟩ : Fin m) ∈ T) else false)

theorem aggName_spec {m : ℕ} (T : Set (Fin m)) : winSet m (aggName T) = T := by
  classical
  ext u
  simp [winSet, aggName]

theorem aggName_normal {m : ℕ} (T : Set (Fin m)) (dom : List ℕ) (hd : dom.length = m) :
    aggName T = aggNormalizeRow (dom, aggName T) := by
  classical
  unfold aggNormalizeRow aggName
  rw [hd]
  apply List.filter_congr
  intro u hu
  have hu' := List.mem_range.1 hu
  simp [hu']

theorem aggName_length {m : ℕ} (T : Set (Fin m)) : (aggName T).length = T.ncard := by
  have h := ncard_winSet (aggName T) (List.nodup_range.filter _)
    (fun u hu => List.mem_range.1 (List.mem_filter.1 hu).1)
  rw [aggName_spec] at h
  exact h.symm

/-- Coverage, stated in the mathematical vocabulary of §13.2. -/
theorem aggTestSets_cover {c : ℕ} {ks dom : List ℕ}
    (hg : ks.length ≤ guardBound c dom.length) (T : Set (Fin dom.length))
    (hT : T.ncard = ks.length) : aggName T ∈ aggTestSets c (ks, dom) :=
  (aggMem_testSets hg).2 ⟨(aggName_length T).trans hT, aggName_normal T dom rfl⟩

theorem aggDecoded_mem {c : ℕ} {ks dom row : List ℕ}
    (hg : ks.length ≤ guardBound c dom.length) (hr : row ∈ aggTestSets c (ks, dom)) :
    (winSet dom.length row).ncard = ks.length := by
  obtain ⟨hnd, hlt, hl⟩ := aggRow_wf hg hr
  exact (ncard_winSet row hnd hlt).trans hl

/-- The well-formedness hypotheses hold, for example, at arity zero on one point. -/
example : ([] : List ℕ) ∈ aggTestSets 1 ([], [0]) := by
  apply (aggMem_testSets (by simp [guardBound])).2
  simp [aggNormalizeRow]

/-- The normal name can be recovered from its decoded set. -/
theorem aggName_inverse {c : ℕ} {ks dom row : List ℕ}
    (hg : ks.length ≤ guardBound c dom.length) (hr : row ∈ aggTestSets c (ks, dom)) :
    aggName (winSet dom.length row) = row := by
  rw [(aggMem_testSets hg).1 hr |>.2]
  apply List.filter_congr
  intro u hu
  simp only [aggNormalizeRow] at *
  simp [winSet, List.mem_range.1 hu]

/-- Decoding introduces no repetitions. -/
theorem aggNodup_decoded {c : ℕ} {ks dom : List ℕ}
    (hg : ks.length ≤ guardBound c dom.length) :
    ((aggTestSets c (ks, dom)).map (winSet dom.length)).Nodup := by
  apply List.Nodup.map_on _ (aggNodup_testSets c ks dom hg)
  intro a ha b hb he
  exact (aggName_inverse hg ha).symm.trans ((congrArg aggName he).trans (aggName_inverse hg hb))

/-- Membership in the paper's list does not depend on its unspecified order. -/
theorem aggMem_paperList {m t : ℕ} {T : Set (Fin m)} :
    T ∈ Babai.testSetList (Fin m) t ↔ T.ncard = t := by
  classical
  constructor
  · exact Babai.ncard_of_mem_testSetList
  · intro hT
    apply List.mem_map.2
    refine ⟨⟨T.toFinset, ?_⟩, Finset.mem_toList.2 (Finset.mem_univ _), ?_⟩
    · exact (Set.ncard_eq_toFinset_card' T).symm.trans hT
    · exact Set.coe_toFinset T

theorem aggPaperList_nodup (m t : ℕ) : (Babai.testSetList (Fin m) t).Nodup := by
  classical
  apply List.Nodup.map _ (Finset.nodup_toList _)
  intro a b h
  exact Subtype.ext (Finset.coe_injective h)

/-- §13.2: the raw order is a permutation of the paper's test-set order. -/
theorem aggTestSets_perm {c : ℕ} {ks dom : List ℕ}
    (hg : ks.length ≤ guardBound c dom.length) :
    ((aggTestSets c (ks, dom)).map (winSet dom.length)).Perm
      (Babai.testSetList (Fin dom.length) ks.length) := by
  apply List.perm_of_nodup_nodup_toFinset_eq (aggNodup_decoded hg)
    (aggPaperList_nodup _ _)
  ext T
  simp only [List.mem_toFinset, List.mem_map, aggMem_paperList]
  constructor
  · rintro ⟨row, hr, rfl⟩; exact aggDecoded_mem hg hr
  · intro hT
    exact ⟨aggName T, aggTestSets_cover hg T hT, aggName_spec T⟩

theorem aggLength_testSets {c : ℕ} {ks dom : List ℕ}
    (hg : ks.length ≤ guardBound c dom.length) :
    (aggTestSets c (ks, dom)).length = dom.length.choose ks.length := by
  have h := (aggTestSets_perm hg).length_eq
  simpa only [List.length_map, Babai.length_testSetList, Fintype.card_fin] using h

/-- The size in the number of test sets and the size of the point domain. -/
theorem aggSize_testSets_explicit {c : ℕ} {ks dom : List ℕ}
    (hg : ks.length ≤ guardBound c dom.length) (ht : ks.length ≤ dom.length) :
    Enc.size (aggTestSets c (ks, dom)) ≤
      1 + dom.length.choose ks.length * (2 * strBound dom.length + 1) := by
  have h := size_list_le_of_entries (aggTestSets c (ks, dom)) (strBound dom.length)
    (fun row hr => size_natList_le
      ((aggRow_wf hg hr).2.2.le.trans ht) (aggRow_wf hg hr).2.1)
  rwa [aggLength_testSets hg] at h

end Algo
