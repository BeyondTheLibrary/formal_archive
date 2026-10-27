/-
An explicit running time for Theorem 1.1.1 (Babai, version 2.5), part 1: the width of one
node of the recursion of Section 9 (Theorem 9.2.2 on the RAM). Not part of the faithful
formalization.
-/
import Workspace.Algo.SplitBipCallBound
import Workspace.Algo.SplitBipCaseSize
import Workspace.Algo.SplitDesignLog

/-!
# Section 9: the number of children of one node, explicitly

`Algo.exists_sbipNodeGraphs_bound` bounds the stored children of a node of the recursion of
Section 9 through the (quasipolynomial, implicit) size of the whole turn. Here the count is
explicit: at a represented node on `m` points,

`(sbipNodeGraphs c I).length ≤ (m + 1) ^ (3 * (log₂ m + 1))`.

Every branch of step 9 lists at most `m` entries, except Case 3 of Sec. 9.7 (the design
case), which lists the versions of the Design Lemma: one per tuple of individualized points
of the second part. The tuples have the length of the witness of the call, which is the rank
(Case 3a, `2^{3d} ≤ k^7`, so `d ≤ (7/3) log₂ k`) or the skeleton rank
(`⌈(7/4) log₂ k⌉`), where `k ≤ m` is the size of the first part.
-/

namespace Explicit

open Algo RAM Babai

/-! ## The witness of the design call is logarithmic -/

theorem pow_lt_two_pow_log_succ (k e : ℕ) : k ^ e ≤ 2 ^ (e * (Nat.log 2 k + 1)) := by
  have h : k < 2 ^ (Nat.log 2 k + 1) := Nat.lt_pow_succ_log_self (by norm_num) k
  calc k ^ e ≤ (2 ^ (Nat.log 2 k + 1)) ^ e := Nat.pow_le_pow_left h.le e
    _ = 2 ^ (e * (Nat.log 2 k + 1)) := by rw [← pow_mul, mul_comm]

/-- Case 3a: the rank is at most `3 (log₂ k + 1)`. -/
theorem designRank_le_of_case3a {r : RawUpccCase} (h : designCase3a r = true) :
    designRank r ≤ 3 * (Nat.log 2 r.2.1.length + 1) := by
  unfold designCase3a designSmallRank at h
  rw [decide_eq_true_eq, designRankWitness_length] at h
  have h1 := pow_lt_two_pow_log_succ r.2.1.length 7
  have h2 : 3 * designRank r ≤ 7 * (Nat.log 2 r.2.1.length + 1) :=
    (Nat.pow_le_pow_iff_right (by norm_num)).1 (h.trans h1)
  omega

/-- The skeleton rank is at most `2 (log₂ k + 1)`. -/
theorem designSkel_le_log (l : List ℕ) : designSkel l ≤ 2 * (Nat.log 2 l.length + 1) := by
  set t := 2 * (Nat.log 2 l.length + 1) with ht
  have hlog : Nat.log 2 l.length ≤ l.length := Nat.log_le_self 2 l.length
  have hmem : t ∈ designSkelCandidates l := by
    simp only [designSkelCandidates, List.mem_filter, List.mem_range, designSkelPass,
      decide_eq_true_eq]
    refine ⟨by omega, ?_⟩
    rw [min_eq_left (by omega)]
    refine (pow_lt_two_pow_log_succ l.length 7).trans (Nat.pow_le_pow_right (by norm_num) ?_)
    omega
  have hne : designSkelCandidates l ≠ [] := by intro hh; simp [hh] at hmem
  exact (upccCaseLeast_spec _ hne).2 t hmem

theorem designCallWitness_length_le (r : RawUpccCase) :
    (designCallWitness r).length ≤ 3 * (Nat.log 2 r.2.1.length + 1) := by
  unfold designCallWitness
  split
  next h => rw [designRankWitness_length]; exact designRank_le_of_case3a h
  next =>
    unfold designSkelWitness
    rw [List.length_take]
    have := designSkel_le_log r.2.1
    omega

/-! ## The number of versions of the design call -/

theorem length_tabRead (s : List ℕ × List (List ℕ)) : (tabRead s).2.length = s.2.length := by
  simp [tabRead]

/-- The rows of the table of the design call: at most `|dom| ^ |witness|`. -/
theorem length_aggTable_le (c : ℕ) (a : RawAggTestInput) :
    (aggTable c a).2.length ≤ (a.2.2.length + 1) ^ a.1.length := by
  unfold aggTable aggTabSetUp
  split
  next hg =>
    rw [tabStep_iterate, length_tabRead, length_tuplesOf]
    exact Nat.pow_le_pow_left (Nat.le_succ _) _
  next =>
    simp only [Function.iterate_zero, id, length_tabRead, List.length_nil]
    exact Nat.zero_le _

theorem length_designCase3Graphs_le (r : RawUpccCase) :
    (designCase3Graphs r).length ≤
      (r.2.2.length + 1) ^ (3 * (Nat.log 2 r.2.1.length + 1)) := by
  unfold designCase3Graphs designCase3GraphMap designCallReadFamily ambientDesignReadFamily
  rw [List.length_map, List.length_map]
  unfold ambientDesignVersions
  cases hp : ambientDesignProcedure 3 (designCallGIn r) with
  | none => simp
  | some xs =>
    simp only [Option.elim_some]
    unfold ambientDesignVersionsAt ambientDesignVersionRows
    refine (List.length_filter_le _ _).trans ?_
    rw [List.length_map]
    refine (length_aggTable_le 3 _).trans ?_
    simp only [designCallGIn, List.length_range, List.length_take]
    refine (Nat.pow_le_pow_right (Nat.succ_pos _) (min_le_right _ _)).trans ?_
    exact Nat.pow_le_pow_right (Nat.succ_pos _) (designCallWitness_length_le r)

/-! ## The number of entries of step 9 -/

/-- The bound on the number of entries of one turn: `(k₂ + 1) ^ (3 (log₂ k₁ + 1))`, where
`k₁ k₂` are the sizes of the two parts. -/
def turnWidth (k₁ k₂ : ℕ) : ℕ := (k₂ + 1) ^ (3 * (Nat.log 2 k₁ + 1))

theorem le_turnWidth (k₁ k₂ : ℕ) : k₂ + 1 ≤ turnWidth k₁ k₂ := by
  unfold turnWidth
  calc k₂ + 1 = (k₂ + 1) ^ 1 := (pow_one _).symm
    _ ≤ _ := Nat.pow_le_pow_right (Nat.succ_pos _) (by omega)

theorem length_impStep2Graphs_le (r : RawUpccCase) :
    (impStep2Graphs r).length ≤ r.2.2.length + 1 := by
  unfold impStep2Graphs
  split
  · simp
  · rw [List.length_map]
    refine (List.length_filter_le _ _).trans ?_
    unfold impGroups
    refine (length_dedupG_le _).trans ?_
    simp

theorem length_sbipTurnCases_le (z : RawSbipTurnCase) :
    (sbipTurnCases z).length ≤ turnWidth z.2.1.2.1.length z.2.1.2.2.length := by
  have hw := le_turnWidth z.2.1.2.1.length z.2.1.2.2.length
  unfold sbipTurnCases
  split
  · unfold sbipTurnImp
    split
    · rw [List.length_map]; omega
    · rw [List.length_map]; have := length_impStep2Graphs_le z.2.1; omega
  · split
    · unfold sbipTurnDesign
      cases designCase12 z.2 with
      | none =>
        simp only [Option.elim_none]
        unfold sbipTurnDesign3
        rw [List.length_map]
        exact length_designCase3Graphs_le z.2.1
      | some o => simp only [Option.elim_some, List.length_singleton]; omega
    · unfold sbipTurnUpccFamily
      rw [List.length_map]; omega

theorem length_sbipTurnChildren_le (L : List RawSbipTurnEntry) :
    (sbipTurnChildren L).length ≤ L.length := by
  unfold sbipTurnChildren
  rw [List.length_map]
  exact List.length_filter_le _ _

theorem turnWidth_mono {a a' b b' : ℕ} (ha : a ≤ a') (hb : b ≤ b') :
    turnWidth a b ≤ turnWidth a' b' := by
  unfold turnWidth
  calc (b + 1) ^ (3 * (Nat.log 2 a + 1)) ≤ (b' + 1) ^ (3 * (Nat.log 2 a + 1)) :=
        Nat.pow_le_pow_left (by omega) _
    _ ≤ (b' + 1) ^ (3 * (Nat.log 2 a' + 1)) :=
        Nat.pow_le_pow_right (by omega) (by have := Nat.log_mono_right (b := 2) ha; omega)

/-- **The width of a node of Section 9, explicitly**: a represented node on `m` points stores
at most `(m + 1) ^ (3 (log₂ m + 1))` children. -/
theorem sbipNodeGraphs_length_le {m : ℕ} {I : RawSbipNode} (h : SbipNodeValid m I) (c : ℕ) :
    (sbipNodeGraphs c I).length ≤ turnWidth m m := by
  obtain ⟨X, hX⟩ := h
  rcases sbipNodeGraphs_cases_or_empty c I with he | ⟨-, he⟩
  · rw [he]; exact Nat.zero_le _
  · rw [he]
    refine (length_sbipTurnChildren_le _).trans ((length_sbipTurnCases_le _).trans ?_)
    apply turnWidth_mono
    · change ((List.range (sbipGraphConstituent (sbipTurnGraphInput I.1)).1.1.length).map
        _).length ≤ m
      rw [List.length_map, List.length_range]
      have hl := sbipGraphConstituent_left_length (sbipTurnGraphInput I.1)
      have hp := hX.first_length_le
      change (sbipTurnGraphInput I.1).1.1.1.length ≤ m at hp
      omega
    · change (List.range (sbipGraphConstituent (sbipTurnGraphInput I.1)).1.2.1.length).length
        ≤ m
      rw [List.length_range]
      have hr := sbipGraphConstituent_right_length (sbipTurnGraphInput I.1)
      have hb := hX.blocks_le
      change (sbipTurnGraphInput I.1).1.1.2.1.length ≤ m at hb
      omega

/-- The width in the two-scale form: `(m+1)^{3(log₂ m+1)} ≤ 2^{3(log₂ m+1)^2}`. -/
theorem turnWidth_le_two_pow (m : ℕ) :
    turnWidth m m ≤ 2 ^ (3 * (Nat.log 2 m + 1) ^ 2) := by
  unfold turnWidth
  have h : m + 1 ≤ 2 ^ (Nat.log 2 m + 1) := Nat.lt_pow_succ_log_self (by norm_num) m
  calc (m + 1) ^ (3 * (Nat.log 2 m + 1)) ≤ (2 ^ (Nat.log 2 m + 1)) ^ (3 * (Nat.log 2 m + 1)) :=
        Nat.pow_le_pow_left h _
    _ = 2 ^ (3 * (Nat.log 2 m + 1) ^ 2) := by rw [← pow_mul]; ring_nf

end Explicit
