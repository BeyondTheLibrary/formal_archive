/-
An explicit running time for Theorem 1.1.1 (Babai, version 2.5), part 1: the number of
outcomes of the recursion of Section 9. Not part of the faithful formalization.
-/
import Workspace.Explicit.Sec9Count

/-!
# Section 9: the number of outcomes, in the degree

The family that Theorem 9.2.2 returns (on the RAM, `Algo.sbipRun`) is the list of all the
outcomes that the nodes of the recursion tree return, lifted to the root. At a valid node on
`m` points this list has at most

`(returns per node) · (nodes + 1) ≤ 2^{45 (log₂ m + 2)^3}`

entries for `c = 0` (`Explicit.sbipValue_length_le_zero`), where

* a node returns at most `sbipReturnsBound c m` outcomes (`(m+1)^{3(log₂ m+1)}` from step 9,
  and at most `(c+1)^c` and `(c log₂ m + 1)^{c log₂ m}` from steps 1 and 2);
* the tree below a node on `m` points has at most `(2m+1)·(W+1)^{14(log₂ m+1)+2}` nodes,
  where `W = (m+1)^{3(log₂ m+1)}` is the width (`Explicit.Sec9Width`).

These bounds are in the degree `m`, not in the encoded size of the node.
-/

namespace Explicit

open Algo RAM Babai

/-! ## The number of outcomes one node returns -/

theorem length_sbipNumberings_le' (c : ℕ) (p : List ℕ × List ℕ) :
    (sbipNumberings c p).length ≤ (p.2.length + 1) ^ p.2.length := by
  unfold sbipNumberings
  refine (List.length_filter_le _ _).trans ?_
  rw [List.length_map]
  refine (length_aggTable_le c _).trans ?_
  simp

/-- The returns of one turn: steps 1 and 2 (small parts) and step 9. -/
def sbipReturnsBound (c m : ℕ) : ℕ :=
  (c + 1) ^ c + (c * Nat.log 2 m + 1) ^ (c * Nat.log 2 m) + turnWidth m m

theorem length_sbipTurn_le {m : ℕ} {I : RawSbipNode} (h : SbipNodeValid m I) (c : ℕ) :
    (sbipTurn c I.1).length ≤ sbipReturnsBound c m := by
  obtain ⟨X, hX⟩ := h
  have hp := hX.first_length_le
  have hb := hX.blocks_le
  change (sbipTurnGraphInput I.1).1.1.1.length ≤ m at hp
  change (sbipTurnGraphInput I.1).1.1.2.1.length ≤ m at hb
  unfold sbipReturnsBound
  unfold sbipTurn
  split
  next h1 =>
    rw [List.length_map]
    unfold sbipGraphEarly1 sbipStep1Versions
    rw [List.length_map]
    refine (length_sbipNumberings_le' _ _).trans ?_
    unfold sbipGraphSmall1 at h1
    rw [decide_eq_true_eq] at h1
    change (I.1.2.1.1.1.1.length + 1) ^ I.1.2.1.1.1.1.length ≤ _
    have : (I.1.2.1.1.1.1.length + 1) ^ I.1.2.1.1.1.1.length ≤ (c + 1) ^ c :=
      (Nat.pow_le_pow_left (by omega) _).trans (Nat.pow_le_pow_right (by omega) h1)
    omega
  next h1 =>
    split
    next h2 =>
      rw [List.length_map]
      unfold sbipGraphEarly2 sbipStep2Versions
      rw [List.length_map]
      refine (length_sbipNumberings_le' _ _).trans ?_
      unfold sbipGraphSmall2 at h2
      rw [decide_eq_true_eq] at h2
      change (I.1.2.1.1.1.2.1.length + 1) ^ I.1.2.1.1.1.2.1.length ≤ _
      have hl : c * Nat.log 2 I.1.2.1.1.1.1.length ≤ c * Nat.log 2 m :=
        Nat.mul_le_mul_left c (Nat.log_mono_right hp)
      have : (I.1.2.1.1.1.2.1.length + 1) ^ I.1.2.1.1.1.2.1.length ≤
          (c * Nat.log 2 m + 1) ^ (c * Nat.log 2 m) :=
        (Nat.pow_le_pow_left (by omega) _).trans (Nat.pow_le_pow_right (by omega) (h2.trans hl))
      omega
    next h2 =>
      unfold sbipTurnLarge
      cases (sbipGraphSteps35 (sbipTurnGraphInput I.1)).2 with
      | none =>
        simp only [Option.elim_none, List.length_singleton]
        have := le_turnWidth m m; omega
      | some a =>
        simp only [Option.elim_some]
        unfold sbipTurnAfter35
        split
        · simp only [List.length_singleton]; have := le_turnWidth m m; omega
        · refine (length_sbipTurnCases_le _).trans ?_
          have : turnWidth (sbipTurnCase I.1).2.1.2.1.length (sbipTurnCase I.1).2.1.2.2.length
              ≤ turnWidth m m := by
            apply turnWidth_mono
            · change ((List.range (sbipGraphConstituent (sbipTurnGraphInput I.1)).1.1.length).map
                _).length ≤ m
              rw [List.length_map, List.length_range]
              have hl := sbipGraphConstituent_left_length (sbipTurnGraphInput I.1)
              omega
            · change (List.range
                (sbipGraphConstituent (sbipTurnGraphInput I.1)).1.2.1.length).length ≤ m
              rw [List.length_range]
              have hr := sbipGraphConstituent_right_length (sbipTurnGraphInput I.1)
              omega
          omega

theorem length_sbipNodeInit_le {m : ℕ} {I : RawSbipNode} (h : SbipNodeValid m I) (c : ℕ) :
    (sbipNodeInit c I).length ≤ sbipReturnsBound c m := by
  unfold sbipNodeInit sbipTurnReturns
  rw [List.length_map]
  exact (List.length_filter_le _ _).trans (length_sbipTurn_le h c)

/-! ## The value is at most the returns per node times the nodes -/

theorem length_sbipLoopAux_le (c : ℕ) (rec : RawSbipNode → RawSbipAnswers) (I : RawSbipNode) :
    ∀ (w j : ℕ) (s : RawSbipAnswers),
      ((sbipRound c).loopAux rec w I j s).length ≤
        s.length + (((sbipRound c).loopCalls rec w I j s).map (fun J => (rec J).length)).sum := by
  intro w
  induction w with
  | zero => intro j s; simp [Round.loopAux, sbipRound]
  | succ w ih =>
    intro j s
    cases hc : (sbipRound c).child (I, j, s) with
    | none =>
      rw [Round.loopAux_succ_none _ hc, Round.loopCalls_succ_none _ hc]
      simp [sbipRound]
    | some J =>
      rw [Round.loopAux_succ_some _ hc, Round.loopCalls_succ_some _ hc]
      refine (ih (j + 1) _).trans ?_
      have hcomb : ((sbipRound c).combine (I, j, s, rec J)).length = s.length + (rec J).length := by
        simp [sbipRound, sbipNodeCombine]
      rw [hcomb, List.map_cons, List.sum_cons]
      omega

/-- The value has at most `r · (nodes + 1)` outcomes when every node below returns at most
`r`. -/
theorem sbipValue_length_le (c m n r : ℕ) (hr : ∀ J, SbipResources m n J →
      (sbipNodeInit c J).length ≤ r) :
    ∀ f I, SbipResources m n I →
      ((sbipRound c).value f I).length ≤ r * ((sbipRound c).nodes f I + 1) := by
  intro f
  induction f with
  | zero => intro I _; simp [sbipRound]
  | succ f ih =>
    intro I hI
    rw [Round.value_succ, Round.nodes_succ]
    refine (length_sbipLoopAux_le c _ I _ 0 _).trans ?_
    change (sbipNodeInit c I).length + (((sbipRound c).roundCalls f I).map
      (fun J => ((sbipRound c).value f J).length)).sum ≤ _
    have h1 := hr I hI
    have h2 : (((sbipRound c).roundCalls f I).map
        (fun J => ((sbipRound c).value f J).length)).sum ≤
        (((sbipRound c).roundCalls f I).map (fun J => r * ((sbipRound c).nodes f J + 1))).sum := by
      apply List.sum_le_sum
      intro J hJ
      obtain ⟨k, t, hc⟩ := (sbipRound c).mem_roundCalls_child hJ
      exact ih J (hI.child hc)
    have h3 : (((sbipRound c).roundCalls f I).map (fun J => r * ((sbipRound c).nodes f J + 1))).sum
        = r * ((sbipRound c).roundCalls f I).length +
          r * (((sbipRound c).roundCalls f I).map ((sbipRound c).nodes f)).sum := by
      rw [← Nat.mul_add]
      induction ((sbipRound c).roundCalls f I) with
      | nil => simp
      | cons a l ihl =>
        simp only [List.map_cons, List.sum_cons, List.length_cons] at ihl ⊢
        rw [ihl]; ring
    rw [h3] at h2
    have : r * (((sbipRound c).roundCalls f I).length +
        (((sbipRound c).roundCalls f I).map ((sbipRound c).nodes f)).sum + 1) =
        r * ((sbipRound c).roundCalls f I).length +
          r * (((sbipRound c).roundCalls f I).map ((sbipRound c).nodes f)).sum + r := by ring
    rw [this]
    omega

/-- The tree below a valid node on `m` points, counted in `m`. -/
theorem sbip_nodes_le_degree (c : ℕ) {m : ℕ} {I : RawSbipNode} (hI : SbipNodeValid m I)
    (f : ℕ) :
    (sbipRound c).nodes f I ≤
      (2 * m + 1) * sbipBudgetBound (turnWidth m m + 1) m := by
  obtain ⟨X, hX⟩ := hI
  have hres := hX.resources
  have hb : 1 ≤ turnWidth m m + 1 := by omega
  have hw : ∀ J, SbipResources m (Enc.size I) J →
      (sbipNodeGraphs c J).length ≤ turnWidth m m + 1 :=
    fun J hJ => (sbipNodeGraphs_length_le hJ.valid c).trans (Nat.le_succ _)
  have hn := sbip_nodes_budget c m (Enc.size I) _ hb hw f I hres
  have hm : sbipNodeMeasure I ≤ 2 * m + 1 := by
    have hh := hX.blocks_le
    have hi := sbipNodeBit_le I
    unfold sbipNodeMeasure
    omega
  exact hn.trans (Nat.mul_le_mul hm (sbipBudget_le hb hX.blocks_le (sbipNodeBit_le I)))

/-- **The number of outcomes of the recursion of Section 9**, at a valid node on `m` points. -/
theorem sbipValue_length_le_degree (c : ℕ) {m : ℕ} {I : RawSbipNode} (hI : SbipNodeValid m I)
    (f : ℕ) :
    ((sbipRound c).value f I).length ≤ sbipReturnsBound c m *
      ((2 * m + 1) * sbipBudgetBound (turnWidth m m + 1) m + 1) := by
  obtain ⟨X, hX⟩ := hI
  refine (sbipValue_length_le c m (Enc.size I) _ (fun J hJ => length_sbipNodeInit_le hJ.valid c)
    f I hX.resources).trans ?_
  exact Nat.mul_le_mul_left _ (Nat.add_le_add_right (sbip_nodes_le_degree c ⟨X, hX⟩ f) 1)

/-- The closed form at `c = 0`: `2^{45 (log₂ m + 2)^3}`. -/
theorem sbip_outcomes_arith (m : ℕ) :
    sbipReturnsBound 0 m * ((2 * m + 1) * sbipBudgetBound (turnWidth m m + 1) m + 1) ≤
      2 ^ (45 * (Nat.log 2 m + 2) ^ 3) := by
  unfold sbipReturnsBound sbipBudgetBound
  simp only [pow_zero, zero_mul, zero_add]
  set x := Nat.log 2 m + 1 with hx
  have hW : turnWidth m m ≤ 2 ^ (3 * x ^ 2) := turnWidth_le_two_pow m
  have hN : 2 * m + 1 ≤ 2 ^ (x + 1) := by
    have h : m < 2 ^ x := by rw [hx]; exact Nat.lt_pow_succ_log_self (by norm_num) m
    rw [pow_succ]; omega
  have h1 : (1 : ℕ) ≤ 2 ^ (3 * x ^ 2) := Nat.one_le_two_pow
  have hB : turnWidth m m + 1 ≤ 2 ^ (3 * x ^ 2 + 1) := by rw [pow_succ]; omega
  have hR : 1 + 1 + turnWidth m m ≤ 2 ^ (3 * x ^ 2 + 2) := by
    rw [pow_add]; omega
  have hT : (2 * m + 1) * (turnWidth m m + 1) ^ (14 * x + 2) + 1 ≤
      2 ^ ((x + 1) + (3 * x ^ 2 + 1) * (14 * x + 2) + 1) := by
    have h2 : (2 * m + 1) * (turnWidth m m + 1) ^ (14 * x + 2) ≤
        2 ^ ((x + 1) + (3 * x ^ 2 + 1) * (14 * x + 2)) := by
      calc (2 * m + 1) * (turnWidth m m + 1) ^ (14 * x + 2)
          ≤ 2 ^ (x + 1) * (2 ^ (3 * x ^ 2 + 1)) ^ (14 * x + 2) :=
            Nat.mul_le_mul hN (Nat.pow_le_pow_left hB _)
        _ = _ := by rw [← pow_mul, ← pow_add]
    have h3 : (1 : ℕ) ≤ 2 ^ ((x + 1) + (3 * x ^ 2 + 1) * (14 * x + 2)) := Nat.one_le_two_pow
    have e := pow_succ 2 ((x + 1) + (3 * x ^ 2 + 1) * (14 * x + 2))
    omega
  have hxl : Nat.log 2 m + 2 = x + 1 := by omega
  rw [hxl]
  calc (1 + 1 + turnWidth m m) * ((2 * m + 1) * (turnWidth m m + 1) ^ (14 * x + 2) + 1)
      ≤ 2 ^ (3 * x ^ 2 + 2) * 2 ^ ((x + 1) + (3 * x ^ 2 + 1) * (14 * x + 2) + 1) :=
        Nat.mul_le_mul hR hT
    _ = 2 ^ ((3 * x ^ 2 + 2) + ((x + 1) + (3 * x ^ 2 + 1) * (14 * x + 2) + 1)) := by
        rw [← pow_add]
    _ ≤ 2 ^ (45 * (x + 1) ^ 3) := by
        apply Nat.pow_le_pow_right (by norm_num)
        have e1 : (3 * x ^ 2 + 2) + ((x + 1) + (3 * x ^ 2 + 1) * (14 * x + 2) + 1) =
            42 * x ^ 3 + 9 * x ^ 2 + 15 * x + 6 := by ring
        have e2 : 45 * (x + 1) ^ 3 = 45 * x ^ 3 + 135 * x ^ 2 + 135 * x + 45 := by ring
        rw [e1, e2]; omega

/-- **The outcomes of Section 9 at `c = 0`**: at most `2^{45 (log₂ m + 2)^3}`. -/
theorem sbipValue_length_le_zero {m : ℕ} {I : RawSbipNode} (hI : SbipNodeValid m I) (f : ℕ) :
    ((sbipRound 0).value f I).length ≤ 2 ^ (45 * (Nat.log 2 m + 2) ^ 3) :=
  (sbipValue_length_le_degree 0 hI f).trans (sbip_outcomes_arith m)

end Explicit
