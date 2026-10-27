/-
An explicit running time for Theorem 1.1.1 (Babai, version 2.5), part 1: the count of the
recursion of Section 9 with an explicit fuel exponent. Not part of the faithful formalization.
-/
import Workspace.Explicit.Sec9Width
import Workspace.Algo.SplitBipRunExact
import Workspace.Algo.SplitSolverCanonical
import Workspace.Algo.TopMasterL57Final

/-!
# Section 9: the recursion fits in `roundCount 2`

`Algo.exists_sbipRun_count` gives *some* fuel exponent `t` with
`subSteps ≤ roundCount t (size I)`. With the explicit width of `Explicit.Sec9Width`
(`(m+1)^{3(log₂ m+1)} ≤ 2^{3(log₂ m+1)²}`), the count of `Algo.sbip_nodes_budget`,

`nodes ≤ (2N+1) · base^{14(log₂ N+1)+2}`,

is at most `2^{42(log₂ N+2)³+…}`, so `t = 2` suffices, and a fortiori `t = 3`
(`Algo.Round.roundCount t N = 3·2^{30(log₂ N+2)^{t+2}}+1`).

The exact run at the fixed exponents follows as in `Algo.exists_sbipRun_exact`, and with it
the parameter specifications of Section 9 at `t = 3`: `Algo.BipInputRunCanonical`,
`Algo.Line4cBounds` and `Algo.AggnRestoredEntryGood`.
-/

namespace Explicit

open Algo RAM Babai

/-- The arithmetic of the count: `3·(2N+1)·(W+1)^{14(log₂ N+1)+2}+1 ≤ roundCount 2 N` when
`W ≤ 2^{3(log₂ N+1)²}`. -/
theorem sbip_count_arith (N W : ℕ) (hW : W ≤ 2 ^ (3 * (Nat.log 2 N + 1) ^ 2)) :
    3 * ((2 * N + 1) * sbipBudgetBound (W + 1) N) + 1 ≤ Round.roundCount 2 N := by
  unfold sbipBudgetBound Round.roundCount
  set x := Nat.log 2 N + 1 with hx
  have hN : 2 * N + 1 ≤ 2 ^ (x + 1) := by
    have h : N < 2 ^ x := by rw [hx]; exact Nat.lt_pow_succ_log_self (by norm_num) N
    rw [pow_succ]; omega
  have hB : W + 1 ≤ 2 ^ (3 * x ^ 2 + 1) := by
    rw [pow_succ]
    have : 1 ≤ 2 ^ (3 * x ^ 2) := Nat.one_le_two_pow
    omega
  have hE : (x + 1) + (3 * x ^ 2 + 1) * (14 * x + 2) ≤ 30 * (x + 1) ^ (2 + 2) := by
    have e : 30 * (x + 1) ^ (2 + 2) = 30 * x ^ 4 + 120 * x ^ 3 + 180 * x ^ 2 + 120 * x + 30 := by
      ring
    have e2 : (x + 1) + (3 * x ^ 2 + 1) * (14 * x + 2) = 42 * x ^ 3 + 6 * x ^ 2 + 15 * x + 3 := by
      ring
    rw [e, e2]
    nlinarith [Nat.zero_le (x ^ 4)]
  have hxl : Nat.log 2 N + 2 = x + 1 := by omega
  rw [hxl]
  apply Nat.add_le_add_right
  apply Nat.mul_le_mul_left
  calc (2 * N + 1) * (W + 1) ^ (14 * x + 2)
      ≤ 2 ^ (x + 1) * (2 ^ (3 * x ^ 2 + 1)) ^ (14 * x + 2) :=
        Nat.mul_le_mul hN (Nat.pow_le_pow_left hB _)
    _ = 2 ^ ((x + 1) + (3 * x ^ 2 + 1) * (14 * x + 2)) := by rw [← pow_mul, ← pow_add]
    _ ≤ 2 ^ (30 * (x + 1) ^ (2 + 2)) := Nat.pow_le_pow_right (by norm_num) hE

/-- **The count of Section 9 with fuel exponent `2`** (the explicit form of
`Algo.exists_sbipRun_count`). -/
theorem sbipRun_count_two (c : ℕ) :
    ∀ m I, SbipNodeValid m I → ∀ f,
      (sbipRound c).subSteps f I ≤ Round.roundCount 2 (Enc.size I) := by
  intro m I hI f
  obtain ⟨X, hX⟩ := hI
  set N := Enc.size I with hNdef
  have hres := hX.resources
  set W := turnWidth N N with hWdef
  have hb : 1 ≤ W + 1 := by omega
  have hw : ∀ J, SbipResources m N J → (sbipNodeGraphs c J).length ≤ W + 1 := by
    intro J hJ
    exact ((sbipNodeGraphs_length_le hJ.valid c).trans
      (turnWidth_mono hJ.degree hJ.degree)).trans (Nat.le_succ _)
  have hn := sbip_nodes_budget c m N (W + 1) hb hw f I hres
  have hm : sbipNodeMeasure I ≤ 2 * N + 1 := by
    have hh := hX.blocks_le.trans hres.degree
    have hi := sbipNodeBit_le I
    unfold sbipNodeMeasure
    omega
  have hbudget := sbipBudget_le hb (hX.blocks_le.trans hres.degree) (sbipNodeBit_le I)
  have hnodes : (sbipRound c).nodes f I ≤ (2 * N + 1) * sbipBudgetBound (W + 1) N :=
    hn.trans (Nat.mul_le_mul hm hbudget)
  have hs := (sbipRound c).subSteps_le f I
  have ha := sbip_count_arith N W (turnWidth_le_two_pow N)
  omega

theorem roundCount_mono_left {t t' : ℕ} (h : t ≤ t') (N : ℕ) :
    Round.roundCount t N ≤ Round.roundCount t' N := by
  unfold Round.roundCount
  have h1 : (Nat.log 2 N + 2) ^ (t + 2) ≤ (Nat.log 2 N + 2) ^ (t' + 2) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have h2 := Nat.pow_le_pow_right (n := 2) (by norm_num) (Nat.mul_le_mul_left 30 h1)
  omega

/-- **The count of Section 9 with fuel exponent `3`**, the value of `Explicit.Params.t` and
`Explicit.Params.tt`. -/
theorem sbipRun_count_three (c : ℕ) :
    ∀ m I, SbipNodeValid m I → ∀ f,
      (sbipRound c).subSteps f I ≤ Round.roundCount 3 (Enc.size I) :=
  fun m I hI f => (sbipRun_count_two c m I hI f).trans (roundCount_mono_left (by norm_num) _)

/-! ## The exact run at `t = 3` -/

/-- `Algo.exists_sbipRun_exact` at the fuel exponent `3`. -/
theorem exists_sbipRun_exact_three (c : ℕ) :
    ∃ d, ∀ m I, SbipNodeValid m I → ∀ f, sbipNodeMeasure I < f →
      sbipRun c 3 d I = some ((sbipRound c).value f I) := by
  obtain ⟨B, hB, hb⟩ := exists_sbipOrbit_envelope c (Round.roundCount 3)
    (Round.quasiPolyBound_roundCount 3)
  obtain ⟨d, hd⟩ := hB
  refine ⟨d, ?_⟩
  intro m I hI f hf
  apply sbipRun_eq_value c 3 d f I hf (sbipRun_count_three c m I hI f)
  intro k hk hcount
  exact (hb m I hI k hcount).trans (hd _)

/-- Theorem 9.2.2 on the RAM at `t = 3` (as `Algo.exists_bipInputRun_valid_canonical`), for a
cap `d` at which the run is exact. -/
theorem bipInputRun_valid_canonical_of_exact {c d : ℕ}
    (he : ∀ m I, SbipNodeValid m I → ∀ f, sbipNodeMeasure I < f →
      sbipRun c 3 d I = some ((sbipRound c).value f I)) :
    BipInputRunGood c 3 d ∧ BipInputRunCanonical c 3 d := by
  refine ⟨?_, bipInputRun_canonical_of_sbip (sbipRun_canonical_of_exact he)⟩
  intro m r X h
  have hI : SbipNodeValid m (bipInputNode r) := ⟨bipToBlkObj X, h.node⟩
  let f := sbipNodeMeasure (bipInputNode r) + 1
  have hA := he m (bipInputNode r) hI f (Nat.lt_succ_self _)
  have hgood := sbipValue_valid_nonempty (c := c) hI (Nat.lt_succ_self (sbipNodeMeasure (bipInputNode r)))
  exact ⟨_, hA, hgood.1, fun o ho => hgood.2 (bipToBlkObj X) h.node o ho⟩

/-- Theorem 9.2.2 on the RAM at `t = 3` (as `Algo.exists_bipInputRun_valid_canonical`). -/
theorem exists_bipInputRun_valid_canonical_three (c : ℕ) :
    ∃ d, BipInputRunGood c 3 d ∧ BipInputRunCanonical c 3 d := by
  obtain ⟨d, he⟩ := exists_sbipRun_exact_three c
  exact ⟨d, bipInputRun_valid_canonical_of_exact he⟩

/-- Theorem 9.2.3 on the RAM at `t = 3`, for a cap `d` at which the run is exact: the validity
half of `Algo.exists_extendedSplitFamily_valid_canonical`, with the same proof. -/
theorem extendedSplitFamily_valid_of_exact {c d : ℕ}
    (he : ∀ m I, SbipNodeValid m I → ∀ f, sbipNodeMeasure I < f →
      sbipRun c 3 d I = some ((sbipRound c).value f I)) :
    BipInputRunCanonical c 3 d ∧ ∀ a,
      (∀ n g, ExtendedInputRep a n g →
        (∃ p, p ∈ extendedSplitFamily a c 3 d g) ∧
        ∀ p ∈ extendedSplitFamily a c 3 d g, ∃ Z, decAlignOutcome n p = some Z ∧
          IsSplitOutcome (sbipAlphaValue g.2) Set.univ Z) := by
  obtain ⟨hgood, hcan⟩ := bipInputRun_valid_canonical_of_exact he
  have hsolver := upccSplitFamilyGood_of_bip hgood
  refine ⟨hcan, fun a => ?_⟩
  intro n g h
  constructor
  · obtain ⟨⟨xs, o⟩, ho⟩ := h.read_nonempty
    obtain ⟨p, hp⟩ := (extendedSplitBranch_valid hsolver h ho).1
    exact ⟨p, List.mem_flatMap.2 ⟨(xs, o), ho, hp⟩⟩
  · intro p hp
    obtain ⟨⟨xs, o⟩, ho, hp⟩ := List.mem_flatMap.1 hp
    exact (extendedSplitBranch_valid hsolver h ho).2 p hp

/-- Theorem 9.2.3 on the RAM at `t = 3`: the validity half of
`Algo.exists_extendedSplitFamily_valid_canonical`, with the same proof. -/
theorem exists_extendedSplitFamily_valid_three (c : ℕ) :
    ∃ d, BipInputRunCanonical c 3 d ∧ ∀ a,
      (∀ n g, ExtendedInputRep a n g →
        (∃ p, p ∈ extendedSplitFamily a c 3 d g) ∧
        ∀ p ∈ extendedSplitFamily a c 3 d g, ∃ Z, decAlignOutcome n p = some Z ∧
          IsSplitOutcome (sbipAlphaValue g.2) Set.univ Z) := by
  obtain ⟨d, he⟩ := exists_sbipRun_exact_three c
  exact ⟨d, extendedSplitFamily_valid_of_exact he⟩

/-- **The bounds of line 4c at `tt = 3`**, for a cap at which the run is exact. -/
theorem line4cBounds_of_exact {c dd : ℕ}
    (he : ∀ m I, SbipNodeValid m I → ∀ f, sbipNodeMeasure I < f →
      sbipRun c 3 dd I = some ((sbipRound c).value f I)) : Line4cBounds c 3 dd := by
  obtain ⟨hcan, h⟩ := extendedSplitFamily_valid_of_exact he
  exact ⟨hcan, h 1⟩

/-- **The bounds of line 4c at `tt = 3`** (`Algo.exists_line4cBounds` at a fixed exponent). -/
theorem exists_line4cBounds_three (c : ℕ) : ∃ dd, Line4cBounds c 3 dd := by
  obtain ⟨d, he⟩ := exists_sbipRun_exact_three c
  exact ⟨d, line4cBounds_of_exact he⟩

/-- **The constants of Section 9 for lines 5–7 at `t = 3`**, for a cap at which the run is
exact. -/
theorem restoredEntry_good_bip_of_exact {b d : ℕ}
    (he : ∀ m I, SbipNodeValid m I → ∀ f, sbipNodeMeasure I < f →
      sbipRun b 3 d I = some ((sbipRound b).value f I)) :
    BipInputRunCanonical b 3 d ∧ ∀ c, AggnRestoredEntryGood c b 3 d := by
  obtain ⟨hcan, hfam⟩ := extendedSplitFamily_valid_of_exact he
  refine ⟨hcan, fun c => ?_⟩
  intro m dom a hdom hnd hlt hlarge hI
  obtain ⟨hne, hgood⟩ := hfam (c + 1) a.1.length (a.2, (3, 4)) hI
  constructor
  · obtain ⟨o, ho⟩ := hne
    exact ⟨_, List.mem_map_of_mem ho⟩
  · intro o ho
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 ho
    obtain ⟨Z, hdec, hZ⟩ := hgood p hp
    exact aggnRestoreOutcome_valid hnd hlt hlarge dom hdom hdec hZ

/-- **The constants of Section 9 for lines 5–7 at `t = 3`** (`Algo.exists_restoredEntry_good_bip`
at a fixed exponent). -/
theorem exists_restoredEntry_good_bip_three (b : ℕ) :
    ∃ d, BipInputRunCanonical b 3 d ∧ ∀ c, AggnRestoredEntryGood c b 3 d := by
  obtain ⟨d, he⟩ := exists_sbipRun_exact_three b
  exact ⟨d, restoredEntry_good_bip_of_exact he⟩

end Explicit
