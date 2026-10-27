import Workspace.Algo.SplitBipCaseSize

/-! The threshold is stored without cancelling factors. Its bit count
grows additively at each turn. Charging that growth to the decreasing
node measure gives one bound for every node in the actual recursion. -/
namespace Algo
open RAM Babai

def sbipNodeAlphaBits (I : RawSbipNode) : ℕ :=
  Nat.size I.1.2.2.1 + Nat.size I.1.2.2.2

def sbipNodeAlphaPotential (m : ℕ) (I : RawSbipNode) : ℕ :=
  sbipNodeAlphaBits I + sbipNodeMeasure I * (2 * Nat.size m)

namespace SbipNodeRep
variable {m : ℕ} {I : RawSbipNode} {X : Pt (BipBlockInputs (Fin m))}
    (h : SbipNodeRep m I X)
include h

theorem case_alpha_bits : Nat.size (sbipTurnCase I.1).2.2.1 +
    Nat.size (sbipTurnCase I.1).2.2.2 ≤ sbipNodeAlphaBits I + 2 * Nat.size m := by
  have hl := h.first_length_le
  have hd : (sbipDominant (sbipGraphClasses (sbipTurnGraphInput I.1))).length ≤ m :=
    (List.length_filter_le _ _).trans hl
  exact sbipAlphaUpdate_bits I.1.2.2 hl hd

theorem child_alpha_potential {c j : ℕ} {J : RawSbipNode}
    (hc : sbipNodeChild c (I,j) = some J) :
    sbipNodeAlphaPotential m J ≤ sbipNodeAlphaPotential m I := by
  obtain ⟨g,hg,rfl,hm⟩ := sbipNodeChild_some hc
  have hb := h.case_alpha_bits
  change sbipNodeAlphaBits (sbipNodeMakeChild (I,g)) ≤
    sbipNodeAlphaBits I + 2 * Nat.size m at hb
  have hmul := Nat.mul_le_mul_right (2 * Nat.size m)
    (show sbipNodeMeasure (sbipNodeMakeChild (I,g)) + 1 ≤ sbipNodeMeasure I by omega)
  unfold sbipNodeAlphaPotential
  nlinarith

theorem case_alpha_size : Enc.size (sbipTurnCase I.1).2.2 ≤
    2 * sbipNodeAlphaPotential m I + 4*m + 8 := by
  have hb := h.case_alpha_bits
  have hs := Combine.size_pair_le (sbipTurnCase I.1).2.2.1 (sbipTurnCase I.1).2.2.2
  change Enc.size (sbipTurnCase I.1).2.2 ≤ _ at hs
  rw [Small.size_nat,Small.size_nat] at hs
  have hn := size_le_self m
  unfold sbipNodeAlphaPotential
  omega

theorem node_alpha_size : Enc.size I.1.2.2 ≤ 2 * sbipNodeAlphaPotential m I + 8 := by
  have hs := Combine.size_pair_le I.1.2.2.1 I.1.2.2.2
  change Enc.size I.1.2.2 ≤ _ at hs
  rw [Small.size_nat,Small.size_nat] at hs
  unfold sbipNodeAlphaPotential sbipNodeAlphaBits
  omega

theorem case_total_size (hd : ¬ AllClassesSmall X) :
    Enc.size (sbipTurnCase I.1) ≤ 8 * Enc.size I.1.1 + 8 * sbipDictionaryBound m +
      4 * strBound m + 4 * sbipCaseSizeBound (2*m) +
      8 * sbipNodeAlphaPotential m I + 16*m + 32 := by
  have hw := Combine.size_pair_le (sbipTurnCase I.1).1.1.1 (sbipTurnCase I.1).1.1.2
  have hl := Combine.size_pair_le (sbipTurnCase I.1).1.1 (sbipTurnCase I.1).1.2
  have hr := Combine.size_pair_le (sbipTurnCase I.1).2.1 (sbipTurnCase I.1).2.2
  have ht := Combine.size_pair_le (sbipTurnCase I.1).1 (sbipTurnCase I.1).2
  change Enc.size (sbipTurnCase I.1).1.1 ≤ _ at hw
  change Enc.size (sbipTurnCase I.1).1 ≤ _ at hl
  change Enc.size (sbipTurnCase I.1).2 ≤ _ at hr
  change Enc.size (sbipTurnCase I.1) ≤ _ at ht
  have hd := h.case_dictionary_size hd
  have hp := size_natList_le h.first_length_le h.point_lt
  change Enc.size (sbipTurnCase I.1).1.2 ≤ strBound m at hp
  have hc := h.case_size
  have ha := h.case_alpha_size
  change Enc.size (sbipTurnCase I.1).1.1 ≤ 2*Enc.size I.1.1 + _ at hw
  omega

end SbipNodeRep
end Algo
