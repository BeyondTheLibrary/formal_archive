import Workspace.Algo.PrimitiveLine4cVersions
import Workspace.Algo.TopMasterRoute

/-! # Section 15, lines 4c–4d on the RAM, called from the Master's route

The Master's dispatcher (`masterHintRoute`) takes route `4` exactly when lines 2, 4, 4a and
4b have failed: the Johnson parameter `m` exceeds `ℓ = (log₂ n)³`, the primitive-case test
passes with arity `t ≠ 1`, and the relative symmetry defect of `H(x)` is at least `1/2`
(`masterHintRoute_line4cd`). This file is the node the dispatcher calls there:

* `masterLine4cInput` reads the node's input off the Master's input, and
  `quasiFun_masterLine4cVersions` is its RAM bound;
* `masterLine4c_facts` derives from route `4` what lines 4c–4d use: the primitive
  identification, `t ≥ 2`, `217 ≤ m ≤ n` and the large defect of `H(x)`;
* `masterLine4c_versions` is Theorem 9.2.3 on the RAM at line 4c (the canonical versions),
  and `masterLine4c_line4cdData` is the Master's round of lines 4c–4d built on them
  (Procedure Align, `Babai.nonempty_alignData_of_versions`).
-/

namespace Algo
open Babai RAM Equiv

/-- Line 4c's input, read off the Master's input: the top action with both strings, and
the standard-block arity `t` of the hint. -/
def masterLine4cInput (p : MasterHintInput) : RawLine4cIn := (masterHintTop p, p.2.2)

theorem polyFun_masterLine4cInput : PolyFun masterLine4cInput :=
  polyFun_masterHintTop.pair (polyFun_snd.comp polyFun_snd)

theorem quasiFun_masterLine4cVersions (c tt dd : ℕ) :
    QuasiFun (fun p => line4cVersions c tt dd (masterLine4cInput p)) :=
  polyFun_masterLine4cInput.comp_quasiFun (quasiFun_line4cVersions c tt dd)

/-- `C(m, 1) = m ≤ C(m, t)` for `1 ≤ t` and `4t < m`. -/
theorem le_choose_of_four_mul_lt {m t : ℕ} (ht : 1 ≤ t) (h4 : 4 * t < m) :
    m ≤ m.choose t := by
  induction t, ht using Nat.le_induction with
  | base => simp
  | succ k hk ih =>
    exact (ih (by omega)).trans (Nat.choose_le_succ_of_lt_half_left (by omega))

section Facts

variable (p : MasterHintInput) {n m : ℕ} {ϕ : decGroup n (masterHintTop p).1.1.2 →* Perm (Fin m)}
    (hp : RawAction.WF n m (masterHintTop p).1 ϕ)
    (hG : IsTransitive (decGroup n (masterHintTop p).1.1.2)) (hϕ : IsGiantRep ϕ)
    (hn : 64 ≤ n) (hroute : masterHintRoute p = 4)

include hp hG hϕ hn hroute

/-- Route `4` of the Master: lines 2, 4, 4a, 4b have failed. What lines 4c–4d need
follows: the primitive identification by `T(u)`, `t ≥ 2` (line 4a failed and `n > 1`),
`217 ≤ m` (line 2 failed), `m ≤ n` (`n = C(m, t)`), and a relative symmetry defect of
`H(x)` of at least `1/2` (line 4b failed). -/
theorem masterLine4c_facts :
    VeryLargeK m (maxOrbitLength (decGroup n (masterHintTop p).1.1.2)) ∧
    ∃ id : PrimitiveCaseId ϕ p.2.2, 2 ≤ p.2.2 ∧ 217 ≤ m ∧ m ≤ n ∧
      ¬ defect (colorAut p.2.2 (hyperColoring id (decStrN n (masterHintTop p).2.1))) < 1 / 2 := by
  obtain ⟨h2, h4, ht1, hsd⟩ := (masterHintRoute_line4cd p).1 hroute
  have hn' : p.1.1.length = n := hp.1
  have hm' : p.2.1.1.length = m := hp.2.1
  have hhuge : HugeM m (Nat.card (Fin n)) := by
    have h := masterHintRoute_huge (m := m) hm' (by rw [hn']; exact hn) (by omega)
    rwa [hn'] at h
  have hvl := veryLargeK_of_hugeM hG hhuge
  let id : PrimitiveCaseId ϕ p.2.2 := top4PrimitiveId hp hG hϕ hhuge h4
  have hc : n = m.choose p.2.2 := by
    have he := Nat.card_congr id.label
    rw [card_binom (Fin m) p.2.2] at he
    simpa only [Nat.card_eq_fintype_card, Fintype.card_fin] using he
  have hfour : 4 * p.2.2 < m := by simpa only [Fintype.card_fin] using id.four_t
  have ht0 : p.2.2 ≠ 0 := by
    intro h0
    rw [h0, Nat.choose_zero_right] at hc
    omega
  refine ⟨hvl, id, by omega, ?_, ?_, ?_⟩
  · have hL := six_le_natLog hn
    have hell : ellOf n < m := by rw [← hn', ← hm']; omega
    have h216 : 216 ≤ ellOf n := by
      rw [ellOf]
      calc 216 = 6 ^ 3 := by norm_num
        _ ≤ Nat.log 2 n ^ 3 := Nat.pow_le_pow_left hL 3
    omega
  · rw [hc]
    exact le_choose_of_four_mul_lt (by omega) hfour
  · intro hlt
    have h := primitiveSmallDefect_spec hp.1 hp.2.1 hp.2.2.2.2 hϕ hvl id (masterHintTop p).2.1
    simp only [map_encPerm_decPerm hp.2.2.1, map_encPerm_decPerm hp.2.2.2.1, Prod.mk.eta] at h
    rw [h.2 hlt] at hsd
    exact Bool.false_ne_true hsd.symm

variable {c tt dd : ℕ} (hb : Line4cBounds c tt dd)
    (hx : (masterHintTop p).2.1.length = n) (hy : (masterHintTop p).2.2.length = n)

include hb hx hy

/-- **Section 15, line 4c at route `4`**: the node's two lists are the canonical family of
versions of Theorem 9.2.3 at `x` and at `y` (`line4c_versions_spec`). -/
theorem masterLine4c_versions
    [inst : MulAction (Perm (Fin m)) (Pt (SplitOutcomes (Fin m)))]
    (hK : IsCatAction (SplitOutcomes (Fin m))) :
    let P := masterHintTop p
    IsCanonicalVersions ϕ (line4cVers c tt dd P.1 p.2.2 P.2.1 P.2.2 m) ∧
      (line4cVers c tt dd P.1 p.2.2 P.2.1 P.2.2 m (decStrN n P.2.1)).Nonempty ∧
      (∀ Z, Z ∈ line4cVers c tt dd P.1 p.2.2 P.2.1 P.2.2 m (decStrN n P.2.1) ↔
        ∃ o ∈ (line4cVersions c tt dd (masterLine4cInput p)).1, decAlignOutcome m o = some Z) ∧
      (∀ Z, Z ∈ line4cVers c tt dd P.1 p.2.2 P.2.1 P.2.2 m (decStrN n P.2.2) ↔
        primitiveSmallDefect (P.1, P.2.2) = false ∧
          ∃ o ∈ (line4cVersions c tt dd (masterLine4cInput p)).2, decAlignOutcome m o = some Z) ∧
      (∀ w : Fin n → ℕ, (line4cVers c tt dd P.1 p.2.2 P.2.1 P.2.2 m w).Finite) ∧
      (line4cVers c tt dd P.1 p.2.2 P.2.1 P.2.2 m (decStrN n P.2.2)).ncard ≤
        (line4cVersions c tt dd (masterLine4cInput p)).2.length ∧
      (∀ w : Fin n → ℕ, ∀ Z ∈ line4cVers c tt dd P.1 p.2.2 P.2.1 P.2.2 m w,
        IsSplitOutcome (3 / 4 : ℝ) (Set.univ : Set (Fin m)) Z) := by
  obtain ⟨hvl, id, ht2, -, -, hdef⟩ := masterLine4c_facts p hp hG hϕ hn hroute
  exact line4c_versions_spec hp hϕ hvl id hb hx hy ht2 hdef hK

/-- **Section 15, lines 4c–4d at route `4`**: the Master's round of Procedure Align on the
machine's versions. Its number of versions is the length of the node's list for `y`. -/
theorem masterLine4c_line4cdData :
    Nonempty (Line4cdData (Fin n) ℕ (decGroup n (masterHintTop p).1.1.2)
      (decStrN n (masterHintTop p).2.1) (decStrN n (masterHintTop p).2.2) m
      ((line4cVersions c tt dd (masterLine4cInput p)).2.length * (Fintype.card (Fin n) + 1) *
        AlignDominantRoundData.alignDominantRoundCost (Fintype.card (Fin n)))) := by
  obtain ⟨hvl, id, ht2, hm, hmn, hdef⟩ := masterLine4c_facts p hp hG hϕ hn hroute
  exact nonempty_line4cdData_ram hp hϕ hvl id hb hx hy hG ht2 hm hmn hdef

end Facts

end Algo

#print axioms Algo.quasiFun_masterLine4cVersions
#print axioms Algo.masterLine4c_versions
#print axioms Algo.masterLine4c_line4cdData
