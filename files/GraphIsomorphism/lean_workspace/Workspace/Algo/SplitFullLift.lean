import Workspace.Algo.SplitBipTurnLift
import Workspace.Algo.SplitBipNodeRAM
import Workspace.Algo.AggNodeRestorePartition

/-! The outer reductions extend a first-part partition to the complete
input domain by one complement block. Johnson answers already use the
original names, so their rows and carrier are retained. -/
namespace Algo
open Babai RAM
open scoped Classical

def splitFullLift (z : (List ℕ × List ℕ) × RawAlignOutcome) : RawAlignOutcome :=
  sbipNodeLift ((List.range z.1.1.length,z.1.2),z.2)

theorem polyFun_splitFullLift : PolyFun splitFullLift :=
  (((((polyFun_fst.comp polyFun_fst).comp polyFun_rangeLength).pair
    (polyFun_fst.comp polyFun_snd)).pair polyFun_snd).comp polyFun_sbipNodeLift)

theorem splitFullLift_decode {m : ℕ} (dom L : List ℕ) (hd : dom.length = m)
    (hn : L.Nodup) (hb : ∀ a ∈ L,a < m)
    {o : RawAlignOutcome} {Z : Pt (SplitOutcomes (Fin m))}
    (h : sbipDecodeNamed m L o = some Z) :
    decAlignOutcome m (splitFullLift ((dom,L),o)) = some (extendOutcome Z) := by
  rcases o with ⟨p,j⟩
  cases p with
  | some p =>
    cases j with
    | some j => simp [sbipDecodeNamed,decAlignOutcome] at h
    | none =>
      have hz := Option.some.inj ((sbipDecodeNamed_partition L hn hb p).symm.trans h)
      subst Z
      change decAlignOutcome m (rawAlignPartition
        (rawExtendPartition ((List.range dom.length,L),p))) = _
      rw [hd,decAlignOutcome_partition,aggnRestorePartition_eq hn hb]
      rfl
  | none =>
    cases j with
    | none => simp [sbipDecodeNamed,decAlignOutcome] at h
    | some j =>
      change decAlignOutcome m (rawAlignJohnson j) = some Z at h
      change (if hw : j.WF m (rawJDeg j) j.2.1 then
        some (decAlignJohnson j hw) else none) = some Z at h
      split at h
      next hw =>
        have hz := Option.some.inj h
        subst Z
        exact decAlignOutcome_johnson j hw
      next hw => cases h

/-- The threshold identity is precisely the transfer step of Lemma 9.3.1. -/
theorem splitExtendOutcome_valid {m : ℕ} {α β : ℝ} {W : Set (Fin m)}
    (ha : α ≤ 1) (hb : 1/2 ≤ β)
    (hbalance : α * (W.ncard : ℝ) = β * m)
    {Z : Pt (SplitOutcomes (Fin m))} (hZ : IsSplitOutcome α W Z) :
    IsSplitOutcome β Set.univ (extendOutcome Z) := by
  rcases Z with ⟨s,P|J⟩
  · rcases hZ with ⟨rfl,hP⟩
    refine ⟨rfl,?_⟩
    apply extendPartition.isAlphaPartition (Set.subset_univ _) (Fintype.ofFinite _)
      (Fintype.ofFinite _) P ha hb _ hP
    simpa only [Set.ncard_univ,Nat.card_fin] using hbalance
  · refine ⟨Set.subset_univ _,?_⟩
    simpa only [Set.ncard_univ,Nat.card_fin,← hbalance] using hZ.2

theorem splitFullLift_valid {m : ℕ} (dom L : List ℕ) (hd : dom.length = m)
    (hn : L.Nodup) (hb : ∀ a ∈ L,a < m) {α β : ℝ}
    (ha : α ≤ 1) (hβ : 1/2 ≤ β)
    (hbalance : α * ((winSet m L).ncard : ℝ) = β * m)
    {o : RawAlignOutcome} {Z : Pt (SplitOutcomes (Fin m))}
    (hdec : sbipDecodeNamed m L o = some Z) (hZ : IsSplitOutcome α (winSet m L) Z) :
    ∃ Z',decAlignOutcome m (splitFullLift ((dom,L),o)) = some Z' ∧
      IsSplitOutcome β Set.univ Z' :=
  ⟨extendOutcome Z,splitFullLift_decode dom L hd hn hb hdec,
    splitExtendOutcome_valid ha hβ hbalance hZ⟩

end Algo
