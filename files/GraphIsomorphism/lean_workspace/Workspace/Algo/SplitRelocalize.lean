import Workspace.Algo.SplitFullLift
import Workspace.Algo.AggNodeRestoreValidity

/-! A locally numbered UPCC answer is restored through its stored subset
list. Its adjusted threshold pays for the complement block exactly. -/
namespace Algo
open Babai RAM
open scoped Classical

theorem splitRestoreOutcome_valid {m : ℕ} {L : List ℕ}
    (hn : L.Nodup) (hb : ∀ a ∈ L,a < m) (dom : List ℕ) (hd : dom.length = m)
    {α β : ℝ} (ha : α ≤ 1) (hβ : 1/2 ≤ β)
    (hbalance : α * L.length = β * m)
    {o : RawAlignOutcome} {Z : Pt (SplitOutcomes (Fin L.length))}
    (hdec : decAlignOutcome L.length o = some Z) (hZ : IsSplitOutcome α Set.univ Z) :
    ∃ Z',decAlignOutcome m (aggnRestoreOutcome ((dom,L),o)) = some Z' ∧
      IsSplitOutcome β Set.univ Z' := by
  rcases o with ⟨p,j⟩
  cases p with
  | some p =>
    cases j with
    | some j => simp [decAlignOutcome] at hdec
    | none =>
      have hz : decAlignPartition L.length p = Z := Option.some.inj hdec
      subst Z
      refine ⟨_,aggnRestorePartition_decode hn hb dom hd p,?_⟩
      apply splitExtendOutcome_valid (W := winSet m L) ha hβ
      · simpa only [ncard_winSet L hn hb] using hbalance
      · refine ⟨rfl,?_⟩
        convert aggnLocalPartition_valid hn hb p (aggnDecAlignPartition_valid p hZ) using 1
  | none =>
    cases j with
    | none => simp [decAlignOutcome] at hdec
    | some j =>
      change (if hj : j.WF L.length (rawJDeg j) j.2.1 then
        some (decAlignJohnson j hj) else none) = some Z at hdec
      split at hdec
      next hj =>
        have hz := Option.some.inj hdec
        subst Z
        refine ⟨_,aggnRestoreJohnson_decode hn hb hj dom,Set.subset_univ _,?_⟩
        change β * (Set.univ : Set (Fin m)).ncard ≤
          (RawJohnson.carrier m (aggnRestoreJohnson (L,j))).ncard
        rw [aggnRestoreJohnson_card hn hb hj]
        have hh := hZ.2
        simpa only [Set.ncard_univ,Nat.card_fin,hbalance] using hh
      next hj => cases hdec

end Algo
