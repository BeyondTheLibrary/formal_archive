import Workspace.Algo.AggNodeRestorePartition
import Workspace.Algo.TestSetNaming

/-! Every valid local answer becomes an Align-admissible answer on the full
original domain. The bound `11m ≤ 15|D|` covers Case 2b's deleted points as
well as Case 3's larger fixed set. It gives Johnson threshold `11/20`, while
a partition keeps threshold `3/4` after adding the complement block.
-/
namespace Algo
open Babai RAM
open scoped Classical

variable {m : ℕ} {D : List ℕ}

theorem aggnDecAlignPartition_valid {k : ℕ} (P : RawColPart) {α : ℝ}
    (h : IsSplitOutcome α Set.univ (decAlignPartition k P)) :
    (decColPartition k P).IsAlphaPartition α := by
  apply ColoredPartition.isAlphaPartition_of_kernel_rel
    (show ColoredPartition ↥(Set.univ : Set (Fin k)) ℕ from
      {color := fun x => (decColPartition k P).color x.val
       part := Setoid.comap Subtype.val (decColPartition k P).part
       part_le_color := fun h => (decColPartition k P).part_le_color h})
    (decColPartition k P) (Equiv.Set.univ (Fin k))
  · intro x y; rfl
  · intro x y; rfl
  · convert h.2 using 1

theorem aggnRestorePartition_valid (hnd : D.Nodup) (hlt : ∀ a ∈ D, a < m)
    (hlarge : 11*m ≤ 15*D.length) (P : RawColPart)
    (hP : (decColPartition D.length P).IsAlphaPartition (3/4 : ℝ)) :
    ∃ β : ℝ, 1/2 < β ∧ 0 ≤ β ∧ 5*β ≤ 4 ∧
      IsSplitOutcome β Set.univ (decAlignPartition m (rawExtendPartition ((List.range m,D),P))) := by
  rw [aggnRestorePartition_eq hnd hlt]
  have hd := ncard_winSet D hnd hlt
  have hle := length_le_of_nodup_lt hnd hlt
  have hl : (11 : ℝ)*m ≤ 15*D.length := by exact_mod_cast hlarge
  have hu : (D.length : ℝ) ≤ m := by exact_mod_cast hle
  apply isSplitOutcome_extendOutcome_of (α := (3/4 : ℝ)) (βJ := (11/20 : ℝ))
    (βP := (3/4 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  · rw [hd]; linarith
  · rw [hd]; linarith
  · rw [hd]; linarith
  · refine ⟨rfl,?_⟩
    convert aggnLocalPartition_valid hnd hlt P hP using 1

theorem aggnRestoreJohnson_card {ms ts : ℕ} {J : RawJohnson}
    (hnd : D.Nodup) (hlt : ∀ a ∈ D, a < m) (h : J.WF D.length ms ts) :
    (RawJohnson.carrier m (aggnRestoreJohnson (D,J))).ncard =
      (RawJohnson.carrier D.length J).ncard := by
  have hr := aggnRestoreJohnson_wf hnd hlt h
  change (winSet m (aggnRestoreJohnson (D,J)).1).ncard = (winSet D.length J.1).ncard
  rw [ncard_winSet _ hr.wNodup hr.wLt,ncard_winSet _ h.wNodup h.wLt]
  exact length_rawRestrictStr D J.1

theorem aggnRestoreJohnson_valid {ms ts : ℕ} {J : RawJohnson}
    (hnd : D.Nodup) (hlt : ∀ a ∈ D, a < m) (hlarge : 11*m ≤ 15*D.length)
    (h : J.WF D.length ms ts) (hJ : IsSplitOutcome (3/4 : ℝ) Set.univ (decAlignJohnson J h)) :
    IsSplitOutcome (11/20 : ℝ) Set.univ
      (decAlignJohnson (aggnRestoreJohnson (D,J)) (aggnRestoreJohnson_wf hnd hlt h)) := by
  refine ⟨Set.subset_univ _,?_⟩
  change (11/20 : ℝ) * (Set.univ : Set (Fin m)).ncard ≤
    (RawJohnson.carrier m (aggnRestoreJohnson (D,J))).ncard
  rw [aggnRestoreJohnson_card hnd hlt h]
  have hh : (3/4 : ℝ) * (Set.univ : Set (Fin D.length)).ncard ≤
      (RawJohnson.carrier D.length J).ncard := hJ.2
  simp only [Set.ncard_univ,Nat.card_fin] at hh ⊢
  have hl : (11 : ℝ)*m ≤ 15*D.length := by exact_mod_cast hlarge
  linarith

/-- Decoding a valid recursive answer remains successful after restoration, and
its threshold lies in the interval required by Procedure Align. -/
theorem aggnRestoreOutcome_valid (hnd : D.Nodup) (hlt : ∀ a ∈ D, a < m)
    (hlarge : 11*m ≤ 15*D.length) (dom : List ℕ) (hdom : dom.length = m)
    {r : RawAlignOutcome} {Z : Pt (SplitOutcomes (Fin D.length))}
    (hdec : decAlignOutcome D.length r = some Z)
    (hZ : IsSplitOutcome (3/4 : ℝ) Set.univ Z) :
    ∃ (β : ℝ) (Z' : Pt (SplitOutcomes (Fin m))),
      decAlignOutcome m (aggnRestoreOutcome ((dom,D),r)) = some Z' ∧
      1/2 < β ∧ 0 ≤ β ∧ 5*β ≤ 4 ∧ IsSplitOutcome β Set.univ Z' := by
  rcases r with ⟨P,J⟩
  cases P with
  | none =>
    cases J with
    | none => simp [decAlignOutcome] at hdec
    | some J =>
      by_cases hj : J.WF D.length (rawJDeg J) J.2.1
      · have he : decAlignJohnson J hj = Z := by
          simpa only [decAlignOutcome,dif_pos hj,Option.some.injEq] using hdec
        subst Z
        refine ⟨11/20,_,aggnRestoreJohnson_decode hnd hlt hj dom,
          by norm_num,by norm_num,by norm_num,?_⟩
        exact aggnRestoreJohnson_valid hnd hlt hlarge hj hZ
      · simp only [decAlignOutcome,dif_neg hj] at hdec
        cases hdec
  | some P =>
    cases J with
    | none =>
      have he : decAlignPartition D.length P = Z := Option.some.inj hdec
      subst Z
      obtain ⟨β,hβ⟩ := aggnRestorePartition_valid hnd hlt hlarge P (aggnDecAlignPartition_valid P hZ)
      refine ⟨β,_,?_,hβ⟩
      change decAlignOutcome m (aggnRestoreOutcome ((dom,D),rawAlignPartition P)) = _
      rw [aggnRestoreOutcome_partition,hdom,decAlignOutcome_partition]
    | some J => simp [decAlignOutcome] at hdec

end Algo
