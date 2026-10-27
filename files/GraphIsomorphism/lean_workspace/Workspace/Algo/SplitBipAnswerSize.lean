import Workspace.Algo.SplitBipNodeRaw
import Workspace.Algo.DesignOut

/-! Extending a partition keeps one label per parent point and adds one
to each retained label. Johnson data pass through unchanged. This bounds
successive extensions without composing a size polynomial at every level. -/
namespace Algo
open RAM Babai

def SbipOutcomeSize (L b : ℕ) (o : RawAlignOutcome) : Prop :=
  (∀ P,o.1 = some P → P.1.length ≤ L ∧ P.2.length ≤ L ∧
    ∀ a ∈ P.1 ++ P.2,Nat.size a ≤ b) ∧
  (∀ J,o.2 = some J → Enc.size J ≤ L)

theorem sbipOutcomeSize_of_size {L : ℕ} {o : RawAlignOutcome} (h : Enc.size o ≤ L) :
    SbipOutcomeSize L L o := by
  constructor
  · intro P hp
    have hh := (Combine.size_fst_le o.1 o.2).trans h
    rw [hp,size_some_eq] at hh
    have h1 := Combine.size_fst_le P.1 P.2
    have h2 := Combine.size_snd_le P.1 P.2
    change Enc.size P.1 ≤ Enc.size P at h1
    change Enc.size P.2 ≤ Enc.size P at h2
    have hl := length_le_size P.1
    have hr := length_le_size P.2
    refine ⟨by omega,by omega,?_⟩
    intro a ha
    rcases List.mem_append.1 ha with ha | ha
    · have hh' := size_mem_le ha
      rw [Small.size_nat] at hh'
      omega
    · have hh' := size_mem_le ha
      rw [Small.size_nat] at hh'
      omega
  · intro J hj
    have hh := (Combine.size_snd_le o.1 o.2).trans h
    rw [hj,size_some_eq] at hh
    omega

theorem SbipOutcomeSize.mono {L b L' b' : ℕ} {o : RawAlignOutcome}
    (h : SbipOutcomeSize L b o) (hL : L ≤ L') (hb : b ≤ b') :
    SbipOutcomeSize L' b' o := by
  refine ⟨?_,fun J hj => (h.2 J hj).trans hL⟩
  intro P hp
  obtain ⟨h1,h2,h3⟩ := h.1 P hp
  exact ⟨h1.trans hL,h2.trans hL,fun a ha => (h3 a ha).trans hb⟩

theorem sbip_size_succ_le (a : ℕ) : Nat.size (a+1) ≤ Nat.size a + 1 := by
  apply Nat.size_le.2
  have hh := Nat.lt_size_self a
  have hp : 0 < 2 ^ Nat.size a := Nat.two_pow_pos _
  rw [pow_succ]
  omega

theorem rawExtendLabels_bits (V W : List ℕ) (lab : RawLab) {b : ℕ}
    (hb : ∀ a ∈ lab,Nat.size a ≤ b) :
    ∀ a ∈ rawExtendLabels ((V,W),lab),Nat.size a ≤ b+1 := by
  intro a ha
  obtain ⟨x,hx,rfl⟩ := List.mem_map.1 ha
  unfold rawExtendLabel
  split
  · apply (sbip_size_succ_le _).trans
    apply Nat.add_le_add_right
    by_cases hi : rawLetterIndex (W,x) < lab.length
    · exact hb _ (by simpa only [labAt,List.getD_eq_getElem _ _ hi] using List.getElem_mem hi)
    · simp [labAt,hi]
  · simp

theorem sbipNodeLift_size_shape {L b : ℕ} (V W : List ℕ) {o : RawAlignOutcome}
    (hV : V.length ≤ L) (h : SbipOutcomeSize L b o) :
    SbipOutcomeSize L (b+1) (sbipNodeLift ((V,W),o)) := by
  refine ⟨?_,h.2⟩
  intro P hp
  cases he : o.1 with
  | none => simp [sbipNodeLift,he] at hp
  | some Q =>
    have heq : rawExtendPartition ((V,W),Q) = P := by
      simpa only [sbipNodeLift,he,Option.map_some,Option.some.injEq] using hp
    subst P
    obtain ⟨h1,h2,hb⟩ := h.1 Q he
    refine ⟨by simpa [rawExtendPartition,rawExtendLabels] using hV,
      by simpa [rawExtendPartition,rawExtendLabels] using hV,?_⟩
    intro a ha
    rcases List.mem_append.1 ha with ha | ha
    · exact rawExtendLabels_bits V W Q.1 (fun a ha => hb a (List.mem_append_left _ ha)) a ha
    · exact rawExtendLabels_bits V W Q.2 (fun a ha => hb a (List.mem_append_right _ ha)) a ha

def sbipOutcomeBound (L b : ℕ) : ℕ :=
  8 * (1+L*(2*(b+2)+1)) + 2*L + 8

theorem SbipOutcomeSize.size_le {L b : ℕ} {o : RawAlignOutcome}
    (h : SbipOutcomeSize L b o) : Enc.size o ≤ sbipOutcomeBound L b := by
  have hp : Enc.size o.1 ≤ 4*(1+L*(2*(b+2)+1))+2 := by
    cases he : o.1 with
    | none => rw [Round.size_none_eq]; omega
    | some P =>
      obtain ⟨h1,h2,hb⟩ := h.1 P he
      have hleft := size_list_le_of_entries P.1 (b+2) (fun a ha => by
        rw [Small.size_nat]; exact Nat.add_le_add_right (hb a (List.mem_append_left _ ha)) 2)
      have hright := size_list_le_of_entries P.2 (b+2) (fun a ha => by
        rw [Small.size_nat]; exact Nat.add_le_add_right (hb a (List.mem_append_right _ ha)) 2)
      have hl := Nat.mul_le_mul_right (2*(b+2)+1) h1
      have hr := Nat.mul_le_mul_right (2*(b+2)+1) h2
      have hh := Combine.size_pair_le P.1 P.2
      change Enc.size P ≤ _ at hh
      rw [size_some_eq]
      omega
  have hj : Enc.size o.2 ≤ L+2 := by
    cases he : o.2 with
    | none => rw [Round.size_none_eq]; omega
    | some J => rw [size_some_eq]; exact Nat.add_le_add_right (h.2 J he) 2
  have hh := Combine.size_pair_le o.1 o.2
  change Enc.size o ≤ _ at hh
  unfold sbipOutcomeBound
  omega

end Algo
