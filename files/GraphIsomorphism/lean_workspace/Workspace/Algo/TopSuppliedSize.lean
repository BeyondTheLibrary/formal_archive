import Workspace.Algo.TopSuppliedRAM

/-! # Uniform storage bounds for supplied top-action 3

Every coset is normalized against the source domain before it is retained.
Consequently the state bound holds after every update, with no assumption on
its incoming state or answer. The prepared context is charged separately by
its polynomial bound in the original domain size.
-/

namespace Algo

open RAM RAM.Targets

 theorem topcsFields_size (P : TopcsInput) :
    Enc.size (topcsX P) ≤ Enc.size P ∧ Enc.size (topcsY P) ≤ Enc.size P ∧
    Enc.size (topcsWins P) ≤ Enc.size P ∧ Enc.size (topcsTests P) ≤ Enc.size P := by
  have h1 := size_snd_le' P
  have h2 := le_trans (size_snd_le' P.2) h1
  have h3 := le_trans (size_snd_le' P.2.2) h2
  exact ⟨size_fst_le' P, le_trans (size_fst_le' P.2) h1,
    le_trans (size_fst_le' P.2.2) h2, le_trans (size_fst_le' P.2.2.2) h3⟩

 theorem topcsCount_le (P : TopcsInput) : topcsCount P ≤ Enc.size P :=
  le_trans (length_le_size _) (topcsFields_size P).2.2.2
 theorem topcsWins_length_le (P : TopcsInput) : (topcsWins P).length ≤ Enc.size P :=
  le_trans (length_le_size _) (topcsFields_size P).2.2.1

 theorem size_topcsBegin {n : ℕ} {P : TopcsInput} (hx : (topcsX P).length = n) (t : ℕ) :
    Enc.size (topcsBegin P t) ≤ chainBound n :=
  size_top2NormC_le hx le_rfl _

/-- The six fields that every raw update retains. -/
def TopcsStored (n : ℕ) (P : TopcsInput) (s : TopcsState) : Prop :=
  s.1 ≤ topcsJobs P ∧ s.2.1 ≤ (topcsWins P).length ∧
  Enc.size s.2.2.1 ≤ chainBound n ∧ Enc.size s.2.2.2.1 ≤ chainBound n + 2 ∧
  Enc.size s.2.2.2.2.1 ≤ chainBound n ∧ Enc.size s.2.2.2.2.2 ≤ chainBound n

 theorem topcsClose_stored {n : ℕ} {P : TopcsInput} (hx : (topcsX P).length = n)
    (t : ℕ) (A : Top1State) (B D a : RawCoset) :
    TopcsStored n P (topcsClose P t A B D a) := by
  have hc := fun c => size_top2NormC_le hx (le_refl n) c
  have hs := fun s => size_top2NormS_le hx (le_refl n) s
  have hb := size_topcsBegin hx
  unfold topcsClose
  split
  · rename_i ht
    exact ⟨by dsimp; unfold topcsJobs; omega, Nat.zero_le _, hb _, hs _, hc _, hc _⟩
  · split
    · refine ⟨?_, Nat.zero_le _, hb _, hs _, hc _, hc _⟩
      dsimp
      split <;> unfold topcsJobs <;> omega
    · split
      · refine ⟨?_, Nat.zero_le _, hb _, hs _, hc _, hc _⟩
        dsimp
        split <;> unfold topcsJobs <;> omega
      · exact ⟨le_rfl, Nat.zero_le _, hb _, hs _, hc _, hc _⟩

 theorem topcsStep_stored {n : ℕ} {P : TopcsInput} (hx : (topcsX P).length = n)
    (t i : ℕ) (A : Top1State) (B D a : RawCoset) :
    TopcsStored n P (topcsStep P t i A B D a) := by
  unfold topcsStep
  split
  · exact ⟨Nat.min_le_right _ _, Nat.min_le_right _ _,
      size_top2NormC_le hx le_rfl _, size_top2NormS_le hx le_rfl _,
      size_top2NormC_le hx le_rfl _, size_top2NormC_le hx le_rfl _⟩
  · exact topcsClose_stored hx t A B D a

 theorem topcsInit_stored {n : ℕ} {I : TopcsNode} (hx : (topcsX I.1).length = n) :
    TopcsStored n I.1 (topcsInit I) := by
  have h := chainBound_ge n
  refine ⟨Nat.zero_le _, Nat.zero_le _, size_topcsBegin hx _, ?_, ?_, ?_⟩
  · change Enc.size (some (none : RawCoset)) ≤ _
    rw [size_some_eq, size_none]; omega
  · change Enc.size (none : RawCoset) ≤ _
    rw [size_none]; omega
  · change Enc.size (none : RawCoset) ≤ _
    rw [size_none]; omega

/-- One polynomial bounds the node, state and answer. -/
def topcsBound (B : ℕ → ℕ) (n : ℕ) : ℕ := 256 * (B n + chainBound n + 4)

 theorem polyBound_topcsBound {B : ℕ → ℕ} (hB : PolyBound B) : PolyBound (topcsBound B) :=
  (polyBound_const 256).mul ((hB.add polyBound_chainBound).add (polyBound_const 4))

 theorem mono_topcsBound {B : ℕ → ℕ} (hB : Monotone B) : Monotone (topcsBound B) := by
  intro a b hab
  have := hB hab
  have := mono_chainBound hab
  unfold topcsBound
  omega

 theorem size_topcsStored {B : ℕ → ℕ} {n : ℕ} {P : TopcsInput} {s : TopcsState}
    (hP : Enc.size P ≤ B n) (hs : TopcsStored n P s) :
    Enc.size s ≤ topcsBound B n := by
  have ht := topcsCount_le P
  have hw := topcsWins_length_le P
  have h1 := size_nat_le_self s.1
  have h2 := size_nat_le_self s.2.1
  have h3 := size_top3State_le s
  rcases hs with ⟨hs1, hs2, hs3, hs4, hs5, hs6⟩
  unfold topcsJobs at hs1
  unfold topcsBound
  omega

 theorem size_topcsLeaf {n : ℕ} {P : TopcsInput} (hx : (topcsX P).length = n)
    (t i : ℕ) (c : RawGens × RawPerm) :
    Enc.size (topcsLeaf P t i c) ≤ 64 * (Enc.size P + chainBound n + 1) := by
  have hf := topcsFields_size P
  have hw : Enc.size ((topcsWins P).getD i []) ≤ Enc.size P + 1 := by
    by_cases hi : i < (topcsWins P).length
    · have hm : (topcsWins P).getD i [] ∈ topcsWins P := by
        rw [List.getD_eq_getElem _ _ hi]
        exact List.getElem_mem _
      have := size_mem_le hm
      omega
    · rw [List.getD_eq_default _ _ (by omega)]
      have : Enc.size ([] : List ℕ) = 1 := rfl
      omega
  have hg : Enc.size (tidyGens (topcsX P, c.1)) ≤ gensBound n :=
    size_gens_le' le_rfl (wf_tidyGens hx _) (length_tidyGens hx _)
  have hr : Enc.size (normPerm (topcsX P, c.2)) ≤ strBound n :=
    size_perm_le' le_rfl (wf_normPerm hx _)
  have hy : Enc.size (topcsTgt P t) ≤ Enc.size P := by
    unfold topcsTgt
    split <;> exact (by omega)
  have h1 := Combine.size_pair_le ((topcsWins P).getD i [])
    ((tidyGens (topcsX P, c.1), normPerm (topcsX P, c.2), topcsX P, topcsTgt P t) :
      RawGens × RawPerm × RawStr × RawStr)
  have h2 := Combine.size_pair_le (tidyGens (topcsX P, c.1))
    ((normPerm (topcsX P, c.2), topcsX P, topcsTgt P t) : RawPerm × RawStr × RawStr)
  have h3 := Combine.size_pair_le (normPerm (topcsX P, c.2))
    ((topcsX P, topcsTgt P t) : RawStr × RawStr)
  have h4 := Combine.size_pair_le (topcsX P) (topcsTgt P t)
  have hsg := strBound_le_gensBound n
  have hcb : chainBound n = 16 * (gensBound n + n + 1) := rfl
  change Enc.size (((topcsWins P).getD i [], tidyGens (topcsX P, c.1),
    normPerm (topcsX P, c.2), topcsX P, topcsTgt P t) : RawWinSI) ≤ _
  omega

 theorem size_topcsNode {B : ℕ → ℕ} {n : ℕ} {I : TopcsNode} (hI : TopcsWF n B I) :
    Enc.size I ≤ topcsBound B n := by
  have hp : Enc.size I ≤ 2 * Enc.size I.1 + 2 * Enc.size I.2 := size_pair_le' I
  obtain ⟨hx, hP, hleaf⟩ := hI
  cases ho : I.2 with
  | none =>
    have hs : Enc.size I.2 = 2 := by rw [ho, size_none]
    unfold topcsBound
    omega
  | some W =>
    obtain ⟨t, i, c, rfl⟩ := hleaf W ho
    have hs := size_topcsLeaf hx t i c
    have he : Enc.size I.2 = Enc.size (topcsLeaf I.1 t i c) + 2 := by rw [ho, size_some_eq]
    unfold topcsBound
    omega

 theorem size_topcsAnswer {n : ℕ} {P : TopcsInput} (hx : (topcsX P).length = n)
    (s : TopcsState) : Enc.size ((topcsAnswer P s).getD none) ≤ chainBound n := by
  have h0 := chainBound_ge n
  unfold topcsAnswer
  cases ha : s.2.2.2.1 with
  | none => simp only [Option.map_none, Option.getD_none, size_none]; omega
  | some a =>
    simp only [Option.map_some, Option.getD_some]
    split
    · exact size_top3Prod_le hx le_rfl _ _
    · rcases hb : top3Prod (topcsX P, s.2.2.2.2.2, a) with _ | b
      · rw [rawCosetJoin_none]; exact size_top3Prod_le hx le_rfl _ _
      · exact size_rawCosetJoin_some_le hx le_rfl _ b
          (by rw [← hb]; exact size_top3Prod_le hx le_rfl _ _)

end Algo
