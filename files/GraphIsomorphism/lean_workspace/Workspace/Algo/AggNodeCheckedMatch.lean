import Workspace.Algo.AggNodeChecked

/-! # The checked boundary preserves the certificate phase

The alphabet condition used at the boundary follows from the actual calls
of the certificate tree. Recompute always compares one input string with
itself, and the phase selects that string from the original source and target.
Thus the checked carrier has the same fixed-tree match and the same final
stores, for every encoding of each correct child answer.
-/
namespace Algo
open Babai Equiv

/-- The Chain Rule keeps both strings unchanged. -/
theorem aggnCalls_chain_strings {Ω Λ : Type*} (x y : Ω → Λ) :
    ∀ (windows : List (Set Ω)) (C : Set (Perm Ω)) (I : SIInstance Ω Λ),
      I ∈ (Babai.cosetChain x y windows C).calls → I.x = x ∧ I.y = y := by
  intro windows
  induction windows with
  | nil => simp [Babai.cosetChain]
  | cons W rest ih =>
    intro C I hI
    classical
    by_cases hc : C = ∅
    · simp [Babai.cosetChain, hc] at hI
    · simp only [Babai.cosetChain, if_neg hc, SIReduction.calls_call, List.mem_cons] at hI
      rcases hI with rfl | hI
      · exact ⟨rfl, rfl⟩
      · exact ih _ I hI

/-- Sec. 13.1, line 04e: every certificate call compares the selected input
string with itself. This statement is independent of the enumeration order. -/
theorem aggnCalls_certPhase_strings {Ω Γ Λ : Type*}
    [Fintype Ω] [DecidableEq Ω] [Fintype Γ] [DecidableEq Γ]
    {G : Subgroup (Perm Ω)} (ϕ : G →* Perm Γ) (x y : Ω → Λ) (E : AggEnum Ω Γ)
    {I : SIInstance Ω Λ} (hI : I ∈ (certPhaseStrong ϕ x y E).calls) :
    ∃ b : Bool, I.x = cond b y x ∧ I.y = cond b y x := by
  obtain ⟨S, hS, hI⟩ := SIReduction.mem_calls_sequence hI
  obtain ⟨b, T, _, rfl⟩ := (mem_certRunsStrong E).mp hS
  rw [calls_certRunStrong, calls_localCertStrong] at hI
  obtain ⟨i, _, hI⟩ := mem_calls_loopStrong _ _ _ I hI
  rw [calls_recomputeStrong, List.mem_flatMap] at hI
  obtain ⟨σ, _, hI⟩ := hI
  exact ⟨b, aggnCalls_chain_strings _ _ _ _ I hI⟩

/-- A normalized raw string satisfies the boundary's decoded alphabet bound. -/
theorem aggnDecodedStr_le {n : ℕ} {xs : RawStr} (h : RawStr.WF n (2 * n) xs)
    (i : Fin n) : decStrN n xs i ≤ 2 * n := by
  have hi : (i : ℕ) < xs.length := h.1 ▸ i.isLt
  change xs.getD i.val 0 ≤ 2 * n
  rw [List.getD_eq_getElem _ _ hi]
  exact (h.2 _ (List.getElem_mem hi)).le

/-- Transport a match using only properties of the calls on the correct path.
No extra invariant is imposed on the raw states or answers. -/
theorem aggnCheckedLoopMatch {β : Type*} {c n : ℕ} {I : AggnPhaseNode}
    (hlen : I.1.2.1.length = n) {w j : ℕ} {s : AggnPhaseState}
    {S : SIReduction (Fin n) ℕ β} {Q : β → ℕ → ℕ → AggnPhaseState → Prop}
    (h : LoopMatchK (aggnPhaseRound c n) (aggnPhaseDecode n) (decCoset n) I w j s S Q)
    (hletters : ∀ K ∈ S.calls, (∀ u, K.x u ≤ 2 * n) ∧ (∀ u, K.y u ≤ 2 * n)) :
    LoopMatchK (aggnCheckedRound c n) (aggnPhaseDecode n) (decCoset n) I w j s S Q := by
  induction h with
  | done w j s b Q hQ => exact .done w j s b Q hQ
  | call w j s J cont Q hc hn ih =>
    have hb := hletters (aggnPhaseDecode n J) (by simp)
    obtain ⟨_, W, hJ⟩ := aggnPhaseChild_some hc
    have hd : aggnPhaseDecode n (aggnCheckedNode J) = aggnPhaseDecode n J := by
      rw [hJ] at hb ⊢
      exact aggnCheckedWindow_decode hlen W hb.1 hb.2
    have hc' : (aggnCheckedRound c n).child (I, j, s) = some (aggnCheckedNode J) := by
      change ((aggnPhaseRound c n).child (I, j, s)).map aggnCheckedNode = _
      rw [hc]
      rfl
    have hm := LoopMatchK.call (R := aggnCheckedRound c n)
      (decI := aggnPhaseDecode n) (decA := decCoset n) (I := I)
      w j s (aggnCheckedNode J) cont Q hc' (fun a ha => by
        rw [hd] at ha ⊢
        exact ih a ha (fun K hK => hletters K (List.mem_cons_of_mem _ hK)))
    simpa only [hd] using hm

theorem aggnCheckedPhaseMatch {β : Type*} {c n : ℕ} {I : AggnPhaseNode}
    (hlen : I.1.2.1.length = n) {fuel j : ℕ} {s : AggnPhaseState}
    {S : SIReduction (Fin n) ℕ β} {Q : β → ℕ → AggnPhaseState → Prop}
    (h : PhaseMatch (aggnPhaseRound c n) (aggnPhaseDecode n) (decCoset n) I fuel j s S Q)
    (hletters : ∀ K ∈ S.calls, (∀ u, K.x u ≤ 2 * n) ∧ (∀ u, K.y u ≤ 2 * n)) :
    PhaseMatch (aggnCheckedRound c n) (aggnPhaseDecode n) (decCoset n) I fuel j s S Q :=
  fun r => aggnCheckedLoopMatch hlen (h r) hletters

/-- Sec. 13.2, the complete certificate phase on normalized input strings.
The result is the existing store specification, with no weakened conclusion. -/
theorem aggnChecked_certificates {c n m : ℕ} {C : AggnPhaseCtx}
    {ϕ : decGroup n C.1.1.2 →* Perm (Fin m)}
    (hC : AggnPhaseCtxWF c n m C ϕ) (hgiant : IsGiantRep ϕ)
    (ht : LargeK C.2.2.2.length (Nat.card (Fin n))) (htm : 10 * C.2.2.2.length ≤ m)
    (hx : RawStr.WF n (2 * n) C.2.1) (hy : RawStr.WF n (2 * n) C.2.2.1) :
    PhaseMatch (aggnCheckedRound c n) (aggnPhaseDecode n) (decCoset n) (C, none)
      (aggnPhaseWidth c C) 0 ((aggnCheckedRound c n).init (C, none))
      (certPhaseStrong ϕ (decStrN n C.2.1) (decStrN n C.2.2.1)
        (aggnRawCertEnum c ϕ (decStrN n C.2.1) (decStrN n C.2.2.1)
          C.2.2.2 C.2.1 C.1.2.1))
      (fun _ _ v => v.1 = [] ∧ AggnStoresComplete c ϕ v.2.1) := by
  apply aggnCheckedPhaseMatch hC.source (aggnPhase_certificates hC hgiant ht htm)
  intro K hK
  obtain ⟨b, hbx, hby⟩ := aggnCalls_certPhase_strings _ _ _ _ hK
  rw [hbx, hby]
  cases b
  · exact ⟨aggnDecodedStr_le hx, aggnDecodedStr_le hx⟩
  · exact ⟨aggnDecodedStr_le hy, aggnDecodedStr_le hy⟩

end Algo
