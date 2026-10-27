import Workspace.Algo.AggNodeCompareChecked
import Workspace.Algo.AggNodeCompareMatch
import Workspace.Algo.AggNodeCheckedMatch

/-! # The normalized boundary preserves every comparison call

Every source descent compares the original source with itself. Every
comparison descent uses the original source and the selected input string.
These facts derive the boundary's alphabet condition from the actual tree.
-/
namespace Algo
open Babai Equiv
open scoped Classical

theorem aggnCalls_strong_strings {Ω Λ : Type*} [Fintype Ω] [DecidableEq Ω]
    (N : Subgroup (Perm Ω)) (x y : Ω → Λ) (L : List (Perm Ω)) (ws : List (Set Ω))
    {I : SIInstance Ω Λ} (hI : I ∈ (strongDescent N x y L ws).calls) : I.x = x ∧ I.y = y := by
  rw [calls_strongDescent, List.mem_flatMap] at hI
  obtain ⟨r, _, hI⟩ := hI
  exact aggnCalls_chain_strings x y ws _ I hI

theorem aggnCalls_compare_strings {Ω Γ Λ : Type*}
    [Fintype Ω] [DecidableEq Ω] [Fintype Γ] [DecidableEq Γ]
    {G : Subgroup (Perm Ω)} (ϕ : G →* Perm Γ) (x y : Ω → Λ) (T : Set Γ)
    (σ : Option (Perm Ω)) (E : StrongPairEnum Ω)
    {I : SIInstance Ω Λ} (hI : I ∈ (compareStrong ϕ x T y σ E).calls) :
    I.x = x ∧ (I.y = x ∨ I.y = y) := by
  cases σ with
  | none => simp [compareStrong] at hI
  | some σ =>
    rw [compareStrong, calls_pairedComparisonStrong_eq] at hI
    obtain ⟨i, _, hI⟩ := mem_calls_pairedLoopStrong σ E _ hI
    rcases hI with hI | hI
    · have hs := aggnCalls_strong_strings _ x x _ _ hI
      exact ⟨hs.1, Or.inl hs.2⟩
    · have hs := aggnCalls_strong_strings _ x y _ _ hI
      exact ⟨hs.1, Or.inr hs.2⟩

theorem aggnCalls_comparePhase_strings {Ω Γ Λ : Type*}
    [Fintype Ω] [DecidableEq Ω] [Fintype Γ] [DecidableEq Γ]
    {G : Subgroup (Perm Ω)} (ϕ : G →* Perm Γ) (x y : Ω → Λ) (E : AggEnum Ω Γ)
    {I : SIInstance Ω Λ} (hI : I ∈ (comparePhaseStrong ϕ x y E).calls) :
    I.x = x ∧ (I.y = x ∨ I.y = y) := by
  obtain ⟨S, hS, hI⟩ := SIReduction.mem_calls_sequence hI
  obtain ⟨b, T, _, T', _, rfl⟩ := (mem_compareRunsStrong E).mp hS
  have hs := aggnCalls_compare_strings ϕ x (cond b y x) T _ _ hI
  refine ⟨hs.1, ?_⟩
  cases b
  · exact Or.inl (hs.2.elim id id)
  · exact hs.2

theorem aggnCompareCheckedLoopMatch {β : Type*} {c n : ℕ} {I : AggnPhaseNode}
    (hlen : I.1.2.1.length = n) {w j : ℕ} {s : AggnCompareState}
    {S : SIReduction (Fin n) ℕ β} {Q : β → ℕ → ℕ → AggnCompareState → Prop}
    (h : LoopMatchK (aggnCompareRound c n) (aggnPhaseDecode n) (decCoset n) I w j s S Q)
    (hletters : ∀ K ∈ S.calls, (∀ u, K.x u ≤ 2 * n) ∧ (∀ u, K.y u ≤ 2 * n)) :
    LoopMatchK (aggnCompareCheckedRound c) (aggnPhaseDecode n) (decCoset n) I w j s S Q := by
  induction h with
  | done w j s b Q hQ => exact .done w j s b Q hQ
  | call w j s J cont Q hc hn ih =>
    have hb := hletters (aggnPhaseDecode n J) (by simp)
    obtain ⟨_, W, hJ⟩ := aggnCompareChild_some hc
    have hd : aggnPhaseDecode n (aggnCheckedNode J) = aggnPhaseDecode n J := by
      rw [hJ] at hb ⊢
      exact aggnCheckedWindow_decode hlen W hb.1 hb.2
    have hc' : (aggnCompareCheckedRound c).child (I, j, s) = some (aggnCheckedNode J) := by
      change ((aggnCompareRound c n).child (I, j, s)).map aggnCheckedNode = _
      rw [hc]
      rfl
    have hm := LoopMatchK.call (R := aggnCompareCheckedRound c)
      (decI := aggnPhaseDecode n) (decA := decCoset n) (I := I)
      w j s (aggnCheckedNode J) cont Q hc' (fun a ha => by
        rw [hd] at ha ⊢
        exact ih a ha (fun K hK => hletters K (List.mem_cons_of_mem _ hK)))
    simpa only [hd] using hm

theorem aggnCompareCheckedPhaseMatch {β : Type*} {c n : ℕ} {I : AggnPhaseNode}
    (hlen : I.1.2.1.length = n) {fuel j : ℕ} {s : AggnCompareState}
    {S : SIReduction (Fin n) ℕ β} {Q : β → ℕ → AggnCompareState → Prop}
    (h : PhaseMatch (aggnCompareRound c n) (aggnPhaseDecode n) (decCoset n) I fuel j s S Q)
    (hletters : ∀ K ∈ S.calls, (∀ u, K.x u ≤ 2 * n) ∧ (∀ u, K.y u ≤ 2 * n)) :
    PhaseMatch (aggnCompareCheckedRound c) (aggnPhaseDecode n) (decCoset n) I fuel j s S Q :=
  fun r => aggnCompareCheckedLoopMatch hlen (h r) hletters

theorem aggnCompareChecked_comparisons {c n m : ℕ} {C : AggnPhaseCtx}
    {ϕ : decGroup n C.1.1.2 →* Perm (Fin m)}
    (hC : AggnPhaseCtxWF c n m C ϕ) (hgiant : IsGiantRep ϕ) (h2 : 2 ≤ C.2.2.2.length)
    (hx : RawStr.WF n (2 * n) C.2.1) (hy : RawStr.WF n (2 * n) C.2.2.1) :
    PhaseMatch (aggnCompareCheckedRound c) (aggnPhaseDecode n) (decCoset n) (C, none)
      (aggnCompareWidth c C) 0 ((aggnCompareCheckedRound c).init (C, none))
      (comparePhaseStrong ϕ (decStrN n C.2.1) (decStrN n C.2.2.1)
        (aggnFullEnum ϕ (decStrN n C.2.1) (decStrN n C.2.2.1)
          ((aggnPhaseRows c C).map (winSet m))))
      (fun B _ v => v.1 = [] ∧ v.2.1.reverse.map (decCoset n) = B) := by
  apply aggnCompareCheckedPhaseMatch hC.source (aggnComparePhase_comparisons hC hgiant h2)
  intro K hK
  obtain ⟨hkx, hky⟩ := aggnCalls_comparePhase_strings _ _ _ _ hK
  refine ⟨fun u => hkx ▸ aggnDecodedStr_le hx u, ?_⟩
  rcases hky with hky | hky
  · exact fun u => hky ▸ aggnDecodedStr_le hx u
  · exact fun u => hky ▸ aggnDecodedStr_le hy u

end Algo
