/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 11.1: the Chain Rule, Eq. (63), iterated over a list of windows, in coset form.
-/
import Workspace.TopAction.PrelimExtra

/-!
# The Chain Rule over a list of windows, in coset form

`Babai.cosetChain` and its value, call list and window sizes.  The file sits below
`Workspace/LocalCertificates/`, so that Procedure Recompute (Sec. 13.1, line 04e, "strong
descent") can run the same chain that `Workspace/Master/CosetForms.lean` aligns.

No axiom, no `sorry`.
-/

universe u v w

namespace Babai

open MulAction Equiv Equiv.Perm
open scoped Pointwise

/-! ## Eq. (63) in coset form: the Chain Rule over a list of windows

The chain is a fold, and its state is the coset reached so far — nothing else.  The
candidate set of the `j`-th call is the answer of the `(j-1)`-st.  `Babai.SIInstance` takes
an arbitrary set of candidates (Def. 11.1.2), so the coset needs no representative. -/

section CosetChain

variable {Ω : Type u} {A : Type v}

/-- §11.1, **Eq. (63) iterated, in the coset form** (the middle term of Eq. (62)): the
`j`-th call is the instance whose candidate set is the coset reached so far, and the value
is the last coset.

`Babai.chainReduction` is the same chain written in the group form (the right-hand term of
Eq. (62)): there the state is a group and a shift, here it is the coset itself. -/
noncomputable def cosetChain (x y : Ω → A) :
    List (Set Ω) → Set (Equiv.Perm Ω) → SIReduction Ω A (Set (Equiv.Perm Ω))
  | [], C => .done C
  | Δ :: rest, C =>
      if C = ∅ then .done ∅
      else .call ⟨C, Δ, x, y⟩ fun ans => cosetChain x y rest ans

/-- §11.1, **Prop. 11.1.7 iterated, Eq. (63)**: the chain computes the window isomorphisms
for the union of the windows. -/
theorem run_cosetChain (x y : Ω → A) :
    ∀ (Δs : List (Set Ω)) (C : Set (Equiv.Perm Ω)),
      (cosetChain x y Δs C).run = wIso (⋃ Δ ∈ Δs, Δ) C x y := by
  intro Δs
  induction Δs with
  | nil =>
    intro C
    rw [cosetChain, SIReduction.run_done]
    simp only [List.not_mem_nil, Set.iUnion_of_empty, Set.iUnion_empty]
    ext τ
    simp [wIso]
  | cons Δ rest ih =>
    intro C
    rw [cosetChain]
    by_cases hC : C = ∅
    · rw [if_pos hC, SIReduction.run_done, hC]
      symm
      rw [Set.eq_empty_iff_forall_notMem]
      exact fun τ hτ => hτ.1
    rw [if_neg hC, SIReduction.run_call]
    have hans : (⟨C, Δ, x, y⟩ : SIInstance Ω A).answer = wIso Δ C x y := rfl
    rw [hans, ih]
    have hunion : (⋃ Δ' ∈ (Δ :: rest), Δ') = Δ ∪ ⋃ Δ' ∈ rest, Δ' := by
      ext u
      simp only [Set.mem_iUnion, List.mem_cons, exists_prop, Set.mem_union]
      constructor
      · rintro ⟨Δ', (rfl | hΔ'), hu⟩
        · exact Or.inl hu
        · exact Or.inr ⟨Δ', hΔ', hu⟩
      · rintro (hu | ⟨Δ', hΔ', hu⟩)
        · exact ⟨Δ, Or.inl rfl, hu⟩
        · exact ⟨Δ', Or.inr hΔ', hu⟩
    rw [hunion, wIso_window_union]
    ext τ
    simp only [mem_wIso, Set.mem_inter_iff]
    constructor
    · rintro ⟨⟨hC', h1⟩, h2⟩; exact ⟨⟨hC', h1⟩, ⟨hC', h2⟩⟩
    · rintro ⟨⟨hC', h1⟩, ⟨-, h2⟩⟩; exact ⟨⟨hC', h1⟩, h2⟩

/-- The chain makes at most one call per window, and every call has a window of the list. -/
theorem calls_cosetChain (x y : Ω → A) :
    ∀ (Δs : List (Set Ω)) (C : Set (Equiv.Perm Ω)),
      (cosetChain x y Δs C).calls.length ≤ Δs.length ∧
        ∀ J ∈ (cosetChain x y Δs C).calls, J.Δ ∈ Δs := by
  intro Δs
  induction Δs with
  | nil => intro C; rw [cosetChain]; simp
  | cons Δ rest ih =>
    intro C
    rw [cosetChain]
    by_cases hC : C = ∅
    · rw [if_pos hC]; simp
    · rw [if_neg hC, SIReduction.calls_call]
      obtain ⟨hlen, hmem⟩ := ih (⟨C, Δ, x, y⟩ : SIInstance Ω A).answer
      refine ⟨by simpa using hlen, ?_⟩
      intro J hJ
      rcases List.mem_cons.1 hJ with rfl | hJ
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (hmem J hJ)

/-- The chain never revisits a window, so the total window size of its calls is at most the
total size of the list.  This is what turns "the parts partition the window" into the bound
"instances of total size `≤ n`" of recurrence (i) of Sec. 11.4. -/
theorem sum_windowSize_calls_cosetChain (x y : Ω → A) :
    ∀ (Δs : List (Set Ω)) (C : Set (Equiv.Perm Ω)),
      (((cosetChain x y Δs C).calls).map SIInstance.windowSize).sum ≤
        (Δs.map (fun Δ => Δ.ncard)).sum := by
  intro Δs
  induction Δs with
  | nil => intro C; rw [cosetChain]; simp
  | cons Δ rest ih =>
    intro C
    rw [cosetChain]
    have hw : (⟨C, Δ, x, y⟩ : SIInstance Ω A).windowSize = Δ.ncard := rfl
    by_cases hC : C = ∅
    · rw [if_pos hC]; simp
    · rw [if_neg hC, SIReduction.calls_call]
      simp only [List.map_cons, List.sum_cons, hw]
      exact Nat.add_le_add_left (ih (⟨C, Δ, x, y⟩ : SIInstance Ω A).answer) _

/-- Every call of the chain has its candidate set inside the set the chain started from:
the answer of a call is a subset of its candidate set, so the coset only shrinks. -/
theorem calls_cosetChain_K (x y : Ω → A) :
    ∀ (Δs : List (Set Ω)) (C : Set (Equiv.Perm Ω)),
      ∀ J ∈ (cosetChain x y Δs C).calls, J.K ⊆ C := by
  intro Δs
  induction Δs with
  | nil => intro C J hJ; rw [cosetChain] at hJ; simp at hJ
  | cons Δ rest ih =>
    intro C J hJ
    rw [cosetChain] at hJ
    by_cases hC : C = ∅
    · rw [if_pos hC] at hJ; simp at hJ
    · rw [if_neg hC, SIReduction.calls_call] at hJ
      rcases List.mem_cons.1 hJ with rfl | hJ
      · exact le_rfl
      · exact le_trans (ih _ J hJ) (wIso_subset Δ C x y)

/-- An empty candidate set makes no calls, for any supplied window order. -/
@[simp] theorem cosetChain_empty_calls (x y : Ω → A) (Δs : List (Set Ω)) :
    (cosetChain x y Δs ∅).calls = [] := by
  cases Δs <;> simp [cosetChain]

/-- Sec. 14.1, line 6: the first window is processed with the initial candidate set.
Every later call uses a window from the tail. -/
theorem calls_cosetChain_cons (x y : Ω → A) (Δ : Set Ω) (rest : List (Set Ω))
    (C : Set (Equiv.Perm Ω)) :
    ∀ J ∈ (cosetChain x y (Δ :: rest) C).calls,
      J = (⟨C, Δ, x, y⟩ : SIInstance Ω A) ∨ J.Δ ∈ rest := by
  classical
  intro J hJ
  by_cases hC : C = ∅
  · simp [hC] at hJ
  · rw [cosetChain, if_neg hC, SIReduction.calls_call] at hJ
    rcases List.mem_cons.1 hJ with rfl | hJ
    · exact Or.inl rfl
    · exact Or.inr ((calls_cosetChain x y rest _).2 J hJ)

/-- A nonempty candidate set and a nonempty window list force a first call. -/
theorem calls_cosetChain_cons_ne_nil (x y : Ω → A) (Δ : Set Ω) (rest : List (Set Ω))
    {C : Set (Equiv.Perm Ω)} (hC : C.Nonempty) :
    (cosetChain x y (Δ :: rest) C).calls ≠ [] := by
  rw [cosetChain, if_neg hC.ne_empty, SIReduction.calls_call]
  exact List.cons_ne_nil _ _

end CosetChain

end Babai
