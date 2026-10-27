/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 11.1: the **coset form** of Luks's Eqs. (62)–(63), and its alignment.
-/
import Workspace.LocalCertificates.AggregateGroup
import Workspace.TopAction.PrelimExtra
import Workspace.TopAction.Lifting
import Workspace.TopAction.CosetChain

/-!
# The coset form of Eqs. (62)–(63), and the alignment that turns it into the group form

Sec. 11.1 prints each subproblem of Luks's method in **two** forms.  Eq. (62) reads

> `Iso_G(x,y) = ⋃_i Iso_{Hσ_i}(x,y) = ⋃_i Iso_H(x, y^{σ_i⁻¹}) σ_i`

and Eq. (63) is the same identity for windows.  The **middle** term asks the isomorphism
problem for a *coset* `Hσ_i` and leaves the strings alone; the **right-hand** term asks it
for the *group* `H` and shifts the second string.  Remark 11.1.4 names the passage from the
first to the second the **alignment step**, and `Babai.alignInst` is that step.

The mathematical layer has so far written only the right-hand form
(`Babai.chainReduction`, `Babai.descentReduction`, `Babai.liftingReduction`), because
`Babai.IsGroupInstance` holds for it.  A machine cannot: a raw round has to walk one fixed
tree for every raw answer that decodes to the true answer, so a child may depend on the
coset an answer names but not on a representative chosen inside it.  The machine therefore
writes the middle form.

This file writes the middle form on the mathematical side:

* `Babai.cosetChain` — Eq. (63) iterated: the candidate set of the next call is the answer
  of the previous one, so no representative is ever chosen;
* `Babai.cosetDescent` — Eq. (62) itself: one call per coset `σH`, and the plain union of
  the answers;
* `Babai.cosetLift` — Prop. 12.0.1: one call with the candidate set `ϕ⁻¹(σ̄)`.

and the alignment `Babai.SIReduction.alignRed` that carries each of them to the group form.
The three `run` facts say the coset form computes the same thing as the group form, the
three `calls` facts say what it asks, and the three "coset instance" facts say that after
alignment every call is a `Babai.IsGroupInstance` again
(`Babai.isGroupInstance_alignInst`).

`Babai.SIReduction.alignRed` has the same body as `Algo.alignRed` of
`Workspace/Algo/AlignTransfer.lean`, so the two are equal by `rfl`; the copy lives here so
that `Master` does not import `Algo`.

No axiom, no `sorry`.
-/

universe u v w

namespace Babai

open MulAction Equiv Equiv.Perm
open scoped Pointwise

/-! ## The alignment of a whole round

`Babai.SIReduction.alignCalls` aligns every call.  A round of the recursion also has a
*value*, and the value of the aligned round is the value of the coset round read in the
aligned frame: shifted back by the representative of the node the round belongs to. -/

section AlignRed

variable {Ω : Type u} {A : Type v}

/-- **The aligned form of one round** (Remark 11.1.4): put the alignment step in front of
every call, then shift the value back by the representative of the node `I₀`.

Same body as `Algo.alignRed`; the two are equal by `rfl`. -/
noncomputable def SIReduction.alignRed (I₀ : SIInstance Ω A)
    (T : SIReduction Ω A (Set (Equiv.Perm Ω))) : SIReduction Ω A (Set (Equiv.Perm Ω)) :=
  T.alignCalls.bind fun v => .done ((cosetRepOf I₀.K)⁻¹ • v)

@[simp] theorem alignRed_done (I₀ : SIInstance Ω A) (a : Set (Equiv.Perm Ω)) :
    SIReduction.alignRed I₀ (SIReduction.done (Ω := Ω) (A := A) a)
      = .done ((cosetRepOf I₀.K)⁻¹ • a) := rfl

/-- **One step of the aligned round**: it asks the aligned instance, and hands the
continuation of the coset round that answer shifted forward again (Eq. (59)). -/
theorem alignRed_call (I₀ J : SIInstance Ω A)
    (k : Set (Equiv.Perm Ω) → SIReduction Ω A (Set (Equiv.Perm Ω))) :
    SIReduction.alignRed I₀ (.call J k)
      = .call (alignInst J) fun a =>
          SIReduction.alignRed I₀ (k ((cosetRepOf J.K) • a)) := rfl

/-- Alignment changes the value only by the shift at the root (Eq. (59)). -/
@[simp] theorem run_alignRed (I₀ : SIInstance Ω A)
    (T : SIReduction Ω A (Set (Equiv.Perm Ω))) :
    (SIReduction.alignRed I₀ T).run = (cosetRepOf I₀.K)⁻¹ • T.run := by
  rw [SIReduction.alignRed, SIReduction.run_bind, run_alignCalls, SIReduction.run_done]

/-- **At an already aligned node nothing moves**: if the candidate set of the node contains
`1` — a group instance, for example — the aligned round has the value of the coset round. -/
theorem run_alignRed_of_one_mem {I₀ : SIInstance Ω A}
    (h : (1 : Equiv.Perm Ω) ∈ I₀.K) (T : SIReduction Ω A (Set (Equiv.Perm Ω))) :
    (SIReduction.alignRed I₀ T).run = T.run := by
  rw [run_alignRed, cosetRepOf_eq_one h, inv_one, one_smul]

/-- The calls of the aligned round are the calls of the coset round, aligned.  So their
number is unchanged, and so are their windows (`Babai.windowSize_alignInst`). -/
theorem calls_alignRed (I₀ : SIInstance Ω A) (T : SIReduction Ω A (Set (Equiv.Perm Ω))) :
    (SIReduction.alignRed I₀ T).calls = T.calls.map alignInst := by
  rw [SIReduction.alignRed, SIReduction.calls_bind, calls_alignCalls,
    SIReduction.calls_done, List.append_nil]

theorem calls_length_alignRed (I₀ : SIInstance Ω A)
    (T : SIReduction Ω A (Set (Equiv.Perm Ω))) :
    (SIReduction.alignRed I₀ T).calls.length = T.calls.length := by
  rw [calls_alignRed, List.length_map]

/-- Alignment leaves every window size where it was, so it leaves their sum where it was. -/
theorem sum_windowSize_calls_alignRed (I₀ : SIInstance Ω A)
    (T : SIReduction Ω A (Set (Equiv.Perm Ω))) :
    (((SIReduction.alignRed I₀ T).calls).map SIInstance.windowSize).sum =
      ((T.calls).map SIInstance.windowSize).sum := by
  rw [calls_alignRed, List.map_map]
  congr 1

/-- **The aligned round is correct** when the coset round is. -/
theorem run_alignRed_eq_answer {I₀ : SIInstance Ω A}
    {T : SIReduction Ω A (Set (Equiv.Perm Ω))} (h : T.run = I₀.answer) :
    (SIReduction.alignRed I₀ T).run = (alignInst I₀).answer := by
  rw [run_alignRed, h, ← smul_answer_alignInst I₀, inv_smul_smul]

end AlignRed

/-! ## Eq. (63) in coset form: the Chain Rule over a list of windows

`Babai.cosetChain`, with `run_cosetChain`, `calls_cosetChain`,
`sum_windowSize_calls_cosetChain` and `calls_cosetChain_K`, is in
`Workspace/TopAction/CosetChain.lean`, below `Workspace/LocalCertificates/`. -/

/-! ### The states of the coset chain are cosets

Every call of the chain is an instance with respect to a coset of a subgroup of the
ambient group `N`, so after alignment every call is a group instance
(`Babai.isGroupInstance_alignInst`).  The step is Remark 11.1.5 (ii): the answer for a
coset is empty or a coset of the window automorphism group. -/

section CosetChainStates

variable {Ω : Type u} {A : Type v} [Fintype Ω] [DecidableEq Ω]

theorem IsCosetInstance.K_subset {G : Subgroup (Perm Ω)} {J : SIInstance Ω A} (h : IsCosetInstance G J) :
    J.K ⊆ (G : Set (Perm Ω)) := by
  obtain ⟨N, σ, hN, hσ, he, _⟩ := h
  rw [he]
  rintro _ ⟨τ, hτ, rfl⟩
  exact G.mul_mem hσ (hN hτ)

/-- The answer of a coset call is empty, or a coset of a subgroup of `N` again.  This is
Remark 11.1.5 (ii) together with `Babai.wAut_eq_inf`. -/
theorem wIso_smul_eq_empty_or_smul_coe {G N M : Subgroup (Equiv.Perm Ω)} {Δ : Set Ω}
    (hNG : N ≤ G) (hMN : M ≤ N) (hΔ : IsInvariant N Δ) (x y : Ω → A) {σ : Equiv.Perm Ω}
    (hσ : σ ∈ G) :
    wIso Δ (σ • (M : Set (Equiv.Perm Ω))) x y = ∅ ∨
      ∃ (M' : Subgroup (Equiv.Perm Ω)) (σ' : Equiv.Perm Ω), M' ≤ N ∧ σ' ∈ G ∧
        wIso Δ (σ • (M : Set (Equiv.Perm Ω))) x y = σ' • (M' : Set (Equiv.Perm Ω)) := by
  rcases Set.eq_empty_or_nonempty (wIso Δ (σ • (M : Set (Equiv.Perm Ω))) x y) with he | ⟨ρ, hρ⟩
  · exact Or.inl he
  · refine Or.inr ⟨M ⊓ autWindow N Δ x, ρ, le_trans inf_le_left hMN, ?_, ?_⟩
    · have : ρ ∈ σ • (M : Set (Equiv.Perm Ω)) := hρ.1
      obtain ⟨μ, hμ, rfl⟩ := this
      exact mul_mem hσ (hNG (hMN hμ))
    · have hMΔ : IsInvariant M Δ := fun τ hτ => hΔ τ (hMN hτ)
      rw [wIso_eq_smul_wAut hMΔ σ hρ, ← wAut_eq_inf hMN hΔ x]

/-- **Every call of the coset chain is a coset instance.**  The chain starts from a coset
of a subgroup of `N` with an `N`-invariant window, and each answer is a coset again. -/
theorem isCosetInstance_calls_cosetChain {G N : Subgroup (Equiv.Perm Ω)} (hNG : N ≤ G)
    (x y : Ω → A) :
    ∀ (Δs : List (Set Ω)) (C : Set (Equiv.Perm Ω)),
      (∀ Δ ∈ Δs, IsInvariant N Δ) →
      (∃ (M : Subgroup (Equiv.Perm Ω)) (σ : Equiv.Perm Ω), M ≤ N ∧ σ ∈ G ∧
        C = σ • (M : Set (Equiv.Perm Ω))) →
      ∀ J ∈ (cosetChain x y Δs C).calls, IsCosetInstance G J := by
  intro Δs
  induction Δs with
  | nil => intro C _ _ J hJ; rw [cosetChain] at hJ; simp at hJ
  | cons Δ rest ih =>
    rintro C hinv ⟨M, σ, hMN, hσ, rfl⟩ J hJ
    have hΔ : IsInvariant N Δ := hinv Δ List.mem_cons_self
    rw [cosetChain] at hJ
    by_cases hC : σ • (M : Set (Equiv.Perm Ω)) = ∅
    · rw [if_pos hC] at hJ; simp at hJ
    · rw [if_neg hC, SIReduction.calls_call] at hJ
      rcases List.mem_cons.1 hJ with rfl | hJ
      · exact ⟨M, σ, le_trans hMN hNG, hσ, rfl, fun τ hτ => hΔ τ (hMN hτ)⟩
      · have hans : (⟨σ • (M : Set (Equiv.Perm Ω)), Δ, x, y⟩ : SIInstance Ω A).answer
            = wIso Δ (σ • (M : Set (Equiv.Perm Ω))) x y := rfl
        rw [hans] at hJ
        rcases wIso_smul_eq_empty_or_smul_coe hNG hMN hΔ x y hσ with
          he | ⟨M', σ', hM'N, hσ', he⟩
        · rw [he] at hJ
          rcases rest with _ | ⟨Δ', rest'⟩
          · rw [cosetChain] at hJ; simp at hJ
          · rw [cosetChain, if_pos rfl] at hJ; simp at hJ
        · rw [he] at hJ
          exact ih _ (fun Δ' hΔ' => hinv Δ' (List.mem_cons_of_mem _ hΔ'))
            ⟨M', σ', hM'N, hσ', rfl⟩ J hJ

/-- **After alignment every call of the chain is a group instance** — what the cost
analysis of `Workspace/Master/Cost.lean` asks of a round. -/
theorem isGroupInstance_calls_alignRed_cosetChain {G N : Subgroup (Equiv.Perm Ω)}
    (hNG : N ≤ G) (x y : Ω → A) (I₀ : SIInstance Ω A) (Δs : List (Set Ω))
    (C : Set (Equiv.Perm Ω)) (hinv : ∀ Δ ∈ Δs, IsInvariant N Δ)
    (hC : ∃ (M : Subgroup (Equiv.Perm Ω)) (σ : Equiv.Perm Ω), M ≤ N ∧ σ ∈ G ∧
      C = σ • (M : Set (Equiv.Perm Ω))) :
    ∀ J ∈ (SIReduction.alignRed I₀ (cosetChain x y Δs C)).calls,
      IsGroupInstance J ∧ J.K ⊆ (G : Set (Equiv.Perm Ω)) := by
  intro J hJ
  rw [calls_alignRed, List.mem_map] at hJ
  obtain ⟨J', hJ', rfl⟩ := hJ
  have h := isCosetInstance_calls_cosetChain hNG x y Δs C hinv hC J' hJ'
  exact ⟨isGroupInstance_alignInst h, K_alignInst_subset h⟩

end CosetChainStates

/-! ## Eq. (62) in coset form: the Luks descent

Eq. (62) is printed as `Iso_G(x,y) = ⋃_i Iso_{Hσ_i}(x,y)`.  `Babai.cosetDescent` is that
union, term by term: one call per coset, and the **plain union** of the answers, which is
what Eq. (62) prints.  (`Babai.descentReduction` is the right-hand term of the same
equation, where the `σ_i` reappears as a translation of the answer.) -/

section CosetDescent

variable {Ω : Type u} {A : Type v}

/-- §11.1, **Proposition 11.1.6 (Descent), Eq. (62) in coset form**: one call of
`Iso^Δ_{σH}(x,y)` per representative `σ` in the list, and the union of the answers.

The translation by `σ` of the right-hand term of Eq. (62) is absent here: it is already
inside the answer of the coset call. -/
noncomputable def cosetDescent (H : Subgroup (Equiv.Perm Ω)) (Δ : Set Ω) (x y : Ω → A) :
    List (Equiv.Perm Ω) → SIReduction Ω A (Set (Equiv.Perm Ω))
  | [] => .done ∅
  | σ :: rest =>
      .call ⟨σ • (H : Set (Equiv.Perm Ω)), Δ, x, y⟩ fun ans =>
        (cosetDescent H Δ x y rest).bind fun s => .done (ans ∪ s)

/-- Eq. (62), left to middle: the value is the union of the answers of the coset calls. -/
theorem run_cosetDescent (H : Subgroup (Equiv.Perm Ω)) (Δ : Set Ω) (x y : Ω → A) :
    ∀ L : List (Equiv.Perm Ω), (cosetDescent H Δ x y L).run =
      ⋃ σ ∈ L, wIso Δ (σ • (H : Set (Equiv.Perm Ω))) x y := by
  intro L
  induction L with
  | nil => rw [cosetDescent]; simp
  | cons σ rest ih =>
    rw [cosetDescent, SIReduction.run_call, SIReduction.run_bind, SIReduction.run_done, ih]
    have hans : (⟨σ • (H : Set (Equiv.Perm Ω)), Δ, x, y⟩ : SIInstance Ω A).answer =
        wIso Δ (σ • (H : Set (Equiv.Perm Ω))) x y := rfl
    rw [hans]
    ext τ
    simp only [Set.mem_union, Set.mem_iUnion, List.mem_cons, exists_prop]
    constructor
    · rintro (h | ⟨ρ, hρ, hτ⟩)
      · exact ⟨σ, Or.inl rfl, h⟩
      · exact ⟨ρ, Or.inr hρ, hτ⟩
    · rintro ⟨ρ, (rfl | hρ), hτ⟩
      · exact Or.inl hτ
      · exact Or.inr ⟨ρ, hρ, hτ⟩

/-- The descent makes exactly one call per representative. -/
theorem calls_cosetDescent (H : Subgroup (Equiv.Perm Ω)) (Δ : Set Ω) (x y : Ω → A) :
    ∀ L : List (Equiv.Perm Ω), (cosetDescent H Δ x y L).calls =
      L.map (fun σ => (⟨σ • (H : Set (Equiv.Perm Ω)), Δ, x, y⟩ : SIInstance Ω A)) := by
  intro L
  induction L with
  | nil => rw [cosetDescent]; simp
  | cons σ rest ih =>
    rw [cosetDescent, SIReduction.calls_call, SIReduction.calls_bind,
      SIReduction.calls_done, ih]
    simp

theorem calls_length_cosetDescent (H : Subgroup (Equiv.Perm Ω)) (Δ : Set Ω) (x y : Ω → A)
    (L : List (Equiv.Perm Ω)) : (cosetDescent H Δ x y L).calls.length = L.length := by
  rw [calls_cosetDescent, List.length_map]

/-- **The aligned form of a coset call is the group call.**  Aligning `⟨σH, Δ, x, y⟩` gives
an instance whose candidate set is `H` itself; only the second string keeps a trace of the
coset, shifted by the representative the alignment chose.  This is the passage from the
middle to the right-hand term of Eq. (62). -/
theorem K_alignInst_smul_coe (H : Subgroup (Equiv.Perm Ω)) (Δ : Set Ω) (x y : Ω → A)
    (σ : Equiv.Perm Ω) :
    (alignInst (⟨σ • (H : Set (Equiv.Perm Ω)), Δ, x, y⟩ : SIInstance Ω A)).K
      = (H : Set (Equiv.Perm Ω)) := by
  set C : Set (Equiv.Perm Ω) := σ • (H : Set (Equiv.Perm Ω)) with hC
  have hne : C.Nonempty := ⟨σ, ⟨1, H.one_mem, by simp⟩⟩
  have hmem : cosetRepOf C ∈ C := cosetRepOf_mem hne
  obtain ⟨ν, hν, hrep⟩ := hmem
  show (cosetRepOf C)⁻¹ • C = (H : Set (Equiv.Perm Ω))
  have hrep' : σ * ν = cosetRepOf C := hrep
  rw [hC, ← hrep', smul_smul, show (σ * ν)⁻¹ * σ = ν⁻¹ by group]
  exact smul_coe_set (inv_mem hν)

/-- The window of an aligned coset call is the window of the coset call. -/
@[simp] theorem Δ_alignInst_smul_coe (H : Subgroup (Equiv.Perm Ω)) (Δ : Set Ω) (x y : Ω → A)
    (σ : Equiv.Perm Ω) :
    (alignInst (⟨σ • (H : Set (Equiv.Perm Ω)), Δ, x, y⟩ : SIInstance Ω A)).Δ = Δ := rfl

/-- Every call of the descent has the window of the instance, and a coset of `H` for its
candidate set. -/
theorem calls_cosetDescent_spec (H : Subgroup (Equiv.Perm Ω)) (Δ : Set Ω) (x y : Ω → A)
    (L : List (Equiv.Perm Ω)) :
    ∀ J ∈ (cosetDescent H Δ x y L).calls,
      (∃ σ ∈ L, J.K = σ • (H : Set (Equiv.Perm Ω))) ∧ J.Δ = Δ := by
  intro J hJ
  rw [calls_cosetDescent, List.mem_map] at hJ
  obtain ⟨σ, hσ, rfl⟩ := hJ
  exact ⟨⟨σ, hσ, rfl⟩, rfl⟩

variable [Fintype Ω] [DecidableEq Ω]

/-- **Every call of the descent is a coset instance**, so after alignment every call is a
group instance with respect to `H`. -/
theorem isCosetInstance_calls_cosetDescent {H G : Subgroup (Equiv.Perm Ω)} (hHG : H ≤ G)
    {Δ : Set Ω} (hΔ : IsInvariant H Δ) (x y : Ω → A) {L : List (Equiv.Perm Ω)}
    (hL : ∀ σ ∈ L, σ ∈ G) :
    ∀ J ∈ (cosetDescent H Δ x y L).calls, IsCosetInstance G J := by
  intro J hJ
  rw [calls_cosetDescent, List.mem_map] at hJ
  obtain ⟨σ, hσ, rfl⟩ := hJ
  exact ⟨H, σ, hHG, hL σ hσ, rfl, hΔ⟩

/-- **After alignment every call of the descent is a group instance.** -/
theorem isGroupInstance_calls_alignRed_cosetDescent {H G : Subgroup (Equiv.Perm Ω)}
    (hHG : H ≤ G) {Δ : Set Ω} (hΔ : IsInvariant H Δ) (x y : Ω → A)
    (I₀ : SIInstance Ω A) {L : List (Equiv.Perm Ω)} (hL : ∀ σ ∈ L, σ ∈ G) :
    ∀ J ∈ (SIReduction.alignRed I₀ (cosetDescent H Δ x y L)).calls,
      IsGroupInstance J ∧ J.K ⊆ (G : Set (Equiv.Perm Ω)) := by
  intro J hJ
  rw [calls_alignRed, List.mem_map] at hJ
  obtain ⟨J', hJ', rfl⟩ := hJ
  have h := isCosetInstance_calls_cosetDescent hHG hΔ x y hL J' hJ'
  exact ⟨isGroupInstance_alignInst h, K_alignInst_subset h⟩

/-- The aligned descent has exactly one call per representative. -/
theorem calls_length_alignRed_cosetDescent (H : Subgroup (Equiv.Perm Ω)) (Δ : Set Ω)
    (x y : Ω → A) (I₀ : SIInstance Ω A) (L : List (Equiv.Perm Ω)) :
    (SIReduction.alignRed I₀ (cosetDescent H Δ x y L)).calls.length = L.length := by
  rw [calls_length_alignRed, calls_length_cosetDescent]

end CosetDescent

/-! ## Proposition 12.0.1 in coset form: the lifting

`Babai.liftingReduction` calls `Iso_N(x^σ, y)` for a chosen lifting `σ` of `σ̄`.  The coset
form asks the same question of the coset `ϕ⁻¹(σ̄)` itself, with the strings untouched. -/

section CosetLift

variable {Ω : Type u} {A : Type v} {G : Subgroup (Equiv.Perm Ω)} {H : Type w} [Group H]

/-- `Iso_{ϕ⁻¹(σ̄)}(x,y)` is the set of liftings of `σ̄` that are isomorphisms: the preimage
is inside `G`, so the two descriptions agree. -/
theorem wIso_univ_preimageSet (ϕ : G →* H) (x y : Ω → A) (σ : H) :
    wIso Set.univ (preimageSet ϕ σ) x y = liftingSet ϕ x y σ := by
  ext τ
  simp only [mem_wIso, liftingSet, Set.mem_inter_iff, strIso, Set.mem_sep_iff,
    Set.mem_univ, forall_const]
  constructor
  · rintro ⟨hP, h⟩
    refine ⟨hP, preimageSet_subset ϕ σ hP, ?_⟩
    funext u
    have := h (τ⁻¹ u)
    simpa [strAct] using this
  · rintro ⟨hP, -, h⟩
    refine ⟨hP, fun u => ?_⟩
    have := congrFun h (τ u)
    simpa [strAct] using this

/-- §12, **Proposition 12.0.1 (Lifting) in coset form**: one call, the instance whose
candidate set is the coset `ϕ⁻¹(σ̄)` and whose window is all of `Ω`. -/
noncomputable def cosetLift (ϕ : G →* H) (x y : Ω → A) (σ : H) :
    SIReduction Ω A (Set (Equiv.Perm Ω)) :=
  .call ⟨preimageSet ϕ σ, Set.univ, x, y⟩ fun ans => .done ans

/-- Prop. 12.0.1 in coset form computes the set of liftings. -/
theorem run_cosetLift (ϕ : G →* H) (x y : Ω → A) (σ : H) :
    (cosetLift ϕ x y σ).run = liftingSet ϕ x y σ := by
  rw [cosetLift, SIReduction.run_call, SIReduction.run_done]
  exact wIso_univ_preimageSet ϕ x y σ

/-- Prop. 12.0.1 in coset form makes exactly one call. -/
theorem calls_cosetLift (ϕ : G →* H) (x y : Ω → A) (σ : H) :
    (cosetLift ϕ x y σ).calls = [(⟨preimageSet ϕ σ, Set.univ, x, y⟩ : SIInstance Ω A)] := by
  rw [cosetLift, SIReduction.calls_call, SIReduction.calls_done]

variable [Fintype Ω] [DecidableEq Ω]

/-- The preimage of `σ̄` is a coset of the kernel: it is `N ρ = ρ N` for any lifting `ρ`,
and `N` is normal in `G`. -/
theorem preimageSet_eq_smul_kerSubgroup (ϕ : G →* H) {σ : H} (h : σ ∈ ϕ.range) :
    preimageSet ϕ σ =
      liftRep ϕ σ • ((kerSubgroup ϕ : Subgroup (Equiv.Perm Ω)) : Set (Equiv.Perm Ω)) := by
  obtain ⟨hG, hϕ⟩ := liftRep_mem ϕ h
  ext τ
  constructor
  · rintro ⟨hτG, hτϕ⟩
    refine ⟨(liftRep ϕ σ)⁻¹ * τ, ?_, by show liftRep ϕ σ * ((liftRep ϕ σ)⁻¹ * τ) = τ; group⟩
    have hmem : (liftRep ϕ σ)⁻¹ * τ ∈ G := mul_mem (inv_mem hG) hτG
    refine mem_kerSubgroup.2 ⟨hmem, ?_⟩
    have hsplit : (⟨(liftRep ϕ σ)⁻¹ * τ, hmem⟩ : G) = (⟨liftRep ϕ σ, hG⟩ : G)⁻¹ * ⟨τ, hτG⟩ :=
      rfl
    rw [hsplit, map_mul, map_inv, hϕ, hτϕ, inv_mul_cancel]
  · rintro ⟨ν, hν, hτ⟩
    have hτ' : liftRep ϕ σ * ν = τ := hτ
    subst hτ'
    obtain ⟨hνG, hνϕ⟩ := mem_kerSubgroup.1 hν
    have hmem : liftRep ϕ σ * ν ∈ G := mul_mem hG hνG
    refine ⟨hmem, ?_⟩
    have hsplit : (⟨liftRep ϕ σ * ν, hmem⟩ : G) = (⟨liftRep ϕ σ, hG⟩ : G) * ⟨ν, hνG⟩ := rfl
    rw [hsplit, map_mul, hϕ, hνϕ, mul_one]

/-- **The call of the coset lift is a coset instance**, so after alignment it is a group
instance with respect to `N = ker ϕ`. -/
theorem isCosetInstance_calls_cosetLift (ϕ : G →* H) (x y : Ω → A) {σ : H}
    (h : σ ∈ ϕ.range) :
    ∀ J ∈ (cosetLift ϕ x y σ).calls, IsCosetInstance G J := by
  intro J hJ
  rw [calls_cosetLift, List.mem_singleton] at hJ
  subst hJ
  refine ⟨kerSubgroup ϕ, liftRep ϕ σ, kerSubgroup_le ϕ, (liftRep_mem ϕ h).1, ?_,
    fun τ _ => by simp⟩
  exact preimageSet_eq_smul_kerSubgroup ϕ h

/-- **After alignment the call of the lift is a group instance.** -/
theorem isGroupInstance_calls_alignRed_cosetLift (ϕ : G →* H) (x y : Ω → A)
    (I₀ : SIInstance Ω A) {σ : H} (h : σ ∈ ϕ.range) :
    ∀ J ∈ (SIReduction.alignRed I₀ (cosetLift ϕ x y σ)).calls,
      IsGroupInstance J ∧ J.K ⊆ (G : Set (Equiv.Perm Ω)) := by
  intro J hJ
  rw [calls_alignRed, List.mem_map] at hJ
  obtain ⟨J', hJ', rfl⟩ := hJ
  have hc := isCosetInstance_calls_cosetLift ϕ x y h J' hJ'
  exact ⟨isGroupInstance_alignInst hc, K_alignInst_subset hc⟩

end CosetLift

/-! ## The aligned forms, under their own names

Each of the three coset forms, aligned: `Babai.SIReduction.alignRed` of it, at the node the
round belongs to.  These are the right-hand terms of Eqs. (62)–(63) and of Prop. 12.0.1, and
they are what the rounds of Sec. 15 run.  `Babai.chainReduction`, `Babai.descentReduction`
and `Babai.liftingReduction` keep their names and their bodies: they are the same
mathematics with the representative chosen by hand instead of by `Babai.cosetRepOf`, and
three `Algo` theorems are stated against them.

At a node whose candidate set contains `1` — a group instance, which is the standing
invariant of Decision 7 — the shift at the root is trivial, so the aligned round has the
value of the coset round (`Babai.run_alignRed_of_one_mem`), and the aligned round is just
the coset round with every call aligned (`Babai.alignRed_eq_alignCalls`). -/

section AlignedForms

variable {Ω : Type u} {A : Type v}

/-- Binding a reduction to `done` changes nothing. -/
@[simp] theorem SIReduction.bind_done (R : SIReduction Ω A (Set (Equiv.Perm Ω))) :
    R.bind (fun v => .done v) = R := by
  induction R with
  | done a => rfl
  | call I k ih => rw [SIReduction.bind]; exact congrArg _ (funext fun a => ih a)

/-- **At a group node the alignment is just the alignment of the calls.** -/
theorem alignRed_eq_alignCalls {I₀ : SIInstance Ω A} (h : (1 : Equiv.Perm Ω) ∈ I₀.K)
    (T : SIReduction Ω A (Set (Equiv.Perm Ω))) :
    SIReduction.alignRed I₀ T = T.alignCalls := by
  rw [SIReduction.alignRed, cosetRepOf_eq_one h]
  rw [show (fun v : Set (Equiv.Perm Ω) => SIReduction.done (Ω := Ω) (A := A)
      (((1 : Equiv.Perm Ω))⁻¹ • v)) = fun v => .done v from
    funext fun v => by rw [inv_one, one_smul]]
  exact SIReduction.bind_done _

/-- **One step of the aligned round, read as a call.**  This is `Babai.alignRed_call`, kept
here so that a branch that is defined as an aligned round can be unfolded one call at a
time. -/
theorem alignRed_call' (I₀ J : SIInstance Ω A)
    (k : Set (Equiv.Perm Ω) → SIReduction Ω A (Set (Equiv.Perm Ω))) :
    SIReduction.alignRed I₀ (.call J k)
      = .call (alignInst J) fun a =>
          SIReduction.alignRed I₀ (k ((cosetRepOf J.K) • a)) := rfl

end AlignedForms

/-! ### The aligned Chain Rule -/

section AlignedChain

variable {Ω : Type u} {A : Type v} [Fintype Ω] [DecidableEq Ω]

/-- §11.1, **Eq. (63) iterated in the group form**: the Chain Rule over a list of windows,
with every call aligned (Remark 11.1.4). -/
noncomputable def alignedChain (I₀ : SIInstance Ω A) (x y : Ω → A) (Δs : List (Set Ω))
    (C : Set (Equiv.Perm Ω)) : SIReduction Ω A (Set (Equiv.Perm Ω)) :=
  SIReduction.alignRed I₀ (cosetChain x y Δs C)

/-- The aligned chain computes the window isomorphisms for the union of the windows, read
in the frame of the node. -/
theorem run_alignedChain (I₀ : SIInstance Ω A) (x y : Ω → A) (Δs : List (Set Ω))
    (C : Set (Equiv.Perm Ω)) :
    (alignedChain I₀ x y Δs C).run =
      (cosetRepOf I₀.K)⁻¹ • wIso (⋃ Δ ∈ Δs, Δ) C x y := by
  rw [alignedChain, run_alignRed, run_cosetChain]

/-- At a group node the shift at the root is trivial. -/
theorem run_alignedChain_of_one_mem {I₀ : SIInstance Ω A} (h : (1 : Equiv.Perm Ω) ∈ I₀.K)
    (x y : Ω → A) (Δs : List (Set Ω)) (C : Set (Equiv.Perm Ω)) :
    (alignedChain I₀ x y Δs C).run = wIso (⋃ Δ ∈ Δs, Δ) C x y := by
  rw [alignedChain, run_alignRed_of_one_mem h, run_cosetChain]

theorem calls_alignedChain (I₀ : SIInstance Ω A) (x y : Ω → A) (Δs : List (Set Ω))
    (C : Set (Equiv.Perm Ω)) :
    (alignedChain I₀ x y Δs C).calls = (cosetChain x y Δs C).calls.map alignInst :=
  calls_alignRed _ _

/-- The aligned chain makes at most one call per window, and every call has a window of the
list. -/
theorem calls_length_alignedChain (I₀ : SIInstance Ω A) (x y : Ω → A) (Δs : List (Set Ω))
    (C : Set (Equiv.Perm Ω)) :
    (alignedChain I₀ x y Δs C).calls.length ≤ Δs.length ∧
      ∀ J ∈ (alignedChain I₀ x y Δs C).calls, J.Δ ∈ Δs := by
  obtain ⟨hlen, hmem⟩ := calls_cosetChain x y Δs C
  refine ⟨by rw [alignedChain, calls_length_alignRed]; exact hlen, ?_⟩
  intro J hJ
  rw [calls_alignedChain, List.mem_map] at hJ
  obtain ⟨J', hJ', rfl⟩ := hJ
  rw [alignInst_Δ]
  exact hmem J' hJ'

/-- The aligned chain never revisits a window. -/
theorem sum_windowSize_calls_alignedChain (I₀ : SIInstance Ω A) (x y : Ω → A)
    (Δs : List (Set Ω)) (C : Set (Equiv.Perm Ω)) :
    (((alignedChain I₀ x y Δs C).calls).map SIInstance.windowSize).sum ≤
      (Δs.map (fun Δ => Δ.ncard)).sum := by
  rw [alignedChain, sum_windowSize_calls_alignRed]
  exact sum_windowSize_calls_cosetChain x y Δs C

/-- **Every call of the aligned chain is a group instance** inside `N`. -/
theorem isGroupInstance_calls_alignedChain {G N : Subgroup (Equiv.Perm Ω)} (hNG : N ≤ G)
    (I₀ : SIInstance Ω A) (x y : Ω → A) (Δs : List (Set Ω)) (C : Set (Equiv.Perm Ω))
    (hinv : ∀ Δ ∈ Δs, IsInvariant N Δ)
    (hC : ∃ (M : Subgroup (Equiv.Perm Ω)) (σ : Equiv.Perm Ω), M ≤ N ∧ σ ∈ G ∧
      C = σ • (M : Set (Equiv.Perm Ω))) :
    ∀ J ∈ (alignedChain I₀ x y Δs C).calls,
      IsGroupInstance J ∧ J.K ⊆ (G : Set (Equiv.Perm Ω)) :=
  isGroupInstance_calls_alignRed_cosetChain hNG x y I₀ Δs C hinv hC

end AlignedChain

/-! ### The aligned descent -/

section AlignedDescent

variable {Ω : Type u} {A : Type v} [Fintype Ω] [DecidableEq Ω]

/-- §11.1, **Eq. (62) in the group form**: the Luks descent with every call aligned. -/
noncomputable def alignedDescent (I₀ : SIInstance Ω A) (H : Subgroup (Equiv.Perm Ω))
    (Δ : Set Ω) (x y : Ω → A) (L : List (Equiv.Perm Ω)) :
    SIReduction Ω A (Set (Equiv.Perm Ω)) :=
  SIReduction.alignRed I₀ (cosetDescent H Δ x y L)

theorem run_alignedDescent (I₀ : SIInstance Ω A) (H : Subgroup (Equiv.Perm Ω)) (Δ : Set Ω)
    (x y : Ω → A) (L : List (Equiv.Perm Ω)) :
    (alignedDescent I₀ H Δ x y L).run =
      (cosetRepOf I₀.K)⁻¹ • ⋃ σ ∈ L, wIso Δ (σ • (H : Set (Equiv.Perm Ω))) x y := by
  rw [alignedDescent, run_alignRed, run_cosetDescent]

theorem calls_alignedDescent (I₀ : SIInstance Ω A) (H : Subgroup (Equiv.Perm Ω))
    (Δ : Set Ω) (x y : Ω → A) (L : List (Equiv.Perm Ω)) :
    (alignedDescent I₀ H Δ x y L).calls =
      L.map (fun σ => alignInst (⟨σ • (H : Set (Equiv.Perm Ω)), Δ, x, y⟩ : SIInstance Ω A)) := by
  rw [alignedDescent, calls_alignRed, calls_cosetDescent, List.map_map]
  rfl

theorem calls_length_alignedDescent (I₀ : SIInstance Ω A) (H : Subgroup (Equiv.Perm Ω))
    (Δ : Set Ω) (x y : Ω → A) (L : List (Equiv.Perm Ω)) :
    (alignedDescent I₀ H Δ x y L).calls.length = L.length := by
  rw [calls_alignedDescent, List.length_map]

/-- Every call of the aligned descent is the instance with respect to `H` on the window of
the instance: the candidate set is `H` itself (`Babai.K_alignInst_smul_coe`), and only the
second string remembers the coset. -/
theorem calls_alignedDescent_spec (I₀ : SIInstance Ω A) (H : Subgroup (Equiv.Perm Ω))
    (Δ : Set Ω) (x y : Ω → A) (L : List (Equiv.Perm Ω)) :
    ∀ J ∈ (alignedDescent I₀ H Δ x y L).calls,
      J.K = (H : Set (Equiv.Perm Ω)) ∧ J.Δ = Δ ∧ J.x = x ∧ J.windowSize = Δ.ncard := by
  intro J hJ
  rw [calls_alignedDescent, List.mem_map] at hJ
  obtain ⟨σ, -, rfl⟩ := hJ
  exact ⟨K_alignInst_smul_coe H Δ x y σ, rfl, rfl, rfl⟩

end AlignedDescent

/-! ### The aligned lift -/

section AlignedLift

variable {Ω : Type u} {A : Type v} {G : Subgroup (Equiv.Perm Ω)} {H : Type w} [Group H]

/-- §12, **Proposition 12.0.1 in the group form**: the single call, aligned. -/
noncomputable def alignedLift (I₀ : SIInstance Ω A) (ϕ : G →* H) (x y : Ω → A) (σ : H) :
    SIReduction Ω A (Set (Equiv.Perm Ω)) :=
  SIReduction.alignRed I₀ (cosetLift ϕ x y σ)

theorem run_alignedLift (I₀ : SIInstance Ω A) (ϕ : G →* H) (x y : Ω → A) (σ : H) :
    (alignedLift I₀ ϕ x y σ).run = (cosetRepOf I₀.K)⁻¹ • liftingSet ϕ x y σ := by
  rw [alignedLift, run_alignRed, run_cosetLift]

theorem run_alignedLift_of_one_mem {I₀ : SIInstance Ω A} (h : (1 : Equiv.Perm Ω) ∈ I₀.K)
    (ϕ : G →* H) (x y : Ω → A) (σ : H) :
    (alignedLift I₀ ϕ x y σ).run = liftingSet ϕ x y σ := by
  rw [alignedLift, run_alignRed_of_one_mem h, run_cosetLift]

theorem calls_alignedLift (I₀ : SIInstance Ω A) (ϕ : G →* H) (x y : Ω → A) (σ : H) :
    (alignedLift I₀ ϕ x y σ).calls =
      [alignInst (⟨preimageSet ϕ σ, Set.univ, x, y⟩ : SIInstance Ω A)] := by
  rw [alignedLift, calls_alignRed, calls_cosetLift, List.map_cons, List.map_nil]

theorem calls_length_alignedLift (I₀ : SIInstance Ω A) (ϕ : G →* H) (x y : Ω → A) (σ : H) :
    (alignedLift I₀ ϕ x y σ).calls.length = 1 := by
  rw [calls_alignedLift, List.length_singleton]

/-- The window of the aligned lift is all of `Ω`, as in Prop. 12.0.1. -/
theorem calls_alignedLift_window (I₀ : SIInstance Ω A) (ϕ : G →* H) (x y : Ω → A) (σ : H) :
    ∀ J ∈ (alignedLift I₀ ϕ x y σ).calls, J.Δ = Set.univ ∧ J.x = x := by
  intro J hJ
  rw [calls_alignedLift, List.mem_singleton] at hJ
  subst hJ
  exact ⟨rfl, rfl⟩

end AlignedLift


/-! ### The coset chain over the orbits of `N`

Cor. 12.0.6 and the imprimitive Luks reduction substitute, for each instance "with respect
to `N`", the Chain Rule over the orbits of `N`.  In coset form the instance may be with
respect to a *coset* of `N`, and the chain starts from that coset. -/

section CosetChainOverOrbits

variable {Ω : Type u} {A : Type v} [Fintype Ω] [DecidableEq Ω]

/-- The coset-form Chain Rule of the instance `I` over the orbits of `N`: the chain starts
from the candidate set of `I`, whatever it is.  `Babai.chainOverOrbits` is the group form of
the same thing. -/
noncomputable def cosetChainOverOrbits (N : Subgroup (Equiv.Perm Ω)) (I : SIInstance Ω A) :
    SIReduction Ω A (Set (Equiv.Perm Ω)) :=
  cosetChain I.x I.y (orbitList N) I.K

/-- The coset chain over the orbits answers every instance whose window is all of `Ω`.
Unlike `Babai.run_chainOverOrbits` it asks nothing of the candidate set. -/
theorem run_cosetChainOverOrbits (N : Subgroup (Equiv.Perm Ω)) {I : SIInstance Ω A}
    (hΔ : I.Δ = Set.univ) : (cosetChainOverOrbits N I).run = I.answer := by
  rw [cosetChainOverOrbits, run_cosetChain, iUnion_orbitList, SIInstance.answer, hΔ]

theorem calls_length_cosetChainOverOrbits (N : Subgroup (Equiv.Perm Ω)) (I : SIInstance Ω A) :
    (cosetChainOverOrbits N I).calls.length ≤ (orbitList N).length :=
  (calls_cosetChain I.x I.y (orbitList N) I.K).1

theorem calls_cosetChainOverOrbits_window (N : Subgroup (Equiv.Perm Ω)) (I : SIInstance Ω A) :
    ∀ J ∈ (cosetChainOverOrbits N I).calls, J.Δ ∈ orbitList N :=
  (calls_cosetChain I.x I.y (orbitList N) I.K).2

theorem calls_cosetChainOverOrbits_K (N : Subgroup (Equiv.Perm Ω)) (I : SIInstance Ω A) :
    ∀ J ∈ (cosetChainOverOrbits N I).calls, J.K ⊆ I.K :=
  calls_cosetChain_K I.x I.y (orbitList N) I.K

/-- Every call of the coset chain over the orbits of `N` is a coset instance, as soon as the
candidate set of `I` is a coset of a subgroup of `N`. -/
theorem isCosetInstance_calls_cosetChainOverOrbits {G N : Subgroup (Equiv.Perm Ω)}
    (hNG : N ≤ G) (I : SIInstance Ω A)
    (hK : ∃ (M : Subgroup (Equiv.Perm Ω)) (σ : Equiv.Perm Ω), M ≤ N ∧ σ ∈ G ∧
      I.K = σ • (M : Set (Equiv.Perm Ω))) :
    ∀ J ∈ (cosetChainOverOrbits N I).calls, IsCosetInstance G J :=
  isCosetInstance_calls_cosetChain hNG I.x I.y (orbitList N) I.K
    (fun _ hΔ => isInvariant_of_mem_orbitList hΔ) hK

end CosetChainOverOrbits

/-! ### The independent lifts of Prop. 12.0.5, in coset form -/

section CosetLiftAll

variable {Ω : Type u} {A : Type v} {G : Subgroup (Equiv.Perm Ω)} {H : Type w} [Group H]

/-- The `|S'|` independent calls of Prop. 12.0.5, one per element of `S'`, in coset form.
`Babai.liftAll` is the group form of the same thing. -/
noncomputable def cosetLiftAll (ϕ : G →* H) (x y : Ω → A) :
    List H → SIReduction Ω A (List (Set (Equiv.Perm Ω)))
  | [] => .done []
  | σ :: rest => (cosetLift ϕ x y σ).bind
      (fun a => (cosetLiftAll ϕ x y rest).bind (fun as => .done (a :: as)))

theorem run_cosetLiftAll (ϕ : G →* H) (x y : Ω → A) (l : List H) :
    (cosetLiftAll ϕ x y l).run = l.map (liftingSet ϕ x y) := by
  induction l with
  | nil => rw [cosetLiftAll]; simp
  | cons σ rest ih =>
    rw [cosetLiftAll, SIReduction.run_bind, SIReduction.run_bind, SIReduction.run_done,
      run_cosetLift, ih]
    simp

theorem calls_cosetLiftAll (ϕ : G →* H) (x y : Ω → A) (l : List H) :
    (cosetLiftAll ϕ x y l).calls =
      l.map (fun σ => (⟨preimageSet ϕ σ, Set.univ, x, y⟩ : SIInstance Ω A)) := by
  induction l with
  | nil => rw [cosetLiftAll]; simp
  | cons σ rest ih =>
    rw [cosetLiftAll, SIReduction.calls_bind, SIReduction.calls_bind, SIReduction.calls_done,
      calls_cosetLift, ih]
    simp

end CosetLiftAll

/-! ### An empty candidate set makes no calls -/

section EmptyChain

variable {Ω : Type u} {A : Type v}

/-- The coset chain asks nothing when the coset it has reached is empty: the branch is
already known to be unsolvable. -/
theorem calls_cosetChain_empty (x y : Ω → A) (Δs : List (Set Ω)) :
    (cosetChain x y Δs (∅ : Set (Equiv.Perm Ω))).calls = [] := by
  cases Δs with
  | nil => rw [cosetChain]; rfl
  | cons Δ rest => rw [cosetChain, if_pos rfl]; rfl

end EmptyChain

/-! ### Leaves

A branch with no call is already aligned: the shift at the root is trivial at a group
node. -/

section Leaf

variable {Ω : Type u} {A : Type v}

/-- **A leaf is its own alignment** at a group node. -/
theorem alignRed_done_self {I₀ : SIInstance Ω A} (h : (1 : Equiv.Perm Ω) ∈ I₀.K)
    (a : Set (Equiv.Perm Ω)) :
    SIReduction.alignRed I₀ (SIReduction.done (Ω := Ω) (A := A) a) = .done a := by
  rw [alignRed_done, cosetRepOf_eq_one h, inv_one, one_smul]

/-- §11.1, Eq. (59): **a leaf in coset form**.  A branch that answers outright returns the
answer read in the shifted frame of Eq. (62); the alignment step shifts it back.  Writing the
leaf this way needs no hypothesis on `I₀`, so it also covers the escape branch of line 1,
where the instance is not with respect to a group. -/
noncomputable def cosetLeaf (I₀ : SIInstance Ω A) (a : Set (Equiv.Perm Ω)) :
    SIReduction Ω A (Set (Equiv.Perm Ω)) := .done (cosetRepOf I₀.K • a)

@[simp] theorem alignRed_cosetLeaf (I₀ : SIInstance Ω A) (a : Set (Equiv.Perm Ω)) :
    SIReduction.alignRed I₀ (cosetLeaf I₀ a) = .done a := by
  rw [cosetLeaf, alignRed_done, inv_smul_smul]

end Leaf

end Babai
