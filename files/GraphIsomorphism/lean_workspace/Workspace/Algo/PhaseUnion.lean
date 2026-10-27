import Workspace.Algo.PhaseChain
import Workspace.LocalCertificates.StrongDescent

/-! # A union of phases

Procedure Recompute runs one Chain Rule for each representative. The union does
not choose later calls. This lets a raw fold keep the coset hull of the answers
while the mathematical reduction keeps their union.
-/

namespace Algo

open Babai Equiv
open scoped Pointwise

universe u v w z

/-- The two versions of the Chain Rule have the same tree. -/
theorem aggrCosetChain_eq {Ω : Type u} {Λ : Type v} (x y : Ω → Λ) :
    ∀ (Δs : List (Set Ω)) (C : Set (Perm Ω)),
      Algo.cosetChain x y Δs C = Babai.cosetChain x y Δs C := by
  intro Δs
  induction Δs with
  | nil => intro C; rfl
  | cons Δ Δs ih =>
    intro C
    simp only [Algo.cosetChain, Babai.cosetChain]
    split
    · rfl
    · exact congrArg (SIReduction.call _) (funext ih)

/-- Reassociate consecutive phases without changing their calls. -/
theorem aggrBind_assoc {Ω : Type u} {Λ : Type v} {α : Type w} {β : Type z}
    {γ : Type*} (S : SIReduction Ω Λ α) (f : α → SIReduction Ω Λ β)
    (g : β → SIReduction Ω Λ γ) :
    (S.bind f).bind g = S.bind (fun a => (f a).bind g) := by
  induction S with
  | done a => rfl
  | call J k ih => exact congrArg (SIReduction.call J) (funext ih)

/-- One job adds its answer to the union accumulated so far. -/
def aggrUnionStep {Ω : Type u} {Λ : Type v} (A : Set (Perm Ω))
    (S : SIReduction Ω Λ (Set (Perm Ω))) : SIReduction Ω Λ (Set (Perm Ω)) :=
  S.bind fun B => .done (A ∪ B)

/-- A left fold of unions and `unionAnswers` give the same reduction. -/
theorem aggrUnionFold_eq {Ω : Type u} {Λ : Type v}
    (Ss : List (SIReduction Ω Λ (Set (Perm Ω)))) (A : Set (Perm Ω)) :
    phaseFold aggrUnionStep A Ss =
      (unionAnswers Ss).bind (fun B => .done (A ∪ B)) := by
  induction Ss generalizing A with
  | nil => simp [phaseFold, unionAnswers, SIReduction.bind]
  | cons S Ss ih =>
    simp only [phaseFold, aggrUnionStep, aggrBind_assoc, SIReduction.bind,
      ih, unionAnswers]
    simp only [Set.union_assoc]

section Union

variable {ι ω α Ω Λ : Type*} {R : Round ι ω α}
  {decI : ι → SIInstance Ω Λ} {decA : α → Set (Perm Ω)} {I : ι}

/-- All branches admitted by a phase return its mathematical value. -/
theorem aggrLoopMatchK_value {β : Type*} {w j : ℕ} {s : ω}
    {S : SIReduction Ω Λ β} {Q : β → ℕ → ℕ → ω → Prop}
    (h : LoopMatchK R decI decA I w j s S Q) :
    LoopMatchK R decI decA I w j s S (fun b w' j' s' => Q b w' j' s' ∧ b = S.run) := by
  induction h with
  | done w j s b Q hQ => exact .done w j s b _ ⟨hQ, rfl⟩
  | call w j s J k Q hc hn ih => exact .call w j s J k _ hc ih

/-- Keep the value equation when composing a raw phase with a state update. -/
theorem aggrPhaseMatch_value {β : Type*} {c j : ℕ} {s : ω}
    {S : SIReduction Ω Λ β} {Q : β → ℕ → ω → Prop}
    (h : PhaseMatch R decI decA I c j s S Q) :
    PhaseMatch R decI decA I c j s S (fun b j' s' => Q b j' s' ∧ b = S.run) := by
  intro r
  exact loopMatchK_mono_Q (fun _ _ _ _ hb => ⟨hb.1.1, hb.1.2, hb.2⟩)
    (aggrLoopMatchK_value (h r))

/-- A union of reductions is one phase. The invariant may decode the raw
accumulator to the hull of `A`, instead of to `A` itself. -/
theorem aggrPhaseMatch_unionAnswers
    (cost : SIReduction Ω Λ (Set (Perm Ω)) → ℕ)
    (Inv : List (SIReduction Ω Λ (Set (Perm Ω))) → Set (Perm Ω) → ℕ → ω → Prop)
    (hstep : ∀ S Ss A j s, Inv (S :: Ss) A j s →
      PhaseMatch R decI decA I (cost S) j s S
        (fun B j' s' => Inv Ss (A ∪ B) j' s'))
    (Ss : List (SIReduction Ω Λ (Set (Perm Ω)))) (j : ℕ) (s : ω)
    (h : Inv Ss ∅ j s) :
    PhaseMatch R decI decA I (Ss.map cost).sum j s (unionAnswers Ss)
      (fun B j' s' => Inv [] B j' s') := by
  have hf := phaseMatch_fold (R := R) (decI := decI) (decA := decA) (I := I)
    (step := aggrUnionStep) (cost := cost) (Inv := Inv) (by
      intro S Ss A j s hA
      have hm := phaseMatch_bind (hstep S Ss A j s hA)
        (fun B j' s' hB => phaseMatch_done hB)
      simpa only [Nat.add_zero] using hm) Ss ∅ j s h
  rw [aggrUnionFold_eq] at hf
  simp only [Set.empty_union, bind_done] at hf
  exact hf

/-- Sec. 13.1, line 04e: run the chains in representative order and union
their answers. Each chain costs at most the number of windows. -/
theorem aggrPhaseMatch_strongDescent [Fintype Ω] [DecidableEq Ω]
    (N : Subgroup (Perm Ω)) (x y : Ω → Λ) (L : List (Perm Ω))
    (Δs : List (Set Ω))
    (Inv : List (Perm Ω) → Set (Perm Ω) → ℕ → ω → Prop)
    (hstep : ∀ σ σs A j s, Inv (σ :: σs) A j s →
      PhaseMatch R decI decA I Δs.length j s
        (Babai.cosetChain x y Δs (σ • (N : Set (Perm Ω))))
        (fun B j' s' => Inv σs (A ∪ B) j' s'))
    (j : ℕ) (s : ω) (h : Inv L ∅ j s) :
    PhaseMatch R decI decA I (L.length * Δs.length) j s
      (strongDescent N x y L Δs) (fun B j' s' => Inv [] B j' s') := by
  let chain := fun σ : Perm Ω => Babai.cosetChain x y Δs (σ • (N : Set (Perm Ω)))
  have hf := phaseMatch_fold_const (R := R) (decI := decI) (decA := decA) (I := I)
    (step := fun A σ => aggrUnionStep A (chain σ)) (c := Δs.length) (Inv := Inv)
    (by
      intro σ σs A j s hA
      have hm := phaseMatch_bind (hstep σ σs A j s hA)
        (fun B j' s' hB => phaseMatch_done hB)
      simpa only [Nat.add_zero] using hm) L ∅ j s h
  have he : ∀ (σs : List (Perm Ω)) A,
      phaseFold (fun A σ => aggrUnionStep A (chain σ)) A σs =
        phaseFold aggrUnionStep A (σs.map chain) := by
    intro σs
    induction σs with
    | nil => intro A; rfl
    | cons σ σs ih =>
      intro A
      simp only [phaseFold, List.map_cons]
      exact congrArg (SIReduction.bind _) (funext ih)
  rw [he, aggrUnionFold_eq] at hf
  simp only [Set.empty_union, bind_done] at hf
  exact hf

end Union

end Algo
