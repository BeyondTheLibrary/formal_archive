/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: the strings of every call of Cor. 12.0.10 (`Babai.cosetTopAction4With`)
take their values among those of the two input strings. The round of Sec. 15, lines 5–7, uses
this at outcome (2a) of Theorem 13.2.1 to pass the calls of Cor. 12.0.10 through the checked
window normalization of the aggregate carrier (`Algo.aggnCheckedWindow`), which clamps the
string values at `2n`.
-/
import Workspace.Algo.TopFourAggregate

/-!
# The call strings of Cor. 12.0.10

`Algo.AllCalls P R` says that every call node of the tree `R`, on every branch, satisfies `P`;
it implies that the executed calls satisfy `P` (`Algo.AllCalls.mem_calls`) and is closed under
`bind`, `expand` and the window transport (`Babai.SIReduction.window`).

`Algo.StrValsIn V J` says that both strings of the instance `J` take values in `V`.  Every
call of Cor. 12.0.10 has this property when the two input strings do
(`Algo.allCalls_cosetTopAction4With`): the calls either carry the input strings, the second
one translated by a permutation (the alignment of Cor. 12.0.10), or their restrictions to a
window extended by the first string outside the window.
-/

namespace Algo
open Babai Equiv
open scoped Classical

universe u v w w'

section AllCalls

variable {Ω : Type u} {A : Type v} {α : Type w} {β : Type w'}

/-- Every call node of the tree, on every branch, satisfies `P`. -/
def AllCalls (P : SIInstance Ω A → Prop) : SIReduction Ω A α → Prop
  | .done _ => True
  | .call I k => P I ∧ ∀ a, AllCalls P (k a)

@[simp] theorem allCalls_done (P : SIInstance Ω A → Prop) (a : α) :
    AllCalls P (SIReduction.done (Ω := Ω) (A := A) a) := trivial

@[simp] theorem allCalls_call {P : SIInstance Ω A → Prop} {I : SIInstance Ω A}
    {k : Set (Perm Ω) → SIReduction Ω A α} :
    AllCalls P (SIReduction.call I k) ↔ P I ∧ ∀ a, AllCalls P (k a) := Iff.rfl

theorem AllCalls.mem_calls {P : SIInstance Ω A → Prop} :
    ∀ {R : SIReduction Ω A α}, AllCalls P R → ∀ J ∈ R.calls, P J
  | .done _, _, J, hJ => by simp at hJ
  | .call I k, h, J, hJ => by
    rw [SIReduction.calls_call, List.mem_cons] at hJ
    rcases hJ with rfl | hJ
    · exact h.1
    · exact AllCalls.mem_calls (h.2 _) J hJ

theorem AllCalls.bind {P : SIInstance Ω A → Prop} {g : β → SIReduction Ω A α} :
    ∀ {R : SIReduction Ω A β}, AllCalls P R → (∀ b, AllCalls P (g b)) →
      AllCalls P (R.bind g)
  | .done b, _, hg => hg b
  | .call I k, h, hg => ⟨h.1, fun a => AllCalls.bind (h.2 a) hg⟩

theorem AllCalls.expand {P Q : SIInstance Ω A → Prop}
    {f : SIInstance Ω A → SIReduction Ω A (Set (Perm Ω))}
    (hf : ∀ I, Q I → AllCalls P (f I)) : ∀ {R : SIReduction Ω A α}, AllCalls Q R →
      AllCalls P (R.expand f)
  | .done a, _ => trivial
  | .call I k, h => AllCalls.bind (hf I h.1) (fun ans => AllCalls.expand hf (h.2 ans))

theorem AllCalls.window [Fintype Ω] [DecidableEq Ω] {K : Subgroup (Perm Ω)} {Δ : Set Ω}
    {hK : IsInvariant K Δ} {x₀ : Ω → A} {P : SIInstance Ω A → Prop} {Q : SIInstance Δ A → Prop}
    (hQ : ∀ J, Q J → P (windowInstance K Δ hK x₀ J)) :
    ∀ {R : SIReduction Δ A α}, AllCalls Q R → AllCalls P (SIReduction.window K Δ hK x₀ R)
  | .done a, _ => trivial
  | .call J k, h => ⟨hQ J h.1, fun a => AllCalls.window hQ (h.2 _)⟩

/-- Both strings of the instance take values in `V`. -/
def StrValsIn (V : Set A) (J : SIInstance Ω A) : Prop := (∀ u, J.x u ∈ V) ∧ ∀ u, J.y u ∈ V

end AllCalls

section Strings

variable {Ω : Type u} {A : Type v} [Fintype Ω] [DecidableEq Ω] {V : Set A}

theorem allCalls_cosetChain {x y : Ω → A} (hx : ∀ u, x u ∈ V) (hy : ∀ u, y u ∈ V) :
    ∀ (Δs : List (Set Ω)) (C : Set (Perm Ω)), AllCalls (StrValsIn V) (Babai.cosetChain x y Δs C)
  | [], C => by rw [Babai.cosetChain]; trivial
  | Δ :: rest, C => by
    rw [Babai.cosetChain]
    split_ifs
    · trivial
    · exact ⟨⟨hx, hy⟩, fun a => allCalls_cosetChain hx hy rest a⟩

theorem allCalls_cosetLiftAll {G : Subgroup (Perm Ω)} {H : Type w} [Group H] (ϕ : G →* H)
    {x y : Ω → A} (hx : ∀ u, x u ∈ V) (hy : ∀ u, y u ∈ V) :
    ∀ l : List H, AllCalls (StrValsIn V) (cosetLiftAll ϕ x y l)
  | [] => by rw [cosetLiftAll]; trivial
  | σ :: rest => by
    rw [cosetLiftAll]
    refine AllCalls.bind ⟨⟨hx, hy⟩, fun _ => trivial⟩ (fun a => ?_)
    exact AllCalls.bind (allCalls_cosetLiftAll ϕ hx hy rest) (fun _ => trivial)

theorem allCalls_cosetGiantAWith {G : Subgroup (Perm Ω)} {m : ℕ}
    (ψ : G →* alternatingGroup (Fin m)) (S : List (alternatingGroup (Fin m)))
    (E : OrbitEnum (kerSubgroup ψ)) {x y : Ω → A} (hx : ∀ u, x u ∈ V) (hy : ∀ u, y u ∈ V) :
    AllCalls (StrValsIn V) (cosetGiantAWith ψ S E x y) := by
  rw [cosetGiantAWith]
  refine AllCalls.expand (Q := StrValsIn V) ?_ ?_
  · intro J hJ
    exact allCalls_cosetChain hJ.1 hJ.2 _ _
  · rw [cosetTopAction1]
    exact AllCalls.bind (allCalls_cosetLiftAll _ hx hy _) (fun _ => trivial)

theorem allCalls_cosetTopAction3With {G : Subgroup (Perm Ω)} {m : ℕ} (ϕ : G →* Perm (Fin m))
    (S : List (alternatingGroup (Fin m))) (O : TopActionOdd ϕ)
    (E : OrbitEnum (kerSubgroup ϕ)) {x y : Ω → A} (hx : ∀ u, x u ∈ V) (hy : ∀ u, y u ∈ V) :
    AllCalls (StrValsIn V) (cosetTopAction3With ϕ S O E x y) := by
  rw [cosetTopAction3With]
  refine AllCalls.bind (allCalls_cosetGiantAWith _ _ _ hx hx) (fun r0 => ?_)
  by_cases h0 : r0 = none
  · rw [if_pos h0]; trivial
  · rw [if_neg h0]
    refine AllCalls.bind (allCalls_cosetChain hx hy _ _) (fun s1 => ?_)
    by_cases hr : ϕ.range ≤ alternatingGroup (Fin m)
    · rw [if_pos hr]; trivial
    · rw [if_neg hr]
      exact AllCalls.bind (allCalls_cosetChain hx hy _ _) (fun _ => trivial)

theorem allCalls_cosetWindowTopAction3With {m : ℕ} (K : Subgroup (Perm Ω)) (Δ : Set Ω)
    (hinv : IsInvariant K Δ) (ϕ : restrictTo K Δ hinv →* Perm (Fin m))
    (S : List (alternatingGroup (Fin m))) (O : TopActionOdd ϕ) (E : OrbitEnum (kerSubgroup ϕ))
    {x y : Ω → A} (hx : ∀ u, x u ∈ V) (hy : ∀ u, y u ∈ V) :
    AllCalls (StrValsIn V) (cosetWindowTopAction3With K Δ hinv ϕ S O E x y) := by
  rw [cosetWindowTopAction3With]
  refine AllCalls.bind ?_ (fun _ => trivial)
  refine AllCalls.window (Q := StrValsIn V) (fun J hJ => ⟨fun u => ?_, fun u => ?_⟩)
    (allCalls_cosetTopAction3With ϕ S O E (fun w => hx w) (fun w => hy w))
  · show extendStr Δ x J.x u ∈ V
    unfold extendStr
    split_ifs
    · exact hJ.1 _
    · exact hx u
  · show extendStr Δ x J.y u ∈ V
    unfold extendStr
    split_ifs
    · exact hJ.2 _
    · exact hx u

/-- **The calls of Cor. 12.0.10 carry strings with values among those of the inputs.** -/
theorem allCalls_cosetTopAction4With {m : ℕ} {G : Subgroup (Perm Ω)} {κ : Type w}
    (hG : IsTransitive G) (ϕ : G →* Perm (Fin m))
    (hϕ : IsGiantRep ϕ) (hk : VeryLargeK m (maxOrbitLength G))
    (col : (Ω → A) → Fin m → κ) (c : κ) {x y : Ω → A}
    (hC : m < 2 * (colorClass col x c).ncard)
    (E : TopAction4Data hG ϕ hϕ hk (colorClass col x c) hC) (τ : G)
    (hx : ∀ u, x u ∈ V) (hy : ∀ u, y u ∈ V) :
    AllCalls (StrValsIn V) (cosetTopAction4With hG ϕ hϕ hk col c x y hC E τ) := by
  rw [cosetTopAction4With]
  split_ifs
  · refine AllCalls.bind ?_ (fun _ => trivial)
    rw [cosetTopAction4BodyWith]
    refine AllCalls.bind (allCalls_cosetWindowTopAction3With _ _ _ _ _ _ _ hx
      (fun u => hy _)) (fun r => ?_)
    rcases r with _ | S
    · trivial
    · exact allCalls_cosetChain hx (fun u => hy ((τ : Perm Ω)⁻¹⁻¹ u)) _ _
  · trivial

end Strings

section Aggregate

variable {c n m : ℕ} {C : AggnPhaseCtx} {s : AggnAggregateState}
    {ϕ : decGroup n C.1.1.2 →* Perm (Fin m)}
    (hC : AggnPhaseCtxWF c n m C ϕ) (hs : AggnStoresComplete c ϕ s.1.2.1)
    (hG : LocalCertSetting (decGroup n C.1.1.2) ϕ)
    (hm : HugeM m (Nat.card (Fin n)))
    (h2a : aggnAggregateGiantBranch (C, s) = true)

/-- §15, line 5, outcome (2a): **every call of the tree of Cor. 12.0.10 has strings with
values at most `2n`**, when the two input strings do. -/
theorem allCalls_top4AggregateTree (hx : ∀ u, decStrN n C.2.1 u ≤ 2 * n)
    (hy : ∀ u, decStrN n C.2.2.1 u ≤ 2 * n) :
    AllCalls (StrValsIn {v | v ≤ 2 * n}) (top4AggregateTree hC hs hG hm h2a) := by
  unfold top4AggregateTree Top4Source.autoTree
  exact allCalls_cosetTopAction4With _ _ _ _ _ _ _ _ _ hx hy

end Aggregate

end Algo
