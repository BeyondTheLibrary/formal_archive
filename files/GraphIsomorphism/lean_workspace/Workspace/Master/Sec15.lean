/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 15: the data the tests of Procedure String-Isomorphism produce, and the branches
that are named reductions.
-/
import Workspace.Master.TestSet
import Workspace.Master.KAryOfString
import Workspace.Master.CosetWindow
import Workspace.Master.CosetEnums
import Workspace.TopAction.CosetTopAction4

/-!
# The tests of Sec. 15 as data

`Workspace/Master/Assemble.lean` turns seven branches into one round, with the five tests of
the pseudo-code as abstract predicates on an instance.  The named reductions of Secs. 11–14
do not take an instance: they take the data that lines 1–3 produce — the window, the group
induced on it, a system of imprimitivity, the Johnson parameter `m`, and the giant
representation `ϕ : G → S(Γ)`.  This file is the layer in between.

`Babai.JohnsonCaseData I` is that data, and the test of line 1 is

> `Babai.IsJohnson I := Nonempty (JohnsonCaseData I)`.

The data itself is recovered by `Classical.choice` (`Babai.johnsonData`).  Choice costs
nothing here: `Iso_G(x,y)` does not depend on it, and both strings of one instance are
looked at through the *same* chosen data, which is all that canonicity relative to
`(G, ϕ)` needs.  The Johnson parameter `Babai.param` and the parameter `t` of the standard
blocks (`Babai.tParam`) are read off the chosen data.

**The window.**  An instance carries a window `Δ ⊆ Ω`, and the group of line 2 is the group
`G = K^Δ` induced on the window (Notation 2.2.1), which acts on the type `↥Δ`.  Every named
reduction of Secs. 11–14 therefore runs on `↥Δ` and is carried back to `Ω` by
`Babai.SIReduction.window`; `Babai.liftWindow` is that transport, packaged with the
translation of the answer (`Babai.windowPreim`).  The window sizes and the number of calls
are unchanged by it (`Babai.calls_liftWindow`), so the bounds proved on `↥Δ` are exactly the
bounds the Master Algorithm needs.
-/

universe u v

namespace Babai

open MulAction Equiv Equiv.Perm

/-! ### Transporting a reduction on the window back to `Ω` -/

section LiftWindow

variable {Ω : Type u} {A : Type v} {K : Subgroup (Equiv.Perm Ω)} {Δ : Set Ω}

/-- A reduction on the window `Δ`, read as a reduction on `Ω`.

The reduction `R` works on the type `↥Δ` with the group `K^Δ` induced on the window; its
calls are lifted by `Babai.windowInstance`, and its value, a set of permutations of `Δ`, is
turned into the set of permutations of `Ω` above it (`Babai.windowPreim`).  This is the
passage the paper makes silently whenever it says "we now have an instance of String
Isomorphism with window `Δ`". -/
noncomputable def liftWindow (K : Subgroup (Equiv.Perm Ω)) (Δ : Set Ω)
    (h : IsInvariant K Δ) (x₀ : Ω → A) (R : SIReduction Δ A (Set (Equiv.Perm Δ))) :
    SIReduction Ω A (Set (Equiv.Perm Ω)) :=
  (SIReduction.window K Δ h x₀ R).bind fun s => .done (windowPreim K Δ h s)

/-- The lifted reduction is correct: if `R` computes `Iso_{K^Δ}(x|_Δ, y|_Δ)` then the lift
computes `Iso^Δ_K(x,y)`.  The two are matched by `Babai.wIso_eq_windowPreim`. -/
theorem run_liftWindow (h : IsInvariant K Δ) (x y : Ω → A)
    (R : SIReduction Δ A (Set (Equiv.Perm Δ)))
    (hK : ∀ J ∈ R.calls, J.K ⊆ (restrictTo K Δ h : Set (Equiv.Perm Δ)))
    (hrun : R.run = strIso ((restrictTo K Δ h : Subgroup (Equiv.Perm Δ)) :
      Set (Equiv.Perm Δ)) (restrictStr Δ x) (restrictStr Δ y)) :
    (liftWindow K Δ h x R).run = wIso Δ (K : Set (Equiv.Perm Ω)) x y := by
  rw [liftWindow, SIReduction.run_bind, SIReduction.run_done,
    SIReduction.run_window h x R hK, hrun, ← wIso_eq_windowPreim]

/-- The lifted reduction makes exactly the lifted calls. -/
theorem calls_liftWindow (h : IsInvariant K Δ) (x₀ : Ω → A)
    (R : SIReduction Δ A (Set (Equiv.Perm Δ)))
    (hK : ∀ J ∈ R.calls, J.K ⊆ (restrictTo K Δ h : Set (Equiv.Perm Δ))) :
    (liftWindow K Δ h x₀ R).calls = R.calls.map (windowInstance K Δ h x₀) := by
  rw [liftWindow, SIReduction.calls_bind, SIReduction.calls_done, List.append_nil,
    SIReduction.calls_window h x₀ R hK]

/-- The lift changes neither the number of calls nor their window sizes: to every call of
the lift belongs a call of `R` with the same window size. -/
theorem calls_liftWindow_windowSize (h : IsInvariant K Δ) (x₀ : Ω → A)
    (R : SIReduction Δ A (Set (Equiv.Perm Δ)))
    (hK : ∀ J ∈ R.calls, J.K ⊆ (restrictTo K Δ h : Set (Equiv.Perm Δ))) :
    ∀ J ∈ (liftWindow K Δ h x₀ R).calls,
      ∃ J' ∈ R.calls, J.windowSize = J'.windowSize := by
  intro J hJ
  rw [calls_liftWindow h x₀ R hK, List.mem_map] at hJ
  obtain ⟨J', hJ', rfl⟩ := hJ
  exact ⟨J', hJ', windowSize_windowInstance h x₀ J'⟩

theorem calls_length_liftWindow (h : IsInvariant K Δ) (x₀ : Ω → A)
    (R : SIReduction Δ A (Set (Equiv.Perm Δ)))
    (hK : ∀ J ∈ R.calls, J.K ⊆ (restrictTo K Δ h : Set (Equiv.Perm Δ))) :
    ((liftWindow K Δ h x₀ R).calls).length = (R.calls).length := by
  rw [calls_liftWindow h x₀ R hK, List.length_map]

/-- The lift of a reduction whose calls are group instances has group instances for its
calls (`Babai.isGroupInstance_windowInstance`). -/
theorem calls_liftWindow_isGroupInstance (h : IsInvariant K Δ) (x₀ : Ω → A)
    (R : SIReduction Δ A (Set (Equiv.Perm Δ)))
    (hK : ∀ J ∈ R.calls, J.K ⊆ (restrictTo K Δ h : Set (Equiv.Perm Δ)))
    (hgrp : ∀ J ∈ R.calls, IsGroupInstance J) :
    ∀ J ∈ (liftWindow K Δ h x₀ R).calls, IsGroupInstance J := by
  intro J hJ
  rw [calls_liftWindow h x₀ R hK, List.mem_map] at hJ
  obtain ⟨J', hJ', rfl⟩ := hJ
  exact isGroupInstance_windowInstance h x₀ (hgrp J' hJ')

/-- Every call of a reduction lifted to `Ω` is a coset instance, as soon as every call
downstairs is. -/
theorem calls_liftWindow_isCosetInstance (h : IsInvariant K Δ) (x₀ : Ω → A)
    (R : SIReduction Δ A (Set (Equiv.Perm Δ)))
    (hK : ∀ J ∈ R.calls, J.K ⊆ (restrictTo K Δ h : Set (Equiv.Perm Δ)))
    (hcoset : ∀ J ∈ R.calls, IsCosetInstance (restrictTo K Δ h) J) :
    ∀ J ∈ (liftWindow K Δ h x₀ R).calls, IsCosetInstance K J := by
  intro J hJ
  rw [calls_liftWindow h x₀ R hK, List.mem_map] at hJ
  obtain ⟨J', hJ', rfl⟩ := hJ
  exact isCosetInstance_windowInstance h x₀ (hcoset J' hJ')

end LiftWindow

/-! ### The data of lines 1–3 -/

section Data

variable {Ω : Type u} {A : Type v} [Fintype Ω] [DecidableEq Ω]

open scoped Classical in
/-- §15, what lines 1–3 leave on the table.

Line 1 (Procedure Reduce-to-Johnson, Sec. 11.3) ends in the Johnson case (Def. 11.4.1):
the instance is with respect to a group `K`, the window `Δ` is `K`-invariant, the group
`G = K^Δ` induced on the window is transitive, and `G` has a system `ℬ` of imprimitivity on
which it acts as a Johnson group `S_m^{(t)}` or `A_m^{(t)}`.  Line 3 adds the giant
representation `ϕ : G → S(Γ)`, `Γ` of size `m`, which the paper says is *"inferred from
`G`"*.

Two fields record facts that hold in the Johnson case but that this development does not
derive from the others, and that the construction of the data must therefore supply:

* `two_blocks` — the block system is nontrivial, which is what makes line 2 an
  *imprimitive* Luks reduction; in the Johnson case the number of blocks is `C(m,t) ≥ 2`;
* `window_large` — the window has at least `64` points.  This is not an extra hypothesis
  on any theorem: line 2 of Procedure Reduce-to-Johnson (Sec. 11.3) reads *"if `|G| < C₀`
  for some absolute constant `C₀` then compute `Iso_G(x,y)` by brute force, exit"*, so an
  instance that reaches line 2 of Sec. 15 has a window above any fixed absolute size.  It
  is what turns the test of line 2, `m > ℓ = (log n)³`, into the numeric hypotheses of
  Theorem 10.5.1 and Cor. 12.0.10 (`Babai.hugeM_of_line2`). -/
structure JohnsonCaseData (I : SIInstance Ω A) where
  /-- The group the instance is with respect to. -/
  K : Subgroup (Equiv.Perm Ω)
  /-- The candidate set of the instance is that group. -/
  isGroup : I.K = (K : Set (Equiv.Perm Ω))
  /-- The window is invariant, so `K` acts on it. -/
  invariant : IsInvariant K I.Δ
  /-- The system of imprimitivity of the group induced on the window. -/
  ℬ : Set (Set I.Δ)
  /-- The Johnson parameter `m = |Γ|`. -/
  m : ℕ
  /-- The parameter `t` of the standard blocks `Φ = {B_T | T ∈ Γ^{(t)}}`. -/
  t : ℕ
  /-- Definition 11.4.1: the Johnson case. -/
  johnson : IsJohnsonCase (restrictTo K I.Δ invariant) ℬ m t
  /-- The block system is nontrivial: there are at least two blocks. -/
  two_blocks : ∃ B₁ ∈ ℬ, ∃ B₂ ∈ ℬ, B₁ ≠ B₂
  /-- Line 3: *"let `ϕ : G → S(Γ)` be a giant representation (inferred from `G`)"*. -/
  ϕ : (restrictTo K I.Δ invariant) →* Equiv.Perm (Fin m)
  /-- Line 3: `ϕ` is a giant representation. -/
  giant : IsGiantRep ϕ
  /-- `Γ` is no larger than the window: `m ≤ |Φ| ≤ n`. -/
  param_le : m ≤ I.windowSize
  /-- The window is not bounded: Reduce-to-Johnson has not exited by brute force. -/
  window_large : 64 ≤ I.windowSize

namespace JohnsonCaseData

variable {I : SIInstance Ω A}

/-- The group `G = K^Δ` induced on the window, the group of lines 2–7a. -/
def windowGroup (d : JohnsonCaseData I) : Subgroup (Equiv.Perm I.Δ) :=
  restrictTo d.K I.Δ d.invariant

/-- `G` is transitive on the window (Def. 11.4.1). -/
theorem transitive (d : JohnsonCaseData I) : IsTransitive d.windowGroup :=
  d.johnson.transitive

/-- `ℬ` is a system of imprimitivity for `G` (Def. 11.4.1). -/
theorem system (d : JohnsonCaseData I) :
    IsSystemOfImprimitivity d.windowGroup Set.univ d.ℬ :=
  d.johnson.system

/-- The window is nonempty, because `G` is transitive on it. -/
theorem one_le_windowSize (d : JohnsonCaseData I) : 1 ≤ I.windowSize := by
  have : Nonempty I.Δ := d.transitive.nonempty
  obtain ⟨w⟩ := this
  have hne : I.Δ.Nonempty := ⟨(w : Ω), w.2⟩
  have hfin : I.Δ.Finite := Set.toFinite _
  exact (Set.ncard_pos hfin).2 hne

end JohnsonCaseData

/-! ### Hinted instances

Sec. 14.2 measures a pair `(G, ϕ)`: *"Let `T(G, ϕ)` be the maximum cost over all input
strings for the pair `(G, ϕ)`"*, and line 11 of Procedure Align hands `ϕ*` down *"for
recursive processing of the corresponding window"*.  The Johnson parameter is **not**
determined by the group: `G = S_b × S_m` on `[b] × [m]` has two giant representations and
two minimal block systems, so the parameter of a recursive call cannot be recovered from
the call alone.

So the recursion of Sec. 15 runs on instances that **carry** their Johnson data: a
`Babai.HintedInstance` is a String Isomorphism instance together with the outcome of
lines 1–3 for it, when there is one.  The tests of lines 1–4 read the hint, and each branch
says with `lift` what hint it attaches to each of its calls. -/

/-- §15: a String Isomorphism instance together with the data lines 1–3 have found for it,
if any.  This is the paper's pair `(G, ϕ)` of Sec. 14.2. -/
structure HintedInstance (Ω : Type u) (A : Type v) [Fintype Ω] [DecidableEq Ω] where
  /-- The String Isomorphism instance. -/
  inst : SIInstance Ω A
  /-- The Johnson case data lines 1–3 have produced for it, if any. -/
  hint : Option (JohnsonCaseData inst)

namespace HintedInstance

variable (i : HintedInstance Ω A)

/-- The window size of a hinted instance. -/
noncomputable def win : ℕ := i.inst.windowSize

end HintedInstance

/-- §15, the test of line 1: the instance is already in the Johnson case, so Procedure
Reduce-to-Johnson has nothing left to do.  Line 1 is taken exactly when this fails.

With hinted instances this is not a property of the group but a property of the instance as
the algorithm carries it: the data of lines 1–3 has been attached to it. -/
def IsJohnson (i : HintedInstance Ω A) : Prop := i.hint.isSome = true

/-- The data of lines 1–3 of an instance that carries it.  No choice is involved: it is the
hint the previous round attached. -/
def johnsonData {i : HintedInstance Ω A} (h : IsJohnson i) : JohnsonCaseData i.inst :=
  i.hint.get h

theorem hint_eq_some {i : HintedInstance Ω A} (h : IsJohnson i) :
    i.hint = some (johnsonData h) := (Option.some_get h).symm

theorem isJohnson_of_hint {I : SIInstance Ω A} {d : JohnsonCaseData I} :
    IsJohnson (⟨I, some d⟩ : HintedInstance Ω A) := rfl

theorem not_isJohnson_of_none {I : SIInstance Ω A} :
    ¬ IsJohnson (⟨I, none⟩ : HintedInstance Ω A) := by simp [IsJohnson]

theorem johnsonData_of_hint {I : SIInstance Ω A} {d : JohnsonCaseData I} :
    johnsonData (isJohnson_of_hint (d := d)) = d := rfl

/-- §15, line 2: **the Johnson parameter `m`** of the hinted instance.

Outside the Johnson case there is no Johnson parameter, and the instance is given the value
`2n`.  This is not an arbitrary convention: `param` is the second component of the measure
of `Workspace/Master/Procedure.lean`, and `2n` is the top of its range, so an instance that
Procedure Reduce-to-Johnson has not processed yet ranks above every Johnson case on the same
window.  That is what makes line 1 of Sec. 15 *progress*: the Johnson case reached at the
end of Procedure Reduce-to-Johnson (Sec. 11.3, step 6) has the same window, and its Johnson
parameter `m ≤ n` satisfies `2m ≤ 2n`, so the second component of the measure drops.  It is
also what recurrence (ii) of Sec. 11.4 says, `T_trans(x) ≤ m(T_Jh(x) + p(x))`: the cost of
a transitive instance is that of a Johnson case on the same window, times `m`. -/
noncomputable def param (i : HintedInstance Ω A) : ℕ :=
  match i.hint with
  | some d => d.m
  | none => 2 * i.inst.windowSize

/-- §15, line 3: the parameter `t` of the standard blocks, `0` outside the Johnson case. -/
noncomputable def tParam (i : HintedInstance Ω A) : ℕ :=
  match i.hint with
  | some d => d.t
  | none => 0

@[simp] theorem param_some {I : SIInstance Ω A} (d : JohnsonCaseData I) :
    param (⟨I, some d⟩ : HintedInstance Ω A) = d.m := rfl

@[simp] theorem param_none {I : SIInstance Ω A} :
    param (⟨I, none⟩ : HintedInstance Ω A) = 2 * I.windowSize := rfl

@[simp] theorem tParam_some {I : SIInstance Ω A} (d : JohnsonCaseData I) :
    tParam (⟨I, some d⟩ : HintedInstance Ω A) = d.t := rfl

theorem param_eq {i : HintedInstance Ω A} (h : IsJohnson i) :
    param i = (johnsonData h).m := by
  obtain ⟨I, hnt⟩ := i
  cases hnt with
  | none => exact absurd h (by simp [IsJohnson])
  | some d => rfl

theorem tParam_eq {i : HintedInstance Ω A} (h : IsJohnson i) :
    tParam i = (johnsonData h).t := by
  obtain ⟨I, hnt⟩ := i
  cases hnt with
  | none => exact absurd h (by simp [IsJohnson])
  | some d => rfl

/-- Outside the Johnson case the parameter is `2n`. -/
theorem param_eq_of_not {i : HintedInstance Ω A} (h : ¬ IsJohnson i) :
    param i = 2 * i.inst.windowSize := by
  obtain ⟨I, hnt⟩ := i
  cases hnt with
  | none => rfl
  | some d => exact absurd rfl h

/-- The Johnson parameter never exceeds twice the window size: in the Johnson case it is
`m ≤ n` (`Γ` is a quotient of a subset of the window), outside it is `2n`. -/
theorem param_le (i : HintedInstance Ω A) : param i ≤ 2 * i.inst.windowSize := by
  by_cases h : IsJohnson i
  · rw [param_eq h]; have := (johnsonData h).param_le; omega
  · rw [param_eq_of_not h]

/-- In the Johnson case the parameter is at most the window size. -/
theorem param_le_windowSize {i : HintedInstance Ω A} (h : IsJohnson i) :
    param i ≤ i.inst.windowSize := by
  rw [param_eq h]; exact (johnsonData h).param_le

/-- An instance outside the Johnson case carries no hint. -/
theorem eq_none_of_not_isJohnson {i : HintedInstance Ω A} (h : ¬ IsJohnson i) :
    i = ⟨i.inst, none⟩ := by
  obtain ⟨I, hnt⟩ := i
  cases hnt with
  | none => rfl
  | some d => exact absurd rfl h

/-- The Johnson parameter of an instance that carries a hint is at most its window size. -/
theorem param_le_windowSize_of_some {J : SIInstance Ω A} (d : JohnsonCaseData J) :
    param (⟨J, some d⟩ : HintedInstance Ω A) ≤ J.windowSize := d.param_le

/-- The Johnson parameter of an instance that carries a hint is at most its window size. -/
theorem param_le_windowSize_of_isSome {J : SIInstance Ω A} {o : Option (JohnsonCaseData J)}
    (h : o.isSome = true) : param (⟨J, o⟩ : HintedInstance Ω A) ≤ J.windowSize := by
  cases o with
  | none => exact absurd h (by simp)
  | some d => exact d.param_le

/-- §15, line 4a: the test *"`t = 1`"*. -/
def TIsOne (i : HintedInstance Ω A) : Prop := tParam i = 1

end Data

/-! ### Line 2 as a branch of the round -/

section Line2

open scoped Classical

variable {Ω : Type u} {A : Type v} [Fintype Ω] [DecidableEq Ω] {I : SIInstance Ω A}

namespace JohnsonCaseData

/-- §15, line 2: the action `ψ : G → Ḡ` of the window group on the blocks, with `Ḡ` its
image — the paper's *"the `G`-action `Ḡ` on blocks"*. -/
noncomputable def blockAction (d : JohnsonCaseData I) :
    d.windowGroup →* (blockHom d.windowGroup d.ℬ d.system.permutes).range :=
  (blockHom d.windowGroup d.ℬ d.system.permutes).rangeRestrict

/-- The kernel of `ψ` does not change when `ψ` is corestricted to its image. -/
theorem kerSubgroup_blockAction (d : JohnsonCaseData I) :
    kerSubgroup d.blockAction = blockKernel d.windowGroup d.ℬ d.system.permutes := by
  rw [kerSubgroup, blockKernel, blockAction, MonoidHom.ker_rangeRestrict]

end JohnsonCaseData

/-- §15, line 2, **the multiplicative cost**: `|Ḡ| ≤ m!`.

In the Johnson case `Ḡ` is, after the identification of the blocks with the `t`-subsets of
`Γ`, the Johnson group `S_m^{(t)}` or `A_m^{(t)}`, which is the image of `S_m` or of `A_m`
in its action on `t`-sets; so it has at most `m!` elements.  Line 2 applies it with
`m ≤ ℓ`, giving the paper's multiplicative cost `ℓ!`. -/
theorem card_onBlocks_le_factorial_of_johnson {Δ : Type*} [Fintype Δ] [DecidableEq Δ]
    {G : Subgroup (Equiv.Perm Δ)} {ℬ : Set (Set Δ)} {m t : ℕ}
    (hJ : IsJohnsonCase G ℬ m t) :
    Nat.card (onBlocks G ℬ hJ.system.permutes) ≤ Nat.factorial m := by
  classical
  have hperm := hJ.system.permutes
  -- the two Johnson cases are treated alike: transport, then bound the Johnson group
  have step : ∀ (e : ℬ ≃ binom (Fin m) t) (H : Subgroup (Equiv.Perm (Fin m))),
      (onBlocks G ℬ hperm).map (Equiv.permCongrHom e).toMonoidHom = inducedOnTSets H t →
      Nat.card (onBlocks G ℬ hperm) ≤ Nat.factorial m := by
    intro e H he
    have hinj : Function.Injective (Equiv.permCongrHom e).toMonoidHom :=
      (Equiv.permCongrHom e).injective
    have h1 : Nat.card (onBlocks G ℬ hperm) =
        Nat.card ((onBlocks G ℬ hperm).map (Equiv.permCongrHom e).toMonoidHom) :=
      Nat.card_congr (Subgroup.equivMapOfInjective _ _ hinj).toEquiv
    have h2 : Nat.card (inducedOnTSets H t) ≤ Nat.card H := by
      rw [inducedOnTSets]
      exact Nat.card_le_card_of_surjective
        (fun g : H => (⟨tAction t (g : Equiv.Perm (Fin m)), ⟨g, g.2, rfl⟩⟩ :
          H.map (tAction t)))
        (by rintro ⟨g, hg, hgg, rfl⟩; exact ⟨⟨hg, hgg⟩, rfl⟩)
    have h3 : Nat.card H ≤ Nat.factorial m := by
      have := Subgroup.card_le_card_group H
      rwa [Nat.card_eq_fintype_card (α := Equiv.Perm (Fin m)), Fintype.card_perm,
        Fintype.card_fin] at this
    rw [h1, he]
    omega
  rcases hJ.johnson with ⟨e, he⟩ | ⟨e, he⟩
  · exact step e ⊤ he
  · exact step e (alternatingGroup (Fin m)) he

/-- The identity is in the candidate set of the instance, so the alignment at the root does
nothing. -/
theorem one_mem_K_johnson (d : JohnsonCaseData I) : (1 : Equiv.Perm Ω) ∈ I.K := by
  rw [d.isGroup]; exact d.K.one_mem

/-- §15, **line 2** as a branch of the round: the imprimitive Luks reduction of
`Babai.line2Reduction`, run on the window with the group `G = K^Δ` induced on it and its
action on the blocks, and carried back to `Ω`. -/
noncomputable def line2Coset (d : JohnsonCaseData I) (E : Line2Enum d.blockAction) :
    SIReduction Ω A (Set (Equiv.Perm Ω)) :=
  liftWindow d.K I.Δ d.invariant I.x
    (cosetLine2ReductionWith d.blockAction (restrictStr I.Δ I.x) (restrictStr I.Δ I.y) E)

/-- §15, **line 2** as a branch of the round: the alignment (Remark 11.1.4) of the coset
form `Babai.line2Coset`. -/
noncomputable def line2Branch (d : JohnsonCaseData I) (E : Line2Enum d.blockAction) :
    SIReduction Ω A (Set (Equiv.Perm Ω)) :=
  SIReduction.alignRed I (line2Coset d E)

/-- §15, line 2: **the branch is the alignment of its coset form** (Remark 11.1.4). -/
theorem line2Branch_eq (d : JohnsonCaseData I) (E : Line2Enum d.blockAction) :
    line2Branch d E = SIReduction.alignRed I (line2Coset d E) := rfl

/-- Every call of line 2 stays inside the group induced on the window, which is what lets
the branch be carried back to `Ω`. -/
theorem calls_line2Branch_K (d : JohnsonCaseData I) (E : Line2Enum d.blockAction) :
    ∀ J ∈ (cosetLine2ReductionWith d.blockAction (restrictStr I.Δ I.x)
      (restrictStr I.Δ I.y) E).calls,
      J.K ⊆ (restrictTo d.K I.Δ d.invariant : Set (Equiv.Perm I.Δ)) :=
  calls_cosetLine2ReductionWith_K d.blockAction _ _ E

/-- §15, line 2 in coset form **is correct**. -/
theorem run_line2Coset (d : JohnsonCaseData I) (E : Line2Enum d.blockAction) : (line2Coset d E).run = I.answer := by
  rw [line2Coset,
    run_liftWindow d.invariant I.x I.y _ (calls_line2Branch_K d E)
      (run_cosetLine2ReductionWith d.blockAction _ _ E),
    SIInstance.answer, d.isGroup]

/-- §15, line 2 **is correct**: the branch returns `Iso^Δ_K(x,y)`. -/
theorem run_line2Branch (d : JohnsonCaseData I) (E : Line2Enum d.blockAction) : (line2Branch d E).run = I.answer := by
  rw [line2Branch_eq, run_alignRed_of_one_mem (one_mem_K_johnson d), run_line2Coset d E]

/-- §15, line 2, **the number of calls**: at most `m!` (the paper's multiplicative cost,
`ℓ!` once `m ≤ ℓ`) times the number of orbits of `N`, which is at most `n`. -/
theorem calls_length_line2Branch (d : JohnsonCaseData I) (E : Line2Enum d.blockAction) :
    ((line2Branch d E).calls).length ≤ Nat.factorial d.m * I.windowSize := by
  classical
  rw [line2Branch_eq, calls_length_alignRed, line2Coset,
    calls_length_liftWindow d.invariant I.x _ (calls_line2Branch_K d E)]
  refine le_trans (calls_length_cosetLine2ReductionWith d.blockAction _ _ E) ?_
  have hcard : Fintype.card (blockHom d.windowGroup d.ℬ d.system.permutes).range ≤
      Nat.factorial d.m := by
    rw [← Nat.card_eq_fintype_card]
    exact card_onBlocks_le_factorial_of_johnson d.johnson
  have horb : (orbitList (kerSubgroup d.blockAction)).length ≤ I.windowSize := by
    refine le_trans (length_orbitList_le _) ?_
    rw [SIInstance.windowSize, Nat.card_coe_set_eq]
  exact Nat.mul_le_mul hcard horb

/-- §15, line 2, **the progress**: every call has a window of at most half the size.

The kernel `N` of the action on the blocks fixes every block setwise, so its orbits lie
inside blocks; with at least two blocks `N` is intransitive, and all its orbits have the
same length `n/m' ≤ n/2` (Fact 11.1.8). -/
theorem decreases_line2Branch (d : JohnsonCaseData I) (E : Line2Enum d.blockAction) :
    ∀ J ∈ (line2Branch d E).calls, 2 * J.windowSize ≤ I.windowSize := by
  classical
  intro J hJ
  rw [line2Branch_eq, calls_alignRed, List.mem_map] at hJ
  obtain ⟨J₀, hJ₀, rfl⟩ := hJ
  rw [windowSize_alignInst, line2Coset] at *
  obtain ⟨J', hJ', hsize⟩ :=
    calls_liftWindow_windowSize d.invariant I.x _ (calls_line2Branch_K d E) J₀ hJ₀
  have hwin : J'.Δ ∈ orbitList (kerSubgroup d.blockAction) :=
    calls_cosetLine2ReductionWith_window d.blockAction _ _ E J' hJ'
  obtain ⟨u, hu⟩ := mem_orbitList hwin
  obtain ⟨B₁, hB₁, B₂, hB₂, hne⟩ := d.two_blocks
  have hbound := two_mul_ncard_orbit_le d.transitive
    d.system.isInvariantPartitionOn hB₁ hB₂ hne u
  have hker : kerSubgroup d.blockAction =
      blockKernel d.windowGroup d.ℬ d.system.permutes := d.kerSubgroup_blockAction
  have hn : Fintype.card I.Δ = I.windowSize := by
    rw [← Nat.card_eq_fintype_card, SIInstance.windowSize, Nat.card_coe_set_eq]
  rw [hsize, SIInstance.windowSize, hu, hker, ← hn]
  exact hbound

/-- §15, line 2 in coset form: **every call is a coset instance** with respect to `K`. -/
theorem calls_line2Coset_isCosetInstance (d : JohnsonCaseData I) (E : Line2Enum d.blockAction) :
    ∀ J ∈ (line2Coset d E).calls, IsCosetInstance d.K J :=
  calls_liftWindow_isCosetInstance d.invariant I.x _ (calls_line2Branch_K d E)
    (isCosetInstance_calls_cosetLine2ReductionWith d.blockAction _ _ E)

/-- §15, line 2: **every call is a group instance**. -/
theorem calls_line2Branch_isGroupInstance (d : JohnsonCaseData I) (E : Line2Enum d.blockAction) :
    ∀ J ∈ (line2Branch d E).calls, IsGroupInstance J := by
  intro J hJ
  rw [line2Branch_eq, calls_alignRed, List.mem_map] at hJ
  obtain ⟨J₀, hJ₀, rfl⟩ := hJ
  exact isGroupInstance_alignInst (calls_line2Coset_isCosetInstance d E J₀ hJ₀)

end Line2

/-! ### Line 4b as a branch of the round -/

section Line4b

open scoped Classical

variable {Ω : Type u} {A : Type v} [Fintype Ω] [DecidableEq Ω] {I : SIInstance Ω A}

/-- §15, lines 2 and 4b: the test of line 2, `m > ℓ = (log₂ n)³`, gives the numeric
hypothesis `m ≥ max{16, 4 + 2 log₂ n}` of Cor. 12.0.10.

*Proof.*  Write `L = ⌊log₂ n⌋ ≥ 6`.  Then `m > L³ ≥ 6·6·L ≥ 216`, so `m ≥ 16`, and
`4 + 2 log₂ n < 2L + 6 ≤ L³ < m`. -/
theorem hugeM_of_line2 {n m : ℕ} (hn : 64 ≤ n) (hm : ellOf n < m) : HugeM m n := by
  have hL : 6 ≤ Nat.log 2 n := six_le_natLog hn
  have hlog := logb_lt_natLog_succ (n := n) (by omega)
  rw [ellOf] at hm
  have h1 : 36 * Nat.log 2 n ≤ Nat.log 2 n ^ 3 :=
    calc 36 * Nat.log 2 n = 6 * 6 * Nat.log 2 n := by ring
      _ ≤ Nat.log 2 n * Nat.log 2 n * Nat.log 2 n :=
          Nat.mul_le_mul (Nat.mul_le_mul hL hL) le_rfl
      _ = Nat.log 2 n ^ 3 := by ring
  have h16 : 16 ≤ m := by omega
  have hnat : 2 * Nat.log 2 n + 6 ≤ m := by omega
  have hcast : (2 : ℝ) * (Nat.log 2 n : ℝ) + 6 ≤ (m : ℝ) := by exact_mod_cast hnat
  have h16' : (16 : ℝ) ≤ (m : ℝ) := by exact_mod_cast h16
  rw [HugeM, max_le_iff]
  exact ⟨h16', by linarith⟩

/-- §15, **line 4b**: the data Cor. 12.0.10 is applied to.

Line 4b reads the strings as edge-colored `t`-uniform hypergraphs on `Γ` and tests whether
the relative symmetry defect of `H(x)` is `< 1/2`.  What Cor. 12.0.10 consumes is the
consequence of that test: a canonically defined set `C ⊆ Γ` of more than `m/2` vertices, on
which the automorphism group of `x` induces at least the alternating group.  The set is
given here as a canonical two-coloring of `Γ` together with the color `c` of `C`, which is
the shape of the `col`, `c` arguments of `Babai.Corollary_12_0_10`.

The Sec. 7 symmetry-defect argument supplies the coloring and its properties through
`Babai.smallDefect_data`, as used by `Babai.nonempty_smallDefectData` below. The remaining
fields carry the choices used by the top-action tree. -/
structure SmallDefectData (d : JohnsonCaseData I) where
  /-- The canonical two-coloring of `Γ` that marks the symmetric set `C`. -/
  col : (I.Δ → A) → Fin d.m → Bool
  /-- `C` is canonical: `C(x^σ) = C(x)^{σ^ϕ}`. -/
  canonical : IsCanonicalColoring d.ϕ col
  /-- The color of `C`. -/
  c : Bool
  /-- `|C| > m/2`: the relative symmetry defect is less than `1/2`. -/
  large : d.m < 2 * (colorClass col (restrictStr I.Δ I.x) c).ncard
  /-- On `C`, the automorphisms of `x` induce at least the alternating group — the
  hypothesis `hgiantC` of Cor. 12.0.10. -/
  giantOn : ∀ α : Equiv.Perm (Fin d.m), α ∈ alternatingGroup (Fin d.m) →
      (∀ γ, γ ∉ colorClass col (restrictStr I.Δ I.x) c → α γ = γ) →
      ∃ β ∈ homImage d.ϕ (strAut (d.windowGroup : Set (Equiv.Perm I.Δ))
        (restrictStr I.Δ I.x)),
        ∀ γ ∈ colorClass col (restrictStr I.Δ I.x) c, β γ = α γ

  /-- The supplied labels, ordered generators, odd representative, and window orders. -/
  top : (hm : HugeM d.m (Nat.card I.Δ)) →
    TopAction4Data d.transitive d.ϕ d.giant (veryLargeK_of_hugeM d.transitive hm)
      (colorClass col (restrictStr I.Δ I.x) c) large :=
    fun hm => .default _ _ _ _ _ _ (by
      have h := (hm.largeK_of_two_mul_lt large).eight_lt
      omega)
  /-- The element used in Align, with its class-image specification. -/
  alignment : (hm : HugeM d.m (Nat.card I.Δ)) →
    TopActionAlignment d.ϕ col c (restrictStr I.Δ I.x) (restrictStr I.Δ I.y) :=
    fun hm => .default d.ϕ d.giant (by
      have h : (16 : ℝ) ≤ (d.m : ℝ) := le_trans (le_max_left _ _) hm
      have hm16 : 16 ≤ d.m := by exact_mod_cast h
      omega) col c _ _

/-- Line 4b before the alignment of Remark 11.1.4. -/
noncomputable def line4bBranchCoset (d : JohnsonCaseData I) (s : SmallDefectData d)
    (hm : HugeM d.m (Nat.card I.Δ)) : SIReduction Ω A (Set (Perm Ω)) :=
  liftWindow d.K I.Δ d.invariant I.x
    (cosetTopAction4With d.transitive d.ϕ d.giant (veryLargeK_of_hugeM d.transitive hm)
      s.col s.c (restrictStr I.Δ I.x) (restrictStr I.Δ I.y) s.large (s.top hm) (s.alignment hm).element)

/-- §15, **line 4b** as a branch of the round: Cor. 12.0.10
(`Babai.cosetTopAction4With`), run with the supplied choices on the window and carried
back to `Ω`. -/
noncomputable def line4bBranch (d : JohnsonCaseData I) (s : SmallDefectData d)
    (hm : HugeM d.m (Nat.card I.Δ)) : SIReduction Ω A (Set (Equiv.Perm Ω)) :=
  SIReduction.alignRed I (line4bBranchCoset d s hm)

theorem calls_line4bBranch_K (d : JohnsonCaseData I) (s : SmallDefectData d)
    (hm : HugeM d.m (Nat.card I.Δ)) :
    ∀ J ∈ (cosetTopAction4With d.transitive d.ϕ d.giant
        (veryLargeK_of_hugeM d.transitive hm) s.col s.c (restrictStr I.Δ I.x)
        (restrictStr I.Δ I.y) s.large (s.top hm) (s.alignment hm).element).calls,
      J.K ⊆ (restrictTo d.K I.Δ d.invariant : Set (Equiv.Perm I.Δ)) :=
  fun J hJ => (isCosetInstance_calls_cosetTopAction4With d.transitive d.ϕ d.giant hm
    s.col s.c _ _ s.large (s.top hm) (s.alignment hm).element J hJ).K_subset

/-- The window of the instance, counted in the two ways the statements use. -/
theorem card_window (d : JohnsonCaseData I) :
    Fintype.card I.Δ = I.windowSize := by
  rw [← Nat.card_eq_fintype_card, SIInstance.windowSize, Nat.card_coe_set_eq]

/-- §15, line 4b **is correct**: the branch returns `Iso^Δ_K(x,y)`.  This is the last
clause of Cor. 12.0.10. -/
theorem run_line4bBranch (d : JohnsonCaseData I) (s : SmallDefectData d)
    (hm : HugeM d.m (Nat.card I.Δ)) : (line4bBranch d s hm).run = I.answer := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hrun⟩ :=
    cosetCorollary_12_0_10_with d.transitive d.ϕ d.giant hm (restrictStr I.Δ I.x)
      (restrictStr I.Δ I.y) s.col s.canonical s.c s.large s.giantOn (s.top hm) (s.alignment hm).element (s.alignment hm).spec
  rw [line4bBranch, run_alignRed_of_one_mem (one_mem_K_johnson d), line4bBranchCoset,
    run_liftWindow d.invariant I.x I.y _ (calls_line4bBranch_K d s hm) hrun,
    SIInstance.answer, d.isGroup]

/-- §15, line 4b, **the progress**: every call has a window of at most `2n/3`. -/
theorem decreases_line4bBranch (d : JohnsonCaseData I) (s : SmallDefectData d)
    (hm : HugeM d.m (Nat.card I.Δ)) :
    ∀ J ∈ (line4bBranch d s hm).calls, 3 * J.windowSize ≤ 2 * I.windowSize := by
  intro J hJ
  rw [line4bBranch, calls_alignRed, List.mem_map] at hJ
  obtain ⟨J₀, hJ, rfl⟩ := hJ
  rw [line4bBranchCoset] at hJ
  obtain ⟨J', hJ', hsize⟩ :=
    calls_liftWindow_windowSize d.invariant I.x _ (calls_line4bBranch_K d s hm) J₀ hJ
  have h := decreases_cosetTopAction4With d.transitive d.ϕ d.giant hm
    (restrictStr I.Δ I.x) (restrictStr I.Δ I.y) s.col s.canonical s.c s.large s.giantOn (s.top hm) (s.alignment hm).element (s.alignment hm).spec
    J' hJ'
  rw [windowSize_alignInst, hsize, ← card_window d]
  exact h

/-- §15, line 4b, **the number of calls**: at most `7n`. -/
theorem calls_length_line4bBranch (d : JohnsonCaseData I) (s : SmallDefectData d)
    (hm : HugeM d.m (Nat.card I.Δ)) :
    ((line4bBranch d s hm).calls).length ≤ 7 * I.windowSize := by
  rw [line4bBranch, calls_length_alignRed, line4bBranchCoset,
    calls_length_liftWindow d.invariant I.x _ (calls_line4bBranch_K d s hm),
    ← card_window d]
  exact calls_length_cosetTopAction4With d.transitive d.ϕ d.giant hm
    (restrictStr I.Δ I.x) (restrictStr I.Δ I.y) s.col s.canonical s.c s.large s.giantOn (s.top hm) (s.alignment hm).element (s.alignment hm).spec

/-- §15, line 4b: **every call is a group instance**. -/
theorem calls_line4bBranch_isGroupInstance (d : JohnsonCaseData I) (s : SmallDefectData d)
    (hm : HugeM d.m (Nat.card I.Δ)) :
    ∀ J ∈ (line4bBranch d s hm).calls, IsGroupInstance J := by
  intro J hJ
  rw [line4bBranch, calls_alignRed, List.mem_map] at hJ
  obtain ⟨J₀, hJ, rfl⟩ := hJ
  apply isGroupInstance_alignInst
  exact calls_liftWindow_isCosetInstance d.invariant I.x _ (calls_line4bBranch_K d s hm)
    (isCosetInstance_calls_cosetTopAction4With d.transitive d.ϕ d.giant hm
      s.col s.c _ _ s.large (s.top hm) (s.alignment hm).element) J₀ hJ

end Line4b

/-! ### The round with lines 2 and 4a filled in -/

section Assemble

open scoped Classical

variable {Ω : Type u} {A : Type v} [Fintype Ω] [DecidableEq Ω]

/-- §15, line 4: the test *"`G` primitive (: i.e. `Ω = Φ` :)"*, as the data it produces:
the window is the set of standard blocks, labelled by the `t`-subsets of `Γ`
(Theorem 10.5.1 (e), `Babai.PrimitiveCaseId`). -/
def IsPrimitiveCase (i : HintedInstance Ω A) : Prop :=
  ∃ h : IsJohnson i, Nonempty (PrimitiveCaseId (johnsonData h).ϕ (johnsonData h).t)

/-- The identification of line 4, obtained from its existence proof.

The `label_eq` field fixes the label of each point `u` to `T(u)`, so every inhabitant
of `PrimitiveCaseId` has the same labeling. The `label_unique` and `Subsingleton`
proofs are in `Workspace/Master/PrimitiveCaseIdUnique.lean`. -/
noncomputable def primitiveCaseId {i : HintedInstance Ω A} (hJ : IsJohnson i)
    (hp : IsPrimitiveCase i) : PrimitiveCaseId (johnsonData hJ).ϕ (johnsonData hJ).t :=
  Classical.choice (by obtain ⟨h, hn⟩ := hp; exact hn)

/-- §15, **line 4b, the test**: *"if relative symmetry defect of `H(x)` is `< 1/2`"*.

This is the paper's own test, on the paper's own object: `H(x)` is the string of the window,
read through the labelling of line 4 as an edge coloring of the `t`-uniform hypergraph on
`Γ` (`Babai.hyperColoring`), its automorphism group is `Babai.colorAut`, and *"relative
symmetry defect"* is `Babai.defect` (Definition 2.3.13).

Line 4b is inside line 4, so the test carries the primitive case with it; its negation is
therefore *"`G` is primitive and the defect is `≥ 1/2`"*, which is exactly the hypothesis
line 4c is given (`Babai.largeDefectData_of_not_smallDefect`). -/
def SmallDefect (i : HintedInstance Ω A) : Prop :=
  ∃ hJ : IsJohnson i, ∃ hp : IsPrimitiveCase i,
    defect (colorAut (johnsonData hJ).t
      (hyperColoring (primitiveCaseId hJ hp) (restrictStr i.inst.Δ i.inst.x))) < 1 / 2

/-- §15, line 4b: **the test produces the data Cor. 12.0.10 consumes**.

The dominant twin class of `Aut(H(x))` is marked by the canonical two-coloring
`Babai.bigTwinColoring`, it has more than `m/2` vertices, and it carries every even
permutation of `Γ` supported in it (`Babai.smallDefect_data`). -/
theorem nonempty_smallDefectData {i : HintedInstance Ω A} (hJ : IsJohnson i)
    (hs : SmallDefect i) : Nonempty (SmallDefectData (johnsonData hJ)) := by
  obtain ⟨hJ', hp, hd⟩ := hs
  obtain ⟨hcanon, hlarge, hgiant⟩ :=
    smallDefect_data (primitiveCaseId hJ hp) (johnsonData hJ).giant
      (restrictStr i.inst.Δ i.inst.x) hd
  exact ⟨{ col := bigTwinColoring (primitiveCaseId hJ hp)
           canonical := hcanon
           c := true
           large := hlarge
           giantOn := hgiant }⟩

/-- The data of line 4b, chosen once and for all. -/
noncomputable def smallDefectData {i : HintedInstance Ω A} (hJ : IsJohnson i)
    (hs : SmallDefect i) : SmallDefectData (johnsonData hJ) :=
  Classical.choice (nonempty_smallDefectData hJ hs)

/-- There is only one `t`-subset when `t = 0`. -/
theorem binom_zero_subsingleton {Γ : Type*} (a b : binom Γ 0) : a = b := by
  obtain ⟨s, hs⟩ := a
  obtain ⟨s', hs'⟩ := b
  rw [Finset.card_eq_zero] at hs hs'
  subst hs; subst hs'; rfl

/-- §15, line 4c: **`t ≥ 2`**, which is line 4b's *"else (: `t ≥ 2` :)"*.

Line 4a's test `t = 1` has failed, and `t = 0` is impossible: the window would be the set of
`0`-subsets of `Γ`, a single point, while it has at least `64`
(`Babai.JohnsonCaseData.window_large`). -/
theorem two_le_tParam {i : HintedInstance Ω A} (hJ : IsJohnson i) (hp : IsPrimitiveCase i)
    (ht : ¬ TIsOne i) : 2 ≤ (johnsonData hJ).t := by
  have hne1 : (johnsonData hJ).t ≠ 1 := by
    rw [TIsOne, tParam_eq hJ] at ht; exact ht
  have hne0 : (johnsonData hJ).t ≠ 0 := by
    intro h0
    have hsingle : ∀ a b : binom (Fin (johnsonData hJ).m) (johnsonData hJ).t, a = b := by
      rw [h0]; exact binom_zero_subsingleton
    have hsub : ∀ a b : i.inst.Δ, a = b := fun a b =>
      (primitiveCaseId hJ hp).label.injective (hsingle _ _)
    have hcard : Fintype.card i.inst.Δ ≤ 1 :=
      Fintype.card_le_one_iff.2 hsub
    have := (johnsonData hJ).window_large
    rw [← card_window (johnsonData hJ)] at this
    omega
  omega

/-- §15, **line 4c**: the negation of line 4b's test is the hypothesis of the Extended
Design Lemma.

*"now their relative symmetry defect is `≥ 1/2`"* is what Theorem 9.2.3 asks for as
*"relative symmetry defect `> 1 - α`"*, for every threshold `α > 1/2`; Theorem 9.2.3 is
applied with `3/4 ≤ α < 1`. -/
theorem largeDefectData_of_not_smallDefect {i : HintedInstance Ω A} (hJ : IsJohnson i)
    (hp : IsPrimitiveCase i) (ht : ¬ TIsOne i) (hs : ¬ SmallDefect i) {α : ℝ}
    (hα : 1 / 2 < α) :
    LargeDefectData (primitiveCaseId hJ hp) (restrictStr i.inst.Δ i.inst.x) α where
  t_two := two_le_tParam hJ hp ht
  four_t := by
    have h := (primitiveCaseId hJ hp).four_t
    rw [Fintype.card_fin] at h
    omega
  large_defect := by
    have hge : (1 : ℚ) / 2 ≤ defect (colorAut (johnsonData hJ).t
        (hyperColoring (primitiveCaseId hJ hp) (restrictStr i.inst.Δ i.inst.x))) :=
      le_of_not_gt fun hlt => hs ⟨hJ, hp, hlt⟩
    have hcast : ((1 : ℚ) / 2 : ℝ) ≤ (defect (colorAut (johnsonData hJ).t
        (hyperColoring (primitiveCaseId hJ hp) (restrictStr i.inst.Δ i.inst.x))) : ℝ) := by
      exact_mod_cast hge
    have hhalf : ((1 : ℚ) / 2 : ℝ) = 1 / 2 := by norm_num
    rw [hhalf] at hcast
    linarith

/-- §15, lines 2 and 4b: the numeric hypothesis of Cor. 12.0.10 at an instance that has
passed the test of line 2. -/
theorem hugeM_of_data {i : HintedInstance Ω A} (hJ : IsJohnson i)
    (hℓ : ¬ param i ≤ ellOf i.inst.windowSize) :
    HugeM (johnsonData hJ).m (Nat.card i.inst.Δ) := by
  have hcard : Nat.card i.inst.Δ = i.inst.windowSize := by
    rw [SIInstance.windowSize, Nat.card_coe_set_eq]
  rw [hcard]
  refine hugeM_of_line2 (johnsonData hJ).window_large ?_
  rw [← param_eq hJ]
  omega

/-- Each round can supply its image and kernel-orbit lists for line 2. -/
def Line2Choice (Ω : Type u) (A : Type v) [Fintype Ω] [DecidableEq Ω] :=
  ∀ (i : HintedInstance Ω A) (h : IsJohnson i), Line2Enum (johnsonData h).blockAction

noncomputable def line2ChoiceOf : Line2Choice Ω A := fun _ _ => .default _

/-- Line 4b supplies its coloring and both top-action lists as live choice data. -/
def Line4bChoice (Ω : Type u) (A : Type v) [Fintype Ω] [DecidableEq Ω] :=
  ∀ (i : HintedInstance Ω A) (hJ : IsJohnson i) (hs : SmallDefect i),
    SmallDefectData (johnsonData hJ)

noncomputable def line4bChoiceOf : Line4bChoice Ω A := fun _ hJ hs => smallDefectData hJ hs

/-- §15, line 4b: the branch, as a function of the hinted instance. -/
noncomputable def line4bFunCoset (C : Line4bChoice Ω A) (i : HintedInstance Ω A) : SIReduction Ω A (Set (Equiv.Perm Ω)) :=
  if h : (IsJohnson i ∧ ¬ param i ≤ ellOf i.inst.windowSize) ∧ SmallDefect i then
    line4bBranchCoset (johnsonData h.1.1) (C i h.1.1 h.2)
      (hugeM_of_data h.1.1 h.1.2)
  else cosetLeaf i.inst i.inst.answer

/-- Line 4b aligns once, after lifting the complete coset round. -/
noncomputable def line4bFun (C : Line4bChoice Ω A) (i : HintedInstance Ω A) : SIReduction Ω A (Set (Equiv.Perm Ω)) :=
  SIReduction.alignRed i.inst (line4bFunCoset C i)

/-- §15, line 2: the branch, as a function of the hinted instance.  Outside the Johnson case
there is nothing to do, and the leaf `.done I.answer` is never reached, because line 1 is
taken there. -/
noncomputable def line2Fun (C : Line2Choice Ω A) (i : HintedInstance Ω A) : SIReduction Ω A (Set (Equiv.Perm Ω)) :=
  if h : IsJohnson i then line2Branch (johnsonData h) (C i h) else .done i.inst.answer

/-- §15, **line 2 in coset form**: the imprimitive Luks reduction written in the middle form
of Eqs. (62)–(63), before the alignment step of Remark 11.1.4. -/
noncomputable def line2FunCoset (C : Line2Choice Ω A) (i : HintedInstance Ω A) :
    SIReduction Ω A (Set (Equiv.Perm Ω)) :=
  if h : IsJohnson i then line2Coset (johnsonData h) (C i h)
  else cosetLeaf i.inst i.inst.answer

/-- §15, line 2: **the round is the alignment of its coset form** (Remark 11.1.4). -/
theorem line2Fun_eq_alignRed (C : Line2Choice Ω A) (i : HintedInstance Ω A) :
    line2Fun C i = SIReduction.alignRed i.inst (line2FunCoset C i) := by
  rw [line2Fun, line2FunCoset]
  split
  · rfl
  · rw [alignRed_cosetLeaf]

/-- The number of instances one round of lines 2 and 4a produces, as a function of the
window size: the multiplicative cost `ℓ!` of line 2, once per orbit of `N`, plus the `7n`
calls of Cor. 12.0.10 at line 4b. -/
def masterRoundCost (n : ℕ) : ℕ := Nat.factorial (ellOf n) * n + 7 * n


end Assemble

end Babai
