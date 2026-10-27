/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Sections 9.5 and 9.7, Case 3a2: the turn that starts from a hinted instance and reaches the
clique branch of step 9 halves `n₂`.
-/
import Workspace.SplitOrJohnson.Step9Func

/-!
# §9.7, Case 3a2: the hinted pass does reduce `n₂`

Version 2.5, lines 4285–4294 (§9.7, Case 3a2) and 4176–4181 (§9.5).

§9.5 counts *"`X₂` moves from clique to UPCC while `n₂` does not increase"* as major
progress.  The turn that starts from the instance this progress left must itself reduce
`n₂`, or the recursion would not terminate.  The paper's argument is the last sentence of
Case 3a2:

> *"If `(X₂)_new` is not a UPCC, i.e., it has rank 2, then `U` was a clique in `Y` and
> therefore `|U| ≤ |W|/2 ≤ n₂/2` by Prop. 2.4.11."*

Here `Y` is the hint the instance carries (`Babai.VColBipBlk.HasHint`), a homogeneous
coherent configuration of rank at least `3` on the blocks, and `U` is the family of blocks
that the pass is left with, that is the blocks of the instance step 8 leaves.  *"`(X₂)_new`
has rank 2"* is the branch condition of step 9(ii), `Babai.Step9Clique`.

The formal chain is short.  The coloring of step 8 refines the initial coloring of step 8
(`Babai.initColor_eq_of_step8Raw_eq`), which records the hint
(`Babai.VColBipBlk.h_eq_of_initColor_eq`), and the restrictions of steps 5 and 7 keep the
hint (`Babai.VColBipBlk.restrictTo_h`).  So all ordered pairs of distinct blocks of `U`
carry one value of `h`, and `Babai.VColBipBlk.two_mul_ncard_le_of_hint` — Prop. 2.4.11 —
gives `2|U| ≤ n₂`.

| Paper | Lean |
|---|---|
| §9.5, the input of the pass carries the hint | `Babai.HasHintAt` |
| §9.7, Case 3a2, the clique branch of a hinted pass | `Babai.two_mul_step8NumBlocks_le_of_hint` |
-/

namespace Babai

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

/-! ### The input of a pass carries the hint -/

/-- §9.5.  **The instance carries the hint**, read at an object of the category of the
inputs.  This is the condition that `Babai.hintBit` tests. -/
noncomputable def HasHintAt (X : Pt (BipBlockInputs Ω)) : Prop :=
  letI : Fintype ↥X.car := Fintype.ofFinite _
  letI : DecidableEq ↥X.car := Classical.decEq _
  X.obj.1.1.HasHint

theorem hintBit_eq_zero_iff (X : Pt (BipBlockInputs Ω)) :
    hintBit X = 0 ↔ HasHintAt X := by
  classical
  letI : Fintype ↥X.car := Fintype.ofFinite _
  letI : DecidableEq ↥X.car := Classical.decEq _
  rw [hintBit]
  by_cases hX : X.obj.1.1.HasHint
  · rw [if_pos hX]
    exact ⟨fun _ => hX, fun _ => rfl⟩
  · rw [if_neg hX]
    exact ⟨fun h => absurd h one_ne_zero, fun h => absurd h hX⟩

theorem hintBit_eq_one_of_not (X : Pt (BipBlockInputs Ω)) (h : ¬ HasHintAt X) :
    hintBit X = 1 := by
  have h1 := hintBit_le_one X
  have h2 : hintBit X ≠ 0 := fun hc => h ((hintBit_eq_zero_iff X).1 hc)
  omega

/-- §9.5.  The hint is an isomorphism invariant (`Babai.VColBipBlk.hasHint_congr`). -/
theorem hasHintAt_congr {X Y : Pt (BipBlockInputs Ω)}
    (h : ((BipBlockInputs Ω).IsoP X Y).Nonempty) (hX : HasHintAt X) : HasHintAt Y := by
  classical
  letI : Fintype ↥X.car := Fintype.ofFinite _
  letI : DecidableEq ↥X.car := Classical.decEq _
  letI : Fintype ↥Y.car := Fintype.ofFinite _
  letI : DecidableEq ↥Y.car := Classical.decEq _
  obtain ⟨φ, hφ⟩ := h
  exact VColBipBlk.hasHint_congr (hφ.2 : X.obj.1.1.IsIsoTo Y.obj.1.1 φ) hX

/-! ### The hint survives steps 5, 7 and 8 -/

variable (X : Pt (BipBlockInputs Ω))

/-- §9.4, steps 7 and 8.  **The hint of the instance step 8 leaves is the hint of the
input**, read at the images of the two sets: step 8 does not touch the coloring `h`, and
the restriction of step 7 keeps it (`Babai.VColBipBlk.restrictTo_h`). -/
theorem step8Obj_h (A B : Set ↥(step7Set X)) :
    (step8Obj X).h A B
      = X.obj.1.1.h (VColBipBlk.incl (step7Set_subset X) '' A)
          (VColBipBlk.incl (step7Set_subset X) '' B) := rfl

/-- §9.4, step 9(ii).  **In the clique branch the hint is constant on the ordered pairs of
distinct blocks of the instance step 8 leaves.**

The coloring of step 8 is constant there by the branch condition
(`Babai.Step9Clique`); it is the `natColor` of `Babai.step8Config`
(`Babai.step8CaseColor_vtx`), which refines the initial coloring of step 8
(`Babai.step8Config_color_eq_iff`, `Babai.initColor_eq_of_step8Raw_eq`), and the initial
coloring records the hint (`Babai.VColBipBlk.h_eq_of_initColor_eq`). -/
theorem step8_h_const_of_clique (hcl : Step9Clique X)
    {A B A' B' : Set ↥(step7Set X)}
    (hA : A ∈ (step8Obj X).blocks) (hB : B ∈ (step8Obj X).blocks)
    (hA' : A' ∈ (step8Obj X).blocks) (hB' : B' ∈ (step8Obj X).blocks)
    (hAB : A ≠ B) (hA'B' : A' ≠ B') :
    (step8Obj X).h A B = (step8Obj X).h A' B' := by
  classical
  letI : Fintype ↥(step7Set X) := Fintype.ofFinite _
  letI : DecidableEq ↥(step7Set X) := Classical.decEq _
  set u : ↥((step8Obj X).vtx) := ⟨A, Or.inr hA⟩ with hu
  set v : ↥((step8Obj X).vtx) := ⟨B, Or.inr hB⟩ with hv
  set u' : ↥((step8Obj X).vtx) := ⟨A', Or.inr hA'⟩ with hu'
  set v' : ↥((step8Obj X).vtx) := ⟨B', Or.inr hB'⟩ with hv'
  have hne : (⟨u, hA⟩ : ↥(step8Blks X)) ≠ ⟨v, hB⟩ := by
    intro hc
    exact hAB (congrArg (fun w : ↥(step8Blks X) => ((w : ↥((step8Obj X).vtx)) :
      Set ↥(step7Set X))) hc)
  have hne' : (⟨u', hA'⟩ : ↥(step8Blks X)) ≠ ⟨v', hB'⟩ := by
    intro hc
    exact hA'B' (congrArg (fun w : ↥(step8Blks X) => ((w : ↥((step8Obj X).vtx)) :
      Set ↥(step7Set X))) hc)
  have hc := hcl ⟨u, hA⟩ ⟨v, hB⟩ ⟨u', hA'⟩ ⟨v', hB'⟩ hne hne'
  have hc' : step8CaseColor X A B = step8CaseColor X A' B' := hc
  rw [step8CaseColor_vtx X u v, step8CaseColor_vtx X u' v'] at hc'
  have hraw : step8Raw X u v = step8Raw X u' v' :=
    (step8Config_color_eq_iff X u v u' v').1 hc'
  have hinit := initColor_eq_of_step8Raw_eq X hraw
  exact (VColBipBlk.h_eq_of_initColor_eq hAB hA'B' hinit).1

/-! ### The clique branch of a hinted pass halves `n₂` -/

/-- §9.7, Case 3a2.  **A pass that starts from a hinted instance and reaches the clique
branch of step 9 halves `n₂`.**  *"`U` was a clique in `Y` and therefore
`|U| ≤ |W|/2 ≤ n₂/2` by Prop. 2.4.11."*  (Version 2.5, lines 4285–4294.)

The blocks that step 8 leaves are, inside the blocks of the input, a set on which the hint
is constant off the diagonal (`Babai.step8_h_const_of_clique`), and there are at least two
of them (`Babai.two_le_step8NumBlocks`), so
`Babai.VColBipBlk.two_mul_ncard_le_of_hint` applies. -/
theorem two_mul_step8NumBlocks_le_of_hint (hsmall : ¬ AllClassesSmall X)
    (hcl : Step9Clique X) (hhint : HasHintAt X) :
    2 * step8NumBlocks X ≤ BipBlockInputs.numBlocks X := by
  classical
  letI : Fintype ↥X.car := Fintype.ofFinite _
  letI : DecidableEq ↥X.car := Classical.decEq _
  set ι := VColBipBlk.incl (step7Set_subset X) with hι
  -- the blocks that step 8 leaves, read inside the blocks of the input
  set D : Set ↥(X.obj.1.1.blocks) := {C | (C : Set ↥X.car) ∈ step7Blocks X} with hD
  have hDimg : Subtype.val '' D = step7Blocks X := by
    ext C
    constructor
    · rintro ⟨c, hc, rfl⟩; exact hc
    · intro hC; exact ⟨⟨C, hC.1⟩, hC, rfl⟩
  have hDcard : D.ncard = step8NumBlocks X := by
    have h1 : D.ncard = (Subtype.val '' D).ncard :=
      (Set.ncard_image_of_injective _ Subtype.val_injective).symm
    rw [h1, hDimg, ← step7Obj_numBlocks X]
    rfl
  -- every member of `D` comes from a block of the instance step 8 leaves
  have hpre : ∀ C ∈ D, ∃ c ∈ (step8Obj X).blocks, ι '' c = (C : Set ↥X.car) := by
    intro C hC
    have : (C : Set ↥X.car) ∈
        (fun B : Set ↥(step7Set X) => ι '' B) '' (step7Obj X).blocks := by
      rw [step7Obj_blocks_image X]; exact hC
    obtain ⟨c, hc, hcimg⟩ := this
    exact ⟨c, hc, hcimg⟩
  have hkeyclique : ∀ A ∈ D, ∀ B ∈ D, ∀ A' ∈ D, ∀ B' ∈ D, A ≠ B → A' ≠ B' →
      X.obj.1.1.h (A : Set ↥X.car) (B : Set ↥X.car)
        = X.obj.1.1.h (A' : Set ↥X.car) (B' : Set ↥X.car) := by
    intro A hA B hB A' hA' B' hB' hne hne'
    obtain ⟨a, ha, haimg⟩ := hpre A hA
    obtain ⟨b, hb, hbimg⟩ := hpre B hB
    obtain ⟨a', ha', ha'img⟩ := hpre A' hA'
    obtain ⟨b', hb', hb'img⟩ := hpre B' hB'
    have hab : a ≠ b := by
      intro hc
      exact hne (Subtype.ext (by rw [← haimg, ← hbimg, hc]))
    have ha'b' : a' ≠ b' := by
      intro hc
      exact hne' (Subtype.ext (by rw [← ha'img, ← hb'img, hc]))
    have hkey := step8_h_const_of_clique X hcl ha hb ha' hb' hab ha'b'
    rw [step8Obj_h X a b, step8Obj_h X a' b', haimg, hbimg, ha'img, hb'img] at hkey
    exact hkey
  have key : 2 * D.ncard ≤ X.obj.1.1.numBlocks :=
    VColBipBlk.two_mul_ncard_le_of_hint hhint
      (by rw [hDcard]; exact two_le_step8NumBlocks hsmall) hkeyclique
  rw [← hDcard]
  exact key

end Babai
