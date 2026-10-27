/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Sections 9.5 and 9.7: an equipartition of the blocks is a hint.
-/
import Workspace.SplitOrJohnson.HintBuild

/-!
# §9.7, Cases 3a1 and 3b: an equipartitioned family of blocks carries the hint

Version 2.5, lines 4281-4301; the original, `babai-gi.tex`, lines 3981-3992.

*"If color class selected is greater than `3n₂/4`, this color class is equipartitioned;
apply Procedure ImprimitiveCase."*  The structure the paper leaves on the selected class is
an equivalence relation on the blocks whose classes all have one common size `m ≥ 2`, with
at least two classes.  `Babai.eqvConfig` is the coherent configuration of such a relation
(`Workspace/SplitOrJohnson/HintBuild.lean`); this file reads it on the blocks of an object
of `Babai.VColBipBlk` whose hint coloring is the three-color coloring of the relation, and
concludes `Babai.VColBipBlk.HasHint`.

Cases 3a1 and 3b both end this way, so the statement is made once, for an arbitrary
relation on the blocks.
-/

namespace Babai

namespace VColBipBlk

variable {s : Type} [Fintype s] [DecidableEq s]

open scoped Classical in
/-- §9.5, §9.7, Cases 3a1 and 3b.  **An equipartitioned family of blocks is a hint.**  Let
`r` be an equivalence relation on the blocks of `X`, all of whose classes have the same
size `m`, with `2 ≤ m` and at least two classes (`m < n₂`), and let the hint coloring `h`
of `X` be the three-color coloring *"equal"*, *"different, same class"*, *"different
classes"* of `r`.  Then `X` carries the hint.

This is `Babai.eqvConfig` read on `Babai.VColBipBlk.blocks`. -/
theorem hasHint_of_eqvPart {X : VColBipBlk s ℕ} {r : Set s → Set s → Prop} {m : ℕ}
    (hrefl : ∀ A ∈ X.blocks, r A A)
    (hsymm : ∀ A ∈ X.blocks, ∀ B ∈ X.blocks, r A B → r B A)
    (htrans : ∀ A ∈ X.blocks, ∀ B ∈ X.blocks, ∀ C ∈ X.blocks, r A B → r B C → r A C)
    (hm : ∀ A ∈ X.blocks, {B | B ∈ X.blocks ∧ r A B}.ncard = m)
    (h2m : 2 ≤ m) (hlt : m < X.numBlocks)
    (hh : ∀ A ∈ X.blocks, ∀ B ∈ X.blocks,
      X.h A B = if A = B then 0 else if r A B then 1 else 2) :
    X.HasHint := by
  classical
  letI : Fintype ↥X.blocks := Fintype.ofFinite _
  set R : ↥X.blocks → ↥X.blocks → Prop := fun a b => r (a : Set s) (b : Set s) with hRdef
  have hRe : Equivalence R :=
    ⟨fun a => hrefl a a.2, fun {a b} hab => hsymm a a.2 b b.2 hab,
      fun {a b c} hab hbc => htrans a a.2 b b.2 c c.2 hab hbc⟩
  have hcard : Fintype.card ↥X.blocks = X.numBlocks := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]; rfl
  have hmR : ∀ a : ↥X.blocks, ({b | R a b} : Set ↥X.blocks).ncard = m := by
    intro a
    have himg : Subtype.val '' ({b | R a b} : Set ↥X.blocks)
        = {B | B ∈ X.blocks ∧ r (a : Set s) B} := by
      ext B
      constructor
      · rintro ⟨b, hb, rfl⟩; exact ⟨b.2, hb⟩
      · rintro ⟨hB, hr⟩; exact ⟨⟨B, hB⟩, hr, rfl⟩
    rw [← Set.ncard_image_of_injective _ Subtype.val_injective, himg]
    exact hm (a : Set s) a.2
  have hltR : m < Fintype.card ↥X.blocks := by rw [hcard]; exact hlt
  refine hasHint_of_structure (eqvConfig hRe hmR h2m hltR) (eqvConfig_isCoherent _ _ _ _)
    (eqvConfig_isHomogeneous _ _ _ _) (by rw [eqvConfig_rank]) (fun A B => ?_)
  rw [hh (A : Set s) A.2 (B : Set s) B.2]
  show _ = ((eqvColor R A B : Fin 3) : ℕ)
  unfold eqvColor
  by_cases hAB : (A : Set s) = (B : Set s)
  · have : A = B := Subtype.ext hAB
    rw [if_pos hAB, if_pos this]; rfl
  · have hne : A ≠ B := fun hc => hAB (congrArg Subtype.val hc)
    rw [if_neg hAB, if_neg hne]
    by_cases hr : r (A : Set s) (B : Set s)
    · rw [if_pos hr, if_pos (show R A B from hr)]; rfl
    · rw [if_neg hr, if_neg (show ¬ R A B from hr)]; rfl

end VColBipBlk

end Babai
