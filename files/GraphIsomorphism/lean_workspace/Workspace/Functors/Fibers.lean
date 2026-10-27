/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 6: splitting a category into the fibers of an isomorphism-invariant number.
-/
import Workspace.Functors.Induction

/-!
# §6  Splitting a reduction into the fibers of a numerical invariant

Several statements of §8 are stated for a **fixed** arity: the Design Lemma
(Theorem 8.1.2) is a reduction of the category `Babai.KAryInputs Ω k α` of `k`-ary
relational structures, with `k` a parameter of the category.  Several uses of it in §9 feed
it a structure whose arity depends on the input: in Case 3a of §9.7 the neighborhood
hypergraph `H` is `d'`-ary with `d' = min(d₁, n₂ − d₁)`, a number read off the input, and
in Case 3b the `t`-skeleton is `t`-ary with `t = ⌈(7/4) log₂ n₁⌉`, again read off the
input.

`Babai.FindsAtMultCost.ofFibers` is what lets one apply such a statement anyway: **it is
enough to give the reduction on each fiber `{X | f X = N}` separately.**  On that fiber the
arity is the constant `N`, so the fixed-arity statement applies, and the fibers glue
because `f` is an isomorphism invariant, so *"is `f X = N`?"* is a canonical question.

The proof is `Babai.FindsAtMultCost.strongInduction` for the measure `f`, with a step that
ignores the induction hypothesis: the fibers do not call each other.

## Numbering map

| Paper | Lean |
|---|---|
| running a fixed-arity reduction at an arity read off the input (§9.7 Case 3a, 3b) | `Babai.FindsAtMultCost.ofFibers` |
-/

namespace Babai

variable {Ω : Type}

/-- §6.  **A reduction may be given fiber by fiber.**  Let `f` be a number attached to the
objects of `C` that is an isomorphism invariant (`hf`) and bounded by `B` (`hbd`).  If, for
every `N`, the reduction exists on the full subcategory of the objects with `f X = N`, at
the same cost and for the same property found, then it exists on all of `C`.

The case distinction is canonical because `f` is an isomorphism invariant, which is what
`Babai.FindsAtMultCost.cases` asks for; the bound is what makes the number of cases finite.
This is `Babai.FindsAtMultCost.strongInduction` for the measure `f`, with a step that makes
no use of the induction hypothesis. -/
theorem FindsAtMultCost.ofFibers {C K : Cat.{0, 0} Ω} (f : Pt C → ℕ)
    {cost : Pt C → ℕ} {Good : Pt C → Pt K → Prop}
    (hf : ∀ {X Y : Pt C}, (C.IsoP X Y).Nonempty → f X = f Y)
    (B : ℕ) (hbd : ∀ X : Pt C, f X ≤ B)
    (hfib : ∀ N : ℕ, FindsAtMultCost (C.full fun s Y => f ⟨s, Y⟩ = N) K
      (fun X => cost ⟨X.car, X.obj.1⟩) (fun X Z => Good ⟨X.car, X.obj.1⟩ Z)) :
    FindsAtMultCost C K cost Good :=
  FindsAtMultCost.strongInduction f hf (B + 1) (fun X => Nat.lt_succ_of_le (hbd X))
    fun N _ => hfib N

/-! ### Non-vacuity

The gluing is tested on `Babai.Sets Ω` with `f X = |□X|`, an isomorphism invariant with
many non-empty fibers: on each fiber the identity is a canonical embedding, so each fiber
has a reduction at cost `1` (`Babai.FindsAtMultCost.of_canonicalEmbedding`), and
`Babai.FindsAtMultCost.ofFibers` glues them into a reduction of `Babai.Sets Ω` at cost `1`.
So the hypotheses of `Babai.FindsAtMultCost.ofFibers` are satisfiable and the statement is
not vacuous. -/

/-- **Non-vacuity of `Babai.FindsAtMultCost.ofFibers`.**  Gluing the fibers of `|□X|` over
`Babai.Sets Ω` gives the reduction at cost `1` whose outcome is the object on `□X`
itself. -/
example (Ω : Type) [Finite Ω] :
    FindsAtMultCost (Sets Ω) (Sets Ω) (fun _ => 1) (fun X Z => Z.car = X.car) := by
  refine FindsAtMultCost.ofFibers (fun X => X.car.ncard) ?_ (Nat.card Ω) ?_ ?_
  · rintro X Y ⟨e, -⟩
    show X.car.ncard = Y.car.ncard
    rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, Nat.card_congr e]
  · intro X
    show X.car.ncard ≤ Nat.card Ω
    rw [← Set.ncard_univ Ω]
    exact Set.ncard_le_ncard (Set.subset_univ _) Set.finite_univ
  · intro N
    exact FindsAtMultCost.of_canonicalEmbedding
      (Func.ofObjMap (fun {s} _ => (PUnit.unit : (Sets Ω).Obj s)) fun _ _ _ _ => trivial)
      (Func.ofObjMap_isCanonicalEmbedding _ _) fun _ => rfl

end Babai
