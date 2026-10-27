/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 6: "at a multiplicative cost of `s` we can find a canonical …", the common shape of
the conclusions of Sections 8 and 9.
-/
import Workspace.Functors.Tuples

/-!
# §6 Finding a canonical object at a multiplicative cost

Many statements of §8 and §9 have the form

> *"at a multiplicative cost of `s` we can find a canonical `…`"*

or, with the canonicity spelled out,

> *"at a multiplicative cost of `s` we can find a (relative) canonically embedded `…`"*.

Definitions 6.0.3, 6.0.5 and 6.0.7 say what this means, and `Babai.FindsAtMultCost` is
their conjunction:

* Definition 6.0.3: a reduction of the isomorphism problem in `C` to a category `D` *"at
  multiplicative cost `s`"* is a functor `F : C → E` into a category `E` of tuples of `D`
  with `|F(X)| = s`.  As in `Babai.IsReductionAtCost`, `|F(X)| = s` with `s` a number says
  that the tuple `F(X)` is **finite** and has `s` members; `Set.ncard` of an infinite set is
  `0`, so the finiteness has to be stated separately — without it an infinite tuple would
  count as having cost `0`, and every statement of the above form would become vacuous.
* Definition 6.0.5: the category `C^F` of pairs `(X, X')` with `X' ∈ F(X)`.
* Definition 6.0.7: an object *canonically assigned to `X` relative to `X'`* is the value at
  `(X, X')` of a functor on `C^F`.

The paper's bound is a bound valid for every input, so `|F(X)| ≤ cost X` is required for
every object `X` of `C` (for most statements `cost X` is a function of the number `n` of
vertices of `X`; for Lemma 9.6.1 it is `n₂ = |V₂|`).

The functor `G` into the category of outputs is required to be a **canonical embedding**
(§6): the object found lives on a subset of the vertex set of `X` and the morphisms of `C`
act on it by restriction.  This is what *"canonical colored partition **of `V`**"* and
*"**canonically embedded** Johnson scheme **on a subset of `V`**"* mean, and it is what
makes the notion non-trivial: an output category cannot be canonical "for free", because
`G` must commute with all of `Iso(X,Y)` while `□G(X,X') ⊆ □X`.

Finally, the required property `Good` is asserted for **every** member `X'` of the tuple,
not for one of them: the algorithm may return any member of the tuple it individualizes,
and all of them must be solutions.

## Numbering map

| Paper | Lean |
|---|---|
| "at a multiplicative cost of `s` we can find a canonical …" (Defs. 6.0.3, 6.0.5, 6.0.7) | `Babai.FindsAtMultCost` |
-/

namespace Babai

/-- Definitions 6.0.3, 6.0.5 and 6.0.7.  *"At a multiplicative cost of `s` we can find a
canonical object with property `Good`"*: there is a reduction `F : C → E` of the
isomorphism problem in `C` to a category `E` of tuples of some category `D`, with `F(X)`
finite of size `≤ cost X` for every object `X` (Def. 6.0.3), and a functor `G` on the
category `C^F` of pairs `(X, X')`, `X' ∈ F(X)` (Def. 6.0.5), so that `G(X,X')` is
canonically assigned to `X` relative to `X'` (Def. 6.0.7), is canonically embedded in `X`,
and has the required property for every `X' ∈ F(X)`.

The finiteness of the tuple is part of `|F(X)| ≤ s`; see the module docstring. -/
def FindsAtMultCost {Ω : Type} (C : Cat.{0, 0} Ω) (H : Cat.{0, 0} Ω) (cost : Pt C → ℕ)
    (Good : Pt C → Pt H → Prop) : Prop :=
  ∃ (D : Cat.{0, 0} Ω) (E : TupleClass D) (F : Func C E.cat) (G : Func (pairCat F) H),
    G.IsCanonicalEmbedding ∧
    (∀ X : Pt C, (tupleOf F X).Finite ∧ (tupleOf F X).ncard ≤ cost X) ∧
    ∀ (X : Pt C) (X' : D.Obj (F.obj X).car) (hX' : X' ∈ tupleOf F X),
      Good X (G.obj ⟨X.car, ⟨X.obj, ⟨X', hX'⟩⟩⟩)

/-- A tuple is non-empty (Def. 6.0.1), so a multiplicative cost is at least `1`: nothing can
be found at cost `0`.  This is the sanity check that the cost bound of `FindsAtMultCost` is
not vacuous; before the finiteness clause was added, an infinite tuple satisfied
`(tupleOf F X).ncard ≤ 0`. -/
theorem FindsAtMultCost.one_le_cost {Ω : Type} {C H : Cat.{0, 0} Ω} {cost : Pt C → ℕ}
    {Good : Pt C → Pt H → Prop} (h : FindsAtMultCost C H cost Good) (X : Pt C) :
    1 ≤ cost X := by
  obtain ⟨D, E, F, G, -, hcost, -⟩ := h
  obtain ⟨hfin, hle⟩ := hcost X
  have hne : (tupleOf F X).Nonempty := E.nonempty ((F.obj X).obj).2
  have : 0 < (tupleOf F X).ncard := (Set.ncard_pos hfin).2 hne
  omega

end Babai
