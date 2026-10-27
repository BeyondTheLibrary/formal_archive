/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 6 / Section 9.5: a reduction may call itself on strictly smaller instances.
-/
import Workspace.Functors.Equivariant

/-!
# §6, §9.5  Building a reduction by induction on a measure of progress

§9.4 proves Theorem 9.2.2 by a procedure that, in several of its steps, hands a **smaller**
instance back to Theorem 9.2.2 itself.  §9.5 ("Measures of progress") is what makes this
terminate:

> *"Throughout the process, `n₁ = |V₁|` will not increase.  We say that a parameter `m` is
> significantly reduced if `m_new ≤ 0.9 m_old`.  We deem to have made major progress if any
> of the following occurs: goal (a) or (b) is achieved; `n₂` is significantly reduced; `X₂`
> moves from clique to UPCC while `n₂` does not increase."*

So the recursive call is made on an input whose measure is strictly smaller, and the
recursion is well founded because the measure is a natural number.

`Babai.FindsAtMultCost.strongInduction` is that recursion at the level of §6.  It takes a
measure `m` on the objects of the input category and proves the reduction for all objects
from the single step

> for every `N`, *if* the reduction is available on the objects of measure `< N`, *then* it
> is available on the objects of measure `= N`,

which is exactly the shape of the proof of §9.4: each branch of Procedure Bipartite
Split-or-Johnson either terminates or calls the procedure on a strictly smaller instance.

Two hypotheses are needed beyond the step.

* `hm`: **the measure is an isomorphism invariant.**  `m` is a function of a `Babai.Pt`,
  which carries the underlying set, so nothing forces `m` to agree on two isomorphic
  objects living on different subsets of `Ω`; without this the subcategories `m < N` are
  not closed under isomorphism and `Babai.FindsAtMultCost.cases` does not apply.  For the
  measure `n₁ + n₂` of §9.5 it holds because an isomorphism is a bijection.
* `hbd`: **the measure is bounded.**  The conclusion is a single statement about *all*
  objects, while the induction only reaches the objects of measure `< N` for a fixed `N`.
  For the measures of §9.5 the bound is `|Ω|`, since `n₁ + n₂ ≤ |Ω|`.

## Numbering map

| Paper | Lean |
|---|---|
| §9.5, a reduction that calls itself on smaller instances | `Babai.FindsAtMultCost.strongInduction` |
| the empty input category (the base case `N = 0`) | `Babai.FindsAtMultCost.of_isEmpty` |
| relabelling the objects of the input category | `Babai.Func.ofObjMap`, `Babai.FindsAtMultCost.reindex` |
-/

namespace Babai

variable {Ω : Type}

/-! ### Relabelling the input category -/

/-- A functor that is the identity on underlying sets and on morphisms: it only renames the
objects, by a map `o` that turns a morphism of `C` into a morphism of `D`.

This is what relates the various ways of writing one and the same full subcategory, for
instance `(C.full P).full Q` and `C.full (fun s X => P s X ∧ Q s X)`, whose objects are
different Lean types but which have the same objects and the same morphisms. -/
def Func.ofObjMap {C D : Cat.{0, 0} Ω} (o : ∀ {s : Set Ω}, C.Obj s → D.Obj s)
    (hiso : ∀ {s t : Set Ω} (X : C.Obj s) (Y : C.Obj t) (f : ↥s ≃ ↥t),
      f ∈ C.Iso X Y → f ∈ D.Iso (o X) (o Y)) :
    Func C D where
  obj X := ⟨X.car, o X.obj⟩
  map f := ⟨f.1, hiso _ _ _ f.2⟩
  map_id _ := rfl
  map_trans _ _ := rfl

theorem Func.ofObjMap_isCanonicalEmbedding {C D : Cat.{0, 0} Ω}
    (o : ∀ {s : Set Ω}, C.Obj s → D.Obj s)
    (hiso : ∀ {s t : Set Ω} (X : C.Obj s) (Y : C.Obj t) (f : ↥s ≃ ↥t),
      f ∈ C.Iso X Y → f ∈ D.Iso (o X) (o Y)) :
    (Func.ofObjMap o hiso).IsCanonicalEmbedding where
  car_subset _ := subset_rfl
  map_restrict _ _ := rfl

/-- §6.  **Relabelling the input category.**  A reduction stated for `D` is a reduction for
`C`, as soon as every object of `C` names an object of `D` on the same underlying set in a
way that preserves the morphisms.  This is `Babai.FindsAtMultCost.precomp` for the functor
`Babai.Func.ofObjMap`. -/
theorem FindsAtMultCost.reindex {C D K : Cat.{0, 0} Ω} {cost : Pt D → ℕ}
    {Good : Pt D → Pt K → Prop} (o : ∀ {s : Set Ω}, C.Obj s → D.Obj s)
    (hiso : ∀ {s t : Set Ω} (X : C.Obj s) (Y : C.Obj t) (f : ↥s ≃ ↥t),
      f ∈ C.Iso X Y → f ∈ D.Iso (o X) (o Y))
    (h : FindsAtMultCost D K cost Good) :
    FindsAtMultCost C K (fun X => cost ⟨X.car, o X.obj⟩)
      (fun X Z => Good ⟨X.car, o X.obj⟩ Z) :=
  FindsAtMultCost.precomp (Func.ofObjMap o hiso)
    (Func.ofObjMap_isCanonicalEmbedding o hiso) h

/-! ### The empty input category -/

/-- The class of tuples with no members: it is a `Babai.TupleClass` because both of its
conditions quantify over members. -/
def TupleClass.empty (C : Cat.{0, 0} Ω) : TupleClass C where
  mem _ := ∅
  nonempty h := absurd h (Set.notMem_empty _)
  cond_ii h _ _ _ _ _ := absurd h (Set.notMem_empty _)

/-- §6.  A reduction of a category **with no objects** exists, at any cost and for any
property: there is nothing to find.  This is the base case `N = 0` of
`Babai.FindsAtMultCost.strongInduction`, where the subcategory of the objects of measure
`< 0` is empty. -/
theorem FindsAtMultCost.of_isEmpty {C K : Cat.{0, 0} Ω} {cost : Pt C → ℕ}
    {Good : Pt C → Pt K → Prop} (h : ∀ s : Set Ω, IsEmpty (C.Obj s)) :
    FindsAtMultCost C K cost Good := by
  -- The class of tuples is empty, so every condition on it is vacuous, and the two
  -- functors are defined by the elimination of an empty type.
  refine ⟨C, TupleClass.empty C,
    { obj := fun X => (h X.car).elim X.obj
      map := fun {X _} _ => (h X.car).elim X.obj
      map_id := fun X => (h X.car).elim X.obj
      map_trans := fun {X _ _} _ _ => (h X.car).elim X.obj },
    { obj := fun p => (h p.car).elim p.obj.1
      map := fun {p _} _ => (h p.car).elim p.obj.1
      map_id := fun p => (h p.car).elim p.obj.1
      map_trans := fun {p _ _} _ _ => (h p.car).elim p.obj.1 },
    ⟨fun p => (h p.car).elim p.obj.1, fun {p _} _ _ => (h p.car).elim p.obj.1⟩,
    fun X => (h X.car).elim X.obj, fun X => (h X.car).elim X.obj⟩

/-! ### The recursion of §9.5 -/

/-- §6, §9.5.  **A reduction may call itself on strictly smaller instances.**

Let `m` be a measure on the objects of `C` that is invariant under isomorphism (`hm`) and
bounded by `N₀` (`hbd`).  Suppose that for every `N`, a reduction on the full subcategory of
the objects of measure `< N` yields a reduction on the full subcategory of the objects of
measure exactly `N`, at the same cost and for the same property found (`step`).  Then the
reduction exists on all of `C`.

This is the form of `Babai.FindsAtMultCost.cases` that §9.4 needs: Procedure Bipartite
Split-or-Johnson reduces Theorem 9.2.2 to itself on instances on which the measure of
progress of §9.5 has dropped, so the reduction being proved must be available inside its
own proof, on the smaller instances only.

The proof is the induction on `N` of the statement "the reduction exists on the objects of
measure `< N`".  The step splits the objects of measure `< N+1` into those of measure `= N`
and those of measure `< N` — a canonical case distinction, since `m` is an isomorphism
invariant — and applies `step N` to the first part and the induction hypothesis to the
second (`Babai.FindsAtMultCost.cases`).  The base case is the empty category. -/
theorem FindsAtMultCost.strongInduction {C K : Cat.{0, 0} Ω} (m : Pt C → ℕ)
    {cost : Pt C → ℕ} {Good : Pt C → Pt K → Prop}
    (hm : ∀ {X Y : Pt C}, (C.IsoP X Y).Nonempty → m X = m Y)
    (N₀ : ℕ) (hbd : ∀ X : Pt C, m X < N₀)
    (step : ∀ N : ℕ,
      FindsAtMultCost (C.full fun s Y => m ⟨s, Y⟩ < N) K
          (fun X => cost ⟨X.car, X.obj.1⟩) (fun X Z => Good ⟨X.car, X.obj.1⟩ Z) →
      FindsAtMultCost (C.full fun s Y => m ⟨s, Y⟩ = N) K
          (fun X => cost ⟨X.car, X.obj.1⟩) (fun X Z => Good ⟨X.car, X.obj.1⟩ Z)) :
    FindsAtMultCost C K cost Good := by
  -- the reduction on the objects of measure `< N`, by induction on `N`
  have key : ∀ N : ℕ, FindsAtMultCost (C.full fun s Y => m ⟨s, Y⟩ < N) K
      (fun X => cost ⟨X.car, X.obj.1⟩) (fun X Z => Good ⟨X.car, X.obj.1⟩ Z) := by
    intro N
    induction N with
    | zero =>
      exact FindsAtMultCost.of_isEmpty fun _ => ⟨fun Y => absurd Y.2 (Nat.not_lt_zero _)⟩
    | succ N ih =>
      -- the case distinction "is the measure exactly `N`?" inside the objects of
      -- measure `< N+1`; it is canonical because `m` is an isomorphism invariant
      have hP : ∀ {X Y : Pt (C.full fun s Y => m ⟨s, Y⟩ < N + 1)},
          ((C.full fun s Y => m ⟨s, Y⟩ < N + 1).IsoP X Y).Nonempty →
            m ⟨X.car, X.obj.1⟩ = N → m ⟨Y.car, Y.obj.1⟩ = N := by
        rintro X Y ⟨f, hf⟩ hx
        exact (hm (X := ⟨X.car, X.obj.1⟩) (Y := ⟨Y.car, Y.obj.1⟩) ⟨f, hf⟩).symm.trans hx
      -- the objects of measure `= N`: `step N` applied to the induction hypothesis
      have hpos := FindsAtMultCost.reindex
        (C := (C.full fun s Y => m ⟨s, Y⟩ < N + 1).full fun s Y => m ⟨s, Y.1⟩ = N)
        (D := C.full fun s Y => m ⟨s, Y⟩ = N)
        (fun {_} Y => ⟨Y.1.1, Y.2⟩) (fun _ _ _ hf => hf) (step N ih)
      -- the objects of measure `< N`: the induction hypothesis itself
      have hneg := FindsAtMultCost.reindex
        (C := (C.full fun s Y => m ⟨s, Y⟩ < N + 1).full fun s Y => ¬ m ⟨s, Y.1⟩ = N)
        (D := C.full fun s Y => m ⟨s, Y⟩ < N)
        (fun {_} Y => ⟨Y.1.1, lt_of_le_of_ne (Nat.lt_succ_iff.1 Y.1.2) Y.2⟩)
        (fun _ _ _ hf => hf) ih
      exact (FindsAtMultCost.cases hP hpos hneg).mono
        (fun _ => le_of_eq (max_self _)) fun _ _ h => h
  -- every object has measure `< N₀`
  exact FindsAtMultCost.reindex (C := C) (D := C.full fun s Y => m ⟨s, Y⟩ < N₀)
    (fun {s} X => ⟨X, hbd ⟨s, X⟩⟩) (fun _ _ _ hf => hf) (key N₀)

end Babai
