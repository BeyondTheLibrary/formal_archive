/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 6: the projection of the category of pairs (input, object found) onto the object
found.
-/
import Workspace.Functors.Equivariant

/-!
# §6 The second component of a pair, as a functor

`Babai.PairCatOf C H Good` (`Workspace/Functors/Equivariant.lean`) is the category of
pairs *(input, object found)* on which the second step of a chain of canonical reductions
lives.  `Babai.pairFst` and `Babai.pairSnd` are the two components, as maps on objects.
The first one is a functor with no work (a morphism of pairs *is* a morphism of the first
components).  The second one is a functor too, but the morphism of `H` it uses is hidden
inside an existential quantifier in the definition of `PairCatOf`, exactly as in
`Babai.Cat.sub`; it is unique (`pairSndMap_eq`), so choosing it defines a function of the
morphism.

The projection is a **canonical embedding** (§6): the object found lives on a subset of
the input's vertex set, and a morphism acts on it by restriction.  This is what lets a
later step of §9 be applied to the object that an earlier step produced, through
`Babai.FindsAtMultCost.precomp`.

## Numbering map

| Paper | Lean |
|---|---|
| the object found, as a functor on the pairs | `Babai.pairSndFunc`, `.pairSndFunc_isCanonicalEmbedding` |
| the input, as a functor on the pairs | `Babai.pairFstFunc` |
-/

namespace Babai

variable {Ω : Type} {C H : Cat.{0, 0} Ω} {Good : Pt C → Pt H → Prop}

/-- The input of a pair, as a functor.  A morphism of pairs is in particular a morphism of
the first components, so there is nothing to choose here. -/
def pairFstFunc (C H : Cat.{0, 0} Ω) (Good : Pt C → Pt H → Prop) :
    Func (PairCatOf C H Good) C where
  obj := pairFst
  map f := ⟨f.1, f.2.1⟩
  map_id _ := rfl
  map_trans _ _ := rfl

/-- The input projection is the identity on underlying sets, hence a canonical
embedding. -/
theorem pairFstFunc_isCanonicalEmbedding (C H : Cat.{0, 0} Ω)
    (Good : Pt C → Pt H → Prop) : (pairFstFunc C H Good).IsCanonicalEmbedding where
  car_subset _ := subset_rfl
  map_restrict _ _ := rfl

open scoped Classical in
/-- The morphism of `H` underlying a morphism of `Babai.PairCatOf C H Good`.  It is unique
(`pairSndMap_eq`), so it is a well-defined function of the morphism. -/
noncomputable def pairSndMap {p q : Pt (PairCatOf C H Good)}
    (f : Hom (PairCatOf C H Good) p q) : ↥p.obj.sub ≃ ↥q.obj.sub := f.2.2.choose

theorem pairSndMap_spec {p q : Pt (PairCatOf C H Good)}
    (f : Hom (PairCatOf C H Good) p q) (x : ↥p.obj.sub) :
    ((pairSndMap f x : Ω)) = ((f.1 ⟨(x : Ω), p.obj.sub_subset x.2⟩ : Ω)) :=
  f.2.2.choose_spec.1 x

theorem pairSndMap_mem {p q : Pt (PairCatOf C H Good)}
    (f : Hom (PairCatOf C H Good) p q) :
    pairSndMap f ∈ H.Iso p.obj.snd q.obj.snd := f.2.2.choose_spec.2

/-- The morphism of `H` underlying a morphism of pairs is unique: it is determined
pointwise by the underlying bijection of the ambient sets. -/
theorem pairSndMap_eq {p q : Pt (PairCatOf C H Good)}
    (f : Hom (PairCatOf C H Good) p q) (g : ↥p.obj.sub ≃ ↥q.obj.sub)
    (hg : ∀ x : ↥p.obj.sub,
      ((g x : Ω)) = ((f.1 ⟨(x : Ω), p.obj.sub_subset x.2⟩ : Ω))) :
    pairSndMap f = g :=
  Equiv.ext fun x => Subtype.ext ((pairSndMap_spec f x).trans (hg x).symm)

/-- §6.  The object found, as a functor on the category of pairs: it forgets the input and
keeps the object the first step produced. -/
noncomputable def pairSndFunc (C H : Cat.{0, 0} Ω) (Good : Pt C → Pt H → Prop) :
    Func (PairCatOf C H Good) H where
  obj := pairSnd
  map f := ⟨pairSndMap f, pairSndMap_mem f⟩
  map_id p := Subtype.ext (pairSndMap_eq _ _ fun _ => rfl)
  map_trans := fun {p q _} f g => Subtype.ext (pairSndMap_eq _ _ fun x => by
    have h1 := pairSndMap_spec g (pairSndMap f x)
    have h2 : (⟨((pairSndMap f x : Ω)), q.obj.sub_subset (pairSndMap f x).2⟩ : ↥q.car)
        = f.1 ⟨(x : Ω), p.obj.sub_subset x.2⟩ := Subtype.ext (pairSndMap_spec f x)
    show ((pairSndMap g (pairSndMap f x) : Ω)) = _
    rw [h1, h2]
    rfl)

/-- §6.  The projection to the object found is a canonical embedding: `□(F(p)) ⊆ □p` and
`F(f)` is the restriction of `f`. -/
theorem pairSndFunc_isCanonicalEmbedding (C H : Cat.{0, 0} Ω)
    (Good : Pt C → Pt H → Prop) : (pairSndFunc C H Good).IsCanonicalEmbedding where
  car_subset p := p.obj.sub_subset
  map_restrict f x := pairSndMap_spec f x

@[simp] theorem pairSndFunc_obj (C H : Cat.{0, 0} Ω) (Good : Pt C → Pt H → Prop)
    (p : Pt (PairCatOf C H Good)) : (pairSndFunc C H Good).obj p = pairSnd p := rfl

@[simp] theorem pairFstFunc_obj (C H : Cat.{0, 0} Ω) (Good : Pt C → Pt H → Prop)
    (p : Pt (PairCatOf C H Good)) : (pairFstFunc C H Good).obj p = pairFst p := rfl

/-- There are no morphisms between the two summands of `Babai.Cat.sum`, so "the object
found lies in the first summand" is invariant under isomorphism of pairs.  This is the
hypothesis of the canonical case distinction `Babai.FindsAtMultCost.cases` for both case
distinctions of the proof of Theorem 9.2.1. -/
theorem pairSnd_isLeft_iso {C A B : Cat.{0, 0} Ω} {Good : Pt C → Pt (Cat.sum A B) → Prop}
    {p q : Pt (PairCatOf C (Cat.sum A B) Good)}
    (h : ((PairCatOf C (Cat.sum A B) Good).IsoP p q).Nonempty)
    (hp : (p.obj.snd).isLeft) : (q.obj.snd).isLeft := by
  obtain ⟨f, -, g, -, hH⟩ := h
  rcases hps : p.obj.snd with P | Y
  · rcases hqs : q.obj.snd with Q | Y'
    · simp
    · rw [hps, hqs] at hH
      exact absurd hH (Set.notMem_empty g)
  · rw [hps] at hp
    simp at hp

end Babai
