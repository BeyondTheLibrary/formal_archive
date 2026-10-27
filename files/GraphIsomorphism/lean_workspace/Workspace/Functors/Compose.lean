/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 6: chaining canonical reductions; the multiplicative costs multiply.
-/
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.QuotientGroup.Defs
import Workspace.Functors.Cost

/-!
# §6 Chaining reductions: the multiplicative costs multiply

Every procedure of §8 and §9 is a chain of steps of the form

> *"at a multiplicative cost of `a` we can find a canonical `Y`; from `Y`, at a
> multiplicative cost of `b`, we can find a canonical `Z`"*,

and the paper then speaks of the total multiplicative cost `ab` (Def. 6.0.3 and the
remarks after Prop. 6.0.4: a reduction at multiplicative cost `s` splits `Iso(X,Y)` into
`|F(Y)| = s` equal parts, so performing a second reduction inside each part splits it into
`s·s'` parts).  This file proves that principle for `Babai.FindsAtMultCost`.

The construction is the paper's: the tuple that the composite reduction assigns to `X` is
the set of pairs *(a version `X'` of `X` from step 1, a version `Z'` of `G₁(X,X')` from
step 2)*.  Concretely, if

* `F₁ : C → E₁` is the first reduction and `G₁ : C^{F₁} → H` the object it finds, and
* `F₂ : H → E₂` is the second reduction and `G₂ : H^{F₂} → K` the object it finds,

then `F₂ ∘ G₁ : C^{F₁} → E₂` is a reduction of `C^{F₁}`, and the category of pairs of
*that* reduction, `(C^{F₁})^{F₂ ∘ G₁}`, is used as the category `D` of the composite: the
composite tuple assigned to `X` is the set of its objects whose `C`-component is `X`
(`Babai.Compose.tup`).  The composite `G` is the chain

  `C^{F}  →  (C^{F₁})^{F₂ ∘ G₁}  →  H^{F₂}  →  K`,

whose middle map `Babai.Compose.psi` is a canonical embedding because `G₁` is; so the
composite is one too (`Babai.Func.IsCanonicalEmbedding.comp`), which is what makes the
canonicity of the composite a theorem and not an assumption.

**Finiteness.**  `Set.ncard` of an infinite set is `0`, so the cost bound of
`FindsAtMultCost` carries the finiteness of the tuple with it; the composite tuple is
finite because it is the range of a map from a `Σ`-type whose base and fibres are the
(finite) tuples of the two steps.

## Numbering map

| Paper | Lean |
|---|---|
| "at multiplicative cost `a`…, then at multiplicative cost `b`…; total `ab`" (§6, after Prop. 6.0.4) | `Babai.FindsAtMultCost.comp` |
| a canonical construction with no choices is a reduction at cost `1` | `Babai.FindsAtMultCost.of_canonicalEmbedding` |
| weakening the cost bound / the property found | `Babai.FindsAtMultCost.mono` |
| a canonical case distinction combines two reductions | `Babai.FindsAtMultCost.cases` |
| a reduction whose tuple lives on `□X` (normal form) | `Babai.NormalRed`, `Babai.FindsAtMultCost.of_normal`, `.exists_normal` |
| full subcategory of admissible inputs, disjoint union of categories | `Babai.Cat.full`, `Babai.Cat.sum` |
| individualizing `t` vertices is a reduction at cost `n(n-1)…(n-t+1)` (§6, individualization example) | `Babai.FindsAtMultCost.individualize` |
-/

universe u v v' v''

namespace Babai

/-! ### Composition of canonical embeddings -/

/-- §6.  A composite of canonical embeddings is a canonical embedding: the underlying sets
shrink twice, and the map is the restriction of a restriction. -/
theorem Func.IsCanonicalEmbedding.comp {Ω : Type u} {C : Cat.{u, v} Ω} {D : Cat.{u, v'} Ω}
    {K : Cat.{u, v''} Ω} {F : Func C D} {G : Func D K} (hF : F.IsCanonicalEmbedding)
    (hG : G.IsCanonicalEmbedding) : (F.comp G).IsCanonicalEmbedding where
  car_subset X := (hG.car_subset (F.obj X)).trans (hF.car_subset X)
  map_restrict {X Y} f x := by
    have h1 := hG.map_restrict (F.map f) x
    have h2 := hF.map_restrict f ⟨(x : Ω), hG.car_subset (F.obj X) x.2⟩
    exact h1.trans h2

/-! ### A step of a reduction produces a matching member of the next tuple

This is the step of the proof of Prop. 6.0.4 that is used over and over below: an
isomorphism `f : X → Y` of `C` and a member `X'` of the tuple `F(X)` determine a member
`Y'` of `F(Y)` with `f ∈ F⁻¹Iso(X',Y')`. -/

section Step

variable {Ω Ω' : Type u} {C : Cat.{u, v} Ω} {D : Cat.{u, v'} Ω'} {E : TupleClass D}

/-- Definition 6.0.1(ii), in the form used throughout §6: for every `X' ∈ F(X)` and every
`f ∈ Iso(X,Y)` there is `Y' ∈ F(Y)` with `f ∈ F⁻¹(Iso(X',Y'))`.  (This is the second half
of the proof of Prop. 6.0.4.) -/
theorem exists_mem_tupleOf_preimageIso (F : Func C E.cat) {X Y : Pt C}
    {X' : D.Obj (F.obj X).car} (hX' : X' ∈ tupleOf F X) {f : ↥X.car ≃ ↥Y.car}
    (hf : f ∈ C.IsoP X Y) : ∃ Y' ∈ tupleOf F Y, f ∈ preimageIso F X' Y' := by
  obtain ⟨A, hA, B, hB, hAB⟩ := (F.map (⟨f, hf⟩ : Hom C X Y)).2
  obtain ⟨Y', hY', h⟩ := E.cond_ii ((F.obj X).obj).2 ((F.obj Y).obj).2 hA hX' hB hAB
  exact ⟨Y', hY', hf, h⟩

/-- The tuple assigned to an object is non-empty (Def. 6.0.1). -/
theorem tupleOf_nonempty (F : Func C E.cat) (X : Pt C) : (tupleOf F X).Nonempty :=
  E.nonempty ((F.obj X).obj).2

end Step

/-! ### Proposition 6.0.4 in group form: the index of `Aut(X,X')` in `Aut(X)`

§6, after Prop. 6.0.4: a reduction at multiplicative cost `s` splits `Iso(X,Y)` into at
most `s` disjoint parts of equal size.  For `Y = X` the parts are the cosets of the
subgroup `Aut(X,X') = Iso((X,X'),(X,X'))` of `Aut(X)`, so that subgroup has index at most
`|F(X)|`.  This is what the paper uses whenever it says that individualizing costs a factor
`s` (and it is what Prop. 9.1.1 needs). -/

section Index

variable {Ω Ω' : Type u} {C : Cat.{u, v} Ω} {D : Cat.{u, v'} Ω'} {E : TupleClass D}

/-- Definition 6.0.5: the object `(X, X')` of `C^F`. -/
def pairPt (F : Func C E.cat) {X : Pt C} {X' : D.Obj (F.obj X).car}
    (hX' : X' ∈ tupleOf F X) : Pt (pairCat F) := ⟨X.car, ⟨X.obj, ⟨X', hX'⟩⟩⟩

open scoped Classical in
/-- The member of `F(X)` that an automorphism `σ` of `X` carries `X'` to: the unique
`Y' ∈ F(X)` with `σ ∈ F⁻¹(Iso(X',Y'))` (Prop. 6.0.4). -/
noncomputable def versionOf (F : Func C E.cat) {X : Pt C} {X' : D.Obj (F.obj X).car}
    (hX' : X' ∈ tupleOf F X) (σ : ↥(C.Aut X)) : ↥(tupleOf F X) :=
  ⟨(exists_mem_tupleOf_preimageIso F hX' σ.2).choose,
    (exists_mem_tupleOf_preimageIso F hX' σ.2).choose_spec.1⟩

theorem mem_preimageIso_versionOf (F : Func C E.cat) {X : Pt C}
    {X' : D.Obj (F.obj X).car} (hX' : X' ∈ tupleOf F X) (σ : ↥(C.Aut X)) :
    (σ : Equiv.Perm ↥X.car) ∈ preimageIso F X' (versionOf F hX' σ).1 :=
  (exists_mem_tupleOf_preimageIso F hX' σ.2).choose_spec.2

/-- Uniqueness in Prop. 6.0.4: the terms of the union are disjoint. -/
theorem versionOf_eq_of_mem (F : Func C E.cat) {X : Pt C} {X' : D.Obj (F.obj X).car}
    (hX' : X' ∈ tupleOf F X) (σ : ↥(C.Aut X)) {Y' : D.Obj (F.obj X).car}
    (h : (σ : Equiv.Perm ↥X.car) ∈ preimageIso F X' Y') :
    (versionOf F hX' σ).1 = Y' := by
  by_contra hne
  exact Set.disjoint_left.1 (preimageIso_disjoint F X' hne)
    (mem_preimageIso_versionOf F hX' σ) h

/-- Prop. 6.0.4 for `Y = X`: two automorphisms of `X` carry `X'` to the same member of
`F(X)` exactly if they lie in the same left coset of `Aut(X,X')`. -/
theorem versionOf_eq_iff (F : Func C E.cat) {X : Pt C} {X' : D.Obj (F.obj X).car}
    (hX' : X' ∈ tupleOf F X) (σ τ : ↥(C.Aut X)) :
    versionOf F hX' σ = versionOf F hX' τ ↔
      ((σ⁻¹ * τ : Equiv.Perm ↥X.car)) ∈ (pairCat F).Aut (pairPt F hX') := by
  have hσ := mem_preimageIso_versionOf F hX' σ
  have hτ := mem_preimageIso_versionOf F hX' τ
  have hτ' : (τ : Equiv.Perm ↥X.car) ∈ (pairCat F).Iso (pairPt F hX').obj
      (pairPt F (versionOf F hX' τ).2).obj := hτ
  have hmul : ((σ⁻¹ * τ : Equiv.Perm ↥X.car))
      = (τ : Equiv.Perm ↥X.car).trans (σ : Equiv.Perm ↥X.car).symm := rfl
  constructor
  · intro heq
    have hset : preimageIso F X' (versionOf F hX' σ).1
        = preimageIso F X' (versionOf F hX' τ).1 :=
      congrArg (fun z : ↥(tupleOf F X) => preimageIso F X' z.1) heq
    have hσ' : (σ : Equiv.Perm ↥X.car) ∈ preimageIso F X' (versionOf F hX' τ).1 :=
      hset ▸ hσ
    have hσ'' : (σ : Equiv.Perm ↥X.car) ∈ (pairCat F).Iso (pairPt F hX').obj
        (pairPt F (versionOf F hX' τ).2).obj := hσ'
    have hmem : ((τ : Equiv.Perm ↥X.car).trans (σ : Equiv.Perm ↥X.car).symm)
        ∈ (pairCat F).Iso (pairPt F hX').obj (pairPt F hX').obj :=
      (pairCat F).trans_mem hτ' ((pairCat F).symm_mem hσ'')
    exact Set.mem_of_eq_of_mem hmul hmem
  · intro h
    have hg : ((τ : Equiv.Perm ↥X.car).trans (σ : Equiv.Perm ↥X.car).symm)
        ∈ (pairCat F).Iso (pairPt F hX').obj (pairPt F hX').obj :=
      Set.mem_of_eq_of_mem hmul.symm h
    have hcomp := (pairCat F).trans_mem ((pairCat F).symm_mem hg) hτ'
    have heqe : ((τ : Equiv.Perm ↥X.car).trans
        (σ : Equiv.Perm ↥X.car).symm).symm.trans (τ : Equiv.Perm ↥X.car)
        = (σ : Equiv.Perm ↥X.car) := by
      ext x; simp
    have hσ' : (σ : Equiv.Perm ↥X.car) ∈ preimageIso F X' (versionOf F hX' τ).1 :=
      Set.mem_of_eq_of_mem heqe.symm hcomp
    exact Subtype.ext (versionOf_eq_of_mem F hX' σ hσ')

/-- Proposition 6.0.4, group form.  *"`Iso(X,Y) = ⋃ {F⁻¹(Iso(X',Y')) | Y' ∈ F(Y)}`, the
terms are disjoint and all the nonempty terms have the same cardinality."*  Taken at
`Y = X`: the terms are the left cosets of `Aut(X,X')` in `Aut(X)`, so

  `[Aut(X) : Aut(X,X')] ≤ |F(X)|`,

which is the meaning of *"at a multiplicative cost of `|F(X)|`"*. -/
theorem relIndex_aut_pairCat_le (F : Func C E.cat) {X : Pt C}
    {X' : D.Obj (F.obj X).car} (hX' : X' ∈ tupleOf F X) (hfin : (tupleOf F X).Finite) :
    ((pairCat F).Aut (pairPt F hX')).relIndex (C.Aut X) ≤ (tupleOf F X).ncard := by
  classical
  haveI : Finite ↥(tupleOf F X) := hfin.to_subtype
  set H := ((pairCat F).Aut (pairPt F hX')).subgroupOf (C.Aut X) with hH
  letI : Setoid ↥(C.Aut X) := QuotientGroup.leftRel H
  have hwd : ∀ a b : ↥(C.Aut X), a ≈ b → versionOf F hX' a = versionOf F hX' b := by
    intro a b hab
    have hab' : (a : ↥(C.Aut X))⁻¹ * b ∈ H := (QuotientGroup.leftRel_apply (s := H)).1 hab
    exact (versionOf_eq_iff F hX' a b).2 hab'
  have hinj : Function.Injective
      (Quotient.lift (versionOf F hX') hwd : ↥(C.Aut X) ⧸ H → ↥(tupleOf F X)) := by
    refine Quotient.ind₂ ?_
    intro a b hab
    have hab' : versionOf F hX' a = versionOf F hX' b := hab
    refine Quotient.sound ?_
    exact (QuotientGroup.leftRel_apply (s := H)).2 ((versionOf_eq_iff F hX' a b).1 hab')
  have hle := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_coe_set_eq] at hle
  exact hle

end Index

/-! ### The composite reduction -/

namespace Compose

variable {Ω : Type} {C H K : Cat.{0, 0} Ω}
  {D₁ : Cat.{0, 0} Ω} {E₁ : TupleClass D₁}
  {D₂ : Cat.{0, 0} Ω} {E₂ : TupleClass D₂}

/-- The pair `(X, X')` of §6, Def. 6.0.5, as an object of `C^{F₁}`. -/
abbrev pt₁ (F₁ : Func C E₁.cat) (X : Pt C) (X' : ↥(tupleOf F₁ X)) : Pt (pairCat F₁) :=
  ⟨X.car, ⟨X.obj, X'⟩⟩

/-- The index set of the composite tuple of `X`: a version `X'` of `X` from step 1,
followed by a version `Z'` of `G₁(X,X')` from step 2. -/
abbrev Index (F₁ : Func C E₁.cat) (G₁ : Func (pairCat F₁) H) (F₂ : Func H E₂.cat)
    (X : Pt C) : Type :=
  (X' : ↥(tupleOf F₁ X)) × ↥(tupleOf (G₁.comp F₂) (pt₁ F₁ X X'))

/-- The member of the composite tuple indexed by a pair of versions. -/
def mk (F₁ : Func C E₁.cat) (G₁ : Func (pairCat F₁) H) (F₂ : Func H E₂.cat) (X : Pt C)
    (p : Index F₁ G₁ F₂ X) : (pairCat (G₁.comp F₂)).Obj X.car :=
  ⟨⟨X.obj, p.1⟩, p.2⟩

/-- The composite tuple assigned to `X`: all pairs *(version of `X`, version of the object
found from it)*. -/
def tup (F₁ : Func C E₁.cat) (G₁ : Func (pairCat F₁) H) (F₂ : Func H E₂.cat) (X : Pt C) :
    Set ((pairCat (G₁.comp F₂)).Obj X.car) :=
  Set.range (mk F₁ G₁ F₂ X)

variable (F₁ : Func C E₁.cat) (G₁ : Func (pairCat F₁) H) (F₂ : Func H E₂.cat)

theorem mem_tup_iff {X : Pt C} (q : (pairCat (G₁.comp F₂)).Obj X.car) :
    q ∈ tup F₁ G₁ F₂ X ↔ q.1.1 = X.obj := by
  constructor
  · rintro ⟨p, rfl⟩; rfl
  · intro h
    obtain ⟨⟨X₀, X'⟩, Z'⟩ := q
    simp only at h
    subst h
    exact ⟨⟨X', Z'⟩, rfl⟩

theorem mk_mem_tup {X : Pt C} (p : Index F₁ G₁ F₂ X) : mk F₁ G₁ F₂ X p ∈ tup F₁ G₁ F₂ X :=
  ⟨p, rfl⟩

/-- The step that both Definition 6.0.1(ii) for the composite and the functoriality of the
composite reduction need: an isomorphism `f : X → Y` of `C` carries a pair of versions of
`X` to a pair of versions of `Y`, and is then a morphism of the composite tuple category.
It is Definition 6.0.1(ii) applied twice, once for each step. -/
theorem exists_index_iso {X Y : Pt C} {f : ↥X.car ≃ ↥Y.car} (hf : f ∈ C.IsoP X Y)
    (p : Index F₁ G₁ F₂ X) :
    ∃ q : Index F₁ G₁ F₂ Y,
      f ∈ (pairCat (G₁.comp F₂)).Iso (mk F₁ G₁ F₂ X p) (mk F₁ G₁ F₂ Y q) := by
  obtain ⟨X'B, hX'B, hf1⟩ := exists_mem_tupleOf_preimageIso F₁ p.1.2 hf
  have hf1' : f ∈ (pairCat F₁).IsoP (pt₁ F₁ X p.1) (pt₁ F₁ Y ⟨X'B, hX'B⟩) := hf1
  obtain ⟨Z'B, hZ'B, hf2⟩ :=
    exists_mem_tupleOf_preimageIso (G₁.comp F₂) p.2.2 hf1'
  exact ⟨⟨⟨X'B, hX'B⟩, ⟨Z'B, hZ'B⟩⟩, hf2⟩

/-- Definition 6.0.1 for the composite: the class of composite tuples. -/
def tupleClass : TupleClass (pairCat (G₁.comp F₂)) where
  mem s := {𝒳 | ∃ X : C.Obj s, 𝒳 = tup F₁ G₁ F₂ ⟨s, X⟩}
  nonempty := by
    rintro s 𝒳 ⟨X, rfl⟩
    obtain ⟨X', hX'⟩ := tupleOf_nonempty F₁ (⟨s, X⟩ : Pt C)
    obtain ⟨Z', hZ'⟩ := tupleOf_nonempty (G₁.comp F₂) (pt₁ F₁ ⟨s, X⟩ ⟨X', hX'⟩)
    exact ⟨_, mk_mem_tup F₁ G₁ F₂ ⟨⟨X', hX'⟩, ⟨Z', hZ'⟩⟩⟩
  cond_ii := by
    rintro s t 𝒳 𝒴 ⟨X, rfl⟩ ⟨Y, rfl⟩ A A' B hA hA' hB f hf
    rw [mem_tup_iff] at hA hB
    obtain ⟨p, rfl⟩ := hA'
    -- `f` is an isomorphism of `C` from `X` to `Y`
    have hfC : f ∈ C.IsoP (⟨s, X⟩ : Pt C) ⟨t, Y⟩ := by
      have h := hf.1.1
      rwa [hA, hB] at h
    obtain ⟨q, hq⟩ := exists_index_iso F₁ G₁ F₂ hfC p
    exact ⟨_, mk_mem_tup F₁ G₁ F₂ q, hq⟩

/-- The composite reduction `F : C → E` of Definition 6.0.3. -/
noncomputable def redFunc : Func C (tupleClass F₁ G₁ F₂).cat where
  obj X := ⟨X.car, ⟨tup F₁ G₁ F₂ X, ⟨X.obj, rfl⟩⟩⟩
  map {X Y} f := by
    refine ⟨f.1, ?_⟩
    obtain ⟨X', hX'⟩ := tupleOf_nonempty F₁ X
    obtain ⟨Z', hZ'⟩ := tupleOf_nonempty (G₁.comp F₂) (pt₁ F₁ X ⟨X', hX'⟩)
    obtain ⟨q, hq⟩ :=
      exists_index_iso F₁ G₁ F₂ f.2 (⟨⟨X', hX'⟩, ⟨Z', hZ'⟩⟩ : Index F₁ G₁ F₂ X)
    exact ⟨_, mk_mem_tup F₁ G₁ F₂ _, _, mk_mem_tup F₁ G₁ F₂ q, hq⟩
  map_id _ := Subtype.ext rfl
  map_trans _ _ := Subtype.ext rfl

theorem tupleOf_redFunc (X : Pt C) :
    tupleOf (redFunc F₁ G₁ F₂) X = tup F₁ G₁ F₂ X := rfl

/-- The first leg of the composite functor: forget the `C`-component of a pair of the
composite reduction. -/
def phi : Func (pairCat (redFunc F₁ G₁ F₂)) (pairCat (G₁.comp F₂)) where
  obj p := ⟨p.car, p.obj.2.1⟩
  map f := ⟨f.1, f.2.2⟩
  map_id _ := Subtype.ext rfl
  map_trans _ _ := Subtype.ext rfl

theorem phi_isCanonicalEmbedding : (phi F₁ G₁ F₂).IsCanonicalEmbedding where
  car_subset _ := subset_rfl
  map_restrict _ _ := rfl

/-- The second leg: a pair `((X,X'),Z')` of the two-step reduction is the pair
`(G₁(X,X'), Z')` of the second reduction.  This is the step that carries the canonicity of
`G₁` into the composite. -/
def psi : Func (pairCat (G₁.comp F₂)) (pairCat F₂) where
  obj p := ⟨(G₁.obj ⟨p.car, p.obj.1⟩).car, ⟨(G₁.obj ⟨p.car, p.obj.1⟩).obj, p.obj.2⟩⟩
  map {p q} f := ⟨(G₁.map (⟨f.1, f.2.1⟩ : Hom (pairCat F₁) ⟨p.car, p.obj.1⟩
      ⟨q.car, q.obj.1⟩)).1, ⟨(G₁.map _).2, f.2.2⟩⟩
  map_id p := by
    refine Hom.ext fun x => ?_
    have h : (G₁.map (Hom.id (⟨p.car, p.obj.1⟩ : Pt (pairCat F₁)))) x = x := by
      rw [G₁.map_id]; rfl
    exact h
  map_trans {p q r} f g := by
    refine Hom.ext fun x => ?_
    have h : (G₁.map (Hom.trans
          (⟨f.1, f.2.1⟩ : Hom (pairCat F₁) ⟨p.car, p.obj.1⟩ ⟨q.car, q.obj.1⟩)
          (⟨g.1, g.2.1⟩ : Hom (pairCat F₁) ⟨q.car, q.obj.1⟩ ⟨r.car, r.obj.1⟩))) x
        = (G₁.map (⟨g.1, g.2.1⟩ : Hom (pairCat F₁) ⟨q.car, q.obj.1⟩ ⟨r.car, r.obj.1⟩))
            ((G₁.map (⟨f.1, f.2.1⟩ : Hom (pairCat F₁) ⟨p.car, p.obj.1⟩
              ⟨q.car, q.obj.1⟩)) x) := by
      rw [G₁.map_trans]; rfl
    exact h

theorem psi_isCanonicalEmbedding (hG₁ : G₁.IsCanonicalEmbedding) :
    (psi F₁ G₁ F₂).IsCanonicalEmbedding where
  car_subset p := hG₁.car_subset ⟨p.car, p.obj.1⟩
  map_restrict f x := hG₁.map_restrict _ x

end Compose

/-! ### The composition theorem -/

open Compose in
/-- §6 (Def. 6.0.3 and the remarks after Prop. 6.0.4).  **Multiplicative costs multiply.**
If at multiplicative cost `c₁` we can canonically find an object `Y` with `Good₁ X Y`, and
from any such `Y` at multiplicative cost `c₂ Y` an object `Z` with `Good₂ Y Z`, then at
multiplicative cost `c₁ X · c₂' X` we can canonically find a `Z` for which such an
intermediate `Y` exists — provided `c₂ Y ≤ c₂' X` for every `Y` that step 1 can produce
from `X`, so that the second cost can be expressed in terms of the input of step 1.

The tuple of the composite is the set of pairs *(version from step 1, version from step 2)*
and the composite functor is the chain `C^F → (C^{F₁})^{F₂∘G₁} → H^{F₂} → K`; its
canonicity is proved, not assumed. -/
theorem FindsAtMultCost.comp {Ω : Type} {C H K : Cat.{0, 0} Ω} {c₁ : Pt C → ℕ}
    {c₂ : Pt H → ℕ} {c₂' : Pt C → ℕ} {Good₁ : Pt C → Pt H → Prop}
    {Good₂ : Pt H → Pt K → Prop} (h₁ : FindsAtMultCost C H c₁ Good₁)
    (h₂ : FindsAtMultCost H K c₂ Good₂)
    (hc : ∀ (X : Pt C) (Y : Pt H), Good₁ X Y → c₂ Y ≤ c₂' X) :
    FindsAtMultCost C K (fun X => c₁ X * c₂' X) (fun X Z => ∃ Y, Good₁ X Y ∧ Good₂ Y Z) := by
  classical
  obtain ⟨D₁, E₁, F₁, G₁, hG₁emb, hcost₁, hgood₁⟩ := h₁
  obtain ⟨D₂, E₂, F₂, G₂, hG₂emb, hcost₂, hgood₂⟩ := h₂
  refine ⟨pairCat (G₁.comp F₂), tupleClass F₁ G₁ F₂, redFunc F₁ G₁ F₂,
    (phi F₁ G₁ F₂).comp ((psi F₁ G₁ F₂).comp G₂), ?_, ?_, ?_⟩
  · exact (phi_isCanonicalEmbedding F₁ G₁ F₂).comp
      ((psi_isCanonicalEmbedding F₁ G₁ F₂ hG₁emb).comp hG₂emb)
  · -- the cost bound
    intro X
    have hfin₁ : (tupleOf F₁ X).Finite := (hcost₁ X).1
    have hfib : ∀ X' : ↥(tupleOf F₁ X),
        (tupleOf (G₁.comp F₂) (pt₁ F₁ X X')).Finite :=
      fun X' => (hcost₂ (G₁.obj (pt₁ F₁ X X'))).1
    haveI instB : Fintype ↥(tupleOf F₁ X) := hfin₁.fintype
    haveI instF : ∀ X' : ↥(tupleOf F₁ X),
        Fintype ↥(tupleOf (G₁.comp F₂) (pt₁ F₁ X X')) := fun X' => (hfib X').fintype
    -- each fibre is the tuple of step 2 for an object that step 1 can produce from `X`
    have hb : ∀ X' : ↥(tupleOf F₁ X),
        Nat.card ↥(tupleOf (G₁.comp F₂) (pt₁ F₁ X X')) ≤ c₂' X := by
      intro X'
      rw [Nat.card_coe_set_eq]
      exact ((hcost₂ (G₁.obj (pt₁ F₁ X X'))).2).trans
        (hc X _ (hgood₁ X X'.1 X'.2))
    have hIdx : Nat.card (Index F₁ G₁ F₂ X) ≤ c₁ X * c₂' X := by
      rw [Nat.card_eq_fintype_card, Fintype.card_sigma]
      calc ∑ X' : ↥(tupleOf F₁ X),
              Fintype.card ↥(tupleOf (G₁.comp F₂) (pt₁ F₁ X X'))
          ≤ ∑ _X' : ↥(tupleOf F₁ X), c₂' X :=
            Finset.sum_le_sum fun X' _ => by
              rw [← Nat.card_eq_fintype_card]; exact hb X'
        _ = Fintype.card ↥(tupleOf F₁ X) * c₂' X := by
            rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
        _ ≤ c₁ X * c₂' X :=
            Nat.mul_le_mul_right _
              (by rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]; exact (hcost₁ X).2)
    have hrange : tupleOf (redFunc F₁ G₁ F₂) X = Set.range (mk F₁ G₁ F₂ X) := rfl
    refine ⟨by rw [hrange]; exact Set.finite_range _, ?_⟩
    rw [hrange, ← Set.image_univ]
    refine (Set.ncard_image_le Set.finite_univ).trans ?_
    rw [Set.ncard_univ]
    exact hIdx
  · -- the property found
    intro X q hq
    have hq' : q.1.1 = X.obj := (mem_tup_iff F₁ G₁ F₂ (X := X) q).1 hq
    obtain ⟨⟨X₀, X'⟩, Z'⟩ := q
    simp only at hq'
    subst hq'
    exact ⟨G₁.obj (pt₁ F₁ X X'), hgood₁ X X'.1 X'.2, hgood₂ _ Z'.1 Z'.2⟩

/-! ### The cost-one case, monotonicity, and a canonical case distinction -/

/-- §6.  A canonical construction that makes no choices is a reduction at multiplicative
cost `1`: take the tuple `F(X) = {X}` itself (the one-element tuples of Def. 6.0.1), so
that `C^F ≅ C`, and let the functor found be the given canonical embedding `G : C → K`. -/
theorem FindsAtMultCost.of_canonicalEmbedding {Ω : Type} {C K : Cat.{0, 0} Ω}
    {Good : Pt C → Pt K → Prop} (G : Func C K) (hG : G.IsCanonicalEmbedding)
    (hgood : ∀ X : Pt C, Good X (G.obj X)) :
    FindsAtMultCost C K (fun _ => 1) Good := by
  classical
  -- `D := C`, and `F(X)` is the singleton tuple `{X}`.
  refine ⟨C, ⟨fun s => {𝒳 | ∃ X : C.Obj s, 𝒳 = {X}}, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rintro s 𝒳 ⟨X, rfl⟩; exact ⟨X, rfl⟩
  · rintro s t 𝒳 𝒴 ⟨X, rfl⟩ ⟨Y, rfl⟩ A A' B hA hA' hB f hf
    simp only [Set.mem_singleton_iff] at hA hA' hB
    subst hA; subst hA'; subst hB
    exact ⟨B, rfl, hf⟩
  · -- the reduction functor
    exact
      { obj := fun X => ⟨X.car, ⟨{X.obj}, ⟨X.obj, rfl⟩⟩⟩
        map := fun {X Y} f => ⟨f.1, X.obj, rfl, Y.obj, rfl, f.2⟩
        map_id := fun _ => Subtype.ext rfl
        map_trans := fun _ _ => Subtype.ext rfl }
  · -- the functor on pairs: forget the (unique) version and apply `G`
    exact
      { obj := fun p => G.obj ⟨p.car, p.obj.1⟩
        map := fun {p q} f => G.map ⟨f.1, f.2.1⟩
        map_id := fun p => G.map_id ⟨p.car, p.obj.1⟩
        map_trans := fun {p q r} f g =>
          G.map_trans (⟨f.1, f.2.1⟩ : Hom C ⟨p.car, p.obj.1⟩ ⟨q.car, q.obj.1⟩)
            (⟨g.1, g.2.1⟩ : Hom C ⟨q.car, q.obj.1⟩ ⟨r.car, r.obj.1⟩) }
  · exact ⟨fun p => hG.car_subset ⟨p.car, p.obj.1⟩, fun f x => hG.map_restrict _ x⟩
  · intro X
    refine ⟨Set.finite_singleton _, ?_⟩
    show ({X.obj} : Set (C.Obj X.car)).ncard ≤ 1
    simp
  · intro X X' hX'
    exact hgood X

/-- §6.  Weakening: a reduction at cost `cost` is one at any larger cost, and a property
found implies any weaker one. -/
theorem FindsAtMultCost.mono {Ω : Type} {C K : Cat.{0, 0} Ω} {cost cost' : Pt C → ℕ}
    {Good Good' : Pt C → Pt K → Prop} (h : FindsAtMultCost C K cost Good)
    (hcost : ∀ X, cost X ≤ cost' X) (hgood : ∀ X Z, Good X Z → Good' X Z) :
    FindsAtMultCost C K cost' Good' := by
  obtain ⟨D, E, F, G, hGemb, hc, hg⟩ := h
  exact ⟨D, E, F, G, hGemb, fun X => ⟨(hc X).1, (hc X).2.trans (hcost X)⟩,
    fun X X' hX' => hgood _ _ (hg X X' hX')⟩

/-! ### Two constructions on the paper's categories

These are the categories in which §9 states its results, and the two constructions that a
canonical case distinction needs: the full subcategory of the admissible inputs, and the
disjoint union of two categories. -/

/-- The full subcategory of `C` on the objects satisfying `P`: same morphisms.

This is where the hypotheses on the *input* of the algorithms of §9 live: the source
category of the canonical construction is the category of admissible inputs. -/
def Cat.full {Ω : Type u} (C : Cat.{u, v} Ω) (P : ∀ s : Set Ω, C.Obj s → Prop) :
    Cat.{u, v} Ω where
  Obj s := {X : C.Obj s // P s X}
  Iso X Y := C.Iso X.1 Y.1
  refl_mem X := C.refl_mem X.1
  symm_mem hf := C.symm_mem hf
  trans_mem hf hg := C.trans_mem hf hg
  faithful hid := Subtype.ext (C.faithful hid)

/-- The disjoint union of two categories: an object is an object of `C` or an object of
`D` (with the same underlying set), and there are no morphisms between the two kinds.

§9.2 needs it because the output of the algorithm is *either* a colored partition *or* an
embedded Johnson scheme, and the paper's canonicity is canonicity of that output, whichever
kind it is. -/
def Cat.sum {Ω : Type u} (C D : Cat.{u, v} Ω) : Cat.{u, v} Ω where
  Obj s := C.Obj s ⊕ D.Obj s
  Iso {s t} X Y :=
    match X, Y with
    | Sum.inl X, Sum.inl Y => C.Iso X Y
    | Sum.inr X, Sum.inr Y => D.Iso X Y
    | _, _ => (∅ : Set (↥s ≃ ↥t))
  refl_mem X := by cases X with
    | inl X => exact C.refl_mem X
    | inr X => exact D.refl_mem X
  symm_mem {s t X Y f} hf := by
    cases X with
    | inl X => cases Y with
      | inl Y => exact C.symm_mem hf
      | inr Y => exact absurd hf (Set.notMem_empty f)
    | inr X => cases Y with
      | inl Y => exact absurd hf (Set.notMem_empty f)
      | inr Y => exact D.symm_mem hf
  trans_mem {s t r X Y Z f g} hf hg := by
    cases X with
    | inl X => cases Y with
      | inl Y => cases Z with
        | inl Z => exact C.trans_mem hf hg
        | inr Z => exact absurd hg (Set.notMem_empty g)
      | inr Y => exact absurd hf (Set.notMem_empty f)
    | inr X => cases Y with
      | inl Y => exact absurd hf (Set.notMem_empty f)
      | inr Y => cases Z with
        | inl Z => exact absurd hg (Set.notMem_empty g)
        | inr Z => exact D.trans_mem hf hg
  faithful {s X Y} hid := by
    cases X with
    | inl X => cases Y with
      | inl Y => exact congrArg Sum.inl (C.faithful hid)
      | inr Y => exact absurd hid (Set.notMem_empty _)
    | inr X => cases Y with
      | inl Y => exact absurd hid (Set.notMem_empty _)
      | inr Y => exact congrArg Sum.inr (D.faithful hid)



/-- The inclusion of a full subcategory (`Cat.full`) into the ambient category: it is the
identity on underlying sets and on morphisms. -/
def Cat.fullIncl {Ω : Type u} (C : Cat.{u, v} Ω) (P : ∀ s : Set Ω, C.Obj s → Prop) :
    Func (C.full P) C where
  obj X := ⟨X.car, X.obj.1⟩
  map f := ⟨f.1, f.2⟩
  map_id _ := rfl
  map_trans _ _ := rfl

/-- §6.  **Restriction to a full subcategory.**  A canonical reduction of the whole
category restricts to the full subcategory of the objects satisfying `P`: the reduction
functor is composed with the inclusion, the tuple assigned to an object is unchanged, and
the object found is the same.

This is how a statement proved for a category whose objects carry a parameter as *data*
(so that the parameter may depend on the object, as `FindsAtMultCost.comp` requires)
implies the statement in which the parameter is fixed: the objects with a given value of
the parameter are a full subcategory. -/
theorem FindsAtMultCost.full {Ω : Type} {C K : Cat.{0, 0} Ω} {cost : Pt C → ℕ}
    {Good : Pt C → Pt K → Prop} (P : ∀ s : Set Ω, C.Obj s → Prop)
    (h : FindsAtMultCost C K cost Good) :
    FindsAtMultCost (C.full P) K (fun X => cost ⟨X.car, X.obj.1⟩)
      (fun X Z => Good ⟨X.car, X.obj.1⟩ Z) := by
  obtain ⟨D, E, F, G, hGemb, hc, hg⟩ := h
  refine ⟨D, E, (C.fullIncl P).comp F,
    { obj := fun p => G.obj ⟨p.car, ⟨p.obj.1.1, p.obj.2⟩⟩
      map := fun {_ _} f => G.map ⟨f.1, f.2⟩
      map_id := fun _ => G.map_id _
      map_trans := fun {p q r} f g =>
        G.map_trans
          (⟨f.1, f.2⟩ : Hom (pairCat F) ⟨p.car, ⟨p.obj.1.1, p.obj.2⟩⟩
            ⟨q.car, ⟨q.obj.1.1, q.obj.2⟩⟩)
          (⟨g.1, g.2⟩ : Hom (pairCat F) ⟨q.car, ⟨q.obj.1.1, q.obj.2⟩⟩
            ⟨r.car, ⟨r.obj.1.1, r.obj.2⟩⟩) },
    ⟨fun p => hGemb.car_subset _, fun f x => hGemb.map_restrict _ x⟩,
    fun X => hc _, fun X X' hX' => hg _ X' hX'⟩

/-! ### Individualization as a reduction -/

/-- §6, the individualization example (after Def. 6.0.7).  *"An example of this procedure
is individualization.  Suppose we individualize an ordered set of `t` vertices of the
hypergraph `X`; we do the same with `Y`. … The multiplicative cost will be
`s = n(n-1)…(n-t+1) ≤ n^t` where `n` is the number of vertices of `X`."*

As a `Babai.FindsAtMultCost` statement: at multiplicative cost `n(n-1)…(n-t+1)` we can
canonically find an individualized version of the input, i.e. the input together with an
ordered `t`-tuple of distinct vertices.  The hypothesis `hC` is the one of
`Babai.Individualize.redFunc`: every object has at least `t` vertices, without which the
set of individualized versions is empty and Definition 6.0.1 is violated.

For `t = 1` this is *"individualize one vertex, at a multiplicative cost of `n`"*, the
first step of Lemma 9.3.1, of Procedure ImprimitiveCase (§9.6) and of Procedure
Reduce-by-UPCC (§9.8). -/
theorem FindsAtMultCost.individualize {Ω : Type} {C : Cat.{0, 0} Ω} {t : ℕ}
    (hC : ∀ X : Pt C, Nonempty (Fin t ↪ ↥X.car)) (hfin : ∀ X : Pt C, X.car.Finite) :
    FindsAtMultCost C (Individualize.cat C t)
      (fun X => (Nat.card ↥X.car).descFactorial t)
      (fun X Z => ∃ u : Fin t ↪ ↥X.car, Z = ⟨X.car, (X.obj, u)⟩) := by
  classical
  refine ⟨Individualize.cat C t, Individualize.tupleClass t, Individualize.redFunc hC,
    { obj := fun p => ⟨p.car, p.obj.2.1⟩
      map := fun f => ⟨f.1, f.2.2⟩
      map_id := fun _ => Subtype.ext rfl
      map_trans := fun _ _ => Subtype.ext rfl },
    ⟨fun _ => subset_rfl, fun _ _ => rfl⟩, fun X => ?_, fun X X' hX' => ?_⟩
  · haveI : Finite ↥X.car := (hfin X).to_subtype
    obtain ⟨h1, h2⟩ := Individualize.isReductionAtCost_redFunc hC X X
    exact ⟨h1, h2.le⟩
  · refine ⟨X'.2, ?_⟩
    have h1 : X'.1 = X.obj := hX'
    have h2 : X' = (X.obj, X'.2) := Prod.ext h1 rfl
    exact congrArg (fun z => (⟨X.car, z⟩ : Pt (Individualize.cat C t))) h2

/-- §6, the individualization example, in the form the algorithms of §9 use it:
*"individualize `t` vertices, then perform a canonical construction on the individualized
object"*.  The multiplicative cost is that of the individualization alone, since the second
step makes no choices (`FindsAtMultCost.of_canonicalEmbedding`).

This is the shape of the first step of Lemma 9.3.1 (`t = 1`: individualize `x ∈ V`, then
build the colored partition `{Rᵢ(x)}` or the bipartite graph `X̄`), of step 1 of Procedure
ImprimitiveCase (§9.6) and of Procedure Reduce-by-UPCC (§9.8).  What remains to be supplied
in each case is the canonical construction `G` on the individualized objects. -/
theorem FindsAtMultCost.individualize_then {Ω : Type} {C K : Cat.{0, 0} Ω} {t : ℕ}
    {Good : Pt C → Pt K → Prop}
    (hC : ∀ X : Pt C, Nonempty (Fin t ↪ ↥X.car)) (hfin : ∀ X : Pt C, X.car.Finite)
    (G : Func (Individualize.cat C t) K) (hG : G.IsCanonicalEmbedding)
    (hgood : ∀ (X : Pt C) (u : Fin t ↪ ↥X.car), Good X (G.obj ⟨X.car, (X.obj, u)⟩)) :
    FindsAtMultCost C K (fun X => (Nat.card ↥X.car).descFactorial t) Good := by
  have h := (FindsAtMultCost.individualize hC hfin).comp
    (FindsAtMultCost.of_canonicalEmbedding (Good := fun Y Z => Z = G.obj Y) G hG
      (fun _ => rfl))
    (c₂' := fun _ => 1) (fun _ _ _ => le_rfl)
  refine h.mono (fun X => by rw [Nat.mul_one]) ?_
  rintro X Z ⟨Y, ⟨u, rfl⟩, rfl⟩
  exact hgood X u

/-! ### Reductions in normal form, and a canonical case distinction

§6: a canonical construction may branch on a property of the input that is invariant under
isomorphism (for instance *"does the UPCC have an `α`-dominant color?"*, §9.8).  The two
branches are reductions on the two full subcategories cut out by the property; together
they must be a single reduction on the whole category.

The obstacle is that the tuple `F(X)` of Definition 6.0.3 lives on the set `□(F(X))`, which
the definition leaves free, so two reductions need not put their tuples on the same set and
cannot be glued.  They can be *normalized* first: every reduction is equivalent to one
whose tuple consists of objects on `□X` itself and which acts on morphisms by the identity
(`Babai.NormalRed`, `Babai.FindsAtMultCost.exists_normal`).  Two normalized reductions are
glued by taking the disjoint union of their categories (`Babai.Cat.sum`), which is what
`Babai.FindsAtMultCost.cases` does. -/

/-- A reduction of Definition 6.0.3 in **normal form**: a category `D` whose objects on `s`
are "versions" of objects of `C` on `s` — the map `base` says of which one — such that a
morphism of `D` is a morphism of `C` between the underlying objects, every object has at
least one version, and a morphism `f : X → Y` of `C` carries each version of `X` to a
version of `Y` (Definition 6.0.1(ii)).

The tuple assigned to `X` is then the set `Babai.NormalRed.versions X` of versions of `X`,
which lives on `□X` itself. -/
structure NormalRed {Ω : Type} (C : Cat.{0, 0} Ω) where
  /-- The category of versions. -/
  D : Cat.{0, 0} Ω
  /-- The object of `C` that a version is a version of. -/
  base : ∀ {s : Set Ω}, D.Obj s → C.Obj s
  /-- A morphism of versions is a morphism of the underlying objects. -/
  iso_base : ∀ {s t : Set Ω} {A : D.Obj s} {B : D.Obj t} {f : ↥s ≃ ↥t},
    f ∈ D.Iso A B → f ∈ C.Iso (base A) (base B)
  /-- Definition 6.0.1: the tuple is non-empty. -/
  nonempty : ∀ X : Pt C, ∃ A : D.Obj X.car, base A = X.obj
  /-- Definition 6.0.1(ii). -/
  transport : ∀ {X Y : Pt C} {f : ↥X.car ≃ ↥Y.car}, f ∈ C.IsoP X Y →
    ∀ A : D.Obj X.car, base A = X.obj →
      ∃ B : D.Obj Y.car, base B = Y.obj ∧ f ∈ D.Iso A B

namespace NormalRed

variable {Ω : Type} {C K : Cat.{0, 0} Ω} (N : NormalRed C)

/-- The tuple that a normalized reduction assigns to `X`: the versions of `X`. -/
def versions (X : Pt C) : Set (N.D.Obj X.car) := {A | N.base A = X.obj}

@[simp] theorem mem_versions {X : Pt C} {A : N.D.Obj X.car} :
    A ∈ N.versions X ↔ N.base A = X.obj := Iff.rfl

/-- Definition 6.0.1 for a normalized reduction. -/
def tupleClass : TupleClass N.D where
  mem s := {𝒳 | ∃ X : C.Obj s, 𝒳 = N.versions ⟨s, X⟩}
  nonempty := by
    rintro s 𝒳 ⟨X, rfl⟩
    obtain ⟨A, hA⟩ := N.nonempty (⟨s, X⟩ : Pt C)
    exact ⟨A, hA⟩
  cond_ii := by
    rintro s t 𝒳 𝒴 ⟨X, rfl⟩ ⟨Y, rfl⟩ A A' B hA hA' hB f hf
    have hfC : f ∈ C.IsoP (⟨s, X⟩ : Pt C) ⟨t, Y⟩ := by
      have h := N.iso_base hf
      rwa [show N.base A = X from hA, show N.base B = Y from hB] at h
    obtain ⟨B', hB', hf'⟩ := N.transport hfC A' hA'
    exact ⟨B', hB', hf'⟩

/-- Definition 6.0.3 for a normalized reduction: the tuple of `X` is `versions X`, and the
reduction acts on morphisms by the identity. -/
def redFunc : Func C N.tupleClass.cat where
  obj X := ⟨X.car, ⟨N.versions X, ⟨X.obj, rfl⟩⟩⟩
  map {X Y} f := by
    refine ⟨f.1, ?_⟩
    obtain ⟨A, hA⟩ := N.nonempty X
    obtain ⟨B, hB, hf⟩ := N.transport f.2 A hA
    exact ⟨A, hA, B, hB, hf⟩
  map_id _ := Subtype.ext rfl
  map_trans _ _ := Subtype.ext rfl

theorem tupleOf_redFunc (X : Pt C) : tupleOf N.redFunc X = N.versions X := rfl

/-- The category of pairs `(X, X')` of a normalized reduction is `D` itself: the pair is
determined by its version, since the version knows its base. -/
def toD : Func (pairCat N.redFunc) N.D where
  obj p := ⟨p.car, p.obj.2.1⟩
  map f := ⟨f.1, f.2.2⟩
  map_id _ := Subtype.ext rfl
  map_trans _ _ := Subtype.ext rfl

theorem toD_isCanonicalEmbedding : N.toD.IsCanonicalEmbedding where
  car_subset _ := subset_rfl
  map_restrict _ _ := rfl

end NormalRed

/-- §6.  A normalized reduction, a canonical embedding `G` on its category of versions, a
cost bound and the required property give *"at a multiplicative cost of `cost` we can find
a canonical object with property `Good`"*. -/
theorem FindsAtMultCost.of_normal {Ω : Type} {C K : Cat.{0, 0} Ω} {cost : Pt C → ℕ}
    {Good : Pt C → Pt K → Prop} (N : NormalRed C) (G : Func N.D K)
    (hG : G.IsCanonicalEmbedding)
    (hcost : ∀ X : Pt C, (N.versions X).Finite ∧ (N.versions X).ncard ≤ cost X)
    (hgood : ∀ (X : Pt C) (A : N.D.Obj X.car), N.base A = X.obj →
      Good X (G.obj ⟨X.car, A⟩)) :
    FindsAtMultCost C K cost Good :=
  ⟨N.D, N.tupleClass, N.redFunc, N.toD.comp G, N.toD_isCanonicalEmbedding.comp hG,
    hcost, fun X A hA => hgood X A hA⟩

/-- The normal form of a reduction `F` with its functor `G`: the versions of `X` are the
pairs `(X, X')` with `X' ∈ F(X)`. -/
def NormalRed.ofReduction {Ω : Type} {C : Cat.{0, 0} Ω} {D : Cat.{0, 0} Ω}
    {E : TupleClass D} (F : Func C E.cat) : NormalRed C where
  D := pairCat F
  base p := p.1
  iso_base hf := hf.1
  nonempty X := by
    obtain ⟨X', hX'⟩ := tupleOf_nonempty F X
    exact ⟨⟨X.obj, ⟨X', hX'⟩⟩, rfl⟩
  transport := by
    rintro X Y f hf ⟨X₀, X'⟩ hbase
    simp only at hbase
    subst hbase
    obtain ⟨Y', hY', hf'⟩ := exists_mem_tupleOf_preimageIso F X'.2 hf
    exact ⟨⟨Y.obj, ⟨Y', hY'⟩⟩, rfl, hf'⟩

theorem NormalRed.versions_ofReduction {Ω : Type} {C : Cat.{0, 0} Ω} {D : Cat.{0, 0} Ω}
    {E : TupleClass D} (F : Func C E.cat) (X : Pt C) :
    (NormalRed.ofReduction F).versions X
      = Set.range (fun X' : ↥(tupleOf F X) => (⟨X.obj, X'⟩ : PairObj F X.car)) := by
  ext q
  constructor
  · intro hq
    obtain ⟨X₀, X'⟩ := q
    have hq' : X₀ = X.obj := hq
    subst hq'
    exact ⟨X', rfl⟩
  · rintro ⟨X', rfl⟩; rfl

theorem NormalRed.ncard_versions_ofReduction {Ω : Type} {C : Cat.{0, 0} Ω}
    {D : Cat.{0, 0} Ω} {E : TupleClass D} (F : Func C E.cat) (X : Pt C)
    (hfin : (tupleOf F X).Finite) :
    ((NormalRed.ofReduction F).versions X).Finite ∧
      ((NormalRed.ofReduction F).versions X).ncard = (tupleOf F X).ncard := by
  classical
  haveI : Finite ↥(tupleOf F X) := hfin.to_subtype
  have hinj : Function.Injective
      (fun X' : ↥(tupleOf F X) => (⟨X.obj, X'⟩ : PairObj F X.car)) := by
    intro a b hab
    simpa using hab
  rw [NormalRed.versions_ofReduction]
  refine ⟨Set.finite_range _, ?_⟩
  exact (Set.ncard_range_of_injective hinj).trans (Nat.card_coe_set_eq _)

/-- §6.  **Every reduction can be normalized.**  The category of pairs `C^F` of
Definition 6.0.5 already has the two properties: its objects on `s` are pairs `(X, X')`
with `□X = s`, so they are versions of objects of `C` on `s`, and its morphisms are those
morphisms of `C` that `F` maps into `Iso(X',Y')`.  The functor `G` of `FindsAtMultCost` is
then a functor on the category of versions itself. -/
theorem FindsAtMultCost.exists_normal {Ω : Type} {C K : Cat.{0, 0} Ω} {cost : Pt C → ℕ}
    {Good : Pt C → Pt K → Prop} (h : FindsAtMultCost C K cost Good) :
    ∃ (N : NormalRed C) (G : Func N.D K), G.IsCanonicalEmbedding ∧
      (∀ X : Pt C, (N.versions X).Finite ∧ (N.versions X).ncard ≤ cost X) ∧
      (∀ (X : Pt C) (A : N.D.Obj X.car), N.base A = X.obj →
        Good X (G.obj ⟨X.car, A⟩)) := by
  classical
  obtain ⟨D, E, F, G, hGemb, hcost, hgood⟩ := h
  refine ⟨NormalRed.ofReduction F, G, hGemb, fun X => ?_, ?_⟩
  · obtain ⟨hfin, hcard⟩ := NormalRed.ncard_versions_ofReduction F X (hcost X).1
    exact ⟨hfin, hcard ▸ (hcost X).2⟩
  · rintro X ⟨X₀, X'⟩ hbase
    have hbase' : X₀ = X.obj := hbase
    subst hbase'
    exact hgood X X'.1 X'.2

/-! ### Gluing two normalized reductions -/

namespace CaseSplit

variable {Ω : Type} {C K : Cat.{0, 0} Ω} {P : ∀ s : Set Ω, C.Obj s → Prop}
  (Np : NormalRed (C.full P)) (Nn : NormalRed (C.full fun s X => ¬ P s X))

/-- The object of `C` underlying a version from either branch. -/
def base : ∀ {s : Set Ω}, (Cat.sum Np.D Nn.D).Obj s → C.Obj s
  | _, Sum.inl a => (Np.base a).1
  | _, Sum.inr a => (Nn.base a).1

/-- The two branches glued into a single normalized reduction of `C`. -/
def red (hP : ∀ {X Y : Pt C}, (C.IsoP X Y).Nonempty → P X.car X.obj → P Y.car Y.obj) :
    NormalRed C where
  D := Cat.sum Np.D Nn.D
  base := base Np Nn
  iso_base := by
    rintro s t (a | a) (b | b) f hf
    · exact Np.iso_base hf
    · exact absurd hf (Set.notMem_empty f)
    · exact absurd hf (Set.notMem_empty f)
    · exact Nn.iso_base hf
  nonempty := by
    intro X
    by_cases hx : P X.car X.obj
    · obtain ⟨a, ha⟩ := Np.nonempty (⟨X.car, ⟨X.obj, hx⟩⟩ : Pt (C.full P))
      exact ⟨Sum.inl a, by show (Np.base a).1 = X.obj; rw [ha]⟩
    · obtain ⟨a, ha⟩ :=
        Nn.nonempty (⟨X.car, ⟨X.obj, hx⟩⟩ : Pt (C.full fun s X => ¬ P s X))
      exact ⟨Sum.inr a, by show (Nn.base a).1 = X.obj; rw [ha]⟩
  transport := by
    rintro X Y f hf (a | a) hbase
    · have hbase' : (Np.base a).1 = X.obj := hbase
      have hx : P X.car X.obj := hbase' ▸ (Np.base a).2
      have hy : P Y.car Y.obj := hP ⟨f, hf⟩ hx
      have hba : Np.base a = (⟨X.obj, hx⟩ : (C.full P).Obj X.car) := Subtype.ext hbase'
      obtain ⟨b, hb, hfb⟩ :=
        Np.transport (X := ⟨X.car, ⟨X.obj, hx⟩⟩) (Y := ⟨Y.car, ⟨Y.obj, hy⟩⟩) hf a hba
      exact ⟨Sum.inl b, by show (Np.base b).1 = Y.obj; rw [hb], hfb⟩
    · have hbase' : (Nn.base a).1 = X.obj := hbase
      have hx : ¬ P X.car X.obj := hbase' ▸ (Nn.base a).2
      have hy : ¬ P Y.car Y.obj := fun h => hx (hP ⟨f.symm, C.symm_mem hf⟩ h)
      have hba : Nn.base a
          = (⟨X.obj, hx⟩ : (C.full fun s X => ¬ P s X).Obj X.car) := Subtype.ext hbase'
      obtain ⟨b, hb, hfb⟩ :=
        Nn.transport (X := ⟨X.car, ⟨X.obj, hx⟩⟩) (Y := ⟨Y.car, ⟨Y.obj, hy⟩⟩) hf a hba
      exact ⟨Sum.inr b, by show (Nn.base b).1 = Y.obj; rw [hb], hfb⟩

/-- The two branches' output functors glued into one. -/
def found (Gp : Func Np.D K) (Gn : Func Nn.D K) : Func (Cat.sum Np.D Nn.D) K where
  obj p :=
    match p with
    | ⟨s, Sum.inl a⟩ => Gp.obj ⟨s, a⟩
    | ⟨s, Sum.inr a⟩ => Gn.obj ⟨s, a⟩
  map {p q} f :=
    match p, q, f with
    | ⟨_, Sum.inl _⟩, ⟨_, Sum.inl _⟩, f => Gp.map ⟨f.1, f.2⟩
    | ⟨_, Sum.inl _⟩, ⟨_, Sum.inr _⟩, f => absurd f.2 (Set.notMem_empty f.1)
    | ⟨_, Sum.inr _⟩, ⟨_, Sum.inl _⟩, f => absurd f.2 (Set.notMem_empty f.1)
    | ⟨_, Sum.inr _⟩, ⟨_, Sum.inr _⟩, f => Gn.map ⟨f.1, f.2⟩
  map_id := by
    rintro ⟨s, (a | a)⟩
    · exact Gp.map_id ⟨s, a⟩
    · exact Gn.map_id ⟨s, a⟩
  map_trans := by
    rintro ⟨s, (a | a)⟩ ⟨t, (b | b)⟩ ⟨r, (c | c)⟩ f g
    · exact Gp.map_trans (⟨f.1, f.2⟩ : Hom Np.D ⟨s, a⟩ ⟨t, b⟩)
        (⟨g.1, g.2⟩ : Hom Np.D ⟨t, b⟩ ⟨r, c⟩)
    · exact absurd g.2 (Set.notMem_empty g.1)
    · exact absurd f.2 (Set.notMem_empty f.1)
    · exact absurd f.2 (Set.notMem_empty f.1)
    · exact absurd f.2 (Set.notMem_empty f.1)
    · exact absurd f.2 (Set.notMem_empty f.1)
    · exact absurd g.2 (Set.notMem_empty g.1)
    · exact Gn.map_trans (⟨f.1, f.2⟩ : Hom Nn.D ⟨s, a⟩ ⟨t, b⟩)
        (⟨g.1, g.2⟩ : Hom Nn.D ⟨t, b⟩ ⟨r, c⟩)

theorem found_isCanonicalEmbedding {Gp : Func Np.D K} {Gn : Func Nn.D K}
    (hGp : Gp.IsCanonicalEmbedding) (hGn : Gn.IsCanonicalEmbedding) :
    (found Np Nn Gp Gn).IsCanonicalEmbedding := by
  constructor
  case car_subset =>
    rintro ⟨s, (a | a)⟩
    · exact hGp.car_subset ⟨s, a⟩
    · exact hGn.car_subset ⟨s, a⟩
  case map_restrict =>
    rintro ⟨s, (a | a)⟩ ⟨t, (b | b)⟩ f x
    · exact hGp.map_restrict (⟨f.1, f.2⟩ : Hom Np.D ⟨s, a⟩ ⟨t, b⟩) x
    · exact absurd f.2 (Set.notMem_empty f.1)
    · exact absurd f.2 (Set.notMem_empty f.1)
    · exact hGn.map_restrict (⟨f.1, f.2⟩ : Hom Nn.D ⟨s, a⟩ ⟨t, b⟩) x

/-- The versions of `X` in the glued reduction are those of the branch `X` belongs to. -/
theorem versions_red
    (hP : ∀ {X Y : Pt C}, (C.IsoP X Y).Nonempty → P X.car X.obj → P Y.car Y.obj)
    (X : Pt C) :
    (∃ hx : P X.car X.obj,
        (red Np Nn hP).versions X = Sum.inl '' Np.versions ⟨X.car, ⟨X.obj, hx⟩⟩) ∨
      (∃ hx : ¬ P X.car X.obj,
        (red Np Nn hP).versions X = Sum.inr '' Nn.versions ⟨X.car, ⟨X.obj, hx⟩⟩) := by
  classical
  by_cases hx : P X.car X.obj
  · refine Or.inl ⟨hx, ?_⟩
    ext (a | a)
    · constructor
      · intro h
        exact ⟨a, Subtype.ext (show (Np.base a).1 = X.obj from h), rfl⟩
      · rintro ⟨b, hb, hab⟩
        cases hab
        exact congrArg Subtype.val hb
    · constructor
      · intro h
        exact absurd ((show (Nn.base a).1 = X.obj from h) ▸ (Nn.base a).2) (not_not.2 hx)
      · rintro ⟨b, hb, hab⟩; exact absurd hab (by simp)
  · refine Or.inr ⟨hx, ?_⟩
    ext (a | a)
    · constructor
      · intro h
        exact absurd ((show (Np.base a).1 = X.obj from h) ▸ (Np.base a).2) hx
      · rintro ⟨b, hb, hab⟩; exact absurd hab (by simp)
    · constructor
      · intro h
        exact ⟨a, Subtype.ext (show (Nn.base a).1 = X.obj from h), rfl⟩
      · rintro ⟨b, hb, hab⟩
        cases hab
        exact congrArg Subtype.val hb

end CaseSplit

/-- §6.  **A canonical case distinction.**  Let `P` be a property of the objects of `C`
that is invariant under isomorphism.  If the full subcategory of the objects satisfying `P`
and the full subcategory of those not satisfying it each admit a reduction finding an
object with the *same* property `Good`, then `C` does, at the larger of the two costs.

The proof normalizes the two reductions (`FindsAtMultCost.exists_normal`), so that their
tuples live on `□X`, and glues them: the category of versions of the glued reduction is the
disjoint union of the two categories of versions, and the version of `X` decides which
branch `X` is in.  (The two branches must land in the same output category `K`; in §9 this
is the category of "a colored partition or a Johnson scheme".) -/
theorem FindsAtMultCost.cases {Ω : Type} {C K : Cat.{0, 0} Ω}
    {P : ∀ s : Set Ω, C.Obj s → Prop}
    (hP : ∀ {X Y : Pt C}, (C.IsoP X Y).Nonempty → P X.car X.obj → P Y.car Y.obj)
    {costp costn : Pt C → ℕ} {Good : Pt C → Pt K → Prop}
    (hpos : FindsAtMultCost (C.full P) K (fun X => costp ⟨X.car, X.obj.1⟩)
      (fun X Z => Good ⟨X.car, X.obj.1⟩ Z))
    (hneg : FindsAtMultCost (C.full fun s X => ¬ P s X) K (fun X => costn ⟨X.car, X.obj.1⟩)
      (fun X Z => Good ⟨X.car, X.obj.1⟩ Z)) :
    FindsAtMultCost C K (fun X => max (costp X) (costn X)) Good := by
  classical
  obtain ⟨Np, Gp, hGp, hcp, hgp⟩ := hpos.exists_normal
  obtain ⟨Nn, Gn, hGn, hcn, hgn⟩ := hneg.exists_normal
  refine FindsAtMultCost.of_normal (CaseSplit.red Np Nn hP)
    (CaseSplit.found Np Nn Gp Gn)
    (CaseSplit.found_isCanonicalEmbedding Np Nn hGp hGn) (fun X => ?_) ?_
  · rcases CaseSplit.versions_red Np Nn hP X with ⟨hx, hv⟩ | ⟨hx, hv⟩
    · rw [hv]
      have hcard := Set.ncard_image_of_injective
        (f := (Sum.inl : Np.D.Obj X.car → Np.D.Obj X.car ⊕ Nn.D.Obj X.car))
        (Np.versions (⟨X.car, ⟨X.obj, hx⟩⟩ : Pt (C.full P))) Sum.inl_injective
      exact ⟨(hcp _).1.image _, hcard.trans_le (le_trans (hcp _).2 (le_max_left _ _))⟩
    · rw [hv]
      have hcard := Set.ncard_image_of_injective
        (f := (Sum.inr : Nn.D.Obj X.car → Np.D.Obj X.car ⊕ Nn.D.Obj X.car))
        (Nn.versions (⟨X.car, ⟨X.obj, hx⟩⟩ : Pt (C.full fun s X => ¬ P s X)))
        Sum.inr_injective
      exact ⟨(hcn _).1.image _, hcard.trans_le (le_trans (hcn _).2 (le_max_right _ _))⟩
  · rintro X (a | a) hbase
    · have hbase' : (Np.base a).1 = X.obj := hbase
      have hx : P X.car X.obj := hbase' ▸ (Np.base a).2
      exact hgp (⟨X.car, ⟨X.obj, hx⟩⟩ : Pt (C.full P)) a (Subtype.ext hbase')
    · have hbase' : (Nn.base a).1 = X.obj := hbase
      have hx : ¬ P X.car X.obj := hbase' ▸ (Nn.base a).2
      exact hgn (⟨X.car, ⟨X.obj, hx⟩⟩ : Pt (C.full fun s X => ¬ P s X)) a
        (Subtype.ext hbase')

end Babai
