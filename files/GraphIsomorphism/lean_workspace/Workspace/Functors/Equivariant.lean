/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 6: two introduction rules for "at a multiplicative cost of `s` we can find a
canonical …".
-/
import Workspace.Functors.Compose

/-!
# §6 Two ways to produce a reduction at a multiplicative cost

`Babai.FindsAtMultCost` (Definitions 6.0.3, 6.0.5, 6.0.7) is stated in terms of a category
`E` of tuples, a reduction functor `F : C → E` and a functor `G` on the category of pairs
`C^F`.  Building those three by hand for every step of §8 and §9 is what made the steps
hard to state.  This file proves the two introduction rules that every step of §9 actually
uses.

## (a) From an equivariant family of outcomes

Definition 6.0.1 read elementwise.  Suppose that to every object `X ∈ C` we attach a
non-empty finite set `Out(X)` of objects of `K` **on the same underlying set** `□X`, in
such a way that

> for `f ∈ Iso(X,Y)` and `Z ∈ Out(X)` there is `Z' ∈ Out(Y)` with `f ∈ Iso(Z,Z')`,

which is exactly condition (ii) of Definition 6.0.1 for the family of tuples
`{(X,Z) | Z ∈ Out(X)}`, and that every `Z ∈ Out(X)` has the desired property.  Then *"at a
multiplicative cost of `|Out(X)|` we can find a canonical `Z`"*
(`Babai.FindsAtMultCost.of_outcomes`).

The category `D` of Definition 6.0.1 is the category `Babai.outCat` of pairs `(X,Z)` with
`Z ∈ Out(X)`, whose morphisms are the bijections that are morphisms of `C` **and** of `K`;
the functor found is the projection `(X,Z) ↦ Z`, which is a canonical embedding because it
is the identity on underlying sets and on maps.  This is the paper's own example of §6
("for those `~u` for which the procedure does not work, we embed the empty UPCC"): the
tuple of `X` is the set of all outcomes, and *every* member of it must be a solution,
which is the last hypothesis.

## (b) Dependent composition: the second step sees the first step's input

§6, after Prop. 6.0.4, chains two reductions and multiplies their costs; this is
`Babai.FindsAtMultCost.comp`.  In §9 the second step usually has to look at the **original
input** as well as at the object the first step produced — the last step of Lemma 9.3.1
transfers a solution for the bipartite graph `X̄` back to a solution for the UPCC `X`, and
that transfer is a construction out of the pair `(X, solution for X̄)`.

`Babai.PairCatOf C H Good₁` is the category of such pairs: an object of `C` on `□X`
together with an object of `H` on a **subset** of `□X` (that is where a canonical
embedding puts it) satisfying `Good₁`, with the morphisms that are morphisms of both.
`Babai.FindsAtMultCost.toPair` says that a reduction finding `Good₁` is a reduction finding
a pair, and `Babai.FindsAtMultCost.comp_dep` is then `Babai.FindsAtMultCost.comp` applied
to it.

## Numbering map

| Paper | Lean |
|---|---|
| Definition 6.0.1 for a family of outcomes on `□X` | `Babai.outCat`, `Babai.NormalRed.ofOutcomes` |
| "at a multiplicative cost of `|Out(X)|` we can find a canonical …" | `Babai.FindsAtMultCost.of_outcomes` |
| the category of pairs (input, object found) | `Babai.PairCatOf` |
| "…, then, at a multiplicative cost of `b`, from the input **and** the object found …" | `Babai.FindsAtMultCost.comp_dep` |
| an object of `K` on a subset of `□X`, as a canonical embedding produces it | `Babai.Cat.sub`, `Babai.Cat.subProj`, `Babai.FindsAtMultCost.of_outcomes_sub` |
| applying a result of §9 to an object canonically embedded in the input | `Babai.FindsAtMultCost.precomp` |
-/

namespace Babai

variable {Ω : Type}

/-! ### (a) An equivariant family of outcomes -/

/-- Definition 6.0.1 for a family of outcomes living on the underlying set of the input:
the category `D` whose objects on `s` are the pairs `(X, Z)` with `X` an object of `C` on
`s` and `Z ∈ Out(X)` an object of `K` on `s`, and whose morphisms are the bijections that
are morphisms of `C` and morphisms of `K` at the same time.

This is the category of *versions* of the objects of `C`: the version `(X,Z)` remembers
which outcome was chosen, and `□(X,Z) = □X`. -/
def outCat (C K : Cat.{0, 0} Ω) (Out : ∀ X : Pt C, Set (K.Obj X.car)) : Cat.{0, 0} Ω where
  Obj s := {p : C.Obj s × K.Obj s // p.2 ∈ Out ⟨s, p.1⟩}
  Iso p q := {f | f ∈ C.Iso p.1.1 q.1.1 ∧ f ∈ K.Iso p.1.2 q.1.2}
  refl_mem p := ⟨C.refl_mem _, K.refl_mem _⟩
  symm_mem hf := ⟨C.symm_mem hf.1, K.symm_mem hf.2⟩
  trans_mem hf hg := ⟨C.trans_mem hf.1 hg.1, K.trans_mem hf.2 hg.2⟩
  faithful hid := Subtype.ext (Prod.ext (C.faithful hid.1) (K.faithful hid.2))

/-- Definition 6.0.1 for an equivariant family of outcomes, in normal form
(`Babai.NormalRed`): the versions of `X` are the pairs `(X,Z)` with `Z ∈ Out(X)`.

The hypothesis `hequiv` is condition (ii) of Definition 6.0.1: *"if `X, X' ∈ 𝒳 ∈ E` and
`Y ∈ 𝒴 ∈ E` and `f ∈ Iso(X,Y)` then there exists `Y' ∈ 𝒴` such that `f ∈ Iso(X',Y')`"*. -/
def NormalRed.ofOutcomes {C K : Cat.{0, 0} Ω} (Out : ∀ X : Pt C, Set (K.Obj X.car))
    (hne : ∀ X : Pt C, (Out X).Nonempty)
    (hequiv : ∀ {X Y : Pt C} {f : ↥X.car ≃ ↥Y.car}, f ∈ C.IsoP X Y →
      ∀ Z ∈ Out X, ∃ Z' ∈ Out Y, f ∈ K.Iso Z Z') :
    NormalRed C where
  D := outCat C K Out
  base p := p.1.1
  iso_base hf := hf.1
  nonempty X := ⟨⟨(X.obj, (hne X).choose), (hne X).choose_spec⟩, rfl⟩
  transport := by
    rintro X Y f hf ⟨⟨A, Z⟩, hZ⟩ hbase
    have hbase' : A = X.obj := hbase
    subst hbase'
    obtain ⟨Z', hZ', hfZ⟩ := hequiv hf Z hZ
    exact ⟨⟨(Y.obj, Z'), hZ'⟩, rfl, hf, hfZ⟩

/-- The versions of `X` are in bijection with the outcomes `Out(X)`. -/
theorem NormalRed.versions_ofOutcomes {C K : Cat.{0, 0} Ω}
    (Out : ∀ X : Pt C, Set (K.Obj X.car)) (hne : ∀ X : Pt C, (Out X).Nonempty)
    (hequiv : ∀ {X Y : Pt C} {f : ↥X.car ≃ ↥Y.car}, f ∈ C.IsoP X Y →
      ∀ Z ∈ Out X, ∃ Z' ∈ Out Y, f ∈ K.Iso Z Z') (X : Pt C) :
    (NormalRed.ofOutcomes Out hne hequiv).versions X
      = Set.range (fun Z : ↥(Out X) =>
          (⟨(X.obj, Z.1), Z.2⟩ : (outCat C K Out).Obj X.car)) := by
  ext A
  constructor
  · intro hA
    obtain ⟨⟨B, Z⟩, hZ⟩ := A
    have hB : B = X.obj := hA
    subst hB
    exact ⟨⟨Z, hZ⟩, rfl⟩
  · rintro ⟨Z, rfl⟩; rfl

/-- The identity functor. -/
def Func.id (C : Cat.{0, 0} Ω) : Func C C where
  obj X := X
  map f := f
  map_id _ := rfl
  map_trans _ _ := rfl

theorem Func.id_isCanonicalEmbedding (C : Cat.{0, 0} Ω) :
    (Func.id C).IsCanonicalEmbedding :=
  ⟨fun _ => subset_rfl, fun _ _ => rfl⟩

/-- §6.  **From an equivariant family of outcomes, followed by a canonical embedding.**
Suppose that to every object `X` of `C` we attach a non-empty finite set `Out(X)` of at
most `cost X` objects of `K₀` on `□X`, equivariantly (condition (ii) of
Definition 6.0.1), and that the canonical embedding `G` carries every member of `Out(X)`
to an object with the required property.  Then *"at a multiplicative cost of `cost X` we
can find a canonical object with property `Good`"*.

The category of tuples is the one of `Babai.NormalRed.ofOutcomes`, and the functor found is
the projection `(X,Z) ↦ Z` — a canonical embedding onto `□X` — followed by `G`.  The extra
functor `G` is what lets the object found live on a *subset* of `□X`, as §6 allows and as
every step of §9 needs; see `Babai.FindsAtMultCost.of_outcomes_sub`. -/
theorem FindsAtMultCost.of_outcomes_emb {C K₀ K : Cat.{0, 0} Ω} {cost : Pt C → ℕ}
    {Good : Pt C → Pt K → Prop} (Out : ∀ X : Pt C, Set (K₀.Obj X.car))
    (G : Func K₀ K) (hG : G.IsCanonicalEmbedding)
    (hne : ∀ X : Pt C, (Out X).Nonempty)
    (hfin : ∀ X : Pt C, (Out X).Finite)
    (hcost : ∀ X : Pt C, (Out X).ncard ≤ cost X)
    (hequiv : ∀ {X Y : Pt C} {f : ↥X.car ≃ ↥Y.car}, f ∈ C.IsoP X Y →
      ∀ Z ∈ Out X, ∃ Z' ∈ Out Y, f ∈ K₀.Iso Z Z')
    (hgood : ∀ (X : Pt C), ∀ Z ∈ Out X, Good X (G.obj ⟨X.car, Z⟩)) :
    FindsAtMultCost C K cost Good := by
  classical
  set N := NormalRed.ofOutcomes Out hne hequiv with hN
  refine FindsAtMultCost.of_normal N
    (Func.comp
      { obj := fun p => ⟨p.car, p.obj.1.2⟩
        map := fun f => ⟨f.1, f.2.2⟩
        map_id := fun _ => Subtype.ext rfl
        map_trans := fun _ _ => Subtype.ext rfl } G)
    (Func.IsCanonicalEmbedding.comp ⟨fun _ => subset_rfl, fun _ _ => rfl⟩ hG)
    (fun X => ?_) (fun X A hA => ?_)
  · have hinj : Function.Injective
        (fun Z : ↥(Out X) => (⟨(X.obj, Z.1), Z.2⟩ : (outCat C K₀ Out).Obj X.car)) := by
      intro a b hab
      exact Subtype.ext (congrArg (fun q : (outCat C K₀ Out).Obj X.car => q.1.2) hab)
    haveI : Finite ↥(Out X) := (hfin X).to_subtype
    rw [hN, NormalRed.versions_ofOutcomes]
    refine ⟨Set.finite_range _, ?_⟩
    exact ((Set.ncard_range_of_injective hinj).trans
      (Nat.card_coe_set_eq _)).trans_le (hcost X)
  · obtain ⟨⟨B, Z⟩, hZ⟩ := A
    have hB : B = X.obj := hA
    subst hB
    exact hgood X Z hZ

/-- §6.  **From an equivariant family of outcomes.**  The case of
`Babai.FindsAtMultCost.of_outcomes_emb` in which the outcomes are already objects of the
target category, on `□X` itself. -/
theorem FindsAtMultCost.of_outcomes {C K : Cat.{0, 0} Ω} {cost : Pt C → ℕ}
    {Good : Pt C → Pt K → Prop} (Out : ∀ X : Pt C, Set (K.Obj X.car))
    (hne : ∀ X : Pt C, (Out X).Nonempty)
    (hfin : ∀ X : Pt C, (Out X).Finite)
    (hcost : ∀ X : Pt C, (Out X).ncard ≤ cost X)
    (hequiv : ∀ {X Y : Pt C} {f : ↥X.car ≃ ↥Y.car}, f ∈ C.IsoP X Y →
      ∀ Z ∈ Out X, ∃ Z' ∈ Out Y, f ∈ K.Iso Z Z')
    (hgood : ∀ (X : Pt C), ∀ Z ∈ Out X, Good X ⟨X.car, Z⟩) :
    FindsAtMultCost C K cost Good :=
  FindsAtMultCost.of_outcomes_emb Out (Func.id K) (Func.id_isCanonicalEmbedding K)
    hne hfin hcost hequiv hgood

/-! ### Objects living on a subset of `□X` -/

/-- §6.  The category whose objects on `s` are the objects of `K` on a **subset** of `s`,
with the bijections of `s` that carry one subset onto the other by a morphism of `K`.

A canonical embedding satisfies `□(F(X)) ⊆ □(X)` with `□(F(X))` varying with `X`, so this
is the category in which an outcome of a step of §9 lives when it is an object on a subset
of the input's vertex set (the bipartite graph `X̄` of Lemma 9.3.1, the Johnson scheme of
Theorems 9.2.1–9.2.3).  The projection `Babai.Cat.subProj` back to `K` is a canonical
embedding, which is what makes `Babai.FindsAtMultCost.of_outcomes_sub` a special case of
`Babai.FindsAtMultCost.of_outcomes_emb`. -/
def Cat.sub (K : Cat.{0, 0} Ω) : Cat.{0, 0} Ω where
  Obj s := Σ' t : {t : Set Ω // t ⊆ s}, K.Obj t.1
  Iso p q :=
    {f | ∃ g : ↥p.1.1 ≃ ↥q.1.1,
      (∀ x : ↥p.1.1, ((g x : Ω)) = ((f ⟨(x : Ω), p.1.2 x.2⟩ : Ω))) ∧ g ∈ K.Iso p.2 q.2}
  refl_mem p := ⟨Equiv.refl _, fun _ => rfl, K.refl_mem _⟩
  symm_mem := by
    rintro s t p q f ⟨g, hg, hH⟩
    refine ⟨g.symm, fun y => ?_, K.symm_mem hH⟩
    have h1 : ((g (g.symm y) : Ω)) = ((f ⟨(g.symm y : Ω), p.1.2 (g.symm y).2⟩ : Ω)) := hg _
    rw [Equiv.apply_symm_apply] at h1
    have h2 : f ⟨(g.symm y : Ω), p.1.2 (g.symm y).2⟩ = ⟨(y : Ω), q.1.2 y.2⟩ :=
      Subtype.ext h1.symm
    have h3 := congrArg f.symm h2
    rw [Equiv.symm_apply_apply] at h3
    exact congrArg Subtype.val h3
  trans_mem := by
    rintro s t r p q z f g ⟨g₁, hg₁, hH₁⟩ ⟨g₂, hg₂, hH₂⟩
    refine ⟨g₁.trans g₂, fun x => ?_, K.trans_mem hH₁ hH₂⟩
    have h1 : ((g₂ (g₁ x) : Ω)) = ((g ⟨(g₁ x : Ω), q.1.2 (g₁ x).2⟩ : Ω)) := hg₂ _
    have h2 : (g₁ x : Ω) = ((f ⟨(x : Ω), p.1.2 x.2⟩ : Ω)) := hg₁ x
    have h3 : (⟨(g₁ x : Ω), q.1.2 (g₁ x).2⟩ : ↥t) = f ⟨(x : Ω), p.1.2 x.2⟩ := Subtype.ext h2
    rw [Equiv.trans_apply, h1, h3, Equiv.trans_apply]
  faithful := by
    rintro s ⟨t, Y⟩ ⟨t', Y'⟩ ⟨g, hg, hH⟩
    simp only at hg hH
    have hgval : ∀ x : ↥t.1, ((g x : Ω)) = ((x : Ω)) := by
      intro x; simpa using hg x
    have htt : t.1 = t'.1 := by
      ext x
      constructor
      · intro hx
        have := (g ⟨x, hx⟩).2
        rwa [hgval ⟨x, hx⟩] at this
      · intro hx
        have h1 := hgval (g.symm ⟨x, hx⟩)
        rw [Equiv.apply_symm_apply] at h1
        have := (g.symm ⟨x, hx⟩).2
        rwa [← h1] at this
    obtain ⟨t, ht⟩ := t
    obtain ⟨t', ht'⟩ := t'
    simp only at htt
    subst htt
    have hgid : g = Equiv.refl _ := Equiv.ext fun x => Subtype.ext (hgval x)
    subst hgid
    have : Y = Y' := K.faithful hH
    subst this
    rfl

namespace Cat

variable {K : Cat.{0, 0} Ω}

open scoped Classical in
/-- The morphism of `K` underlying a morphism of `Babai.Cat.sub K`.  It is unique
(`subMap_unique`), so it is a well-defined function of the morphism. -/
noncomputable def subMap {p q : Pt (Cat.sub K)} (f : Hom (Cat.sub K) p q) :
    ↥p.obj.1.1 ≃ ↥q.obj.1.1 := f.2.choose

theorem subMap_spec {p q : Pt (Cat.sub K)} (f : Hom (Cat.sub K) p q) (x : ↥p.obj.1.1) :
    ((subMap f x : Ω)) = ((f.1 ⟨(x : Ω), p.obj.1.2 x.2⟩ : Ω)) := f.2.choose_spec.1 x

theorem subMap_mem {p q : Pt (Cat.sub K)} (f : Hom (Cat.sub K) p q) :
    subMap f ∈ K.Iso p.obj.2 q.obj.2 := f.2.choose_spec.2

/-- The morphism of `K` underlying a morphism of `Babai.Cat.sub K` is unique: it is
determined pointwise by the underlying bijection of the ambient sets. -/
theorem subMap_eq {p q : Pt (Cat.sub K)} (f : Hom (Cat.sub K) p q)
    (g : ↥p.obj.1.1 ≃ ↥q.obj.1.1)
    (hg : ∀ x : ↥p.obj.1.1, ((g x : Ω)) = ((f.1 ⟨(x : Ω), p.obj.1.2 x.2⟩ : Ω))) :
    subMap f = g :=
  Equiv.ext fun x => Subtype.ext ((subMap_spec f x).trans (hg x).symm)

/-- §6.  The projection of `Babai.Cat.sub K` to `K`: it forgets the ambient set and is a
canonical embedding, since `□(F(p)) ⊆ □p` and `F(f)` is the restriction of `f`. -/
noncomputable def subProj (K : Cat.{0, 0} Ω) : Func (Cat.sub K) K where
  obj p := ⟨p.obj.1.1, p.obj.2⟩
  map f := ⟨subMap f, subMap_mem f⟩
  map_id p := Subtype.ext (subMap_eq _ _ fun _ => rfl)
  map_trans := fun {p q _} f g => Subtype.ext (subMap_eq _ _ fun x => by
    have h1 := subMap_spec g (subMap f x)
    have h2 : (⟨((subMap f x : Ω)), q.obj.1.2 (subMap f x).2⟩ : ↥q.car)
        = f.1 ⟨(x : Ω), p.obj.1.2 x.2⟩ := Subtype.ext (subMap_spec f x)
    show ((subMap g (subMap f x) : Ω)) = _
    rw [h1, h2]
    rfl)

theorem subProj_isCanonicalEmbedding (K : Cat.{0, 0} Ω) :
    (subProj K).IsCanonicalEmbedding where
  car_subset p := p.obj.1.2
  map_restrict f x := subMap_spec f x

end Cat

/-- §6.  **From an equivariant family of outcomes on subsets of `□X`.**  The form of
`Babai.FindsAtMultCost.of_outcomes` in which each outcome is an object of `K` on a subset
of `□X`, which is what a canonical embedding produces and what every step of §9 returns. -/
theorem FindsAtMultCost.of_outcomes_sub {C K : Cat.{0, 0} Ω} {cost : Pt C → ℕ}
    {Good : Pt C → Pt K → Prop} (Out : ∀ X : Pt C, Set ((Cat.sub K).Obj X.car))
    (hne : ∀ X : Pt C, (Out X).Nonempty)
    (hfin : ∀ X : Pt C, (Out X).Finite)
    (hcost : ∀ X : Pt C, (Out X).ncard ≤ cost X)
    (hequiv : ∀ {X Y : Pt C} {f : ↥X.car ≃ ↥Y.car}, f ∈ C.IsoP X Y →
      ∀ Z ∈ Out X, ∃ Z' ∈ Out Y, f ∈ (Cat.sub K).Iso Z Z')
    (hgood : ∀ (X : Pt C), ∀ Z ∈ Out X, Good X ⟨Z.1.1, Z.2⟩) :
    FindsAtMultCost C K cost Good :=
  FindsAtMultCost.of_outcomes_emb Out (Cat.subProj K) (Cat.subProj_isCanonicalEmbedding K)
    hne hfin hcost hequiv hgood

/-! ### Pulling a reduction back along a canonical embedding -/

/-- The category of pairs of a reduction that has been precomposed with a functor `Φ`: a
pair `(X, X')` of `C^{Φ∘F}` is the pair `(Φ(X), X')` of `D^F`.  (For `Φ` the functor found
by a first reduction this is `Babai.Compose.psi`.) -/
def Func.pairPrecomp {C D D₀ : Cat.{0, 0} Ω} {E : TupleClass D₀} (Φ : Func C D)
    (F : Func D E.cat) : Func (pairCat (Φ.comp F)) (pairCat F) where
  obj p := ⟨(Φ.obj ⟨p.car, p.obj.1⟩).car, ⟨(Φ.obj ⟨p.car, p.obj.1⟩).obj, p.obj.2⟩⟩
  map {p q} f := ⟨(Φ.map (⟨f.1, f.2.1⟩ : Hom C ⟨p.car, p.obj.1⟩ ⟨q.car, q.obj.1⟩)).1,
    ⟨(Φ.map _).2, f.2.2⟩⟩
  map_id p := by
    refine Hom.ext fun x => ?_
    have h : (Φ.map (Hom.id (⟨p.car, p.obj.1⟩ : Pt C))) x = x := by rw [Φ.map_id]; rfl
    exact h
  map_trans {p q r} f g := by
    refine Hom.ext fun x => ?_
    have h : (Φ.map (Hom.trans
          (⟨f.1, f.2.1⟩ : Hom C ⟨p.car, p.obj.1⟩ ⟨q.car, q.obj.1⟩)
          (⟨g.1, g.2.1⟩ : Hom C ⟨q.car, q.obj.1⟩ ⟨r.car, r.obj.1⟩))) x
        = (Φ.map (⟨g.1, g.2.1⟩ : Hom C ⟨q.car, q.obj.1⟩ ⟨r.car, r.obj.1⟩))
            ((Φ.map (⟨f.1, f.2.1⟩ : Hom C ⟨p.car, p.obj.1⟩ ⟨q.car, q.obj.1⟩)) x) := by
      rw [Φ.map_trans]; rfl
    exact h

theorem Func.pairPrecomp_isCanonicalEmbedding {C D D₀ : Cat.{0, 0} Ω} {E : TupleClass D₀}
    {Φ : Func C D} (hΦ : Φ.IsCanonicalEmbedding) (F : Func D E.cat) :
    (Φ.pairPrecomp F).IsCanonicalEmbedding where
  car_subset p := hΦ.car_subset ⟨p.car, p.obj.1⟩
  map_restrict f x := hΦ.map_restrict _ x

/-- §6.  **Pulling a reduction back along a canonical embedding.**  If `Φ : C → D` is a
canonical embedding and *"at a multiplicative cost of `c` we can find a canonical object
with property `Good`"* for the objects of `D`, then the same holds for the objects of `C`,
at the cost `c(Φ(X))` and for the property `Good(Φ(X), ·)`.

This is what every application of one result of §9 to an object *constructed inside*
another one needs: Theorem 9.2.2 is stated for the category `BipInputs Ω`, while Lemma
9.3.1 applies it to the bipartite graph `X̄` that it has canonically embedded in the UPCC,
i.e. to the image of a canonical embedding of the category of inputs of Theorem 9.2.1. -/
theorem FindsAtMultCost.precomp {C D K : Cat.{0, 0} Ω} {c : Pt D → ℕ}
    {Good : Pt D → Pt K → Prop} (Φ : Func C D) (hΦ : Φ.IsCanonicalEmbedding)
    (h : FindsAtMultCost D K c Good) :
    FindsAtMultCost C K (fun X => c (Φ.obj X)) (fun X Z => Good (Φ.obj X) Z) := by
  obtain ⟨D₀, E, F, G, hGemb, hcost, hgood⟩ := h
  exact ⟨D₀, E, Φ.comp F, (Φ.pairPrecomp F).comp G,
    (Func.pairPrecomp_isCanonicalEmbedding hΦ F).comp hGemb,
    fun X => hcost (Φ.obj X), fun X X' hX' => hgood (Φ.obj X) X' hX'⟩

/-! ### (b) The category of pairs (input, object found) -/

/-- The objects of `Babai.PairCatOf`: an object `X` of `C` on `s`, together with an object
`Y` of `H` on a subset of `s` with `Good X Y`.

The subset is there because a canonical embedding puts the object it finds on a *subset* of
`□X` (§6), so the pair `(X, Y)` cannot be a pair of objects on one and the same set. -/
structure PairObjOf (C H : Cat.{0, 0} Ω) (Good : Pt C → Pt H → Prop) (s : Set Ω) where
  /-- The object of `C`: the input. -/
  base : C.Obj s
  /-- The underlying set of the object found. -/
  sub : Set Ω
  /-- §6: a canonical embedding satisfies `□(F(X)) ⊆ □(X)`. -/
  sub_subset : sub ⊆ s
  /-- The object of `H`: the object found. -/
  snd : H.Obj sub
  /-- The property that the first step guarantees. -/
  good : Good ⟨s, base⟩ ⟨sub, snd⟩

/-- §6.  The category of pairs *(input, object found)*.  A morphism `(X,Y) → (X',Y')` is a
bijection `□X → □X'` that is a morphism `X → X'` of `C` and carries `□Y` onto `□Y'` by a
morphism `Y → Y'` of `H`.

This is the category on which the *second* step of a chain of canonical reductions lives
when it has to see the original input as well as the object the first step produced. -/
def PairCatOf (C H : Cat.{0, 0} Ω) (Good : Pt C → Pt H → Prop) : Cat.{0, 0} Ω where
  Obj s := PairObjOf C H Good s
  Iso p q :=
    {f | f ∈ C.Iso p.base q.base ∧ ∃ g : ↥p.sub ≃ ↥q.sub,
      (∀ x : ↥p.sub, ((g x : Ω)) = ((f ⟨(x : Ω), p.sub_subset x.2⟩ : Ω))) ∧
        g ∈ H.Iso p.snd q.snd}
  refl_mem p := ⟨C.refl_mem _, Equiv.refl _, fun _ => rfl, H.refl_mem _⟩
  symm_mem := by
    rintro s t p q f ⟨hC, g, hg, hH⟩
    refine ⟨C.symm_mem hC, g.symm, fun y => ?_, H.symm_mem hH⟩
    have h1 : ((g (g.symm y) : Ω)) = ((f ⟨(g.symm y : Ω), p.sub_subset (g.symm y).2⟩ : Ω)) :=
      hg _
    rw [Equiv.apply_symm_apply] at h1
    have h2 : f ⟨(g.symm y : Ω), p.sub_subset (g.symm y).2⟩
        = ⟨(y : Ω), q.sub_subset y.2⟩ := Subtype.ext h1.symm
    have h3 := congrArg f.symm h2
    rw [Equiv.symm_apply_apply] at h3
    exact congrArg Subtype.val h3
  trans_mem := by
    rintro s t r p q z f g ⟨hC₁, g₁, hg₁, hH₁⟩ ⟨hC₂, g₂, hg₂, hH₂⟩
    refine ⟨C.trans_mem hC₁ hC₂, g₁.trans g₂, fun x => ?_, H.trans_mem hH₁ hH₂⟩
    have h1 : ((g₂ (g₁ x) : Ω))
        = ((g ⟨(g₁ x : Ω), q.sub_subset (g₁ x).2⟩ : Ω)) := hg₂ _
    have h2 : (g₁ x : Ω) = ((f ⟨(x : Ω), p.sub_subset x.2⟩ : Ω)) := hg₁ x
    have h3 : (⟨(g₁ x : Ω), q.sub_subset (g₁ x).2⟩ : ↥t)
        = f ⟨(x : Ω), p.sub_subset x.2⟩ := Subtype.ext h2
    rw [Equiv.trans_apply, h1, h3, Equiv.trans_apply]
  faithful := by
    rintro s ⟨b, t, ht, Y, hgood⟩ ⟨b', t', ht', Y', hgood'⟩ ⟨hC, g, hg, hH⟩
    simp only at hC hg hH
    have hb : b = b' := C.faithful hC
    subst hb
    have hgval : ∀ x : ↥t, ((g x : Ω)) = ((x : Ω)) := by
      intro x; simpa using hg x
    have htt : t = t' := by
      ext x
      constructor
      · intro hx
        have := (g ⟨x, hx⟩).2
        rwa [hgval ⟨x, hx⟩] at this
      · intro hx
        have h1 := hgval (g.symm ⟨x, hx⟩)
        rw [Equiv.apply_symm_apply] at h1
        have := (g.symm ⟨x, hx⟩).2
        rwa [← h1] at this
    subst htt
    have hgid : g = Equiv.refl ↥t := Equiv.ext fun x => Subtype.ext (hgval x)
    subst hgid
    have : Y = Y' := H.faithful hH
    subst this
    rfl

/-- The input component of a pair. -/
def pairFst {C H : Cat.{0, 0} Ω} {Good : Pt C → Pt H → Prop}
    (p : Pt (PairCatOf C H Good)) : Pt C := ⟨p.car, p.obj.base⟩

/-- The component found by the first step. -/
def pairSnd {C H : Cat.{0, 0} Ω} {Good : Pt C → Pt H → Prop}
    (p : Pt (PairCatOf C H Good)) : Pt H := ⟨p.obj.sub, p.obj.snd⟩

theorem pairGood {C H : Cat.{0, 0} Ω} {Good : Pt C → Pt H → Prop}
    (p : Pt (PairCatOf C H Good)) : Good (pairFst p) (pairSnd p) := p.obj.good

/-- §6.  A reduction that finds an object with property `Good₁` is a reduction that finds
the **pair** *(input, object found)*: the pair carries no more information, and the
projection to the pair is a canonical embedding onto `□X`. -/
theorem FindsAtMultCost.toPair {C H : Cat.{0, 0} Ω} {c : Pt C → ℕ}
    {Good₁ : Pt C → Pt H → Prop} (h : FindsAtMultCost C H c Good₁) :
    FindsAtMultCost C (PairCatOf C H Good₁) c (fun X p => pairFst p = X) := by
  obtain ⟨D, E, F, G, hGemb, hcost, hgood⟩ := h
  refine ⟨D, E, F,
    { obj := fun q =>
        ⟨q.car, { base := q.obj.1
                  sub := (G.obj q).car
                  sub_subset := hGemb.car_subset q
                  snd := (G.obj q).obj
                  good := hgood ⟨q.car, q.obj.1⟩ q.obj.2.1 q.obj.2.2 }⟩
      map := fun {p q} f =>
        ⟨f.1, f.2.1, (G.map f).1, fun x => hGemb.map_restrict f x, (G.map f).2⟩
      map_id := fun _ => Subtype.ext rfl
      map_trans := fun _ _ => Subtype.ext rfl },
    ⟨fun _ => subset_rfl, fun _ _ => rfl⟩, hcost, fun X X' hX' => rfl⟩

/-- §6 (Def. 6.0.3 and the remarks after Prop. 6.0.4).  **Dependent composition of
reductions.**  If at multiplicative cost `c₁` we can canonically find a `Y` with
`Good₁ X Y`, and from the **pair** `(X,Y)` — so the second step may look at the original
input — at multiplicative cost `c₂` an object `Z` with `Good₂ (X,Y) Z`, then at
multiplicative cost `c₁ X · c₂' X` we can canonically find such a `Z`, provided
`c₂ (X,Y) ≤ c₂' X` for every pair, so that the second cost is expressed in terms of the
input of the first step.

`Babai.FindsAtMultCost.comp` is the special case in which the second step does not look at
`X`; this one is what the last step of Lemma 9.3.1 (transferring a solution for `X̄` back to
a solution for `X`) and every later step of §9 need. -/
theorem FindsAtMultCost.comp_dep {C H K : Cat.{0, 0} Ω} {c₁ : Pt C → ℕ}
    {Good₁ : Pt C → Pt H → Prop} {c₂' : Pt C → ℕ}
    {Good₂ : Pt (PairCatOf C H Good₁) → Pt K → Prop}
    {c₂ : Pt (PairCatOf C H Good₁) → ℕ}
    (h₁ : FindsAtMultCost C H c₁ Good₁)
    (h₂ : FindsAtMultCost (PairCatOf C H Good₁) K c₂ Good₂)
    (hc : ∀ p : Pt (PairCatOf C H Good₁), c₂ p ≤ c₂' (pairFst p)) :
    FindsAtMultCost C K (fun X => c₁ X * c₂' X)
      (fun X Z => ∃ p : Pt (PairCatOf C H Good₁), pairFst p = X ∧ Good₂ p Z) := by
  refine (h₁.toPair.comp h₂ ?_).mono (fun _ => le_rfl) (fun X Z h => h)
  intro X p hp
  exact (hc p).trans_eq (congrArg c₂' hp)

end Babai
