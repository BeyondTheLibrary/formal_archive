/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 6: categories of tuples, reductions at a multiplicative cost.
-/
import Workspace.Functors.Basic
import Mathlib.Data.Set.Card
import Mathlib.Logic.Equiv.Embedding
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Data.Fintype.CardEmbedding

/-!
# §6 Categories of tuples (Definitions 6.0.1–6.0.7)

## Numbering map

| Paper | Lean |
|---|---|
| Definition 6.0.1 | `Babai.TupleClass`, `Babai.TupleClass.cat` |
| Proposition 6.0.2 | `Babai.TupleClass.cat` (its four axioms), `Babai.TupleClass.trans_mem` |
| Definition 6.0.3 | `Babai.IsReductionAtCost` |
| Proposition 6.0.4, Eq. (40) | `Babai.iso_eq_iUnion_preimageIso`, `.preimageIso_disjoint`, `.ncard_preimageIso_eq` |
| Definition 6.0.5 | `Babai.pairCat` |
| Proposition 6.0.6 | `Babai.pairCat` (its four axioms) |
| Definition 6.0.7 | `Babai.IsCanonicallyAssignedRelative` |
| individualization example | `Babai.Individualize` section |

## Encoding notes

Condition (i) of Definition 6.0.1, *"if `X, X' ∈ 𝒳 ∈ E` then `□(X) = □(X')`"*, is
automatic here: in `Babai.Cat` the objects with underlying set `s` form the type
`D.Obj s`, so a set of objects `𝒳 : Set (D.Obj s)` consists of objects with the same
underlying set by construction, and `□(𝒳) = s` is Definition 6.0.1(a).
-/

universe u v v' w

namespace Babai

variable {Ω : Type u}

/-! ### Definition 6.0.1: the category of tuples -/

/-- Definition 6.0.1 (Category of tuples).  *"Let `D` be a category.  Let `E` be a class of
non-empty sets of objects from `D` with the following properties: (i) if `X, X' ∈ 𝒳 ∈ E`
then `□(X) = □(X')`; (ii) if `X, X' ∈ 𝒳 ∈ E` and `Y ∈ 𝒴 ∈ E` and `f ∈ Iso(X,Y)` then there
exists `Y' ∈ 𝒴` such that `f ∈ Iso(X',Y')`."*

Condition (i) is automatic in our encoding (see the module docstring), so `mem s` is the
class of those members of `E` whose common underlying set is `s`. -/
structure TupleClass (D : Cat.{u, v} Ω) where
  /-- The members of `E` with common underlying set `s`. -/
  mem : ∀ s : Set Ω, Set (Set (D.Obj s))
  /-- The members of `E` are non-empty sets of objects. -/
  nonempty : ∀ {s : Set Ω} {𝒳 : Set (D.Obj s)}, 𝒳 ∈ mem s → 𝒳.Nonempty
  /-- Condition (ii). -/
  cond_ii : ∀ {s t : Set Ω} {𝒳 : Set (D.Obj s)} {𝒴 : Set (D.Obj t)},
    𝒳 ∈ mem s → 𝒴 ∈ mem t → ∀ {X X' : D.Obj s} {Y : D.Obj t}, X ∈ 𝒳 → X' ∈ 𝒳 → Y ∈ 𝒴 →
      ∀ {f : ↥s ≃ ↥t}, f ∈ D.Iso X Y → ∃ Y' ∈ 𝒴, f ∈ D.Iso X' Y'

namespace TupleClass

variable {D : Cat.{u, v} Ω} (E : TupleClass D)

/-- Definition 6.0.1(b).  *"For `𝒳, 𝒴 ∈ E`, we set `Iso(𝒳,𝒴) = ⋃ {Iso(X,Y) | X ∈ 𝒳,
Y ∈ 𝒴}`."* -/
def IsoT {s t : Set Ω} (𝒳 : Set (D.Obj s)) (𝒴 : Set (D.Obj t)) : Set (↥s ≃ ↥t) :=
  {f | ∃ X ∈ 𝒳, ∃ Y ∈ 𝒴, f ∈ D.Iso X Y}

/-- Proposition 6.0.2.  *"We need to show that the morphisms in `E` are closed under
composition.  Let `f ∈ Iso(𝒳,𝒴)` and `g ∈ Iso(𝒴,𝒵)`.  We need to show that `fg ∈
Iso(𝒳,𝒵)`.  By definition, there exist objects `X ∈ 𝒳` and `Y ∈ 𝒴` such that
`f ∈ Iso(X,Y)`.  Now `g ∈ Iso(Y',Z')` for some objects `Y' ∈ 𝒴` and `Z' ∈ 𝒵`.  By
assumption (ii) there exists `Z ∈ 𝒵` such that `g ∈ Iso(Y,Z)`.  Therefore
`fg ∈ Iso(X,Z) ⊆ Iso(𝒳,𝒵)`."* -/
theorem trans_mem {s t r : Set Ω} {𝒳 : Set (D.Obj s)} {𝒴 : Set (D.Obj t)}
    {𝒵 : Set (D.Obj r)} (h𝒴 : 𝒴 ∈ E.mem t) (h𝒵 : 𝒵 ∈ E.mem r)
    {f : ↥s ≃ ↥t} {g : ↥t ≃ ↥r} (hf : f ∈ IsoT 𝒳 𝒴) (hg : g ∈ IsoT 𝒴 𝒵) :
    f.trans g ∈ IsoT 𝒳 𝒵 := by
  obtain ⟨X, hX, Y, hY, hfXY⟩ := hf
  obtain ⟨Y', hY', Z', hZ', hgYZ⟩ := hg
  obtain ⟨Z, hZ, hgZ⟩ := E.cond_ii h𝒴 h𝒵 hY' hY hZ' hgYZ
  exact ⟨X, hX, Z, hZ, D.trans_mem hfXY hgZ⟩

/-- Proposition 6.0.2.  *"`E` is a category."*  Note that being a category in the paper's
sense also includes containing the identities, being closed under inverses, and
faithfulness of `□`; the paper's proof addresses the only point that is not immediate. -/
def cat : Cat.{u, v} Ω where
  Obj s := {𝒳 : Set (D.Obj s) // 𝒳 ∈ E.mem s}
  Iso 𝒳 𝒴 := IsoT 𝒳.1 𝒴.1
  refl_mem 𝒳 :=
    ⟨(E.nonempty 𝒳.2).choose, (E.nonempty 𝒳.2).choose_spec,
      (E.nonempty 𝒳.2).choose, (E.nonempty 𝒳.2).choose_spec, D.refl_mem _⟩
  symm_mem := by
    rintro s t 𝒳 𝒴 f ⟨X, hX, Y, hY, hf⟩
    exact ⟨Y, hY, X, hX, D.symm_mem hf⟩
  trans_mem {_ _ _ _ 𝒴 𝒵 _ _} hf hg := E.trans_mem 𝒴.2 𝒵.2 hf hg
  faithful := by
    rintro s 𝒳 𝒴 ⟨X, hX, Y, hY, hf⟩
    have hXY : X = Y := D.faithful hf
    subst hXY
    refine Subtype.ext (Set.Subset.antisymm ?_ ?_)
    · intro X' hX'
      obtain ⟨Y', hY', hid⟩ := E.cond_ii 𝒳.2 𝒴.2 hX hX' hY hf
      exact (D.faithful hid) ▸ hY'
    · intro Y' hY'
      have hback : Equiv.refl ↥s ∈ D.Iso X X := D.refl_mem X
      obtain ⟨X', hX', hid⟩ := E.cond_ii 𝒴.2 𝒳.2 hY hY' hX hback
      exact (D.faithful hid) ▸ hX'

theorem mem_cat_iso {s t : Set Ω} {𝒳 : (E.cat).Obj s} {𝒴 : (E.cat).Obj t}
    {f : ↥s ≃ ↥t} : f ∈ (E.cat).Iso 𝒳 𝒴 ↔ ∃ X ∈ 𝒳.1, ∃ Y ∈ 𝒴.1, f ∈ D.Iso X Y := Iff.rfl

end TupleClass

/-! ### Definition 6.0.3 and Proposition 6.0.4 -/

section Reduction

variable {Ω' : Type u} {C : Cat.{u, w} Ω} {D : Cat.{u, v} Ω'} {E : TupleClass D}

/-- The set of objects of `D` that make up the tuple `F(X)`. -/
def tupleOf (F : Func C E.cat) (X : Pt C) : Set (D.Obj (F.obj X).car) := ((F.obj X).obj).1

/-- Definition 6.0.3 (Reduction at multiplicative cost).  *"By a reduction of the
isomorphism problem for objects `X, Y ∈ C` to objects in `D` 'at multiplicative cost `s`'
we mean a functor `F : C → E` for some category `E` of tuples of `D` such that
`|F(Y)| = s`."*

The condition constrains only the tuple `F(Y)` assigned to the second object; `X` is part
of the isomorphism problem `Iso(X,Y)` being reduced, and is recorded here for that reason
only.  (This is the reading forced by the text; cf. the note after Prop. 6.0.4, where `X'`
is chosen arbitrarily from `F(X)`.)

`|F(Y)| = s` with `s` a number says that the tuple `F(Y)` is finite and has `s` members.
`Set.ncard` of an infinite set is `0`, so finiteness is stated separately; without it an
infinite tuple would count as having cost `0`. -/
def IsReductionAtCost (F : Func C E.cat) (_X Y : Pt C) (s : ℕ) : Prop :=
  (tupleOf F Y).Finite ∧ (tupleOf F Y).ncard = s

/-- `F⁻¹(Iso(X',Y'))`: the morphisms `X → Y` of `C` that `F` maps into `Iso(X',Y')`. -/
def preimageIso (F : Func C E.cat) {X Y : Pt C} (X' : D.Obj (F.obj X).car)
    (Y' : D.Obj (F.obj Y).car) : Set (↥X.car ≃ ↥Y.car) :=
  {f | ∃ h : f ∈ C.IsoP X Y, ((F.map (⟨f, h⟩ : Hom C X Y)).1) ∈ D.Iso X' Y'}

theorem preimageIso_subset (F : Func C E.cat) {X Y : Pt C} (X' : D.Obj (F.obj X).car)
    (Y' : D.Obj (F.obj Y).car) : preimageIso F X' Y' ⊆ C.IsoP X Y := fun _ hf => hf.1

/-- Proposition 6.0.4, Eq. (40).  *"If `F` is a reduction of `Iso(X,Y)` to `D` as above
then for any `X' ∈ F(X)` we have `Iso(X,Y) = ⋃ {F⁻¹(Iso(X',Y')) | Y' ∈ F(Y)}`."*
(*"Note that `X'` is fixed in this union and is chosen arbitrarily from `F(X)`."*)

Proof: `⊇` is `preimageIso_subset`.  For `⊆`, let `f ∈ Iso(X,Y)`.  Then
`F(f) ∈ Iso(F(X),F(Y))`, so by Definition 6.0.1(b) there are `A ∈ F(X)` and `B ∈ F(Y)`
with `F(f) ∈ Iso(A,B)`; condition (ii) of Definition 6.0.1, applied to `A, X' ∈ F(X)` and
`B ∈ F(Y)`, gives `Y' ∈ F(Y)` with `F(f) ∈ Iso(X',Y')`. -/
theorem iso_eq_iUnion_preimageIso (F : Func C E.cat) {X Y : Pt C}
    {X' : D.Obj (F.obj X).car} (hX' : X' ∈ tupleOf F X) :
    C.IsoP X Y = ⋃ Y' ∈ tupleOf F Y, preimageIso F X' Y' := by
  refine Set.Subset.antisymm ?_ ?_
  · intro f hf
    obtain ⟨A, hA, B, hB, hAB⟩ := (F.map (⟨f, hf⟩ : Hom C X Y)).2
    obtain ⟨Y', hY', hY'iso⟩ :=
      E.cond_ii ((F.obj X).obj).2 ((F.obj Y).obj).2 hA hX' hB hAB
    exact Set.mem_biUnion hY' ⟨hf, hY'iso⟩
  · exact Set.iUnion₂_subset fun Y' _ => preimageIso_subset F X' Y'

/-- Proposition 6.0.4.  *"Moreover, the terms in this union are disjoint"*.

Proof (the paper says "Clear"): if `f` lies in the terms of `Y'₁` and of `Y'₂` then
`F(f) ∈ Iso(X',Y'₁) ∩ Iso(X',Y'₂)`, so `F(f)⁻¹F(f) = id ∈ Iso(Y'₁,Y'₂)`, whence
`Y'₁ = Y'₂` because `□` is faithful on `D`. -/
theorem preimageIso_disjoint (F : Func C E.cat) {X Y : Pt C}
    (X' : D.Obj (F.obj X).car) {Y'₁ Y'₂ : D.Obj (F.obj Y).car} (hne : Y'₁ ≠ Y'₂) :
    Disjoint (preimageIso F X' Y'₁) (preimageIso F X' Y'₂) := by
  rw [Set.disjoint_left]
  rintro f ⟨h, h₁⟩ ⟨h', h₂⟩
  have h₂' : ((F.map (⟨f, h⟩ : Hom C X Y)).1) ∈ D.Iso X' Y'₂ := h₂
  have := D.trans_mem (D.symm_mem h₁) h₂'
  rw [Equiv.symm_trans_self] at this
  exact hne (D.faithful this)

/-- Proposition 6.0.4.  *"and all the nonempty terms have the same cardinality."*

Proof (the paper says "Clear"): if `f₁ ∈ F⁻¹(Iso(X',Y'₁))` and `f₂ ∈ F⁻¹(Iso(X',Y'₂))`
then `h ↦ h f₁⁻¹ f₂` is a bijection from the first term onto the second: it is injective
because it is composition with a fixed bijection, it lands in the second term because
`F(h f₁⁻¹ f₂) = F(h)F(f₁)⁻¹F(f₂) ∈ Iso(X',Y'₁)Iso(Y'₁,X')Iso(X',Y'₂) ⊆ Iso(X',Y'₂)`, and
`g ↦ g f₂⁻¹ f₁` is its inverse. -/
theorem preimageIso_image (F : Func C E.cat) {X Y : Pt C}
    (X' : D.Obj (F.obj X).car) {Y'₁ Y'₂ : D.Obj (F.obj Y).car}
    {f₁ f₂ : ↥X.car ≃ ↥Y.car} (h₁ : f₁ ∈ preimageIso F X' Y'₁)
    (h₂ : f₂ ∈ preimageIso F X' Y'₂) :
    (fun h : ↥X.car ≃ ↥Y.car => h.trans (f₁.symm.trans f₂)) '' preimageIso F X' Y'₁
      = preimageIso F X' Y'₂ := by
  obtain ⟨hf₁, hF₁⟩ := h₁
  obtain ⟨hf₂, hF₂⟩ := h₂
  have key : ∀ {Z₁ Z₂ : D.Obj (F.obj Y).car} {g₁ g₂ : ↥X.car ≃ ↥Y.car},
      g₁ ∈ preimageIso F X' Z₁ → g₂ ∈ preimageIso F X' Z₂ →
      ∀ h ∈ preimageIso F X' Z₁, h.trans (g₁.symm.trans g₂) ∈ preimageIso F X' Z₂ := by
    rintro Z₁ Z₂ g₁ g₂ ⟨hg₁, hG₁⟩ ⟨hg₂, hG₂⟩ h ⟨hh, hH⟩
    have hmem : h.trans (g₁.symm.trans g₂) ∈ C.IsoP X Y :=
      C.trans_mem hh (C.trans_mem (C.symm_mem hg₁) hg₂)
    refine ⟨hmem, ?_⟩
    have e1 : (⟨h.trans (g₁.symm.trans g₂), hmem⟩ : Hom C X Y)
        = Hom.trans (⟨h, hh⟩ : Hom C X Y)
            (Hom.trans (Hom.symm (⟨g₁, hg₁⟩ : Hom C X Y)) (⟨g₂, hg₂⟩ : Hom C X Y)) := rfl
    rw [e1, F.map_trans, F.map_trans, F.map_symm]
    exact D.trans_mem hH (D.trans_mem (D.symm_mem hG₁) hG₂)
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨h, hh, rfl⟩
    exact key ⟨hf₁, hF₁⟩ ⟨hf₂, hF₂⟩ h hh
  · intro g hg
    refine ⟨g.trans (f₂.symm.trans f₁), key ⟨hf₂, hF₂⟩ ⟨hf₁, hF₁⟩ g hg, ?_⟩
    ext x
    simp

/-- Proposition 6.0.4.  *"all the nonempty terms have the same cardinality."* -/
theorem ncard_preimageIso_eq (F : Func C E.cat) {X Y : Pt C}
    (X' : D.Obj (F.obj X).car) {Y'₁ Y'₂ : D.Obj (F.obj Y).car}
    (h₁ : (preimageIso F X' Y'₁).Nonempty) (h₂ : (preimageIso F X' Y'₂).Nonempty) :
    (preimageIso F X' Y'₁).ncard = (preimageIso F X' Y'₂).ncard := by
  obtain ⟨f₁, hf₁⟩ := h₁
  obtain ⟨f₂, hf₂⟩ := h₂
  have himg := preimageIso_image F X' hf₁ hf₂
  have hinj : Function.Injective
      (fun h : ↥X.car ≃ ↥Y.car => h.trans (f₁.symm.trans f₂)) := by
    intro a b hab
    refine Equiv.ext fun x => ?_
    have h3 : (f₁.symm.trans f₂) (a x) = (f₁.symm.trans f₂) (b x) :=
      congrArg (fun e : ↥X.car ≃ ↥Y.car => e x) hab
    exact (f₁.symm.trans f₂).injective h3
  rw [← himg, Set.ncard_image_of_injective _ hinj]

end Reduction

/-! ### Definitions 6.0.5–6.0.7 -/

section PairCat

variable {Ω' : Type u} {C : Cat.{u, w} Ω} {D : Cat.{u, v} Ω'} {E : TupleClass D}

/-- Definition 6.0.5.  *"Let `F` be a reduction of the isomorphism problem in `C` to `D` at
a multiplicative cost.  Consider the category `D^F` whose objects are the pairs `(X,X')`
where `X ∈ C` and `X' ∈ F(X)`.  We set `□(X,X') = □(X)` and
`Iso((X,X'),(Y,Y')) = F⁻¹Iso(X',Y')`."*

Notational slip in version 2.5: the category is called `D^F` here and `C^F` in
Prop. 6.0.6 and Def. 6.0.7.  We use one name for it. -/
def PairObj (F : Func C E.cat) (s : Set Ω) : Type (max w v) :=
  Σ' X : C.Obj s, {X' : D.Obj (F.obj ⟨s, X⟩).car // X' ∈ tupleOf F ⟨s, X⟩}

/-- Definition 6.0.5, continued. -/
def pairCat (F : Func C E.cat) : Cat.{u, max w v} Ω where
  Obj s := PairObj F s
  Iso p q := preimageIso F p.2.1 q.2.1
  refl_mem p := by
    refine ⟨C.refl_mem p.1, ?_⟩
    have : (⟨Equiv.refl _, C.refl_mem p.1⟩ : Hom C ⟨_, p.1⟩ ⟨_, p.1⟩) = Hom.id _ := rfl
    rw [this, F.map_id]
    exact D.refl_mem _
  symm_mem := by
    rintro s t p q f ⟨hf, hF⟩
    refine ⟨C.symm_mem hf, ?_⟩
    have : (⟨f.symm, C.symm_mem hf⟩ : Hom C ⟨_, q.1⟩ ⟨_, p.1⟩)
        = Hom.symm (⟨f, hf⟩ : Hom C ⟨_, p.1⟩ ⟨_, q.1⟩) := rfl
    rw [this, F.map_symm]
    exact D.symm_mem hF
  trans_mem := by
    rintro s t r p q z f g ⟨hf, hF⟩ ⟨hg, hG⟩
    refine ⟨C.trans_mem hf hg, ?_⟩
    have : (⟨f.trans g, C.trans_mem hf hg⟩ : Hom C ⟨_, p.1⟩ ⟨_, z.1⟩)
        = Hom.trans (⟨f, hf⟩ : Hom C ⟨_, p.1⟩ ⟨_, q.1⟩) (⟨g, hg⟩ : Hom C ⟨_, q.1⟩ ⟨_, z.1⟩) :=
      rfl
    rw [this, F.map_trans]
    exact D.trans_mem hF hG
  faithful := by
    rintro s p q ⟨hf, hF⟩
    have hpq : p.1 = q.1 := C.faithful hf
    obtain ⟨X, X'⟩ := p
    obtain ⟨Y, Y'⟩ := q
    simp only at hpq
    subst hpq
    have hid : (⟨Equiv.refl _, hf⟩ : Hom C ⟨s, X⟩ ⟨s, X⟩) = Hom.id _ := rfl
    rw [hid, F.map_id] at hF
    have hXY : X'.1 = Y'.1 := D.faithful hF
    have h2 : X' = Y' := Subtype.ext hXY
    rw [h2]

/-- Definition 6.0.7.  *"Let `H : C^F → 𝓗` be a functor and let `(X,X') ∈ C^F`.  We say
that `H(X,X')` is canonically assigned to `X` relative to `X'`."*

Two notational slips of version 2.5 are resolved here: the text
writes `F(X,X')` where the functor `H` is meant, and it uses the letter `H` both for the
functor and for its target category. -/
def IsCanonicallyAssignedRelative {Ω'' : Type u} {H : Cat.{u, v'} Ω''} (F : Func C E.cat)
    (Hf : Func (pairCat F) H) (s : Set Ω) (X : C.Obj s)
    (X' : {X' : D.Obj (F.obj ⟨s, X⟩).car // X' ∈ tupleOf F ⟨s, X⟩}) (Z : Pt H) : Prop :=
  Z = Hf.obj (Pt.mk s (⟨X, X'⟩ : PairObj F s))

end PairCat

/-! ### The individualization example

*"An example of this procedure is individualization.  Let `C` have two objects, each of
them a hypergraph.  Suppose we individualize an ordered set of `t` vertices of the
hypergraph `X`; we do the same with `Y`.  We consider the category `D` of all
individualized versions of `X` and `Y`.  The category `E` will have two objects, the set of
individualized versions of `X` and the set of individualized versions of `Y`. ...  The
multiplicative cost will be `s = n(n-1)…(n-t+1) ≤ n^t` where `n` is the number of vertices
of `X`."*

We formalize this for an arbitrary category `C` (not only one with two hypergraphs as
objects) each of whose objects has at least `t` vertices, which is what makes the
individualized versions of an object a *non-empty* set, as Definition 6.0.1 requires. -/

namespace Individualize

variable {C : Cat.{u, v} Ω} (t : ℕ)

/-- The category of individualized versions of the objects of `C`: an object is an object
`X` of `C` together with an ordered set `u` of `t` distinct vertices of `X`, and the
morphisms are the isomorphisms of `C` carrying the one individualized tuple to the other. -/
def cat (C : Cat.{u, v} Ω) (t : ℕ) : Cat.{u, max u v} Ω where
  Obj s := C.Obj s × (Fin t ↪ ↥s)
  Iso X Y := {f | f ∈ C.Iso X.1 Y.1 ∧ ∀ i, f (X.2 i) = Y.2 i}
  refl_mem X := ⟨C.refl_mem X.1, fun _ => rfl⟩
  symm_mem := by
    rintro s r X Y f ⟨hf, hu⟩
    refine ⟨C.symm_mem hf, fun i => ?_⟩
    rw [← hu i, Equiv.symm_apply_apply]
  trans_mem := by
    rintro s r q X Y Z f g ⟨hf, hu⟩ ⟨hg, hv⟩
    exact ⟨C.trans_mem hf hg, fun i => by rw [Equiv.trans_apply, hu i, hv i]⟩
  faithful := by
    rintro s X Y ⟨hf, hu⟩
    exact Prod.ext (C.faithful hf) (Function.Embedding.ext fun i => hu i)

/-- The set of all individualized versions of the object `X`. -/
def versions {s : Set Ω} (X : C.Obj s) : Set ((cat C t).Obj s) := {Z | Z.1 = X}

/-- Definition 6.0.1 for individualization: `E` consists of the non-empty sets of all
individualized versions of an object. -/
def tupleClass : TupleClass (cat C t) where
  mem s := {𝒳 | ∃ X : C.Obj s, 𝒳 = versions t X ∧ 𝒳.Nonempty}
  nonempty := by rintro s 𝒳 ⟨X, rfl, h⟩; exact h
  cond_ii := by
    rintro s r 𝒳 𝒴 ⟨X₀, rfl, -⟩ ⟨Y₀, rfl, -⟩ A A' B hA hA' hB f ⟨hf, hu⟩
    simp only [versions, Set.mem_setOf_eq] at hA hA' hB
    have hfA' : f ∈ C.Iso A'.1 B.1 := by rw [hA', ← hA]; exact hf
    exact ⟨⟨B.1, ⟨fun i => f (A'.2 i), fun i j hij => A'.2.injective (f.injective hij)⟩⟩,
      hB, hfA', fun _ => rfl⟩

/-- The individualized versions of `X` are in bijection with the ordered `t`-tuples of
distinct vertices. -/
def versionsEquiv {s : Set Ω} (X : C.Obj s) : ↑(versions t X) ≃ (Fin t ↪ ↑s) where
  toFun Z := Z.1.2
  invFun u := ⟨(X, u), rfl⟩
  left_inv := by
    rintro ⟨⟨A, u⟩, hA⟩
    simp only [versions, Set.mem_setOf_eq] at hA
    subst hA
    rfl
  right_inv _ := rfl

variable {t}

/-- The reduction `F` of the example: `F(X)` is the set of all individualized versions of
`X`.  The hypothesis says that every object of `C` has at least `t` vertices, without
which the set of individualized versions would be empty, which Definition 6.0.1 forbids. -/
def redFunc (hC : ∀ X : Pt C, Nonempty (Fin t ↪ ↑X.car)) :
    Func C (tupleClass (C := C) t).cat where
  obj X := ⟨X.car, ⟨versions t X.obj, ⟨X.obj, rfl, ⟨⟨X.obj, (hC X).some⟩, rfl⟩⟩⟩⟩
  map {X Y} f :=
    ⟨f.1, ⟨X.obj, (hC X).some⟩, rfl,
      ⟨Y.obj, ⟨fun i => f.1 ((hC X).some i),
        fun i j hij => (hC X).some.injective (f.1.injective hij)⟩⟩, rfl, f.2, fun _ => rfl⟩
  map_id X := Subtype.ext rfl
  map_trans f g := Subtype.ext rfl

/-- Definition 6.0.3 for the example: *"The multiplicative cost will be
`s = n(n-1)…(n-t+1) ≤ n^t` where `n` is the number of vertices of `X`."*  Here
`Nat.descFactorial n t = n(n-1)…(n-t+1)`. -/
theorem isReductionAtCost_redFunc (hC : ∀ X : Pt C, Nonempty (Fin t ↪ ↑X.car))
    (X Y : Pt C) [Finite ↑Y.car] :
    IsReductionAtCost (redFunc hC) X Y ((Nat.card ↑Y.car).descFactorial t) := by
  classical
  have : Fintype ↑Y.car := Fintype.ofFinite _
  have hfin : Finite ↥(versions t Y.obj) := Finite.of_equiv _ (versionsEquiv t Y.obj).symm
  refine ⟨show (versions t Y.obj).Finite from Set.toFinite _, ?_⟩
  show (versions t Y.obj).ncard = _
  rw [← Nat.card_coe_set_eq, Nat.card_congr (versionsEquiv t Y.obj),
    Nat.card_eq_fintype_card, Fintype.card_embedding_eq, Nat.card_eq_fintype_card,
    Fintype.card_fin]

/-- *"… `≤ n^t` …"* -/
theorem cost_le_pow (n : ℕ) : n.descFactorial t ≤ n ^ t := Nat.descFactorial_le_pow n t

end Individualize


end Babai
