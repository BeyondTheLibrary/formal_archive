/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 6: transporting a reduction across a change of the ambient type.
-/
import Workspace.Functors.Compose

/-!
# §6  A reduction on an assigned object, read on the original category

§9.7 needs to apply the Design Lemma to the neighborhood hypergraph `H`, a `d₁`-ary
relational structure **on the set of blocks**.  `Babai.designLemma_finds` is a reduction
`Babai.FindsAtMultCost (KAryInputs Ω' d₁ α) (DesignOutcomes Ω') …` for an ambient type
`Ω'`, and a block is a *set* of points, so the ambient type of that application is
`Ω' = Set Ω` while the ambient type of §9.7 is `Ω`.

**A reduction cannot simply be moved from `Ω'` to `Ω`.**  `Babai.FindsAtMultCost C H cost
Good` quantifies over a category `D : Cat.{0,0} Ω` of tuples over the *same* ambient type
as `C`, and the tuple category that a reduction over `Ω'` produces has its objects on
subsets of `Ω'`; they are not objects over `Ω`.

**What does transport is the normal form.**  A reduction in normal form
(`Babai.NormalRed`) is a category of *versions* of the objects, and a version of `X ∈ C`
may perfectly well be *the object `X` together with a version of an object of another
category assigned to `X`* — that is a type indexed by `□X`, so it is a legal category over
`Ω`.  This is `Babai.NormalRed.comap`: the pullback of a normalized reduction of `D'` along
a functor `A : C → D'`, with `D'` over any ambient type.  Its cost is unchanged
(`Babai.NormalRed.ncard_versions_comap`), and `Babai.FindsAtMultCost.of_comap` finishes the
job once a canonical embedding of the category of versions into the outcome category over
`Ω` is supplied — the *way back*, which for §9.7 sends a family `W` of blocks to
`⋃ W ⊆ □X`.  The way back has to be given on the versions, and not as a functor of the
outcome category over `Ω'` alone: a morphism of that category is an arbitrary bijection of
families of blocks, and only the ones that come from a bijection of `Ω` induce a bijection
of `⋃ W`.

## Numbering map

| Paper | Lean |
|---|---|
| a reduction of `D'` pulled back along `A : C → D'` | `Babai.NormalRed.comap` |
| *"at a multiplicative cost of `s` we can find …"*, after such a pullback | `Babai.FindsAtMultCost.of_comap` |
| the image of a block under a morphism | `Babai.Hom.imgSet` |
| a functor whose object is a family of blocks and whose morphism is `B ↦ f(B)` | `Babai.Func.IsBlockFunc` |
-/

namespace Babai

variable {Ω Ω' : Type}

/-! ### The pullback of a normalized reduction along a functor -/

namespace NormalRed

variable {C : Cat.{0, 0} Ω} {D' : Cat.{0, 0} Ω'}

/-- The category of versions of `Babai.NormalRed.comap`: a version of the object `X` of `C`
on the set `s` is `X` itself together with a version, in the sense of `N'`, of the object
`A(X)` of `D'` assigned to it.  A morphism is a morphism `f` of `C` such that `A(f)` is a
morphism of the versions.

This is a category over `Ω`, although the versions live over `Ω'`: the version is carried
as *data attached to `X`*, and `□` of the new object is `□X`. -/
def comapCat (A : Func C D') (N' : NormalRed D') : Cat.{0, 0} Ω where
  Obj s := Σ' X : C.Obj s,
    {a : N'.D.Obj (A.obj ⟨s, X⟩).car // N'.base a = (A.obj ⟨s, X⟩).obj}
  Iso {s t} p q := {f : ↥s ≃ ↥t | ∃ hf : f ∈ C.Iso p.1 q.1,
    (A.map (⟨f, hf⟩ : Hom C ⟨s, p.1⟩ ⟨t, q.1⟩)).1 ∈ N'.D.Iso p.2.1 q.2.1}
  refl_mem {s} p := by
    refine ⟨C.refl_mem p.1, ?_⟩
    have hid : (⟨Equiv.refl ↥s, C.refl_mem p.1⟩ : Hom C ⟨s, p.1⟩ ⟨s, p.1⟩)
        = Hom.id ⟨s, p.1⟩ := rfl
    rw [hid, A.map_id]
    exact N'.D.refl_mem p.2.1
  symm_mem {s t p q f} hf := by
    obtain ⟨hf₁, hf₂⟩ := hf
    refine ⟨C.symm_mem hf₁, ?_⟩
    have hsymm : (⟨f.symm, C.symm_mem hf₁⟩ : Hom C ⟨t, q.1⟩ ⟨s, p.1⟩)
        = Hom.symm (⟨f, hf₁⟩ : Hom C ⟨s, p.1⟩ ⟨t, q.1⟩) := rfl
    rw [hsymm, A.map_symm]
    exact N'.D.symm_mem hf₂
  trans_mem {s t r p q z f g} hf hg := by
    obtain ⟨hf₁, hf₂⟩ := hf
    obtain ⟨hg₁, hg₂⟩ := hg
    refine ⟨C.trans_mem hf₁ hg₁, ?_⟩
    have htr : (⟨f.trans g, C.trans_mem hf₁ hg₁⟩ : Hom C ⟨s, p.1⟩ ⟨r, z.1⟩)
        = Hom.trans (⟨f, hf₁⟩ : Hom C ⟨s, p.1⟩ ⟨t, q.1⟩)
            (⟨g, hg₁⟩ : Hom C ⟨t, q.1⟩ ⟨r, z.1⟩) := rfl
    rw [htr, A.map_trans]
    exact N'.D.trans_mem hf₂ hg₂
  faithful {s p q} hid := by
    obtain ⟨hf₁, hf₂⟩ := hid
    obtain ⟨X, a⟩ := p
    obtain ⟨Y, b⟩ := q
    have hXY : X = Y := C.faithful hf₁
    subst hXY
    have hid' : (⟨Equiv.refl ↥s, hf₁⟩ : Hom C ⟨s, X⟩ ⟨s, X⟩) = Hom.id ⟨s, X⟩ := rfl
    rw [hid', A.map_id] at hf₂
    have : a.1 = b.1 := N'.D.faithful hf₂
    exact congrArg (PSigma.mk X) (Subtype.ext this)

/-- §6.  **The pullback of a normalized reduction along a functor.**  If `A : C → D'` is a
functor into a category over *any* ambient type and `N'` is a reduction of `D'` in normal
form, then the versions of `A(X)` are a family of versions of `X`, and this family is a
normalized reduction of `C`.

Definition 6.0.1(i) (the tuple is non-empty) and 6.0.1(ii) (a morphism carries the tuple
of `X` into the tuple of `Y`) come from the corresponding conditions for `N'`, applied to
the morphism `A(f)`. -/
def comap (A : Func C D') (N' : NormalRed D') : NormalRed C where
  D := comapCat A N'
  base p := p.1
  iso_base hf := hf.choose
  nonempty X := by
    obtain ⟨a, ha⟩ := N'.nonempty (A.obj X)
    exact ⟨⟨X.obj, ⟨a, ha⟩⟩, rfl⟩
  transport := by
    rintro X Y f hf ⟨X₀, a⟩ hbase
    have hbase' : X₀ = X.obj := hbase
    subst hbase'
    have hA : (A.map (⟨f, hf⟩ : Hom C X Y)).1 ∈ D'.IsoP (A.obj X) (A.obj Y) :=
      (A.map (⟨f, hf⟩ : Hom C X Y)).2
    obtain ⟨b, hb, hab⟩ := N'.transport hA a.1 a.2
    exact ⟨⟨Y.obj, ⟨b, hb⟩⟩, rfl, ⟨hf, hab⟩⟩

@[simp] theorem comap_base (A : Func C D') (N' : NormalRed D') {s : Set Ω}
    (p : (comap A N').D.Obj s) : (comap A N').base p = p.1 := rfl

/-- The versions of `X` for the pullback are the versions of `A(X)`, tagged with `X`. -/
theorem versions_comap (A : Func C D') (N' : NormalRed D') (X : Pt C) :
    (comap A N').versions X
      = Set.range (fun a : ↥(N'.versions (A.obj X)) =>
          (⟨X.obj, ⟨a.1, a.2⟩⟩ : (comap A N').D.Obj X.car)) := by
  ext p
  constructor
  · intro hp
    obtain ⟨X₀, a⟩ := p
    have hX : X₀ = X.obj := hp
    subst hX
    exact ⟨⟨a.1, a.2⟩, rfl⟩
  · rintro ⟨a, rfl⟩; rfl

/-- The multiplicative cost is unchanged by the pullback. -/
theorem ncard_versions_comap (A : Func C D') (N' : NormalRed D') (X : Pt C)
    (hfin : (N'.versions (A.obj X)).Finite) :
    ((comap A N').versions X).Finite ∧
      ((comap A N').versions X).ncard = (N'.versions (A.obj X)).ncard := by
  classical
  haveI : Finite ↥(N'.versions (A.obj X)) := hfin.to_subtype
  have hinj : Function.Injective (fun a : ↥(N'.versions (A.obj X)) =>
      (⟨X.obj, ⟨a.1, a.2⟩⟩ : (comap A N').D.Obj X.car)) := by
    intro a b hab
    injection hab with h1 h2
  rw [versions_comap]
  exact ⟨Set.finite_range _,
    (Set.ncard_range_of_injective hinj).trans (Nat.card_coe_set_eq _)⟩

end NormalRed

/-- §6.  **A reduction of `C` from a reduction of an assigned category over another ambient
type.**  `A` assigns to each object of `C` an object of `D'`, `N'` is a reduction of `D'`
in normal form, and `G` is the *way back*: a canonical embedding of the category of
versions of `Babai.NormalRed.comap` into the outcome category `K` over `Ω`.  Then `C` has a
reduction at the multiplicative cost of `N'` at the assigned object. -/
theorem FindsAtMultCost.of_comap {C K : Cat.{0, 0} Ω} {D' : Cat.{0, 0} Ω'}
    {cost : Pt C → ℕ} {Good : Pt C → Pt K → Prop} (A : Func C D') (N' : NormalRed D')
    (G : Func (NormalRed.comap A N').D K) (hG : G.IsCanonicalEmbedding)
    (hcost : ∀ X : Pt C, (N'.versions (A.obj X)).Finite ∧
      (N'.versions (A.obj X)).ncard ≤ cost X)
    (hgood : ∀ (X : Pt C) (a : N'.D.Obj (A.obj X).car) (ha : N'.base a = (A.obj X).obj),
      Good X (G.obj ⟨X.car, ⟨X.obj, ⟨a, ha⟩⟩⟩)) :
    FindsAtMultCost C K cost Good := by
  refine FindsAtMultCost.of_normal (NormalRed.comap A N') G hG (fun X => ?_) ?_
  · obtain ⟨hfin, hle⟩ := hcost X
    obtain ⟨h1, h2⟩ := NormalRed.ncard_versions_comap A N' X hfin
    exact ⟨h1, h2 ▸ hle⟩
  · rintro X ⟨X₀, a⟩ hbase
    have hX : X₀ = X.obj := hbase
    subst hX
    exact hgood X a.1 a.2

/-! ### Blocks: the shape of the assignment that §9.7 makes

§9.7 assigns to an input the family of its **blocks**, which are subsets of `□X`, and a
morphism `f` of the input acts on a block by `B ↦ f(B)`.  This is what makes the way back
`W ↦ ⋃ W` available: the bijection of the families of blocks that a version morphism
carries is the image map of a bijection of `Ω`, so it carries `⋃ W` onto `⋃ W'`. -/

/-- The image of a subset of `□X` under a morphism of `C`, read in the ambient type. -/
def Hom.imgSet {C : Cat.{0, 0} Ω} {X Y : Pt C} (f : Hom C X Y) (B : Set Ω) : Set Ω :=
  Subtype.val '' (f.1 '' (Subtype.val ⁻¹' B))

/-- §9.7.  A functor into a category over `Set Ω` **is a family of blocks** when a morphism
acts on the assigned objects by taking images: `A(f)(B) = f(B)`.  This is the only property
of the assignment of §9.7 that the way back uses. -/
def Func.IsBlockFunc {C : Cat.{0, 0} Ω} {D' : Cat.{0, 0} (Set Ω)} (A : Func C D') : Prop :=
  ∀ {X Y : Pt C} (f : Hom C X Y) (B : ↥(A.obj X).car),
    ((A.map f B : Set Ω)) = f.imgSet (B : Set Ω)

/-! ### Non-vacuity

The pullback is tested on the simplest assignment over `Ω' = Set Ω`: the functor that sends
every object of `Babai.Sets Ω` to the object of `Babai.Sets (Set Ω)` on the family of all
the singletons `{x}`, `x ∈ □X`, with the image action.  It is a `Babai.Func.IsBlockFunc`,
the trivial reduction of `Babai.Sets (Set Ω)` pulls back to a reduction with exactly one
version of every object, and `Babai.FindsAtMultCost.of_comap` then gives a reduction at
cost `1` — so the hypotheses of `Babai.FindsAtMultCost.of_comap` are satisfiable and the
statement is not vacuous. -/

namespace AmbientTest

/-- The trivial normalized reduction: the only version of `X` is `X` itself. -/
def trivialRed (D : Cat.{0, 0} Ω') : NormalRed D where
  D := D
  base := id
  iso_base hf := hf
  nonempty X := ⟨X.obj, rfl⟩
  transport := by
    rintro X Y f hf A hA
    have hA' : A = X.obj := hA
    subst hA'
    exact ⟨Y.obj, rfl, hf⟩

theorem versions_trivialRed (D : Cat.{0, 0} Ω') (X : Pt D) :
    (trivialRed D).versions X = {X.obj} := rfl

/-- The singletons of the points of `s`, as a family of blocks. -/
def sglBlk (s : Set Ω) : Set (Set Ω) := Set.range (fun x : ↥s => ({(x : Ω)} : Set Ω))

theorem sgl_injective (s : Set Ω) :
    Function.Injective (fun x : ↥s => ({(x : Ω)} : Set Ω)) :=
  fun _ _ h => Subtype.ext (Set.singleton_eq_singleton_iff.1 h)

/-- `s` and its family of singletons are the same set. -/
noncomputable def sglEquiv (s : Set Ω) : ↥s ≃ ↥(sglBlk s) :=
  Equiv.ofInjective _ (sgl_injective s)

/-- *"Points as singleton blocks"*, as an assignment into a category over `Set Ω`. -/
noncomputable def sglBlocks (Ω : Type) : Func (Sets Ω) (Sets (Set Ω)) where
  obj X := ⟨sglBlk X.car, PUnit.unit⟩
  map {X Y} f := ⟨(sglEquiv X.car).symm.trans (f.1.trans (sglEquiv Y.car)), trivial⟩
  map_id X := Hom.ext fun B => (sglEquiv X.car).apply_symm_apply B
  map_trans {X Y Z} f g := Hom.ext fun B => by
    show (sglEquiv Z.car) (g.1 (f.1 ((sglEquiv X.car).symm B)))
      = (sglEquiv Z.car)
          (g.1 ((sglEquiv Y.car).symm ((sglEquiv Y.car) (f.1 ((sglEquiv X.car).symm B)))))
    rw [Equiv.symm_apply_apply]

theorem sglBlocks_isBlockFunc (Ω : Type) : (sglBlocks Ω).IsBlockFunc := by
  intro X Y f B
  have hB : (B : Set Ω) = {(((sglEquiv X.car).symm B : ↥X.car) : Ω)} :=
    congrArg Subtype.val ((sglEquiv X.car).apply_symm_apply B).symm
  show ({((f.1 ((sglEquiv X.car).symm B) : ↥Y.car) : Ω)} : Set Ω) = Hom.imgSet f (B : Set Ω)
  rw [Hom.imgSet, hB]
  have hpre : (Subtype.val ⁻¹' ({(((sglEquiv X.car).symm B : ↥X.car) : Ω)} : Set Ω))
      = ({(sglEquiv X.car).symm B} : Set ↥X.car) := by
    ext y
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  rw [hpre, Set.image_singleton, Set.image_singleton]

/-- The way back for the test: forget the version. -/
noncomputable def forgetVersion (Ω : Type) :
    Func (NormalRed.comap (sglBlocks Ω) (trivialRed (Sets (Set Ω)))).D (Sets Ω) where
  obj p := ⟨p.car, PUnit.unit⟩
  map f := ⟨f.1, trivial⟩
  map_id _ := rfl
  map_trans _ _ := rfl

theorem forgetVersion_isCanonicalEmbedding (Ω : Type) :
    (forgetVersion Ω).IsCanonicalEmbedding where
  car_subset _ := subset_rfl
  map_restrict _ _ := rfl

/-- **Non-vacuity of `Babai.FindsAtMultCost.of_comap`.**  The pullback of the trivial
reduction of `Babai.Sets (Set Ω)` along *"points as singleton blocks"* is a reduction of
`Babai.Sets Ω` at the multiplicative cost `1` whose outcome is the object on `□X` itself.
All the hypotheses of `Babai.FindsAtMultCost.of_comap` are met, so the statement is not
vacuous. -/
example (Ω : Type) :
    FindsAtMultCost (Sets Ω) (Sets Ω) (fun _ => 1) (fun X Z => Z.car = X.car) :=
  FindsAtMultCost.of_comap (sglBlocks Ω) (trivialRed (Sets (Set Ω))) (forgetVersion Ω)
    (forgetVersion_isCanonicalEmbedding Ω)
    (fun X => by
      rw [versions_trivialRed]
      exact ⟨Set.finite_singleton _, le_of_eq (Set.ncard_singleton _)⟩)
    (fun _ _ _ => rfl)

end AmbientTest

end Babai
