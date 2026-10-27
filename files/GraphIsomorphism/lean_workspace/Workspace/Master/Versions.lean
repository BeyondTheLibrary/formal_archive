/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Sections 6 and 14.2: the outcomes of a canonical reduction at multiplicative cost, read as
the canonical *versions* of a structure attached to a string.
-/
import Workspace.Master.Bridge
import Workspace.Functors.Cost

/-!
# From `FindsAtMultCost` to `IsCanonicalVersions`

Theorems 8.1.2, 9.2.1 and 9.2.3 conclude *"at a multiplicative cost of `s` we can find a
canonical …"*, which `Workspace/Functors/Cost.lean` states as `Babai.FindsAtMultCost`: a
functor `F` from the input category `C` into a category of tuples, and a functor `G` on the
pairs `(X, X')` with `X' ∈ F(X)` giving the object found.

`Workspace/Master/Bridge.lean` consumes something else: an assignment `z ↦ Vers z` of a
**set of structures on `Γ`** to each *string* `z` on `Ω`, canonical with respect to the
giant representation `ϕ` in the sense `Vers (z^σ) = (ϕ σ) • Vers z`
(`Babai.IsCanonicalVersions`).

This file is the passage between the two — piece (ii) of Mismatch 2 in
`Workspace/Master/DESIGN.md`.  Given

* a canonical reduction `FindsAtMultCost C K cost Good` on the ambient type `Γ`,
* an action of `S(Γ)` on the points of the output category `K` that is *its own* action,
  i.e. moves the underlying set by `π` and is a morphism of `K` (`Babai.IsCatAction`), and
* a canonical assignment `z ↦ Str z` of an object of `C` to each string
  (`Babai.IsCanonicalObj`: `Str (z^σ) = (Str z)^{ϕ σ}`),

`Babai.exists_canonicalVersions` produces the versions: `Vers z` is the set of outcomes
`G(Str z, X')` over the members `X'` of the tuple `F(Str z)`.  It is canonical, non-empty,
finite, has at most `cost (Str z)` members — which is the multiplicative cost of Eq. (71) —
and every member has the property `Good`.

## Why the action has to be given

A `Babai.Cat` carries no action of `S(Γ)`: `Cat.Iso X Y` is a set of bijections, and there
is no operation moving an object along a permutation.  What plays that role is
`Babai.Cat.IsTransportable` — *every object can be moved by every permutation* — and
faithfulness of `□` makes the moved object **unique** (`Babai.Cat.eq_of_transport`), so a
transportable category has exactly one action compatible with its morphisms
(`Babai.Cat.transportAction`, `Babai.isCatAction_transportAction`).

## Numbering map

| Paper | Lean |
|---|---|
| the tuple of versions of `X(z)` (Sec. 6, Sec. 14.2) | `Babai.versOf` |
| *"we need to compare not one but `q(m)` instances of `X(y)` with `X(x)`"* | `Babai.exists_canonicalVersions` |
-/

universe u v

namespace Babai

open Equiv
open scoped Pointwise

/-! ### Moving an object of a category along a permutation -/

section Transport

variable {Γ : Type} {C : Cat.{0, 0} Γ}

/-- The bijection `□X → □Y` that a permutation `π` of `Γ` induces when `□Y = π(□X)`. -/
noncomputable def permHom (π : Equiv.Perm Γ) (X Y : Pt C) (h : Y.car = π '' X.car) :
    ↥X.car ≃ ↥Y.car :=
  (Equiv.Set.image (π : Γ → Γ) X.car π.injective).trans (Equiv.setCongr h.symm)

@[simp] theorem permHom_apply (π : Equiv.Perm Γ) (X Y : Pt C) (h : Y.car = π '' X.car)
    (x : ↥X.car) : ((permHom π X Y h x : ↥Y.car) : Γ) = π (x : Γ) := rfl

/-- `X ↦ X^π` exists in `C`: every object can be moved along every permutation of `Γ`. -/
def Cat.IsTransportable (C : Cat.{0, 0} Γ) : Prop :=
  ∀ (π : Equiv.Perm Γ) (X : Pt C), ∃ (Y : Pt C) (h : Y.car = π '' X.car),
    permHom π X Y h ∈ C.IsoP X Y

/-- The moved object is unique: `□` is faithful, so two objects on the same underlying set
between which `π` induces the identity are equal. -/
theorem Cat.eq_of_transport {π : Equiv.Perm Γ} {X Y Z : Pt C} (hY : Y.car = π '' X.car)
    (hZ : Z.car = π '' X.car) (hfY : permHom π X Y hY ∈ C.IsoP X Y)
    (hfZ : permHom π X Z hZ ∈ C.IsoP X Z) : Y = Z := by
  have hcar : Y.car = Z.car := hY.trans hZ.symm
  refine Cat.faithful_pt hcar ?_
  have hmem : (permHom π X Y hY).symm.trans (permHom π X Z hZ) ∈ C.IsoP Y Z :=
    C.trans_mem (C.symm_mem hfY) hfZ
  have heq : (permHom π X Y hY).symm.trans (permHom π X Z hZ) = Equiv.setCongr hcar := by
    refine Equiv.ext fun y => Subtype.ext ?_
    set x := (permHom π X Y hY).symm y with hx
    have h1 : ((permHom π X Y hY x : ↥Y.car) : Γ) = π (x : Γ) := rfl
    have h2 : (permHom π X Y hY) x = y := by rw [hx]; simp
    have h3 : ((permHom π X Z hZ x : ↥Z.car) : Γ) = π (x : Γ) := rfl
    show ((permHom π X Z hZ x : ↥Z.car) : Γ) = ((Equiv.setCongr hcar y : ↥Z.car) : Γ)
    rw [h3, ← h1, h2]
    rfl
  rwa [heq] at hmem

/-- An action of `S(Γ)` on the objects of `C` that is the category's own: it moves the
underlying set by `π`, and `π` is then a morphism of `C`. -/
structure IsCatAction (C : Cat.{0, 0} Γ) [MulAction (Equiv.Perm Γ) (Pt C)] : Prop where
  /-- `□(X^π) = π(□X)`. -/
  car_smul : ∀ (π : Equiv.Perm Γ) (X : Pt C), (π • X).car = π '' X.car
  /-- `π : X → X^π` is a morphism of `C`. -/
  iso_smul : ∀ (π : Equiv.Perm Γ) (X : Pt C),
    permHom π X (π • X) (car_smul π X) ∈ C.IsoP X (π • X)

/-- The action is determined by the two conditions: an object moved by `π` in the sense of
`Babai.Cat.IsTransportable` **is** `π • X`. -/
theorem IsCatAction.eq_smul [MulAction (Equiv.Perm Γ) (Pt C)] (hC : IsCatAction C)
    {π : Equiv.Perm Γ} {X Y : Pt C} (h : Y.car = π '' X.car)
    (hf : permHom π X Y h ∈ C.IsoP X Y) : Y = π • X :=
  Cat.eq_of_transport h (hC.car_smul π X) hf (hC.iso_smul π X)

end Transport

/-! ### The action a transportable category carries

A transportable category has an action of `S(Γ)` on its objects, and only one.  This is
what makes `Babai.IsCatAction` a property of the category rather than extra data. -/

section TransportAction

variable {Γ : Type} {C : Cat.{0, 0} Γ}

open scoped Classical in
/-- `X^π`, the object `X` moved along `π`. -/
noncomputable def Cat.transport (hC : C.IsTransportable) (π : Equiv.Perm Γ) (X : Pt C) :
    Pt C := (hC π X).choose

theorem Cat.transport_car (hC : C.IsTransportable) (π : Equiv.Perm Γ) (X : Pt C) :
    (Cat.transport hC π X).car = π '' X.car := (hC π X).choose_spec.choose

theorem Cat.transport_iso (hC : C.IsTransportable) (π : Equiv.Perm Γ) (X : Pt C) :
    permHom π X (Cat.transport hC π X) (Cat.transport_car hC π X) ∈
      C.IsoP X (Cat.transport hC π X) :=
  (hC π X).choose_spec.choose_spec

/-- The action of `S(Γ)` on the objects of a transportable category. -/
noncomputable def Cat.transportAction (hC : C.IsTransportable) :
    MulAction (Equiv.Perm Γ) (Pt C) where
  smul := Cat.transport hC
  one_smul X := by
    have h1 : X.car = (1 : Equiv.Perm Γ) '' X.car := by simp
    have h2 : permHom (1 : Equiv.Perm Γ) X X h1 ∈ C.IsoP X X := by
      have he : permHom (1 : Equiv.Perm Γ) X X h1 = Equiv.refl _ :=
        Equiv.ext fun x => Subtype.ext rfl
      rw [he]
      exact C.refl_mem X.obj
    exact Cat.eq_of_transport (Cat.transport_car hC 1 X) h1 (Cat.transport_iso hC 1 X) h2
  mul_smul π τ X := by
    have hY := Cat.transport_car hC τ X
    have hZ : (Cat.transport hC π (Cat.transport hC τ X)).car = (π * τ) '' X.car := by
      rw [Cat.transport_car hC π (Cat.transport hC τ X), hY, ← Set.image_comp]
      rfl
    have hmem : (permHom τ X (Cat.transport hC τ X) hY).trans
        (permHom π (Cat.transport hC τ X)
          (Cat.transport hC π (Cat.transport hC τ X))
          (Cat.transport_car hC π (Cat.transport hC τ X))) ∈
        C.IsoP X (Cat.transport hC π (Cat.transport hC τ X)) :=
      C.trans_mem (Cat.transport_iso hC τ X)
        (Cat.transport_iso hC π (Cat.transport hC τ X))
    have heq : (permHom τ X (Cat.transport hC τ X) hY).trans
        (permHom π (Cat.transport hC τ X)
          (Cat.transport hC π (Cat.transport hC τ X))
          (Cat.transport_car hC π (Cat.transport hC τ X)))
        = permHom (π * τ) X (Cat.transport hC π (Cat.transport hC τ X)) hZ :=
      Equiv.ext fun x => Subtype.ext rfl
    rw [heq] at hmem
    exact Cat.eq_of_transport (Cat.transport_car hC (π * τ) X) hZ
      (Cat.transport_iso hC (π * τ) X) hmem

/-- The action of `Babai.Cat.transportAction` is the category's own. -/
theorem isCatAction_transportAction (hC : C.IsTransportable) :
    letI := Cat.transportAction hC
    IsCatAction C := by
  letI := Cat.transportAction hC
  exact ⟨fun π X => Cat.transport_car hC π X, fun π X => Cat.transport_iso hC π X⟩

end TransportAction

/-! ### A canonical assignment of objects to strings -/

section CanonicalObj

variable {Ω : Type u} {A : Type v} {Γ : Type} {C : Cat.{0, 0} Γ}
  {G : Subgroup (Equiv.Perm Ω)}

/-- §14.  The assignment `z ↦ Str z` of an object of `C` to a string on `Ω` is *canonical*
with respect to `ϕ : G → S(Γ)` when a `G`-shift of the string moves the object by the
corresponding permutation of `Γ`: `Str (z^σ) = (Str z)^{ϕ σ}`.

Since a `Babai.Cat` carries no action, *"`= (Str z)^{ϕ σ}`"* is spelled out as the two
things it means: the underlying set is moved by `ϕ σ`, and `ϕ σ` is a morphism of `C`. -/
structure IsCanonicalObj (ϕ : G →* Equiv.Perm Γ) (Str : (Ω → A) → Pt C) : Prop where
  /-- `□(Str (z^σ)) = (ϕ σ)(□(Str z))`. -/
  car : ∀ (z : Ω → A) (σ : G),
    (Str (strAct z (σ : Equiv.Perm Ω))).car = (ϕ σ) '' (Str z).car
  /-- `ϕ σ : Str z → Str (z^σ)` is a morphism of `C`. -/
  iso : ∀ (z : Ω → A) (σ : G),
    permHom (ϕ σ) (Str z) (Str (strAct z (σ : Equiv.Perm Ω))) (car z σ) ∈
      C.IsoP (Str z) (Str (strAct z (σ : Equiv.Perm Ω)))

/-- §14.  Canonicity of `z ↦ Str z` **on a set of strings**.

A theorem of Secs. 8–9 applies to the strings whose structure is an admissible input of the
theorem — at line 4c, to the strings whose hypergraph has a large symmetry defect — and to
no others.  The set of those strings is `G`-invariant, so it makes sense to ask for
canonicity on it and for nothing off it. -/
structure IsCanonicalObjOn (ϕ : G →* Equiv.Perm Γ) (Adm : (Ω → A) → Prop)
    (Str : (Ω → A) → Pt C) : Prop where
  /-- `□(Str (z^σ)) = (ϕ σ)(□(Str z))`, for an admissible `z`. -/
  car : ∀ (z : Ω → A), Adm z → ∀ σ : G,
    (Str (strAct z (σ : Equiv.Perm Ω))).car = (ϕ σ) '' (Str z).car
  /-- `ϕ σ : Str z → Str (z^σ)` is a morphism of `C`, for an admissible `z`. -/
  iso : ∀ (z : Ω → A) (hz : Adm z) (σ : G),
    permHom (ϕ σ) (Str z) (Str (strAct z (σ : Equiv.Perm Ω))) (car z hz σ) ∈
      C.IsoP (Str z) (Str (strAct z (σ : Equiv.Perm Ω)))

/-- A canonical assignment is canonical on every set of strings. -/
theorem IsCanonicalObj.on {ϕ : G →* Equiv.Perm Γ} {Str : (Ω → A) → Pt C}
    (h : IsCanonicalObj ϕ Str) (Adm : (Ω → A) → Prop) : IsCanonicalObjOn ϕ Adm Str where
  car z _ σ := h.car z σ
  iso z _ σ := h.iso z σ

end CanonicalObj

/-! ### The versions -/

section Versions

variable {Ω : Type u} {A : Type v} {Γ : Type} {C K : Cat.{0, 0} Γ}
  {G : Subgroup (Equiv.Perm Ω)} {D : Cat.{0, 0} Γ} {E : TupleClass D}

/-- Sec. 6, Sec. 14.2: the versions of the canonical structure of the string `z` — the
outcomes `G(X, X')` of the canonical reduction over all members `X'` of the tuple `F(X)`,
for `X = Str z` the object attached to `z`. -/
def versOf (F : Func C E.cat) (Gf : Func (pairCat F) K) (Str : (Ω → A) → Pt C)
    (z : Ω → A) : Set (Pt K) :=
  Set.range fun X' : {X' : D.Obj (F.obj (Str z)).car // X' ∈ tupleOf F (Str z)} =>
    Gf.obj ⟨(Str z).car, ⟨(Str z).obj, X'⟩⟩

theorem mem_versOf {F : Func C E.cat} {Gf : Func (pairCat F) K} {Str : (Ω → A) → Pt C}
    {z : Ω → A} {Z : Pt K} :
    Z ∈ versOf F Gf Str z ↔ ∃ (X' : D.Obj (F.obj (Str z)).car)
      (hX' : X' ∈ tupleOf F (Str z)),
      Z = Gf.obj ⟨(Str z).car, ⟨(Str z).obj, ⟨X', hX'⟩⟩⟩ := by
  constructor
  · rintro ⟨⟨X', hX'⟩, rfl⟩; exact ⟨X', hX', rfl⟩
  · rintro ⟨X', hX', rfl⟩; exact ⟨⟨X', hX'⟩, rfl⟩

variable [MulAction (Equiv.Perm Γ) (Pt K)]

/-- **One half of canonicity**: a `G`-shift of the string carries every version of `z` to a
version of `z^σ`.

*Proof.*  Let `f` be the morphism `Str z → Str (z^σ)` given by `ϕ σ`.  `F(f)` is a morphism
of tuples, so it is an isomorphism of *some* member of `F(Str z)` with *some* member of
`F(Str (z^σ))`; condition (ii) of Definition 6.0.1 (`Babai.TupleClass.cond_ii`) then makes
it an isomorphism of the given `X'` with some `Y' ∈ F(Str (z^σ))`.  The pair `(f, F(f))` is
therefore a morphism of `C^F`, and `G` of it is a morphism `G(Str z, X') → G(Str (z^σ), Y')`
which, `G` being a canonical embedding, is the restriction of `ϕ σ`.  So the second outcome
is the first moved by `ϕ σ`. -/
theorem smul_versOf_subset_at {F : Func C E.cat} {Gf : Func (pairCat F) K}
    (hGf : Gf.IsCanonicalEmbedding) (hK : IsCatAction K) {ϕ : G →* Equiv.Perm Γ}
    {Str : (Ω → A) → Pt C} (z : Ω → A) (σ : G)
    (hcar : (Str (strAct z (σ : Equiv.Perm Ω))).car = (ϕ σ) '' (Str z).car)
    (hiso : permHom (ϕ σ) (Str z) (Str (strAct z (σ : Equiv.Perm Ω))) hcar ∈
      C.IsoP (Str z) (Str (strAct z (σ : Equiv.Perm Ω)))) :
    (ϕ σ) • versOf F Gf Str z ⊆ versOf F Gf Str (strAct z (σ : Equiv.Perm Ω)) := by
  rintro _ ⟨Z, hZ, rfl⟩
  rw [mem_versOf] at hZ
  obtain ⟨X', hX', rfl⟩ := hZ
  set zσ := strAct z (σ : Equiv.Perm Ω) with hzσ
  set f : Hom C (Str z) (Str zσ) :=
    ⟨permHom (ϕ σ) (Str z) (Str zσ) hcar, hiso⟩ with hf
  -- `F(f)` is a morphism of tuples: some member of each tuple corresponds
  obtain ⟨X₀, hX₀, Y₀, hY₀, hiso⟩ : ∃ X₀ ∈ tupleOf F (Str z), ∃ Y₀ ∈ tupleOf F (Str zσ),
      (F.map f).1 ∈ D.Iso X₀ Y₀ := (F.map f).2
  obtain ⟨Y', hY', hisoY⟩ :=
    E.cond_ii ((F.obj (Str z)).obj).2 ((F.obj (Str zσ)).obj).2 hX₀ hX' hY₀ hiso
  -- the pair morphism, and its image under `G`
  set p : Pt (pairCat F) := ⟨(Str z).car, ⟨(Str z).obj, ⟨X', hX'⟩⟩⟩ with hp
  set q : Pt (pairCat F) := ⟨(Str zσ).car, ⟨(Str zσ).obj, ⟨Y', hY'⟩⟩⟩ with hq
  have hpair : (f.1 : ↥(Str z).car ≃ ↥(Str zσ).car) ∈ (pairCat F).IsoP p q :=
    ⟨f.2, hisoY⟩
  set g : Hom K (Gf.obj p) (Gf.obj q) := Gf.map ⟨f.1, hpair⟩ with hg
  -- `G` is a canonical embedding, so `g` is the restriction of `ϕ σ`
  have hgval : ∀ x : ↥(Gf.obj p).car, ((g x : ↥(Gf.obj q).car) : Γ) = (ϕ σ) ((x : Γ)) := by
    intro x
    have := hGf.map_restrict (⟨f.1, hpair⟩ : Hom (pairCat F) p q) x
    rw [this]
    rfl
  have hcar : (Gf.obj q).car = (ϕ σ) '' (Gf.obj p).car := by
    refine Set.Subset.antisymm ?_ ?_
    · intro y hy
      obtain ⟨x, hx⟩ := g.1.surjective ⟨y, hy⟩
      refine ⟨(x : Γ), x.2, ?_⟩
      rw [← hgval x, hx]
    · rintro _ ⟨y, hy, rfl⟩
      have := (g ⟨y, hy⟩).2
      rwa [hgval ⟨y, hy⟩] at this
  have hperm : permHom (ϕ σ) (Gf.obj p) (Gf.obj q) hcar = g.1 := by
    refine Equiv.ext fun x => Subtype.ext ?_
    rw [permHom_apply, hgval x]
  refine mem_versOf.2 ⟨Y', hY', ?_⟩
  refine (hK.eq_smul hcar ?_).symm ▸ ?_
  · rw [hperm]; exact g.2
  · rfl

/-- **One half of canonicity**, for a canonical assignment of objects to strings. -/
theorem smul_versOf_subset {F : Func C E.cat} {Gf : Func (pairCat F) K}
    (hGf : Gf.IsCanonicalEmbedding) (hK : IsCatAction K) {ϕ : G →* Equiv.Perm Γ}
    {Str : (Ω → A) → Pt C} (hStr : IsCanonicalObj ϕ Str) (z : Ω → A) (σ : G) :
    (ϕ σ) • versOf F Gf Str z ⊆ versOf F Gf Str (strAct z (σ : Equiv.Perm Ω)) :=
  smul_versOf_subset_at hGf hK z σ (hStr.car z σ) (hStr.iso z σ)

/-- **Sec. 14.2, the versions of a canonical reduction, on an admissible set of strings.**
The outcomes of `Babai.FindsAtMultCost`, over all individualizations, form a canonical tuple
of structures in the sense `Workspace/Master/Bridge.lean` needs, with the multiplicative cost
of the reduction as the bound on the size of the tuple:

> we need to compare not one but `q(m)` instances of `X(y)` with `X(x)`.

The reduction applies to the strings whose structure is an admissible input of the theorem
of Secs. 8–9 in question.  That set of strings is `G`-invariant (`hAdm`), so the versions of
a string outside it can be taken to be none at all, and the tuple stays canonical.

This is piece (ii) of Mismatch 2 in `Workspace/Master/DESIGN.md`. -/
theorem exists_canonicalVersions_on {cost : Pt C → ℕ} {Good : Pt C → Pt K → Prop}
    (hF : FindsAtMultCost C K cost Good) (hK : IsCatAction K) (ϕ : G →* Equiv.Perm Γ)
    (Adm : (Ω → A) → Prop)
    (hAdm : ∀ (z : Ω → A) (σ : G), Adm (strAct z (σ : Equiv.Perm Ω)) ↔ Adm z)
    (Str : (Ω → A) → Pt C) (hStr : IsCanonicalObjOn ϕ Adm Str) :
    ∃ Vers : (Ω → A) → Set (Pt K),
      IsCanonicalVersions ϕ Vers ∧ (∀ z, Adm z → (Vers z).Nonempty) ∧
        (∀ z, (Vers z).Finite) ∧ (∀ z, Adm z → (Vers z).ncard ≤ cost (Str z)) ∧
        (∀ z, Adm z → ∀ Z ∈ Vers z, Good (Str z) Z) ∧
        (∀ z, ¬ Adm z → Vers z = ∅) := by
  classical
  obtain ⟨D, E, F, Gf, hGf, hcost, hgood⟩ := hF
  refine ⟨fun z => if Adm z then versOf F Gf Str z else ∅, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- canonicity
    intro z σ
    show (if Adm (strAct z (σ : Equiv.Perm Ω)) then versOf F Gf Str
        (strAct z (σ : Equiv.Perm Ω)) else ∅)
      = (ϕ σ) • (if Adm z then versOf F Gf Str z else ∅)
    by_cases hz : Adm z
    · have hzσ : Adm (strAct z (σ : Equiv.Perm Ω)) := (hAdm z σ).2 hz
      rw [if_pos hzσ, if_pos hz]
      refine Set.Subset.antisymm ?_ ?_
      · -- `Vers (z^σ) ⊆ (ϕ σ) • Vers z`, by the other half applied at `z^σ` and `σ⁻¹`
        have hback := smul_versOf_subset_at (Str := Str) hGf hK
          (strAct z (σ : Equiv.Perm Ω)) σ⁻¹
          (hStr.car (strAct z (σ : Equiv.Perm Ω)) hzσ σ⁻¹)
          (hStr.iso (strAct z (σ : Equiv.Perm Ω)) hzσ σ⁻¹)
        have hz' : strAct (strAct z (σ : Equiv.Perm Ω)) ((σ⁻¹ : G) : Equiv.Perm Ω) = z := by
          rw [← strAct_mul]
          simp
        rw [hz'] at hback
        have hϕ : (ϕ (σ⁻¹ : G)) = (ϕ σ)⁻¹ := by rw [map_inv]
        rw [hϕ] at hback
        intro Z hZ
        have : (ϕ σ)⁻¹ • Z ∈ versOf F Gf Str z := hback ⟨Z, hZ, rfl⟩
        have h2 : (ϕ σ) • ((ϕ σ)⁻¹ • Z) ∈ (ϕ σ) • versOf F Gf Str z :=
          Set.smul_mem_smul_set this
        rwa [smul_inv_smul] at h2
      · exact smul_versOf_subset_at hGf hK z σ (hStr.car z hz σ) (hStr.iso z hz σ)
    · have hzσ : ¬ Adm (strAct z (σ : Equiv.Perm Ω)) := fun h => hz ((hAdm z σ).1 h)
      rw [if_neg hzσ, if_neg hz, Set.smul_set_empty]
  · -- non-empty: a tuple is non-empty (Def. 6.0.1)
    intro z hz
    show (if Adm z then versOf F Gf Str z else ∅).Nonempty
    rw [if_pos hz]
    obtain ⟨X', hX'⟩ := E.nonempty ((F.obj (Str z)).obj).2
    exact ⟨_, mem_versOf.2 ⟨X', hX', rfl⟩⟩
  · -- finite
    intro z
    show (if Adm z then versOf F Gf Str z else ∅).Finite
    by_cases hz : Adm z
    · rw [if_pos hz]
      have hfin := (hcost (Str z)).1
      have : Finite {X' : D.Obj (F.obj (Str z)).car // X' ∈ tupleOf F (Str z)} :=
        Set.Finite.to_subtype hfin
      exact Set.finite_range _
    · rw [if_neg hz]; exact Set.finite_empty
  · -- at most `cost` many
    intro z hz
    show (if Adm z then versOf F Gf Str z else ∅).ncard ≤ _
    rw [if_pos hz]
    have hfin := (hcost (Str z)).1
    have hsub : Finite {X' : D.Obj (F.obj (Str z)).car // X' ∈ tupleOf F (Str z)} :=
      Set.Finite.to_subtype hfin
    have h1 : (versOf F Gf Str z).ncard ≤
        Nat.card {X' : D.Obj (F.obj (Str z)).car // X' ∈ tupleOf F (Str z)} := by
      rw [versOf, ← Set.image_univ]
      have := Set.ncard_image_le (s := (Set.univ :
        Set {X' : D.Obj (F.obj (Str z)).car // X' ∈ tupleOf F (Str z)}))
        (f := fun X' => Gf.obj ⟨(Str z).car, ⟨(Str z).obj, X'⟩⟩) Set.finite_univ
      rwa [Set.ncard_univ] at this
    have h2 : Nat.card {X' : D.Obj (F.obj (Str z)).car // X' ∈ tupleOf F (Str z)}
        = (tupleOf F (Str z)).ncard := (Nat.card_coe_set_eq _).symm ▸ rfl
    rw [h2] at h1
    exact le_trans h1 (hcost (Str z)).2
  · -- every version is good
    intro z hz Z hZ
    replace hZ : Z ∈ (if Adm z then versOf F Gf Str z else ∅) := hZ
    rw [if_pos hz, mem_versOf] at hZ
    obtain ⟨X', hX', rfl⟩ := hZ
    exact hgood (Str z) X' hX'
  · intro z hz
    show (if Adm z then versOf F Gf Str z else ∅) = ∅
    rw [if_neg hz]

/-- **Sec. 14.2, the versions of a canonical reduction.**  The case of
`Babai.exists_canonicalVersions_on` in which every string is admissible. -/
theorem exists_canonicalVersions {cost : Pt C → ℕ} {Good : Pt C → Pt K → Prop}
    (hF : FindsAtMultCost C K cost Good) (hK : IsCatAction K) (ϕ : G →* Equiv.Perm Γ)
    (Str : (Ω → A) → Pt C) (hStr : IsCanonicalObj ϕ Str) :
    ∃ Vers : (Ω → A) → Set (Pt K),
      IsCanonicalVersions ϕ Vers ∧ (∀ z, (Vers z).Nonempty) ∧ (∀ z, (Vers z).Finite) ∧
        (∀ z, (Vers z).ncard ≤ cost (Str z)) ∧
        (∀ z, ∀ Z ∈ Vers z, Good (Str z) Z) := by
  obtain ⟨Vers, hcan, hne, hfin, hcost, hgood, -⟩ :=
    exists_canonicalVersions_on hF hK ϕ (fun _ => True) (fun _ _ => Iff.rfl) Str
      (hStr.on _)
  exact ⟨Vers, hcan, fun z => hne z trivial, hfin, fun z => hcost z trivial,
    fun z => hgood z trivial⟩

end Versions


/-! ### Non-vacuity

`Babai.Cat.IsTransportable` and `Babai.IsCatAction` are not empty conditions: the category
`Babai.Sets` of bare sets is transportable, so it carries an action of `S(Γ)` which is its
own.  A real instance of `Babai.IsCanonicalObj` is
`Babai.isCanonicalObj_hyperPt` (`Workspace/Master/KAryOfString.lean`), the assignment of
line 4c. -/

section Nonvacuity

variable {Γ : Type}

/-- The category of bare sets is transportable: `π` carries the set `□X` to `π(□X)`, and
every bijection is a morphism. -/
theorem isTransportable_sets : (Sets.{0, 0} Γ).IsTransportable := by
  intro π X
  exact ⟨⟨π '' X.car, PUnit.unit⟩, rfl, trivial⟩

/-- Hence there is an action of `S(Γ)` on the bare sets which is the category's own. -/
theorem exists_isCatAction_sets :
    ∃ inst : MulAction (Equiv.Perm Γ) (Pt (Sets.{0, 0} Γ)),
      @IsCatAction Γ (Sets.{0, 0} Γ) inst :=
  ⟨Cat.transportAction isTransportable_sets,
    isCatAction_transportAction isTransportable_sets⟩

end Nonvacuity

end Babai
