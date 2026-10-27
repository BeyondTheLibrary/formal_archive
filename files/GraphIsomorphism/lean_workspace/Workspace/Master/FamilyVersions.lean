/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Sections 6 and 14.2: the canonical versions of a canonical **family** of structures.
-/
import Workspace.Master.Versions

/-!
# The versions of a canonical family

`Workspace/Master/Versions.lean` turns a canonical assignment `z ↦ Str z` of **one** object
into canonical versions.  Case (2b) of Theorem 13.2.1 does not give one object: it
individualizes a set `S` of `d − 1` points and then one off-diagonal constituent of an
orbital configuration, and the paper warns

> **Warning**: the numbering of the `R_i` is not canonical; isomorphisms may permute the
> `R_i`.

So what is canonical is the **family** of all the individualized constituents, as a set, and
not any single member of it.  Sec. 14.2's multiplicative costs then multiply: the number of
individualizations times the number of versions of each.

This file states that passage once, in general form.

| piece | name |
|---|---|
| the versions of one object of the input category | `Babai.versAt` |
| a permutation carries the versions of an object onto the versions of the moved object | `Babai.versAt_eq_smul` |
| the cardinality of a finite union | `Babai.ncard_biUnion_le` |
| the versions of a canonical family | `Babai.exists_canonicalVersions_family_on` |

The family is indexed by a bare type `ι` with a move `mv : S(Γ) → ι → ι` rather than by
objects of the input category `C`, so that no action of `S(Γ)` on `Pt C` has to be produced:
all that is asked is that the object `Str r` attached to a member moves the way
`Babai.IsCanonicalObj` asks, and only at the members that actually occur (`Ok`).
-/

universe u v w

namespace Babai

open Equiv
open scoped Pointwise

/-! ### The versions of one object -/

section VersAt

variable {Γ : Type} {C K : Cat.{0, 0} Γ} {D : Cat.{0, 0} Γ} {E : TupleClass D}

/-- Sec. 6, Sec. 14.2: **the versions of one object** — the outcomes `G(X, X')` of the
canonical reduction over all members `X'` of the tuple `F(X)`.

`Babai.versOf` is this at the object attached to a string. -/
def versAt (F : Func C E.cat) (Gf : Func (pairCat F) K) (X : Pt C) : Set (Pt K) :=
  Set.range fun X' : {X' : D.Obj (F.obj X).car // X' ∈ tupleOf F X} =>
    Gf.obj ⟨X.car, ⟨X.obj, X'⟩⟩

theorem mem_versAt {F : Func C E.cat} {Gf : Func (pairCat F) K} {X : Pt C} {Z : Pt K} :
    Z ∈ versAt F Gf X ↔ ∃ (X' : D.Obj (F.obj X).car) (hX' : X' ∈ tupleOf F X),
      Z = Gf.obj ⟨X.car, ⟨X.obj, ⟨X', hX'⟩⟩⟩ := by
  constructor
  · rintro ⟨⟨X', hX'⟩, rfl⟩; exact ⟨X', hX', rfl⟩
  · rintro ⟨X', hX', rfl⟩; exact ⟨⟨X', hX'⟩, rfl⟩

theorem versOf_eq_versAt {Ω : Type u} {A : Type v} {F : Func C E.cat}
    {Gf : Func (pairCat F) K} {Str : (Ω → A) → Pt C} (z : Ω → A) :
    versOf F Gf Str z = versAt F Gf (Str z) := rfl

/-- The tuple is finite, so there are finitely many versions. -/
theorem versAt_finite {F : Func C E.cat} {Gf : Func (pairCat F) K} {X : Pt C}
    (h : (tupleOf F X).Finite) : (versAt F Gf X).Finite := by
  haveI : Finite {X' : D.Obj (F.obj X).car // X' ∈ tupleOf F X} := Set.Finite.to_subtype h
  exact Set.finite_range _

/-- There is at least one version: a tuple is non-empty (Def. 6.0.1). -/
theorem versAt_nonempty (F : Func C E.cat) (Gf : Func (pairCat F) K) (X : Pt C) :
    (versAt F Gf X).Nonempty := by
  obtain ⟨X', hX'⟩ := E.nonempty ((F.obj X).obj).2
  exact ⟨_, mem_versAt.2 ⟨X', hX', rfl⟩⟩

/-- There are at most `|F(X)|` versions. -/
theorem ncard_versAt_le {F : Func C E.cat} {Gf : Func (pairCat F) K} {X : Pt C}
    (h : (tupleOf F X).Finite) : (versAt F Gf X).ncard ≤ (tupleOf F X).ncard := by
  haveI : Finite {X' : D.Obj (F.obj X).car // X' ∈ tupleOf F X} := Set.Finite.to_subtype h
  have h1 : (versAt F Gf X).ncard ≤
      Nat.card {X' : D.Obj (F.obj X).car // X' ∈ tupleOf F X} := by
    rw [versAt, ← Set.image_univ]
    have := Set.ncard_image_le (s := (Set.univ :
      Set {X' : D.Obj (F.obj X).car // X' ∈ tupleOf F X}))
      (f := fun X' => Gf.obj ⟨X.car, ⟨X.obj, X'⟩⟩) Set.finite_univ
    rwa [Set.ncard_univ] at this
  have h2 : Nat.card {X' : D.Obj (F.obj X).car // X' ∈ tupleOf F X}
      = (tupleOf F X).ncard := (Nat.card_coe_set_eq _).symm ▸ rfl
  rwa [h2] at h1

end VersAt

/-! ### Moving the versions along a permutation -/

section Move

variable {Γ : Type} {C K : Cat.{0, 0} Γ} {D : Cat.{0, 0} Γ} {E : TupleClass D}

/-- `□X = π⁻¹(□Y)` whenever `□Y = π(□X)`. -/
theorem car_inv_of_car {π : Equiv.Perm Γ} {X Y : Pt C} (h : Y.car = π '' X.car) :
    X.car = ⇑(π⁻¹ : Equiv.Perm Γ) '' Y.car := by
  rw [h]
  ext w
  constructor
  · intro hw
    exact ⟨π w, ⟨w, hw, rfl⟩, by simp⟩
  · rintro ⟨u, ⟨v, hv, rfl⟩, rfl⟩
    simpa using hv

/-- The inverse of the bijection `π : □X → □Y` is the bijection `π⁻¹ : □Y → □X`. -/
theorem permHom_symm {π : Equiv.Perm Γ} {X Y : Pt C} (h : Y.car = π '' X.car) :
    (permHom π X Y h).symm = permHom π⁻¹ Y X (car_inv_of_car h) := by
  refine Equiv.ext fun y => Subtype.ext ?_
  have hy : ((permHom π X Y h ((permHom π X Y h).symm y) : ↥Y.car) : Γ) = (y : Γ) := by
    rw [Equiv.apply_symm_apply]
  rw [permHom_apply] at hy
  show (((permHom π X Y h).symm y : ↥X.car) : Γ) = π⁻¹ (y : Γ)
  rw [← hy]
  simp

variable [MulAction (Equiv.Perm Γ) (Pt K)]

/-- **One half of canonicity, for one object.**  If `π` is an isomorphism `X → Y` of the
input category, then it carries every version of `X` to a version of `Y`.

This is `Babai.smul_versOf_subset_at` with the two objects given directly instead of being
read off a string; the proof is the same, and is the one real step of Sec. 14.2: condition
(ii) of Definition 6.0.1 upgrades *"`F(f)` matches some member of the first tuple with some
member of the second"* to *"it matches **the given** `X'` with some `Y'`"*. -/
theorem smul_versAt_subset {F : Func C E.cat} {Gf : Func (pairCat F) K}
    (hGf : Gf.IsCanonicalEmbedding) (hK : IsCatAction K) (π : Equiv.Perm Γ) (X Y : Pt C)
    (hcar : Y.car = π '' X.car) (hiso : permHom π X Y hcar ∈ C.IsoP X Y) :
    π • versAt F Gf X ⊆ versAt F Gf Y := by
  rintro _ ⟨Z, hZ, rfl⟩
  rw [mem_versAt] at hZ
  obtain ⟨X', hX', rfl⟩ := hZ
  set f : Hom C X Y := ⟨permHom π X Y hcar, hiso⟩ with hf
  obtain ⟨X₀, hX₀, Y₀, hY₀, hisoXY⟩ : ∃ X₀ ∈ tupleOf F X, ∃ Y₀ ∈ tupleOf F Y,
      (F.map f).1 ∈ D.Iso X₀ Y₀ := (F.map f).2
  obtain ⟨Y', hY', hisoY⟩ :=
    E.cond_ii ((F.obj X).obj).2 ((F.obj Y).obj).2 hX₀ hX' hY₀ hisoXY
  set p : Pt (pairCat F) := ⟨X.car, ⟨X.obj, ⟨X', hX'⟩⟩⟩ with hp
  set q : Pt (pairCat F) := ⟨Y.car, ⟨Y.obj, ⟨Y', hY'⟩⟩⟩ with hq
  have hpair : (f.1 : ↥X.car ≃ ↥Y.car) ∈ (pairCat F).IsoP p q := ⟨f.2, hisoY⟩
  set g : Hom K (Gf.obj p) (Gf.obj q) := Gf.map ⟨f.1, hpair⟩ with hg
  have hgval : ∀ x : ↥(Gf.obj p).car, ((g x : ↥(Gf.obj q).car) : Γ) = π ((x : Γ)) := by
    intro x
    have := hGf.map_restrict (⟨f.1, hpair⟩ : Hom (pairCat F) p q) x
    rw [this]
    rfl
  have hcar' : (Gf.obj q).car = π '' (Gf.obj p).car := by
    refine Set.Subset.antisymm ?_ ?_
    · intro w hw
      obtain ⟨x, hx⟩ := g.1.surjective ⟨w, hw⟩
      refine ⟨(x : Γ), x.2, ?_⟩
      rw [← hgval x, hx]
    · rintro _ ⟨w, hw, rfl⟩
      have := (g ⟨w, hw⟩).2
      rwa [hgval ⟨w, hw⟩] at this
  have hperm : permHom π (Gf.obj p) (Gf.obj q) hcar' = g.1 := by
    refine Equiv.ext fun x => Subtype.ext ?_
    rw [permHom_apply, hgval x]
  refine mem_versAt.2 ⟨Y', hY', ?_⟩
  refine (hK.eq_smul hcar' ?_).symm ▸ ?_
  · rw [hperm]; exact g.2
  · rfl

/-- **A permutation carries the versions of an object onto the versions of the moved
object.**  This is the lemma the family form of Sec. 14.2 rests on. -/
theorem versAt_eq_smul {F : Func C E.cat} {Gf : Func (pairCat F) K}
    (hGf : Gf.IsCanonicalEmbedding) (hK : IsCatAction K) (π : Equiv.Perm Γ) (X Y : Pt C)
    (hcar : Y.car = π '' X.car) (hiso : permHom π X Y hcar ∈ C.IsoP X Y) :
    versAt F Gf Y = π • versAt F Gf X := by
  refine Set.Subset.antisymm ?_ (smul_versAt_subset hGf hK π X Y hcar hiso)
  have hback : π⁻¹ • versAt F Gf Y ⊆ versAt F Gf X := by
    refine smul_versAt_subset hGf hK π⁻¹ Y X (car_inv_of_car hcar) ?_
    rw [← permHom_symm hcar]
    exact C.symm_mem hiso
  intro Z hZ
  have h1 : π⁻¹ • Z ∈ versAt F Gf X := hback ⟨Z, hZ, rfl⟩
  have h2 : π • (π⁻¹ • Z) ∈ π • versAt F Gf X := Set.smul_mem_smul_set h1
  rwa [smul_inv_smul] at h2

end Move

/-! ### The size of a finite union -/

section Union

open scoped Classical in
/-- A union of at most `V` sets of at most `c₀` elements each has at most `V·c₀`
elements. -/
theorem ncard_biUnion_le {α β : Type*} {s : Set α} (hs : s.Finite) (f : α → Set β)
    (hf : ∀ a ∈ s, (f a).Finite) {V c₀ : ℕ} (hsc : s.ncard ≤ V)
    (hfc : ∀ a ∈ s, (f a).ncard ≤ c₀) : (⋃ a ∈ s, f a).ncard ≤ V * c₀ := by
  classical
  set F : α → Finset β := fun a => if h : (f a).Finite then h.toFinset else ∅ with hF
  have hFval : ∀ a ∈ s, (↑(F a) : Set β) = f a := by
    intro a ha
    rw [hF]
    simp only [dif_pos (hf a ha)]
    exact Set.Finite.coe_toFinset _
  have hEq : (⋃ a ∈ s, f a) = ↑(hs.toFinset.biUnion F) := by
    ext b
    constructor
    · intro hb
      obtain ⟨a, ha, hb⟩ : ∃ a ∈ s, b ∈ f a := by
        simpa only [Set.mem_iUnion, exists_prop] using hb
      refine Finset.mem_coe.2 (Finset.mem_biUnion.2 ⟨a, hs.mem_toFinset.2 ha, ?_⟩)
      exact Finset.mem_coe.1 (by rw [hFval a ha]; exact hb)
    · intro hb
      obtain ⟨a, ha, hb⟩ := Finset.mem_biUnion.1 (Finset.mem_coe.1 hb)
      have ha' : a ∈ s := hs.mem_toFinset.1 ha
      refine Set.mem_biUnion ha' ?_
      rw [← hFval a ha']
      exact Finset.mem_coe.2 hb
  rw [hEq, Set.ncard_coe_finset]
  refine le_trans (Finset.card_biUnion_le) ?_
  have hcard : ∀ a ∈ hs.toFinset, (F a).card ≤ c₀ := by
    intro a ha
    rw [Set.Finite.mem_toFinset] at ha
    have hFc : (F a).card = (f a).ncard := by
      rw [← Set.ncard_coe_finset, hFval a ha]
    rw [hFc]
    exact hfc a ha
  refine le_trans (Finset.sum_le_card_nsmul _ _ c₀ hcard) ?_
  have hstot : hs.toFinset.card = s.ncard := by
    rw [← Set.ncard_coe_finset, Set.Finite.coe_toFinset]
  simp only [smul_eq_mul]
  rw [hstot]
  exact Nat.mul_le_mul_right _ hsc

end Union

/-! ### The versions of a canonical family -/

section Family

variable {Ω : Type u} {A : Type v} {Γ : Type} {C K : Cat.{0, 0} Γ}
  {G : Subgroup (Equiv.Perm Ω)} [MulAction (Equiv.Perm Γ) (Pt K)]

/-- **Sec. 14.2, the versions of a canonical reduction applied to a canonical family.**

The input is not one object per string but a finite **family** `Fam z ⊆ ι` of members, each
carrying an object `Str r` of the input category, with

* `Fam (z^σ) = (ϕσ)·Fam z` — the family moves as a *set*, which is what the paper's
  *"Warning: the numbering of the `R_i` is not canonical; isomorphisms may permute the
  `R_i`"* allows, and
* `Str (mv π r) = (Str r)^π` for every member — spelled out, as `Babai.IsCanonicalObj` does,
  as *"the underlying set moves by `π`, and `π` is a morphism"*.

The versions of `z` are the versions of all the members together.  The two multiplicative
costs multiply: at most `V` members, at most `c₀` versions each.

This is the family form of `Babai.exists_canonicalVersions_on`, which is the case of a
one-member family. -/
theorem exists_canonicalVersions_family_on {ι : Type w} {cost : Pt C → ℕ}
    {Good : Pt C → Pt K → Prop} (hF : FindsAtMultCost C K cost Good) (hK : IsCatAction K)
    (ϕ : G →* Equiv.Perm Γ) (Adm : (Ω → A) → Prop)
    (hAdm : ∀ (z : Ω → A) (σ : G), Adm (strAct z (σ : Equiv.Perm Ω)) ↔ Adm z)
    (Fam : (Ω → A) → Set ι) (Str : ι → Pt C) (mv : Equiv.Perm Γ → ι → ι)
    (Ok : ι → Prop)
    (hFamOk : ∀ z, Adm z → ∀ r ∈ Fam z, Ok r)
    (hFam : ∀ z, Adm z → ∀ σ : G,
      Fam (strAct z (σ : Equiv.Perm Ω)) = mv (ϕ σ) '' Fam z)
    (hcar : ∀ (π : Equiv.Perm Γ) (r : ι), Ok r → (Str (mv π r)).car = π '' (Str r).car)
    (hiso : ∀ (π : Equiv.Perm Γ) (r : ι) (hr : Ok r),
      permHom π (Str r) (Str (mv π r)) (hcar π r hr) ∈ C.IsoP (Str r) (Str (mv π r)))
    (V c₀ : ℕ) (hne : ∀ z, Adm z → (Fam z).Nonempty) (hfin : ∀ z, (Fam z).Finite)
    (hcard : ∀ z, Adm z → (Fam z).ncard ≤ V)
    (hcost : ∀ z, Adm z → ∀ r ∈ Fam z, cost (Str r) ≤ c₀) :
    ∃ Vers : (Ω → A) → Set (Pt K),
      IsCanonicalVersions ϕ Vers ∧ (∀ z, Adm z → (Vers z).Nonempty) ∧
        (∀ z, (Vers z).Finite) ∧ (∀ z, Adm z → (Vers z).ncard ≤ V * c₀) ∧
        (∀ z, Adm z → ∀ Z ∈ Vers z, ∃ r ∈ Fam z, Good (Str r) Z) ∧
        (∀ z, ¬ Adm z → Vers z = ∅) := by
  classical
  obtain ⟨D, E, F, Gf, hGf, hcostF, hgood⟩ := hF
  refine ⟨fun z => if Adm z then ⋃ r ∈ Fam z, versAt F Gf (Str r) else ∅,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- canonicity
    intro z σ
    show (if Adm (strAct z (σ : Equiv.Perm Ω)) then
        ⋃ r ∈ Fam (strAct z (σ : Equiv.Perm Ω)), versAt F Gf (Str r) else ∅)
      = (ϕ σ) • (if Adm z then ⋃ r ∈ Fam z, versAt F Gf (Str r) else ∅)
    by_cases hz : Adm z
    · have hzσ : Adm (strAct z (σ : Equiv.Perm Ω)) := (hAdm z σ).2 hz
      rw [if_pos hzσ, if_pos hz, hFam z hz σ, Set.biUnion_image]
      have hstep : ∀ r ∈ Fam z, versAt F Gf (Str (mv (ϕ σ) r))
          = (ϕ σ) • versAt F Gf (Str r) := by
        intro r hr
        exact versAt_eq_smul hGf hK (ϕ σ) (Str r) (Str (mv (ϕ σ) r))
          (hcar _ r (hFamOk z hz r hr)) (hiso _ r (hFamOk z hz r hr))
      rw [Set.iUnion₂_congr fun r hr => hstep r hr, Set.smul_set_iUnion₂]
    · have hzσ : ¬ Adm (strAct z (σ : Equiv.Perm Ω)) := fun h => hz ((hAdm z σ).1 h)
      rw [if_neg hzσ, if_neg hz, Set.smul_set_empty]
  · -- non-empty
    intro z hz
    show (if Adm z then ⋃ r ∈ Fam z, versAt F Gf (Str r) else ∅).Nonempty
    rw [if_pos hz]
    obtain ⟨r, hr⟩ := hne z hz
    obtain ⟨Z, hZ⟩ := versAt_nonempty F Gf (Str r)
    exact ⟨Z, Set.mem_biUnion hr hZ⟩
  · -- finite
    intro z
    show (if Adm z then ⋃ r ∈ Fam z, versAt F Gf (Str r) else ∅).Finite
    by_cases hz : Adm z
    · rw [if_pos hz]
      exact (hfin z).biUnion fun r _ => versAt_finite (hcostF (Str r)).1
    · rw [if_neg hz]; exact Set.finite_empty
  · -- at most `V·c₀` many
    intro z hz
    show (if Adm z then ⋃ r ∈ Fam z, versAt F Gf (Str r) else ∅).ncard ≤ V * c₀
    rw [if_pos hz]
    refine ncard_biUnion_le (hfin z) _ (fun r _ => versAt_finite (hcostF (Str r)).1)
      (hcard z hz) (fun r hr => ?_)
    exact le_trans (ncard_versAt_le (hcostF (Str r)).1)
      (le_trans (hcostF (Str r)).2 (hcost z hz r hr))
  · -- every version is good for the member it came from
    intro z hz Z hZ
    replace hZ : Z ∈ (if Adm z then ⋃ r ∈ Fam z, versAt F Gf (Str r) else ∅) := hZ
    rw [if_pos hz] at hZ
    simp only [Set.mem_iUnion, exists_prop] at hZ
    obtain ⟨r, hr, hZ⟩ := hZ
    rw [mem_versAt] at hZ
    obtain ⟨X', hX', rfl⟩ := hZ
    exact ⟨r, hr, hgood (Str r) X' hX'⟩
  · intro z hz
    show (if Adm z then ⋃ r ∈ Fam z, versAt F Gf (Str r) else ∅) = ∅
    rw [if_neg hz]

end Family

end Babai
