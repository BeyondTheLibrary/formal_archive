/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 13.2 (Aggregating the local certificates): the "Local guide" proposition, which
version 2.5 cites as `Prop. ??` in the proof of Theorem 13.2.1 (3).  The statement and the
proof are taken from the original version of the paper, Section "Local asymmetry to global
irregularity: local guides" (`babai-gi-source/babai-gi.tex`, lines 3204–3320), and adapted
to the definitions of version 2.5.
-/
import Workspace.Prelim.Structures

/-!
# Local guides (§13.2, the missing `Prop. ??`)

## The hole

The proof of Theorem 13.2.1, case (3) reads

> Proof.  We apply Prop. ?? (Local guides).  To do so, we need to define the relevant
> categories.

Version 2.5 has no such proposition: the cross-reference is a hole (`PLAN.md`,
Decision 3 (a): a hole is filled from the original version).  The original has it as
"Proposition (Local guide)":

> Let `α` be a threshold parameter, `3/4 ≤ α < 1`.  Let `C` be a category with two
> objects, `X₁` and `X₂`, with underlying sets `□(X_i) = Ω_i` where `|Ω₁| = |Ω₂| = n`.
> Let `3 ≤ k ≤ n/4`.  Let the category `L` be a `k`-local guide to the category `C`.
> Assume further that none of the sets `L ∈ (Ω₁ choose k)` is full for `i = 1`.  Then, in
> time `n^{O(k)}` we can either refute isomorphism of `X₁` and `X₂` [or] find a pair of
> canonical `k`-ary relational structures `X'₁` and `X'₂` with `□(X'_i) = □(X_i)` such
> that the strong symmetry defect of each `X'_i` is `≥ n − k + 1`.

with the definitions

> We say that `L` is a *`k`-local guide* for `C` if for every morphism `f : X_i → X_j`
> (`i, j ∈ {1,2}`), the restriction of `f` to any `L ∈ (Ω_i choose k)` is a morphism
> `X_i(L) → X_j(L^f)`.

> Let us say that the set `L ∈ (Ω_i choose k)` is *full* for index `i` if
> `Aut(X_i(L)) = Sym(L)`.

and the proof

> For `u ∈ P_i` let `L(u) = {u₁,…,u_k}`. … We say that the pairs `(u,i)` and `(v,j)` are
> equivalent, written `(u,i) ∼ (v,j)`, if there exists `α ∈ Iso(X_i(L(u)), X_j(L(v)))`
> such that `u^α = v`.  The `∼` relation is an equivalence relation on `P`, because `L` is
> a category (closed under composition of morphisms).  Let `Ξ` denote the set of `∼`
> equivalence classes.  For `Q ∈ Ξ`, let `Q_i = {u | (u,i) ∈ Q}`.  Since `L` is a `k`-local
> guide for `C`, it follows that the assignment `X_i ↦ Q_i` is canonical (for `C`) for each
> `Q`.  Let `𝔷_i = (Ω_i; Q_i | Q ∈ Ξ)`.  These are `k`-ary relational structures,
> canonically assigned to `X_i`.
>
> Claim.  The strong symmetry defect of `𝔷_i` is at least `n − k + 1`.
> Proof.  Indeed, no subset `L ∈ (Ω_i choose k)` can be strongly symmetrical in `𝔷_i` since
> `Aut(X_i(L)) ≠ Sym(L)`.

## What was adapted, and how the Claim is proved with 2.5's definitions

* **"Strong symmetry defect" → "symmetry defect".**  Version 2.5 removed the notions of
  weak and strong twins (its footnote 5); there is one twin relation (Definition 2.3.9)
  and one symmetry defect (Definitions 2.3.13 and 2.3.16).  The original's "strong
  symmetry defect" is 2.5's symmetry defect, `Babai.symDefect`, so the conclusion here is
  `n − k + 1 ≤ symDefect (Aut 𝔷_i)`.  The original's one-line proof of the Claim ("no
  subset `L` can be strongly symmetrical") becomes, with 2.5's twins: if a twin class `S`
  of `Aut(𝔷_i)` had `|S| ≥ k`, pick `L ⊆ S` with `|L| = k`; then `Sym(L) ≤ Aut(𝔷_i)`
  (Observation 2.3.12), so for `σ ∈ Sym(L)` and an ordering `u` of `L` the tuples `u` and
  `σu` lie in the same relation `Q_i`, hence `(u,i) ∼ (σu,i)`, hence some
  `α ∈ Aut(X_i(L))` has `u^α = σu`, i.e. `α = σ|_L`.  So `Aut(X_i(L)) = Sym(L)`, i.e. `L`
  is full — against the hypothesis.  Therefore every set of twins has fewer than `k`
  elements and the symmetry defect is `≥ n − k + 1`
  (`Babai.LocalGuideData.symDefect_guideStruct`).
* **Two objects → an arbitrary index type.**  The original fixes `i ∈ {1,2}`; nothing in
  the statement or the proof uses that, and Theorem 13.2.1 applies it to the two inputs
  `x₁, x₂`.  The index type is left arbitrary (`I`), which contains the paper's case.
* **The "refute isomorphism" branch.**  The original assumes fullness fails for `i = 1`
  and obtains fullness failure for `i = 2` from an invariant check ("We shall introduce
  invariants of `X_i`.  If we find any invariant that differs for `X₁` and `X₂`, exit with
  rejection.").  Fullness *is* such an invariant
  (`Babai.LocalGuideData.isFullAt_image`), so if no `k`-set is full for `i` and some
  `k`-set is full for `j` then there is no morphism `X_i → X_j`
  (`Babai.LocalGuideData.morC_eq_empty_of_full`).  This is the rejection branch of
  `Babai.proposition_localGuide`.
* **Categories.**  Section 6's `Babai.Cat` indexes objects by their underlying set inside
  one ambient type.  Here the objects of `C` have *different* carriers `Ω_i`, and the
  objects of `L` are indexed by *pairs* `(L, i)` with the same carrier `L` for both `i`,
  which `Cat.faithful` would collapse.  So the two categories are given concretely, as
  families of sets of bijections closed under identity, inverse and composition
  (`Babai.LocalGuideData`), and canonicity is stated as the concrete equivariance
  (`Babai.LocalGuideData.guideStruct_map`): every morphism `f : X_i → X_j` of `C` is an
  isomorphism `𝔷_i → 𝔷_j` of the constructed structures.
* **Hypotheses not needed.**  The original's `3 ≤ k ≤ n/4` and the threshold `α` are used
  only for the running time and for feeding the output to the Design Lemma; the two
  conclusions formalized here hold without them (only `1 ≤ k`, and `k ≤ n` to state the
  defect bound in `ℕ`).  The running time `n^{O(k)}` is covered inside the RAM proof of Theorem
  1.1.1 (`Algo.theorem_1_1_1`) and not stated as a separate RAM theorem.

## Numbering map

| Paper (original, Sec. "local guides") | Lean |
|---|---|
| the categories `C` and `L`, and "`L` is a `k`-local guide for `C`" | `Babai.LocalGuideData` |
| `L` is full for index `i` | `Babai.LocalGuideData.IsFullAt` |
| the relation `(u,i) ∼ (v,j)` | `Babai.LocalGuideData.Equiv'`, `Babai.LocalGuideData.setoid` |
| `Ξ`, the classes `Q` | `Babai.LocalGuideData.Class` |
| `Q_i` | `Babai.LocalGuideData.classRel` |
| `𝔷_i = (Ω_i; Q_i : Q ∈ Ξ)` | `Babai.LocalGuideData.guideStruct` |
| "the assignment `X_i ↦ Q_i` is canonical" | `Babai.LocalGuideData.guideStruct_map` |
| Claim: the symmetry defect of `𝔷_i` is at least `n − k + 1` | `Babai.LocalGuideData.symDefect_guideStruct` |
| Proposition (Local guide) | `Babai.proposition_localGuide` |
-/

namespace Babai

open scoped Classical

universe u v

/-! ### The restriction of a bijection to a subset -/

/-- The restriction of a bijection `f : α ≃ β` to a subset `L ⊆ α`, as a bijection
`L → f(L)`.  This is the paper's "restriction of `f` to `L`". -/
def restrictEquiv {α β : Type*} (f : α ≃ β) (L : Set α) : ↥L ≃ ↥(f '' L) where
  toFun a := ⟨f a, ⟨a, a.2, rfl⟩⟩
  invFun b := ⟨f.symm b, by
    obtain ⟨a, ha, hb⟩ := b.2
    simpa [← hb] using ha⟩
  left_inv a := by ext; simp
  right_inv b := by ext; simp

@[simp] theorem restrictEquiv_apply {α β : Type*} (f : α ≃ β) (L : Set α) (a : ↥L) :
    ((restrictEquiv f L a : ↥(f '' L)) : β) = f (a : α) := rfl

/-! ### The data of the two categories -/

/-- The situation of the Local guide proposition: a category `C` whose objects `X_i` have
underlying sets `Ω_i`, a category `L` whose objects `X_i(L)` are indexed by the pairs
`(L, i)` with `L ∈ (Ω_i choose k)` and have underlying set `L`, and the hypothesis that
`L` is a `k`-local guide for `C`.

Both categories are concrete Brandt groupoids (§6): the morphisms are bijections of the
underlying sets, they contain the identities, and they are closed under inverse and
composition.  Since the objects of `C` have different carriers and the objects of `L` are
indexed by pairs, the two categories are given here as bare families of sets of bijections
rather than through `Babai.Cat`; see the module docstring. -/
structure LocalGuideData (I : Type u) (Ω : I → Type v) (k : ℕ) where
  /-- `Iso(X_i, X_j)`, the morphisms of the category `C`. -/
  morC : ∀ i j : I, Set (Ω i ≃ Ω j)
  /-- `Iso(X_i(L), X_j(L'))`, the morphisms of the category `L`. -/
  morL : ∀ (i j : I) (L : Set (Ω i)) (L' : Set (Ω j)), Set (↥L ≃ ↥L')
  /-- `C` contains the identities. -/
  morC_refl : ∀ i, Equiv.refl (Ω i) ∈ morC i i
  /-- Every morphism of `C` is invertible. -/
  morC_symm : ∀ {i j : I} {f : Ω i ≃ Ω j}, f ∈ morC i j → f.symm ∈ morC j i
  /-- Morphisms of `C` compose. -/
  morC_trans : ∀ {i j l : I} {f : Ω i ≃ Ω j} {g : Ω j ≃ Ω l},
    f ∈ morC i j → g ∈ morC j l → f.trans g ∈ morC i l
  /-- `L` contains the identities. -/
  morL_refl : ∀ (i : I) (L : Set (Ω i)), Equiv.refl ↥L ∈ morL i i L L
  /-- Every morphism of `L` is invertible. -/
  morL_symm : ∀ {i j : I} {L : Set (Ω i)} {L' : Set (Ω j)} {α : ↥L ≃ ↥L'},
    α ∈ morL i j L L' → α.symm ∈ morL j i L' L
  /-- Morphisms of `L` compose. -/
  morL_trans : ∀ {i j l : I} {L : Set (Ω i)} {L' : Set (Ω j)} {L'' : Set (Ω l)}
    {α : ↥L ≃ ↥L'} {β : ↥L' ≃ ↥L''},
    α ∈ morL i j L L' → β ∈ morL j l L' L'' → α.trans β ∈ morL i l L L''
  /-- "`L` is a `k`-local guide for `C`": for every morphism `f : X_i → X_j` of `C`, the
  restriction of `f` to any `L ∈ (Ω_i choose k)` is a morphism `X_i(L) → X_j(L^f)`. -/
  guide : ∀ {i j : I} {f : Ω i ≃ Ω j}, f ∈ morC i j → ∀ L : Set (Ω i), L.ncard = k →
    restrictEquiv f L ∈ morL i j L (f '' L)

namespace LocalGuideData

variable {I : Type u} {Ω : I → Type v} {k : ℕ} (D : LocalGuideData I Ω k)

/-- "Let us say that the set `L ∈ (Ω_i choose k)` is *full* for index `i` if
`Aut(X_i(L)) = Sym(L)`." -/
def IsFullAt (i : I) (L : Set (Ω i)) : Prop := D.morL i i L L = Set.univ

/-- Transport of a morphism along an equality of underlying sets: if `L' = L` then a
morphism `X_i(L) → X_i(L')` is a morphism `X_i(L) → X_i(L)`. -/
theorem morL_of_eq {i j : I} {L : Set (Ω i)} {L' L'' : Set (Ω j)} (h : L' = L'')
    {α : ↥L ≃ ↥L'} (hα : α ∈ D.morL i j L L') :
    α.trans (Equiv.setCongr h) ∈ D.morL i j L L'' := by
  subst h
  rwa [show α.trans (Equiv.setCongr (rfl : L' = L')) = α from
    Equiv.ext fun z => Subtype.ext rfl]

/-! ### The equivalence relation `∼` on ordered `k`-tuples -/

/-- `P = (P₁ × {1}) ∪ (P₂ × {2})` where `P_i = Ω_i^{⟨k⟩}` is the set of ordered `k`-tuples
of distinct elements of `Ω_i`. -/
abbrev Tuples (I : Type u) (Ω : I → Type v) (k : ℕ) : Type max u v := Σ i : I, Fin k ↪ Ω i

/-- For `u ∈ P_i`, the set `L(u) = {u₁, …, u_k} ∈ (Ω_i choose k)`. -/
abbrev supp (p : Tuples I Ω k) : Set (Ω p.1) := Set.range p.2

theorem ncard_range_embedding {i : I} (u : Fin k ↪ Ω i) :
    (Set.range (u : Fin k → Ω i)).ncard = k := by
  classical
  have h : (Set.range (u : Fin k → Ω i)) = (u : Fin k → Ω i) '' Set.univ := by simp
  rw [h, Set.ncard_image_of_injective _ u.injective, Set.ncard_univ,
    Nat.card_eq_fintype_card, Fintype.card_fin]

theorem ncard_supp (p : Tuples I Ω k) : (supp p).ncard = k := ncard_range_embedding p.2

/-- "We say that the pairs `(u,i)` and `(v,j)` are *equivalent*, written `(u,i) ∼ (v,j)`,
if there exists `α ∈ Iso(X_i(L(u)), X_j(L(v)))` such that `u^α = v`." -/
def Equiv' (p q : Tuples I Ω k) : Prop :=
  ∃ α ∈ D.morL p.1 q.1 (supp p) (supp q),
    ∀ t : Fin k, ((α ⟨p.2 t, ⟨t, rfl⟩⟩ : ↥(supp q)) : Ω q.1) = q.2 t

/-- "The `∼` relation is an equivalence relation on `P`, because `L` is a category (closed
under composition of morphisms)." -/
theorem equiv'_equivalence : Equivalence D.Equiv' where
  refl p := ⟨Equiv.refl _, D.morL_refl _ _, fun _ => rfl⟩
  symm := by
    rintro p q ⟨α, hα, hu⟩
    refine ⟨α.symm, D.morL_symm hα, fun t => ?_⟩
    have h : α ⟨p.2 t, ⟨t, rfl⟩⟩ = (⟨q.2 t, ⟨t, rfl⟩⟩ : ↥(supp q)) := Subtype.ext (hu t)
    rw [show (⟨q.2 t, ⟨t, rfl⟩⟩ : ↥(supp q)) = α ⟨p.2 t, ⟨t, rfl⟩⟩ from h.symm,
      Equiv.symm_apply_apply]
  trans := by
    rintro p q r ⟨α, hα, hu⟩ ⟨β, hβ, hv⟩
    refine ⟨α.trans β, D.morL_trans hα hβ, fun t => ?_⟩
    have h : α ⟨p.2 t, ⟨t, rfl⟩⟩ = (⟨q.2 t, ⟨t, rfl⟩⟩ : ↥(supp q)) := Subtype.ext (hu t)
    rw [Equiv.trans_apply, h]
    exact hv t

/-- The setoid of the relation `∼`. -/
def setoid : Setoid (Tuples I Ω k) where
  r := D.Equiv'
  iseqv := D.equiv'_equivalence

/-- `Ξ`, the set of `∼` equivalence classes. -/
def Class (D : LocalGuideData I Ω k) : Type max u v := Quotient D.setoid

/-- The class of a tuple. -/
def mkClass (p : Tuples I Ω k) : D.Class := Quotient.mk D.setoid p

theorem mkClass_eq_iff {p q : Tuples I Ω k} : D.mkClass p = D.mkClass q ↔ D.Equiv' p q :=
  Quotient.eq (r := D.setoid)

/-- "For `Q ∈ Ξ`, let `Q_i = {u | (u,i) ∈ Q}`", as a `k`-ary relation on `Ω_i`. -/
def classRel (i : I) (Q : D.Class) : Set (Fin k → Ω i) :=
  {w | ∃ u : Fin k ↪ Ω i, (u : Fin k → Ω i) = w ∧ D.mkClass ⟨i, u⟩ = Q}

theorem mem_classRel {i : I} {Q : D.Class} {u : Fin k ↪ Ω i} :
    (u : Fin k → Ω i) ∈ D.classRel i Q ↔ D.mkClass ⟨i, u⟩ = Q := by
  constructor
  · rintro ⟨v, hv, hQ⟩
    have huv : u = v := Function.Embedding.ext fun t => congrFun hv.symm t
    rw [huv]
    exact hQ
  · intro h
    exact ⟨u, rfl, h⟩

/-! ### The `k`-ary relational structures `𝔷_i` -/

section Struct

variable [Finite I] [∀ i, Finite (Ω i)]

instance instFiniteTuples : Finite (Tuples I Ω k) := by
  classical
  haveI : ∀ i : I, Finite (Fin k ↪ Ω i) := fun i =>
    Finite.of_injective (fun u : Fin k ↪ Ω i => (u : Fin k → Ω i))
      (fun _ _ h => Function.Embedding.ext (congrFun h))
  infer_instance

instance instFiniteClass : Finite D.Class := Quotient.finite _

/-- "Let `𝔷_i = (Ω_i; Q_i | Q ∈ Ξ)`.  These are `k`-ary relational structures, canonically
assigned to `X_i`." -/
noncomputable def guideStruct (i : I) : RelStructure (Ω i) where
  numRel := Nat.card D.Class
  arity := fun _ => k
  rel := fun j => D.classRel i ((Finite.equivFin D.Class).symm j)

theorem isKAry_guideStruct (i : I) : (D.guideStruct i).IsKAry k := fun _ => rfl

/-! ### Canonicity -/

/-- The classes are carried into one another by the morphisms of `C`: if `f : X_i → X_j`
is a morphism of `C` and `u` is a `k`-tuple in `Ω_i`, then `(u, i) ∼ (u^f, j)`.

"Since `L` is a `k`-local guide for `C`, it follows that the assignment `X_i ↦ Q_i` is
canonical (for `C`) for each `Q`." -/
theorem mkClass_comp {i j : I} {f : Ω i ≃ Ω j} (hf : f ∈ D.morC i j) (u : Fin k ↪ Ω i) :
    D.mkClass ⟨j, u.trans f.toEmbedding⟩ = D.mkClass ⟨i, u⟩ := by
  refine D.mkClass_eq_iff.2 (D.equiv'_equivalence.symm ?_)
  have hsupp : (f : Ω i → Ω j) '' Set.range (u : Fin k → Ω i)
      = Set.range ((u.trans f.toEmbedding : Fin k ↪ Ω j) : Fin k → Ω j) := by
    ext z
    constructor
    · rintro ⟨a, ⟨t, rfl⟩, rfl⟩
      exact ⟨t, rfl⟩
    · rintro ⟨t, rfl⟩
      exact ⟨u t, ⟨t, rfl⟩, rfl⟩
  have hguide := D.guide hf (Set.range (u : Fin k → Ω i)) (ncard_range_embedding u)
  refine ⟨(restrictEquiv f (Set.range (u : Fin k → Ω i))).trans (Equiv.setCongr hsupp),
    D.morL_of_eq hsupp hguide, fun t => rfl⟩

/-- **Canonicity** of the Local guide construction: every morphism `f : X_i → X_j` of `C`
is an isomorphism `𝔷_i → 𝔷_j` of the constructed `k`-ary relational structures.

This is the paper's "the assignment `X_i ↦ Q_i` is canonical (for `C`) for each `Q`",
stated as the concrete equivariance because the two objects have different carriers (see
the module docstring). -/
theorem guideStruct_map {i j : I} {f : Ω i ≃ Ω j} (hf : f ∈ D.morC i j) :
    (D.guideStruct i).map (f : Ω i → Ω j) = D.guideStruct j := by
  have key : ∀ (i j : I) (f : Ω i ≃ Ω j), f ∈ D.morC i j → ∀ Q : D.Class,
      mapRel (f : Ω i → Ω j) (D.classRel i Q) ⊆ D.classRel j Q := by
    rintro i j f hf Q w ⟨v, ⟨u, rfl, hQ⟩, rfl⟩
    have hval : tupleMap (f : Ω i → Ω j) (u : Fin k → Ω i)
        = ((u.trans f.toEmbedding : Fin k ↪ Ω j) : Fin k → Ω j) := rfl
    rw [hval, D.mem_classRel, D.mkClass_comp hf u]
    exact hQ
  have hrel : ∀ Q : D.Class, mapRel (f : Ω i → Ω j) (D.classRel i Q) = D.classRel j Q := by
    intro Q
    refine le_antisymm (key i j f hf Q) fun w hw => ?_
    have hback : tupleMap ((f.symm : Ω j → Ω i)) w ∈ D.classRel i Q :=
      key j i f.symm (D.morC_symm hf) Q ⟨w, hw, rfl⟩
    refine ⟨tupleMap ((f.symm : Ω j → Ω i)) w, hback, ?_⟩
    funext t
    simp [tupleMap]
  simp only [RelStructure.map, guideStruct, RelStructure.mk.injEq, heq_eq_eq, true_and]
  funext jj
  exact hrel _

/-! ### The symmetry defect of `𝔷_i` -/

/-- An automorphism of `𝔷_i` preserves the class of every `k`-tuple. -/
theorem mkClass_comp_aut {i : I} {σ : Equiv.Perm (Ω i)}
    (hσ : σ ∈ (D.guideStruct i).Aut) (u : Fin k ↪ Ω i) :
    D.mkClass ⟨i, u.trans σ.toEmbedding⟩ = D.mkClass ⟨i, u⟩ := by
  have h : (D.guideStruct i).map (σ : Ω i → Ω i) = D.guideStruct i := hσ
  simp only [RelStructure.map, guideStruct, RelStructure.mk.injEq, heq_eq_eq, true_and] at h
  set Q : D.Class := D.mkClass ⟨i, u⟩ with hQ
  set jj : Fin (Nat.card D.Class) := Finite.equivFin D.Class Q with hjj
  have hQjj : (Finite.equivFin D.Class).symm jj = Q := by rw [hjj, Equiv.symm_apply_apply]
  have hfun := congrFun h jj
  rw [hQjj] at hfun
  have hmem : (u : Fin k → Ω i) ∈ D.classRel i Q := (D.mem_classRel).2 rfl
  have himg : tupleMap (σ : Ω i → Ω i) (u : Fin k → Ω i) ∈ D.classRel i Q := by
    rw [← hfun]
    exact ⟨_, hmem, rfl⟩
  have hval : tupleMap (σ : Ω i → Ω i) (u : Fin k → Ω i)
      = ((u.trans σ.toEmbedding : Fin k ↪ Ω i) : Fin k → Ω i) := rfl
  rw [hval, D.mem_classRel] at himg
  exact himg

variable [∀ i, Fintype (Ω i)] [∀ i, DecidableEq (Ω i)]

/-- The Claim of the original's proof, in the form "every set of twins of `Aut(𝔷_i)` has
fewer than `k` elements": if a set `L` of `k` twins existed, then `L` would be full for
`i`.  (`Sym(L) ≤ Aut(𝔷_i)` by Observation 2.3.12, and each `σ ∈ Sym(L)` is realized by a
morphism `X_i(L) → X_i(L)` because `u` and `σu` lie in the same class.) -/
theorem isFullAt_of_isTwinSet {i : I} {L : Set (Ω i)} (hL : L.ncard = k)
    (hΨ : IsTwinSet (D.guideStruct i).Aut L) : D.IsFullAt i L := by
  classical
  -- an ordering `u` of `L`; after `subst` the set `L` *is* `L(u) = range u`
  obtain ⟨u, hu⟩ : ∃ u : Fin k ↪ Ω i, Set.range (u : Fin k → Ω i) = L := by
    have hcard : Nat.card ↥L = k := by rw [Nat.card_coe_set_eq]; exact hL
    have e : Fin k ≃ ↥L := (finCongr hcard.symm).trans (Finite.equivFin ↥L).symm
    refine ⟨⟨fun t => ((e t : Ω i)), fun a b hab => e.injective (Subtype.ext hab)⟩, ?_⟩
    ext z
    constructor
    · rintro ⟨t, rfl⟩
      exact (e t).2
    · intro hz
      exact ⟨e.symm ⟨z, hz⟩, by simp⟩
  subst hu
  -- `Sym(L) ≤ Aut(𝔷_i)` (Observation 2.3.12)
  have hsym : symOn (Set.range (u : Fin k → Ω i)) ≤ (D.guideStruct i).Aut :=
    (isTwinSet_iff_symOn_le _ _).1 hΨ
  refine Set.eq_univ_of_forall fun π => ?_
  -- extend `π` to `σ ∈ Sym(L) ≤ Aut(𝔷_i)`
  set σ : Equiv.Perm (Ω i) := Equiv.Perm.ofSubtype π with hσdef
  have hfix : ∀ z ∉ Set.range (u : Fin k → Ω i), σ z = z := fun z hz =>
    Equiv.Perm.ofSubtype_apply_of_not_mem π hz
  have hmemL : ∀ (z : Ω i) (hz : z ∈ Set.range (u : Fin k → Ω i)),
      σ z = (π ⟨z, hz⟩ : Ω i) := fun z hz => Equiv.Perm.ofSubtype_apply_of_mem π hz
  have hσmem : σ ∈ (D.guideStruct i).Aut := hsym (mem_symOn.2 hfix)
  -- `σ` maps `L` onto `L`, so `L(σu) = L(u)`
  have himage : (σ : Ω i → Ω i) '' Set.range (u : Fin k → Ω i)
      = Set.range (u : Fin k → Ω i) := by
    ext z
    constructor
    · rintro ⟨a, ha, rfl⟩
      rw [hmemL a ha]
      exact (π ⟨a, ha⟩).2
    · intro hz
      refine ⟨(π.symm ⟨z, hz⟩ : Ω i), (π.symm ⟨z, hz⟩).2, ?_⟩
      rw [hmemL _ (π.symm ⟨z, hz⟩).2]
      simp
  have hrange : Set.range ((u.trans σ.toEmbedding : Fin k ↪ Ω i) : Fin k → Ω i)
      = Set.range (u : Fin k → Ω i) := by
    have hcomp : Set.range ((u.trans σ.toEmbedding : Fin k ↪ Ω i) : Fin k → Ω i)
        = (σ : Ω i → Ω i) '' Set.range (u : Fin k → Ω i) := by
      ext z
      constructor
      · rintro ⟨t, rfl⟩
        exact ⟨u t, ⟨t, rfl⟩, rfl⟩
      · rintro ⟨a, ⟨t, rfl⟩, rfl⟩
        exact ⟨t, rfl⟩
    rw [hcomp, himage]
  -- `(u,i) ∼ (σu,i)`, and the witnessing morphism is `π`
  have hclass := D.mkClass_comp_aut hσmem u
  obtain ⟨α, hα, hαval⟩ := D.mkClass_eq_iff.1 hclass.symm
  have hαL : α.trans (Equiv.setCongr hrange)
      ∈ D.morL i i (Set.range (u : Fin k → Ω i)) (Set.range (u : Fin k → Ω i)) :=
    D.morL_of_eq hrange hα
  have hπ : α.trans (Equiv.setCongr hrange) = π := by
    refine Equiv.ext fun z => Subtype.ext ?_
    obtain ⟨t, ht⟩ : ∃ t : Fin k, u t = (z : Ω i) := z.2
    have hz : z = (⟨u t, ⟨t, rfl⟩⟩ : ↥(Set.range (u : Fin k → Ω i))) := (Subtype.ext ht).symm
    rw [hz]
    have hval := hαval t
    have hstep : (((α.trans (Equiv.setCongr hrange)) ⟨u t, ⟨t, rfl⟩⟩ :
        ↥(Set.range (u : Fin k → Ω i))) : Ω i)
        = ((α ⟨u t, ⟨t, rfl⟩⟩ :
            ↥(supp (⟨i, u.trans σ.toEmbedding⟩ : Tuples I Ω k))) : Ω i) := rfl
    rw [hstep, hval]
    exact hmemL _ ⟨t, rfl⟩
  rw [← hπ]
  exact hαL

/-- The Claim of the original's proof: "the strong symmetry defect of `𝔷_i` is at least
`n − k + 1`", in the form "every set of twins has fewer than `k` elements". -/
theorem symmetricity_guideStruct_lt {i : I} (hk : 1 ≤ k)
    (hfull : ∀ L : Set (Ω i), L.ncard = k → ¬ D.IsFullAt i L) :
    symmetricity (D.guideStruct i).Aut < k := by
  classical
  refine lt_of_le_of_lt (symmetricity_le (k := k - 1) fun Ψ hΨ => ?_) (by omega)
  by_contra hcard
  push_neg at hcard
  obtain ⟨L, hLsub, hLcard⟩ := Finset.exists_subset_card_eq (s := Ψ) (n := k) (by omega)
  refine hfull (↑L : Set (Ω i)) (by rw [Set.ncard_coe_finset]; exact hLcard) ?_
  refine D.isFullAt_of_isTwinSet (by rw [Set.ncard_coe_finset]; exact hLcard) ?_
  intro a ha b hb hab
  exact hΨ a (hLsub (by simpa using ha)) b (hLsub (by simpa using hb)) hab

/-- **The Claim** of the Local guide proposition, in the paper's form: the symmetry defect
of `𝔷_i` is at least `n − k + 1`. -/
theorem symDefect_guideStruct {i : I} (hk : 1 ≤ k) (hkn : k ≤ Fintype.card (Ω i))
    (hfull : ∀ L : Set (Ω i), L.ncard = k → ¬ D.IsFullAt i L) :
    Fintype.card (Ω i) - k + 1 ≤ symDefect (D.guideStruct i).Aut := by
  have h1 := D.symmetricity_guideStruct_lt hk hfull
  have h2 := symmetricity_le_card (D.guideStruct i).Aut
  rw [symDefect]
  omega

/-! ### Fullness is an invariant -/

/-- Fullness is an invariant of the objects of `C`: if `f : X_i → X_j` is a morphism then
`L` is full for `i` if and only if `L^f` is full for `j`.  ("We shall introduce invariants
of `X_i`.") -/
theorem isFullAt_image {i j : I} {f : Ω i ≃ Ω j} (hf : f ∈ D.morC i j) {L : Set (Ω i)}
    (hL : L.ncard = k) : D.IsFullAt i L ↔ D.IsFullAt j ((f : Ω i → Ω j) '' L) := by
  have hr : restrictEquiv f L ∈ D.morL i j L ((f : Ω i → Ω j) '' L) := D.guide hf L hL
  constructor
  · intro hfull
    refine Set.eq_univ_of_forall fun β => ?_
    have hmem : (restrictEquiv f L).trans (β.trans (restrictEquiv f L).symm)
        ∈ D.morL i i L L := by rw [hfull]; trivial
    have hcomp := D.morL_trans (D.morL_trans (D.morL_symm hr) hmem) hr
    have heq : (((restrictEquiv f L).symm.trans
        ((restrictEquiv f L).trans (β.trans (restrictEquiv f L).symm))).trans
          (restrictEquiv f L)) = β := by
      ext z; simp
    rwa [heq] at hcomp
  · intro hfull
    refine Set.eq_univ_of_forall fun π => ?_
    have hmem : (restrictEquiv f L).symm.trans (π.trans (restrictEquiv f L))
        ∈ D.morL j j ((f : Ω i → Ω j) '' L) ((f : Ω i → Ω j) '' L) := by
      rw [hfull]; trivial
    have hcomp := D.morL_trans (D.morL_trans hr hmem) (D.morL_symm hr)
    have heq : (((restrictEquiv f L).trans
        ((restrictEquiv f L).symm.trans (π.trans (restrictEquiv f L)))).trans
          (restrictEquiv f L).symm) = π := by
      ext z; simp
    rwa [heq] at hcomp

/-- The rejection branch: if no `k`-set is full for `i` but some `k`-set is full for `j`,
then there is no morphism `X_i → X_j`, i.e. isomorphism is refuted. -/
theorem morC_eq_empty_of_full {i j : I}
    (hi : ∀ L : Set (Ω i), L.ncard = k → ¬ D.IsFullAt i L)
    {L' : Set (Ω j)} (hL' : L'.ncard = k) (hj : D.IsFullAt j L') : D.morC i j = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun f hf => ?_
  have hback := D.morC_symm hf
  have hL : ((f.symm : Ω j → Ω i) '' L').ncard = k := by
    rw [Set.ncard_image_of_injective _ f.symm.injective]; exact hL'
  exact hi _ hL ((D.isFullAt_image hback hL').1 hj)

end Struct

end LocalGuideData

/-- **Proposition (Local guide)**, §13.2 (`Prop. ??` of version 2.5; the statement is the
original's Proposition [Local guide], `babai-gi.tex:3236`, with version 2.5's symmetry
defect in place of the original's strong symmetry defect — see the module docstring).

> Let `C` be a category with two objects, `X₁` and `X₂`, with underlying sets
> `□(X_i) = Ω_i` where `|Ω₁| = |Ω₂| = n`.  Let `3 ≤ k ≤ n/4`.  Let the category `L` be a
> `k`-local guide to the category `C`.  Assume further that none of the sets
> `L ∈ (Ω₁ choose k)` is full for `i = 1`.  Then, in time `n^{O(k)}` we can either refute
> isomorphism of `X₁` and `X₂` [or] find a pair of canonical `k`-ary relational structures
> `X'₁` and `X'₂` with `□(X'_i) = □(X_i)` such that the [strong] symmetry defect of each
> `X'_i` is `≥ n − k + 1`.

The three conclusions are: the structures `𝔷_i` are `k`-ary (`isKAry_guideStruct`); they
are canonical, i.e. every morphism `X_i → X_j` of `C` is an isomorphism `𝔷_i → 𝔷_j`; and
either isomorphism of `X_i` and `X_j` is refuted (`morC i j = ∅`) or both structures have
symmetry defect `≥ n − k + 1`.  The running time `n^{O(k)}` is
covered inside the RAM proof of Theorem 1.1.1 (`Algo.theorem_1_1_1`) and not stated as a
separate RAM theorem.  The original's `3 ≤ k ≤ n/4` and its threshold `α` are not
needed for these conclusions; only `1 ≤ k` and, to state the bound in `ℕ`, `k ≤ n`. -/
theorem proposition_localGuide {I : Type u} {Ω : I → Type v} {k : ℕ}
    [Finite I] [∀ i, Fintype (Ω i)] [∀ i, DecidableEq (Ω i)]
    (D : LocalGuideData I Ω k) (hk : 1 ≤ k) (i j : I)
    (hkn : k ≤ Fintype.card (Ω i)) (hkn' : k ≤ Fintype.card (Ω j))
    (hfull : ∀ L : Set (Ω i), L.ncard = k → ¬ D.IsFullAt i L) :
    (∀ l : I, (D.guideStruct l).IsKAry k) ∧
      (∀ {l l' : I} {f : Ω l ≃ Ω l'}, f ∈ D.morC l l' →
        (D.guideStruct l).map (f : Ω l → Ω l') = D.guideStruct l') ∧
      (D.morC i j = ∅ ∨
        (Fintype.card (Ω i) - k + 1 ≤ symDefect (D.guideStruct i).Aut ∧
          Fintype.card (Ω j) - k + 1 ≤ symDefect (D.guideStruct j).Aut)) := by
  refine ⟨D.isKAry_guideStruct, fun hf => D.guideStruct_map hf, ?_⟩
  by_cases hj : ∀ L : Set (Ω j), L.ncard = k → ¬ D.IsFullAt j L
  · exact Or.inr ⟨D.symDefect_guideStruct hk hkn hfull, D.symDefect_guideStruct hk hkn' hj⟩
  · push_neg at hj
    obtain ⟨L', hL', hfullL'⟩ := hj
    exact Or.inl (D.morC_eq_empty_of_full hfull hL' (by simpa using hfullL'))

end Babai
