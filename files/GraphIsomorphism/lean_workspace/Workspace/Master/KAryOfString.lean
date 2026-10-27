/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 15, line 4c: the edge-colored `t`-uniform hypergraph `H(x)` as a `t`-ary relational
structure, i.e. as an object of `Babai.KAryInputs`.
-/
import Workspace.Master.Hypergraph
import Workspace.Master.Versions
import Workspace.SplitOrJohnson.Main

/-!
# `H(x)` as an object of `KAryInputs`

> 4c. else (: now their relative symmetry defect is `≥ 1/2` :)
>     (: view these hypergraphs as `t`-ary relational structures :)
>     apply Extended Design Lemma (Theorem 9.2.3)

`Workspace/Master/Hypergraph.lean` has the string `x` read as an edge coloring
`Babai.hyperColoring` of the `t`-subsets of `Γ`.  This file is the parenthetical *"view
these hypergraphs as `t`-ary relational structures"*: the relational structure has one
relation per color `a`, namely the set of *injective* `t`-tuples whose underlying `t`-set
has color `a` (`Babai.relOfColoring`).  Its automorphism group is the automorphism group of
the edge coloring (`Babai.aut_relOfColoring`), so the paper's *"relative symmetry defect of
`H(x)`"* is the symmetry defect of the relational structure
(`Babai.structDefect_relOfColoring`).

`Babai.hyperInput` is the resulting object of `Babai.KAryInputs (Fin m) t α`, on the
underlying set `Set.univ`, and `Babai.hyperInput_iso` is the equivariance
`H(x^σ) = H(x)^{ϕ(σ)}` read as an isomorphism of that category.

This is piece (i) of Mismatch 2 in `Workspace/Master/DESIGN.md`.

## The admissibility hypotheses

`Babai.KAryInputs Ω k α` is the full subcategory of the `k`-ary relational structures on the
objects with *"`2 ≤ k ≤ n/4`"* and *"relative strong symmetry defect `> 1 - α`"*.  At line 4c
the three read:

* `2 ≤ t` is line 4b's test *"else (: `t ≥ 2` :)"*, the negation of line 4a's `t = 1`;
* `4t ≤ m` is Theorem 10.5.1 (a), `4t < m`, carried by `Babai.PrimitiveCaseId`;
* `1 - α < defect(H(x))` is line 4c's *"now their relative symmetry defect is `≥ 1/2`"*,
  which for the `α` of Theorem 9.2.3 (`3/4 ≤ α < 1`) is implied by `1/2 ≤ defect(H(x))`.

All three are now available from the tests of `Workspace/Master/Round.lean`:
`Babai.SmallDefect` is the defect bound of line 4b itself, so its negation is the defect
bound of line 4c (`Babai.largeDefectData_of_not_smallDefect`,
`Workspace/Master/Sec15.lean`).

The section "The test of line 4b" below is the other half of that change: it turns the
paper's test, *"relative symmetry defect of `H(x)` is `< 1/2`"*, into the data Cor. 12.0.10
consumes (`Babai.smallDefect_data`).
-/

universe u v

namespace Babai

open Equiv

/-! ### Transport of the symmetry defect along a bijection

Definition 2.3.13 is about a permutation group on a fixed set.  The category
`Babai.KAryStructures` puts its objects on a *subset* `s ⊆ Γ`, so the structure of line 4c
has to be moved from `Γ` to `↥(Set.univ : Set Γ)`; the symmetry defect has to come along.
Twins are transpositions, and a bijection carries transpositions to transpositions, so
nothing is lost. -/

section Transport

variable {Ω : Type*} {Ω' : Type*}

theorem permCongr_swap [DecidableEq Ω] [DecidableEq Ω'] (e : Ω ≃ Ω') (a b : Ω) :
    e.permCongr (Equiv.swap a b) = Equiv.swap (e a) (e b) := by
  ext z
  simp only [Equiv.permCongr_apply]
  rcases eq_or_ne z (e a) with rfl | ha
  · simp
  rcases eq_or_ne z (e b) with rfl | hb
  · simp
  have ha' : e.symm z ≠ a := fun h => ha (by rw [← h]; simp)
  have hb' : e.symm z ≠ b := fun h => hb (by rw [← h]; simp)
  rw [Equiv.swap_apply_of_ne_of_ne ha' hb', Equiv.apply_symm_apply,
    Equiv.swap_apply_of_ne_of_ne ha hb]

theorem mem_map_permCongrHom [DecidableEq Ω] [DecidableEq Ω'] (e : Ω ≃ Ω')
    (G : Subgroup (Equiv.Perm Ω)) (σ : Equiv.Perm Ω) :
    e.permCongr σ ∈ G.map e.permCongrHom.toMonoidHom ↔ σ ∈ G := by
  constructor
  · rintro ⟨τ, hτ, hEq⟩
    have : e.permCongr τ = e.permCongr σ := hEq
    rwa [(Equiv.permCongr e).injective this] at hτ
  · intro h
    exact ⟨σ, h, rfl⟩

/-- Twins transport along a bijection: `x, y` are twins for `G` exactly when `e x, e y` are
twins for the transported group. -/
theorem isTwinSet_map_permCongrHom [DecidableEq Ω] [DecidableEq Ω'] (e : Ω ≃ Ω')
    (G : Subgroup (Equiv.Perm Ω)) (Ψ : Set Ω) :
    IsTwinSet (G.map e.permCongrHom.toMonoidHom) (e '' Ψ) ↔ IsTwinSet G Ψ := by
  constructor
  · intro h x hx y hy hxy
    have hne : e x ≠ e y := fun hc => hxy (e.injective hc)
    have := (h (e x) ⟨x, hx, rfl⟩ (e y) ⟨y, hy, rfl⟩ hne).2
    rw [← permCongr_swap e x y, mem_map_permCongrHom] at this
    exact ⟨hxy, this⟩
  · rintro h _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hxy
    have hne : x ≠ y := fun hc => hxy (by rw [hc])
    refine ⟨hxy, ?_⟩
    rw [← permCongr_swap e x y, mem_map_permCongrHom]
    exact (h x hx y hy hne).2

/-- Definition 2.3.11: a single pair of twins transports along a bijection. -/
theorem isTwin_map_permCongrHom [DecidableEq Ω] [DecidableEq Ω'] (e : Ω ≃ Ω')
    (G : Subgroup (Equiv.Perm Ω)) (x y : Ω) :
    IsTwin (G.map e.permCongrHom.toMonoidHom) (e x) (e y) ↔ IsTwin G x y := by
  rw [IsTwin, IsTwin, ← permCongr_swap e x y, mem_map_permCongrHom, e.injective.ne_iff]

/-- Definition 2.3.11: the twin equivalence classes transport along a bijection. -/
theorem twinClass_map_permCongrHom [DecidableEq Ω] [DecidableEq Ω'] (e : Ω ≃ Ω')
    (G : Subgroup (Equiv.Perm Ω)) (x : Ω) :
    twinClass (G.map e.permCongrHom.toMonoidHom) (e x) = e '' twinClass G x := by
  ext z
  obtain ⟨y, rfl⟩ := e.surjective z
  simp only [twinClass, Set.mem_setOf_eq, TwinOrEq, isTwin_map_permCongrHom e G x y,
    e.injective.eq_iff]
  constructor
  · intro h; exact ⟨y, h, rfl⟩
  · rintro ⟨w, hw, hwe⟩
    rwa [e.injective hwe] at hw

open scoped Classical in
/-- Definition 2.3.13: the symmetricity is invariant under transport along a bijection. -/
theorem symmetricity_map_permCongrHom [Fintype Ω] [DecidableEq Ω] [Fintype Ω']
    [DecidableEq Ω'] (e : Ω ≃ Ω') (G : Subgroup (Equiv.Perm Ω)) :
    symmetricity (G.map e.permCongrHom.toMonoidHom) = symmetricity G := by
  refine le_antisymm (Finset.sup_le fun Ψ' hΨ' => ?_) (Finset.sup_le fun Ψ hΨ => ?_)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hΨ'
    have himg : (↑(Ψ'.map e.symm.toEmbedding) : Set Ω) = e.symm '' (↑Ψ' : Set Ω') := by
      simp [Finset.coe_map]
    have htw : IsTwinSet G (↑(Ψ'.map e.symm.toEmbedding) : Set Ω) := by
      rw [himg]
      refine (isTwinSet_map_permCongrHom e G (e.symm '' (↑Ψ' : Set Ω'))).1 ?_
      have : e '' (e.symm '' (↑Ψ' : Set Ω')) = (↑Ψ' : Set Ω') := by
        rw [← Set.image_comp]; simp
      rwa [this]
    have := le_symmetricity htw
    simpa using this
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hΨ
    have himg : (↑(Ψ.map e.toEmbedding) : Set Ω') = e '' (↑Ψ : Set Ω) := by
      simp [Finset.coe_map]
    have htw : IsTwinSet (G.map e.permCongrHom.toMonoidHom)
        (↑(Ψ.map e.toEmbedding) : Set Ω') := by
      rw [himg]; exact (isTwinSet_map_permCongrHom e G _).2 hΨ
    have := le_symmetricity htw
    simpa using this

/-- Definition 2.3.13: the relative symmetry defect is invariant under transport along a
bijection.  This is what lets the structure of line 4c live on `↥(Set.univ : Set Γ)` while
the paper's defect hypothesis is about `Γ`. -/
theorem defect_map_permCongrHom [Fintype Ω] [DecidableEq Ω] [Fintype Ω'] [DecidableEq Ω']
    (e : Ω ≃ Ω') (G : Subgroup (Equiv.Perm Ω)) :
    defect (G.map e.permCongrHom.toMonoidHom) = defect G := by
  have hcard : Fintype.card Ω' = Fintype.card Ω := (Fintype.card_congr e).symm
  rw [defect, defect, relSymmetricity, relSymmetricity,
    symmetricity_map_permCongrHom e G, hcard]

end Transport

/-! ### The automorphism group of a transported relational structure -/

section MapAut

variable {Ω : Type*} {Ω' : Type*}

theorem RelStructure.map_injective (e : Ω ≃ Ω') :
    Function.Injective fun X : RelStructure Ω => X.map (e : Ω → Ω') := by
  intro X Y h
  have := congrArg (fun Z : RelStructure Ω' => Z.map (e.symm : Ω' → Ω)) h
  simpa only [RelStructure.map_map, show ((e.symm : Ω' → Ω) ∘ (e : Ω → Ω')) = id from
    funext fun x => by simp, RelStructure.map_id] using this

/-- `Aut(X^e) = Aut(X)^e`: the automorphism group of a transported relational structure is
the transport of its automorphism group. -/
theorem RelStructure.aut_map_equiv [DecidableEq Ω] [DecidableEq Ω'] (X : RelStructure Ω)
    (e : Ω ≃ Ω') :
    (X.map (e : Ω → Ω')).Aut = X.Aut.map e.permCongrHom.toMonoidHom := by
  ext τ
  constructor
  · intro hτ
    refine ⟨e.permCongr.symm τ, ?_, ?_⟩
    · show X.map ((e.permCongr.symm τ : Equiv.Perm Ω) : Ω → Ω) = X
      refine RelStructure.map_injective e ?_
      show (X.map ((e.permCongr.symm τ : Equiv.Perm Ω) : Ω → Ω)).map (e : Ω → Ω')
        = X.map (e : Ω → Ω')
      rw [RelStructure.map_map]
      have hfun : ((e : Ω → Ω') ∘ ((e.permCongr.symm τ : Equiv.Perm Ω) : Ω → Ω))
          = ((τ : Ω' → Ω') ∘ (e : Ω → Ω')) := by
        funext z
        simp [Equiv.permCongr_symm_apply]
      rw [hfun, ← RelStructure.map_map]
      exact hτ
    · show e.permCongr (e.permCongr.symm τ) = τ
      exact e.permCongr.apply_symm_apply τ
  · rintro ⟨σ, hσ, rfl⟩
    show (X.map (e : Ω → Ω')).map ((e.permCongrHom.toMonoidHom σ : Equiv.Perm Ω') :
      Ω' → Ω') = X.map (e : Ω → Ω')
    have hval : ((e.permCongrHom.toMonoidHom σ : Equiv.Perm Ω') : Ω' → Ω')
        = ((e.permCongr σ : Equiv.Perm Ω') : Ω' → Ω') := rfl
    rw [hval, RelStructure.map_map]
    have hfun : (((e.permCongr σ : Equiv.Perm Ω') : Ω' → Ω') ∘ (e : Ω → Ω'))
        = ((e : Ω → Ω') ∘ ((σ : Equiv.Perm Ω) : Ω → Ω)) := by
      funext z; simp
    rw [hfun, ← RelStructure.map_map]
    exact congrArg (fun Z : RelStructure Ω => Z.map (e : Ω → Ω')) hσ

/-- Definition 2.3.16: the symmetry defect of a relational structure is invariant under
transport along a bijection. -/
theorem RelStructure.structDefect_map_equiv [Fintype Ω] [DecidableEq Ω] [Fintype Ω']
    [DecidableEq Ω'] (X : RelStructure Ω) (e : Ω ≃ Ω') :
    structDefect (X.map (e : Ω → Ω')) = structDefect X := by
  show defect (X.map (e : Ω → Ω')).Aut = defect X.Aut
  rw [X.aut_map_equiv e, defect_map_permCongrHom]

end MapAut

/-! ### An edge-colored `t`-uniform hypergraph as a `t`-ary relational structure -/

section ColorAut

variable {Γ : Type*} [DecidableEq Γ] {A : Type*} {t : ℕ}

/-- The `t`-set underlying a `t`-tuple: its set of entries.  It has `t` elements exactly
when the tuple is injective. -/
def edgeOf (v : Fin t → Γ) : Finset Γ := Finset.image v Finset.univ

theorem edgeOf_tupleMap {Γ' : Type*} [DecidableEq Γ'] (σ : Γ → Γ') (v : Fin t → Γ) :
    edgeOf (tupleMap σ v) = (edgeOf v).image σ := by
  rw [edgeOf, edgeOf, Finset.image_image]
  rfl

/-- §15, line 4b: `Aut(H)`, the automorphism group of the edge-colored `t`-uniform
hypergraph `H` on the vertex set `Γ`: the permutations of `Γ` that preserve the color of
every edge.  The paper's *"relative symmetry defect of `H(x)`"* is `defect` of this
group. -/
def colorAut (t : ℕ) (H : binom Γ t → A) : Subgroup (Equiv.Perm Γ) where
  carrier := {σ | ∀ s, H (tAction t σ s) = H s}
  one_mem' := by intro s; simp
  mul_mem' := by
    intro a b ha hb s
    have : tAction t (a * b) s = tAction t a (tAction t b s) := by
      rw [map_mul]; rfl
    rw [this, ha, hb]
  inv_mem' := by
    intro a ha s
    have := ha (tAction t a⁻¹ s)
    have hc : tAction t a (tAction t a⁻¹ s) = s := by
      have h1 : (tAction t a : Equiv.Perm (binom Γ t)) * tAction t a⁻¹ = 1 := by
        rw [← map_mul]; simp
      calc tAction t a (tAction t a⁻¹ s)
          = ((tAction t a : Equiv.Perm (binom Γ t)) * tAction t a⁻¹) s := rfl
        _ = s := by rw [h1]; rfl
    rw [hc] at this
    exact this.symm

theorem mem_colorAut {H : binom Γ t → A} {σ : Equiv.Perm Γ} :
    σ ∈ colorAut t H ↔ ∀ s, H (tAction t σ s) = H s := Iff.rfl

theorem tAction_inv_apply (σ : Equiv.Perm Γ) (s : binom Γ t) :
    tAction t σ⁻¹ (tAction t σ s) = s := by
  have h1 : (tAction t σ⁻¹ : Equiv.Perm (binom Γ t)) * tAction t σ = 1 := by
    rw [← map_mul]; simp
  calc tAction t σ⁻¹ (tAction t σ s)
      = ((tAction t σ⁻¹ : Equiv.Perm (binom Γ t)) * tAction t σ) s := rfl
    _ = s := by rw [h1]; rfl

theorem tAction_apply_inv (σ : Equiv.Perm Γ) (s : binom Γ t) :
    tAction t σ (tAction t σ⁻¹ s) = s := by
  simpa using tAction_inv_apply (t := t) σ⁻¹ s

theorem tAction_mul_apply (σ τ : Equiv.Perm Γ) (s : binom Γ t) :
    tAction t (σ * τ) s = tAction t σ (tAction t τ s) := by
  rw [map_mul]; rfl

/-- Conjugation: `Equiv.permCongr` on permutations of one set is `π σ π⁻¹`. -/
theorem permCongr_eq_conj (π σ : Equiv.Perm Γ) :
    (π : Γ ≃ Γ).permCongr σ = π * σ * π⁻¹ := rfl

/-- The automorphism group of a shifted edge coloring: `Aut(H^π) = π Aut(H) π⁻¹`.

(As in `Babai.relOfColoring_map`, the shift of a coloring by `π` is `H ∘ (π⁻¹)^{(t)}`.) -/
theorem mem_colorAut_smul {H : binom Γ t → A} {π τ : Equiv.Perm Γ} :
    τ ∈ colorAut t (fun s => H (tAction t π⁻¹ s)) ↔ π⁻¹ * τ * π ∈ colorAut t H := by
  simp only [mem_colorAut]
  constructor
  · intro h s
    have h1 := h (tAction t π s)
    rw [tAction_mul_apply, tAction_mul_apply, h1, tAction_inv_apply]
  · intro h s
    have h1 := h (tAction t π⁻¹ s)
    rwa [tAction_mul_apply, tAction_mul_apply, tAction_apply_inv] at h1

/-- The automorphism group of a shifted edge coloring, as a subgroup:
`Aut(H^π) = Aut(H)^π`. -/
theorem colorAut_smul (H : binom Γ t → A) (π : Equiv.Perm Γ) :
    colorAut t (fun s => H (tAction t π⁻¹ s))
      = (colorAut t H).map (Equiv.permCongrHom (π : Γ ≃ Γ)).toMonoidHom := by
  ext τ
  rw [mem_colorAut_smul]
  constructor
  · intro h
    refine ⟨π⁻¹ * τ * π, h, ?_⟩
    show (π : Γ ≃ Γ).permCongr (π⁻¹ * τ * π) = τ
    rw [permCongr_eq_conj]
    group
  · rintro ⟨σ, hσ, rfl⟩
    have hconj : π⁻¹ * ((π : Γ ≃ Γ).permCongr σ) * π = σ := by
      rw [permCongr_eq_conj]; group
    show π⁻¹ * (Equiv.permCongrHom (π : Γ ≃ Γ)).toMonoidHom σ * π ∈ colorAut t H
    rwa [show (Equiv.permCongrHom (π : Γ ≃ Γ)).toMonoidHom σ = (π : Γ ≃ Γ).permCongr σ from rfl,
      hconj]

end ColorAut

section RelOfColoring

variable {Γ : Type*} [DecidableEq Γ] {A : Type*} [Fintype A] [DecidableEq A] {t : ℕ}

/-- §15, line 4c: the relation of the color `a` — the injective `t`-tuples whose underlying
`t`-set has color `a` in the edge coloring `H`. -/
def hyperRel (t : ℕ) (H : binom Γ t → A) (a : A) : Set (Fin t → Γ) :=
  {v | ∃ h : (edgeOf v).card = t, H ⟨edgeOf v, h⟩ = a}

/-- §15, line 4c, *"view these hypergraphs as `t`-ary relational structures"*: the `t`-ary
relational structure with one relation per color. -/
def relOfColoring (t : ℕ) (H : binom Γ t → A) : RelStructure Γ where
  numRel := Fintype.card A
  arity _ := t
  rel i := hyperRel t H ((Fintype.equivFin A).symm i)

theorem relOfColoring_isKAry (H : binom Γ t → A) : (relOfColoring t H).IsKAry t :=
  fun _ => rfl

/-- The edge coloring can be read back off the relational structure, so `relOfColoring` is
injective.  (Every `t`-set has an injective enumeration.) -/
theorem relOfColoring_injective :
    Function.Injective (relOfColoring (Γ := Γ) (A := A) t) := by
  intro H H' hEq
  funext s
  -- an injective enumeration of `s`
  obtain ⟨s, hs⟩ := s
  set w : Fin t ≃ ↥(s : Finset Γ) :=
    (finCongr hs.symm).trans s.equivFin.symm with hw
  set v : Fin t → Γ := fun i => ((w i : ↥(s : Finset Γ)) : Γ) with hv
  have hedge : edgeOf v = s := by
    apply Finset.eq_of_subset_of_card_le
    · intro z hz
      simp only [edgeOf, Finset.mem_image, Finset.mem_univ, true_and] at hz
      obtain ⟨i, rfl⟩ := hz
      exact (w i).2
    · have hcard : (edgeOf v).card = t := by
        rw [edgeOf, Finset.card_image_of_injective _ ?_, Finset.card_univ, Fintype.card_fin]
        intro i j hij
        exact w.injective (Subtype.ext hij)
      omega
  have hcard : (edgeOf v).card = t := by rw [hedge]; exact hs
  have hmem : v ∈ hyperRel t H (H ⟨s, hs⟩) := ⟨hcard, by
    congr 1
    exact Subtype.ext hedge⟩
  -- transport membership across the equality of structures
  set i : Fin (Fintype.card A) := (Fintype.equivFin A) (H ⟨s, hs⟩) with hi
  have hsplit : (fun j : Fin (Fintype.card A) => hyperRel t H ((Fintype.equivFin A).symm j))
      = (fun j => hyperRel t H' ((Fintype.equivFin A).symm j)) := by
    have h := hEq
    simp only [relOfColoring, RelStructure.mk.injEq, heq_eq_eq, true_and] at h
    exact h
  have hH : (Fintype.equivFin A).symm i = H ⟨s, hs⟩ := by rw [hi]; simp
  have hmem' : v ∈ hyperRel t H' (H ⟨s, hs⟩) := by
    have h1 : v ∈ hyperRel t H ((Fintype.equivFin A).symm i) := by rw [hH]; exact hmem
    have h2 : v ∈ hyperRel t H' ((Fintype.equivFin A).symm i) := by
      rw [← congrFun hsplit i]; exact h1
    rwa [hH] at h2
  obtain ⟨h1, h2⟩ := hmem'
  have heq : (⟨edgeOf v, h1⟩ : binom Γ t) = ⟨s, hs⟩ := Subtype.ext hedge
  rw [← h2, heq]

/-- §15, line 4c: the structure moves with the coloring, `H^σ` giving `(relOfColoring H)^σ`.

(`RelStructure.map` is a *left* action while the paper's `X ↦ X^σ` is a right one, which is
why `σ⁻¹` appears on the coloring; see the module docstring of
`Workspace/Prelim/Structures.lean`.) -/
theorem relOfColoring_map (H : binom Γ t → A) (σ : Equiv.Perm Γ) :
    (relOfColoring t H).map ((σ : Equiv.Perm Γ) : Γ → Γ)
      = relOfColoring t (fun s => H (tAction t σ⁻¹ s)) := by
  have hrel : ∀ a : A, mapRel (σ : Γ → Γ) (hyperRel t H a)
      = hyperRel t (fun s => H (tAction t σ⁻¹ s)) a := by
    intro a
    ext w
    constructor
    · rintro ⟨v, ⟨hv, hcol⟩, rfl⟩
      have he : edgeOf (tupleMap (σ : Γ → Γ) v) = (edgeOf v).image σ :=
        edgeOf_tupleMap _ v
      have hc : (edgeOf (tupleMap (σ : Γ → Γ) v)).card = t := by
        rw [he, Finset.card_image_of_injective _ σ.injective]; exact hv
      refine ⟨hc, ?_⟩
      have heq : tAction t σ⁻¹ (⟨edgeOf (tupleMap (σ : Γ → Γ) v), hc⟩ : binom Γ t)
          = ⟨edgeOf v, hv⟩ := by
        refine Subtype.ext ?_
        rw [tAction_apply_coe]
        show (edgeOf (tupleMap (σ : Γ → Γ) v)).image ((σ⁻¹ : Equiv.Perm Γ) : Γ → Γ)
          = edgeOf v
        rw [he, Finset.image_image]
        simp
      show H (tAction t σ⁻¹ (⟨edgeOf (tupleMap (σ : Γ → Γ) v), hc⟩ : binom Γ t)) = a
      rw [heq]
      exact hcol
    · rintro ⟨hw, hcol⟩
      have hc2 : (edgeOf (tupleMap ((σ⁻¹ : Equiv.Perm Γ) : Γ → Γ) w)).card = t := by
        rw [edgeOf_tupleMap, Finset.card_image_of_injective _ (σ⁻¹ : Equiv.Perm Γ).injective]
        exact hw
      refine ⟨tupleMap ((σ⁻¹ : Equiv.Perm Γ) : Γ → Γ) w, ⟨hc2, ?_⟩, ?_⟩
      · have heq : (⟨edgeOf (tupleMap ((σ⁻¹ : Equiv.Perm Γ) : Γ → Γ) w), hc2⟩ : binom Γ t)
            = tAction t σ⁻¹ ⟨edgeOf w, hw⟩ := by
          refine Subtype.ext ?_
          rw [tAction_apply_coe]
          exact edgeOf_tupleMap _ w
        rw [heq]
        exact hcol
      · funext i
        simp [tupleMap]
  simp only [RelStructure.map, relOfColoring, RelStructure.mk.injEq, heq_eq_eq, true_and]
  funext i
  exact hrel _

/-- §15, line 4c: the automorphism group of the relational structure is the automorphism
group of the edge coloring.  This is what makes *"the relative symmetry defect of `H(x)`"*
the symmetry defect of the structure the Extended Design Lemma is applied to. -/
theorem aut_relOfColoring (H : binom Γ t → A) :
    (relOfColoring t H).Aut = colorAut t H := by
  ext σ
  rw [RelStructure.mem_Aut, relOfColoring_map, mem_colorAut]
  constructor
  · intro h
    have hH : (fun s => H (tAction t σ⁻¹ s)) = H := relOfColoring_injective h
    intro s
    have h2 := congrFun hH (tAction t σ s)
    rw [tAction_inv_apply] at h2
    exact h2.symm
  · intro h
    refine congrArg _ ?_
    funext s
    have h2 := h (tAction t σ⁻¹ s)
    rw [tAction_apply_inv] at h2
    exact h2.symm

/-- Definition 2.3.16 for the structure of line 4c: its symmetry defect is the paper's
*"relative symmetry defect of `H(x)`"*. -/
theorem structDefect_relOfColoring [Fintype Γ] (H : binom Γ t → A) :
    structDefect (relOfColoring t H) = defect (colorAut t H) := by
  show defect (relOfColoring t H).Aut = _
  rw [aut_relOfColoring]

end RelOfColoring

/-! ### The test of line 4b: a small symmetry defect marks one twin class

> 4b. else (: `t ≥ 2` :) view `x, y` as edge-colored `t`-uniform hypergraphs `H(x)` and
>     `H(y)` on vertex set `Γ`
>     if relative symmetry defect of `H(x)` is `< 1/2` then apply Cor. 12.0.10

The test is a statement about `H(x)` alone; what Cor. 12.0.10 consumes is a *canonically
defined* set `C ⊆ Γ` of more than `m/2` vertices on which `Aut_G(x)` induces at least the
alternating group.  This section is the passage from the one to the other.

A relative symmetry defect below `1/2` says that the symmetricity of `Aut(H(x))` exceeds
`m/2`, so some twin class `C` of `Aut(H(x))` has more than `m/2` vertices, and it is the
only class that large.  So marking the classes of more than `m/2` vertices
(`Babai.bigTwinColoring`) is a canonical two-coloring of `Γ` whose class of the color
`true` is exactly `C`.  On `C` the whole symmetric group `S(C)` preserves the coloring
`H(x)`, so every `α ∈ A(Γ)` supported in `C` does; `ϕ` is a giant representation, so
`α = ϕ(g)` for some `g` in the window group, and in the primitive case `ϕ(g)` preserving
`H(x)` means `x^g = x`.  So `α` itself is the automorphism Cor. 12.0.10 asks for. -/

section Line4bTest

variable {Ω : Type*} {A : Type*} [Fintype Ω] [DecidableEq Ω] {m : ℕ}
  {G : Subgroup (Equiv.Perm Ω)} {ϕ : G →* Equiv.Perm (Fin m)} {t : ℕ}

/-- Observation 2.3.10: the twin class of a member of a twin class is that class. -/
theorem twinClass_eq_of_mem {Λ : Type*} [DecidableEq Λ] {K : Subgroup (Equiv.Perm Λ)}
    {γ δ : Λ} (h : δ ∈ twinClass K γ) : twinClass K δ = twinClass K γ := by
  have he := twinOrEq_equivalence K
  ext z
  show TwinOrEq K δ z ↔ TwinOrEq K γ z
  exact ⟨fun hz => he.trans h hz, fun hz => he.trans (he.symm h) hz⟩

/-- Definition 2.3.13 and line 4b: **a relative symmetry defect below `1/2` produces a twin
class of more than half of the points**.

*Proof.*  If every twin class had at most `m/2` points then so would every set of twins
(Observation 2.3.12), so the symmetricity would be at most `m/2` and the defect at least
`1/2`. -/
theorem exists_dominant_twinClass {K : Subgroup (Equiv.Perm (Fin m))}
    (h : defect K < 1 / 2) : ∃ γ₀ : Fin m, m < 2 * (twinClass K γ₀).ncard := by
  have hcard : Fintype.card (Fin m) = m := Fintype.card_fin m
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with rfl | hpos
    · exfalso
      have hs : symmetricity K = 0 := by
        have := symmetricity_le_card K
        rw [hcard] at this
        omega
      rw [defect, relSymmetricity, hs, hcard] at h
      norm_num at h
    · exact hpos
  have hmq : (0 : ℚ) < (m : ℚ) := by exact_mod_cast hm
  have hs : m < 2 * symmetricity K := by
    rw [defect, relSymmetricity, hcard] at h
    have hhalf : (1 : ℚ) / 2 < (symmetricity K : ℚ) / (m : ℚ) := by linarith
    have hmul := mul_lt_mul_of_pos_right hhalf hmq
    rw [div_mul_cancel₀ _ (ne_of_gt hmq)] at hmul
    have : (m : ℚ) < 2 * (symmetricity K : ℚ) := by linarith
    exact_mod_cast this
  by_contra hcon
  push_neg at hcon
  have hbound : ∀ Ψ : Finset (Fin m), IsTwinSet K (↑Ψ : Set (Fin m)) →
      2 * Ψ.card ≤ Fintype.card (Fin m) := by
    intro Ψ hΨ
    rcases Finset.eq_empty_or_nonempty Ψ with rfl | ⟨γ, hγ⟩
    · simp
    · have hγ' : γ ∈ (↑Ψ : Set (Fin m)) := hγ
      have hsub : (↑Ψ : Set (Fin m)) ⊆ twinClass K γ := hΨ.subset_twinClass hγ'
      have hle : Ψ.card ≤ (twinClass K γ).ncard := by
        rw [← Set.ncard_coe_finset Ψ]
        exact Set.ncard_le_ncard hsub (Set.toFinite _)
      have := hcon γ
      omega
  have hfin := two_mul_symmetricity_le hbound
  rw [hcard] at hfin
  omega

open scoped Classical in
/-- §15, line 4b: **the canonical two-coloring of `Γ` that marks the dominant twin class**:
a vertex has the color `true` when its twin class in `Aut(H(z))` has more than `m/2`
vertices. -/
noncomputable def bigTwinColoring (id : PrimitiveCaseId ϕ t) (z : Ω → A) (γ : Fin m) :
    Bool :=
  decide (m < 2 * (twinClass (colorAut t (hyperColoring id z)) γ).ncard)

open scoped Classical in
theorem bigTwinColoring_eq_true {id : PrimitiveCaseId ϕ t} {z : Ω → A} {γ : Fin m} :
    bigTwinColoring id z γ = true ↔
      m < 2 * (twinClass (colorAut t (hyperColoring id z)) γ).ncard := by
  rw [bigTwinColoring, decide_eq_true_eq]

/-- The edge coloring of a shifted string, as a shift of the edge coloring:
`H(z^σ) = H(z) ∘ ((σ^ϕ)⁻¹)^{(t)}`. -/
theorem hyperColoring_strAct_eq (id : PrimitiveCaseId ϕ t) (z : Ω → A) (σ : G) :
    hyperColoring id (strAct z (σ : Equiv.Perm Ω))
      = fun s => hyperColoring id z (tAction t (ϕ σ)⁻¹ s) := by
  funext s
  have h := hyperColoring_strAct id z σ (tAction t (ϕ σ)⁻¹ s)
  rwa [tAction_apply_inv] at h

/-- §15, line 4b: **the two-coloring is canonical** — a `G`-shift of the string shifts it by
the corresponding permutation of `Γ`.  This is the hypothesis `hcol` of Cor. 12.0.10. -/
theorem isCanonicalColoring_bigTwinColoring (id : PrimitiveCaseId ϕ t) :
    IsCanonicalColoring ϕ (bigTwinColoring (A := A) id) := by
  classical
  intro z σ γ
  rw [bigTwinColoring, bigTwinColoring, hyperColoring_strAct_eq id z σ, colorAut_smul,
    twinClass_map_permCongrHom, Set.ncard_image_of_injective _ (ϕ σ).injective]

/-- §15, line 4b: **the marked class is the dominant twin class**.  Two twin classes of more
than `m/2` vertices would be disjoint and together have more than `m` vertices, so there is
only one. -/
theorem colorClass_bigTwinColoring (id : PrimitiveCaseId ϕ t) (x : Ω → A) {γ₀ : Fin m}
    (h : m < 2 * (twinClass (colorAut t (hyperColoring id x)) γ₀).ncard) :
    colorClass (bigTwinColoring id) x true
      = twinClass (colorAut t (hyperColoring id x)) γ₀ := by
  classical
  ext δ
  show bigTwinColoring id x δ = true ↔ _
  rw [bigTwinColoring_eq_true]
  set K := colorAut t (hyperColoring id x) with hK
  constructor
  · intro hδ
    by_contra hmem
    have hdisj : Disjoint (twinClass K δ) (twinClass K γ₀) := by
      rw [Set.disjoint_left]
      intro z hz hz'
      refine hmem ?_
      have h1 : twinClass K z = twinClass K δ := twinClass_eq_of_mem hz
      have h2 : twinClass K z = twinClass K γ₀ := twinClass_eq_of_mem hz'
      have hδδ : δ ∈ twinClass K δ := Or.inl rfl
      rw [← h1, h2] at hδδ
      exact hδδ
    have hun := Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _)
    have hle : (twinClass K δ ∪ twinClass K γ₀).ncard ≤ m := by
      have hsub := Set.ncard_le_ncard
        (Set.subset_univ (twinClass K δ ∪ twinClass K γ₀)) Set.finite_univ
      rwa [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] at hsub
    omega
  · intro hδ
    rw [twinClass_eq_of_mem hδ]
    exact h

/-- The string is read back off its edge coloring: the color of the label of `u` is the
letter at `u`. -/
theorem hyperColoring_label (id : PrimitiveCaseId ϕ t) (z : Ω → A) (u : Ω) :
    hyperColoring id z (id.label u) = z u := by
  rw [hyperColoring, Equiv.symm_apply_apply]

/-- §15, line 4b, **the primitive case**: if `σ^ϕ` preserves the edge coloring `H(x)` then
`σ` is an automorphism of `x`.  In the primitive case the string *is* its edge coloring
(`Ω = Φ = Γ^{(t)}`), so there is nothing left for `σ` to move. -/
theorem strAct_eq_of_mem_colorAut (id : PrimitiveCaseId ϕ t) (x : Ω → A) (g : G)
    (h : ϕ g ∈ colorAut t (hyperColoring id x)) :
    strAct x (g : Equiv.Perm Ω) = x := by
  have hH : hyperColoring id (strAct x (g : Equiv.Perm Ω)) = hyperColoring id x := by
    rw [hyperColoring_strAct_eq id x g]
    funext s
    exact mem_colorAut.1 ((colorAut t (hyperColoring id x)).inv_mem h) s
  funext u
  rw [← hyperColoring_label id (strAct x (g : Equiv.Perm Ω)) u, hH, hyperColoring_label]

/-- §15, line 4b, **the hypothesis `hgiantC` of Cor. 12.0.10**: on a set of twins of
`Aut(H(x))` the automorphisms of `x` induce every even permutation.

*Proof.*  A set of twins carries the whole symmetric group (Observation 2.3.12), so an `α`
supported in `C` preserves `H(x)`.  Being even, it is `ϕ(g)` for some `g` in the window
group (`ϕ` is a giant representation), and then `x^g = x`
(`Babai.strAct_eq_of_mem_colorAut`), so `α` itself lies in `Aut_G(x)^ϕ`. -/
theorem exists_mem_homImage_of_isTwinSet (id : PrimitiveCaseId ϕ t) (hϕ : IsGiantRep ϕ)
    (x : Ω → A) {C : Set (Fin m)} (hC : IsTwinSet (colorAut t (hyperColoring id x)) C)
    (α : Equiv.Perm (Fin m)) (hα : α ∈ alternatingGroup (Fin m))
    (hfix : ∀ γ, γ ∉ C → α γ = γ) :
    ∃ β ∈ homImage ϕ (strAut (G : Set (Equiv.Perm Ω)) x), ∀ γ ∈ C, β γ = α γ := by
  have hsym : α ∈ colorAut t (hyperColoring id x) :=
    (isTwinSet_iff_symOn_le _ C).1 hC (mem_symOn.2 hfix)
  obtain ⟨g, hg⟩ := hϕ hα
  refine ⟨α, ⟨(g : Equiv.Perm Ω), ⟨g.2, ?_⟩, g.2, ?_⟩, fun γ _ => rfl⟩
  · refine strAct_eq_of_mem_colorAut id x g ?_
    rw [hg]; exact hsym
  · show ϕ g = α
    exact hg

/-- §15, **line 4b**: *"if relative symmetry defect of `H(x)` is `< 1/2`"* produces the data
Cor. 12.0.10 consumes — a canonical two-coloring of `Γ` whose class of the color `true` has
more than `m/2` vertices and carries every even permutation of `Γ` supported in it. -/
theorem smallDefect_data (id : PrimitiveCaseId ϕ t) (hϕ : IsGiantRep ϕ) (x : Ω → A)
    (hd : defect (colorAut t (hyperColoring id x)) < 1 / 2) :
    IsCanonicalColoring ϕ (bigTwinColoring (A := A) id) ∧
      m < 2 * (colorClass (bigTwinColoring id) x true).ncard ∧
      ∀ α : Equiv.Perm (Fin m), α ∈ alternatingGroup (Fin m) →
        (∀ γ, γ ∉ colorClass (bigTwinColoring id) x true → α γ = γ) →
        ∃ β ∈ homImage ϕ (strAut (G : Set (Equiv.Perm Ω)) x),
          ∀ γ ∈ colorClass (bigTwinColoring id) x true, β γ = α γ := by
  obtain ⟨γ₀, hγ₀⟩ := exists_dominant_twinClass hd
  have hcol : colorClass (bigTwinColoring id) x true
      = twinClass (colorAut t (hyperColoring id x)) γ₀ :=
    colorClass_bigTwinColoring id x hγ₀
  refine ⟨isCanonicalColoring_bigTwinColoring id, ?_, ?_⟩
  · rw [hcol]; exact hγ₀
  · intro α hα hfix
    refine exists_mem_homImage_of_isTwinSet id hϕ x ?_ α hα hfix
    rw [hcol]
    exact twinClass_isTwinSet _ γ₀

end Line4bTest

/-! ### The admissible input of line 4c -/

section LargeDefect

variable {Ω : Type*} {A : Type*} [Fintype Ω] [DecidableEq Ω] {m : ℕ}
  {G : Subgroup (Equiv.Perm Ω)} {ϕ : G →* Equiv.Perm (Fin m)} {t : ℕ}

/-- §15, line 4c: what the Extended Design Lemma asks of its input, at line 4c.

* `t_two` is *"else (: `t ≥ 2` :)"* of line 4b, the negation of line 4a's test;
* `four_t` is Theorem 10.5.1 (a), `4t < m`;
* `large_defect` is line 4c's *"now their relative symmetry defect is `≥ 1/2`"*, in the form
  Theorem 9.2.3 asks for it: *"relative symmetry defect `> 1 - α`"*. -/
structure LargeDefectData (id : PrimitiveCaseId ϕ t) (x : Ω → A) (α : ℝ) : Prop where
  /-- Line 4b: `t ≥ 2`. -/
  t_two : 2 ≤ t
  /-- Theorem 10.5.1 (a): `4t < m`. -/
  four_t : 4 * t ≤ m
  /-- Line 4c: *"relative symmetry defect `≥ 1/2`"*, in the form of Theorem 9.2.3. -/
  large_defect : (1 : ℝ) - α < (defect (colorAut t (hyperColoring id x)) : ℝ)

end LargeDefect

/-! ### `H(x)` as an object of `KAryInputs` -/

section HyperInput

variable {Ω : Type u} {A : Type v} [Fintype Ω] [DecidableEq Ω] [Fintype A] [DecidableEq A]
  {m : ℕ} {G : Subgroup (Equiv.Perm Ω)} {ϕ : G →* Equiv.Perm (Fin m)} {t : ℕ}

/-- `Γ ≃ ↥(Set.univ : Set Γ)`: the objects of `Babai.KAryStructures` live on a subset of the
ambient type, and the structure of line 4c lives on all of `Γ`. -/
def univEquiv (Γ : Type*) : Γ ≃ ↥(Set.univ : Set Γ) := (Equiv.Set.univ Γ).symm

/-- §15, line 4c: the string `x`, read as an edge-colored `t`-uniform hypergraph on `Γ` and
then as a `t`-ary relational structure, on the underlying set `Set.univ`. -/
def hyperStructure (id : PrimitiveCaseId ϕ t) (x : Ω → A) :
    RelStructure ↥(Set.univ : Set (Fin m)) :=
  (relOfColoring t (hyperColoring id x)).map ((univEquiv (Fin m)) : Fin m → _)

theorem hyperStructure_isKAry (id : PrimitiveCaseId ϕ t) (x : Ω → A) :
    (hyperStructure id x).IsKAry t := fun _ => rfl

/-- §15, line 4c: `H(x)` as an object of the category of `t`-ary relational structures. -/
def hyperPt (id : PrimitiveCaseId ϕ t) (x : Ω → A) : Pt (KAryStructures (Fin m) t) :=
  ⟨Set.univ, ⟨hyperStructure id x, hyperStructure_isKAry id x⟩⟩

@[simp] theorem hyperPt_car (id : PrimitiveCaseId ϕ t) (x : Ω → A) :
    (hyperPt id x).car = Set.univ := rfl

/-- §15, lines 4b–4c: **`H(x^σ) = H(x)^{ϕ(σ)}` as an isomorphism of `t`-ary relational
structures**.  This is `Babai.hyperColoring_strAct` read in the category
`Babai.KAryStructures`, which is where Theorem 9.2.3 asks for it. -/
theorem hyperPt_iso (id : PrimitiveCaseId ϕ t) (x : Ω → A) (σ : G)
    (h : (hyperPt id (strAct x (σ : Equiv.Perm Ω))).car = (ϕ σ) '' (hyperPt id x).car) :
    permHom (ϕ σ) (hyperPt id x) (hyperPt id (strAct x (σ : Equiv.Perm Ω))) h ∈
      (KAryStructures (Fin m) t).IsoP (hyperPt id x)
        (hyperPt id (strAct x (σ : Equiv.Perm Ω))) := by
  show (hyperStructure id x).map
      ((permHom (ϕ σ) (hyperPt id x) (hyperPt id (strAct x (σ : Equiv.Perm Ω))) h :
        ↥(hyperPt id x).car ≃ _) : ↥(hyperPt id x).car → _)
    = hyperStructure id (strAct x (σ : Equiv.Perm Ω))
  set e : Fin m ≃ ↥(Set.univ : Set (Fin m)) := univEquiv (Fin m) with he
  set R := relOfColoring t (hyperColoring id x) with hR
  set R' := relOfColoring t (hyperColoring id (strAct x (σ : Equiv.Perm Ω))) with hR'
  -- the coloring identity `H(x^σ) = H(x) ∘ (ϕ σ)⁻¹`
  have hcol : (fun s => hyperColoring id x (tAction t (ϕ σ)⁻¹ s))
      = hyperColoring id (strAct x (σ : Equiv.Perm Ω)) := by
    funext s
    have hstr := hyperColoring_strAct id x σ (tAction t (ϕ σ)⁻¹ s)
    rw [tAction_apply_inv] at hstr
    exact hstr.symm
  -- the induced bijection of `↥univ` is `permCongr e (ϕ σ)`
  have hperm : ((permHom (ϕ σ) (hyperPt id x) (hyperPt id (strAct x (σ : Equiv.Perm Ω))) h :
      ↥(hyperPt id x).car ≃ _) : ↥(hyperPt id x).car → _)
      = ((e.permCongr (ϕ σ) : Equiv.Perm ↥(Set.univ : Set (Fin m))) :
        ↥(Set.univ : Set (Fin m)) → ↥(Set.univ : Set (Fin m))) := by
    funext z
    refine Subtype.ext ?_
    rw [permHom_apply]
    rfl
  show (R.map (e : Fin m → _)).map _ = R'.map (e : Fin m → _)
  rw [hperm, RelStructure.map_map]
  have hfun : (((e.permCongr (ϕ σ) : Equiv.Perm ↥(Set.univ : Set (Fin m))) :
      ↥(Set.univ : Set (Fin m)) → ↥(Set.univ : Set (Fin m))) ∘ (e : Fin m → _))
      = ((e : Fin m → _) ∘ ((ϕ σ : Equiv.Perm (Fin m)) : Fin m → Fin m)) := by
    funext z; simp [he, univEquiv]
  rw [hfun, ← RelStructure.map_map, hR, relOfColoring_map, hcol]

/-- The underlying set does not move: both structures live on all of `Γ`. -/
theorem hyperPt_car_smul (id : PrimitiveCaseId ϕ t) (x : Ω → A) (σ : G) :
    (hyperPt id (strAct x (σ : Equiv.Perm Ω))).car = (ϕ σ) '' (hyperPt id x).car := by
  simp [hyperPt_car, Set.image_univ, Equiv.range_eq_univ]

/-- §15, line 4c: **the assignment `x ↦ H(x)` is canonical** in the sense of
`Babai.IsCanonicalObj`, for the category of `t`-ary relational structures.  Together with
`Babai.exists_canonicalVersions` this is what turns Theorem 9.2.3 into the canonical
versions that `Workspace/Master/Bridge.lean` consumes. -/
theorem isCanonicalObj_hyperPt (id : PrimitiveCaseId ϕ t) :
    IsCanonicalObj ϕ (hyperPt (A := A) id) where
  car := hyperPt_car_smul id
  iso x σ := hyperPt_iso id x σ (hyperPt_car_smul id x σ)

/-- §15, line 4c: the symmetry defect of the relational structure is the paper's
*"relative symmetry defect of `H(x)`"*, the defect of the automorphism group of the
edge-colored hypergraph.  (The structure lives on `↥(Set.univ : Set Γ)` and the coloring on
`Γ`; `Babai.RelStructure.structDefect_map_equiv` is what bridges the two.) -/
theorem structDefect_hyperStructure (id : PrimitiveCaseId ϕ t) (x : Ω → A) :
    letI : Fintype ↥(Set.univ : Set (Fin m)) := Fintype.ofFinite _
    letI : DecidableEq ↥(Set.univ : Set (Fin m)) := Classical.decEq _
    structDefect (hyperStructure id x) = defect (colorAut t (hyperColoring id x)) := by
  letI : Fintype ↥(Set.univ : Set (Fin m)) := Fintype.ofFinite _
  letI : DecidableEq ↥(Set.univ : Set (Fin m)) := Classical.decEq _
  rw [hyperStructure, RelStructure.structDefect_map_equiv, structDefect_relOfColoring]

/-- §15, line 4c: **`H(x)` as an admissible input of Theorem 9.2.3**. -/
def hyperInput (id : PrimitiveCaseId ϕ t) {x : Ω → A} {α : ℝ}
    (hx : LargeDefectData id x α) : Pt (KAryInputs (Fin m) t α) := by
  refine ⟨Set.univ, ⟨⟨hyperStructure id x, hyperStructure_isKAry id x⟩, ?_⟩⟩
  letI : Fintype ↥(Set.univ : Set (Fin m)) := Fintype.ofFinite _
  letI : DecidableEq ↥(Set.univ : Set (Fin m)) := Classical.decEq _
  refine ⟨hx.t_two, ?_, ?_⟩
  · rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]
    exact hx.four_t
  · rw [structDefect_hyperStructure]
    exact hx.large_defect

@[simp] theorem hyperInput_car (id : PrimitiveCaseId ϕ t) {x : Ω → A} {α : ℝ}
    (hx : LargeDefectData id x α) : (hyperInput id hx).car = Set.univ := rfl

end HyperInput

end Babai
