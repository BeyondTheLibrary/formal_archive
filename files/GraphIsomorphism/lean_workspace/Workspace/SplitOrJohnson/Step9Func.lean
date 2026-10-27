/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 9.4, step 9: the branch conditions of the three cases, and the three functors from
the instance that step 8 leaves into the input categories of Sections 9.6, 9.7 and 9.8.
-/
import Workspace.SplitOrJohnson.Step9Functors
import Workspace.SplitOrJohnson.Step9

/-!
# §9.4, step 9: the branch conditions and the three functors

Version 2.5, lines 4166-4172 of `babai-gi-source/quasi25.txt`.

> *"9. We need to consider the following cases: (i) `X₂` is imprimitive: Section 9.6;
> (ii) `X₂` is the clique configuration; we refer to this as the 'block design case',
> Section 9.7; (iii) `X₂` is uniprimitive: Section 9.8."*

## The two branch conditions

`Babai.FindsAtMultCost.cases` asks for a branch condition that is a **function of the
object** and invariant under isomorphism.  Both conditions are therefore read off the
coloring `Babai.step8CaseColor` on the blocks — `Babai.step9BlkColor` — and never off a
configuration chosen from an existential; then invariance is `Babai.step8CaseColor_map`
alone.  This is the same device as step 6 (`Babai.Step6Imprimitive`).

* `Babai.Step9Imprimitive`, case (i): *some off-diagonal color of `X₂` is disconnected*.
  Since `X₂` is homogeneous (`Babai.step8_induced₂_isHomogeneous`), this is Def. 3.2.1 for
  `X₂`: `Babai.step9Imprimitive_iff`.
* `Babai.Step9Clique`, case (ii): *all ordered pairs of distinct blocks get the same
  color*.  This is the clique configuration (Def. 3.1.8), that is rank `≤ 2`:
  `Babai.step9Clique_iff_rank_le_two`.  With `Babai.two_le_step8_numBlocks` the rank is
  then exactly `2`.
* Case (iii) is the negation of both; `Babai.step8_induced₂_trichotomy` turns it into
  uniprimitivity.

## The three functors

The object is the same in the three cases — the point set `W₁ ∪ D_j`
(`Babai.step7Set`), the first part and the blocks of the graph `(V₁, V₂; R_i)` of step 8,
and the coloring `Babai.step8CaseColor` — and only the `Case` heading differs; those are
`Babai.step8_isImprimitiveCaseOn`, `Babai.step8_isBlockDesignCaseOn` and
`Babai.step8_isUPCCCaseOn`.  The morphisms are the restriction `Babai.step7Equiv` of a
morphism of the inputs, and the functor is a canonical embedding because
`Babai.step7Set_subset` and `Babai.step7Equiv` is that restriction.

| Paper | Lean |
|---|---|
| §9.4, step 9(i), the branch condition | `Babai.Step9Imprimitive` |
| §9.4, step 9(ii), the branch condition | `Babai.Step9Clique` |
| §9.4, step 9(i), the functor into §9.6 | `Babai.step9ImpFunc` |
| §9.4, step 9(ii), the functor into §9.7 | `Babai.step9DesignFunc` |
| §9.4, step 9(iii), the functor into §9.8 | `Babai.step9UPCCFunc` |
-/

namespace Babai

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

open VColBipBlk

/-! ### The coloring of `X₂` on the blocks -/

section BlkColor

variable (X : Pt (BipBlockInputs Ω))

/-- §9.4, step 9.  **The coloring of `X₂`**: the coloring `Babai.step8CaseColor` that the
object of step 8 carries, read on the blocks alone.  The two branch conditions of step 9
are conditions on this coloring, which is what makes them functions of the object. -/
noncomputable def step9BlkColor (u v : ↥(step8Blks X)) : ℕ :=
  step8CaseColor X ((u : ↥((step8Obj X).vtx)) : Set ↥(step7Set X))
    ((v : ↥((step8Obj X).vtx)) : Set ↥(step7Set X))

/-- §9.4, step 9.  The coloring of the blocks has the same color classes as the coloring of
the induced configuration `X₂`.  This is what lets Def. 3.2.1 be read off it. -/
theorem sameKernel_step9BlkColor [Fintype ↥((step8Obj X).vtx)] [Fintype ↥(step8Blks X)] :
    SameKernel (step9BlkColor X) ((step8Config X).induced (step8Blks X)).natColor := by
  intro a b a' b'
  show step8CaseColor X _ _ = step8CaseColor X _ _ ↔ _
  rw [step8CaseColor_vtx, step8CaseColor_vtx]
  exact ((step8Config X).natColor_induced_eq_iff (step8Blks X) a b a' b').symm

end BlkColor

/-! ### The branch condition of case (i): `X₂` is imprimitive -/

/-- §9.4, step 9(i).  **The branch condition**: *"`X₂` is imprimitive"*, read off the
coloring of `X₂` as *"some off-diagonal color of `X₂` is disconnected"*, exactly as step 6
reads the imprimitivity of `X₁` (`Babai.Step6Imprimitive`). -/
noncomputable def Step9Imprimitive (X : Pt (BipBlockInputs Ω)) : Prop :=
  ∃ k, IsDisconnectedColor (step9BlkColor X) k

/-- §9.4, step 9(i).  The branch condition is Definition 3.2.1 for `X₂`, which is
homogeneous (`Babai.step8_induced₂_isHomogeneous`). -/
theorem step9Imprimitive_iff (X : Pt (BipBlockInputs Ω))
    [Fintype ↥((step8Obj X).vtx)] [Fintype ↥(step8Blks X)] :
    Step9Imprimitive X ↔ ¬ ((step8Config X).induced (step8Blks X)).IsPrimitive := by
  letI : Finite ↥(step8Blks X) := Finite.of_fintype _
  exact (exists_isDisconnectedColor_congr (sameKernel_step9BlkColor X)).trans
    (exists_isDisconnectedColor_iff_not_isPrimitive
      (step8_induced₂_isHomogeneous X (S := step8Blks X) rfl))

/-! ### The branch condition of case (ii): `X₂` is the clique configuration -/

/-- §9.4, step 9(ii).  **The branch condition**: *"`X₂` is the clique configuration"*, read
off the coloring of `X₂` as *"all ordered pairs of distinct blocks get the same color"*.
This is Definition 3.1.8 for `X₂`, that is rank `≤ 2`
(`Babai.step9Clique_iff_rank_le_two`). -/
def Step9Clique (X : Pt (BipBlockInputs Ω)) : Prop :=
  ∀ u v u' v' : ↥(step8Blks X), u ≠ v → u' ≠ v' →
    step9BlkColor X u v = step9BlkColor X u' v'

/-- Definition 3.1.8 read off the coloring: **a homogeneous configuration is the clique
configuration — rank `≤ 2` — exactly when all ordered pairs of distinct vertices get the
same color.**

One direction counts three colors: the diagonal color, and two different off-diagonal
colors; a diagonal color is never an off-diagonal one, by axiom (i) of Def. 3.1.2.  The
other direction is that every color occurs (Def. 3.1.1), so the colors are among the
common diagonal color and the common off-diagonal one. -/
theorem rank_le_two_iff_color_const {T : Type*} [Fintype T] (P : PartitionStructure T)
    (hcfg : P.IsConfiguration) (hhom : P.IsHomogeneous) :
    P.rank ≤ 2 ↔ ∀ u v u' v' : T, u ≠ v → u' ≠ v' → P.color u v = P.color u' v' := by
  classical
  constructor
  · intro hr u v u' v' huv hu'v'
    by_contra hne
    have hd1 : P.color u u ≠ P.color u v := fun hc => huv (hcfg.diag u v u hc.symm)
    have hd2 : P.color u u ≠ P.color u' v' := fun hc => hu'v' (hcfg.diag u' v' u hc.symm)
    have hcard : ({P.color u u, P.color u v, P.color u' v'} :
        Finset (Fin P.rank)).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp [hd1, hd2]),
        Finset.card_insert_of_notMem (by simp [hne]), Finset.card_singleton]
    have hle := Finset.card_le_card (Finset.subset_univ
      ({P.color u u, P.color u v, P.color u' v'} : Finset (Fin P.rank)))
    rw [hcard, Finset.card_univ, Fintype.card_fin] at hle
    omega
  · intro hconst
    rcases isEmpty_or_nonempty T with hE | hnonempty
    · by_contra hr
      obtain ⟨x, -, -⟩ := P.color_surjective ⟨0, by omega⟩
      exact (hE.false x).elim
    · obtain ⟨t₀⟩ := hnonempty
      by_cases hpair : ∃ u v : T, u ≠ v
      · obtain ⟨u₀, v₀, huv₀⟩ := hpair
        have hsub : (Finset.univ : Finset (Fin P.rank))
            ⊆ {P.color t₀ t₀, P.color u₀ v₀} := by
          intro i _
          obtain ⟨x, y, hxy⟩ := P.color_surjective i
          by_cases hxyeq : x = y
          · subst hxyeq
            have hx : P.color x x = P.color t₀ t₀ := hhom x t₀
            rw [← hxy, hx]
            simp
          · have hx : P.color x y = P.color u₀ v₀ := hconst x y u₀ v₀ hxyeq huv₀
            rw [← hxy, hx]
            simp
        have hle := Finset.card_le_card hsub
        rw [Finset.card_univ, Fintype.card_fin] at hle
        exact hle.trans (Finset.card_insert_le _ _ |>.trans (by simp))
      · push_neg at hpair
        have hsub : (Finset.univ : Finset (Fin P.rank)) ⊆ {P.color t₀ t₀} := by
          intro i _
          obtain ⟨x, y, hxy⟩ := P.color_surjective i
          have hxyeq : x = y := hpair x y
          subst hxyeq
          have hx : P.color x x = P.color t₀ t₀ := hhom x t₀
          rw [← hxy, hx]
          simp
        have hle := Finset.card_le_card hsub
        rw [Finset.card_univ, Fintype.card_fin, Finset.card_singleton] at hle
        omega

/-- §9.4, step 9(ii).  The branch condition is Definition 3.1.8 for `X₂`, which is
homogeneous (`Babai.step8_induced₂_isHomogeneous`): *"`X₂` is the clique configuration"*. -/
theorem step9Clique_iff_rank_le_two (X : Pt (BipBlockInputs Ω))
    [Fintype ↥((step8Obj X).vtx)] [Fintype ↥(step8Blks X)] :
    Step9Clique X ↔ ((step8Config X).induced (step8Blks X)).rank ≤ 2 := by
  have hker := sameKernel_step9BlkColor X
  have hiff : ∀ u v u' v' : ↥(step8Blks X),
      step9BlkColor X u v = step9BlkColor X u' v'
        ↔ ((step8Config X).induced (step8Blks X)).color u v
          = ((step8Config X).induced (step8Blks X)).color u' v' := by
    intro u v u' v'
    exact (hker u v u' v').trans
      (((step8Config X).induced (step8Blks X)).natColor_eq_iff u v u' v')
  rw [rank_le_two_iff_color_const _
    ((step8Config X).induced_isConfiguration _ (step8Config_isCoherent X).toIsConfiguration)
    (step8_induced₂_isHomogeneous X (S := step8Blks X) rfl)]
  exact ⟨fun h u v u' v' huv hu'v' => (hiff u v u' v').1 (h u v u' v' huv hu'v'),
    fun h u v u' v' huv hu'v' => (hiff u v u' v').2 (h u v u' v' huv hu'v')⟩

/-! ### The two branch conditions are isomorphism invariants -/

section Congr

variable {X Y : Pt (BipBlockInputs Ω)} {φ : ↥X.car ≃ ↥Y.car}

/-- §9.4, step 9.  A morphism of the inputs carries the blocks of the object of step 8
onto the blocks of the image. -/
noncomputable def step8BlkIso (hφ : φ ∈ (BipBlockInputs Ω).IsoP X Y) :
    ↥(step8Blks X) ≃ ↥(step8Blks Y) :=
  Equiv.subtypeEquiv (step8VtxIso hφ) fun u => ((step8Obj_isIsoTo hφ).blocks _).symm

/-- §9.4, step 9.  The coloring of `X₂` is canonical: `Babai.step8CaseColor_map` read on
the blocks. -/
theorem step9BlkColor_map (hφ : φ ∈ (BipBlockInputs Ω).IsoP X Y) (u v : ↥(step8Blks X)) :
    step9BlkColor Y (step8BlkIso hφ u) (step8BlkIso hφ v) = step9BlkColor X u v :=
  step8CaseColor_map hφ _ _

/-- §9.4, step 9(i).  **The branch condition of case (i) is an isomorphism invariant**,
which is what `Babai.FindsAtMultCost.cases` asks of it. -/
theorem step9Imprimitive_congr (h : ((BipBlockInputs Ω).IsoP X Y).Nonempty)
    (hX : Step9Imprimitive X) : Step9Imprimitive Y := by
  obtain ⟨φ, hφ⟩ := h
  obtain ⟨k, hk⟩ := hX
  exact ⟨k, (isDisconnectedColor_map (step8BlkIso hφ) (step9BlkColor_map hφ) k).2 hk⟩

/-- §9.4, step 9(ii).  **The branch condition of case (ii) is an isomorphism
invariant.** -/
theorem step9Clique_congr (h : ((BipBlockInputs Ω).IsoP X Y).Nonempty)
    (hX : Step9Clique X) : Step9Clique Y := by
  obtain ⟨φ, hφ⟩ := h
  intro u v u' v' huv hu'v'
  have hne : ∀ a b : ↥(step8Blks Y), a ≠ b →
      (step8BlkIso hφ).symm a ≠ (step8BlkIso hφ).symm b := fun a b hab hc =>
    hab (by simpa using congrArg (step8BlkIso hφ) hc)
  have key := hX ((step8BlkIso hφ).symm u) ((step8BlkIso hφ).symm v)
    ((step8BlkIso hφ).symm u') ((step8BlkIso hφ).symm v') (hne u v huv) (hne u' v' hu'v')
  rw [← step9BlkColor_map hφ, ← step9BlkColor_map hφ] at key
  simpa using key

end Congr

/-! ### Collapsing a tower of full subcategories

Steps 1, 2, 4, 6 and 9 of §9.4 each cut the category of the inputs down by one condition,
so the category that step 9 runs in is a tower of `Babai.Cat.full`s.  The three functors
below start from the *one* full subcategory of `Babai.BipBlockInputs` cut out by the
conditions that they use; `Babai.fullOfBase` is the canonical embedding of the tower into
it. -/

/-- The canonical embedding of a category `D` into a full subcategory of `C`, given a
projection on objects that keeps the underlying set and the morphisms.  For a tower of
full subcategories the projection is a chain of `.1`s and the morphisms are literally the
same. -/
def fullOfBase {C D : Cat.{0, 0} Ω} (Q : ∀ s : Set Ω, C.Obj s → Prop)
    (π : ∀ {s : Set Ω}, D.Obj s → C.Obj s)
    (hiso : ∀ {s t : Set Ω} {A : D.Obj s} {B : D.Obj t} {ψ : ↥s ≃ ↥t},
      ψ ∈ D.Iso A B → ψ ∈ C.Iso (π A) (π B))
    (hQ : ∀ {s : Set Ω} (A : D.Obj s), Q s (π A)) : Func D (C.full Q) where
  obj A := ⟨A.car, ⟨π A.obj, hQ A.obj⟩⟩
  map f := ⟨f.1, hiso f.2⟩
  map_id _ := rfl
  map_trans _ _ := rfl

theorem fullOfBase_isCanonicalEmbedding {C D : Cat.{0, 0} Ω}
    (Q : ∀ s : Set Ω, C.Obj s → Prop) (π : ∀ {s : Set Ω}, D.Obj s → C.Obj s)
    (hiso : ∀ {s t : Set Ω} {A : D.Obj s} {B : D.Obj t} {ψ : ↥s ≃ ↥t},
      ψ ∈ D.Iso A B → ψ ∈ C.Iso (π A) (π B))
    (hQ : ∀ {s : Set Ω} (A : D.Obj s), Q s (π A)) :
    (fullOfBase Q π hiso hQ).IsCanonicalEmbedding where
  car_subset _ := subset_rfl
  map_restrict _ _ := rfl

/-! ### The object that step 8 leaves, in the shape the three cases ask for -/

section Objects

variable (X : Pt (BipBlockInputs Ω))

/-- §9.4, step 9(i).  **The input of §9.6 that step 8 leaves**: the first part and the
blocks of the graph `(V₁, V₂; R_i)` of step 8, with the coloring `Babai.step8CaseColor`;
the `Case` of §9.6 is `Babai.step8_isImprimitiveCaseOn`. -/
noncomputable def step9ImpObj (h : ¬ AllClassesSmall X) (himp : ¬ Step6Imprimitive X)
    (himp₂ : Step9Imprimitive X) : BlkImprimitiveObj (step7Set X) :=
  letI : Fintype ↥(step7Set X) := Fintype.ofFinite _
  letI : Fintype ↥((step8Obj X).vtx) := Fintype.ofFinite _
  letI : Fintype ↥(step8Blks X) := Fintype.ofFinite _
  { part₁ := (step8Obj X).part₁
    blocks := (step8Obj X).blocks
    blocks_nonempty := (step8Obj X).blocks_nonempty
    blocks_disjoint := (step8Obj X).blocks_disjoint
    blocks_off₁ := (step8Obj X).blocks_off₁
    c := step8CaseColor X
    c_off := fun _ _ hAB => step8CaseColor_off X hAB
    case := step8_isImprimitiveCaseOn X h himp (S := step8Blks X) rfl
      ((step9Imprimitive_iff X).1 himp₂) }

/-- §9.4, step 9(ii).  **The input of §9.7 that step 8 leaves.**  The `Case` of §9.7 is
`Babai.step8_isBlockDesignCaseOn`; the rank of `X₂` is `≤ 2` by the branch condition
(`Babai.step9Clique_iff_rank_le_two`). -/
noncomputable def step9DesignObj (h : ¬ AllClassesSmall X) (himp : ¬ Step6Imprimitive X)
    (hcl : Step9Clique X) :
    BlkCaseObj (step7Set X) (fun c 𝒱₁ 𝒞 => IsBlockDesignCaseOn c 𝒱₁ 𝒞) :=
  letI : Fintype ↥(step7Set X) := Fintype.ofFinite _
  letI : Fintype ↥((step8Obj X).vtx) := Fintype.ofFinite _
  letI : Fintype ↥(step8Blks X) := Fintype.ofFinite _
  { part₁ := (step8Obj X).part₁
    blocks := (step8Obj X).blocks
    blocks_nonempty := (step8Obj X).blocks_nonempty
    blocks_disjoint := (step8Obj X).blocks_disjoint
    blocks_off₁ := (step8Obj X).blocks_off₁
    c := step8CaseColor X
    c_off := fun _ _ hAB => step8CaseColor_off X hAB
    case := step8_isBlockDesignCaseOn X h himp (S := step8Blks X) rfl
      ((step9Clique_iff_rank_le_two X).1 hcl) }

/-- §9.4, step 9(iii).  **The input of §9.8 that step 8 leaves.**  The `Case` of §9.8 is
`Babai.step8_isUPCCCaseOn`; `X₂` is a UPCC because it is homogeneous, primitive (the
negation of the branch condition of case (i)) and not a clique (the negation of the branch
condition of case (ii)), which is `Babai.step8_induced₂_trichotomy`. -/
noncomputable def step9UPCCObj (h : ¬ AllClassesSmall X) (himp : ¬ Step6Imprimitive X)
    (himp₂ : ¬ Step9Imprimitive X) (hcl : ¬ Step9Clique X) : UPCCObj (step7Set X) :=
  letI : Fintype ↥(step7Set X) := Fintype.ofFinite _
  letI : Fintype ↥((step8Obj X).vtx) := Fintype.ofFinite _
  letI : Fintype ↥(step8Blks X) := Fintype.ofFinite _
  { part₁ := (step8Obj X).part₁
    blocks := (step8Obj X).blocks
    blocks_nonempty := (step8Obj X).blocks_nonempty
    blocks_disjoint := (step8Obj X).blocks_disjoint
    blocks_off₁ := (step8Obj X).blocks_off₁
    c := step8CaseColor X
    c_off := fun _ _ hAB => step8CaseColor_off X hAB
    case := step8_isUPCCCaseOn X h himp (S := step8Blks X) rfl
      (by
        rcases step8_induced₂_trichotomy X (S := step8Blks X) rfl with
          ⟨-, hnp⟩ | hrk | huni
        · exact absurd ((step9Imprimitive_iff X).2 hnp) himp₂
        · exact absurd ((step9Clique_iff_rank_le_two X).2 hrk) hcl
        · exact huni) }

end Objects

/-! ### The three functors -/

/-- §9.4, step 9.  What the turn knows about its input when step 9 is reached: the measure
of §9.5 is the one the turn was called with (step 4 of the recursion), some vertex-color
class of `V₁` is large (the negative branch of step 4) and `X₁` is primitive (the negative
branch of step 6). -/
def Step9Cond (N : ℕ) (X : Pt (BipBlockInputs Ω)) : Prop :=
  measure_9_5 X = N ∧ ¬ AllClassesSmall X ∧ ¬ Step6Imprimitive X

/-- §9.4, step 9(i).  The full subcategory of the inputs on which case (i) is run: after
step 4 (some vertex-color class of `V₁` is large), after step 6 (`X₁` is primitive) and in
the branch *"`X₂` is imprimitive"* of step 9. -/
def Step9ImpInputs (Ω : Type) [Fintype Ω] [DecidableEq Ω] (N : ℕ) : Cat.{0, 0} Ω :=
  (BipBlockInputs Ω).full fun s Y => Step9Cond N ⟨s, Y⟩ ∧ Step9Imprimitive ⟨s, Y⟩

/-- §9.4, step 9(ii).  The full subcategory of the inputs on which case (ii) is run. -/
def Step9DesignInputs (Ω : Type) [Fintype Ω] [DecidableEq Ω] (N : ℕ) : Cat.{0, 0} Ω :=
  (BipBlockInputs Ω).full fun s Y =>
    Step9Cond N ⟨s, Y⟩ ∧ ¬ Step9Imprimitive ⟨s, Y⟩ ∧ Step9Clique ⟨s, Y⟩

/-- §9.4, step 9(iii).  The full subcategory of the inputs on which case (iii) is run. -/
def Step9UPCCInputs (Ω : Type) [Fintype Ω] [DecidableEq Ω] (N : ℕ) : Cat.{0, 0} Ω :=
  (BipBlockInputs Ω).full fun s Y =>
    Step9Cond N ⟨s, Y⟩ ∧ ¬ Step9Imprimitive ⟨s, Y⟩ ∧ ¬ Step9Clique ⟨s, Y⟩

/-- The input of the three cases, as an object of `Babai.BipBlockInputs`. -/
def step9Base {Q : ∀ s : Set Ω, (BipBlockInputs Ω).Obj s → Prop}
    (X : Pt ((BipBlockInputs Ω).full Q)) : Pt (BipBlockInputs Ω) := ⟨X.car, X.obj.1⟩

theorem step9Base_isoP {Q : ∀ s : Set Ω, (BipBlockInputs Ω).Obj s → Prop}
    {X Y : Pt ((BipBlockInputs Ω).full Q)} {φ : ↥X.car ≃ ↥Y.car}
    (hφ : φ ∈ ((BipBlockInputs Ω).full Q).IsoP X Y) :
    φ ∈ (BipBlockInputs Ω).IsoP (step9Base X) (step9Base Y) := hφ

/-- §9.4, step 9(i).  **The functor from the inputs of step 9 into the inputs of §9.6.**
The object is the instance step 8 leaves (`Babai.step9ImpObj`) and the morphism is the
restriction `Babai.step7Equiv` of a morphism of the inputs; it is a morphism of
`Babai.BlkImprimitiveCases` because step 8 is canonical (`Babai.step8Obj_isIsoTo`) and so
is its coloring (`Babai.step8CaseColor_map`). -/
noncomputable def step9ImpFunc (N : ℕ) : Func (Step9ImpInputs Ω N) (BlkImprimitiveCases Ω) where
  obj X := ⟨step7Set (step9Base X),
    step9ImpObj (step9Base X) X.obj.2.1.2.1 X.obj.2.1.2.2 X.obj.2.2⟩
  map {A B} f :=
    ⟨step7Equiv (X := step9Base A) (Y := step9Base B) f.2,
      ⟨fun x => (step8Obj_isIsoTo f.2).part₁ x, fun B' => (step8Obj_isIsoTo f.2).blocks B',
        fun A' B' => step8CaseColor_map f.2 A' B'⟩⟩
  map_id _ := Subtype.ext (Equiv.ext fun _ => Subtype.ext rfl)
  map_trans _ _ := Subtype.ext (Equiv.ext fun _ => Subtype.ext rfl)

theorem step9ImpFunc_isCanonicalEmbedding (N : ℕ) :
    (step9ImpFunc (Ω := Ω) N).IsCanonicalEmbedding where
  car_subset X := step7Set_subset (step9Base X)
  map_restrict _ _ := rfl

/-- §9.4, step 9(iii).  **The functor from the inputs of step 9 into the inputs of
§9.8.**  Word for word `Babai.step9ImpFunc`, with the `Case` of §9.8. -/
noncomputable def step9UPCCFunc (N : ℕ) : Func (Step9UPCCInputs Ω N) (BlkUPCCCases Ω) where
  obj X := ⟨step7Set (step9Base X),
    step9UPCCObj (step9Base X) X.obj.2.1.2.1 X.obj.2.1.2.2 X.obj.2.2.1 X.obj.2.2.2⟩
  map {A B} f :=
    ⟨step7Equiv (X := step9Base A) (Y := step9Base B) f.2,
      ⟨fun x => (step8Obj_isIsoTo f.2).part₁ x, fun B' => (step8Obj_isIsoTo f.2).blocks B',
        fun A' B' => step8CaseColor_map f.2 A' B'⟩⟩
  map_id _ := Subtype.ext (Equiv.ext fun _ => Subtype.ext rfl)
  map_trans _ _ := Subtype.ext (Equiv.ext fun _ => Subtype.ext rfl)

theorem step9UPCCFunc_isCanonicalEmbedding (N : ℕ) :
    (step9UPCCFunc (Ω := Ω) N).IsCanonicalEmbedding where
  car_subset X := step7Set_subset (step9Base X)
  map_restrict _ _ := rfl

/-- §9.4, step 9(ii).  **The functor from the inputs of step 9 into the inputs of §9.7.**
In addition to `Babai.step9ImpFunc` the object carries the threshold `α_new` of step 5 and
the two numeric invariants that §9.7 asks for: *"`2/3 ≤ α < 1`"*
(`Babai.claim_9_4_step5_at`) and *"`|V₂| < α|V₁|`"* (`Babai.step8Obj_numBlocks_lt`).  A
morphism preserves the threshold by `Babai.alphaNew_congr`. -/
noncomputable def step9DesignFunc (N : ℕ) :
    Func (Step9DesignInputs Ω N) (BlkBlockDesignInputs Ω) where
  obj X := ⟨step7Set (step9Base X),
    ⟨⟨step9DesignObj (step9Base X) X.obj.2.1.2.1 X.obj.2.1.2.2 X.obj.2.2.2,
      alphaNew (step9Base X)⟩,
      ⟨(claim_9_4_step5_at X.obj.2.1.2.1).1, (claim_9_4_step5_at X.obj.2.1.2.1).2.1,
        step8Obj_numBlocks_lt (step9Base X) X.obj.2.1.2.1⟩⟩⟩
  map {A B} f :=
    ⟨step7Equiv (X := step9Base A) (Y := step9Base B) f.2,
      ⟨alphaNew_congr ⟨f.1, f.2⟩,
        fun x => (step8Obj_isIsoTo f.2).part₁ x, fun B' => (step8Obj_isIsoTo f.2).blocks B',
        fun A' B' => step8CaseColor_map f.2 A' B'⟩⟩
  map_id _ := Subtype.ext (Equiv.ext fun _ => Subtype.ext rfl)
  map_trans _ _ := Subtype.ext (Equiv.ext fun _ => Subtype.ext rfl)

theorem step9DesignFunc_isCanonicalEmbedding (N : ℕ) :
    (step9DesignFunc (Ω := Ω) N).IsCanonicalEmbedding where
  car_subset X := step7Set_subset (step9Base X)
  map_restrict _ _ := rfl

/-! ### §9.4, step 9: the branch shared by §9.6 and §9.8

Cases (i) and (iii) return the same kind of object (`Babai.IsBlkImprimitiveOutcome`) and
cost the same (`n₂`), so one lemma serves both.  The data of the instance that step 8
leaves, read in the ambient type, is `Babai.step8V₁` and `Babai.step8NumBlocks`. -/

/-- §9.4, steps 5-8.  **`W₁`, the first part of the instance that step 8 leaves, as a
subset of `Ω`.**  Steps 7 and 8 keep the first part of step 5, so this is the dominant
vertex-color class of step 5 (`Babai.step8V₁_eq`). -/
def step8V₁ (X : Pt (BipBlockInputs Ω)) : Set Ω :=
  Subtype.val '' {x : ↥(step7Set X) | (step8Obj X).part₁ x}

/-- §9.4, steps 5-8.  **`n₂` does not change after step 5.** -/
noncomputable def step8NumBlocks (X : Pt (BipBlockInputs Ω)) : ℕ :=
  (step8Obj X).blocks.ncard

theorem step8V₁_eq (X : Pt (BipBlockInputs Ω)) :
    step8V₁ X = Subtype.val '' dominantClass X := by
  rw [step8V₁, ← step7Obj_V₁_image X, Set.image_image]
  rfl

theorem step8V₁_subset (X : Pt (BipBlockInputs Ω)) :
    step8V₁ X ⊆ BipBlockInputs.V₁ X := by
  rw [step8V₁_eq]; exact dominantClass_image_subset_V₁ X

/-- §9.4, step 5, the bookkeeping that makes the transfer of step 9 work:
`α_new |W₁| = α n₁`. -/
theorem alphaNew_mul_step8V₁ {X : Pt (BipBlockInputs Ω)} (h : ¬ AllClassesSmall X) :
    alphaNew X * ((step8V₁ X).ncard : ℝ)
      = BipBlockInputs.alpha X * ((BipBlockInputs.V₁ X).ncard : ℝ) := by
  have h1 : (step8V₁ X).ncard = (dominantClass X).ncard := by
    rw [step8V₁_eq]; exact ncard_image_val _
  have h2 : (BipBlockInputs.V₁ X).ncard = BipBlockInputs.n₁ X := ncard_image_val _
  rw [h1, h2]
  exact alphaNew_mul_dominantClass h

/-! ### The arithmetic of the instance step 8 leaves -/

theorem step8V₁_ncard (X : Pt (BipBlockInputs Ω)) :
    (step8V₁ X).ncard = (dominantClass X).ncard := by
  rw [step8V₁_eq]; exact ncard_image_val _

/-- §9.4, steps 5-8.  **`n₂` does not increase.** -/
theorem step8NumBlocks_le (X : Pt (BipBlockInputs Ω)) :
    step8NumBlocks X ≤ BipBlockInputs.numBlocks X := step7Obj_numBlocks_le X

/-- §9.4, step 9.  **There are at least two blocks after step 8**
(`Babai.two_le_step8_numBlocks`). -/
theorem two_le_step8NumBlocks {X : Pt (BipBlockInputs Ω)} (h : ¬ AllClassesSmall X) :
    2 ≤ step8NumBlocks X := by
  letI : Fintype ↥(step7Set X) := Fintype.ofFinite _
  exact two_le_step8_numBlocks X h

/-- §9.4, step 9.  `n₂ ≥ 2` at the input of the pass: step 8 does not create blocks. -/
theorem two_le_numBlocks_of_step9 {X : Pt (BipBlockInputs Ω)} (h : ¬ AllClassesSmall X) :
    2 ≤ BipBlockInputs.numBlocks X :=
  le_trans (two_le_step8NumBlocks h) (step8NumBlocks_le X)

theorem two_le_step8V₁_ncard {X : Pt (BipBlockInputs Ω)} (h : ¬ AllClassesSmall X) :
    2 ≤ (step8V₁ X).ncard := by
  rw [step8V₁_ncard]; exact two_le_dominantClass_ncard h

theorem twothirds_le_alphaNew {X : Pt (BipBlockInputs Ω)} (h : ¬ AllClassesSmall X) :
    (2 : ℝ) / 3 ≤ alphaNew X :=
  le_trans X.obj.2.1 (alpha_le_alphaNew h)

/-- §9.4, step 9.  *"`|V₂| < α|V₁|`"* at the instance step 8 leaves
(`Babai.step8Obj_numBlocks_lt`), read in the ambient type. -/
theorem step8NumBlocks_lt {X : Pt (BipBlockInputs Ω)} (h : ¬ AllClassesSmall X) :
    (step8NumBlocks X : ℝ) < alphaNew X * ((step8V₁ X).ncard : ℝ) := by
  have h1 := step8Obj_numBlocks_lt X h
  rw [step8Obj_V₁_ncard] at h1
  rw [step8V₁_ncard]
  exact h1

/-! ### What the three branches of step 9 share

Every branch of step 9 ends the same way.  A case of §9.6, §9.7 or §9.8 either finishes
Theorem 9.2.2 for the pair `(α_new, W₁)` that step 5 left, or hands back a smaller
admissible instance, on which the recursion of §9.5 is called and which again returns a
solution for `(α_new, W₁)`.  In both cases the last move is the same: a solution for
`(α_new, W₁)` is a solution for `(α, V₁)`, because `W₁ ⊆ V₁` and `α_new |W₁| = α n₁`.
That last move is `Babai.step9_transfer`.

The other shared piece is `Babai.attachThr`: §9.6 and §9.8 return a *bare* graph
(`Babai.IsBlkImprimitiveOutcome`), while the recursion runs on instances that carry their
threshold as data (`Babai.BipBlockInputs`).  The threshold to attach is `α_new` of the
input of the pass, which is an isomorphism invariant (`Babai.alphaNew_congr`), so attaching
it is a functor. -/

/-- §9.4, step 9.  **The graph a case hands back, with its threshold attached.**  The
objects of `Babai.VColBlkThr` are pairs *(graph, threshold)*, and a morphism preserves the
threshold, so a functor into `Babai.VColBlkGraphs` together with an isomorphism-invariant
threshold `α` is a functor into `Babai.VColBlkThr`. -/
def attachThr {D : Cat.{0, 0} Ω} (F : Func D (VColBlkGraphs Ω ℕ)) (α : Pt D → ℝ)
    (hα : ∀ {X Y : Pt D}, (D.IsoP X Y).Nonempty → α X = α Y) : Func D (VColBlkThr Ω) where
  obj X := ⟨(F.obj X).car, ((F.obj X).obj, α X)⟩
  map {X Y} f := ⟨(F.map f).1, hα ⟨f.1, f.2⟩, (F.map f).2⟩
  map_id X := by
    refine Subtype.ext ?_
    show (F.map (Hom.id X)).1 = Equiv.refl _
    rw [F.map_id X]
    rfl
  map_trans f g := by
    refine Subtype.ext ?_
    show (F.map (f.trans g)).1 = ((F.map f).1.trans (F.map g).1)
    rw [F.map_trans f g]
    rfl

theorem attachThr_isCanonicalEmbedding {D : Cat.{0, 0} Ω} {F : Func D (VColBlkGraphs Ω ℕ)}
    (hF : F.IsCanonicalEmbedding) (α : Pt D → ℝ)
    (hα : ∀ {X Y : Pt D}, (D.IsoP X Y).Nonempty → α X = α Y) :
    (attachThr F α hα).IsCanonicalEmbedding where
  car_subset X := hF.car_subset X
  map_restrict f x := hF.map_restrict f x

/-- A morphism of admissible inputs carries `V₁` onto `V₁`, read on the points of the
ambient type.  This is what makes `Babai.BipBlockInputs.V₁` an admissible *set to be split*
for `Babai.transfer_finds_on`. -/
theorem mem_V₁_iff_of_isoP {X Y : Pt (BipBlockInputs Ω)} {φ : ↥X.car ≃ ↥Y.car}
    (hφ : φ ∈ (BipBlockInputs Ω).IsoP X Y) (x : ↥X.car) :
    ((φ x : Ω)) ∈ BipBlockInputs.V₁ Y ↔ (x : Ω) ∈ BipBlockInputs.V₁ X := by
  have hiso : X.obj.1.1.IsIsoTo Y.obj.1.1 φ := hφ.2
  constructor
  · rintro ⟨w, hw, hwz⟩
    have hw' : w = φ x := Subtype.ext hwz
    subst hw'
    exact ⟨x, (hiso.part₁ x).1 hw, rfl⟩
  · rintro ⟨w, hw, hwz⟩
    have hw' : w = x := Subtype.ext hwz
    exact ⟨φ x, (hiso.part₁ x).2 (hw' ▸ hw), rfl⟩

theorem V₁_subset_car (X : Pt (BipBlockInputs Ω)) : BipBlockInputs.V₁ X ⊆ X.car := by
  rintro z ⟨w, -, rfl⟩
  exact w.2

/-- §9.4, step 9, the last move of every branch.  **A solution for `(α_new, W₁)` is a
solution for `(α, V₁)`.**

This is the transfer clause of Lemma 9.3.1 (`Babai.transfer_finds_on`) for the set to be
split `V₁`, which is a proper subset of the point set: a Johnson scheme is kept, and a
colored `α_new`-partition of `W₁` is extended by the one block `V₁ ∖ W₁`.  The bookkeeping
that makes it work is step 5: `W₁ ⊆ V₁` (`Babai.step8V₁_subset`) and
`α_new |W₁| = α n₁` (`Babai.alphaNew_mul_step8V₁`). -/
theorem step9_transfer {Q : ∀ s : Set Ω, (BipBlockInputs Ω).Obj s → Prop}
    (hsmall : ∀ X : Pt ((BipBlockInputs Ω).full Q), ¬ AllClassesSmall (step9Base X))
    {cost : Pt ((BipBlockInputs Ω).full Q) → ℕ}
    (h : FindsAtMultCost ((BipBlockInputs Ω).full Q) (SplitOutcomes Ω) cost
      (fun X Z => IsSplitOutcome (alphaNew (step9Base X)) (step8V₁ (step9Base X)) Z)) :
    FindsAtMultCost ((BipBlockInputs Ω).full Q) (SplitOutcomes Ω) cost
      (fun X Z => Good_9_2_2 (step9Base X) Z) := by
  classical
  have hVsub : ∀ X : Pt ((BipBlockInputs Ω).full Q),
      BipBlockInputs.V₁ (step9Base X) ⊆ X.car := fun X => V₁_subset_car (step9Base X)
  have hViso : ∀ {X Y : Pt ((BipBlockInputs Ω).full Q)}
      (f : Hom ((BipBlockInputs Ω).full Q) X Y) (x : ↥X.car),
      ((f.1 x : Ω)) ∈ BipBlockInputs.V₁ (step9Base Y)
        ↔ (x : Ω) ∈ BipBlockInputs.V₁ (step9Base X) := by
    intro X Y f x
    exact mem_V₁_iff_of_isoP (X := step9Base X) (Y := step9Base Y) f.2 x
  have htr := transfer_finds_on (C := (BipBlockInputs Ω).full Q)
    (Good := fun X Z => IsSplitOutcome (alphaNew (step9Base X)) (step8V₁ (step9Base X)) Z)
    (V := fun X => BipBlockInputs.V₁ (step9Base X)) hVsub hViso
    (fun X => BipBlockInputs.alpha (step9Base X))
    (fun X => by
      have : (2 : ℝ) / 3 ≤ BipBlockInputs.alpha (step9Base X) := (step9Base X).obj.2.1
      linarith)
    (fun X Z hZ => ⟨alphaNew (step9Base X), step8V₁ (step9Base X),
      step8V₁_subset (step9Base X),
      le_of_lt (alphaNew_lt_one (hsmall X)),
      alphaNew_mul_step8V₁ (hsmall X), hZ⟩)
  refine (h.comp_dep htr (c₂' := fun _ => 1) (fun _ => le_rfl)).mono
    (fun X => by simp) (fun X Z hZ => ?_)
  obtain ⟨p, hp, hgood⟩ := hZ
  have h1 : IsSplitOutcome (BipBlockInputs.alpha (step9Base (pairFst p)))
      (BipBlockInputs.V₁ (step9Base (pairFst p))) Z := hgood
  rw [hp] at h1
  exact h1

/-! #### The pieces of the branch shared by §9.6 and §9.8 -/

section Halved

variable (Q : ∀ s : Set Ω, (BipBlockInputs Ω).Obj s → Prop)

/-- §9.4, step 9, branches (i) and (iii).  The outcome of §9.6 and of §9.8, read at an
object of the category in which step 9 runs. -/
def HalvedGood (X : Pt ((BipBlockInputs Ω).full Q))
    (Z : Pt (Cat.sum (ColoredPartitions Ω ℕ) (VColBlkGraphs Ω ℕ))) : Prop :=
  IsBlkImprimitiveOutcome (step8V₁ (step9Base X)) (step8NumBlocks (step9Base X)) Z

/-- §9.4, step 9.  The pairs *(input of the pass, outcome of the case)*: the category the
second stage of the branch runs on, so that the recursive call may look at the input. -/
def HalvedPairs : Cat.{0, 0} Ω :=
  PairCatOf ((BipBlockInputs Ω).full Q)
    (Cat.sum (ColoredPartitions Ω ℕ) (VColBlkGraphs Ω ℕ)) (HalvedGood Q)

variable {Q}

/-- The input of the pass, read at a pair. -/
def halvedBase (p : Pt (HalvedPairs Q)) : Pt (BipBlockInputs Ω) := step9Base (pairFst p)

/-- §9.4, step 9.  The branch of the case distinction on which the case returned a colored
partition: the partition itself is the outcome.  Word for word `Babai.upccStage2Left`. -/
noncomputable def halvedLeftFunc :
    Func ((HalvedPairs Q).full fun _ p => (p.snd).isLeft) (SplitOutcomes Ω) :=
  (((Cat.fullIncl (HalvedPairs Q) (fun _ p => (p.snd).isLeft)).comp
      (pairSndFunc ((BipBlockInputs Ω).full Q)
        (Cat.sum (ColoredPartitions Ω ℕ) (VColBlkGraphs Ω ℕ)) (HalvedGood Q))).intoFull
      (Cat.sumIsLeft (ColoredPartitions Ω ℕ) (VColBlkGraphs Ω ℕ))
      (fun X => X.obj.2)).comp
    ((Cat.sumLeftProj (ColoredPartitions Ω ℕ) (VColBlkGraphs Ω ℕ)).comp
      (Cat.sumLeftIncl (ColoredPartitions Ω ℕ) (JohnsonSchemes Ω)))

theorem halvedLeftFunc_isCanonicalEmbedding :
    (halvedLeftFunc (Q := Q)).IsCanonicalEmbedding :=
  (Func.intoFull_isCanonicalEmbedding (Func.IsCanonicalEmbedding.comp
      (Cat.fullIncl_isCanonicalEmbedding (HalvedPairs Q) _)
      (pairSndFunc_isCanonicalEmbedding _ _ _)) _ _).comp
    ((Cat.sumLeftProj_isCanonicalEmbedding _ _).comp
      (Cat.sumLeftIncl_isCanonicalEmbedding _ _))

/-- §9.4, step 9.  The branch on which the case returned a bipartite graph: the graph
itself.  Word for word `Babai.upccStage2Right`. -/
noncomputable def halvedRightGraph :
    Func ((HalvedPairs Q).full fun _ p => ¬ (p.snd).isLeft) (VColBlkGraphs Ω ℕ) :=
  (((Cat.fullIncl (HalvedPairs Q) (fun _ p => ¬ (p.snd).isLeft)).comp
      (pairSndFunc ((BipBlockInputs Ω).full Q)
        (Cat.sum (ColoredPartitions Ω ℕ) (VColBlkGraphs Ω ℕ)) (HalvedGood Q))).intoFull
      (Cat.sumIsRight (ColoredPartitions Ω ℕ) (VColBlkGraphs Ω ℕ))
      (fun X => Sum.not_isLeft.mp X.obj.2)).comp
    (Cat.sumRightProj (ColoredPartitions Ω ℕ) (VColBlkGraphs Ω ℕ))

theorem halvedRightGraph_isCanonicalEmbedding :
    (halvedRightGraph (Q := Q)).IsCanonicalEmbedding :=
  (Func.intoFull_isCanonicalEmbedding (Func.IsCanonicalEmbedding.comp
      (Cat.fullIncl_isCanonicalEmbedding (HalvedPairs Q) _)
      (pairSndFunc_isCanonicalEmbedding _ _ _)) _ _).comp
    (Cat.sumRightProj_isCanonicalEmbedding _ _)

/-- The threshold `α_new` of step 5, read at a pair on the right branch. -/
noncomputable def halvedAlpha
    (p : Pt ((HalvedPairs Q).full fun _ p => ¬ (p.snd).isLeft)) : ℝ :=
  alphaNew (halvedBase ⟨p.car, p.obj.1⟩)

theorem halvedAlpha_congr {p q : Pt ((HalvedPairs Q).full fun _ p => ¬ (p.snd).isLeft)}
    (h : (((HalvedPairs Q).full fun _ p => ¬ (p.snd).isLeft).IsoP p q).Nonempty) :
    halvedAlpha p = halvedAlpha q := by
  obtain ⟨φ, hφ⟩ := h
  exact alphaNew_congr ⟨φ, hφ.1⟩

/-- §9.4, step 9.  **What the case guarantees on the branch where it returned a graph.**
The returned graph lives on a subset of `□X`, its first part is `W₁`, it has at most half
as many blocks as the instance step 8 left, and its symmetry defect on `W₁` is at least
`1/2`. -/
theorem halvedRight_spec
    (p : Pt ((HalvedPairs Q).full fun _ p => ¬ (p.snd).isLeft)) :
    letI : Fintype ↥((halvedRightGraph.obj p).car) := Fintype.ofFinite _
    letI : DecidableEq ↥((halvedRightGraph.obj p).car) := Classical.decEq _
    Subtype.val '' (halvedRightGraph.obj p).obj.V₁
        = step8V₁ (halvedBase ⟨p.car, p.obj.1⟩) ∧
      2 * (halvedRightGraph.obj p).obj.numBlocks
        ≤ step8NumBlocks (halvedBase ⟨p.car, p.obj.1⟩) ∧
      1 / 2 ≤ (halvedRightGraph.obj p).obj.defect₁ := by
  have hgood := p.obj.1.good
  have hr : (p.obj.1.snd).isRight := Sum.not_isLeft.mp p.obj.2
  have hs : p.obj.1.snd = Sum.inr (p.obj.1.snd.getRight hr) :=
    Sum.eq_right_getRight_of_isRight hr
  rw [HalvedGood, IsBlkImprimitiveOutcome, hs] at hgood
  exact hgood

/-- §9.4, step 9.  **The graph the case returned is an admissible input of Theorem 9.2.2
for the threshold `α_new` of step 5**: `Babai.isThm922Input_of_halved` at the data of
`Babai.halvedRight_spec`. -/
theorem halvedRec_admissible {N : ℕ}
    (hQ : ∀ X : Pt ((BipBlockInputs Ω).full Q), Step9Cond N (step9Base X))
    (p : Pt ((HalvedPairs Q).full fun _ p => ¬ (p.snd).isLeft)) :
    letI : Fintype ↥((halvedRightGraph.obj p).car) := Fintype.ofFinite _
    letI : DecidableEq ↥((halvedRightGraph.obj p).car) := Classical.decEq _
    (2 : ℝ) / 3 ≤ halvedAlpha p ∧ halvedAlpha p < 1 ∧
      (halvedRightGraph.obj p).obj.IsThm922Input (halvedAlpha p) := by
  letI : Fintype ↥((halvedRightGraph.obj p).car) := Fintype.ofFinite _
  letI : DecidableEq ↥((halvedRightGraph.obj p).car) := Classical.decEq _
  obtain ⟨hV, hhalf, hdef⟩ := halvedRight_spec p
  have hsmall := (hQ (pairFst ⟨p.car, p.obj.1⟩)).2.1
  exact ⟨twothirds_le_alphaNew hsmall, alphaNew_lt_one hsmall,
    isThm922Input_of_halved _ (twothirds_le_alphaNew hsmall) hV
      (two_le_step8V₁_ncard hsmall) (step8NumBlocks_lt hsmall) hhalf hdef⟩

/-- §9.4, step 9 and §9.5.  **The instance handed back has smaller measure.**  Its `n₂` is
at most `n₂/2` and its hint bit is at most `1`, so its measure is at most `n₂ + 1`, which
is below `2 n₂` because `n₂ ≥ 2` (`Babai.two_le_numBlocks_of_step9`). -/
theorem halvedRec_measure {N : ℕ}
    (hQ : ∀ X : Pt ((BipBlockInputs Ω).full Q), Step9Cond N (step9Base X))
    (p : Pt ((HalvedPairs Q).full fun _ p => ¬ (p.snd).isLeft))
    (hadm : (BipBlockInputs Ω).Obj (halvedRightGraph.obj p).car)
    (hcar : hadm.1 = ((halvedRightGraph.obj p).obj, halvedAlpha p)) :
    measure_9_5 (⟨(halvedRightGraph.obj p).car, hadm⟩ : Pt (BipBlockInputs Ω)) < N := by
  obtain ⟨hV, hhalf, hdef⟩ := halvedRight_spec p
  have hsmall := (hQ (pairFst ⟨p.car, p.obj.1⟩)).2.1
  have hN : measure_9_5 (halvedBase ⟨p.car, p.obj.1⟩) = N :=
    (hQ (pairFst ⟨p.car, p.obj.1⟩)).1
  have hn₂ : 2 ≤ BipBlockInputs.numBlocks (halvedBase ⟨p.car, p.obj.1⟩) :=
    two_le_numBlocks_of_step9 hsmall
  have hle : step8NumBlocks (halvedBase ⟨p.car, p.obj.1⟩)
      ≤ BipBlockInputs.numBlocks (halvedBase ⟨p.car, p.obj.1⟩) :=
    step8NumBlocks_le _
  have hnum : BipBlockInputs.numBlocks (⟨(halvedRightGraph.obj p).car, hadm⟩ :
      Pt (BipBlockInputs Ω)) = (halvedRightGraph.obj p).obj.numBlocks := by
    rw [BipBlockInputs.numBlocks, hcar]
  have hbit := hintBit_le_one (⟨(halvedRightGraph.obj p).car, hadm⟩ : Pt (BipBlockInputs Ω))
  have hmeas : measure_9_5 (halvedBase ⟨p.car, p.obj.1⟩)
      = 2 * BipBlockInputs.numBlocks (halvedBase ⟨p.car, p.obj.1⟩)
        + hintBit (halvedBase ⟨p.car, p.obj.1⟩) := rfl
  rw [measure_9_5, hnum]
  omega

/-- §9.4, step 9.  **The instance the recursion of §9.5 is called on**, on the branch where
§9.6 or §9.8 returned a graph: that graph with the threshold `α_new` of step 5 attached
(`Babai.attachThr`), which is an admissible input of Theorem 9.2.2
(`Babai.halvedRec_admissible`) of strictly smaller measure
(`Babai.halvedRec_measure`). -/
noncomputable def halvedRecFunc {N : ℕ}
    (hQ : ∀ X : Pt ((BipBlockInputs Ω).full Q), Step9Cond N (step9Base X)) :
    Func ((HalvedPairs Q).full fun _ p => ¬ (p.snd).isLeft)
      ((BipBlockInputs Ω).full fun s Y => measure_9_5 ⟨s, Y⟩ < N) :=
  Func.intoFull
    (show Func ((HalvedPairs Q).full fun _ p => ¬ (p.snd).isLeft) (BipBlockInputs Ω) from
      Func.intoFull (attachThr halvedRightGraph halvedAlpha halvedAlpha_congr) _
        (fun p => halvedRec_admissible hQ p))
    _ (fun p => halvedRec_measure hQ p _ rfl)

theorem halvedRecFunc_isCanonicalEmbedding {N : ℕ}
    (hQ : ∀ X : Pt ((BipBlockInputs Ω).full Q), Step9Cond N (step9Base X)) :
    (halvedRecFunc hQ).IsCanonicalEmbedding :=
  Func.intoFull_isCanonicalEmbedding
    (Func.intoFull_isCanonicalEmbedding
      (attachThr_isCanonicalEmbedding halvedRightGraph_isCanonicalEmbedding _ _) _ _) _ _

end Halved

/-- §9.4, step 9, the branches (i) and (iii).  **The two cases of step 9 that halve `n₂`**
— §9.6 (`Babai.lemma_9_6_1`) and §9.8 (`Babai.case_9_8`) — return the same kind of object
and cost the same, so they share this branch.

The case is run on the instance `(W₁, V₂)` that step 8 leaves, at multiplicative cost
`n₂`.  Its outcome is either a colored `1/2`-partition of `W₁`, or a bipartite graph on
`W₁` with at most half as many blocks and symmetry defect at least `1/2`.  In the first
case objective (a) for `(α, V₁)` follows by extending the partition by the block
`V₁ \ W₁`; in the second, the graph is an admissible input of Theorem 9.2.2 for the
threshold `α_new` of step 5 (`Babai.isThm922Input_of_halved`) whose measure is smaller
(`n₂` has halved, and `n₂ ≥ 2` by `Babai.two_le_step8_numBlocks`), so the recursion `hrec`
applies to it and returns a solution for `(α_new, W₁)`.  Both cases end in
`Babai.transfer_finds_on` for `V X = V₁` and `β X = α`, which is legitimate because
`α_new |W₁| = α n₁` (`Babai.alphaNew_mul_step8V₁`).  The cost is
`Babai.caseCost_mul_costRec_9_4_le` together with `Babai.cost_9_4_le_costRec_9_4`.

The assembly is a three-stage `Babai.FindsAtMultCost.comp_dep` chain: the case
(`hcase`), then on the pairs *(input, outcome)* the case distinction by the side of the sum
(`Babai.halvedLeftFunc` and `Babai.halvedRecFunc`), and last the transfer
(`Babai.step9_transfer`). -/
theorem step9_halvedBranch (C₀ N : ℕ) {Q : ∀ s : Set Ω, (BipBlockInputs Ω).Obj s → Prop}
    (hQ : ∀ X : Pt ((BipBlockInputs Ω).full Q), Step9Cond N (step9Base X))
    (hrec : FindsAtMultCost ((BipBlockInputs Ω).full fun s Y => measure_9_5 ⟨s, Y⟩ < N)
      (SplitOutcomes Ω) (fun X => cost_9_4 C₀ ⟨X.car, X.obj.1⟩)
      (fun X Z => Good_9_2_2 ⟨X.car, X.obj.1⟩ Z))
    (hcase : FindsAtMultCost ((BipBlockInputs Ω).full Q)
      (Cat.sum (ColoredPartitions Ω ℕ) (VColBlkGraphs Ω ℕ))
      (fun X => step8NumBlocks (step9Base X))
      (fun X Z => IsBlkImprimitiveOutcome (step8V₁ (step9Base X))
        (step8NumBlocks (step9Base X)) Z)) :
    FindsAtMultCost ((BipBlockInputs Ω).full Q) (SplitOutcomes Ω)
      (fun X => cost_9_4 C₀ (step9Base X))
      (fun X Z => Good_9_2_2 (step9Base X) Z) := by
  classical
  have hcase' : FindsAtMultCost ((BipBlockInputs Ω).full Q)
      (Cat.sum (ColoredPartitions Ω ℕ) (VColBlkGraphs Ω ℕ))
      (fun X => step8NumBlocks (step9Base X)) (HalvedGood Q) := hcase
  -- the branch of the sum on which the case returned a colored `1/2`-partition of `W₁`
  have hleft : FindsAtMultCost ((HalvedPairs Q).full fun _ p => (p.snd).isLeft)
      (SplitOutcomes Ω) (fun _ => 1)
      (fun p Z => IsSplitOutcome (alphaNew (halvedBase ⟨p.car, p.obj.1⟩))
        (step8V₁ (halvedBase ⟨p.car, p.obj.1⟩)) Z) := by
    refine FindsAtMultCost.of_canonicalEmbedding halvedLeftFunc
      halvedLeftFunc_isCanonicalEmbedding (fun p => ?_)
    have hgood := p.obj.1.good
    have hl : (p.obj.1.snd).isLeft := p.obj.2
    have hs : p.obj.1.snd = Sum.inl (p.obj.1.snd.getLeft hl) :=
      Sum.eq_left_getLeft_of_isLeft hl
    rw [HalvedGood, IsBlkImprimitiveOutcome, hs] at hgood
    obtain ⟨hcar, hpart⟩ := hgood
    have hsmall : ¬ AllClassesSmall (halvedBase ⟨p.car, p.obj.1⟩) :=
      (hQ (pairFst ⟨p.car, p.obj.1⟩)).2.1
    have hhalf : (1 : ℝ) / 2 ≤ alphaNew (halvedBase ⟨p.car, p.obj.1⟩) := by
      have := twothirds_le_alphaNew hsmall; linarith
    exact ⟨hcar, hpart.1, hpart.2.trans
      (mul_le_mul_of_nonneg_right hhalf (by positivity))⟩
  -- the branch on which the case returned a graph: the recursion of §9.5
  have hright : FindsAtMultCost ((HalvedPairs Q).full fun _ p => ¬ (p.snd).isLeft)
      (SplitOutcomes Ω)
      (fun p => costRec_9_4 C₀ (halvedBase ⟨p.car, p.obj.1⟩))
      (fun p Z => IsSplitOutcome (alphaNew (halvedBase ⟨p.car, p.obj.1⟩))
        (step8V₁ (halvedBase ⟨p.car, p.obj.1⟩)) Z) := by
    refine (FindsAtMultCost.precomp (halvedRecFunc hQ)
      (halvedRecFunc_isCanonicalEmbedding hQ) hrec).mono (fun p => ?_) (fun p Z hZ => ?_)
    · obtain ⟨-, hhalf, -⟩ := halvedRight_spec p
      exact cost_9_4_le_costRec_9_4 p.obj.1.sub_subset
        (le_trans hhalf (step8NumBlocks_le _))
    · obtain ⟨hV, -, -⟩ := halvedRight_spec p
      have h1 : IsSplitOutcome (alphaNew (halvedBase ⟨p.car, p.obj.1⟩))
          (Subtype.val '' (halvedRightGraph.obj p).obj.V₁) Z := hZ
      rwa [hV] at h1
  -- the two branches, glued
  have hmid0 := FindsAtMultCost.cases (C := HalvedPairs Q)
    (P := fun _ p => (p.snd).isLeft)
    (costp := fun _ => 1)
    (costn := fun p => costRec_9_4 C₀ (halvedBase p))
    (Good := fun p Z => IsSplitOutcome (alphaNew (halvedBase p)) (step8V₁ (halvedBase p)) Z)
    (fun {X Y} h hp => pairSnd_isLeft_iso h hp) hleft hright
  -- the case, then the two branches
  have hmid := hcase'.comp_dep hmid0
    (c₂' := fun X => costRec_9_4 C₀ (step9Base X))
    (fun p => max_le (one_le_costRec_9_4 _ _) le_rfl)
  refine step9_transfer (fun X => (hQ X).2.1) (hmid.mono (fun X => ?_) (fun X Z hZ => ?_))
  · exact caseCost_mul_costRec_9_4_le
      (le_trans (step8NumBlocks_le _) (numBlocks_le_turnCost _))
      (lt_of_lt_of_le (by norm_num) (two_le_numBlocks_of_step9 (hQ X).2.1))
  · obtain ⟨p, hp, h1⟩ := hZ
    have h2 : IsSplitOutcome (alphaNew (step9Base (pairFst p)))
        (step8V₁ (step9Base (pairFst p))) Z := h1
    rw [hp] at h2
    exact h2

end Babai
