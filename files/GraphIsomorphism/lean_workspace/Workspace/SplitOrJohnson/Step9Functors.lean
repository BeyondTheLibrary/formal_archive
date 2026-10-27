/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 9.4, step 9: the instance that step 8 leaves is an input of one of the three cases
of Sections 9.6, 9.7 and 9.8.
-/
import Workspace.SplitOrJohnson.Step8Canon

/-!
# §9.4, step 9: the `Case` headings at the instance step 8 leaves

Version 2.5, lines 4166-4172 of `babai-gi-source/quasi25.txt`.

> *"9. We need to consider the following cases: (i) `X₂` is imprimitive: Section 9.6;
> (ii) `X₂` is the clique configuration; we refer to this as the 'block design case',
> Section 9.7; (iii) `X₂` is uniprimitive: Section 9.8."*

Step 9 hands the instance that step 8 leaves to one of the three cases.  What each case
asks of its input is a `Case` heading (`Babai.IsImprimitiveCaseOn`,
`Babai.IsBlockDesignCaseOn`, `Babai.IsUPCCCaseOn`), read on the vertex set *"points of
`V₁` plus blocks"*.  This file proves those three headings for the object of step 8, with
the coloring `Babai.step8CaseColor` that the case categories carry.

The three lemmas below are the `case` field of the object of the functor from the inputs of
§9.4 into the input category of the case; the rest of that functor is the data
(`Babai.step8Obj`) and the morphisms (`Workspace/SplitOrJohnson/Step8Canon.lean`).

## `n₂ ≥ 2` after step 8

The `Case` of §9.7 asks that `X₂` be *the clique configuration*, which is rank **2**
(Def. 3.1.8), while the trichotomy of step 9 only excludes rank `≥ 3`.  Rank `1` is ruled
out by counting: a homogeneous configuration of rank `1` lives on one point, and after
step 8 there are at least two blocks.  That is `Babai.two_le_step8_numBlocks`, and its
reason is the parenthetical of step 8 itself: with a single block the graph
`(V₁, V₂; R_i)` is semiregular, so all the points of `V₁` have the same degree, which is
`0` or `1`; in the first case `R_i` is empty and in the second it is complete, and both
contradict *"`X` is semiregular, **nontrivial**"*.

| Paper | Lean |
|---|---|
| §9.4, step 8, *"nontrivial"* forces two blocks | `Babai.VColBipBlk.numBlocks_ne_one` |
| §9.4, step 9, `n₂ ≥ 2` | `Babai.two_le_step8_numBlocks` |
| §9.4, step 9, the `Case` of step 9 | `Babai.step8_isBipartiteCaseOn` |
| §9.4, step 9(i), the `Case` of §9.6 | `Babai.step8_isImprimitiveCaseOn` |
| §9.4, step 9(ii), the `Case` of §9.7 | `Babai.step8_isBlockDesignCaseOn` |
| §9.4, step 9(iii), the `Case` of §9.8 | `Babai.step8_isUPCCCaseOn` |
-/

namespace Babai

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

open VColBipBlk

/-! ### Two bookkeeping lemmas about instance arguments

`Babai.PartitionStructure.induced` and `Babai.IsTwin` take a `Fintype` resp. a
`DecidableEq` instance, and the statements of §9.4 and of §9.6-§9.8 do not always reach
them with the same one.  The instances are subsingletons, so nothing depends on the
choice. -/

theorem PartitionStructure.induced_congr_inst {V : Type} (P : PartitionStructure V)
    (S : Set V) (i₁ i₂ : Fintype ↥S) :
    @PartitionStructure.induced V P S i₁ = @PartitionStructure.induced V P S i₂ := by
  have h : i₁ = i₂ := Subsingleton.elim _ _
  subst h
  rfl

/-- Primitivity of an induced subconfiguration depends on the subset only, not on the
`Fintype` instance it is read with. -/
theorem PartitionStructure.induced_isPrimitive_congr {V : Type} (P : PartitionStructure V)
    {S T : Set V} (i₁ : Fintype ↥S) (i₂ : Fintype ↥T) (h : S = T)
    (hp : (@PartitionStructure.induced V P S i₁).IsPrimitive) :
    (@PartitionStructure.induced V P T i₂).IsPrimitive := by
  subst h
  rw [PartitionStructure.induced_congr_inst P S i₂ i₁]
  exact hp

/-- Uniprimitivity of an induced subconfiguration depends on the subset only. -/
theorem PartitionStructure.induced_isUniprimitive_congr {V : Type} (P : PartitionStructure V)
    {S T : Set V} (i₁ : Fintype ↥S) (i₂ : Fintype ↥T) (h : S = T)
    (hp : (@PartitionStructure.induced V P S i₁).IsUniprimitive) :
    (@PartitionStructure.induced V P T i₂).IsUniprimitive := by
  subst h
  rw [PartitionStructure.induced_congr_inst P S i₂ i₁]
  exact hp

/-- The rank of an induced subconfiguration depends on the subset only. -/
theorem PartitionStructure.induced_rank_congr_set {V : Type} (P : PartitionStructure V)
    {S T : Set V} (i₁ : Fintype ↥S) (i₂ : Fintype ↥T) (h : S = T) :
    (@PartitionStructure.induced V P S i₁).rank = (@PartitionStructure.induced V P T i₂).rank := by
  subst h
  rw [PartitionStructure.induced_congr_inst P S i₂ i₁]

theorem isTwin_congr_inst {V : Type} (i₁ i₂ : DecidableEq V) (G : Subgroup (Equiv.Perm V))
    (x y : V) : @IsTwin V i₁ G x y ↔ @IsTwin V i₂ G x y := by
  have h : i₁ = i₂ := Subsingleton.elim _ _
  subst h
  exact Iff.rfl

/-! ### `n₂ ≥ 2` after step 8 -/

namespace VColBipBlk

/-- §9.4, step 8, the parenthetical *"`X` is semiregular, nontrivial"*: **a nontrivial
semiregular graph has at least two blocks.**

With a single block `B` every point of `V₁` has the same degree, which is `0` or `1`; in
the first case the edge set is empty, in the second every point of `V₁` is joined to `B`,
so the edge set is everything.  Both are excluded by nontriviality. -/
theorem numBlocks_ne_one {s : Type} [Fintype s] {κ : Type} [Zero κ] {X : VColBipBlk s κ}
    (hsr : X.IsSemiregular) (hnt : ¬ X.IsTrivial) : X.blocks.ncard ≠ 1 := by
  classical
  intro hone
  obtain ⟨B, hB⟩ := Set.ncard_eq_one.1 hone
  obtain ⟨⟨d, hd⟩, -⟩ := hsr
  have hsub : ∀ x : s, {B' | (x, B') ∈ X.E} ⊆ ({B} : Set (Set s)) := by
    intro x B' hB'
    rw [← hB]
    exact (X.E_sub _ hB').2
  rcases Nat.eq_zero_or_pos d with hd0 | hdpos
  · -- degree `0`: no edges
    refine hnt (Or.inl ?_)
    refine Set.eq_empty_iff_forall_notMem.2 ?_
    rintro ⟨x, B'⟩ hxB
    have hx : x ∈ X.V₁ := (X.E_sub _ hxB).1
    have hemp : {B'' | (x, B'') ∈ X.E} = ∅ := by
      rw [← Set.ncard_eq_zero (Set.toFinite _), hd x hx, hd0]
    exact absurd (hemp ▸ hxB : B' ∈ (∅ : Set (Set s))) (Set.notMem_empty B')
  · -- positive degree: every point of `V₁` is joined to the only block
    refine hnt (Or.inr ?_)
    have hall : ∀ x ∈ X.V₁, (x, B) ∈ X.E := by
      intro x hx
      have hne : {B' | (x, B') ∈ X.E}.Nonempty := by
        refine (Set.ncard_pos (Set.toFinite _)).1 ?_
        rw [hd x hx]; exact hdpos
      obtain ⟨B', hB'⟩ := hne
      have : B' = B := hsub x hB'
      rwa [this] at hB'
    ext p
    constructor
    · intro hp
      exact ⟨(X.E_sub _ hp).1, (X.E_sub _ hp).2⟩
    · rintro ⟨hp₁, hp₂⟩
      have hpB : p.2 = B := by rw [hB] at hp₂; exact hp₂
      have := hall p.1 hp₁
      rw [← hpB] at this
      exact this

end VColBipBlk

section NumBlocks

variable (X : Pt (BipBlockInputs Ω))

/-- §9.4, step 9.  **There are at least two blocks after step 8.**  There is at least one
(`Babai.step7Blocks_nonempty`), and there is not exactly one
(`Babai.VColBipBlk.numBlocks_ne_one`, with `Babai.step8Obj_isSemiregular` and
`Babai.step8Obj_not_isTrivial`).

This is what makes `X₂` *the clique configuration* in case (ii) of step 9, and not the
configuration of rank `1` on a single vertex. -/
theorem two_le_step8_numBlocks (h : ¬ AllClassesSmall X) [Fintype ↥(step7Set X)] :
    2 ≤ (step8Obj X).numBlocks := by
  classical
  have hne : ((step8Obj X).blocks).Nonempty := by
    obtain ⟨B, hB⟩ := step7Blocks_nonempty X h
    obtain ⟨B', hB', hB'img⟩ : ∃ B' ∈ (step7Obj X).blocks,
        VColBipBlk.incl (step7Set_subset X) '' B' = B := by
      have : B ∈ (fun C : Set ↥(step7Set X) => VColBipBlk.incl (step7Set_subset X) '' C) ''
          (step7Obj X).blocks := by rw [step7Obj_blocks_image X]; exact hB
      exact this
    exact ⟨B', hB'⟩
  have hpos : 0 < (step8Obj X).numBlocks := by
    rw [VColBipBlk.numBlocks]
    exact (Set.ncard_pos (Set.toFinite _)).2 hne
  have hone : (step8Obj X).blocks.ncard ≠ 1 :=
    VColBipBlk.numBlocks_ne_one (step8Obj_isSemiregular X h) (step8Obj_not_isTrivial X h)
  have : (step8Obj X).numBlocks ≠ 1 := hone
  omega

/-- §9.4, step 9.  `X₂` has **at least two colors**: its vertex set has at least two
points.  The argument of `Babai.two_le_rank_step8`, on the second part. -/
theorem two_le_rank_step8_blks (h : ¬ AllClassesSmall X) [Fintype ↥(step7Set X)]
    {S : Set ↥((step8Obj X).vtx)} (hS : S = step8Blks X)
    [Fintype ↥((step8Obj X).vtx)] [Fintype ↥S] :
    2 ≤ ((step8Config X).induced S).rank := by
  classical
  subst hS
  have hcard : 2 ≤ (step8Blks X).ncard := by
    rw [ncard_step8Blks]; exact two_le_step8_numBlocks X h
  obtain ⟨a, ha, b, hb, hab⟩ :=
    (Set.one_lt_ncard (Set.toFinite (step8Blks X))).1 (by omega)
  set u : ↥(step8Blks X) := ⟨a, ha⟩ with hu
  set v : ↥(step8Blks X) := ⟨b, hb⟩ with hv
  have huv : u ≠ v := fun hc => hab (congrArg Subtype.val hc)
  by_contra hlt
  rw [Nat.not_le] at hlt
  have h1 := (((step8Config X).induced (step8Blks X)).color u v).isLt
  have h2 := (((step8Config X).induced (step8Blks X)).color v v).isLt
  have hsub : ((step8Config X).induced (step8Blks X)).color u v
      = ((step8Config X).induced (step8Blks X)).color v v := Fin.ext (by omega)
  exact huv (Subtype.ext ((step8Config_isCoherent X).toIsConfiguration.diag _ _ _
    (((step8Config X).induced_color_eq_iff (step8Blks X) u v v v).1 hsub)))

end NumBlocks

/-! ### The `Case` headings -/

section Cases

variable (X : Pt (BipBlockInputs Ω))

/-- §9.4, step 9.  **The `Case` heading of step 9 at the instance step 8 leaves**: the
coloring after step 8 is the coloring of a coherent configuration whose vertex set is the
union of the two vertex-color classes `V₁` and `V₂`, `X₁` is a UPCC, and the link `X₁₂` is
nontrivial.

The three ingredients are `Babai.step8Config_parts` (*"(: `X` bihomogeneous :)"*),
`Babai.step8_induced_isUniprimitive` (*"`X₁` remains a UPCC by Claim above"*) and
`Babai.step8_link_nontrivial` (*"`X₁₂` remains nontrivial"*). -/
theorem step8_isBipartiteCaseOn (h : ¬ AllClassesSmall X) (himp : ¬ Step6Imprimitive X)
    [Fintype ↥(step7Set X)] [Fintype ↥((step8Obj X).vtx)] :
    IsBipartiteCase (V := ↥((step8Obj X).vtx))
      (fun u v => step8CaseColor X (u : Set ↥(step7Set X)) (v : Set ↥(step7Set X)))
      (step8Pts X) (step8Blks X) := by
  classical
  obtain ⟨i₀, j₀, hij, hV₁, hV₂, hcover⟩ := step8Config_parts X h
  obtain ⟨u₁, hu₁, v₁, hv₁, u₂, hu₂, v₂, hv₂, hne⟩ := step8_link_nontrivial X h
  have hcolor : (fun u v : ↥((step8Obj X).vtx) =>
      step8CaseColor X (u : Set ↥(step7Set X)) (v : Set ↥(step7Set X)))
      = (step8Config X).natColor :=
    funext fun u => funext fun v => step8CaseColor_vtx X u v
  rw [hcolor, hV₁, hV₂]
  refine isBipartiteCase_induced (step8Config X) (step8Config_isCoherent X) hij hcover
    (step8_induced_isUniprimitive X h himp hV₁ hV₂ hcover)
    (x₁ := ⟨u₁, hV₁ ▸ hu₁⟩) (y₁ := ⟨v₁, hV₂ ▸ hv₁⟩)
    (x₂ := ⟨u₂, hV₁ ▸ hu₂⟩) (y₂ := ⟨v₂, hV₂ ▸ hv₂⟩) ?_
  intro hc
  exact hne ((step8Config_color_eq_iff X u₁ v₁ u₂ v₂).1 hc)

/-- §9.4, step 9(i).  **The `Case` of §9.6** at the instance step 8 leaves: in addition
`X₂` is homogeneous (`Babai.step8_induced₂_isHomogeneous`) and imprimitive, which is the
branch condition. -/
theorem step8_isImprimitiveCaseOn (h : ¬ AllClassesSmall X) (himp : ¬ Step6Imprimitive X)
    [Fintype ↥(step7Set X)] [Fintype ↥((step8Obj X).vtx)]
    {S : Set ↥((step8Obj X).vtx)} [instS : Fintype ↥S] (hS : S = step8Blks X)
    (hprim₂ : ¬ ((step8Config X).induced S).IsPrimitive) :
    IsImprimitiveCaseOn (step8CaseColor X)
      {A | ∃ x, (step8Obj X).part₁ x ∧ A = {x}} (step8Obj X).blocks := by
  classical
  subst hS
  obtain ⟨i₀, j₀, hij, hV₁, hV₂, hcover⟩ := step8Config_parts X h
  have hcolor : (fun u v : ↥((step8Obj X).vtx) =>
      step8CaseColor X (u : Set ↥(step7Set X)) (v : Set ↥(step7Set X)))
      = (step8Config X).natColor :=
    funext fun u => funext fun v => step8CaseColor_vtx X u v
  have hprim₂' : ¬ ((step8Config X).induced ((step8Config X).vertexClass j₀)).IsPrimitive :=
    fun hc => hprim₂ (PartitionStructure.induced_isPrimitive_congr (step8Config X) _ instS
      hV₂.symm hc)
  obtain ⟨u₁, hu₁, v₁, hv₁, u₂, hu₂, v₂, hv₂, hne⟩ := step8_link_nontrivial X h
  show IsImprimitiveCase (V := ↥((step8Obj X).vtx))
      (fun u v => step8CaseColor X (u : Set ↥(step7Set X)) (v : Set ↥(step7Set X)))
      (step8Pts X) (step8Blks X)
  rw [hcolor, hV₁, hV₂]
  refine isImprimitiveCase_induced (step8Config X) (step8Config_isCoherent X) hij hcover
    (step8_induced_isUniprimitive X h himp hV₁ hV₂ hcover)
    (step8_induced₂_isHomogeneous X hV₂.symm) hprim₂'
    (x₁ := ⟨u₁, hV₁ ▸ hu₁⟩) (y₁ := ⟨v₁, hV₂ ▸ hv₁⟩)
    (x₂ := ⟨u₂, hV₁ ▸ hu₂⟩) (y₂ := ⟨v₂, hV₂ ▸ hv₂⟩) ?_
  intro hc
  exact hne ((step8Config_color_eq_iff X u₁ v₁ u₂ v₂).1 hc)

/-- §9.4, step 9(ii).  **The `Case` of §9.7** (the block design case) at the instance
step 8 leaves: in addition `X₂` is the clique configuration, that is homogeneous of
rank `2`, and there are no `X`-twins in `V₁` (`Babai.claim_9_4_step8_at`, the Claim of
step 8).

The branch condition of step 9 is *"rank `≤ 2`"* (`Babai.step8_induced₂_trichotomy`); the
rank is exactly `2` because `X₂` has at least two vertices
(`Babai.two_le_rank_step8_blks`). -/
theorem step8_isBlockDesignCaseOn (h : ¬ AllClassesSmall X) (himp : ¬ Step6Imprimitive X)
    [Fintype ↥(step7Set X)] [Fintype ↥((step8Obj X).vtx)]
    {S : Set ↥((step8Obj X).vtx)} [instS : Fintype ↥S] (hS : S = step8Blks X)
    (hrank₂ : ((step8Config X).induced S).rank ≤ 2) :
    IsBlockDesignCaseOn (step8CaseColor X)
      {A | ∃ x, (step8Obj X).part₁ x ∧ A = {x}} (step8Obj X).blocks := by
  letI : DecidableEq ↥((step8Obj X).vtx) := Classical.decEq _
  classical
  subst hS
  obtain ⟨i₀, j₀, hij, hV₁, hV₂, hcover⟩ := step8Config_parts X h
  obtain ⟨u₁, hu₁, v₁, hv₁, u₂, hu₂, v₂, hv₂, hne⟩ := step8_link_nontrivial X h
  have hcolor : (fun u v : ↥((step8Obj X).vtx) =>
      step8CaseColor X (u : Set ↥(step7Set X)) (v : Set ↥(step7Set X)))
      = (step8Config X).natColor :=
    funext fun u => funext fun v => step8CaseColor_vtx X u v
  have hrank : ((step8Config X).induced ((step8Config X).vertexClass j₀)).rank = 2 := by
    have h2 : 2 ≤ ((step8Config X).induced (step8Blks X)).rank :=
      two_le_rank_step8_blks X h (S := step8Blks X) rfl
    have heq : ((step8Config X).induced (step8Blks X)).rank
        = ((step8Config X).induced ((step8Config X).vertexClass j₀)).rank :=
      PartitionStructure.induced_rank_congr_set (step8Config X) _ _ hV₂
    have heq' : ((step8Config X).induced (step8Blks X)).rank
        = (@PartitionStructure.induced _ (step8Config X) (step8Blks X) instS).rank :=
      PartitionStructure.induced_rank_congr_set (step8Config X) _ _ rfl
    omega
  have hnoTwins := claim_9_4_step8_at X h himp hij hV₁ hV₂ hcover
  show IsBlockDesignCase (V := ↥((step8Obj X).vtx))
      (fun u v => step8CaseColor X (u : Set ↥(step7Set X)) (v : Set ↥(step7Set X)))
      (step8Pts X) (step8Blks X)
  rw [hcolor, hV₁, hV₂]
  refine isBlockDesignCase_induced (step8Config X) (step8Config_isCoherent X) hij hcover
    (step8_induced_isUniprimitive X h himp hV₁ hV₂ hcover)
    (step8_induced₂_isHomogeneous X hV₂.symm) hrank ?_
    (x₁ := ⟨u₁, hV₁ ▸ hu₁⟩) (y₁ := ⟨v₁, hV₂ ▸ hv₁⟩)
    (x₂ := ⟨u₂, hV₁ ▸ hu₂⟩) (y₂ := ⟨v₂, hV₂ ▸ hv₂⟩) ?_
  · intro u hu v hv hc
    exact hnoTwins u hu v hv ((isTwin_congr_inst _ _ _ u v).1 hc)
  · intro hc
    exact hne ((step8Config_color_eq_iff X u₁ v₁ u₂ v₂).1 hc)

/-- §9.4, step 9(iii).  **The `Case` of §9.8** at the instance step 8 leaves: in addition
`X₂` is a UPCC, which is the branch condition. -/
theorem step8_isUPCCCaseOn (h : ¬ AllClassesSmall X) (himp : ¬ Step6Imprimitive X)
    [Fintype ↥(step7Set X)] [Fintype ↥((step8Obj X).vtx)]
    {S : Set ↥((step8Obj X).vtx)} [instS : Fintype ↥S] (hS : S = step8Blks X)
    (huni₂ : ((step8Config X).induced S).IsUniprimitive) :
    IsUPCCCaseOn (step8CaseColor X)
      {A | ∃ x, (step8Obj X).part₁ x ∧ A = {x}} (step8Obj X).blocks := by
  classical
  subst hS
  obtain ⟨i₀, j₀, hij, hV₁, hV₂, hcover⟩ := step8Config_parts X h
  obtain ⟨u₁, hu₁, v₁, hv₁, u₂, hu₂, v₂, hv₂, hne⟩ := step8_link_nontrivial X h
  have hcolor : (fun u v : ↥((step8Obj X).vtx) =>
      step8CaseColor X (u : Set ↥(step7Set X)) (v : Set ↥(step7Set X)))
      = (step8Config X).natColor :=
    funext fun u => funext fun v => step8CaseColor_vtx X u v
  have huni₂' : ((step8Config X).induced ((step8Config X).vertexClass j₀)).IsUniprimitive :=
    PartitionStructure.induced_isUniprimitive_congr (step8Config X) instS _ hV₂ huni₂
  show IsUPCCCase (V := ↥((step8Obj X).vtx))
      (fun u v => step8CaseColor X (u : Set ↥(step7Set X)) (v : Set ↥(step7Set X)))
      (step8Pts X) (step8Blks X)
  rw [hcolor, hV₁, hV₂]
  refine isUPCCCase_induced (step8Config X) (step8Config_isCoherent X) hij hcover
    (step8_induced_isUniprimitive X h himp hV₁ hV₂ hcover) huni₂'
    (x₁ := ⟨u₁, hV₁ ▸ hu₁⟩) (y₁ := ⟨v₁, hV₂ ▸ hv₁⟩)
    (x₂ := ⟨u₂, hV₁ ▸ hu₂⟩) (y₂ := ⟨v₂, hV₂ ▸ hv₂⟩) ?_
  intro hc
  exact hne ((step8Config_color_eq_iff X u₁ v₁ u₂ v₂).1 hc)

end Cases

end Babai
