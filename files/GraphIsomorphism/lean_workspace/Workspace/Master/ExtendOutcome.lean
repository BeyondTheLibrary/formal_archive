/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Sections 13.2 and 14.1: an outcome living on a canonical subset `D ⊆ Γ`, read as an
outcome on all of `Γ`.
-/
import Workspace.Master.SplitTransport

/-!
# From an outcome on `D ⊆ Γ` to an outcome on `Γ`

Theorem 13.2.1 says it finds *"a canonically embedded `t`-ary relational structure with
relative symmetry defect `≥ 1/2` on `Γ`"*, but its cases (2b) and (3) build the structure
on a canonical **subset** of `Γ`: on `C' = C ∖ S` in case (2b), and on the set `D` of fixed
points of `F^Γ` in case (3), with `|D| ≥ 4m/5`.  Theorem 9.2.3, applied to that structure
at line 6a of Sec. 15, then returns an outcome on the subset, not on `Γ`:
`Babai.IsSplitOutcome α D Z` and not `Babai.IsSplitOutcome α Set.univ Z`.

Procedure Align (Sec. 14.1) asks for the outcome on `Γ`.  The passage is the step the
paper takes silently when it writes *"on `Γ`"*: a canonical structure on a canonical subset
`D` of `Γ` carries with it the canonical two-coloring `(D, Γ ∖ D)` of `Γ`, so the outcome
becomes an outcome on `Γ` by **adding `Γ ∖ D` as one further block, with a color of its
own**.  That is `Babai.extendOutcome`.

* On the Johnson summand there is nothing to do: the outcome is already a Johnson scheme on
  a subset of `Γ`, which is what `Babai.IsSplitOutcome` asks for on `Γ` as well, only with a
  weaker constant — `|Z.car| ≥ α|D| > (4α/5)m`.
* On the colored-partition summand the partition of `D` is extended by the single block
  `Γ ∖ D`, colored `0`, the old colors being shifted up by one
  (`Babai.ColoredPartition.extend`).  The extension is admissible (Def. 7.1.1: the new color
  class `Γ ∖ D` is a single block equal to its color class, and the old classes keep their
  blocks), and `ρ` grows to at most `max(ρ(Π), |Γ ∖ D|) ≤ max(αm, m/5)`.

The map is **equivariant**: `Babai.extendOutcome_smul` says `(Z^π)'' = (Z'')^π`, because
`π` carries `D` onto `π(D)` and the complement onto the complement.  So a canonical family
of versions stays canonical after the extension, which is what both outcome (2b) and
outcome (3) of Theorem 13.2.1 need at line 6a.

## Numbering map

| Paper | Lean |
|---|---|
| §13.2, *"a canonical `t`-ary relational structure on `D`"* read *"on `Γ`"* | `Babai.extendOutcome` |
| §14.1, line 4, the extra color class `Γ ∖ D` | `Babai.ColoredPartition.extend` |
-/

universe u

namespace Babai

open Equiv
open scoped Pointwise

/-! ### Extending a colored partition by the complement of its ground set -/

namespace ColoredPartition

variable {Γ : Type} {D : Set Γ}

open scoped Classical in
/-- §7.1, §14.1: **a colored partition of `D ⊆ Γ`, extended to `Γ`** by adding `Γ ∖ D` as
one further block with a color of its own.

The old colors are shifted up by one so that the new color `0` belongs to `Γ ∖ D` alone.
Two points are in the same block when they lie on the same side of `D` and, if inside `D`,
were in the same block there. -/
noncomputable def extend (P : ColoredPartition ↥D ℕ) :
    ColoredPartition ↥(Set.univ : Set Γ) ℕ where
  color x := if h : (x : Γ) ∈ D then P.color ⟨(x : Γ), h⟩ + 1 else 0
  part :=
    { r := fun x y => ((x : Γ) ∈ D ↔ (y : Γ) ∈ D) ∧
        ∀ (hx : (x : Γ) ∈ D) (hy : (y : Γ) ∈ D), P.part ⟨(x : Γ), hx⟩ ⟨(y : Γ), hy⟩
      iseqv :=
        { refl := fun _ => ⟨Iff.rfl, fun _ _ => P.part.refl _⟩
          symm := fun h => ⟨h.1.symm, fun hy hx => P.part.symm (h.2 hx hy)⟩
          trans := fun h₁ h₂ => ⟨h₁.1.trans h₂.1, fun hx hz =>
            P.part.trans (h₁.2 hx (h₁.1.1 hx)) (h₂.2 (h₁.1.1 hx) hz)⟩ } }
  part_le_color := by
    intro x y h
    by_cases hx : (x : Γ) ∈ D
    · have hy : (y : Γ) ∈ D := h.1.1 hx
      simp only [dif_pos hx, dif_pos hy]
      rw [P.part_le_color (h.2 hx hy)]
    · have hy : (y : Γ) ∉ D := fun hc => hx (h.1.2 hc)
      simp only [dif_neg hx, dif_neg hy]

theorem extend_color_of_mem (P : ColoredPartition ↥D ℕ) {x : ↥(Set.univ : Set Γ)}
    (hx : (x : Γ) ∈ D) : P.extend.color x = P.color ⟨(x : Γ), hx⟩ + 1 := by
  classical
  show (if h : (x : Γ) ∈ D then P.color ⟨(x : Γ), h⟩ + 1 else 0) = _
  rw [dif_pos hx]

theorem extend_color_of_notMem (P : ColoredPartition ↥D ℕ) {x : ↥(Set.univ : Set Γ)}
    (hx : (x : Γ) ∉ D) : P.extend.color x = 0 := by
  classical
  show (if h : (x : Γ) ∈ D then P.color ⟨(x : Γ), h⟩ + 1 else 0) = _
  rw [dif_neg hx]

theorem extend_part_iff (P : ColoredPartition ↥D ℕ) {x y : ↥(Set.univ : Set Γ)} :
    P.extend.part x y ↔ (((x : Γ) ∈ D ↔ (y : Γ) ∈ D) ∧
      ∀ (hx : (x : Γ) ∈ D) (hy : (y : Γ) ∈ D), P.part ⟨(x : Γ), hx⟩ ⟨(y : Γ), hy⟩) :=
  Iff.rfl

theorem extend_part_of_mem (P : ColoredPartition ↥D ℕ) {x y : ↥(Set.univ : Set Γ)}
    (hx : (x : Γ) ∈ D) (hy : (y : Γ) ∈ D) :
    P.extend.part x y ↔ P.part ⟨(x : Γ), hx⟩ ⟨(y : Γ), hy⟩ :=
  ⟨fun h => h.2 hx hy, fun h => ⟨⟨fun _ => hy, fun _ => hx⟩, fun _ _ => h⟩⟩

theorem extend_part_of_notMem (P : ColoredPartition ↥D ℕ) {x y : ↥(Set.univ : Set Γ)}
    (hx : (x : Γ) ∉ D) : P.extend.part x y ↔ (y : Γ) ∉ D :=
  ⟨fun h hc => hx (h.1.2 hc), fun h =>
    ⟨⟨fun hc => absurd hc hx, fun hc => absurd hc h⟩, fun hc => absurd hc hx⟩⟩

theorem extend_mem_iff (P : ColoredPartition ↥D ℕ) {x y : ↥(Set.univ : Set Γ)}
    (h : P.extend.part x y) : ((x : Γ) ∈ D ↔ (y : Γ) ∈ D) := h.1

/-! #### The blocks and the color classes of the extension -/

/-- The inclusion `↥D → ↥(univ : Set Γ)`. -/
def univInc (D : Set Γ) (a : ↥D) : ↥(Set.univ : Set Γ) := ⟨(a : Γ), Set.mem_univ _⟩

theorem univInc_injective (D : Set Γ) : Function.Injective (univInc D) := by
  intro a b hab
  exact Subtype.ext (congrArg (fun z : ↥(Set.univ : Set Γ) => (z : Γ)) hab)

/-- The block of a point of `D` is the old block, carried into `Γ`. -/
theorem extend_block_of_mem (P : ColoredPartition ↥D ℕ)
    {x : ↥(Set.univ : Set Γ)} (hx : (x : Γ) ∈ D) :
    P.extend.block x = univInc D '' P.block ⟨(x : Γ), hx⟩ := by
  ext y
  constructor
  · intro hy
    have hyD : (y : Γ) ∈ D := (P.extend_mem_iff hy).2 hx
    exact ⟨⟨(y : Γ), hyD⟩, (P.extend_part_of_mem hyD hx).1 hy, Subtype.ext rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact (P.extend_part_of_mem a.2 hx).2 ha

/-- The block of a point outside `D` is all of `Γ ∖ D`. -/
theorem extend_block_of_notMem (P : ColoredPartition ↥D ℕ)
    {x : ↥(Set.univ : Set Γ)} (hx : (x : Γ) ∉ D) :
    P.extend.block x = {y : ↥(Set.univ : Set Γ) | (y : Γ) ∉ D} := by
  ext y
  show P.extend.part y x ↔ _
  constructor
  · intro hy
    intro hc
    exact hx ((P.extend_mem_iff hy).1 hc)
  · intro hy
    exact (P.extend_part_of_notMem hy).2 hx

/-- The color class of a point of `D` is the old color class, carried into `Γ`. -/
theorem extend_colorClass_of_mem (P : ColoredPartition ↥D ℕ)
    {x : ↥(Set.univ : Set Γ)} (hx : (x : Γ) ∈ D) :
    P.extend.colorClass (P.extend.color x)
      = univInc D '' P.colorClass (P.color ⟨(x : Γ), hx⟩) := by
  ext y
  constructor
  · intro hy
    have hcol : P.extend.color y = P.extend.color x := hy
    rw [P.extend_color_of_mem hx] at hcol
    have hyD : (y : Γ) ∈ D := by
      by_contra hc
      rw [P.extend_color_of_notMem hc] at hcol
      omega
    rw [P.extend_color_of_mem hyD] at hcol
    refine ⟨⟨(y : Γ), hyD⟩, ?_, Subtype.ext rfl⟩
    show P.color ⟨(y : Γ), hyD⟩ = _
    omega
  · rintro ⟨a, ha, rfl⟩
    show P.extend.color (univInc D a) = P.extend.color x
    have haD : ((univInc D a : ↥(Set.univ : Set Γ)) : Γ) ∈ D := a.2
    rw [P.extend_color_of_mem haD, P.extend_color_of_mem hx]
    have hav : (⟨((univInc D a : ↥(Set.univ : Set Γ)) : Γ), haD⟩ : ↥D) = a :=
      Subtype.ext rfl
    rw [hav]
    exact congrArg (fun k : ℕ => k + 1) ha

/-- The color class of a point outside `D` is all of `Γ ∖ D`. -/
theorem extend_colorClass_of_notMem (P : ColoredPartition ↥D ℕ)
    {x : ↥(Set.univ : Set Γ)} (hx : (x : Γ) ∉ D) :
    P.extend.colorClass (P.extend.color x) = {y : ↥(Set.univ : Set Γ) | (y : Γ) ∉ D} := by
  ext y
  rw [P.extend_color_of_notMem hx]
  constructor
  · intro hy
    have hcol : P.extend.color y = 0 := hy
    by_cases hc : (y : Γ) ∈ D
    · rw [P.extend_color_of_mem hc] at hcol
      omega
    · exact hc
  · intro hy
    exact P.extend_color_of_notMem hy

/-! #### Admissibility and `ρ` -/

/-- §7.1, Def. 7.1.1: **the extension is admissible**.  A color class inside `D` is an old
color class, with the old blocks; the new class `Γ ∖ D` is a single block equal to its
color class, so it satisfies the condition whatever its size. -/
theorem isAdmissible_extend (P : ColoredPartition ↥D ℕ)
    (hP : P.IsAdmissible) : P.extend.IsAdmissible := by
  intro x hx
  by_cases hxD : (x : Γ) ∈ D
  · rw [P.extend_block_of_mem hxD,
      Set.ncard_image_of_injective _ (univInc_injective D)]
    refine hP ⟨(x : Γ), hxD⟩ ?_
    rw [P.extend_colorClass_of_mem hxD,
      Set.ncard_image_of_injective _ (univInc_injective D)] at hx
    exact hx
  · rw [P.extend_block_of_notMem hxD]
    rwa [P.extend_colorClass_of_notMem hxD] at hx

/-- The size of the extra block: the complement of `D` in `Γ`. -/
theorem ncard_compl_block (D : Set Γ) :
    ({y : ↥(Set.univ : Set Γ) | (y : Γ) ∉ D} : Set ↥(Set.univ : Set Γ)).ncard
      = (Dᶜ : Set Γ).ncard := by
  classical
  have himg : ({y : ↥(Set.univ : Set Γ) | (y : Γ) ∉ D} : Set ↥(Set.univ : Set Γ))
      = (fun a : Γ => (⟨a, Set.mem_univ a⟩ : ↥(Set.univ : Set Γ))) '' (Dᶜ : Set Γ) := by
    ext y
    exact ⟨fun hy => ⟨(y : Γ), hy, Subtype.ext rfl⟩, by rintro ⟨a, ha, rfl⟩; exact ha⟩
  rw [himg, Set.ncard_image_of_injective _ (fun a b hab => congrArg Subtype.val hab)]

/-- §7.1, Def. 7.1.1: **`ρ` of the extension**.  Every block is either an old block or the
one new block `Γ ∖ D`. -/
theorem rho_extend_le [Fintype ↥D] [Fintype ↥(Set.univ : Set Γ)]
    (P : ColoredPartition ↥D ℕ)
    {r : ℕ} (hr : P.rho ≤ r) (hc : (Dᶜ : Set Γ).ncard ≤ r) : P.extend.rho ≤ r := by
  classical
  refine rho_le _ fun x => ?_
  by_cases hxD : (x : Γ) ∈ D
  · rw [P.extend_block_of_mem hxD,
      Set.ncard_image_of_injective _ (univInc_injective D)]
    exact le_trans (P.ncard_block_le_rho _) hr
  · rw [P.extend_block_of_notMem hxD, ncard_compl_block D]
    exact hc

end ColoredPartition

/-! ### The extension of an outcome -/

section Extend

variable {Γ : Type}

/-- §13.2, §14.1: **an outcome on `D ⊆ Γ`, read as an outcome on `Γ`**.  A colored
partition of `D` gains `Γ ∖ D` as one more block with a color of its own; a Johnson scheme
on a subset of `D` is already a Johnson scheme on a subset of `Γ`. -/
noncomputable def extendPt (D : Set Γ) (o : (SplitOutcomes Γ).Obj D) :
    Pt (SplitOutcomes Γ) :=
  match o with
  | Sum.inl P => ⟨Set.univ, Sum.inl P.extend⟩
  | Sum.inr J => ⟨D, Sum.inr J⟩

/-- §13.2, §14.1: `Z''`, the outcome `Z` read on all of `Γ`. -/
noncomputable def extendOutcome (Z : Pt (SplitOutcomes Γ)) : Pt (SplitOutcomes Γ) :=
  extendPt Z.car Z.obj

@[simp] theorem extendOutcome_inl (D : Set Γ) (P : ColoredPartition ↥D ℕ) :
    extendOutcome (⟨D, Sum.inl P⟩ : Pt (SplitOutcomes Γ))
      = ⟨Set.univ, Sum.inl P.extend⟩ := rfl

@[simp] theorem extendOutcome_inr (D : Set Γ) (J : (JohnsonSchemes Γ).Obj D) :
    extendOutcome (⟨D, Sum.inr J⟩ : Pt (SplitOutcomes Γ)) = ⟨D, Sum.inr J⟩ := rfl

end Extend

/-! ### The extension is equivariant -/

section Equivariant

variable {Γ : Type}

/-- The bijection `↥univ ≃ ↥univ` induced by `π`, as a morphism of the extended colored
partitions.  This is the one computation behind `Babai.extendOutcome_smul`. -/
theorem permHom_extend_mem {π : Equiv.Perm Γ} {D D' : Set Γ} (hD' : D' = π '' D)
    {P : ColoredPartition ↥D ℕ} {P' : ColoredPartition ↥D' ℕ}
    (hiso : permHom π (⟨D, P⟩ : Pt (ColoredPartitions Γ ℕ)) ⟨D', P'⟩ hD'
      ∈ (ColoredPartitions Γ ℕ).IsoP ⟨D, P⟩ ⟨D', P'⟩)
    (hcar : (⟨Set.univ, Sum.inl P'.extend⟩ : Pt (SplitOutcomes Γ)).car
      = π '' (⟨Set.univ, Sum.inl P.extend⟩ : Pt (SplitOutcomes Γ)).car) :
    permHom π (⟨Set.univ, Sum.inl P.extend⟩ : Pt (SplitOutcomes Γ))
        ⟨Set.univ, Sum.inl P'.extend⟩ hcar
      ∈ (SplitOutcomes Γ).IsoP ⟨Set.univ, Sum.inl P.extend⟩
        ⟨Set.univ, Sum.inl P'.extend⟩ := by
  classical
  obtain ⟨hcol, hpart⟩ := hiso
  -- `π` carries `D` onto `D'`
  have hmem : ∀ a : Γ, a ∈ D ↔ π a ∈ D' := by
    intro a
    rw [hD']
    exact ⟨fun ha => ⟨a, ha, rfl⟩, fun ⟨b, hb, hba⟩ => by rwa [π.injective hba] at hb⟩
  set f := permHom π (⟨Set.univ, Sum.inl P.extend⟩ : Pt (SplitOutcomes Γ))
    (⟨Set.univ, Sum.inl P'.extend⟩) hcar with hf
  have hfval : ∀ x : ↥(Set.univ : Set Γ), ((f x : ↥(Set.univ : Set Γ)) : Γ) = π (x : Γ) :=
    fun x => rfl
  -- the two ways of moving a point of `D`
  have hkey : ∀ (x : ↥(Set.univ : Set Γ)) (hx : (x : Γ) ∈ D)
      (hx' : ((f x : ↥(Set.univ : Set Γ)) : Γ) ∈ D'),
      (⟨((f x : ↥(Set.univ : Set Γ)) : Γ), hx'⟩ : ↥D')
        = permHom π (⟨D, P⟩ : Pt (ColoredPartitions Γ ℕ)) ⟨D', P'⟩ hD' ⟨(x : Γ), hx⟩ :=
    fun x hx hx' => Subtype.ext (by rw [hfval x]; rfl)
  refine ⟨fun x => ?_, fun x y => ?_⟩
  · -- colors
    by_cases hx : (x : Γ) ∈ D
    · have hx' : ((f x : ↥(Set.univ : Set Γ)) : Γ) ∈ D' := by
        rw [hfval x]; exact (hmem _).1 hx
      rw [P'.extend_color_of_mem hx', P.extend_color_of_mem hx, hkey x hx hx', hcol]
    · have hx' : ((f x : ↥(Set.univ : Set Γ)) : Γ) ∉ D' := by
        rw [hfval x]; exact fun hc => hx ((hmem _).2 hc)
      rw [P'.extend_color_of_notMem hx', P.extend_color_of_notMem hx]
  · -- the partition
    by_cases hx : (x : Γ) ∈ D
    · have hx' : ((f x : ↥(Set.univ : Set Γ)) : Γ) ∈ D' := by
        rw [hfval x]; exact (hmem _).1 hx
      by_cases hy : (y : Γ) ∈ D
      · have hy' : ((f y : ↥(Set.univ : Set Γ)) : Γ) ∈ D' := by
          rw [hfval y]; exact (hmem _).1 hy
        rw [P.extend_part_of_mem hx hy, P'.extend_part_of_mem hx' hy',
          hkey x hx hx', hkey y hy hy']
        exact hpart ⟨(x : Γ), hx⟩ ⟨(y : Γ), hy⟩
      · have hy' : ((f y : ↥(Set.univ : Set Γ)) : Γ) ∉ D' := by
          rw [hfval y]; exact fun hc => hy ((hmem _).2 hc)
        constructor
        · intro h; exact absurd ((P.extend_mem_iff h).1 hx) hy
        · intro h; exact absurd ((P'.extend_mem_iff h).1 hx') hy'
    · have hx' : ((f x : ↥(Set.univ : Set Γ)) : Γ) ∉ D' := by
        rw [hfval x]; exact fun hc => hx ((hmem _).2 hc)
      rw [P.extend_part_of_notMem hx, P'.extend_part_of_notMem hx']
      constructor
      · intro h
        rw [hfval y]
        exact fun hc => h ((hmem _).2 hc)
      · intro h
        rw [hfval y] at h
        exact fun hc => h ((hmem _).1 hc)

variable [MulAction (Equiv.Perm Γ) (Pt (SplitOutcomes Γ))]

/-- §13.2, §14.1: **the extension is equivariant**: `(Z^π)'' = (Z'')^π`.

The two conditions of `Babai.IsCatAction.eq_smul` are checked: the underlying sets agree
(both are `Γ` in the partition case, both are `Z.car` moved by `π` in the Johnson case), and
`π` is a morphism of the extended objects, which is `Babai.permHom_extend_mem`. -/
theorem extendOutcome_smul (hK : IsCatAction (SplitOutcomes Γ)) (π : Equiv.Perm Γ)
    (Z : Pt (SplitOutcomes Γ)) :
    extendOutcome (π • Z) = π • extendOutcome Z := by
  classical
  obtain ⟨s, o⟩ := Z
  -- the transport of `Z` along `π`, which by `IsCatAction.eq_smul` is `π • Z`
  obtain ⟨Y, hYcar, hYiso⟩ := isTransportable_splitOutcomes π (⟨s, o⟩ : Pt (SplitOutcomes Γ))
  have hYeq : Y = π • (⟨s, o⟩ : Pt (SplitOutcomes Γ)) := hK.eq_smul hYcar hYiso
  obtain ⟨car, obj⟩ := Y
  cases o with
  | inl P =>
    cases obj with
    | inr J' => exact absurd hYiso (Set.notMem_empty _)
    | inl P' =>
      have hisoP : permHom π (⟨s, P⟩ : Pt (ColoredPartitions Γ ℕ)) ⟨car, P'⟩ hYcar
          ∈ (ColoredPartitions Γ ℕ).IsoP ⟨s, P⟩ ⟨car, P'⟩ := hYiso
      rw [← hYeq, extendOutcome_inl, extendOutcome_inl]
      refine (hK.eq_smul (X := (⟨Set.univ, Sum.inl P.extend⟩ : Pt (SplitOutcomes Γ)))
        (Y := (⟨Set.univ, Sum.inl P'.extend⟩ : Pt (SplitOutcomes Γ))) ?_ ?_)
      · show (Set.univ : Set Γ) = π '' (Set.univ : Set Γ)
        simp [Set.image_univ]
      · exact permHom_extend_mem hYcar hisoP _
  | inr J =>
    cases obj with
    | inl P' => exact absurd hYiso (Set.notMem_empty _)
    | inr J' =>
      rw [← hYeq, extendOutcome_inr, extendOutcome_inr, hYeq]

/-- §13.2, §14.1: **a canonical family of outcomes on subsets of `Γ` stays canonical after
the extension**.  This is what both outcome (2b) and outcome (3) of Theorem 13.2.1 hand to
Procedure Align at line 6a: the versions live on `C'` or on `D`, and Align reads them on
`Γ`. -/
theorem isCanonicalVersions_image_extendOutcome {Ω : Type u} {A : Type*}
    {G : Subgroup (Equiv.Perm Ω)} {ϕ : G →* Equiv.Perm Γ}
    (hK : IsCatAction (SplitOutcomes Γ))
    {Vers : (Ω → A) → Set (Pt (SplitOutcomes Γ))} (hcan : IsCanonicalVersions ϕ Vers) :
    IsCanonicalVersions ϕ (fun z => extendOutcome '' Vers z) := by
  intro z σ
  show extendOutcome '' Vers (strAct z (σ : Equiv.Perm Ω)) = (ϕ σ) • (extendOutcome '' Vers z)
  rw [hcan z σ]
  ext Z
  constructor
  · rintro ⟨W, hW, rfl⟩
    obtain ⟨W₀, hW₀, rfl⟩ := hW
    exact ⟨extendOutcome W₀, ⟨W₀, hW₀, rfl⟩, (extendOutcome_smul hK (ϕ σ) W₀).symm⟩
  · rintro ⟨W, hW, rfl⟩
    obtain ⟨W₀, hW₀, rfl⟩ := hW
    exact ⟨(ϕ σ) • W₀, ⟨W₀, hW₀, rfl⟩, extendOutcome_smul hK (ϕ σ) W₀⟩

end Equivariant

/-! ### The extension is an outcome on `Γ` -/

section Numeric

variable {m : ℕ}

/-- §13.2, §14.1: **the extension of an outcome on `D` is an outcome on `Γ`**, with the two
thresholds given separately.

The Align core asks of its threshold only `1/2 < β`, `0 ≤ β` and `5β ≤ 4`, and which value
of `β` the extension reaches depends on the summand the outcome lands in.  So the two values
are two parameters here:

* a Johnson scheme inside `D` has at least `α|D|` vertices, so `βJ` serves as soon as
  `βJ·m ≤ α|D|`;
* a colored `α`-partition of `D`, extended by `Γ ∖ D` as one block of its own color, has
  `ρ ≤ max(α|D|, m − |D|)`, so `βP` serves as soon as `α|D| ≤ βP·m` and `m − |D| ≤ βP·m`.

`Babai.isSplitOutcome_extendOutcome` is the case `βJ = 4α/5`, `βP = α` of a set `D` with
`4m < 5|D|`.  Outcome (2b) of Theorem 13.2.1 needs the general form: there `D` is `C ∖ S`
with `|C| > 4m/5` and `|S| = d − 1 ≤ 4`, which gives only `|D| > 4m/5 − 4`, and that is not
above `4m/5` (take `m = 100`, `|C| = 81`, `d = 5`: then `|D| = 77 < 80`). -/
theorem isSplitOutcome_extendOutcome_of {α βJ βP : ℝ}
    (hJ12 : 1 / 2 < βJ) (hJ0 : 0 ≤ βJ) (hJ45 : 5 * βJ ≤ 4)
    (hP12 : 1 / 2 < βP) (hP0 : 0 ≤ βP) (hP45 : 5 * βP ≤ 4)
    {D : Set (Fin m)}
    (hJb : βJ * (m : ℝ) ≤ α * (D.ncard : ℝ))
    (hPb : α * (D.ncard : ℝ) ≤ βP * (m : ℝ))
    (hCb : (m : ℝ) - (D.ncard : ℝ) ≤ βP * (m : ℝ))
    {Z : Pt (SplitOutcomes (Fin m))} (hZ : IsSplitOutcome α D Z) :
    ∃ β : ℝ, 1 / 2 < β ∧ 0 ≤ β ∧ 5 * β ≤ 4 ∧
      IsSplitOutcome β (Set.univ : Set (Fin m)) (extendOutcome Z) := by
  classical
  have hm : (Set.univ : Set (Fin m)).ncard = m := by
    rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]
  obtain ⟨s, o⟩ := Z
  cases o with
  | inr J =>
    obtain ⟨hsub, hbig⟩ := hZ
    refine ⟨βJ, hJ12, hJ0, hJ45, ?_⟩
    rw [extendOutcome_inr]
    refine ⟨Set.subset_univ _, ?_⟩
    rw [hm]
    linarith
  | inl P =>
    obtain ⟨hs, hP⟩ := hZ
    refine ⟨βP, hP12, hP0, hP45, ?_⟩
    rw [extendOutcome_inl]
    refine ⟨rfl, ?_⟩
    letI : Fintype ↥(Set.univ : Set (Fin m)) := Fintype.ofFinite _
    letI : Fintype ↥s := Fintype.ofFinite _
    have hcardU : Fintype.card ↥(Set.univ : Set (Fin m)) = m := by
      rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, hm]
    have hcards : Fintype.card ↥s = s.ncard := by
      rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
    have hsv : s = D := hs
    obtain ⟨hadm, hrho⟩ := hP
    refine ⟨ColoredPartition.isAdmissible_extend P hadm, ?_⟩
    have hsum : s.ncard + (sᶜ : Set (Fin m)).ncard = m := by
      have h := Set.ncard_add_ncard_compl s
      rw [Nat.card_eq_fintype_card, Fintype.card_fin] at h
      exact h
    have hsumR : (s.ncard : ℝ) + ((sᶜ : Set (Fin m)).ncard : ℝ) = (m : ℝ) := by
      exact_mod_cast congrArg (fun k : ℕ => (k : ℝ)) hsum
    have hsn : (s.ncard : ℝ) = (D.ncard : ℝ) := by rw [hsv]
    have hrho' : (P.rho : ℝ) ≤ βP * (m : ℝ) := by
      rw [hcards, hsn] at hrho
      linarith
    have hcompl : (((sᶜ : Set (Fin m)).ncard : ℕ) : ℝ) ≤ βP * (m : ℝ) := by linarith
    set r := max P.rho (sᶜ : Set (Fin m)).ncard with hr
    have hrle : (P.extend.rho : ℝ) ≤ (r : ℝ) := by
      have h : P.extend.rho ≤ r :=
        ColoredPartition.rho_extend_le P (le_max_left _ _) (le_max_right _ _)
      exact_mod_cast h
    have hrα : (r : ℝ) ≤ βP * (m : ℝ) := by
      rcases max_cases P.rho (sᶜ : Set (Fin m)).ncard with ⟨h, -⟩ | ⟨h, -⟩
      · rw [hr, h]; exact hrho'
      · rw [hr, h]; exact hcompl
    show (P.extend.rho : ℝ) ≤ βP * (Fintype.card ↥(Set.univ : Set (Fin m)) : ℝ)
    rw [hcardU]
    linarith

/-- §13.2, §14.1: **the extension of an outcome on `D` is an outcome on `Γ`**, at a
threshold that the Align core accepts.

`D` is the canonical subset Theorem 13.2.1 works on, with `|D| > 4m/5`.  In the
colored-partition case nothing is lost: `ρ` of the extension is at most
`max(α|D|, |Γ ∖ D|) ≤ max(αm, m/5) ≤ αm`, so `β = α` serves.  In the Johnson case the
vertex set of the scheme has at least `α|D| > (4α/5)m` points, so `β = 4α/5` serves.

Both values meet the three conditions `Babai.nonempty_alignCore_of_versions` asks of its
threshold, `1/2 < β`, `0 ≤ β` and `5β ≤ 4`, when `3/4 ≤ α ≤ 4/5`. -/
theorem isSplitOutcome_extendOutcome {α : ℝ} (hα34 : 3 / 4 ≤ α) (hα45 : α ≤ 4 / 5)
    {D : Set (Fin m)} (hD : 4 * m < 5 * D.ncard) {Z : Pt (SplitOutcomes (Fin m))}
    (hZ : IsSplitOutcome α D Z) :
    ∃ β : ℝ, 1 / 2 < β ∧ 0 ≤ β ∧ 5 * β ≤ 4 ∧
      IsSplitOutcome β (Set.univ : Set (Fin m)) (extendOutcome Z) := by
  have hDR : (4 : ℝ) * (m : ℝ) < 5 * (D.ncard : ℝ) := by exact_mod_cast hD
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
  have hDm : D.ncard ≤ m := by
    have h := Set.ncard_le_ncard (Set.subset_univ D) (Set.toFinite _)
    rwa [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] at h
  have hDmR : ((D.ncard : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast hDm
  exact isSplitOutcome_extendOutcome_of (βJ := 4 / 5 * α) (βP := α)
    (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    (by nlinarith) (by nlinarith) (by nlinarith) hZ

end Numeric

end Babai
