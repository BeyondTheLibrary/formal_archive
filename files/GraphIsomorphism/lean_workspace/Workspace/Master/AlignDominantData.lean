/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 14.1, Procedure Align, lines 7–11, the dominant window: the Johnson case data of
the first Chain Rule call.
-/
import Workspace.Master.AlignDominant
import Workspace.Master.Descent

/-!
# The Johnson case of the dominant orbit

the corrected paper (Procedure Align, lines 7–11) repairs a missing step of Procedure Align:
`G* = ϕ⁻¹(Aut(Y))` need not be transitive on the window `Ω(Δ_j)`, so the window is split
into the orbits of `G*` by the Chain Rule, the largest orbit first.  Item 3 of the repair
says what the first call is when that largest orbit `Δ₁` has more than `2n/3` points:

> For an affected orbit the kernel of the restriction `G* → G*^{Δ₁}` lies in `ker ϕ*`, so
> `ϕ*` is a giant representation of the transitive group `G*^{Δ₁}`, and Theorem 10.5.1 (e)
> gives the standard blocks on `Δ₁`.  This first call is the Johnson case with parameter
> `m* ≤ m/2` of Eq. (73).

This file carries that out.  `Workspace/Master/AlignDominant.lean` proves the two facts the
construction rests on (`AlignDominantA/B.affected_and_pointwiseStab_le_ker`); here they are
the fields `affected` and `stab_le` of `Babai.AlignDominantOrbit`, and the output is
`Babai.AlignDominantOrbit.johnsonCaseData`, a `Babai.JohnsonCaseData` for the instance
`⟨G*, Δ₁, x, y'⟩` with Johnson parameter `m*`.

The one new step is the passage from `ϕ*` on `G*` to `ϕ*` on the group `G*^{Δ₁}` induced on
the orbit.  The kernel of `G* → G*^{Δ₁}` is the pointwise stabilizer of `Δ₁`
(`Babai.ker_restrictOnto`), and that lies in `ker ϕ*`, so `ϕ*` factors:
`Babai.restrictFactor`.  Everything else is then Theorem 10.5.1 (e) read on `G*^{Δ₁}`,
which is transitive on `Δ₁`, so its one orbit is all of `↥Δ₁` and the system of
imprimitivity Theorem 10.5.1 (e) produces is a system on the whole window of the call.
-/

universe u v

namespace Babai

open MulAction Equiv Equiv.Perm

/-! ## A giant representation read on the group induced on an invariant set -/

section Factor

variable {Ω : Type u} [Fintype Ω] [DecidableEq Ω] {G : Subgroup (Equiv.Perm Ω)} {Δ : Set Ω}
  {k : ℕ}

/-- A homomorphism `ϕ : G → S(Γ)` that is trivial on the pointwise stabilizer of an
invariant set `Δ`, read on the group `G^Δ` induced on `Δ`.

This is the step of item 3 of the repair of Procedure Align: `ϕ*` factors through
`G* → G*^{Δ₁}` because the kernel of that restriction is the pointwise stabilizer of `Δ₁`
(`Babai.ker_restrictOnto`) and that lies in `ker ϕ*`
(`Babai.AlignDominant.pointwiseStab_orbit_le_ker`). -/
noncomputable def restrictFactor (hΔ : IsInvariant G Δ) (ϕ : G →* Equiv.Perm (Fin k))
    (hker : pointwiseStab G Δ ≤ ϕ.ker) : restrictTo G Δ hΔ →* Equiv.Perm (Fin k) :=
  MonoidHom.liftOfSurjective (restrictOnto hΔ) (restrictOnto_surjective hΔ)
    ⟨ϕ, by rw [ker_restrictOnto]; exact hker⟩

/-- `ϕ` factors as advertised: the lift composed with the restriction is `ϕ`. -/
@[simp] theorem restrictFactor_restrictOnto (hΔ : IsInvariant G Δ)
    (ϕ : G →* Equiv.Perm (Fin k)) (hker : pointwiseStab G Δ ≤ ϕ.ker) (g : G) :
    restrictFactor hΔ ϕ hker (restrictOnto hΔ g) = ϕ g :=
  MonoidHom.liftOfRightInverse_comp_apply _ _ _ ⟨ϕ, by rw [ker_restrictOnto]; exact hker⟩ g

theorem restrictFactor_comp (hΔ : IsInvariant G Δ) (ϕ : G →* Equiv.Perm (Fin k))
    (hker : pointwiseStab G Δ ≤ ϕ.ker) :
    (restrictFactor hΔ ϕ hker).comp (restrictOnto hΔ) = ϕ :=
  MonoidHom.ext fun g => restrictFactor_restrictOnto hΔ ϕ hker g

/-- The lift has the same image as `ϕ`, so it is a giant representation if `ϕ` is. -/
theorem isGiantRep_restrictFactor (hΔ : IsInvariant G Δ) (ϕ : G →* Equiv.Perm (Fin k))
    (hker : pointwiseStab G Δ ≤ ϕ.ker) (hϕ : IsGiantRep ϕ) :
    IsGiantRep (restrictFactor hΔ ϕ hker) := by
  intro a ha
  obtain ⟨g, hg⟩ := hϕ ha
  exact ⟨restrictOnto hΔ g, by rw [restrictFactor_restrictOnto]; exact hg⟩

/-- The two groups attach the same image to the stabilizer of a point of `Δ`
(`Babai.map_stabilizer_of_restrict_factor`), so a point of `Δ` is affected by the lift
exactly when it is affected by `ϕ`. -/
theorem affected_restrictFactor (hΔ : IsInvariant G Δ) (ϕ : G →* Equiv.Perm (Fin k))
    (hker : pointwiseStab G Δ ≤ ϕ.ker) (x : ↥Δ) :
    Affected (restrictFactor hΔ ϕ hker) x ↔ Affected ϕ (x : Ω) := by
  rw [Affected, Affected,
    map_stabilizer_of_restrict_factor hΔ (restrictFactor_comp hΔ ϕ hker) x]

/-- The label `T(x)` of Theorem 10.5.1 (a) is the same read on `G` and on `G^Δ`. -/
theorem Tpoint_restrictFactor (hΔ : IsInvariant G Δ) (ϕ : G →* Equiv.Perm (Fin k))
    (hker : pointwiseStab G Δ ≤ ϕ.ker) (x : ↥Δ) :
    Tpoint (restrictFactor hΔ ϕ hker) x = Tpoint ϕ (x : Ω) := by
  rw [Tpoint, Tpoint, map_stabilizer_of_restrict_factor hΔ (restrictFactor_comp hΔ ϕ hker) x]

end Factor

/-! ## Counting the blocks in the Johnson case `S_k^{(t)}`

`Workspace/Master/Descent.lean` proves `Babai.johnson_param_le` and
`Babai.two_blocks_of_actsAsJohnsonA` for `A_k^{(t)}`, which is all line 1 needs (Theorem
11.2.1 returns a group acting as `A_k^{(t)}`).  Theorem 10.5.1 (e) returns `A_k^{(t)}` *or*
`S_k^{(t)}`, so both counts are needed here.  The proofs are the ones of
`Workspace/Master/Descent.lean`: the block set is in bijection with `Γ^{(t)}` in either
case. -/

section CountBlocksS

variable {β : Type u} [Fintype β] {G : Subgroup (Equiv.Perm β)} {Δ : Set β}
  {ℬ : Set (Set β)} {k t : ℕ}

omit [Fintype β] in
/-- A group acting on `ℬ` as `S_k^{(t)}` has `C(k,t)` blocks. -/
theorem card_blocks_of_actsAsJohnsonS
    {hperm : ∀ σ ∈ G, ∀ B ∈ ℬ, (σ : Equiv.Perm β) '' B ∈ ℬ}
    (h : ActsAsJohnsonS G ℬ hperm k t) : Nat.card ℬ = k.choose t := by
  obtain ⟨e, -⟩ := h
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_finset_len, Fintype.card_fin]

/-- The Johnson parameter is at most the number of points, in both Johnson cases. -/
theorem johnson_param_le_or (ht : 1 ≤ t) (hk : 2 * t < k)
    (h : IsSystemOfImprimitivity G Δ ℬ)
    (hj : ActsAsJohnsonS G ℬ h.permutes k t ∨ ActsAsJohnsonA G ℬ h.permutes k t) :
    k ≤ Fintype.card β := by
  have h1 : k ≤ Nat.card ℬ := by
    rcases hj with hj | hj
    · rw [card_blocks_of_actsAsJohnsonS hj]; exact self_le_choose ht hk
    · rw [card_blocks_of_actsAsJohnsonA hj]; exact self_le_choose ht hk
  exact le_trans h1 (card_blocks_le h)

/-- A Johnson case has at least two blocks, in both Johnson cases. -/
theorem two_blocks_of_actsAsJohnson_or (ht : 1 ≤ t) (hk : 2 * t < k)
    (h : IsSystemOfImprimitivity G Δ ℬ)
    (hj : ActsAsJohnsonS G ℬ h.permutes k t ∨ ActsAsJohnsonA G ℬ h.permutes k t) :
    ∃ B₁ ∈ ℬ, ∃ B₂ ∈ ℬ, B₁ ≠ B₂ := by
  have : Finite ℬ := Set.Finite.to_subtype (Set.toFinite ℬ)
  have h1 : 1 < Nat.card ℬ := by
    have hcard : Nat.card ℬ = k.choose t := by
      rcases hj with hj | hj
      · exact card_blocks_of_actsAsJohnsonS hj
      · exact card_blocks_of_actsAsJohnsonA hj
    have := self_le_choose ht hk
    omega
  have : Nontrivial ℬ := Finite.one_lt_card_iff_nontrivial.1 h1
  obtain ⟨B₁, B₂, hne⟩ := exists_pair_ne ℬ
  exact ⟨(B₁ : Set β), B₁.2, (B₂ : Set β), B₂.2, fun hc => hne (Subtype.ext hc)⟩

end CountBlocksS

/-! ## The dominant orbit -/

section Orbit

open scoped Classical

variable {Ω : Type u} [Fintype Ω] [DecidableEq Ω] {A : Type v}

/-- §14.1, the repair of lines 7–11, item 3: **the largest orbit of `G*` in the dominant
window**, together with what
`Babai.AlignDominantA.affected_and_pointwiseStab_le_ker` and
`Babai.AlignDominantB.affected_and_pointwiseStab_le_ker` prove about it.

The two structures of `Workspace/Master/AlignDominant.lean` (the two cases of line 7)
produce `affected` and `stab_le` from `dominant`; they are fields here so that the
construction below is independent of which case of line 7 the round is in.

`window_large` is the exit of line 2 of Procedure Reduce-to-Johnson, *"if `|G| < C₀` for
some absolute constant `C₀` then compute `Iso_G(x,y)` by brute force, exit"*, in the form
the `window_large` field of `Babai.JohnsonCaseData` needs it: `|Δ₁| > 2n/3`, so `n ≥ 96`
gives `|Δ₁| ≥ 64`.  It is carried, not assumed away, exactly like
`Babai.DescentData.window_large`. -/
structure AlignDominantOrbit (D : AlignDominant Ω) where
  /-- A point of the orbit. -/
  u : Ω
  /-- The orbit lies in the window `Ω(Δ_j)`. -/
  mem_window : u ∈ D.window
  /-- The orbit is dominant: it has more than `2n/3` points. -/
  dominant : 2 * Fintype.card Ω < 3 * (orbit D.Gs u).ncard
  /-- Every point of the orbit is affected by `ϕ*`. -/
  affected : ∀ z ∈ orbit D.Gs u, Affected D.phis z
  /-- The pointwise stabilizer of the orbit lies in `ker ϕ*`. -/
  stab_le : pointwiseStab D.Gs (orbit D.Gs u) ≤ D.phis.ker
  /-- The round is in case 3: `m*` is above the threshold of Theorem 10.5.1. -/
  veryLarge : VeryLargeK D.ms (maxOrbitLength D.Gs)
  /-- Line 2 of Procedure Reduce-to-Johnson: the ambient window is above the absolute
  constant of the brute-force exit. -/
  window_large : 96 ≤ Fintype.card Ω

namespace AlignDominantOrbit

variable {D : AlignDominant Ω} (c : AlignDominantOrbit D)

/-- The orbit `Δ₁`, the window of the first Chain Rule call. -/
def Δ₁ : Set Ω := orbit D.Gs c.u

theorem isInvariant_Δ₁ : IsInvariant D.Gs c.Δ₁ := isInvariant_orbit' D.Gs c.u

/-- `Δ₁` lies in the window `Ω(Δ_j)`. -/
theorem Δ₁_subset_window : c.Δ₁ ⊆ D.window := D.orbit_subset_window c.mem_window

instance : Nonempty ↥c.Δ₁ := ⟨⟨c.u, mem_orbit_self c.u⟩⟩

/-- The base point of `Δ₁`. -/
def basePoint : ↥c.Δ₁ := ⟨c.u, mem_orbit_self c.u⟩

/-- `G*^{Δ₁}`, the group induced on the orbit. -/
noncomputable def windowGroup : Subgroup (Equiv.Perm ↥c.Δ₁) :=
  restrictTo D.Gs c.Δ₁ c.isInvariant_Δ₁

/-- `G*^{Δ₁}` is transitive on `Δ₁`. -/
theorem transitive : IsTransitive c.windowGroup :=
  isTransitive_restrictTo_orbit c.isInvariant_Δ₁

/-- Line 10, read on `G*^{Δ₁}`: `ϕ*` factors through the restriction, because the kernel of
the restriction is the pointwise stabilizer of `Δ₁` and that lies in `ker ϕ*`. -/
noncomputable def phi : c.windowGroup →* Equiv.Perm (Fin D.ms) :=
  restrictFactor c.isInvariant_Δ₁ D.phis c.stab_le

/-- Line 10: `ϕ*` is a giant representation of `G*^{Δ₁}`. -/
theorem isGiantRep_phi : IsGiantRep c.phi :=
  isGiantRep_restrictFactor _ _ _ D.isGiantRep_phis

/-- The numeric hypothesis of Theorem 10.5.1 for `(G*^{Δ₁}, ϕ*)`: the orbits of the
restricted group are orbits of `G*` (`Babai.maxOrbitLength_restrictTo_le`). -/
theorem veryLargeK_phi : VeryLargeK D.ms (maxOrbitLength c.windowGroup) :=
  c.veryLarge.mono (maxOrbitLength_restrictTo_le c.isInvariant_Δ₁)

/-- The one orbit of the transitive group `G*^{Δ₁}` is all of `Δ₁`. -/
theorem orbit_basePoint : orbit c.windowGroup c.basePoint = Set.univ :=
  (isTransitive_iff_orbit_eq_univ c.windowGroup).1 c.transitive c.basePoint

/-- Theorem 10.5.1 (e): the standard blocks of `ϕ*` on `Δ₁`. -/
noncomputable def blocks : Set (Set ↥c.Δ₁) :=
  standardBlocks c.phi (orbit c.windowGroup c.basePoint)

/-- Theorem 10.5.1 (e): the standard blocks are a system of imprimitivity of `G*^{Δ₁}` on
all of `Δ₁`, because `G*^{Δ₁}` is transitive. -/
theorem isSystem : IsSystemOfImprimitivity c.windowGroup Set.univ c.blocks := by
  rw [← c.orbit_basePoint]
  exact theorem_10_5_1_e_isSystem c.phi c.isGiantRep_phi c.veryLargeK_phi c.basePoint

/-- The parameter `t` of the standard blocks on `Δ₁`. -/
noncomputable def tPar : ℕ := tPoint c.phi c.basePoint

/-- `1 ≤ t`: the points of `Δ₁` are affected by `ϕ*` (item 3 of the repair), so their
labels are nonempty (Theorem 10.5.1 (b)). -/
theorem one_le_tPar : 1 ≤ c.tPar := by
  have haff : Affected c.phi c.basePoint :=
    (affected_restrictFactor c.isInvariant_Δ₁ D.phis c.stab_le c.basePoint).2
      (c.affected c.u (mem_orbit_self c.u))
  exact (theorem_10_5_1_b c.phi c.isGiantRep_phi c.veryLargeK_phi c.basePoint).1 haff

/-- Theorem 10.5.1 (a): `4t < m*`. -/
theorem four_mul_tPar_lt : 4 * c.tPar < D.ms :=
  (theorem_10_5_1_a c.phi c.isGiantRep_phi c.veryLargeK_phi c.basePoint).1.1

theorem two_mul_tPar_lt : 2 * c.tPar < D.ms := by have := c.four_mul_tPar_lt; omega

/-- Theorem 10.5.1 (e): `G*^{Δ₁}` acts on the standard blocks as `S_{m*}^{(t)}` or
`A_{m*}^{(t)}`. -/
theorem actsAsJohnson :
    ActsAsJohnsonS c.windowGroup c.blocks c.isSystem.permutes D.ms c.tPar ∨
      ActsAsJohnsonA c.windowGroup c.blocks c.isSystem.permutes D.ms c.tPar := by
  obtain ⟨e, -, he⟩ :=
    theorem_10_5_1_e_johnson c.phi c.isGiantRep_phi c.veryLargeK_phi c.basePoint
  exact he.symm.imp (fun h => ⟨e, h⟩) (fun h => ⟨e, h⟩)

/-- **Definition 11.4.1 for the first Chain Rule call**: `(G*^{Δ₁}, ℬ)` is a Johnson case
with Johnson parameter `m*`. -/
theorem isJohnsonCase : IsJohnsonCase c.windowGroup c.blocks D.ms c.tPar where
  t_pos := c.one_le_tPar
  two_mul_t_le := c.two_mul_tPar_lt.le
  transitive := c.transitive
  system := c.isSystem
  johnson := c.actsAsJohnson

/-- `|Δ₁| ≥ 64`: the orbit has more than `2n/3` points and `n ≥ 96`. -/
theorem ncard_Δ₁_large : 64 ≤ c.Δ₁.ncard := by
  have h1 := c.dominant
  have h2 := c.window_large
  show 64 ≤ (orbit D.Gs c.u).ncard
  omega

theorem card_Δ₁ : Fintype.card ↥c.Δ₁ = c.Δ₁.ncard := by
  rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]

/-- `m* ≤ |Δ₁|`: there are `C(m*,t) ≥ m*` standard blocks, and they are nonempty and
disjoint. -/
theorem param_le : D.ms ≤ c.Δ₁.ncard := by
  have h := johnson_param_le_or (β := ↥c.Δ₁) c.one_le_tPar c.two_mul_tPar_lt c.isSystem
    c.actsAsJohnson
  rw [c.card_Δ₁] at h
  exact h

/-- §14.1, lines 7–11, item 3 of the repair: **the Johnson case data of the first Chain
Rule call**.

The call is the instance with respect to `G*` on the orbit `Δ₁`, with the second string
shifted (Eq. (62) of the Chain Rule).  Its Johnson parameter is `m*`, and `m* ≤ m/2` is
Eq. (73) (`Babai.AlignDominant.param_halved`), which is what makes the round *progress* in
the sense of `Babai.MakesProgress` although the window does not shrink. -/
noncomputable def johnsonCaseData (x' y' : Ω → A) :
    JohnsonCaseData (⟨(D.Gs : Set (Equiv.Perm Ω)), c.Δ₁, x', y'⟩ : SIInstance Ω A) where
  K := D.Gs
  isGroup := rfl
  invariant := c.isInvariant_Δ₁
  ℬ := c.blocks
  m := D.ms
  t := c.tPar
  johnson := c.isJohnsonCase
  two_blocks :=
    two_blocks_of_actsAsJohnson_or c.one_le_tPar c.two_mul_tPar_lt c.isSystem c.actsAsJohnson
  ϕ := c.phi
  giant := c.isGiantRep_phi
  param_le := c.param_le
  window_large := c.ncard_Δ₁_large

@[simp] theorem johnsonCaseData_m (x' y' : Ω → A) :
    (c.johnsonCaseData (A := A) x' y').m = D.ms := rfl

/-- Eq. (73) for the first Chain Rule call: its Johnson parameter is at most `m/2`. -/
theorem two_mul_param_le (x' y' : Ω → A) :
    2 * (c.johnsonCaseData (A := A) x' y').m ≤ D.m := D.param_halved

end AlignDominantOrbit

/-! ## The dominant orbit in the two cases of line 7

`Babai.AlignDominantOrbit` records the conclusions of
`Babai.AlignDominantA.affected_and_pointwiseStab_le_ker` and
`Babai.AlignDominantB.affected_and_pointwiseStab_le_ker` as fields, so that the
construction above is the same in both cases of line 7.  These two definitions are the
proof that the fields are met. -/

/-- §14.1, line 7 (A): the dominant orbit of `G*` in the window, with everything item 3 of
the repair proves about it. -/
noncomputable def AlignDominantA.dominantOrbit (D : AlignDominantA Ω)
    (hvl : VeryLargeK D.ms (maxOrbitLength D.toAlignDominant.Gs))
    (hn : 96 ≤ Fintype.card Ω) {u : Ω} (hu : u ∈ D.toAlignDominant.window)
    (hbig : 2 * Fintype.card Ω < 3 * (orbit D.toAlignDominant.Gs u).ncard) :
    AlignDominantOrbit D.toAlignDominant where
  u := u
  mem_window := hu
  dominant := hbig
  affected := (D.affected_and_pointwiseStab_le_ker hvl hu hbig).1
  stab_le := (D.affected_and_pointwiseStab_le_ker hvl hu hbig).2
  veryLarge := hvl
  window_large := hn

/-- §14.1, line 7 (B): the dominant orbit of `G*` in the window.  Case (B) needs no
hypothesis on `m*`: the Johnson parameters already give `m* ≥ 2t* + 1 ≥ 5`.  The field
`veryLarge` is still asked for, because Theorem 10.5.1 (e) is applied to `(G*, ϕ*)`. -/
noncomputable def AlignDominantB.dominantOrbit (D : AlignDominantB Ω)
    (hvl : VeryLargeK D.ms (maxOrbitLength D.toAlignDominant.Gs))
    (hn : 96 ≤ Fintype.card Ω) {u : Ω} (hu : u ∈ D.toAlignDominant.window)
    (hbig : 2 * Fintype.card Ω < 3 * (orbit D.toAlignDominant.Gs u).ncard) :
    AlignDominantOrbit D.toAlignDominant where
  u := u
  mem_window := hu
  dominant := hbig
  affected := (D.affected_and_pointwiseStab_le_ker hu hbig).1
  stab_le := (D.affected_and_pointwiseStab_le_ker hu hbig).2
  veryLarge := hvl
  window_large := hn

end Orbit

end Babai
