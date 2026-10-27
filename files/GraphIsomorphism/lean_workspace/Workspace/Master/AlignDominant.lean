/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Sections 14.1 and 14.2: Procedure Align on the dominant window.
-/
import Workspace.Master.Sec15
import Workspace.Canonical.AlignJohnson
import Workspace.Master.AlignDominantAux

/-!
# Procedure Align, lines 6–11: the dominant window

> 6. If `(∃j)(|Δ_j| > m/2)` ("dominant color") then start the application of the Chain Rule
>    with the window `Ω(Δ_j) = ⋃_{T ∈ (Δ_j choose t)} B_T`.
> 7. While processing window `Ω(Δ_j)`
>    (A) if `X` gives a nontrivial equipartition of `Δ_j` then let `Y` be this equivalence
>        relation on `Δ_j` and `Γ*` the set of blocks
>    (B) if `Δ_j` is the vertex set of a Johnson scheme `J(m*, t*)` (`t* ≥ 2`) then identify
>        `Δ_j` with `(Γ* choose t*)`, `|Γ*| = m*`, and let `Y` denote this Johnson scheme
> 8. let `H = Aut(Y)` and `ψ : H → S(Γ*)` be the natural epimorphism
> 9. let `G* = ϕ⁻¹(H)`
> 10. let `ϕ* : G* → S(Γ*)` be the composition of `ϕ` restricted to `G*` and `ψ`
> 11. update: `G ← G*`, `Γ ← Γ*`, `ϕ ← ϕ*`

Sec. 14.2 charges the recursive call on `Ω(Δ_j)` as `T_Jh(n, m/2)`, that is, as a *Johnson
case* on a window that need not shrink.  the corrected paper (Sec. 14.1–14.2, Procedure Align)
shows that a step is missing: the group `G* = ϕ⁻¹(Aut(Y))` need not be transitive on
`Ω(Δ_j)`, so the next round does not start from a Johnson case.  The repair the entry
proposes is to apply the Chain Rule to the orbits of `G*` on `Ω(Δ_j)`, **largest orbit
first**, and it splits into three cases:

1. `m*` below the threshold of Theorem 10.5.1: descend to `ker ϕ*` first (multiplicative
   cost `m*!`) and take the orbits of the kernel, all of which are small;
2. every orbit of `G*` has at most `2n/3` points: every call shrinks the window;
3. otherwise the largest orbit `Δ₁` has more than `2n/3` points; then `Δ₁` is *affected* by
   `ϕ*`, the pointwise stabilizer of `Δ₁` in `G*` lies in `ker ϕ*`, so `ϕ*` is a giant
   representation of the transitive group `G*^{Δ₁}`, and Theorem 10.5.1 (e) turns that call
   into the Johnson case of Eq. (73), with parameter `m* ≤ m/2`.  All other orbits have
   fewer than `n/3` points.

## The shape of this file

`Babai.AlignDominant` carries what lines 6, 8, 9, 10 put on the table *without* the
structure `Y` of line 7: the group, the giant representation, the dominant class `Δ_j`, the
subgroup `H ≤ S(Γ)` that permutes `Δ_j`, and the epimorphism `ψ : H → S(Γ*)`.  The facts
that only need this much are proved on it: the group `G*` and the window `Ω(Δ_j)` of lines
9 and 11, that `ϕ*` is a giant representation, that being unaffected is a property of a
whole `G*`-orbit, that a dominant orbit is affected once the unaffected part of the window
is small, and that all other orbits are then smaller than `n/3`.

**The counting lemmas need `Y` itself.**  Without it `Babai.AlignDominant` has degenerate
inhabitants — for instance `Δ_j = Γ`, `H = ⊤`, `m* = 1`, `ψ` the trivial map onto the
trivial group `S(Γ*)`, which satisfies every field — and for those the counting statements
are plainly false: `ϕ*` is then trivial, its kernel is `G*` itself, and the window is all
of `Ω`.  So the two cases of line 7 are separate structures,
`Babai.AlignDominantA` (an equipartition of `Δ_j`) and `Babai.AlignDominantB` (a Johnson
scheme on `Δ_j`), and each counting lemma is stated once per case.

All five statements of this file are now proved; the shared steps live in
`Workspace/Master/AlignDominantAux.lean`.  What is still owed is the branch of
`Babai.designAlignReduction` that uses them, see `Workspace/Master/DESIGN.md`,
Mismatch 5.
-/

universe u

namespace Babai

open MulAction Equiv Equiv.Perm

variable {Ω : Type u} [Fintype Ω] [DecidableEq Ω]

/-- §14.1, lines 6 and 8–10: what Procedure Align has on the table while it processes the
dominant window, *except* the structure `Y` of line 7.

The fields are the Situation of Sec. 14 (*"We have a transitive group `G ≤ S(Ω)`"* with a
giant representation `ϕ : G → S(Γ)`, `|Γ| = m`), the common label size `t = t_Δ` of
Theorem 10.5.1 (c), line 6 (the dominant color class `Δ_j`, `|Δ_j| > m/2`), line 8 (`H` and
`ψ : H → S(Γ*)`, *"the natural epimorphism"*), and Eq. (73) (`m* ≤ m/2`, which is
`Babai.Align_johnson_param_halved` in case (B) and
`Babai.Align_equipartition_param_halved` in case (A)).

The field `stab` is what makes `Δ_j` the vertex set of `Y`: an automorphism of `Y` permutes
`Δ_j`.  It is what carries the window `Ω(Δ_j)` into itself
(`Babai.AlignDominant.isInvariant_window`).

This structure deliberately says nothing about *which* structure on `Δ_j` the group `H`
preserves.  Everything that depends on that lives in `Babai.AlignDominantA` and
`Babai.AlignDominantB`. -/
structure AlignDominant (Ω : Type u) [Fintype Ω] [DecidableEq Ω] where
  /-- Sec. 14, Situation: the group of the instance. -/
  G : Subgroup (Equiv.Perm Ω)
  /-- Sec. 14, Situation: *"a transitive group `G ≤ S(Ω)`"*. -/
  transitive : IsTransitive G
  /-- `|Γ| = m`. -/
  m : ℕ
  /-- Sec. 14, Situation: the giant representation `ϕ : G → S(Γ)`. -/
  ϕ : G →* Equiv.Perm (Fin m)
  /-- `ϕ` is a giant representation. -/
  giant : IsGiantRep ϕ
  /-- The numeric hypothesis of Theorem 10.5.1 for `(G, ϕ)`. -/
  veryLarge : VeryLargeK m (maxOrbitLength G)
  /-- Theorem 10.5.1 (c): the common size `t_Δ` of the labels.  `G` is transitive, so there
  is one orbit and one value. -/
  t : ℕ
  /-- `t` is the label size of every point. -/
  t_const : ∀ u : Ω, tPoint ϕ u = t
  /-- Line 6: the dominant color class `Δ_j ⊆ Γ`. -/
  Δj : Set (Fin m)
  /-- Line 6: *"`|Δ_j| > m/2`"*. -/
  dominant : m < 2 * Δj.ncard
  /-- Line 7: `|Γ*| = m*`. -/
  ms : ℕ
  /-- Line 8: `H = Aut(Y)`. -/
  H : Subgroup (Equiv.Perm (Fin m))
  /-- An automorphism of `Y` permutes the vertex set `Δ_j` of `Y`. -/
  stab : ∀ h ∈ H, h '' Δj = Δj
  /-- Line 8: *"`ψ : H → S(Γ*)` the natural epimorphism"*. -/
  ψ : H →* Equiv.Perm (Fin ms)
  /-- Line 8: `ψ` is onto (`Babai.surjective_johnsonSchemePsi`,
  `Babai.surjective_equipartitionPsi`). -/
  ψ_surj : Function.Surjective ψ
  /-- Eq. (73): `m* ≤ m/2`. -/
  param_halved : 2 * ms ≤ m

namespace AlignDominant

variable (D : AlignDominant Ω)

/-- `m ≥ 9` is part of `VeryLargeK`. -/
theorem nine_le_m : 9 ≤ D.m := by
  have : (9 : ℝ) ≤ (D.m : ℝ) := le_trans (le_max_left _ _) D.veryLarge
  exact_mod_cast this

/-- `A(Γ)` is nontrivial, because `m ≥ 9 ≥ 5`. -/
theorem exists_alternating_ne_one :
    ∃ π : Equiv.Perm (Fin D.m), π ∈ alternatingGroup (Fin D.m) ∧ π ≠ 1 := by
  have h3 : 3 ≤ Fintype.card (Fin D.m) := by
    rw [Fintype.card_fin]; have := D.nine_le_m; omega
  haveI := alternatingGroup.nontrivial_of_three_le_card (α := Fin D.m) h3
  obtain ⟨π, hπ⟩ := exists_ne (1 : alternatingGroup (Fin D.m))
  exact ⟨(π : Equiv.Perm (Fin D.m)), π.2, fun h => hπ (Subtype.ext h)⟩

include D in
/-- `Ω` is nonempty.  If it were empty then `G` would be the trivial group, so `ϕ` would
have trivial image, contradicting `A(Γ) ≤ ϕ(G)` with `m ≥ 9`. -/
theorem nonempty : Nonempty Ω := by
  by_contra hcon
  rw [not_nonempty_iff] at hcon
  obtain ⟨π, hπmem, hπne⟩ := D.exists_alternating_ne_one
  obtain ⟨σ, hσ⟩ := D.giant hπmem
  have h1 : σ = 1 := Subtype.ext (Equiv.ext fun z => hcon.elim z)
  exact hπne (by rw [← hσ, h1, map_one])

/-- Theorem 10.5.1 (a): `4t < m`. -/
theorem four_mul_t_lt : 4 * D.t < D.m := by
  obtain ⟨u⟩ := D.nonempty
  have h := (theorem_10_5_1_a D.ϕ D.giant D.veryLarge u).1.1
  rw [show (Tpoint D.ϕ u).ncard = tPoint D.ϕ u from rfl, D.t_const u] at h
  exact h

/-- `t ≥ 1`: some point is affected by `ϕ`.

By Theorem 10.5.1 (b), `t = 0` says that no point of `Ω` is affected by `ϕ`.  Then the
Unaffected Stabilizers Theorem 10.3.5 gives `A(Γ) ≤ ϕ(G_(Ω))`, and `G_(Ω)` — the subgroup
fixing every point — is trivial, so `A(Γ)` would be trivial, contradicting `m ≥ 9`. -/
theorem one_le_t : 1 ≤ D.t := by
  by_contra hcon
  have ht0 : D.t = 0 := by omega
  have hall : unaffectedSet D.ϕ = (Set.univ : Set Ω) := by
    ext u
    simp only [Set.mem_univ, iff_true]
    show ¬ Affected D.ϕ u
    rw [theorem_10_5_1_b D.ϕ D.giant D.veryLarge u]
    rw [show (Tpoint D.ϕ u).ncard = tPoint D.ϕ u from rfl, D.t_const u, ht0]
    omega
  have hmain := theorem_10_3_5 D.ϕ D.giant D.veryLarge.largeK
  rw [hall] at hmain
  have hbot : pointwiseStab D.G (Set.univ : Set Ω) = ⊥ := by
    refine le_antisymm (fun σ hσ => ?_) bot_le
    rw [mem_pointwiseStab] at hσ
    exact Subgroup.mem_bot.2 (Subtype.ext (Equiv.ext fun x => hσ x (Set.mem_univ x)))
  rw [hbot] at hmain
  obtain ⟨π, hπmem, hπne⟩ := D.exists_alternating_ne_one
  obtain ⟨σ, hσmem, hσ⟩ := hmain hπmem
  rw [SetLike.mem_coe, Subgroup.mem_bot] at hσmem
  exact hπne (by rw [← hσ, hσmem, map_one])

/-- `2t < |Δ_j|`: from `4t < m` (Theorem 10.5.1 (a)) and `m < 2|Δ_j|` (line 6). -/
theorem two_mul_t_lt_ncard_Δj : 2 * D.t < D.Δj.ncard := by
  have h1 := D.four_mul_t_lt
  have h2 := D.dominant
  omega

/-- Line 9: `G* = ϕ⁻¹(H)`. -/
def Gs : Subgroup (Equiv.Perm Ω) := preimageSubgroup D.ϕ D.H

theorem Gs_le : D.Gs ≤ D.G := preimageSubgroup_le _ _

/-- Line 10: `ϕ* : G* → S(Γ*)`, *"the composition of `ϕ` restricted to `G*` and `ψ`"*. -/
def phis : D.Gs →* Equiv.Perm (Fin D.ms) := D.ψ.comp (phiStar D.ϕ D.H)

/-- §14.1, line 10, the parenthetical *"(: this is a giant representation :)"*.  This is
`Babai.Align_phiStar_isGiant`: every square of `S(Γ*)` is in the image of `ϕ*`, and the
`3`-cycles are squares. -/
theorem isGiantRep_phis : IsGiantRep D.phis :=
  Align_phiStar_isGiant D.ϕ D.giant D.H D.ψ D.ψ_surj

/-- Line 11: the window `Ω(Δ_j) = ⋃_{T ⊆ Δ_j, |T| = t} B_T`, in the form of
`Babai.omegaOf`: the points whose label `T(u)` lies inside `Δ_j`. -/
def window : Set Ω := omegaOf D.ϕ D.Δj

/-- §14.1, line 11: the window `Ω(Δ_j)` is `G*`-invariant, so `G*` really does *"process
the corresponding window"*.  This is `Babai.isInvariant_omegaOf_of_le`: the labels
transform by `ϕ` (Eq. (54)), and `ϕ(G*) ≤ H` permutes `Δ_j`. -/
theorem isInvariant_window : IsInvariant D.Gs D.window := by
  refine isInvariant_omegaOf_of_le D.ϕ D.giant D.veryLarge D.Δj D.Gs D.Gs_le ?_
  intro τ hτ
  obtain ⟨hτG, hτH⟩ := mem_preimageSubgroup.1 hτ
  exact D.stab _ hτH

/-- The orbit of a point of the window stays inside the window. -/
theorem orbit_subset_window {u : Ω} (hu : u ∈ D.window) :
    orbit D.Gs u ⊆ D.window := by
  rintro _ ⟨σ, rfl⟩
  have := D.isInvariant_window (σ : Equiv.Perm Ω) σ.2
  rw [← this]
  exact ⟨u, hu, rfl⟩

/-- `3 ≤ m`, from `m ≥ 9`. -/
theorem three_le_m : 3 ≤ D.m := by have := D.nine_le_m; omega

/-- `2t ≤ m`, from Theorem 10.5.1 (a). -/
theorem two_mul_t_le : 2 * D.t ≤ D.m := by have := D.four_mul_t_lt; omega

/-- The label of a point has `t` elements. -/
theorem ncard_Tpoint (u : Ω) : (Tpoint D.ϕ u).ncard = D.t := D.t_const u

/-- A point of the window has its label inside `Δ_j`. -/
theorem Tpoint_subset_of_mem_window {u : Ω} (hu : u ∈ D.window) :
    Tpoint D.ϕ u ⊆ D.Δj := hu

/-- `ϕ*` is `ψ ∘ ϕ|_{G*}`, the shape `Workspace/Master/AlignDominantAux.lean` speaks in. -/
theorem phis_eq : D.phis = D.ψ.comp (phiStar D.ϕ D.H) := rfl

/-- The image under `ϕ` of an element of `G*`, read inside `H`. -/
theorem coe_phiStar_elt (σ : D.Gs) :
    ((phiStar D.ϕ D.H σ : D.H) : Equiv.Perm (Fin D.m))
      = D.ϕ ⟨(σ : Equiv.Perm Ω), D.Gs_le σ.2⟩ := rfl

/-- Eq. (54) for an element of `G*`: `T(u^σ) = T(u)^{ϕ(σ)}`. -/
theorem Tpoint_smul (σ : D.Gs) (u : Ω) :
    Tpoint D.ϕ ((σ : Equiv.Perm Ω) u)
      = ((phiStar D.ϕ D.H σ : D.H) : Equiv.Perm (Fin D.m)) '' Tpoint D.ϕ u := by
  rw [D.coe_phiStar_elt σ]
  exact theorem_10_5_1_c_eq54 D.ϕ D.giant D.veryLarge u ⟨(σ : Equiv.Perm Ω), D.Gs_le σ.2⟩

/-- **The shared first step of case 3**, on this structure: if `u` is unaffected by `ϕ*`
then every `π ∈ A(Γ*)` is `ψ(h)` for an `h ∈ H` stabilizing the label `T(u)` setwise.
This is `Babai.exists_mem_setwiseStab_map_eq_of_unaffected`. -/
theorem exists_stab_label_map_eq {u : Ω} (hu : u ∈ unaffectedSet D.phis)
    {π : Equiv.Perm (Fin D.ms)} (hπ : π ∈ alternatingGroup (Fin D.ms)) :
    ∃ h : D.H, (h : Equiv.Perm (Fin D.m)) '' Tpoint D.ϕ u = Tpoint D.ϕ u ∧ D.ψ h = π :=
  exists_mem_setwiseStab_map_eq_of_unaffected D.ϕ D.giant D.veryLarge D.H D.ψ hu hπ

/-! ### Case 3 of the repair: the facts that do not need the structure `Y`

The lemmas of this section are the part of the repair proposed in the corrected paper
(Sec. 14.1–14.2, Procedure Align, "Smallest change", item 3) that can be stated and proved
without knowing which structure `H` preserves.  The estimate they take as an input — that
the unaffected part of the window is at most `2n/3` — is supplied once per case, by
`Babai.AlignDominantA.three_mul_ncard_unaffected_le` and by
`Babai.AlignDominantB.three_mul_ncard_unaffected_le`. -/

/-- Being unaffected is a property of the orbit (`Babai.unaffected_of_mem_orbit`). -/
theorem unaffected_of_orbit {u z : Ω} (hu : u ∈ unaffectedSet D.phis)
    (hz : z ∈ orbit D.Gs u) : z ∈ unaffectedSet D.phis := by
  obtain ⟨σ, rfl⟩ := hz
  exact unaffected_of_mem_orbit D.phis hu σ rfl

/-- **Case 3, first step**: the dominant orbit is affected by `ϕ*`.

If an orbit of `G*` inside the window has more than `2n/3` points then every one of its
points is affected: otherwise, by `Babai.AlignDominant.unaffected_of_orbit`, the whole orbit
would be unaffected, and it lies in the window, so it would be contained in the at most
`2n/3` unaffected points of the window.

The hypothesis `hun` is the case analysis of line 7; it is discharged by
`Babai.AlignDominantA.three_mul_ncard_unaffected_le` in case (A) and by
`Babai.AlignDominantB.three_mul_ncard_unaffected_le` in case (B). -/
theorem affected_of_dominant_orbit
    (hun : 3 * (D.window ∩ unaffectedSet D.phis).ncard ≤ 2 * Fintype.card Ω)
    {u : Ω} (hu : u ∈ D.window)
    (hbig : 2 * Fintype.card Ω < 3 * (orbit D.Gs u).ncard) :
    ∀ z ∈ orbit D.Gs u, Affected D.phis z := by
  intro z hz
  by_contra hcon
  have hzu : z ∈ unaffectedSet D.phis := hcon
  have hunsub : orbit D.Gs u ⊆ D.window ∩ unaffectedSet D.phis := by
    intro w hw
    refine ⟨D.orbit_subset_window hu hw, ?_⟩
    refine D.unaffected_of_orbit hzu ?_
    have h1 : orbit D.Gs z = orbit D.Gs u := orbit_eq_iff.2 hz
    rw [h1]
    exact hw
  have hle : (orbit D.Gs u).ncard ≤ (D.window ∩ unaffectedSet D.phis).ncard :=
    Set.ncard_le_ncard hunsub (Set.toFinite _)
  omega

/-- **Case 3, second step**: the pointwise stabilizer of an affected orbit lies in the
kernel of `ϕ*`.

*Why it is true.*  Write `N` for the pointwise stabilizer of the orbit `Δ₁` in `G*`.  It is
normal in `G*`, so `ϕ*(N)` is normal in `ϕ*(G*)`, and `A(Γ*) ≤ ϕ*(G*) ≤ S(Γ*)`
(`Babai.AlignDominant.isGiantRep_phis`).  Hence `ϕ*(N) ∩ A(Γ*)` is normal in `A(Γ*)`, which
is simple for `m* ≥ 5`, so it is trivial or all of `A(Γ*)`.

* If `A(Γ*) ≤ ϕ*(N)`: pick `z ∈ Δ₁` (the orbit is nonempty, it contains `u`).  Then
  `N ≤ G*_z`, so `A(Γ*) ≤ ϕ*(G*_z)`, that is, `z` is unaffected — contradicting `haff`.
* If `ϕ*(N) ∩ A(Γ*) = 1`: both are normal in `ϕ*(G*)`, so they commute elementwise, and
  the centralizer of `A(Γ*)` in `S(Γ*)` is trivial for `m* ≥ 5`.  So `ϕ*(N) = 1`.

This statement needs no case data: it uses only that `ϕ*` is giant and `m* ≥ 5`, both of
which `Babai.AlignDominant` already gives (`m* ≥ 5` is the hypothesis `hm5`, which in the
algorithm comes from *"`m*` is not below the threshold of Theorem 10.5.1"* — for
`m* ≤ 4` the round takes case 1 instead).

*In Lean*: the group-theoretic step is
`Babai.eq_one_or_alternating_le_of_conj_mem` (`Workspace/Master/AlignDominantAux.lean`),
which rests on `Babai.isSimpleGroup_alternatingGroup` and, for the trivial-intersection
case, on `Babai.eq_one_of_commute_alternating` (the centralizer of `A(Γ*)` in `S(Γ*)` is
trivial for `m* ≥ 4`). -/
theorem pointwiseStab_orbit_le_ker {u : Ω} (hm5 : 5 ≤ D.ms)
    (haff : ∀ z ∈ orbit D.Gs u, Affected D.phis z) :
    pointwiseStab D.Gs (orbit D.Gs u) ≤ D.phis.ker := by
  classical
  have hcard5 : 5 ≤ Fintype.card (Fin D.ms) := by rw [Fintype.card_fin]; exact hm5
  -- `N`, the pointwise stabilizer of the orbit, is normal in `G*`
  haveI hNnorm : (pointwiseStab D.Gs (orbit D.Gs u)).Normal :=
    pointwiseStab_normal (isInvariant_orbit D.Gs u)
  -- its image `Q` is normalized by `A(Γ*)`, because `A(Γ*) ≤ ϕ*(G*)`
  have hconj : ∀ a ∈ alternatingGroup (Fin D.ms),
      ∀ q ∈ (pointwiseStab D.Gs (orbit D.Gs u)).map D.phis,
        a * q * a⁻¹ ∈ (pointwiseStab D.Gs (orbit D.Gs u)).map D.phis := by
    intro a ha q hq
    obtain ⟨n, hn, rfl⟩ := hq
    obtain ⟨σ, hσ⟩ := D.isGiantRep_phis ha
    refine ⟨σ * n * σ⁻¹, hNnorm.conj_mem n hn σ, ?_⟩
    rw [map_mul, map_mul, map_inv, hσ]
  rcases eq_one_or_alternating_le_of_conj_mem hcard5 _ hconj with h1 | h2
  · intro n hn
    exact MonoidHom.mem_ker.2 (h1 _ ⟨n, hn, rfl⟩)
  · exfalso
    refine haff u (mem_orbit_self u) (h2.trans (Subgroup.map_mono ?_))
    intro n hn
    rw [MulAction.mem_stabilizer_iff]
    exact (mem_pointwiseStab.1 hn) u (mem_orbit_self u)

/-- **Case 3, the other orbits**: if one orbit has more than `2n/3` points then every other
orbit has fewer than `n/3`, hence at most `2n/3`.

This is the paper's *"The total contribution of all other `Ω_i` to the right-hand side of
Eq. (71) is at most `q(m) T(n/3)`"* (Sec. 14.2), read one orbit at a time: distinct orbits
are disjoint, so what is left over is `n - |Δ₁| < n/3`. -/
theorem other_orbit_small {u v : Ω}
    (hbig : 2 * Fintype.card Ω < 3 * (orbit D.Gs u).ncard)
    (hne : v ∉ orbit D.Gs u) :
    3 * (orbit D.Gs v).ncard < Fintype.card Ω := by
  classical
  have hdisj : Disjoint (orbit D.Gs u) (orbit D.Gs v) := by
    rw [Set.disjoint_left]
    intro w hwu hwv
    exact hne (by
      have h1 : orbit D.Gs w = orbit D.Gs u := orbit_eq_iff.2 hwu
      have h2 : orbit D.Gs w = orbit D.Gs v := orbit_eq_iff.2 hwv
      rw [← h1, h2]
      exact mem_orbit_self v)
  have hsum : (orbit D.Gs u).ncard + (orbit D.Gs v).ncard
      = (orbit D.Gs u ∪ orbit D.Gs v).ncard :=
    (Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _)).symm
  have hle : (orbit D.Gs u ∪ orbit D.Gs v).ncard ≤ Fintype.card Ω := by
    have h := Set.ncard_le_ncard (Set.subset_univ (orbit D.Gs u ∪ orbit D.Gs v))
      (Set.toFinite (Set.univ : Set Ω))
    rwa [Set.ncard_univ, Nat.card_eq_fintype_card] at h
  omega

end AlignDominant

/-! ## Line 7 (A): a nontrivial equipartition of `Δ_j` -/

/-- §14.1, line 7 (A): *"if `X` gives a nontrivial equipartition of `Δ_j` then let `Y` be
this equivalence relation on `Δ_j` and `Γ*` the set of blocks"*.

The equipartition is given by its block map `block : Γ → Γ*`, of which only the restriction
to `Δ_j` matters.  *Nontrivial* is the pair of conditions `m* ≥ 2` (at least two blocks) and
`blockSize ≥ 2` (each block has at least two points); these are exactly the hypotheses of
`Babai.Align_equipartition_param_halved`, which is where Eq. (73) comes from in this case.

The field `psi_block` is line 8 in this case: `ψ` is *"the natural epimorphism"*, the action
of an automorphism on the blocks.  It is `Babai.equipartitionPsi_spec` transported to the
ambient set `Γ`; `Babai.surjective_equipartitionPsi` is why `ψ_surj` holds. -/
structure AlignDominantA (Ω : Type u) [Fintype Ω] [DecidableEq Ω] extends
    AlignDominant Ω where
  /-- *Nontrivial*: there are at least two blocks. -/
  ms_two : 2 ≤ ms
  /-- The common size of a block. -/
  blockSize : ℕ
  /-- *Nontrivial*: each block has at least two points. -/
  blockSize_two : 2 ≤ blockSize
  /-- The block map of the equipartition. -/
  block : Fin m → Fin ms
  /-- *Equi*-partition: every block meets `Δ_j` in the same number of points, and every
  element of `Γ*` really is a block. -/
  block_card : ∀ γ : Fin ms, (Δj ∩ block ⁻¹' {γ}).ncard = blockSize
  /-- Line 8: `ψ` is the induced action on the blocks. -/
  psi_block : ∀ (h : H) (d : Fin m), d ∈ Δj →
    block ((h : Equiv.Perm (Fin m)) d) = ψ h (block d)

namespace AlignDominantA

variable (D : AlignDominantA Ω)

/-! ### The color vector of a label

Lemma 7.2.1 colors a `t`-subset `T ⊆ Γ` by the vector `γ ↦ |T ∩ block⁻¹(γ)|`
(`Babai.tupleColor`).  The two counting lemmas below both work by showing that the set they
bound lies inside one color class of the coloring of `Φ = (Γ choose t)` that the block map
induces, and then quoting Lemma 7.2.1 (a). -/

/-- An `h ∈ H` that carries a set `T ⊆ Δ_j` of `Γ` onto itself permutes the color vector of
`T` by `ψ(h)`: it maps `T ∩ block⁻¹(γ)` bijectively onto `T ∩ block⁻¹(ψ(h) γ)`, by
`psi_block`. -/
theorem tupleColor_psi_apply (h : D.H) {T : Finset (Fin D.m)}
    (hTΔ : ∀ d ∈ T, d ∈ D.Δj)
    (himg : (h : Equiv.Perm (Fin D.m)) '' (T : Set (Fin D.m)) = (T : Set (Fin D.m)))
    (γ : Fin D.ms) :
    tupleColor D.block T (D.ψ h γ) = tupleColor D.block T γ := by
  classical
  have hmem : ∀ d, ((h : Equiv.Perm (Fin D.m)) d ∈ T ↔ d ∈ T) := by
    intro d
    constructor
    · intro hd
      have hd' : (h : Equiv.Perm (Fin D.m)) d ∈
          (h : Equiv.Perm (Fin D.m)) '' (T : Set (Fin D.m)) := by rw [himg]; exact hd
      obtain ⟨e, he, hed⟩ := hd'
      rwa [(h : Equiv.Perm (Fin D.m)).injective hed] at he
    · intro hd
      have hd' : (h : Equiv.Perm (Fin D.m)) d ∈
          (h : Equiv.Perm (Fin D.m)) '' (T : Set (Fin D.m)) := ⟨d, hd, rfl⟩
      rw [himg] at hd'; exact hd'
  symm
  show (T.filter fun d => D.block d = γ).card
    = (T.filter fun d => D.block d = D.ψ h γ).card
  refine Finset.card_nbij' (fun d => (h : Equiv.Perm (Fin D.m)) d)
    (fun d => (h : Equiv.Perm (Fin D.m))⁻¹ d) ?_ ?_ ?_ ?_
  · intro d hd
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at hd ⊢
    exact ⟨(hmem d).2 hd.1, by rw [D.psi_block h d (hTΔ d hd.1), hd.2]⟩
  · intro d hd
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at hd ⊢
    have hd1 : (h : Equiv.Perm (Fin D.m))⁻¹ d ∈ T := by
      rw [← hmem]; simpa using hd.1
    refine ⟨hd1, ?_⟩
    have hps := D.psi_block h ((h : Equiv.Perm (Fin D.m))⁻¹ d) (hTΔ _ hd1)
    have hdd : (h : Equiv.Perm (Fin D.m)) ((h : Equiv.Perm (Fin D.m))⁻¹ d) = d := by simp
    rw [hdd] at hps
    exact (D.ψ h).injective (by rw [← hps]; exact hd.2)
  · intro d _; simp
  · intro d _; simp

/-- **Case 3, the key estimate, in case (A)**: the points of the window that `ϕ*` leaves
*unaffected* are at most two thirds of `Ω`.

*Why it is true* (the corrected paper Align, "Smallest change", item 3).  Let
`u ∈ B_T` be a point of the window, so `T = T(u) ⊆ Δ_j` and `|T| = t`.  Then
`ϕ*(G*_u) = ψ(ϕ(G_u) ∩ H)`, and Theorem 10.5.1 (a) sandwiches `ϕ(G_u)` between the pointwise
stabilizer of `T` in `A(Γ)` and the setwise stabilizer of `T` in `S(Γ)`.  So if `u` is
unaffected then `A(Γ*) ≤ ψ(H_T)`, the image of the setwise stabilizer of `T` in `H`.

An element `h ∈ H_T` maps `T ∩ block⁻¹(γ)` bijectively onto `T ∩ block⁻¹(ψ(h) γ)`, by
`psi_block` and `h '' T = T`.  So every element of `ψ(H_T)` preserves the color vector
`γ ↦ |T ∩ block⁻¹(γ)|` of Lemma 7.2.1.  Now `m* ≥ 9` (from `hvl`, the hypothesis of case 3),
so `A(Γ*)` is transitive on `Γ*`, and `A(Γ*) ≤ ψ(H_T)` forces that vector to be constant.

The `T ⊆ Δ_j` with a constant color vector form one color class of the coloring of
`(Δ_j choose t)` induced by the equipartition.  Its color vector is not exceptional: it is
constant with sum `t ≥ 1` over `m* ≥ 2` blocks, so no coordinate equals `t`.  Lemma 7.2.1
(a) (`Babai.lemma_7_2_1a`, applicable because `2t < |Δ_j|` by
`Babai.AlignDominant.two_mul_t_lt_ncard_Δj`) bounds that class by `(2/3)·C(|Δ_j|, t)`.
Multiplying by the common size of a standard block, and using `C(|Δ_j|, t) ≤ C(m, t)`,
gives the bound on `Ω`, exactly as in `Babai.three_mul_ncard_omegaCut_le`.

*In Lean*: the passage from *"`u` is unaffected"* to *"`A(Γ*) ≤ ψ(H_T)`"* is
`Babai.AlignDominant.exists_stab_label_map_eq`, the action of `ψ(H_T)` on the color vector
is `Babai.AlignDominantA.tupleColor_psi_apply`, and the transitivity of `A(Γ*)` on `Γ*` is
`Babai.exists_mem_image_eq_of_ncard_eq` on singletons.  Lemma 7.2.1 (a) is *not* transferred
to `Δ_j`: it is quoted on all of `Γ`, which is enough, because the bound is multiplied by
the common size of a standard block and `n = C(m,t)·b`.

The hypothesis `hvl` is *"`m*` is not below the threshold of Theorem 10.5.1"*, that is, the
statement that the round is in case 3 rather than case 1.  It cannot be dropped: for
`m* = 2` the group `A(Γ*)` is trivial, so **every** point is unaffected by `ϕ*` and the
conclusion fails. -/
theorem three_mul_ncard_unaffected_le
    (hvl : VeryLargeK D.ms (maxOrbitLength D.toAlignDominant.Gs)) :
    3 * (D.toAlignDominant.window ∩ unaffectedSet D.toAlignDominant.phis).ncard
      ≤ 2 * Fintype.card Ω := by
  classical
  have hms9 : 9 ≤ D.ms := by
    have : (9 : ℝ) ≤ (D.ms : ℝ) := le_trans (le_max_left _ _) hvl
    exact_mod_cast this
  haveI : Nonempty (Fin D.ms) := ⟨⟨0, by omega⟩⟩
  have ht1 := D.toAlignDominant.one_le_t
  have h2t := D.toAlignDominant.two_mul_t_le
  have hm3 := D.toAlignDominant.three_le_m
  set v : Fin D.ms → ℕ := fun _ => D.t / D.ms with hv
  -- every unaffected point of the window carries the constant color vector `t / m*`
  have hsub : D.toAlignDominant.window ∩ unaffectedSet D.toAlignDominant.phis ⊆
      ↑(labelPreim D.ϕ (tupleClass D.block D.t v)) := by
    rintro u ⟨huw, hun⟩
    have hTΔ : ∀ d ∈ labelF D.ϕ u, d ∈ D.Δj := fun d hd =>
      D.toAlignDominant.Tpoint_subset_of_mem_window huw (mem_labelF.1 hd)
    have hcard : (labelF D.ϕ u).card = D.t := by rw [card_labelF, D.t_const u]
    -- `A(Γ*)` is transitive on `Γ*`, and `ψ(H_T)` contains it, so the vector is constant
    have hconst : ∀ γ γ' : Fin D.ms,
        tupleColor D.block (labelF D.ϕ u) γ = tupleColor D.block (labelF D.ϕ u) γ' := by
      intro γ γ'
      obtain ⟨π, hπ, hπeq⟩ := exists_mem_image_eq_of_ncard_eq (Ω := Fin D.ms)
        (K := alternatingGroup (Fin D.ms)) le_rfl
        (T := ({γ} : Set (Fin D.ms))) (U := ({γ'} : Set (Fin D.ms)))
        (Set.ncard_singleton γ) (Set.ncard_singleton γ')
        (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega)
      have hπγ : π γ = γ' := by
        have hmem : π γ ∈ ({γ'} : Set (Fin D.ms)) := by rw [← hπeq]; exact ⟨γ, rfl, rfl⟩
        simpa using hmem
      obtain ⟨h, hhT, hhψ⟩ := D.toAlignDominant.exists_stab_label_map_eq hun hπ
      have hcol := D.tupleColor_psi_apply h hTΔ (by rw [coe_labelF]; exact hhT) γ
      rw [hhψ, hπγ] at hcol
      exact hcol.symm
    have hsum : ∑ γ : Fin D.ms, tupleColor D.block (labelF D.ϕ u) γ = D.t := by
      rw [sum_tupleColor, hcard]
    have hall : tupleColor D.block (labelF D.ϕ u) = v := by
      funext γ
      have hs2 : ∑ γ' : Fin D.ms, tupleColor D.block (labelF D.ϕ u) γ'
          = D.ms * tupleColor D.block (labelF D.ϕ u) γ := by
        rw [Finset.sum_congr rfl (fun γ' _ => hconst γ' γ), Finset.sum_const,
          Finset.card_univ, Fintype.card_fin, smul_eq_mul]
      rw [hs2] at hsum
      show tupleColor D.block (labelF D.ϕ u) γ = D.t / D.ms
      rw [← hsum, Nat.mul_div_cancel_left _ (by omega : 0 < D.ms)]
    refine Finset.mem_coe.2 ?_
    simp only [labelPreim, Finset.mem_filter, Finset.mem_univ, true_and]
    exact mem_tupleClass.2 ⟨hcard, hall⟩
  -- Lemma 7.2.1 (a): the constant vector is not exceptional, because `t / m* < t`
  have hvne : ∀ i : Fin D.ms, v i ≠ D.t :=
    fun _ => Nat.ne_of_lt (Nat.div_lt_self (by omega) (by omega))
  obtain ⟨T₀, hT₀⟩ : ∃ T₀ : Finset (Fin D.m), T₀.card = D.t := by
    obtain ⟨T₀, -, hT₀⟩ := Finset.exists_subset_card_eq
      (s := (Finset.univ : Finset (Fin D.m))) (n := D.t)
      (by rw [Finset.card_univ, Fintype.card_fin]; omega)
    exact ⟨T₀, hT₀⟩
  have h721 := lemma_7_2_1a (Γ := Fin D.m) (ι := Fin D.ms) D.block
    (t := D.t) (by rw [Fintype.card_fin]; exact h2t) (v := v) hvne
  rw [card_Phi, Fintype.card_fin] at h721
  have hpre := card_labelPreim_eq_mul (Ω := Ω) D.ϕ D.giant D.veryLarge hm3
    (tupleClass D.block D.t v) (fun T hT => (mem_tupleClass.1 hT).1) T₀ hT₀
  have hn := card_univ_eq_mul D.transitive D.ϕ D.giant D.veryLarge hm3 D.t_const T₀ hT₀
  have hle : (D.toAlignDominant.window ∩ unaffectedSet D.toAlignDominant.phis).ncard
      ≤ (labelPreim (Ω := Ω) D.ϕ (tupleClass D.block D.t v)).card := by
    have h := Set.ncard_le_ncard hsub (Set.toFinite _)
    rwa [Set.ncard_coe_finset] at h
  rw [hpre] at hle
  rw [hn]
  calc 3 * (D.toAlignDominant.window ∩ unaffectedSet D.toAlignDominant.phis).ncard
      ≤ 3 * ((tupleClass D.block D.t v).card * (labelFiber (Ω := Ω) D.ϕ T₀).card) :=
        Nat.mul_le_mul_left _ hle
    _ = (3 * (tupleClass D.block D.t v).card) * (labelFiber (Ω := Ω) D.ϕ T₀).card := by ring
    _ ≤ (2 * D.m.choose D.t) * (labelFiber (Ω := Ω) D.ϕ T₀).card :=
        Nat.mul_le_mul_right _ h721
    _ = 2 * (D.m.choose D.t * (labelFiber (Ω := Ω) D.ϕ T₀).card) := by ring

/-- In case (A) the kernel of `ψ` fixes every block of the equipartition setwise, so for
`σ ∈ ker ϕ*` and `u` in the window the label `T(u^σ) = T(u)^{ϕ(σ)}` stays inside `Δ_j` and
keeps its color vector. -/
theorem tupleColor_smul_ker (σ : D.toAlignDominant.Gs)
    (hσ : D.toAlignDominant.phis σ = 1) {u : Ω} (hu : u ∈ D.toAlignDominant.window) :
    (∀ d ∈ labelF D.ϕ ((σ : Equiv.Perm Ω) u), d ∈ D.Δj) ∧
      tupleColor D.block (labelF D.ϕ ((σ : Equiv.Perm Ω) u))
        = tupleColor D.block (labelF D.ϕ u) := by
  classical
  have hTsub : Tpoint D.ϕ u ⊆ D.Δj := D.toAlignDominant.Tpoint_subset_of_mem_window hu
  set h : D.H := phiStar D.ϕ D.H σ with hhdef
  have hψ1 : D.ψ h = 1 := hσ
  have hblock : ∀ d ∈ D.Δj, D.block ((h : Equiv.Perm (Fin D.m)) d) = D.block d := by
    intro d hd; rw [D.psi_block h d hd, hψ1]; rfl
  have himg : Tpoint D.ϕ ((σ : Equiv.Perm Ω) u)
      = (h : Equiv.Perm (Fin D.m)) '' Tpoint D.ϕ u := D.toAlignDominant.Tpoint_smul σ u
  have hhΔ : (h : Equiv.Perm (Fin D.m)) '' D.Δj = D.Δj := D.stab _ h.2
  refine ⟨?_, ?_⟩
  · intro d hd
    rw [mem_labelF, himg] at hd
    obtain ⟨e, he, rfl⟩ := hd
    rw [← hhΔ]
    exact ⟨e, hTsub he, rfl⟩
  · funext γ
    show ((labelF D.ϕ ((σ : Equiv.Perm Ω) u)).filter fun d => D.block d = γ).card
      = ((labelF D.ϕ u).filter fun d => D.block d = γ).card
    symm
    refine Finset.card_nbij' (fun d => (h : Equiv.Perm (Fin D.m)) d)
      (fun d => (h : Equiv.Perm (Fin D.m))⁻¹ d) ?_ ?_ ?_ ?_
    · intro d hd
      simp only [Finset.coe_filter, Set.mem_setOf_eq, mem_labelF, himg] at hd ⊢
      exact ⟨⟨d, hd.1, rfl⟩, by rw [hblock d (hTsub hd.1)]; exact hd.2⟩
    · intro d hd
      simp only [Finset.coe_filter, Set.mem_setOf_eq, mem_labelF, himg] at hd ⊢
      obtain ⟨⟨e, he, hed⟩, hdγ⟩ := hd
      have hinv : (h : Equiv.Perm (Fin D.m))⁻¹ d = e := by
        rw [← hed]; simp
      rw [hinv]
      refine ⟨he, ?_⟩
      rw [← hblock e (hTsub he), hed]
      exact hdγ
    · intro d _; simp
    · intro d _; simp

/-- **Case 1, in case (A)**: the orbits of `ker ϕ*` on the window are at most `2n/3`.

*Why it is true* (the corrected paper Align, "Smallest change", item 1).  An element
`σ ∈ ker ϕ*` has `ϕ(σ) ∈ H` with `ψ(ϕ(σ)) = 1`, so by `psi_block` it fixes every block of
the equipartition setwise.  By Eq. (54) the label moves as `T(σ·u) = ϕ(σ)''T(u)`, so for
`u` in the window the labels along the orbit of `u` all have the same color vector
`γ ↦ |T ∩ block⁻¹(γ)|`.  The orbit therefore lies inside one color class of
`(Δ_j choose t)`, lifted to `Ω`.

A color class is small, in both of the two possible ways:

* if its color vector is not exceptional, Lemma 7.2.1 (a) (`Babai.lemma_7_2_1a`) gives
  `3·|class| ≤ 2·C(|Δ_j|, t)`;
* if it is exceptional, all `t` elements of `T` lie in one block `P`, and the class is
  `(P choose t)`.  From `m* ≥ 2` we get `2|P| ≤ |Δ_j|`, hence
  `C(|P|, t) ≤ C(|Δ_j|, t)/2` for `t ≥ 1`, which is stronger than needed.

  (This second half is a refinement of the corrected paper, which appeals to Lemma 7.2.1
  alone; Lemma 7.2.1 (a) explicitly excludes the exceptional vectors.)

Multiplying by the common size of a standard block, and using `C(|Δ_j|, t) ≤ C(m, t)`,
turns this into the bound on `Ω`.

*In Lean*: the containment of the orbit in a color class is
`Babai.AlignDominantA.tupleColor_smul_ker`.  The class is intersected with
*"all elements lie in `Δ_j`"*, which is what makes the exceptional half work: an
exceptional `T` lies in `Δ_j ∩ block⁻¹(γ₀)`, of size `blockSize`, and `2·blockSize ≤ m`
because two distinct parts are disjoint subsets of `Δ_j`.

The hypothesis `hu` cannot be dropped: outside the window the label of `u` meets
`Γ ∖ Δ_j`, where `ker ψ` is unconstrained. -/
theorem three_mul_ncard_orbit_ker_le {u : Ω} (hu : u ∈ D.toAlignDominant.window) :
    3 * (orbit D.toAlignDominant.phis.ker u).ncard ≤ 2 * Fintype.card Ω := by
  classical
  haveI : Nonempty (Fin D.ms) := ⟨⟨0, by have := D.ms_two; omega⟩⟩
  have ht1 := D.toAlignDominant.one_le_t
  have h2t := D.toAlignDominant.two_mul_t_le
  have hm3 := D.toAlignDominant.three_le_m
  set v := tupleColor D.block (labelF D.ϕ u) with hvdef
  set S : Finset (Finset (Fin D.m)) :=
    (tupleClass D.block D.t v).filter (fun T => ∀ d ∈ T, d ∈ D.Δj) with hSdef
  -- the orbit lies inside the class of `Φ(Δ_j)` with the colour vector of `T(u)`
  have hsubset : orbit D.toAlignDominant.phis.ker u ⊆ ↑(labelPreim D.ϕ S) := by
    rintro _ ⟨σ, rfl⟩
    obtain ⟨hΔ, hcol⟩ := D.tupleColor_smul_ker (σ : D.toAlignDominant.Gs)
      (MonoidHom.mem_ker.1 σ.2) hu
    refine Finset.mem_coe.2 (Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩)
    exact Finset.mem_filter.2
      ⟨mem_tupleClass.2 ⟨by rw [card_labelF, D.t_const _], hcol⟩, hΔ⟩
  have hScard : ∀ T ∈ S, T.card = D.t := fun T hT =>
    (mem_tupleClass.1 (Finset.mem_filter.1 hT).1).1
  -- `|S| ≤ (2/3)·C(m,t)`, in the two ways the colour vector can behave
  have hSbound : 3 * S.card ≤ 2 * D.m.choose D.t := by
    by_cases hexc : ∀ i : Fin D.ms, v i ≠ D.t
    · -- not exceptional: Lemma 7.2.1 (a)
      have h721 := lemma_7_2_1a (Γ := Fin D.m) (ι := Fin D.ms) D.block
        (t := D.t) (by rw [Fintype.card_fin]; exact h2t) (v := v) hexc
      rw [card_Phi, Fintype.card_fin] at h721
      have : S.card ≤ (tupleClass D.block D.t v).card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      omega
    · -- exceptional: all `t` elements of `T` lie in one part `P`, and `2|P| ≤ |Δ_j| ≤ m`
      push_neg at hexc
      obtain ⟨γ₀, hγ₀⟩ := hexc
      set B : Fin D.ms → Finset (Fin D.m) :=
        fun γ => Finset.univ.filter (fun d => d ∈ D.Δj ∧ D.block d = γ) with hBdef
      have hBcoe : ∀ γ, ((B γ : Finset (Fin D.m)) : Set (Fin D.m))
          = D.Δj ∩ D.block ⁻¹' {γ} := by
        intro γ
        ext d
        simp [hBdef, Set.mem_preimage]
      have hBcard : ∀ γ, (B γ).card = D.blockSize := by
        intro γ
        have := D.block_card γ
        rw [← hBcoe γ, Set.ncard_coe_finset] at this
        exact this
      -- two distinct blocks are disjoint subsets of `Δ_j`
      have h2bs : 2 * D.blockSize ≤ D.m := by
        obtain ⟨γ₁, hγ₁⟩ := Fintype.exists_ne_of_one_lt_card
          (by rw [Fintype.card_fin]; have := D.ms_two; omega) γ₀
        have hdisj : Disjoint (B γ₁) (B γ₀) := by
          rw [Finset.disjoint_left]
          intro d h1 h0
          simp only [hBdef, Finset.mem_filter] at h1 h0
          exact hγ₁ (h1.2.2.symm.trans h0.2.2)
        have hsubΔ : B γ₁ ∪ B γ₀ ⊆ Finset.univ.filter (fun d => d ∈ D.Δj) := by
          intro d hd
          simp only [hBdef, Finset.mem_union, Finset.mem_filter] at hd ⊢
          rcases hd with hd | hd
          · exact ⟨Finset.mem_univ _, hd.2.1⟩
          · exact ⟨Finset.mem_univ _, hd.2.1⟩
        have hcardu := Finset.card_union_of_disjoint hdisj
        have hle := Finset.card_le_card hsubΔ
        have hΔle : (Finset.univ.filter (fun d => d ∈ D.Δj)).card ≤ D.m := by
          have := Finset.card_filter_le (Finset.univ : Finset (Fin D.m)) (fun d => d ∈ D.Δj)
          rw [Finset.card_univ, Fintype.card_fin] at this
          exact this
        rw [hBcard, hBcard] at hcardu
        omega
      -- every member of `S` is a `t`-subset of the part `B γ₀`
      have hSsub : S ⊆ (B γ₀).powersetCard D.t := by
        intro T hT
        rw [Finset.mem_filter] at hT
        obtain ⟨hTc, hTΔ⟩ := hT
        obtain ⟨hTcard, hTcol⟩ := mem_tupleClass.1 hTc
        have hfil : (T.filter fun d => D.block d = γ₀).card = T.card := by
          have : tupleColor D.block T γ₀ = D.t := by rw [hTcol]; exact hγ₀
          rw [hTcard]
          exact this
        have hfeq : T.filter (fun d => D.block d = γ₀) = T :=
          Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (le_of_eq hfil.symm)
        rw [Finset.mem_powersetCard]
        refine ⟨fun d hd => ?_, hTcard⟩
        have hd' : d ∈ T.filter fun d => D.block d = γ₀ := by rw [hfeq]; exact hd
        rw [Finset.mem_filter] at hd'
        simp only [hBdef, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hTΔ d hd, hd'.2⟩
      have hcard1 : S.card ≤ D.blockSize.choose D.t := by
        have := Finset.card_le_card hSsub
        rwa [Finset.card_powersetCard, hBcard] at this
      have hcard2 : 2 * D.blockSize.choose D.t ≤ D.m.choose D.t :=
        two_mul_choose_le_of_two_mul_le ht1 h2bs
      omega
  -- multiply by the common size of a standard block
  obtain ⟨T₀, hT₀⟩ : ∃ T₀ : Finset (Fin D.m), T₀.card = D.t := by
    obtain ⟨T₀, -, hT₀⟩ := Finset.exists_subset_card_eq
      (s := (Finset.univ : Finset (Fin D.m))) (n := D.t)
      (by rw [Finset.card_univ, Fintype.card_fin]; omega)
    exact ⟨T₀, hT₀⟩
  have hpre := card_labelPreim_eq_mul (Ω := Ω) D.ϕ D.giant D.veryLarge hm3 S hScard T₀ hT₀
  have hn := card_univ_eq_mul D.transitive D.ϕ D.giant D.veryLarge hm3 D.t_const T₀ hT₀
  have hle : (orbit D.toAlignDominant.phis.ker u).ncard
      ≤ (labelPreim (Ω := Ω) D.ϕ S).card := by
    have h := Set.ncard_le_ncard hsubset (Set.toFinite _)
    rwa [Set.ncard_coe_finset] at h
  rw [hpre] at hle
  rw [hn]
  calc 3 * (orbit D.toAlignDominant.phis.ker u).ncard
      ≤ 3 * (S.card * (labelFiber (Ω := Ω) D.ϕ T₀).card) := Nat.mul_le_mul_left _ hle
    _ = (3 * S.card) * (labelFiber (Ω := Ω) D.ϕ T₀).card := by ring
    _ ≤ (2 * D.m.choose D.t) * (labelFiber (Ω := Ω) D.ϕ T₀).card :=
        Nat.mul_le_mul_right _ hSbound
    _ = 2 * (D.m.choose D.t * (labelFiber (Ω := Ω) D.ϕ T₀).card) := by ring

/-- **Case 3 of the repair, packaged, in case (A)**: what the round needs about the largest
orbit.  If an orbit of `G*` inside the window has more than `2n/3` points then all of its
points are affected by `ϕ*` and its pointwise stabilizer lies in `ker ϕ*`, so `ϕ*` factors
through the transitive group `G*^{Δ₁}` and Theorem 10.5.1 (e) applies to it.

The hypothesis `hvl` is *"`m*` is not below the threshold of Theorem 10.5.1"*, that is,
*"the round is in case 3, not case 1"*.  It gives `m* ≥ 9 ≥ 5`, which is what
`Babai.AlignDominant.pointwiseStab_orbit_le_ker` needs. -/
theorem affected_and_pointwiseStab_le_ker
    (hvl : VeryLargeK D.ms (maxOrbitLength D.toAlignDominant.Gs))
    {u : Ω} (hu : u ∈ D.toAlignDominant.window)
    (hbig : 2 * Fintype.card Ω < 3 * (orbit D.toAlignDominant.Gs u).ncard) :
    (∀ z ∈ orbit D.toAlignDominant.Gs u, Affected D.toAlignDominant.phis z) ∧
      pointwiseStab D.toAlignDominant.Gs (orbit D.toAlignDominant.Gs u)
        ≤ D.toAlignDominant.phis.ker := by
  have hms9 : 9 ≤ D.ms := by
    have : (9 : ℝ) ≤ (D.ms : ℝ) := le_trans (le_max_left _ _) hvl
    exact_mod_cast this
  have haff := D.toAlignDominant.affected_of_dominant_orbit
    (D.three_mul_ncard_unaffected_le hvl) hu hbig
  exact ⟨haff, D.toAlignDominant.pointwiseStab_orbit_le_ker (by omega) haff⟩

end AlignDominantA

/-! ## Line 7 (B): a Johnson scheme on `Δ_j` -/

/-- §14.1, line 7 (B): *"if `Δ_j` is the vertex set of a Johnson scheme `J(m*, t*)`
(`t* ≥ 2`) then identify `Δ_j` with `(Γ* choose t*)`, `|Γ*| = m*`, and let `Y` denote this
Johnson scheme"*.

The identification is the map `label : Γ → 𝒫(Γ*)`, of which only the restriction to `Δ_j`
matters: on `Δ_j` it is a bijection onto the `t*`-subsets of `Γ*` (`label_ncard`,
`label_inj`, `label_surj`).  `ts_two` and `ms_ge` are the parameters of a Johnson scheme
(Def. 3.2.9), which are the hypotheses of `Babai.Align_johnson_param_halved`, the source of
Eq. (73) in this case.

The field `psi_label` is line 8 in this case: an automorphism of a Johnson scheme is
`π^{(t*)}` for exactly one `π ∈ S(Γ*)`, and `ψ` returns that `π`
(`Babai.johnsonSchemePsi`, `Babai.surjective_johnsonSchemePsi`). -/
structure AlignDominantB (Ω : Type u) [Fintype Ω] [DecidableEq Ω] extends
    AlignDominant Ω where
  /-- Line 7 (B): `t* ≥ 2`. -/
  ts : ℕ
  /-- Line 7 (B): *"`t* ≥ 2`"*. -/
  ts_two : 2 ≤ ts
  /-- Def. 3.2.9: the parameters of a Johnson scheme satisfy `m* ≥ 2t* + 1`. -/
  ms_ge : 2 * ts + 1 ≤ ms
  /-- The identification of `Δ_j` with `(Γ* choose t*)`. -/
  label : Fin m → Set (Fin ms)
  /-- On `Δ_j` the label is a `t*`-subset. -/
  label_ncard : ∀ d ∈ Δj, (label d).ncard = ts
  /-- The identification is injective on `Δ_j`. -/
  label_inj : ∀ d ∈ Δj, ∀ d' ∈ Δj, label d = label d' → d = d'
  /-- The identification is onto `(Γ* choose t*)`. -/
  label_surj : ∀ T : Set (Fin ms), T.ncard = ts → ∃ d ∈ Δj, label d = T
  /-- Line 8: `ψ` returns the permutation of `Γ*` that induces the automorphism. -/
  psi_label : ∀ (h : H) (d : Fin m), d ∈ Δj →
    label ((h : Equiv.Perm (Fin m)) d) = ψ h '' label d

namespace AlignDominantB

variable (D : AlignDominantB Ω)

/-- **Case 3, the key estimate, in case (B)**: in case (B) there is no unaffected point in
the window at all.

*Why it is true* (the corrected paper Align, "Smallest change", item 3).  Let `u` be
a point of the window with label `T = T(u) ⊆ Δ_j`, `|T| = t`.  As in case (A), if `u` is
unaffected then `A(Γ*) ≤ ψ(H_T)`.  By `psi_label`, `ψ(H_T)` is the stabilizer of `T` for
the action of `S(Γ*)` on `Δ_j = (Γ* choose t*)`, so `A(Γ*)` stabilizes the set `T` of
vertices of the Johnson scheme.

But `A(Γ*)` is transitive on `(Γ* choose t*)` (`Babai.exists_mem_image_eq_of_ncard_eq`,
applicable because `m* ≥ 2t* + 1 ≥ t* + 2`), so an `A(Γ*)`-invariant subset of `Δ_j` is `∅`
or `Δ_j`.  Both are excluded: `|T| = t ≥ 1` by `Babai.AlignDominant.one_le_t`, and
`t < |Δ_j|` because `2t < |Δ_j|` (`Babai.AlignDominant.two_mul_t_lt_ncard_Δj`).

Unlike case (A) this needs no lower bound on `m*` beyond the one the Johnson parameters
already give: `m* ≥ 2t* + 1 ≥ 5`.

*In Lean*: the passage from *"`u` is unaffected"* to *"`A(Γ*) ≤ ψ(H_T)`"* is
`Babai.AlignDominant.exists_stab_label_map_eq`, and the transitivity of `A(Γ*)` on
`(Γ* choose t*)` is `Babai.exists_mem_image_eq_of_ncard_eq`. -/
theorem window_inter_unaffected_eq_empty :
    D.toAlignDominant.window ∩ unaffectedSet D.toAlignDominant.phis = ∅ := by
  classical
  rw [Set.eq_empty_iff_forall_notMem]
  rintro u ⟨huw, hun⟩
  -- the label of `u`, a `t`-subset of `Δ_j`
  have hTsub : Tpoint D.ϕ u ⊆ D.Δj := D.toAlignDominant.Tpoint_subset_of_mem_window huw
  have hTcard : (Tpoint D.ϕ u).ncard = D.t := D.toAlignDominant.ncard_Tpoint u
  have hinj : Set.InjOn D.label D.Δj := fun a ha b hb h => D.label_inj a ha b hb h
  -- `S = label '' T(u)`, a set of `t*`-subsets of `Γ*` of size `t`
  set S : Set (Set (Fin D.ms)) := D.label '' Tpoint D.ϕ u with hSdef
  have hScard : S.ncard = D.t := by
    rw [hSdef, Set.ncard_image_of_injOn (hinj.mono hTsub), hTcard]
  -- `S` is a proper subset of `label '' Δ_j`, because `t < |Δ_j|`
  have hSsub : S ⊆ D.label '' D.Δj := Set.image_mono hTsub
  have hDcard : (D.label '' D.Δj).ncard = D.Δj.ncard := Set.ncard_image_of_injOn hinj
  have hlt : S.ncard < (D.label '' D.Δj).ncard := by
    have := D.toAlignDominant.two_mul_t_lt_ncard_Δj
    omega
  obtain ⟨V, hVmem, hVnot⟩ : ∃ V ∈ D.label '' D.Δj, V ∉ S := by
    by_contra hcon
    push_neg at hcon
    exact absurd (Set.ncard_le_ncard hcon (Set.toFinite _)) (by omega)
  have hVcard : V.ncard = D.ts := by
    obtain ⟨d, hd, rfl⟩ := hVmem
    exact D.label_ncard d hd
  -- pick a member of `S`
  have hTne : (Tpoint D.ϕ u).Nonempty := by
    rw [← Set.ncard_pos (Set.toFinite _), hTcard]
    exact D.toAlignDominant.one_le_t
  obtain ⟨d₀, hd₀⟩ := hTne
  have hd₀Δ : d₀ ∈ D.Δj := hTsub hd₀
  have hS₀card : (D.label d₀).ncard = D.ts := D.label_ncard d₀ hd₀Δ
  -- `A(Γ*)` is transitive on the `t*`-subsets of `Γ*`
  have hm2 : D.ts + 2 ≤ Nat.card (Fin D.ms) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fin]
    have := D.ts_two; have := D.ms_ge; omega
  obtain ⟨π, hπ, hπeq⟩ := exists_mem_image_eq_of_ncard_eq (Ω := Fin D.ms)
    (K := alternatingGroup (Fin D.ms)) le_rfl hS₀card hVcard hm2
  -- the shared first step: some `h ∈ H_T` has `ψ h = π`
  obtain ⟨h, hhT, hhψ⟩ := D.toAlignDominant.exists_stab_label_map_eq hun hπ
  have hdh : (h : Equiv.Perm (Fin D.m)) d₀ ∈ Tpoint D.ϕ u := by
    rw [← hhT]; exact ⟨d₀, hd₀, rfl⟩
  have : D.label ((h : Equiv.Perm (Fin D.m)) d₀) = V := by
    rw [D.psi_label h d₀ hd₀Δ, hhψ, hπeq]
  exact hVnot ⟨_, hdh, this⟩

/-- **Case 3, the key estimate, in case (B)**, in the form
`Babai.AlignDominant.affected_of_dominant_orbit` asks for.  Immediate from
`Babai.AlignDominantB.window_inter_unaffected_eq_empty`. -/
theorem three_mul_ncard_unaffected_le :
    3 * (D.toAlignDominant.window ∩ unaffectedSet D.toAlignDominant.phis).ncard
      ≤ 2 * Fintype.card Ω := by
  rw [D.window_inter_unaffected_eq_empty, Set.ncard_empty]
  omega

/-- In case (B) the kernel of `ψ` fixes `Δ_j` pointwise: an automorphism of a Johnson
scheme is determined by the permutation of `Γ*` it induces (here: by `psi_label` and
`label_inj`).  So for `σ ∈ ker ϕ*` and `u` in the window, Eq. (54) gives `T(u^σ) = T(u)`. -/
theorem Tpoint_smul_ker (σ : D.toAlignDominant.Gs)
    (hσ : D.toAlignDominant.phis σ = 1) {u : Ω} (hu : u ∈ D.toAlignDominant.window) :
    Tpoint D.ϕ ((σ : Equiv.Perm Ω) u) = Tpoint D.ϕ u := by
  have hTsub : Tpoint D.ϕ u ⊆ D.Δj := D.toAlignDominant.Tpoint_subset_of_mem_window hu
  set h : D.H := phiStar D.ϕ D.H σ with hhdef
  have hψ1 : D.ψ h = 1 := hσ
  have hfixΔ : ∀ d ∈ D.Δj, (h : Equiv.Perm (Fin D.m)) d = d := by
    intro d hd
    have hmem : (h : Equiv.Perm (Fin D.m)) d ∈ D.Δj := by
      rw [← D.stab _ h.2]; exact ⟨d, hd, rfl⟩
    refine D.label_inj _ hmem d hd ?_
    rw [D.psi_label h d hd, hψ1]
    simp
  rw [D.toAlignDominant.Tpoint_smul σ u, ← hhdef]
  refine Set.eq_of_subset_of_ncard_le ?_ ?_ (Set.toFinite _)
  · rintro _ ⟨d, hd, rfl⟩
    rw [hfixΔ d (hTsub hd)]; exact hd
  · exact le_of_eq (Set.ncard_image_of_injective _
      (h : Equiv.Perm (Fin D.m)).injective).symm

/-- **Case 1, in case (B)**: the orbits of `ker ϕ*` on the window are at most `2n/3`.

*Why it is true* (the corrected paper Align, "Smallest change", item 1).  An
automorphism of a Johnson scheme is determined by the permutation of `Γ*` it induces
(`Babai.exists_unique_perm_of_mem_aut_johnsonScheme`), so `ker ψ` acts trivially on `Δ_j`:
by `psi_label`, `ψ(h) = 1` forces `label (h d) = label d`, hence `h d = d`, for every
`d ∈ Δ_j`.

Let `σ ∈ ker ϕ*` and let `u` be in the window.  Then `ϕ(σ) ∈ ker ψ` fixes `Δ_j` pointwise,
and `T(u) ⊆ Δ_j`, so Eq. (54) gives `T(σ·u) = ϕ(σ)''T(u) = T(u)`.  The orbit of `u` under
`ker ϕ*` therefore lies inside the single standard block `B_{T(u)}`.

The standard blocks all have the same size and there are `C(m, t)` of them, with `t ≥ 1`
and `m ≥ 9`, so `C(m, t) ≥ 9` and `9·|B_T| ≤ n`; in particular `3·|B_T| ≤ 2n`.

*In Lean*: that `ker ψ` fixes `Δ_j` pointwise, hence the label, is
`Babai.AlignDominantB.Tpoint_smul_ker`, and the count of the standard blocks is
`Babai.three_mul_card_labelFiber_le` (`Workspace/Master/AlignDominantAux.lean`).

The hypothesis `hu` cannot be dropped: outside the window the label of `u` meets
`Γ ∖ Δ_j`, where `ker ψ` is unconstrained. -/
theorem three_mul_ncard_orbit_ker_le {u : Ω} (hu : u ∈ D.toAlignDominant.window) :
    3 * (orbit D.toAlignDominant.phis.ker u).ncard ≤ 2 * Fintype.card Ω := by
  classical
  have hstep : orbit D.toAlignDominant.phis.ker u ⊆
      ↑(labelFiber D.ϕ (labelF D.ϕ u)) := by
    rintro _ ⟨σ, rfl⟩
    have hTeq := D.Tpoint_smul_ker (σ : D.toAlignDominant.Gs)
      (MonoidHom.mem_ker.1 σ.2) hu
    refine Finset.mem_coe.2 (mem_labelFiber.2 (Finset.coe_injective ?_))
    rw [coe_labelF, coe_labelF]
    exact hTeq
  -- a standard block is at most `2n/3`
  have hle : (orbit D.toAlignDominant.phis.ker u).ncard ≤
      (labelFiber (Ω := Ω) D.ϕ (labelF D.ϕ u)).card := by
    have := Set.ncard_le_ncard hstep (Set.toFinite _)
    rwa [Set.ncard_coe_finset] at this
  have hblock := three_mul_card_labelFiber_le D.transitive D.ϕ D.giant D.veryLarge
    D.toAlignDominant.three_le_m D.t_const D.toAlignDominant.one_le_t
    D.toAlignDominant.two_mul_t_le (labelF D.ϕ u)
    (by rw [card_labelF, D.t_const u])
  omega

/-- **Case 3 of the repair, packaged, in case (B)**: what the round needs about the largest
orbit.  Unlike case (A) this needs no hypothesis on `m*`: the Johnson parameters already
give `m* ≥ 2t* + 1 ≥ 5`, and there is no unaffected point in the window at all. -/
theorem affected_and_pointwiseStab_le_ker
    {u : Ω} (hu : u ∈ D.toAlignDominant.window)
    (hbig : 2 * Fintype.card Ω < 3 * (orbit D.toAlignDominant.Gs u).ncard) :
    (∀ z ∈ orbit D.toAlignDominant.Gs u, Affected D.toAlignDominant.phis z) ∧
      pointwiseStab D.toAlignDominant.Gs (orbit D.toAlignDominant.Gs u)
        ≤ D.toAlignDominant.phis.ker := by
  have hms5 : 5 ≤ D.ms := by have := D.ts_two; have := D.ms_ge; omega
  have haff := D.toAlignDominant.affected_of_dominant_orbit
    D.three_mul_ncard_unaffected_le hu hbig
  exact ⟨haff, D.toAlignDominant.pointwiseStab_orbit_le_ker hms5 haff⟩

end AlignDominantB

end Babai
