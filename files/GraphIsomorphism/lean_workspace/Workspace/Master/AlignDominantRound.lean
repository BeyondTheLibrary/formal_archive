/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 14.1, Procedure Align, lines 7–11, the dominant window: the round.
-/
import Workspace.Master.AlignDominantData
import Workspace.Master.Line1

/-!
# The round of the dominant window

the corrected paper (Procedure Align, lines 7–11) repairs the missing step of Procedure Align:
`G* = ϕ⁻¹(Aut(Y))` need not be transitive on the window `Ω(Δ_j)`, so

> while processing the window `Ω(Δ_j)` with `|Ω(Δ_j)| > 2n/3`, apply the Chain Rule to the
> orbits of `G*`, the largest orbit first.

with three cases.  `Babai.AlignDominantRoundData.round` is that reduction, in the style of
`Babai.line1Round` (`Workspace/Master/Line1.lean`):

* **case 1**, `m*` below the threshold of Theorem 10.5.1: first the Luks descent to
  `ker ϕ*` at the multiplicative cost `|G* : ker ϕ*| ≤ m*!`
  (`Babai.descentReduction` over `Babai.cosetRepList`), then the Chain Rule over the orbits
  of `ker ϕ*` in the window, which have at most `2n/3` points;
* **case 2**, every orbit of `G*` in the window at most `2n/3`: the Chain Rule over those
  orbits;
* **case 3**: the same Chain Rule, with the dominant orbit `Δ₁` first; that first call
  carries the Johnson case data of `Workspace/Master/AlignDominantData.lean`, with
  parameter `m* ≤ m/2` (Eq. (73)), and every other call has fewer than `n/3` points.

Cases 2 and 3 are the same reduction; they differ only in the hint attached and in the way
the progress is proved.

**One call per orbit, not one orbit and the rest.**  `Babai.chainRuleBranch` of line 1
splits the window into *one orbit and its complement* and lets the iteration of the round
do the rest, which is why `Babai.MasterStep.decreases` has the `Babai.IsChainRuleRound`
alternative.  That device is not needed here, and is not used: every call of this round
satisfies `Babai.MakesProgress` on its own — the small orbits because their windows are at
most `2n/3`, and the dominant orbit because it carries a hint with `2m* ≤ m`.  Splitting
off "the rest" would produce an instance whose window is a union of orbits and which
carries no hint, so it would restart at line 1 of the Master Algorithm and lose `ϕ*` —
exactly what the repair is there to prevent.
-/

universe u v

namespace Babai

open MulAction Equiv Equiv.Perm

/-! ## The orbits of a group inside an invariant set -/

section OrbitsOn

open scoped Classical

variable {Ω : Type u} [Fintype Ω] [DecidableEq Ω] {A : Type v}

/-- The orbit of a point really is one of the entries of `Babai.orbitList`. -/
theorem orbit_mem_orbitList (N : Subgroup (Equiv.Perm Ω)) (u : Ω) :
    orbit N u ∈ orbitList N := by
  have h : u ∈ (⋃ Δ ∈ orbitList N, Δ) := by rw [iUnion_orbitList]; trivial
  obtain ⟨Δ, hΔ, hu⟩ := Set.mem_iUnion₂.1 h
  obtain ⟨v, rfl⟩ := mem_orbitList hΔ
  rwa [orbit_eq_iff.2 hu]

/-- The orbits of `N` that lie inside `Δ`.  For an `N`-invariant `Δ` these are exactly the
orbits of the points of `Δ`, and they partition `Δ`. -/
noncomputable def orbitListOn (N : Subgroup (Equiv.Perm Ω)) (Δ : Set Ω) : List (Set Ω) :=
  (orbitList N).filter (fun S => decide (S ⊆ Δ))

theorem mem_orbitListOn {N : Subgroup (Equiv.Perm Ω)} {Δ S : Set Ω} :
    S ∈ orbitListOn N Δ ↔ S ∈ orbitList N ∧ S ⊆ Δ := by
  rw [orbitListOn, List.mem_filter]
  simp

theorem subset_of_mem_orbitListOn {N : Subgroup (Equiv.Perm Ω)} {Δ S : Set Ω}
    (h : S ∈ orbitListOn N Δ) : S ⊆ Δ := (mem_orbitListOn.1 h).2

theorem isInvariant_of_mem_orbitListOn {N : Subgroup (Equiv.Perm Ω)} {Δ S : Set Ω}
    (h : S ∈ orbitListOn N Δ) : IsInvariant N S :=
  isInvariant_of_mem_orbitList (mem_orbitListOn.1 h).1

theorem exists_orbit_of_mem_orbitListOn {N : Subgroup (Equiv.Perm Ω)} {Δ S : Set Ω}
    (h : S ∈ orbitListOn N Δ) : ∃ u ∈ Δ, S = orbit N u := by
  obtain ⟨u, rfl⟩ := mem_orbitList (mem_orbitListOn.1 h).1
  exact ⟨u, (mem_orbitListOn.1 h).2 (mem_orbit_self u), rfl⟩

/-- The orbit of a point of an invariant set lies inside that set, so it is one of the
entries of `Babai.orbitListOn`. -/
theorem orbit_mem_orbitListOn {N : Subgroup (Equiv.Perm Ω)} {Δ : Set Ω}
    (hinv : IsInvariant N Δ) {u : Ω} (hu : u ∈ Δ) : orbit N u ∈ orbitListOn N Δ := by
  refine mem_orbitListOn.2 ⟨orbit_mem_orbitList N u, ?_⟩
  rintro _ ⟨σ, rfl⟩
  rw [← hinv (σ : Equiv.Perm Ω) σ.2]
  exact ⟨u, hu, rfl⟩

/-- The orbits inside an invariant set cover it: this is the partition the Chain Rule runs
over. -/
theorem iUnion_orbitListOn {N : Subgroup (Equiv.Perm Ω)} {Δ : Set Ω}
    (hinv : IsInvariant N Δ) : (⋃ S ∈ orbitListOn N Δ, S) = Δ := by
  ext u
  constructor
  · intro h
    obtain ⟨S, hS, hu⟩ := Set.mem_iUnion₂.1 h
    exact subset_of_mem_orbitListOn hS hu
  · intro hu
    exact Set.mem_iUnion₂.2 ⟨orbit N u, orbit_mem_orbitListOn hinv hu, mem_orbit_self u⟩

theorem length_orbitListOn_le (N : Subgroup (Equiv.Perm Ω)) (Δ : Set Ω) :
    (orbitListOn N Δ).length ≤ Fintype.card Ω :=
  le_trans (List.length_filter_le _ _)
    (by have := length_orbitList_le N; rwa [Nat.card_eq_fintype_card] at this)

/-- The Chain Rule over the orbits of `N` inside the `N`-invariant set `Δ`. -/
noncomputable def chainOverOrbitsOn (N : Subgroup (Equiv.Perm Ω)) (Δ : Set Ω)
    (I : SIInstance Ω A) : SIReduction Ω A (Set (Equiv.Perm Ω)) :=
  chainReduction N I.x I.y (orbitListOn N Δ) 1 N

/-- The Chain Rule over the orbits inside `Δ` answers every instance with respect to `N`
whose window is `Δ`. -/
theorem run_chainOverOrbitsOn {N : Subgroup (Equiv.Perm Ω)} {Δ : Set Ω}
    (hinv : IsInvariant N Δ) {I : SIInstance Ω A} (hK : I.K = (N : Set (Equiv.Perm Ω)))
    (hΔ : I.Δ = Δ) : (chainOverOrbitsOn N Δ I).run = I.answer := by
  have hrun := run_chainReduction (N := N) I.x I.y (orbitListOn N Δ) ∅ 1 N
    (fun S hS => isInvariant_of_mem_orbitListOn hS) (by intro σ _; simp) le_rfl (one_mem _)
    (by rw [wIso_empty]; simp)
  rw [chainOverOrbitsOn, hrun, iUnion_orbitListOn hinv, Set.empty_union, SIInstance.answer,
    hK, hΔ]

theorem calls_length_chainOverOrbitsOn (N : Subgroup (Equiv.Perm Ω)) (Δ : Set Ω)
    (I : SIInstance Ω A) :
    (chainOverOrbitsOn N Δ I).calls.length ≤ Fintype.card Ω :=
  le_trans (calls_chainReduction N I.x I.y (orbitListOn N Δ) 1 N).1
    (length_orbitListOn_le N Δ)

theorem calls_chainOverOrbitsOn_window (N : Subgroup (Equiv.Perm Ω)) (Δ : Set Ω)
    (I : SIInstance Ω A) :
    ∀ J ∈ (chainOverOrbitsOn N Δ I).calls, J.Δ ∈ orbitListOn N Δ :=
  (calls_chainReduction N I.x I.y (orbitListOn N Δ) 1 N).2

theorem calls_chainOverOrbitsOn_K (N : Subgroup (Equiv.Perm Ω)) (Δ : Set Ω)
    (I : SIInstance Ω A) :
    ∀ J ∈ (chainOverOrbitsOn N Δ I).calls, J.K ⊆ (N : Set (Equiv.Perm Ω)) :=
  calls_chainReduction_K N I.x I.y (orbitListOn N Δ) 1 N

theorem calls_chainOverOrbitsOn_isGroupInstance (N : Subgroup (Equiv.Perm Ω)) (Δ : Set Ω)
    (I : SIInstance Ω A) :
    ∀ J ∈ (chainOverOrbitsOn N Δ I).calls, IsGroupInstance J :=
  calls_chainReduction_isGroupInstance I.x I.y
    (fun _ hS => isInvariant_of_mem_orbitListOn hS) 1 le_rfl

/-! ### The largest orbit first -/

/-- The orbits of `N` inside `Δ`, with a dominant orbit — one of more than `2n/3` points —
put first when there is one.  This is the paper's *"the largest orbit first"*: the first
call of the Chain Rule is the one made with respect to the whole group `G*`, and that is
where the Johnson case data of Eq. (73) is attached. -/
noncomputable def orbitListDomFirst (N : Subgroup (Equiv.Perm Ω)) (Δ : Set Ω) :
    List (Set Ω) :=
  match (orbitListOn N Δ).find? (fun S => decide (2 * Fintype.card Ω < 3 * S.ncard)) with
  | some S => S :: (orbitListOn N Δ).erase S
  | none => orbitListOn N Δ

/-- Reordering does not change the collection of windows. -/
theorem orbitListDomFirst_perm (N : Subgroup (Equiv.Perm Ω)) (Δ : Set Ω) :
    (orbitListDomFirst N Δ).Perm (orbitListOn N Δ) := by
  rw [orbitListDomFirst]
  cases h : (orbitListOn N Δ).find? (fun S => decide (2 * Fintype.card Ω < 3 * S.ncard)) with
  | none => exact List.Perm.refl _
  | some S => exact (List.perm_cons_erase (List.mem_of_find?_eq_some h)).symm

theorem mem_orbitListDomFirst {N : Subgroup (Equiv.Perm Ω)} {Δ S : Set Ω} :
    S ∈ orbitListDomFirst N Δ ↔ S ∈ orbitListOn N Δ :=
  (orbitListDomFirst_perm N Δ).mem_iff

theorem length_orbitListDomFirst (N : Subgroup (Equiv.Perm Ω)) (Δ : Set Ω) :
    (orbitListDomFirst N Δ).length = (orbitListOn N Δ).length :=
  (orbitListDomFirst_perm N Δ).length_eq

theorem iUnion_orbitListDomFirst {N : Subgroup (Equiv.Perm Ω)} {Δ : Set Ω}
    (hinv : IsInvariant N Δ) : (⋃ S ∈ orbitListDomFirst N Δ, S) = Δ := by
  have h : (⋃ S ∈ orbitListDomFirst N Δ, S) = (⋃ S ∈ orbitListOn N Δ, S) := by
    ext u
    simp only [Set.mem_iUnion, exists_prop]
    exact ⟨fun ⟨S, hS, hu⟩ => ⟨S, mem_orbitListDomFirst.1 hS, hu⟩,
      fun ⟨S, hS, hu⟩ => ⟨S, mem_orbitListDomFirst.2 hS, hu⟩⟩
  rw [h, iUnion_orbitListOn hinv]

/-- If some orbit inside `Δ` is dominant, it is the head of the reordered list. -/
theorem orbitListDomFirst_eq_cons {N : Subgroup (Equiv.Perm Ω)} {Δ S₀ : Set Ω}
    (hS₀ : S₀ ∈ orbitListOn N Δ) (hbig : 2 * Fintype.card Ω < 3 * S₀.ncard) :
    ∃ S ∈ orbitListOn N Δ, 2 * Fintype.card Ω < 3 * S.ncard ∧
      orbitListDomFirst N Δ = S :: (orbitListOn N Δ).erase S := by
  rw [orbitListDomFirst]
  cases h : (orbitListOn N Δ).find? (fun S => decide (2 * Fintype.card Ω < 3 * S.ncard)) with
  | none =>
    exact absurd (List.find?_eq_none.1 h S₀ hS₀) (by simpa using hbig)
  | some S =>
    exact ⟨S, List.mem_of_find?_eq_some h, by simpa using List.find?_some h, rfl⟩

end OrbitsOn

/-! ## The kernel of `ϕ*` as a subgroup of `S(Ω)` -/

section Kernel

variable {Ω : Type u} [Fintype Ω] [DecidableEq Ω] {G : Subgroup (Equiv.Perm Ω)} {k : ℕ}

/-- **The multiplicative cost of case 1**: `|G : ker ϕ| ≤ k!`, because `G/ker ϕ` embeds in
`S(Γ)`.  This is the paper's *"first descend to `ker ϕ*` at the multiplicative cost
`m*!`"*. -/
theorem relIndex_kerSubgroup_le (ϕ : G →* Equiv.Perm (Fin k)) :
    (kerSubgroup ϕ).relIndex G ≤ Nat.factorial k := by
  have hsub : (kerSubgroup ϕ).subgroupOf G = ϕ.ker := by
    rw [kerSubgroup, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective G)]
  have h1 : (kerSubgroup ϕ).relIndex G = Nat.card (G ⧸ ϕ.ker) := by
    rw [Subgroup.relIndex, hsub, Subgroup.index]
  have h2 : Nat.card (G ⧸ ϕ.ker) = Nat.card ϕ.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange ϕ).toEquiv
  have h3 : Nat.card ϕ.range ≤ Nat.card (Equiv.Perm (Fin k)) :=
    Nat.card_le_card_of_injective (fun g => (g : Equiv.Perm (Fin k))) Subtype.val_injective
  have h4 : Nat.card (Equiv.Perm (Fin k)) = Nat.factorial k := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  omega

end Kernel

/-! ## Two list facts the reordering needs -/

section Nodup

open scoped Classical

variable {Ω : Type u} [Fintype Ω] [DecidableEq Ω]

/-- The orbits of `Babai.orbitList` are pairwise distinct: the list has one entry per
orbit. -/
theorem nodup_orbitList (N : Subgroup (Equiv.Perm Ω)) : (orbitList N).Nodup := by
  classical
  letI : Fintype (orbitRel.Quotient N Ω) := Fintype.ofFinite _
  refine List.Nodup.map ?_ (Finset.nodup_toList _)
  intro q q' h
  have hq : (q.out : Ω) ∈ orbitRel.Quotient.orbit q :=
    (orbitRel.Quotient.mem_orbit (G := N)).2 q.out_eq'
  have hq' : (q.out : Ω) ∈ orbitRel.Quotient.orbit q' := by rw [← h]; exact hq
  rw [orbitRel.Quotient.mem_orbit (G := N)] at hq hq'
  rw [← hq, hq']

theorem nodup_orbitListOn (N : Subgroup (Equiv.Perm Ω)) (Δ : Set Ω) :
    (orbitListOn N Δ).Nodup := (nodup_orbitList N).filter _

theorem not_mem_erase_orbitListOn (N : Subgroup (Equiv.Perm Ω)) (Δ S : Set Ω) :
    S ∉ (orbitListOn N Δ).erase S := (nodup_orbitListOn N Δ).not_mem_erase

end Nodup

/-! ## The calls of a Chain Rule over a nonempty list -/

section ChainCons

variable {Ω : Type u} [Fintype Ω] [DecidableEq Ω] {A : Type v}

/-- The first call of the Chain Rule over `Δ₁ :: rest` is the instance with respect to the
full group `M` on the window `Δ₁`; every other call has one of the remaining windows.  This
is why the paper puts *the largest orbit first*: only the first call is made with respect to
`G*` itself, and only there can the Johnson case data of Eq. (73) be attached. -/
theorem calls_chainReduction_cons (N : Subgroup (Equiv.Perm Ω)) (x y : Ω → A)
    (Δ₁ : Set Ω) (rest : List (Set Ω)) (σ : Equiv.Perm Ω) (M : Subgroup (Equiv.Perm Ω)) :
    ∀ J ∈ (chainReduction N x y (Δ₁ :: rest) σ M).calls,
      J = (⟨(M : Set (Equiv.Perm Ω)), Δ₁, x, strAct y σ⁻¹⟩ : SIInstance Ω A) ∨ J.Δ ∈ rest := by
  classical
  intro J hJ
  rw [chainReduction, SIReduction.calls_call] at hJ
  rcases List.mem_cons.1 hJ with rfl | hJ
  · exact Or.inl rfl
  · by_cases h : (SIInstance.answer
        (⟨(M : Set (Equiv.Perm Ω)), Δ₁, x, strAct y σ⁻¹⟩ : SIInstance Ω A)).Nonempty
    · rw [dif_pos h] at hJ
      exact Or.inr ((calls_chainReduction N x y rest (σ * h.some)
        (M ⊓ autWindow N Δ₁ x)).2 J hJ)
    · rw [dif_neg h, SIReduction.calls_done] at hJ
      exact absurd hJ (List.not_mem_nil)

end ChainCons

/-! ## The round -/

section Round

open scoped Classical

variable {Ω : Type u} [Fintype Ω] [DecidableEq Ω] {A : Type v}

/-- §14.1, lines 7–11: **what the round of the dominant window needs from line 7**.

`Babai.AlignDominant` is lines 6 and 8–10 without the structure `Y` of line 7, and the two
counting lemmas of the repair cannot be stated on it (see
`Workspace/Master/AlignDominant.lean`).  This structure adds exactly those two, so that the
round is written once and instantiated in either case of line 7 by
`Babai.AlignDominantA.roundData` and `Babai.AlignDominantB.roundData`.

* `orbit_ker_le` is item 1 of the repair (`AlignDominantA/B.three_mul_ncard_orbit_ker_le`),
  used in case 1;
* `unaffected_le` is item 3 (`AlignDominantA.three_mul_ncard_unaffected_le`,
  `AlignDominantB.three_mul_ncard_unaffected_le`); it is asked for only under the
  hypothesis of case 3, because in case (A) it is false for `m* = 2`;
* `window_large` is the brute-force exit of line 2 of Procedure Reduce-to-Johnson, as in
  `Babai.DescentData.window_large`. -/
structure AlignDominantRoundData (Ω : Type u) [Fintype Ω] [DecidableEq Ω] extends
    AlignDominant Ω where
  /-- Line 2 of Procedure Reduce-to-Johnson: the window is above the absolute constant of
  the brute-force exit.  `96` is what turns *"`|Δ₁| > 2n/3`"* into the `64` of
  `Babai.JohnsonCaseData.window_large`. -/
  window_large : 96 ≤ Fintype.card Ω
  /-- Item 1 of the repair: the orbits of `ker ϕ*` in the window are at most `2n/3`. -/
  orbit_ker_le : ∀ u ∈ toAlignDominant.window,
    3 * (orbit toAlignDominant.phis.ker u).ncard ≤ 2 * Fintype.card Ω
  /-- Item 3 of the repair: in case 3 the unaffected part of the window is at most
  `2n/3`. -/
  unaffected_le : VeryLargeK toAlignDominant.ms (maxOrbitLength toAlignDominant.Gs) →
    3 * (toAlignDominant.window ∩ unaffectedSet toAlignDominant.phis).ncard
      ≤ 2 * Fintype.card Ω

namespace AlignDominantRoundData

variable (D : AlignDominantRoundData Ω)

/-- The test that tells case 1 from cases 2 and 3: is `m*` above the threshold of
Theorem 10.5.1? -/
def LargeParam : Prop :=
  VeryLargeK D.toAlignDominant.ms (maxOrbitLength D.toAlignDominant.Gs)

/-- `ker ϕ*`, read inside `S(Ω)`. -/
noncomputable def ker : Subgroup (Equiv.Perm Ω) := kerSubgroup D.toAlignDominant.phis

theorem ker_le : D.ker ≤ D.toAlignDominant.Gs := kerSubgroup_le _

theorem isInvariant_window : IsInvariant D.toAlignDominant.Gs D.toAlignDominant.window :=
  D.toAlignDominant.isInvariant_window

theorem isInvariant_window_ker : IsInvariant D.ker D.toAlignDominant.window :=
  fun σ hσ => D.toAlignDominant.isInvariant_window σ (D.ker_le hσ)

/-- **Case 3**: the dominant orbit of `G*` in the window, with everything item 3 of the
repair proves about it (`Babai.AlignDominantOrbit`).  The two facts that are fields there —
that every point of the orbit is affected by `ϕ*` and that the pointwise stabilizer of the
orbit lies in `ker ϕ*` — are obtained here from `unaffected_le`. -/
noncomputable def dominantOrbit (h : D.LargeParam) {u : Ω}
    (hu : u ∈ D.toAlignDominant.window)
    (hbig : 2 * Fintype.card Ω < 3 * (orbit D.toAlignDominant.Gs u).ncard) :
    AlignDominantOrbit D.toAlignDominant where
  u := u
  mem_window := hu
  dominant := hbig
  affected := D.toAlignDominant.affected_of_dominant_orbit (D.unaffected_le h) hu hbig
  stab_le := by
    have hms9 : 9 ≤ D.toAlignDominant.ms := by
      have : (9 : ℝ) ≤ (D.toAlignDominant.ms : ℝ) := le_trans (le_max_left _ _) h
      exact_mod_cast this
    exact D.toAlignDominant.pointwiseStab_orbit_le_ker (by omega)
      (D.toAlignDominant.affected_of_dominant_orbit (D.unaffected_le h) hu hbig)
  veryLarge := h
  window_large := D.window_large

/-- §14.1, lines 7–11, **the round of the dominant window**.

Cases 2 and 3: the Chain Rule over the orbits of `G*` inside the window, the dominant orbit
first.  Case 1: the Luks descent to `ker ϕ*` over a set of coset representatives, each of
its instances expanded by the Chain Rule over the orbits of `ker ϕ*` inside the window. -/
noncomputable def round (I : SIInstance Ω A) : SIReduction Ω A (Set (Equiv.Perm Ω)) :=
  if D.LargeParam then
    chainReduction D.toAlignDominant.Gs I.x I.y
      (orbitListDomFirst D.toAlignDominant.Gs D.toAlignDominant.window) 1
      D.toAlignDominant.Gs
  else
    (descentReduction D.ker D.toAlignDominant.window I.x I.y
        (cosetRepList D.ker D.toAlignDominant.Gs)).expand
      (chainOverOrbitsOn D.ker D.toAlignDominant.window)

/-- The predicate that picks out the instances of the descent of case 1. -/
def DescentCall (J : SIInstance Ω A) : Prop :=
  J.K = (D.ker : Set (Equiv.Perm Ω)) ∧ J.Δ = D.toAlignDominant.window

theorem calls_descent_descentCall (I : SIInstance Ω A) :
    ∀ J ∈ (descentReduction D.ker D.toAlignDominant.window I.x I.y
      (cosetRepList D.ker D.toAlignDominant.Gs)).calls, D.DescentCall J :=
  calls_descentReduction_spec _ _ _ _ _

theorem run_chainOverOrbitsOn_descentCall :
    ∀ J : SIInstance Ω A, D.DescentCall J →
      (chainOverOrbitsOn D.ker D.toAlignDominant.window J).run = J.answer :=
  fun _ hJ => run_chainOverOrbitsOn D.isInvariant_window_ker hJ.1 hJ.2

/-- §14.1, lines 7–11, **the round is correct**: it answers the instance with respect to
`G*` whose window is `Ω(Δ_j)`.

In cases 2 and 3 this is Luks's Chain Rule over a partition of the window into invariant
sets (Prop. 11.1.7).  In case 1 it is Eq. (62) for the descent to `ker ϕ*`, followed by the
same Chain Rule for each coset. -/
theorem run_round (I : SIInstance Ω A)
    (hK : I.K = (D.toAlignDominant.Gs : Set (Equiv.Perm Ω)))
    (hΔ : I.Δ = D.toAlignDominant.window) : (D.round I).run = I.answer := by
  classical
  rw [round]
  by_cases h : D.LargeParam
  · rw [if_pos h]
    have hrun := run_chainReduction (N := D.toAlignDominant.Gs) I.x I.y
      (orbitListDomFirst D.toAlignDominant.Gs D.toAlignDominant.window) ∅ 1
      D.toAlignDominant.Gs
      (fun S hS => isInvariant_of_mem_orbitListOn (mem_orbitListDomFirst.1 hS))
      (by intro σ _; simp) le_rfl (one_mem _) (by rw [wIso_empty]; simp)
    rw [hrun, iUnion_orbitListDomFirst D.isInvariant_window, Set.empty_union,
      SIInstance.answer, hK, hΔ]
  · rw [if_neg h,
      SIReduction.run_expand_of_calls (D.run_chainOverOrbitsOn_descentCall) _
        (D.calls_descent_descentCall I),
      run_descentReduction_cosetRepList D.ker_le D.toAlignDominant.window I.x I.y,
      SIInstance.answer, hK, hΔ]

/-- §14.1, lines 7–11: **every call of the round is a group instance** (Decision 7 of
`Workspace/Master/DESIGN.md`). -/
theorem calls_round_isGroupInstance (I : SIInstance Ω A) :
    ∀ J ∈ (D.round I).calls, IsGroupInstance J := by
  classical
  rw [round]
  by_cases h : D.LargeParam
  · rw [if_pos h]
    exact calls_chainReduction_isGroupInstance I.x I.y
      (fun _ hS => isInvariant_of_mem_orbitListOn (mem_orbitListDomFirst.1 hS)) 1 le_rfl
  · rw [if_neg h]
    exact SIReduction.mem_calls_expand_of_calls (D.run_chainOverOrbitsOn_descentCall)
      (fun J _ => calls_chainOverOrbitsOn_isGroupInstance D.ker _ J) _
      (D.calls_descent_descentCall I)

/-! ### The windows of the calls -/

theorem calls_round_window_case1 (I : SIInstance Ω A) (h : ¬ D.LargeParam) :
    ∀ J ∈ (D.round I).calls, J.Δ ∈ orbitListOn D.ker D.toAlignDominant.window := by
  classical
  rw [round, if_neg h]
  exact SIReduction.mem_calls_expand_of_calls (D.run_chainOverOrbitsOn_descentCall)
    (fun J _ => calls_chainOverOrbitsOn_window D.ker _ J) _ (D.calls_descent_descentCall I)

theorem calls_round_window_case23 (I : SIInstance Ω A) (h : D.LargeParam) :
    ∀ J ∈ (D.round I).calls,
      J.Δ ∈ orbitListDomFirst D.toAlignDominant.Gs D.toAlignDominant.window := by
  classical
  rw [round, if_pos h]
  exact (calls_chainReduction _ I.x I.y _ 1 _).2

/-! ### The hint

Line 11 of Procedure Align hands `ϕ*` down *"for recursive processing of the corresponding
window"*.  In the repaired procedure that is the first Chain Rule call of case 3, and what
is handed down is the `Babai.JohnsonCaseData` of
`Workspace/Master/AlignDominantData.lean`, whose Johnson parameter is `m* ≤ m/2`
(Eq. (73)).  All other calls get `none` and start again at line 1 of the Master
Algorithm. -/

/-- Transporting the Johnson case data along an equality of instances does not change the
Johnson parameter. -/
theorem JohnsonCaseData.m_eqRec {I J : SIInstance Ω A} (h : I = J) (d : JohnsonCaseData I) :
    (h ▸ d).m = d.m := by subst h; rfl

/-- The calls that carry the hint: in case 3, the call with respect to `G*` whose window is
a dominant orbit. -/
def HasHint (I J : SIInstance Ω A) : Prop :=
  D.LargeParam ∧ ∃ c : AlignDominantOrbit D.toAlignDominant,
    (⟨(D.toAlignDominant.Gs : Set (Equiv.Perm Ω)), c.Δ₁, I.x, J.y⟩ : SIInstance Ω A) = J

/-- §14.1, line 11: **the hint the round attaches to each of its calls**. -/
noncomputable def hint (I J : SIInstance Ω A) : Option (JohnsonCaseData J) :=
  if h : D.HasHint I J then some (h.2.choose_spec ▸ h.2.choose.johnsonCaseData I.x J.y)
  else none

/-- The Johnson parameter of the hinted call is `m*`. -/
theorem param_hint (I J : SIInstance Ω A) (h : D.HasHint I J) :
    param (⟨J, D.hint I J⟩ : HintedInstance Ω A) = D.toAlignDominant.ms := by
  rw [hint, dif_pos h]
  show (h.2.choose_spec ▸ h.2.choose.johnsonCaseData I.x J.y).m = _
  rw [JohnsonCaseData.m_eqRec]
  rfl

/-- Eq. (73) at the hinted call: `2 m* ≤ m`. -/
theorem two_mul_param_hint_le (I J : SIInstance Ω A) (h : D.HasHint I J) :
    2 * param (⟨J, D.hint I J⟩ : HintedInstance Ω A) ≤ D.toAlignDominant.m := by
  rw [D.param_hint I J h]
  exact D.toAlignDominant.param_halved

/-! ### The progress -/

theorem ncard_le_card (S : Set Ω) : S.ncard ≤ Fintype.card Ω := by
  have h := Set.ncard_le_ncard (Set.subset_univ S) (Set.toFinite (Set.univ : Set Ω))
  rwa [Set.ncard_univ, Nat.card_eq_fintype_card] at h

/-- In case 3 there is only one dominant orbit: two orbits of more than `2n/3` points would
overlap (`Babai.AlignDominant.other_orbit_small`). -/
theorem dominant_orbit_unique {u v : Ω}
    (hu : 2 * Fintype.card Ω < 3 * (orbit D.toAlignDominant.Gs u).ncard)
    (hv : 2 * Fintype.card Ω < 3 * (orbit D.toAlignDominant.Gs v).ncard) :
    orbit D.toAlignDominant.Gs v = orbit D.toAlignDominant.Gs u := by
  by_cases hmem : v ∈ orbit D.toAlignDominant.Gs u
  · exact orbit_eq_iff.2 hmem
  · exact absurd (D.toAlignDominant.other_orbit_small hu hmem) (by omega)

/-- §14.1, lines 7–11, **the progress of the round**, in the sense of
`Babai.MakesProgress` for the instance `i` of line 4c — the one with window `Ω` and Johnson
parameter `m`.

* In case 1 every call has a window of at most `2n/3` (item 1 of the repair).
* In cases 2 and 3 every call whose window is not dominant has at most `2n/3` points; the
  one call whose window is dominant is the first call of the Chain Rule, and it carries the
  hint, whose Johnson parameter is `m* ≤ m/2` (Eq. (73)).

So the round never needs the `Babai.IsChainRuleRound` alternative: each call makes progress
on its own. -/
theorem decreases_round (i : HintedInstance Ω A)
    (hwin : i.inst.windowSize = Fintype.card Ω)
    (hparam : param i = D.toAlignDominant.m) (I : SIInstance Ω A) :
    ∀ J ∈ (D.round I).calls,
      MakesProgress HintedInstance.win param i (⟨J, D.hint I J⟩ : HintedInstance Ω A) := by
  classical
  intro J hJ
  have hn : 96 ≤ Fintype.card Ω := D.window_large
  have hwin1 : 1 ≤ HintedInstance.win i := by
    show 1 ≤ i.inst.windowSize
    omega
  by_cases h : D.LargeParam
  · -- cases 2 and 3
    have hmem : J.Δ ∈ orbitListOn D.toAlignDominant.Gs D.toAlignDominant.window :=
      mem_orbitListDomFirst.1 (D.calls_round_window_case23 I h J hJ)
    obtain ⟨v, hv, hJv⟩ := exists_orbit_of_mem_orbitListOn hmem
    by_cases hsmall : 3 * J.Δ.ncard ≤ 2 * Fintype.card Ω
    · exact Or.inl ⟨hwin1, by show 5 * J.Δ.ncard ≤ 4 * i.inst.windowSize; omega⟩
    · -- `J.Δ` is a dominant orbit, so `J` is the first call and carries the hint
      have hbig : 2 * Fintype.card Ω < 3 * (orbit D.toAlignDominant.Gs v).ncard := by
        rw [← hJv]; omega
      obtain ⟨S, hS, hSbig, hlist⟩ := orbitListDomFirst_eq_cons hmem (by rw [hJv] at hsmall ⊢; omega)
      obtain ⟨w, hw, hSw⟩ := exists_orbit_of_mem_orbitListOn hS
      have hSJ : S = J.Δ := by
        rw [hSw, hJv]
        exact D.dominant_orbit_unique hbig (by rw [← hSw]; exact hSbig)
      have hhead : J = (⟨(D.toAlignDominant.Gs : Set (Equiv.Perm Ω)), S, I.x,
          strAct I.y (1 : Equiv.Perm Ω)⁻¹⟩ : SIInstance Ω A) := by
        have hJ' := hJ
        rw [round, if_pos h, hlist] at hJ'
        rcases calls_chainReduction_cons _ I.x I.y S _ 1 _ J hJ' with heq | hmem'
        · exact heq
        · exact absurd (hSJ ▸ hmem') (not_mem_erase_orbitListOn _ _ _)
      have hhint : D.HasHint I J := by
        refine ⟨h, D.dominantOrbit h hv hbig, ?_⟩
        show (⟨(D.toAlignDominant.Gs : Set (Equiv.Perm Ω)),
          orbit D.toAlignDominant.Gs v, I.x, J.y⟩ : SIInstance Ω A) = J
        rw [← hJv, hhead]
      refine Or.inr ⟨?_, ?_, ?_⟩
      · show J.Δ.ncard ≤ i.inst.windowSize
        have := ncard_le_card (Ω := Ω) J.Δ
        omega
      · rw [hparam]
        have := D.toAlignDominant.nine_le_m
        omega
      · rw [hparam]
        exact D.two_mul_param_hint_le I J hhint
  · -- case 1
    have hmem := D.calls_round_window_case1 I h J hJ
    obtain ⟨v, hv, hJv⟩ := exists_orbit_of_mem_orbitListOn hmem
    have hle : 3 * J.Δ.ncard ≤ 2 * Fintype.card Ω := by
      rw [hJv, ker, orbit_kerSubgroup]
      exact D.orbit_ker_le v hv
    exact Or.inl ⟨hwin1, by show 5 * J.Δ.ncard ≤ 4 * i.inst.windowSize; omega⟩

/-! ### The number of calls -/

/-- §14.1, lines 7–11: the number of instances one round of the dominant window produces.

The factor `m*! ≤ ℓ(n)!` is the multiplicative cost of the Luks descent of case 1, and the
factor `n` bounds the number of orbits the Chain Rule runs over; the summand `n` is cases 2
and 3, where there is no descent.  It stays below `Babai.masterRoundCost`, the cost of
lines 2 and 4b. -/
def alignDominantRoundCost (n : ℕ) : ℕ := Nat.factorial (ellOf n) * n + n

theorem alignDominantRoundCost_le_masterRoundCost (n : ℕ) :
    alignDominantRoundCost n ≤ masterRoundCost n := by
  rw [alignDominantRoundCost, masterRoundCost]
  omega

/-- **Case 1 is below the threshold of line 2**: if `m*` is below the threshold of
Theorem 10.5.1 then `m* ≤ ℓ(n) = (log₂ n)³`, so the multiplicative cost `m*!` of the Luks
descent is at most `ℓ(n)!`, the cost line 2 of the Master Algorithm already pays.

*Proof.*  `¬ VeryLargeK m* n₀` with `n₀ = maxOrbitLength G* ≤ n` gives
`m* < max{9, 2 log₂ n}`, and for `n ≥ 96` we have `L = ⌊log₂ n⌋ ≥ 6`, hence `9 ≤ L³` and
`2 log₂ n < 2(L+1) ≤ L³`. -/
theorem ms_le_ellOf (h : ¬ D.LargeParam) :
    D.toAlignDominant.ms ≤ ellOf (Fintype.card Ω) := by
  have hn : 96 ≤ Fintype.card Ω := D.window_large
  have hmax : maxOrbitLength D.toAlignDominant.Gs ≤ Fintype.card Ω := by
    refine maxOrbitLength_le fun z => ?_
    have := Nat.card_le_card_of_injective
      (fun w : orbit D.toAlignDominant.Gs z => (w : Ω)) Subtype.val_injective
    simpa [Nat.card_eq_fintype_card] using this
  have hVL : ¬ VeryLargeK D.toAlignDominant.ms (Fintype.card Ω) := fun hc => h (hc.mono hmax)
  have hlt : (D.toAlignDominant.ms : ℝ) <
      max 9 (2 * Real.logb 2 (Fintype.card Ω)) := not_le.1 hVL
  have hL6 : 6 ≤ Nat.log 2 (Fintype.card Ω) := six_le_natLog (by omega)
  have hcube : 36 * Nat.log 2 (Fintype.card Ω) ≤ Nat.log 2 (Fintype.card Ω) ^ 3 :=
    calc 36 * Nat.log 2 (Fintype.card Ω) = 6 * 6 * Nat.log 2 (Fintype.card Ω) := by ring
      _ ≤ Nat.log 2 (Fintype.card Ω) * Nat.log 2 (Fintype.card Ω) *
            Nat.log 2 (Fintype.card Ω) := Nat.mul_le_mul (Nat.mul_le_mul hL6 hL6) le_rfl
      _ = Nat.log 2 (Fintype.card Ω) ^ 3 := by ring
  have h9 : (9 : ℝ) ≤ (ellOf (Fintype.card Ω) : ℝ) := by
    have : 9 ≤ ellOf (Fintype.card Ω) := by rw [ellOf]; omega
    exact_mod_cast this
  have h2 : 2 * Real.logb 2 (Fintype.card Ω) ≤ (ellOf (Fintype.card Ω) : ℝ) := by
    have hlogb := logb_lt_natLog_succ (n := Fintype.card Ω) (by omega)
    have hnat : 2 * Nat.log 2 (Fintype.card Ω) + 2 ≤ ellOf (Fintype.card Ω) := by
      rw [ellOf]; omega
    have hcast : (2 : ℝ) * (Nat.log 2 (Fintype.card Ω) : ℝ) + 2 ≤
        (ellOf (Fintype.card Ω) : ℝ) := by exact_mod_cast hnat
    linarith
  have : (D.toAlignDominant.ms : ℝ) < (ellOf (Fintype.card Ω) : ℝ) :=
    lt_of_lt_of_le hlt (max_le h9 h2)
  exact_mod_cast le_of_lt this

/-- §14.1, lines 7–11, **the number of calls of the round**: at most `ℓ(n)! · n + n`.

In cases 2 and 3 there is one call per orbit of `G*` in the window, and there are at most
`n` orbits.  In case 1 there are `|G* : ker ϕ*| ≤ m*! ≤ ℓ(n)!` cosets, each expanded by the
Chain Rule over at most `n` orbits of `ker ϕ*`. -/
theorem calls_length_round (I : SIInstance Ω A) :
    (D.round I).calls.length ≤ alignDominantRoundCost (Fintype.card Ω) := by
  classical
  rw [round]
  by_cases h : D.LargeParam
  · rw [if_pos h]
    have h1 := (calls_chainReduction D.toAlignDominant.Gs I.x I.y
      (orbitListDomFirst D.toAlignDominant.Gs D.toAlignDominant.window) 1
      D.toAlignDominant.Gs).1
    have h2 : (orbitListDomFirst D.toAlignDominant.Gs D.toAlignDominant.window).length
        ≤ Fintype.card Ω := by
      rw [length_orbitListDomFirst]
      exact length_orbitListOn_le _ _
    have h3 : 0 ≤ Nat.factorial (ellOf (Fintype.card Ω)) * Fintype.card Ω := Nat.zero_le _
    rw [alignDominantRoundCost]
    omega
  · rw [if_neg h]
    have hexp := SIReduction.calls_expand_length_le_of_calls
      (D.run_chainOverOrbitsOn_descentCall) (c := Fintype.card Ω)
      (fun J _ => calls_length_chainOverOrbitsOn D.ker _ J) _ (D.calls_descent_descentCall I)
    rw [calls_length_descentReduction, length_cosetRepList] at hexp
    have hrel : (D.ker).relIndex D.toAlignDominant.Gs ≤
        Nat.factorial (ellOf (Fintype.card Ω)) :=
      le_trans (relIndex_kerSubgroup_le D.toAlignDominant.phis)
        (Nat.factorial_le (D.ms_le_ellOf h))
    have : D.ker.relIndex D.toAlignDominant.Gs * Fintype.card Ω ≤
        Nat.factorial (ellOf (Fintype.card Ω)) * Fintype.card Ω :=
      Nat.mul_le_mul_right _ hrel
    rw [alignDominantRoundCost]
    omega

end AlignDominantRoundData

/-! ### The round data in the two cases of line 7 -/

/-- §14.1, line 7 (A): the equipartition case supplies the two counting facts of the
repair. -/
noncomputable def AlignDominantA.roundData (D : AlignDominantA Ω)
    (hn : 96 ≤ Fintype.card Ω) : AlignDominantRoundData Ω where
  toAlignDominant := D.toAlignDominant
  window_large := hn
  orbit_ker_le := fun _ hu => D.three_mul_ncard_orbit_ker_le hu
  unaffected_le := fun hvl => D.three_mul_ncard_unaffected_le hvl

/-- §14.1, line 7 (B): the Johnson scheme case supplies the two counting facts of the
repair.  Its estimate on the unaffected part needs no hypothesis on `m*`: in case (B) there
is no unaffected point in the window at all. -/
noncomputable def AlignDominantB.roundData (D : AlignDominantB Ω)
    (hn : 96 ≤ Fintype.card Ω) : AlignDominantRoundData Ω where
  toAlignDominant := D.toAlignDominant
  window_large := hn
  orbit_ker_le := fun _ hu => D.three_mul_ncard_orbit_ker_le hu
  unaffected_le := fun _ => D.three_mul_ncard_unaffected_le

end Round

end Babai
