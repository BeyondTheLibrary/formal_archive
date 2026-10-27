/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 15, line 2: the imprimitive Luks reduction with brute force over `Ḡ`.
-/
import Workspace.Master.Lines
import Workspace.TopAction.TopAction2
import Workspace.Luks.Framework
import Workspace.Master.CosetForms

/-!
# §15, line 2

> 2. (: `G` is transitive, `G`-action `Ḡ` on blocks is Johnson group isomorphic to `S_m` or
>    `A_m` :) set `ℓ = (log n)³`; if `m ≤ ℓ` then apply imprimitive Luks reduction to reduce
>    to kernel of the `G`-action on the blocks (brute force on small primitive group `Ḡ`,
>    multiplicative cost `ℓ!`)

The line has two halves.

* The **imprimitive Luks reduction** (Theorem 11.1.9): descend to `N = ker(ψ)`, where
  `ψ : G → Ḡ` is the action on the blocks.  "Brute force on `Ḡ`" means: run over *all*
  `|Ḡ|` elements `σ̄` of `Ḡ`, and for each of them find the isomorphisms in `G` above `σ̄`
  (Prop. 12.0.1, `Babai.liftingReduction`).  Their union is `Iso_G(x,y)`
  (`Babai.iUnion_liftingSet`).  This is `Babai.luksBruteForceReduction`, of multiplicative
  cost `|Ḡ|`, which for `m ≤ ℓ` is at most `ℓ!` (`Babai.card_onBlocks_le_factorial`).
* The **Chain Rule over the orbits of `N`** (`Babai.chainOverOrbits`): each of the `|Ḡ|`
  instances is with respect to `N` on the whole window, and is broken into one instance per
  orbit of `N`.  This is `Babai.SIReduction.expand`, as in `Babai.giantAReduction` of
  Sec. 12.

The composite is `Babai.line2Reduction`.

**Why not `Babai.TopAction1Reduction`.**  Prop. 12.0.5 also runs over a set of elements of
`Ḡ` and lifts each of them, but it answers a different question: it *decides* whether `ϕ`
maps `Iso_G(x,y)` onto `Ḡ`, and returns `Iso_G(x,y)` only when the answer is affirmative
(its value is `none` otherwise).  Line 2 has to return `Iso_G(x,y)` in every case, so what
it uses is the union of the liftings itself, `Babai.luksBruteForceReduction`, and not the
subcoset closure of Prop. 12.0.5 (ii).  Both are built from the same `Babai.liftAll`.

**The progress.**  `N` fixes every block setwise, so an orbit of `N` lies inside a block
(`Babai.orbit_blockKernel_subset`).  With at least two blocks, `N` is intransitive, and all
its orbits then have the same length `n/m'` where `m'` is their number
(`Babai.orbit_ncard_mul_eq_card`, Fact 11.1.8); so `2|Δ| ≤ n` for every window `Δ` the line
produces (`Babai.two_mul_ncard_orbit_le`), which is the first branch of
`Babai.MasterStep.decreases`.
-/

universe u v

namespace Babai

open MulAction Equiv Equiv.Perm

variable {Ω : Type u} {A : Type v} [Fintype Ω] [DecidableEq Ω]
  {G : Subgroup (Equiv.Perm Ω)} {H : Type*} [Group H]

/-! ### The union of the liftings is `Iso_G(x,y)` -/

/-- §11.1, the imprimitive Luks reduction, the identity behind *"brute force on `Ḡ`"*: the
sets `ϕ⁻¹(σ̄) ∩ Iso_G(x,y)`, for `σ̄` running over the whole group `Ḡ`, cover `Iso_G(x,y)`.

*Proof.*  Each of them is contained in `Iso_G(x,y)` by definition.  Conversely an
isomorphism `τ ∈ Iso_G(x,y)` lies in `G`, so it lies above `σ̄ = ϕ(τ)`. -/
theorem iUnion_liftingSet (ϕ : G →* H) (x y : Ω → A) :
    (⋃ σ : H, liftingSet ϕ x y σ) = strIso (G : Set (Equiv.Perm Ω)) x y := by
  ext τ
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨σ, hσ⟩
    exact hσ.2
  · intro hτ
    exact ⟨ϕ ⟨τ, hτ.1⟩, ⟨⟨hτ.1, rfl⟩, hτ⟩⟩

/-! ### Brute force over a finite group -/

/-- All the elements of a finite group, as a list: the paper's *"brute force on the small
primitive group `Ḡ`"* of line 2. -/
noncomputable def allElements (H : Type*) [Fintype H] : List H :=
  (Finset.univ : Finset H).toList

theorem mem_allElements [Fintype H] (σ : H) : σ ∈ allElements H := by
  rw [allElements, Finset.mem_toList]
  exact Finset.mem_univ σ

theorem length_allElements [Fintype H] : (allElements H).length = Fintype.card H := by
  rw [allElements, Finset.length_toList, Finset.card_univ]

open scoped Classical in
/-- §15, line 2, the first half: the **imprimitive Luks reduction by brute force over
`Ḡ`**.  One call of Prop. 12.0.1 per element of `Ḡ`, and the answer is the union of what
they return. -/
noncomputable def luksBruteForceReduction [Fintype H] (ϕ : G →* H) (x y : Ω → A) :
    SIReduction Ω A (Set (Equiv.Perm Ω)) :=
  (liftAll ϕ x y (allElements H)).bind fun L => .done (⋃ s ∈ L, s)

/-- §15, line 2: the brute force over `Ḡ` returns `Iso_G(x,y)`. -/
theorem run_luksBruteForceReduction [Fintype H] (ϕ : G →* H) (x y : Ω → A) :
    (luksBruteForceReduction ϕ x y).run = strIso (G : Set (Equiv.Perm Ω)) x y := by
  classical
  rw [luksBruteForceReduction, SIReduction.run_bind, SIReduction.run_done, run_liftAll,
    ← iUnion_liftingSet ϕ x y]
  ext τ
  simp only [Set.mem_iUnion, List.mem_map, exists_prop]
  constructor
  · rintro ⟨s, ⟨σ, -, rfl⟩, hτ⟩
    exact ⟨σ, hτ⟩
  · rintro ⟨σ, hτ⟩
    exact ⟨_, ⟨σ, mem_allElements σ, rfl⟩, hτ⟩

/-- §15, line 2: the brute force makes exactly `|Ḡ|` calls. -/
theorem calls_length_luksBruteForceReduction [Fintype H] (ϕ : G →* H) (x y : Ω → A) :
    (luksBruteForceReduction ϕ x y).calls.length = Fintype.card H := by
  classical
  rw [luksBruteForceReduction, SIReduction.calls_bind, SIReduction.calls_done,
    calls_liftAll]
  simp [length_allElements]

/-- §15, line 2: every call of the brute force is an instance with respect to `N = ker ϕ`
on the whole window. -/
theorem calls_luksBruteForceReduction_wrt [Fintype H] (ϕ : G →* H) (x y : Ω → A) :
    ∀ I ∈ (luksBruteForceReduction ϕ x y).calls,
      I.K = ((kerSubgroup ϕ : Subgroup (Equiv.Perm Ω)) : Set (Equiv.Perm Ω)) ∧
        I.Δ = Set.univ := by
  classical
  rw [luksBruteForceReduction, SIReduction.calls_bind, SIReduction.calls_done, calls_liftAll]
  intro I hI
  simp only [List.append_nil, List.mem_map] at hI
  obtain ⟨σ, -, rfl⟩ := hI
  exact ⟨rfl, rfl⟩

/-! ### Line 2 as a reduction -/

/-- §15, **line 2**: the imprimitive Luks reduction (brute force over `Ḡ`), each of whose
`|Ḡ|` instances with respect to `N` is broken up by the Chain Rule over the orbits of
`N`. -/
noncomputable def line2Reduction [Fintype H] (ϕ : G →* H) (x y : Ω → A) :
    SIReduction Ω A (Set (Equiv.Perm Ω)) :=
  (luksBruteForceReduction ϕ x y).expand (chainOverOrbits (kerSubgroup ϕ))

/-- §15, line 2 **is correct**: its value is `Iso_G(x,y)`. -/
theorem run_line2Reduction [Fintype H] (ϕ : G →* H) (x y : Ω → A) :
    (line2Reduction ϕ x y).run = strIso (G : Set (Equiv.Perm Ω)) x y := by
  rw [line2Reduction,
    SIReduction.run_expand_of_calls
      (P := fun I => I.K = ((kerSubgroup ϕ : Subgroup (Equiv.Perm Ω)) : Set (Equiv.Perm Ω))
        ∧ I.Δ = Set.univ)
      (fun I hI => run_chainOverOrbits hI.1 hI.2) _
      (calls_luksBruteForceReduction_wrt ϕ x y)]
  exact run_luksBruteForceReduction ϕ x y

/-- §15, line 2, **the number of calls**: at most `|Ḡ|` times the number of orbits of
`N`.  The factor `|Ḡ|` is the paper's multiplicative cost, at most `ℓ!` for `m ≤ ℓ`. -/
theorem calls_length_line2Reduction [Fintype H] (ϕ : G →* H) (x y : Ω → A) :
    (line2Reduction ϕ x y).calls.length ≤
      Fintype.card H * (orbitList (kerSubgroup ϕ)).length := by
  have h := SIReduction.calls_expand_length_le_of_calls
    (P := fun I => I.K = ((kerSubgroup ϕ : Subgroup (Equiv.Perm Ω)) : Set (Equiv.Perm Ω))
      ∧ I.Δ = Set.univ)
    (fun I hI => run_chainOverOrbits hI.1 hI.2)
    (c := (orbitList (kerSubgroup ϕ)).length)
    (fun I _ => calls_length_chainOverOrbits _ I)
    (luksBruteForceReduction ϕ x y) (calls_luksBruteForceReduction_wrt ϕ x y)
  rw [line2Reduction]
  rw [calls_length_luksBruteForceReduction ϕ x y] at h
  exact h

/-- §15, line 2: **every call has an orbit of `N` for its window**. -/
theorem calls_line2Reduction_window [Fintype H] (ϕ : G →* H) (x y : Ω → A) :
    ∀ J ∈ (line2Reduction ϕ x y).calls, J.Δ ∈ orbitList (kerSubgroup ϕ) := by
  rw [line2Reduction]
  exact SIReduction.mem_calls_expand_of_calls
    (P := fun I => I.K = ((kerSubgroup ϕ : Subgroup (Equiv.Perm Ω)) : Set (Equiv.Perm Ω))
      ∧ I.Δ = Set.univ)
    (fun I hI => run_chainOverOrbits hI.1 hI.2)
    (fun I _ => calls_chainOverOrbits_window _ I)
    (luksBruteForceReduction ϕ x y) (calls_luksBruteForceReduction_wrt ϕ x y)

/-- §15, line 2: **every call has its candidate set inside `G`**.  The Chain Rule of the
imprimitive Luks reduction works inside `N = ker ϕ`, and `N ≤ G`.

This is what lets the line be read on a window: a reduction on the window `Δ` may be lifted
to `Ω` only when its calls stay inside the group `G = K^Δ` induced on the window
(`Babai.SIReduction.calls_window`). -/
theorem calls_line2Reduction_K [Fintype H] (ϕ : G →* H) (x y : Ω → A) :
    ∀ J ∈ (line2Reduction ϕ x y).calls, J.K ⊆ (G : Set (Equiv.Perm Ω)) := by
  rw [line2Reduction]
  refine SIReduction.mem_calls_expand_of_calls
    (P := fun I => I.K = ((kerSubgroup ϕ : Subgroup (Equiv.Perm Ω)) : Set (Equiv.Perm Ω))
      ∧ I.Δ = Set.univ)
    (fun I hI => run_chainOverOrbits hI.1 hI.2)
    (fun I _ J hJ => ?_)
    (luksBruteForceReduction ϕ x y) (calls_luksBruteForceReduction_wrt ϕ x y)
  exact subset_trans (calls_chainOverOrbits_K _ I J hJ) (kerSubgroup_le ϕ)


/-! ### Line 2 in coset form

The middle term of Eqs. (62)–(63): the `|Ḡ|` calls are the instances with respect to the
**cosets** `ϕ⁻¹(σ̄)`, with the strings untouched, and each of them is broken up by the coset
Chain Rule over the orbits of `N`.  `Babai.line2Reduction` is the same round in the group
form; the branches of Sec. 15 run the alignment of the coset form
(`Babai.SIReduction.alignRed`). -/

section CosetLine2

open scoped Classical in
/-- §15, line 2, the first half **in coset form**: one call `⟨ϕ⁻¹(σ̄), Ω, x, y⟩` per element
of `Ḡ`, and the union of what they return. -/
noncomputable def cosetLuksBruteForce [Fintype H] (ϕ : G →* H) (x y : Ω → A) :
    SIReduction Ω A (Set (Equiv.Perm Ω)) :=
  (cosetLiftAll ϕ x y (allElements H)).bind fun L => .done (⋃ s ∈ L, s)

/-- §15, line 2: the coset brute force over `Ḡ` returns `Iso_G(x,y)`. -/
theorem run_cosetLuksBruteForce [Fintype H] (ϕ : G →* H) (x y : Ω → A) :
    (cosetLuksBruteForce ϕ x y).run = strIso (G : Set (Equiv.Perm Ω)) x y := by
  classical
  rw [cosetLuksBruteForce, SIReduction.run_bind, SIReduction.run_done, run_cosetLiftAll,
    ← iUnion_liftingSet ϕ x y]
  ext τ
  simp only [Set.mem_iUnion, List.mem_map, exists_prop]
  constructor
  · rintro ⟨s, ⟨σ, -, rfl⟩, hτ⟩
    exact ⟨σ, hτ⟩
  · rintro ⟨σ, hτ⟩
    exact ⟨_, ⟨σ, mem_allElements σ, rfl⟩, hτ⟩

theorem calls_length_cosetLuksBruteForce [Fintype H] (ϕ : G →* H) (x y : Ω → A) :
    (cosetLuksBruteForce ϕ x y).calls.length = Fintype.card H := by
  classical
  rw [cosetLuksBruteForce, SIReduction.calls_bind, SIReduction.calls_done,
    calls_cosetLiftAll]
  simp [length_allElements]

/-- §15, line 2: every call of the coset brute force is an instance with respect to a coset
`ϕ⁻¹(σ̄)` of `N = ker ϕ`, on the whole window. -/
theorem calls_cosetLuksBruteForce_wrt [Fintype H] (ϕ : G →* H) (x y : Ω → A) :
    ∀ I ∈ (cosetLuksBruteForce ϕ x y).calls,
      (∃ σ : H, I.K = preimageSet ϕ σ) ∧ I.Δ = Set.univ := by
  classical
  rw [cosetLuksBruteForce, SIReduction.calls_bind, SIReduction.calls_done,
    calls_cosetLiftAll]
  intro I hI
  simp only [List.append_nil, List.mem_map] at hI
  obtain ⟨σ, -, rfl⟩ := hI
  exact ⟨⟨σ, rfl⟩, rfl⟩

open scoped Classical in
/-- §15, **line 2 in coset form**: the coset brute force over `Ḡ`, each of whose `|Ḡ|`
instances is broken up by the coset Chain Rule over the orbits of `N`. -/
noncomputable def cosetLine2Reduction [Fintype H] (ϕ : G →* H) (x y : Ω → A) :
    SIReduction Ω A (Set (Equiv.Perm Ω)) :=
  (cosetLuksBruteForce ϕ x y).expand (cosetChainOverOrbits (kerSubgroup ϕ))

/-- The Chain Rule answers every call of the coset brute force: its window is all of `Ω`,
and the coset chain asks nothing of the candidate set. -/
theorem run_cosetChainOverOrbits_of_wrt [Fintype H] {ϕ : G →* H} {I : SIInstance Ω A}
    (hI : (∃ σ : H, I.K = preimageSet ϕ σ) ∧ I.Δ = Set.univ) :
    (cosetChainOverOrbits (kerSubgroup ϕ) I).run = I.answer :=
  run_cosetChainOverOrbits _ hI.2

/-- §15, line 2 in coset form **is correct**. -/
theorem run_cosetLine2Reduction [Fintype H] (ϕ : G →* H) (x y : Ω → A) :
    (cosetLine2Reduction ϕ x y).run = strIso (G : Set (Equiv.Perm Ω)) x y := by
  rw [cosetLine2Reduction,
    SIReduction.run_expand_of_calls
      (P := fun I => (∃ σ : H, I.K = preimageSet ϕ σ) ∧ I.Δ = Set.univ)
      (fun I hI => run_cosetChainOverOrbits_of_wrt hI) _
      (calls_cosetLuksBruteForce_wrt ϕ x y)]
  exact run_cosetLuksBruteForce ϕ x y

/-- §15, line 2 in coset form, **the number of calls**. -/
theorem calls_length_cosetLine2Reduction [Fintype H] (ϕ : G →* H) (x y : Ω → A) :
    (cosetLine2Reduction ϕ x y).calls.length ≤
      Fintype.card H * (orbitList (kerSubgroup ϕ)).length := by
  have h := SIReduction.calls_expand_length_le_of_calls
    (P := fun I => (∃ σ : H, I.K = preimageSet ϕ σ) ∧ I.Δ = Set.univ)
    (fun I hI => run_cosetChainOverOrbits_of_wrt hI)
    (c := (orbitList (kerSubgroup ϕ)).length)
    (fun I _ => calls_length_cosetChainOverOrbits _ I)
    (cosetLuksBruteForce ϕ x y) (calls_cosetLuksBruteForce_wrt ϕ x y)
  rw [cosetLine2Reduction]
  rw [calls_length_cosetLuksBruteForce ϕ x y] at h
  exact h

/-- §15, line 2 in coset form: **every call has an orbit of `N` for its window**. -/
theorem calls_cosetLine2Reduction_window [Fintype H] (ϕ : G →* H) (x y : Ω → A) :
    ∀ J ∈ (cosetLine2Reduction ϕ x y).calls, J.Δ ∈ orbitList (kerSubgroup ϕ) := by
  rw [cosetLine2Reduction]
  exact SIReduction.mem_calls_expand_of_calls
    (P := fun I => (∃ σ : H, I.K = preimageSet ϕ σ) ∧ I.Δ = Set.univ)
    (fun I hI => run_cosetChainOverOrbits_of_wrt hI)
    (fun I _ => calls_cosetChainOverOrbits_window _ I)
    (cosetLuksBruteForce ϕ x y) (calls_cosetLuksBruteForce_wrt ϕ x y)

/-- §15, line 2 in coset form: **every call has its candidate set inside `G`**. -/
theorem calls_cosetLine2Reduction_K [Fintype H] (ϕ : G →* H) (x y : Ω → A) :
    ∀ J ∈ (cosetLine2Reduction ϕ x y).calls, J.K ⊆ (G : Set (Equiv.Perm Ω)) := by
  rw [cosetLine2Reduction]
  refine SIReduction.mem_calls_expand_of_calls
    (P := fun I => (∃ σ : H, I.K = preimageSet ϕ σ) ∧ I.Δ = Set.univ)
    (fun I hI => run_cosetChainOverOrbits_of_wrt hI)
    (fun I hI J hJ => ?_)
    (cosetLuksBruteForce ϕ x y) (calls_cosetLuksBruteForce_wrt ϕ x y)
  obtain ⟨⟨σ, hσ⟩, -⟩ := hI
  refine subset_trans (calls_cosetChainOverOrbits_K _ I J hJ) ?_
  rw [hσ]
  exact preimageSet_subset ϕ σ

/-- §15, line 2 in coset form: **every call is a coset instance** with respect to `G`, so
after alignment every call is a group instance. -/
theorem isCosetInstance_calls_cosetLine2Reduction [Fintype H] (ϕ : G →* H) (x y : Ω → A) :
    ∀ J ∈ (cosetLine2Reduction ϕ x y).calls, IsCosetInstance G J := by
  rw [cosetLine2Reduction]
  refine SIReduction.mem_calls_expand_of_calls
    (P := fun I => (∃ σ : H, I.K = preimageSet ϕ σ) ∧ I.Δ = Set.univ)
    (fun I hI => run_cosetChainOverOrbits_of_wrt hI)
    (fun I hI J hJ => ?_)
    (cosetLuksBruteForce ϕ x y) (calls_cosetLuksBruteForce_wrt ϕ x y)
  obtain ⟨⟨σ, hσ⟩, -⟩ := hI
  by_cases hr : σ ∈ ϕ.range
  · refine isCosetInstance_calls_cosetChainOverOrbits (kerSubgroup_le ϕ) I ?_ J hJ
    exact ⟨kerSubgroup ϕ, liftRep ϕ σ, le_rfl, (liftRep_mem ϕ hr).1,
      by rw [hσ]; exact preimageSet_eq_smul_kerSubgroup ϕ hr⟩
  · exfalso
    have hempty : I.K = (∅ : Set (Equiv.Perm Ω)) := by
      rw [hσ]; exact preimageSet_eq_empty ϕ hr
    rw [cosetChainOverOrbits, hempty, calls_cosetChain_empty] at hJ
    exact absurd hJ (List.not_mem_nil)

end CosetLine2

/-! ### The progress of line 2: the orbits of `N` lie inside blocks -/

section Blocks

variable {ℬ : Set (Set Ω)}

/-- §15, line 2, the progress, first step: the kernel of the action on the blocks fixes
every block setwise, so each of its orbits lies inside a block. -/
theorem orbit_blockKernel_subset
    {hperm : ∀ σ ∈ G, ∀ B ∈ ℬ, (σ : Equiv.Perm Ω) '' B ∈ ℬ} {B : Set Ω} (hB : B ∈ ℬ)
    {u : Ω} (hu : u ∈ B) : orbit (blockKernel G ℬ hperm) u ⊆ B := by
  rintro w hw
  obtain ⟨σ, rfl⟩ := mem_orbit_iff.1 hw
  have hinv : IsInvariant (blockKernel G ℬ hperm) B := isInvariant_blockKernel hB
  rw [← hinv (σ : Equiv.Perm Ω) σ.2]
  exact ⟨u, hu, rfl⟩

/-- §15, line 2, the progress, second step: with at least two blocks the kernel of the
action on the blocks is intransitive.

*Proof.*  An orbit of the kernel lies inside a block, so a kernel orbit equal to `Ω` would
force that block to be `Ω`; but a second, different block is nonempty and disjoint from
it. -/
theorem not_isTransitive_blockKernel (hℬ : IsInvariantPartitionOn G Set.univ ℬ)
    {B₁ B₂ : Set Ω} (hB₁ : B₁ ∈ ℬ) (hB₂ : B₂ ∈ ℬ) (hne : B₁ ≠ B₂) :
    ¬ IsTransitive (blockKernel G ℬ hℬ.permutes) := by
  rintro ⟨u, hu⟩
  -- the block containing `u`
  have humem : u ∈ ⋃₀ ℬ := by rw [hℬ.covers]; trivial
  obtain ⟨B₀, hB₀, huB₀⟩ := humem
  have hsub : (Set.univ : Set Ω) ⊆ B₀ := by
    rw [← hu]; exact orbit_blockKernel_subset hB₀ huB₀
  have hB₀univ : B₀ = Set.univ := Set.Subset.antisymm (Set.subset_univ _) hsub
  -- one of `B₁`, `B₂` differs from `B₀`
  obtain ⟨C, hC, hCne⟩ : ∃ C ∈ ℬ, C ≠ B₀ := by
    by_cases h : B₁ = B₀
    · exact ⟨B₂, hB₂, fun hc => hne (h.trans hc.symm)⟩
    · exact ⟨B₁, hB₁, h⟩
  obtain ⟨w, hw⟩ := hℬ.nonempty C hC
  have hdisj := hℬ.pairwiseDisjoint C hC B₀ hB₀ hCne
  have : w ∈ C ∩ B₀ := ⟨hw, by rw [hB₀univ]; trivial⟩
  rw [Set.disjoint_iff_inter_eq_empty.1 hdisj] at this
  exact this

/-- §15, line 2, **the progress**: with `G` transitive and at least two blocks, every orbit
of `N = ker(ψ)` has at most `n/2` elements.

This is the recurrence (ii) of Sec. 11.4 with `m' ≥ 2`: all the orbits of a normal
intransitive subgroup of a transitive group have the same length `n/m'`
(`Babai.orbit_ncard_mul_eq_card`, Fact 11.1.8). -/
theorem two_mul_ncard_orbit_le (hG : IsTransitive G)
    (hℬ : IsInvariantPartitionOn G Set.univ ℬ) {B₁ B₂ : Set Ω} (hB₁ : B₁ ∈ ℬ) (hB₂ : B₂ ∈ ℬ)
    (hne : B₁ ≠ B₂) (u : Ω) :
    2 * (orbit (blockKernel G ℬ hℬ.permutes) u).ncard ≤ Fintype.card Ω := by
  obtain ⟨m', hm', hall⟩ := orbit_ncard_mul_eq_card hG
    (isNormalIn_kerSubgroup (blockHom G ℬ hℬ.permutes))
    (not_isTransitive_blockKernel hℬ hB₁ hB₂ hne)
  have h := hall u
  calc 2 * (orbit (blockKernel G ℬ hℬ.permutes) u).ncard
      ≤ m' * (orbit (blockKernel G ℬ hℬ.permutes) u).ncard :=
        Nat.mul_le_mul_right _ hm'
    _ = Fintype.card Ω := by rw [mul_comm]; exact h

/-- §15, line 2: `|Ḡ| ≤ m!`, where `m` is the number of blocks — the paper's multiplicative
cost `ℓ!` once `m ≤ ℓ`.  `Ḡ` is a subgroup of `S(ℬ)`, and `|S(ℬ)| = m!`. -/
theorem card_onBlocks_le_factorial
    (hperm : ∀ σ ∈ G, ∀ B ∈ ℬ, (σ : Equiv.Perm Ω) '' B ∈ ℬ) [Fintype ℬ] :
    Nat.card (onBlocks G ℬ hperm) ≤ Nat.factorial (Fintype.card ℬ) := by
  classical
  have h1 : Nat.card (onBlocks G ℬ hperm) ≤ Nat.card (Equiv.Perm ℬ) :=
    Nat.card_le_card_of_injective (fun σ : onBlocks G ℬ hperm => (σ : Equiv.Perm ℬ))
      Subtype.val_injective
  have h2 : Nat.card (Equiv.Perm ℬ) = Nat.factorial (Fintype.card ℬ) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm]
  omega

end Blocks

end Babai
