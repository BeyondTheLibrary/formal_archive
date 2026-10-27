/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 11.3 (Reduction to Johnson groups).
-/
import Workspace.Luks.JohnsonBarrier

/-!
# §11.3 Reduction to Johnson groups

> We summarize the reduction to Johnson groups.
>
> **Procedure Reduce-to-Johnson**
>
> Input: group `G ≤ S(Ω)`, strings `x, y : Ω → Σ`
>
> Output: `Iso_G(x,y)` or updated `Ω, G, x, y`, `G` transitive, with set `ℬ` of blocks on
> which `Ḡ` acts as Johnson group `Ḡ ≤ S(ℬ)`
>
> 1. **if** `G ≤ Aut(x)` **then**
>      **if** `x = y` **then return** `Iso_G(x,y) = G`, **exit**
>      **else return** `Iso_G(x,y) = ∅`, **exit**
> 2. **if** `|G| < C₀` for some absolute constant `C₀` **then** compute `Iso_G(x,y)` by
>    brute force, **exit**
> 3. **if** `G` intransitive **then** apply Chain Rule
> 4. (: `G` transitive :) Find minimal block system `ℬ`.  Let `m = |ℬ|`.  Let
>    `Ḡ ≤ S(ℬ)` be the induced `G`-action on `ℬ` and `N` the kernel of the `G → Ḡ`
>    epimorphism (: `Ḡ` is a primitive group :)
> 5. **if** `|Ḡ| < m^{1+log₂ m}` **then** reduce `G` to `N` via imprimitive Luks reduction
> 6. **else** (: `Ḡ` a Cameron group of order `≥ m^{1+log₂ m}` :) reduce `Ḡ` to Johnson
>    group via Luks descent (: Theorem 11.2.1, multiplicative cost `≤ m` :)
> 7. (: `Ḡ` a Johnson group :)
>    **return** `Ω, G, ℬ, Ḡ` (Johnson group), `x, y`

Only the mathematical content of each step is formalized: the identity or structural fact
the step relies on.  The control flow, the brute force of step 2 and all running-time
claims are not modelled; see the corrected paper.

Step 5 is Theorem 11.1.9 (`Babai.Theorem_11_1_9`), step 6 is Theorem 11.2.1
(`Babai.Theorem_11_2_1`), and the output of step 7 is the Johnson case of
Definition 11.4.1 (`Babai.IsJohnsonCase`).
-/

namespace Babai

open MulAction Equiv Equiv.Perm
open scoped Pointwise

variable {Ω A : Type*}

/-- §11.3, Procedure Reduce-to-Johnson, **step 1**.

> **if** `G ≤ Aut(x)` **then if** `x = y` **then return** `Iso_G(x,y) = G`, **exit**
> **else return** `Iso_G(x,y) = ∅`, **exit**

If every element of `G` fixes the string `x`, then `Iso_G(x,y)` is all of `G` when
`x = y` and empty otherwise. -/
theorem reduceToJohnson_step1 {G : Subgroup (Equiv.Perm Ω)} {x y : Ω → A}
    (hG : (G : Set (Equiv.Perm Ω)) ⊆ strAut (G : Set (Equiv.Perm Ω)) x) :
    (x = y → strIso (G : Set (Equiv.Perm Ω)) x y = (G : Set (Equiv.Perm Ω))) ∧
      (x ≠ y → strIso (G : Set (Equiv.Perm Ω)) x y = ∅) := by
  constructor
  · rintro rfl
    ext τ
    exact ⟨fun h => h.1, fun h => ⟨h, (hG h).2⟩⟩
  · intro hxy
    rw [Set.eq_empty_iff_forall_notMem]
    rintro τ ⟨hτ, hact⟩
    exact hxy (((hG hτ).2).symm.trans hact)

/-- §11.3, Procedure Reduce-to-Johnson, **step 3**.

> **if** `G` intransitive **then** apply Chain Rule

The orbits of `G` are `G`-invariant and cover `Ω`, so the Chain Rule
(`Babai.wIso_window_sUnion`, the identity behind Prop. 11.1.7) expresses `Iso_G(x,y)` as
the intersection of the window-isomorphism sets on the orbits.  The number of subproblems
is the number of orbits. -/
theorem reduceToJohnson_step3 (G : Subgroup (Equiv.Perm Ω)) (x y : Ω → A) :
    strIso (G : Set (Equiv.Perm Ω)) x y =
      (G : Set (Equiv.Perm Ω)) ∩
        ⋂ B ∈ {B : Set Ω | ∃ u : Ω, B = orbit G u},
          wIso B (G : Set (Equiv.Perm Ω)) x y := by
  have hcover : ⋃₀ {B : Set Ω | ∃ u : Ω, B = orbit G u} = (Set.univ : Set Ω) := by
    ext u
    exact ⟨fun _ => trivial, fun _ => ⟨orbit G u, ⟨u, rfl⟩, mem_orbit_self u⟩⟩
  rw [← wIso_univ, ← hcover, wIso_window_sUnion]

/-! ### Images of a block

Step 4 builds the block system as the set of `G`-images of one block, so we need: an
image of a block of imprimitivity is a block of imprimitivity, and two images of the same
block are equal or disjoint. -/

/-- The image of a block of imprimitivity under an element of `G` is again a block of
imprimitivity. -/
theorem isBlockOfImprimitivity_image {G : Subgroup (Equiv.Perm Ω)} {B : Set Ω}
    (hB : IsBlockOfImprimitivity G B) {σ : Equiv.Perm Ω} (hσ : σ ∈ G) :
    IsBlockOfImprimitivity G ((σ : Equiv.Perm Ω) '' B) := by
  refine ⟨hB.1.image _, fun g hg => ?_⟩
  have hmem : σ⁻¹ * g * σ ∈ G := mul_mem (mul_mem (inv_mem hσ) hg) hσ
  have hconj : (σ : Equiv.Perm Ω) '' ((σ⁻¹ * g * σ : Equiv.Perm Ω) '' B) =
      (g : Equiv.Perm Ω) '' ((σ : Equiv.Perm Ω) '' B) := by
    rw [image_image_eq_mul_image, image_image_eq_mul_image]
    congr 1
    group
  rcases hB.2 _ hmem with h | h
  · left
    rw [← hconj, h]
  · right
    have himg : (σ : Equiv.Perm Ω) '' (((σ⁻¹ * g * σ : Equiv.Perm Ω) '' B) ∩ B) =
        (σ : Equiv.Perm Ω) '' (∅ : Set Ω) := by rw [h]
    rwa [Set.image_inter σ.injective, hconj, Set.image_empty] at himg

/-- Two `G`-images of a block of imprimitivity are equal or disjoint. -/
theorem image_eq_or_disjoint_image {G : Subgroup (Equiv.Perm Ω)} {B : Set Ω}
    (hB : IsBlockOfImprimitivity G B) {σ τ : Equiv.Perm Ω} (hσ : σ ∈ G) (hτ : τ ∈ G) :
    (σ : Equiv.Perm Ω) '' B = (τ : Equiv.Perm Ω) '' B ∨
      Disjoint ((σ : Equiv.Perm Ω) '' B) ((τ : Equiv.Perm Ω) '' B) := by
  have hmul : (τ * (τ⁻¹ * σ) : Equiv.Perm Ω) = σ := by group
  rcases hB.2 (τ⁻¹ * σ) (mul_mem (inv_mem hτ) hσ) with h | h
  · left
    have h2 : (τ : Equiv.Perm Ω) '' ((τ⁻¹ * σ : Equiv.Perm Ω) '' B) =
        (τ : Equiv.Perm Ω) '' B := by rw [h]
    rwa [image_image_eq_mul_image, hmul] at h2
  · right
    rw [Set.disjoint_iff_inter_eq_empty]
    have h2 : (τ : Equiv.Perm Ω) '' (((τ⁻¹ * σ : Equiv.Perm Ω) '' B) ∩ B) =
        (τ : Equiv.Perm Ω) '' (∅ : Set Ω) := by rw [h]
    rwa [Set.image_inter τ.injective, image_image_eq_mul_image, hmul,
      Set.image_empty] at h2

/-- §11.3, Procedure Reduce-to-Johnson, **step 4**: "Find minimal block system `ℬ`."

For a transitive group on at least two points there is a minimal system of imprimitivity
(a system with at least two blocks whose blocks are maximal): start from the system of
singletons and take a system whose blocks are maximal among the proper blocks of
imprimitivity, which exists because `Ω` is finite.

In detail: `{u}` is a block of imprimitivity that is not all of `Ω` (here `|Ω| ≥ 2` is
used), so among the blocks of imprimitivity containing `u` and different from `Ω` there is
a maximal one, `B`.  The system is `ℬ = {B^σ | σ ∈ G}`; transitivity makes it cover `Ω`
and makes `G` transitive on it, and `B ≠ Ω` gives a second block.  A block `C ⊇ B^σ` is
carried by `σ⁻¹` to a block containing `B`, so by maximality it is `B` or `Ω`, i.e.
`C = B^σ` or `C = Ω`. -/
theorem exists_minimalSystemOfImprimitivity [Fintype Ω] {G : Subgroup (Equiv.Perm Ω)}
    (hG : IsTransitive G) (h2 : 2 ≤ Fintype.card Ω) :
    ∃ ℬ : Set (Set Ω), IsMinimalSystemOfImprimitivity G Set.univ ℬ := by
  classical
  obtain ⟨u, hu⟩ := hG
  have htrans : ∀ x : Ω, ∃ σ ∈ G, (σ : Equiv.Perm Ω) u = x := by
    intro x
    have hx : x ∈ orbit G u := by rw [hu]; trivial
    obtain ⟨g, hg⟩ := mem_orbit_iff.1 hx
    exact ⟨(g : Equiv.Perm Ω), g.2, by simpa [Subgroup.smul_def] using hg⟩
  -- `{u}` is a block of imprimitivity, and it is not all of `Ω`
  have hsingle_ne : ({u} : Set Ω) ≠ Set.univ := by
    intro h
    have hsub : ∀ x : Ω, x = u := by
      intro x
      have : x ∈ ({u} : Set Ω) := by rw [h]; trivial
      simpa using this
    have : Fintype.card Ω ≤ 1 :=
      Fintype.card_le_one_iff.2 fun x y => by rw [hsub x, hsub y]
    omega
  have hsing : ({u} : Set Ω) ∈
      {B : Set Ω | IsBlockOfImprimitivity G B ∧ u ∈ B ∧ B ≠ Set.univ} := by
    refine ⟨⟨⟨u, rfl⟩, fun g hg => ?_⟩, rfl, hsingle_ne⟩
    by_cases h : (g : Equiv.Perm Ω) u = u
    · left; simp [h]
    · right
      ext x
      simp only [Set.image_singleton, Set.mem_inter_iff, Set.mem_singleton_iff,
        Set.mem_empty_iff_false, iff_false, not_and]
      rintro rfl hx
      exact h hx
  -- a maximal block of imprimitivity containing `u` and different from `Ω`
  obtain ⟨B, hBmax⟩ :=
    Set.Finite.exists_maximal (s := {B : Set Ω | IsBlockOfImprimitivity G B ∧ u ∈ B ∧
      B ≠ Set.univ}) (Set.toFinite _) ⟨_, hsing⟩
  obtain ⟨hBblock, huB, hBne⟩ := hBmax.1
  have hBmaximal : ∀ C : Set Ω, IsBlockOfImprimitivity G C → u ∈ C → C ≠ Set.univ →
      B ⊆ C → C = B := fun C hC huC hCne hBC =>
    Set.Subset.antisymm (hBmax.2 ⟨hC, huC, hCne⟩ hBC) hBC
  refine ⟨{C : Set Ω | ∃ σ ∈ G, C = (σ : Equiv.Perm Ω) '' B}, ?_⟩
  have hcovers : ⋃₀ {C : Set Ω | ∃ σ ∈ G, C = (σ : Equiv.Perm Ω) '' B} = Set.univ := by
    ext x
    refine ⟨fun _ => trivial, fun _ => ?_⟩
    obtain ⟨σ, hσ, hσu⟩ := htrans x
    exact ⟨(σ : Equiv.Perm Ω) '' B, ⟨σ, hσ, rfl⟩, ⟨u, huB, hσu⟩⟩
  refine ⟨⟨isInvariant_univ G, ?_, ?_, hcovers, ?_, ⟨B, ⟨1, one_mem _, by simp⟩⟩, ?_⟩,
    ?_, ?_⟩
  · rintro _ ⟨σ, hσ, rfl⟩
    exact hBblock.1.image _
  · rintro _ ⟨σ, hσ, rfl⟩ _ ⟨τ, hτ, rfl⟩ hne
    rcases image_eq_or_disjoint_image hBblock hσ hτ with h | h
    · exact absurd h hne
    · exact h
  · rintro σ hσ _ ⟨τ, hτ, rfl⟩
    exact ⟨σ * τ, mul_mem hσ hτ, image_image_eq_mul_image _ _ _⟩
  · rintro _ ⟨σ, hσ, rfl⟩ _ ⟨τ, hτ, rfl⟩
    refine ⟨τ * σ⁻¹, mul_mem hτ (inv_mem hσ), ?_⟩
    rw [image_image_eq_mul_image]
    congr 1
    group
  · -- at least two blocks
    obtain ⟨x, hx⟩ : ∃ x : Ω, x ∉ B := by
      by_contra hcon
      exact hBne (Set.eq_univ_iff_forall.2 (by simpa using hcon))
    obtain ⟨σ, hσ, hσu⟩ := htrans x
    have hxmem : x ∈ (σ : Equiv.Perm Ω) '' B := ⟨u, huB, hσu⟩
    refine (Set.one_lt_ncard (Set.toFinite _)).2
      ⟨B, ⟨1, one_mem _, by simp⟩, (σ : Equiv.Perm Ω) '' B, ⟨σ, hσ, rfl⟩, fun h => ?_⟩
    exact hx (h ▸ hxmem)
  · -- the blocks are maximal
    rintro _ ⟨σ, hσ, rfl⟩ C - hsub hC
    have hCpre : IsBlockOfImprimitivity G ((σ⁻¹ : Equiv.Perm Ω) '' C) :=
      isBlockOfImprimitivity_image hC (inv_mem hσ)
    have hBsub : B ⊆ (σ⁻¹ : Equiv.Perm Ω) '' C := by
      intro z hz
      refine ⟨(σ : Equiv.Perm Ω) z, hsub ⟨z, hz, rfl⟩, by simp⟩
    have huC : u ∈ (σ⁻¹ : Equiv.Perm Ω) '' C := hBsub huB
    by_cases hCuniv : (σ⁻¹ : Equiv.Perm Ω) '' C = Set.univ
    · right
      have : (σ : Equiv.Perm Ω) '' ((σ⁻¹ : Equiv.Perm Ω) '' C) = C := by
        rw [image_image_eq_mul_image]
        simp
      rw [hCuniv] at this
      rw [← this, Set.image_univ, Equiv.range_eq_univ]
    · left
      have heq := hBmaximal _ hCpre huC hCuniv hBsub
      have : (σ : Equiv.Perm Ω) '' ((σ⁻¹ : Equiv.Perm Ω) '' C) = C := by
        rw [image_image_eq_mul_image]
        simp
      rw [heq] at this
      exact this.symm

end Babai
