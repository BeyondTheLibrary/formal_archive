/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 11.2: the block system given by the fibres of one coordinate.
-/
import Workspace.Luks.Wreath

/-!
# The fibres of one coordinate as a system of imprimitivity

In the proof of Theorem 11.2.1 (§11.2) the domain is identified with `Γ^s`, the group `N`
is the base group `H^s` of Definition 11.2.2 (with `H = A_k^(t)`), and the system of
imprimitivity is the set of fibres of one coordinate: for `c ∈ Γ`, the block is
`{x | x_{i₀} = c}`.  The base group permutes these blocks through the `i₀`-th coordinate
alone, so the group it induces on the blocks is exactly `H`.

Nothing here corresponds to a numbered item of the paper.
-/

namespace Babai

open MulAction Equiv

variable {Ω Γ : Type*} {s : ℕ}

/-- The fibre of the `i₀`-th coordinate over `c`, read in `Ω` through the identification
`e : Ω ≃ Γ^s`. -/
def coordFibre (e : Ω ≃ (Fin s → Γ)) (i₀ : Fin s) (c : Γ) : Set Ω := {x | e x i₀ = c}

/-- The set of fibres of the `i₀`-th coordinate: the candidate block system. -/
def coordFibres (e : Ω ≃ (Fin s → Γ)) (i₀ : Fin s) : Set (Set Ω) :=
  Set.range (coordFibre e i₀)

variable (e : Ω ≃ (Fin s → Γ)) (i₀ : Fin s)

@[simp] theorem mem_coordFibre {c : Γ} {x : Ω} : x ∈ coordFibre e i₀ c ↔ e x i₀ = c := Iff.rfl

/-- The identification `e` intertwines a permutation of `Ω` with its image in `S(Γ^s)`. -/
theorem permCongrHom_apply_eq (σ : Equiv.Perm Ω) (x : Ω) :
    (Equiv.permCongrHom e) σ (e x) = e (σ x) := by
  simp [Equiv.permCongrHom_coe, Equiv.permCongr_apply]

/-- Each fibre is nonempty: the constant tuple `c` lies in it. -/
theorem coordFibre_nonempty (c : Γ) : (coordFibre e i₀ c).Nonempty :=
  ⟨e.symm (fun _ => c), by simp [coordFibre]⟩

/-- Different values give different fibres. -/
theorem coordFibre_injective : Function.Injective (coordFibre e i₀) := by
  intro c c' h
  have hx : e.symm (fun _ => c) ∈ coordFibre e i₀ c' := by
    rw [← h]; simp [coordFibre]
  simpa [coordFibre] using hx

/-- Fibres over different values are disjoint. -/
theorem coordFibre_disjoint {c c' : Γ} (h : c ≠ c') :
    Disjoint (coordFibre e i₀ c) (coordFibre e i₀ c') := by
  rw [Set.disjoint_left]
  intro x hx hx'
  simp only [mem_coordFibre] at hx hx'
  exact h (hx.symm.trans hx')

/-- The fibres cover `Ω`. -/
theorem sUnion_coordFibres : ⋃₀ (coordFibres e i₀) = (Set.univ : Set Ω) := by
  ext x
  refine ⟨fun _ => trivial, fun _ => ?_⟩
  exact ⟨coordFibre e i₀ (e x i₀), ⟨_, rfl⟩, rfl⟩

/-- An element of the base group moves the fibre over `c` to the fibre over `h i₀ c`. -/
theorem image_coordFibre {σ : Equiv.Perm Ω} {h : Fin s → Equiv.Perm Γ}
    (hσ : (Equiv.permCongrHom e) σ = wreathPerm h 1) (c : Γ) :
    (σ : Equiv.Perm Ω) '' coordFibre e i₀ c = coordFibre e i₀ (h i₀ c) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    simp only [mem_coordFibre] at hy ⊢
    have := permCongrHom_apply_eq e σ y
    rw [hσ] at this
    rw [← this]
    simp [hy]
  · intro hx
    refine ⟨σ⁻¹ x, ?_, by simp⟩
    simp only [mem_coordFibre] at hx ⊢
    have := permCongrHom_apply_eq e σ (σ⁻¹ x)
    rw [hσ] at this
    have hxx : σ (σ⁻¹ x) = x := by simp
    rw [hxx] at this
    have hcoord : e (σ⁻¹ x) i₀ = (h i₀)⁻¹ (e x i₀) := by
      rw [← this]
      simp
    rw [hcoord, hx]
    simp

variable {H : Subgroup (Equiv.Perm Γ)} {N : Subgroup (Equiv.Perm Ω)}

/-- The base group permutes the fibres of one coordinate. -/
theorem coordFibres_permutes
    (hN : N.map (Equiv.permCongrHom e).toMonoidHom = basePower H s) :
    ∀ σ ∈ N, ∀ B ∈ coordFibres e i₀, (σ : Equiv.Perm Ω) '' B ∈ coordFibres e i₀ := by
  rintro σ hσ _ ⟨c, rfl⟩
  have hmem : (Equiv.permCongrHom e) σ ∈ basePower H s := by
    rw [← hN]; exact ⟨σ, hσ, rfl⟩
  obtain ⟨h, -, hh⟩ := hmem
  exact ⟨h i₀ c, (image_coordFibre e i₀ hh c).symm⟩

/-- The fibres of one coordinate form a system of imprimitivity for the base group `H^s`,
provided `H` is transitive on `Γ`. -/
theorem coordFibres_isSystemOfImprimitivity [Nonempty Γ]
    (hN : N.map (Equiv.permCongrHom e).toMonoidHom = basePower H s)
    (htrans : ∀ c c' : Γ, ∃ a ∈ H, a c = c') :
    IsSystemOfImprimitivity N Set.univ (coordFibres e i₀) where
  invariant := fun σ _ => Set.image_univ_of_surjective (σ : Equiv.Perm Ω).surjective
  nonempty := by rintro _ ⟨c, rfl⟩; exact coordFibre_nonempty e i₀ c
  pairwiseDisjoint := by
    rintro _ ⟨c, rfl⟩ _ ⟨c', rfl⟩ hne
    exact coordFibre_disjoint e i₀ (fun hcc => hne (by rw [hcc]))
  covers := sUnion_coordFibres e i₀
  permutes := coordFibres_permutes e i₀ hN
  blocks_nonempty := ⟨coordFibre e i₀ (Classical.arbitrary Γ), ⟨_, rfl⟩⟩
  transitiveOnBlocks := by
    rintro _ ⟨c, rfl⟩ _ ⟨c', rfl⟩
    obtain ⟨a, haH, hac⟩ := htrans c c'
    -- the element of `H^s` that is `a` in the coordinate `i₀` and the identity elsewhere
    classical
    set h : Fin s → Equiv.Perm Γ := fun i => if i = i₀ then a else 1 with hhdef
    have hhmem : ∀ i, h i ∈ H := by
      intro i
      by_cases hi : i = i₀ <;> simp [hhdef, hi, haH, one_mem]
    have hbase : wreathPerm h 1 ∈ basePower H s := ⟨h, hhmem, rfl⟩
    rw [← hN] at hbase
    obtain ⟨σ, hσN, hσ⟩ := hbase
    refine ⟨σ, hσN, ?_⟩
    rw [image_coordFibre e i₀ hσ c]
    simp [hhdef, hac]

/-- On the fibres of one coordinate, the base group `H^s` induces exactly `H`. -/
theorem coordFibres_onBlocks
    (hN : N.map (Equiv.permCongrHom e).toMonoidHom = basePower H s)
    (hperm : ∀ σ ∈ N, ∀ B ∈ coordFibres e i₀, (σ : Equiv.Perm Ω) '' B ∈ coordFibres e i₀) :
    ∃ e' : (coordFibres e i₀) ≃ Γ,
      (onBlocks N (coordFibres e i₀) hperm).map (Equiv.permCongrHom e').toMonoidHom = H := by
  classical
  -- the blocks are indexed by `Γ`
  have hbij : Function.Bijective
      (fun c : Γ => (⟨coordFibre e i₀ c, ⟨c, rfl⟩⟩ : (coordFibres e i₀))) := by
    constructor
    · intro c c' hcc
      exact coordFibre_injective e i₀ (congrArg Subtype.val hcc)
    · rintro ⟨_, c, rfl⟩
      exact ⟨c, rfl⟩
  set f : Γ ≃ (coordFibres e i₀) := Equiv.ofBijective _ hbij with hfdef
  have hf : ∀ c : Γ, f c = (⟨coordFibre e i₀ c, ⟨c, rfl⟩⟩ : (coordFibres e i₀)) :=
    fun c => rfl
  refine ⟨f.symm, ?_⟩
  -- the block permutation of an element of `N` is its `i₀`-th coordinate
  have hkey : ∀ (σ : Equiv.Perm Ω) (hσ : σ ∈ N) (h : Fin s → Equiv.Perm Γ),
      (Equiv.permCongrHom e) σ = wreathPerm h 1 →
      (Equiv.permCongrHom f.symm).toMonoidHom
        (blockHom N (coordFibres e i₀) hperm ⟨σ, hσ⟩) = h i₀ := by
    intro σ hσ h hh
    refine Equiv.ext fun c => ?_
    show f.symm (blockHom N (coordFibres e i₀) hperm ⟨σ, hσ⟩ (f c)) = h i₀ c
    have hblk : blockHom N (coordFibres e i₀) hperm ⟨σ, hσ⟩ (f c) = f (h i₀ c) := by
      refine Subtype.ext ?_
      rw [blockHom_apply_coe]
      exact image_coordFibre e i₀ hh c
    rw [hblk, Equiv.symm_apply_apply]
  apply le_antisymm
  · rintro _ ⟨_, ⟨⟨σ, hσ⟩, rfl⟩, rfl⟩
    have hmem : (Equiv.permCongrHom e) σ ∈ basePower H s := by
      rw [← hN]; exact ⟨σ, hσ, rfl⟩
    obtain ⟨h, hhmem, hh⟩ := hmem
    rw [hkey σ hσ h hh]
    exact hhmem i₀
  · intro a haH
    -- the element of `H^s` that is `a` in the coordinate `i₀` and the identity elsewhere
    set h : Fin s → Equiv.Perm Γ := fun i => if i = i₀ then a else 1 with hhdef
    have hhmem : ∀ i, h i ∈ H := by
      intro i
      by_cases hi : i = i₀ <;> simp [hhdef, hi, haH, one_mem]
    have hbase : wreathPerm h 1 ∈ basePower H s := ⟨h, hhmem, rfl⟩
    rw [← hN] at hbase
    obtain ⟨σ, hσN, hσ⟩ := hbase
    refine ⟨blockHom N (coordFibres e i₀) hperm ⟨σ, hσN⟩, ⟨⟨σ, hσN⟩, rfl⟩, ?_⟩
    rw [hkey σ hσN h hσ]
    simp [hhdef]

end Babai
