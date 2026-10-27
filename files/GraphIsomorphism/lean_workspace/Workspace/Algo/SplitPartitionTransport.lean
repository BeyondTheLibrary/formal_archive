import Workspace.ColoredPartitions.Basic

/-! Validity of a stored partition depends on its color classes and blocks.
Changing the names of colors or vertices leaves these bounds unchanged. -/

namespace Babai.ColoredPartition

universe u v w z

variable {V : Type u} {W : Type v} {C : Type w} {D : Type z}
    (P : ColoredPartition V C) (Q : ColoredPartition W D) (e : V ≃ W)
    (hc : ∀ x y, P.color x = P.color y ↔ Q.color (e x) = Q.color (e y))
    (hp : ∀ x y, P.part x y ↔ Q.part (e x) (e y))

include hp in
theorem image_block_of_rel (x : V) : e '' P.block x = Q.block (e x) := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact (hp z x).mp hz
  · intro hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    apply (hp _ _).mpr
    simpa using hy

include hc in
theorem image_colorClass_of_kernel (x : V) :
    e '' P.colorClass (P.color x) = Q.colorClass (Q.color (e x)) := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact (hc z x).mp hz
  · intro hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    apply (hc _ _).mpr
    simpa using hy

include hp in
theorem ncard_block_of_rel (x : V) :
    (P.block x).ncard = (Q.block (e x)).ncard := by
  rw [← image_block_of_rel P Q e hp x, Set.ncard_image_of_injective _ e.injective]

include hc in
theorem ncard_colorClass_of_kernel (x : V) :
    (P.colorClass (P.color x)).ncard = (Q.colorClass (Q.color (e x))).ncard := by
  rw [← image_colorClass_of_kernel P Q e hc x,
    Set.ncard_image_of_injective _ e.injective]

include hc hp in
theorem isAdmissible_of_kernel_rel (h : P.IsAdmissible) : Q.IsAdmissible := by
  intro y hy
  obtain ⟨x, rfl⟩ := e.surjective y
  rw [← ncard_block_of_rel P Q e hp x]
  apply h x
  rwa [ncard_colorClass_of_kernel P Q e hc x]

include hp in
theorem rho_of_rel [Fintype V] [Fintype W] : P.rho = Q.rho := by
  apply Nat.le_antisymm
  · apply P.rho_le
    intro x
    rw [ncard_block_of_rel P Q e hp x]
    exact Q.ncard_block_le_rho (e x)
  · apply Q.rho_le
    intro y
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [← ncard_block_of_rel P Q e hp x]
    exact P.ncard_block_le_rho x

include hc hp in
theorem isAlphaPartition_of_kernel_rel [Fintype V] [Fintype W] {α : ℝ}
    (h : P.IsAlphaPartition α) : Q.IsAlphaPartition α := by
  refine ⟨isAdmissible_of_kernel_rel P Q e hc hp h.1, ?_⟩
  rw [← rho_of_rel P Q e hp, ← Fintype.card_congr e]
  exact h.2

include hc hp in
theorem isEquipartition_of_kernel_rel (h : P.IsEquipartition) :
    Q.IsEquipartition := by
  intro x y hxy
  obtain ⟨a, rfl⟩ := e.surjective x
  obtain ⟨b, rfl⟩ := e.surjective y
  rw [← ncard_block_of_rel P Q e hp a, ← ncard_block_of_rel P Q e hp b]
  exact h a b ((hc a b).mpr hxy)

end Babai.ColoredPartition
