/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Tools for the proof of [DiM, Thm. 5.2A,B]: relabeling the permutation domain.
-/
import Workspace.AltQuotients.DM52.FinPerm

/-!
# Relabeling the permutation domain

A bijection `e : α ≃ β` carries a subgroup `G ≤ Sym(α)` to `G^e := e G e⁻¹ ≤ Sym(β)`; this
preserves the alternating group, indices, primitivity and the isomorphism type.  The
small-degree cases of [DiM, Thm. 5.2A,B] are done on `Fin n` and carried back.
-/

namespace Babai.DM52

open Equiv Equiv.Perm MulAction Nat Subgroup

variable {α β : Type*}

/-- The relabeled group `e G e⁻¹`. -/
abbrev relabel (e : α ≃ β) (G : Subgroup (Perm α)) : Subgroup (Perm β) :=
  G.map e.permCongrHom.toMonoidHom

theorem relabel_injective (e : α ≃ β) : Function.Injective (relabel e) :=
  Subgroup.map_injective e.permCongrHom.injective

theorem relabel_le_relabel_iff (e : α ≃ β) {G H : Subgroup (Perm α)} :
    relabel e G ≤ relabel e H ↔ G ≤ H :=
  Subgroup.map_le_map_iff_of_injective e.permCongrHom.injective

theorem relabel_relIndex (e : α ≃ β) (G H : Subgroup (Perm α)) :
    (relabel e G).relIndex (relabel e H) = G.relIndex H :=
  Subgroup.relIndex_map_map_of_injective G H e.permCongrHom.injective

theorem relabel_index (e : α ≃ β) (G : Subgroup (Perm α)) :
    (relabel e G).index = G.index :=
  Subgroup.index_map_equiv (G := Perm α) (G' := Perm β) (H := G) e.permCongrHom

theorem card_relabel (e : α ≃ β) (G : Subgroup (Perm α)) :
    Nat.card (relabel e G) = Nat.card G :=
  (Nat.card_congr (e.permCongrHom.subgroupMap G).toEquiv).symm

/-- `G ≃* e G e⁻¹`. -/
noncomputable def relabelEquiv (e : α ≃ β) (G : Subgroup (Perm α)) : G ≃* relabel e G :=
  e.permCongrHom.subgroupMap G

theorem mem_relabel (e : α ≃ β) {G : Subgroup (Perm α)} {g : Perm β} :
    g ∈ relabel e G ↔ e.symm.permCongr g ∈ G := by
  constructor
  · rintro ⟨h, hh, rfl⟩
    have : e.symm.permCongr (e.permCongr h) = h := e.permCongr.symm_apply_apply h
    simpa [Equiv.permCongrHom_coe, this] using hh
  · intro hg
    exact ⟨e.symm.permCongr g, hg, by
      simpa [Equiv.permCongrHom_coe] using e.permCongr.apply_symm_apply g⟩

theorem relabel_apply (e : α ≃ β) (g : Perm α) (x : β) :
    e.permCongrHom g x = e (g (e.symm x)) := rfl

/-- Primitivity is preserved by relabeling. -/
theorem isPreprimitive_relabel_iff (e : α ≃ β) (G : Subgroup (Perm α)) :
    IsPreprimitive (relabel e G) β ↔ IsPreprimitive G α := by
  let ψ : G → relabel e G := (relabelEquiv e G)
  let f : α →ₑ[ψ] β := ⟨e, fun g x => by
    simp only [ψ, relabelEquiv, Subgroup.smul_def, Perm.smul_def]
    show e ((g : Perm α) x) = e.permCongrHom (g : Perm α) (e x)
    simp⟩
  exact (isPreprimitive_congr (relabelEquiv e G).surjective
    (f := f) e.bijective).symm

variable [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

theorem relabel_alternatingGroup (e : α ≃ β) :
    relabel e (alternatingGroup α) = alternatingGroup β := by
  ext g
  rw [mem_relabel, mem_alternatingGroup, mem_alternatingGroup]
  simp [sign_permCongr]

/-- Transport of the hypotheses and conclusion `Alt ≤ G` along a relabeling. -/
theorem alternatingGroup_le_of_relabel (e : α ≃ β) {G : Subgroup (Perm α)}
    (h : alternatingGroup β ≤ relabel e G) : alternatingGroup α ≤ G := by
  rw [← relabel_alternatingGroup e, relabel_le_relabel_iff] at h; exact h

theorem relabel_le_alternatingGroup (e : α ≃ β) {G : Subgroup (Perm α)}
    (h : G ≤ alternatingGroup α) : relabel e G ≤ alternatingGroup β := by
  rw [← relabel_alternatingGroup e, relabel_le_relabel_iff]; exact h

theorem relabel_relIndex_alternatingGroup (e : α ≃ β) (G : Subgroup (Perm α)) :
    (relabel e G).relIndex (alternatingGroup β) = G.relIndex (alternatingGroup α) := by
  rw [← relabel_alternatingGroup e, relabel_relIndex]

end Babai.DM52
