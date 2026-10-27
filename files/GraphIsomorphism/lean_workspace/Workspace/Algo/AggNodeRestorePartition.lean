import Workspace.Algo.AggNodeRestoreJohnson

/-! The restored partition is the paper's extension of the decoded local
partition, transported through the original-name dictionary. This identifies
its actual colors and blocks, rather than only their size bounds.
-/
namespace Algo
open Babai RAM
open scoped Classical

variable {m : ℕ} {D : List ℕ}

noncomputable def aggnLocalPartition (m : ℕ) (D : List ℕ) (hnd : D.Nodup)
    (hlt : ∀ a ∈ D, a < m) (P : RawColPart) : ColoredPartition ↥(winSet m D) ℕ :=
  (decColPartition D.length P).pushforward (winEquiv m D hnd hlt)

theorem aggnRestorePartition_eq (hnd : D.Nodup) (hlt : ∀ a ∈ D, a < m) (P : RawColPart) :
    decAlignPartition m (rawExtendPartition ((List.range m,D),P)) =
      extendOutcome ⟨winSet m D,Sum.inl (aggnLocalPartition m D hnd hlt P)⟩ := by
  let e := winEquiv m D hnd hlt
  let eV : ↥(Set.univ : Set (Fin m)) ≃ Fin (List.range m).length :=
    (Equiv.Set.univ (Fin m)).trans (finCongr (List.length_range (n := m)).symm)
  have hv : ∀ x, (List.range m)[(eV x).val]'(eV x).isLt = x.val.val := by
    intro x
    simp [eV]
  have hw : ∀ x, D[(e.symm x).val]'(e.symm x).isLt = x.val.val := by
    intro x
    have hh := winEquiv_symm_val D hnd hlt x
    rw [List.getD_eq_getElem _ _ (e.symm x).isLt] at hh
    exact hh
  have hmem : ∀ x : ↥(Set.univ : Set (Fin m)), x.val.val ∈ D ↔ x.val ∈ winSet m D :=
    fun _ => Iff.rfl
  have hc : ∀ x, labAt P.1 (e.symm x) = (aggnLocalPartition m D hnd hlt P).color x :=
    fun _ => rfl
  have hp : ∀ x y, cellOf P (e.symm x) = cellOf P (e.symm y) ↔
      (aggnLocalPartition m D hnd hlt P).part x y := fun _ _ => Iff.rfl
  change (⟨Set.univ,Sum.inl _⟩ : Pt (SplitOutcomes (Fin m))) = ⟨Set.univ,Sum.inl _⟩
  congr 1
  apply congrArg Sum.inl
  apply ColoredPartition.ext
  · funext x
    have hh := rawExtendPartition_color (aggnLocalPartition m D hnd hlt P) Fin.val
      eV hv e.symm hw hnd hmem hc x
    simpa only [eV,Equiv.trans_apply,Equiv.Set.univ_apply,finCongr_apply,
      Fin.val_cast,List.length_range] using hh
  · apply Setoid.ext
    intro x y
    have hh := rawExtendPartition_part (aggnLocalPartition m D hnd hlt P) Fin.val
      eV hv e.symm hw hnd hmem hp x y
    simpa only [eV,Equiv.trans_apply,Equiv.Set.univ_apply,finCongr_apply,
      Fin.val_cast,List.length_range] using hh

theorem aggnRestorePartition_decode (hnd : D.Nodup) (hlt : ∀ a ∈ D, a < m)
    (dom : List ℕ) (hdom : dom.length = m) (P : RawColPart) :
    decAlignOutcome m (aggnRestoreOutcome ((dom,D),rawAlignPartition P)) =
      some (extendOutcome ⟨winSet m D,Sum.inl (aggnLocalPartition m D hnd hlt P)⟩) := by
  rw [aggnRestoreOutcome_partition,hdom,decAlignOutcome_partition,aggnRestorePartition_eq hnd hlt]

/-- Local partition validity survives the change from positions to old names. -/
theorem aggnLocalPartition_valid (hnd : D.Nodup) (hlt : ∀ a ∈ D, a < m)
    (P : RawColPart) {α : ℝ} (hP : (decColPartition D.length P).IsAlphaPartition α) :
    (aggnLocalPartition m D hnd hlt P).IsAlphaPartition α := by
  apply ColoredPartition.isAlphaPartition_of_kernel_rel (decColPartition D.length P)
    (aggnLocalPartition m D hnd hlt P) (winEquiv m D hnd hlt)
  · intro x y
    simp only [aggnLocalPartition,ColoredPartition.pushforward,Equiv.symm_apply_apply]
  · intro x y
    change (decColPartition D.length P).part x y ↔
      (decColPartition D.length P).part
        ((winEquiv m D hnd hlt).symm ((winEquiv m D hnd hlt) x))
        ((winEquiv m D hnd hlt).symm ((winEquiv m D hnd hlt) y))
    simp only [Equiv.symm_apply_apply]
  · exact hP

end Algo
