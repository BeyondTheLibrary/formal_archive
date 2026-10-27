import Workspace.Algo.SplitDesignDomRaw

/-! # The position bijections for the dominant-class Johnson output -/
namespace Algo
open Babai RAM

section
variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {s : Set Ω}
    {X : BlkDesignObj s} {name₁ : ↥X.Pt₁ → ℕ} {name₂ : ↥X.blocks → ℕ}
    {r : RawUpccCase} (h : DesignNames X name₁ name₂ r)
    (e₁ : ↥X.Pt₁ ≃ Fin r.2.1.length) (he₁ : ∀ x, r.2.1[(e₁ x).val] = name₁ x)
    (e₂ : ↥X.blocks ≃ Fin r.2.2.length) (he₂ : ∀ B, r.2.2[(e₂ B).val] = name₂ B)
include h he₁ he₂

theorem designBigEquiv_exists : ∃ eC : ↥X.bigTwin ≃ Fin (designBigPositions r).length,
    ∀ B, (designBigPositions r)[(eC B).val] =
      (e₂ ⟨B.val,X.bigTwin_subset_blocks B.property⟩).val := by
  apply splitNameEquiv_exists
    (fun B : ↥X.bigTwin => (e₂ ⟨B.val,X.bigTwin_subset_blocks B.property⟩).val)
    (fun B C hh => Subtype.ext (congrArg (fun B : ↥X.blocks => B.val) (e₂.injective (Fin.ext hh))))
    (designBigPositions r) (List.nodup_range.filter _)
  intro i
  constructor
  · intro hi
    have hil := List.mem_range.1 (List.mem_of_mem_filter hi)
    let B := e₂.symm ⟨i,hil⟩
    have hB : B.val ∈ X.bigTwin := (designBigPositions_spec h e₁ he₁ e₂ he₂ B).1 (by
      simpa only [B,Equiv.apply_symm_apply] using hi)
    refine ⟨⟨B.val,hB⟩,?_⟩
    change (e₂ B).val = i
    exact congrArg Fin.val (e₂.apply_symm_apply _)
  · rintro ⟨B,rfl⟩
    exact (designBigPositions_spec h e₁ he₁ e₂ he₂
      ⟨B.val,X.bigTwin_subset_blocks B.property⟩).2 B.property

theorem designDomEquiv_exists (p : ℕ × ℕ) (hb : 0 < p.2) :
    ∃ eA : ↥(X.domClass (sbipAlphaValue p)) ≃ Fin (designDomPositions (r,p)).length,
      ∀ x, (designDomPositions (r,p))[(eA x).val] = (e₁ ⟨x.val,x.property.1⟩).val := by
  apply splitNameEquiv_exists
    (fun x : ↥(X.domClass (sbipAlphaValue p)) => (e₁ ⟨x.val,x.property.1⟩).val)
    (fun x y hh => Subtype.ext (congrArg (fun x : ↥X.Pt₁ => x.val) (e₁.injective (Fin.ext hh))))
    (designDomPositions (r,p)) (List.nodup_range.filter _)
  intro i
  constructor
  · intro hi
    have hil := List.mem_range.1 (List.mem_of_mem_filter hi)
    let x := e₁.symm ⟨i,hil⟩
    have hx : x.val ∈ X.domClass (sbipAlphaValue p) :=
      (designDomPositions_spec h e₁ he₁ e₂ he₂ p hb x).1 (by
        simpa only [x,Equiv.apply_symm_apply] using hi)
    refine ⟨⟨x.val,hx⟩,?_⟩
    change (e₁ x).val = i
    exact congrArg Fin.val (e₁.apply_symm_apply _)
  · rintro ⟨x,rfl⟩
    exact (designDomPositions_spec h e₁ he₁ e₂ he₂ p hb ⟨x.val,x.property.1⟩).2 x.property

theorem designDomPositions_size (p : ℕ × ℕ) (hb : 0 < p.2) :
    (designDomPositions (r,p)).length = (X.domClass (sbipAlphaValue p)).ncard := by
  obtain ⟨eA,_⟩ := designDomEquiv_exists h e₁ he₁ e₂ he₂ p hb
  have hh := Nat.card_congr eA
  rw [Nat.card_coe_set_eq,Nat.card_fin] at hh
  exact hh.symm

omit h he₁ he₂ in
theorem designDomPoints_nodup (p : ℕ × ℕ) (hleft : r.2.1.Nodup) :
    (designDomPoints (r,p)).Nodup := by
  apply List.Nodup.map_on ?_ (List.nodup_range.filter _)
  intro i hi j hj hh
  have hil := List.mem_range.1 (List.mem_of_mem_filter hi)
  have hjl := List.mem_range.1 (List.mem_of_mem_filter hj)
  change labAt r.2.1 i = labAt r.2.1 j at hh
  simp only [labAt,List.getD_eq_getElem _ _ hil,List.getD_eq_getElem _ _ hjl] at hh
  exact (List.Nodup.getElem_inj_iff hleft).1 hh

end
end Algo
