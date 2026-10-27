import Workspace.Algo.SplitDesignJohnson
import Workspace.Algo.SplitNamedLists
import Workspace.Algo.SplitBipStep9Input

/-! # Section 9.7: feed the block design case from the second refinement

The vertex positions used by step 9 give names for the first-part points
and second-part blocks. The refinement theorem supplies the exact colors,
so the implementation needs no separate color-table assumption.
-/
namespace Algo
open Babai RAM

section Input
variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {N : ℕ}
    (X : Pt (Step9DesignInputs Ω N)) {r : RawSbipRefine}
    {name : (step8Obj (step9Base X)).Vtx → ℕ}
    (h : SbipStep8Names (step9Base X) r name)
    (hd : (r.1.2.2 ++ r.1.2.1).Nodup)
    (e : (step8Obj (step9Base X)).Vtx ≃ Fin (r.1.2.2 ++ r.1.2.1).length)
    (hl : ∀ A, (r.1.2.2 ++ r.1.2.1)[(e A).val] = name A)

include h hd hl

/-- The raw input computed in step 9 satisfies every naming hypothesis of Section 9.7. -/
theorem sbipStep9Input_designNames :
    DesignNames (BlkBlockDesignInputs.obj₀ ((step9DesignFunc N).obj X))
      (fun x => (e ((BlkBlockDesignInputs.obj₀ ((step9DesignFunc N).obj X)).vtxOfPt x)).val)
      (fun B => (e ((BlkBlockDesignInputs.obj₀ ((step9DesignFunc N).obj X)).vtxOfBlk B)).val)
      (sbipStep9Input r) := by
  let Y := (BlkBlockDesignInputs.obj₀ ((step9DesignFunc N).obj X))
  have hleft (A : (step8Obj (step9Base X)).Vtx) :
      r.1.2.2.length ≤ (e A).val ↔ ∃ x, Y.part₁ x ∧ A.val = {x} := by
    rw [← sbipSuffix_mem _ _ hd (e A),hl A]
    exact h.left A
  have hright (A : (step8Obj (step9Base X)).Vtx) :
      (e A).val < r.1.2.2.length ↔ A.val ∈ Y.blocks := by
    rw [← sbipPrefix_mem _ _ hd (e A),hl A]
    exact h.right A
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · intro x y hh
    exact Subtype.ext (Set.singleton_injective (congrArg Subtype.val (e.injective (Fin.ext hh))))
  · intro B C hh
    have hb := congrArg (fun A : (step8Obj (step9Base X)).Vtx => A.val) (e.injective (Fin.ext hh))
    exact Subtype.ext hb
  · intro a
    constructor
    · intro ha
      obtain ⟨hlo,hhi⟩ := (sbipStep9Input_left r _).1 ha
      let A := e.symm ⟨a,hhi⟩
      have hA : (e A).val = a := congrArg Fin.val (e.apply_symm_apply ⟨a,hhi⟩)
      obtain ⟨x,hx,he⟩ := (hleft A).1 (hA.symm ▸ hlo)
      refine ⟨⟨x,hx⟩,?_⟩
      have hv : Y.vtxOfPt ⟨x,hx⟩ = A := Subtype.ext he.symm
      change (e (Y.vtxOfPt ⟨x,hx⟩)).val = a
      rw [hv,hA]
    · rintro ⟨x,rfl⟩
      exact (sbipStep9Input_left r _).2
        ⟨(hleft (Y.vtxOfPt x)).2 ⟨x,x.property,rfl⟩,(e (Y.vtxOfPt x)).isLt⟩
  · intro a
    constructor
    · intro ha
      have hlo := (sbipStep9Input_right r _).1 ha
      have hhi : a < (r.1.2.2 ++ r.1.2.1).length := by simp only [List.length_append]; omega
      let A := e.symm ⟨a,hhi⟩
      have hA : (e A).val = a := congrArg Fin.val (e.apply_symm_apply ⟨a,hhi⟩)
      have hb := (hright A).1 (hA.symm ▸ hlo)
      refine ⟨⟨A.val,hb⟩,?_⟩
      have hv : Y.vtxOfBlk ⟨A.val,hb⟩ = A := Subtype.ext rfl
      change (e (Y.vtxOfBlk ⟨A.val,hb⟩)).val = a
      rw [hv,hA]
    · rintro ⟨B,rfl⟩
      exact (sbipStep9Input_right r _).2 ((hright (Y.vtxOfBlk B)).2 B.property)
  · intro x B
    change binColor (sbipStep9Table r,(e (Y.vtxOfPt x),e (Y.vtxOfBlk B))) =
      step8CaseColor (step9Base X) _ _
    rw [sbipStep9Table_spec h e hl]
    exact (step8CaseColor_vtx (step9Base X) _ _).symm
  · intro B C
    change binColor (sbipStep9Table r,(e (Y.vtxOfBlk B),e (Y.vtxOfBlk C))) =
      step8CaseColor (step9Base X) _ _
    rw [sbipStep9Table_spec h e hl]
    exact (step8CaseColor_vtx (step9Base X) _ _).symm

  · intro x y
    change binColor (sbipStep9Table r,(e (Y.vtxOfPt x),e (Y.vtxOfPt y))) =
      step8CaseColor (step9Base X) _ _
    rw [sbipStep9Table_spec h e hl]
    exact (step8CaseColor_vtx (step9Base X) _ _).symm

/-- The computed case test reaches the block design case on its actual input category. -/
theorem sbipStep9Input_designCase : sbipStep9Case (sbipStep9Input r) = 1 := by
  have hr (A : (step8Obj (step9Base X)).Vtx) :
      (e A).val < r.1.2.2.length ↔ A.val ∈ (step8Obj (step9Base X)).blocks := by
    rw [← sbipPrefix_mem _ _ hd (e A),hl A]
    exact h.right A
  let eb : ↥(step8Blks (step9Base X)) ≃ Fin r.1.2.2.length := {
    toFun := fun B => ⟨e B.val,(hr B.val).2 B.property⟩
    invFun := fun i => ⟨e.symm ⟨i.val,by simp only [List.length_append]; omega⟩,
      (hr _).1 (by simpa using i.isLt)⟩
    left_inv := fun B => Subtype.ext (e.symm_apply_apply B.val)
    right_inv := by
      intro i
      apply Fin.ext
      change (e (e.symm ⟨i.val,by simp only [List.length_append]; omega⟩)).val = i.val
      simp only [Equiv.apply_symm_apply] }
  let eb' : ↥(step8Blks (step9Base X)) ≃ Fin (sbipStep9Input r).2.2.length :=
    eb.trans (finCongr (by simp [sbipStep9Input]))
  have hc : ∀ u v, binColor ((sbipStep9Input r).1,
      ((sbipStep9Input r).2.2[(eb' u).val],(sbipStep9Input r).2.2[(eb' v).val])) =
        step9BlkColor (step9Base X) u v := by
    intro u v
    simp only [sbipStep9Input,List.getElem_range]
    change binColor (sbipStep9Table r,(e u.val,e v.val)) = _
    rw [sbipStep9Table_spec h e hl]
    exact (step8CaseColor_vtx (step9Base X) u.val v.val).symm
  exact (sbipStep9Case_spec (step9Base X) (sbipStep9Input r) eb' hc).2.1.mpr ⟨X.obj.2.2.1,X.obj.2.2.2⟩

/-- Case 1 at the actual step-9 input returns the paper's Johnson scheme. -/
theorem sbipStep9Input_designJohnson
    (hc : designCase1 (sbipStep9Input r) = true) :
    let Y := BlkBlockDesignInputs.obj₀ ((step9DesignFunc N).obj X)
    let r' := sbipStep9Input r
    RawJohnson.WF r'.1.1.length Y.n₂ Y.d' (designJohnson r') ∧
      ∀ x y : ↥Y.Pt₁,
        rawJDiff (designJohnson r',
          ((e (Y.vtxOfPt x)).val,(e (Y.vtxOfPt y)).val)) =
          Y.johnsonColor x.val y.val := by
  dsimp only
  have hn := sbipStep9Input_designNames X h hd e hl
  have hw := sbipStep9Input_wf r
  obtain ⟨e₁,he₁⟩ := splitNameEquiv_exists _ hn.inj₁ _ hw.left_nodup hn.left
  obtain ⟨e₂,he₂⟩ := splitNameEquiv_exists _ hn.inj₂ _ hw.right_nodup hn.right
  have hcase := (designCase1_spec hn e₁ he₁ e₂ he₂).1 hc
  exact ⟨designJohnson_wf hn e₁ he₁ e₂ he₂ hw
      (BlkBlockDesignInputs.numBlocks_lt_n₁ ((step9DesignFunc N).obj X)) hcase,
    designJohnson_color hn e₁ he₁ e₂ he₂ hw.left_nodup⟩

end Input
end Algo
