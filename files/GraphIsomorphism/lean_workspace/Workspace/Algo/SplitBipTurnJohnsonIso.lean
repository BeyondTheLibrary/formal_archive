import Workspace.Algo.SplitBipTurnDesignPartitionFamily

/-! Johnson exits of a split turn are compared through the input map.
A restored Johnson scheme is isomorphic to another one when the input map
carries its carrier onto the other carrier and keeps every stored color.
The local form reads both conditions from named points of Step 9.
-/
namespace Algo
open Babai RAM
open scoped Classical

/-- Sec. 9.2 (the Johnson summand of the outcome category): two restored
Johnson outputs are isomorphic by the restriction of `φ` when `φ` maps one
carrier onto the other and preserves the colors `|S ∖ T|`. -/
theorem sbipNamedOutcomeIso_johnson {m : ℕ} {I J : RawSbipNode}
    {X Y : Pt (BipBlockInputs (Fin m))} (φ : ↥X.car ≃ ↥Y.car) {ms ts ms' ts' : ℕ}
    (K K' : RawJohnson) (hK : K.WF m ms ts) (hK' : K'.WF m ms' ts')
    (hZ : RawJohnson.carrier m K ⊆ X.car) (hZ' : RawJohnson.carrier m K' ⊆ Y.car)
    (hmem : ∀ x : ↥X.car,((x.val : ℕ) ∈ K.1 ↔ ((φ x).val : ℕ) ∈ K'.1))
    (hcol : ∀ x y : ↥X.car,(x.val : ℕ) ∈ K.1 → (y.val : ℕ) ∈ K.1 →
      rawJDiff (K',(((φ x).val : ℕ),((φ y).val : ℕ))) =
        rawJDiff (K,((x.val : ℕ),(y.val : ℕ)))) :
    SbipNamedOutcomeIso I J X Y φ (rawAlignJohnson K) (rawAlignJohnson K') := by
  refine ⟨_,_,sbipDecodeNamed_johnson _ K hK,sbipDecodeNamed_johnson _ K' hK',hZ,hZ',?_⟩
  let g : ↥(RawJohnson.carrier m K) ≃ ↥(RawJohnson.carrier m K') :=
    { toFun := fun u => ⟨(φ ⟨u.val,hZ u.2⟩).val,(hmem ⟨u.val,hZ u.2⟩).1 u.2⟩
      invFun := fun w => ⟨(φ.symm ⟨w.val,hZ' w.2⟩).val,
        (hmem (φ.symm ⟨w.val,hZ' w.2⟩)).2 (by simpa only [Equiv.apply_symm_apply] using w.2)⟩
      left_inv := fun u => by simp
      right_inv := fun w => by simp }
  refine ⟨g,fun _ => rfl,?_⟩
  intro u v
  exact hcol ⟨u.val,hZ u.2⟩ ⟨v.val,hZ v.2⟩ u.2 v.2

section Local
variable {m : ℕ} {I J : RawSbipNode} {X Y : Pt (BipBlockInputs (Fin m))}
    {φ : ↥X.car ≃ ↥Y.car} (hφ : φ ∈ (BipBlockInputs (Fin m)).IsoP X Y)
    {P : Set ↥(step7Set X)} {P' : Set ↥(step7Set Y)}
    (hP : ∀ z,z ∈ P ↔ step7Equiv hφ z ∈ P')
    {d d' : List (List ℕ)} {K K' : RawJohnson} {name : ↥P → ℕ} {name' : ↥P' → ℕ}
    (hrow : ∀ u,sbipDictPoint (d,name u) = (u.val.val : ℕ))
    (hrow' : ∀ u,sbipDictPoint (d',name' u) = (u.val.val : ℕ))
    (hK₁ : ∀ a,a ∈ K.1 ↔ ∃ u,name u = a) (hK₁' : ∀ a,a ∈ K'.1 ↔ ∃ u,name' u = a)
    {N N' ms ts ms' ts' : ℕ} (hK : K.WF N ms ts) (hK' : K'.WF N' ms' ts')

omit hφ in
include hrow hK₁ hK in
private theorem johnson_local_restore :
    (∀ a,a ∈ (sbipCaseJohnson (d,K)).1 ↔ ∃ u : ↥P,(u.val.val : ℕ) = a) ∧
    (sbipCaseJohnson (d,K)).WF m ms ts ∧
    ∀ u v : ↥P,rawJDiff (sbipCaseJohnson (d,K),((u.val.val : ℕ),(v.val.val : ℕ))) =
      rawJDiff (K,(name u,name v)) := by
  have hinj : Set.InjOn (fun a => sbipDictPoint (d,a)) {a | a ∈ K.1} := by
    intro a ha b hb he
    obtain ⟨u,rfl⟩ := (hK₁ a).1 ha
    obtain ⟨v,rfl⟩ := (hK₁ b).1 hb
    change sbipDictPoint (d,name u) = sbipDictPoint (d,name v) at he
    rw [hrow,hrow] at he
    exact congrArg name (Subtype.ext (Subtype.ext (Fin.ext he)))
  have hlt : ∀ a ∈ K.1,sbipDictPoint (d,a) < m := by
    intro a ha
    obtain ⟨u,rfl⟩ := (hK₁ a).1 ha
    rw [hrow]
    exact u.val.val.isLt
  refine ⟨fun a => ?_,sbipCaseJohnson_wf hinj hlt hK,fun u v => ?_⟩
  · simp only [sbipCaseJohnson,List.mem_map]
    constructor
    · rintro ⟨b,hb,rfl⟩
      obtain ⟨u,rfl⟩ := (hK₁ b).1 hb
      exact ⟨u,(hrow u).symm⟩
    · rintro ⟨u,rfl⟩
      exact ⟨name u,(hK₁ _).2 ⟨u,rfl⟩,hrow u⟩
  · rw [← hrow u,← hrow v]
    exact sbipCaseJohnson_diff hinj hlt hK ((hK₁ _).2 ⟨u,rfl⟩) ((hK₁ _).2 ⟨v,rfl⟩)

include hP hrow hrow' hK₁ hK₁' hK hK' in
/-- Sec. 9.7 (Johnson exits, Case 1 and the last exit of Case 2): a Johnson
output named on Step 9 points is carried by the input map when the point
set and the stored colors correspond under the restriction of `φ`. -/
theorem sbipNamedOutcomeIso_johnson_local
    (hcol : ∀ u v : ↥P,rawJDiff (K',(name' ⟨step7Equiv hφ u.val,(hP u.val).1 u.2⟩,
      name' ⟨step7Equiv hφ v.val,(hP v.val).1 v.2⟩)) = rawJDiff (K,(name u,name v))) :
    SbipNamedOutcomeIso I J X Y φ (rawAlignJohnson (sbipCaseJohnson (d,K)))
      (rawAlignJohnson (sbipCaseJohnson (d',K'))) := by
  obtain ⟨hm,hw,hc⟩ := johnson_local_restore hrow hK₁ hK
  obtain ⟨hm',hw',hc'⟩ := johnson_local_restore hrow' hK₁' hK'
  let pm : ↥P → ↥P' := fun u => ⟨step7Equiv hφ u.val,(hP u.val).1 u.2⟩
  have hpm (u : ↥P) : ((pm u).val.val : Fin m) = (φ ⟨u.val.val,step7Set_subset X u.val.2⟩).val := rfl
  have hZ : RawJohnson.carrier m (sbipCaseJohnson (d,K)) ⊆ X.car := by
    intro a ha
    obtain ⟨u,hu⟩ := (hm _).1 ha
    rw [show a = u.val.val from Fin.ext hu.symm]
    exact step7Set_subset X u.val.2
  have hZ' : RawJohnson.carrier m (sbipCaseJohnson (d',K')) ⊆ Y.car := by
    intro a ha
    obtain ⟨u,hu⟩ := (hm' _).1 ha
    rw [show a = u.val.val from Fin.ext hu.symm]
    exact step7Set_subset Y u.val.2
  -- a point of the carrier is the value of a named point
  have hx (x : ↥X.car) (hx : (x.val : ℕ) ∈ (sbipCaseJohnson (d,K)).1) :
      ∃ u : ↥P,x = ⟨u.val.val,step7Set_subset X u.val.2⟩ := by
    obtain ⟨u,hu⟩ := (hm _).1 hx
    exact ⟨u,Subtype.ext (Fin.ext hu.symm)⟩
  apply sbipNamedOutcomeIso_johnson φ _ _ hw hw' hZ hZ'
  · intro x
    constructor
    · intro hxm
      obtain ⟨u,rfl⟩ := hx x hxm
      exact (hm' _).2 ⟨pm u,by rw [hpm]⟩
    · intro hxm
      obtain ⟨u',hu'⟩ := (hm' _).1 hxm
      let z := (step7Equiv hφ).symm u'.val
      have hz : z ∈ P := (hP z).2 (by simpa only [z,Equiv.apply_symm_apply] using u'.2)
      have hzx : (⟨z.val,step7Set_subset X z.2⟩ : ↥X.car) = x := by
        apply φ.injective
        apply Subtype.ext
        apply Fin.ext
        rw [← hu']
        have := step7Equiv_val hφ z
        simp only [z,Equiv.apply_symm_apply] at this
        rw [← this]
      exact (hm _).2 ⟨⟨z,hz⟩,by rw [← hzx]⟩
  · intro x y hxm hym
    obtain ⟨u,rfl⟩ := hx x hxm
    obtain ⟨v,rfl⟩ := hx y hym
    rw [hc u v,← hpm u,← hpm v,hc' (pm u) (pm v)]
    exact hcol u v

end Local

end Algo
