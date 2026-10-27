import Workspace.Algo.SplitBipTurnLift
import Workspace.Algo.SplitBipTurnJohnsonIso

/-! A child answer is lifted to its parent by the complement extension of
Sec. 9.4 (a partition), or kept unchanged (a Johnson scheme). Isomorphic
child answers, whose map restricts the parent input map, lift to
isomorphic parent answers by that same input map.
-/
namespace Algo
open Babai RAM
open scoped Classical

/-- The named decoder returns either an extended-list partition or a
well-formed Johnson scheme. -/
theorem sbipDecodeNamed_cases {m : ℕ} {L : List ℕ} {o : RawAlignOutcome}
    {Z : Pt (SplitOutcomes (Fin m))} (hd : sbipDecodeNamed m L o = some Z) :
    (∃ q,o = rawAlignPartition q ∧ ∃ (hn : L.Nodup) (hb : ∀ a ∈ L,a < m),
      Z = sbipDecodeNamedPartition L hn hb q) ∨
    (∃ j,o = rawAlignJohnson j ∧ ∃ hw : j.WF m (rawJDeg j) j.2.1,Z = decAlignJohnson j hw) := by
  rcases o with ⟨_|q,_|j⟩
  · simp [sbipDecodeNamed,decAlignOutcome] at hd
  · refine Or.inr ⟨j,rfl,?_⟩
    change (if hw : j.WF m (rawJDeg j) j.2.1 then some (decAlignJohnson j hw) else none) = some Z at hd
    split at hd
    next hw => exact ⟨hw,(Option.some.inj hd).symm⟩
    next => cases hd
  · refine Or.inl ⟨q,rfl,?_⟩
    change (if h : L.Nodup ∧ ∀ a ∈ L,a < m then
      some (sbipDecodeNamedPartition L h.1 h.2 q) else none) = some Z at hd
    split at hd
    next hh => exact ⟨hh.1,hh.2,(Option.some.inj hd).symm⟩
    next => cases hd
  · simp [sbipDecodeNamed,decAlignOutcome] at hd

/-- The restriction of `φ` to two subsets that it matches. -/
def sbipRestrictEquiv {Ω : Type} {s t : Set Ω} (φ : ↥s ≃ ↥t) {A B : Set Ω}
    (hA : A ⊆ s) (hB : B ⊆ t) (hmem : ∀ x : ↥s,x.val ∈ A ↔ (φ x).val ∈ B) : ↥A ≃ ↥B where
  toFun u := ⟨(φ ⟨u.val,hA u.2⟩).val,(hmem _).1 u.2⟩
  invFun w := ⟨(φ.symm ⟨w.val,hB w.2⟩).val,
    (hmem _).2 (by simpa only [Equiv.apply_symm_apply] using w.2)⟩
  left_inv u := by simp
  right_inv w := by simp

namespace SbipNodeRep
variable {m : ℕ} {I J K K' : RawSbipNode} {X Y Z Z' : Pt (BipBlockInputs (Fin m))}
    (h : SbipNodeRep m I X) (h' : SbipNodeRep m J Y)
    (hK : SbipNodeRep m K Z) (hK' : SbipNodeRep m K' Z')
    (φ : ↥X.car ≃ ↥Y.car) (hφ : φ ∈ (BipBlockInputs (Fin m)).IsoP X Y)
include h h' hK hK' hφ

/-- Sec. 9.4 (the complement extension after step 5, and a Johnson answer
kept as it is): lifting two isomorphic child answers to their parents
gives isomorphic parent answers, by the parent input map. -/
theorem lift_transport (hV : BipBlockInputs.V₁ Z = step8V₁ X)
    (hV' : BipBlockInputs.V₁ Z' = step8V₁ Y)
    (hS : Z.car ⊆ X.car) (hT : Z'.car ⊆ Y.car) (ψ : ↥Z.car ≃ ↥Z'.car)
    (hψ : ∀ x,(ψ x).val = (φ ⟨x.val,hS x.property⟩).val)
    (p p' : RawAlignOutcome) (hiso : SbipNamedOutcomeIso K K' Z Z' ψ p p') :
    SbipNamedOutcomeIso I J X Y φ (sbipNodeLift ((I.1.2.1.1.1.1,K.1.2.1.1.1.1),p))
      (sbipNodeLift ((J.1.2.1.1.1.1,K'.1.2.1.1.1.1),p')) := by
  obtain ⟨Zc,Zc',hdec,hdec',hZ,hZ',e,he,hiso⟩ := hiso
  have hVX : winSet m I.1.2.1.1.1.1 ⊆ X.car := by
    rw [h.point_set]; exact V₁_subset_car X
  have hVY : winSet m J.1.2.1.1.1.1 ⊆ Y.car := by
    rw [h'.point_set]; exact V₁_subset_car Y
  have hWV : winSet m K.1.2.1.1.1.1 ⊆ winSet m I.1.2.1.1.1.1 := by
    rw [hK.point_set,hV,h.point_set]; exact step8V₁_subset X
  have hWV' : winSet m K'.1.2.1.1.1.1 ⊆ winSet m J.1.2.1.1.1.1 := by
    rw [hK'.point_set,hV',h'.point_set]; exact step8V₁_subset Y
  rcases sbipDecodeNamed_cases hdec with ⟨q,rfl,hn,hb,rfl⟩ | ⟨j,rfl,hw,rfl⟩ <;>
    rcases sbipDecodeNamed_cases hdec' with ⟨q',rfl,hn',hb',rfl⟩ | ⟨j',rfl,hw',rfl⟩
  · -- two partitions: the complement extension at both parents
    have hmem (x : ↥X.car) : x.val ∈ winSet m I.1.2.1.1.1.1 ↔
        (φ x).val ∈ winSet m J.1.2.1.1.1.1 := by
      rw [h.point_set,h'.point_set]
      constructor
      · rintro ⟨u,hu,hux⟩
        have hx : u = x := Subtype.ext hux
        subst hx
        exact ⟨φ u,(hφ.2.part₁ u).2 hu,rfl⟩
      · rintro ⟨u,hu,hux⟩
        have hx : u = φ x := Subtype.ext hux
        subst hx
        exact ⟨x,(hφ.2.part₁ x).1 hu,rfl⟩
    let f := sbipRestrictEquiv φ hVX hVY hmem
    refine ⟨_,_,sbipDecodeNamed_partition _ h.left_nodup h.point_lt _,
      sbipDecodeNamed_partition _ h'.left_nodup h'.point_lt _,hVX,hVY,f,fun _ => rfl,?_⟩
    change f ∈ (ColoredPartitions (Fin m) ℕ).Iso _ _
    rw [sbipNamedPartition_extend _ _ h.left_nodup h.point_lt hn hb,
      sbipNamedPartition_extend _ _ h'.left_nodup h'.point_lt hn' hb']
    apply extendPartition.mem_iso hWV hWV' f e
    · intro x
      exact (he x).trans (hψ _)
    · exact hiso
  · exact hiso.elim
  · exact hiso.elim
  · -- two Johnson schemes: the lift keeps them, with their carriers
    exact ⟨_,_,hdec,hdec',hZ.trans hS,hZ'.trans hT,e,fun x => (he x).trans (hψ _),hiso⟩

end SbipNodeRep
end Algo
