import Workspace.Algo.SplitBipCaseOutcomePartition
import Workspace.Algo.SplitImprimitiveCase
import Workspace.Algo.SplitUpccCaseOutcome
import Workspace.Algo.SplitDesignCase12Spec

/-! Exact local partition decoders for the three case procedures. These
lemmas read the actual returned arrays, including the UPCC name gather.
-/
namespace Algo
open Babai RAM
open scoped Classical

section Local
variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {s : Set Ω} {W : Set ↥s}
    {n : ℕ} (e : ↥W ≃ Fin n) (q : RawColPart)
    (P : ColoredPartition ↥(Subtype.val '' W) ℕ)
    (hc : ∀ x : ↥W,labAt q.1 (e x) = P.color (mkPt x.property))
    (hp : ∀ x y : ↥W,LabRel q.2 (e x) (e y) ↔
      P.part (mkPt x.property) (mkPt y.property))
include hc hp

theorem sbipCaseLocalPartition_cell (x y : ↥W) :
    cellOf q (e x) = cellOf q (e y) ↔ P.part (mkPt x.property) (mkPt y.property) := by
  change (labAt q.1 (e x),labAt q.2 (e x)) = (labAt q.1 (e y),labAt q.2 (e y)) ↔ _
  rw [Prod.mk.injEq]
  exact ⟨fun h => (hp x y).1 h.2,fun h => ⟨by rw [hc,hc]; exact P.part_le_color h,
    (hp x y).2 h⟩⟩

theorem sbipCaseLocalPartition_decode :
    (decColPartition n q).pushforward ((splitPointImageEquiv W).trans e).symm = P := by
  apply ColoredPartition.ext
  · funext x
    exact hc ((splitPointImageEquiv W) x)
  · apply Setoid.ext
    intro x y
    exact sbipCaseLocalPartition_cell e q P hc hp
      ((splitPointImageEquiv W) x) ((splitPointImageEquiv W) y)

theorem sbipCaseLocalPartition_valid {α : ℝ}
    (hv : @ColoredPartition.IsAlphaPartition _ _ P (Fintype.ofFinite _) α) :
    (decColPartition n q).IsAlphaPartition α := by
  letI : Fintype ↥(Subtype.val '' W) := Fintype.ofFinite _
  apply ColoredPartition.isAlphaPartition_of_kernel_rel P _
    ((splitPointImageEquiv W).trans e) ?_ ?_ hv
  · intro x y
    change P.color x = P.color y ↔ labAt q.1 (e (splitPointImageEquiv W x)) =
      labAt q.1 (e (splitPointImageEquiv W y))
    rw [hc,hc]
    rfl
  · intro x y
    exact (sbipCaseLocalPartition_cell e q P hc hp
      (splitPointImageEquiv W x) (splitPointImageEquiv W y)).symm
end Local

section Imp
variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {s : Set Ω}
    {X : BlkImprimitiveObj s} {name₁ : ↥X.Pt₁ → ℕ} {name₂ : ↥X.blocks → ℕ}
    {r : RawUpccCase} (h : ImpNames X name₁ name₂ r)
    (hleft : r.2.1.Nodup) (hright : r.2.2.Nodup)
    (e₁ : ↥X.Pt₁ ≃ Fin r.2.1.length) (he₁ : ∀ x,r.2.1[(e₁ x).val] = name₁ x)
    (e₂ : ↥X.blocks ≃ Fin r.2.2.length) (he₂ : ∀ B,r.2.2[(e₂ B).val] = name₂ B)
include h hleft hright he₁ he₂

theorem sbipCaseImp_local (lab : RawLab) (hq : (lab,none) ∈ impCase r) :
    ∃ P : ColoredPartition ↥(Subtype.val '' X.Pt₁) ℕ,
      (decColPartition r.2.1.length (lab,lab)).pushforward
        ((splitPointImageEquiv X.Pt₁).trans e₁).symm = P ∧
      @ColoredPartition.IsAlphaPartition _ _ P (Fintype.ofFinite _) (1/2) ∧
      (decColPartition r.2.1.length (lab,lab)).IsAlphaPartition (1/2) := by
  obtain ⟨Z,hrep,hgood⟩ := impCase_spec h hleft hright e₁ he₁ e₂ he₂ (lab,none) hq
  rcases hrep with ⟨_,P,rfl,hc,hp⟩
  exact ⟨P,sbipCaseLocalPartition_decode e₁ (lab,lab) P hc hp,hgood.2,
    sbipCaseLocalPartition_valid e₁ (lab,lab) P hc hp hgood.2⟩
end Imp

section Upcc
variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    (X : Pt (BlkUPCCCases Ω)) {n : ℕ} (e : ↥X.obj.vtxSet ≃ Fin n)
    {r : RawUpccCase} (hw : r.WF) (hn : UpccCaseNames X.obj e r)
include hw hn

theorem sbipCaseUpcc_local (B : ↥X.obj.blocks)
    (hq : (UpccCase.versionF (r,upccCaseName₂ X.obj e B)).2.2 = none)
    (e₁ : ↥X.obj.Pt₁ ≃ Fin r.2.1.length)
    (he₁ : ∀ x,r.2.1[(e₁ x).val] = upccCaseName₁ X.obj e x) :
    let q := sbipCaseGather (r.2.1,(UpccCase.versionF (r,upccCaseName₂ X.obj e B)).2.1)
    ∃ P : ColoredPartition ↥(Subtype.val '' X.obj.Pt₁) ℕ,
      (decColPartition r.2.1.length q).pushforward
        ((splitPointImageEquiv X.obj.Pt₁).trans e₁).symm = P ∧
      @ColoredPartition.IsAlphaPartition _ _ P (Fintype.ofFinite _) (1/2) ∧
      (decColPartition r.2.1.length q).IsAlphaPartition (1/2) := by
  obtain ⟨Z,hrep,hgood⟩ := UpccCase.versionF_spec X e hw hn B
  rcases hrep with ⟨_,_,_,hrep⟩
  rw [hq] at hrep
  obtain ⟨P,rfl,hc,hp⟩ := hrep
  let q := sbipCaseGather (r.2.1,(UpccCase.versionF (r,upccCaseName₂ X.obj e B)).2.1)
  have hcol (x : ↥X.obj.Pt₁) : labAt q.1 (e₁ x) = P.color (mkPt x.property) := by
    rw [(sbipCaseGather_get _ _ (e₁ x)).1,he₁]
    exact hc x
  have hpart (x y : ↥X.obj.Pt₁) : LabRel q.2 (e₁ x) (e₁ y) ↔
      P.part (mkPt x.property) (mkPt y.property) := by
    change labAt q.2 (e₁ x) = labAt q.2 (e₁ y) ↔ _
    rw [(sbipCaseGather_get _ _ (e₁ x)).2,(sbipCaseGather_get _ _ (e₁ y)).2,he₁,he₁]
    exact hp x y
  exact ⟨P,sbipCaseLocalPartition_decode e₁ q P hcol hpart,hgood.2,
    sbipCaseLocalPartition_valid e₁ q P hcol hpart hgood.2⟩
end Upcc

end Algo
