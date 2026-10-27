import Workspace.Algo.SplitDesignCase12
import Workspace.Algo.SplitPartitionTransport

/-! The first two branch tests supply the hypotheses of their local exits.
Their stored partitions carry the same color classes and blocks as the paper. -/
namespace Algo
open Babai RAM

def splitPointImageEquiv {Ω : Type} [Fintype Ω] [DecidableEq Ω] {s : Set Ω} (W : Set ↥s) :
    ↥(Subtype.val '' W) ≃ ↥W where
  toFun x := ⟨liftPt (W := W) x,liftPt_mem x⟩
  invFun x := mkPt (W := W) (x := x.val) x.property
  left_inv _ := Subtype.ext rfl
  right_inv x := Subtype.ext (liftPt_mkPt x.property)

section
variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {s : Set Ω}
    {X : BlkDesignObj s} {name₁ : ↥X.Pt₁ → ℕ} {name₂ : ↥X.blocks → ℕ}
    {r : RawUpccCase} (h : DesignNames X name₁ name₂ r)
    (e₁ : ↥X.Pt₁ ≃ Fin r.2.1.length) (he₁ : ∀ x, r.2.1[(e₁ x).val] = name₁ x)
    (e₂ : ↥X.blocks ≃ Fin r.2.2.length) (he₂ : ∀ B, r.2.2[(e₂ B).val] = name₂ B)
include h he₁ he₂

theorem designDomHyp_of_tests (p : ℕ × ℕ) (hb : 0 < p.2)
    (ha : 2 / 3 ≤ sbipAlphaValue p) (ha1 : sbipAlphaValue p < 1)
    (hn : (X.n₂ : ℝ) < sbipAlphaValue p * X.n₁)
    (h2 : designCase2 r = true) (ht : designTie r ≠ true)
    (hs : designSmall (r,p) ≠ true) : X.DomHyp (sbipAlphaValue p) := by
  refine ⟨ha,ha1,hn,(designCase2_spec h e₁ he₁ e₂ he₂).1 h2,
    fun hh => ht ((designTie_spec h e₁ he₁ e₂ he₂).2 hh),?_⟩
  have hh : ¬ ∀ x : ↥X.Pt₁,
      ((X.localSizeClass x.val).ncard : ℝ) < sbipAlphaValue p * X.n₁ :=
    fun hh => hs ((designSmall_spec h e₁ he₁ e₂ he₂ p hb).2 hh)
  push Not at hh
  obtain ⟨x,hx⟩ := hh
  exact ⟨x.val,x.property,hx⟩

theorem designBigNames_mem (B : ↥X.blocks) :
    name₂ B ∈ designBigNames r ↔ B.val ∈ X.bigTwin := by
  simp only [designBigNames,List.mem_map]
  constructor
  · rintro ⟨i,hi,he⟩
    have hil := List.mem_range.1 (List.mem_of_mem_filter hi)
    let C := e₂.symm ⟨i,hil⟩
    have hc : name₂ C = name₂ B := by
      rw [← he₂ C]
      simpa only [C,Equiv.apply_symm_apply,labAt,List.getD_eq_getElem _ _ hil] using he
    have hC := (designBigPositions_spec h e₁ he₁ e₂ he₂ C).1 (by
      simpa only [C,Equiv.apply_symm_apply] using hi)
    rwa [h.inj₂ hc] at hC
  · intro hB
    refine ⟨(e₂ B).val,(designBigPositions_spec h e₁ he₁ e₂ he₂ B).2 hB,?_⟩
    simp [labAt,(e₂ B).isLt,he₂]

theorem designOtherNames_mem (B : ↥X.blocks) :
    name₂ B ∈ designOtherNames r ↔ B.val ∈ X.blocks \ X.bigTwin := by
  simp only [designOtherNames,List.mem_filter,Bool.not_eq_true',decide_eq_false_iff_not,
    designBigNames_mem h e₁ he₁ e₂ he₂,Set.mem_diff]
  exact and_congr (iff_of_true ((h.right _).2 ⟨B,rfl⟩) B.property) Iff.rfl

omit h he₁ he₂ in
theorem designOtherNames_sub {a : ℕ} (ha : a ∈ designOtherNames r) : a ∈ r.2.2 :=
  List.mem_of_mem_filter ha

omit h he₁ he₂ in
theorem designOtherNames_nodup (hw : r.WF) : (designOtherNames r).Nodup :=
  hw.right_nodup.filter _

omit h he₁ he₂ in
theorem designPartition_transfer (P : ColoredPartition ↥(Subtype.val '' X.Pt₁) ℕ)
    (q : RawColPart) (α : ℝ)
    (hc : ∀ x : ↥X.Pt₁, P.color (mkPt x.property) = labAt q.1 (e₁ x))
    (hp : ∀ x y : ↥X.Pt₁, P.part (mkPt x.property) (mkPt y.property) ↔
      (decColPartition r.2.1.length q).part (e₁ x) (e₁ y))
    (iF : Fintype ↥(Subtype.val '' X.Pt₁))
    (hv : @ColoredPartition.IsAlphaPartition _ _ P iF α) :
    (decColPartition r.2.1.length q).IsAlphaPartition α := by
  letI := iF
  apply ColoredPartition.isAlphaPartition_of_kernel_rel P _
    ((splitPointImageEquiv X.Pt₁).trans e₁) ?_ ?_ hv
  · intro a b
    obtain ⟨x,rfl⟩ := (splitPointImageEquiv X.Pt₁).symm.surjective a
    obtain ⟨y,rfl⟩ := (splitPointImageEquiv X.Pt₁).symm.surjective b
    simp only [Equiv.trans_apply,Equiv.apply_symm_apply]
    change P.color (mkPt x.property) = P.color (mkPt y.property) ↔
      labAt q.1 (e₁ x) = labAt q.1 (e₁ y)
    rw [hc,hc]
  · intro a b
    obtain ⟨x,rfl⟩ := (splitPointImageEquiv X.Pt₁).symm.surjective a
    obtain ⟨y,rfl⟩ := (splitPointImageEquiv X.Pt₁).symm.surjective b
    simp only [Equiv.trans_apply,Equiv.apply_symm_apply]
    exact hp x y

theorem designSmallPartition_valid (p : ℕ × ℕ) (hb : 0 < p.2)
    (hs : designSmall (r,p) = true) :
    (decColPartition r.2.1.length (designSmallPartition r)).IsAlphaPartition (sbipAlphaValue p) := by
  classical
  have spec := designSmallPartition_spec h e₁ he₁ e₂ he₂
  apply designPartition_transfer e₁ (kerPartition X.Pt₁ X.localSize) _ _
    (fun x => (spec.2.1 x).symm) (fun x y => (spec.2.2 x y).symm) (Fintype.ofFinite _)
  exact designSmallPartition_good h e₁ he₁ e₂ he₂ p hb hs _

theorem designDomPartition_valid (p : ℕ × ℕ) (hb : 0 < p.2)
    (hd : X.DomHyp (sbipAlphaValue p)) (ht : designHasDomTwins (r,p) = true) :
    (decColPartition r.2.1.length (designDomPartition (r,p))).IsAlphaPartition (sbipAlphaValue p) := by
  classical
  have spec := designDomPartition_spec h e₁ he₁ e₂ he₂ p hb
  apply designPartition_transfer e₁
    (labPartition X.Pt₁ X.localSize (X.domLab (sbipAlphaValue p))) _ _
    (fun x => (spec.2.1 x).symm) (fun x y => (spec.2.2 x y).symm) (Fintype.ofFinite _)
  exact designDomPartition_good h e₁ he₁ e₂ he₂ p hb hd ht _

theorem designPairPartition_valid (p : ℕ × ℕ) (hb : 0 < p.2)
    (hd : X.DomHyp (sbipAlphaValue p)) (ht : designHasDomTwins (r,p) ≠ true)
    (hbnd : designDomBoundary (r,p) = true) :
    (decColPartition r.2.1.length (designPairPartition (r,p))).IsAlphaPartition (sbipAlphaValue p) := by
  classical
  have spec := designPairPartition_spec h e₁ he₁ e₂ he₂ p hb
  apply designPartition_transfer e₁
    (labPartition X.Pt₁ X.localSize (X.domPairLab (sbipAlphaValue p))) _ _
    (fun x => (spec.2.1 x).symm) (fun x y => (spec.2.2 x y).symm) (Fintype.ofFinite _)
  exact designPairPartition_good h e₁ he₁ e₂ he₂ p hb hd ht hbnd _

end
end Algo
