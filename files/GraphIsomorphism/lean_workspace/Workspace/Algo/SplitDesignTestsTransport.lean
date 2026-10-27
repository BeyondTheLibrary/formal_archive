import Workspace.Algo.SplitDesignCase12Spec
import Workspace.SplitOrJohnson.BlockDesignHyper

/-! The executable DesignCase tests depend on the colored structure and
its threshold. Independent orders of the two stored vertex lists give
the same decisions under the supplied isomorphism.
-/
namespace Algo
open Babai RAM
open scoped Classical
section
variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {s t : Set Ω}
    {X : BlkDesignObj s} {Y : BlkDesignObj t} {φ : ↥s ≃ ↥t}
    (hφ : X.IsMorphOn Y φ)
    {n₁ : ↥X.Pt₁ → ℕ} {n₂ : ↥X.blocks → ℕ}
    {n₁' : ↥Y.Pt₁ → ℕ} {n₂' : ↥Y.blocks → ℕ} {r r' : RawUpccCase}
    (h : DesignNames X n₁ n₂ r) (h' : DesignNames Y n₁' n₂' r')
    (e₁ : ↥X.Pt₁ ≃ Fin r.2.1.length) (he₁ : ∀ x,r.2.1[(e₁ x).val] = n₁ x)
    (e₂ : ↥X.blocks ≃ Fin r.2.2.length) (he₂ : ∀ B,r.2.2[(e₂ B).val] = n₂ B)
    (e₁' : ↥Y.Pt₁ ≃ Fin r'.2.1.length) (he₁' : ∀ x,r'.2.1[(e₁' x).val] = n₁' x)
    (e₂' : ↥Y.blocks ≃ Fin r'.2.2.length) (he₂' : ∀ B,r'.2.2[(e₂' B).val] = n₂' B)
include hφ h h' he₁ he₂ he₁' he₂'

/-- Sec. 9.7, Case 1 test is invariant under isomorphism of the design object. -/
theorem designCase1_transport : designCase1 r = designCase1 r' := by
  apply Bool.eq_iff_iff.mpr
  rw [designCase1_spec h e₁ he₁ e₂ he₂,designCase1_spec h' e₁' he₁' e₂' he₂']
  exact hφ.isCase1_iff.symm

/-- Sec. 9.7, Case 2 test is invariant under isomorphism of the design object. -/
theorem designCase2_transport : designCase2 r = designCase2 r' := by
  apply Bool.eq_iff_iff.mpr
  rw [designCase2_spec h e₁ he₁ e₂ he₂,designCase2_spec h' e₁' he₁' e₂' he₂']
  exact hφ.isCase2_iff.symm

/-- Sec. 9.7, tie test is invariant under isomorphism of the design object. -/
theorem designTie_transport : designTie r = designTie r' := by
  apply Bool.eq_iff_iff.mpr
  rw [designTie_spec h e₁ he₁ e₂ he₂,designTie_spec h' e₁' he₁' e₂' he₂']
  exact hφ.bigTwin_eq_blocks_iff.symm

/-- Sec. 9.7 (Reduce-Part2-by-Color): the absolute-defect test on the large twin class is
invariant under isomorphism. -/
theorem designSelectC_transport : designSelectC r = designSelectC r' := by
  letI : Fintype ↥s := Fintype.ofFinite _
  letI : Fintype ↥t := Fintype.ofFinite _
  letI : DecidableEq ↥s := Classical.decEq _
  letI : DecidableEq ↥t := Classical.decEq _
  apply Bool.eq_iff_iff.mpr
  rw [designSelectC_spec h e₁ he₁ e₂ he₂,designSelectC_spec h' e₁' he₁' e₂' he₂']
  exact hφ.selP_iff.symm

variable (p p' : ℕ × ℕ) (hb : 0 < p.2) (hb' : 0 < p'.2)
    (ha : sbipAlphaValue p = sbipAlphaValue p')
include hb hb' ha

/-- Sec. 9.7, Case 2 small-class test is invariant under isomorphism. -/
theorem designSmall_transport : designSmall (r,p) = designSmall (r',p') := by
  apply Bool.eq_iff_iff.mpr
  rw [designSmall_spec h e₁ he₁ e₂ he₂ p hb,
    designSmall_spec h' e₁' he₁' e₂' he₂' p' hb']
  constructor
  · intro hh y
    let x : ↥X.Pt₁ := ⟨φ.symm y.val,(hφ.part₁ (φ.symm y.val)).1 (by simpa only [Equiv.apply_symm_apply] using y.property)⟩
    have hc := hφ.ncard_localSizeClass x.val
    simp only [x,Equiv.apply_symm_apply] at hc
    change (Y.localSizeClass y.val).ncard = (X.localSizeClass x.val).ncard at hc
    rw [hc,← ha,hφ.n₁_eq]
    exact hh x
  · intro hh x
    let y : ↥Y.Pt₁ := ⟨φ x.val,(hφ.part₁ x.val).2 x.property⟩
    have hy := hh y
    have hc := hφ.ncard_localSizeClass x.val
    change (Y.localSizeClass y.val).ncard = (X.localSizeClass x.val).ncard at hc
    rw [hc,← ha,hφ.n₁_eq] at hy
    exact hy

/-- Sec. 9.7, Case 2 dominant-twin test is invariant under isomorphism. -/
theorem designHasDomTwins_transport : designHasDomTwins (r,p) = designHasDomTwins (r',p') := by
  apply Bool.eq_iff_iff.mpr
  rw [designHasDomTwins_spec h e₁ he₁ e₂ he₂ p hb,
    designHasDomTwins_spec h' e₁' he₁' e₂' he₂' p' hb',← ha]
  constructor
  · rintro ⟨u,hu,v,hv,huv,htr⟩
    refine ⟨φ u,(hφ.mem_domClass_iff _ u).2 hu,φ v,(hφ.mem_domClass_iff _ v).2 hv,
      fun hh => huv (φ.injective hh),?_⟩
    rw [hφ.trace_eq u,hφ.trace_eq v,htr]
  · rintro ⟨u,hu,v,hv,huv,htr⟩
    refine ⟨φ.symm u,(hφ.symm.mem_domClass_iff _ u).2 hu,
      φ.symm v,(hφ.symm.mem_domClass_iff _ v).2 hv,
      fun hh => huv (φ.symm.injective hh),?_⟩
    rw [hφ.symm.trace_eq u,hφ.symm.trace_eq v,htr]

/-- Sec. 9.7, Case 2 complementary-pair boundary test is invariant under isomorphism. -/
theorem designDomBoundary_transport : designDomBoundary (r,p) = designDomBoundary (r',p') := by
  apply Bool.eq_iff_iff.mpr
  rw [designDomBoundary_spec h e₁ he₁ e₂ he₂ p hb,
    designDomBoundary_spec h' e₁' he₁' e₂' he₂' p' hb',← ha]
  constructor
  · rintro ⟨x,hx,hc⟩
    refine ⟨φ x,(hφ.mem_domClass_iff _ x).2 hx,?_⟩
    rw [hφ.ncard_bigTwin_eq,hφ.localSize_eq]
    exact hc
  · rintro ⟨y,hy,hc⟩
    refine ⟨φ.symm y,(hφ.symm.mem_domClass_iff _ y).2 hy,?_⟩
    rw [hφ.symm.ncard_bigTwin_eq,hφ.symm.localSize_eq]
    exact hc

end
end Algo
