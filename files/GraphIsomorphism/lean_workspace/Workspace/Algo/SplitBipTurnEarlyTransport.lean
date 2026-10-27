import Workspace.Algo.SplitBipTurnExtensionTransport

/-! The early families transport across arbitrary independent stored
orders. Every source numbering has its transported target numbering,
and the decoders identify the same paper partition along the induced map.
-/
namespace Algo
open Babai RAM
open scoped Classical

section Early1
variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    (X Y : Pt (BipBlockInputs Ω)) (z z' : RawSbipGraph × (ℕ × ℕ))
    (e : ↥X.obj.1.1.V₁ ≃ Fin z.1.1.1.length)
    (e' : ↥Y.obj.1.1.V₁ ≃ Fin z'.1.1.1.length)
    (ha : sbipAlphaValue z.2 = BipBlockInputs.alpha X)
    (ha' : sbipAlphaValue z'.2 = BipBlockInputs.alpha Y)
    (φ : ↥X.car ≃ ↥Y.car) (hφ : X.obj.1.1.IsIsoTo Y.obj.1.1 φ)
    (hα : BipBlockInputs.alpha X = BipBlockInputs.alpha Y)
include ha ha' hφ hα

/-- Every actual Step 1 output has its transported output, without any
assumption that the two raw first lists have matching orders. -/
theorem sbipGraphEarly1_transport {c : ℕ} (hsmall : z.1.1.1.length ≤ c)
    (q : RawColPart) (hq : q ∈ sbipGraphEarly1 c z) :
    ∃ q' ∈ sbipGraphEarly1 c z',
      subEquiv φ (fun x => hφ.part₁ x) ∈ (ColoredPartitions Ω ℕ).Iso
        (sbipGraphDecodePartition X.obj.1.1 e q)
        (sbipGraphDecodePartition Y.obj.1.1 e' q') := by
  have hn := VColBipBlk.V₁_ncard_eq_of_isIsoTo hφ
  have hl := sbipGraphEarly_first_size X z.1 e
  have hl' := sbipGraphEarly_first_size Y z'.1 e'
  have hsmall' : z'.1.1.1.length ≤ c := by
    change z.1.1.1.length = X.obj.1.1.V₁.ncard at hl
    change z'.1.1.1.length = Y.obj.1.1.V₁.ncard at hl'
    omega
  obtain ⟨σ,hσ,hqσ⟩ := sbipGraphEarly1_paper X z e ha hsmall q hq
  obtain ⟨q',hq',he'⟩ := sbipGraphEarly1_covers Y z' e' ha' hsmall'
    (fun y => σ (φ.symm y)) (isPart₁Numbering_map hφ hσ)
  refine ⟨q',hq',?_⟩
  rw [hqσ,he']
  apply kerPartition_mem_iso φ (fun x => hφ.part₁ x)
  intro x
  rw [← hn,← hα]
  simp only [indivColor,Equiv.symm_apply_apply]

end Early1
section Early2
variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    (X Y : Pt (BipBlockInputs Ω)) (r r' : RawSbipGraph)
    (name : X.obj.1.1.Vtx → ℕ) (name' : Y.obj.1.1.Vtx → ℕ)
    (h : SbipGraphColorNames X.obj.1.1 r name)
    (h' : SbipGraphColorNames Y.obj.1.1 r' name')
    (hl : r.1.1.Nodup) (hr : r.1.2.1.Nodup)
    (hl' : r'.1.1.Nodup) (hr' : r'.1.2.1.Nodup)
    (e₁ : ↥X.obj.1.1.V₁ ≃ Fin r.1.1.length)
    (e₂ : ↥X.obj.1.1.blocks ≃ Fin r.1.2.1.length)
    (e₁' : ↥Y.obj.1.1.V₁ ≃ Fin r'.1.1.length)
    (e₂' : ↥Y.obj.1.1.blocks ≃ Fin r'.1.2.1.length)
    (he₁ : ∀ x,r.1.1[(e₁ x).val] = sbipGraphPointName X name x)
    (he₂ : ∀ B,r.1.2.1[(e₂ B).val] = sbipGraphBlockName X name B)
    (he₁' : ∀ x,r'.1.1[(e₁' x).val] = sbipGraphPointName Y name' x)
    (he₂' : ∀ B,r'.1.2.1[(e₂' B).val] = sbipGraphBlockName Y name' B)
    (φ : ↥X.car ≃ ↥Y.car) (hφ : X.obj.1.1.IsIsoTo Y.obj.1.1 φ)
include h h' hl hr hl' hr' he₁ he₂ he₁' he₂' hφ

/-- The entire block-numbering family has the same covariance, including
independent orders of the point and block lists in the two inputs. -/
theorem sbipGraphEarly2_transport {c : ℕ}
    (hsmall : r.1.2.1.length ≤ c * Nat.log 2 r.1.1.length)
    (q : RawColPart) (hq : q ∈ sbipGraphEarly2 (c+1) r) :
    ∃ q' ∈ sbipGraphEarly2 (c+1) r',
      subEquiv φ (fun x => hφ.part₁ x) ∈ (ColoredPartitions Ω ℕ).Iso
        (sbipGraphDecodePartition X.obj.1.1 e₁ q)
        (sbipGraphDecodePartition Y.obj.1.1 e₁' q') := by
  have hn := VColBipBlk.V₁_ncard_eq_of_isIsoTo hφ
  have hm := VColBipBlk.numBlocks_eq_of_isIsoTo hφ
  have hlen : r'.1.1.length = r.1.1.length := by
    rw [sbipGraphEarly_first_size Y r' e₁',sbipGraphEarly_first_size X r e₁]
    exact hn.symm
  have hnum : r'.1.2.1.length = r.1.2.1.length := by
    rw [sbipGraphEarly_block_size Y r' e₂',sbipGraphEarly_block_size X r e₂]
    exact hm.symm
  have hsmall' : r'.1.2.1.length ≤ c * Nat.log 2 r'.1.1.length := by
    rwa [hlen,hnum]
  obtain ⟨σ,hσ,hqσ⟩ := sbipGraphEarly2_paper X r name h hl hr e₁ e₂ he₁ he₂ hsmall q hq
  obtain ⟨q',hq',he'⟩ := sbipGraphEarly2_covers Y r' name' h' hl' hr' e₁' e₂' he₁' he₂' hsmall'
    (fun C => σ (φ.symm '' C)) (isBlockNumbering_map hφ hσ)
  refine ⟨q',hq',?_⟩
  rw [hqσ,he']
  exact kerPartition_mem_iso φ (fun x => hφ.part₁ x) (blkColor_map hφ σ)

end Early2

end Algo
