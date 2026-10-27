import Workspace.Algo.SplitBipGraphEarlyDecode

/-! The actual Step 4 exit has the paper's parent-domain partition. Its
alpha bound follows from the computed no-dominant-class test, through the
already proved exact refinement colors.
-/
namespace Algo
open Babai RAM
open scoped Classical

section
variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    (X : Pt (BipBlockInputs Ω)) (z : RawSbipGraph × (ℕ × ℕ))
    (name : X.obj.1.1.Vtx → ℕ)
    (h : SbipGraphColorNames X.obj.1.1 z.1 name)
    (hnd : (sbipGraphVertices z.1).Nodup)
    (e : X.obj.1.1.Vtx ≃ Fin (sbipGraphVertices z.1).length)
    (he : ∀ A,(sbipGraphVertices z.1)[(e A).val]'(e A).isLt = name A)
    (hp : sbipGraphPointName X name '' Set.univ = {a | a ∈ z.1.1.1})
    (ha : sbipAlphaValue z.2 = BipBlockInputs.alpha X)
    (hb : 0 < z.2.2) (hl : z.1.1.1.Nodup)
include h hnd he hp ha hl

theorem sbipGraphEarly4_decode :
    ∃ e₁ : ↥X.obj.1.1.V₁ ≃ Fin z.1.1.1.length,
      (∀ x,z.1.1.1[(e₁ x).val] = sbipGraphPointName X name x) ∧
      sbipGraphDecodePartition X.obj.1.1 e₁ (sbipGraphEarly4 z) =
        kerPartition X.obj.1.1.V₁ (VColBipBlk.wlDiag X.obj.1.1) := by
  have hc := sbipGraphClasses_names X z name h hnd e he hp ha
  obtain ⟨e₁,he₁⟩ := splitNameEquiv_exists _ hc.injective z.1.1.1 hl (fun a => by
    rw [← show a ∈ sbipGraphPointName X name '' Set.univ ↔ a ∈ z.1.1.1 from by rw [hp]; rfl]
    simp)
  have hs (x y : ↥X.obj.1.1.V₁) := sbipStep4_spec hc x y (e₁ x) (e₁ y) (he₁ x) (he₁ y)
  exact ⟨e₁,he₁,sbipGraphDecodePartition_eq X.obj.1.1 e₁ _ _
    (fun x => (hs x x).1) (sbipGraphCell_spec X.obj.1.1 e₁ _ _
      (fun x => (hs x x).1) (fun x y => (hs x y).2))⟩

include hb in
theorem sbipGraphEarly4_valid (hexit : (sbipGraphSteps35 z).2 = none) :
    (decColPartition z.1.1.1.length (sbipGraphEarly4 z)).IsAlphaPartition
      (BipBlockInputs.alpha X) := by
  have hc := sbipGraphClasses_names X z name h hnd e he hp ha
  obtain ⟨e₁,he₁,_⟩ := sbipGraphEarly4_decode X z name h hnd e he hp ha hl
  have hs (x y : ↥X.obj.1.1.V₁) := sbipStep4_spec hc x y (e₁ x) (e₁ y) (he₁ x) (he₁ y)
  have hv := (sbipStep4_good X ((sbipGraphSteps35_exit_iff X z name h hnd e he hp ha hb hl).1 hexit)).2
  exact sbipGraphDecodedPartition_valid X.obj.1.1 e₁ _ _ (fun x => (hs x x).1)
    (sbipGraphCell_spec X.obj.1.1 e₁ _ _ (fun x => (hs x x).1) (fun x y => (hs x y).2)) (Fintype.ofFinite _) hv

end
end Algo
