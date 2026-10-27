import Workspace.Algo.SplitBipGraphEarlyNames

/-! Step 2 colors each point by its old color and its neighborhood in the
chosen block numbering. The common graph supplies both inputs exactly.
-/
namespace Algo
open Babai RAM
open scoped Classical

section
variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    (X : Pt (BipBlockInputs Ω)) (r : RawSbipGraph)
    (name : X.obj.1.1.Vtx → ℕ) (h : SbipGraphColorNames X.obj.1.1 r name)
    (hl : r.1.1.Nodup) (hr : r.1.2.1.Nodup)
    (e₁ : ↥X.obj.1.1.V₁ ≃ Fin r.1.1.length)
    (e₂ : ↥X.obj.1.1.blocks ≃ Fin r.1.2.1.length)
    (he₁ : ∀ x,r.1.1[(e₁ x).val] = sbipGraphPointName X name x)
    (he₂ : ∀ B,r.1.2.1[(e₂ B).val] = sbipGraphBlockName X name B)
include h hl hr he₁ he₂

theorem sbipGraphEarly2_row (row : RawPerm) (hw : RawPerm.WF r.1.2.1.length row) :
    let P := kerPartition X.obj.1.1.V₁ (blkColor X.obj.1.1
      (sbipBlockNumbering X.obj.1.1 (r := (sbipGraphEarly2Input r,row)) e₂))
    sbipGraphDecodePartition X.obj.1.1 e₁ (sbipStep2 (sbipGraphEarly2Input r,row)) = P ∧
      (decColPartition r.1.1.length (sbipStep2 (sbipGraphEarly2Input r,row))).IsAlphaPartition
        (BipBlockInputs.alpha X) := by
  have hs (x y : ↥X.obj.1.1.V₁) :=
    sbipStep2_spec X.obj.1.1 (r := (sbipGraphEarly2Input r,row)) e₁ e₂ hw
      (sbipGraphEarly2_edge X r name h e₁ e₂ he₁ he₂ hl hr)
      (sbipGraphEarly2_color X r name h e₁ he₁) x y
  have hc := fun x => (hs x x).1
  have hp := sbipGraphCell_spec X.obj.1.1 e₁ _ _ hc (fun x y => (hs x y).2)
  exact ⟨sbipGraphDecodePartition_eq X.obj.1.1 e₁ _ _ hc hp,
    sbipGraphDecodedPartition_valid X.obj.1.1 e₁ _ _ hc hp (Fintype.ofFinite _)
      (sbipStep2_good X (r := (sbipGraphEarly2Input r,row)) e₂).2⟩

theorem sbipGraphEarly2_valid {c : ℕ} (hsmall : r.1.2.1.length ≤ c * Nat.log 2 r.1.1.length)
    (q : RawColPart) (hq : q ∈ sbipGraphEarly2 (c+1) r) :
    (decColPartition r.1.1.length q).IsAlphaPartition (BipBlockInputs.alpha X) := by
  obtain ⟨row,hm,rfl⟩ := List.mem_map.1 hq
  exact (sbipGraphEarly2_row X r name h hl hr e₁ e₂ he₁ he₂ row
    ((mem_sbipNumberings (sbip_log_guard hsmall)).1 hm)).2

theorem sbipGraphEarly2_covers {c : ℕ} (hsmall : r.1.2.1.length ≤ c * Nat.log 2 r.1.1.length)
    (σ : Set ↥X.car → ℕ) (hσ : IsBlockNumbering X.obj.1.1 σ) :
    ∃ q ∈ sbipGraphEarly2 (c+1) r,
      sbipGraphDecodePartition X.obj.1.1 e₁ q = kerPartition X.obj.1.1.V₁ (blkColor X.obj.1.1 σ) := by
  obtain ⟨row,hm,he⟩ := sbipBlockNumbering_complete X.obj.1.1
    (r := (sbipGraphEarly2Input r,[])) e₂ (sbip_log_guard hsmall) σ hσ
  refine ⟨_,List.mem_map.2 ⟨row,hm,rfl⟩,?_⟩
  have hs := (sbipGraphEarly2_row X r name h hl hr e₁ e₂ he₁ he₂ row
    ((mem_sbipNumberings (sbip_log_guard hsmall)).1 hm)).1
  simpa only [he] using hs

theorem sbipGraphEarly2_paper {c : ℕ} (hsmall : r.1.2.1.length ≤ c * Nat.log 2 r.1.1.length)
    (q : RawColPart) (hq : q ∈ sbipGraphEarly2 (c+1) r) :
    ∃ σ : Set ↥X.car → ℕ,IsBlockNumbering X.obj.1.1 σ ∧
      sbipGraphDecodePartition X.obj.1.1 e₁ q = kerPartition X.obj.1.1.V₁ (blkColor X.obj.1.1 σ) := by
  obtain ⟨row,hm,rfl⟩ := List.mem_map.1 hq
  exact ⟨sbipBlockNumbering X.obj.1.1 (r := (sbipGraphEarly2Input r,row)) e₂,
    sbipBlockNumbering_valid _ _,
    (sbipGraphEarly2_row X r name h hl hr e₁ e₂ he₁ he₂ row
      ((mem_sbipNumberings (sbip_log_guard hsmall)).1 hm)).1⟩

end

theorem sbipGraphEarly2_nonempty (c : ℕ) (r : RawSbipGraph)
    (hsmall : r.1.2.1.length ≤ c * Nat.log 2 r.1.1.length) :
    ∃ q,q ∈ sbipGraphEarly2 (c+1) r := by
  obtain ⟨row,hr⟩ := sbipNumberings_nonempty (sbip_log_guard hsmall)
  exact ⟨_,List.mem_map.2 ⟨row,hr,rfl⟩⟩

theorem sbipGraphEarly2_width (c : ℕ) (r : RawSbipGraph)
    (hsmall : r.1.2.1.length ≤ c * Nat.log 2 r.1.1.length) :
    (sbipGraphEarly2 (c+1) r).length ≤ r.1.2.1.length ^ r.1.2.1.length :=
  sbipStep2Versions_width _ hsmall

end Algo
