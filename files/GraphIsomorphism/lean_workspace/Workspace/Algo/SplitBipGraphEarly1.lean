import Workspace.Algo.SplitBipGraphEarlyNames

/-! Step 1 returns the paper's individualized partition on the parent
first part. Every emitted numbering is well formed, and every allowed
mathematical numbering is represented in the returned family.
-/
namespace Algo
open Babai RAM
open scoped Classical

section
variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    (X : Pt (BipBlockInputs Ω)) (z : RawSbipGraph × (ℕ × ℕ))
    (e₁ : ↥X.obj.1.1.V₁ ≃ Fin z.1.1.1.length)
    (ha : sbipAlphaValue z.2 = BipBlockInputs.alpha X)
include ha

theorem sbipGraphEarly1_row (row : RawPerm) (hw : RawPerm.WF z.1.1.1.length row) :
    let P := kerPartition X.obj.1.1.V₁
      (indivColor (sbipPartNumbering X.obj.1.1 e₁ row)
        (X.obj.1.1.V₁.ncard - ⌊BipBlockInputs.alpha X * X.obj.1.1.V₁.ncard⌋₊))
    sbipGraphDecodePartition X.obj.1.1 e₁ (sbipStep1 ((z.1.1.1,z.2),row)) = P ∧
      (decColPartition z.1.1.1.length (sbipStep1 ((z.1.1.1,z.2),row))).IsAlphaPartition
        (BipBlockInputs.alpha X) := by
  have hs (x y : ↥X.obj.1.1.V₁) := sbipStep1_spec X.obj.1.1 e₁ z.2 hw x y
  simp_rw [ha] at hs
  have hc := fun x => (hs x x).1
  have hb (x y : ↥X.obj.1.1.V₁) := (hs x y).2
  have hb' (x y : ↥X.obj.1.1.V₁) :
      LabRel (sbipStep1 ((z.1.1.1,z.2),row)).2 (e₁ x) (e₁ y) ↔
        (kerPartition X.obj.1.1.V₁ (indivColor (sbipPartNumbering X.obj.1.1 e₁ row)
          (X.obj.1.1.V₁.ncard - ⌊BipBlockInputs.alpha X * X.obj.1.1.V₁.ncard⌋₊))).part
            (mkPt x.property) (mkPt y.property) := by
    have hh := hb x y
    change LabRel _ _ _ ↔ indivColor _
      (X.obj.1.1.V₁.ncard - ⌊sbipAlphaValue z.2 * X.obj.1.1.V₁.ncard⌋₊) x.val =
        indivColor _ (X.obj.1.1.V₁.ncard - ⌊sbipAlphaValue z.2 * X.obj.1.1.V₁.ncard⌋₊) y.val at hh
    rw [ha] at hh
    exact hh
  have hp := sbipGraphCell_spec X.obj.1.1 e₁ _ _ hc hb'
  exact ⟨sbipGraphDecodePartition_eq X.obj.1.1 e₁ _ _ hc hp,
    sbipGraphDecodedPartition_valid X.obj.1.1 e₁ _ _ hc hp (Fintype.ofFinite _)
      (sbipStep1_good X e₁ row).2⟩

include e₁ in
theorem sbipGraphEarly1_valid {c : ℕ} (hsmall : z.1.1.1.length ≤ c)
    (q : RawColPart) (hq : q ∈ sbipGraphEarly1 c z) :
    (decColPartition z.1.1.1.length q).IsAlphaPartition (BipBlockInputs.alpha X) := by
  obtain ⟨row,hr,rfl⟩ := List.mem_map.1 hq
  exact (sbipGraphEarly1_row X z e₁ ha row ((mem_sbipNumberings (sbip_small_guard hsmall)).1 hr)).2

theorem sbipGraphEarly1_covers {c : ℕ} (hsmall : z.1.1.1.length ≤ c)
    (σ : ↥X.car → ℕ) (hσ : IsPart₁Numbering X.obj.1.1 σ) :
    ∃ q ∈ sbipGraphEarly1 c z,
      sbipGraphDecodePartition X.obj.1.1 e₁ q =
        kerPartition X.obj.1.1.V₁ (indivColor σ
          (X.obj.1.1.V₁.ncard - ⌊BipBlockInputs.alpha X * X.obj.1.1.V₁.ncard⌋₊)) := by
  obtain ⟨row,hr,he⟩ := sbipPartNumbering_complete X.obj.1.1 e₁ hsmall σ hσ
  refine ⟨_,List.mem_map.2 ⟨row,hr,rfl⟩,?_⟩
  have hs := (sbipGraphEarly1_row X z e₁ ha row ((mem_sbipNumberings (sbip_small_guard hsmall)).1 hr)).1
  simpa only [he] using hs

theorem sbipGraphEarly1_paper {c : ℕ} (hsmall : z.1.1.1.length ≤ c)
    (q : RawColPart) (hq : q ∈ sbipGraphEarly1 c z) :
    ∃ σ : ↥X.car → ℕ,IsPart₁Numbering X.obj.1.1 σ ∧
      sbipGraphDecodePartition X.obj.1.1 e₁ q =
        kerPartition X.obj.1.1.V₁ (indivColor σ
          (X.obj.1.1.V₁.ncard - ⌊BipBlockInputs.alpha X * X.obj.1.1.V₁.ncard⌋₊)) := by
  obtain ⟨row,hr,rfl⟩ := List.mem_map.1 hq
  exact ⟨sbipPartNumbering X.obj.1.1 e₁ row,sbipPartNumbering_valid _ _ _,
    (sbipGraphEarly1_row X z e₁ ha row ((mem_sbipNumberings (sbip_small_guard hsmall)).1 hr)).1⟩

end

theorem sbipGraphEarly1_nonempty (c : ℕ) (z : RawSbipGraph × (ℕ × ℕ))
    (hsmall : z.1.1.1.length ≤ c) : ∃ q,q ∈ sbipGraphEarly1 c z := by
  obtain ⟨row,hr⟩ := sbipNumberings_nonempty (sbip_small_guard hsmall)
  exact ⟨_,List.mem_map.2 ⟨row,hr,rfl⟩⟩

theorem sbipGraphEarly1_width (c : ℕ) (z : RawSbipGraph × (ℕ × ℕ))
    (hsmall : z.1.1.1.length ≤ c) : (sbipGraphEarly1 c z).length ≤ constFactor c :=
  sbipStep1Versions_width _ hsmall

end Algo
