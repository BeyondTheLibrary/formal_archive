import Workspace.Algo.SplitDesignLog
import Workspace.Algo.SplitHypergraph
import Workspace.Algo.SplitImprimitiveScan

/-! # Section 9.7: the neighborhood hypergraph in stored coordinates

The first link color determines the edges. Names and position bijections
connect those edges to the block design object without changing any colors.
-/
namespace Algo
open Babai RAM

/-- The constituent selected in step 8, read from the refined link. -/
def designBip (r : RawUpccCase) : RawBipConstituent :=
  ((r.1,sbipFirstInvolved r),r.2)

theorem polyFun_designBip : PolyFun designBip :=
  (polyFun_fst.pair sbipPoly_firstInvolved).pair polyFun_snd

section Names
variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {s : Set Ω}
    (X : BlkDesignObj s) (name₁ : ↥X.Pt₁ → ℕ) (name₂ : ↥X.blocks → ℕ)
    (r : RawUpccCase)

/-- Stored names preserve the two parts and all colors needed in Section 9.7. -/
structure DesignNames : Prop where
  inj₁ : Function.Injective name₁
  inj₂ : Function.Injective name₂
  left : ∀ a, a ∈ r.2.1 ↔ ∃ x, name₁ x = a
  right : ∀ b, b ∈ r.2.2 ↔ ∃ B, name₂ B = b
  link : ∀ x B, binColor (r.1,(name₁ x,name₂ B)) = X.c {x.val} B.val
  blocks : ∀ B C, binColor (r.1,(name₂ B,name₂ C)) = X.c B.val C.val
  points : ∀ x y, binColor (r.1,(name₁ x,name₁ y)) = X.c {x.val} {y.val}

variable {X name₁ name₂ r} (h : DesignNames X name₁ name₂ r)
include h

theorem designLink_mem (k : ℕ) : k ∈ sbipLinkColors r ↔ X.HasLinkColor k := by
  rw [sbipLinkColors_mem]
  constructor
  · rintro ⟨a,ha,b,hb,hc⟩
    obtain ⟨x,rfl⟩ := (h.left _).1 ha
    obtain ⟨B,rfl⟩ := (h.right _).1 hb
    exact ⟨x,x.property,B,B.property,(h.link x B).symm.trans hc⟩
  · rintro ⟨x,hx,B,hB,hc⟩
    exact ⟨name₁ ⟨x,hx⟩,(h.left _).2 ⟨_,rfl⟩,name₂ ⟨B,hB⟩,
      (h.right _).2 ⟨_,rfl⟩,(h.link _ _).trans hc⟩

theorem designFirst_spec : sbipFirstInvolved r = X.linkColor :=
  upccCaseLeast_find X.HasLinkColor _ (designLink_mem h)

variable (e₁ : ↥X.Pt₁ ≃ Fin r.2.1.length) (he₁ : ∀ x, r.2.1[(e₁ x).val] = name₁ x)
    (e₂ : ↥X.blocks ≃ Fin r.2.2.length) (he₂ : ∀ B, r.2.2[(e₂ B).val] = name₂ B)
include he₁ he₂

/-- A stored neighborhood contains exactly the incident mathematical blocks. -/
theorem designRow_mem (x : ↥X.Pt₁) (B : ↥X.blocks) :
    (e₂ B).val ∈ splitNeighborhoodRow (designBip r,e₁ x) ↔ B.val ∈ X.nbhd x.val := by
  rw [mem_splitNeighborhoodRow]
  change ((e₂ B).val < r.2.2.length ∧ _) ↔ _
  rw [and_iff_right (e₂ B).isLt]
  change decide (binColor (r.1,(r.2.1.getD (e₁ x) 0,r.2.2.getD (e₂ B) 0)) =
    sbipFirstInvolved r) = true ↔ _
  rw [List.getD_eq_getElem _ 0 (e₁ x).isLt,List.getD_eq_getElem _ 0 (e₂ B).isLt,
    he₁,he₂,h.link,designFirst_spec h,decide_eq_true_eq]
  exact (and_iff_right B.property).symm

omit h he₁ he₂ in
include e₁ in
theorem designLeft_length : r.2.1.length = X.n₁ := by
  have hc := Nat.card_congr e₁
  simpa [Nat.card_coe_set_eq,Nat.card_fin,BlkCaseObj.n₁,BlkCaseObj.Pt₁] using hc.symm

omit h he₁ he₂ in
include e₂ in
theorem designRight_length : r.2.2.length = X.n₂ := by
  have hc := Nat.card_congr e₂
  simpa [Nat.card_coe_set_eq,Nat.card_fin,BlkCaseObj.n₂] using hc.symm

/-- The computed degree agrees with the common degree in the paper. -/
theorem designRow_length (x : ↥X.Pt₁) :
    (splitNeighborhoodRow (designBip r,e₁ x)).length = X.d₁ := by
  have hn : (splitNeighborhoodRow (designBip r,e₁ x)).Nodup :=
    List.nodup_range.filter _
  have hh := splitNamedCount (fun B : ↥X.blocks => (e₂ B).val)
    (fun B C hh => e₂.injective (Fin.ext hh))
    (List.range r.2.2.length) List.nodup_range
    (fun a => by
      simp only [List.mem_range]
      constructor
      · intro ha; exact ⟨e₂.symm ⟨a,ha⟩,congrArg Fin.val (e₂.apply_symm_apply _)⟩
      · rintro ⟨B,rfl⟩; exact (e₂ B).isLt)
    (fun v => bipAdjRaw (designBip r,(e₁ x,v)))
  change (splitNeighborhoodRow (designBip r,e₁ x)).length = _ at hh
  rw [hh]
  have he : {B : ↥X.blocks | bipAdjRaw (designBip r,(e₁ x,e₂ B)) = true} =
      {B : ↥X.blocks | B.val ∈ X.nbhd x.val} := by
    ext B
    exact ((and_iff_right (e₂ B).isLt).symm.trans
      ((mem_splitNeighborhoodRow _ _ _).symm.trans (designRow_mem h e₁ he₁ e₂ he₂ x B)))
  rw [he,X.ncard_coe_blocks (X.nbhd_subset_blocks _),X.nbhd_ncard_eq_d₁ x.property]

end Names
end Algo
