import Workspace.Algo.SplitImprimitiveStep2

/-! # Section 9.6: the complete ImprimitiveCase implementation

The first branch returns the colors and their fibers after individualizing
one second-part vertex. Otherwise the procedure returns one of the graphs
proved correct in `SplitImprimitiveStep2`. Both branches keep the original
first part and satisfy Lemma 9.6.1.
-/
namespace Algo
open Babai RAM

section Representation
variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {s : Set Ω}
    (X : BlkImprimitiveObj s) (name₁ : ↥X.Pt₁ → ℕ) (name₂ : ↥X.blocks → ℕ)
    (r : RawUpccCase) (e₁ : ↥X.Pt₁ ≃ Fin r.2.1.length)

def ImpOutcomeRep (q : RawImpOutcome)
    (Z : Pt (Cat.sum (ColoredPartitions Ω ℕ) (VColBlkGraphs Ω ℕ))) : Prop :=
  match q.2 with
  | none => q.1.length = r.2.1.length ∧
      ∃ P : ColoredPartition ↥(Subtype.val '' X.Pt₁) ℕ,
        Z = ⟨Subtype.val '' X.Pt₁,Sum.inl P⟩ ∧
        (∀ x : ↥X.Pt₁, labAt q.1 (e₁ x) = P.color (mkPt x.property)) ∧
        (∀ x y : ↥X.Pt₁, LabRel q.1 (e₁ x) (e₁ y) ↔
          P.part (mkPt x.property) (mkPt y.property))
  | some g => q.1 = [] ∧ ∃ Y : VColBipBlk ↥s ℕ,
      Z = ⟨s,Sum.inr Y⟩ ∧ ImpGraphRep X name₁ name₂ r g Y

end Representation

section Specification
variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {s : Set Ω}
    {X : BlkImprimitiveObj s} {name₁ : ↥X.Pt₁ → ℕ} {name₂ : ↥X.blocks → ℕ}
    {r : RawUpccCase} (h : ImpNames X name₁ name₂ r)
    (hleft : r.2.1.Nodup) (hright : r.2.2.Nodup)
    (e₁ : ↥X.Pt₁ ≃ Fin r.2.1.length) (he₁ : ∀ x, r.2.1[(e₁ x).val] = name₁ x)
    (e₂ : ↥X.blocks ≃ Fin r.2.2.length) (he₂ : ∀ B, r.2.2[(e₂ B).val] = name₂ B)

include h he₁

theorem impSplit_rep (B : ↥X.blocks) :
    ImpOutcomeRep X name₁ name₂ r e₁ (impSplitLab (r,name₂ B),none)
      ⟨Subtype.val '' X.Pt₁,Sum.inl (kerPartition X.Pt₁ (fun x => X.c {x} B.val))⟩ := by
  refine ⟨by simp [impSplitLab],_,rfl,?_,?_⟩
  · intro x
    exact impSplitLab_spec h B x (e₁ x) (he₁ x)
  · intro x y
    rw [LabRel,impSplitLab_spec h B x (e₁ x) (he₁ x),
      impSplitLab_spec h B y (e₁ y) (he₁ y)]
    rfl

omit h he₁ in
/-- The degree bound of step 1 bounds every color class of its returned partition. -/
theorem impSplit_good (hsplit : ImprimitiveSplits X) (B : ↥X.blocks) :
    IsBlkImprimitiveOutcome (Subtype.val '' X.Pt₁) X.blocks.ncard
      ⟨Subtype.val '' X.Pt₁,Sum.inl (kerPartition X.Pt₁ (fun x => X.c {x} B.val))⟩ := by
  classical
  refine ⟨rfl,kerPartition_isAlphaPartition _ _ _
    (k := X.Pt₁.ncard / 2) (fun x hx => ?_) ?_⟩
  · have hh := hsplit B.val B.property (X.c {x} B.val)
    change {y : ↥s | X.part₁ y ∧ X.c {y} B.val = X.c {x} B.val}.ncard ≤ _
    change 2 * _ ≤ X.Pt₁.ncard at hh
    omega
  · have hh : 2 * (X.Pt₁.ncard / 2) ≤ X.Pt₁.ncard := by omega
    have hh' : (2 : ℝ) * (X.Pt₁.ncard / 2 : ℕ) ≤ X.Pt₁.ncard := by exact_mod_cast hh
    linarith

include hleft hright he₂

/-- Every returned raw outcome represents an outcome of Lemma 9.6.1. -/
theorem impCase_spec (q : RawImpOutcome) (hq : q ∈ impCase r) :
    ∃ Z : Pt (Cat.sum (ColoredPartitions Ω ℕ) (VColBlkGraphs Ω ℕ)),
      ImpOutcomeRep X name₁ name₂ r e₁ q Z ∧
        IsBlkImprimitiveOutcome (Subtype.val '' X.Pt₁) X.blocks.ncard Z := by
  unfold impCase at hq
  split at hq
  next hs =>
    obtain ⟨b,hb,rfl⟩ := List.mem_map.1 hq
    obtain ⟨B,rfl⟩ := (h.right _).1 hb
    exact ⟨_,impSplit_rep h e₁ he₁ B,impSplit_good ((impSplits_spec h hleft).1 hs) B⟩
  next hs =>
    obtain ⟨g,hg,rfl⟩ := List.mem_map.1 hq
    have hn : ¬ ImprimitiveSplits X := fun hx => hs ((impSplits_spec h hleft).2 hx)
    obtain ⟨Y,hrep,hY,hdef,_,hsize⟩ := impStep2Graphs_spec h hleft hright e₂ he₂ hn g hg
    refine ⟨⟨s,Sum.inr Y⟩,⟨rfl,Y,rfl,hrep⟩,?_,?_,hdef⟩
    · change Subtype.val '' Y.V₁ = Subtype.val '' X.Pt₁
      exact congrArg (fun p : ↥s → Prop => Subtype.val '' {x | p x}) hrep.part
    · rw [hrep.numBlocks]
      exact hsize

omit hleft hright he₁ he₂ in
theorem impCase_nonempty : ∃ q, q ∈ impCase r := by
  unfold impCase
  split
  · obtain ⟨B,hB⟩ := X.blocks_nonempty'
    exact ⟨_,List.mem_map.2 ⟨name₂ ⟨B,hB⟩,(h.right _).2 ⟨_,rfl⟩,rfl⟩⟩
  · obtain ⟨g,hg⟩ := impStep2Graphs_nonempty (r := r)
    exact ⟨_,List.mem_map.2 ⟨g,hg,rfl⟩⟩

end Specification

/-- At most one graph per component, with one contraction as the fallback. -/
theorem impStep2Graphs_length (r : RawUpccCase) :
    (impStep2Graphs r).length ≤ max 1 r.2.2.length := by
  unfold impStep2Graphs
  split
  · simpa using Nat.le_max_left 1 r.2.2.length
  · rw [List.length_map]
    apply (List.length_filter_le _ _).trans
    have hh := length_dedupG_le ((List.range r.2.2.length).map (fun i => impGroup (r,i)))
    simpa only [List.length_map,List.length_range] using hh.trans (Nat.le_max_right 1 _)

/-- The complete family has at most `n₂` versions on a nonempty second part. -/
theorem impCase_length (r : RawUpccCase) (hn : 0 < r.2.2.length) :
    (impCase r).length ≤ r.2.2.length := by
  unfold impCase
  split
  · simp
  · rw [List.length_map]
    exact (impStep2Graphs_length r).trans (max_le (by omega) le_rfl)

end Algo
