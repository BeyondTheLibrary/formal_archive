import Workspace.Algo.SplitImprimitiveGraphRep

/-! # Section 9.6: correctness of both graph branches

The restriction case returns exactly the passing groups. The contraction
case is reached only when none passes. The paper's defect lemma then proves
that the contracted graph has the required defect.
-/
set_option maxHeartbeats 1000000
namespace Algo
open Babai RAM

section Restriction
variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {s : Set Ω}
    {X : BlkImprimitiveObj s} {name₁ : ↥X.Pt₁ → ℕ} {name₂ : ↥X.blocks → ℕ}
    {r : RawUpccCase} (h : ImpNames X name₁ name₂ r) (hleft : r.2.1.Nodup)
    (e : ↥X.blocks ≃ Fin r.2.2.length) (he : ∀ B, r.2.2[(e B).val] = name₂ B)

include h hleft he

/-- Every field of a restricted graph agrees with `blkZ`. -/
theorem impRestrictionGraph_rep (G : Set ↥X.blocks) (g : List ℕ) (hnd : g.Nodup)
    (hg : ∀ a, a ∈ g ↔ ∃ C ∈ G, name₂ C = a) :
    ImpGraphRep X name₁ name₂ r (impRestrictionGraph (r,g)) (X.blkZ G) := by
  refine impMakeGraph_rep h (impJ r) (g.map (fun b => [b])) (X.blkZ G) rfl
    (hnd.map (fun a b heq => List.singleton_inj.1 heq)) ?_
    (impColumns_restriction h e he G g hg) ?_
    (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
  · rintro l hl l' hl' heq
    obtain ⟨a,ha,rfl⟩ := List.mem_map.1 hl
    obtain ⟨b,hb,rfl⟩ := List.mem_map.1 hl'
    obtain ⟨B,_,rfl⟩ := (hg _).1 ha
    obtain ⟨C,_,rfl⟩ := (hg _).1 hb
    rw [impColumnSet_singleton X name₂ h.inj₂,impColumnSet_singleton X name₂ h.inj₂] at heq
    exact congrArg (fun D : ↥X.blocks => [name₂ D]) (Subtype.ext heq)
  · intro x l hl
    obtain ⟨a,ha,rfl⟩ := List.mem_map.1 hl
    obtain ⟨B,hB,rfl⟩ := (hg _).1 ha
    rw [impColumnSet_singleton X name₂ h.inj₂,impColumnEdge_spec]
    have hb : B.val ∈ (X.blkZ G).blocks := ⟨B,hB,rfl⟩
    change (∃ b ∈ [name₂ B], binColor (r.1,(name₁ x,b)) = impJ r) ↔
      B.val ∈ (X.blkZ G).blocks ∧ X.part₁ x.val ∧ X.c {x.val} B.val = X.jColor
    simp only [List.mem_singleton,exists_eq_left,h.link,impJ_spec h hleft,hb,true_and]
    exact (and_iff_right x.property).symm

end Restriction

section Selection
variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {s : Set Ω}
    {X : BlkImprimitiveObj s} {name₁ : ↥X.Pt₁ → ℕ} {name₂ : ↥X.blocks → ℕ}
    {r : RawUpccCase} (h : ImpNames X name₁ name₂ r)
    (hleft : r.2.1.Nodup) (hright : r.2.2.Nodup)
    (e : ↥X.blocks ≃ Fin r.2.2.length) (he : ∀ B, r.2.2[(e B).val] = name₂ B)

include h hleft hright he

theorem impGoodGroups_empty : (impGoodGroups r).isEmpty = true ↔ ¬ X.hasGoodBlock := by
  rw [← impGoodGroups_nonempty h hleft hright e he]
  simp [List.isEmpty_iff,List.eq_nil_iff_forall_not_mem]

open scoped Classical in
/-- The contraction has sufficient defect when the fallback is needed.
The proof uses the paper's existence lemma and rules out its restriction case. -/
theorem impContraction_defect (hsplit : ¬ ImprimitiveSplits X)
    (hempty : (impGoodGroups r).isEmpty = true) :
    letI : Fintype ↥s := Fintype.ofFinite _
    letI : DecidableEq ↥s := Classical.decEq _
    1 / 2 ≤ X.blkContr.defect₁ := by
  have hn := (impGoodGroups_empty h hleft hright e he).1 hempty
  obtain ⟨Y,hY,hdef⟩ := step2Cands_exists_defect X hsplit
  rcases hY with ⟨G,hG,rfl⟩ | rfl
  · exact (hn ⟨G,hG,hdef⟩).elim
  · exact hdef

open scoped Classical in
/-- Every returned graph has the paper's exact representation and belongs to
the selected mathematical branch, with the same defect and halving bounds. -/
theorem impStep2Graphs_spec (hsplit : ¬ ImprimitiveSplits X)
    (q : RawImpGraph) (hq : q ∈ impStep2Graphs r) :
    letI : Fintype ↥s := Fintype.ofFinite _
    letI : DecidableEq ↥s := Classical.decEq _
    ∃ Y : VColBipBlk ↥s ℕ, ImpGraphRep X name₁ name₂ r q Y ∧
      Y ∈ X.step2Cands ∧ 1 / 2 ≤ Y.defect₁ ∧
      (X.hasGoodBlock → Y ∈ X.blkZ '' X.groups) ∧
      2 * q.2.1.length ≤ X.blocks.ncard := by
  classical
  letI : Fintype ↥s := Fintype.ofFinite _
  letI : DecidableEq ↥s := Classical.decEq _
  unfold impStep2Graphs at hq
  split at hq
  next hempty =>
    have heq : q = impContractionGraph r := List.mem_singleton.1 hq
    subst q
    have hr := impContractionGraph_rep h hleft e he
    refine ⟨X.blkContr,hr,Or.inr rfl,
      impContraction_defect h hleft hright e he hsplit hempty,
      fun hh => ((impGoodGroups_empty h hleft hright e he).1 hempty hh).elim,?_⟩
    rw [← hr.numBlocks]
    exact step2Cands_two_mul_numBlocks_le X _ (Or.inr rfl)
  next _ =>
    obtain ⟨g,hg,rfl⟩ := List.mem_map.1 hq
    obtain ⟨hmem,hpass⟩ := List.mem_filter.1 hg
    obtain ⟨G,hG,hrep⟩ := impGroups_spec h e he g hmem
    have hnd := impGroups_members_nodup hright hmem
    have hr := impRestrictionGraph_rep h hleft e he G g hnd hrep
    have hZ : X.blkZ G ∈ X.blkZ '' X.groups := ⟨G,hG,rfl⟩
    refine ⟨X.blkZ G,hr,Or.inl hZ,(impGoodGroup_iff h hleft G g hnd hrep).1 hpass,
      fun _ => hZ,?_⟩
    rw [← hr.numBlocks]
    exact step2Cands_two_mul_numBlocks_le X _ (Or.inl hZ)

open scoped Classical in
/-- Every passing block restriction has a returned raw version. -/
theorem impStep2Graphs_complete (G : Set ↥X.blocks) (hG : G ∈ X.groups)
    (hdef : letI : Fintype ↥s := Fintype.ofFinite _
      letI : DecidableEq ↥s := Classical.decEq _
      1 / 2 ≤ (X.blkZ G).defect₁) :
    ∃ q ∈ impStep2Graphs r, ImpGraphRep X name₁ name₂ r q (X.blkZ G) := by
  obtain ⟨g,hmem,hrep⟩ := impGroups_complete h e he G hG
  have hnd := impGroups_members_nodup hright hmem
  have hgood : g ∈ impGoodGroups r := List.mem_filter.2
    ⟨hmem,(impGoodGroup_iff h hleft G g hnd hrep).2 hdef⟩
  have hne : ¬ (impGoodGroups r).isEmpty = true := by
    intro hh
    have := List.isEmpty_iff.1 hh
    simp [this] at hgood
  refine ⟨impRestrictionGraph (r,g),?_,impRestrictionGraph_rep h hleft e he G g hnd hrep⟩
  rw [impStep2Graphs,if_neg hne]
  exact List.mem_map.2 ⟨g,hgood,rfl⟩

open scoped Classical in
/-- Every graph in the selected mathematical family has a returned encoding. -/
theorem impStep2Graphs_covers (Y : VColBipBlk ↥s ℕ)
    (hY : Y ∈ X.step2Cands)
    (hdef : letI : Fintype ↥s := Fintype.ofFinite _
      letI : DecidableEq ↥s := Classical.decEq _
      1 / 2 ≤ Y.defect₁)
    (hbranch : X.hasGoodBlock → Y ∈ X.blkZ '' X.groups) :
    ∃ q ∈ impStep2Graphs r, ImpGraphRep X name₁ name₂ r q Y := by
  classical
  by_cases hg : X.hasGoodBlock
  · obtain ⟨G,hG,rfl⟩ := hbranch hg
    exact impStep2Graphs_complete h hleft hright e he G hG hdef
  · rcases hY with ⟨G,hG,rfl⟩ | rfl
    · exact (hg ⟨G,hG,hdef⟩).elim
    · refine ⟨impContractionGraph r,?_,impContractionGraph_rep h hleft e he⟩
      rw [impStep2Graphs,if_pos ((impGoodGroups_empty h hleft hright e he).2 hg)]
      exact List.mem_singleton_self _

omit [Fintype Ω] [DecidableEq Ω] h hleft hright he in
theorem impStep2Graphs_nonempty : ∃ q, q ∈ impStep2Graphs r := by
  unfold impStep2Graphs
  split
  · exact ⟨_,List.mem_singleton_self _⟩
  · rename_i hn
    have hm : ∃ g, g ∈ impGoodGroups r := by
      simpa only [List.isEmpty_iff,List.eq_nil_iff_forall_not_mem,not_forall,not_not] using hn
    obtain ⟨g,hg⟩ := hm
    exact ⟨_,List.mem_map.2 ⟨g,hg,rfl⟩⟩

end Selection
end Algo
