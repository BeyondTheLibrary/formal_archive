import Workspace.Algo.SplitBipCaseOutcomeLocal
import Workspace.Algo.SplitBipCaseOutcomeJohnson

/-! Case 1 and Case 2 read their output tests directly. Every partition
exit has the promised local alpha bound. Johnson carriers keep their
subset rows while their singleton names are restored.
-/
namespace Algo
open Babai RAM
open scoped Classical

section Partitions
variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {s : Set Ω}
    {X : BlkDesignObj s} {name₁ : ↥X.Pt₁ → ℕ} {name₂ : ↥X.blocks → ℕ}
    {r : RawUpccCase} (h : DesignNames X name₁ name₂ r)
    (e₁ : ↥X.Pt₁ ≃ Fin r.2.1.length) (he₁ : ∀ x,r.2.1[(e₁ x).val] = name₁ x)
    (e₂ : ↥X.blocks ≃ Fin r.2.2.length) (he₂ : ∀ B,r.2.2[(e₂ B).val] = name₂ B)
    (p : ℕ × ℕ) (hb : 0 < p.2)
    (ha : 2/3 ≤ sbipAlphaValue p) (ha1 : sbipAlphaValue p < 1)
    (hn : (X.n₂ : ℝ) < sbipAlphaValue p * X.n₁)
include h he₁ he₂ hb ha ha1 hn

theorem sbipCaseDesign_partition (l : List ℕ) (q : RawColPart)
    (hout : designCase12 (r,p) = some ((l,rawAlignPartition q),none)) :
    l = r.2.1 ∧ (decColPartition r.2.1.length q).IsAlphaPartition (sbipAlphaValue p) := by
  unfold designCase12 at hout
  split at hout
  · simp [designJohnsonExit,rawAlignJohnson,rawAlignPartition] at hout
  next h1 =>
    split at hout
    next h2 =>
      unfold designCase2Exit at hout
      split at hout
      · simp [designGraphExit,rawAlignPartition] at hout
      next ht =>
        split at hout
        next hc =>
          split at hout
          next hs =>
            simp only [designPartExit,rawAlignPartition,Option.some.injEq,Prod.mk.injEq,
              and_true] at hout
            rcases hout with ⟨rfl,rfl⟩
            exact ⟨rfl,designSmallPartition_valid h e₁ he₁ e₂ he₂ p hb hs⟩
          next hs =>
            have hd := designDomHyp_of_tests h e₁ he₁ e₂ he₂ p hb ha ha1 hn h2 ht hs
            unfold designDominantExit at hout
            split at hout
            next htw =>
              simp only [designPartExit,rawAlignPartition,Option.some.injEq,Prod.mk.injEq,
                and_true] at hout
              rcases hout with ⟨rfl,rfl⟩
              exact ⟨rfl,designDomPartition_valid h e₁ he₁ e₂ he₂ p hb hd htw⟩
            next htw =>
              split at hout
              next hbnd =>
                simp only [designPartExit,rawAlignPartition,Option.some.injEq,Prod.mk.injEq,
                  and_true] at hout
                rcases hout with ⟨rfl,rfl⟩
                exact ⟨rfl,designPairPartition_valid h e₁ he₁ e₂ he₂ p hb hd htw hbnd⟩
              · simp [designJohnsonExit,rawAlignJohnson,rawAlignPartition] at hout
        · simp [designGraphExit,rawAlignPartition] at hout
    · simp at hout

theorem sbipCaseDesign_johnson (hw : r.WF) (l : List ℕ) (J : RawJohnson)
    (hout : designCase12 (r,p) = some ((l,rawAlignJohnson J),none)) :
    l = r.2.1 ∧ (∀ a ∈ J.1,a ∈ r.2.1) ∧
      sbipAlphaValue p * (r.2.1.length : ℝ) ≤ (J.1.length : ℝ) ∧
      ∃ ms ts,J.WF r.1.1.length ms ts := by
  have hlt : X.n₂ < X.n₁ := by
    have hh : (X.n₂ : ℝ) < X.n₁ := hn.trans_le
      (mul_le_of_le_one_left (Nat.cast_nonneg _) ha1.le)
    exact_mod_cast hh
  unfold designCase12 at hout
  split at hout
  next h1 =>
    simp only [designJohnsonExit,rawAlignJohnson,Option.some.injEq,Prod.mk.injEq,
      and_true,true_and] at hout
    rcases hout with ⟨rfl,rfl⟩
    exact ⟨rfl,fun _ ha => ha,mul_le_of_le_one_left (Nat.cast_nonneg _) ha1.le,
      _,_,designJohnson_wf h e₁ he₁ e₂ he₂ hw hlt
        ((designCase1_spec h e₁ he₁ e₂ he₂).1 h1)⟩
  next h1 =>
    split at hout
    next h2 =>
      unfold designCase2Exit at hout
      split at hout
      · simp [designGraphExit,rawAlignJohnson] at hout
      next ht =>
        split at hout
        next hc =>
          split at hout
          · simp [designPartExit,rawAlignPartition,rawAlignJohnson] at hout
          next hs =>
            have hd := designDomHyp_of_tests h e₁ he₁ e₂ he₂ p hb ha ha1 hn h2 ht hs
            unfold designDominantExit at hout
            split at hout
            · simp [designPartExit,rawAlignPartition,rawAlignJohnson] at hout
            next htw =>
              split at hout
              · simp [designPartExit,rawAlignPartition,rawAlignJohnson] at hout
              next hbnd =>
                simp only [designJohnsonExit,rawAlignJohnson,Option.some.injEq,Prod.mk.injEq,
                  and_true,true_and] at hout
                rcases hout with ⟨rfl,rfl⟩
                refine ⟨rfl,?_,?_,_,_,designDomJohnson_wf h e₁ he₁ e₂ he₂ p hb hd hw htw hbnd⟩
                · intro a ha'
                  obtain ⟨i,hi,rfl⟩ := List.mem_map.1 ha'
                  have hil := List.mem_range.1 (List.mem_of_mem_filter hi)
                  rw [labAt,List.getD_eq_getElem _ _ hil]
                  exact List.getElem_mem _
                · simpa only [designDomJohnson,designDomPoints,List.length_map,
                    designDomPositions_size h e₁ he₁ e₂ he₂ p hb,designLeft_length e₁]
                    using hd.alpha_le_ncard_domClass
        · simp [designGraphExit,rawAlignJohnson] at hout
    · simp at hout

/-- All raw Johnson exits retain a complete scheme after restoring their
singleton dictionary names. The ambient bound is the original degree. -/
theorem sbipCaseDesign_johnson_restored (hw : r.WF) (l : List ℕ) (J : RawJohnson)
    (hout : designCase12 (r,p) = some ((l,rawAlignJohnson J),none))
    (point : ↥s → ℕ) (hpoint : Function.Injective point) (d : List (List ℕ))
    (hrow : ∀ x : ↥X.Pt₁,sbipDictPoint (d,name₁ x) = point x.val)
    (m : ℕ) (hlt : ∀ x : ↥X.Pt₁,point x.val < m) :
    ∃ ms ts,(sbipCaseJohnson (d,J)).WF m ms ts ∧
      ∀ a b,a ∈ J.1 → b ∈ J.1 →
        rawJDiff (sbipCaseJohnson (d,J),(sbipDictPoint (d,a),sbipDictPoint (d,b))) =
          rawJDiff (J,(a,b)) := by
  obtain ⟨_,hsub,_,ms,ts,hJ⟩ := sbipCaseDesign_johnson h e₁ he₁ e₂ he₂ p hb ha ha1 hn hw l J hout
  have hinj : Set.InjOn (fun a => sbipDictPoint (d,a)) {a | a ∈ J.1} := by
    intro a ha b hb he
    obtain ⟨x,rfl⟩ := (h.left a).1 (hsub a ha)
    obtain ⟨y,rfl⟩ := (h.left b).1 (hsub b hb)
    change sbipDictPoint (d,name₁ x) = sbipDictPoint (d,name₁ y) at he
    rw [hrow,hrow] at he
    exact congrArg name₁ (Subtype.ext (hpoint he))
  have hbnd : ∀ a ∈ J.1,sbipDictPoint (d,a) < m := by
    intro a ha
    obtain ⟨x,rfl⟩ := (h.left a).1 (hsub a ha)
    rw [hrow]
    exact hlt x
  exact ⟨ms,ts,sbipCaseJohnson_wf hinj hbnd hJ,
    fun _ _ ha hb => sbipCaseJohnson_diff hinj hbnd hJ ha hb⟩
end Partitions

end Algo
