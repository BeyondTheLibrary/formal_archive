import Workspace.Algo.TopMasterLeafCost

/-! # Bounds read from the computed Reduce-to-Johnson route
A fixed small-group cutoff forces every surviving window past the required
absolute degree. The block branch, including the small Cameron-degree
exception, fits the existing line-1 multiplicative cost.
-/
namespace Algo
open RAM RAM.Targets Babai Equiv

theorem masterGroupCard_le_factorial (n : ℕ) (gs : RawGens) :
    Nat.card (decGroup n gs) ≤ n.factorial := by
  have h := Nat.card_le_card_of_injective (fun g : decGroup n gs => g.val) Subtype.val_injective
  simpa only [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin] using h

/-- The early exits guarantee a large enough window without a promised degree. -/
theorem masterReduceRoute_large_window {n B C₀ N : ℕ} {W : RawWinSI}
    (hw : RawGens.WF n W.2.1) (hnd : W.1.Nodup) (hlt : ∀ u ∈ W.1, u < n)
    (hinv : IsInvariant (decGroup n W.2.1) (winSet n W.1))
    (hC : N.factorial < C₀) (h0 : masterReduceRoute B C₀ W ≠ 0)
    (h1 : masterReduceRoute B C₀ W ≠ 1) : N < W.1.length := by
  have ha := mt (masterReduceRoute_trivial B C₀ W).mpr h0
  have hg : C₀ ≤ rawOrder (W.1, (primitiveWindowInput W).1) := by
    by_contra h
    have hb : rawOrder ((masterWindowGroup W).2, (masterWindowGroup W).1) < C₀ := by
      exact Nat.lt_of_not_ge h
    exact h1 ((masterReduceRoute_brute B C₀ W).mpr ⟨Bool.eq_false_iff.mpr ha, hb⟩)
  have hgs : RawGens.WF W.1.length (primitiveWindowInput W).1 :=
    rawRestrictGens_wf_of_raw hw hnd hlt hinv
  have he := rawOrder_spec W.1 rfl ((primitiveWindowInput W).1.map (decPerm W.1.length))
  rw [map_encPerm_decPerm hgs] at he
  rw [he] at hg
  change C₀ ≤ Nat.card (decGroup W.1.length (primitiveWindowInput W).1) at hg
  have hc := masterGroupCard_le_factorial W.1.length (primitiveWindowInput W).1
  by_contra hn
  have hf := Nat.factorial_le (Nat.le_of_not_gt hn)
  omega

/-- The block branch has the same multiplicative budget as the mathematical line-1 case. -/
theorem masterReduceRoute_block_cost {n B C₀ : ℕ} {W : RawWinSI}
    (hx : W.2.2.2.1.length = n) (hw : RawGens.WF n W.2.1)
    (hnd : W.1.Nodup) (hlt : ∀ u ∈ W.1, u < n)
    (hinv : IsInvariant (decGroup n W.2.1) (winSet n W.1))
    (hC : (max 64 B.factorial).factorial < C₀)
    (hr : masterReduceRoute B C₀ W = 3) :
    Nat.card (decGroup (masterBlockGroup W).2.length (masterBlockGroup W).1) ≤
      line1Cost W.1.length := by
  have hlarge := masterReduceRoute_large_window hw hnd hlt hinv hC
    (by omega : masterReduceRoute B C₀ W ≠ 0) (by omega : masterReduceRoute B C₀ W ≠ 1)
  have hwin : 1 ≤ W.1.length := by have := le_max_left 64 B.factorial; omega
  have hn : 2 ≤ W.1.length := by have := le_max_left 64 B.factorial; omega
  obtain ⟨_, _, ht, hs⟩ := (masterReduceRoute_block B C₀ W).mp hr
  have hgs : RawGens.WF W.1.length (primitiveWindowInput W).1 :=
    rawRestrictGens_wf_of_raw hw hnd hlt hinv
  have htr := (rawIsTransitive_eq_true_iff hgs rfl).mp ht
  have hp := masterWindowBlockAction_wf hx hw hnd hlt hinv htr hn
  rcases hs with hs | hs
  · have hc := masterGroupCard_le_factorial (masterBlockGroup W).2.length (masterBlockGroup W).1
    have hf := Nat.factorial_le hs.le
    have hm := le_max_right 64 B.factorial
    exact hc.trans (hf.trans ((by omega : B.factorial ≤ W.1.length).trans (self_le_line1Cost hwin)))
  · have hm : 1 ≤ (masterBlockGroup W).2.length := by
      by_contra h
      have hz : (masterBlockGroup W).2.length = 0 := by omega
      simp [masterSmallOrder, masterOrderCap, hz, masterClog] at hs
    have hc := masterSmallOrder_true rfl (hp.2.1 ▸ hp.2.2.2.1) hm hs
    have hml : (masterBlockGroup W).2.length ≤ W.1.length := by
      change (blkDom (rawMinBlocks ((primitiveWindowInput W).1, W.1))).length ≤ W.1.length
      rw [length_blkDom]
      exact (blocksWF_rawMinBlocks rfl (primitiveWindowInput W).1).length_le
    exact hc.trans (line1Cost_mono hml)
end Algo
