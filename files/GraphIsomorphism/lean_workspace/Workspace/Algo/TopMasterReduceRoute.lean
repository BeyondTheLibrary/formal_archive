import Workspace.Algo.TopMasterTrivial

/-! # The executable Reduce-to-Johnson dispatcher
The early tests follow Section 11.3 in order. The order guard uses the
provisional rounding in `TopMasterOrder`; exact source branch matching is
not claimed. The two fixed constants are the
small-group cutoff and the absolute Cameron-degree threshold. Codes are
0 for the string-fixing exit, 1 for small-group brute force, 2 for the
Chain Rule, 3 for the block-kernel descent, and 4 for Cameron descent.
-/
namespace Algo
open RAM RAM.Targets Babai Equiv

def masterWindowGroup (W : RawWinSI) : RawGens × List ℕ := ((primitiveWindowInput W).1, W.1)
def masterBlockGroup (W : RawWinSI) : RawGens × List ℕ :=
  ((masterWindowBlockAction W).2.2, (masterWindowBlockAction W).2.1)

def masterReduceRoute (B C₀ : ℕ) (W : RawWinSI) : ℕ :=
  if masterAutTest (primitiveWindowInput W) then 0
  else if rawOrder ((masterWindowGroup W).2, (masterWindowGroup W).1) < C₀ then 1
  else if rawIsTransitive (masterWindowGroup W) then
    if (masterBlockGroup W).2.length < B then 3
    else if masterSmallOrder (masterBlockGroup W) then 3 else 4
  else 2

theorem polyFun_masterWindowGroup : PolyFun masterWindowGroup :=
  (polyFun_primitiveWindowInput.comp polyFun_fst).pair polyFun_fst

theorem polyFun_masterBlockGroup : PolyFun masterBlockGroup :=
  ((polyFun_masterWindowBlockAction.comp polyFun_snd).comp polyFun_snd).pair
    ((polyFun_masterWindowBlockAction.comp polyFun_snd).comp polyFun_fst)

theorem polyFun_masterReduceRoute (B C₀ : ℕ) : PolyFun (masterReduceRoute B C₀) := by
  have ha := polyFun_primitiveWindowInput.comp polyFun_masterAutTest
  have ho := (polyFun_masterWindowGroup.comp polyFun_swap).comp polyFun_rawOrder
  have hs := (ho.add (polyFun_const 1)).le (polyFun_const C₀)
  have ht := polyFun_masterWindowGroup.comp polyFun_rawIsTransitive
  have hb := (((polyFun_masterBlockGroup.comp polyFun_snd).comp polyFun_length).add
    (polyFun_const 1)).le (polyFun_const B)
  have hm := polyFun_masterBlockGroup.comp polyFun_masterSmallOrder
  exact (PolyFun.ite ha (polyFun_const 0) (PolyFun.ite hs (polyFun_const 1)
    (PolyFun.ite ht (PolyFun.ite hb (polyFun_const 3)
      (PolyFun.ite hm (polyFun_const 3) (polyFun_const 4))) (polyFun_const 2)))).of_eq
        (fun W => by simp only [masterReduceRoute, decide_eq_true_eq, Nat.add_one_le_iff])

theorem masterReduceRoute_trivial (B C₀ : ℕ) (W : RawWinSI) :
    masterReduceRoute B C₀ W = 0 ↔ masterAutTest (primitiveWindowInput W) = true := by
  unfold masterReduceRoute
  split_ifs <;> simp_all

theorem masterReduceRoute_brute (B C₀ : ℕ) (W : RawWinSI) :
    masterReduceRoute B C₀ W = 1 ↔ masterAutTest (primitiveWindowInput W) = false ∧
      rawOrder ((masterWindowGroup W).2, (masterWindowGroup W).1) < C₀ := by
  unfold masterReduceRoute
  split_ifs <;> simp_all

theorem masterReduceRoute_chain (B C₀ : ℕ) (W : RawWinSI) :
    masterReduceRoute B C₀ W = 2 ↔ masterAutTest (primitiveWindowInput W) = false ∧
      C₀ ≤ rawOrder ((masterWindowGroup W).2, (masterWindowGroup W).1) ∧
      rawIsTransitive (masterWindowGroup W) = false := by
  unfold masterReduceRoute
  split_ifs <;> simp_all

theorem masterReduceRoute_block (B C₀ : ℕ) (W : RawWinSI) :
    masterReduceRoute B C₀ W = 3 ↔ masterAutTest (primitiveWindowInput W) = false ∧
      C₀ ≤ rawOrder ((masterWindowGroup W).2, (masterWindowGroup W).1) ∧
      rawIsTransitive (masterWindowGroup W) = true ∧
      ((masterBlockGroup W).2.length < B ∨ masterSmallOrder (masterBlockGroup W) = true) := by
  unfold masterReduceRoute
  split_ifs <;> simp_all

theorem masterReduceRoute_cameron (B C₀ : ℕ) (W : RawWinSI) :
    masterReduceRoute B C₀ W = 4 ↔ masterAutTest (primitiveWindowInput W) = false ∧
      C₀ ≤ rawOrder ((masterWindowGroup W).2, (masterWindowGroup W).1) ∧
      rawIsTransitive (masterWindowGroup W) = true ∧
      B ≤ (masterBlockGroup W).2.length ∧ masterSmallOrder (masterBlockGroup W) = false := by
  unfold masterReduceRoute
  split_ifs <;> simp_all

/-- The branch test itself supplies the real order premise for the next phase. -/
theorem masterReduceRoute_cameron_order {n B C₀ : ℕ} {W : RawWinSI}
    (hx : W.2.2.2.1.length = n) (hw : RawGens.WF n W.2.1)
    (hnd : W.1.Nodup) (hlt : ∀ u ∈ W.1, u < n)
    (hinv : IsInvariant (decGroup n W.2.1) (winSet n W.1))
    (hn : 2 ≤ W.1.length) (hB : 1 ≤ B) (hr : masterReduceRoute B C₀ W = 4) :
    ((masterBlockGroup W).2.length : ℝ) ^ (1 + Real.logb 2 (masterBlockGroup W).2.length) ≤
      Nat.card (decGroup (masterBlockGroup W).2.length (masterBlockGroup W).1) := by
  obtain ⟨_, _, ht, hm, ho⟩ := (masterReduceRoute_cameron B C₀ W).mp hr
  have hgs := rawRestrictGens_wf_of_raw (dom := W.2.2.2.1) hw hnd hlt hinv
  have htr := (rawIsTransitive_eq_true_iff hgs rfl).mp ht
  have hp := masterWindowBlockAction_wf hx hw hnd hlt hinv htr hn
  exact masterSmallOrder_false rfl (hp.2.1 ▸ hp.2.2.2.1) (hB.trans hm) ho
end Algo
