import Workspace.Algo.TopMasterChainCost

/-! # Exact matching of the degree-uniform orbit chain -/
namespace Algo
open Babai Equiv
open scoped Pointwise

section Match

variable {n : ℕ} {P : MasterChainInput}

theorem masterChainDecode_leaf (hx : (masterChainX P).length = n) (j : ℕ) (c : RawGens × RawPerm) :
    masterChainDecode n (P, some (masterChainLeaf (P, j, c))) =
      ⟨decCoset n (some c), winSet n (P.2.getD j []), decStrN n P.1.2.2.2.1, decStrN n P.1.2.2.2.2⟩ := by
  exact topclDecode_leaf (P := masterChainArray P) hx j c

/-- The raw fold matches each call, with the same strings and candidate set.
Only the decoding of each answer is required, not its representation. -/
theorem masterChainPhase_chain (a b : ℕ) (solve : RawWinSI → RawCoset) (hx : (masterChainX P).length = n) :
    ∀ Δs C j s, topclInv n (masterChainArray P) Δs C j s →
      PhaseMatch (masterChainRound a b solve) (masterChainDecode n) (decCoset n) (P, none)
        Δs.length j s (Babai.cosetChain (decStrN n P.1.2.2.2.1) (decStrN n P.1.2.2.2.2) Δs C)
        (fun C' j' s' => topclInv n (masterChainArray P) [] C' j' s') := by
  intro Δs C j s h
  rw [← aggrCosetChain_eq]
  refine phaseMatch_cosetChain _ _ (topclInv n (masterChainArray P)) ?_ ?_ Δs C j s h
  · intro Δ rest C j s h hC
    obtain ⟨hs, hlist⟩ := h
    have he := hlist.resolve_right hC
    change Δ :: rest = (P.2.drop j).map (winSet n) at he
    have hj : j < P.2.length := by
      by_contra hj
      rw [List.drop_eq_nil_of_le (by omega), List.map_nil] at he
      cases he
    rw [List.drop_eq_getElem_cons hj, List.map_cons] at he
    obtain ⟨rfl, rfl⟩ := List.cons.inj he
    obtain ⟨q, rfl⟩ : ∃ q, s = some q := by
      cases s with
      | none => exact (hC hs.symm).elim
      | some q => exact ⟨q, rfl⟩
    refine ⟨(P, some (masterChainLeaf (P, j, q))), ?_, ?_, ?_⟩
    · change masterChainChild ((P, none), j, some q) = _
      simp only [masterChainChild, Option.elim_none, if_pos hj, Option.map_some]
    · rw [masterChainDecode_leaf hx, List.getD_eq_getElem _ _ hj, hs]
    · intro a ha
      exact ⟨(decCoset_top2NormC hx a).trans ha, Or.inl rfl⟩
  · intro Δs C j s h he
    exact ⟨h.1.trans he, Or.inr rfl⟩

theorem masterChainInv_finish (a b : ℕ) (solve : RawWinSI → RawCoset)
    (hx : (masterChainX P).length = n) {C : Set (Perm (Fin n))} {j : ℕ} {s : RawCoset} (h : topclInv n (masterChainArray P) [] C j s) :
    (masterChainRound a b solve).child ((P, none), j, s) = none ∧
      decCoset n ((masterChainRound a b solve).finish ((P, none), s)) = C := by
  refine ⟨?_, (decCoset_top2NormC hx s).trans h.1⟩
  change masterChainChild ((P, none), j, s) = none
  simp only [masterChainChild, Option.elim_none]
  rcases h.2 with hw | he
  · have hh := congrArg List.length hw
    simp only [List.length_nil, List.length_map] at hh
    change 0 = (P.2.drop j).length at hh
    rw [List.length_drop] at hh
    rw [if_neg (by omega)]
  · have hs : s = none := by
      cases s with
      | none => rfl
      | some q =>
        have hm : decPerm n q.2 ∈ decCoset n (some q) :=
          ⟨1, one_mem _, by rw [mul_one]⟩
        rw [h.1, he] at hm
        exact hm.elim
    simp [hs]

/-- Exact matching of the complete local chain, including its stopping rule. -/
theorem masterChainLoop_chain (a b : ℕ) (solve : RawWinSI → RawCoset) (hx : (masterChainX P).length = n) :
    LoopMatch (masterChainRound a b solve) (masterChainDecode n) (decCoset n) (P, none)
      P.2.length 0 (masterChainInit (P, none))
      (Babai.cosetChain (decStrN n P.1.2.2.2.1) (decStrN n P.1.2.2.2.2)
        (P.2.map (winSet n)) (decCoset n (masterChainArray P).2.2.2)) := by
  apply loopMatch_of_phaseMatch (masterChainPhase_chain a b solve hx _ _ _ _ ⟨decCoset_top2NormC hx _, Or.inl rfl⟩)
    (fun _ _ _ h => masterChainInv_finish a b solve hx h)
  simp [masterChainArray]

end Match

end Algo
