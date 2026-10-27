import Workspace.Algo.TopMasterDescentCost

/-! # Exact phase matching for the computed Luks descent -/
namespace Algo
open RAM RAM.Targets Babai Equiv
open scoped Pointwise

section Match
variable (a b c d : ℕ) (solve : RawWinSI → RawCoset)
  {n : ℕ} {p : MasterDescInput} (hx : (masterDescX p).length = n)

include hx in
theorem masterDesc_loop_from : ∀ (w j : ℕ) (s : RawCoset), j + w = masterDescWidth p →
    LoopMatch (masterDescRound a b c d solve) (masterDescDecode n) (decCoset n) (p, none) w j s
      (descentChain (decGroup n (topKernel (masterDescAction p))) (decWinSI n p.1).Δ
        (decWinSI n p.1).x (decWinSI n p.1).y (decCoset n s)
        ((List.range' j w).map (fun k => decPerm n (masterDescRep (p, k))))) := by
  intro w
  induction w with
  | zero =>
    intro j s hj
    simp only [List.range'_zero, List.map_nil, descentChain]
    exact .done 0 j s _ (by simp [masterDescRound, masterDescChild]; omega)
      (decCoset_top2NormC hx s)
  | succ w ih =>
    intro j s hj
    have hj' : j < masterDescWidth p := by omega
    rw [List.range'_succ, List.map_cons, descentChain]
    rw [← masterDescJob_spec (p := p) (n := n) j]
    change LoopMatch _ _ _ _ _ _ _ (.call
      (masterDescDecode n (p, some (masterDescJob (p, j)))) _)
    refine .call w j s (p, some (masterDescJob (p, j))) _
      (by simp [masterDescRound, masterDescChild, hj']) ?_
    intro z hz
    have hh := ih (j + 1) (masterDescCombine ((p, none), j, s, z)) (by omega)
    have he : decCoset n (masterDescCombine ((p, none), j, s, z)) =
        cosetHull (decCoset n s ∪ (masterDescDecode n (p, some (masterDescJob (p, j)))).answer) := by
      change decCoset n (top2NormC (masterDescX p) (rawCosetJoin (masterDescX p, s, z))) = _
      rw [decCoset_top2NormC hx, decCoset_rawCosetJoin hx, hz]
    rw [he] at hh
    exact hh

include hx in
/-- The actual ordered jobs and every returned representative are retained. -/
theorem masterDesc_loop :
    LoopMatch (masterDescRound a b c d solve) (masterDescDecode n) (decCoset n)
      (masterDescEnter p) (masterDescWidth p) 0 none (masterDescTree n p) := by
  simpa only [masterDescEnter, masterDescTree, masterDescPerms, List.range_eq_range', decCoset]
    using masterDesc_loop_from a b c d solve hx (masterDescWidth p) 0 none (Nat.zero_add _)
end Match

/-- The hull fold never changes the number or order of recursive calls. -/
theorem masterDescChain_calls {Ω A : Type*} (H : Set (Perm Ω)) (Δ : Set Ω) (x y : Ω → A)
    (L : List (Perm Ω)) (acc : Set (Perm Ω)) :
    (descentChain H Δ x y acc L).calls = L.map (fun σ => (⟨σ • H, Δ, x, y⟩ : SIInstance Ω A)) := by
  induction L generalizing acc with
  | nil => rfl
  | cons σ L ih => simp only [descentChain, SIReduction.calls_call, List.map_cons, ih]

theorem masterDescTree_calls (n : ℕ) (p : MasterDescInput) :
    (masterDescTree n p).calls.length = masterDescWidth p := by
  rw [masterDescTree, masterDescChain_calls]
  simp [masterDescPerms]

theorem masterDescEnter_wf {a b c d : ℕ} {p : MasterDescInput}
    (hs : Enc.size p ≤ topcsContextCap a b (masterDescX p).length)
    (hw : masterDescWidth p ≤ topcsContextCap c d (masterDescX p).length) :
    MasterDescWF a b c d (masterDescEnter p) :=
  ⟨hs, hw, fun _ h => by contradiction⟩
end Algo
