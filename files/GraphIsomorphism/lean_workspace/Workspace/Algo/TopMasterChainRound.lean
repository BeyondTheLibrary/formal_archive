import Workspace.Algo.TopMasterLeafChoices

/-! # A degree-uniform orbit-chain carrier
The context retains the parent window instance and the displayed ordered
windows. Each child uses the current candidate coset. Answers are normalized
before the next call, and empty candidates stop the chain as in Equation (64).
-/
namespace Algo
open RAM RAM.Targets Babai

abbrev MasterChainInput := RawWinSI × List (List ℕ)
abbrev MasterChainNode := MasterChainInput × Option RawWinSI

def masterChainX (p : MasterChainInput) : RawStr := p.1.2.2.2.1

def masterChainArray (p : MasterChainInput) : TopCosetChainInput :=
  (p.1.2.2.2.1, p.1.2.2.2.2, p.2, some (p.1.2.1, p.1.2.2.1))

def masterChainLeaf (q : MasterChainInput × ℕ × (RawGens × RawPerm)) : RawWinSI :=
  topclLeaf (masterChainArray q.1) q.2.1 q.2.2

def MasterChainWF (a b : ℕ) (I : MasterChainNode) : Prop :=
  Enc.size I.1 ≤ topcsContextCap a b (masterChainX I.1).length ∧
    ∀ W, I.2 = some W → Enc.size W ≤ masterDescJobBound (Enc.size I.1) ∧
      W.2.2.2.1.length = (masterChainX I.1).length

def masterChainChild (z : MasterChainNode × ℕ × RawCoset) : Option MasterChainNode :=
  z.1.2.elim
    (if z.2.1 < z.1.1.2.length then
      z.2.2.map (fun c => (z.1.1, some (masterChainLeaf (z.1.1, z.2.1, c))))
    else none) (fun _ => none)

def masterChainInit (I : MasterChainNode) : RawCoset :=
  top2NormC (masterChainX I.1) (masterChainArray I.1).2.2.2

def masterChainCombine (z : MasterChainNode × ℕ × RawCoset × RawCoset) : RawCoset :=
  top2NormC (masterChainX z.1.1) z.2.2.2

def masterChainFinish (solve : RawWinSI → RawCoset) (z : MasterChainNode × RawCoset) : RawCoset :=
  top2NormC (masterChainX z.1.1) (z.1.2.elim z.2 solve)

theorem masterChainLeaf_size (p : MasterChainInput) (j : ℕ) (c : RawGens × RawPerm) :
    Enc.size (masterChainLeaf (p, j, c)) ≤ masterDescJobBound (Enc.size p) := by
  let W := masterChainLeaf (p, j, c)
  have hn : (masterChainX p).length ≤ Enc.size p := (length_le_size _).trans
    ((size_fst_le' p.1.2.2.2).trans ((size_snd_le' p.1.2.2).trans
      ((size_snd_le' p.1.2).trans ((size_snd_le' p.1).trans (size_fst_le' p)))))
  have hg : Enc.size W.2.1 ≤ gensBound (Enc.size p) :=
    size_gens_le' hn (wf_tidyGens rfl _) (length_tidyGens rfl _)
  have hr : Enc.size W.2.2.1 ≤ strBound (Enc.size p) := size_perm_le' hn (wf_normPerm rfl _)
  have hΔ : Enc.size W.1 ≤ Enc.size p + 1 := by
    change Enc.size (p.2.getD j []) ≤ _
    by_cases hj : j < p.2.length
    · have hh := size_mem_le (List.getElem_mem hj)
      rw [List.getD_eq_getElem _ _ hj]
      exact hh.trans ((size_snd_le' p).trans (Nat.le_succ _))
    · rw [List.getD_eq_default _ _ (by omega)]
      exact Nat.succ_le_succ (Nat.zero_le _)
  have hxy : Enc.size W.2.2.2 ≤ Enc.size p :=
    (size_snd_le' p.1.2.2).trans ((size_snd_le' p.1.2).trans
      ((size_snd_le' p.1).trans (size_fst_le' p)))
  have h1 := size_pair_le' W
  have h2 := size_pair_le' W.2
  have h3 := size_pair_le' W.2.2
  change Enc.size W ≤ _
  unfold masterDescJobBound
  omega

theorem masterChainChild_some {z : MasterChainNode × ℕ × RawCoset} {J : MasterChainNode}
    (h : masterChainChild z = some J) :
    ∃ c, z.1.2 = none ∧ z.2.2 = some c ∧ z.2.1 < z.1.1.2.length ∧
      J = (z.1.1, some (masterChainLeaf (z.1.1, z.2.1, c))) := by
  cases ho : z.1.2 with
  | some W => simp [masterChainChild, ho] at h
  | none =>
    simp only [masterChainChild, ho, Option.elim_none] at h
    split_ifs at h with hj
    obtain ⟨c, hs, hJ⟩ := Option.map_eq_some_iff.mp h
    exact ⟨c, rfl, hs, hj, hJ.symm⟩

def masterChainRound (a b : ℕ) (solve : RawWinSI → RawCoset) :
    Round MasterChainNode RawCoset RawCoset where
  WF := MasterChainWF a b
  ground I := (masterChainX I.1).length
  measure I := I.2.elim 1 (fun _ => 0)
  width I := I.2.elim I.1.2.length (fun _ => 0)
  child := masterChainChild
  init := masterChainInit
  combine := masterChainCombine
  finish := masterChainFinish solve
  bot := none
  child_eq_none := by
    intro I j s hj
    unfold masterChainChild
    cases ho : I.2 with
    | some W => rfl
    | none =>
      rw [ho] at hj
      simp only [Option.elim_none]
      exact if_neg (Nat.not_lt.mpr hj)
  child_wf := by
    intro I j s J hI hJ
    obtain ⟨c, _, _, _, rfl⟩ := masterChainChild_some hJ
    refine ⟨hI.1, ?_⟩
    intro W hw
    cases Option.some.inj hw
    exact ⟨masterChainLeaf_size I.1 j c, rfl⟩
  child_measure := by
    intro I j s J _ hJ
    obtain ⟨c, ho, _, _, rfl⟩ := masterChainChild_some hJ
    change 0 < I.2.elim 1 (fun _ => 0)
    rw [ho]
    exact Nat.zero_lt_one
  child_ground := by
    intro I j s J _ hJ
    obtain ⟨c, _, _, _, rfl⟩ := masterChainChild_some hJ
    rfl

noncomputable def masterChainDecode (n : ℕ) (I : MasterChainNode) : SIInstance (Fin n) ℕ :=
  decWinSI n (I.2.getD I.1.1)

def masterChainEnter (W : RawWinSI) : MasterChainNode := ((W, winOrbits (W.2.1, W.1)), none)
end Algo
