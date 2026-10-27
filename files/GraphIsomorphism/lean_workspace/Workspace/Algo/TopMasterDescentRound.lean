import Workspace.Algo.TopMasterDescentRaw

/-! # A uniform carrier for action-kernel descent
The degree is read from the retained source string. Every job has the
same strings and window and has shortened subgroup generators. The only
recursive work is the displayed ordered list of candidate cosets.
-/
namespace Algo
open RAM RAM.Targets Babai

abbrev MasterDescNode := MasterDescInput × Option RawWinSI

def masterDescX (p : MasterDescInput) : RawStr := p.1.2.2.2.1

def masterDescJobBound (s : ℕ) : ℕ := 16 * (s + gensBound s + strBound s + 4)

theorem polyBound_masterDescJobBound : PolyBound masterDescJobBound :=
  (polyBound_const 16).mul ((((polyBound_id.add polyBound_gensBound).add polyBound_strBound).add
    (polyBound_const 4)))

theorem mono_masterDescJobBound : Monotone masterDescJobBound := by
  intro n m h
  have := mono_gensBound h
  have := mono_strBound h
  unfold masterDescJobBound
  omega

theorem masterDescJob_size (p : MasterDescInput) (j : ℕ) :
    Enc.size (masterDescJob (p, j)) ≤ masterDescJobBound (Enc.size p) := by
  let W := masterDescJob (p, j)
  let n := (masterDescX p).length
  have hx : p.1.2.2.2.1.length = n := rfl
  have hn : n ≤ Enc.size p := (length_le_size _).trans
    ((size_fst_le' p.1.2.2.2).trans ((size_snd_le' p.1.2.2).trans
      ((size_snd_le' p.1.2).trans ((size_snd_le' p.1).trans (size_fst_le' p)))))
  have hg : Enc.size W.2.1 ≤ gensBound (Enc.size p) :=
    size_gens_le' hn (wf_tidyGens hx _) (length_tidyGens hx _)
  have hr : Enc.size W.2.2.1 ≤ strBound (Enc.size p) :=
    size_perm_le' hn (wf_rawMul (wf_normPerm hx _) (wf_normPerm hx _))
  have hΔ : Enc.size W.1 ≤ Enc.size p := (size_fst_le' p.1).trans (size_fst_le' p)
  have hxy : Enc.size W.2.2.2 ≤ Enc.size p :=
    (size_snd_le' p.1.2.2).trans ((size_snd_le' p.1.2).trans
      ((size_snd_le' p.1).trans (size_fst_le' p)))
  have h1 := size_pair_le' W
  have h2 := size_pair_le' W.2
  have h3 := size_pair_le' W.2.2
  change Enc.size W ≤ _
  unfold masterDescJobBound
  omega

def MasterDescWF (a b c d : ℕ) (I : MasterDescNode) : Prop :=
  Enc.size I.1 ≤ topcsContextCap a b (masterDescX I.1).length ∧
    masterDescWidth I.1 ≤ topcsContextCap c d (masterDescX I.1).length ∧
    ∀ W, I.2 = some W → Enc.size W ≤ masterDescJobBound (Enc.size I.1) ∧
      W.2.2.2.1.length = (masterDescX I.1).length

def masterDescChild (p : MasterDescNode × ℕ × RawCoset) : Option MasterDescNode :=
  p.1.2.elim
    (if p.2.1 < masterDescWidth p.1.1 then some (p.1.1, some (masterDescJob (p.1.1, p.2.1)))
      else none) (fun _ => none)

def masterDescCombine (p : MasterDescNode × ℕ × RawCoset × RawCoset) : RawCoset :=
  masterDescJoin (masterDescX p.1.1, p.2.2.1, p.2.2.2)

def masterDescFinish (solve : RawWinSI → RawCoset) (p : MasterDescNode × RawCoset) : RawCoset :=
  top2NormC (masterDescX p.1.1) (p.1.2.elim p.2 solve)

theorem masterDescChild_some {I J : MasterDescNode} {j : ℕ} {s : RawCoset}
    (hh : masterDescChild (I, j, s) = some J) :
    I.2 = none ∧ j < masterDescWidth I.1 ∧ J = (I.1, some (masterDescJob (I.1, j))) := by
  unfold masterDescChild at hh
  cases ho : I.2 with
  | some W => simp [ho] at hh
  | none =>
    rw [ho] at hh
    simp only [Option.elim_none] at hh
    split_ifs at hh with hj
    · exact ⟨rfl, hj, (Option.some.inj hh).symm⟩

def masterDescRound (a b c d : ℕ) (solve : RawWinSI → RawCoset) :
    Round MasterDescNode RawCoset RawCoset where
  WF := MasterDescWF a b c d
  ground I := (masterDescX I.1).length
  measure I := I.2.elim 1 (fun _ => 0)
  width I := I.2.elim (masterDescWidth I.1) (fun _ => 0)
  child := masterDescChild
  init _ := none
  combine := masterDescCombine
  finish := masterDescFinish solve
  bot := none
  child_eq_none := by
    intro I j s hj
    unfold masterDescChild
    cases ho : I.2 with
    | some W => rfl
    | none =>
      rw [ho] at hj
      simpa using (if_neg (Nat.not_lt.mpr hj) :
        (if j < masterDescWidth I.1 then some (I.1, some (masterDescJob (I.1, j))) else none) = none)
  child_wf := by
    intro I j s J hI hJ
    obtain ⟨_, _, rfl⟩ := masterDescChild_some hJ
    refine ⟨hI.1, hI.2.1, ?_⟩
    intro W hw
    cases Option.some.inj hw
    exact ⟨masterDescJob_size I.1 j, rfl⟩
  child_measure := by
    intro I j s J _ hJ
    obtain ⟨ho, _, rfl⟩ := masterDescChild_some hJ
    simp [ho]
  child_ground := by
    intro I j s J _ hJ
    obtain ⟨_, _, rfl⟩ := masterDescChild_some hJ
    rfl

noncomputable def masterDescDecode (n : ℕ) (I : MasterDescNode) : SIInstance (Fin n) ℕ :=
  decWinSI n (I.2.getD I.1.1)

def masterDescEnter (p : MasterDescInput) : MasterDescNode := (p, none)
end Algo
