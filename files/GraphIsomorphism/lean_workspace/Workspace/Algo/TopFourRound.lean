import Workspace.Algo.TopWindowPhaseCost
import Workspace.Algo.PhaseChain

/-! # The two phases of the supplied top-action 4 round
The restricted top-action phase runs first. Its result is lifted to the
ambient group, then the Chain Rule processes the supplied remaining
windows in order. No recursive call is inserted between the two phases.
-/
set_option synthInstance.maxSize 2048
namespace Algo
open RAM RAM.Targets Babai Equiv

abbrev Top4Context := TopwpContext × (List (List ℕ) × RawStr)
abbrev Top4Node := Top4Context × Option RawWinSI
abbrev Top4State := TopcsState × ℕ × RawCoset

def top4X (C : Top4Context) : RawStr := C.1.1.2.2
def top4Y (C : Top4Context) : RawStr := C.2.2
def top4Wins (C : Top4Context) : List (List ℕ) := C.2.1
def top4Base (C : Top4Context) : ℕ := topcsJobs C.1.2 * (topcsWins C.1.2).length
def top4Width (C : Top4Context) : ℕ := top4Base C + (top4Wins C).length

def top4Open (C : Top4Context) (s : TopcsState) : Top4State :=
  (s, 0, top2NormC (top4X C)
    (topwCosetPreimage (C.1.1.1, C.1.1.2.1, (topcsAnswer C.1.2 s).getD none)))
def top4Closed (C : Top4Context) : TopcsState :=
  (topcsJobs C.1.2, 0, none, none, none, none)
def top4Leaf (C : Top4Context) (i : ℕ) (q : RawGens × RawPerm) : RawWinSI :=
  ((top4Wins C).getD i [], tidyGens (top4X C, q.1), normPerm (top4X C, q.2), top4X C, top4Y C)
def top4Child (e f : ℕ) (z : Top4Node × ℕ × Top4State) : Option Top4Node :=
  z.1.2.elim
    (if z.2.1 < top4Width z.1.1 then
      if z.2.2.1.1 < topcsJobs z.1.1.1.2 then
        (topwpChild e f ((z.1.1.1, none), z.2.1, z.2.2.1)).map fun J => (z.1.1, J.2)
      else if z.2.2.2.1 < (top4Wins z.1.1).length then
        z.2.2.2.2.map fun q => (z.1.1, some (top4Leaf z.1.1 z.2.2.2.1 q))
      else none
    else none) (fun _ => none)
def top4Init (I : Top4Node) : Top4State := top4Open I.1 (topwpInit (I.1.1, none))
def top4Combine (z : Top4Node × ℕ × Top4State × RawCoset) : Top4State :=
  if z.2.2.1.1.1 < topcsJobs z.1.1.1.2 then
    top4Open z.1.1 (topwpCombine ((z.1.1.1, none), z.2.1, z.2.2.1.1, z.2.2.2))
  else (top4Closed z.1.1, min (z.2.2.1.2.1 + 1) (top4Wins z.1.1).length,
    top2NormC (top4X z.1.1) z.2.2.2)
def top4Finish (solve : RawWinSI → RawCoset) (z : Top4Node × Top4State) : RawCoset :=
  top2NormC (top4X z.1.1) (z.1.2.elim z.2.2.2 solve)
noncomputable def top4Decode (n : ℕ) (I : Top4Node) : SIInstance (Fin n) ℕ :=
  I.2.elim ⟨decGroup n I.1.1.1.1.2, Set.univ, decStrN n (top4X I.1), decStrN n (top4Y I.1)⟩ (decWinSI n)
def top4LeafCap (e f : ℕ) (N : ℕ) : ℕ :=
  topcsContextCap e f N + 64 * (N + chainBound N + 1)
def Top4WF (c d e f : ℕ) (I : Top4Node) : Prop :=
  Enc.size I.1 ≤ topcsContextCap c d (top4X I.1).length ∧
    ∀ W, I.2 = some W → Enc.size W ≤ top4LeafCap e f (Enc.size I.1)

 theorem size_top4Leaf (C : Top4Context) (i : ℕ) (q : RawGens × RawPerm) :
    Enc.size (top4Leaf C i q) ≤ 64 * (Enc.size C + chainBound (Enc.size C) + 1) := by
  have hx : Enc.size (top4X C) ≤ Enc.size C :=
    (size_snd_le' C.1.1.2).trans ((size_snd_le' C.1.1).trans ((size_fst_le' C.1).trans (size_fst_le' C)))
  have hy := (size_snd_le' C.2).trans (size_snd_le' C)
  have hw := (size_fst_le' C.2).trans (size_snd_le' C)
  have hd : Enc.size ((top4Wins C).getD i []) ≤ Enc.size C + 1 := by
    by_cases hi : i < (top4Wins C).length
    · have hm : (top4Wins C).getD i [] ∈ top4Wins C := by
        rw [List.getD_eq_getElem _ _ hi]
        exact List.getElem_mem _
      have hh := size_mem_le hm
      change Enc.size (top4Wins C) ≤ Enc.size C at hw
      omega
    · rw [List.getD_eq_default _ _ (by omega)]
      exact Nat.succ_le_succ (Nat.zero_le _)
  have hg : Enc.size (tidyGens (top4X C, q.1)) ≤ gensBound (top4X C).length :=
    size_gens_le' le_rfl (wf_tidyGens rfl _) (length_tidyGens rfl _)
  have hr : Enc.size (normPerm (top4X C, q.2)) ≤ strBound (top4X C).length :=
    size_perm_le' le_rfl (wf_normPerm rfl _)
  have hsg := strBound_le_gensBound (top4X C).length
  have hn : (top4X C).length ≤ Enc.size C := (length_le_size _).trans hx
  have hchain := mono_chainBound hn
  have hs := Combine.size_pair_le ((top4Wins C).getD i [])
    (tidyGens (top4X C, q.1), normPerm (top4X C, q.2), top4X C, top4Y C)
  have hs1 := Combine.size_pair_le (tidyGens (top4X C, q.1))
    (normPerm (top4X C, q.2), top4X C, top4Y C)
  have hs2 := Combine.size_pair_le (normPerm (top4X C, q.2)) (top4X C, top4Y C)
  have hs3 := Combine.size_pair_le (top4X C) (top4Y C)
  change Enc.size (top4Y C) ≤ Enc.size C at hy
  change Enc.size (((top4Wins C).getD i [], tidyGens (top4X C, q.1), normPerm (top4X C, q.2), top4X C, top4Y C) : RawWinSI) ≤ _
  have hcb : chainBound (top4X C).length = 16 * (gensBound (top4X C).length + (top4X C).length + 1) := rfl
  omega

 theorem top4Child_some {e f : ℕ} {z : Top4Node × ℕ × Top4State} {J : Top4Node}
    (h : top4Child e f z = some J) :
    z.1.2 = none ∧ ∃ W, J = (z.1.1, some W) ∧
      Enc.size W ≤ top4LeafCap e f (Enc.size z.1.1) := by
  cases ho : z.1.2 with
  | some W => simp [top4Child, ho] at h
  | none =>
    simp only [top4Child, ho, Option.elim_none] at h
    split at h
    next =>
      split at h
      next =>
        obtain ⟨J', hc, hJ⟩ := Option.map_eq_some_iff.mp h
        obtain ⟨_, W, rfl, hW⟩ := topwpChild_some hc
        refine ⟨rfl, W, hJ.symm, ?_⟩
        have hm := mono_topcsContextCap e f (size_fst_le' z.1.1)
        dsimp only at hW
        unfold top4LeafCap
        omega
      next =>
        split at h
        next =>
          obtain ⟨q, _, hJ⟩ := Option.map_eq_some_iff.mp h
          exact ⟨rfl, _, hJ.symm, (size_top4Leaf _ _ _).trans (Nat.le_add_left _ _)⟩
        next => simp at h
    next => simp at h

 def top4Round (c d e f : ℕ) (solve : RawWinSI → RawCoset) : Round Top4Node Top4State RawCoset where
  WF := Top4WF c d e f
  ground := fun I => (top4X I.1).length
  measure := fun I => I.2.elim 1 (fun _ => 0)
  width := fun I => I.2.elim (top4Width I.1) (fun _ => 0)
  child := top4Child e f
  init := top4Init
  combine := top4Combine
  finish := top4Finish solve
  bot := none
  child_eq_none := by
    intro I j s hj
    cases ho : I.2 with
    | some W => simp [top4Child, ho]
    | none =>
      rw [ho] at hj
      simp only [Option.elim_none] at hj
      simp [top4Child, ho, not_lt.mpr hj]
  child_wf := by
    intro I j s J hI hc
    obtain ⟨_, W, rfl, hW⟩ := top4Child_some hc
    exact ⟨hI.1, fun V hV => by cases Option.some.inj hV; exact hW⟩
  child_measure := by
    intro I j s J _ hc
    obtain ⟨ho, W, rfl, _⟩ := top4Child_some hc
    change 0 < I.2.elim 1 (fun _ => 0)
    rw [ho]
    exact Nat.zero_lt_one
  child_ground := by
    intro I j s J _ hc
    obtain ⟨_, W, rfl, _⟩ := top4Child_some hc
    exact le_rfl

end Algo
