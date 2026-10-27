import Workspace.Algo.TopWindowTransport

/-! # A bounded raw carrier for the restricted top-action phase

The state is the supplied top-action state on the restricted domain. Each
recursive call is lifted as a full coset instance, and its answer is restricted
before the fold continues. A concrete size guard makes every child bounded
on arbitrary states. The next theorem chooses a fixed polynomial for which
that guard accepts every child actually constructed by this adapter.
-/
set_option synthInstance.maxSize 1024
namespace Algo
open RAM RAM.Targets Babai Equiv

abbrev TopwpContext := TopwContext × TopcsInput
abbrev TopwpNode := TopwpContext × Option RawWinSI

 theorem topwp_child_bound : ∃ e f : ℕ, ∀ (C : TopwpContext) (t i : ℕ)
    (q : RawGens × RawPerm) (W : RawWinSI),
    topwRawInstance (C.1, topcsLeaf C.2 t i q) = some W →
      Enc.size W ≤ topcsContextCap e f (Enc.size C) := by
  obtain ⟨F, hF, hmF, hsF⟩ := polyFun_topwRawInstance.size.exists_polyBound
  have hV : PolyBound (fun N => 2 * N + 128 * (N + chainBound N + 1)) :=
    ((polyBound_const 2).mul polyBound_id).add ((polyBound_const 128).mul
      ((polyBound_id.add polyBound_chainBound).add (polyBound_const 1)))
  obtain ⟨e, f, hcap⟩ := hF.comp hV
  refine ⟨e, f, ?_⟩
  intro C t i q W hW
  have hC := size_fst_le' C
  have hP := size_snd_le' C
  have hk : (topcsX C.2).length ≤ Enc.size C :=
    (length_le_size _).trans ((topcsFields_size C.2).1.trans hP)
  have hleaf := size_topcsLeaf (P := C.2) rfl t i q
  have hmono := mono_chainBound hk
  have hin := Combine.size_pair_le C.1 (topcsLeaf C.2 t i q)
  have hout := hsF (C.1, topcsLeaf C.2 t i q)
  rw [hW, size_some_eq] at hout
  have hinput : Enc.size (C.1, topcsLeaf C.2 t i q) ≤
      2 * Enc.size C + 128 * (Enc.size C + chainBound (Enc.size C) + 1) := by omega
  exact (by omega : Enc.size W ≤ F (Enc.size (C.1, topcsLeaf C.2 t i q))).trans
    ((hmF _ _ hinput).trans (hcap (Enc.size C)))

 def topwpAccept (e f : ℕ) (p : TopwpContext × RawWinSI) : Option TopwpNode :=
  if Enc.size p.2 ≤ topcsContextCap e f (Enc.size p.1) then some (p.1, some p.2) else none

 def topwpChild (e f : ℕ) (z : TopwpNode × ℕ × TopcsState) : Option TopwpNode :=
  z.1.2.elim
    ((topcsChild ((z.1.1.2, none), z.2.1, z.2.2)).bind fun J =>
      J.2.bind fun W => (topwRawInstance (z.1.1.1, W)).bind fun V => topwpAccept e f (z.1.1, V))
    (fun _ => none)

 def topwpInit (I : TopwpNode) : TopcsState := topcsInit (I.1.2, none)
 def topwpCombine (z : TopwpNode × ℕ × TopcsState × RawCoset) : TopcsState :=
  topcsCombine ((z.1.1.2, none), z.2.1, z.2.2.1,
    topwCosetImage (z.1.1.1.1.1, z.1.1.1.2.1, z.2.2.2))
 def topwpFinish (solve : RawWinSI → RawCoset) (z : TopwpNode × TopcsState) : RawCoset :=
  top2NormC z.1.1.1.2.2
    (z.1.2.elim
      (topwCosetPreimage (z.1.1.1.1, z.1.1.1.2.1, (topcsAnswer z.1.1.2 z.2).getD none)) solve)

noncomputable def topwpDecode (n : ℕ) (I : TopwpNode) : SIInstance (Fin n) ℕ :=
  I.2.elim ⟨decGroup n I.1.1.1.2, winSet n I.1.1.2.1,
    decStrN n I.1.1.2.2, decStrN n I.1.1.2.2⟩ (decWinSI n)

 def TopwpWF (c d e f : ℕ) (I : TopwpNode) : Prop :=
  Enc.size I.1 ≤ topcsContextCap c d I.1.1.2.2.length ∧
    ∀ W, I.2 = some W → Enc.size W ≤ topcsContextCap e f (Enc.size I.1)

 theorem topwpChild_some {e f : ℕ} {z : TopwpNode × ℕ × TopcsState} {J : TopwpNode}
    (h : topwpChild e f z = some J) :
    z.1.2 = none ∧ ∃ W, J = (z.1.1, some W) ∧
      Enc.size W ≤ topcsContextCap e f (Enc.size z.1.1) := by
  cases ho : z.1.2 with
  | some W => simp [topwpChild, ho] at h
  | none =>
    simp only [topwpChild, ho, Option.elim_none] at h
    obtain ⟨J', _, hJ⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨W, _, hW⟩ := Option.bind_eq_some_iff.mp hJ
    obtain ⟨V, _, hV⟩ := Option.bind_eq_some_iff.mp hW
    unfold topwpAccept at hV
    split at hV
    next hsize => exact ⟨rfl, V, (Option.some.inj hV).symm, hsize⟩
    next => simp at hV

 def topwpRound (c d e f : ℕ) (solve : RawWinSI → RawCoset) :
    Round TopwpNode TopcsState RawCoset where
  WF := TopwpWF c d e f
  ground := fun I => I.1.1.2.2.length
  measure := fun I => I.2.elim 1 (fun _ => 0)
  width := fun I => I.2.elim (topcsJobs I.1.2 * (topcsWins I.1.2).length) (fun _ => 0)
  child := topwpChild e f
  init := topwpInit
  combine := topwpCombine
  finish := topwpFinish solve
  bot := none
  child_eq_none := by
    intro I j s hj
    cases ho : I.2 with
    | some W => simp [topwpChild, ho]
    | none =>
      rw [ho] at hj
      simp only [topwpChild, ho, Option.elim_none]
      have hn := (topcsRound 0 (fun _ => 0) solve).child_eq_none (I.1.2, none) j s hj
      change topcsChild ((I.1.2, none), j, s) = none at hn
      rw [hn]
      rfl
  child_wf := by
    intro I j s J hI hc
    obtain ⟨_, W, rfl, hW⟩ := topwpChild_some hc
    exact ⟨hI.1, fun V hV => by cases Option.some.inj hV; exact hW⟩
  child_measure := by
    intro I j s J _ hc
    obtain ⟨ho, W, rfl, _⟩ := topwpChild_some hc
    change 0 < I.2.elim 1 (fun _ => 0)
    rw [ho]
    exact Nat.zero_lt_one
  child_ground := by
    intro I j s J _ hc
    obtain ⟨_, W, rfl, _⟩ := topwpChild_some hc
    exact le_rfl

end Algo
