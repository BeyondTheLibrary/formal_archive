import Workspace.Algo.TopFourOutput

/-! # Top-action 4 inside an ambient master window
The inner machine uses the explicit list labels of the window. Each call
is lifted to the original domain, and each returned coset is restricted
before the inner fold continues. The final coset is lifted once more.
-/
set_option synthInstance.maxSize 2048
namespace Algo
open RAM RAM.Targets Babai Equiv

abbrev Top4wContext := TopwContext × Top4aNode
abbrev Top4wNode := Top4wContext × Option RawWinSI

def top4wAccept (u v : ℕ) (p : Top4wContext × RawWinSI) : Option Top4wNode :=
  if Enc.size p.2 ≤ topcsContextCap u v (Enc.size p.1) then some (p.1, some p.2) else none

def top4wChild (e f u v : ℕ) (z : Top4wNode × ℕ × Top4State) : Option Top4wNode :=
  z.1.2.elim
    ((top4aChild e f (z.1.1.2, z.2)).bind fun J =>
      J.1.2.bind fun W => (topwRawInstance (z.1.1.1, W)).bind fun V => top4wAccept u v (z.1.1, V))
    (fun _ => none)

def top4wInit (I : Top4wNode) : Top4State := top4aInit I.1.2
def top4wCombine (z : Top4wNode × ℕ × Top4State × RawCoset) : Top4State :=
  top4aCombine (z.1.1.2, z.2.1, z.2.2.1,
    topwCosetImage (z.1.1.1.1.1, z.1.1.1.2.1, z.2.2.2))
def top4wFinish (solve : RawWinSI → RawCoset) (z : Top4wNode × Top4State) : RawCoset :=
  top2NormC z.1.1.1.2.2 (z.1.2.elim
    (topwCosetPreimage (z.1.1.1.1, z.1.1.1.2.1, top4aFinish solve (z.1.1.2, z.2))) solve)

noncomputable def top4wDecode (n : ℕ) (I : Top4wNode) : SIInstance (Fin n) ℕ :=
  I.2.elim ⟨decGroup n I.1.1.1.2, winSet n I.1.1.2.1,
    decStrN n I.1.1.2.2, decStrN n I.1.1.2.2⟩ (decWinSI n)

def Top4wWF (a b c d e f u v : ℕ) (I : Top4wNode) : Prop :=
  Enc.size I.1 ≤ topcsContextCap a b I.1.1.2.2.length ∧
    ∀ W, I.2 = some W → Enc.size W ≤ topcsContextCap u v (Enc.size I.1)

theorem top4wChild_some {e f u v : ℕ} {z : Top4wNode × ℕ × Top4State} {J : Top4wNode}
    (h : top4wChild e f u v z = some J) :
    z.1.2 = none ∧ ∃ W, J = (z.1.1, some W) ∧ Enc.size W ≤ topcsContextCap u v (Enc.size z.1.1) := by
  cases ho : z.1.2 with
  | some W => simp [top4wChild, ho] at h
  | none =>
    simp only [top4wChild, ho, Option.elim_none] at h
    obtain ⟨J', _, hJ⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨W, _, hW⟩ := Option.bind_eq_some_iff.mp hJ
    obtain ⟨V, _, hV⟩ := Option.bind_eq_some_iff.mp hW
    unfold top4wAccept at hV
    split at hV
    next hsize => exact ⟨rfl, V, (Option.some.inj hV).symm, hsize⟩
    next => simp at hV

def top4wRound (a b c d e f u v : ℕ) (solve : RawWinSI → RawCoset) :
    Round Top4wNode Top4State RawCoset where
  WF := Top4wWF a b c d e f u v
  ground := fun I => I.1.1.2.2.length
  measure := fun I => I.2.elim 1 (fun _ => 0)
  width := fun I => I.2.elim ((top4aRound c d e f solve).width I.1.2) (fun _ => 0)
  child := top4wChild e f u v
  init := top4wInit
  combine := top4wCombine
  finish := top4wFinish solve
  bot := none
  child_eq_none := by
    intro I j s hj
    cases ho : I.2 with
    | some W => simp [top4wChild, ho]
    | none =>
      rw [ho] at hj
      have hn := (top4aRound c d e f solve).child_eq_none I.1.2 j s hj
      change top4aChild e f (I.1.2, j, s) = none at hn
      simp [top4wChild, ho, hn]
  child_wf := by
    intro I j s J hI hc
    obtain ⟨_, W, rfl, hW⟩ := top4wChild_some hc
    exact ⟨hI.1, fun V hV => by cases Option.some.inj hV; exact hW⟩
  child_measure := by
    intro I j s J _ hc
    obtain ⟨ho, W, rfl, _⟩ := top4wChild_some hc
    change 0 < I.2.elim 1 (fun _ => 0)
    rw [ho]
    exact Nat.zero_lt_one
  child_ground := by
    intro I j s J _ hc
    obtain ⟨_, W, rfl, _⟩ := top4wChild_some hc
    exact le_rfl

def Top4wCap (e f u v : ℕ) : Prop := ∀ (C : Top4wContext) (j : ℕ) (s : Top4State)
    (J : Top4aNode) (W V : RawWinSI), top4aChild e f (C.2, j, s) = some J →
      J.1.2 = some W → topwRawInstance (C.1, W) = some V →
        Enc.size V ≤ topcsContextCap u v (Enc.size C)

theorem top4wCap_exists (e f : ℕ) : ∃ u v : ℕ, Top4wCap e f u v := by
  obtain ⟨F, hF, hmF, hsF⟩ := polyFun_topwRawInstance.size.exists_polyBound
  have hb : PolyBound (fun N => 4 * (N + top4LeafCap e f N + 1)) :=
    (polyBound_const 4).mul ((polyBound_id.add (polyBound_top4LeafCap e f)).add (polyBound_const 1))
  obtain ⟨u, v, huv⟩ := hF.comp hb
  refine ⟨u, v, ?_⟩
  intro C j s J W V hc hW hV
  obtain ⟨_, K, hK, rfl⟩ := top4aChild_some hc
  obtain ⟨_, W', rfl, hW'⟩ := top4Child_some hK
  cases Option.some.inj hW
  have hctx : Enc.size C.2.1.1 ≤ Enc.size C :=
    (size_fst_le' C.2.1).trans ((size_fst_le' C.2).trans (size_snd_le' C))
  have hleaf := hW'.trans (mono_top4LeafCap e f hctx)
  have hframe := size_fst_le' C
  have hp := Combine.size_pair_le C.1 W
  have hout := hsF (C.1, W)
  rw [hV, size_some_eq] at hout
  have hin : Enc.size (C.1, W) ≤ 4 * (Enc.size C + top4LeafCap e f (Enc.size C) + 1) := by omega
  exact (by omega : Enc.size V ≤ F (Enc.size (C.1, W))).trans
    ((hmF _ _ hin).trans (huv (Enc.size C)))

end Algo
