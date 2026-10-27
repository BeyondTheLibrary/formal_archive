import Workspace.Algo.TopSuppliedCost
import Workspace.Algo.AggNodeSizeRoutine

/-! # One executable top-action carrier for every degree

The carrier reads its degree from the retained source string. Its validity
test computes the concrete sizes of the product, list and option encodings.
All bounds and RAM programs are selected before the input degree.
-/

set_option synthInstance.maxSize 1024

namespace Algo
open RAM RAM.Targets Babai Equiv

 def topcsContextCap (c d n : ℕ) : ℕ := c * (n + 1) ^ d
 def topcsLeafCap (P : TopcsInput) : ℕ :=
  64 * (Enc.size P + chainBound (topcsX P).length + 1)
 def TopcsUniformWF (c d : ℕ) (I : TopcsNode) : Prop :=
  Enc.size I.1 ≤ topcsContextCap c d (topcsX I.1).length ∧
    ∀ W, I.2 = some W → Enc.size W ≤ topcsLeafCap I.1
 def topcsUniformCheck (c d : ℕ) (I : TopcsNode) : Bool :=
  decide (Enc.size I.1 ≤ topcsContextCap c d (topcsX I.1).length) &&
    I.2.elim true (fun W => decide (Enc.size W ≤ topcsLeafCap I.1))

 theorem topcsUniformCheck_spec (c d : ℕ) (I : TopcsNode) :
    topcsUniformCheck c d I = true ↔ TopcsUniformWF c d I := by
  cases ho : I.2 <;> simp [topcsUniformCheck, TopcsUniformWF, ho]

/-- Normalizing the recursive solver's output enforces the answer bound on
all leaves and preserves its decoded coset. -/
def topcsUniformFinish (solve : RawWinSI → RawCoset) (z : TopcsNode × TopcsState) : RawCoset :=
  top2NormC (topcsX z.1.1) (topcsFinish solve z)

 def topcsUniformRound (c d : ℕ) (solve : RawWinSI → RawCoset) :
    Round TopcsNode TopcsState RawCoset where
  WF := TopcsUniformWF c d
  ground := fun I => (topcsX I.1).length
  measure := fun I => I.2.elim 1 (fun _ => 0)
  width := fun I => I.2.elim (topcsJobs I.1 * (topcsWins I.1).length) (fun _ => 0)
  child := topcsChild
  init := topcsInit
  combine := topcsCombine
  finish := topcsUniformFinish solve
  bot := none
  child_eq_none := (topcsRound 0 (topcsContextCap c d) solve).child_eq_none
  child_wf := by
    intro I j s J hI hc
    obtain ⟨q, _, _, _, _, _, rfl⟩ := topcsChild_some hc
    refine ⟨hI.1, ?_⟩
    intro W hW
    cases Option.some.inj hW
    exact size_topcsLeaf rfl s.1 s.2.1 q
  child_measure := by
    intro I j s J _ hc
    obtain ⟨q, ho, _, _, _, _, rfl⟩ := topcsChild_some hc
    change 0 < I.2.elim 1 (fun _ => 0)
    rw [ho]
    exact Nat.zero_lt_one
  child_ground := by
    intro I j s J _ hc
    obtain ⟨q, _, _, _, _, _, rfl⟩ := topcsChild_some hc
    exact le_rfl

 theorem polyFun_topcsContextCap (c d : ℕ) : PolyFun (topcsContextCap c d) :=
  (polyFun_const c).mul (polyFun_powConst (polyFun_id.add (polyFun_const 1)) d)
 theorem polyBound_topcsContextCap (c d : ℕ) : PolyBound (topcsContextCap c d) :=
  polyBound_witness c d
 theorem mono_topcsContextCap (c d : ℕ) : Monotone (topcsContextCap c d) :=
  fun _ _ h => polyBound_witness_mono c d h

 theorem polyFun_topcsChainBound : PolyFun chainBound := by
  have hs : PolyFun strBound := (polyFun_const 1).add (polyFun_id.mul
    (((polyFun_const 2).mul (polyFun_id.add (polyFun_const 2))).add (polyFun_const 1)))
  have hg : PolyFun gensBound := (polyFun_const 1).add ((polyFun_id.mul polyFun_id).mul
    (((polyFun_const 2).mul hs).add (polyFun_const 1)))
  exact (polyFun_const 16).mul ((hg.add polyFun_id).add (polyFun_const 1))

 theorem polyFun_topcsLeafCap : PolyFun topcsLeafCap :=
  (polyFun_const 64).mul ((AggnSizeRoutine.polyFun_size.add
    ((polyFun_topcsX.comp polyFun_length).comp polyFun_topcsChainBound)).add (polyFun_const 1))

 theorem polyFun_topcsUniformCheck (c d : ℕ) : PolyFun (topcsUniformCheck c d) := by
  have hp : PolyFun (fun I : TopcsNode => I.1) := polyFun_fst
  have hs := hp.comp AggnSizeRoutine.polyFun_size
  have hn := (hp.comp polyFun_topcsX).comp polyFun_length
  have hctx := hs.le (hn.comp (polyFun_topcsContextCap c d))
  have hleaf : PolyFun (fun z : RawWinSI × TopcsNode =>
      decide (Enc.size z.1 ≤ topcsLeafCap z.2.1)) :=
    (polyFun_fst.comp AggnSizeRoutine.polyFun_size).le
      ((polyFun_snd.comp hp).comp polyFun_topcsLeafCap)
  have hopt := ((polyFun_snd.pair polyFun_id).comp
    (PolyFun.optionElim (polyFun_const true) hleaf))
  exact (PolyFun.ite hctx hopt (polyFun_const false)).of_eq (fun I => by
    simp only [topcsUniformCheck]
    cases decide (Enc.size I.1 ≤ topcsContextCap c d (topcsX I.1).length) <;> rfl)

 theorem quasiFun_topcsUniformFinish {solve : RawWinSI → RawCoset} (hs : QuasiFun solve) :
    QuasiFun (topcsUniformFinish solve) :=
  (((polyFun_fst.comp polyFun_fst).comp polyFun_topcsX).quasiFun.pair
    (quasiFun_topcsFinish hs)).comp polyFun_top2NormC.quasiFun

 theorem topcsUniform_size {c d : ℕ} {I : TopcsNode} (hI : TopcsUniformWF c d I) :
    Enc.size I ≤ topcsBound (topcsContextCap c d) (topcsX I.1).length := by
  have hp := size_pair_le' I
  cases ho : I.2 with
  | none =>
    have hs : Enc.size I.2 = 2 := by rw [ho, size_none]
    unfold topcsBound
    have := hI.1
    omega
  | some W =>
    have hw := hI.2 W ho
    have hs : Enc.size I.2 = Enc.size W + 2 := by rw [ho, size_some_eq]
    unfold topcsLeafCap at hw
    unfold topcsBound
    have := hI.1
    omega

/-- A single runnable carrier, independent of the degree. The chosen recursive
solver is itself one uniform RAM routine, and all its results are normalized. -/
def topcsUniformRunCostQ (c d : ℕ) (solve : RawWinSI → RawCoset) (hsolve : QuasiFun solve) :
    Round.RunCostQ (topcsUniformRound c d solve) where
  bound := topcsBound (topcsContextCap c d)
  polyBound_bound := polyBound_topcsBound (polyBound_topcsContextCap c d)
  mono_bound := mono_topcsBound (mono_topcsContextCap c d)
  stateBound := topcsBound (topcsContextCap c d)
  quasiPolyBound_stateBound := (polyBound_topcsBound (polyBound_topcsContextCap c d)).quasiPoly
  mono_stateBound := mono_topcsBound (mono_topcsContextCap c d)
  widthBound := fun n => (topcsContextCap c d n + 2) * topcsContextCap c d n
  quasiPolyBound_widthBound := (((polyBound_topcsContextCap c d).add
    (polyBound_const 2)).mul (polyBound_topcsContextCap c d)).quasiPoly
  quasiFun_child := polyFun_topcsChild.quasiFun
  quasiFun_init := polyFun_topcsInit.quasiFun
  quasiFun_combine := polyFun_topcsCombine.quasiFun
  quasiFun_finish := quasiFun_topcsUniformFinish hsolve
  ground_le := fun I => (length_le_size _).trans ((topcsFields_size I.1).1.trans (size_fst_le' I))
  size_le := fun _ hI => topcsUniform_size hI
  init_le := fun _ hI => size_topcsStored hI.1 (topcsInit_stored rfl)
  combine_le := fun _ _ _ _ hI _ _ => size_topcsStored hI.1 (topcsStep_stored rfl _ _ _ _ _ _)
  finish_le := by
    intro I s _ _
    have h := size_top2NormC_le (n := (topcsX I.1).length) rfl (le_refl _) (topcsFinish solve (I, s))
    change Enc.size (top2NormC (topcsX I.1) _) ≤ topcsBound (topcsContextCap c d) (topcsX I.1).length
    unfold topcsBound
    omega
  bot_le := by
    intro n
    change Enc.size (none : RawCoset) ≤ _
    rw [size_none]
    unfold topcsBound
    omega
  width_le := by
    intro I hI
    change I.2.elim _ (fun _ => 0) ≤ _
    cases I.2 with
    | some _ => exact Nat.zero_le _
    | none =>
      apply Nat.mul_le_mul
      · exact Nat.add_le_add_right ((topcsCount_le I.1).trans hI.1) 2
      · exact (topcsWins_length_le I.1).trans hI.1
  polyFun_ground := (polyFun_fst.comp polyFun_topcsX).comp polyFun_length
  wfCheck := topcsUniformCheck c d
  polyFun_wfCheck := polyFun_topcsUniformCheck c d
  wfCheck_eq_true := topcsUniformCheck_spec c d
  measureBound := fun _ => 1
  polyBound_measureBound := polyBound_const 1
  mono_measureBound := fun _ _ _ => le_rfl
  measure_le := by
    intro I _
    change I.2.elim 1 (fun _ => 0) ≤ 1
    cases I.2 <;> simp

 theorem topcsUniformLoopMatch {β : Type*} {n c d : ℕ} {B : ℕ → ℕ}
    {solve : RawWinSI → RawCoset} {I : TopcsNode} {w j : ℕ} {s : TopcsState}
    {T : SIReduction (Fin n) ℕ β} {Q : β → ℕ → ℕ → TopcsState → Prop}
    (h : LoopMatchK (topcsRound n B solve) (topcsDecode n) (decCoset n) I w j s T Q) :
    LoopMatchK (topcsUniformRound c d solve) (topcsDecode n) (decCoset n) I w j s T Q := by
  induction h with
  | done w j s b Q hQ => exact .done w j s b Q hQ
  | call w j s J k Q hc hn ih => exact .call w j s J k Q hc (fun a ha => ih a ha)

 theorem TopcsSpec.uniform_phase {n m c d : ℕ} {G : Subgroup (Perm (Fin n))}
    {P : TopcsInput} {ϕ : G →* Perm (Fin m)} {S : List (alternatingGroup (Fin m))}
    {O : TopActionOdd ϕ} {E : OrbitEnum (kerSubgroup ϕ)} {x y : Fin n → ℕ}
    (h : TopcsSpec P ϕ S O E x y) (solve : RawWinSI → RawCoset) (hn : 0 < n)
    (hϕ : IsGiantRep ϕ) (hS : Subgroup.closure {σ : alternatingGroup (Fin m) | σ ∈ S} = ⊤) :
    PhaseMatch (topcsUniformRound c d solve) (topcsDecode n) (decCoset n) (P, none)
      (topcsJobs P * (topcsWins P).length) 0 (topcsInit (P, none))
      (cosetTopAction3With ϕ S O E x y) (TopcsDone n P) :=
  fun r => topcsUniformLoopMatch (h.phase (topcsContextCap c d) solve hn hϕ hS r)

 theorem topcsUniformFinish_decode {n : ℕ} {I : TopcsNode}
    (hx : (topcsX I.1).length = n) (solve : RawWinSI → RawCoset) (s : TopcsState) :
    decCoset n (topcsUniformFinish solve (I, s)) = decCoset n (topcsFinish solve (I, s)) :=
  decCoset_top2NormC hx _

/-- A polynomial bound on raw input encodings gives one polynomial prepared
context cap, chosen before every degree and every input. -/
theorem topcsPrepare_uniform_cap (C D : ℕ) : ∃ c d : ℕ,
    ∀ n (p : TopcsRawInput), Enc.size p ≤ topcsContextCap C D n →
      Enc.size (topcsPrepare p) ≤ topcsContextCap c d n := by
  obtain ⟨F, hF, hmF, hs⟩ := polyFun_topcsPrepare.size.exists_polyBound
  obtain ⟨c, d, hcap⟩ := hF.comp (polyBound_topcsContextCap C D)
  exact ⟨c, d, fun n p hp => (hs p).trans ((hmF _ _ hp).trans (hcap n))⟩

theorem topcsUniformWF_prepared {c d n : ℕ} {p : TopcsRawInput}
    (hd : p.1.1.1.1.length = n)
    (hp : Enc.size (topcsPrepare p) ≤ topcsContextCap c d n) :
    TopcsUniformWF c d (topcsPrepare p, none) := by
  refine ⟨?_, fun W hW => by cases hW⟩
  change Enc.size (topcsPrepare p) ≤ topcsContextCap c d (fixStr _).length
  rwa [length_fixStr, hd]

end Algo
