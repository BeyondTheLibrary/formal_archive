/-
An explicit running time for Theorem 1.1.1 (Babai, version 2.5): `Explicit.StepBounds` from the
node carrier under its state invariant, and the final theorem with the bounds of route 5 as
hypotheses. Not part of the faithful formalization.
-/
import Workspace.Explicit.CarriersInvDispatch
import Workspace.Explicit.NodeStep
import Workspace.Explicit.NodeEasy
import Workspace.Explicit.NodeCalls5
import Workspace.Explicit.NodeParams
import Workspace.Explicit.Tier2.Final
import Workspace.Explicit.Line1.Calls

/-!
# The step bounds from the node carrier

A run of the depth-first evaluator (`Algo.Round.stepDFS`) of the admitted round
`Algo.masterAdmittedRound a b F` from a good root of degree `n` keeps the invariant
`Explicit.RunInv`:

* every frame `(I, j, s)` of the stack is a good, well-formed node of degree `n`, its fold index
  is at most the width, its state satisfies the carrier's invariant `J n I j s`, and the fold
  still follows the node's reduction (`Algo.LoopMatchG`, whose value is the true answer);
* each frame is the child the frame below it asked for;
* a returned answer fits the input cap and decodes to the true answer of the child that asked.

The goodness of the children (and so their route predicate, e.g. a good hint at routes 4 and 5)
comes from the match of the fold with the reduction (`Algo.MasterRecursion.impl`).

* `Explicit.runInv_start`, `Explicit.runInv_step`: the invariant holds along a run.
* `Explicit.runInv_size`: under the invariant the evaluator state has size at most
  `2^{kS (log₂ n+2)^5}`: every frame and answer is within the input cap or the state bound, the
  fold index is at most the width, and the stack is at most as deep as the measure bound.
* `Explicit.tn_runStep`: one step, bounded at the root degree with exponent 5
  (`Explicit.TN.stepDFS`).
* `Explicit.exists_stepBounds_of_inv`: `Explicit.StepBounds p cam` from the carrier's bounds
  (`Explicit.CarrierTNJ`, `Explicit.StateInvXR`), a master recursion, and the calls bounds.
* `Explicit.exists_stepBounds_route5`, `Explicit.theorem_1_1_1_exponent5_numeral_of_route5`,
  `Explicit.theorem_1_1_1_exponent5_of_route5`: at parameters with `Explicit.ParamsOK`, the
  step bounds and Theorem 1.1.1 with exponent 5, from the bounds of route 5 alone.
-/

set_option synthInstance.maxSize 4096
set_option maxHeartbeats 1000000

namespace Explicit

open RAM Algo Babai

private theorem pfst {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {f : α → β × γ}
    (h : PolyFun f) : PolyFun (fun a => (f a).1) := h.comp polyFun_fst

/-! ## The invariant of a run -/

section Run

variable {S : Type} [Enc S] (a b : ℕ) (F : MasterOps S) (J : StInv S)
  (M : ∀ n, MasterRecursion (masterAdmittedRound a b F) n)

/-- **A frame of a run from a root of degree `n`.** -/
def FrameOK (n : ℕ) (fr : Round.Frame RawMasterSI S) : Prop :=
  (M n).Good fr.1 ∧ MasterInputWF a b fr.1 ∧ masterDegree fr.1 = n ∧ fr.2.1 ≤ F.width fr.1 ∧
    J n fr.1 fr.2.1 fr.2.2 ∧
    ∃ w T, LoopMatchG (masterAdmittedRound a b F) ((M n).Ch fr.1)
      (fun P => decWinSI n P.1) (fun _ => decCoset n) fr.1 w fr.2.1 fr.2.2 T ∧
      T.run = (decWinSI n fr.1.1).answer

/-- **The stack of a run**: its frames, each the child asked by the frame below. -/
def RunChain (n : ℕ) : List (Round.Frame RawMasterSI S) → Prop
  | [] => True
  | [fr] => FrameOK a b F J M n fr
  | fr :: fr' :: rest => FrameOK a b F J M n fr ∧
      (masterAdmittedRound a b F).child fr' = some fr.1 ∧ RunChain n (fr' :: rest)

/-- **The invariant of a run from a root of degree `n`.** -/
def RunInv (n : ℕ) (x : Round.EvalState RawMasterSI S RawCoset) : Prop :=
  RunChain a b F J M n x.1 ∧ ∀ A, x.2 = some A → Enc.size A ≤ masterInputCap a b n ∧
    ∀ fr rest, x.1 = fr :: rest → ∃ C, (masterAdmittedRound a b F).child fr = some C ∧
      decCoset n A = (decWinSI n C.1).answer

variable {a b F J M}

theorem runChain_head {n : ℕ} {fr : Round.Frame RawMasterSI S} {rest : List _}
    (h : RunChain a b F J M n (fr :: rest)) : FrameOK a b F J M n fr := by
  cases rest with
  | nil => exact h
  | cons _ _ => exact h.1

theorem runChain_tail {n : ℕ} {fr : Round.Frame RawMasterSI S} {rest : List _}
    (h : RunChain a b F J M n (fr :: rest)) : RunChain a b F J M n rest := by
  cases rest with
  | nil => trivial
  | cons _ _ => exact h.2.2

theorem runChain_mem {n : ℕ} {st : List (Round.Frame RawMasterSI S)}
    (h : RunChain a b F J M n st) : ∀ fr ∈ st, FrameOK a b F J M n fr := by
  induction st with
  | nil => intro fr hfr; simp at hfr
  | cons fr rest ih =>
    intro fr' hfr'
    rcases List.mem_cons.mp hfr' with rfl | hr
    · exact runChain_head h
    · exact ih (runChain_tail h) fr' hr

theorem runChain_setTop {n : ℕ} {fr fr₂ : Round.Frame RawMasterSI S} {rest : List _}
    (h₂ : FrameOK a b F J M n fr₂) (he : fr₂.1 = fr.1) (h : RunChain a b F J M n (fr :: rest)) :
    RunChain a b F J M n (fr₂ :: rest) := by
  cases rest with
  | nil => exact h₂
  | cons _ _ => exact ⟨h₂, he ▸ h.2.1, h.2.2⟩

/-- The stack of a run is at most as deep as the measure bound. -/
theorem runChain_length_aux {n : ℕ} (rest : List (Round.Frame RawMasterSI S)) :
    ∀ fr, RunChain a b F J M n (fr :: rest) →
      rest.length + masterRawMeasure fr.1 ≤ masterMeasureBound n := by
  induction rest with
  | nil =>
    intro fr h
    obtain ⟨-, hW, hd, -⟩ := runChain_head h
    have := masterRawMeasure_le hW.2.1 hW.2.2
    rw [hd] at this
    simpa using this
  | cons fr' rest ih =>
    intro fr h
    obtain ⟨I', j', s'⟩ := fr'
    have h1 : rest.length + masterRawMeasure I' ≤ masterMeasureBound n := ih (I', j', s') h.2.2
    have h2 := (masterGuardedChild_some (a := a) (b := b) (F := F) h.2.1).2.2.2.2.1
    simp only [List.length_cons]
    omega

theorem runChain_length {n : ℕ} {st : List (Round.Frame RawMasterSI S)}
    (h : RunChain a b F J M n st) : st.length ≤ masterMeasureBound n + 1 := by
  cases st with
  | nil => simp
  | cons fr rest =>
    have := runChain_length_aux rest fr h
    simp only [List.length_cons]
    omega

section Frames

variable {K : ℕ} {Rt : RawMasterSI → Prop} (hS : StateInvXR a b K F Rt J)
  (hRt : ∀ n P, (M n).Good P → MasterInputWF a b P → Rt P)

include hRt in
theorem frameOK_nodeAt {n : ℕ} {fr : Round.Frame RawMasterSI S}
    (h : FrameOK a b F J M n fr) : NodeAt a b Rt n fr.1 :=
  ⟨h.2.1, h.2.2.1, hRt n _ h.1 h.2.1⟩

include hS hRt in
/-- A frame at the root of a run, or pushed for a good child. -/
theorem frameOK_start {n : ℕ} {I : RawMasterSI} (hG : (M n).Good I) (hW : MasterInputWF a b I)
    (hd : masterDegree I = n) : FrameOK a b F J M n (I, 0, F.init I) :=
  ⟨hG, hW, hd, Nat.zero_le _, hS.1 n I ⟨hW, hd, hRt n I hG hW⟩, _, _, (M n).impl I hG hW,
    (M n).correct I hG hW⟩

/-- **The child a frame asks for is good**, well formed and of the same degree. -/
theorem frameOK_child {n : ℕ} {I C : RawMasterSI} {j : ℕ} {s : S}
    (h : FrameOK a b F J M n (I, j, s))
    (hc : (masterAdmittedRound a b F).child (I, j, s) = some C) :
    (M n).Good C ∧ MasterInputWF a b C ∧ masterDegree C = n := by
  obtain ⟨-, -, hd, -, -, w, T, hm, -⟩ := h
  have hs := masterGuardedChild_some (a := a) (b := b) (F := F) hc
  refine ⟨?_, hs.2.2.1, hs.2.2.2.1.trans hd⟩
  cases hm with
  | done _ _ _ _ hc' _ => rw [hc'] at hc; cases hc
  | call _ _ _ J' _ hc' hC _ =>
    rw [hc'] at hc
    cases hc
    exact (M n).progress.good_child I C hC

include hS hRt in
/-- **Combining the true answer of the child** keeps the frame. -/
theorem frameOK_combine {n : ℕ} {I C : RawMasterSI} {j : ℕ} {s : S} {A : RawCoset}
    (h : FrameOK a b F J M n (I, j, s))
    (hc : (masterAdmittedRound a b F).child (I, j, s) = some C)
    (hdec : decCoset n A = (decWinSI n C.1).answer) (hA : Enc.size A ≤ masterInputCap a b n) :
    FrameOK a b F J M n (I, j + 1, F.combine (I, j, s, A)) := by
  obtain ⟨hG, hW, hd, -, hJ, w, T, hm, hrun⟩ := h
  have hs := masterGuardedChild_some (a := a) (b := b) (F := F) hc
  refine ⟨hG, hW, hd, hs.1, hS.2.1 n I j s C A ⟨hW, hd, hRt n I hG hW⟩ hJ hs.1 hs.2.1 hA, ?_⟩
  cases hm with
  | done _ _ _ _ hc' _ => rw [hc'] at hc; cases hc
  | call w' _ _ J' k hc' _ hnext =>
    rw [hc'] at hc
    cases hc
    exact ⟨w', k (decWinSI n C.1).answer, hnext A hdec, hrun⟩

/-- **A frame that asks for no child returns the true answer.** -/
theorem frameOK_done {n : ℕ} {I : RawMasterSI} {j : ℕ} {s : S}
    (h : FrameOK a b F J M n (I, j, s))
    (hc : (masterAdmittedRound a b F).child (I, j, s) = none) :
    decCoset n (F.finish (I, s)) = (decWinSI n I.1).answer := by
  obtain ⟨-, -, -, -, -, w, T, hm, hrun⟩ := h
  cases hm with
  | done _ _ _ _ _ ha => exact ha.trans hrun
  | call _ _ _ _ _ hc' _ _ => rw [hc'] at hc; cases hc

include hS hRt in
/-- **The invariant starts at a good root.** -/
theorem runInv_start {n : ℕ} {I : RawMasterSI} (hG : (M n).Good I) (hW : MasterInputWF a b I)
    (hd : masterDegree I = n) :
    RunInv a b F J M n ((masterAdmittedRound a b F).startState I) :=
  ⟨frameOK_start hS hRt hG hW hd, fun A h => by cases h⟩

include hS hRt in
/-- **The invariant is kept by one step of the evaluator.** -/
theorem runInv_step {n : ℕ} {x : Round.EvalState RawMasterSI S RawCoset}
    (h : RunInv a b F J M n x) : RunInv a b F J M n ((masterAdmittedRound a b F).stepDFS x) := by
  obtain ⟨st, ret⟩ := x
  obtain ⟨hch, hret⟩ := h
  dsimp only at hch hret
  cases st with
  | nil => rw [Round.stepDFS_nil]; exact ⟨hch, hret⟩
  | cons fr rest =>
    obtain ⟨I, j, s⟩ := fr
    have hfr := runChain_head hch
    cases ret with
    | some A =>
      rw [Round.stepDFS_some]
      obtain ⟨hA, hpar⟩ := hret A rfl
      obtain ⟨C, hc, hdec⟩ := hpar _ _ rfl
      exact ⟨runChain_setTop (fr := (I, j, s)) (frameOK_combine hS hRt hfr hc hdec hA) rfl hch,
        fun A' h => by cases h⟩
    | none =>
      cases hc : (masterAdmittedRound a b F).child (I, j, s) with
      | some C =>
        rw [(masterAdmittedRound a b F).stepDFS_push rest hc]
        obtain ⟨hG, hW, hd⟩ := frameOK_child hfr hc
        exact ⟨⟨frameOK_start hS hRt hG hW hd, hc, hch⟩, fun A' h => by cases h⟩
      | none =>
        rw [(masterAdmittedRound a b F).stepDFS_pop rest hc]
        refine ⟨runChain_tail hch, fun A' hA' => ?_⟩
        cases hA'
        refine ⟨hS.2.2.2.1 n I j s (frameOK_nodeAt hRt hfr) hfr.2.2.2.2.1,
          fun fr' rest' hrest => ?_⟩
        subst hrest
        exact ⟨I, hch.2.1, frameOK_done hfr hc⟩

end Frames

/-! ## The size of the states of a run -/

/-- **The states of a run are quasipolynomially small**, with exponent 5 in the root degree. -/
theorem runInv_size {K : ℕ} {Rt : RawMasterSI → Prop} (hw : TN F.width (CarrierPre a b Rt) 5)
    (hS : StateInvXR a b K F Rt J) (hRt : ∀ n P, (M n).Good P → MasterInputWF a b P → Rt P) :
    ∃ kS, ∀ n x, RunInv a b F J M n x → Enc.size x ≤ 2 ^ (kS * (Nat.log 2 n + 2) ^ 5) := by
  obtain ⟨Aw, bw, hwb⟩ := hw
  have hcap := q5_masterInputCap a b
  have hW : Q5 (fun n => tsB Aw 5 bw n (masterInputCap a b n)) :=
    ((q5_two_pow_lg Aw 5 le_rfl).mul ((hcap.add (q5_const 1)).pow bw)).mono (fun _ => le_rfl)
  have hE := q5_two_pow_lg K 5 le_rfl
  have hMB := q5_of_polyBound polyBound_masterMeasureBound
  have hSfr := ((q5_const 2).mul hcap).add ((q5_const 2).mul
    (((q5_const 2).mul (hW.add (q5_const 0))).add ((q5_const 2).mul hE)))
  obtain ⟨c, hc⟩ := ((q5_const 2).mul ((q5_const 1).add ((hMB.add (q5_const 1)).mul
    (((q5_const 2).mul hSfr).add (q5_const 1))))).add ((q5_const 2).mul (hcap.add (q5_const 2)))
  refine ⟨c, fun n x hx => ?_⟩
  have hcn := hc n
  simp only at hcn
  set Wn := tsB Aw 5 bw n (masterInputCap a b n) with hWn
  set En := 2 ^ (K * lg n ^ 5) with hEn
  set Cn := masterInputCap a b n with hCn
  set Sfr := 2 * Cn + 2 * (2 * (Wn + 0) + 2 * En) with hSfr
  -- one frame
  have hframe : ∀ fr ∈ x.1, Enc.size fr ≤ Sfr := by
    intro fr hfr
    obtain ⟨I, j, s⟩ := fr
    have h := runChain_mem hx.1 _ hfr
    obtain ⟨hG, hWf, hd, hj, hJ, -⟩ := h
    have hd' : masterDegree I = n := hd
    have hI : Enc.size I ≤ Cn := by rw [hCn, ← hd']; exact hWf.1
    have hwI := (hwb.size n I ⟨hWf, hd.le, hRt n I hG hWf⟩).trans (tsB_mono_right _ _ _ _ hI)
    have hjs : Enc.size j ≤ Wn := (size_nat_le_of_le hj).trans hwI
    have hss : Enc.size s ≤ En := hS.2.2.1 n I j s ⟨hWf, hd, hRt n I hG hWf⟩ hJ
    have h1 := Combine.size_pair_le I (j, s)
    have h2 := Combine.size_pair_le j s
    omega
  have hlist := size_list_le_of_entries x.1 Sfr hframe
  have hlen := runChain_length hx.1
  have hmul : x.1.length * (2 * Sfr + 1) ≤ (masterMeasureBound n + 1) * (2 * Sfr + 1) :=
    Nat.mul_le_mul_right _ hlen
  have hret : Enc.size x.2 ≤ Cn + 2 := by
    obtain ⟨st, ret⟩ := x
    cases ret with
    | none => rw [size_none]; omega
    | some A =>
      rw [size_some_eq]
      exact Nat.add_le_add_right ((hx.2 A rfl).1) 2
  have hx2 := size_pair_le' x
  refine le_trans ?_ hcn
  change Enc.size x ≤ 2 * (1 + (masterMeasureBound n + 1) * (2 * Sfr + 1)) + 2 * (Cn + 2)
  omega

/-! ## One step -/

/-- **The guarded child of the admitted round, bounded at the degree.** -/
theorem tn_guardedChild {Rt : RawMasterSI → Prop} (hC : CarrierTNJ a b F Rt J) :
    TN (masterGuardedChild a b F)
      (fun n z => CarrierPre a b Rt n z.1 ∧ J n z.1 z.2.1 z.2.2) 5 := by
  have ht : TN (fun z : RawMasterSI × ℕ × S => decide (z.2.1 < F.width z.1))
      (fun n z => CarrierPre a b Rt n z.1 ∧ J n z.1 z.2.1 z.2.2) 5 :=
    ((TN.ofPoly (pfst polyFun_snd) _ 5).pair
      ((TN.poly_comp polyFun_fst hC.width).restrict (fun _ _ h => h.1))).comp_poly polyFun_natLt
  have h1 : TN (fun z : RawMasterSI × ℕ × S => masterAdmitChild a b (z.1, F.child z))
      (fun n z => CarrierPre a b Rt n z.1 ∧ J n z.1 z.2.1 z.2.2) 5 :=
    ((TN.ofPoly polyFun_fst _ 5).pair hC.child).comp_poly (polyFun_masterAdmitChild a b)
  refine (TN.iteT ht h1 (TN.const' none _ 5)).of_eq (fun z => ?_)
  unfold masterGuardedChild
  by_cases h : z.2.1 < F.width z.1 <;> simp [h]

/-- **One step of the evaluator with its loop counter, bounded at the root degree** on the
states of a run. -/
theorem tn_runStep {Rt : RawMasterSI → Prop} (hC : CarrierTNJ a b F Rt J) (hRt : ∀ n P, (M n).Good P → MasterInputWF a b P → Rt P) :
    TN (fun x : ℕ × Round.EvalState RawMasterSI S RawCoset =>
        (x.1 - 1, (masterAdmittedRound a b F).stepDFS x.2))
      (fun n x => RunInv a b F J M n x.2) 5 := by
  have hstep : TN (masterAdmittedRound a b F).stepDFS (RunInv a b F J M) 5 := by
    refine TN.stepDFS (masterAdmittedRound a b F) (tn_guardedChild hC) hC.init hC.combine
      hC.finish ?_ ?_ ?_ ?_
    · intro n fr rest h
      have hf := runChain_head h.1
      exact ⟨(frameOK_nodeAt hRt hf).pre, hf.2.2.2.2.1⟩
    · intro n fr rest C h hc
      obtain ⟨I, j, s⟩ := fr
      obtain ⟨hG, hW, hd⟩ := frameOK_child (runChain_head h.1) hc
      exact ⟨hW, hd.le, hRt n C hG hW⟩
    · intro n I j s rest h _
      have hf := runChain_head h.1
      exact ⟨(frameOK_nodeAt hRt hf).pre, j, hf.2.2.2.2.1⟩
    · intro n I j s rest A h
      have hf := runChain_head h.1
      exact ⟨(frameOK_nodeAt hRt hf).pre, hf.2.2.2.2.1, (h.2 A rfl).1⟩
  exact TN.stepDFS_counter _ hstep

end Run

/-! ## The step bounds of the variant Master -/

/-- **The fields of `Explicit.StepBounds` fixed by the assembly**: the bound on instances is
`Algo.masterInputCap p.a p.b`, the bound on the measure is `Algo.masterMeasureBound`, the
well-formedness test is `Algo.masterInputCheck p.a p.b`, and the calls exponent of line 2 is
`Aw`. Tier 2 uses the first two to put numerals in `kB dB kM dM`, and the third for `kP dP`. -/
def StepBoundsFixed {p : Params} {cam : RawGens × List ℕ → Option RawCameron}
    (sb : StepBounds p cam) (Aw : ℕ) : Prop :=
  sb.cost.bound = masterInputCap p.a p.b ∧ sb.cost.measureBound = masterMeasureBound ∧
    sb.cost.wfCheck = masterInputCheck p.a p.b ∧ sb.Aw = Aw

/-- **`Explicit.StepBounds` from the node carrier under its state invariant**: the carrier's
bounds, a master recursion whose good nodes satisfy the carrier's node predicate, and the
calls bounds. -/
theorem exists_stepBounds_of_inv (p : Params) {cam : RawGens × List ℕ → Option RawCameron}
    (hc : PolyFun cam) {Rt : RawMasterSI → Prop} {J : StInv StateE} {K : ℕ}
    (hC : CarrierTNJ p.a p.b (masterOpsE p cam) Rt J)
    (hS : StateInvXR p.a p.b K (masterOpsE p cam) Rt J)
    (M : ∀ n, MasterRecursion (masterRoundE p cam) n)
    (hMG : ∀ n P, MasterNodeGood n P → MasterInputWF p.a p.b P → (M n).Good P)
    (hRt : ∀ n P, (M n).Good P → MasterInputWF p.a p.b P → Rt P)
    (hRt0 : ∀ P : RawMasterSI, P.2 = none → Rt P) (Aw : ℕ)
    (hl2 : ∀ (n : ℕ) (P : RawMasterSI) (f : ℕ), MasterNodeGood n P →
      (masterRoundE p cam).WF P → (masterRoundE p cam).measure P < f + 1 → masterRoute P = 1 →
      ((masterRoundE p cam).roundCalls f P).length ≤ 2 ^ (Aw * (Nat.log 2 n + 2) ^ 4))
    (Ap : ℕ)
    (hoth : ∀ (n : ℕ) (P : RawMasterSI) (f : ℕ), MasterNodeGood n P →
      (masterRoundE p cam).WF P → (masterRoundE p cam).measure P < f + 1 → masterRoute P ≠ 1 →
      ((masterRoundE p cam).roundCalls f P).length ≤ 2 ^ (Ap * (Nat.log 2 n + 2) ^ 3)) :
    ∃ sb : StepBounds p cam, StepBoundsFixed sb Aw := by
  obtain ⟨⟨kB, dB, hB⟩, ⟨kM, dM, hM⟩, kP, dP, hent, hents, hgr, hwf, hro⟩ := exists_polyFields p
  obtain ⟨kS, hsize⟩ := runInv_size (M := M) hC.width hS hRt
  obtain ⟨A₁, b₁, hstep⟩ := tn_runStep (M := M) hC hRt
  obtain ⟨A₂, b₂, hinit⟩ := hC.init
  have hstep' := hstep.mono (fun _ _ h => h) (Nat.le_add_right A₁ A₂) le_rfl
    (Nat.le_add_right b₁ b₂)
  obtain ⟨⟨Q, hQw, hQ⟩, -⟩ := hinit.mono (fun _ _ h => h) (Nat.le_add_left A₂ A₁) le_rfl
    (Nat.le_add_left b₂ b₁)
  exact ⟨{
    cost := (exists_nodeCost p hc).some.runCostQ
    kB := kB, dB := dB, bound_le := hB
    kM := kM, dM := dM, measure_le := hM
    Aw := Aw, calls_line2 := hl2, Ap := Ap, calls_other := hoth
    As := A₁ + A₂, ds := b₁ + b₂
    Inv := RunInv p.a p.b (masterOpsE p cam) J M
    inv_start := fun I hW hG => runInv_start hS hRt (hMG _ I hG hW) hW rfl
    inv_step := fun n x h => runInv_step hS hRt h
    kS := kS, inv_size := hsize
    step := stepForm_of_TNB hstep'
    kP := kP, dP := dP, entry := hent, entry_size := hents, ground := hgr, wfCheck := hwf
    init := ⟨Q, hQw, fun I hW hnone =>
      hQ (Enc.size I) I ⟨hW, masterDegree_le_size I, hRt0 I hnone⟩⟩
    readOff := hro }, rfl, rfl, rfl, rfl⟩

/-- A node without a hint is on route 0. -/
theorem masterRoute_of_none {P : RawMasterSI} (h : P.2 = none) : masterRoute P = 0 := by
  obtain ⟨W, o⟩ := P
  subst h
  rfl

/-- **The step bounds of the variant Master from the bounds of route 5**, at parameters with
`Explicit.ParamsOK` and exact runs of Sec. 9 at lines 4c and 5–7. The route-5 carrier
`Explicit.route5OpsE p` is bounded at the degree with exponent 5 under an invariant `J5`
(`Explicit.CarrierTNJ`, `Explicit.StateInvXR`) at the nodes `R5`, and every good node of route 5
satisfies `R5`. -/
theorem exists_stepBounds_route5 {p : Params} (ok : ParamsOK p) (he4 : SbipExact p.tt p.dd)
    (he5 : SbipExact p.t p.d) {cam : RawGens × List ℕ → Option RawCameron} (hc : PolyFun cam)
    (hs : CameronSpec cam) (ht : p.tt + 2 ≤ 5) {R5 : RawMasterSI → Prop}
    {J5 : StInv AggnL57GState} {K5 : ℕ} (h5 : CarrierTNJ p.a p.b (route5OpsE p) R5 J5)
    (s5 : StateInvXR p.a p.b K5 (route5OpsE p) R5 J5)
    (hR5 : ∀ n P, MasterNodeGood n P → MasterInputWF p.a p.b P → masterRoute P = 5 → R5 P) :
    ∃ sb : StepBounds p cam, StepBoundsFixed sb 6 := by
  obtain ⟨q, hq, hT⟩ := exists_treesE ok hc hs
  obtain ⟨K, hS⟩ := stateInvXR_masterOpsE p hc ht s5
  obtain ⟨hl2, Ap, hoth⟩ := exists_calls_bounds ok he4 he5 hc hs
  refine exists_stepBounds_of_inv p hc (carrierTNJ_masterOpsE p hc ht h5) hS
    (fun n => masterRecE hq n (hT n)) (fun n P hG _ => hG)
    (fun n P hG hW => ⟨fun h4 => ⟨h4, hG.2⟩, fun h5' => hR5 n P hG hW h5'⟩)
    (fun P hP => ?_) 6 hl2 Ap hoth
  have h0 := masterRoute_of_none hP
  exact ⟨fun h4 => by omega, fun h5' => by omega⟩

/-- **Theorem 1.1.1 with exponent 5 and the constant `cFinal sb`, from the bounds of route 5**:
at parameters with `Explicit.ParamsOK` and exact runs of Sec. 9, with the Cameron routine
`Algo.masterCameron` of the cited Theorem 11.2.3. -/
theorem theorem_1_1_1_exponent5_numeral_of_route5 {p : Params} (ok : ParamsOK p)
    (he4 : SbipExact p.tt p.dd) (he5 : SbipExact p.t p.d) (ht : p.tt + 2 ≤ 5)
    {R5 : RawMasterSI → Prop} {J5 : StInv AggnL57GState} {K5 : ℕ}
    (h5 : CarrierTNJ p.a p.b (route5OpsE p) R5 J5)
    (s5 : StateInvXR p.a p.b K5 (route5OpsE p) R5 J5)
    (hR5 : ∀ n P, MasterNodeGood n P → MasterInputWF p.a p.b P → masterRoute P = 5 → R5 P) :
    ∃ sb : StepBounds p masterCameron, Theorem_1_1_1_exponent5_numeral (cFinal sb) := by
  obtain ⟨sb, -⟩ := exists_stepBounds_route5 ok he4 he5 masterCameron_spec.1 masterCameron_spec.2
    ht h5 s5 hR5
  obtain ⟨rk⟩ := recOK_of_paramsOK ok sb masterCameron_spec.1 masterCameron_spec.2
  exact ⟨sb, main_of_recX sb rk⟩

/-- **The step bounds of the variant Master from the bounds of route 5, at explicit line-1
thresholds** (`Explicit.ParamsOKX`): as `Explicit.exists_stepBounds_route5`, with the master
recursion `Explicit.masterRecEX` and the calls bounds `Explicit.exists_calls_boundsX`. -/
theorem exists_stepBounds_route5X {p : Params} (ok : ParamsOKX p) (he4 : SbipExact p.tt p.dd)
    (he5 : SbipExact p.t p.d) {cam : RawGens × List ℕ → Option RawCameron} (hc : PolyFun cam)
    (hs : CameronSpec cam) (ht : p.tt + 2 ≤ 5) {R5 : RawMasterSI → Prop}
    {J5 : StInv AggnL57GState} {K5 : ℕ} (h5 : CarrierTNJ p.a p.b (route5OpsE p) R5 J5)
    (s5 : StateInvXR p.a p.b K5 (route5OpsE p) R5 J5)
    (hR5 : ∀ n P, MasterNodeGood n P → MasterInputWF p.a p.b P → masterRoute P = 5 → R5 P) :
    ∃ sb : StepBounds p cam, StepBoundsFixed sb 6 := by
  obtain ⟨q, hq, hT⟩ := exists_treesX ok hc hs
  obtain ⟨K, hS⟩ := stateInvXR_masterOpsE p hc ht s5
  obtain ⟨hl2, Ap, hoth⟩ := exists_calls_boundsX ok he4 he5 hc hs
  refine exists_stepBounds_of_inv p hc (carrierTNJ_masterOpsE p hc ht h5) hS
    (fun n => masterRecEX hq n (hT n)) (fun n P hG _ => hG)
    (fun n P hG hW => ⟨fun h4 => ⟨h4, hG.2⟩, fun h5' => hR5 n P hG hW h5'⟩)
    (fun P hP => ?_) 6 hl2 Ap hoth
  have h0 := masterRoute_of_none hP
  exact ⟨fun h4 => by omega, fun h5' => by omega⟩

/-- **Theorem 1.1.1 with exponent 5 and the constant `cFinal sb`, from the bounds of route 5,
at explicit line-1 thresholds** (`Explicit.ParamsOKX`, e.g. `B = 25`,
`C₀ = (max 64 25!)! + 1`), with the Cameron routine `Algo.masterCameron` of the cited
Theorem 11.2.3. -/
theorem theorem_1_1_1_exponent5_numeral_of_route5X {p : Params} (ok : ParamsOKX p)
    (he4 : SbipExact p.tt p.dd) (he5 : SbipExact p.t p.d) (ht : p.tt + 2 ≤ 5)
    {R5 : RawMasterSI → Prop} {J5 : StInv AggnL57GState} {K5 : ℕ}
    (h5 : CarrierTNJ p.a p.b (route5OpsE p) R5 J5)
    (s5 : StateInvXR p.a p.b K5 (route5OpsE p) R5 J5)
    (hR5 : ∀ n P, MasterNodeGood n P → MasterInputWF p.a p.b P → masterRoute P = 5 → R5 P) :
    ∃ sb : StepBounds p masterCameron, Theorem_1_1_1_exponent5_numeral (cFinal sb) := by
  obtain ⟨sb, -⟩ := exists_stepBounds_route5X ok he4 he5 masterCameron_spec.1 masterCameron_spec.2
    ht h5 s5 hR5
  exact ⟨sb, theorem_1_1_1_exponent5_numeral_of_bounds ok sb⟩

/-- **Parameters at the explicit line-1 thresholds** `B = 25`, `C₀ = (max 64 25!)! + 1`
(`Explicit.line1OK_X`), with the other parameters of `Explicit.exists_paramsOK_exact`. -/
theorem exists_paramsOKX_exact : ∃ p : Params, ParamsOKX p ∧ p.B = line1BX ∧ p.C₀ = line1C₀X ∧
    p.t = 3 ∧ p.tt = 3 ∧ SbipExact p.tt p.dd ∧ SbipExact p.t p.d := by
  obtain ⟨p₀, ok, h3, htt, he4, he5⟩ := exists_paramsOK_exact
  have e : paramsL1 { p₀ with B := line1BX, C₀ := line1C₀X } = p₀ := by
    obtain ⟨hB, hC⟩ := ok.line1
    cases p₀
    simp only at hB hC
    subst hB hC
    rfl
  exact ⟨{ p₀ with B := line1BX, C₀ := line1C₀X }, ⟨line1OK_X, e ▸ ok⟩, rfl, rfl, h3, htt, he4, he5⟩

/-- **The bounds of route 5 at a parameter set**: the route-5 carrier is bounded at the degree
with exponent 5 under an invariant, at nodes `R5` that contain the good nodes of route 5. -/
def Route5Bounds (p : Params) : Prop :=
  ∃ (R5 : RawMasterSI → Prop) (J5 : StInv AggnL57GState) (K5 : ℕ),
    CarrierTNJ p.a p.b (route5OpsE p) R5 J5 ∧ StateInvXR p.a p.b K5 (route5OpsE p) R5 J5 ∧
    ∀ n P, MasterNodeGood n P → MasterInputWF p.a p.b P → masterRoute P = 5 → R5 P

/-- **Theorem 1.1.1 with exponent 5, at the explicit line-1 thresholds**, from the bounds of
route 5 at every parameter set of `Explicit.exists_paramsOKX_exact`: one RAM program solves
String Isomorphism within `2^{cFinal sb · (log₂ N + 2)^5}` steps, where `sb` are the step
bounds at parameters with `B = 25`, `C₀ = (max 64 25!)! + 1`. -/
theorem theorem_1_1_1_exponent5_of_route5
    (H : ∀ p : Params, ParamsOKX p → p.B = line1BX → p.C₀ = line1C₀X → p.t = 3 → p.tt = 3 →
      SbipExact p.tt p.dd → SbipExact p.t p.d → Route5Bounds p) :
    ∃ (p : Params) (sb : StepBounds p masterCameron), p.B = line1BX ∧ p.C₀ = line1C₀X ∧
      Theorem_1_1_1_exponent5_numeral (cFinal sb) := by
  obtain ⟨p, ok, hB, hC, h3, htt, he4, he5⟩ := exists_paramsOKX_exact
  obtain ⟨R5, J5, K5, h5, s5, hR5⟩ := H p ok hB hC h3 htt he4 he5
  obtain ⟨sb, h⟩ :=
    theorem_1_1_1_exponent5_numeral_of_route5X ok he4 he5 (by omega) h5 s5 hR5
  exact ⟨p, sb, hB, hC, h⟩

end Explicit
