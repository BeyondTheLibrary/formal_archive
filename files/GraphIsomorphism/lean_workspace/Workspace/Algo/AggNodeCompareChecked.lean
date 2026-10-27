import Workspace.Algo.AggNodeCompareRAM
import Workspace.Algo.AggNodeUniform

/-! # A bounded child boundary for the comparison phase

The executable degree is read from the retained source context. Normalize
every requested window before exposing it to the recursive evaluator.
-/
set_option synthInstance.maxSize 1024
set_option maxHeartbeats 1000000
namespace Algo
open RAM RAM.Targets

def aggnCompareCheckedChild (c : ℕ) (z : AggnPhaseNode × ℕ × AggnCompareState) :
    Option AggnPhaseNode := (aggnCompareChild c z).map aggnCheckedNode

theorem aggnCompareCheckedChild_some {c : ℕ} {z : AggnPhaseNode × ℕ × AggnCompareState}
    {J : AggnPhaseNode} (h : aggnCompareCheckedChild c z = some J) :
    z.1.2 = none ∧ ∃ W, aggnCompareChild c z = some (z.1.1, some W) ∧
      J = (z.1.1, some (aggnCheckedWindow (z.1.1.2.1, W))) := by
  obtain ⟨J', hJ', rfl⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨ho, W, rfl⟩ := aggnCompareChild_some hJ'
  exact ⟨ho, W, hJ', rfl⟩

def aggnCompareCheckedRound (c : ℕ) : Round AggnPhaseNode AggnCompareState RawCoset where
  WF := fun I => AggnCheckedWF I.1.2.1.length I
  ground := (aggnCompareRound c 0).ground
  measure := (aggnCompareRound c 0).measure
  width := (aggnCompareRound c 0).width
  child := aggnCompareCheckedChild c
  init := (aggnCompareRound c 0).init
  combine := (aggnCompareRound c 0).combine
  finish := (aggnCompareRound c 0).finish
  bot := none
  child_eq_none := by
    intro I j s hj
    unfold aggnCompareCheckedChild
    change ((aggnCompareRound c 0).child (I, j, s)).map aggnCheckedNode = none
    rw [(aggnCompareRound c 0).child_eq_none I j s hj]
    rfl
  child_wf := by
    intro I j s J hI hJ
    obtain ⟨_, W, _, rfl⟩ := aggnCompareCheckedChild_some hJ
    refine ⟨rfl, hI.2.1, ?_⟩
    intro W' hW'
    cases Option.some.inj hW'
    exact aggnCheckedWindow_wf _ _
  child_measure := by
    intro I j s J _ hJ
    obtain ⟨ho, W, _, rfl⟩ := aggnCompareCheckedChild_some hJ
    change 0 < I.2.elim 1 (fun _ => 0)
    rw [ho]
    exact Nat.zero_lt_one
  child_ground := by
    intro I j s J _ hJ
    obtain ⟨_, W, _, rfl⟩ := aggnCompareCheckedChild_some hJ
    exact le_rfl

theorem aggnQuasiFun_compareCheckedChild (c : ℕ) : QuasiFun (aggnCompareCheckedChild c) := by
  have hf : PolyFun (fun z : AggnPhaseNode × Option AggnPhaseNode => some (aggnCheckedNode z.1)) :=
    (polyFun_fst.comp aggnPolyFun_checkedNode).comp polyFun_some
  have hm : PolyFun (fun o : Option AggnPhaseNode => o.map aggnCheckedNode) :=
    ((polyFun_id.pair polyFun_id).comp (PolyFun.optionElim (polyFun_const none) hf)).of_eq
      (fun o => by cases o <;> rfl)
  exact (aggnQuasiFun_compareChild c).comp_poly hm

/-- The numerical comparison width is bounded even for invalid actions. -/
theorem aggnCompareWidth_bound_in_size (c : ℕ) : ∃ d : ℕ, ∀ C : AggnPhaseCtx,
    aggnCompareWidth c C ≤ 2 ^ ((Nat.log 2 (Enc.size C) + 2) ^ d) := by
  obtain ⟨d, hs⟩ := (aggnQuasiFun_compareJobs c).size
  let P := fun N => 2 ^ ((Nat.log 2 N + 2) ^ d) *
    (2 * (N * (2 ^ ((Nat.log 2 N + 2) ^ (c + 1)) * N)))
  have hp : QuasiPolyBound P := (quasiPolyBound_witness d).mul
    ((polyBound_const 2).quasiPoly.mul (polyBound_id.quasiPoly.mul
      ((quasiPolyBound_witness (c + 1)).mul polyBound_id.quasiPoly)))
  obtain ⟨e, he⟩ := hp
  refine ⟨e, fun C => le_trans ?_ (he (Enc.size C))⟩
  by_cases hg : C.2.2.2.length ≤ guardBound c C.2.1.length
  · have hn : C.2.1.length ≤ Enc.size C :=
      (length_le_size C.2.1).trans ((size_fst_le' C.2).trans (size_snd_le' C))
    have ht : C.2.2.2.length ≤ Enc.size C :=
      (length_le_size C.2.2.2).trans
        ((size_snd_le' C.2.2).trans ((size_snd_le' C.2).trans (size_snd_le' C)))
    have hguard : C.2.2.2.length ≤ guardBound c (Enc.size C) :=
      hg.trans (Nat.pow_le_pow_left (Nat.add_le_add_right (Nat.log_mono_right hn) 1) c)
    have hf := aggnFactorial_le c ht hguard
    have hj := (length_le_size (aggnCompareJobs c C)).trans (hs C)
    exact Nat.mul_le_mul hj (Nat.mul_le_mul_left 2 (Nat.mul_le_mul hn (Nat.mul_le_mul hf hn)))
  · simp only [aggnCompareWidth, aggnCompareJobs, aggnPhaseRows_eq_nil_of_not_guard hg,
      List.map_nil, List.flatMap_nil, List.flatMap_cons, List.nil_append,
      List.length_nil, Nat.zero_mul, Nat.zero_le]

theorem aggnCompareChecked_width_bound (c : ℕ) : ∃ W : ℕ → ℕ,
    QuasiPolyBound W ∧ Monotone W ∧ ∀ I,
      (aggnCompareCheckedRound c).WF I →
        (aggnCompareCheckedRound c).width I ≤ W ((aggnCompareCheckedRound c).ground I) := by
  obtain ⟨d, hd⟩ := aggnCompareWidth_bound_in_size c
  let W := fun n => 2 ^ ((Nat.log 2 (2 * aggnCheckedWindowBound n) + 2) ^ d)
  refine ⟨W, (quasiPolyBound_witness d).comp_poly
    ((polyBound_const 2).mul aggnPolyBound_checkedWindow), ?_, ?_⟩
  · intro a b hab
    exact quasiPolyBound_witness_mono d
      (Nat.mul_le_mul_left 2 (aggnMono_checkedWindowBound hab))
  · intro I hI
    have h : aggnCompareWidth c I.1 ≤ W I.1.2.1.length :=
      (hd I.1).trans (quasiPolyBound_witness_mono d hI.2.1)
    change I.2.elim (aggnCompareWidth c I.1) (fun _ => 0) ≤ W I.1.2.1.length
    cases I.2 with
    | none => exact h
    | some _ => exact Nat.zero_le _

end Algo
