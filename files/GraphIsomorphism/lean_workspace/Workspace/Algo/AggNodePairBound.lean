import Workspace.Algo.AggNodeCompareCacheBound

/-! # A size invariant for paired stages

The source loop keeps its fixed context. The current comparison coset,
completed source answer, and two descent accumulators share a fixed bound.
The cache bound does not depend on any of those coset encodings.
-/
set_option synthInstance.maxSize 1024
set_option maxHeartbeats 1000000
namespace Algo
open RAM RAM.Targets

structure AggnCompareEnvelope (c : ℕ) (C : AggnPhaseCtx) where
  base : ℕ
  loopState : ℕ
  cache : ℕ
  coset : ℕ
  context_le : Enc.size C ≤ base
  jobs_le : Enc.size (aggnCompareJobs c C) ≤ base
  open_le : ∀ a ∈ aggnCompareJobs c C,
    AggnLoopBound base loopState (aggnCompareCtx C a).1 ∧
    Enc.size (aggnCompareCtx C a).2.1 ≤ base ∧ Enc.size (aggnCompareCtx C a).2.2 ≤ coset
  empty_le : AggnLoopBound base loopState (([], []), ([], [], []))
  empty_coset_le : Enc.size (none : RawCoset) ≤ coset
  step_le : lcStBound base ≤ loopState
  cache_le : ∀ p ys q mode, AggnLoopBound base loopState p → Enc.size ys ≤ base →
    Enc.size (aggnPairInput c p ys q mode) ≤ cache
  coset_le : 4 * cache + chainBound base + 4 ≤ coset

def AggnPairBound {c : ℕ} {C : AggnPhaseCtx} (B : AggnCompareEnvelope c C)
    (ys : RawStr) (j : ℕ) (v : AggnPairState) : Prop :=
  AggnLoopBound B.base B.loopState v.1 ∧ Enc.size ys ≤ B.base ∧
    Enc.size v.2.1 ≤ B.coset ∧ (∀ H, v.2.2.1 = some H → Enc.size H ≤ B.coset) ∧
    v.2.2.2.1 = aggnPairInput c v.1 ys v.2.1 v.2.2.1 ∧
    v.2.2.2.2.1 ≤ j ∧ AggnRecomputeBound B.cache B.coset v.2.2.2.2.2

theorem AggnPairBound.start {c : ℕ} {C : AggnPhaseCtx} (B : AggnCompareEnvelope c C)
    {p : RawLCLoop} {ys : RawStr} {q : RawCoset} {mode : Option RawCoset}
    (hp : AggnLoopBound B.base B.loopState p) (hy : Enc.size ys ≤ B.base)
    (hq : Enc.size q ≤ B.coset) (hm : ∀ H, mode = some H → Enc.size H ≤ B.coset) (j : ℕ) :
    AggnPairBound B ys j (aggnPairStart c p ys q mode) :=
  ⟨hp, hy, hq, hm, rfl, Nat.zero_le _, aggnInit_bound (B.cache_le p ys q mode hp hy)
    (by have := B.coset_le; omega)⟩

theorem aggnPairInput_source (c : ℕ) (p : RawLCLoop) (ys : RawStr) (q : RawCoset)
    (mode : Option RawCoset) : (aggnPairInput c p ys q mode).1.2.2.2.1 = p.1.1 := by
  cases mode <;> rfl

theorem AggnPairBound.combine {c : ℕ} {C : AggnPhaseCtx} {B : AggnCompareEnvelope c C}
    {ys : RawStr} {j : ℕ} {v : AggnPairState} (h : AggnPairBound B ys j v)
    {ans : RawCoset} (ha : Enc.size ans ≤ B.coset) (P : AggnPairCtx) (hys : P.2.1 = ys) (i : ℕ) :
    AggnPairBound B ys (j + 1) (aggnPairCombine c ((P, none), i, v, ans)) := by
  have hp : Enc.size v.2.2.2.1 ≤ B.cache :=
    h.2.2.2.2.1 ▸ B.cache_le v.1 ys v.2.1 v.2.2.1 h.1 h.2.1
  have hx : v.2.2.2.1.1.2.2.2.1.length ≤ B.base := by
    rw [h.2.2.2.2.1, aggnPairInput_source]
    exact (length_le_size v.1.1.1).trans ((size_fst_le' v.1.1).trans h.1.1)
  have hs := aggnStep_bound hp hx (by have := B.coset_le; omega)
    (by have := B.coset_le; omega) h.2.2.2.2.2.2.2.2.2 ha v.2.2.2.2.2.1 v.2.2.2.2.2.2.1
  change AggnPairBound B ys (j + 1) (aggnPairPack c v.1 P.2.1 v.2.1 v.2.2.1
    (v.2.2.2.2.1 + 1) (aggnrStep v.2.2.2.1 v.2.2.2.2.2.1
      v.2.2.2.2.2.2.1 v.2.2.2.2.2.2.2.2 ans))
  rw [hys]
  generalize hv : aggnrStep v.2.2.2.1 v.2.2.2.2.2.1 v.2.2.2.2.2.2.1
    v.2.2.2.2.2.2.2.2 ans = next at hs ⊢
  dsimp only [aggnPairPack]
  split
  · exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, rfl,
      Nat.add_le_add_right h.2.2.2.2.2.1 1, hs⟩
  · cases hm : v.2.2.1 with
    | none =>
      exact AggnPairBound.start B h.1 h.2.1 h.2.2.1
        (fun H he => by cases Option.some.inj he; exact hs.2.2.2) _
    | some H =>
      exact AggnPairBound.start B (h.1.step B.step_le H) h.2.1 hs.2.2.2
        (fun H he => by cases he) _

theorem AggnPairBound.size {c : ℕ} {C : AggnPhaseCtx} {B : AggnCompareEnvelope c C}
    {ys : RawStr} {j : ℕ} {v : AggnPairState} (h : AggnPairBound B ys j v) :
    Enc.size v ≤ 4096 * (B.base + B.loopState + B.cache + B.coset + j + 1) := by
  have hp := h.1.size
  have hq := h.2.2.1
  have hm : Enc.size v.2.2.1 ≤ B.coset + 2 := by
    cases he : v.2.2.1 with
    | none => rw [size_none]; omega
    | some H => rw [size_some_eq]; have := h.2.2.2.1 H he; omega
  have hP : Enc.size v.2.2.2.1 ≤ B.cache :=
    h.2.2.2.2.1 ▸ B.cache_le v.1 ys v.2.1 v.2.2.1 h.1 h.2.1
  have hn : ∀ a b : ℕ, a ≤ b → Enc.size a ≤ b + 2 := by
    intro a b hab
    rw [Small.size_nat]
    have := size_le_self a
    omega
  have hj := hn _ _ h.2.2.2.2.2.1
  have ht := hn _ _ h.2.2.2.2.2.2.1
  have hi := hn _ _ h.2.2.2.2.2.2.2.1
  have ha := h.2.2.2.2.2.2.2.2.1
  have hb := h.2.2.2.2.2.2.2.2.2
  have h0 := Combine.size_pair_le v.1 v.2
  have h1 := Combine.size_pair_le v.2.1 v.2.2
  have h2 := Combine.size_pair_le v.2.2.1 v.2.2.2
  have h3 := Combine.size_pair_le v.2.2.2.1 v.2.2.2.2
  have h4 := Combine.size_pair_le v.2.2.2.2.1 v.2.2.2.2.2
  have h5 := Combine.size_pair_le v.2.2.2.2.2.1 v.2.2.2.2.2.2
  have h6 := Combine.size_pair_le v.2.2.2.2.2.2.1 v.2.2.2.2.2.2.2
  have h7 := Combine.size_pair_le v.2.2.2.2.2.2.2.1 v.2.2.2.2.2.2.2.2
  simp only [Prod.eta] at h0 h1 h2 h3 h4 h5 h6 h7
  omega

end Algo
