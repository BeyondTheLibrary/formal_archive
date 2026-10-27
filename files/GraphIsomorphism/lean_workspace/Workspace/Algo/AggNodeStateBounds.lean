import Workspace.Algo.AggNodeSizeRoutine

/-! # Bounds preserved inside a certificate execution

The bounds in this file do not use correctness of an answer. The local loop
already shortens its generators. We also shorten each answer before storing
it, so one fixed coset bound works through every chain and union.
-/
set_option synthInstance.maxSize 1024
set_option maxHeartbeats 1000000
namespace Algo
open RAM RAM.Targets

/-- Store the standard short coset representation of an arbitrary answer. -/
def aggnNormAnswer (xs : RawStr) (a : RawCoset) : RawCoset :=
  a.map fun q => (tidyGens (xs, q.1), normPerm (xs, q.2))

theorem aggnNormAnswer_decode {n : ℕ} {xs : RawStr} (hx : xs.length = n) (a : RawCoset) :
    decCoset n (aggnNormAnswer xs a) = decCoset n a := by
  cases a with
  | none => rfl
  | some q =>
    rcases q with ⟨gs, r⟩
    simp [aggnNormAnswer, decCoset_some, decGroup_tidyGens hx, decPerm_normPerm hx]

theorem aggnNormAnswer_size {xs : RawStr} {b : ℕ} (hx : xs.length ≤ b) (a : RawCoset) :
    Enc.size (aggnNormAnswer xs a) ≤ chainBound b := by
  cases a with
  | none =>
    change Enc.size (none : RawCoset) ≤ _
    rw [size_none]
    dsimp [chainBound]
    omega
  | some q => exact size_coset_le' hx (wf_tidyGens rfl _) (length_tidyGens rfl _) (wf_normPerm rfl _)

theorem aggnPolyFun_normAnswer : PolyFun (fun z : RawStr × RawCoset => aggnNormAnswer z.1 z.2) := by
  have hq : PolyFun (fun z : (RawGens × RawPerm) × RawStr =>
      some (tidyGens (z.2, z.1.1), normPerm (z.2, z.1.2))) :=
    (((polyFun_snd.pair (polyFun_fst.comp polyFun_fst)).comp polyFun_tidyGens).pair
      ((polyFun_snd.pair (polyFun_fst.comp polyFun_snd)).comp polyFun_normPerm)).comp polyFun_some
  exact (polyFun_swap.comp (PolyFun.optionElim (polyFun_const none) hq)).of_eq
    (fun z => by cases z.2 <;> rfl)

/-- Separate the fixed context from the repeatedly replaced loop state. -/
def AggnLoopBound (b s : ℕ) (p : RawLCLoop) : Prop :=
  Enc.size p.1 ≤ b ∧ Enc.size p.2 ≤ s

theorem AggnLoopBound.step {b s : ℕ} {p : RawLCLoop} (h : AggnLoopBound b s p)
    (hs : lcStBound b ≤ s) (a : RawCoset) : AggnLoopBound b s (lcStepWith a p) := by
  refine ⟨by simpa only [lcwStep_fst] using h.1, (lcwSize_step a p).trans ?_⟩
  exact max_le h.2 ((mono_lcStBound h.1).trans hs)

theorem AggnLoopBound.size {b s : ℕ} {p : RawLCLoop} (h : AggnLoopBound b s p) :
    Enc.size p ≤ 2 * b + 2 * s := by
  have hp : Enc.size p ≤ 2 * Enc.size p.1 + 2 * Enc.size p.2 := Combine.size_pair_le _ _
  obtain ⟨hb, hs⟩ := h
  omega

/-- Pack one completed local loop. Its cache and counters are irrelevant. -/
def aggnLoopEntry (z : AggnJob × RawLCLoop) : RawAggCert :=
  aggPack (z.2.1.1, z.1.2, lcOutOf z.2)

theorem aggnPolyFun_loopEntry : PolyFun aggnLoopEntry := by
  have hx : PolyFun (fun z : AggnJob × RawLCLoop => z.2.1.1) :=
    (polyFun_snd.comp polyFun_fst).comp polyFun_fst
  exact (hx.pair ((polyFun_fst.comp polyFun_snd).pair
    (polyFun_snd.comp lcwPolyFun_out))).comp aggPolyFun_pack

/-- Concrete envelopes used only in the size proof. Existence is derived below
from the already proved machine routines, not required from the caller. -/
structure AggnStateEnvelope (c : ℕ) (C : AggnPhaseCtx) where
  base : ℕ
  loopState : ℕ
  cache : ℕ
  coset : ℕ
  entry : ℕ
  context_le : Enc.size C ≤ base
  jobs_le : Enc.size (aggnPhaseJobs c C) ≤ base
  open_le : ∀ a ∈ aggnPhaseJobs c C, AggnLoopBound base loopState (aggnJobLoop C a)
  empty_le : AggnLoopBound base loopState (([], []), ([], [], []))
  step_le : lcStBound base ≤ loopState
  cache_le : ∀ p, AggnLoopBound base loopState p → Enc.size (aggnrInputOf c p) ≤ cache
  coset_le : 4 * cache + chainBound base + 4 ≤ coset
  entry_le : ∀ a ∈ aggnPhaseJobs c C, ∀ p, AggnLoopBound base loopState p →
    Enc.size (aggnLoopEntry (a, p)) ≤ entry

/-- The two indices are bounded by the cache, and both cosets have one common bound. -/
def AggnRecomputeBound (k a : ℕ) (v : AggnRecomputeState) : Prop :=
  v.1 ≤ k ∧ v.2.1 ≤ k ∧ Enc.size v.2.2.1 ≤ a ∧ Enc.size v.2.2.2 ≤ a

private theorem aggnSize_getD {α : Type*} [Enc α] (l : List α) (i : ℕ) (a : α) :
    Enc.size (l.getD i a) ≤ max (Enc.size l) (Enc.size a) := by
  by_cases hi : i < l.length
  · rw [List.getD_eq_getElem _ _ hi]
    exact (size_mem_le (List.getElem_mem hi)).trans (le_max_left _ _)
  · rw [List.getD_eq_default l a (by omega)]
    exact le_max_right _ _

private theorem aggnBegin_size {P : AggnRecomputeInput} {k a : ℕ}
    (hp : Enc.size P ≤ k) (ha : 4 * k + 4 ≤ a) (t : ℕ) :
    Enc.size (aggnrBegin P t) ≤ a := by
  have hker := (size_fst_le' P.2).trans (size_snd_le' P)
  have hreps := (size_fst_le' P.2.2).trans ((size_snd_le' P.2).trans (size_snd_le' P))
  have hrep := aggnSize_getD P.2.2.1 t ([] : RawPerm)
  rw [size_nil] at hrep
  have hs := Combine.size_pair_le P.2.1 (P.2.2.1.getD t [])
  change Enc.size (some (P.2.1, P.2.2.1.getD t []) : RawCoset) ≤ a
  rw [size_some_eq]
  omega

theorem aggnInit_bound {P : AggnRecomputeInput} {k a : ℕ}
    (hp : Enc.size P ≤ k) (ha : 4 * k + 4 ≤ a) :
    AggnRecomputeBound k a (aggnrInit (P, none)) := by
  refine ⟨Nat.zero_le _, Nat.zero_le _, aggnBegin_size hp ha 0, ?_⟩
  change Enc.size (if (aggnrWindows P).isEmpty then
    some (P.1.2.1, P.1.2.2.1) else none : RawCoset) ≤ a
  split
  · rw [size_some_eq]
    have hg := (size_fst_le' P.1.2).trans ((size_snd_le' P.1).trans (size_fst_le' P))
    have hr := (size_fst_le' P.1.2.2).trans ((size_snd_le' P.1.2).trans
      ((size_snd_le' P.1).trans (size_fst_le' P)))
    have hs := Combine.size_pair_le P.1.2.1 P.1.2.2.1
    omega
  · rw [size_none]; omega

theorem aggnStep_bound {P : AggnRecomputeInput} {k a b : ℕ}
    (hp : Enc.size P ≤ k) (hx : P.1.2.2.2.1.length ≤ b)
    (hka : 4 * k + 4 ≤ a) (hba : chainBound b ≤ a)
    {acc ans : RawCoset} (hacc : Enc.size acc ≤ a) (hans : Enc.size ans ≤ a) (t i : ℕ) :
    AggnRecomputeBound k a (aggnrStep P t i acc ans) := by
  have hc : aggnrCount P ≤ k := (length_le_size P.2.2.1).trans
    (((size_fst_le' P.2.2).trans ((size_snd_le' P.2).trans (size_snd_le' P))).trans hp)
  have hw : (aggnrWindows P).length ≤ k := (length_le_size P.2.2.2).trans
    (((size_snd_le' P.2.2).trans ((size_snd_le' P.2).trans (size_snd_le' P))).trans hp)
  unfold aggnrStep
  split
  · exact ⟨(Nat.min_le_right _ _).trans hc, (Nat.min_le_right _ _).trans hw, hans, hacc⟩
  · exact ⟨(Nat.min_le_right _ _).trans hc, Nat.zero_le _, aggnBegin_size hp hka _,
      size_rawCosetJoin_le rfl hx hba hacc hans⟩

/-- The cache is freshly computed from the retained loop. -/
def AggnCertBound {c : ℕ} {C : AggnPhaseCtx} (B : AggnStateEnvelope c C)
    (j : ℕ) (v : AggnCertState) : Prop :=
  AggnLoopBound B.base B.loopState v.1 ∧ v.2.1 = aggnrInputOf c v.1 ∧
    v.2.2.1 ≤ j ∧ AggnRecomputeBound B.cache B.coset v.2.2.2

theorem AggnCertBound.open {c : ℕ} {C : AggnPhaseCtx} (B : AggnStateEnvelope c C)
    {p : RawLCLoop} (h : AggnLoopBound B.base B.loopState p) (j : ℕ) :
    AggnCertBound B j (aggnCertOpen c p) :=
  ⟨h, rfl, Nat.zero_le _, aggnInit_bound (B.cache_le p h) (by have := B.coset_le; omega)⟩

theorem AggnCertBound.mono {c : ℕ} {C : AggnPhaseCtx} {B : AggnStateEnvelope c C}
    {j k : ℕ} {v : AggnCertState} (h : AggnCertBound B j v) (hjk : j ≤ k) :
    AggnCertBound B k v := ⟨h.1, h.2.1, h.2.2.1.trans hjk, h.2.2.2⟩

theorem AggnCertBound.combine {c : ℕ} {C : AggnPhaseCtx} {B : AggnStateEnvelope c C}
    {j : ℕ} {v : AggnCertState} (h : AggnCertBound B j v)
    {ans : RawCoset} (ha : Enc.size ans ≤ B.coset) (p : AggnCertNode) (i : ℕ) :
    AggnCertBound B (j + 1) (aggnCertCombine c (p, i, v, ans)) := by
  have hp : Enc.size v.2.1 ≤ B.cache := h.2.1 ▸ B.cache_le v.1 h.1
  have hx : v.2.1.1.2.2.2.1.length ≤ B.base := by
    rw [h.2.1]
    exact (lcDeg_le v.1).trans h.1.1
  have hs := aggnStep_bound hp hx (by have := B.coset_le; omega)
    (by have := B.coset_le; omega) h.2.2.2.2.2.2 ha v.2.2.2.1 v.2.2.2.2.1
  change AggnCertBound B (j + 1) (aggnCertPack c v.1 (v.2.2.1 + 1)
    (aggnrStep v.2.1 v.2.2.2.1 v.2.2.2.2.1 v.2.2.2.2.2.2 ans))
  unfold aggnCertPack
  split
  · exact ⟨h.1, rfl, Nat.add_le_add_right h.2.2.1 1, hs⟩
  · exact AggnCertBound.open B (h.1.step B.step_le _) _

end Algo
