import Workspace.Algo.TopCosetMatch

/-! # Machine bounds for one coset lifting phase

Preparing the preimage and the orbit list, issuing a child, and storing its
answer are polynomial in their supplied encodings on every input. The
external leaf solver is excluded from that local work. A master `CostQ`
also needs bounds in the parent domain and the actual master embedding.
-/

namespace Algo

open RAM RAM.Targets

private theorem pfst {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {f : α → β × γ}
    (h : PolyFun f) : PolyFun (fun a => (f a).1) := h.comp polyFun_fst

private theorem psnd {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {f : α → β × γ}
    (h : PolyFun f) : PolyFun (fun a => (f a).2) := h.comp polyFun_snd

private theorem plt : PolyFun (fun p : ℕ × ℕ => decide (p.1 < p.2)) := by
  have h := (((polyFun_fst.pair (polyFun_const 1)).comp polyFun_add).pair polyFun_snd).comp polyFun_le
  exact h.of_eq (fun _ => by simp only [Nat.add_one_le_iff])

private theorem pmap {α β σ : Type*} [Enc α] [Enc β] [Enc σ] {f : α × σ → β}
    (hf : PolyFun f) : PolyFun (fun p : Option α × σ => p.1.map (fun a => f (a, p.2))) :=
  (PolyFun.optionElim (polyFun_const none) (hf.comp polyFun_some)).of_eq
    (fun p => by cases p.1 <;> rfl)

theorem polyFun_topclPrepare : PolyFun topclPrepare := by
  have hp : PolyFun (fun p : RawTopLift => p.1) := polyFun_fst
  have hs : PolyFun (fun p : RawTopLift => p.2.2) := psnd polyFun_snd
  have ht : PolyFun (fun p : RawTopLift => p.2.1) := pfst polyFun_snd
  exact (pfst hs).pair ((psnd hs).pair
    ((hp.comp polyFun_topKernelWindows).pair ((hp.pair ht).comp polyFun_topCosetStart)))

theorem polyFun_topclJobs : PolyFun topclJobs :=
  polyFun_top1Inputs.comp (PolyFun.map polyFun_topclPrepare)

theorem polyFun_topclLeaf :
    PolyFun (fun z : TopCosetChainInput × ℕ × (RawGens × RawPerm) =>
      topclLeaf z.1 z.2.1 z.2.2) := by
  have hp : PolyFun (fun z : TopCosetChainInput × ℕ × (RawGens × RawPerm) => z.1) := polyFun_fst
  have hx := pfst hp
  have hy := pfst (psnd hp)
  have hw := pfst (psnd (psnd hp))
  have hj : PolyFun (fun z : TopCosetChainInput × ℕ × (RawGens × RawPerm) => z.2.1) :=
    pfst polyFun_snd
  have hc : PolyFun (fun z : TopCosetChainInput × ℕ × (RawGens × RawPerm) => z.2.2) :=
    psnd polyFun_snd
  have hd := ((hw.pair hj).pair (polyFun_const ([] : List ℕ))).comp polyFun_getD
  exact hd.pair (((hx.pair (pfst hc)).comp polyFun_tidyGens).pair
    (((hx.pair (psnd hc)).comp polyFun_normPerm).pair (hx.pair hy)))

/-- The child bound holds even for malformed states and arbitrary answer
encodings. Its mathematical specification is proved in `TopCosetChain`. -/
theorem polyFun_topclChild : PolyFun topclChild := by
  let X := TopCosetChainNode × ℕ × RawCoset
  have hp : PolyFun (fun z : X => z.1.1) := pfst polyFun_fst
  have hs : PolyFun (fun z : X => z.2.2) := psnd polyFun_snd
  have hj : PolyFun (fun z : X => z.2.1) := pfst polyFun_snd
  have hw := (pfst (psnd (psnd hp))).comp polyFun_length
  have hbody : PolyFun (fun z : (RawGens × RawPerm) × X =>
      (z.2.1.1, some (topclLeaf z.2.1.1 z.2.2.1 z.1))) := by
    have hp' : PolyFun (fun z : (RawGens × RawPerm) × X => z.2.1.1) := polyFun_snd.comp hp
    have hj' : PolyFun (fun z : (RawGens × RawPerm) × X => z.2.2.1) := polyFun_snd.comp hj
    exact hp'.pair (((hp'.pair (hj'.pair polyFun_fst)).comp polyFun_topclLeaf).comp polyFun_some)
  have hmap := (hs.pair polyFun_id).comp (pmap hbody)
  have hrun : PolyFun (fun z : X => if z.2.1 < z.1.1.2.2.1.length then
      z.2.2.map (fun c => (z.1.1, some (topclLeaf z.1.1 z.2.1 c))) else none) :=
    (PolyFun.ite ((hj.pair hw).comp plt) hmap (polyFun_const none)).of_eq (fun _ => by simp)
  have ho : PolyFun (fun z : X => z.1.2) := psnd polyFun_fst
  exact ((ho.pair polyFun_id).comp
    (PolyFun.optionElim hrun (polyFun_const none))).of_eq (fun _ => rfl)

theorem polyFun_topclInit : PolyFun topclInit := psnd (psnd (psnd polyFun_fst))

theorem polyFun_topclCombine : PolyFun topclCombine := psnd (psnd polyFun_snd)

/-- Finishing the parent phase reads the last answer. The leaf solver belongs
to the recursive caller and is not asserted to be polynomial here. -/
theorem polyFun_topclParentFinish (solve : RawWinSI → RawCoset) :
    PolyFun (fun z : TopCosetChainInput × RawCoset => topclFinish solve ((z.1, none), z.2)) :=
  polyFun_snd

end Algo
