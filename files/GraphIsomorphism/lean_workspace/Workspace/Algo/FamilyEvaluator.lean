import Workspace.Algo.EvaluatorQ
import Workspace.Algo.AggNodeSizeRoutine

/-! Section 9 returns a family, so its answer need not be polynomially
small. We run the same depth-first machine with a size cap fixed by the
original input. The cap bounds arbitrary raw executions. The equality
theorem removes it when the actual execution fits within that bound. -/
namespace Algo
open RAM

namespace FamilyEvaluator
variable {σ ι α : Type*} [Enc σ] [Enc ι] [Enc α]

def select (z : ℕ × (σ × σ)) : σ :=
  if Enc.size z.2.2 ≤ z.1 then z.2.2 else z.2.1

def step (next : σ → σ) (z : ℕ × σ) : ℕ × σ :=
  (z.1,select (z.1,(z.2,next z.2)))

theorem polyFun_select (hs : PolyFun (Enc.size : σ → ℕ)) :
    PolyFun (select (σ := σ)) := by
  have ht : PolyFun (fun z : ℕ × (σ × σ) => decide (Enc.size z.2.2 ≤ z.1)) :=
    (((polyFun_snd.comp polyFun_snd).comp hs).pair polyFun_fst).comp polyFun_le
  exact (PolyFun.ite ht (polyFun_snd.comp polyFun_snd)
    (polyFun_snd.comp polyFun_fst)).of_eq (fun z => by simp [select])

theorem quasiFun_step (hs : PolyFun (Enc.size : σ → ℕ))
    {next : σ → σ} (hn : QuasiFun next) : QuasiFun (step next) := by
  have hp : QuasiFun (fun z : ℕ × σ => (z.1,(z.2,next z.2))) :=
    polyFun_fst.quasiFun.pair
      (polyFun_snd.quasiFun.pair (polyFun_snd.quasiFun.comp hn))
  exact polyFun_fst.quasiFun.pair (hp.comp_poly (polyFun_select hs))

theorem iterate_fst (next : σ → σ) (cap : ℕ) (s : σ) (j : ℕ) :
    ((step next)^[j] (cap,s)).1 = cap := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply']; exact ih

theorem iterate_size (next : σ → σ) (cap : ℕ) (s : σ) (j : ℕ) :
    Enc.size (((step next)^[j] (cap,s)).2) ≤ Enc.size s + cap := by
  induction j with
  | zero => exact Nat.le_add_right _ _
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    change Enc.size (select _) ≤ _
    unfold select
    split
    · rename_i h
      dsimp only [Prod.fst,Prod.snd] at h ⊢
      rw [iterate_fst] at h
      omega
    · exact ih

theorem iterate_eq (next : σ → σ) (cap : ℕ) (s : σ) (j : ℕ)
    (hb : ∀ k, 0 < k → k ≤ j → Enc.size (next^[k] s) ≤ cap) :
    (step next)^[j] (cap,s) = (cap,next^[j] s) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply',ih (fun k hk hkj => hb k hk (by omega))]
    have h := hb (j+1) (by omega) le_rfl
    rw [Function.iterate_succ_apply'] at h
    simp only [step,select,if_pos h,Function.iterate_succ_apply']

def run (count cap : ι → ℕ) (init : ι → σ) (next : σ → σ)
    (read : σ → α) (I : ι) : α :=
  read (((step next)^[count I] (cap I,init I)).2)

theorem quasiFun_run (count cap : ι → ℕ) (init : ι → σ) (next : σ → σ)
    (read : σ → α) (hs : PolyFun (Enc.size : σ → ℕ))
    (hc : PolyFun count) (hk : PolyFun cap) (hi : QuasiFun init)
    (hn : QuasiFun next) (hr : QuasiFun read)
    (q b : ℕ → ℕ) (hq : QuasiPolyBound q) (hb : QuasiPolyBound b)
    (hcount : ∀ I, count I ≤ q (Enc.size I))
    (hcap : ∀ I, cap I ≤ b (Enc.size I)) :
    QuasiFun (run count cap init next read) := by
  have hstart := hk.quasiFun.pair hi
  obtain ⟨S,hS,_,hstartSize⟩ := hstart.size.exists_quasiPolyBound
  have hp : QuasiPolyBound (fun n => 4*S n + 2*b n) :=
    ((polyBound_const 4).quasiPoly.mul hS).add
      ((polyBound_const 2).quasiPoly.mul hb)
  refine QuasiFun.iterateSetup (setUp := fun I => (count I,(cap I,init I)))
    (step := step next) (readOff := fun z : ℕ × σ => read z.2)
    (q := q) (p := fun n => 4*S n + 2*b n)
    (hc.quasiFun.pair hstart) ?_ (polyFun_snd.quasiFun.comp hr)
    hcount hq ?_ hp
  · exact (polyFun_fst.sub (polyFun_const 1)).quasiFun.pair
      (polyFun_snd.quasiFun.comp (quasiFun_step hs hn))
  · intro I j _
    have hleft := size_fst_le' (cap I,init I)
    have hright := size_snd_le' (cap I,init I)
    have hstate := iterate_size next (cap I) (init I) j
    have hstart := hstartSize I
    have hbI := hcap I
    dsimp only [Prod.fst,Prod.snd] at hleft hright hstart
    calc Enc.size ((step next)^[j] (cap I,init I))
        = Enc.size (cap I,((step next)^[j] (cap I,init I)).2) := by
          congr 1
          exact Prod.ext (iterate_fst next (cap I) (init I) j) rfl
      _ ≤ 2 * Enc.size (cap I) +
          2 * Enc.size (((step next)^[j] (cap I,init I)).2) := Combine.size_pair_le _ _
      _ ≤ 4*S (Enc.size I) + 2*b (Enc.size I) := by omega

theorem run_eq (count cap : ι → ℕ) (init : ι → σ) (next : σ → σ)
    (read : σ → α) (I : ι)
    (hb : ∀ k, 0 < k → k ≤ count I → Enc.size (next^[k] (init I)) ≤ cap I) :
    run count cap init next read I = read (next^[count I] (init I)) := by
  rw [run,iterate_eq next (cap I) (init I) (count I) hb]

end FamilyEvaluator

namespace Round
variable {ι ω α : Type*} [Enc ι] [Enc ω] [Enc α] (R : Round ι ω α)

def runFamily (count cap : ι → ℕ) : ι → Option α :=
  FamilyEvaluator.run count cap R.startState R.stepDFS Prod.snd

theorem quasiFun_runFamily (count cap : ι → ℕ)
    (hc : PolyFun count) (hk : PolyFun cap)
    (hs : PolyFun (Enc.size : EvalState ι ω α → ℕ))
    (hchild : QuasiFun R.child) (hinit : QuasiFun R.init)
    (hcombine : QuasiFun R.combine) (hfinish : QuasiFun R.finish)
    (q b : ℕ → ℕ) (hq : QuasiPolyBound q) (hb : QuasiPolyBound b)
    (hcount : ∀ I, count I ≤ q (Enc.size I))
    (hcap : ∀ I, cap I ≤ b (Enc.size I)) : QuasiFun (R.runFamily count cap) := by
  have hframe := polyFun_id.quasiFun.pair ((polyFun_const 0).quasiFun.pair hinit)
  have hstart : QuasiFun R.startState :=
    ((hframe.pair (polyFun_const []).quasiFun).comp_poly polyFun_cons).pair
      (polyFun_const none).quasiFun
  exact FamilyEvaluator.quasiFun_run count cap R.startState R.stepDFS Prod.snd
    hs hc hk hstart (R.quasiFun_stepDFS_of_routines hchild hinit hcombine hfinish)
    polyFun_snd.quasiFun q b hq hb hcount hcap

theorem runFamily_eq_value (count cap : ι → ℕ) (f : ℕ) (I : ι)
    (hI : R.WF I) (hf : R.measure I < f) (hc : R.subSteps f I ≤ count I)
    (hb : ∀ k, 0 < k → k ≤ count I →
      Enc.size (R.stepDFS^[k] (R.startState I)) ≤ cap I) :
    R.runFamily count cap I = some (R.value f I) := by
  rw [runFamily,FamilyEvaluator.run_eq count cap R.startState R.stepDFS Prod.snd I hb]
  exact R.evaluate_eq_value f (count I) I hI hf hc

end Round
end Algo
