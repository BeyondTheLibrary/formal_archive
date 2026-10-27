/-
An explicit running time for Theorem 1.1.1 (Babai, version 2.5): one step of the depth-first
evaluator, bounded at an external degree. Not part of the faithful formalization.
-/
import Workspace.Explicit.NodeTN
import Workspace.Algo.EvaluatorQ

/-!
# One step of the evaluator, bounded at an external degree

`Explicit.TN.stepDFS`: the proof of `Algo.Round.quasiFun_stepDFS_of_routines` in the class
`Explicit.TN`. Each of the four routines of the round needs its bound only on the arguments the
step actually hands it, as read off the state by the precondition.
-/

namespace Explicit

open RAM Algo

namespace TN

variable {ι ω α : Type*} [Enc ι] [Enc ω] [Enc α]

/-- **One step of the evaluator.** -/
theorem stepDFS (R : Round ι ω α) {Pre : ℕ → Round.EvalState ι ω α → Prop}
    {PC : ℕ → Round.Frame ι ω → Prop} {PI : ℕ → ι → Prop}
    {PCo : ℕ → ι × ℕ × ω × α → Prop} {PF : ℕ → ι × ω → Prop} {k : ℕ}
    (hchild : TN R.child PC k) (hinit : TN R.init PI k) (hcombine : TN R.combine PCo k)
    (hfinish : TN R.finish PF k)
    (hPC : ∀ n fr rest, Pre n (fr :: rest, none) → PC n fr)
    (hPI : ∀ n fr rest J, Pre n (fr :: rest, none) → R.child fr = some J → PI n J)
    (hPF : ∀ n (I : ι) j s rest, Pre n ((I, j, s) :: rest, none) → R.child (I, j, s) = none →
      PF n (I, s))
    (hPCo : ∀ n (I : ι) j s rest a, Pre n ((I, j, s) :: rest, some a) → PCo n (I, j, s, a)) :
    TN R.stepDFS Pre k := by
  have hnil : TN (fun ret : Option α => (([] : List (Round.Frame ι ω)), ret))
      (fun _ _ => True) k :=
    ofPoly ((polyFun_const _).pair polyFun_id) _ k
  have hfold : TN (fun x : α × (Round.Frame ι ω × List (Round.Frame ι ω)) =>
      (((x.2.1.1, x.2.1.2.1 + 1, R.combine (x.2.1.1, x.2.1.2.1, x.2.1.2.2, x.1)) :: x.2.2,
        (none : Option α)) : Round.EvalState ι ω α))
      (fun n x => PCo n (x.2.1.1, x.2.1.2.1, x.2.1.2.2, x.1)) k := by
    have ha : PolyFun (fun x : α × (Round.Frame ι ω × List (Round.Frame ι ω)) => x.1) :=
      polyFun_fst
    have hfr : PolyFun (fun x : α × (Round.Frame ι ω × List (Round.Frame ι ω)) => x.2.1) :=
      polyFun_snd.comp polyFun_fst
    have hI : PolyFun (fun x : α × (Round.Frame ι ω × List (Round.Frame ι ω)) => x.2.1.1) :=
      hfr.comp polyFun_fst
    have hj : PolyFun (fun x : α × (Round.Frame ι ω × List (Round.Frame ι ω)) => x.2.1.2.1) :=
      (hfr.comp polyFun_snd).comp polyFun_fst
    have hs : PolyFun (fun x : α × (Round.Frame ι ω × List (Round.Frame ι ω)) => x.2.1.2.2) :=
      (hfr.comp polyFun_snd).comp polyFun_snd
    have hrest : PolyFun (fun x : α × (Round.Frame ι ω × List (Round.Frame ι ω)) => x.2.2) :=
      polyFun_snd.comp polyFun_snd
    have hcomb := poly_comp (hI.pair (hj.pair (hs.pair ha))) hcombine
    have hframe := (ofPoly hI _ k).pair ((ofPoly (hj.add (polyFun_const 1)) _ k).pair hcomb)
    exact ((hframe.pair (ofPoly hrest _ k)).comp_poly polyFun_cons).pair
      (ofPoly (polyFun_const _) _ k)
  have hpop : TN (fun y : Round.Frame ι ω × List (Round.Frame ι ω) =>
      ((y.2, some (R.finish (y.1.1, y.1.2.2))) : Round.EvalState ι ω α))
      (fun n y => PF n (y.1.1, y.1.2.2)) k := by
    have hI : PolyFun (fun y : Round.Frame ι ω × List (Round.Frame ι ω) => y.1.1) :=
      polyFun_fst.comp polyFun_fst
    have hs : PolyFun (fun y : Round.Frame ι ω × List (Round.Frame ι ω) => y.1.2.2) :=
      (polyFun_fst.comp polyFun_snd).comp polyFun_snd
    exact (ofPoly polyFun_snd _ k).pair ((poly_comp (hI.pair hs) hfinish).comp_poly polyFun_some)
  have hpush : TN (fun z : ι × (Round.Frame ι ω × List (Round.Frame ι ω)) =>
      (((z.1, 0, R.init z.1) :: z.2.1 :: z.2.2, (none : Option α)) : Round.EvalState ι ω α))
      (fun n z => PI n z.1) k := by
    have hJ : PolyFun (fun z : ι × (Round.Frame ι ω × List (Round.Frame ι ω)) => z.1) :=
      polyFun_fst
    have hfr : PolyFun (fun z : ι × (Round.Frame ι ω × List (Round.Frame ι ω)) => z.2.1) :=
      polyFun_snd.comp polyFun_fst
    have hrest : PolyFun (fun z : ι × (Round.Frame ι ω × List (Round.Frame ι ω)) => z.2.2) :=
      polyFun_snd.comp polyFun_snd
    have hframe := (ofPoly hJ _ k).pair ((ofPoly (polyFun_const 0) _ k).pair
      (poly_comp hJ hinit))
    have htail := ofPoly ((hfr.pair hrest).comp polyFun_cons) (fun n z => PI n z.1) k
    exact ((hframe.pair htail).comp_poly polyFun_cons).pair (ofPoly (polyFun_const _) _ k)
  have hask : TN (fun y : Round.Frame ι ω × List (Round.Frame ι ω) => (R.child y.1, y))
      (fun n y => PC n y.1) k :=
    (poly_comp polyFun_fst hchild).pair (ofPoly polyFun_id _ k)
  have hnone : TN (fun y : Round.Frame ι ω × List (Round.Frame ι ω) =>
      (match R.child y.1 with
        | some J => (((J, 0, R.init J) :: y.1 :: y.2, none) : Round.EvalState ι ω α)
        | none => (y.2, some (R.finish (y.1.1, y.1.2.2)))))
      (fun n y => PC n y.1 ∧ (R.child y.1 = none → PF n (y.1.1, y.1.2.2)) ∧
        ∀ J, R.child y.1 = some J → PI n J) k := by
    have hel := optionElim (Pre := fun n (p : Option ι × (Round.Frame ι ω ×
        List (Round.Frame ι ω))) => (p.1 = none → PF n (p.2.1.1, p.2.1.2.2)) ∧
        ∀ J, p.1 = some J → PI n J) hpop hpush (fun n s h => h.1 rfl)
      (fun n x s h => h.2 x rfl)
    refine ((hask.restrict (fun n y h => h.1)).comp hel (fun n y h => h.2)).of_eq
      (fun y => ?_)
    cases h : R.child y.1 with
    | none => simp [h]
    | some J => simp [h]
  have hbody : TN (fun w : (Round.Frame ι ω × List (Round.Frame ι ω)) × Option α =>
      (match w.2 with
        | some a => (((w.1.1.1, w.1.1.2.1 + 1,
            R.combine (w.1.1.1, w.1.1.2.1, w.1.1.2.2, a)) :: w.1.2, none) :
              Round.EvalState ι ω α)
        | none =>
            match R.child w.1.1 with
            | some J => ((J, 0, R.init J) :: w.1.1 :: w.1.2, none)
            | none => (w.1.2, some (R.finish (w.1.1.1, w.1.1.2.2)))))
      (fun n w => Pre n (w.1.1 :: w.1.2, w.2)) k := by
    have hel := optionElim (Pre := fun n (p : Option α × (Round.Frame ι ω ×
        List (Round.Frame ι ω))) => Pre n (p.2.1 :: p.2.2, p.1)) hnone hfold
      (fun n s h => ⟨hPC n _ _ h, fun hc => by
        obtain ⟨⟨I, j, s'⟩, rest⟩ := s
        exact hPF n I j s' rest h hc, fun J hJ => hPI n _ _ J h hJ⟩)
      (fun n x s h => by
        obtain ⟨⟨I, j, s'⟩, rest⟩ := s
        exact hPCo n I j s' rest x h)
    refine ((ofPoly (polyFun_swap (α := Round.Frame ι ω × List (Round.Frame ι ω))
      (β := Option α)) _ k).comp hel (fun n w h => h)).of_eq (fun w => ?_)
    cases h : w.2 with
    | none => simp [h]
    | some a => simp [h]
  refine (listCases (Pre := fun n p => Pre n p) hnil hbody (fun _ _ _ => trivial)
    (fun n x l s h => h)).of_eq (fun x => ?_)
  obtain ⟨st, ret⟩ := x
  cases st with
  | nil => rfl
  | cons fr rest =>
    obtain ⟨I, j, s⟩ := fr
    cases ret with
    | some a => rfl
    | none =>
      cases hc : R.child (I, j, s) with
      | none => rw [R.stepDFS_pop rest hc]; simp [hc]
      | some J => rw [R.stepDFS_push rest hc]; simp [hc]

/-- **One step with the loop counter**, the form of `Explicit.StepBounds.step`. -/
theorem stepDFS_counter (R : Round ι ω α) {Pre : ℕ → Round.EvalState ι ω α → Prop} {k : ℕ}
    (h : TN R.stepDFS Pre k) :
    TN (fun x : ℕ × Round.EvalState ι ω α => (x.1 - 1, R.stepDFS x.2))
      (fun n x => Pre n x.2) k :=
  (ofPoly (polyFun_fst.sub (polyFun_const 1)) _ k).pair (poly_comp polyFun_snd h)

end TN

end Explicit
