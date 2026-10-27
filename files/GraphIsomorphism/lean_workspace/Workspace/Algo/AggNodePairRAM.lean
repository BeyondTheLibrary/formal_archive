import Workspace.Algo.AggNodePairPrepare

/-! # Machine bounds for the paired comparison steps

Every routine is bounded on all raw inputs. The two prepared descents use
the established group routines and never invoke the recursive solver.
-/
set_option synthInstance.maxSize 1024
set_option maxHeartbeats 1000000
namespace Algo
open RAM RAM.Targets

private theorem pfst {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {f : α → β × γ}
    (h : PolyFun f) : PolyFun (fun a => (f a).1) := h.comp polyFun_fst
private theorem psnd {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {f : α → β × γ}
    (h : PolyFun f) : PolyFun (fun a => (f a).2) := h.comp polyFun_snd
private theorem plt : PolyFun (fun p : ℕ × ℕ => decide (p.1 < p.2)) := by
  have h := (((polyFun_fst.pair (polyFun_const 1)).comp polyFun_add).pair polyFun_snd).comp polyFun_le
  exact h.of_eq (fun _ => by simp only [Nat.add_one_le_iff])
private theorem pand {α : Type*} [Enc α] {p q : α → Bool}
    (hp : PolyFun p) (hq : PolyFun q) : PolyFun (fun a => p a && q a) :=
  (PolyFun.ite hp hq (polyFun_const false)).of_eq (fun a => by cases p a <;> rfl)

theorem aggnPolyFun_isSome {α : Type*} [Enc α] : PolyFun (@Option.isSome α) := by
  have h : PolyFun (fun z : Option α × Bool => z.1.elim false (fun _ => true)) :=
    PolyFun.optionElim (polyFun_const false) (polyFun_const true)
  exact ((polyFun_id.pair (polyFun_const false)).comp h).of_eq
    (fun z => by cases z <;> rfl)

theorem aggnQuasiFun_pairInput (c : ℕ) :
    QuasiFun (fun z : RawLCLoop × RawStr × RawCoset × Option RawCoset =>
      aggnPairInput c z.1 z.2.1 z.2.2.1 z.2.2.2) := by
  have hp : PolyFun (fun z : RawLCLoop × RawStr × RawCoset × Option RawCoset => z.1) := polyFun_fst
  have hy : PolyFun (fun z : RawLCLoop × RawStr × RawCoset × Option RawCoset => z.2.1) := pfst polyFun_snd
  have hq := pfst (psnd (psnd (polyFun_id : PolyFun (fun z : RawLCLoop × RawStr × RawCoset × Option RawCoset => z))))
  have hm := psnd (psnd (psnd (polyFun_id : PolyFun (fun z : RawLCLoop × RawStr × RawCoset × Option RawCoset => z))))
  have hs := hp.comp_quasiFun (aggnQuasiFun_recomputeInput c)
  have ht := (hp.pair (hy.pair hq)).comp_quasiFun (aggnQuasiFun_compareInput c)
  exact ((hm.pair polyFun_id).comp_quasiFun
    (QuasiFun.optionElim hs (polyFun_snd.comp_quasiFun ht))).of_eq (fun _ => rfl)

theorem aggnQuasiFun_pairStart (c : ℕ) :
    QuasiFun (fun z : RawLCLoop × RawStr × RawCoset × Option RawCoset =>
      aggnPairStart c z.1 z.2.1 z.2.2.1 z.2.2.2) := by
  have hp := aggnQuasiFun_pairInput c
  have hi := (hp.pair (quasiFun_const (none : Option RawWinSI))).comp_poly aggnPolyFun_recomputeInit
  have hz : PolyFun (fun z : RawLCLoop × RawStr × RawCoset × Option RawCoset => z) := polyFun_id
  exact (pfst hz).quasiFun.pair ((pfst (psnd (psnd hz))).quasiFun.pair
    ((psnd (psnd (psnd hz))).quasiFun.pair (hp.pair ((quasiFun_const 0).pair hi))))

theorem aggnQuasiFun_pairPack (c : ℕ) :
    QuasiFun (fun z : RawLCLoop × RawStr × RawCoset × Option RawCoset × ℕ × AggnRecomputeState =>
      aggnPairPack c z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2.1 z.2.2.2.2.2) := by
  let X := RawLCLoop × RawStr × RawCoset × Option RawCoset × ℕ × AggnRecomputeState
  have hz : PolyFun (fun z : X => z) := polyFun_id
  have hp := pfst hz
  have hy := pfst (psnd hz)
  have hq := pfst (psnd (psnd hz))
  have hm := pfst (psnd (psnd (psnd hz)))
  have hj := pfst (psnd (psnd (psnd (psnd hz))))
  have hv := psnd (psnd (psnd (psnd (psnd hz))))
  have hcache := (hp.pair (hy.pair (hq.pair hm))).comp_quasiFun (aggnQuasiFun_pairInput c)
  have hcount := hcache.comp_poly ((pfst (psnd polyFun_snd)).comp polyFun_length)
  have htest := ((pfst hv).quasiFun.pair hcount).comp_poly plt
  have hthen := hp.quasiFun.pair (hq.quasiFun.pair (hm.quasiFun.pair
    (hcache.pair (hj.pair hv).quasiFun)))
  have hans := psnd (psnd (psnd hv))
  have hsource := (hp.pair (hy.pair (hq.pair (hans.comp polyFun_some)))).comp_quasiFun
    (aggnQuasiFun_pairStart c)
  have htarget : QuasiFun (fun z : RawCoset × X =>
      aggnPairStart c (lcStepWith z.1 z.2.1) z.2.2.1 z.2.2.2.2.2.2.2.2.2 none) := by
    have hnext := (polyFun_fst.pair (polyFun_snd.comp hp)).comp lcwPolyFun_step
    exact (hnext.pair ((polyFun_snd.comp hy).pair
      ((polyFun_snd.comp hans).pair (polyFun_const (none : Option RawCoset))))).comp_quasiFun
        (aggnQuasiFun_pairStart c)
  have helse := (hm.pair hz).comp_quasiFun (QuasiFun.optionElim hsource htarget)
  exact (aggnQuasiFun_ite htest hthen helse).of_eq (fun z => by
    simp only [aggnPairPack, aggnrCount, decide_eq_true_eq]
    rfl)

theorem aggnPolyFun_pairActive : PolyFun aggnPairActive :=
  pand (polyFun_fst.comp polyFun_lcCond)
    ((polyFun_snd.comp polyFun_fst).comp aggnPolyFun_isSome)

theorem aggnPolyFun_pairWidth : PolyFun aggnPairWidth :=
  ((polyFun_const 2).pair (polyFun_fst.comp aggnPolyFun_certWidth)).comp polyFun_mul

theorem aggnPolyFun_pairChild : PolyFun aggnPairChild := by
  let X := AggnPairNode × ℕ × AggnPairState
  have hz : PolyFun (fun z : X => z) := polyFun_id
  have hp := pfst (pfst hz)
  have ho := psnd (pfst hz)
  have hj := pfst (psnd hz)
  have hs := psnd (psnd hz)
  have hgate := pand (hs.comp aggnPolyFun_pairActive)
    ((hj.pair (hp.comp aggnPolyFun_pairWidth)).comp plt)
  have hcache := pfst (psnd (psnd (psnd hs)))
  have hj' := pfst (psnd (psnd (psnd (psnd hs))))
  have hv := psnd (psnd (psnd (psnd (psnd hs))))
  have hin := (hcache.pair (polyFun_const (none : Option RawWinSI))).pair (hj'.pair hv)
  have hchild := hin.comp aggnPolyFun_recomputeChild
  have hbody : PolyFun (fun z : AggnRecomputeNode × X => some (z.2.1.1, z.1.2)) :=
    (((polyFun_snd.comp hp).pair (psnd polyFun_fst)).comp polyFun_some)
  have hmap := (hchild.pair hz).comp (PolyFun.optionElim (polyFun_const none) hbody)
  have hrun := PolyFun.ite hgate hmap (polyFun_const none)
  exact ((ho.pair hz).comp (PolyFun.optionElim hrun (polyFun_const none))).of_eq (fun z => by
    simp only [aggnPairChild, aggnPairActive, Bool.and_eq_true, decide_eq_true_eq]
    cases he : z.1.2 with
    | some W => simp
    | none =>
      simp only [Option.elim_none]
      by_cases hc : lcCond z.2.2.1 = true ∧ z.2.2.2.1.isSome = true ∧
          z.2.1 < aggnPairWidth z.1.1
      · rw [if_pos hc, if_pos ⟨⟨hc.1, hc.2.1⟩, hc.2.2⟩]
        cases aggnrChild ((z.2.2.2.2.2.1, none), z.2.2.2.2.2.2.1, z.2.2.2.2.2.2.2) <;> rfl
      · rw [if_neg hc, if_neg (by tauto)])

theorem aggnQuasiFun_pairCombine (c : ℕ) : QuasiFun (aggnPairCombine c) := by
  have hz : PolyFun (fun z : AggnPairNode × ℕ × AggnPairState × RawCoset => z) := polyFun_id
  have hs := pfst (psnd (psnd hz))
  have hy := pfst (psnd (pfst (pfst hz)))
  have hcache := pfst (psnd (psnd (psnd hs)))
  have hj := pfst (psnd (psnd (psnd (psnd hs))))
  have hv := psnd (psnd (psnd (psnd (psnd hs))))
  have ha := psnd (psnd (psnd hz))
  have hr := ((hcache.pair (polyFun_const (none : Option RawWinSI))).pair
    (hj.pair (hv.pair ha))).comp aggnPolyFun_recomputeCombine
  exact ((pfst hs).pair (hy.pair ((pfst (psnd hs)).pair
    ((pfst (psnd (psnd hs))).pair (((hj.pair (polyFun_const 1)).comp polyFun_add).pair hr))))).comp_quasiFun
      (aggnQuasiFun_pairPack c)

end Algo
