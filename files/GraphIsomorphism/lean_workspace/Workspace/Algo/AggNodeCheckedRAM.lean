import Workspace.Algo.AggNodeChecked

/-! # Machine bounds for the checked child routine

All work inside the prepared Recompute cache is polynomial in the supplied
encoding. The phase width uses the guarded test-set table, whose construction
is quasipolynomial on every input. These bounds do not assume reachability.
-/
set_option synthInstance.maxSize 256

namespace Algo
open RAM RAM.Targets

private theorem plt : PolyFun (fun p : ℕ × ℕ => decide (p.1 < p.2)) := by
  have h := (((polyFun_fst.pair (polyFun_const 1)).comp polyFun_add).pair polyFun_snd).comp polyFun_le
  exact h.of_eq (fun _ => by simp only [Nat.add_one_le_iff])

private theorem pfst {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {f : α → β × γ}
    (h : PolyFun f) : PolyFun (fun a => (f a).1) := h.comp polyFun_fst

private theorem psnd {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {f : α → β × γ}
    (h : PolyFun f) : PolyFun (fun a => (f a).2) := h.comp polyFun_snd

private theorem pif {α β : Type*} [Enc α] [Enc β] {p : α → Prop}
    [∀ a, Decidable (p a)] {f g : α → β}
    (hp : PolyFun (fun a => decide (p a))) (hf : PolyFun f) (hg : PolyFun g) :
    PolyFun (fun a => if p a then f a else g a) :=
  (PolyFun.ite hp hf hg).of_eq (fun a => by simp)

private theorem pand {α : Type*} [Enc α] {p q : α → Prop}
    [∀ a, Decidable (p a)] [∀ a, Decidable (q a)]
    (hp : PolyFun (fun a => decide (p a))) (hq : PolyFun (fun a => decide (q a))) :
    PolyFun (fun a => decide (p a ∧ q a)) :=
  (pif hp hq (polyFun_const false)).of_eq (fun a => by by_cases h : p a <;> simp [h])

private theorem pmap {α β σ : Type*} [Enc α] [Enc β] [Enc σ] {f : α × σ → β}
    (hf : PolyFun f) : PolyFun (fun p : Option α × σ => p.1.map (fun a => f (a, p.2))) :=
  (PolyFun.optionElim (polyFun_const none) (hf.comp polyFun_some)).of_eq
    (fun p => by cases p.1 <;> rfl)

theorem aggnPolyFun_certWidth : PolyFun aggnCertWidth := by
  have hx : PolyFun (fun p : RawLCLoop => p.1.1.length) :=
    (pfst polyFun_fst).comp polyFun_length
  have ht : PolyFun (fun p : RawLCLoop => p.1.2.length) :=
    (psnd polyFun_fst).comp polyFun_length
  have hb : ∀ p : RawLCLoop, p.1.2.length ≤ Enc.size p := fun p =>
    (length_le_size p.1.2).trans ((size_snd_le' p.1).trans (size_fst_le' p))
  exact (hx.pair (((ht.factorial hb polyBound_id).pair hx).comp polyFun_mul)).comp polyFun_mul

theorem aggnPolyFun_recomputeLeaf :
    PolyFun (fun z : AggnRecomputeInput × ℕ × (RawGens × RawPerm) => aggnrLeaf z.1 z.2.1 z.2.2) := by
  have hp : PolyFun (fun z : AggnRecomputeInput × ℕ × (RawGens × RawPerm) => z.1) := polyFun_fst
  have hx := pfst (psnd (psnd (psnd (pfst hp))))
  have hy := psnd (psnd (psnd (psnd (pfst hp))))
  have hw := psnd (psnd (psnd hp))
  have hi : PolyFun (fun z : AggnRecomputeInput × ℕ × (RawGens × RawPerm) => z.2.1) :=
    pfst polyFun_snd
  have hq : PolyFun (fun z : AggnRecomputeInput × ℕ × (RawGens × RawPerm) => z.2.2) :=
    psnd polyFun_snd
  have hd := ((hw.pair hi).pair (polyFun_const ([] : List ℕ))).comp polyFun_getD
  exact hd.pair (((hx.pair (pfst hq)).comp polyFun_tidyGens).pair
    (((hx.pair (psnd hq)).comp polyFun_normPerm).pair (hx.pair hy)))

theorem aggnPolyFun_recomputeChild : PolyFun aggnrChild := by
  let X := AggnRecomputeNode × ℕ × AggnRecomputeState
  have hp : PolyFun (fun z : X => z.1.1) := pfst polyFun_fst
  have hs : PolyFun (fun z : X => z.2.2) := psnd polyFun_snd
  have hj : PolyFun (fun z : X => z.2.1) := pfst polyFun_snd
  have ht := pfst hs
  have hi := pfst (psnd hs)
  have hcur := pfst (psnd (psnd hs))
  have hcount := (pfst (psnd (psnd hp))).comp polyFun_length
  have hwin := (psnd (psnd (psnd hp))).comp polyFun_length
  have hgate := pand ((ht.pair hcount).comp plt)
    (pand ((hi.pair hwin).comp plt)
      ((hj.pair ((hcount.pair hwin).comp polyFun_mul)).comp plt))
  have hbody : PolyFun (fun z : (RawGens × RawPerm) × X =>
      (z.2.1.1, some (aggnrLeaf z.2.1.1 z.2.2.2.2.1 z.1))) := by
    have hp' : PolyFun (fun z : (RawGens × RawPerm) × X => z.2.1.1) := polyFun_snd.comp hp
    have hi' : PolyFun (fun z : (RawGens × RawPerm) × X => z.2.2.2.2.1) := polyFun_snd.comp hi
    exact hp'.pair (((hp'.pair (hi'.pair polyFun_fst)).comp aggnPolyFun_recomputeLeaf).comp polyFun_some)
  have hmap := (hcur.pair polyFun_id).comp (pmap hbody)
  have hrun := pif hgate hmap (polyFun_const none)
  have ho : PolyFun (fun z : X => z.1.2) := psnd polyFun_fst
  exact ((ho.pair polyFun_id).comp
    (PolyFun.optionElim hrun (polyFun_const none))).of_eq (fun _ => rfl)

theorem aggnPolyFun_certChild : PolyFun aggnCertChild := by
  let X := AggnCertNode × ℕ × AggnCertState
  have hp : PolyFun (fun z : X => z.1.1) := pfst polyFun_fst
  have hs : PolyFun (fun z : X => z.2.2) := psnd polyFun_snd
  have hj : PolyFun (fun z : X => z.2.1) := pfst polyFun_snd
  have hactive := (pfst hs).comp polyFun_lcCond
  have hgate : PolyFun (fun z : X => decide (lcCond z.2.2.1 = true ∧
      z.2.1 < aggnCertWidth z.1.1)) :=
    pand (hactive.of_eq (fun _ => by simp))
      ((hj.pair (hp.comp aggnPolyFun_certWidth)).comp plt)
  have hcache := pfst (psnd hs)
  have hj' := pfst (psnd (psnd hs))
  have hv := psnd (psnd (psnd hs))
  have hin := (hcache.pair (polyFun_const (none : Option RawWinSI))).pair (hj'.pair hv)
  have hchild := hin.comp aggnPolyFun_recomputeChild
  have hbody : PolyFun (fun z : AggnRecomputeNode × X => (z.2.1.1, z.1.2)) :=
    (polyFun_snd.comp hp).pair (psnd polyFun_fst)
  have hmap := (hchild.pair polyFun_id).comp (pmap hbody)
  have hrun := pif hgate hmap (polyFun_const none)
  have ho : PolyFun (fun z : X => z.1.2) := psnd polyFun_fst
  exact ((ho.pair polyFun_id).comp
    (PolyFun.optionElim hrun (polyFun_const none))).of_eq (fun _ => rfl)

theorem aggnPolyFun_jobLoop :
    PolyFun (fun z : AggnPhaseCtx × AggnJob => aggnJobLoop z.1 z.2) := by
  have hC : PolyFun (fun z : AggnPhaseCtx × AggnJob => z.1) := polyFun_fst
  have ha : PolyFun (fun z : AggnPhaseCtx × AggnJob => z.2) := polyFun_snd
  have hstr := PolyFun.ite (pfst ha) (pfst (psnd (psnd hC))) (pfst (psnd hC))
  exact ((hstr.pair (psnd ha)).pair (((pfst hC).pair (psnd ha)).comp
    aggnPolyFun_initialState)).of_eq (fun z => by unfold aggnJobLoop; cases z.2.1 <;> rfl)

theorem aggnQuasiFun_phaseWidth (c : ℕ) : QuasiFun (aggnPhaseWidth c) := by
  have hC : PolyFun (fun C : AggnPhaseCtx => C) := polyFun_id
  have hx := pfst (psnd hC)
  have ht := psnd (psnd (psnd hC))
  have hm := pfst (psnd (pfst hC))
  have hrows := (ht.pair (hx.pair hm)).comp_quasiFun (aggQuasiFun_testSetsOn c)
  have hn := hx.comp polyFun_length
  have hfact := ht.comp (polyFun_length.factorial length_le_size polyBound_id)
  have hwidth := (hn.pair ((hfact.pair hn).comp polyFun_mul)).comp polyFun_mul
  have hlen := ((polyFun_const 2).quasiFun.pair (hrows.comp_poly polyFun_length)).comp_poly polyFun_mul
  exact ((hlen.pair hwidth.quasiFun).comp_poly polyFun_mul).of_eq (fun C => by
    simp [aggnPhaseWidth, aggnPhaseJobs, aggnPhaseRows, two_mul])

/-- All local tests and cache reads, after the global width has been supplied. -/
private theorem aggnPolyFun_phaseChildAtWidth :
    PolyFun (fun p : ℕ × (AggnPhaseNode × ℕ × AggnPhaseState) =>
      p.2.1.2.elim
        (if p.2.2.1 < p.1 then
          match p.2.2.2.1 with
          | [] => none
          | a :: _ =>
            (aggnCertChild ((aggnJobLoop p.2.1.1 a, none),
              p.2.2.2.2.2.1, p.2.2.2.2.2.2)).map (fun J => (p.2.1.1, J.2))
        else none) (fun _ => none)) := by
  let X := ℕ × (AggnPhaseNode × ℕ × AggnPhaseState)
  have hC : PolyFun (fun z : X => z.2.1.1) := pfst (pfst polyFun_snd)
  have hs : PolyFun (fun z : X => z.2.2.2) := psnd (psnd polyFun_snd)
  have hj : PolyFun (fun z : X => z.2.2.1) := pfst (psnd polyFun_snd)
  have hj' := pfst (psnd (psnd hs))
  have hv := psnd (psnd (psnd hs))
  have hbody : PolyFun (fun z : (AggnJob × List AggnJob) × X =>
      (aggnCertChild ((aggnJobLoop z.2.2.1.1 z.1.1, none),
        z.2.2.2.2.2.2.1, z.2.2.2.2.2.2.2)).map (fun J => (z.2.2.1.1, J.2))) := by
    have hp : PolyFun (fun z : (AggnJob × List AggnJob) × X =>
        aggnJobLoop z.2.2.1.1 z.1.1) :=
      ((polyFun_snd.comp hC).pair (pfst polyFun_fst)).comp aggnPolyFun_jobLoop
    have hi := (hp.pair (polyFun_const (none : Option RawWinSI))).pair
      ((polyFun_snd.comp hj').pair (polyFun_snd.comp hv))
    have hf : PolyFun (fun z : AggnCertNode × ((AggnJob × List AggnJob) × X) =>
        (z.2.2.2.1.1, z.1.2)) :=
      ((psnd polyFun_snd).comp hC).pair (psnd polyFun_fst)
    exact ((hi.comp aggnPolyFun_certChild).pair polyFun_id).comp (pmap hf)
  have hlist := ((pfst hs).pair polyFun_id).comp
    (PolyFun.listCases (polyFun_const none) hbody)
  have htest := (hj.pair polyFun_fst).comp plt
  have hrun := pif htest hlist (polyFun_const none)
  have ho : PolyFun (fun z : X => z.2.1.2) := psnd (pfst polyFun_snd)
  exact ((ho.pair polyFun_id).comp
    (PolyFun.optionElim hrun (polyFun_const none))).of_eq (fun p => by
      simp only [id_eq]
      cases p.2.2.2.1 <;> rfl)

/-- The raw selector is quasipolynomial even for arbitrary cached states. -/
theorem aggnQuasiFun_phaseChild (c : ℕ) : QuasiFun (aggnPhaseChild c) := by
  have hC : PolyFun (fun z : AggnPhaseNode × ℕ × AggnPhaseState => z.1.1) :=
    pfst polyFun_fst
  exact (((hC.comp_quasiFun (aggnQuasiFun_phaseWidth c)).pair polyFun_id.quasiFun).comp_poly
    aggnPolyFun_phaseChildAtWidth).of_eq (fun _ => rfl)

/-- The checked child routine has a machine bound on every raw input. -/
theorem aggnQuasiFun_checkedChild (c : ℕ) : QuasiFun (aggnCheckedChild c) := by
  have hf : PolyFun (fun z : AggnPhaseNode × Option AggnPhaseNode => aggnCheckedNode z.1) :=
    polyFun_fst.comp aggnPolyFun_checkedNode
  have hm : PolyFun (fun o : Option AggnPhaseNode => o.map aggnCheckedNode) :=
    ((polyFun_id.pair polyFun_id).comp (pmap hf)).of_eq (fun _ => rfl)
  exact (aggnQuasiFun_phaseChild c).comp_poly hm

end Algo
