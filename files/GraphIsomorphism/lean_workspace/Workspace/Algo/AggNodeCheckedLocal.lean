import Workspace.Algo.AggNodeCheckedRAM

/-! # Solver-free machine steps inside a certificate

These bounds include malformed inputs. The prepared representative table is
quasipolynomial. The other operations inspect stored lists or use the existing
polynomial group routines. No operation invokes the recursive solver.
-/
set_option synthInstance.maxSize 512
set_option maxHeartbeats 1000000
namespace Algo
open RAM RAM.Targets

private theorem pfst {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {f : α → β × γ}
    (h : PolyFun f) : PolyFun (fun a => (f a).1) := h.comp polyFun_fst
private theorem psnd {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {f : α → β × γ}
    (h : PolyFun f) : PolyFun (fun a => (f a).2) := h.comp polyFun_snd

/-- A quasipolynomial test may be computed before the branch is selected. -/
theorem aggnQuasiFun_ite {α β : Type*} [Enc α] [Enc β]
    {p : α → Bool} {f g : α → β} (hp : QuasiFun p) (hf : QuasiFun f) (hg : QuasiFun g) :
    QuasiFun (fun a => if p a then f a else g a) :=
  ((hp.pair quasiFun_id).comp (QuasiFun.ite polyFun_fst
    (polyFun_snd.comp_quasiFun hf) (polyFun_snd.comp_quasiFun hg))).of_eq (fun _ => rfl)

theorem aggnPolyFun_recomputeBegin :
    PolyFun (fun z : AggnRecomputeInput × ℕ => aggnrBegin z.1 z.2) := by
  have hp : PolyFun (fun z : AggnRecomputeInput × ℕ => z.1) := polyFun_fst
  have hk := pfst (psnd hp)
  have hrs := pfst (psnd (psnd hp))
  have hr := ((hrs.pair polyFun_snd).pair (polyFun_const ([] : RawPerm))).comp polyFun_getD
  exact (hk.pair hr).comp polyFun_some

theorem aggnPolyFun_recomputeInit : PolyFun aggnrInit := by
  have hp : PolyFun (fun z : AggnRecomputeNode => z.1) := polyFun_fst
  have hb := (hp.pair (polyFun_const 0)).comp aggnPolyFun_recomputeBegin
  have hw := (psnd (psnd (psnd hp))).comp polyFun_isEmpty
  have ha := ((pfst (psnd (pfst hp))).pair (pfst (psnd (psnd (pfst hp))))).comp polyFun_some
  exact (polyFun_const 0).pair ((polyFun_const 0).pair (hb.pair
    (PolyFun.ite hw ha (polyFun_const none))))

theorem aggnPolyFun_recomputeStep :
    PolyFun (fun z : AggnRecomputeInput × ℕ × ℕ × RawCoset × RawCoset =>
      aggnrStep z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2) := by
  let X := AggnRecomputeInput × ℕ × ℕ × RawCoset × RawCoset
  have hp : PolyFun (fun z : X => z.1) := polyFun_fst
  have ht : PolyFun (fun z : X => z.2.1) := pfst polyFun_snd
  have hi : PolyFun (fun z : X => z.2.2.1) := pfst (psnd polyFun_snd)
  have ha : PolyFun (fun z : X => z.2.2.2.1) := pfst (psnd (psnd polyFun_snd))
  have hb : PolyFun (fun z : X => z.2.2.2.2) := psnd (psnd (psnd polyFun_snd))
  have hw := (psnd (psnd (psnd hp))).comp polyFun_length
  have hc := (pfst (psnd (psnd hp))).comp polyFun_length
  have hnext := (hi.pair (polyFun_const 1)).comp polyFun_add
  have ht' := (((ht.pair (polyFun_const 1)).comp polyFun_add).pair hc).comp polyFun_min
  have hsome : PolyFun (fun z : X => z.2.2.2.2.isSome) := by
    have he : PolyFun (fun q : Option (RawGens × RawPerm) × X => q.1.elim false (fun _ => true)) :=
      PolyFun.optionElim (polyFun_const false) (polyFun_const true)
    exact ((hb.pair polyFun_id).comp he).of_eq (fun z => by cases z.2.2.2.2 <;> rfl)
  have hlt : PolyFun (fun z : X => decide (z.2.2.1 + 1 < (aggnrWindows z.1).length)) :=
    ((((hnext.pair (polyFun_const 1)).comp polyFun_add).pair hw).comp polyFun_le).of_eq
      (fun _ => by simp only [Nat.add_one_le_iff]; rfl)
  have htest := PolyFun.ite hsome hlt (polyFun_const false)
  have hthen := ((ht.pair hc).comp polyFun_min).pair
    (((hnext.pair hw).comp polyFun_min).pair (hb.pair ha))
  have hx := pfst (psnd (psnd (psnd (pfst hp))))
  have helse := ht'.pair ((polyFun_const 0).pair
    (((hp.pair ht').comp aggnPolyFun_recomputeBegin).pair
      ((hx.pair (ha.pair hb)).comp polyFun_rawCosetJoin)))
  exact (PolyFun.ite htest hthen helse).of_eq (fun z => by
    unfold aggnrStep
    cases z.2.2.2.2 <;> simp [aggnrCount, aggnrWindows])

theorem aggnPolyFun_recomputeCombine : PolyFun aggnrCombine := by
  have hz : PolyFun (fun z : AggnRecomputeNode × ℕ × AggnRecomputeState × RawCoset => z) := polyFun_id
  have hp := pfst (pfst hz)
  have hs := pfst (psnd (psnd hz))
  exact (hp.pair ((pfst hs).pair ((pfst (psnd hs)).pair
    ((psnd (psnd (psnd hs))).pair (psnd (psnd (psnd hz))))))).comp aggnPolyFun_recomputeStep

theorem aggnQuasiFun_recomputeInput (c : ℕ) : QuasiFun (aggnrInputOf c) := by
  have hi := polyFun_lcInst.comp polyFun_fst
  have hk := ((polyFun_lcTdom.pair polyFun_lcImgsOf).pair hi).comp polyFun_lcKer
  have hw := (hk.pair (pfst hi)).comp polyFun_winOrbits
  exact hi.quasiFun.pair (hk.quasiFun.pair ((aggkQuasiFun_rawReps c).pair hw.quasiFun))

theorem aggnQuasiFun_certOpen (c : ℕ) : QuasiFun (aggnCertOpen c) := by
  have hp := aggnQuasiFun_recomputeInput c
  have hi := (hp.pair (quasiFun_const (none : Option RawWinSI))).comp_poly aggnPolyFun_recomputeInit
  exact quasiFun_id.pair (hp.pair ((quasiFun_const 0).pair hi))

theorem aggnQuasiFun_certPack (c : ℕ) :
    QuasiFun (fun z : RawLCLoop × ℕ × AggnRecomputeState => aggnCertPack c z.1 z.2.1 z.2.2) := by
  have hp : PolyFun (fun z : RawLCLoop × ℕ × AggnRecomputeState => z.1) := polyFun_fst
  have hj : PolyFun (fun z : RawLCLoop × ℕ × AggnRecomputeState => z.2.1) := pfst polyFun_snd
  have hv : PolyFun (fun z : RawLCLoop × ℕ × AggnRecomputeState => z.2.2) := psnd polyFun_snd
  have hcache := hp.comp_quasiFun (aggnQuasiFun_recomputeInput c)
  have hcount := hcache.comp_poly ((pfst (psnd polyFun_snd)).comp polyFun_length)
  have htest := ((((pfst hv).pair (polyFun_const 1)).comp polyFun_add).quasiFun.pair hcount).comp_poly polyFun_le
  have hthen := hp.quasiFun.pair (hcache.pair (hj.pair hv).quasiFun)
  have helse := (((psnd (psnd (psnd hv))).pair hp).comp lcwPolyFun_step).comp_quasiFun
    (aggnQuasiFun_certOpen c)
  exact (aggnQuasiFun_ite htest hthen helse).of_eq (fun z => by
    simp only [aggnCertPack, aggnrCount, Nat.add_one_le_iff, decide_eq_true_eq]
    rfl)

theorem aggnQuasiFun_certCombine (c : ℕ) : QuasiFun (aggnCertCombine c) := by
  have hz : PolyFun (fun z : AggnCertNode × ℕ × AggnCertState × RawCoset => z) := polyFun_id
  have hs := pfst (psnd (psnd hz))
  have hP := pfst (psnd hs)
  have hj := pfst (psnd (psnd hs))
  have hv := psnd (psnd (psnd hs))
  have ha := psnd (psnd (psnd hz))
  have hr := (((hP.pair (polyFun_const (none : Option RawWinSI))).pair
    (hj.pair (hv.pair ha))).comp aggnPolyFun_recomputeCombine)
  have hres := ((pfst hs).pair (((hj.pair (polyFun_const 1)).comp polyFun_add).pair hr)).comp_quasiFun
    (aggnQuasiFun_certPack c)
  exact hres.of_eq (fun _ => rfl)

theorem aggnPolyFun_storeJob :
    PolyFun (fun z : AggnJob × AggnCertState × AggnStores => aggnStoreJob z.1 z.2.1 z.2.2) := by
  have ha : PolyFun (fun z : AggnJob × AggnCertState × AggnStores => z.1) := polyFun_fst
  have hv : PolyFun (fun z : AggnJob × AggnCertState × AggnStores => z.2.1) := pfst polyFun_snd
  have hs : PolyFun (fun z : AggnJob × AggnCertState × AggnStores => z.2.2) := psnd polyFun_snd
  have he := ((pfst (pfst (pfst hv))).pair ((psnd ha).pair
    ((pfst hv).comp lcwPolyFun_out))).comp aggPolyFun_pack
  exact (PolyFun.ite (pfst ha)
    ((pfst hs).pair ((he.pair (psnd hs)).comp polyFun_cons))
    (((he.pair (pfst hs)).comp polyFun_cons).pair (psnd hs))).of_eq (fun z => by
      unfold aggnStoreJob aggnCertOut
      cases z.1.1 <;> rfl)

end Algo
