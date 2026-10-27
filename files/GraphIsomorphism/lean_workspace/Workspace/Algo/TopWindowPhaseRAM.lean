import Workspace.Algo.TopWindowPhaseMatch

/-! # RAM routines of the restricted top-action carrier -/
set_option synthInstance.maxSize 1024
namespace Algo
open RAM RAM.Targets

private theorem pfst {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {f : α → β × γ}
    (h : PolyFun f) : PolyFun (fun a => (f a).1) := h.comp polyFun_fst
private theorem psnd {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {f : α → β × γ}
    (h : PolyFun f) : PolyFun (fun a => (f a).2) := h.comp polyFun_snd
private theorem pbind {α β σ : Type*} [Enc α] [Enc β] [Enc σ]
    {f : α × σ → Option β} (hf : PolyFun f) :
    PolyFun (fun z : Option α × σ => z.1.bind (fun a => f (a, z.2))) :=
  (PolyFun.optionElim (polyFun_const none) hf).of_eq (fun z => by cases z.1 <;> rfl)

 theorem polyFun_topwpAccept (e f : ℕ) : PolyFun (topwpAccept e f) := by
  have htest : PolyFun (fun p : TopwpContext × RawWinSI =>
      decide (Enc.size p.2 ≤ topcsContextCap e f (Enc.size p.1))) :=
    (polyFun_snd.comp AggnSizeRoutine.polyFun_size).le
      ((polyFun_fst.comp AggnSizeRoutine.polyFun_size).comp (polyFun_topcsContextCap e f))
  exact (PolyFun.ite htest ((polyFun_fst.pair (polyFun_snd.comp polyFun_some)).comp polyFun_some)
    (polyFun_const none)).of_eq (fun _ => by simp [topwpAccept])

private def topwpLift (e f : ℕ) (p : TopwpContext × Option RawWinSI) : Option TopwpNode :=
  p.2.bind fun W => (topwRawInstance (p.1.1, W)).bind fun V => topwpAccept e f (p.1, V)

private theorem polyFun_topwpLift (e f : ℕ) : PolyFun (topwpLift e f) := by
  have hpre : PolyFun (fun z : RawWinSI × TopwpContext => topwRawInstance (z.2.1, z.1)) :=
    ((pfst polyFun_snd).pair polyFun_fst).comp polyFun_topwRawInstance
  have hpost : PolyFun (fun z : RawWinSI × TopwpContext => topwpAccept e f (z.2, z.1)) :=
    (polyFun_snd.pair polyFun_fst).comp (polyFun_topwpAccept e f)
  have hrun := (hpre.pair polyFun_snd).comp (pbind hpost)
  exact (polyFun_snd.pair polyFun_fst).comp (pbind hrun)

 theorem polyFun_topwpChild (e f : ℕ) : PolyFun (topwpChild e f) := by
  let X := TopwpNode × ℕ × TopcsState
  have hC : PolyFun (fun z : X => z.1.1) := pfst polyFun_fst
  have hP := psnd hC
  have hinner := (((hP.pair (polyFun_const (none : Option RawWinSI))).pair polyFun_snd).comp polyFun_topcsChild)
  have hbody : PolyFun (fun z : TopcsNode × X => topwpLift e f (z.2.1.1, z.1.2)) :=
    ((polyFun_snd.comp hC).pair (psnd polyFun_fst)).comp (polyFun_topwpLift e f)
  have hmain := (hinner.pair polyFun_id).comp (pbind hbody)
  exact (((psnd polyFun_fst).pair polyFun_id).comp
    (PolyFun.optionElim hmain (polyFun_const none))).of_eq (fun _ => rfl)

 theorem polyFun_topwpInit : PolyFun topwpInit :=
  (((psnd polyFun_fst).pair (polyFun_const (none : Option RawWinSI))).comp polyFun_topcsInit)

 theorem polyFun_topwpCombine : PolyFun topwpCombine := by
  let X := TopwpNode × ℕ × TopcsState × RawCoset
  have hC : PolyFun (fun z : X => z.1.1) := pfst polyFun_fst
  have hP := psnd hC
  have hOuter := pfst hC
  have hd := pfst (pfst hOuter)
  have hw := pfst (psnd hOuter)
  have ha : PolyFun (fun z : X => z.2.2.2) := psnd (psnd polyFun_snd)
  have hi := (hd.pair (hw.pair ha)).comp polyFun_topwCosetImage
  exact (((hP.pair (polyFun_const (none : Option RawWinSI))).pair
    ((pfst polyFun_snd).pair ((pfst (psnd polyFun_snd)).pair hi))).comp polyFun_topcsCombine)

 theorem quasiFun_topwpFinish {solve : RawWinSI → RawCoset} (hs : QuasiFun solve) :
    QuasiFun (topwpFinish solve) := by
  let X := TopwpNode × TopcsState
  have hC : PolyFun (fun z : X => z.1.1) := pfst polyFun_fst
  have hP := psnd hC
  have hOuter := pfst hC
  have hg := pfst hOuter
  have hw := pfst (psnd hOuter)
  have hx := psnd (psnd hOuter)
  have hanswer := ((((hP.pair polyFun_snd).comp polyFun_topcsAnswer).pair
    (polyFun_const (none : RawCoset))).comp polyFun_optionGetD)
  have hpre := (hg.pair (hw.pair hanswer)).comp polyFun_topwCosetPreimage
  have hchoose := (((psnd polyFun_fst).pair polyFun_id).quasiFun.comp
    (QuasiFun.optionElim hpre.quasiFun (polyFun_fst.comp_quasiFun hs)))
  exact (hx.quasiFun.pair hchoose).comp polyFun_top2NormC.quasiFun

 def topwpCheck (c d e f : ℕ) (I : TopwpNode) : Bool :=
  decide (Enc.size I.1 ≤ topcsContextCap c d I.1.1.2.2.length) &&
    I.2.elim true (fun W => decide (Enc.size W ≤ topcsContextCap e f (Enc.size I.1)))

 theorem topwpCheck_spec (c d e f : ℕ) (I : TopwpNode) :
    topwpCheck c d e f I = true ↔ TopwpWF c d e f I := by
  cases ho : I.2 <;> simp [topwpCheck, TopwpWF, ho]

 theorem polyFun_topwpCheck (c d e f : ℕ) : PolyFun (topwpCheck c d e f) := by
  have hC : PolyFun (fun I : TopwpNode => I.1) := polyFun_fst
  have hx := psnd (psnd (pfst hC))
  have hsize := hC.comp AggnSizeRoutine.polyFun_size
  have hcap := hsize.comp (polyFun_topcsContextCap e f)
  have htest := hsize.le ((hx.comp polyFun_length).comp (polyFun_topcsContextCap c d))
  have hleaf : PolyFun (fun z : RawWinSI × TopwpNode =>
      decide (Enc.size z.1 ≤ topcsContextCap e f (Enc.size z.2.1))) :=
    (polyFun_fst.comp AggnSizeRoutine.polyFun_size).le (polyFun_snd.comp hcap)
  have hopt := (polyFun_snd.pair polyFun_id).comp (PolyFun.optionElim (polyFun_const true) hleaf)
  exact (PolyFun.ite htest hopt (polyFun_const false)).of_eq (fun I => by
    simp only [topwpCheck]
    cases decide (Enc.size I.1 ≤ topcsContextCap c d I.1.1.2.2.length) <;> rfl)

 theorem polyFun_topwpGround : PolyFun (fun I : TopwpNode => I.1.1.2.2.length) :=
  (psnd (psnd (pfst polyFun_fst))).comp polyFun_length

end Algo
