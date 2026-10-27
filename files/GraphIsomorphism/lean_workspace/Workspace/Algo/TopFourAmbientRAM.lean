import Workspace.Algo.TopFourAmbientMatch

/-! # Executable routines for the ambient top-action adapter -/
set_option synthInstance.maxSize 4096
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

private theorem pand {α : Type*} [Enc α] {p q : α → Bool}
    (hp : PolyFun p) (hq : PolyFun q) : PolyFun (fun x => p x && q x) :=
  (PolyFun.ite hp hq (polyFun_const false)).of_eq (fun x => by cases p x <;> rfl)

theorem polyFun_top4wAccept (u v : ℕ) : PolyFun (top4wAccept u v) := by
  have ht : PolyFun (fun p : Top4wContext × RawWinSI =>
      decide (Enc.size p.2 ≤ topcsContextCap u v (Enc.size p.1))) :=
    (polyFun_snd.comp AggnSizeRoutine.polyFun_size).le
      ((polyFun_fst.comp AggnSizeRoutine.polyFun_size).comp (polyFun_topcsContextCap u v))
  exact (PolyFun.ite ht ((polyFun_fst.pair (polyFun_snd.comp polyFun_some)).comp polyFun_some)
    (polyFun_const none)).of_eq (fun _ => by simp [top4wAccept])

private def top4wLift (u v : ℕ) (p : Top4wContext × Option RawWinSI) : Option Top4wNode :=
  p.2.bind fun W => (topwRawInstance (p.1.1, W)).bind fun V => top4wAccept u v (p.1, V)

private theorem polyFun_top4wLift (u v : ℕ) : PolyFun (top4wLift u v) := by
  have hpre : PolyFun (fun z : RawWinSI × Top4wContext => topwRawInstance (z.2.1, z.1)) :=
    ((pfst polyFun_snd).pair polyFun_fst).comp polyFun_topwRawInstance
  have hpost : PolyFun (fun z : RawWinSI × Top4wContext => top4wAccept u v (z.2, z.1)) :=
    (polyFun_snd.pair polyFun_fst).comp (polyFun_top4wAccept u v)
  exact (polyFun_snd.pair polyFun_fst).comp
    (pbind ((hpre.pair polyFun_snd).comp (pbind hpost)))

theorem polyFun_top4wChild (e f u v : ℕ) : PolyFun (top4wChild e f u v) := by
  let X := Top4wNode × ℕ × Top4State
  have hC : PolyFun (fun z : X => z.1.1) := pfst polyFun_fst
  have hinner := (((psnd hC).pair polyFun_snd).comp (polyFun_top4aChild e f))
  have hbody : PolyFun (fun z : Top4aNode × X => top4wLift u v (z.2.1.1, z.1.1.2)) :=
    ((polyFun_snd.comp hC).pair (psnd (pfst polyFun_fst))).comp (polyFun_top4wLift u v)
  have hmain := (hinner.pair polyFun_id).comp (pbind hbody)
  exact (((psnd polyFun_fst).pair polyFun_id).comp
    (PolyFun.optionElim hmain (polyFun_const none))).of_eq (fun _ => rfl)

theorem polyFun_top4wInit : PolyFun top4wInit :=
  (psnd polyFun_fst).comp polyFun_top4aInit

theorem polyFun_top4wCombine : PolyFun top4wCombine := by
  let X := Top4wNode × ℕ × Top4State × RawCoset
  have hC : PolyFun (fun z : X => z.1.1) := pfst polyFun_fst
  have hP := psnd hC
  have hOuter := pfst hC
  have hd := pfst (pfst hOuter)
  have hw := pfst (psnd hOuter)
  have ha : PolyFun (fun z : X => z.2.2.2) := psnd (psnd polyFun_snd)
  have hi := (hd.pair (hw.pair ha)).comp polyFun_topwCosetImage
  exact (hP.pair ((pfst polyFun_snd).pair ((pfst (psnd polyFun_snd)).pair hi))).comp
    polyFun_top4aCombine

theorem quasiFun_top4wFinish {solve : RawWinSI → RawCoset} (hs : QuasiFun solve) :
    QuasiFun (top4wFinish solve) := by
  let X := Top4wNode × Top4State
  have hC : PolyFun (fun z : X => z.1.1) := pfst polyFun_fst
  have hP := psnd hC
  have hOuter := pfst hC
  have hg := pfst hOuter
  have hw := pfst (psnd hOuter)
  have hx := psnd (psnd hOuter)
  have hanswer := (hP.pair polyFun_snd).quasiFun.comp (quasiFun_top4aFinish hs)
  have hpre := (hg.quasiFun.pair (hw.quasiFun.pair hanswer)).comp polyFun_topwCosetPreimage.quasiFun
  have hchoose := (((psnd polyFun_fst).pair polyFun_id).quasiFun.comp
    (QuasiFun.optionElim hpre (polyFun_fst.comp_quasiFun hs)))
  exact (hx.quasiFun.pair hchoose).comp polyFun_top2NormC.quasiFun

def top4wCheck (a b c d e f u v : ℕ) (I : Top4wNode) : Bool :=
  decide (Enc.size I.1 ≤ topcsContextCap a b I.1.1.2.2.length) &&
    I.2.elim true (fun W => decide (Enc.size W ≤ topcsContextCap u v (Enc.size I.1)))

theorem top4wCheck_spec (a b c d e f u v : ℕ) (I : Top4wNode) :
    top4wCheck a b c d e f u v I = true ↔ Top4wWF a b c d e f u v I := by
  cases ho : I.2 <;> simp [top4wCheck, Top4wWF, ho, top4aCheck_spec]

theorem polyFun_top4wGround : PolyFun (fun I : Top4wNode => I.1.1.2.2.length) :=
  (psnd (psnd (pfst polyFun_fst))).comp polyFun_length

theorem polyFun_top4wCheck (a b c d e f u v : ℕ) : PolyFun (top4wCheck a b c d e f u v) := by
  have hC : PolyFun (fun I : Top4wNode => I.1) := polyFun_fst
  have hn := polyFun_top4wGround
  have hsize := hC.comp AggnSizeRoutine.polyFun_size
  have hcap := hsize.comp (polyFun_topcsContextCap u v)
  have htest := hsize.le (hn.comp (polyFun_topcsContextCap a b))
  have hleaf : PolyFun (fun z : RawWinSI × Top4wNode =>
      decide (Enc.size z.1 ≤ topcsContextCap u v (Enc.size z.2.1))) :=
    (polyFun_fst.comp AggnSizeRoutine.polyFun_size).le (polyFun_snd.comp hcap)
  have hopt := (polyFun_snd.pair polyFun_id).comp (PolyFun.optionElim (polyFun_const true) hleaf)
  exact pand htest hopt

end Algo
