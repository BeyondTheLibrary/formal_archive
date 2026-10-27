import Workspace.Algo.TopFourTail

/-! # Executable routines for the two-phase top-action carrier -/
set_option synthInstance.maxSize 2048
namespace Algo
open RAM RAM.Targets
private theorem pfst {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {f : α → β × γ}
    (h : PolyFun f) : PolyFun (fun a => (f a).1) := h.comp polyFun_fst
private theorem psnd {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {f : α → β × γ}
    (h : PolyFun f) : PolyFun (fun a => (f a).2) := h.comp polyFun_snd

private theorem plt {α : Type*} [Enc α] {f g : α → ℕ} (hf : PolyFun f) (hg : PolyFun g) :
    PolyFun (fun a => decide (f a < g a)) :=
  ((hf.add (polyFun_const 1)).le hg).of_eq (fun _ => by simp only [Nat.add_one_le_iff])
private theorem pif {α β : Type*} [Enc α] [Enc β] {p : α → Prop}
    [∀ a, Decidable (p a)] {f g : α → β}
    (hp : PolyFun (fun a => decide (p a))) (hf : PolyFun f) (hg : PolyFun g) :
    PolyFun (fun a => if p a then f a else g a) :=
  (PolyFun.ite hp hf hg).of_eq (fun _ => by simp)
private theorem pmap {α β σ : Type*} [Enc α] [Enc β] [Enc σ] {f : α × σ → β}
    (hf : PolyFun f) : PolyFun (fun p : Option α × σ => p.1.map (fun a => f (a, p.2))) :=
  (PolyFun.optionElim (polyFun_const none) (hf.comp polyFun_some)).of_eq
    (fun p => by cases p.1 <;> rfl)

theorem polyFun_top4X : PolyFun top4X := psnd (psnd (pfst (pfst polyFun_id)))
theorem polyFun_top4Y : PolyFun top4Y := psnd (psnd polyFun_id)
theorem polyFun_top4Wins : PolyFun top4Wins := pfst (psnd polyFun_id)
theorem polyFun_top4Base : PolyFun top4Base :=
  ((psnd (pfst polyFun_id)).comp polyFun_topcsJobs).mul
    (((psnd (pfst polyFun_id)).comp polyFun_topcsWins).comp polyFun_length)
theorem polyFun_top4Width : PolyFun top4Width :=
  polyFun_top4Base.add (polyFun_top4Wins.comp polyFun_length)

theorem polyFun_top4Open : PolyFun (fun p : Top4Context × TopcsState => top4Open p.1 p.2) := by
  have hC : PolyFun (fun p : Top4Context × TopcsState => p.1) := polyFun_fst
  have hw := pfst hC
  have hout := pfst hw
  have hg := pfst hout
  have hΔ := pfst (psnd hout)
  have hx := hC.comp polyFun_top4X
  have ha := ((((psnd hw).pair polyFun_snd).comp polyFun_topcsAnswer).pair
    (polyFun_const (none : RawCoset))).comp polyFun_optionGetD
  have hpre := (hg.pair (hΔ.pair ha)).comp polyFun_topwCosetPreimage
  exact polyFun_snd.pair ((polyFun_const 0).pair ((hx.pair hpre).comp polyFun_top2NormC))

theorem polyFun_top4Closed : PolyFun top4Closed :=
  (((psnd (pfst polyFun_id)).comp polyFun_topcsJobs).pair
    ((polyFun_const 0).pair ((polyFun_const (none : RawCoset)).pair
      ((polyFun_const (none : Top1State)).pair
        ((polyFun_const (none : RawCoset)).pair (polyFun_const (none : RawCoset)))))))

theorem polyFun_top4Leaf : PolyFun (fun p : Top4Context × ℕ × (RawGens × RawPerm) => top4Leaf p.1 p.2.1 p.2.2) := by
  have hC : PolyFun (fun p : Top4Context × ℕ × (RawGens × RawPerm) => p.1) := polyFun_fst
  have hx := hC.comp polyFun_top4X
  have hw := (((hC.comp polyFun_top4Wins).pair (pfst polyFun_snd)).pair
    (polyFun_const ([] : List ℕ))).comp polyFun_getD
  have hg := (hx.pair (pfst (psnd polyFun_snd))).comp polyFun_tidyGens
  have hr := (hx.pair (psnd (psnd polyFun_snd))).comp polyFun_normPerm
  exact hw.pair (hg.pair (hr.pair (hx.pair (hC.comp polyFun_top4Y))))

theorem polyFun_top4Child (e f : ℕ) : PolyFun (top4Child e f) := by
  let Z := Top4Node × ℕ × Top4State
  have hC : PolyFun (fun z : Z => z.1.1) := pfst polyFun_fst
  have hj := pfst (polyFun_snd : PolyFun (fun z : Z => z.2))
  have hs := psnd (polyFun_snd : PolyFun (fun z : Z => z.2))
  have ht := pfst (pfst hs)
  have hi := pfst (psnd hs)
  have hwide := plt hj (hC.comp polyFun_top4Width)
  have hinner := plt ht ((psnd (pfst hC)).comp polyFun_topcsJobs)
  have hrest := plt hi ((hC.comp polyFun_top4Wins).comp polyFun_length)
  have hw := ((((pfst hC).pair (polyFun_const (none : Option RawWinSI))).pair
    (hj.pair (pfst hs))).comp (polyFun_topwpChild e f))
  have hm : PolyFun (fun p : TopwpNode × Z => (p.2.1.1, p.1.2)) :=
    (polyFun_snd.comp hC).pair (psnd polyFun_fst)
  have hl : PolyFun (fun p : (RawGens × RawPerm) × Z =>
      (p.2.1.1, some (top4Leaf p.2.1.1 p.2.2.2.2.1 p.1))) :=
    (polyFun_snd.comp hC).pair
      ((((polyFun_snd.comp hC).pair ((polyFun_snd.comp hi).pair polyFun_fst)).comp polyFun_top4Leaf).comp polyFun_some)
  have hp := pif hwide
    (pif hinner ((hw.pair polyFun_id).comp (pmap hm))
      (pif hrest (((psnd (psnd hs)).pair polyFun_id).comp (pmap hl)) (polyFun_const none)))
    (polyFun_const none)
  exact (((psnd polyFun_fst).pair polyFun_id).comp
    (PolyFun.optionElim hp (polyFun_const none))).of_eq (fun _ => rfl)

theorem polyFun_top4Init : PolyFun top4Init :=
  (polyFun_fst.pair (((pfst polyFun_fst).pair (polyFun_const (none : Option RawWinSI))).comp polyFun_topwpInit)).comp polyFun_top4Open

theorem polyFun_top4Combine : PolyFun top4Combine := by
  let Z := Top4Node × ℕ × Top4State × RawCoset
  have hC : PolyFun (fun z : Z => z.1.1) := pfst polyFun_fst
  have hj := pfst (polyFun_snd : PolyFun (fun z : Z => z.2))
  have hs := pfst (psnd (polyFun_snd : PolyFun (fun z : Z => z.2)))
  have ha := psnd (psnd (polyFun_snd : PolyFun (fun z : Z => z.2)))
  have hguard := plt (pfst (pfst hs)) ((psnd (pfst hC)).comp polyFun_topcsJobs)
  have hinner := (((pfst hC).pair (polyFun_const (none : Option RawWinSI))).pair
    (hj.pair ((pfst hs).pair ha))).comp polyFun_topwpCombine
  have hopen := (hC.pair hinner).comp polyFun_top4Open
  have hidx := (((pfst (psnd hs)).add (polyFun_const 1)).pair ((hC.comp polyFun_top4Wins).comp polyFun_length)).comp polyFun_min
  have hnorm := ((hC.comp polyFun_top4X).pair ha).comp polyFun_top2NormC
  exact (pif hguard hopen ((hC.comp polyFun_top4Closed).pair (hidx.pair hnorm))).of_eq (fun _ => rfl)

theorem quasiFun_top4Finish {solve : RawWinSI → RawCoset} (hsolve : QuasiFun solve) :
    QuasiFun (top4Finish solve) := by
  have hx : PolyFun (fun z : Top4Node × Top4State => top4X z.1.1) := (pfst polyFun_fst).comp polyFun_top4X
  have hresult := (((psnd polyFun_fst).pair polyFun_id).quasiFun.comp
    (QuasiFun.optionElim (psnd (psnd (polyFun_snd : PolyFun (fun z : Top4Node × Top4State => z.2)))).quasiFun
      (polyFun_fst.comp_quasiFun hsolve)))
  exact (hx.quasiFun.pair hresult).comp polyFun_top2NormC.quasiFun

theorem polyFun_top4LeafCap (e f : ℕ) : PolyFun (top4LeafCap e f) :=
  (polyFun_topcsContextCap e f).add ((polyFun_const 64).mul
    ((polyFun_id.add polyFun_topcsChainBound).add (polyFun_const 1)))

def top4Check (c d e f : ℕ) (I : Top4Node) : Bool :=
  decide (Enc.size I.1 ≤ topcsContextCap c d (top4X I.1).length) &&
    I.2.elim true (fun W => decide (Enc.size W ≤ top4LeafCap e f (Enc.size I.1)))

theorem top4Check_spec (c d e f : ℕ) (I : Top4Node) : top4Check c d e f I = true ↔ Top4WF c d e f I := by
  cases ho : I.2 <;> simp [top4Check, Top4WF, ho]

theorem polyFun_top4Check (c d e f : ℕ) : PolyFun (top4Check c d e f) := by
  have hsize : PolyFun (fun I : Top4Node => Enc.size I.1) := polyFun_fst.comp AggnSizeRoutine.polyFun_size
  have ht := hsize.le (((polyFun_fst.comp polyFun_top4X).comp polyFun_length).comp (polyFun_topcsContextCap c d))
  have hleaf : PolyFun (fun z : RawWinSI × Top4Node =>
      decide (Enc.size z.1 ≤ top4LeafCap e f (Enc.size z.2.1))) :=
    (polyFun_fst.comp AggnSizeRoutine.polyFun_size).le ((polyFun_snd.comp hsize).comp (polyFun_top4LeafCap e f))
  have ho := (polyFun_snd.pair polyFun_id).comp (PolyFun.optionElim (polyFun_const true) hleaf)
  exact (PolyFun.ite ht ho (polyFun_const false)).of_eq (fun I => by
    simp only [top4Check]
    cases decide (Enc.size I.1 ≤ topcsContextCap c d (top4X I.1).length) <;> rfl)

end Algo
