import Workspace.Algo.TopMasterDescentRound

/-! # Complete local RAM bounds for action-kernel descent -/
namespace Algo
open RAM RAM.Targets

private theorem pfst {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {f : α → β × γ}
    (h : PolyFun f) : PolyFun (fun a => (f a).1) := h.comp polyFun_fst
private theorem psnd {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {f : α → β × γ}
    (h : PolyFun f) : PolyFun (fun a => (f a).2) := h.comp polyFun_snd

theorem polyFun_masterDescX : PolyFun masterDescX :=
  pfst (psnd (psnd (psnd polyFun_fst)))

theorem polyFun_masterDescJobBound : PolyFun masterDescJobBound := by
  have hs := polyFun_top4aStrBound
  have hg : PolyFun gensBound := (polyFun_const 1).add ((polyFun_id.mul polyFun_id).mul
    (((polyFun_const 2).mul hs).add (polyFun_const 1)))
  exact (polyFun_const 16).mul (((polyFun_id.add hg).add hs).add (polyFun_const 4))

theorem polyFun_masterDescChild : PolyFun masterDescChild := by
  let X := MasterDescNode × ℕ × RawCoset
  have hI : PolyFun (fun p : X => p.1.1) := pfst polyFun_fst
  have hj : PolyFun (fun p : X => p.2.1) := pfst polyFun_snd
  have ht := (hI.comp polyFun_masterDescWidth).le hj
  have hs := (hI.pair ((hI.pair hj).comp polyFun_masterDescJob |>.comp polyFun_some)).comp polyFun_some
  have hb := PolyFun.ite ht (polyFun_const none) hs
  have hh := (((psnd polyFun_fst).pair polyFun_id).comp
    (PolyFun.optionElim hb (polyFun_const none)))
  exact hh.of_eq (fun p => by
    unfold masterDescChild
    cases p.1.2 <;> simp only [Option.elim_none, Option.elim_some]
    by_cases h : p.2.1 < masterDescWidth p.1.1 <;> simp [h, Nat.not_le, Nat.not_lt] at *)

theorem polyFun_masterDescCombine : PolyFun masterDescCombine :=
  ((pfst polyFun_fst).comp polyFun_masterDescX |>.pair (psnd polyFun_snd)).comp polyFun_masterDescJoin

theorem quasiFun_masterDescFinish {solve : RawWinSI → RawCoset} (hs : QuasiFun solve) :
    QuasiFun (masterDescFinish solve) := by
  have hx : QuasiFun (fun p : MasterDescNode × RawCoset => masterDescX p.1.1) :=
    ((pfst polyFun_fst).comp polyFun_masterDescX).quasiFun
  have hh : QuasiFun (fun p : MasterDescNode × RawCoset => p.1.2.elim p.2 solve) :=
    (((psnd polyFun_fst).pair polyFun_snd).quasiFun.comp
    (QuasiFun.optionElim polyFun_id.quasiFun (polyFun_fst.comp_quasiFun hs)))
  exact (hx.pair hh).comp polyFun_top2NormC.quasiFun

def masterDescCheck (a b c d : ℕ) (I : MasterDescNode) : Bool :=
  decide (Enc.size I.1 ≤ topcsContextCap a b (masterDescX I.1).length) &&
    decide (masterDescWidth I.1 ≤ topcsContextCap c d (masterDescX I.1).length) &&
    I.2.elim true (fun W => decide (Enc.size W ≤ masterDescJobBound (Enc.size I.1)) &&
      decide (W.2.2.2.1.length = (masterDescX I.1).length))

theorem polyFun_masterDescCheck (a b c d : ℕ) : PolyFun (masterDescCheck a b c d) := by
  have hn : PolyFun (fun I : MasterDescNode => (masterDescX I.1).length) :=
    (polyFun_fst.comp polyFun_masterDescX).comp polyFun_length
  have hz : PolyFun (fun I : MasterDescNode => Enc.size I.1) := polyFun_fst.comp AggnSizeRoutine.polyFun_size
  have h1 := hz.le (hn.comp (polyFun_topcsContextCap a b))
  have h2 := (polyFun_fst.comp polyFun_masterDescWidth).le (hn.comp (polyFun_topcsContextCap c d))
  have hbody : PolyFun (fun p : RawWinSI × MasterDescInput =>
      decide (Enc.size p.1 ≤ masterDescJobBound (Enc.size p.2)) &&
        decide (p.1.2.2.2.1.length = (masterDescX p.2).length)) :=
    wftPolyFun_and ((polyFun_fst.comp AggnSizeRoutine.polyFun_size).le
      ((polyFun_snd.comp AggnSizeRoutine.polyFun_size).comp polyFun_masterDescJobBound))
      ((((pfst (psnd (psnd (psnd polyFun_fst)))).comp polyFun_length).natEq
        ((polyFun_snd.comp polyFun_masterDescX).comp polyFun_length)))
  exact wftPolyFun_and (wftPolyFun_and h1 h2)
    ((polyFun_snd.pair polyFun_fst).comp (PolyFun.optionElim (polyFun_const true) hbody))

theorem masterDescCheck_spec (a b c d : ℕ) (I : MasterDescNode) :
    masterDescCheck a b c d I = true ↔ MasterDescWF a b c d I := by
  cases ho : I.2 <;> simp [masterDescCheck, MasterDescWF, ho, and_assoc]

def masterDescBound (a b n : ℕ) : ℕ :=
  16 * (topcsContextCap a b n + masterDescJobBound (topcsContextCap a b n) + chainBound n + 4)

theorem polyBound_masterDescBound (a b : ℕ) : PolyBound (masterDescBound a b) :=
  (polyBound_const 16).mul ((((polyBound_topcsContextCap a b).add
    (polyBound_masterDescJobBound.comp (polyBound_topcsContextCap a b))).add polyBound_chainBound).add
      (polyBound_const 4))

theorem mono_masterDescBound (a b : ℕ) : Monotone (masterDescBound a b) := by
  intro n m h
  have h1 := mono_topcsContextCap a b h
  have h2 := mono_masterDescJobBound h1
  have h3 := mono_chainBound h
  unfold masterDescBound
  omega

theorem masterDescNode_size {a b c d : ℕ} {I : MasterDescNode} (hI : MasterDescWF a b c d I) :
    Enc.size I ≤ masterDescBound a b (masterDescX I.1).length := by
  have hs := size_pair_le' I
  have hc := hI.1
  cases ho : I.2 with
  | none =>
    have he : Enc.size I.2 = 2 := by rw [ho, size_none]
    unfold masterDescBound
    omega
  | some W =>
    have hW := (hI.2.2 W ho).1
    have hm := mono_masterDescJobBound hc
    have he : Enc.size I.2 = Enc.size W + 2 := by rw [ho, size_some_eq]
    unfold masterDescBound
    omega

def masterDescRunCostQ (a b c d : ℕ) (solve : RawWinSI → RawCoset) (hs : QuasiFun solve) :
    Round.RunCostQ (masterDescRound a b c d solve) where
  bound := masterDescBound a b
  polyBound_bound := polyBound_masterDescBound a b
  mono_bound := mono_masterDescBound a b
  stateBound := chainBound
  quasiPolyBound_stateBound := polyBound_chainBound.quasiPoly
  mono_stateBound := mono_chainBound
  widthBound := topcsContextCap c d
  quasiPolyBound_widthBound := (polyBound_topcsContextCap c d).quasiPoly
  quasiFun_child := polyFun_masterDescChild.quasiFun
  quasiFun_init := (polyFun_const none).quasiFun
  quasiFun_combine := polyFun_masterDescCombine.quasiFun
  quasiFun_finish := quasiFun_masterDescFinish hs
  ground_le := fun I => (length_le_size _).trans ((size_fst_le' I.1.1.2.2.2).trans
    ((size_snd_le' I.1.1.2.2).trans ((size_snd_le' I.1.1.2).trans
      ((size_snd_le' I.1.1).trans ((size_fst_le' I.1).trans (size_fst_le' I))))))
  size_le := fun _ hI => masterDescNode_size hI
  init_le := by
    intro I hI
    change Enc.size (none : RawCoset) ≤ chainBound _
    rw [size_none]
    unfold chainBound
    omega
  combine_le := by
    intro I j s z hI _ _
    exact size_top2NormC_le rfl le_rfl _
  finish_le := by
    intro I s _ _
    have h := size_top2NormC_le (n := (masterDescX I.1).length) rfl le_rfl (I.2.elim s solve)
    change Enc.size (top2NormC (masterDescX I.1) (I.2.elim s solve)) ≤
      masterDescBound a b (masterDescX I.1).length
    unfold masterDescBound
    omega
  bot_le := by
    intro n
    change Enc.size (none : RawCoset) ≤ masterDescBound a b n
    rw [size_none]
    unfold masterDescBound
    omega
  width_le := by
    intro I hI
    change I.2.elim _ (fun _ => 0) ≤ _
    cases I.2 with
    | none => exact hI.2.1
    | some _ => exact Nat.zero_le _
  polyFun_ground := (polyFun_fst.comp polyFun_masterDescX).comp polyFun_length
  wfCheck := masterDescCheck a b c d
  polyFun_wfCheck := polyFun_masterDescCheck a b c d
  wfCheck_eq_true := masterDescCheck_spec a b c d
  measureBound := fun _ => 1
  polyBound_measureBound := polyBound_const 1
  mono_measureBound := fun _ _ _ => le_rfl
  measure_le := by
    intro I _
    change I.2.elim 1 (fun _ => 0) ≤ 1
    cases I.2 <;> simp
end Algo
