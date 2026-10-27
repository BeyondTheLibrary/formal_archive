import Workspace.Algo.SplitBipNodeRaw

/-! Every routine of the recursive Section 9 node has one RAM program
for all input degrees. Child calls and answer restoration use the stored
lists. No routine invokes a recursive solver. -/
namespace Algo
open RAM Babai
set_option maxHeartbeats 1000000

private theorem pfst {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {f : α → β × γ}
    (h : PolyFun f) : PolyFun (fun z => (f z).1) := h.comp polyFun_fst
private theorem psnd {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {f : α → β × γ}
    (h : PolyFun f) : PolyFun (fun z => (f z).2) := h.comp polyFun_snd

theorem polyFun_sbipNodeBlocks : PolyFun sbipNodeBlocks := by
  have hg : PolyFun (fun I : RawSbipNode => (sbipTurnGraphInput I.1).1) :=
    (polyFun_fst.comp polyFun_sbipTurnGraphInput).comp polyFun_fst
  exact (pfst (psnd (pfst hg))).comp polyFun_length

theorem polyFun_sbipNodeBit : PolyFun sbipNodeBit := by
  exact (PolyFun.ite (polyFun_snd.natEq (polyFun_const 0))
    (polyFun_const 0) (polyFun_const 1)).of_eq (fun I => by simp [sbipNodeBit])

theorem polyFun_sbipNodeMeasure : PolyFun sbipNodeMeasure :=
  ((polyFun_const 2).mul polyFun_sbipNodeBlocks).add polyFun_sbipNodeBit

theorem polyFun_sbipNodeGround : PolyFun sbipNodeGround :=
  (polyFun_fst.comp polyFun_fst).comp polyFun_length

theorem quasiFun_sbipNodeGraphs (c : ℕ) : QuasiFun (sbipNodeGraphs c) :=
  (polyFun_fst.comp_quasiFun (quasiFun_sbipTurn c)).comp_poly polyFun_sbipTurnChildren

theorem polyFun_sbipNodeMakeChild : PolyFun sbipNodeMakeChild := by
  have h := polyFun_id (α := RawSbipNode × RawSbipStored)
  have hw := pfst (pfst (pfst h))
  have ha := psnd (psnd ((pfst (pfst h)).comp polyFun_sbipTurnCase))
  have hc := (pfst (psnd (pfst (pfst (psnd h))))).comp polyFun_length
  have hp := (pfst h).comp polyFun_sbipNodeBlocks
  have ht := polyFun_rawJAnd ((hc.add (polyFun_const 1)).le hp)
    (((polyFun_const 10).mul hc).le ((polyFun_const 9).mul hp))
  have hb := PolyFun.ite ht (polyFun_const 1) (polyFun_const 0)
  exact ((hw.pair ((psnd h).pair ha)).pair hb).of_eq
    (fun z => by simp only [sbipNodeMakeChild,Bool.and_eq_true,
      decide_eq_true_eq,Nat.add_one_le_iff,id_eq])

theorem polyFun_sbipNodeAdmit : PolyFun sbipNodeAdmit := by
  have hc := polyFun_sbipNodeMakeChild.comp polyFun_sbipNodeMeasure
  have hp : PolyFun (fun z : RawSbipNode × RawSbipStored => sbipNodeMeasure z.1) :=
    polyFun_fst.comp polyFun_sbipNodeMeasure
  exact (PolyFun.ite ((hc.add (polyFun_const 1)).le hp)
    (polyFun_sbipNodeMakeChild.comp polyFun_some) (polyFun_const none)).of_eq
      (fun z => by simp only [sbipNodeAdmit,decide_eq_true_eq,Nat.add_one_le_iff])

theorem quasiFun_sbipNodeChild (c : ℕ) : QuasiFun (sbipNodeChild c) := by
  have hl : QuasiFun (fun z : RawSbipNode × ℕ => sbipNodeGraphs c z.1) :=
    polyFun_fst.comp_quasiFun (quasiFun_sbipNodeGraphs c)
  have ho : QuasiFun (fun z : RawSbipNode × ℕ => (sbipNodeGraphs c z.1)[z.2]?) :=
    (hl.pair polyFun_snd.quasiFun).comp_poly polyFun_getElem?
  have hs : PolyFun (fun z : RawSbipStored × RawSbipNode => sbipNodeAdmit (z.2,z.1)) :=
    (polyFun_snd.pair polyFun_fst).comp polyFun_sbipNodeAdmit
  exact (ho.pair polyFun_fst.quasiFun).comp_poly
    (PolyFun.optionElim (polyFun_const none) hs)

theorem quasiFun_sbipNodeInit (c : ℕ) : QuasiFun (sbipNodeInit c) :=
  (polyFun_fst.comp_quasiFun (quasiFun_sbipTurn c)).comp_poly polyFun_sbipTurnReturns

theorem polyFun_sbipNodeLift : PolyFun sbipNodeLift := by
  have hp : PolyFun (fun z : RawColPart × (List ℕ × List ℕ) =>
      some (rawExtendPartition (z.2,z.1))) :=
    ((polyFun_snd.pair polyFun_fst).comp polyFun_rawExtendPartition).comp polyFun_some
  have ho : PolyFun (fun z : (List ℕ × List ℕ) × RawAlignOutcome =>
      z.2.1.elim none (fun P => some (rawExtendPartition (z.1,P)))) :=
    (((polyFun_snd.comp polyFun_fst).pair polyFun_fst).comp
      (PolyFun.optionElim (polyFun_const none) hp))
  exact (ho.pair (polyFun_snd.comp polyFun_snd)).of_eq
    (fun z => by cases hz : z.2.1 <;> simp [sbipNodeLift,hz])

theorem quasiFun_sbipNodeCombine (c : ℕ) : QuasiFun (sbipNodeCombine c) := by
  let T := RawSbipNode × ℕ × RawSbipAnswers × RawSbipAnswers
  have h := polyFun_id (α := T)
  have hI := pfst h
  have hj := pfst (psnd h)
  have hs := pfst (psnd (psnd h))
  have ha := psnd (psnd (psnd h))
  have hparent := pfst (pfst (pfst ((pfst hI).comp polyFun_sbipTurnGraphInput)))
  have hgraphs := hI.comp_quasiFun (quasiFun_sbipNodeGraphs c)
  have hchild : QuasiFun (fun z : T => (sbipNodeGraphs c z.1).getD z.2.1 default) :=
    (((hgraphs.pair hj.quasiFun).pair (polyFun_const default).quasiFun).comp_poly polyFun_getD)
  have hleft : PolyFun (fun g : RawSbipStored => g.1.1.1) :=
    (polyFun_fst.comp polyFun_fst).comp polyFun_fst
  have hnames := hparent.quasiFun.pair (hchild.comp_poly hleft)
  have hrestored := (hnames.pair ha.quasiFun).comp_poly (PolyFun.mapParam polyFun_sbipNodeLift)
  exact (hs.quasiFun.pair hrestored).comp_poly polyFun_append

theorem quasiFun_sbipRound_step (c : ℕ) : QuasiFun (sbipRound c).stepDFS := by
  apply Round.quasiFun_stepDFS_of_routines
  · exact (polyFun_fst.pair (polyFun_snd.comp polyFun_fst)).comp_quasiFun
      (quasiFun_sbipNodeChild c)
  · exact quasiFun_sbipNodeInit c
  · exact quasiFun_sbipNodeCombine c
  · exact polyFun_snd.quasiFun

end Algo
