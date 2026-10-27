import Workspace.Algo.SplitBipInputRun
import Workspace.Algo.SplitFullLift
import Workspace.Algo.AggNodeCheckedTraverse

/-! Theorem 9.2.1 follows the paper's three steps: individualize each
vertex, solve the returned bipartite input, and extend each answer back to
the whole domain. All choices are retained in the computed family. -/
namespace Algo
open Babai RAM

abbrev RawUpccSplitBranch := RawUpcc × RawUpccOutcome

def upccSplitBipInput (z : ((ℕ × ℕ) × RawUpccBip) × RawUpccSplitBranch) : RawBipInput :=
  ((z.2.1.1.1,(z.2.2.1.1,z.1.2)),z.1.1)

def upccSplitBipAnswers (c t d : ℕ)
    (z : ((ℕ × ℕ) × RawUpccBip) × RawUpccSplitBranch) : List RawAlignOutcome :=
  ((bipInputRun c t d (upccSplitBipInput z)).getD []).map
    (fun o => splitFullLift ((z.2.1.1.1,z.1.2.1),o))

def upccSplitBranch (c t d : ℕ) (z : RawUpccSplitBranch) : List RawAlignOutcome :=
  z.2.2.elim [rawAlignPartition z.2.1] (fun g => upccSplitBipAnswers c t d (g,z))

def upccSplitVersion (c t d : ℕ) (z : RawUpcc × ℕ) : List RawAlignOutcome :=
  upccSplitBranch c t d (z.1,Upcc.versionF z)

def upccSplitFamily (c t d : ℕ) (r : RawUpcc) : List RawAlignOutcome :=
  (List.range r.1.1.length).flatMap (fun x => upccSplitVersion c t d (r,x))

theorem polyFun_upccSplitBipInput : PolyFun upccSplitBipInput := by
  have hw : PolyFun (fun z : ((ℕ × ℕ) × RawUpccBip) × RawUpccSplitBranch => z.2.1.1.1) :=
    ((polyFun_snd.comp polyFun_fst).comp polyFun_fst).comp polyFun_fst
  have hl : PolyFun (fun z : ((ℕ × ℕ) × RawUpccBip) × RawUpccSplitBranch => z.2.2.1.1) :=
    ((polyFun_snd.comp polyFun_snd).comp polyFun_fst).comp polyFun_fst
  exact (hw.pair (hl.pair (polyFun_fst.comp polyFun_snd))).pair
    (polyFun_fst.comp polyFun_fst)

theorem quasiFun_upccSplitBipAnswers (c t d : ℕ) : QuasiFun (upccSplitBipAnswers c t d) := by
  have ha := ((polyFun_upccSplitBipInput.comp_quasiFun (quasiFun_bipInputRun c t d)).pair
    (polyFun_const []).quasiFun).comp_poly polyFun_optionGetD
  have hn : PolyFun (fun z : ((ℕ × ℕ) × RawUpccBip) × RawUpccSplitBranch =>
      (z.2.1.1.1,z.1.2.1)) :=
    ((((polyFun_snd.comp polyFun_fst).comp polyFun_fst).comp polyFun_fst).pair
      ((polyFun_fst.comp polyFun_snd).comp polyFun_fst))
  exact (hn.quasiFun.pair ha).comp_poly (PolyFun.mapParam polyFun_splitFullLift)

theorem quasiFun_upccSplitBranch (c t d : ℕ) : QuasiFun (upccSplitBranch c t d) :=
  (((polyFun_snd.comp polyFun_snd).pair polyFun_id).comp_quasiFun
    (QuasiFun.optionElim
      (((polyFun_snd.comp polyFun_fst).comp polyFun_rawAlignPartition).comp
        polyFun_singleton).quasiFun (quasiFun_upccSplitBipAnswers c t d)))

theorem quasiFun_upccSplitVersion (c t d : ℕ) : QuasiFun (upccSplitVersion c t d) :=
  (polyFun_fst.pair Upcc.polyFun_versionF).comp_quasiFun (quasiFun_upccSplitBranch c t d)

theorem quasiFun_upccSplitFamily (c t d : ℕ) : QuasiFun (upccSplitFamily c t d) :=
  (((polyFun_id.pair ((polyFun_fst.comp polyFun_fst).comp polyFun_rangeLength)).comp_quasiFun
    (aggnQuasiFun_mapParam (quasiFun_upccSplitVersion c t d))).comp_poly
      polyFun_flatten).of_eq (fun _ => rfl)

end Algo
