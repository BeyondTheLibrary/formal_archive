import Workspace.Algo.SplitBipTurnInput
import Workspace.Algo.SplitBipCaseOutcomeRaw
import Workspace.Algo.SplitImprimitiveStoredRaw
import Workspace.Algo.SplitUpccStored
import Workspace.Algo.SplitDesignStored
import Workspace.Algo.SplitDesignCase12
import Workspace.Algo.SplitDesignCase3

/-! Step 9 lists the actual local versions in the paper's order. Each
entry either returns an outcome on the parent first part or retains a
stored graph for the recursive call. No recursive solver occurs here. -/
namespace Algo
open RAM Babai
set_option maxHeartbeats 1000000

abbrev RawSbipTurnEntry := RawAlignOutcome × Option RawSbipStored

def sbipTurnReturn (o : RawAlignOutcome) : RawSbipTurnEntry := (o,none)
def sbipTurnRecur (g : RawSbipStored) : RawSbipTurnEntry := ((none,none),some g)

def sbipTurnContext (z : RawSbipTurnCase) : RawSbipCaseContext :=
  (z.1.2,(z.1.1.2,z.2.1.2.1))

def sbipTurnImpPart (z : RawSbipTurnCase × ℕ) : RawSbipTurnEntry :=
  sbipTurnReturn (sbipCaseImpExit (sbipTurnContext z.1,impSplitLab (z.1.2.1,z.2))).2

def sbipTurnImpGraph (z : RawSbipTurnCase × RawImpGraph) : RawSbipTurnEntry :=
  sbipTurnRecur (impStoredGraph (z.1.1.1,z.2))

def sbipTurnImp (z : RawSbipTurnCase) : List RawSbipTurnEntry :=
  if impSplits z.2.1 then z.2.1.2.2.map (fun b => sbipTurnImpPart (z,b))
  else (impStep2Graphs z.2.1).map (fun g => sbipTurnImpGraph (z,g))

def sbipTurnUpcc (z : RawSbipTurnCase × ℕ) : RawSbipTurnEntry :=
  if upccCaseSplits (z.1.2.1,z.2) then
    sbipTurnReturn (sbipCaseUpccExit
      (sbipTurnContext z.1,upccCaseLocalColors (z.1.2.1,z.2))).2
  else sbipTurnRecur (upccStoredGraph (z.1.1.1,(z.1.2.1,z.2)))

def sbipTurnUpccFamily (z : RawSbipTurnCase) : List RawSbipTurnEntry :=
  z.2.1.2.2.map (fun b => sbipTurnUpcc (z,b))

def sbipTurnDesignGraph (z : RawSbipTurnCase × RawDesignGraph) : RawSbipTurnEntry :=
  sbipTurnRecur (designStored (z.1.1.1,z.2))

def sbipTurnDesign12 (z : RawSbipTurnCase × RawDesignCaseOut) : RawSbipTurnEntry :=
  z.2.2.elim
    (sbipTurnReturn (sbipCaseOutcome (sbipTurnContext z.1,z.2.1.2)).2)
    (fun g => sbipTurnDesignGraph (z.1,g))

def sbipTurnDesign3 (z : RawSbipTurnCase) : List RawSbipTurnEntry :=
  (designCase3Graphs z.2.1).map (fun q => sbipTurnDesignGraph (z,q.2))

def sbipTurnDesign (z : RawSbipTurnCase) : List RawSbipTurnEntry :=
  (designCase12 z.2).elim (sbipTurnDesign3 z) (fun o => [sbipTurnDesign12 (z,o)])

def sbipTurnCases (z : RawSbipTurnCase) : List RawSbipTurnEntry :=
  if sbipStep9Case z.2.1 = 0 then sbipTurnImp z
  else if sbipStep9Case z.2.1 = 1 then sbipTurnDesign z else sbipTurnUpccFamily z

private theorem pfst {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {f : α → β × γ}
    (h : PolyFun f) : PolyFun (fun z => (f z).1) := h.comp polyFun_fst
private theorem psnd {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {f : α → β × γ}
    (h : PolyFun f) : PolyFun (fun z => (f z).2) := h.comp polyFun_snd

theorem polyFun_sbipTurnReturn : PolyFun sbipTurnReturn := polyFun_id.pair (polyFun_const none)
theorem polyFun_sbipTurnRecur : PolyFun sbipTurnRecur := (polyFun_const (none,none)).pair polyFun_some

theorem polyFun_sbipTurnContext : PolyFun sbipTurnContext :=
  (polyFun_fst.comp polyFun_snd).pair
    (((polyFun_fst.comp polyFun_fst).comp polyFun_snd).pair
      ((((polyFun_snd.comp polyFun_fst).comp polyFun_snd).comp polyFun_fst)))

theorem polyFun_sbipTurnImpPart : PolyFun sbipTurnImpPart := by
  have h := polyFun_id (α := RawSbipTurnCase × ℕ)
  have hraw := pfst (psnd (pfst h))
  exact (((pfst h |>.comp polyFun_sbipTurnContext).pair
    ((hraw.pair (psnd h)).comp polyFun_impSplitLab)).comp polyFun_sbipCaseImpExit |>.comp
      polyFun_snd).comp polyFun_sbipTurnReturn

theorem polyFun_sbipTurnImpGraph : PolyFun sbipTurnImpGraph :=
  (((((polyFun_fst.comp polyFun_fst).comp polyFun_fst)).pair polyFun_snd).comp
    polyFun_impStoredGraph).comp polyFun_sbipTurnRecur

theorem polyFun_sbipTurnImp : PolyFun sbipTurnImp := by
  have hr : PolyFun (fun z : RawSbipTurnCase => z.2.1) := polyFun_snd.comp polyFun_fst
  exact PolyFun.ite (hr.comp polyFun_impSplits)
    ((polyFun_id.pair (psnd (psnd hr))).comp (PolyFun.mapParam polyFun_sbipTurnImpPart))
    ((polyFun_id.pair (hr.comp polyFun_impStep2Graphs)).comp
      (PolyFun.mapParam polyFun_sbipTurnImpGraph))

theorem polyFun_sbipTurnUpcc : PolyFun sbipTurnUpcc := by
  have h := polyFun_id (α := RawSbipTurnCase × ℕ)
  have hr := (pfst (psnd (pfst h))).pair (psnd h)
  have hpart := ((((pfst h |>.comp polyFun_sbipTurnContext).pair
    (hr.comp upccCasePoly_localColors)).comp polyFun_sbipCaseUpccExit).comp
      polyFun_snd).comp polyFun_sbipTurnReturn
  have hgraph := (((pfst (pfst (pfst h))).pair hr).comp
    polyFun_upccStoredGraph).comp polyFun_sbipTurnRecur
  exact PolyFun.ite (hr.comp upccCasePoly_splits) hpart hgraph

theorem polyFun_sbipTurnUpccFamily : PolyFun sbipTurnUpccFamily :=
  (polyFun_id.pair (((polyFun_snd.comp polyFun_fst).comp polyFun_snd).comp polyFun_snd)).comp
    (PolyFun.mapParam polyFun_sbipTurnUpcc)

theorem polyFun_sbipTurnDesignGraph : PolyFun sbipTurnDesignGraph :=
  (((((polyFun_fst.comp polyFun_fst).comp polyFun_fst)).pair polyFun_snd).comp
    polyFun_designStored).comp polyFun_sbipTurnRecur

theorem polyFun_sbipTurnDesign12 : PolyFun sbipTurnDesign12 := by
  have h := polyFun_id (α := RawSbipTurnCase × RawDesignCaseOut)
  have hp := ((((pfst h |>.comp polyFun_sbipTurnContext).pair (psnd (pfst (psnd h)))).comp
    polyFun_sbipCaseOutcome).comp polyFun_snd).comp polyFun_sbipTurnReturn
  have hg : PolyFun (fun z : RawDesignGraph × (RawSbipTurnCase × RawDesignCaseOut) =>
      sbipTurnDesignGraph (z.2.1,z.1)) :=
    (((polyFun_snd.comp polyFun_fst).pair polyFun_fst).comp polyFun_sbipTurnDesignGraph)
  exact ((psnd (psnd h)).pair h).comp (PolyFun.optionElim hp hg)

theorem quasiFun_sbipTurnDesign3 : QuasiFun sbipTurnDesign3 := by
  have hfst : PolyFun (fun z : RawSbipTurnCase × (List ℕ × RawDesignGraph) => z.1) :=
    polyFun_fst
  have hsnd : PolyFun (fun z : RawSbipTurnCase × (List ℕ × RawDesignGraph) => z.2) :=
    polyFun_snd
  have hgraph : PolyFun (fun z : List ℕ × RawDesignGraph => z.2) := polyFun_snd
  have hm : PolyFun (fun z : RawSbipTurnCase × (List ℕ × RawDesignGraph) =>
      sbipTurnDesignGraph (z.1,z.2.2)) :=
    (hfst.pair (hsnd.comp hgraph)).comp polyFun_sbipTurnDesignGraph
  have hr : PolyFun (fun z : RawSbipTurnCase => z.2.1) := polyFun_snd.comp polyFun_fst
  have hg : QuasiFun (fun z : RawSbipTurnCase => designCase3Graphs z.2.1) :=
    hr.comp_quasiFun quasiFun_designCase3Graphs
  have hpair : QuasiFun (fun z : RawSbipTurnCase => (z,designCase3Graphs z.2.1)) :=
    polyFun_id.quasiFun.pair hg
  have hmap : PolyFun (fun z : RawSbipTurnCase × List (List ℕ × RawDesignGraph) =>
      z.2.map (fun q => sbipTurnDesignGraph (z.1,q.2))) := PolyFun.mapParam hm
  have hh := hpair.comp_poly hmap
  exact hh.of_eq (fun _ => rfl)

theorem quasiFun_sbipTurnDesign : QuasiFun sbipTurnDesign := by
  have hs : PolyFun (fun z : RawDesignCaseOut × RawSbipTurnCase =>
      [sbipTurnDesign12 (z.2,z.1)]) :=
    (((polyFun_snd.pair polyFun_fst).comp polyFun_sbipTurnDesign12).pair
      (polyFun_const [])).comp polyFun_cons
  exact (((polyFun_snd.comp polyFun_designCase12).pair polyFun_id).quasiFun.comp
    (quasiFun_sbipTurnDesign3.optionElim hs.quasiFun))

theorem quasiFun_sbipTurnCases : QuasiFun sbipTurnCases := by
  have ht : PolyFun (fun z : RawSbipTurnCase => sbipStep9Case z.2.1) :=
    (polyFun_snd.comp polyFun_fst).comp sbipPoly_step9Case
  exact (QuasiFun.ite (ht.natEq (polyFun_const 0)) polyFun_sbipTurnImp.quasiFun
    (QuasiFun.ite (ht.natEq (polyFun_const 1)) quasiFun_sbipTurnDesign
      polyFun_sbipTurnUpccFamily.quasiFun)).of_eq (fun z => by simp [sbipTurnCases])

end Algo
