import Workspace.Algo.SplitImprimitiveRestriction

/-! # Section 9.6: construct the selected bipartite graphs

Each second-part column lists the old blocks whose union it represents.
A restriction uses singleton lists. A contraction uses the component lists.
Both constructions therefore retain the caller's original block dictionary.
-/
namespace Algo
open Babai RAM

/-- First-part names, lists of old block names, and a zero/one adjacency matrix.
All point colors, block colors and hints are zero in Section 9.6. -/
abbrev RawImpGraph := List ℕ × List (List ℕ) × List (List ℕ)

/-- An edge to a union exists exactly when an edge to one of its blocks exists. -/
def impColumnEdge (z : ((RawConfig × ℕ) × List ℕ) × ℕ) : Bool :=
  !(z.1.2.filter (fun b => decide (binColor (z.1.1.1,(z.2,b)) = z.1.1.2))).isEmpty

theorem polyFun_impColumnEdge : PolyFun impColumnEdge := by
  have hp : PolyFun (fun z : (((RawConfig × ℕ) × List ℕ) × ℕ) × ℕ => z.1.1.1.1) :=
    ((polyFun_fst.comp polyFun_fst).comp polyFun_fst).comp polyFun_fst
  have hk : PolyFun (fun z : (((RawConfig × ℕ) × List ℕ) × ℕ) × ℕ => z.1.1.1.2) :=
    ((polyFun_fst.comp polyFun_fst).comp polyFun_fst).comp polyFun_snd
  have ht := ((hp.pair ((polyFun_fst.comp polyFun_snd).pair polyFun_snd)).comp
    polyFun_binColor).natEq hk
  exact polyFun_rawJNot (((polyFun_id.pair (polyFun_fst.comp polyFun_snd)).comp
    (PolyFun.filterParam ht)).comp polyFun_isEmpty)

theorem impColumnEdge_spec (p : RawConfig) (k x : ℕ) (g : List ℕ) :
    impColumnEdge (((p,k),g),x) = true ↔ ∃ b ∈ g, binColor (p,(x,b)) = k := by
  simp only [impColumnEdge,Bool.not_eq_true',Bool.eq_false_iff,ne_eq,List.isEmpty_iff,
    List.eq_nil_iff_forall_not_mem,not_forall,not_not,List.mem_filter,decide_eq_true_eq]

abbrev RawImpBuild := (RawUpccCase × ℕ) × List (List ℕ)

def impGraphRow (z : RawImpBuild × ℕ) : List ℕ :=
  z.1.2.map (fun g => if impColumnEdge (((z.1.1.1.1,z.1.1.2),g),z.2) then 1 else 0)

theorem polyFun_impGraphRow : PolyFun impGraphRow := by
  have hp : PolyFun (fun z : (RawImpBuild × ℕ) × List ℕ => z.1.1.1.1.1) :=
    (((polyFun_fst.comp polyFun_fst).comp polyFun_fst).comp polyFun_fst).comp polyFun_fst
  have hk : PolyFun (fun z : (RawImpBuild × ℕ) × List ℕ => z.1.1.1.2) :=
    ((polyFun_fst.comp polyFun_fst).comp polyFun_fst).comp polyFun_snd
  have ht := (((hp.pair hk).pair polyFun_snd).pair
    (polyFun_fst.comp polyFun_snd)).comp polyFun_impColumnEdge
  exact (polyFun_id.pair (polyFun_fst.comp polyFun_snd)).comp
    (PolyFun.mapParam (PolyFun.ite ht (polyFun_const 1) (polyFun_const 0)))

def impMakeGraph (z : RawImpBuild) : RawImpGraph :=
  (z.1.1.2.1,z.2,z.1.1.2.1.map (fun x => impGraphRow (z,x)))

theorem polyFun_impMakeGraph : PolyFun impMakeGraph := by
  have hl : PolyFun (fun z : RawImpBuild => z.1.1.2.1) :=
    ((polyFun_fst.comp polyFun_fst).comp polyFun_snd).comp polyFun_fst
  exact hl.pair (polyFun_snd.pair
    ((polyFun_id.pair hl).comp (PolyFun.mapParam polyFun_impGraphRow)))

def impRestrictionGraph (z : RawUpccCase × List ℕ) : RawImpGraph :=
  impMakeGraph ((z.1,impJ z.1),z.2.map (fun b => [b]))

theorem polyFun_impRestrictionGraph : PolyFun impRestrictionGraph :=
  ((polyFun_fst.pair (polyFun_fst.comp polyFun_impJ)).pair
    (polyFun_snd.comp (PolyFun.map
      ((polyFun_id.pair (polyFun_const [])).comp polyFun_cons)))).comp polyFun_impMakeGraph

def impContractionGraph (r : RawUpccCase) : RawImpGraph :=
  impMakeGraph ((r,impH r),impGroups r)

theorem polyFun_impContractionGraph : PolyFun impContractionGraph :=
  ((polyFun_id.pair polyFun_impH).pair polyFun_impGroups).comp polyFun_impMakeGraph

/-- The paper tests restrictions first. Contraction is the sole fallback. -/
def impStep2Graphs (r : RawUpccCase) : List RawImpGraph :=
  if (impGoodGroups r).isEmpty then [impContractionGraph r]
  else (impGoodGroups r).map (fun g => impRestrictionGraph (r,g))

theorem polyFun_impStep2Graphs : PolyFun impStep2Graphs :=
  PolyFun.ite (polyFun_impGoodGroups.comp polyFun_isEmpty)
    ((polyFun_impContractionGraph.pair (polyFun_const [])).comp polyFun_cons)
    ((polyFun_id.pair polyFun_impGoodGroups).comp (PolyFun.mapParam polyFun_impRestrictionGraph))

/-- The first tag returns a color partition. The second returns a graph. -/
abbrev RawImpOutcome := RawLab × Option RawImpGraph

def impCase (r : RawUpccCase) : List RawImpOutcome :=
  if impSplits r then r.2.2.map (fun b => (impSplitLab (r,b),none))
  else (impStep2Graphs r).map (fun q => ([],some q))

theorem polyFun_impCase : PolyFun impCase :=
  PolyFun.ite polyFun_impSplits
    ((polyFun_id.pair (polyFun_snd.comp polyFun_snd)).comp
      (PolyFun.mapParam (polyFun_impSplitLab.pair (polyFun_const none))))
    (polyFun_impStep2Graphs.comp (PolyFun.map ((polyFun_const []).pair polyFun_some)))

end Algo
