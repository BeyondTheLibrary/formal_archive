import Workspace.Algo.SplitBipRestoreNames
import Workspace.Algo.SplitBipStep2
import Workspace.Algo.SplitBipStep5

/-! Every recursive turn retains a full decorated graph. Matrix rows and
columns use their stored list orders. Colors and hints use the persistent
point and block names. The refinement temporarily numbers the vertices,
then restores those names before the next restriction. -/
namespace Algo
open Babai RAM

/-- The adjacency matrix, full point colors, block colors, and hint table. -/
abbrev RawSbipGraph := RawUpccBip × RawSbipDecor

def sbipGraphVertices (r : RawSbipGraph) : List ℕ := r.1.1 ++ r.1.2.1

def sbipGraphEdge (z : RawSbipGraph × (ℕ × ℕ)) : ℕ :=
  if decide (z.2.1 ∈ z.1.1.1) && decide (z.2.2 ∈ z.1.1.2.1) then
    if sbipMatrixEntry (z.1.1,
      (rawLetterIndex (z.1.1.1,z.2.1),rawLetterIndex (z.1.1.2.1,z.2.2))) = 0 then 0 else 1
  else 0

def sbipGraphVertexColor (z : RawSbipGraph × ℕ) : ℕ :=
  if decide (z.2 ∈ z.1.1.1) then Nat.pair 1 (labAt z.1.2.1 z.2)
  else if decide (z.2 ∈ z.1.1.2.1) then Nat.pair 2 (labAt z.1.2.2.1 z.2) else 0

def sbipGraphPair (z : RawSbipGraph × (ℕ × ℕ)) : ℕ :=
  if decide (z.2.1 = z.2.2) then Nat.pair 0 (sbipGraphVertexColor (z.1,z.2.1))
  else Nat.pair 1 (Nat.pair
    (Nat.pair (sbipGraphEdge z) (sbipGraphEdge (z.1,(z.2.2,z.2.1))))
    (Nat.pair (binColor (z.1.2.2.2,z.2)) (binColor (z.1.2.2.2,(z.2.2,z.2.1)))))

def sbipGraphRow (z : RawSbipGraph × List ℕ) : List ℕ × ℕ :=
  (z.2,sbipGraphPair (z.1,(rawGet (z.2,0),rawGet (z.2,1))))

def sbipGraphInitial (r : RawSbipGraph) : RawConfig :=
  (sbipGraphVertices r,(tuplesOf (sbipGraphVertices r) 2).map (fun t => sbipGraphRow (r,t)))

def sbipGraphRefine (r : RawSbipGraph) : RawConfig :=
  sbipRefineNames (sbipGraphInitial r,sbipGraphVertices r)

theorem polyFun_sbipGraphVertices : PolyFun sbipGraphVertices :=
  (((polyFun_fst.comp polyFun_fst).pair
    ((polyFun_fst.comp polyFun_snd).comp polyFun_fst)).comp polyFun_append)

theorem polyFun_sbipGraphEdge : PolyFun sbipGraphEdge := by
  have hg : PolyFun (fun z : RawSbipGraph × (ℕ × ℕ) => z.1.1) :=
    polyFun_fst.comp polyFun_fst
  have hl := hg.comp polyFun_fst
  have hr := (hg.comp polyFun_snd).comp polyFun_fst
  have hu : PolyFun (fun z : RawSbipGraph × (ℕ × ℕ) => z.2.1) := polyFun_snd.comp polyFun_fst
  have hv : PolyFun (fun z : RawSbipGraph × (ℕ × ℕ) => z.2.2) := polyFun_snd.comp polyFun_snd
  have ht := polyFun_rawJAnd ((hu.pair hl).comp polyFun_natListMem)
    ((hv.pair hr).comp polyFun_natListMem)
  have he := (hg.pair (((hl.pair hu).comp polyFun_rawLetterIndex).pair
    ((hr.pair hv).comp polyFun_rawLetterIndex))).comp polyFun_sbipMatrixEntry
  exact (PolyFun.ite ht
    (PolyFun.ite (he.natEq (polyFun_const 0)) (polyFun_const 0) (polyFun_const 1))
    (polyFun_const 0)).of_eq (fun z => by simp [sbipGraphEdge])

theorem polyFun_sbipGraphVertexColor : PolyFun sbipGraphVertexColor := by
  have hg : PolyFun (fun z : RawSbipGraph × ℕ => z.1.1) := polyFun_fst.comp polyFun_fst
  have hf : PolyFun (fun z : RawSbipGraph × ℕ => z.1.2.1) :=
    (polyFun_fst.comp polyFun_snd).comp polyFun_fst
  have hb : PolyFun (fun z : RawSbipGraph × ℕ => z.1.2.2.1) :=
    ((polyFun_fst.comp polyFun_snd).comp polyFun_snd).comp polyFun_fst
  exact PolyFun.ite ((polyFun_snd.pair (hg.comp polyFun_fst)).comp polyFun_natListMem)
    (((polyFun_const 1).pair ((hf.pair polyFun_snd).comp polyFun_labAt)).comp polyFun_upccNatPair)
    (PolyFun.ite ((polyFun_snd.pair ((hg.comp polyFun_snd).comp polyFun_fst)).comp polyFun_natListMem)
      (((polyFun_const 2).pair ((hb.pair polyFun_snd).comp polyFun_labAt)).comp polyFun_upccNatPair)
      (polyFun_const 0))

theorem polyFun_sbipGraphPair : PolyFun sbipGraphPair := by
  have hu : PolyFun (fun z : RawSbipGraph × (ℕ × ℕ) => z.2.1) := polyFun_snd.comp polyFun_fst
  have hv : PolyFun (fun z : RawSbipGraph × (ℕ × ℕ) => z.2.2) := polyFun_snd.comp polyFun_snd
  have hh : PolyFun (fun z : RawSbipGraph × (ℕ × ℕ) => z.1.2.2.2) :=
    ((polyFun_fst.comp polyFun_snd).comp polyFun_snd).comp polyFun_snd
  have he := (polyFun_sbipGraphEdge.pair
    ((polyFun_fst.pair (hv.pair hu)).comp polyFun_sbipGraphEdge)).comp polyFun_upccNatPair
  have hi := (((hh.pair polyFun_snd).comp polyFun_binColor).pair
    ((hh.pair (hv.pair hu)).comp polyFun_binColor)).comp polyFun_upccNatPair
  exact PolyFun.ite (hu.natEq hv)
    (((polyFun_const 0).pair ((polyFun_fst.pair hu).comp polyFun_sbipGraphVertexColor)).comp polyFun_upccNatPair)
    (((polyFun_const 1).pair ((he.pair hi).comp polyFun_upccNatPair)).comp polyFun_upccNatPair)

theorem polyFun_sbipGraphRow : PolyFun sbipGraphRow :=
  polyFun_snd.pair ((polyFun_fst.pair
    (((polyFun_snd.pair (polyFun_const 0)).comp polyFun_rawGet).pair
      ((polyFun_snd.pair (polyFun_const 1)).comp polyFun_rawGet))).comp polyFun_sbipGraphPair)

theorem polyFun_sbipGraphInitial : PolyFun sbipGraphInitial :=
  polyFun_sbipGraphVertices.pair ((polyFun_id.pair
    (polyFun_sbipGraphVertices.comp ((polyFun_tuplesOf 2).comp polyFun_snd))).comp
      (PolyFun.mapParam polyFun_sbipGraphRow))

theorem polyFun_sbipGraphRefine : PolyFun sbipGraphRefine :=
  (polyFun_sbipGraphInitial.pair polyFun_sbipGraphVertices).comp polyFun_sbipRefineNames

theorem sbipGraphInitial_get (r : RawSbipGraph) {u v : ℕ}
    (hu : u ∈ sbipGraphVertices r) (hv : v ∈ sbipGraphVertices r) :
    binColor (sbipGraphInitial r,(u,v)) = sbipGraphPair (r,(u,v)) := by
  have ht : [u,v] ∈ tuplesOf (sbipGraphVertices r) 2 := (mem_tuplesOf _ _ _).2
    ⟨rfl,by simpa using And.intro hu hv⟩
  have hh := congrArg (fun o => o.getD 0) (sbipLookup
    (fun t => sbipGraphPair (r,(rawGet (t,0),rawGet (t,1)))) _ ht)
  simpa [sbipGraphInitial,sbipGraphRow,rawGet,binColor,tblGet] using hh

end Algo
