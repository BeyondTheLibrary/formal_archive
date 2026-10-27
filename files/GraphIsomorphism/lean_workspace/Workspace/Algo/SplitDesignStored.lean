import Workspace.Algo.SplitBipFromCase
import Workspace.Algo.SplitDesignGraphRead

/-! Design-case graphs retain their selected link edges and their new hint.
Their point colors come from diagonal table entries, including singleton
block vertices outside the first part. The stored dictionary restores these
colors to the whole ambient domain before the next turn. -/
namespace Algo
open Babai RAM

def sbipDiagAt (z : RawConfig × ℕ) : ℕ := binColor (z.1,(z.2,z.2))

def sbipDiagColors (p : RawConfig) : RawLab :=
  (List.range p.1.length).map (fun u => sbipDiagAt (p,u))

def designStoredRow (z : RawDesignGraph × ℕ) : List ℕ :=
  z.1.1.2.map (fun v => designGraphEdge (z.1,(z.2,v)))

def designStoredMatrix (z : RawDesignGraph) : List (List ℕ) :=
  z.1.1.2.1.map (fun u => designStoredRow (z,u))

def designStoredRaw (z : RawDesignGraph) : RawSbipGraph :=
  ((z.1.1.2.1,z.1.2,designStoredMatrix z),
    (sbipDiagColors z.1.1.1,sbipDiagColors z.1.1.1,z.2))

def designStored (z : (List ℕ × List (List ℕ)) × RawDesignGraph) : RawSbipStored :=
  sbipFromCase (z.1,(designStoredRaw z.2,0))

theorem polyFun_sbipDiagAt : PolyFun sbipDiagAt :=
  (polyFun_fst.pair (polyFun_snd.pair polyFun_snd)).comp polyFun_binColor

theorem polyFun_sbipDiagColors : PolyFun sbipDiagColors :=
  (polyFun_id.pair (polyFun_fst.comp polyFun_rangeLength)).comp
    (PolyFun.mapParam polyFun_sbipDiagAt)

theorem polyFun_designStoredRow : PolyFun designStoredRow :=
  (polyFun_id.pair (((polyFun_fst.comp polyFun_fst).comp polyFun_snd))).comp
    (PolyFun.mapParam ((polyFun_fst.comp polyFun_fst).pair
      ((polyFun_fst.comp polyFun_snd).pair polyFun_snd) |>.comp polyFun_designGraphEdge))

theorem polyFun_designStoredMatrix : PolyFun designStoredMatrix :=
  (polyFun_id.pair (((polyFun_fst.comp polyFun_fst).comp polyFun_snd).comp polyFun_fst)).comp
    (PolyFun.mapParam polyFun_designStoredRow)

theorem polyFun_designStoredRaw : PolyFun designStoredRaw := by
  have hc : PolyFun (fun z : RawDesignGraph => sbipDiagColors z.1.1.1) :=
    (((polyFun_fst.comp polyFun_fst).comp polyFun_fst).comp polyFun_sbipDiagColors)
  exact (((((polyFun_fst.comp polyFun_fst).comp polyFun_snd).comp polyFun_fst).pair
    ((polyFun_fst.comp polyFun_snd).pair polyFun_designStoredMatrix)).pair
      (hc.pair (hc.pair polyFun_snd)))

theorem polyFun_designStored : PolyFun designStored :=
  (polyFun_fst.pair ((polyFun_snd.comp polyFun_designStoredRaw).pair (polyFun_const 0))).comp
    polyFun_sbipFromCase

@[simp] theorem sbipDiagColors_length (p : RawConfig) :
    (sbipDiagColors p).length = p.1.length := by simp [sbipDiagColors]

theorem sbipDiagColors_get (p : RawConfig) (i : ℕ) (hi : i < p.1.length) :
    labAt (sbipDiagColors p) i = binColor (p,(i,i)) := by
  simp [sbipDiagColors,sbipDiagAt,labAt,hi]

theorem designStoredMatrix_get (z : RawDesignGraph) (i : Fin z.1.1.2.1.length)
    (j : Fin z.1.2.length) :
    ((designStoredMatrix z).getD i []).getD j 0 =
      designGraphEdge (z,(z.1.1.2.1[i.val],z.1.2[j.val])) := by
  simp [designStoredMatrix,designStoredRow,i.isLt,j.isLt]

section
variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {s : Set Ω}
    (X : BlkDesignObj s) (point : ↥s → ℕ) (d : List (List ℕ))
    (e : ↥X.vtxSet ≃ Fin d.length)
    (hd : SbipVertexDictionary X.vtxSet point d e) (hp : Function.Injective point)
    {r : RawUpccCase} (hn : r.1.1.length = d.length)
    (hc : ∀ A, binColor (r.1,(e A,e A)) = X.c A.val A.val)
include hd hp hn hc

theorem designStored_pointColor (w : List ℕ) (cols : List ℕ) (hint : RawConfig)
    (x : ↥s) (hx : point x < w.length) :
    labAt (designStored ((w,d),((r,cols),hint))).1.2.1 (point x) = X.c {x} {x} := by
  classical
  rw [designStored,sbipFromCase_pointColor _ _ hx]
  change sbipSingletonColor (((d,sbipDiagColors r.1),0),point x) = _
  rw [sbipVertexDictionary_color hd hp]
  split_ifs with hv
  · rw [sbipDiagColors_get _ _ (by rw [hn]; exact (e _).isLt),hc]
  · exact (X.c_off _ _ (fun hh => hv hh.1)).symm

end
end Algo
