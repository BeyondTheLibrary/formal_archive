import Workspace.Algo.SplitBipPack
import Workspace.Algo.SplitBipVertexDictionary
import Workspace.Algo.SplitBipPackNames

/-! Step-9 graph outputs use positions in the numbered input table.
This adapter restores their point names and block rows, reads all ambient
point colors through singleton rows, and packs the graph for the next turn.
The padding color is retained explicitly because Section 9.8 uses it. -/
namespace Algo
open Babai RAM

abbrev RawSbipFromCase := (List ℕ × List (List ℕ)) × (RawSbipGraph × ℕ)

def sbipFromCaseColumns (z : List (List ℕ) × List ℕ) : List (List ℕ) :=
  z.2.map (fun a => sbipDictGet (z.1,a))

def sbipFromCaseBlockColors (z : RawLab × List ℕ) : RawLab :=
  z.2.map (fun a => labAt z.1 a)

def sbipFromCasePack (z : RawSbipFromCase) : RawSbipPack :=
  ((z.1.1,sbipDictPoints (z.1.2,z.2.1.1.1)),
    (sbipFromCaseColumns (z.1.2,z.2.1.1.2.1),
      (z.2.1.1.2.2,
        (sbipPointColors (z.1.1,((z.1.2,z.2.1.2.1),z.2.2)),
          sbipFromCaseBlockColors (z.2.1.2.2.1,z.2.1.1.2.1),
          sbipIndexed (z.2.1.2.2.2,sbipGraphVertices z.2.1)))))

def sbipFromCase (z : RawSbipFromCase) : RawSbipStored := sbipPack (sbipFromCasePack z)

theorem polyFun_sbipFromCaseColumns : PolyFun sbipFromCaseColumns :=
  PolyFun.mapParam polyFun_sbipDictGet

theorem polyFun_sbipFromCaseBlockColors : PolyFun sbipFromCaseBlockColors :=
  PolyFun.mapParam polyFun_labAt

theorem polyFun_sbipFromCasePack : PolyFun sbipFromCasePack := by
  have hw : PolyFun (fun z : RawSbipFromCase => z.1.1) := polyFun_fst.comp polyFun_fst
  have hd : PolyFun (fun z : RawSbipFromCase => z.1.2) := polyFun_fst.comp polyFun_snd
  have hg : PolyFun (fun z : RawSbipFromCase => z.2.1) := polyFun_snd.comp polyFun_fst
  have hb := hg.comp polyFun_fst
  have hl := hb.comp polyFun_fst
  have hr := (hb.comp polyFun_snd).comp polyFun_fst
  have hc := hg.comp polyFun_snd
  exact (hw.pair ((hd.pair hl).comp polyFun_sbipDictPoints)).pair
    (((hd.pair hr).comp polyFun_sbipFromCaseColumns).pair
      (((hb.comp polyFun_snd).comp polyFun_snd).pair
        (((hw.pair ((hd.pair (hc.comp polyFun_fst)).pair
          (polyFun_snd.comp polyFun_snd))).comp polyFun_sbipPointColors).pair
          (((((hc.comp polyFun_snd).comp polyFun_fst).pair hr).comp
            polyFun_sbipFromCaseBlockColors).pair
              (((((hc.comp polyFun_snd).comp polyFun_snd).pair
                (hg.comp polyFun_sbipGraphVertices))).comp sbipPoly_indexed)))))

theorem polyFun_sbipFromCase : PolyFun sbipFromCase :=
  polyFun_sbipFromCasePack.comp polyFun_sbipPack

@[simp] theorem sbipFromCaseColumns_length (z : List (List ℕ) × List ℕ) :
    (sbipFromCaseColumns z).length = z.2.length := List.length_map _

theorem sbipFromCaseColumns_get (z : List (List ℕ) × List ℕ) (i : Fin z.2.length) :
    sbipDictGet (sbipFromCaseColumns z,i) = sbipDictGet (z.1,z.2[i.val]) := by
  simp [sbipFromCaseColumns,sbipDictGet,i.isLt]

@[simp] theorem sbipFromCase_left (z : RawSbipFromCase) :
    (sbipFromCase z).1.1.1 = sbipDictPoints (z.1.2,z.2.1.1.1) := rfl

@[simp] theorem sbipFromCase_matrix (z : RawSbipFromCase) :
    (sbipFromCase z).1.1.2.2 = z.2.1.1.2.2 := rfl

theorem sbipFromCase_column (z : RawSbipFromCase) (i : Fin z.2.1.1.2.1.length) :
    sbipDictGet ((sbipFromCase z).2,z.1.1.length+i) =
      sbipDictGet (z.1.2,z.2.1.1.2.1[i.val]) := by
  exact (sbipPack_dict (sbipFromCasePack z) i).trans
    (sbipFromCaseColumns_get (z.1.2,z.2.1.1.2.1) i)

theorem sbipFromCase_blockColor (z : RawSbipFromCase) (i : Fin z.2.1.1.2.1.length) :
    labAt (sbipFromCase z).1.2.2.1 (z.1.1.length+i) =
      labAt z.2.1.2.2.1 z.2.1.1.2.1[i.val] := by
  refine (sbipPack_blockColor (sbipFromCasePack z) i).trans ?_
  simp [sbipFromCasePack,sbipFromCaseBlockColors,labAt,i.isLt]

theorem sbipFromCase_pointColor (z : RawSbipFromCase) (u : ℕ) (hu : u < z.1.1.length) :
    labAt (sbipFromCase z).1.2.1 u =
      sbipSingletonColor (((z.1.2,z.2.1.2.1),z.2.2),u) := sbipPointColors_get _ u hu

@[simp] theorem sbipFromCase_vertices_length (z : RawSbipFromCase) :
    (sbipPackVertices (sbipFromCasePack z)).length = (sbipGraphVertices z.2.1).length := by
  simp [sbipPackVertices,sbipFromCasePack,sbipDictPoints,sbipGraphVertices]

theorem sbipFromCase_hint (z : RawSbipFromCase)
    (hnd : (sbipPackVertices (sbipFromCasePack z)).Nodup)
    (i j : Fin (sbipGraphVertices z.2.1).length) :
    binColor ((sbipFromCase z).1.2.2.2,
      ((sbipPackVertices (sbipFromCasePack z))[i.val]'(by simpa using i.isLt),
       (sbipPackVertices (sbipFromCasePack z))[j.val]'(by simpa using j.isLt))) =
      binColor (z.2.1.2.2.2,((sbipGraphVertices z.2.1)[i.val],
        (sbipGraphVertices z.2.1)[j.val])) := by
  exact (sbipPack_hint (sbipFromCasePack z) hnd
    ⟨i.val,by simpa using i.isLt⟩ ⟨j.val,by simpa using j.isLt⟩).trans
      (sbipIndexed_get _ _ i j)

theorem sbipFromCase_hint_zero (z : RawSbipFromCase)
    (hz : ∀ t, tblGet (z.2.1.2.2.2.2,t) = 0) (a b : ℕ) :
    binColor ((sbipFromCase z).1.2.2.2,(a,b)) = 0 := by
  apply sbipRestore_zero
  intro u v
  change (((tuplesOf (List.range (sbipGraphVertices z.2.1).length) 2).map
    (fun t => sbipIndexRow ((z.2.1.2.2.2,sbipGraphVertices z.2.1),t))).lookup [u,v]).getD 0 = 0
  simp only [sbipIndexRow,hz]
  rw [lookup_map_const]
  split_ifs <;> rfl

end Algo
