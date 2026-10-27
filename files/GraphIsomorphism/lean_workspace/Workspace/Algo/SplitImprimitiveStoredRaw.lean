import Workspace.Algo.SplitBipPack
import Workspace.Algo.SplitImprimitiveStoredColumns

/-! Store an ImprimitiveCase graph in the common recursive graph format.
The old compact point names are restored through singleton dictionary rows.
Each new column is the union of its old block rows. The adjacency matrix
is unchanged. Section 9.6 assigns zero to every decoration.
-/
namespace Algo
open Babai RAM

/-- Original ambient witness, current numbered dictionary, and selected graph. -/
abbrev RawImpStore := (List ℕ × List (List ℕ)) × RawImpGraph

def impStoredPack (z : RawImpStore) : RawSbipPack :=
  ((z.1.1,sbipDictPoints (z.1.2,z.2.1)),
    z.2.2.1.map (fun g => sbipDictUnion (z.1.2,g)),
    z.2.2.2,z.1.1.map (fun _ => 0),z.2.2.1.map (fun _ => 0),([],[]))

def impStoredGraph (z : RawImpStore) : RawSbipStored := sbipPack (impStoredPack z)

theorem polyFun_impStoredPack : PolyFun impStoredPack := by
  have hw : PolyFun (fun z : RawImpStore => z.1.1) := polyFun_fst.comp polyFun_fst
  have hd : PolyFun (fun z : RawImpStore => z.1.2) := polyFun_fst.comp polyFun_snd
  have hq : PolyFun (fun z : RawImpStore => z.2) := polyFun_snd
  have hc := (hq.comp polyFun_snd).comp polyFun_fst
  have hl := (hd.pair (hq.comp polyFun_fst)).comp polyFun_sbipDictPoints
  have hb := (hd.pair hc).comp (PolyFun.mapParam polyFun_sbipDictUnion)
  exact (hw.pair hl).pair (hb.pair (((hq.comp polyFun_snd).comp polyFun_snd).pair
    ((hw.comp (PolyFun.map (polyFun_const (0 : ℕ)))).pair
      ((hc.comp (PolyFun.map (polyFun_const (0 : ℕ)))).pair (polyFun_const ([],[]))))))

theorem polyFun_impStoredGraph : PolyFun impStoredGraph := polyFun_impStoredPack.comp polyFun_sbipPack

@[simp] theorem impStoredGraph_left (z : RawImpStore) :
    (impStoredGraph z).1.1.1 = sbipDictPoints (z.1.2,z.2.1) := rfl

@[simp] theorem impStoredGraph_matrix (z : RawImpStore) :
    (impStoredGraph z).1.1.2.2 = z.2.2.2 := rfl

@[simp] theorem impStoredGraph_blocks_length (z : RawImpStore) :
    (impStoredGraph z).1.1.2.1.length = z.2.2.1.length := by
  simp only [impStoredGraph,sbipPack_blocks,sbipPackBlocks_length,impStoredPack,List.length_map]

theorem impStoredGraph_dict (z : RawImpStore) (i : Fin z.2.2.1.length) :
    sbipDictGet ((impStoredGraph z).2,z.1.1.length+i) =
      sbipDictUnion (z.1.2,z.2.2.1[i.val]) := by
  change sbipDictGet ((sbipPack (impStoredPack z)).2,(impStoredPack z).1.1.length+i) = _
  rw [sbipPack_dict]
  simp [impStoredPack,sbipDictGet,i.isLt]

private theorem labAt_zero_map {α : Type} (l : List α) (i : ℕ) :
    labAt (l.map (fun _ => 0)) i = 0 := by
  by_cases hi : i < l.length
  · simp [labAt,hi]
  · simp [labAt,hi]

@[simp] theorem impStoredGraph_pointColor (z : RawImpStore) (i : ℕ) :
    labAt (impStoredGraph z).1.2.1 i = 0 := labAt_zero_map z.1.1 i

@[simp] theorem impStoredGraph_blockColor (z : RawImpStore) (i : ℕ) :
    labAt (impStoredGraph z).1.2.2.1 (z.1.1.length+i) = 0 := by
  change labAt (sbipPack (impStoredPack z)).1.2.2.1 ((impStoredPack z).1.1.length+i) = _
  rw [sbipPack_blockColor]
  exact labAt_zero_map z.2.2.1 i

theorem impStoredGraph_hint (z : RawImpStore) (hnd : (sbipPackVertices (impStoredPack z)).Nodup)
    (i j : Fin (sbipPackVertices (impStoredPack z)).length) :
    binColor ((impStoredGraph z).1.2.2.2,
      ((sbipPackVertices (impStoredPack z))[i.val],(sbipPackVertices (impStoredPack z))[j.val])) = 0 := by
  rw [impStoredGraph,sbipPack_hint _ hnd]
  rfl

end Algo
