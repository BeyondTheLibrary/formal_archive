import Workspace.Algo.SplitBipGraphNumbered
import Workspace.Machine.ListOps3

/-! A recursive graph stores the points of each block. When step 9 moves
to compact vertex positions, its dictionary follows the same list order.
Contraction then takes unions of these rows. Point names stay in the
original ambient domain. -/
namespace Algo
open Babai RAM

abbrev RawSbipStored := RawSbipGraph × List (List ℕ)

def sbipDictGet (z : List (List ℕ) × ℕ) : List ℕ := z.1.getD z.2 []

def sbipDictPoint (z : List (List ℕ) × ℕ) : ℕ := rawGet (sbipDictGet z,0)

def sbipDictPoints (z : List (List ℕ) × List ℕ) : List ℕ :=
  z.2.map (fun a => sbipDictPoint (z.1,a))

def sbipDictUnion (z : List (List ℕ) × List ℕ) : List ℕ :=
  dedupG ([],z.2.flatMap (fun a => sbipDictGet (z.1,a)))

def sbipVertexMembers (z : RawSbipStored × ℕ) : List ℕ :=
  if decide (z.2 ∈ z.1.1.1.1) then [z.2] else sbipDictGet (z.1.2,z.2)

def sbipNumberedDictionary (z : RawSbipStored) : List (List ℕ) :=
  (sbipGraphCaseVertices z.1).map (fun a => sbipVertexMembers (z,a))

theorem polyFun_sbipDictGet : PolyFun sbipDictGet :=
  (polyFun_id.pair (polyFun_const ([] : List ℕ))).comp polyFun_getD

theorem polyFun_sbipDictPoint : PolyFun sbipDictPoint :=
  (polyFun_sbipDictGet.pair (polyFun_const 0)).comp polyFun_rawGet

theorem polyFun_sbipDictPoints : PolyFun sbipDictPoints := PolyFun.mapParam polyFun_sbipDictPoint

theorem polyFun_sbipDictUnion : PolyFun sbipDictUnion :=
  ((polyFun_const ([] : List ℕ)).pair (PolyFun.flatMapParam polyFun_sbipDictGet)).comp
    (polyFun_dedupG polyFun_natEq)

theorem polyFun_sbipVertexMembers : PolyFun sbipVertexMembers :=
  PolyFun.ite ((polyFun_snd.pair
    (((polyFun_fst.comp polyFun_fst).comp polyFun_fst).comp polyFun_fst)).comp polyFun_natListMem)
    (polyFun_snd.comp polyFun_singleton)
    (((polyFun_fst.comp polyFun_snd).pair polyFun_snd).comp polyFun_sbipDictGet)

theorem polyFun_sbipNumberedDictionary : PolyFun sbipNumberedDictionary :=
  (polyFun_id.pair (polyFun_fst.comp polyFun_sbipGraphCaseVertices)).comp
    (PolyFun.mapParam polyFun_sbipVertexMembers)

theorem sbipDictGet_get (d : List (List ℕ)) (i : Fin d.length) :
    sbipDictGet (d,i) = d[i.val] := List.getD_eq_getElem _ _ _

theorem sbipDictPoint_singleton {d : List (List ℕ)} {a u : ℕ}
    (h : sbipDictGet (d,a) = [u]) : sbipDictPoint (d,a) = u := by
  simp only [sbipDictPoint,h,rawGet,List.getD_cons_zero]

theorem sbipDictUnion_mem (d : List (List ℕ)) (l : List ℕ) (u : ℕ) :
    u ∈ sbipDictUnion (d,l) ↔ ∃ a ∈ l, u ∈ sbipDictGet (d,a) := by
  simp only [sbipDictUnion,mem_dedupG_nil,List.mem_flatMap]

theorem sbipDictUnion_nodup (z : List (List ℕ) × List ℕ) : (sbipDictUnion z).Nodup :=
  nodup_dedupG _

@[simp] theorem sbipNumberedDictionary_length (z : RawSbipStored) :
    (sbipNumberedDictionary z).length = (sbipGraphCaseVertices z.1).length := List.length_map _

theorem sbipNumberedDictionary_get (z : RawSbipStored)
    (i : Fin (sbipGraphCaseVertices z.1).length) :
    sbipDictGet (sbipNumberedDictionary z,i) =
      sbipVertexMembers (z,(sbipGraphCaseVertices z.1)[i.val]) := by
  simp [sbipDictGet,sbipNumberedDictionary,i.isLt]

theorem sbipVertexMembers_point (z : RawSbipStored) {a : ℕ} (ha : a ∈ z.1.1.1) :
    sbipVertexMembers (z,a) = [a] := by simp [sbipVertexMembers,ha]

theorem sbipVertexMembers_block (z : RawSbipStored) {a : ℕ} (ha : a ∉ z.1.1.1) :
    sbipVertexMembers (z,a) = sbipDictGet (z.2,a) := by simp [sbipVertexMembers,ha]

end Algo
