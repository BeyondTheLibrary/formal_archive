import Workspace.Algo.DesignReadPairs
import Workspace.Algo.NormalizeSI
import Workspace.Algo.AlignStruct

/-! # The component partition in the Design Lemma's output

When the dominant binary configuration is imprimitive, the first disconnected
constituent gives its component blocks. Other color classes keep one block
each. The raw partition retains the computed vertex colors.
-/
namespace Algo
open Babai RAM

def designReadColors (z : DIn) : RawLab :=
  (List.range z.1.2.1.length).map (fun u => restrVColorAt (z,u))

def designReadComponents (z : DIn) : RawLab :=
  componentsRaw (designDomPairs z,sbipFirstDisconnected (designDomPairs z))

def designReadIndex (z : DIn × ℕ) : ℕ := rawLetterIndex (dominantList z.1,z.2)

def designReadBlock (z : DIn × ℕ) : ℕ :=
  if decide (z.2 ∈ dominantList z.1) then
    labAt (designReadComponents z.1) (designReadIndex z) + 1 else 0

def designReadPart (z : DIn) : RawColPart :=
  (designReadColors z,(List.range z.1.2.1.length).map (fun u => designReadBlock (z,u)))

def designReadPlain (z : DIn) : RawColPart := (designReadColors z,designReadColors z)

theorem polyFun_designReadColors : PolyFun designReadColors :=
  (polyFun_id.pair (((polyFun_fst.comp polyFun_snd).comp polyFun_fst).comp polyFun_rangeLength)).comp
    (PolyFun.mapParam polyFun_restrVColorAt)

theorem polyFun_designReadComponents : PolyFun designReadComponents :=
  (polyFun_designDomPairs.pair (polyFun_designDomPairs.comp sbipPoly_firstDisconnected)).comp
    polyFun_componentsRaw

theorem polyFun_designReadIndex : PolyFun designReadIndex :=
  ((polyFun_fst.comp polyFun_dominantList).pair polyFun_snd).comp polyFun_rawLetterIndex

theorem polyFun_designReadBlock : PolyFun designReadBlock :=
  PolyFun.ite ((polyFun_snd.pair (polyFun_fst.comp polyFun_dominantList)).comp polyFun_natListMem)
    ((((polyFun_fst.comp polyFun_designReadComponents).pair polyFun_designReadIndex).comp
      polyFun_labAt).add (polyFun_const 1)) (polyFun_const 0)

theorem polyFun_designReadPart : PolyFun designReadPart :=
  polyFun_designReadColors.pair
    ((polyFun_id.pair (((polyFun_fst.comp polyFun_snd).comp polyFun_fst).comp polyFun_rangeLength)).comp
      (PolyFun.mapParam polyFun_designReadBlock))

theorem polyFun_designReadPlain : PolyFun designReadPlain :=
  polyFun_designReadColors.pair polyFun_designReadColors

theorem designReadPart_wf (z : DIn) : (designReadPart z).WF z.1.2.1.length := by
  simp [RawColPart.WF,designReadPart,designReadColors]

theorem designReadPlain_wf (z : DIn) : (designReadPlain z).WF z.1.2.1.length := by
  simp [RawColPart.WF,designReadPlain,designReadColors]

theorem designReadPart_color (z : DIn) (u : Fin z.1.2.1.length) :
    (decColPartition z.1.2.1.length (designReadPart z)).color u = restrVColorAt (z,u) := by
  simp [decColPartition,designReadPart,designReadColors,labAt,u.isLt]

theorem designReadPart_rel (z : DIn) (u v : Fin z.1.2.1.length) :
    (decColPartition z.1.2.1.length (designReadPart z)).part u v ↔
      restrVColorAt (z,u) = restrVColorAt (z,v) ∧ designReadBlock (z,u) = designReadBlock (z,v) := by
  change cellOf (designReadPart z) u = cellOf (designReadPart z) v ↔ _
  simp [cellOf,designReadPart,designReadColors,labAt,u.isLt,v.isLt]

theorem designReadBlock_off (z : DIn) {u : ℕ} (hu : u ∉ dominantList z) :
    designReadBlock (z,u) = 0 := by simp [designReadBlock,hu]

theorem designReadBlock_on (z : DIn) {u : ℕ} (hu : u ∈ dominantList z) :
    designReadBlock (z,u) = labAt (designReadComponents z) (designReadIndex (z,u)) + 1 := by
  simp [designReadBlock,hu]

theorem designReadIndex_spec (z : DIn) (hnd : (dominantList z).Nodup)
    (i : Fin (dominantList z).length) :
    designReadIndex (z,(dominantList z)[i.val]) = i.val := by
  have hh := rawLetterIndex_spec (List.getElem_mem i.isLt)
  apply (List.Nodup.getElem_inj_iff hnd).1
  exact (List.getD_eq_getElem _ _ hh.1).symm.trans hh.2

/-- Inside the dominant class, equal labels are precisely its weak components. -/
theorem designReadBlock_components (z : DIn) (hnd : (dominantList z).Nodup)
    (i j : Fin (dominantList z).length) :
    designReadBlock (z,(dominantList z)[i.val]) = designReadBlock (z,(dominantList z)[j.val]) ↔
      (decConstituent (dominantList z).length
        (designDomPairs z,sbipFirstDisconnected (designDomPairs z))).WeaklyAccessible i j := by
  rw [designReadBlock_on z (List.getElem_mem i.isLt),designReadBlock_on z (List.getElem_mem j.isLt),
    designReadIndex_spec z hnd i,designReadIndex_spec z hnd j,Nat.add_right_cancel_iff]
  exact componentsRaw_spec_of_length (by simp [designDomPairs,designPairIndexed]) i j

end Algo
