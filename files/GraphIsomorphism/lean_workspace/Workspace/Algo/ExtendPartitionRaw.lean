import Workspace.Algo.AlignOutcomeRaw
import Workspace.Algo.SplitBipRestoreNames
import Workspace.Algo.SplitPartitionTransport
import Workspace.Master.ExtendOutcome

/-! Extend a local partition by one block on the complement. Both local
labels are shifted by one. This reserves zero for the complement and
implements the extension used in Section 9 and before Procedure Align. -/
namespace Algo
open Babai RAM

/-- Parent names, local names, and labels indexed by the local list. -/
abbrev RawExtendPartition := (List ℕ × List ℕ) × RawColPart

def rawExtendLabel (z : (List ℕ × RawLab) × ℕ) : ℕ :=
  if decide (z.2 ∈ z.1.1) then labAt z.1.2 (rawLetterIndex (z.1.1,z.2)) + 1 else 0

def rawExtendLabels (z : (List ℕ × List ℕ) × RawLab) : RawLab :=
  z.1.1.map (fun a => rawExtendLabel ((z.1.2,z.2),a))

def rawExtendPartition (z : RawExtendPartition) : RawColPart :=
  (rawExtendLabels (z.1,z.2.1),rawExtendLabels (z.1,z.2.2))

theorem polyFun_rawExtendLabel : PolyFun rawExtendLabel := by
  have hl : PolyFun (fun z : (List ℕ × RawLab) × ℕ => z.1.1) := polyFun_fst.comp polyFun_fst
  have hc := ((polyFun_fst.comp polyFun_snd).pair
    ((hl.pair polyFun_snd).comp polyFun_rawLetterIndex)).comp polyFun_labAt
  exact PolyFun.ite ((polyFun_snd.pair hl).comp polyFun_natListMem)
    (hc.add (polyFun_const 1)) (polyFun_const 0)

theorem polyFun_rawExtendLabels : PolyFun rawExtendLabels :=
  ((((polyFun_fst.comp polyFun_snd).pair polyFun_snd).pair
    (polyFun_fst.comp polyFun_fst)).comp (PolyFun.mapParam polyFun_rawExtendLabel))

theorem polyFun_rawExtendPartition : PolyFun rawExtendPartition :=
  ((polyFun_fst.pair (polyFun_snd.comp polyFun_fst)).comp polyFun_rawExtendLabels).pair
    ((polyFun_fst.pair (polyFun_snd.comp polyFun_snd)).comp polyFun_rawExtendLabels)

theorem rawExtendPartition_wf (z : RawExtendPartition) :
    (rawExtendPartition z).WF z.1.1.length := by
  simp [RawColPart.WF,rawExtendPartition,rawExtendLabels]

theorem rawExtendLabels_get (V W : List ℕ) (c : RawLab) (i : Fin V.length) :
    labAt (rawExtendLabels ((V,W),c)) i = rawExtendLabel ((W,c),V[i.val]) := by
  simp [labAt,rawExtendLabels,List.getD_eq_getElem,i.isLt]

theorem rawExtendLabel_of_mem {W : List ℕ} (hW : W.Nodup) (c : RawLab)
    (j : Fin W.length) : rawExtendLabel ((W,c),W[j.val]) = labAt c j + 1 := by
  simp only [rawExtendLabel,List.getElem_mem,decide_true,if_true,sbipLetterIndex_get hW]

theorem rawExtendLabel_of_notMem {W : List ℕ} (c : RawLab) {a : ℕ} (ha : a ∉ W) :
    rawExtendLabel ((W,c),a) = 0 := by simp [rawExtendLabel,ha]

theorem rawExtendPartition_cell (V W : List ℕ) (P : RawColPart) (i : Fin V.length) :
    cellOf (rawExtendPartition ((V,W),P)) i =
      if V[i.val] ∈ W then
        (labAt P.1 (rawLetterIndex (W,V[i.val])) + 1,
         labAt P.2 (rawLetterIndex (W,V[i.val])) + 1) else (0,0) := by
  simp only [cellOf,rawExtendPartition,rawExtendLabels_get,rawExtendLabel,decide_eq_true_eq]
  split_ifs <;> rfl

theorem rawExtendPartition_rel (V W : List ℕ) (P : RawColPart) (i j : Fin V.length) :
    (decColPartition V.length (rawExtendPartition ((V,W),P))).part i j ↔
      (V[i.val] ∈ W ↔ V[j.val] ∈ W) ∧
        (V[i.val] ∈ W → cellOf P (rawLetterIndex (W,V[i.val])) =
          cellOf P (rawLetterIndex (W,V[j.val]))) := by
  change cellOf (rawExtendPartition ((V,W),P)) i =
    cellOf (rawExtendPartition ((V,W),P)) j ↔ _
  rw [rawExtendPartition_cell,rawExtendPartition_cell]
  by_cases hi : V[i.val] ∈ W <;> by_cases hj : V[j.val] ∈ W <;>
    simp [hi,hj,cellOf,Prod.mk.injEq]

end Algo
