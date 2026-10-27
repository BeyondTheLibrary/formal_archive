import Workspace.Algo.SplitEquipRead
import Workspace.Algo.DesignReadExit

/-! A Design Lemma partition supplies the refined color split and its
equivalence-relation hint. A UPCC supplies its carrier and its pair colors.
The hint is zero outside that first part in both cases. -/
namespace Algo
open Babai RAM

def designReadFirst (o : RawDesignReadOut) : List ℕ :=
  o.1.elim o.2.1 rawEquipFirst

def designUpccHintAt (z : (List ℕ × Option RawConfig) × (ℕ × ℕ)) : ℕ :=
  if decide (z.2.1 ∈ z.1.1) && decide (z.2.2 ∈ z.1.1) then
    z.1.2.elim 0 (fun q => binColor (q,
      (rawLetterIndex (z.1.1,z.2.1),rawLetterIndex (z.1.1,z.2.2))))
  else 0

def designReadHintAt (z : RawDesignReadOut × (ℕ × ℕ)) : ℕ :=
  z.1.1.elim (designUpccHintAt (z.1.2,z.2)) (fun P => rawEquipHintAt (P,z.2))

theorem polyFun_designReadFirst : PolyFun designReadFirst :=
  (polyFun_fst.pair (polyFun_snd.comp polyFun_fst)).comp
    (PolyFun.optionElim polyFun_id (polyFun_fst.comp polyFun_rawEquipFirst))

theorem polyFun_designUpccHintAt : PolyFun designUpccHintAt := by
  have hl : PolyFun (fun z : (List ℕ × Option RawConfig) × (ℕ × ℕ) => z.1.1) :=
    polyFun_fst.comp polyFun_fst
  have hi : PolyFun (fun z : (List ℕ × Option RawConfig) × (ℕ × ℕ) => z.2.1) :=
    polyFun_snd.comp polyFun_fst
  have hj : PolyFun (fun z : (List ℕ × Option RawConfig) × (ℕ × ℕ) => z.2.2) :=
    polyFun_snd.comp polyFun_snd
  have hm := polyFun_rawJAnd ((hi.pair hl).comp polyFun_natListMem)
    ((hj.pair hl).comp polyFun_natListMem)
  have ix := (hl.pair hi).comp polyFun_rawLetterIndex
  have jx := (hl.pair hj).comp polyFun_rawLetterIndex
  have hb : PolyFun (fun z : (List ℕ × Option RawConfig) × (ℕ × ℕ) =>
      z.1.2.elim 0 (fun q => binColor (q,(rawLetterIndex (z.1.1,z.2.1),
        rawLetterIndex (z.1.1,z.2.2))))) :=
    ((polyFun_fst.comp polyFun_snd).pair (ix.pair jx)).comp
      (PolyFun.optionElim (polyFun_const 0) polyFun_binColor)
  exact PolyFun.ite hm hb (polyFun_const 0)

theorem polyFun_designReadHintAt : PolyFun designReadHintAt := by
  have hn : PolyFun (fun z : RawDesignReadOut × (ℕ × ℕ) => designUpccHintAt (z.1.2,z.2)) :=
    ((polyFun_fst.comp polyFun_snd).pair polyFun_snd).comp polyFun_designUpccHintAt
  have hs : PolyFun (fun z : RawColPart × (RawDesignReadOut × (ℕ × ℕ)) =>
      rawEquipHintAt (z.1,z.2.2)) :=
    (polyFun_fst.pair (polyFun_snd.comp polyFun_snd)).comp polyFun_rawEquipHintAt
  exact ((polyFun_fst.comp polyFun_fst).pair polyFun_id).comp (PolyFun.optionElim hn hs)

theorem designReadFirst_partition (P : RawColPart) :
    designReadFirst (designReadPartitionExit P) = rawEquipFirst P := rfl

theorem designReadHintAt_partition (P : RawColPart) (i j : ℕ) :
    designReadHintAt (designReadPartitionExit P,(i,j)) = rawEquipHintAt (P,(i,j)) := rfl

theorem designUpccHintAt_get {l : List ℕ} (hnd : l.Nodup) (q : RawConfig)
    (i j : Fin l.length) :
    designUpccHintAt ((l,some q),(l[i.val],l[j.val])) = binColor (q,(i,j)) := by
  have hi := rawLetterIndex_spec (List.getElem_mem i.isLt)
  have hj := rawLetterIndex_spec (List.getElem_mem j.isLt)
  have hei : rawLetterIndex (l,l[i.val]) = i.val :=
    (List.Nodup.getElem_inj_iff hnd).1 ((List.getD_eq_getElem _ _ hi.1).symm.trans hi.2)
  have hej : rawLetterIndex (l,l[j.val]) = j.val :=
    (List.Nodup.getElem_inj_iff hnd).1 ((List.getD_eq_getElem _ _ hj.1).symm.trans hj.2)
  simp [designUpccHintAt,List.getElem_mem,hei,hej]

theorem designReadHintAt_off_first (o : RawDesignReadOut) (i j : ℕ)
    (hoff : i ∉ designReadFirst o ∨ j ∉ designReadFirst o) :
    designReadHintAt (o,(i,j)) = 0 := by
  rcases o with ⟨op,l,q⟩
  cases op with
  | none =>
    change i ∉ l ∨ j ∉ l at hoff
    rcases hoff with hi | hj <;> simp [*,designReadHintAt,designUpccHintAt]
  | some P =>
    change i ∉ rawEquipFirst P ∨ j ∉ rawEquipFirst P at hoff
    rcases hoff with hi | hj <;> simp [*,designReadHintAt,rawEquipHintAt]

end Algo
