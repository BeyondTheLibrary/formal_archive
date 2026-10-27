import Workspace.Algo.SplitBipFromCase
import Workspace.Algo.SplitUpccCaseOutcome

/-! Section 9.8 returns a marked graph on compact vertex names.
Its selected color determines the padding outside the table. We retain
that color while restoring every original point, block, and decoration. -/
namespace Algo
open Babai RAM

abbrev RawUpccStored := (List ℕ × List (List ℕ)) × (RawLab × (ℕ × RawUpccBip))

def upccStoredInput (z : RawUpccStored) : RawSbipFromCase :=
  (z.1,((z.2.2.2,(z.2.1,[],([],[]))),if z.2.2.1 = 0 then 1 else 0))

def upccStored (z : RawUpccStored) : RawSbipStored := sbipFromCase (upccStoredInput z)

def upccStoredGraph (z : (List ℕ × List (List ℕ)) × (RawUpccCase × ℕ)) : RawSbipStored :=
  upccStored (z.1,(upccCaseMarks z.2,(upccCaseM z.2,upccCaseGraph z.2)))

theorem polyFun_upccStoredInput : PolyFun upccStoredInput := by
  have hg : PolyFun (fun z : RawUpccStored => z.2.2.2) :=
    (polyFun_snd.comp polyFun_snd).comp polyFun_snd
  have hm : PolyFun (fun z : RawUpccStored => z.2.2.1) :=
    (polyFun_snd.comp polyFun_snd).comp polyFun_fst
  have hp := PolyFun.ite (hm.natEq (polyFun_const 0)) (polyFun_const 1) (polyFun_const 0)
  exact (polyFun_fst.pair ((hg.pair
    ((polyFun_snd.comp polyFun_fst).pair (polyFun_const ([],([],[]))))).pair hp)).of_eq
      (fun z => by simp [upccStoredInput])

theorem polyFun_upccStored : PolyFun upccStored :=
  polyFun_upccStoredInput.comp polyFun_sbipFromCase

theorem polyFun_upccStoredGraph : PolyFun upccStoredGraph :=
  (polyFun_fst.pair ((polyFun_snd.comp upccCasePoly_marks).pair
    ((polyFun_snd.comp upccCasePoly_m).pair (polyFun_snd.comp upccCasePoly_graph)))).comp
      polyFun_upccStored

@[simp] theorem upccStored_matrix (z : RawUpccStored) :
    (upccStored z).1.1.2.2 = z.2.2.2.2.2 := rfl

theorem upccStored_column (z : RawUpccStored) (i : Fin z.2.2.2.2.1.length) :
    sbipDictGet ((upccStored z).2,z.1.1.length+i) =
      sbipDictGet (z.1.2,z.2.2.2.2.1[i.val]) := sbipFromCase_column (upccStoredInput z) i

theorem upccStored_blockColor (z : RawUpccStored) (i : Fin z.2.2.2.2.1.length) :
    labAt (upccStored z).1.2.2.1 (z.1.1.length+i) = 0 :=
  sbipFromCase_blockColor (upccStoredInput z) i

theorem upccStored_hint (z : RawUpccStored) (a b : ℕ) :
    binColor ((upccStored z).1.2.2.2,(a,b)) = 0 :=
  sbipFromCase_hint_zero (upccStoredInput z) (fun _ => rfl) a b

section
variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {s : Set Ω}
    (X : UPCCObj s) (point : ↥s → ℕ) (d : List (List ℕ))
    (e : ↥X.vtxSet ≃ Fin d.length)
    (hd : SbipVertexDictionary X.vtxSet point d e) (hp : Function.Injective point)
include hd hp

theorem upccStored_pointColor (w : List ℕ) (lab : RawLab) (m : ℕ) (g : RawUpccBip)
    (x : ↥s) (hx : point x < w.length) :
    labAt (upccStored ((w,d),(lab,(m,g)))).1.2.1 (point x) =
      upccCasePointColor X e lab m x := by
  rw [upccStored,sbipFromCase_pointColor _ _ hx]
  exact sbipVertexDictionary_color hd hp lab (if m = 0 then 1 else 0) x

theorem upccStoredGraph_pointColor (w : List ℕ) {r : RawUpccCase}
    (hw : r.WF) (hn : UpccCaseNames X e r) (B : ↥X.blocks)
    (x : ↥s) (hx : point x < w.length) :
    labAt (upccStoredGraph ((w,d),(r,upccCaseName₂ X e B))).1.2.1 (point x) =
      (X.upccBip B).f x :=
  (upccStored_pointColor X point d e hd hp w _ _ _ x hx).trans
    (upccCaseMarks_spec X e hw hn B x)

end
end Algo
