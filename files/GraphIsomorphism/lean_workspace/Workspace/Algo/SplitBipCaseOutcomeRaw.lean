import Workspace.Algo.SplitBipGraphStep9Dictionary
import Workspace.Algo.ExtendPartitionSpec

/-! Local case outcomes return to the current parent first part. Partition
labels use positions in that parent list. Johnson carriers use persistent
original point names. UPCC labels alone require a gather from compact
table names; ImprimitiveCase and DesignCase labels already use positions.
-/
namespace Algo
open Babai RAM

/-- Parent first-part names, numbered dictionary, and local compact names. -/
abbrev RawSbipCaseContext := List ℕ × (List (List ℕ) × List ℕ)

abbrev RawSbipNamedOutcome := List ℕ × RawAlignOutcome

def sbipCasePointList (z : RawSbipCaseContext) : List ℕ := sbipDictPoints z.2

def sbipCaseGather (z : List ℕ × RawLab) : RawColPart :=
  let l := z.1.map (fun a => labAt z.2 a)
  (l,l)

def sbipCasePartition (z : RawSbipCaseContext × RawColPart) : RawColPart :=
  rawExtendPartition ((z.1.1,sbipCasePointList z.1),z.2)

def sbipCaseJohnson (z : List (List ℕ) × RawJohnson) : RawJohnson :=
  (z.2.1.map (fun a => sbipDictPoint (z.1,a)),z.2.2)

def sbipCaseOutcome (z : RawSbipCaseContext × RawAlignOutcome) : RawSbipNamedOutcome :=
  (z.1.1,(z.2.1.map (fun P => sbipCasePartition (z.1,P)),
    z.2.2.map (fun J => sbipCaseJohnson (z.1.2.1,J))))

def sbipCaseImpExit (z : RawSbipCaseContext × RawLab) : RawSbipNamedOutcome :=
  sbipCaseOutcome (z.1,rawAlignPartition (z.2,z.2))

def sbipCaseUpccExit (z : RawSbipCaseContext × RawLab) : RawSbipNamedOutcome :=
  sbipCaseOutcome (z.1,rawAlignPartition (sbipCaseGather (z.1.2.2,z.2)))

theorem polyFun_sbipCasePointList : PolyFun sbipCasePointList :=
  polyFun_snd.comp polyFun_sbipDictPoints

theorem polyFun_sbipCaseGather : PolyFun sbipCaseGather := by
  have hm := (polyFun_snd.pair polyFun_fst).comp (PolyFun.mapParam polyFun_labAt)
  exact hm.pair hm

theorem polyFun_sbipCasePartition : PolyFun sbipCasePartition :=
  (((polyFun_fst.comp polyFun_fst).pair (polyFun_fst.comp polyFun_sbipCasePointList)).pair
    polyFun_snd).comp polyFun_rawExtendPartition

theorem polyFun_sbipCaseJohnson : PolyFun sbipCaseJohnson :=
  ((polyFun_fst.pair (polyFun_snd.comp polyFun_fst)).comp
    (PolyFun.mapParam polyFun_sbipDictPoint)).pair (polyFun_snd.comp polyFun_snd)

theorem polyFun_sbipCaseOutcome : PolyFun sbipCaseOutcome := by
  have hP : PolyFun (fun z : RawColPart × RawSbipCaseContext =>
      some (sbipCasePartition (z.2,z.1))) :=
    ((polyFun_snd.pair polyFun_fst).comp polyFun_sbipCasePartition).comp polyFun_some
  have hJ : PolyFun (fun z : RawJohnson × RawSbipCaseContext =>
      some (sbipCaseJohnson (z.2.2.1,z.1))) :=
    ((((polyFun_snd.comp polyFun_snd).comp polyFun_fst).pair polyFun_fst).comp
      polyFun_sbipCaseJohnson).comp polyFun_some
  have hp : PolyFun (fun z : RawSbipCaseContext × RawAlignOutcome =>
      z.2.1.elim none (fun P => some (sbipCasePartition (z.1,P)))) :=
    (((polyFun_snd.comp polyFun_fst).pair polyFun_fst).comp
    (PolyFun.optionElim (polyFun_const none) hP))
  have hj : PolyFun (fun z : RawSbipCaseContext × RawAlignOutcome =>
      z.2.2.elim none (fun J => some (sbipCaseJohnson (z.1.2.1,J)))) :=
    (((polyFun_snd.comp polyFun_snd).pair polyFun_fst).comp
    (PolyFun.optionElim (polyFun_const none) hJ))
  exact ((polyFun_fst.comp polyFun_fst).pair (hp.pair hj)).of_eq (fun z => by
    rcases z with ⟨d,P,J⟩
    cases P <;> cases J <;> rfl)

theorem polyFun_sbipCaseImpExit : PolyFun sbipCaseImpExit :=
  (polyFun_fst.pair ((polyFun_snd.pair polyFun_snd).comp polyFun_rawAlignPartition)).comp
    polyFun_sbipCaseOutcome

theorem polyFun_sbipCaseUpccExit : PolyFun sbipCaseUpccExit :=
  (polyFun_fst.pair (((((polyFun_fst.comp polyFun_snd).comp polyFun_snd).pair
    polyFun_snd).comp polyFun_sbipCaseGather).comp polyFun_rawAlignPartition)).comp
      polyFun_sbipCaseOutcome

theorem sbipCaseGather_get (l : List ℕ) (c : RawLab) (i : Fin l.length) :
    labAt (sbipCaseGather (l,c)).1 i = labAt c l[i.val] ∧
      labAt (sbipCaseGather (l,c)).2 i = labAt c l[i.val] := by
  simp [sbipCaseGather,labAt,i.isLt]

theorem sbipCaseGather_wf (l : List ℕ) (c : RawLab) :
    RawColPart.WF l.length (sbipCaseGather (l,c)) := by
  simp [RawColPart.WF,sbipCaseGather]

theorem sbipCasePartition_wf (z : RawSbipCaseContext × RawColPart) :
    RawColPart.WF z.1.1.length (sbipCasePartition z) := rawExtendPartition_wf _

@[simp] theorem sbipCaseOutcome_partition (d : RawSbipCaseContext) (P : RawColPart) :
    sbipCaseOutcome (d,rawAlignPartition P) =
      (d.1,rawAlignPartition (sbipCasePartition (d,P))) := rfl

@[simp] theorem sbipCaseOutcome_johnson (d : RawSbipCaseContext) (J : RawJohnson) :
    sbipCaseOutcome (d,rawAlignJohnson J) =
      (d.1,rawAlignJohnson (sbipCaseJohnson (d.2.1,J))) := rfl

end Algo
