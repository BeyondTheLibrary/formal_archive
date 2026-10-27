import Workspace.Algo.SplitBipIndex
import Workspace.Algo.NormalizeSI

/-! Refinement runs on compact positions. The recursive graph also retains
its ambient point and block dictionaries. Reading the output back on the
old names lets the following restrictions keep those dictionaries intact. -/
namespace Algo
open Babai RAM

def sbipRestoreAt (z : (RawConfig × List ℕ) × (ℕ × ℕ)) : ℕ :=
  binColor (z.1.1,(rawLetterIndex (z.1.2,z.2.1),rawLetterIndex (z.1.2,z.2.2)))

def sbipRestoreRow (z : (RawConfig × List ℕ) × List ℕ) : List ℕ × ℕ :=
  (z.2,sbipRestoreAt (z.1,(rawGet (z.2,0),rawGet (z.2,1))))

def sbipRestore (z : RawConfig × List ℕ) : RawConfig :=
  (z.2,(tuplesOf z.2 2).map (fun t => sbipRestoreRow (z,t)))

def sbipRefineNames (z : RawConfig × List ℕ) : RawConfig :=
  sbipRestore (sbipStep3 (sbipIndexed z),z.2)

theorem polyFun_sbipRestoreAt : PolyFun sbipRestoreAt := by
  have hl : PolyFun (fun z : (RawConfig × List ℕ) × (ℕ × ℕ) => z.1.2) :=
    polyFun_fst.comp polyFun_snd
  exact ((polyFun_fst.comp polyFun_fst).pair
    (((hl.pair (polyFun_snd.comp polyFun_fst)).comp polyFun_rawLetterIndex).pair
      ((hl.pair (polyFun_snd.comp polyFun_snd)).comp polyFun_rawLetterIndex))).comp polyFun_binColor

theorem polyFun_sbipRestoreRow : PolyFun sbipRestoreRow :=
  polyFun_snd.pair ((polyFun_fst.pair
    (((polyFun_snd.pair (polyFun_const 0)).comp polyFun_rawGet).pair
      ((polyFun_snd.pair (polyFun_const 1)).comp polyFun_rawGet))).comp polyFun_sbipRestoreAt)

theorem polyFun_sbipRestore : PolyFun sbipRestore :=
  polyFun_snd.pair ((polyFun_id.pair
    (polyFun_snd.comp ((polyFun_tuplesOf 2).comp polyFun_snd))).comp
      (PolyFun.mapParam polyFun_sbipRestoreRow))

theorem polyFun_sbipRefineNames : PolyFun sbipRefineNames :=
  ((sbipPoly_indexed.comp sbipPoly_step3).pair polyFun_snd).comp polyFun_sbipRestore

theorem sbipLetterIndex_get {l : List ℕ} (hnd : l.Nodup) (i : Fin l.length) :
    rawLetterIndex (l,l[i.val]) = i.val := by
  have hh := rawLetterIndex_spec (List.getElem_mem i.isLt)
  apply (List.Nodup.getElem_inj_iff hnd).1
  exact (List.getD_eq_getElem _ _ hh.1).symm.trans hh.2

theorem sbipRestore_get (p : RawConfig) (l : List ℕ) (hnd : l.Nodup) (i j : Fin l.length) :
    binColor (sbipRestore (p,l),(l[i.val],l[j.val])) = binColor (p,(i,j)) := by
  have ht : [l[i.val],l[j.val]] ∈ tuplesOf l 2 := (mem_tuplesOf _ _ _).2
    ⟨rfl,by simpa using And.intro (List.getElem_mem i.isLt) (List.getElem_mem j.isLt)⟩
  have hh := congrArg (fun o => o.getD 0) (sbipLookup
    (fun t => sbipRestoreAt ((p,l),(rawGet (t,0),rawGet (t,1)))) _ ht)
  have hr : binColor (sbipRestore (p,l),(l[i.val],l[j.val])) =
      sbipRestoreAt ((p,l),(l[i.val],l[j.val])) := by
    simpa [sbipRestore,sbipRestoreRow,rawGet,binColor,tblGet] using hh
  rw [hr,sbipRestoreAt,sbipLetterIndex_get hnd,sbipLetterIndex_get hnd]

section
variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {s : Set Ω}
    (G : VColBipBlk ↥s ℕ) (p : RawConfig) (l : List ℕ) (hnd : l.Nodup)
    (name : G.Vtx → ℕ) (e : G.Vtx ≃ Fin l.length)
    (he : ∀ A, l[(e A).val] = name A)

include hnd he in
theorem sbipRefineNames_spec
    (hc : ∀ A B, binColor (p,(name A,name B)) = G.vtxInitColor A B)
    (A B : G.Vtx) :
    binColor (sbipRefineNames (p,l),(name A,name B)) = G.wlNamed A B := by
  rw [sbipRefineNames,← he A,← he B,sbipRestore_get _ l hnd]
  apply sbipStep3_named G e (sbipIndexed_wf p l)
  intro C D
  rw [namedBin,sbipIndexed_get,he,he,hc]

end
end Algo
