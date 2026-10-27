import Workspace.Algo.DesignVersionsAmbient
import Workspace.Algo.SplitBipDisconnect
import Workspace.Algo.SplitBipIndex

/-! # Read the binary skeleton returned by the Design Lemma

The refinement table already contains each binary skeleton color. Reading
these entries preserves the individualizing tuple and avoids another
refinement before the disconnected-constituent test.
-/
namespace Algo
open Babai RAM

def designPairRow (z : DIn × List ℕ) : List ℕ × ℕ :=
  (z.2,restrPairColorAt (z.1,(rawGet (z.2,0),rawGet (z.2,1))))

def designPairTable (z : DIn × List ℕ) : RawConfig :=
  (z.2,(tuplesOf z.2 2).map (fun t => designPairRow (z.1,t)))

def designPairIndexed (z : DIn × List ℕ) : RawConfig :=
  sbipIndexed (designPairTable z,z.2)

def designDomPairs (z : DIn) : RawConfig := designPairIndexed (z,dominantList z)

theorem polyFun_designPairRow : PolyFun designPairRow :=
  polyFun_snd.pair ((polyFun_fst.pair
    (((polyFun_snd.pair (polyFun_const 0)).comp polyFun_rawGet).pair
      ((polyFun_snd.pair (polyFun_const 1)).comp polyFun_rawGet))).comp polyFun_restrPairColorAt)

theorem polyFun_designPairTable : PolyFun designPairTable :=
  polyFun_snd.pair ((polyFun_fst.pair
    (polyFun_snd.comp ((polyFun_tuplesOf 2).comp polyFun_snd))).comp
      (PolyFun.mapParam polyFun_designPairRow))

theorem polyFun_designPairIndexed : PolyFun designPairIndexed :=
  (polyFun_designPairTable.pair polyFun_snd).comp sbipPoly_indexed

theorem polyFun_designDomPairs : PolyFun designDomPairs :=
  (polyFun_id.pair polyFun_dominantList).comp polyFun_designPairIndexed

theorem designPairTable_get (z : DIn) (l : List ℕ) {u v : ℕ}
    (hu : u ∈ l) (hv : v ∈ l) :
    binColor (designPairTable (z,l),(u,v)) = restrPairColorAt (z,(u,v)) := by
  have ht : [u,v] ∈ tuplesOf l 2 := (mem_tuplesOf _ _ _).2 ⟨rfl,by simpa using And.intro hu hv⟩
  have hh := congrArg (fun o => o.getD 0) (sbipLookup
    (fun t => restrPairColorAt (z,(rawGet (t,0),rawGet (t,1)))) _ ht)
  simpa [designPairTable,designPairRow,rawGet,binColor,tblGet] using hh

theorem designPairIndexed_get (z : DIn) (l : List ℕ) (i j : Fin l.length) :
    binColor (designPairIndexed (z,l),(i,j)) = restrPairColorAt (z,(l[i],l[j])) := by
  rw [designPairIndexed,sbipIndexed_get]
  exact designPairTable_get z l (List.getElem_mem i.isLt) (List.getElem_mem j.isLt)

theorem designPairIndexed_wf (z : DIn) (l : List ℕ) :
    NamedBinaryWF l.length (designPairIndexed (z,l)) := sbipIndexed_wf _ _

/-- The stored pair is exactly the restriction's skeleton color. -/
theorem designPairTable_spec {n k t a b : ℕ} {ks : List ℕ} {p : RawWL}
    (hk : ks.length = k) (ht : t ≤ k) (h2 : t+2 ≤ k) (x : Str (Fin n) t)
    (l : List ℕ) (u v : Fin n) (hu : u.val ∈ l) (hv : v.val ∈ l) :
    binColor (designPairTable ((((ks,tupleOf x),p),(a,b)),l),(u,v)) =
      ((decWL n k p).restrTo ht x).skeletonColor (by norm_num) (by omega) ![u,v] := by
  rw [designPairTable_get _ _ hu hv]
  exact restrPairColorAt_spec hk ht h2 x u v

end Algo
