import Workspace.Algo.DesignReadExitIso
import Workspace.Algo.DesignReadFamilyValidity

/-! # Exact relabeling of the ambient-guard Design Lemma pipeline -/
namespace Algo
open Babai RAM
open scoped Classical

/-- The original-domain guard does not affect the paper's canonical refinement. -/
theorem ambientPipeline321_relabel {n c : ℕ} {π : RawPerm} {ks base dom : List ℕ}
    {rels : RawRelStruct} (hπ : RawPerm.WF n π) (hnd : dom.Nodup)
    (hmem : ∀ i,i ∈ dom ↔ i < n) (hg : ks.length ≤ guardBound c base.length)
    (hrels : ∀ R ∈ rels,∀ t ∈ R,∀ i ∈ t,i < n) :
    ambientPipeline321 c ((ks,base,permList π dom),relabelRels (π,rels)) =
      relabelWL (π,ambientPipeline321 c ((ks,base,dom),rels)) := by
  rw [ambientPipeline321_of_guard hg,ambientPipeline321_of_guard hg]
  have ht : RawWL.WF n ks.length (tupleTable dom ks.length) := wf_tupleTable hnd hmem
  have h1 := rawF1_wf (a := (tupleTable dom ks.length,rels)) ht
  have h2 := rawF2I_wf (I := idxOf ks.length) h1
  rw [rawPipeline,rawPipeline,rawPipelineI,rawPipelineI,tupleTable_permList,
    rawF1_relabel hπ ht hrels,
    rawF2I_relabel hπ h1 (fun s hs => pairIdx_getD_lt hs)
      (fun σ hσ => (mem_monIdx.mp hσ).2),rawWLStable_relabelWL hπ h2]

/-- Tuple encodings carry the actual decoded permutation. -/
theorem designTupleOf_relabel {n l : ℕ} {π : RawPerm} (hπ : RawPerm.WF n π)
    (x : Str (Fin n) l) : tupleOf (tupleMap (decPerm n π) x) = permList π (tupleOf x) := by
  simp only [tupleOf,tupleMap,permList,List.map_ofFn]
  congr 1
  funext i
  exact (rawApply_of_wf hπ (x i).isLt).symm

/-- Relabeling a well-formed table supplies the named isomorphism used by read-off. -/
theorem designDecWL_relabel_iso {n k : ℕ} {π : RawPerm} {p : RawWL}
    (hπ : RawPerm.WF n π) (hp : RawWL.WF n k p) :
    decPerm n π ∈ KAryPartStruct.Iso (decWL n k p) (decWL n k (relabelWL (π,p))) := by
  intro x
  change tblGet ((relabelWL (π,p)).2,tupleOf (tupleMap (decPerm n π) x)) = tblGet (p.2,tupleOf x)
  rw [designTupleOf_relabel hπ]
  exact tblGet_relabelWL hπ hp (fun _ h => tupleOf_lt x h)

/-- The concrete scan transports its chosen tuple with the input list order. -/
theorem ambientDesignProcedure_relabel {n a b c : ℕ} {π : RawPerm} {ks base dom : List ℕ}
    {rels : RawRelStruct} (hπ : RawPerm.WF n π) (hnd : dom.Nodup)
    (hmem : ∀ i,i ∈ dom ↔ i < n) (hg : ks.length ≤ guardBound c base.length)
    (hrels : ∀ R ∈ rels,∀ t ∈ R,∀ i ∈ t,i < n) :
    ambientDesignProcedure c (((ks,base,permList π dom),relabelRels (π,rels)),(a,b)) =
      (ambientDesignProcedure c (((ks,base,dom),rels),(a,b))).map (permList π) := by
  unfold ambientDesignProcedure ambientDesignAt
  rw [ambientDesignScan_of_guard hg,ambientDesignScan_of_guard hg,
    ambientPipeline321_relabel hπ hnd hmem hg hrels]
  exact ansUpTo_relabel hπ
    (ambientPipeline321_wf (a := ((ks,base,dom),rels)) hnd hmem hg) [] [] ks.length

end Algo
