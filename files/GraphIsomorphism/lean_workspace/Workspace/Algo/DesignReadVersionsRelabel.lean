import Workspace.Algo.DesignReadPipelineRelabel

/-! # Relabeling the full family of returning tuples

Every successful tuple at the least returning length is retained. Both the
scan and the full table at that length move with the vertex names.
-/
namespace Algo
open Babai RAM

/-- Prefixing the arity always remains inside the original-domain guard. -/
theorem ambientDesignVersionRows_prefix {a b c : ℕ} {ks base dom : List ℕ} {rels : RawRelStruct}
    (hg : ks.length ≤ guardBound c base.length) (xs : List ℕ) :
    ambientDesignVersionRows c ((((ks,base,dom),rels),(a,b)),xs) =
      tuplesOf dom (min xs.length ks.length) := by
  unfold ambientDesignVersionRows
  rw [aggTable_of_guard (by simpa only [List.length_take] using
    (min_le_right xs.length ks.length).trans hg),keys_tupleTable,List.length_take]

section
variable {n a b c : ℕ} {π : RawPerm} {ks base dom : List ℕ} {rels : RawRelStruct}
    (hπ : RawPerm.WF n π) (hnd : dom.Nodup) (hmem : ∀ i,i ∈ dom ↔ i < n)
    (hg : ks.length ≤ guardBound c base.length)
    (hrels : ∀ R ∈ rels,∀ t ∈ R,∀ i ∈ t,i < n)
local notation "g" => (((ks,base,dom),rels),(a,b))
local notation "g'" => (((ks,base,permList π dom),relabelRels (π,rels)),(a,b))
include hπ hnd hmem hg hrels

/-- The whole successful row table, not only its first entry, transports. -/
theorem ambientDesignVersionsAt_relabel (xs : List ℕ) :
    ambientDesignVersionsAt c (g',permList π xs) =
      (ambientDesignVersionsAt c (g,xs)).map (permList π) := by
  rw [ambientDesignVersionsAt,ambientDesignVersionsAt,
    ambientDesignVersionRows_prefix hg,ambientDesignVersionRows_prefix hg,
    length_permList,tuplesOf_permList,filter_map_comm]
  congr 1
  apply List.filter_congr
  intro ys hys
  have hlt : ∀ i ∈ ys,i < n := fun i hi => (hmem i).mp (((mem_tuplesOf _ _ _).mp hys).2 i hi)
  unfold ambientDesignAt
  rw [ambientPipeline321_relabel hπ hnd hmem hg hrels]
  exact returnsB_relabel hπ
    (ambientPipeline321_wf (a := ((ks,base,dom),rels)) hnd hmem hg) hlt

/-- Every returning version moves with the input, preserving the full family. -/
theorem ambientDesignVersions_relabel :
    ambientDesignVersions c g' = (ambientDesignVersions c g).map (permList π) := by
  rw [ambientDesignVersions,ambientDesignVersions,
    ambientDesignProcedure_relabel hπ hnd hmem hg hrels]
  cases hs : ambientDesignProcedure c g with
  | none => rfl
  | some xs => exact ambientDesignVersionsAt_relabel hπ hnd hmem hg hrels xs

end
end Algo
