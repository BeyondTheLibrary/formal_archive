import Workspace.Algo.DesignReadFamilyRelabel

/-! # Size witness contents do not affect the Design Lemma

The arity and original-domain lists supply their lengths. The tuple domain,
relations, and individualizing tuple contain the data that is read. These
identities apply on all raw inputs, including a failed arity guard.
-/
namespace Algo
open Babai RAM

/-- Only the positions in the arity witness are used to build a tuple. -/
theorem designIndivTuple_witness {ks ks' : List ℕ} (hk : ks'.length = ks.length)
    (xs : List ℕ) (u v : ℕ) : indivTuple ((ks',xs),(u,v)) = indivTuple ((ks,xs),(u,v)) := by
  apply List.ext_getElem (by simpa using hk)
  intro i hi hi'
  rw [getElem_indivTuple,getElem_indivTuple]

section
variable {ks ks' : List ℕ} (hk : ks'.length = ks.length) (xs : List ℕ) (p : RawWL) (ab : ℕ × ℕ)
local notation "z" => (((ks,xs),p),ab)
local notation "z'" => (((ks',xs),p),ab)
include hk

theorem designReadPair_witness (u v : ℕ) : restrPairColorAt (z',(u,v)) = restrPairColorAt (z,(u,v)) := by
  simp only [restrPairColorAt,designIndivTuple_witness hk]

theorem designReadDominant_witness : dominantList z' = dominantList z := by
  simp only [dominantList,classSize,restrVColorAt,designReadPair_witness hk]
  rfl

theorem designReadReturn_witness : returnsB z' = returnsB z := by
  simp only [returnsB,noDominantB,restrVColors,classSize,restrVColorAt,
    cliqueRank,pairColors,designReadDominant_witness hk,designReadPair_witness hk,hk]
  rfl

theorem designReadExit_witness : designReadExit z' = designReadExit z := by
  have ht : designDomPairs z' = designDomPairs z := by
    simp only [designDomPairs,designPairIndexed,designPairTable,designPairRow,
      designReadDominant_witness hk,designReadPair_witness hk]
  simp only [designReadExit,designReadHasComponents,designReadHasSkeleton,
    designReadHasUpcc,designReadPartitionExit,designReadUpccExit,designReadUpccTable,
    designReadPart,designReadPlain,designReadColors,designReadBlock,designReadComponents,
    designReadIndex,restrVColorAt,designReadPair_witness hk,ht,designReadDominant_witness hk,
    cliqueRank,pairColors,hk]
  rfl

end

theorem designAnsUpTo_witness {ks ks' : List ℕ} (hk : ks'.length = ks.length)
    (xs : List ℕ) (p : RawWL) (ab : ℕ × ℕ) (j : ℕ) :
    ansUpTo (((ks',xs),p),ab) j = ansUpTo (((ks,xs),p),ab) j := by
  have hs (l : ℕ) : scanLen l (((ks',xs),p),ab) = scanLen l (((ks,xs),p),ab) := by
    simp only [scanLen,withStr,designReadReturn_witness hk]
  induction j with
  | zero => rfl
  | succ j ih => rw [ansUpTo,ansUpTo,ih,hs]

theorem designAggTable_witness {ks ks' base base' dom : List ℕ}
    (hk : ks'.length = ks.length) (hb : base'.length = base.length) (c : ℕ) :
    aggTable c (ks',base',dom) = aggTable c (ks,base,dom) := by
  simp only [aggTable,aggTabSetUp,hk,hb]

theorem designPipeline_witness {ks ks' base base' dom : List ℕ}
    (hk : ks'.length = ks.length) (hb : base'.length = base.length) (c : ℕ) (rels : RawRelStruct) :
    ambientPipeline321 c ((ks',base',dom),rels) = ambientPipeline321 c ((ks,base,dom),rels) := by
  have hmon : ambientMon c ((ks',base',dom),rels) = ambientMon c ((ks,base,dom),rels) := by
    simp only [ambientMon,hk,designAggTable_witness hk hb]
  simp only [ambientPipeline321,ambientIdx,pairIdxOf_eq,hk,hmon,designAggTable_witness hk hb]

/-- The bounded scan reads only the two witness lengths. -/
theorem designAmbientScan_witness {ks ks' base base' : List ℕ}
    (hk : ks'.length = ks.length) (hb : base'.length = base.length)
    (xs : List ℕ) (p : RawWL) (ab : ℕ × ℕ) (c : ℕ) :
    ambientDesignScan c (base',(((ks',xs),p),ab)) = ambientDesignScan c (base,(((ks,xs),p),ab)) := by
  simp only [ambientDesignScan,ambientScanSetUp,scanStep_iterate,
    ambientScanRounds,hk,hb,designAnsUpTo_witness hk]

theorem designAmbientProcedure_witness {ks ks' base base' dom : List ℕ}
    (hk : ks'.length = ks.length) (hb : base'.length = base.length)
    (rels : RawRelStruct) (ab : ℕ × ℕ) (c : ℕ) :
    ambientDesignProcedure c (((ks',base',dom),rels),ab) =
      ambientDesignProcedure c (((ks,base,dom),rels),ab) := by
  simp only [ambientDesignProcedure,ambientDesignAt,designPipeline_witness hk hb,
    designAmbientScan_witness hk hb]

theorem designAmbientVersions_witness {ks ks' base base' dom : List ℕ}
    (hk : ks'.length = ks.length) (hb : base'.length = base.length)
    (rels : RawRelStruct) (ab : ℕ × ℕ) (c : ℕ) :
    ambientDesignVersions c (((ks',base',dom),rels),ab) =
      ambientDesignVersions c (((ks,base,dom),rels),ab) := by
  have hat (xs : List ℕ) : ambientDesignVersionsAt c ((((ks',base',dom),rels),ab),xs) =
      ambientDesignVersionsAt c ((((ks,base,dom),rels),ab),xs) := by
    have ht : (ks'.take xs.length).length = (ks.take xs.length).length := by simp only [List.length_take,hk]
    simp only [ambientDesignVersionsAt,ambientDesignVersionRows,designAggTable_witness ht hb,
      ambientDesignAt,designPipeline_witness hk hb,designReadReturn_witness hk]
  simp only [ambientDesignVersions,designAmbientProcedure_witness hk hb,hat]

/-- Every raw read-off entry is independent of witness contents. -/
theorem designAmbientReadFamily_witness {ks ks' base base' dom : List ℕ}
    (hk : ks'.length = ks.length) (hb : base'.length = base.length)
    (rels : RawRelStruct) (ab : ℕ × ℕ) (c : ℕ) :
    ambientDesignReadFamily c (((ks',base',dom),rels),ab) =
      ambientDesignReadFamily c (((ks,base,dom),rels),ab) := by
  simp only [ambientDesignReadFamily,designAmbientVersions_witness hk hb,
    ambientDesignAt,withStr,designPipeline_witness hk hb,designReadExit_witness hk]

end Algo
