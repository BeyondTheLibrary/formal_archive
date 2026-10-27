import Workspace.Algo.SplitDesignJohnson
import Workspace.Algo.FunctorsAmbient
import Workspace.Algo.WFTests

/-! # Section 9.7: compute the relation of a skeleton

An injective tuple is in the skeleton when one stored edge contains all its
entries. We enumerate tuples at the guarded rank and test this condition.
At the full rank of a uniform hypergraph, the same test gives its own
relation. This avoids enumerating all subsets of the vertex set.
-/
namespace Algo
open Babai RAM

def designSubset (z : List ℕ × List ℕ) : Bool :=
  upccCaseAllB (fun p : List ℕ × ℕ => decide (p.2 ∈ p.1)) (z.2,z.1)

theorem polyFun_designSubset : PolyFun designSubset :=
  (polyFun_snd.pair polyFun_fst).comp
    (upccCasePoly_all ((polyFun_snd.pair polyFun_fst).comp
      (polyFun_listMem polyFun_natEq)))

theorem designSubset_spec (a b : List ℕ) :
    designSubset (a,b) = true ↔ ∀ i ∈ a, i ∈ b := by
  simp only [designSubset,upccCaseAllB_spec,decide_eq_true_eq]

/-- Injectivity and containment in some stored hyperedge. -/
def designRelTest (z : List (List ℕ) × List ℕ) : Bool :=
  wftNodup z.2 && !((z.1.filter (fun row => designSubset (z.2,row))).isEmpty)

theorem polyFun_designRelTest : PolyFun designRelTest := by
  have hf : PolyFun (fun z : List (List ℕ) × List ℕ =>
      z.1.filter (fun row => designSubset (z.2,row))) :=
    (polyFun_snd.pair polyFun_fst).comp (PolyFun.filterParam polyFun_designSubset)
  exact wftPolyFun_and (polyFun_snd.comp wftPolyFun_nodup)
    (polyFun_rawJNot (hf.comp polyFun_isEmpty))

/-- Rank witness, size witness, vertices, and hyperedge rows. -/
abbrev RawDesignRelInput := (List ℕ × List ℕ × List ℕ) × List (List ℕ)

def designRelations (c : ℕ) (z : RawDesignRelInput) : RawRelStruct :=
  [((aggTable c z.1).2.map Prod.fst).filter (fun row => designRelTest (z.2,row))]

theorem quasiFun_designRelations (c : ℕ) : QuasiFun (designRelations c) := by
  have ht : QuasiFun (fun z : RawDesignRelInput => (aggTable c z.1).2.map Prod.fst) :=
    (polyFun_fst.comp_quasiFun (aggQuasiFun_table c)).comp_poly
    (polyFun_snd.comp (PolyFun.map polyFun_fst))
  have hf : QuasiFun (fun z : RawDesignRelInput =>
      ((aggTable c z.1).2.map Prod.fst).filter (fun row => designRelTest (z.2,row))) :=
    (polyFun_snd.quasiFun.pair ht).comp_poly
    (PolyFun.filterParam polyFun_designRelTest)
  exact (hf.pair (polyFun_const ([] : RawRelStruct)).quasiFun).comp_poly polyFun_cons

theorem designSubset_tuple {n k : ℕ} (v : Fin k → Fin n) (row : List ℕ) :
    designSubset (tupleOf v,row) = true ↔
      Finset.univ.image v ⊆ splitRowSet n row := by
  rw [designSubset_spec,Finset.image_subset_iff]
  simp only [tupleOf,List.mem_ofFn,Finset.mem_univ,forall_const,mem_splitRowSet]
  constructor
  · intro hh i; exact hh (v i) ⟨i,rfl⟩
  · intro hh a ⟨i,hi⟩; simpa only [hi] using hh i

/-- The stored list and decoded hypergraph have the same containing edges. -/
theorem designRelTest_spec {n k : ℕ} (rows : List (List ℕ)) (v : Fin k → Fin n) :
    designRelTest (rows,tupleOf v) = true ↔
      Function.Injective v ∧ ∃ i,
        Finset.univ.image v ⊆ (decSplitHypergraph n rows).edge i := by
  rw [designRelTest,Bool.and_eq_true,wftNodup_eq_true_iff]
  have hn : (tupleOf v).Nodup ↔ Function.Injective v := by
    rw [tupleOf,List.nodup_ofFn]
    exact ⟨fun hh i j hij => hh (congrArg Fin.val hij),
      fun hh i j hij => hh (Fin.ext hij)⟩
  rw [hn]
  apply and_congr_right
  intro _
  simp only [Bool.not_eq_true',Bool.eq_false_iff,ne_eq,List.isEmpty_iff,
    List.eq_nil_iff_forall_not_mem,not_forall,not_not,List.mem_filter]
  constructor
  · rintro ⟨row,hr,hs⟩
    obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.1 hr
    refine ⟨⟨i,hi⟩,?_⟩
    change Finset.univ.image v ⊆ splitRowSet n (rows.getD i [])
    rw [List.getD_eq_getElem _ _ hi]
    exact (designSubset_tuple v _).1 hs
  · rintro ⟨i,hi⟩
    refine ⟨rows[i.val],List.getElem_mem i.isLt,?_⟩
    apply (designSubset_tuple v _).2
    change Finset.univ.image v ⊆ splitRowSet n (rows.getD i.val []) at hi
    rwa [List.getD_eq_getElem _ _ i.isLt] at hi

/-- The computed relation is exactly the skeleton relation. -/
theorem designRelations_skeleton {c n k : ℕ} (ks dom vertices : List ℕ)
    (rows : List (List ℕ)) (hk : ks.length = k)
    (hv : ∀ i : Fin n, i.val ∈ vertices)
    (hg : ks.length ≤ guardBound c dom.length) (v : Fin k → Fin n) :
    v ∈ (decRel n k (designRelations c ((ks,dom,vertices),rows))).rel 0 ↔
      v ∈ (((decSplitHypergraph n rows).skeleton k).toRelStructureSimple k).rel ⟨0,by change 0 < 1; omega⟩ := by
  rw [mem_decRel_rel]
  simp only [designRelations,List.getD_cons_zero,List.mem_filter]
  rw [aggTable_of_guard (a := (ks,dom,vertices)) hg,keys_tupleTable]
  have ht : tupleOf v ∈ tuplesOf vertices ks.length := by
    rw [mem_tuplesOf]
    refine ⟨(length_tupleOf v).trans hk.symm,?_⟩
    intro a ha
    obtain ⟨i,rfl⟩ := List.mem_ofFn.1 ha
    exact hv (v i)
  rw [and_iff_right ht,designRelTest_spec]
  change (_ ∧ _) ↔ Function.Injective v ∧ _
  rw [Hypergraph.mem_skeleton_edgeSet]
  apply and_congr_right
  intro hinj
  have hc : (Finset.univ.image v).card = k := by
    rw [Finset.card_image_of_injective _ hinj,Finset.card_univ,Fintype.card_fin]
  rw [hc,and_iff_right rfl]

end Algo
