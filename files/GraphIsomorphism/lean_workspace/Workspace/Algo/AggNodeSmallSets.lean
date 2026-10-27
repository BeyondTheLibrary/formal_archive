import Workspace.Algo.AggNodeTransitivityTransport

/-! # The at most four individualized points in Case 2b

Enumerate all tuple lengths from zero through four, then retain the requested
length and increasing rows. The bound on the degree of transitivity makes
this exactly the paper's sets of size `d-1`, while the fixed enumeration gives
an unconditional polynomial RAM bound.
-/
namespace Algo
open RAM RAM.Targets Babai Equiv
open scoped Classical

def aggnTuplesUpTo : ℕ → List ℕ → List (List ℕ)
  | 0,C => tuplesOf C 0
  | k+1,C => aggnTuplesUpTo k C ++ tuplesOf C (k+1)

theorem aggnPolyFun_tuplesUpTo : ∀ k, PolyFun (aggnTuplesUpTo k)
  | 0 => ((polyFun_tuplesOf 0).comp polyFun_snd)
  | k+1 => ((aggnPolyFun_tuplesUpTo k).pair
      ((polyFun_tuplesOf (k+1)).comp polyFun_snd)).comp polyFun_append

theorem aggnTuplesUpTo_mem (k : ℕ) (C row : List ℕ) :
    row ∈ aggnTuplesUpTo k C ↔ row.length ≤ k ∧ ∀ u ∈ row, u ∈ C := by
  induction k with
  | zero =>
    change row ∈ tuplesOf C 0 ↔ _
    simp only [mem_tuplesOf, Nat.le_zero]
  | succ k ih =>
    simp only [aggnTuplesUpTo, List.mem_append, ih, mem_tuplesOf]
    constructor
    · rintro (⟨hl,hm⟩ | ⟨hl,hm⟩) <;> exact ⟨by omega,hm⟩
    · rintro ⟨hl,hm⟩
      by_cases h : row.length ≤ k
      · exact Or.inl ⟨h,hm⟩
      · exact Or.inr ⟨by omega,hm⟩

/-- Ambient domain, candidate set, and requested cardinality. -/
def aggnSmallSets (p : List ℕ × (List ℕ × ℕ)) : List (List ℕ) :=
  (aggnTuplesUpTo 4 p.2.1).filter fun row =>
    decide (row.length = p.2.2) && decide (row = aggNormalizeRow (p.1,row))

theorem aggnPolyFun_smallSets : PolyFun aggnSmallSets := by
  have hf : PolyFun (fun z : (List ℕ × (List ℕ × ℕ)) × List ℕ =>
      decide (z.2.length = z.1.2.2) && decide (z.2 = aggNormalizeRow (z.1.1,z.2))) :=
    wftPolyFun_and
      ((polyFun_snd.comp polyFun_length).natEq ((polyFun_fst.comp polyFun_snd).comp polyFun_snd))
      ((polyFun_snd.pair (((polyFun_fst.comp polyFun_fst).pair polyFun_snd).comp
        aggPolyFun_normalizeRow)).comp polyFun_listNatEq)
  exact (polyFun_id.pair ((polyFun_snd.comp polyFun_fst).comp
    (aggnPolyFun_tuplesUpTo 4))).comp (PolyFun.filterParam hf)

theorem aggnSmallSets_mem {dom C row : List ℕ} {d : ℕ} (hd : d ≤ 4) :
    row ∈ aggnSmallSets (dom,C,d) ↔
      row.length = d ∧ (∀ u ∈ row,u ∈ C) ∧ row = aggNormalizeRow (dom,row) := by
  simp only [aggnSmallSets, List.mem_filter, aggnTuplesUpTo_mem,
    Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨_,hmem⟩,hl,hn⟩
    exact ⟨hl,hmem,hn⟩
  · rintro ⟨hl,hmem,hn⟩
    exact ⟨⟨by omega,hmem⟩,hl,hn⟩

/-- Every mathematical subset has its increasing name in the enumeration. -/
theorem aggnSmallSets_complete {m d : ℕ} {dom C : List ℕ}
    (hdom : dom.length = m) (hd : d ≤ 4) (S : Set (Fin m))
    (hS : S ⊆ winSet m C) (hcard : S.ncard = d) :
    aggName S ∈ aggnSmallSets (dom,C,d) := by
  rw [aggnSmallSets_mem hd]
  refine ⟨(aggName_length S).trans hcard, ?_, aggName_normal S dom hdom⟩
  intro u hu
  have hul : u < m := List.mem_range.mp (List.mem_filter.mp hu).1
  have hs : (⟨u,hul⟩ : Fin m) ∈ winSet m (aggName S) := hu
  rw [aggName_spec] at hs
  exact hS hs

end Algo
