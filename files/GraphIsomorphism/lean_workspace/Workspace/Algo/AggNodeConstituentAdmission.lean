import Workspace.Algo.AggNodeConstituentInput
import Workspace.Algo.AggNodeGuideAdmission

/-! The actual Case 2b tables satisfy the input conditions of Theorem 9.2.3.
All relation indices are accounted for: index zero is the chosen constituent,
and later indices are empty. The original input degree remains in the raw
input as the witness for the uniform arity guard.
-/
namespace Algo
open RAM RAM.Targets Babai Equiv
open scoped Classical

theorem aggnConstituentEnter_numbered (original : List ℕ) (q : AggnRawConstituent) :
    decRel q.1.length 2 (aggnConstituentEnter (original,q)).2 =
      (aggnNumberedStruct q).toKAry (fun _ => rfl) := by
  apply congrArg KAryRelStruct.mk
  funext i
  apply Set.ext
  intro v
  by_cases hi : i < 1
  · have he : i = 0 := by omega
    subst i
    rw [dif_pos (show 0 < (aggnNumberedStruct q).numRel from by change 0 < 1; decide)]
    rfl
  · rw [dif_neg (show ¬ i < (aggnNumberedStruct q).numRel from hi)]
    change (tupleOf v ∈ ([aggnConstituentRel q] : List RawRel).getD i []) ↔ False
    rw [getD_of_length_le (by simpa using Nat.le_of_not_gt hi)]
    simp

theorem aggnConstituentEnter_defect {m : ℕ} (original : List ℕ) (q : AggnRawConstituent)
    (hnd : q.1.Nodup) (hlt : ∀ a ∈ q.1,a < m) :
    defect (decRel q.1.length 2 (aggnConstituentEnter (original,q)).2).Aut =
      case2bDefect (aggnDecodeConstituent m q) := by
  rw [aggnConstituentEnter_numbered,RelStructure.toKAry_aut]
  have hh := @RelStructure.structDefect_map_equiv (Fin q.1.length) ↥(winSet m q.1)
    inferInstance inferInstance (Fintype.ofFinite _) (Classical.decEq _)
    (aggnNumberedStruct q) (winEquiv m q.1 hnd hlt)
  rw [aggnNumberedStruct_map q hnd hlt] at hh
  exact hh.symm

/-- A computed member supplies its own size, defect, and numbering proofs. -/
theorem aggnAggregateConstituent_admissible {c n m : ℕ} {C : AggnPhaseCtx} {s : AggnAggregateState}
    {ϕ : decGroup n C.1.1.2 →* Perm (Fin m)} (hC : AggnPhaseCtxWF c n m C ϕ)
    (hm : 217 ≤ m) (hcase : aggnAggregateDispatch (C,s) = 2)
    (hgiant : aggnAggregateGiantBranch (C,s) = false)
    {q : AggnRawConstituent} (hq : q ∈ aggnAggregateCase2b ((C,s),false)) :
    q.1.Nodup ∧ (∀ a ∈ q.1,a < m) ∧ 11*m ≤ 15*q.1.length ∧
      2 ≤ 2 ∧ 4*2 ≤ q.1.length ∧
      (1/4 : ℝ) < (defect (decRel q.1.length 2 (aggnConstituentEnter (C.2.1,q)).2).Aut : ℝ) := by
  obtain ⟨hnd,hlt⟩ := aggnCase2bFamily_names hC.action.2.1 hq
  obtain ⟨hok,hlarge⟩ := (aggnAggregateCase2b_source_facts hC hm hcase hgiant).2.1 q hq
  have hc := ncard_winSet q.1 hnd hlt
  change 2 ≤ 2 ∧ 4*2 ≤ (winSet m q.1).ncard ∧ _ at hok
  rw [hc] at hok hlarge
  refine ⟨hnd,hlt,hlarge,hok.1,hok.2.1,?_⟩
  rw [aggnConstituentEnter_defect C.2.1 q hnd hlt]
  linarith [hok.2.2]

end Algo
