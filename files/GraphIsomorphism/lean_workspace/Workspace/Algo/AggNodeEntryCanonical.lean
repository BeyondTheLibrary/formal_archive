import Workspace.Algo.SplitExtendedTransport
import Workspace.Algo.AggNodeContinuationTransport
import Workspace.Algo.AggNodeContinuationCanonical
import Workspace.Algo.SplitSolverCanonical

/-! # The aggregate continuations get a canonical Theorem 9.2.3

Line 6a of Sec. 15 (v2.5) and outcomes (2b) and (3) of Theorem 13.2.1 apply the Extended Design
Lemma, Theorem 9.2.3, whose outputs are canonical. The Section 13 track states the RAM form of
that canonicity as `AggnEntryFamilyCanonical`. It follows from the canonicity of the
bipartite solver of Theorem 9.2.2 (`BipInputRunCanonical`) by `extendedSplitFamily_transport`.
-/
namespace Algo
open Babai RAM

/-- Sec. 9.2, Theorem 9.2.3 (canonicity), in the form the aggregate continuations use. -/
theorem aggnEntryFamilyCanonical_of_bip {c b t d : ℕ} (hsolver : BipInputRunCanonical b t d) :
    AggnEntryFamilyCanonical c b t d := by
  intro k a a' hI hI' h1 f hf o ho
  exact extendedSplitFamily_transport hsolver hI hI' h1 rfl f hf ho

/-- Theorem 9.2.3 for the aggregate continuations, with no premise: one choice of bounds makes
the restored family quasipolynomial and valid (as in `exists_aggnRestoredEntryFamily_valid`)
and Theorem 9.2.3 canonical, for every arity guard. -/
theorem exists_aggnRestoredEntryFamily_valid_canonical (b : ℕ) :
    ∃ t d,∀ c,AggnEntryFamilyCanonical c b t d ∧ QuasiFun (aggnRestoredEntryFamily c b t d) ∧
      ∀ m dom (a : AggnDesignEntry),dom.length = m →
        a.1.Nodup → (∀ u ∈ a.1,u < m) → 11*m ≤ 15*a.1.length →
        ExtendedInputRep (c+1) a.1.length (a.2,(3,4)) →
        (∃ o,o ∈ aggnRestoredEntryFamily c b t d (dom,a)) ∧
        ∀ o ∈ aggnRestoredEntryFamily c b t d (dom,a),∃ β Z,
          decAlignOutcome m o = some Z ∧ 1/2 < β ∧ 0 ≤ β ∧ 5*β ≤ 4 ∧
            IsSplitOutcome β Set.univ Z := by
  obtain ⟨t,d,hcan,hfam⟩ := exists_extendedSplitFamily_valid_canonical b
  refine ⟨t,d,fun c => ⟨aggnEntryFamilyCanonical_of_bip hcan,
    aggnQuasiFun_restoredEntryFamily c b t d,?_⟩⟩
  intro m dom a hdom hnd hlt hlarge hI
  obtain ⟨-,hsolver,-⟩ := hfam (c+1)
  obtain ⟨hne,hgood⟩ := hsolver a.1.length (a.2,(3,4)) hI
  constructor
  · obtain ⟨o,ho⟩ := hne
    exact ⟨_,List.mem_map_of_mem ho⟩
  · intro o ho
    obtain ⟨p,hp,rfl⟩ := List.mem_map.1 ho
    obtain ⟨Z,hdec,hZ⟩ := hgood p hp
    exact aggnRestoreOutcome_valid hnd hlt hlarge dom hdom hdec hZ

end Algo

set_option synthInstance.maxSize 2048
namespace Algo
open RAM RAM.Targets Babai Equiv

/-- §13.2 and §15, lines 6a–7a, with no premise: at the bounds of
`exists_aggnRestoredEntryFamily_valid_canonical`, the versions listed by the continuation at
tags `1`, `3` (outcome (2b)) and `4` (outcome (3)) are canonical. -/
theorem aggnContinuation_transport_of_bip {b t d : ℕ} (hsolver : BipInputRunCanonical b t d)
    {c n m : ℕ} {C : AggnPhaseCtx} {s : AggnAggregateState}
    {ϕ : decGroup n C.1.1.2 →* Perm (Fin m)}
    (hC : AggnPhaseCtxWF c n m C ϕ) (hs : AggnStoresComplete c ϕ s.1.2.1)
    (hm : 217 ≤ m)
    (htbl : AggnCompareTableFor c ϕ (aggnCompareTable c (C,s.2.2.2.1)))
    (hset : LocalCertSetting (decGroup n C.1.1.2) ϕ)
    (ht : LargeK C.2.2.2.length (Nat.card (Fin n))) (htm : 10*C.2.2.2.length ≤ m)
    [Nonempty (Fin n)]
    (htag : (aggnContinuation c b t d (C,s)).1 ∈ ({1,3,4} : Finset ℕ))
    (σ : decGroup n C.1.1.2) (hσ : strAct (decStrN n C.2.1) σ.val = decStrN n C.2.2.1)
    {o : RawAlignOutcome} (ho : o ∈ (aggnContinuation c b t d (C,s)).2.1) :
    ∃ o' ∈ (aggnContinuation c b t d (C,s)).2.2, RawSplitOutcomeIso m (ϕ σ) o o' :=
  aggnContinuation_transport hC hs (aggnEntryFamilyCanonical_of_bip hsolver) hm htbl hset ht htm
    htag σ hσ ho

end Algo
