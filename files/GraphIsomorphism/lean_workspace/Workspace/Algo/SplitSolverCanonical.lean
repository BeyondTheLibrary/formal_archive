import Workspace.Algo.SplitBipTurnDesign3Transport
import Workspace.Algo.SplitBipTurnValueTransport
import Workspace.Algo.SplitBipInputRun
import Workspace.Algo.SplitExtendedTransport

/-! # Theorems 9.2.2 and 9.2.3 on the RAM: valid and canonical, with one choice of bounds

Theorem 9.2.2 (v2.5, Sec. 9.2) returns a canonical family of splits; Theorem 9.2.3 inherits
canonicity. On the RAM the recursive family is canonical at every time and storage bound
for which it computes the recursive values exactly (`sbipRun_canonical_of_exact`), now with
no premise, since Case 3 of Sec. 9.7 is canonical (`sbipDesign3ChildCovariant`). The bounds
of `exists_sbipRun_exact` therefore give one RAM routine that is valid and canonical, and the
UPCC routine (Theorem 9.2.1) and the Extended Design Lemma (Theorem 9.2.3) built on it are
valid and canonical with the same bounds.
-/
namespace Algo
open Babai RAM
open scoped Classical

/-- Sec. 9.4 on the RAM: at bounds where the executed family computes the recursive values,
it is canonical. -/
theorem sbipRun_canonical_of_exact {c t d : ℕ}
    (he : ∀ m I,SbipNodeValid m I → ∀ f,sbipNodeMeasure I < f →
      sbipRun c t d I = some ((sbipRound c).value f I)) : SbipRunCanonical c t d := by
  intro m I J X Y h h' φ hφ o ho
  rw [he m I ⟨X,h⟩ (sbipNodeMeasure I + 1) (by omega)] at ho
  rw [he m J ⟨Y,h'⟩ (sbipNodeMeasure J + 1) (by omega)]
  exact sbipValue_transport sbipDesign3ChildCovariant c _ I J X Y h h' φ hφ (by omega) _
    (by omega) o ho

/-- **Theorem 9.2.2 on the RAM, the recursive family**: quasipolynomial, valid on every
represented node, and canonical. -/
theorem exists_sbipRun_valid_canonical (c : ℕ) :
    ∃ t d,QuasiFun (sbipRun c t d) ∧
      (∀ m I,SbipNodeValid m I → ∃ A,sbipRun c t d I = some A ∧
        (∃ o,o ∈ A) ∧ SbipAnswersGood m I A) ∧ SbipRunCanonical c t d := by
  obtain ⟨t,d,hr,he⟩ := exists_sbipRun_exact c
  refine ⟨t,d,hr,?_,sbipRun_canonical_of_exact he⟩
  intro m I hI
  let f := sbipNodeMeasure I+1
  have hf : sbipNodeMeasure I < f := Nat.lt_succ_self _
  exact ⟨(sbipRound c).value f I,he m I hI f hf,sbipValue_valid_nonempty hI hf⟩

/-- Sec. 9.4 on the RAM: the recursive family is canonical, with no premise. -/
theorem exists_sbipRun_canonical (c : ℕ) :
    ∃ t d,QuasiFun (sbipRun c t d) ∧ SbipRunCanonical c t d := by
  obtain ⟨t,d,hq,-,hc⟩ := exists_sbipRun_valid_canonical c
  exact ⟨t,d,hq,hc⟩

/-- **Theorem 9.2.2 on the RAM**: the bipartite solver is quasipolynomial, valid and
canonical. -/
theorem exists_bipInputRun_valid_canonical (c : ℕ) :
    ∃ t d,QuasiFun (bipInputRun c t d) ∧ BipInputRunGood c t d ∧
      BipInputRunCanonical c t d := by
  obtain ⟨t,d,-,he,hc⟩ := exists_sbipRun_valid_canonical c
  refine ⟨t,d,quasiFun_bipInputRun c t d,?_,bipInputRun_canonical_of_sbip hc⟩
  intro m r X h
  obtain ⟨A,hA,hne,hgood⟩ := he m (bipInputNode r) ⟨bipToBlkObj X,h.node⟩
  exact ⟨A,hA,hne,fun o ho => hgood (bipToBlkObj X) h.node o ho⟩

/-- Theorem 9.2.1 on the RAM from a valid solver of Theorem 9.2.2 (the proof of
`exists_upccSplitFamily_valid`, at given bounds). -/
theorem upccSplitFamilyGood_of_bip {c t d : ℕ} (hsolver : BipInputRunGood c t d) :
    UpccSplitFamilyGood c t d := by
  intro m r C h
  have hd := card_eq_length_dom h.table
  have htwo : 2 ≤ m := by
    simpa only [Set.ncard_univ,Nat.card_fin] using upcc_two_le_ncard C.2
  constructor
  · obtain ⟨o,ho⟩ := (upccSplitVersion_valid hsolver h (i := 0) (by omega)).1
    exact ⟨o,List.mem_flatMap.2 ⟨0,List.mem_range.2 (by omega),ho⟩⟩
  · intro o ho
    obtain ⟨i,hi,ho⟩ := List.mem_flatMap.1 ho
    have him : i < m := by simpa only [List.mem_range,hd] using hi
    exact (upccSplitVersion_valid hsolver h him).2 o ho

/-- **Theorem 9.2.3 on the RAM**: with one choice of bounds, for every arity guard `a`, the
Extended Design Lemma family is quasipolynomial, returns valid splits, and is canonical: an
isomorphism `f` of two admitted inputs with the same arity list, guard string, domain list and
threshold carries every answer of the first to an answer of the second. -/
theorem exists_extendedSplitFamily_valid_canonical (c : ℕ) :
    ∃ t d,BipInputRunCanonical c t d ∧ ∀ a,QuasiFun (extendedSplitFamily a c t d) ∧
      (∀ n g,ExtendedInputRep a n g →
        (∃ p,p ∈ extendedSplitFamily a c t d g) ∧
        ∀ p ∈ extendedSplitFamily a c t d g,∃ Z,decAlignOutcome n p = some Z ∧
          IsSplitOutcome (sbipAlphaValue g.2) Set.univ Z) ∧
      (∀ n (g g' : AmbientGIn),ExtendedInputRep a n g → ExtendedInputRep a n g' →
        g.1.1 = g'.1.1 → g.2 = g'.2 → ∀ f : Equiv.Perm (Fin n),
        f ∈ KAryRelStruct.Iso (decRel n g.1.1.1.length g.1.2) (decRel n g.1.1.1.length g'.1.2) →
        ∀ p ∈ extendedSplitFamily a c t d g,∃ p' ∈ extendedSplitFamily a c t d g',
          RawSplitOutcomeIso n f p p') := by
  obtain ⟨t,d,-,hgood,hcan⟩ := exists_bipInputRun_valid_canonical c
  have hsolver := upccSplitFamilyGood_of_bip hgood
  refine ⟨t,d,hcan,fun a => ⟨quasiFun_extendedSplitFamily a c t d,?_,?_⟩⟩
  · intro n g h
    constructor
    · obtain ⟨⟨xs,o⟩,ho⟩ := h.read_nonempty
      obtain ⟨p,hp⟩ := (extendedSplitBranch_valid hsolver h ho).1
      exact ⟨p,List.mem_flatMap.2 ⟨(xs,o),ho,hp⟩⟩
    · intro p hp
      obtain ⟨⟨xs,o⟩,ho,hp⟩ := List.mem_flatMap.1 hp
      exact (extendedSplitBranch_valid hsolver h ho).2 p hp
  · intro n g g' h h' h1 hα f hf p hp
    exact extendedSplitFamily_transport hcan h h' h1 hα f hf hp

end Algo
