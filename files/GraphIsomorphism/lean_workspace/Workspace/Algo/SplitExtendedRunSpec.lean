import Workspace.Algo.SplitExtendedInput
import Workspace.Algo.SplitRelocalize

/-! Every computed Extended Design Lemma answer has the requested
threshold on the full original domain. The fixed UPCC evaluator bounds
are chosen once for the whole family, before the input is supplied. -/
namespace Algo
open Babai RAM
open scoped Classical

theorem decAlignPartition_isSplitOutcome {n : ℕ} (P : RawColPart) {α : ℝ}
    (hP : (decColPartition n P).IsAlphaPartition α) :
    IsSplitOutcome α Set.univ (decAlignPartition n P) := by
  letI : Fintype ↥(Set.univ : Set (Fin n)) := Fintype.ofFinite _
  refine ⟨rfl,?_⟩
  apply ColoredPartition.isAlphaPartition_of_kernel_rel (decColPartition n P) _
    (Equiv.Set.univ (Fin n)).symm
  · intro x y; rfl
  · intro x y; rfl
  · exact hP

def UpccSplitFamilyGood (c t d : ℕ) : Prop :=
  ∀ m r (C : (UPCCs (Fin m)).Obj Set.univ),UpccInputRep m r C →
    (∃ o,o ∈ upccSplitFamily c t d r) ∧
    ∀ o ∈ upccSplitFamily c t d r,∃ O,decAlignOutcome m o = some O ∧
      IsSplitOutcome (sbipAlphaValue r.2) Set.univ O

theorem extendedSplitBranch_valid {a c t d n : ℕ} (hsolver : UpccSplitFamilyGood c t d)
    {g : AmbientGIn} (h : ExtendedInputRep a n g) {xs : List ℕ} {o : RawDesignReadOut}
    (ho : (xs,o) ∈ ambientDesignReadFamily a g) :
    (∃ p,p ∈ extendedSplitBranch c t d (g,o)) ∧
      ∀ p ∈ extendedSplitBranch c t d (g,o),∃ Z,decAlignOutcome n p = some Z ∧
        IsSplitOutcome (sbipAlphaValue g.2) Set.univ Z := by
  cases hp : o.1 with
  | some P =>
    have he : extendedSplitBranch c t d (g,o) = [rawAlignPartition P] := by
      simp only [extendedSplitBranch,hp,Option.elim_some]
    rw [he]
    refine ⟨⟨_,List.mem_singleton_self _⟩,?_⟩
    intro p hmem
    have he := List.mem_singleton.1 hmem
    subst p
    exact ⟨_,decAlignOutcome_partition n P,
      decAlignPartition_isSplitOutcome P (h.partition_valid ho hp)⟩
  | none =>
    have hshape : ∃ q,o.2.2 = some q := by
      obtain ⟨_,rfl⟩ := (ambientDesignReadFamily_mem a g xs o).1 ho
      obtain ⟨L,q,hq⟩ := designReadExit_of_none hp
      exact ⟨q,congrArg (fun z : RawDesignReadOut => z.2.2) hq⟩
    obtain ⟨q,hq⟩ := hshape
    obtain ⟨C,hC,hupper,hbalance⟩ := h.upcc_admissible ho hq
    obtain ⟨hne,hgood⟩ := hsolver _ _ C hC
    have he : extendedSplitBranch c t d (g,o) =
        (upccSplitFamily c t d (extendedUpccInput ((g,o),q))).map
          (fun p => aggnRestoreOutcome ((g.1.1.2.2,o.2.1),p)) := by
      simp only [extendedSplitBranch,hp,Option.elim_none,hq,Option.elim_some,
        extendedUpccAnswers]
    rw [he]
    refine ⟨?_,?_⟩
    · obtain ⟨p,hp⟩ := hne
      exact ⟨_,List.mem_map_of_mem hp⟩
    · intro p hmem
      obtain ⟨p,hp,rfl⟩ := List.mem_map.1 hmem
      obtain ⟨Z,hdec,hZ⟩ := hgood p hp
      obtain ⟨hnd,hlt,_⟩ := h.upcc_storage ho hq
      have hhalf : 1/2 ≤ sbipAlphaValue g.2 := by have hh := h.lower; linarith
      exact splitRestoreOutcome_valid hnd hlt g.1.1.2.2 h.domain_length
        hupper.le hhalf hbalance hdec hZ

/-- The actual higher-arity RAM family is nonempty and all its entries
decode to valid full-domain answers. Its arity guard is explicit in the
input contract and is discharged at each master-algorithm call site. -/
theorem exists_extendedSplitFamily_valid (a c : ℕ) :
    ∃ t d,QuasiFun (extendedSplitFamily a c t d) ∧
      ∀ n g,ExtendedInputRep a n g →
        (∃ p,p ∈ extendedSplitFamily a c t d g) ∧
        ∀ p ∈ extendedSplitFamily a c t d g,∃ Z,decAlignOutcome n p = some Z ∧
          IsSplitOutcome (sbipAlphaValue g.2) Set.univ Z := by
  obtain ⟨t,d,_,hsolver⟩ := exists_upccSplitFamily_valid c
  refine ⟨t,d,quasiFun_extendedSplitFamily a c t d,?_⟩
  intro n g h
  constructor
  · obtain ⟨⟨xs,o⟩,ho⟩ := h.read_nonempty
    obtain ⟨p,hp⟩ := (extendedSplitBranch_valid hsolver h ho).1
    exact ⟨p,List.mem_flatMap.2 ⟨(xs,o),ho,hp⟩⟩
  · intro p hp
    obtain ⟨⟨xs,o⟩,ho,hp⟩ := List.mem_flatMap.1 hp
    exact (extendedSplitBranch_valid hsolver h ho).2 p hp

end Algo
