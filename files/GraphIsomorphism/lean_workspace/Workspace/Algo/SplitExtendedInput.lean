import Workspace.Algo.SplitExtendedRun
import Workspace.Algo.SplitUpccRunSpec
import Workspace.Algo.SplitRecodeWF

/-! The Extended Design Lemma input supplies the paper's arity and defect
hypotheses. The explicit ambient arity guard is the one used by the RAM
table constructor. Every UPCC exit derives the next call's requirements. -/
namespace Algo
open Babai RAM
open scoped Classical

structure ExtendedInputRep (c n : ℕ) (g : AmbientGIn) : Prop where
  nodup : g.1.1.2.2.Nodup
  domain : ∀ i,i ∈ g.1.1.2.2 ↔ i < n
  guard : g.1.1.1.length ≤ guardBound c g.1.1.2.1.length
  denominator : 0 < g.2.2
  lower : (3 : ℝ)/4 ≤ sbipAlphaValue g.2
  upper : sbipAlphaValue g.2 < 1
  two : 2 ≤ g.1.1.1.length
  arity : 4*g.1.1.1.length ≤ n
  defect : 1-sbipAlphaValue g.2 < (defect (decRel n g.1.1.1.length g.1.2).Aut : ℝ)

theorem designReadUpccTable_wf (z : DIn) :
    RawWL.WF (dominantList z).length 2 (designReadUpccTable z) :=
  sbipRecode_wf (designPairIndexed_wf z (dominantList z))

theorem designReadExit_upcc_storage {n k : ℕ} {z : DIn}
    (hw : RawWL.WF n k z.1.2) {q : RawConfig} (hq : (designReadExit z).2.2 = some q) :
    (designReadExit z).2.1.Nodup ∧ (∀ a ∈ (designReadExit z).2.1,a < n) ∧
      RawWL.WF (designReadExit z).2.1.length 2 q := by
  obtain ⟨_,_,hn,rfl⟩ := designReadExit_upcc hq
  rw [hn]
  exact ⟨hw.domNodup.filter _,fun _ ha => lt_of_mem_dominantList hw ha,
    designReadUpccTable_wf z⟩

namespace ExtendedInputRep
variable {c n : ℕ} {g : AmbientGIn} (h : ExtendedInputRep c n g)
include h

theorem domain_length : g.1.1.2.2.length = n := by
  simpa only [fst_ambientPipeline321] using
    card_eq_length_dom (ambientPipeline321_wf (n := n) (c := c) (a := g.1)
      h.nodup h.domain h.guard)

theorem read_nonempty : ∃ o,o ∈ ambientDesignReadFamily c g := by
  have hhalf : 1/2 ≤ sbipAlphaValue g.2 := by have hh := h.lower; linarith
  obtain ⟨xs,hxs⟩ := ambientDesignProcedure_nonempty g.1.1.1 g.1.1.2.1 g.1.1.2.2 g.1.2
    h.nodup h.domain rfl h.denominator rfl h.guard hhalf h.upper h.two
    (by have hh := h.arity; omega) h.defect.le
  have hm := ambientDesignVersions_nonempty h.nodup h.domain rfl h.guard h.denominator
    (α := sbipAlphaValue g.2) rfl hxs
  exact ⟨_,List.mem_map.2 ⟨xs,hm,rfl⟩⟩

theorem partition_valid {xs : List ℕ} {o : RawDesignReadOut}
    (ho : (xs,o) ∈ ambientDesignReadFamily c g) {P : RawColPart} (hp : o.1 = some P) :
    (decColPartition n P).IsAlphaPartition (sbipAlphaValue g.2) := by
  apply ambientDesignReadFamily_partition_valid h.nodup h.domain rfl h.guard h.denominator
    rfl _ _ ho hp
  · change 1/2 ≤ sbipAlphaValue g.2
    have hh := h.lower; linarith
  · have hh := h.arity; have hh' := h.two; omega

theorem upcc_storage {xs : List ℕ} {o : RawDesignReadOut}
    (ho : (xs,o) ∈ ambientDesignReadFamily c g) {q : RawConfig} (hq : o.2.2 = some q) :
    o.2.1.Nodup ∧ (∀ a ∈ o.2.1,a < n) ∧ RawWL.WF o.2.1.length 2 q := by
  obtain ⟨_,rfl⟩ := (ambientDesignReadFamily_mem c g xs o).1 ho
  exact designReadExit_upcc_storage
    (ambientPipeline321_wf (n := n) (c := c) (a := g.1) h.nodup h.domain h.guard) hq

theorem upcc_admissible {xs : List ℕ} {o : RawDesignReadOut}
    (ho : (xs,o) ∈ ambientDesignReadFamily c g) {q : RawConfig} (hq : o.2.2 = some q) :
    ∃ C : (UPCCs (Fin o.2.1.length)).Obj Set.univ,
      UpccInputRep o.2.1.length (extendedUpccInput ((g,o),q)) C ∧
      sbipAlphaValue (extendedUpccInput ((g,o),q)).2 < 1 ∧
      sbipAlphaValue (extendedUpccInput ((g,o),q)).2 * o.2.1.length =
        sbipAlphaValue g.2 * n := by
  have hhalf : 1/2 ≤ sbipAlphaValue g.2 := by have hh := h.lower; linarith
  obtain ⟨_,hdom,P,hcoh,huni,hcols⟩ := ambientDesignReadFamily_upcc_valid
    h.nodup h.domain rfl h.guard h.denominator rfl hhalf ho hq
  obtain ⟨hnd,hlt,hw⟩ := h.upcc_storage ho hq
  have hn : 0 < n := by have hh := h.arity; have hh' := h.two; omega
  have hlarge : sbipAlphaValue g.2 * n < o.2.1.length := by
    simpa only [IsDominant,Fintype.card_fin,ncard_winSet _ hnd hlt] using hdom
  have hsmall : o.2.1.length ≤ n := length_le_of_nodup_lt hnd hlt
  have hpos : 0 < o.2.1.length := by
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hh := h.lower
    have : (0 : ℝ) < o.2.1.length := by nlinarith
    exact_mod_cast this
  have hposR : (0 : ℝ) < o.2.1.length := by exact_mod_cast hpos
  have he : sbipAlphaValue (extendedUpccInput ((g,o),q)).2 =
      sbipAlphaValue g.2 * n / o.2.1.length := by
    dsimp only [extendedUpccInput,sbipAlphaValue]
    rw [h.domain_length]
    push_cast
    ring
  have hlow : (2 : ℝ)/3 ≤ sbipAlphaValue (extendedUpccInput ((g,o),q)).2 := by
    rw [he,le_div_iff₀ hposR]
    have hh := h.lower
    have hs : (o.2.1.length : ℝ) ≤ n := by exact_mod_cast hsmall
    have hnR : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    nlinarith
  let e := (Equiv.Set.univ (Fin o.2.1.length)).symm
  let C : (UPCCs (Fin o.2.1.length)).Obj Set.univ :=
    ⟨fun u v => binColor (q,(u.val,v.val)),P.congrEquiv e,
      PartitionStructure.congrEquiv_isCoherent e hcoh,
      PartitionStructure.congrEquiv_isUniprimitive e huni,
      by funext u v; exact (hcols u.val v.val).symm⟩
  refine ⟨C,⟨hw,fun _ _ => rfl,?_,hlow⟩,?_,?_⟩
  · exact Nat.mul_pos h.denominator hpos
  · rw [he,div_lt_one hposR]
    exact hlarge
  · rw [he,div_mul_cancel₀ _ (ne_of_gt hposR)]

end ExtendedInputRep
end Algo
