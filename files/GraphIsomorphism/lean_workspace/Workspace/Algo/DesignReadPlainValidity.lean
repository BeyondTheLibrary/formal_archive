import Workspace.Algo.DesignReadUpcc
import Workspace.Algo.SplitPartitionTransport
import Workspace.DesignLemma.Reduction

/-! # Validity of the Design Lemma's plain coloring exit

The RAM output retains the table's vertex colors. The mathematical output
uses their ranks. Equality of colors is the same in both, and each block is
a whole color class, so the alpha-partition bound transfers directly.
-/
namespace Algo
open Babai RAM
open scoped Classical

theorem designReadPlain_color_of_length {n : ℕ} {z : DIn}
    (hd : z.1.2.1.length = n) (u : Fin n) :
    (decColPartition n (designReadPlain z)).color u = restrVColorAt (z,u) := by
  simp [decColPartition,designReadPlain,designReadColors,labAt,hd]

theorem designReadPlain_rel_of_length {n : ℕ} {z : DIn}
    (hd : z.1.2.1.length = n) (u v : Fin n) :
    (decColPartition n (designReadPlain z)).part u v ↔
      restrVColorAt (z,u) = restrVColorAt (z,v) := by
  change cellOf (designReadPlain z) u = cellOf (designReadPlain z) v ↔ _
  simp [cellOf,designReadPlain,designReadColors,labAt,hd,u.isLt,v.isLt]

/-- The stored plain partition inherits the bound of the actual restriction. -/
theorem designReadPlain_isAlphaPartition {n k l a b : ℕ} {ks : List ℕ} {p : RawWL}
    (hw : RawWL.WF n k p) (hk : ks.length = k) (hl : l ≤ k) (x : Str (Fin n) l)
    {α : ℝ} (hα : 1/2 ≤ α)
    (hno : KAryPartStruct.NoDominantColor α ((decWL n k p).restrTo hl x)) :
    (decColPartition n (designReadPlain (((ks,tupleOf x),p),(a,b)))).IsAlphaPartition α := by
  let Y := (decWL n k p).restrTo hl x
  let z : DIn := (((ks,tupleOf x),p),(a,b))
  have hd : z.1.2.1.length = n := card_eq_length_dom hw
  apply ColoredPartition.isAlphaPartition_of_kernel_rel
    (Y.designPart ∅) (decColPartition n (designReadPlain z)) (Equiv.refl _) _ _
    (KAryPartStruct.designPart_isAlphaPartition_of_noDominant hα Y hno)
  · intro u v
    rw [designReadPlain_color_of_length hd,designReadPlain_color_of_length hd]
    exact (Y.natVColor_eq_iff u v).trans (by
      dsimp only [z,Equiv.refl_apply]
      rw [restrVColorAt_spec hk hl x u,restrVColorAt_spec hk hl x v])
  · intro u v
    rw [designReadPlain_rel_of_length hd]
    change (Y.vcolor u = Y.vcolor v ∧ ∀ A ∈ (∅ : Set (Set (Fin n))),_) ↔ _
    simp only [Set.mem_empty_iff_false,IsEmpty.forall_iff,implies_true,and_true]
    dsimp only [z,Equiv.refl_apply]
    rw [restrVColorAt_spec hk hl x u,restrVColorAt_spec hk hl x v]

end Algo
