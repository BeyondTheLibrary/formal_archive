import Workspace.Algo.SplitBipTurnInvariant

/-! A turn returns partitions indexed by its current first list and
Johnson schemes indexed by persistent original names. This single
semantic decoder respects that distinction.
-/
namespace Algo
open Babai RAM
open scoped Classical

noncomputable def sbipDecodeNamedPartition {m : ℕ} (L : List ℕ) (hn : L.Nodup)
    (hb : ∀ a ∈ L,a < m) (q : RawColPart) : Pt (SplitOutcomes (Fin m)) :=
  ⟨winSet m L,Sum.inl ((decColPartition L.length q).pushforward (winEquiv m L hn hb))⟩

noncomputable def sbipDecodeNamed (m : ℕ) (L : List ℕ) (o : RawAlignOutcome) :
    Option (Pt (SplitOutcomes (Fin m))) :=
  match o with
  | (some q,none) => if h : L.Nodup ∧ ∀ a ∈ L,a < m then
      some (sbipDecodeNamedPartition L h.1 h.2 q) else none
  | _ => decAlignOutcome m o

theorem sbipDecodeNamed_partition {m : ℕ} (L : List ℕ) (hn : L.Nodup)
    (hb : ∀ a ∈ L,a < m) (q : RawColPart) :
    sbipDecodeNamed m L (rawAlignPartition q) = some (sbipDecodeNamedPartition L hn hb q) := by
  simp only [sbipDecodeNamed,rawAlignPartition,dif_pos (And.intro hn hb)]

theorem sbipDecodeNamed_johnson {m ms ts : ℕ} (L : List ℕ) (J : RawJohnson)
    (hJ : J.WF m ms ts) :
    sbipDecodeNamed m L (rawAlignJohnson J) = some (decAlignJohnson J hJ) :=
  decAlignOutcome_johnson J hJ

theorem sbipDecodeNamedPartition_valid {m : ℕ} (L : List ℕ) (hn : L.Nodup)
    (hb : ∀ a ∈ L,a < m) (q : RawColPart) {α : ℝ}
    (hq : (decColPartition L.length q).IsAlphaPartition α) :
    IsSplitOutcome α (winSet m L) (sbipDecodeNamedPartition L hn hb q) := by
  refine ⟨rfl,?_⟩
  letI : Fintype ↥(winSet m L) := Fintype.ofFinite _
  apply ColoredPartition.isAlphaPartition_of_kernel_rel (decColPartition L.length q)
    ((decColPartition L.length q).pushforward (winEquiv m L hn hb)) (winEquiv m L hn hb)
  · intro x y
    simp only [ColoredPartition.pushforward,Equiv.symm_apply_apply]
  · intro x y
    change cellOf q x = cellOf q y ↔
      cellOf q ((winEquiv m L hn hb).symm ((winEquiv m L hn hb) x)) =
        cellOf q ((winEquiv m L hn hb).symm ((winEquiv m L hn hb) y))
    simp
  · exact hq

def SbipReturnGood {m : ℕ} (I : RawSbipNode) (X : Pt (BipBlockInputs (Fin m)))
    (o : RawAlignOutcome) : Prop :=
  ∃ Z,sbipDecodeNamed m I.1.2.1.1.1.1 o = some Z ∧
    IsSplitOutcome (BipBlockInputs.alpha X) (BipBlockInputs.V₁ X) Z

def SbipAnswersGood (m : ℕ) (I : RawSbipNode) (A : RawSbipAnswers) : Prop :=
  ∀ X : Pt (BipBlockInputs (Fin m)),SbipNodeRep m I X → ∀ o ∈ A,SbipReturnGood I X o

namespace SbipNodeRep
variable {m : ℕ} {I : RawSbipNode} {X : Pt (BipBlockInputs (Fin m))}
    (h : SbipNodeRep m I X)
include h

theorem partition_good (q : RawColPart)
    (hq : (decColPartition I.1.2.1.1.1.1.length q).IsAlphaPartition (BipBlockInputs.alpha X)) :
    SbipReturnGood I X (rawAlignPartition q) := by
  refine ⟨_,sbipDecodeNamed_partition _ h.left_nodup h.point_lt q,?_⟩
  rw [← h.point_set]
  exact sbipDecodeNamedPartition_valid _ h.left_nodup h.point_lt q hq

theorem johnson_good {ms ts : ℕ} (J : RawJohnson) (hJ : J.WF m ms ts)
    (hgood : IsSplitOutcome (BipBlockInputs.alpha X) (winSet m I.1.2.1.1.1.1)
      (decAlignJohnson J hJ)) : SbipReturnGood I X (rawAlignJohnson J) :=
  ⟨_,sbipDecodeNamed_johnson _ J hJ,h.point_set ▸ hgood⟩
end SbipNodeRep
end Algo
