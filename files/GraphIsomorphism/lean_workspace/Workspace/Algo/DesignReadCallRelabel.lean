import Workspace.Algo.DesignReadCallCoordinates
import Workspace.Algo.DesignReadWitness

/-! Section 9.7 numbers blocks by their positions in the stored list.
Relabeling old names preserves those positions and every computed output.
This statement follows the full Design Lemma scan, including its guards.
-/
namespace Algo
open Babai RAM

section
variable {r : RawUpccCase} {π : RawPerm} (hw : r.WF)
    (hπ : RawPerm.WF r.1.1.length π) (hne : 0 < r.2.1.length)
local notation "r'" => UpccCase.relabelInput π r
include hw hπ hne

/-- The relation table is unchanged in compact block coordinates. -/
theorem designCallRelations_relabel : designCallRelations r' = designCallRelations r := by
  unfold designCallRelations designRelations designCallInput
  rw [designLabels_relabel hw hπ hne]
  have hr : r'.2.2.length = r.2.2.length := by simp [UpccCase.relabelInput]
  have hl : r'.2.1.length = r.2.1.length := by simp [UpccCase.relabelInput]
  rw [hr,designAggTable_witness (designCallWitness_relabel_length hw hπ hne) hl]

/-- The two changed lists are only size witnesses. The compact domain and
relation table retain exactly the same contents. -/
theorem designCallGIn_relabel : designCallGIn r' =
    (((designCallWitness r',r'.2.1,List.range r.2.2.length),designCallRelations r),(3,4)) := by
  unfold designCallGIn
  rw [designCallRelations_relabel hw hπ hne]
  simp only [UpccCase.relabelInput,length_permList]

/-- Every returning tuple and read-off stays identical in compact coordinates. -/
theorem designCallReadFamily_relabel : designCallReadFamily r' = designCallReadFamily r := by
  unfold designCallReadFamily
  rw [designCallGIn_relabel hw hπ hne]
  exact designAmbientReadFamily_witness (designCallWitness_relabel_length hw hπ hne)
    (by simp [UpccCase.relabelInput]) _ _ _

end

section Admissible
variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {s : Set Ω}
    {X : BlkDesignObj s} {name₁ : ↥X.Pt₁ → ℕ} {name₂ : ↥X.blocks → ℕ}
    {r : RawUpccCase} (h : DesignNames X name₁ name₂ r)
    (e₁ : ↥X.Pt₁ ≃ Fin r.2.1.length)
include e₁

/-- Nonemptiness needed by the first-row degree computation follows from
an admissible block-design input. -/
theorem designCall_left_pos : 0 < r.2.1.length := by
  rw [designLeft_length e₁]
  exact (Set.ncard_pos (Set.toFinite _)).2 X.part₁_nonempty

/-- The actual Section 9.7 family is covariant without a separate size premise. -/
theorem designCallReadFamily_relabel_admissible (hw : r.WF) {π : RawPerm}
    (hπ : RawPerm.WF r.1.1.length π) :
    designCallReadFamily (UpccCase.relabelInput π r) = designCallReadFamily r :=
  designCallReadFamily_relabel hw hπ (designCall_left_pos e₁)

end Admissible
end Algo
