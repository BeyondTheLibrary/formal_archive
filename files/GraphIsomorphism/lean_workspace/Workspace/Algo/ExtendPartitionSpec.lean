import Workspace.Algo.ExtendPartitionRaw

/-! The raw extension has exactly the colors and blocks of the paper's
`extendPartition`. This transfers its size and admissibility proof to the
stored answer, under the original parent and local naming lists. -/
namespace Algo
open Babai RAM

section
variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {V W : Set Ω} {vl wl : List ℕ} {p : RawColPart}
    (P : ColoredPartition ↥W ℕ) (name : Ω → ℕ)
    (eV : ↥V ≃ Fin vl.length) (hv : ∀ x, vl[(eV x).val]'(eV x).isLt = name x.val)
    (eW : ↥W ≃ Fin wl.length) (hw : ∀ x, wl[(eW x).val]'(eW x).isLt = name x.val)
    (hnd : wl.Nodup) (hmem : ∀ x : ↥V, name x.val ∈ wl ↔ x.val ∈ W)
    (hc : ∀ x, labAt p.1 (eW x) = P.color x)
    (hp : ∀ x y, cellOf p (eW x) = cellOf p (eW y) ↔ P.part x y)

include hw hnd in
theorem rawExtendPartition_localIndex (x : ↥W) :
    rawLetterIndex (wl,name x.val) = (eW x).val := by
  rw [← hw x,sbipLetterIndex_get hnd]

include hv hw hnd hmem hc in
open scoped Classical in
theorem rawExtendPartition_color (x : ↥V) :
    (decColPartition vl.length (rawExtendPartition ((vl,wl),p))).color (eV x) =
      (extendPartition V W P).color x := by
  change labAt (rawExtendLabels ((vl,wl),p.1)) (eV x) = _
  rw [rawExtendLabels_get,hv]
  by_cases hx : x.val ∈ W
  · have hm := (hmem x).2 hx
    rw [rawExtendLabel,if_pos (by simpa using hm),
      rawExtendPartition_localIndex name eW hw hnd ⟨x.val,hx⟩,
      hc,extendPartition.color_of_mem P hx]
  · rw [rawExtendLabel_of_notMem _ (fun hh => hx ((hmem x).1 hh)),
      extendPartition.color_of_notMem P hx]

include hv hw hnd hmem hp in
open scoped Classical in
theorem rawExtendPartition_part (x y : ↥V) :
    (decColPartition vl.length (rawExtendPartition ((vl,wl),p))).part (eV x) (eV y) ↔
      (extendPartition V W P).part x y := by
  rw [rawExtendPartition_rel,hv,hv]
  by_cases hx : x.val ∈ W <;> by_cases hy : y.val ∈ W
  · rw [rawExtendPartition_localIndex name eW hw hnd ⟨x.val,hx⟩,
      rawExtendPartition_localIndex name eW hw hnd ⟨y.val,hy⟩,hp]
    change (_ ↔ _) ∧ (_ → P.part _ _) ↔
      (x.val ∈ W ↔ y.val ∈ W) ∧ ∀ (_ : x.val ∈ W) (_ : y.val ∈ W), P.part _ _
    simp [hmem,hx,hy]
  · change _ ↔ (x.val ∈ W ↔ y.val ∈ W) ∧ _
    simp [hmem,hx,hy]
  · change _ ↔ (x.val ∈ W ↔ y.val ∈ W) ∧ _
    simp [hmem,hx,hy]
  · change _ ↔ (x.val ∈ W ↔ y.val ∈ W) ∧ _
    simp [hmem,hx,hy]

include hv hw hnd hmem hc hp in
open scoped Classical in
theorem rawExtendPartition_valid [Fintype ↥V] {α : ℝ}
    (hP : (extendPartition V W P).IsAlphaPartition α) :
    (decColPartition vl.length (rawExtendPartition ((vl,wl),p))).IsAlphaPartition α := by
  apply ColoredPartition.isAlphaPartition_of_kernel_rel (extendPartition V W P)
    (decColPartition vl.length (rawExtendPartition ((vl,wl),p))) eV
  · intro x y
    rw [rawExtendPartition_color P name eV hv eW hw hnd hmem hc,
      rawExtendPartition_color P name eV hv eW hw hnd hmem hc]
  · intro x y
    exact (rawExtendPartition_part P name eV hv eW hw hnd hmem hp x y).symm
  · exact hP

end
end Algo
