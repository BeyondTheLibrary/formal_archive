import Workspace.Algo.SplitBipCaseOutcomeNames
import Workspace.Algo.SplitPartitionTransport

/-! The restored partition is exactly the paper's extension by the one
complement block. The local decoding hypotheses are color and block reads;
the case-specific proofs below will supply them from the actual returns.
-/
namespace Algo
open Babai RAM
open scoped Classical

section
variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {V W : Set Ω}
    (P : ColoredPartition ↥W ℕ) (z : RawSbipCaseContext) (q : RawColPart)
    (point : Ω → ℕ) (name : ↥W → ℕ)
    (eV : ↥V ≃ Fin z.1.length) (heV : ∀ x,z.1[(eV x).val] = point x.val)
    (eW : ↥W ≃ Fin z.2.2.length) (heW : ∀ x,z.2.2[(eW x).val] = name x)
    (hrow : ∀ x,sbipDictPoint (z.2.1,name x) = point x.val)
    (hcover : ∀ a,a ∈ z.2.2 ↔ ∃ x,name x = a)
    (hl : z.2.2.Nodup) (hWV : W ⊆ V) (hinj : Set.InjOn point V)
    (hc : ∀ x,labAt q.1 (eW x) = P.color x)
    (hp : ∀ x y,cellOf q (eW x) = cellOf q (eW y) ↔ P.part x y)

noncomputable def sbipCasePointEquiv : ↥W ≃ Fin (sbipCasePointList z).length :=
  eW.trans (finCongr (by simp [sbipCasePointList,sbipDictPoints]))

include heW hrow in
theorem sbipCasePointEquiv_get (x : ↥W) :
    (sbipCasePointList z)[(sbipCasePointEquiv z eW x).val] = point x.val :=
  sbipCasePointList_get point name z.2.1 z.2.2 hrow z.1 eW heW x

include heV heW hrow hcover hl hWV hinj hc hp

theorem sbipCasePartition_decode :
    (decColPartition z.1.length (sbipCasePartition (z,q))).pushforward eV.symm =
      extendPartition V W P := by
  have hnd := sbipCasePointList_nodup point name z.2.1 z.2.2 hrow hcover z.1 hl
    (hinj.mono hWV)
  have hmem := sbipCasePointList_parent_mem point name z.2.1 z.2.2 hrow hcover hWV hinj z.1
  have he := sbipCasePointEquiv_get z point name eW heW hrow
  apply ColoredPartition.ext
  · funext x
    exact rawExtendPartition_color P point eV heV (sbipCasePointEquiv z eW) he hnd hmem hc x
  · apply Setoid.ext
    intro x y
    exact rawExtendPartition_part P point eV heV (sbipCasePointEquiv z eW) he hnd hmem hp x y

theorem sbipCasePartition_valid (iW : Fintype ↥W) (iV : Fintype ↥V)
    {α β : ℝ} (hα : α ≤ 1) (hβ : 1/2 ≤ β)
    (hbalance : α * (W.ncard : ℝ) = β * (V.ncard : ℝ))
    (hP : @ColoredPartition.IsAlphaPartition _ _ P iW α) :
    (decColPartition z.1.length (sbipCasePartition (z,q))).IsAlphaPartition β := by
  letI := iV
  have hnd := sbipCasePointList_nodup point name z.2.1 z.2.2 hrow hcover z.1 hl
    (hinj.mono hWV)
  have hmem := sbipCasePointList_parent_mem point name z.2.1 z.2.2 hrow hcover hWV hinj z.1
  exact rawExtendPartition_valid P point eV heV (sbipCasePointEquiv z eW)
    (sbipCasePointEquiv_get z point name eW heW hrow) hnd hmem hc hp
    (extendPartition.isAlphaPartition hWV iW iV P hα hβ hbalance hP)

omit hc hp in
/-- The actual local decoder suffices for the extension step. Its bounds
can therefore be supplied directly by the three checked case algorithms. -/
theorem sbipCasePartition_valid_of_decode {α β : ℝ} (hα : α ≤ 1) (hβ : 1/2 ≤ β)
    (hbalance : α * (W.ncard : ℝ) = β * (V.ncard : ℝ))
    (hq : (decColPartition z.2.2.length q).IsAlphaPartition α) :
    (decColPartition z.1.length (sbipCasePartition (z,q))).IsAlphaPartition β := by
  letI : Fintype ↥W := Fintype.ofFinite _
  letI : Fintype ↥V := Fintype.ofFinite _
  let P := (decColPartition z.2.2.length q).pushforward eW.symm
  have hP : P.IsAlphaPartition α := by
    apply ColoredPartition.isAlphaPartition_of_kernel_rel _ P eW.symm ?_ ?_ hq
    · intro x y
      change labAt q.1 x = labAt q.1 y ↔
        labAt q.1 (eW (eW.symm x)) = labAt q.1 (eW (eW.symm y))
      simp
    · intro x y
      change cellOf q x = cellOf q y ↔
        cellOf q (eW (eW.symm x)) = cellOf q (eW (eW.symm y))
      simp
  exact sbipCasePartition_valid P z q point name eV heV eW heW hrow hcover hl hWV hinj
    (fun _ => rfl) (fun _ _ => Iff.rfl) inferInstance inferInstance hα hβ hbalance hP

end
end Algo
