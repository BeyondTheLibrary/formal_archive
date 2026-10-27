import Workspace.Algo.SplitBipGraphEarlyRaw

/-! Decode a positional partition on the parent first part. Equality of
the actual colors and block relation identifies the exact paper outcome;
the same equations transfer its alpha-partition bound to the RAM decoder.
-/
namespace Algo
open Babai RAM
open scoped Classical

section
variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {s : Set Ω}
    (G : VColBipBlk ↥s ℕ) {n : ℕ} (e : ↥G.V₁ ≃ Fin n)

noncomputable def sbipGraphDecodePartition (q : RawColPart) :
    ColoredPartition ↥(Subtype.val '' G.V₁) ℕ :=
  (decColPartition n q).pushforward ((splitImageEquiv G.V₁).trans e).symm

variable (P : ColoredPartition ↥(Subtype.val '' G.V₁) ℕ) (q : RawColPart)
    (hc : ∀ x : ↥G.V₁,labAt q.1 (e x) = P.color (mkPt x.property))

include hc in
theorem sbipGraphCell_spec
    (hb : ∀ x y : ↥G.V₁,LabRel q.2 (e x) (e y) ↔
      P.part (mkPt x.property) (mkPt y.property)) (x y : ↥G.V₁) :
    cellOf q (e x) = cellOf q (e y) ↔ P.part (mkPt x.property) (mkPt y.property) := by
  change (labAt q.1 (e x),labAt q.2 (e x)) = (labAt q.1 (e y),labAt q.2 (e y)) ↔ _
  rw [Prod.mk.injEq]
  constructor
  · intro h
    exact (hb x y).1 h.2
  · intro h
    refine ⟨?_,(hb x y).2 h⟩
    rw [hc,hc]
    exact P.part_le_color h

variable
    (hp : ∀ x y : ↥G.V₁,cellOf q (e x) = cellOf q (e y) ↔
      P.part (mkPt x.property) (mkPt y.property))
include hc hp

theorem sbipGraphDecodePartition_eq : sbipGraphDecodePartition G e q = P := by
  apply ColoredPartition.ext
  · funext x
    exact hc (wPt x)
  · apply Setoid.ext
    intro x y
    exact hp (wPt x) (wPt y)

theorem sbipGraphDecodedPartition_valid {α : ℝ}
    (iF : Fintype ↥(Subtype.val '' G.V₁))
    (hv : @ColoredPartition.IsAlphaPartition _ _ P iF α) :
    (decColPartition n q).IsAlphaPartition α := by
  letI := iF
  apply ColoredPartition.isAlphaPartition_of_kernel_rel P _
    ((splitImageEquiv G.V₁).trans e) ?_ ?_ hv
  · intro x y
    change P.color x = P.color y ↔ labAt q.1 (e (wPt x)) = labAt q.1 (e (wPt y))
    rw [hc,hc]
    rfl
  · intro x y
    exact (hp (wPt x) (wPt y)).symm

end
end Algo
