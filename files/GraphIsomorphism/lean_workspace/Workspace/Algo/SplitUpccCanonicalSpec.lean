import Workspace.Algo.SplitUpccSpec

/-! The computed UPCC version is exactly the paper's canonical object.
The strict large-cell test has at most one passing color, so the stored
order cannot change the choice. The middle colors already use the same
least-pair rule in the raw and mathematical constructions. -/
namespace Algo
open Babai RAM
open scoped Classical

namespace Upcc

theorem versionF_rep_exact {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    (X : Pt (UPCCs Ω)) {n a b : ℕ} {p : RawConfig}
    (h : RawWL.WF n 2 p) (e : ↥X.car ≃ Fin n) (he : UpccNames e p X.obj.1)
    (hb : 0 < b) (hβ : (2 : ℝ) / 3 ≤ (a : ℝ) / b) (x : ↥X.car) :
    UpccOutcomeRep e (versionF ((p,(a,b)),e x))
      ⟨(upccOutcome ((a : ℝ)/b) X.obj.1 x).1.1,
        (upccOutcome ((a : ℝ)/b) X.obj.1 x).2⟩ := by
  have hlen : (upccCellsRaw (p,e x)).length = n := by
    simp [card_eq_length_dom h]
  cases hk : upccBigColor ((p,(a,b)),e x) with
  | none =>
    have hnil : upccBigColors ((p,(a,b)),e x) = [] := by
      simpa [upccBigColor] using hk
    have hsmall := (upccCellSmall_spec h e he hb x).1
      (show upccCellSmall ((p,(a,b)),e x) = true by simp [upccCellSmall,hnil])
    have hn : ¬ ∃ k : ℕ,(a : ℝ)/b * X.car.ncard < (cellOf X.obj.1 x k).ncard := by
      rintro ⟨k,hk⟩
      exact (not_lt_of_ge (hsmall k)) hk
    rw [upccOutcome,dif_neg hn]
    simp only [versionF,hk,Option.elim_none,UpccOutcomeRep]
    exact ⟨hlen,hlen,Equiv.refl _,fun _ => rfl,
      upccCellsRaw_spec h e he x,upccCellsRaw_blocks h e he x⟩
  | some k =>
    have hbig := upccBigColor_spec h e he hb x hk
    have hex : ∃ k : ℕ,(a : ℝ)/b * X.car.ncard < (cellOf X.obj.1 x k).ncard := ⟨k,hbig⟩
    have hidx := bigCellIdx_eq (by linarith : (1 : ℝ)/2 ≤ (a : ℝ)/b) hbig
    have hcond := upccBipCond_of_big X.obj.2 hβ hbig
    rw [upccOutcome,dif_pos hex,hidx,upccBipOutcome,dif_pos hcond]
    have hik : midI X.obj.1 x k ≠ k := (bipCase X.obj.2 hβ hbig).1
    have hij := upccMidIJRaw_spec h e he x k
    simp only [versionF,hk,Option.elim_some,UpccOutcomeRep,upccBipBranch,hij]
    refine ⟨hlen,hlen,bipCarrier_subset _ _ _ _,upccBipRaw_rep h e he x k _ _ hik,?_⟩
    rw [upccCellRaw_size h e he,card_eq_length_dom h,bipAlpha,upccNaming_card e]
    push_cast
    ring

end Upcc
end Algo
