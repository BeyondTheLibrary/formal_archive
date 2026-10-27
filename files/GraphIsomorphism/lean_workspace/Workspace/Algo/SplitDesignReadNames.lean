import Workspace.Algo.SplitDesignReadHint

/-! Stored Design Lemma outcomes retain distinct in-range vertex names.
These facts supply the named selector without assuming an output numbering. -/
namespace Algo
open Babai RAM

theorem designReadFirst_exit_nodup (z : DIn) (hnd : z.1.2.1.Nodup) :
    (designReadFirst (designReadExit z)).Nodup := by
  unfold designReadExit
  split
  · exact rawEquipFirst_nodup _
  · split
    · exact hnd.filter _
    · exact rawEquipFirst_nodup _

theorem designReadFirst_exit_lt (z : DIn)
    (hrange : ∀ i ∈ z.1.2.1, i < z.1.2.1.length) :
    ∀ i ∈ designReadFirst (designReadExit z), i < z.1.2.1.length := by
  unfold designReadExit
  split
  · intro i hi
    have hh := rawEquipFirst_lt hi
    simpa [designReadPart,designReadColors] using hh
  · split
    · intro i hi
      exact hrange i (List.mem_of_mem_filter hi)
    · intro i hi
      have hh := rawEquipFirst_lt hi
      simpa [designReadPlain,designReadColors] using hh

theorem designCallReadFirst_names (r : RawUpccCase) {xs : List ℕ} {o : RawDesignReadOut}
    (ho : (xs,o) ∈ designCallReadFamily r) :
    (designReadFirst o).Nodup ∧ ∀ i ∈ designReadFirst o, i < r.2.2.length := by
  have hout := (designCallReadFamily_mem r xs o).1 ho |>.2
  rw [hout]
  let z := ambientDesignAt 3 (designCallGIn r) xs
  have hdom : z.1.2.1 = List.range r.2.2.length := by
    simp [z,ambientDesignAt,designCallGIn]
  refine ⟨designReadFirst_exit_nodup z (by rw [hdom]; exact List.nodup_range),?_⟩
  have hr : ∀ i ∈ z.1.2.1, i < z.1.2.1.length := by
    rw [hdom]
    simpa using (fun i (hi : i ∈ List.range r.2.2.length) => List.mem_range.1 hi)
  have hh := designReadFirst_exit_lt z hr
  simpa only [hdom,List.length_range] using hh

end Algo
