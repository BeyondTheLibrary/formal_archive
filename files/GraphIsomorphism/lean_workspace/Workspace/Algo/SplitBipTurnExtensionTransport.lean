import Workspace.Algo.SplitBipTurnFamily

/-! Reindexing persistent point names preserves the positional partition
labels. Thus the per-parent complement extension commutes with every
injective naming of the two current lists, independently of their order.
-/
namespace Algo
open Babai RAM

section
variable (f : ℕ → ℕ) (V W : List ℕ) (hW : W.Nodup)
    (hi : Set.InjOn f {a | a ∈ V ∨ a ∈ W})
include hW hi

theorem rawExtendLabel_map_names (P : RawLab) (a : ℕ) (ha : a ∈ V) :
    rawExtendLabel ((W.map f,P),f a) = rawExtendLabel ((W,P),a) := by
  have hn : (W.map f).Nodup := (List.nodup_map_iff_inj_on hW).2
    (fun a ha b hb he => hi (Or.inr ha) (Or.inr hb) he)
  by_cases hw : a ∈ W
  · obtain ⟨j,hj,hja⟩ := List.getElem_of_mem hw
    have hj' : j < (W.map f).length := by simpa using hj
    have he : (W.map f)[j] = f a := by simp only [List.getElem_map,hja]
    rw [← he,rawExtendLabel_of_mem hn P ⟨j,hj'⟩,← hja,
      rawExtendLabel_of_mem hW P ⟨j,hj⟩]
  · have hw' : f a ∉ W.map f := by
      rintro hh
      obtain ⟨b,hb,he⟩ := List.mem_map.1 hh
      exact hw ((hi (Or.inr hb) (Or.inl ha) he) ▸ hb)
    rw [rawExtendLabel_of_notMem P hw',rawExtendLabel_of_notMem P hw]

theorem rawExtendLabels_map_names (P : RawLab) :
    rawExtendLabels ((V.map f,W.map f),P) = rawExtendLabels ((V,W),P) := by
  simp only [rawExtendLabels,List.map_map]
  exact List.map_congr_left (fun a ha => rawExtendLabel_map_names f V W hW hi P a ha)

/-- Both the colors and block labels are unchanged at their list positions. -/
theorem rawExtendPartition_map_names (P : RawColPart) :
    rawExtendPartition ((V.map f,W.map f),P) = rawExtendPartition ((V,W),P) := by
  exact Prod.ext (rawExtendLabels_map_names f V W hW hi P.1)
    (rawExtendLabels_map_names f V W hW hi P.2)

end
end Algo
