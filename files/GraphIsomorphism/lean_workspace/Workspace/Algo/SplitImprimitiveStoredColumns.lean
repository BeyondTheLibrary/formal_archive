import Workspace.Algo.SplitImprimitiveFamily

/-! Every old block name used by an actual Section 9.6 graph belongs to the
stored second part. This holds on arbitrary raw inputs. A restriction uses
singletons from a selected component; contraction uses all components.
-/
namespace Algo
open Babai RAM

/-- Every selected graph keeps precisely the old first-part list. -/
theorem impStep2Graphs_left {r : RawUpccCase} {q : RawImpGraph}
    (hq : q ∈ impStep2Graphs r) : q.1 = r.2.1 := by
  unfold impStep2Graphs at hq
  split at hq
  · simpa only [List.mem_singleton] using congrArg (fun q : RawImpGraph => q.1)
      (List.mem_singleton.mp hq)
  · obtain ⟨g,_,rfl⟩ := List.mem_map.mp hq
    rfl

/-- No contraction or restriction reads a block outside the input dictionary. -/
theorem impStep2Graphs_column_names {r : RawUpccCase} {q : RawImpGraph}
    (hq : q ∈ impStep2Graphs r) {g : List ℕ} (hg : g ∈ q.2.1) {a : ℕ} (ha : a ∈ g) :
    a ∈ r.2.2 := by
  unfold impStep2Graphs at hq
  split at hq
  · have he := List.mem_singleton.mp hq
    subst q
    obtain ⟨i,_,hig⟩ := (impGroups_mem r g).mp hg
    exact impGroup_mem_right (hig.symm ▸ ha)
  · obtain ⟨l,hl,rfl⟩ := List.mem_map.mp hq
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hg
    have he := List.mem_singleton.mp ha
    subst a
    obtain ⟨i,_,hil⟩ := (impGroups_mem r l).mp (List.mem_filter.mp hl).1
    exact impGroup_mem_right (hil.symm ▸ hb)

/-- The outer partition-or-graph routine returns precisely these selected graphs. -/
theorem impCase_graph_mem {r : RawUpccCase} {q : RawImpGraph} {lab : RawLab}
    (hq : (lab,some q) ∈ impCase r) : lab = [] ∧ q ∈ impStep2Graphs r := by
  unfold impCase at hq
  split at hq
  · obtain ⟨b,_,he⟩ := List.mem_map.mp hq
    have hh := congrArg Prod.snd he
    cases hh
  · obtain ⟨g,hg,he⟩ := List.mem_map.mp hq
    have hl := congrArg Prod.fst he
    have hh := Option.some.inj (congrArg Prod.snd he)
    exact ⟨hl.symm,hh ▸ hg⟩

end Algo
