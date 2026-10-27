import Workspace.Algo.SplitBipIndex

/-! Closing the gaps in binary color names bounds every new color by the
number of pairs. Thus the actual Design Lemma UPCC table is a valid input
to the UPCC RAM routine without another refinement step. -/
namespace Algo
open Babai RAM

theorem sbipRecode_wf {n : ℕ} {p : RawConfig} (h : NamedBinaryWF n p) :
    RawWL.WF n 2 (sbipRecode p) := by
  have hkeys : (sbipRecode p).2.map Prod.fst = tuplesOf p.1 2 := by
    simp [sbipRecode,sbipRecodeRow,List.map_map,Function.comp_def]
  refine ⟨h.domNodup,h.domMem,?_,?_,?_⟩
  · rw [hkeys]
    exact nodup_tuplesOf h.domNodup 2
  · intro t
    rw [hkeys,mem_tuplesOf]
    simp only [h.domMem]
  · intro q hq
    obtain ⟨t,ht,rfl⟩ := List.mem_map.1 hq
    obtain ⟨hlen,hmem⟩ := (mem_tuplesOf p.1 2 t).1 ht
    obtain ⟨u,v,rfl⟩ : ∃ u v,t = [u,v] := by
      cases t with
      | nil => simp at hlen
      | cons u t =>
        cases t with
        | nil => simp at hlen
        | cons v t =>
          have hz : t = [] := List.length_eq_zero_iff.1 (by simpa using hlen)
          subst t
          exact ⟨u,v,rfl⟩
    have hu : u ∈ p.1 := hmem u (by simp)
    have hv : v ∈ p.1 := hmem v (by simp)
    have hc : [binColor (p,(u,v))] ∈ sbipCodes p := by
      rw [sbipCodes,mem_dedupG_nil]
      exact List.mem_map.2 ⟨(u,v),List.mem_product.2 ⟨hu,hv⟩,rfl⟩
    have hb : (sbipCodes p).length ≤ p.1.length^2 := by
      have hh := length_dedupG_le ((p.1.product p.1).map (fun q => [binColor (p,q)]))
      simpa [sbipCodes,List.product,List.length_flatMap,List.map_map,pow_two] using hh
    have hr := (rankIn_lt_length hc).trans_le hb
    simpa only [sbipRecodeRow,sbipRecode,List.length_map,length_tuplesOf] using hr

end Algo
