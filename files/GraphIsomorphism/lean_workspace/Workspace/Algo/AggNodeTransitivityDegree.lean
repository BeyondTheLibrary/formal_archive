import Workspace.Algo.AggNodeTransitivityTest

/-! # Computing the degree of transitivity

The successful tuple lengths form an initial segment. We test the domain
length plus one possible lengths and count that segment. Each test uses group
orders, so no list of tuples is constructed. This implements Definition 2.2.3
and the choice of `d` in version 2.5, Section 13.2, Case 2b.
-/
namespace Algo
open RAM RAM.Targets Babai Equiv

def aggnDegtrans (p : List ℕ × RawGens) : ℕ :=
  ((List.range (p.1.length + 1)).filter (fun d => aggnTransitivityTest (p, d))).length - 1

theorem aggnPolyFun_degtrans : PolyFun aggnDegtrans := by
  have hr : PolyFun (fun p : List ℕ × RawGens => List.range (p.1.length + 1)) :=
    (((polyFun_fst.comp polyFun_rangeLength).pair
      ((polyFun_fst.comp polyFun_length).comp polyFun_singleton)).comp polyFun_append).of_eq
      (fun _ => List.range_succ.symm)
  exact ((((polyFun_id.pair hr).comp (PolyFun.filterParam aggnPolyFun_transitivityTest)).comp
    polyFun_length).pair (polyFun_const 1)).comp polyFun_sub

theorem aggnDegtrans_le (p : List ℕ × RawGens) : aggnDegtrans p ≤ p.1.length := by
  have h := List.length_filter_le (fun d => aggnTransitivityTest (p, d))
    (List.range (p.1.length + 1))
  simp only [List.length_range] at h
  unfold aggnDegtrans
  omega

theorem aggnDegtrans_spec {m : ℕ} {dom : List ℕ} {gs : RawGens}
    (hd : dom.length = m) (hw : RawGens.WF m gs) :
    aggnDegtrans (dom, gs) = degtrans (decGroup m gs) := by
  let G := decGroup m gs
  have hle : degtrans G ≤ m := by
    simpa only [Fintype.card_fin] using le_card_of_multiplyTransitive (degtrans_spec G).1
  have ht (d : ℕ) : aggnTransitivityTest ((dom, gs), d) = true ↔ d ≤ degtrans G := by
    rw [aggnTransitivityTest_spec hd hw]
    exact ⟨fun h => le_csSup (bddAbove_multiplyTransitive G) h,
      fun h => (degtrans_spec G).1.mono h⟩
  have hp : ((List.range (dom.length + 1)).filter
      (fun d => aggnTransitivityTest ((dom, gs), d))).Perm (List.range (degtrans G + 1)) := by
    apply List.perm_of_nodup_nodup_toFinset_eq
    · exact List.nodup_range.filter _
    · exact List.nodup_range
    · ext d
      simp only [List.mem_toFinset, List.mem_filter, List.mem_range, ht, hd]
      omega
  have hlen := hp.length_eq
  simp only [List.length_range] at hlen
  unfold aggnDegtrans
  rw [hlen]
  exact Nat.add_sub_cancel (degtrans G) 1

end Algo
