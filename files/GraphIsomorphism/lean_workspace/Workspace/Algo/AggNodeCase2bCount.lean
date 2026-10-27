import Workspace.Algo.AggNodeCase2bFamily
import Mathlib.Data.List.Sublists

/-! # The paper's individualization and constituent choice counts -/
namespace Algo
open RAM RAM.Targets Babai Equiv MulAction
open scoped Classical

theorem aggnTuplesUpTo_nodup {C : List ℕ} (hC : C.Nodup) (k : ℕ) :
    (aggnTuplesUpTo k C).Nodup := by
  induction k with
  | zero => exact nodup_tuplesOf hC 0
  | succ k ih =>
    rw [aggnTuplesUpTo,List.nodup_append]
    refine ⟨ih,nodup_tuplesOf hC (k+1),?_⟩
    intro row hr row' ht he
    subst row'
    have h1 := (aggnTuplesUpTo_mem k C row).mp hr
    have h2 := (mem_tuplesOf C (k+1) row).mp ht
    omega

theorem aggnSmallSets_nodup {dom C : List ℕ} (hC : C.Nodup) (d : ℕ) :
    (aggnSmallSets (dom,C,d)).Nodup := (aggnTuplesUpTo_nodup hC 4).filter _

/-- Increasing names are precisely the fixed-length sublists of the large orbit. -/
theorem aggnSmallSets_perm {dom C : List ℕ} (hC : C.Pairwise (· < ·))
    (hlt : ∀ u ∈ C,u < dom.length) {d : ℕ} (hd : d ≤ 4) :
    (aggnSmallSets (dom,C,d)).Perm (C.sublistsLen d) := by
  apply List.perm_of_nodup_nodup_toFinset_eq
    (aggnSmallSets_nodup hC.nodup d) (List.nodup_sublistsLen d hC.nodup)
  ext S
  simp only [List.mem_toFinset,aggnSmallSets_mem hd,List.mem_sublistsLen]
  constructor
  · rintro ⟨hlen,hsub,he⟩
    refine ⟨?_,hlen⟩
    have hsort : S.Pairwise (· < ·) := by rw [he]; exact List.pairwise_lt_range.filter _
    have he' : S = C.filter (fun u => decide (u ∈ S)) := by
      apply hsort.eq_of_mem_iff (hC.filter _)
      intro u
      simp only [List.mem_filter,decide_eq_true_eq]
      exact ⟨fun hu => ⟨hsub u hu,hu⟩,And.right⟩
    rw [he']
    exact List.filter_sublist
  · rintro ⟨hsub,hlen⟩
    refine ⟨hlen,hsub.subset,?_⟩
    apply (hC.sublist hsub).eq_of_mem_iff (List.pairwise_lt_range.filter _)
    intro u
    simp only [aggNormalizeRow,List.mem_filter,List.mem_range,decide_eq_true_eq]
    exact ⟨fun hu => ⟨hlt u (hsub.subset hu),hu⟩,And.right⟩

theorem aggnSmallSets_length {dom C : List ℕ} (hC : C.Pairwise (· < ·))
    (hlt : ∀ u ∈ C,u < dom.length) {d : ℕ} (hd : d ≤ 4) :
    (aggnSmallSets (dom,C,d)).length = C.length.choose d := by
  rw [(aggnSmallSets_perm hC hlt hd).length_eq,List.length_sublistsLen]

/-- All subset choices times at most `|C|-1` orbital choices, as in Case 2b. -/
theorem aggnCase2bFamily_length {m : ℕ} {dom : List ℕ} {gs : RawGens}
    (hd : dom.length = m) (hw : RawGens.WF m gs)
    (hc : aggnCase2 (dom,gs) = true) (hg : aggnCase2a (dom,gs) = false) :
    (aggnCase2bFamily (dom,gs)).length ≤
      (aggnLargeOrbitPoints (dom,gs)).length.choose (aggnMajorityDegree (dom,gs)-1) *
        ((aggnLargeOrbitPoints (dom,gs)).length-1) := by
  have hd4 : aggnMajorityDegree (dom,gs)-1 ≤ 4 := by
    have h := aggnMajorityDegree_bounds hd hw hc hg
    omega
  have hlen := aggnSmallSets_length (List.pairwise_lt_range.filter
    (fun u => decide (4 * dom.length < 5 * (rawOrbit (gs,u)).length)))
    (aggnLargeOrbitPoints_lt (m := dom.length) rfl) hd4
  change (aggnSmallSets (dom,aggnLargeOrbitPoints (dom,gs),aggnMajorityDegree (dom,gs)-1)).length =
    (aggnLargeOrbitPoints (dom,gs)).length.choose (aggnMajorityDegree (dom,gs)-1) at hlen
  have hbound : ∀ ss : List (List ℕ),
      (ss.flatMap (fun S => aggnCase2bAt ((dom,gs),(aggnLargeOrbitPoints (dom,gs),S)))).length ≤
        ss.length * ((aggnLargeOrbitPoints (dom,gs)).length-1) := by
    intro ss
    induction ss with
    | nil => simp
    | cons S ss ih =>
      have h : (aggnCase2bAt ((dom,gs),(aggnLargeOrbitPoints (dom,gs),S))).length ≤
          (aggnLargeOrbitPoints (dom,gs)).length-1 :=
        (aggnCase2bAt_length ((dom,gs),(aggnLargeOrbitPoints (dom,gs),S))).trans
          (Nat.sub_le_sub_right (List.length_filter_le _ _) 1)
      simp only [List.flatMap_cons,List.length_append,List.length_cons,Nat.add_mul,Nat.one_mul]
      omega
  rw [aggnCase2bFamily,← hlen]
  exact hbound _

end Algo
