import Workspace.Algo.AggNodeCase2bCount
import Workspace.Master.Case2bVersions

/-! # Admissible, nonempty computed Case 2b outputs

These are the actual family members consumed by Section 15, line 6a.
The admissibility and defect proof is the paper's biregular-digraph
argument already formalized in `case2bFamily_facts`.
-/
namespace Algo
open RAM RAM.Targets Babai Equiv MulAction
open scoped Classical

theorem aggnCase2bFamily_pow_bound {m : ℕ} {dom : List ℕ} {gs : RawGens}
    (hd : dom.length = m) (hw : RawGens.WF m gs)
    (hc : aggnCase2 (dom,gs) = true) (hg : aggnCase2a (dom,gs) = false) :
    (aggnCase2bFamily (dom,gs)).length ≤ m^5 := by
  obtain ⟨hd1,hd5⟩ := aggnMajorityDegree_bounds hd hw hc hg
  obtain ⟨γ,hCo,hlarge⟩ := aggnLargeOrbitPoints_orbit hd hw hc
  have hClen : (aggnLargeOrbitPoints (dom,gs)).length ≤ m := by
    exact (List.length_filter_le _ _).trans (by simp [hd])
  have hm : 0 < m := Nat.pos_of_ne_zero (fun he => Fin.elim0 (he ▸ γ))
  calc (aggnCase2bFamily (dom,gs)).length
      ≤ (aggnLargeOrbitPoints (dom,gs)).length.choose (aggnMajorityDegree (dom,gs)-1) *
          ((aggnLargeOrbitPoints (dom,gs)).length-1) := aggnCase2bFamily_length hd hw hc hg
    _ ≤ (aggnLargeOrbitPoints (dom,gs)).length^(aggnMajorityDegree (dom,gs)-1) *
          (aggnLargeOrbitPoints (dom,gs)).length := Nat.mul_le_mul (Nat.choose_le_pow _ _) (Nat.sub_le _ _)
    _ = (aggnLargeOrbitPoints (dom,gs)).length^(aggnMajorityDegree (dom,gs)) := by
      rw [← pow_succ,Nat.sub_add_cancel hd1]
    _ ≤ m^(aggnMajorityDegree (dom,gs)) := Nat.pow_le_pow_left hClen _
    _ ≤ m^5 := Nat.pow_le_pow_right hm hd5

/-- Nonemptiness and the exact admissibility margin, for every raw output. -/
theorem aggnCase2bFamily_facts {m : ℕ} {dom : List ℕ} {gs : RawGens}
    (hd : dom.length = m) (hw : RawGens.WF m gs) (hm : 217 ≤ m)
    (hc : aggnCase2 (dom,gs) = true) (hg : aggnCase2a (dom,gs) = false) :
    (∃ r,r ∈ aggnCase2bFamily (dom,gs)) ∧
      (∀ r ∈ aggnCase2bFamily (dom,gs),Case2bOk (3/4 : ℝ) (aggnDecodeConstituent m r) ∧
        11*m ≤ 15*(winSet m r.1).ncard) ∧
      (aggnCase2bFamily (dom,gs)).length ≤ m^5 := by
  have h2 := (aggnCase2_spec hd hw).mp hc
  have h2a : ∀ γ : Fin m,¬ (4 * Fintype.card (Fin m) < 5*(orbit (decGroup m gs) γ : Set (Fin m)).ncard ∧
      alternatingGroup ↥(orbit (decGroup m gs) γ : Set (Fin m)) ≤
        restrictTo (decGroup m gs) _ (isInvariant_orbit _ γ)) := by
    intro γ h
    have htest := (aggnCase2a_orbit_spec hd hw).mpr ⟨γ,by simpa only [Fintype.card_fin] using h.1,h.2⟩
    rw [hg] at htest
    exact Bool.noConfusion htest.2
  obtain ⟨hne,hok,_⟩ := case2bFamily_facts (decGroup m gs) (by simpa only [Fintype.card_fin] using hm) h2 h2a
  have h6 : 6 ≤ (aggnLargeOrbitPoints (dom,gs)).length := by
    obtain ⟨_,_,h⟩ := aggnLargeOrbitPoints_orbit hd hw hc
    omega
  refine ⟨?_,?_,aggnCase2bFamily_pow_bound hd hw hc hg⟩
  · obtain ⟨q,hq⟩ := hne
    obtain ⟨r,hr,_⟩ := aggnCase2bFamily_complete hd hw hc hg h6 hq
    exact ⟨r,hr⟩
  · intro r hr
    simpa only [Fintype.card_fin] using hok _ (aggnCase2bFamily_sound hd hw hc hg hr)

end Algo
