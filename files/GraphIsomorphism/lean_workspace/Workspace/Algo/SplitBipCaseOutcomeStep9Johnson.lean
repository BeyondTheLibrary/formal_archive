import Workspace.Algo.SplitBipCaseOutcomeStep9
import Workspace.Algo.SplitBipCaseOutcomeJohnson
import Workspace.Algo.TestSetNaming

/-! The computed dictionary has singleton rows at every first-part index.
Consequently all Johnson exits restore into the original parent domain,
with the same carrier size and the same subset rows.
-/
namespace Algo
open Babai RAM
open scoped Classical

section Raw
variable (z : RawSbipStored × (ℕ × ℕ))
    (hl : z.1.1.1.1.Nodup) {m : ℕ} (hb : ∀ a ∈ z.1.1.1.1,a < m)
    {J : RawJohnson} (hsub : ∀ a ∈ J.1,a ∈ (sbipGraphStep9Input (z.1.1,z.2)).2.1)
include hl hsub

theorem sbipCaseStep9_johnson_injective :
    Set.InjOn (fun a => sbipDictPoint (sbipGraphStep9Dictionary z,a)) {a | a ∈ J.1} := by
  have hnd : (sbipCasePointList (z.1.1.1.1,sbipGraphStep9Dictionary z,
      (sbipGraphStep9Input (z.1.1,z.2)).2.1)).Nodup := by
    rw [sbipCasePointList_step9]
    exact hl.filter _
  have hi := (List.nodup_map_iff_inj_on (sbipGraphStep9Input_wf (z.1.1,z.2)).left_nodup).1 hnd
  exact fun a ha b hb he => hi a (hsub a ha) b (hsub b hb) he

omit hl in
theorem sbipCaseStep9_johnson_mem {a : ℕ}
    (ha : a ∈ (sbipCaseJohnson (sbipGraphStep9Dictionary z,J)).1) : a ∈ z.1.1.1.1 := by
  obtain ⟨b,hb,he⟩ := List.mem_map.1 ha
  have hm : a ∈ sbipCasePointList (z.1.1.1.1,sbipGraphStep9Dictionary z,
      (sbipGraphStep9Input (z.1.1,z.2)).2.1) := List.mem_map.2 ⟨b,hsub b hb,he⟩
  rw [sbipCasePointList_step9] at hm
  exact List.mem_of_mem_filter hm

include hb in
theorem sbipCaseStep9_johnson_wf {ms ts : ℕ}
    (hJ : J.WF (sbipGraphStep9Input (z.1.1,z.2)).1.1.length ms ts) :
    (sbipCaseJohnson (sbipGraphStep9Dictionary z,J)).WF m ms ts := by
  apply sbipCaseJohnson_wf (sbipCaseStep9_johnson_injective z hl hsub) ?_ hJ
  intro a ha
  exact hb _ (sbipCaseStep9_johnson_mem z hsub (List.mem_map.2 ⟨a,ha,rfl⟩))

end Raw

section Validity
variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    (X : Pt (BipBlockInputs Ω)) (name : X.obj.1.1.Vtx → ℕ)
    (z : RawSbipStored × (ℕ × ℕ))
    (h : SbipGraphColorNames X.obj.1.1 z.1.1 name)
    (hnd : (sbipGraphVertices z.1.1).Nodup)
    (e : X.obj.1.1.Vtx ≃ Fin (sbipGraphVertices z.1.1).length)
    (he : ∀ A,(sbipGraphVertices z.1.1)[(e A).val] = name A)
    (hp : sbipGraphPointName X name '' Set.univ = {a | a ∈ z.1.1.1.1})
    (hr : sbipGraphBlockName X name '' Set.univ = {a | a ∈ z.1.1.1.2.1})
    (ha : sbipAlphaValue z.2 = BipBlockInputs.alpha X)
    (hb : 0 < z.2.2) (hl : z.1.1.1.1.Nodup) (hd : ¬ AllClassesSmall X)
include h hnd he hp hr ha hb hl hd

theorem sbipCaseStep9_johnson_valid {m ms ts : ℕ}
    (hbound : ∀ a ∈ z.1.1.1.1,a < m) (J : RawJohnson)
    (hsub : ∀ a ∈ J.1,a ∈ (sbipGraphStep9Input (z.1.1,z.2)).2.1)
    (hJ : J.WF (sbipGraphStep9Input (z.1.1,z.2)).1.1.length ms ts)
    (hlarge : alphaNew X * ((sbipGraphStep9Input (z.1.1,z.2)).2.1.length : ℝ) ≤ J.1.length) :
    IsSplitOutcome (BipBlockInputs.alpha X) (winSet m z.1.1.1.1)
      (decAlignJohnson (sbipCaseJohnson (sbipGraphStep9Dictionary z,J))
        (sbipCaseStep9_johnson_wf z hl hbound hsub hJ)) := by
  have hrest := sbipCaseStep9_johnson_wf z hl hbound hsub hJ
  refine ⟨fun a ha => sbipCaseStep9_johnson_mem z hsub ha,?_⟩
  change BipBlockInputs.alpha X * (winSet m z.1.1.1.1).ncard ≤
    (winSet m (sbipCaseJohnson (sbipGraphStep9Dictionary z,J)).1).ncard
  rw [ncard_winSet _ hl hbound,ncard_winSet _ hrest.wNodup hrest.wLt]
  simp only [sbipCaseJohnson,List.length_map]
  obtain ⟨eV,_⟩ := sbipGraphParent_equiv_exists X name (z.1.1,z.2) h hnd e he hp ha hl
  obtain ⟨eW,_⟩ := sbipGraphDominant_equiv_exists X (z.1.1,z.2) name h hnd e he hp hr ha hb hl hd
  have hV : (BipBlockInputs.V₁ X).ncard = z.1.1.1.1.length := by
    simpa only [Nat.card_coe_set_eq,Nat.card_fin] using Nat.card_congr eV
  have hW : (dominantClass X).ncard = (sbipGraphStep9Input (z.1.1,z.2)).2.1.length := by
    have hh := Nat.card_congr eW
    simp only [Nat.card_coe_set_eq,Nat.card_fin] at hh
    simpa only [sbipGraphStep9Input,sbipGraphNumbered,List.length_map,List.length_range] using hh
  have heq : alphaNew X * ((sbipGraphStep9Input (z.1.1,z.2)).2.1.length : ℝ) =
      BipBlockInputs.alpha X * (z.1.1.1.1.length : ℝ) := by
    rw [← hV,← hW]
    simpa only [step8V₁_ncard] using alphaNew_mul_step8V₁ hd
  exact heq ▸ hlarge

end Validity
end Algo
