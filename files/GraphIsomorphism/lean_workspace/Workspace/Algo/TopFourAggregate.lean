import Workspace.Algo.TopFourOutput
import Workspace.Algo.AggNodeAggregateMajority

/-! # The top-action continuation of certificate aggregation
Section 13.2, Case 2a supplies the two large orbits directly from the
completed certificate stores. This entry computes the entire continuation,
including its alignment and its ordered top-action choices.
-/
set_option synthInstance.maxSize 2048
namespace Algo
open RAM RAM.Targets Babai Equiv MulAction
open scoped Classical

def top4AggregateInput (z : AggnPhaseCtx × AggnAggregateState) : Top4AutoInput :=
  (((z.1.1, z.1.2.1, z.1.2.2.1), aggnAggregateMajority (z, false)),
    aggnAggregateMajority (z, true))

def top4AggregateEnter (z : AggnPhaseCtx × AggnAggregateState) : Top4aNode :=
  top4AutoEnter (top4AggregateInput z)

theorem polyFun_top4AggregateInput : PolyFun top4AggregateInput := by
  have hC : PolyFun (fun z : AggnPhaseCtx × AggnAggregateState => z.1) := polyFun_fst
  have ha := hC.comp polyFun_fst
  have hx := (hC.comp polyFun_snd).comp polyFun_fst
  have hy := ((hC.comp polyFun_snd).comp polyFun_snd).comp polyFun_fst
  exact (((ha.pair (hx.pair hy)).pair
    ((polyFun_id.pair (polyFun_const false)).comp aggnPolyFun_aggregateMajority)).pair
      ((polyFun_id.pair (polyFun_const true)).comp aggnPolyFun_aggregateMajority))

theorem polyFun_top4AggregateEnter : PolyFun top4AggregateEnter :=
  polyFun_top4AggregateInput.comp polyFun_top4AutoEnter

theorem top4AggregateEnter_uniform_wf (C D e f : ℕ) : ∃ c d : ℕ,
    ∀ (n : ℕ) (z : AggnPhaseCtx × AggnAggregateState),
      z.1.1.1.1.length = n → Enc.size z ≤ topcsContextCap C D n →
        Top4aWF c d e f (top4AggregateEnter z) := by
  obtain ⟨F, hF, hmF, hsF⟩ := polyFun_top4AggregateInput.size.exists_polyBound
  obtain ⟨a, b, hab⟩ := hF.comp (polyBound_topcsContextCap C D)
  obtain ⟨c, d, hcd⟩ := top4AutoEnter_uniform_wf a b e f
  exact ⟨c, d, fun n z hn hz => hcd n (top4AggregateInput z) hn
    ((hsF z).trans ((hmF _ _ hz).trans (hab n)))⟩

section Checked
variable {c n m : ℕ} {C : AggnPhaseCtx} {s : AggnAggregateState}
    {ϕ : decGroup n C.1.1.2 →* Perm (Fin m)}
    (hC : AggnPhaseCtxWF c n m C ϕ) (hs : AggnStoresComplete c ϕ s.1.2.1)
    (hG : LocalCertSetting (decGroup n C.1.1.2) ϕ)
    (hm : HugeM m (Nat.card (Fin n)))
    (h2a : aggnAggregateGiantBranch (C, s) = true)

include hC hs h2a

theorem top4Aggregate_large : m < 2 * (winSet m (aggnAggregateMajority ((C, s), false))).ncard := by
  obtain ⟨u, hu, _⟩ := (aggnAggregateGiantBranch_spec hC hs).mp h2a
  rw [aggnAggregateMajority_spec hC hs false, cond_false,
    colorClass_bigOrbitColoring_eq_orbit ϕ C.2.2.2.length (decStrN n C.2.1) hu]
  simp only [Fintype.card_fin] at hu
  omega

noncomputable def top4AggregateSource : Top4Source n m :=
  Top4Source.ofRaw hC.action hG.transitive hG.giant (veryLargeK_of_hugeM hG.transitive hm)
    (aggnAggregateMajority ((C, s), false)) (aggnAggregateMajority_names hC false).1
    (aggnAggregateMajority_names hC false).2 (top4Aggregate_large hC hs h2a)

theorem top4AggregateSource_action : (top4AggregateSource hC hs hG hm h2a).action = C.1 :=
  Top4Source.ofRaw_action _ _ _ _ _ _ _ _

theorem top4Aggregate_giantOn :
    ∀ α : Perm (Fin m), α ∈ alternatingGroup (Fin m) →
      (∀ γ, γ ∉ colorClass (bigOrbitColoring ϕ C.2.2.2.length) (decStrN n C.2.1) true → α γ = γ) →
      ∃ β ∈ homImage ϕ (strAut (decGroup n C.1.1.2 : Set (Perm (Fin n))) (decStrN n C.2.1)),
        ∀ γ ∈ colorClass (bigOrbitColoring ϕ C.2.2.2.length) (decStrN n C.2.1) true, β γ = α γ := by
  obtain ⟨u, hu, hgiant⟩ := (aggnAggregateGiantBranch_spec hC hs).mp h2a
  intro α hα hfix
  rw [colorClass_bigOrbitColoring_eq_orbit ϕ C.2.2.2.length (decStrN n C.2.1) hu] at hfix ⊢
  obtain ⟨b, hb, hval⟩ := corollary_12_0_10_hypothesis_of_giant
    (bigFGamma ϕ (decStrN n C.2.1) C.2.2.2.length) (isInvariant_orbit _ u) hgiant α hα hfix
  refine ⟨b, ?_, hval⟩
  obtain ⟨⟨σ, hσ⟩, rfl⟩ := hb
  refine ⟨(σ : Perm (Fin n)), ?_, bigF_le hσ, rfl⟩
  have hmem := bigF_le_autG hσ
  change (σ : Perm (Fin n)) ∈ wAut Set.univ _ _ at hmem
  rwa [wAut, wIso_univ] at hmem

noncomputable def top4AggregateTree : SIReduction (Fin n) ℕ (Set (Perm (Fin n))) :=
  (top4AggregateSource hC hs hG hm h2a).autoTree hm C.2.1 C.2.2.1
    (aggnAggregateMajority ((C, s), true)) (bigOrbitColoring ϕ C.2.2.2.length) true
    (aggnAggregateMajority_spec hC hs false).symm (aggnAggregateMajority_spec hC hs true).symm

theorem top4Aggregate_loop {a b e f : ℕ} (hcap : TopwpCap e f) (solve : RawWinSI → RawCoset) :
    let I := top4AggregateEnter (C, s)
    LoopMatch (top4aRound a b e f solve) (top4aDecode n) (decCoset n) I
      ((top4aRound a b e f solve).width I) 0 (top4aInit I)
      (top4AggregateTree hC hs hG hm h2a) := by
  have h := (top4AggregateSource hC hs hG hm h2a).autoTree_loop (c := a) (d := b) hm hcap C.2.1 C.2.2.1
    (aggnAggregateMajority ((C, s), true)) (aggnAggregateMajority_names hC true).1
    (aggnAggregateMajority_names hC true).2 (bigOrbitColoring ϕ C.2.2.2.length) true
    (aggnAggregateMajority_spec hC hs false).symm (aggnAggregateMajority_spec hC hs true).symm solve
  dsimp only at h
  rw [top4AggregateSource_action] at h
  exact h

theorem top4Aggregate_spec :
    let T := top4AggregateTree hC hs hG hm h2a
    T.run = strIso (decGroup n C.1.1.2 : Set (Perm (Fin n))) (decStrN n C.2.1) (decStrN n C.2.2.1) ∧
      T.calls.length ≤ 7 * n ∧ (∀ J ∈ T.calls, 3 * J.windowSize ≤ 2 * n) :=
  (top4AggregateSource hC hs hG hm h2a).autoTree_spec hm C.2.1 C.2.2.1
    (aggnAggregateMajority ((C, s), true)) (bigOrbitColoring ϕ C.2.2.2.length) true
    (aggnAggregateMajority_spec hC hs false).symm (aggnAggregateMajority_spec hC hs true).symm
    (isCanonicalColoring_bigOrbitColoring ϕ C.2.2.2.length) (top4Aggregate_giantOn hC hs h2a)

end Checked
end Algo
