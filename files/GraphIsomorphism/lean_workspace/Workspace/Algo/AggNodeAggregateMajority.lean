import Workspace.Algo.AggNodeAggregateTests
import Workspace.Master.Line567a

/-! # The canonical large orbit and the Case 2a test

The points belonging to an orbit larger than four fifths form that unique
orbit. Keeping them in increasing order gives its raw name. Restricting
the aggregate group to this list and testing its order decides precisely
whether its action contains the alternating group, as in Section 13.2.
-/
set_option synthInstance.maxSize 1024
namespace Algo
open RAM RAM.Targets Babai Equiv MulAction
open scoped Classical

theorem aggnLargeOrbitPoints_nodup (p : List ℕ × RawGens) :
    (aggnLargeOrbitPoints p).Nodup := List.Nodup.filter _ List.nodup_range

theorem aggnLargeOrbitPoints_lt {m : ℕ} {dom : List ℕ} {gs : RawGens}
    (hd : dom.length = m) : ∀ u ∈ aggnLargeOrbitPoints (dom, gs), u < m := by
  intro u hu
  simpa only [hd] using List.mem_range.mp (List.mem_filter.mp hu).1

/-- The list contains the entire unique large orbit, regardless of which point witnesses it. -/
theorem aggnLargeOrbitPoints_eq_orbit {m : ℕ} {dom : List ℕ} {gs : RawGens}
    (hd : dom.length = m) (hw : RawGens.WF m gs) (u : Fin m)
    (hu : 4 * m < 5 * (orbit (decGroup m gs) u : Set (Fin m)).ncard) :
    winSet m (aggnLargeOrbitPoints (dom, gs)) = orbit (decGroup m gs) u := by
  ext v
  rw [show v ∈ winSet m (aggnLargeOrbitPoints (dom, gs)) ↔
    v.val ∈ aggnLargeOrbitPoints (dom, gs) from Iff.rfl, aggnLargeOrbitPoints_mem hd hw v]
  constructor
  · intro hv
    have he := orbit_eq_of_two_large (H := decGroup m gs) (γ := v) (δ := u)
      (by simpa only [Fintype.card_fin] using (show m < 2 * (orbit (decGroup m gs) v : Set (Fin m)).ncard by omega))
      (by simpa only [Fintype.card_fin] using (show m < 2 * (orbit (decGroup m gs) u : Set (Fin m)).ncard by omega))
    rw [← he]
    exact mem_orbit_self v
  · intro hv
    rw [orbit_eq_iff.mpr hv]
    exact hu

theorem aggnLargeOrbitPoints_orbit {m : ℕ} {dom : List ℕ} {gs : RawGens}
    (hd : dom.length = m) (hw : RawGens.WF m gs) (h : aggnCase2 (dom, gs) = true) :
    ∃ u : Fin m, winSet m (aggnLargeOrbitPoints (dom, gs)) = orbit (decGroup m gs) u ∧
      4 * m < 5 * (aggnLargeOrbitPoints (dom, gs)).length := by
  obtain ⟨u, hu⟩ := (aggnCase2_spec hd hw).mp h
  have hu' : 4 * m < 5 * (orbit (decGroup m gs) u : Set (Fin m)).ncard := by simpa using hu
  have he := aggnLargeOrbitPoints_eq_orbit hd hw u hu'
  refine ⟨u, he, ?_⟩
  have hc := ncard_winSet _ (aggnLargeOrbitPoints_nodup (dom, gs)) (aggnLargeOrbitPoints_lt hd)
  rw [he] at hc
  omega

/-- Even malformed branch selection cannot require an invariance hypothesis from the caller. -/
theorem aggnLargeOrbitPoints_invariant {m : ℕ} {dom : List ℕ} {gs : RawGens}
    (hd : dom.length = m) (hw : RawGens.WF m gs) :
    IsInvariant (decGroup m gs) (winSet m (aggnLargeOrbitPoints (dom, gs))) := by
  by_cases h : aggnCase2 (dom, gs) = true
  · obtain ⟨u, he, _⟩ := aggnLargeOrbitPoints_orbit hd hw h
    rw [he]
    exact isInvariant_orbit _ u
  · have he : aggnLargeOrbitPoints (dom, gs) = [] := by
      simpa only [aggnCase2, Bool.not_eq_true', Bool.not_eq_false, List.isEmpty_iff] using h
    rw [he]
    intro g hg
    simp [winSet]

def aggnMajorityRestricted (p : List ℕ × RawGens) : RawGens :=
  tidyGens (aggnLargeOrbitPoints p, rawRestrictGens ((p.1, p.2), aggnLargeOrbitPoints p))

def aggnCase2a (p : List ℕ × RawGens) : Bool :=
  rawIsGiantSub (aggnLargeOrbitPoints p, aggnMajorityRestricted p)

theorem aggnPolyFun_majorityRestricted : PolyFun aggnMajorityRestricted :=
  (aggnPolyFun_largeOrbitPoints.pair
    ((polyFun_id.pair aggnPolyFun_largeOrbitPoints).comp polyFun_rawRestrictGens)).comp polyFun_tidyGens

theorem aggnPolyFun_case2a : PolyFun aggnCase2a :=
  (aggnPolyFun_largeOrbitPoints.pair aggnPolyFun_majorityRestricted).comp polyFun_rawIsGiantSub

theorem aggnMajorityRestricted_spec {m : ℕ} {dom : List ℕ} {gs : RawGens}
    (hd : dom.length = m) (hw : RawGens.WF m gs) :
    decGroup (aggnLargeOrbitPoints (dom, gs)).length (aggnMajorityRestricted (dom, gs)) =
      (winRestrictHom m (aggnLargeOrbitPoints (dom, gs)) (aggnLargeOrbitPoints_nodup _)
        (aggnLargeOrbitPoints_lt hd) (decGroup m gs) (aggnLargeOrbitPoints_invariant hd hw)).range := by
  rw [aggnMajorityRestricted, decGroup_tidyGens rfl]
  have h := decGroup_rawRestrictGens (aggnLargeOrbitPoints_nodup (dom, gs))
    (aggnLargeOrbitPoints_lt hd) dom (gs.map (decPerm m)) (aggnLargeOrbitPoints_invariant hd hw)
  simpa only [map_encPerm_decPerm hw] using h

/-- The numerical test is exactly the alternating-group condition on the large orbit. -/
theorem aggnCase2a_spec {m : ℕ} {dom : List ℕ} {gs : RawGens}
    (hd : dom.length = m) (hw : RawGens.WF m gs) :
    aggnCase2a (dom, gs) = true ↔
      alternatingGroup ↥(winSet m (aggnLargeOrbitPoints (dom, gs))) ≤
        restrictTo (decGroup m gs) (winSet m (aggnLargeOrbitPoints (dom, gs)))
          (aggnLargeOrbitPoints_invariant hd hw) := by
  have h := rawIsGiantSub_eq_true_iff (dom := aggnLargeOrbitPoints (dom, gs)) rfl
    ((aggnMajorityRestricted (dom, gs)).map (decPerm (aggnLargeOrbitPoints (dom, gs)).length))
  rw [map_encPerm_decPerm (show RawGens.WF _ (aggnMajorityRestricted (dom, gs)) from wf_tidyGens rfl _)] at h
  change aggnCase2a (dom, gs) = true ↔ _ at h
  rw [h]
  change alternatingGroup (Fin (aggnLargeOrbitPoints (dom, gs)).length) ≤
    decGroup (aggnLargeOrbitPoints (dom, gs)).length (aggnMajorityRestricted (dom, gs)) ↔ _
  rw [aggnMajorityRestricted_spec hd hw, range_winRestrictHom]
  exact alternating_le_map_permCongrHom_iff _ _

private theorem alternatingRestrict_congr {m : ℕ} (H : Subgroup (Perm (Fin m)))
    {A B : Set (Fin m)} (h : A = B) (ha : IsInvariant H A) (hb : IsInvariant H B) :
    (alternatingGroup A ≤ restrictTo H A ha) ↔ (alternatingGroup B ≤ restrictTo H B hb) := by
  subst B
  rfl

/-- The conjunction also requires a large orbit, so the empty default is never a Case 2a exit. -/
theorem aggnCase2a_orbit_spec {m : ℕ} {dom : List ℕ} {gs : RawGens}
    (hd : dom.length = m) (hw : RawGens.WF m gs) :
    (aggnCase2 (dom, gs) = true ∧ aggnCase2a (dom, gs) = true) ↔
      ∃ u : Fin m, 4 * m < 5 * (orbit (decGroup m gs) u : Set (Fin m)).ncard ∧
        alternatingGroup ↥(orbit (decGroup m gs) u : Set (Fin m)) ≤
          restrictTo (decGroup m gs) _ (isInvariant_orbit (decGroup m gs) u) := by
  constructor
  · rintro ⟨h2, ha⟩
    obtain ⟨u, hu⟩ := (aggnCase2_spec hd hw).mp h2
    have hu' : 4 * m < 5 * (orbit (decGroup m gs) u : Set (Fin m)).ncard := by simpa using hu
    have he := aggnLargeOrbitPoints_eq_orbit hd hw u hu'
    have hgiant := (aggnCase2a_spec hd hw).mp ha
    refine ⟨u, hu', ?_⟩
    exact (alternatingRestrict_congr _ he _ _).mp hgiant
  · rintro ⟨u, hu, hgiant⟩
    refine ⟨(aggnCase2_spec hd hw).mpr ⟨u, by simpa using hu⟩, (aggnCase2a_spec hd hw).mpr ?_⟩
    have he := aggnLargeOrbitPoints_eq_orbit hd hw u hu
    exact (alternatingRestrict_congr _ he _ _).mpr hgiant

/-- The actual large class list for either source or target. -/
def aggnAggregateMajority (z : (AggnPhaseCtx × AggnAggregateState) × Bool) : List ℕ :=
  aggnLargeOrbitPoints (z.1.1.1.2.1, (aggnAggregateData z).2.1)

theorem aggnPolyFun_aggregateMajority : PolyFun aggnAggregateMajority := by
  have hd : PolyFun (fun z : (AggnPhaseCtx × AggnAggregateState) × Bool => z.1.1.1.2.1) :=
    ((((polyFun_fst.comp polyFun_fst).comp polyFun_fst).comp polyFun_snd).comp polyFun_fst)
  exact (hd.pair ((aggnPolyFun_aggregateData.comp polyFun_snd).comp polyFun_fst)).comp
    aggnPolyFun_largeOrbitPoints

theorem aggnAggregateMajority_spec {c n m : ℕ} {C : AggnPhaseCtx} {s : AggnAggregateState}
    {ϕ : decGroup n C.1.1.2 →* Perm (Fin m)}
    (hC : AggnPhaseCtxWF c n m C ϕ) (hs : AggnStoresComplete c ϕ s.1.2.1) (b : Bool) :
    winSet m (aggnAggregateMajority ((C, s), b)) =
      colorClass (bigOrbitColoring ϕ C.2.2.2.length)
        (cond b (decStrN n C.2.2.1) (decStrN n C.2.1)) true := by
  have hw : RawGens.WF m (aggnAggregateData ((C, s), b)).2.1 := wf_tidyGens hC.action.2.1 _
  ext u
  change u.val ∈ aggnLargeOrbitPoints _ ↔ _
  rw [aggnLargeOrbitPoints_mem hC.action.2.1 hw u, colorClass_bigOrbitColoring,
    (aggnAggregateData_spec hC hs b).2.1]
  simp only [Set.mem_setOf_eq, Fintype.card_fin]

theorem aggnAggregateMajority_names {c n m : ℕ} {C : AggnPhaseCtx} {s : AggnAggregateState}
    {ϕ : decGroup n C.1.1.2 →* Perm (Fin m)} (hC : AggnPhaseCtxWF c n m C ϕ) (b : Bool) :
    (aggnAggregateMajority ((C, s), b)).Nodup ∧
      ∀ u ∈ aggnAggregateMajority ((C, s), b), u < m :=
  ⟨aggnLargeOrbitPoints_nodup _, aggnLargeOrbitPoints_lt hC.action.2.1⟩

/-- Test the source's Case 2a exit on the computed aggregate image. -/
def aggnAggregateGiantBranch (z : AggnPhaseCtx × AggnAggregateState) : Bool :=
  let p := (z.1.1.2.1, (aggnAggregateData (z, false)).2.1)
  aggnCase2 p && aggnCase2a p

theorem aggnPolyFun_aggregateGiantBranch : PolyFun aggnAggregateGiantBranch := by
  have hd : PolyFun (fun z : AggnPhaseCtx × AggnAggregateState => z.1.1.2.1) :=
    ((polyFun_fst.comp polyFun_fst).comp polyFun_snd).comp polyFun_fst
  have hg := (((polyFun_id.pair (polyFun_const false)).comp aggnPolyFun_aggregateData).comp
    polyFun_snd).comp polyFun_fst
  have hp := hd.pair hg
  exact wftPolyFun_and (hp.comp aggnPolyFun_case2) (hp.comp aggnPolyFun_case2a)

theorem aggnAggregateGiantBranch_spec {c n m : ℕ} {C : AggnPhaseCtx} {s : AggnAggregateState}
    {ϕ : decGroup n C.1.1.2 →* Perm (Fin m)}
    (hC : AggnPhaseCtxWF c n m C ϕ) (hs : AggnStoresComplete c ϕ s.1.2.1) :
    aggnAggregateGiantBranch (C, s) = true ↔ AggregateCase2a ϕ (decStrN n C.2.1) C.2.2.2.length := by
  have hw : RawGens.WF m (aggnAggregateData ((C, s), false)).2.1 := wf_tidyGens hC.action.2.1 _
  simp only [aggnAggregateGiantBranch, Bool.and_eq_true]
  rw [aggnCase2a_orbit_spec hC.action.2.1 hw, (aggnAggregateData_spec hC hs false).2.1]
  simp only [AggregateCase2a, Fintype.card_fin]
  rfl

end Algo

