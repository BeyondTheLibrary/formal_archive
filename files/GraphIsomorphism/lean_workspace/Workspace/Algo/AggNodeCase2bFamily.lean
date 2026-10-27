import Workspace.Algo.AggNodeCase2bAtSpec

/-! # The raw Case 2b family is exactly the paper's family

The fixed first row affects only the enumeration order. Every constituent
specified in the paper occurs, over every set of individualized points.
-/
namespace Algo
open RAM RAM.Targets Babai Equiv MulAction
open scoped Classical

private theorem smallSets_wf {m d : ℕ} {dom C S : List ℕ} (hd : dom.length = m)
    (hd4 : d ≤ 4) (hS : S ∈ aggnSmallSets (dom,C,d)) :
    S.Nodup ∧ (∀ u ∈ S,u < m) ∧ winSet m S ⊆ winSet m C ∧ (winSet m S).ncard = d := by
  obtain ⟨hl,hm,he⟩ := (aggnSmallSets_mem hd4).mp hS
  have hnd : S.Nodup := by rw [he]; exact List.nodup_range.filter _
  have hlt : ∀ u ∈ S,u < m := by
    intro u hu
    rw [he] at hu
    simpa only [hd] using List.mem_range.mp (List.mem_filter.mp hu).1
  exact ⟨hnd,hlt,fun u hu => hm u.val hu,(ncard_winSet S hnd hlt).trans hl⟩

private theorem notGiant_orbit {m : ℕ} {dom : List ℕ} {gs : RawGens}
    (hd : dom.length = m) (hw : RawGens.WF m gs)
    (hg : aggnCase2a (dom,gs) = false) (γ : Fin m)
    (he : winSet m (aggnLargeOrbitPoints (dom,gs)) = orbit (decGroup m gs) γ) :
    ¬ alternatingGroup ↥(orbit (decGroup m gs) γ : Set (Fin m)) ≤
      restrictTo (decGroup m gs) _ (isInvariant_orbit _ γ) := by
  have hnot : ¬ alternatingGroup ↥(winSet m (aggnLargeOrbitPoints (dom,gs))) ≤
      restrictTo (decGroup m gs) _ (aggnLargeOrbitPoints_invariant hd hw) := by
    intro h
    have ht := (aggnCase2a_spec hd hw).mpr h
    rw [hg] at ht
    contradiction
  have hc : ∀ (A B : Set (Fin m)) (ha : IsInvariant (decGroup m gs) A)
      (hb : IsInvariant (decGroup m gs) B),A = B →
      (alternatingGroup A ≤ restrictTo (decGroup m gs) A ha ↔
        alternatingGroup B ≤ restrictTo (decGroup m gs) B hb) := by
    intro A B ha hb he
    subst B
    rfl
  exact fun h => hnot ((hc _ _ _ _ he).mpr h)

/-- Every raw output is a member of the faithful Case 2b family. -/
theorem aggnCase2bFamily_sound {m : ℕ} {dom : List ℕ} {gs : RawGens}
    (hd : dom.length = m) (hw : RawGens.WF m gs)
    (hc : aggnCase2 (dom,gs) = true) (hg : aggnCase2a (dom,gs) = false)
    {q : AggnRawConstituent} (hq : q ∈ aggnCase2bFamily (dom,gs)) :
    aggnDecodeConstituent m q ∈ case2bFamily (decGroup m gs) := by
  obtain ⟨γ,hCo,hlarge⟩ := aggnLargeOrbitPoints_orbit hd hw hc
  obtain ⟨S,hS,hq⟩ := List.mem_flatMap.mp hq
  have hd4 : aggnMajorityDegree (dom,gs)-1 ≤ 4 := by
    have h := aggnMajorityDegree_bounds hd hw hc hg
    omega
  obtain ⟨hnd,hlt,hsub,hcard⟩ := smallSets_wf hd hd4 hS
  obtain ⟨a,b,ha,hb,hab,he⟩ := aggnCase2bAt_mem hd hw (aggnLargeOrbitPoints_lt hd) hnd hlt hq
  refine ⟨γ,winSet m S,a,b,?_,?_,?_,?_,?_,hab,?_⟩
  · have hn := ncard_winSet _ (aggnLargeOrbitPoints_nodup (dom,gs)) (aggnLargeOrbitPoints_lt hd)
    rw [hCo] at hn
    simpa only [Fintype.card_fin,hn] using hlarge
  · rwa [← hCo]
  · rw [hcard,aggnMajorityDegree_spec hd hw,hCo]
  · rwa [← hCo]
  · rwa [← hCo]
  · rwa [← hCo]

/-- All choices in the paper occur, with no supplied constituent or tuple. -/
theorem aggnCase2bFamily_complete {m : ℕ} {dom : List ℕ} {gs : RawGens}
    (hd : dom.length = m) (hw : RawGens.WF m gs)
    (hc : aggnCase2 (dom,gs) = true) (hg : aggnCase2a (dom,gs) = false)
    (hlarge : 6 ≤ (aggnLargeOrbitPoints (dom,gs)).length)
    {q : Set (Fin m) × Set (Fin m × Fin m)} (hq : q ∈ case2bFamily (decGroup m gs)) :
    ∃ r ∈ aggnCase2bFamily (dom,gs),aggnDecodeConstituent m r = q := by
  obtain ⟨γ,S,a,b,hγ,hSC,hScard,ha,hb,hab,rfl⟩ := hq
  have he : winSet m (aggnLargeOrbitPoints (dom,gs)) = orbit (decGroup m gs) γ :=
    aggnLargeOrbitPoints_eq_orbit hd hw γ (by simpa only [Fintype.card_fin] using hγ)
  have hd4 : aggnMajorityDegree (dom,gs)-1 ≤ 4 := by
    have h := aggnMajorityDegree_bounds hd hw hc hg
    omega
  have hcard : S.ncard = aggnMajorityDegree (dom,gs)-1 := by
    rw [aggnMajorityDegree_spec hd hw,he]
    exact hScard
  have hS : aggName S ∈ aggnSmallSets
      (dom,aggnLargeOrbitPoints (dom,gs),aggnMajorityDegree (dom,gs)-1) :=
    aggnSmallSets_complete hd hd4 S (by rwa [he]) hcard
  have hnd : (aggName S).Nodup := List.nodup_range.filter _
  have hlt : ∀ u ∈ aggName S,u < m := fun u hu => List.mem_range.mp (List.mem_filter.mp hu).1
  have hc6 : 6 ≤ (orbit (decGroup m gs) γ : Set (Fin m)).ncard := by
    have hn := ncard_winSet _ (aggnLargeOrbitPoints_nodup (dom,gs)) (aggnLargeOrbitPoints_lt hd)
    rw [he] at hn
    omega
  have htr := ((case2b_facts_on (decGroup m gs) γ (notGiant_orbit hd hw hg γ he) hc6).2.2
    S hSC hScard).1
  obtain ⟨r,hr,her⟩ := aggnCase2bAt_complete hd hw (aggnLargeOrbitPoints_lt hd) hnd hlt γ he
    (by simpa only [he,aggName_spec] using htr) a b
    (by simpa only [he,aggName_spec] using ha) (by simpa only [he,aggName_spec] using hb) hab
  refine ⟨r,List.mem_flatMap.mpr ⟨aggName S,hS,hr⟩,?_⟩
  simpa only [he,aggName_spec] using her

/-- The decoded raw output set equals the complete family, including its choices. -/
theorem aggnCase2bFamily_spec {m : ℕ} {dom : List ℕ} {gs : RawGens}
    (hd : dom.length = m) (hw : RawGens.WF m gs)
    (hc : aggnCase2 (dom,gs) = true) (hg : aggnCase2a (dom,gs) = false)
    (hlarge : 6 ≤ (aggnLargeOrbitPoints (dom,gs)).length) :
    {q | ∃ r ∈ aggnCase2bFamily (dom,gs),aggnDecodeConstituent m r = q} =
      case2bFamily (decGroup m gs) := by
  ext q
  constructor
  · rintro ⟨r,hr,rfl⟩
    exact aggnCase2bFamily_sound hd hw hc hg hr
  · exact aggnCase2bFamily_complete hd hw hc hg hlarge

end Algo
