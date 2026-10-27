import Workspace.Algo.AggNodeCase2bRaw

/-! # Reading each individualized constituent in the paper's family -/
namespace Algo
open RAM RAM.Targets Babai Equiv MulAction
open scoped Classical

theorem aggnCase2bAt_mem {m : ℕ} {dom C S : List ℕ} {gs : RawGens}
    (hd : dom.length = m) (hw : RawGens.WF m gs) (hC : ∀ u ∈ C,u < m)
    (hS : S.Nodup) (hSl : ∀ u ∈ S,u < m) {q : AggnRawConstituent}
    (hq : q ∈ aggnCase2bAt ((dom,gs),(C,S))) :
    ∃ a b : Fin m,a ∈ winSet m C \ winSet m S ∧ b ∈ winSet m C \ winSet m S ∧ a ≠ b ∧
      aggnDecodeConstituent m q =
        (winSet m C \ winSet m S,orbitalOn (decGroup m gs) (winSet m S) a b) := by
  obtain ⟨R,hR,rfl⟩ := List.mem_map.mp hq
  have hW : ∀ u ∈ aggnSetDiff (C,S),u < m := fun u hu => hC u (List.mem_filter.mp hu).1
  obtain ⟨a,b,ha,hb,hab,he⟩ := aggnOrbitals_mem hd
    (show RawGens.WF m (aggnPointStab ((dom,gs),S)) from wf_tidyGens hd _) hW hR
  have hrel : aggnDecodePairRel m R = orbitalOn (decGroup m gs) (winSet m S) a b := by
    rw [he,aggnPointStab_spec hd hw hS hSl]
    ext ⟨u,v⟩
    simp only [Set.mem_setOf_eq,orbitalOn,Prod.mk.injEq]
  have ha' : a ∈ winSet m C \ winSet m S := by
    rw [← aggnSetDiff_spec C S]
    exact ha
  have hb' : b ∈ winSet m C \ winSet m S := by
    rw [← aggnSetDiff_spec C S]
    exact hb
  exact ⟨a,b,ha',hb',hab,by rw [aggnDecodeConstituent,aggnSetDiff_spec,hrel]⟩

/-- Every off-diagonal orbital occurs when the individualized action is transitive. -/
theorem aggnCase2bAt_complete {m : ℕ} {dom C S : List ℕ} {gs : RawGens}
    (hd : dom.length = m) (hw : RawGens.WF m gs) (hC : ∀ u ∈ C,u < m)
    (hS : S.Nodup) (hSl : ∀ u ∈ S,u < m) (γ : Fin m)
    (hCo : winSet m C = orbit (decGroup m gs) γ)
    (htr : TransOnDiff (decGroup m gs) (winSet m C) (winSet m S))
    (a b : Fin m) (ha : a ∈ winSet m C \ winSet m S)
    (hb : b ∈ winSet m C \ winSet m S) (hab : a ≠ b) :
    ∃ q ∈ aggnCase2bAt ((dom,gs),(C,S)),aggnDecodeConstituent m q =
      (winSet m C \ winSet m S,orbitalOn (decGroup m gs) (winSet m S) a b) := by
  let W := aggnSetDiff (C,S)
  let hs := aggnPointStab ((dom,gs),S)
  have hsw : RawGens.WF m hs := wf_tidyGens hd _
  have hse := aggnPointStab_spec hd hw hS hSl
  have hWe : winSet m W = winSet m C \ winSet m S := aggnSetDiff_spec C S
  have hW : ∀ u ∈ W,u < m := fun u hu => hC u (List.mem_filter.mp hu).1
  have hinv : IsInvariant (decGroup m hs) (winSet m W) := by
    rw [hse,hWe,hCo]
    apply (isInvariant_iff_mem _ _).mpr
    intro g hg u
    exact mem_diff_iff_of_pointwiseStab hg u
  have htrans : ∀ u ∈ winSet m W,∀ v ∈ winSet m W,∃ g ∈ decGroup m hs,g u = v := by
    rw [hse,hWe]
    exact htr
  obtain ⟨R,hR,he⟩ := aggnOrbitals_complete hd hsw hW hinv htrans a b
    (by change a ∈ winSet m W; rwa [hWe])
    (by change b ∈ winSet m W; rwa [hWe]) hab
  have hrel : aggnDecodePairRel m R = orbitalOn (decGroup m gs) (winSet m S) a b := by
    rw [he,hse]
    ext ⟨u,v⟩
    simp only [Set.mem_setOf_eq,orbitalOn,Prod.mk.injEq]
  refine ⟨(W,R),List.mem_map.mpr ⟨R,hR,rfl⟩,?_⟩
  rw [aggnDecodeConstituent,hWe,hrel]

end Algo
