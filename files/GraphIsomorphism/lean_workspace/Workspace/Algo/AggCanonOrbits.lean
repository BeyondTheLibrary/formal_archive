import Workspace.Algo.AggNodeEnum
import Workspace.Algo.TopOrbits
import Workspace.LocalCertificates.Canonical

/-! # Fixed affected-point and orbit orders

The affected points are listed in increasing order. The orbit scan appends an
orbit at its first uncovered point. Changing generators changes the raw orbit
lists, but does not change the list of decoded windows.
-/

namespace Algo

open Babai Equiv MulAction
open scoped Classical Pointwise

theorem aggkCovered_congr {n : ℕ} {A B : List (List ℕ)}
    (h : A.map (winSet n) = B.map (winSet n)) (u : Fin n) :
    u.val ∈ A.flatten ↔ u.val ∈ B.flatten := by
  have he := congrArg (fun L : List (Set (Fin n)) => ∃ Δ ∈ L, u ∈ Δ) h
  simpa [winSet] using Iff.of_eq he

theorem aggkOrbitStep_congr {n : ℕ} {gs gs' : RawGens}
    (hgs : RawGens.WF n gs) (hgs' : RawGens.WF n gs')
    (hg : decGroup n gs = decGroup n gs') {A B : List (List ℕ)}
    (h : A.map (winSet n) = B.map (winSet n)) {u : ℕ} (hu : u < n) :
    (rawOrbitsStep (gs, A, u)).map (winSet n) =
      (rawOrbitsStep (gs', B, u)).map (winSet n) := by
  have hc := aggkCovered_congr h (⟨u, hu⟩ : Fin n)
  by_cases ha : u ∈ A.flatten
  · simp only [rawOrbitsStep, if_pos ha, if_pos (hc.mp ha)]
    exact h
  · have hb : u ∉ B.flatten := fun hb => ha (hc.mpr hb)
    simp only [rawOrbitsStep, if_neg ha, if_neg hb, List.map_append, List.map_cons,
      List.map_nil]
    rw [h, winSet_rawOrbit hgs ⟨u, hu⟩, winSet_rawOrbit hgs' ⟨u, hu⟩, hg]

theorem aggkOrbitFold_congr {n : ℕ} {gs gs' : RawGens}
    (hgs : RawGens.WF n gs) (hgs' : RawGens.WF n gs')
    (hg : decGroup n gs = decGroup n gs') (W : List ℕ)
    (hW : ∀ u ∈ W, u < n) (A B : List (List ℕ))
    (h : A.map (winSet n) = B.map (winSet n)) :
    (W.foldl (fun acc u => rawOrbitsStep (gs, acc, u)) A).map (winSet n) =
      (W.foldl (fun acc u => rawOrbitsStep (gs', acc, u)) B).map (winSet n) := by
  induction W generalizing A B with
  | nil => exact h
  | cons u W ih =>
    exact ih (fun v hv => hW v (List.mem_cons_of_mem u hv)) _ _
      (aggkOrbitStep_congr hgs hgs' hg h (hW u List.mem_cons_self))

/-- The decoded orbit order depends on the group and the window list alone. -/
theorem aggkWinOrbits_congr {n : ℕ} {gs gs' : RawGens}
    (hgs : RawGens.WF n gs) (hgs' : RawGens.WF n gs')
    (hg : decGroup n gs = decGroup n gs') (W : List ℕ)
    (hW : ∀ u ∈ W, u < n) :
    (winOrbits (gs, W)).map (winSet n) = (winOrbits (gs', W)).map (winSet n) :=
  aggkOrbitFold_congr hgs hgs' hg W hW [] [] rfl

theorem aggkRawAff_sorted (p : RawAction) : (rawAff p).SortedLT :=
  ((List.sortedLT_range _).pairwise.sublist (List.filter_sublist)).sortedLT

/-- Increasing natural names of a mathematical window. -/
noncomputable def aggkWindowNames {n : ℕ} (W : Set (Fin n)) : List ℕ :=
  (List.range n).filter fun u => decide (∃ hu : u < n, (⟨u, hu⟩ : Fin n) ∈ W)

theorem aggkWindowNames_sorted {n : ℕ} (W : Set (Fin n)) :
    (aggkWindowNames W).SortedLT :=
  ((List.sortedLT_range _).pairwise.sublist (List.filter_sublist)).sortedLT

@[simp] theorem aggkMem_windowNames {n : ℕ} (W : Set (Fin n)) (u : ℕ) :
    u ∈ aggkWindowNames W ↔ ∃ hu : u < n, (⟨u, hu⟩ : Fin n) ∈ W := by
  simp only [aggkWindowNames, List.mem_filter, List.mem_range, decide_eq_true_eq]
  exact ⟨And.right, fun h => ⟨h.choose, h⟩⟩

theorem aggkRawAff_eq_names {n : ℕ} {p : RawAction} (hn : p.1.1.length = n) :
    rawAff p = aggkWindowNames (winSet n (rawAff p)) := by
  apply (aggkRawAff_sorted p).eq_of_mem_iff (aggkWindowNames_sorted _)
  intro u
  rw [aggkMem_windowNames]
  exact ⟨fun hu => ⟨hn ▸ lt_of_mem_rawAff hu, hu⟩, fun ⟨_, hu⟩ => hu⟩

/-- An uncovered point in an increasing scan is the least point of its orbit. -/
theorem aggkLeast_new {n : ℕ} {gs : RawGens} (hgs : RawGens.WF n gs)
    {W tail : List ℕ} {u : ℕ} {A : List (List ℕ)}
    (hW : ∀ v ∈ W, v < n) (hu : u ∈ W)
    (hinv : IsInvariant (decGroup n gs) (winSet n W))
    (htail : ∀ v ∈ tail, u < v)
    (hA : ∀ w ∈ A, ∃ v, v < n ∧ w = rawOrbit (gs, v))
    (hcovered : ∀ v ∈ W, v ∉ u :: tail → v ∈ A.flatten)
    (hnew : u ∉ A.flatten) :
    aggkLeast (winSet n (rawOrbit (gs, u))) = u := by
  have hun := hW u hu
  have horb := winSet_rawOrbit hgs (⟨u, hun⟩ : Fin n)
  have hus : (⟨u, hun⟩ : Fin n) ∈ winSet n (rawOrbit (gs, u)) := by
    rw [horb]; exact mem_orbit_self _
  obtain ⟨v, hv, he⟩ := aggkLeast_mem ⟨_, hus⟩
  have hvle : aggkLeast (winSet n (rawOrbit (gs, u))) ≤ u := aggkLeast_le hus
  have hvW : v.val ∈ W := by
    have hsub := (isInvariant_iff_orbit_subset _ _).mp hinv ⟨u, hun⟩ hu
    exact hsub (horb ▸ hv)
  apply le_antisymm hvle
  by_contra hlt
  have hvlt : v.val < u := by rw [he]; exact Nat.lt_of_not_ge hlt
  have hvnot : v.val ∉ u :: tail := by
    intro hm
    rcases List.mem_cons.mp hm with hm | hm
    · omega
    · have := htail _ hm; omega
  obtain ⟨w, hw, hvw⟩ := List.mem_flatten.mp (hcovered v.val hvW hvnot)
  obtain ⟨a, ha, rfl⟩ := hA w hw
  exact hnew (List.mem_flatten.mpr ⟨_, hw,
    mem_rawOrbit_of_mem_mem hgs hun ha hv hvw⟩)

/-- The least points stay in increasing order throughout the orbit scan. -/
theorem aggkOrbitFold_sorted {n : ℕ} {gs : RawGens} (hgs : RawGens.WF n gs)
    (W : List ℕ) (hW : ∀ v ∈ W, v < n)
    (hinv : IsInvariant (decGroup n gs) (winSet n W)) :
    ∀ (todo : List ℕ), todo.SortedLT → todo ⊆ W → ∀ (A : List (List ℕ)),
    (∀ w ∈ A, ∃ v, v < n ∧ w = rawOrbit (gs, v)) →
    (∀ v ∈ W, v ∉ todo → v ∈ A.flatten) →
    A.Pairwise (fun a b => aggkLeast (winSet n a) < aggkLeast (winSet n b)) →
    (∀ w ∈ A, ∀ v ∈ todo, aggkLeast (winSet n w) < v) →
    (todo.foldl (fun acc u => rawOrbitsStep (gs, acc, u)) A).Pairwise
      (fun a b => aggkLeast (winSet n a) < aggkLeast (winSet n b)) := by
  intro todo
  induction todo with
  | nil => intro _ _ A _ _ hs _; exact hs
  | cons u todo ih =>
    intro hs hsub A hA hc hsorted hb
    have hpair := List.pairwise_cons.mp hs.pairwise
    have hut : u ∈ W := hsub List.mem_cons_self
    have hsubt : todo ⊆ W := fun _ hv => hsub (List.mem_cons_of_mem u hv)
    rw [List.foldl_cons]
    by_cases hnew : u ∈ A.flatten
    · rw [rawOrbitsStep, if_pos hnew]
      apply ih hpair.2.sortedLT hsubt A hA _ hsorted
        (fun w hw v hv => hb w hw v (List.mem_cons_of_mem u hv))
      intro v hv hvt
      by_cases he : v = u
      · simpa [he] using hnew
      · exact hc v hv (by simp [he, hvt])
    · have hleast := aggkLeast_new hgs hW hut hinv hpair.1 hA hc hnew
      rw [rawOrbitsStep, if_neg hnew]
      apply ih hpair.2.sortedLT hsubt
      · intro w hw
        rcases List.mem_append.mp hw with hw | hw
        · exact hA w hw
        · exact ⟨u, hW u hut, List.mem_singleton.mp hw⟩
      · intro v hv hvt
        by_cases he : v = u
        · subst v
          have hum : u ∈ rawOrbit (gs, u) :=
            (mem_rawOrbit_iff hgs (hW u hut) u).mpr ⟨hW u hut, mem_orbit_self _⟩
          simp only [List.flatten_append, List.flatten_cons, List.flatten_nil,
            List.append_nil, List.mem_append]
          exact Or.inr hum
        · have hvA := hc v hv (by simp [he, hvt])
          exact List.mem_flatten.mpr (by
            obtain ⟨w, hw, hvw⟩ := List.mem_flatten.mp hvA
            exact ⟨w, List.mem_append_left _ hw, hvw⟩)
      · rw [List.pairwise_append]
        refine ⟨hsorted, by simp, ?_⟩
        intro w hw v hv
        rw [List.mem_singleton.mp hv, hleast]
        exact hb w hw u List.mem_cons_self
      · intro w hw v hv
        rcases List.mem_append.mp hw with hw | hw
        · exact hb w hw v (List.mem_cons_of_mem u hv)
        · rw [List.mem_singleton.mp hw, hleast]
          exact hpair.1 v hv

/-- With an increasing invariant window, the orbit order is the least-point order. -/
theorem aggkWinOrbits_sorted {n : ℕ} {gs : RawGens} (hgs : RawGens.WF n gs)
    {W : List ℕ} (hW : ∀ v ∈ W, v < n) (hs : W.SortedLT)
    (hinv : IsInvariant (decGroup n gs) (winSet n W)) :
    (((winOrbits (gs, W)).map (winSet n)).map aggkLeast).SortedLT := by
  rw [List.sortedLT_iff_pairwise, List.pairwise_map, List.pairwise_map]
  exact aggkOrbitFold_sorted hgs W hW hinv W hs (fun _ h => h) []
    (by simp) (by simp) (by simp) (by simp)

/-- Covering a window by whole orbits determines which orbit sets occur. -/
theorem aggkOrbitList_mem_iff {n : ℕ} (N : Subgroup (Perm (Fin n))) (W : Set (Fin n))
    (Ds : List (Set (Fin n))) (ho : ∀ Δ ∈ Ds, ∃ u ∈ W, Δ = orbit N u)
    (hc : (⋃ Δ ∈ Ds, Δ) = W) (Δ : Set (Fin n)) :
    Δ ∈ Ds ↔ ∃ u ∈ W, Δ = orbit N u := by
  refine ⟨ho Δ, ?_⟩
  rintro ⟨u, hu, rfl⟩
  rw [← hc] at hu
  obtain ⟨Δ, hΔ, huΔ⟩ := Set.mem_iUnion₂.mp hu
  obtain ⟨v, _, rfl⟩ := ho Δ hΔ
  rw [(orbit_eq_iff).mpr huΔ]
  exact hΔ

section Stage

variable {n m : ℕ} {G : Subgroup (Perm (Fin n))} {ϕ : G →* Perm (Fin m)}
  {xs : RawStr} {tdom : List ℕ} {hc : LCCtxWF n m xs tdom}
  {s : Stage ϕ (decStrN n xs) (winSet m tdom)} {st st' : RawLCSt}

/-- The raw affected list, including its order, is fixed by the decoded stage. -/
theorem aggkAffNew_eq (h : StateFor hc s st) :
    lcAffNew ((xs, tdom), st) = aggkWindowNames s.aff := by
  have he := aggkRawAff_eq_names (p := lcAct ((xs, tdom), st)) hc.lenStr
  change lcAffNew ((xs, tdom), st) = aggkWindowNames (winSet n (lcAffNew _)) at he
  rwa [winSet_lcAffNew h] at he

/-- Both raw lists have the same decoded windows under the stage invariant. -/
theorem aggkStage_windows_congr (h : StateFor hc s st) (h' : StateFor hc s st') :
    (aggrWindows (aggrInputOf ((xs, tdom), st))).map (winSet n) =
      (aggrWindows (aggrInputOf ((xs, tdom), st'))).map (winSet n) := by
  have he : lcAffNew ((xs, tdom), st) = lcAffNew ((xs, tdom), st') :=
    (aggkAffNew_eq h).trans (aggkAffNew_eq h').symm
  apply aggkOrbitFold_congr (wf_lcKer (lcwf_lcInst h)) (wf_lcKer (lcwf_lcInst h'))
    ((aggrKernel_eq h).trans (aggrKernel_eq h').symm)
    (lcAffNew ((xs, tdom), st)) (fun u hu => lt_lcAffNew hc hu) [] [] rfl |>.trans
    (congrArg (fun W => (winOrbits (_, W)).map (winSet n)) he)

/-- The raw orbit windows are exactly the mathematical canonical list. -/
theorem aggkStage_windows_eq (h : StateFor hc s st) :
    (aggrWindows (aggrInputOf ((xs, tdom), st))).map (winSet n) = aggkCanonWindows s := by
  let P := aggrInputOf ((xs, tdom), st)
  let Ds := (aggrWindows P).map (winSet n)
  have hgs : RawGens.WF n (lcKer P.1 P.2.1) := wf_lcKer (lcwf_lcInst h)
  have hlt : ∀ u ∈ P.1.1, u < n := fun u hu => lt_lcAffNew hc hu
  have hinv : IsInvariant (decGroup n (lcKer P.1 P.2.1)) (winSet n P.1.1) := by
    rw [aggrKernel_eq h]
    change IsInvariant (kerN s) (winSet n (lcAffNew ((xs, tdom), st)))
    rw [winSet_lcAffNew h]
    exact (isInvariant_iff_orbit_subset _ _).mpr (fun _ hu => orbit_kerN_subset_aff s hu)
  have hs : (Ds.map aggkLeast).SortedLT :=
    aggkWinOrbits_sorted hgs hlt (aggkRawAff_sorted _) hinv
  have hcover := aggrStage_cover h
  have hbound := aggrStage_bound h
  have hm : ∀ Δ, Δ ∈ Ds ↔ Δ ∈ aggkCanonWindows s := by
    intro Δ
    rw [aggkOrbitList_mem_iff _ _ _ hbound.orbits hcover.windows,
      aggkOrbitList_mem_iff _ _ _ (aggkStage_bound s []).orbits
        (aggkStage_cover s []).windows]
  have hp : Ds.Perm (aggkCanonWindows s) := by
    apply List.perm_of_nodup_nodup_toFinset_eq (List.Nodup.of_map _ hs.nodup)
      (aggkCanonWindows_nodup s)
    ext Δ
    simpa using hm Δ
  apply List.Perm.eq_of_pairwise
    (le := fun a b : Set (Fin n) => aggkLeast a ≤ aggkLeast b)
  · intro a b ha hb hab hba
    obtain ⟨u, _, rfl⟩ := hbound.orbits a ha
    obtain ⟨v, _, rfl⟩ := (aggkStage_bound s []).orbits b hb
    exact aggkOrbit_eq_of_least_eq _ _ _ (le_antisymm hab hba)
  · exact List.pairwise_map.mp hs.sortedLE.pairwise
  · exact List.pairwise_map.mp (aggkCanonWindows_sorted s).pairwise
  · exact hp

end Stage

end Algo
