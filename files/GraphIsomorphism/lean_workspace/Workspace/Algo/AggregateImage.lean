import Workspace.Algo.AggregateRaw
import Workspace.Algo.TopOrbits

/-! # The action of the aggregate group and its fixed points (§13.2)

The store gives `F` on `Ω`. The original action supplies its image on `Γ`.
The fixed points are the set `D` used by case (3) and lines 6–7 of the Master Algorithm.
-/
namespace Algo
open RAM RAM.Targets
open Equiv (Perm)

/-- Map a subgroup's generators through the given action, then shorten them. -/
def aggImage (p : RawAction × RawGens) : RawGens :=
  tidyGens (p.1.2.1, p.2.map (fun g => normPerm (p.1.2.1, rawImgOf (p.1, g))))

theorem aggPolyFun_image : PolyFun aggImage := by
  have hd : PolyFun (fun p : RawAction × RawGens => p.1.2.1) :=
    (polyFun_fst.comp polyFun_snd).comp polyFun_fst
  have he : PolyFun (fun z : RawAction × RawPerm =>
      normPerm (z.1.2.1, rawImgOf z)) :=
    (((polyFun_fst.comp polyFun_snd).comp polyFun_fst).pair polyFun_rawImgOf).comp
      polyFun_normPerm
  exact ((hd.pair (PolyFun.mapParam he)).comp polyFun_tidyGens).of_eq (fun _ => rfl)

theorem aggSize_image (p : RawAction × RawGens) :
    Enc.size (aggImage p) ≤ gensBound p.1.2.1.length :=
  size_gens_le' (le_refl _) (wf_tidyGens rfl _) (length_tidyGens rfl _)

/-- The image calculation agrees with `Babai.imgPhi` (Notation 13.1.1). -/
theorem aggImage_spec {n m : ℕ} {dom gdom : List ℕ}
    {gens : List (Perm (Fin n))} {imgs : List (Perm (Fin m))}
    {ϕ : genGroup gens →* Perm (Fin m)} {gs : RawGens}
    (hd : dom.length = n) (hm : gdom.length = m) (hi : ImgsOf gens imgs ϕ)
    (hwf : RawGens.WF n gs) (hle : decGroup n gs ≤ genGroup gens) :
    decGroup m (aggImage (((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m))), gs)) =
      Babai.imgPhi ϕ hle := by
  let act : RawAction := ((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m)))
  let ys := gs.map (fun g => normPerm (gdom, rawImgOf (act, g)))
  have hi' : ImgsOf (gs.map (decPerm n)) (ys.map (decPerm m)) (Babai.phiOn ϕ hle) := by
    refine ⟨by simp [ys], ?_⟩
    intro i hi₁ hi₂
    have hil : i < gs.length := by simpa using hi₁
    have hmem := List.getElem_mem hil
    have hσ : decPerm n gs[i] ∈ genGroup gens :=
      hle (Subgroup.subset_closure (List.mem_map_of_mem hmem))
    have hv := rawImgOf_spec hd hm hi hσ
    rw [encPerm_decPerm (hwf _ hmem)] at hv
    simp only [ys, List.getElem_map, decPerm_normPerm hm]
    rw [show rawImgOf (act, gs[i]) = encPerm m (ϕ ⟨decPerm n gs[i], hσ⟩) from hv,
      decPerm_encPerm]
    rfl
  rw [aggImage, decGroup_tidyGens hm]
  exact hi'.range_eq_genGroup.symm

/-- §13.2: `F^Γ`, from the original action and the completed store. -/
def aggFGamma (p : RawAction × RawAggStore) : RawGens :=
  aggImage (p.1, rawF (p.1.1.1, p.2))

theorem aggPolyFun_FGamma : PolyFun aggFGamma :=
  (polyFun_fst.pair
    ((((polyFun_fst.comp polyFun_fst).comp polyFun_fst).pair polyFun_snd).comp
      aggPolyFun_F)).comp aggPolyFun_image

theorem aggSize_FGamma (p : RawAction × RawAggStore) :
    Enc.size (aggFGamma p) ≤ gensBound p.1.2.1.length := aggSize_image _

/-- The computed action is exactly `Babai.bigFGamma` of Theorem 13.2.1. -/
theorem aggFGamma_spec {n m t : ℕ} {dom gdom : List ℕ}
    {gens : List (Perm (Fin n))} {imgs : List (Perm (Fin m))}
    {ϕ : genGroup gens →* Perm (Fin m)} {x : Fin n → ℕ} {store : RawAggStore}
    (hd : dom.length = n) (hm : gdom.length = m) (hi : ImgsOf gens imgs ϕ)
    (hs : AggStoreFor ϕ x t store) (hall : AggComplete m t store) :
    decGroup m (aggFGamma (((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m))), store)) =
      Babai.bigFGamma ϕ x t := by
  have hF := aggF_spec hd hs hall
  have hle : decGroup n (rawF (dom, store)) ≤ genGroup gens := by
    rw [hF]; exact Babai.bigF_le
  unfold aggFGamma
  dsimp only
  rw [aggImage_spec hd hm hi (show RawGens.WF n (rawF (dom, store)) from wf_tidyGens hd _) hle]
  unfold Babai.imgPhi Babai.bigFGamma
  ext b
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨⟨a.val, hF ▸ a.property⟩, rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨⟨a.val, hF.symm ▸ a.property⟩, rfl⟩

/-- Test whether all listed generators fix a point. -/
def aggFixTest (p : RawGens × ℕ) : Bool :=
  (p.1.filter (fun g => decide (rawApply (g, p.2) ≠ p.2))).isEmpty

/-- §13.2, case (3): the list of fixed points `D`. -/
def aggFixed (p : List ℕ × RawGens) : List ℕ :=
  (List.range p.1.length).filter (fun u => aggFixTest (p.2, u))

theorem aggPolyFun_fixTest : PolyFun aggFixTest := by
  have ht : PolyFun (fun z : ℕ × RawPerm => decide (rawApply (z.2, z.1) = z.1)) :=
    (((polyFun_snd.pair polyFun_fst).comp polyFun_rawApply).pair polyFun_fst).comp
      polyFun_natEq
  have hn : PolyFun (fun z : ℕ × RawPerm => decide (rawApply (z.2, z.1) ≠ z.1)) :=
    (PolyFun.ite ht (polyFun_const false) (polyFun_const true)).of_eq
      (fun z => by by_cases h : rawApply (z.2, z.1) = z.1 <;> simp [h])
  exact (((polyFun_snd.pair polyFun_fst).comp (PolyFun.filterParam hn)).comp
    polyFun_isEmpty).of_eq (fun _ => rfl)

theorem aggPolyFun_fixed : PolyFun aggFixed :=
  (((polyFun_snd.pair (polyFun_fst.comp polyFun_rangeLength)).comp
    (PolyFun.filterParam aggPolyFun_fixTest))).of_eq (fun _ => rfl)

theorem aggFixTest_spec {m : ℕ} {gs : RawGens} (hwf : RawGens.WF m gs) (u : Fin m) :
    aggFixTest (gs, u.val) = true ↔ ∀ g ∈ decGroup m gs, g u = u := by
  have ht : aggFixTest (gs, u.val) = true ↔ ∀ r ∈ gs, decPerm m r u = u := by
    simp only [aggFixTest, List.isEmpty_iff, List.filter_eq_nil_iff, decide_eq_true_eq,
      not_not]
    constructor
    · intro h r hr
      apply Fin.ext
      simpa only [rawApply_of_wf (hwf r hr) u.isLt, Fin.eta] using h r hr
    · intro h r hr
      rw [rawApply_of_wf (hwf r hr) u.isLt, Fin.eta, h r hr]
  rw [ht]
  constructor
  · intro h
    have hs : decGroup m gs ≤ MulAction.stabilizer (Perm (Fin m)) u := by
      apply (Subgroup.closure_le _).2
      intro g hg
      obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hg
      exact h r hr
    exact fun g hg => hs hg
  · intro h r hr
    exact h _ (Subgroup.subset_closure (List.mem_map_of_mem hr))

theorem aggFixed_spec {m : ℕ} {dom : List ℕ} {gs : RawGens}
    (hd : dom.length = m) (hwf : RawGens.WF m gs) :
    winSet m (aggFixed (dom, gs)) = Babai.fixedSet (decGroup m gs) := by
  ext u
  simp only [winSet, Set.mem_setOf_eq, aggFixed, List.mem_filter, List.mem_range, hd]
  exact (and_iff_right u.isLt).trans (aggFixTest_spec hwf u)

theorem aggSize_fixed (p : List ℕ × RawGens) : Enc.size (aggFixed p) ≤ strBound p.1.length :=
  size_natList_le ((List.length_filter_le _ _).trans (List.length_range).le)
    (fun _ hu => List.mem_range.1 (List.mem_filter.1 hu).1)

/-- Directly read the set used by lines 6–7 from the aggregate store. -/
def aggFixedGamma (p : RawAction × RawAggStore) : List ℕ :=
  aggFixed (p.1.2.1, aggFGamma p)

theorem aggPolyFun_fixedGamma : PolyFun aggFixedGamma :=
  ((((polyFun_fst.comp polyFun_snd).comp polyFun_fst).pair aggPolyFun_FGamma).comp
    aggPolyFun_fixed).of_eq (fun _ => rfl)

theorem aggSize_fixedGamma (p : RawAction × RawAggStore) :
    Enc.size (aggFixedGamma p) ≤ strBound p.1.2.1.length := aggSize_fixed _

/-- The non-fullness-side data matched here is `Babai.fixedGamma`. -/
theorem aggFixedGamma_spec {n m t : ℕ} {dom gdom : List ℕ}
    {gens : List (Perm (Fin n))} {imgs : List (Perm (Fin m))}
    {ϕ : genGroup gens →* Perm (Fin m)} {x : Fin n → ℕ} {store : RawAggStore}
    (hd : dom.length = n) (hm : gdom.length = m) (hi : ImgsOf gens imgs ϕ)
    (hs : AggStoreFor ϕ x t store) (hall : AggComplete m t store) :
    winSet m (aggFixedGamma (((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m))), store)) =
      Babai.fixedGamma ϕ x t := by
  unfold aggFixedGamma
  dsimp only
  have hw : RawGens.WF m (aggFGamma
      (((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m))), store)) :=
    wf_tidyGens hm _
  rw [aggFixed_spec hm hw, aggFGamma_spec hd hm hi hs hall]
  rfl

/-- Keep exactly the non-full entries, with their `M(T)` generators. -/
def aggNonfull (store : RawAggStore) : RawAggStore := store.filter (fun e => !e.2.1)

theorem aggPolyFun_nonfull : PolyFun aggNonfull :=
  PolyFun.filter ((PolyFun.ite (polyFun_snd.comp polyFun_fst)
    (polyFun_const false) (polyFun_const true)).of_eq
      (fun e => by cases e.2.1 <;> rfl))

theorem aggNonfull_spec {n m t : ℕ} {G : Subgroup (Perm (Fin n))}
    {ϕ : G →* Perm (Fin m)} {x : Fin n → ℕ} {store : RawAggStore}
    (hs : AggStoreFor ϕ x t store) (e : RawAggCert) :
    e ∈ aggNonfull store ↔ e ∈ store ∧ ¬ Babai.IsFull ϕ x (winSet m e.1) := by
  simp only [aggNonfull, List.mem_filter, Bool.not_eq_true']
  constructor
  · rintro ⟨he, hf⟩
    exact ⟨he, fun h => by have := (hs.2 e he).full.2 h; simp_all⟩
  · rintro ⟨he, hf⟩
    refine ⟨he, ?_⟩
    cases hb : e.2.1
    · rfl
    · exact (hf ((hs.2 e he).full.1 hb)).elim

end Algo
