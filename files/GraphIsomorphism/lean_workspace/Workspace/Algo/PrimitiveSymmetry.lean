import Workspace.Algo.PrimitiveHypergraph
import Workspace.Algo.WFTests
import Workspace.Master.KAryOfString

/-! # Section 15, line 4b: testing the symmetry defect

Two vertices are twins when their transposition preserves every edge color.
The primitive hypergraph table contains every edge, so a scan of its rows
tests this condition. Counting each twin class then tests whether one has
more than half the vertices. This is the test in version 2.5, Section 15,
line 4b, using Definitions 2.3.9 and 2.3.13.

The routines have polynomial RAM bounds on all inputs. On a valid primitive
action they compute the paper's defect test and its canonical two-coloring.
All loops use lengths of stored lists.
-/

namespace Algo
open Babai RAM RAM.Targets
open Equiv (Perm)

/-- Check the color of one edge after swapping two top-domain vertices. -/
def primitiveSwapTest (z : ((RawAction × RawStr) × (ℕ × ℕ)) × ℕ) : Bool :=
  decide ((primitiveHyperColor (z.1.1,
    splitSwapRow ((z.1.1.1.2.1, rawTpoint (z.1.1.1, z.2)), z.1.2))).getD 0 =
      z.1.1.2.getD z.2 0)

/-- Definition 2.3.9 for the edge-colored hypergraph of Section 15. -/
def primitiveTwinTest (z : (RawAction × RawStr) × (ℕ × ℕ)) : Bool :=
  wftAll primitiveSwapTest (z, List.range z.1.1.1.1.length)

/-- List the twin class of a top-domain vertex, including the vertex itself. -/
def primitiveTwinClass (z : (RawAction × RawStr) × ℕ) : List ℕ :=
  relationClassRaw primitiveTwinTest ((z.1, z.1.1.2.1), z.2)

/-- Section 15, line 4b: mark vertices whose twin class has more than half the points. -/
def primitiveBigTwin (z : (RawAction × RawStr) × ℕ) : Bool :=
  decide (z.1.1.2.1.length < 2 * (primitiveTwinClass z).length)

/-- Section 15, line 4b: the relative symmetry defect is below one half. -/
def primitiveSmallDefect (p : RawAction × RawStr) : Bool :=
  !((List.range p.1.2.1.length).filter (fun u => primitiveBigTwin (p, u))).isEmpty

/-- The dominant twin class, or the empty list when no class is that large. -/
def primitiveDominantClass (p : RawAction × RawStr) : List ℕ :=
  (List.range p.1.2.1.length).filter (fun u => primitiveBigTwin (p, u))

theorem polyFun_primitiveSwapTest : PolyFun primitiveSwapTest := by
  let Z := ((RawAction × RawStr) × (ℕ × ℕ)) × ℕ
  have hp : PolyFun (fun z : Z => z.1.1) := polyFun_fst.comp polyFun_fst
  have ha := hp.comp polyFun_fst
  have hd := (ha.comp polyFun_snd).comp polyFun_fst
  have hr := (ha.pair polyFun_snd).comp polyFun_rawTpoint
  have hs := ((hd.pair hr).pair (polyFun_fst.comp polyFun_snd)).comp polyFun_splitSwapRow
  have hc := (((hp.pair hs).comp polyFun_primitiveHyperColor).pair
    (polyFun_const 0)).comp polyFun_optionGetD
  exact hc.natEq ((((hp.comp polyFun_snd).pair polyFun_snd).pair
    (polyFun_const 0)).comp polyFun_getD)

theorem polyFun_primitiveTwinTest : PolyFun primitiveTwinTest :=
  (polyFun_id.pair ((((polyFun_fst.comp polyFun_fst).comp polyFun_fst).comp
    polyFun_fst).comp polyFun_rangeLength)).comp (wftPolyFun_all polyFun_primitiveSwapTest)

theorem polyFun_primitiveTwinClass : PolyFun primitiveTwinClass := by
  have hd : PolyFun (fun z : (RawAction × RawStr) × ℕ => z.1.1.2.1) :=
    ((polyFun_fst.comp polyFun_fst).comp polyFun_snd).comp polyFun_fst
  exact ((polyFun_fst.pair hd).pair polyFun_snd).comp
    (polyFun_relationClassRaw polyFun_primitiveTwinTest)

theorem polyFun_primitiveBigTwin : PolyFun primitiveBigTwin := by
  have hd : PolyFun (fun z : (RawAction × RawStr) × ℕ => z.1.1.2.1.length) :=
    (((polyFun_fst.comp polyFun_fst).comp polyFun_snd).comp polyFun_fst).comp polyFun_length
  have hs := polyFun_primitiveTwinClass.comp polyFun_length
  exact (((hs.add hs).pair hd).comp wftPolyFun_lt).of_eq (fun z => by
    simp only [wftLt, primitiveBigTwin, two_mul])

theorem polyFun_primitiveSmallDefect : PolyFun primitiveSmallDefect := by
  have hd : PolyFun (fun p : RawAction × RawStr => List.range p.1.2.1.length) :=
    ((polyFun_fst.comp polyFun_snd).comp polyFun_fst).comp polyFun_rangeLength
  exact wftPolyFun_not (((polyFun_id.pair hd).comp
    (PolyFun.filterParam polyFun_primitiveBigTwin)).comp polyFun_isEmpty)

theorem polyFun_primitiveDominantClass : PolyFun primitiveDominantClass := by
  have hd : PolyFun (fun p : RawAction × RawStr => List.range p.1.2.1.length) :=
    ((polyFun_fst.comp polyFun_snd).comp polyFun_fst).comp polyFun_rangeLength
  exact (polyFun_id.pair hd).comp (PolyFun.filterParam polyFun_primitiveBigTwin)

theorem nodup_primitiveDominantClass (p : RawAction × RawStr) :
    (primitiveDominantClass p).Nodup := List.Nodup.filter _ List.nodup_range

theorem length_primitiveDominantClass_le (p : RawAction × RawStr) :
    (primitiveDominantClass p).length ≤ p.1.2.1.length := by
  exact (List.length_filter_le _ _).trans_eq List.length_range

/-- The raw transposition sends a decoded subset to its image. -/
theorem winSet_splitSwapRow {m : ℕ} (dom row : List ℕ) (hd : dom.length = m)
    (u v : Fin m) :
    winSet m (splitSwapRow ((dom, row), ((u : ℕ), (v : ℕ)))) =
      Equiv.swap u v '' winSet m row := by
  ext w
  simp only [mem_winSet, splitSwapRow, List.mem_filter, List.mem_range, hd,
    w.isLt, true_and, decide_eq_true_eq, swapPointRaw_spec]
  constructor
  · intro h
    exact ⟨Equiv.swap u v w, h, by simp⟩
  · rintro ⟨a, ha, rfl⟩
    simpa using ha

section Specification

variable {n m t : ℕ} {gens : List (Perm (Fin n))} {imgs : List (Perm (Fin m))}
    {ϕ : genGroup gens →* Perm (Fin m)} {dom gdom : List ℕ}
    (hd : dom.length = n) (hg : gdom.length = m) (hI : ImgsOf gens imgs ϕ)
    (hϕ : IsGiantRep ϕ) (hk : VeryLargeK m (maxOrbitLength (genGroup gens)))
    (id : PrimitiveCaseId ϕ t)

local notation "act" => ((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m)))

include hd hg hI hϕ hk id

/-- Each check compares the two colors in the definition of `colorAut`. -/
theorem primitiveSwapTest_spec (x : RawStr) (u v : Fin m) (j : Fin n) :
    primitiveSwapTest (((act, x), ((u : ℕ), (v : ℕ))), (j : ℕ)) = true ↔
      hyperColoring id (decStrN n x) (tAction t (Equiv.swap u v) (id.label j)) =
        hyperColoring id (decStrN n x) (id.label j) := by
  have hr : winSet m (rawTpoint (act, j)) = (id.label j : Finset (Fin m)) :=
    primitiveHyperRow_label hd hg hI hϕ hk id x j
  have hs : winSet m (splitSwapRow ((gdom, rawTpoint (act, j)), ((u : ℕ), (v : ℕ)))) =
      (tAction t (Equiv.swap u v) (id.label j) : Finset (Fin m)) := by
    rw [winSet_splitSwapRow _ _ hg, hr]
    simp only [tAction_apply_coe, Finset.coe_image]
  have hc := primitiveHyperColor_spec hd hg hI hϕ hk id x _ _ hs
  simp only [primitiveSwapTest, hc, Option.getD_some, decide_eq_true_eq]
  simp only [hyperColoring, Equiv.symm_apply_apply, decStrN]

/-- The complete edge scan tests exactly the twin-or-equal relation. -/
theorem primitiveTwinTest_spec (x : RawStr) (u v : Fin m) :
    primitiveTwinTest ((act, x), ((u : ℕ), (v : ℕ))) = true ↔
      TwinOrEq (colorAut t (hyperColoring id (decStrN n x))) u v := by
  have he : primitiveTwinTest ((act, x), ((u : ℕ), (v : ℕ))) = true ↔
      Equiv.swap u v ∈ colorAut t (hyperColoring id (decStrN n x)) := by
    rw [primitiveTwinTest, wftAll_eq_true_iff, mem_colorAut]
    constructor
    · intro h T
      obtain ⟨j, rfl⟩ := id.label.surjective T
      exact (primitiveSwapTest_spec hd hg hI hϕ hk id x u v j).mp
        (h j (List.mem_range.mpr (by simpa only [hd] using j.isLt)))
    · intro h j hj
      have hjn : j < n := by simpa only [List.mem_range, hd] using hj
      exact (primitiveSwapTest_spec hd hg hI hϕ hk id x u v ⟨j, hjn⟩).mpr (h _)
  rw [he]
  by_cases huv : u = v
  · subst v
    exact ⟨fun _ => Or.inl rfl, fun _ => by
      simpa only [Equiv.swap_self] using (colorAut t (hyperColoring id (decStrN n x))).one_mem⟩
  · simp [TwinOrEq, IsTwin, huv]

/-- The raw count is the size of the paper's twin class. -/
theorem primitiveTwinClass_length (x : RawStr) (u : Fin m) :
    (primitiveTwinClass ((act, x), (u : ℕ))).length =
      (twinClass (colorAut t (hyperColoring id (decStrN n x))) u).ncard := by
  have hh := ncard_eq_length_filter (List.range gdom.length) List.nodup_range
    (fun a ha => (by simpa only [List.mem_range, hg] using ha : a < m))
    (fun v => primitiveTwinTest ((act, x), ((u : ℕ), v)))
  have he : {v : Fin m | (v : ℕ) ∈ List.range gdom.length ∧
      primitiveTwinTest ((act, x), ((u : ℕ), (v : ℕ))) = true} =
      twinClass (colorAut t (hyperColoring id (decStrN n x))) u := by
    ext v
    simp only [Set.mem_setOf_eq, List.mem_range, hg, v.isLt, true_and,
      primitiveTwinTest_spec hd hg hI hϕ hk id, twinClass]
  rw [he] at hh
  exact hh.symm

/-- Section 15, line 4b: the exact canonical coloring consumed by Corollary 12.0.10. -/
theorem primitiveBigTwin_spec (x : RawStr) (u : Fin m) :
    primitiveBigTwin ((act, x), (u : ℕ)) = bigTwinColoring id (decStrN n x) u := by
  apply Bool.eq_iff_iff.mpr
  rw [bigTwinColoring_eq_true]
  simp only [primitiveBigTwin, hg, decide_eq_true_eq,
    primitiveTwinClass_length hd hg hI hϕ hk id]

/-- The emitted list is exactly the `true` color class used by line 4b. -/
theorem primitiveDominantClass_spec (x : RawStr) :
    winSet m (primitiveDominantClass (act, x)) =
      {u | bigTwinColoring id (decStrN n x) u = true} := by
  ext u
  simp only [mem_winSet, primitiveDominantClass, List.mem_filter, List.mem_range,
    hg, u.isLt, true_and, primitiveBigTwin_spec hd hg hI hϕ hk id, Set.mem_setOf_eq]

end Specification

/-- Definition 2.3.13: a twin class larger than half the domain gives defect below one half. -/
theorem smallDefect_iff_dominant_twinClass {m : ℕ} (K : Subgroup (Perm (Fin m))) :
    defect K < 1 / 2 ↔ ∃ u : Fin m, m < 2 * (twinClass K u).ncard := by
  constructor
  · exact exists_dominant_twinClass
  · rintro ⟨u, hu⟩
    have hm : 0 < m := Nat.zero_lt_of_lt u.isLt
    have hs : (twinClass K u).ncard ≤ symmetricity K := by
      classical
      have hh := le_symmetricity (Ψ := (twinClass K u).toFinset)
        (by simpa only [Set.coe_toFinset] using twinClass_isTwinSet K u)
      rwa [← Set.ncard_coe_finset, Set.coe_toFinset] at hh
    have hmq : (0 : ℚ) < (m : ℚ) := by exact_mod_cast hm
    have hsq : (m : ℚ) < 2 * (symmetricity K : ℚ) := by exact_mod_cast (by omega : m < 2 * symmetricity K)
    rw [defect, relSymmetricity, Fintype.card_fin]
    have hh : (1 : ℚ) / 2 < (symmetricity K : ℚ) / m :=
      (lt_div_iff₀ hmq).mpr (by linarith)
    linarith

/-- Section 15, line 4b: the polynomial test is exactly the relative-defect test. -/
theorem primitiveSmallDefect_spec {n m t : ℕ} {gens : List (Perm (Fin n))}
    {imgs : List (Perm (Fin m))} {ϕ : genGroup gens →* Perm (Fin m)}
    {dom gdom : List ℕ} (hd : dom.length = n) (hg : gdom.length = m)
    (hI : ImgsOf gens imgs ϕ) (hϕ : IsGiantRep ϕ)
    (hk : VeryLargeK m (maxOrbitLength (genGroup gens))) (id : PrimitiveCaseId ϕ t)
    (x : RawStr) :
    primitiveSmallDefect ((((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m))), x)) = true ↔
      defect (colorAut t (hyperColoring id (decStrN n x))) < 1 / 2 := by
  rw [smallDefect_iff_dominant_twinClass]
  simp only [primitiveSmallDefect, Bool.not_eq_true', List.isEmpty_eq_false_iff_exists_mem,
    List.mem_filter]
  constructor
  · rintro ⟨u, hu, hb⟩
    have hum : u < m := by simpa only [List.mem_range, hg] using hu
    refine ⟨⟨u, hum⟩, ?_⟩
    exact bigTwinColoring_eq_true.mp
      ((primitiveBigTwin_spec hd hg hI hϕ hk id x ⟨u, hum⟩) ▸ hb)
  · rintro ⟨u, hu⟩
    refine ⟨u, List.mem_range.mpr (by simpa only [hg] using u.isLt), ?_⟩
    rw [primitiveBigTwin_spec hd hg hI hϕ hk id x u, bigTwinColoring_eq_true]
    exact hu

end Algo

#print axioms Algo.polyFun_primitiveSmallDefect
#print axioms Algo.primitiveSmallDefect_spec
#print axioms Algo.primitiveBigTwin_spec
