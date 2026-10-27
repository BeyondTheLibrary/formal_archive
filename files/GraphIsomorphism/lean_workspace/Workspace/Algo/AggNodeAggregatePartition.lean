import Workspace.Algo.AggNodeAggregateTests
import Workspace.Algo.SplitUpccCaseSpec
import Workspace.Algo.AlignStruct
import Workspace.Master.Line567a

/-! # The colored partition returned by Section 13.2, Case 1

Fixed points form one block and one color. Moved points have the other
color, and their blocks are the orbits. Numeric block labels use the least
point of each orbit. Only equality of block labels is part of the output
structure, so these numeric names do not affect its canonicity.
-/
set_option synthInstance.maxSize 1024
set_option maxHeartbeats 1000000
namespace Algo
open RAM RAM.Targets Babai Equiv MulAction
open scoped Classical

/-- The least point of an orbit, using a finite polynomial scan. -/
def aggnOrbitLabel (p : RawGens × ℕ) : ℕ := upccCaseLeast (rawOrbit p)

theorem aggnPolyFun_orbitLabel : PolyFun aggnOrbitLabel := polyFun_rawOrbit.comp upccCasePoly_least

def aggnOrbitColor (p : RawGens × ℕ) : ℕ := if aggFixTest p then 1 else 0

def aggnOrbitBlock (p : RawGens × ℕ) : ℕ := if aggFixTest p then 0 else aggnOrbitLabel p

def aggnOrbitPartition (p : List ℕ × RawGens) : RawColPart :=
  ((List.range p.1.length).map (fun u => aggnOrbitColor (p.2, u)),
    (List.range p.1.length).map (fun u => aggnOrbitBlock (p.2, u)))

theorem aggnPolyFun_orbitColor : PolyFun aggnOrbitColor :=
  PolyFun.ite aggPolyFun_fixTest (polyFun_const 1) (polyFun_const 0)

theorem aggnPolyFun_orbitBlock : PolyFun aggnOrbitBlock :=
  PolyFun.ite aggPolyFun_fixTest (polyFun_const 0) aggnPolyFun_orbitLabel

theorem aggnPolyFun_orbitPartition : PolyFun aggnOrbitPartition :=
  ((polyFun_snd.pair (polyFun_fst.comp polyFun_rangeLength)).comp
    (PolyFun.mapParam aggnPolyFun_orbitColor)).pair
  ((polyFun_snd.pair (polyFun_fst.comp polyFun_rangeLength)).comp
    (PolyFun.mapParam aggnPolyFun_orbitBlock))

theorem aggnOrbitPartition_wf {m : ℕ} {dom : List ℕ} (hd : dom.length = m) (gs : RawGens) :
    RawColPart.WF m (aggnOrbitPartition (dom, gs)) := by
  simp only [RawColPart.WF, aggnOrbitPartition, List.length_map, List.length_range, hd, and_self]

theorem aggnOrbitLabel_mem (gs : RawGens) (u : ℕ) :
    aggnOrbitLabel (gs, u) ∈ rawOrbit (gs, u) :=
  (upccCaseLeast_spec _ (List.ne_nil_of_mem (mem_rawOrbit_self gs u))).1

theorem aggnOrbitLabel_eq_iff {m : ℕ} {gs : RawGens} (hw : RawGens.WF m gs) (u v : Fin m) :
    aggnOrbitLabel (gs, u.val) = aggnOrbitLabel (gs, v.val) ↔ v ∈ orbit (decGroup m gs) u := by
  constructor
  · intro he
    have hu := aggnOrbitLabel_mem gs u.val
    have hv := aggnOrbitLabel_mem gs v.val
    rw [he] at hu
    exact ((mem_rawOrbit_iff hw u.isLt v.val).mp
      (mem_rawOrbit_of_mem_mem hw v.isLt u.isLt hv hu)).2
  · intro hv
    have he : orbit (decGroup m gs) v = orbit (decGroup m gs) u := orbit_eq_iff.mpr hv
    have hmem : ∀ k, k ∈ rawOrbit (gs, u.val) ↔ k ∈ rawOrbit (gs, v.val) := by
      intro k
      rw [mem_rawOrbit_iff hw u.isLt, mem_rawOrbit_iff hw v.isLt]
      simp only [he]
    have hu := (upccCaseLeast_spec _ (List.ne_nil_of_mem (mem_rawOrbit_self gs u.val))).2
    have hv := (upccCaseLeast_spec _ (List.ne_nil_of_mem (mem_rawOrbit_self gs v.val))).2
    exact le_antisymm (hu _ ((hmem _).mpr (aggnOrbitLabel_mem gs v.val)))
      (hv _ ((hmem _).mp (aggnOrbitLabel_mem gs u.val)))

private theorem labAt_map_range (f : ℕ → ℕ) {m : ℕ} (u : Fin m) :
    labAt ((List.range m).map f) u.val = f u.val := by
  rw [labAt, List.getD_eq_getElem _ _ (by simpa using u.isLt), List.getElem_map, List.getElem_range]

theorem aggnOrbitPartition_color {m : ℕ} {dom : List ℕ} {gs : RawGens}
    (hd : dom.length = m) (hw : RawGens.WF m gs) (u : Fin m) :
    (decColPartition m (aggnOrbitPartition (dom, gs))).color u =
      cond ((orbitPartition (decGroup m gs)).color u) 1 0 := by
  change labAt ((List.range dom.length).map _) u.val = _
  rw [hd, labAt_map_range]
  have hf : aggFixTest (gs, u.val) = true ↔ u ∈ fixedSet (decGroup m gs) := aggFixTest_spec hw u
  by_cases hu : u ∈ fixedSet (decGroup m gs) <;>
    simp [aggnOrbitColor, orbitPartition, hf, hu]

theorem aggnOrbitPartition_part {m : ℕ} {dom : List ℕ} {gs : RawGens}
    (hd : dom.length = m) (hw : RawGens.WF m gs) (u v : Fin m) :
    (decColPartition m (aggnOrbitPartition (dom, gs))).part u v ↔
      (orbitPartition (decGroup m gs)).part u v := by
  change (labAt (aggnOrbitPartition (dom, gs)).1 u.val, labAt (aggnOrbitPartition (dom, gs)).2 u.val) =
    (labAt (aggnOrbitPartition (dom, gs)).1 v.val, labAt (aggnOrbitPartition (dom, gs)).2 v.val) ↔
    (u ∈ fixedSet (decGroup m gs) ∧ v ∈ fixedSet (decGroup m gs)) ∨ v ∈ orbit (decGroup m gs) u
  have hfu : aggFixTest (gs, u.val) = true ↔ u ∈ fixedSet (decGroup m gs) := aggFixTest_spec hw u
  have hfv : aggFixTest (gs, v.val) = true ↔ v ∈ fixedSet (decGroup m gs) := aggFixTest_spec hw v
  simp only [aggnOrbitPartition, hd, labAt_map_range, aggnOrbitColor, aggnOrbitBlock,
    hfu, hfv, Prod.mk.injEq]
  by_cases hu : u ∈ fixedSet (decGroup m gs) <;> by_cases hv : v ∈ fixedSet (decGroup m gs)
  · simp [hu, hv]
  · have ho : v ∉ orbit (decGroup m gs) u := by
      rw [orbit_eq_singleton_of_mem_fixedSet _ hu]
      intro he
      exact hv (he ▸ hu)
    simp [hu, hv, ho]
  · have ho : v ∉ orbit (decGroup m gs) u := fun ho =>
      not_mem_fixedSet_of_mem_orbit _ hu ho hv
    simp [hu, hv, ho]
  · simpa [hu, hv] using aggnOrbitLabel_eq_iff hw u v

/-- The raw partition is exactly the paper's natural-color partition on the whole domain. -/
theorem aggnOrbitPartition_univ {m : ℕ} {dom : List ℕ} {gs : RawGens}
    (hd : dom.length = m) (hw : RawGens.WF m gs) :
    { color := fun u : ↥(Set.univ : Set (Fin m)) =>
        (decColPartition m (aggnOrbitPartition (dom, gs))).color u.val
      part := Setoid.comap Subtype.val (decColPartition m (aggnOrbitPartition (dom, gs))).part
      part_le_color := fun h => (decColPartition m (aggnOrbitPartition (dom, gs))).part_le_color h :
        ColoredPartition ↥(Set.univ : Set (Fin m)) ℕ } = univColoredPartition (decGroup m gs) := by
  apply ColoredPartition.ext
  · funext u
    exact aggnOrbitPartition_color hd hw u.val
  · ext u v
    exact aggnOrbitPartition_part hd hw u.val v.val

/-- Read a raw whole-domain partition in the outcome category consumed by Align. -/
def aggnDecodePartition (m : ℕ) (P : RawColPart) : Pt (SplitOutcomes (Fin m)) :=
  ⟨Set.univ, Sum.inl
    { color := fun u => (decColPartition m P).color u.val
      part := Setoid.comap Subtype.val (decColPartition m P).part
      part_le_color := fun h => (decColPartition m P).part_le_color h }⟩

theorem aggnDecode_orbitPartition {m : ℕ} {dom : List ℕ} {gs : RawGens}
    (hd : dom.length = m) (hw : RawGens.WF m gs) :
    aggnDecodePartition m (aggnOrbitPartition (dom, gs)) = orbitSplitOutcome (decGroup m gs) := by
  unfold aggnDecodePartition orbitSplitOutcome
  congr 1
  exact congrArg Sum.inl (aggnOrbitPartition_univ hd hw)

theorem aggnOrbitPartition_output {m : ℕ} {dom : List ℕ} {gs : RawGens}
    (hd : dom.length = m) (hw : RawGens.WF m gs) (h : aggnCase1 (dom, gs) = true) :
    IsSplitOutcome (4 / 5 : ℝ) (Set.univ : Set (Fin m))
      (aggnDecodePartition m (aggnOrbitPartition (dom, gs))) := by
  rw [aggnDecode_orbitPartition hd hw]
  exact isSplitOutcome_orbitSplitOutcome _ ((aggnCase1_spec hd hw).mp h)

/-- The actual Case 1 object read from either retained certificate store. -/
def aggnAggregatePartition (z : (AggnPhaseCtx × AggnAggregateState) × Bool) : RawColPart :=
  aggnOrbitPartition (z.1.1.1.2.1, (aggnAggregateData z).2.1)

theorem aggnPolyFun_aggregatePartition : PolyFun aggnAggregatePartition := by
  have hd : PolyFun (fun z : (AggnPhaseCtx × AggnAggregateState) × Bool => z.1.1.1.2.1) :=
    ((((polyFun_fst.comp polyFun_fst).comp polyFun_fst).comp polyFun_snd).comp polyFun_fst)
  exact (hd.pair ((aggnPolyFun_aggregateData.comp polyFun_snd).comp polyFun_fst)).comp
    aggnPolyFun_orbitPartition

theorem aggnAggregatePartition_spec {c n m : ℕ} {C : AggnPhaseCtx} {s : AggnAggregateState}
    {ϕ : decGroup n C.1.1.2 →* Perm (Fin m)}
    (hC : AggnPhaseCtxWF c n m C ϕ) (hs : AggnStoresComplete c ϕ s.1.2.1) (b : Bool) :
    aggnDecodePartition m (aggnAggregatePartition ((C, s), b)) =
      orbitSplitOutcome (bigFGamma ϕ (cond b (decStrN n C.2.2.1) (decStrN n C.2.1)) C.2.2.2.length) := by
  have hw : RawGens.WF m (aggnAggregateData ((C, s), b)).2.1 := wf_tidyGens hC.action.2.1 _
  rw [aggnAggregatePartition, aggnDecode_orbitPartition hC.action.2.1 hw,
    (aggnAggregateData_spec hC hs b).2.1]

theorem aggnAggregatePartition_output {c n m : ℕ} {C : AggnPhaseCtx} {s : AggnAggregateState}
    {ϕ : decGroup n C.1.1.2 →* Perm (Fin m)}
    (hC : AggnPhaseCtxWF c n m C ϕ) (hs : AggnStoresComplete c ϕ s.1.2.1)
    (h : aggnAggregateDispatch (C, s) = 1) :
    IsSplitOutcome (4 / 5 : ℝ) (Set.univ : Set (Fin m))
      (aggnDecodePartition m (aggnAggregatePartition ((C, s), false))) := by
  rw [aggnAggregatePartition_spec hC hs false]
  exact isSplitOutcome_orbitSplitOutcome _ ((aggnAggregateDispatch_spec hC hs).1.mp h)

end Algo
