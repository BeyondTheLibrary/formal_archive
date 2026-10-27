import Workspace.Algo.SplitBipStep5
import Workspace.Algo.SplitComponents

/-!
# Sections 9.4 and 9.6: the first disconnected non-diagonal color

The tests scan positions in the supplied domain. They are total even if the
names or table are malformed. A color must occur and have no diagonal pair.
The last test checks weak connectivity with the component routine.
-/

namespace Algo
open Babai RAM

/-- The pair colors on domain positions, retaining repeats. -/
def sbipColors (p : RawConfig) : List ℕ :=
  (labPairsList p.1).map (fun q => binColor (p,q))

theorem sbipPoly_colors : PolyFun sbipColors :=
  (polyFun_id.pair (polyFun_fst.comp polyFun_labPairsList)).comp
    (PolyFun.mapParam polyFun_binColor)

theorem sbipColors_mem (p : RawConfig) (k : ℕ) :
    k ∈ sbipColors p ↔ ∃ u v : Fin p.1.length, namedBin p.1.length p u v = k := by
  simp only [sbipColors,List.mem_map,Prod.exists,mem_labPairsList]
  constructor
  · rintro ⟨u,v,⟨hu,hv⟩,hc⟩; exact ⟨⟨u,hu⟩,⟨v,hv⟩,hc⟩
  · rintro ⟨u,v,hc⟩; exact ⟨u,v,⟨u.isLt,v.isLt⟩,hc⟩

/-- An off-diagonal color differs from every loop color. -/
def sbipOffTest (z : (RawConfig × ℕ) × ℕ) : Bool :=
  !decide (binColor (z.1.1,(z.2,z.2)) = z.1.2)

theorem sbipPoly_offTest : PolyFun sbipOffTest :=
  polyFun_rawJNot ((((polyFun_fst.comp polyFun_fst).pair
    (polyFun_snd.pair polyFun_snd)).comp polyFun_binColor).natEq
      (polyFun_fst.comp polyFun_snd))

/-- Test all loop colors. -/
def sbipOffDiagonal (z : RawConfig × ℕ) : Bool :=
  upccCaseAllB sbipOffTest (z,List.range z.1.1.length)

theorem sbipPoly_offDiagonal : PolyFun sbipOffDiagonal :=
  (polyFun_id.pair ((polyFun_fst.comp polyFun_fst).comp polyFun_rangeLength)).comp
    (upccCasePoly_all sbipPoly_offTest)

theorem sbipOffDiagonal_spec (p : RawConfig) (k : ℕ) :
    sbipOffDiagonal (p,k) = true ↔ ∀ u : Fin p.1.length, namedBin p.1.length p u u ≠ k := by
  simp only [sbipOffDiagonal,upccCaseAllB_spec,List.mem_range,sbipOffTest,
    Bool.not_eq_true',decide_eq_false_iff_not]
  exact ⟨fun h u => h u u.isLt,fun h u hu => h ⟨u,hu⟩⟩

/-- Every ordered pair lies in a single weak component. -/
def sbipConnected (z : RawConfig × ℕ) : Bool :=
  upccCaseAllB splitComponentTest (z,labPairsList z.1.1)

theorem sbipPoly_connected : PolyFun sbipConnected :=
  (polyFun_id.pair ((polyFun_fst.comp polyFun_fst).comp polyFun_labPairsList)).comp
    (upccCasePoly_all polyFun_splitComponentTest)

theorem sbipConnected_spec (p : RawConfig) (k : ℕ) :
    sbipConnected (p,k) = true ↔
      (colorDigraph (namedBin p.1.length p) k).IsWeaklyConnected := by
  rw [sbipConnected,upccCaseAllB_spec]
  constructor
  · intro h u v
    exact (splitComponentTest_spec (p,k) u v).1 (h (u,v) (mem_labPairsList.2
      ⟨u.isLt,v.isLt⟩))
  · intro h q hq
    obtain ⟨hu,hv⟩ := mem_labPairsList.1 hq
    exact (splitComponentTest_spec (p,k) ⟨q.1,hu⟩ ⟨q.2,hv⟩).2 (h _ _)

/-- Sections 9.4 and 9.6: exactly a disconnected non-diagonal color. -/
def sbipDisconnected (z : RawConfig × ℕ) : Bool :=
  sbipOffDiagonal z && decide (z.2 ∈ sbipColors z.1) && !sbipConnected z

theorem sbipPoly_disconnected : PolyFun sbipDisconnected :=
  polyFun_rawJAnd (polyFun_rawJAnd sbipPoly_offDiagonal
    ((polyFun_snd.pair (polyFun_fst.comp sbipPoly_colors)).comp polyFun_natListMem))
      (polyFun_rawJNot sbipPoly_connected)

theorem sbipDisconnected_spec (p : RawConfig) (k : ℕ) :
    sbipDisconnected (p,k) = true ↔ IsDisconnectedColor (namedBin p.1.length p) k := by
  simp only [sbipDisconnected,Bool.and_eq_true,sbipOffDiagonal_spec,
    decide_eq_true_eq,sbipColors_mem,Bool.not_eq_true',Bool.eq_false_iff,
    ne_eq,sbipConnected_spec,IsDisconnectedColor,and_assoc]

/-- Candidates come from pairs in the input, never from a binary color bound. -/
def sbipDisconnectedColors (p : RawConfig) : List ℕ :=
  (sbipColors p).filter (fun k => sbipDisconnected (p,k))

theorem sbipPoly_disconnectedColors : PolyFun sbipDisconnectedColors :=
  (polyFun_id.pair sbipPoly_colors).comp (PolyFun.filterParam sbipPoly_disconnected)

theorem sbipDisconnectedColors_spec (p : RawConfig) (k : ℕ) :
    k ∈ sbipDisconnectedColors p ↔ IsDisconnectedColor (namedBin p.1.length p) k := by
  simp only [sbipDisconnectedColors,List.mem_filter,sbipDisconnected_spec,sbipColors_mem]
  exact ⟨And.right,fun h => ⟨h.2.1,h⟩⟩

/-- Sections 9.4 and 9.6: the numerically first passing color, or zero. -/
def sbipFirstDisconnected (p : RawConfig) : ℕ := upccCaseLeast (sbipDisconnectedColors p)

theorem sbipPoly_firstDisconnected : PolyFun sbipFirstDisconnected :=
  sbipPoly_disconnectedColors.comp upccCasePoly_least

theorem sbipFirstDisconnected_spec (p : RawConfig) :
    sbipFirstDisconnected p = blockColor (namedBin p.1.length p) :=
  upccCaseLeast_find _ _ (sbipDisconnectedColors_spec p)

/-- The imprimitive branch test. -/
def sbipImprimitive (p : RawConfig) : Bool := !(sbipDisconnectedColors p).isEmpty

theorem sbipPoly_imprimitive : PolyFun sbipImprimitive :=
  polyFun_rawJNot (sbipPoly_disconnectedColors.comp polyFun_isEmpty)

theorem sbipImprimitive_spec (p : RawConfig) :
    sbipImprimitive p = true ↔ ∃ k, IsDisconnectedColor (namedBin p.1.length p) k := by
  simp only [sbipImprimitive,Bool.not_eq_true',Bool.eq_false_iff,ne_eq,List.isEmpty_iff,
    List.eq_nil_iff_forall_not_mem,not_forall,not_not,sbipDisconnectedColors_spec]

/-- Section 9.4, step 6: one color, with the components as blocks. -/
def sbipStep6 (p : RawConfig) : RawLab × RawLab :=
  (p.1.map (fun _ => 0),componentsRaw (p,sbipFirstDisconnected p))

theorem sbipPoly_step6 : PolyFun sbipStep6 :=
  (polyFun_fst.comp (PolyFun.map (polyFun_const 0))).pair
    ((polyFun_id.pair sbipPoly_firstDisconnected).comp polyFun_componentsRaw)

/-- Sections 9.4 and 9.6: the exact component containing a named vertex. -/
theorem sbipStep6_components (p : RawConfig) (u v : Fin p.1.length) :
    LabRel (sbipStep6 p).2 u v ↔ v ∈ blockOf (namedBin p.1.length p) u := by
  change LabRel (componentsRaw _) _ _ ↔ _
  rw [componentsRaw_spec,sbipFirstDisconnected_spec,blockOf,Digraph.weakComponent_eq_weaklyAccessible]
  rfl

/-- Named input to the step-6 scan. The table uses the names of `step6Color`,
which are the ordered names of the restricted configuration from step 5. -/
def SbipStep6Names {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    (X : Pt (BipBlockInputs Ω)) (p : RawConfig)
    (e : ↥(dominantClass X) ≃ Fin p.1.length) : Prop :=
  ∀ u v, namedBin p.1.length p (e u) (e v) = step6Color X u v

/-- Section 9.4, step 6: the raw branch is precisely `Step6Imprimitive`. -/
theorem sbipStep6_iff {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    {X : Pt (BipBlockInputs Ω)} {p : RawConfig}
    (e : ↥(dominantClass X) ≃ Fin p.1.length) (h : SbipStep6Names X p e) :
    sbipImprimitive p = true ↔ Step6Imprimitive X := by
  rw [sbipImprimitive_spec,Step6Imprimitive]
  exact exists_congr (fun k => isDisconnectedColor_map e h k)

/-- Section 9.4, step 6: the first disconnected color has exactly the mathematical name. -/
theorem sbipStep6_color {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    {X : Pt (BipBlockInputs Ω)} {p : RawConfig}
    (e : ↥(dominantClass X) ≃ Fin p.1.length) (h : SbipStep6Names X p e) :
    sbipFirstDisconnected p = blockColor (step6Color X) := by
  rw [sbipFirstDisconnected_spec]
  exact blockColor_map e h

/-- Section 9.4, step 6: read-off of the component partition used in `step6Outcome`. -/
theorem sbipStep6_spec {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    {X : Pt (BipBlockInputs Ω)} {p : RawConfig}
    (e : ↥(dominantClass X) ≃ Fin p.1.length) (h : SbipStep6Names X p e)
    (u v : ↥(dominantClass X)) :
    labAt (sbipStep6 p).1 (e u) = 0 ∧
    (LabRel (sbipStep6 p).2 (e u) (e v) ↔
      (compPartition (dominantClass X) (step6Color X)).part (mkPt u.property) (mkPt v.property)) := by
  constructor
  · simp [sbipStep6,labAt,(e u).isLt]
  · rw [sbipStep6_components,blockOf_map e h,Set.mem_image_equiv]
    simp only [Equiv.symm_apply_apply]
    change v ∈ blockOf (step6Color X) u ↔ _
    change v ∈ blockOf (step6Color X) u ↔ blockOf (step6Color X) u = blockOf (step6Color X) v
    exact ⟨fun hv => ((colorDigraph _ _).weakComponent_eq_of_mem hv).symm,
      fun hv => hv ▸ mem_blockOf_self _ v⟩

/-- The selector is independent of vertex names. -/
theorem sbipFirstDisconnected_congr (p q : RawConfig)
    (e : Fin p.1.length ≃ Fin q.1.length)
    (h : ∀ u v, namedBin q.1.length q (e u) (e v) = namedBin p.1.length p u v) :
    sbipFirstDisconnected q = sbipFirstDisconnected p := by
  rw [sbipFirstDisconnected_spec,sbipFirstDisconnected_spec]
  exact blockColor_map e h

/-- The selected component partition transports along the same naming. -/
theorem sbipStep6_transport (p q : RawConfig)
    (e : Fin p.1.length ≃ Fin q.1.length)
    (h : ∀ u v, namedBin q.1.length q (e u) (e v) = namedBin p.1.length p u v)
    (u v : Fin p.1.length) :
    LabRel (sbipStep6 q).2 (e u) (e v) ↔ LabRel (sbipStep6 p).2 u v := by
  rw [sbipStep6_components,sbipStep6_components,blockOf_map e h,Set.mem_image_equiv,
    Equiv.symm_apply_apply]

end Algo
