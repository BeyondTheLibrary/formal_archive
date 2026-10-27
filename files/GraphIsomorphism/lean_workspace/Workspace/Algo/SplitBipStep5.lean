import Workspace.Algo.SplitBipRestrict

/-!
# Section 9.4, step 5: the restricted graph and configuration

The point and block dictionaries stay with the caller. The first color list is
indexed by the old point dictionary. The second is indexed by the old vertex
dictionary. The last table is the hint. These three fields survive restriction.
The decoder reads them along the inclusion of the new carrier and assigns zero
to a block color outside the retained blocks, as `restrictTo` does.
-/

namespace Algo
open Babai RAM

/-- Point colors, block colors, and the hint, in the original dictionaries. -/
abbrev RawSbipDecor := RawLab × RawLab × RawConfig

/-- Refined classes and second part, with original adjacency and decorations. -/
abbrev RawSbipStep5Input := (RawSbipClasses × List ℕ) × (RawConfig × RawSbipDecor)

/-- The restricted configuration and threshold, and the complete decorated graph. -/
abbrev RawSbipStep5Output := (RawConfig × (ℕ × ℕ)) × (RawUpccBip × RawSbipDecor)

/-- Section 9.4, step 5: restrict both the graph and the old WL table to `W₁ ∪ V₂`. -/
def sbipStep5 (r : RawSbipStep5Input) : RawSbipStep5Output :=
  let w := sbipDominant r.1.1
  ((sbipInduced (r.1.1.1.1,w ++ r.1.2),(sbipClassUpdate r.1.1).2),
    (sbipMatrix (r.2.1,(w,r.1.2)),r.2.2))

theorem sbipPoly_step5 : PolyFun sbipStep5 := by
  have hc : PolyFun (fun r : RawSbipStep5Input => r.1.1) := polyFun_fst.comp polyFun_fst
  have hw := hc.comp sbipPoly_dominant
  have hr : PolyFun (fun r : RawSbipStep5Input => r.1.2) := polyFun_fst.comp polyFun_snd
  have ht : PolyFun (fun r : RawSbipStep5Input => r.1.1.1.1) :=
    (hc.comp polyFun_fst).comp polyFun_fst
  have hu := (hc.comp sbipPoly_classUpdate).comp polyFun_snd
  exact (((ht.pair ((hw.pair hr).comp polyFun_append)).comp sbipPoly_induced).pair hu).pair
    ((((polyFun_snd.comp polyFun_fst).pair (hw.pair hr)).comp sbipPoly_matrix).pair
      (polyFun_snd.comp polyFun_snd))

/-- Section 9.4, step 5: exact graph parts and the threshold `alphaNew`. -/
theorem sbipStep5_parts {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    {X : Pt (BipBlockInputs Ω)} {name : ↥X.obj.1.1.V₁ → ℕ} {r : RawSbipStep5Input}
    (h : SbipClassNames X name r.1.1) (hnd : r.1.1.1.2.Nodup)
    (hb : 0 < r.1.1.2.2) (hd : ¬ AllClassesSmall X) :
    (∀ x, name x ∈ (sbipStep5 r).2.1.1 ↔ x.val ∈ dominantClass X) ∧
    (sbipStep5 r).2.1.2.1 = r.1.2 ∧
    (sbipStep5 r).2.1.1.length = (step5Obj X).V₁.ncard ∧
    sbipAlphaValue (sbipStep5 r).1.2 = alphaNew X := by
  exact ⟨sbipDominant_spec h hnd hb hd,rfl,sbipClassUpdate_spec h hnd hb hd⟩

/-- Section 9.4, step 5: every matrix entry is inherited from the original graph. -/
theorem sbipStep5_matrix (r : RawSbipStep5Input)
    (i : Fin (sbipDominant r.1.1).length) (j : Fin r.1.2.length) :
    ((sbipStep5 r).2.1.2.2.getD i []).getD j 0 =
      binColor (r.2.1,((sbipDominant r.1.1)[i],r.1.2[j])) :=
  sbipMatrix_spec _ _ _ i j

/-- Section 9.4, step 5: the configuration keeps the old colors. -/
theorem sbipStep5_table (r : RawSbipStep5Input) {u v : ℕ}
    (hu : u ∈ sbipDominant r.1.1 ++ r.1.2) (hv : v ∈ sbipDominant r.1.1 ++ r.1.2) :
    binColor ((sbipStep5 r).1.1,(u,v)) = binColor (r.1.1.1.1,(u,v)) :=
  sbipInduced_spec _ _ hu hv

section MathematicalFields
variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    (X : Pt (BipBlockInputs Ω)) {r : RawSbipStep5Input}
    (pointName : ↥X.car → ℕ) (blockName : Set ↥X.car → ℕ)

open scoped Classical in
/-- Input contract for the original graph's inherited fields. The block dictionary
also accepts sets outside the blocks so that the hint's zero padding is specified. -/
structure SbipGraphNames : Prop where
  edge : ∀ x : ↥X.car, ∀ B : Set ↥X.car,
    binColor (r.2.1,(pointName x,blockName B)) = if (x,B) ∈ X.obj.1.1.E then 1 else 0
  pointColor : ∀ x, labAt r.2.2.1 (pointName x) = X.obj.1.1.f x
  blockColor : ∀ B ∈ X.obj.1.1.blocks, labAt r.2.2.2.1 (blockName B) = X.obj.1.1.g B
  hint : ∀ A B, binColor (r.2.2.2.2,(blockName A,blockName B)) = X.obj.1.1.h A B

variable {X pointName blockName}

open scoped Classical in
/-- Section 9.4, step 5: all inherited fields agree with `step5Obj` along
`VColBipBlk.incl (step5Set_subset X)`. The block color is zero off its blocks. -/
theorem sbipStep5_fields (h : SbipGraphNames X (r := r) pointName blockName)
    (x : ↥(step5Set X)) (A B : Set ↥(step5Set X)) :
    let inc := VColBipBlk.incl (step5Set_subset X)
    labAt (sbipStep5 r).2.2.1 (pointName (inc x)) = (step5Obj X).f x ∧
    (if inc '' B ∈ X.obj.1.1.blocks then
      labAt (sbipStep5 r).2.2.2.1 (blockName (inc '' B)) else 0) = (step5Obj X).g B ∧
    binColor ((sbipStep5 r).2.2.2.2,(blockName (inc '' A),blockName (inc '' B))) =
      (step5Obj X).h A B := by
  classical
  dsimp only
  refine ⟨h.pointColor _,?_,h.hint _ _⟩
  change (if _ then _ else _) = (if _ then _ else _)
  split <;> rename_i hb
  · exact h.blockColor _ hb
  · rfl

open scoped Classical in
/-- The raw adjacency entry at a pair of retained names is exactly the edge
field of `step5Obj`, with no new adjacency decision in the specification. -/
theorem sbipStep5_edge (h : SbipGraphNames X (r := r) pointName blockName)
    (i : Fin (sbipDominant r.1.1).length) (j : Fin r.1.2.length)
    (x : ↥(step5Set X)) (B : Set ↥(step5Set X))
    (hi : (sbipDominant r.1.1)[i] = pointName (VColBipBlk.incl (step5Set_subset X) x))
    (hj : r.1.2[j] = blockName (VColBipBlk.incl (step5Set_subset X) '' B)) :
    ((sbipStep5 r).2.1.2.2.getD i []).getD j 0 = if (x,B) ∈ (step5Obj X).E then 1 else 0 := by
  classical
  rw [sbipStep5_matrix,hi,hj,h.edge]
  rfl

end MathematicalFields

section NamedConfiguration
variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    (X : Pt (BipBlockInputs Ω)) {n : ℕ} (e : X.obj.1.1.Vtx ≃ Fin n)
    {r : RawSbipStep5Input}

/-- A block keeps its original name under the step-5 restriction. -/
noncomputable def sbipNamedBlock (B : ↥X.obj.1.1.blocks) : ℕ := (e ⟨B.val,Or.inr B.property⟩).val

/-- Name a vertex of the restricted configuration by inclusion in the old one. -/
noncomputable def sbipStep5Name (A : ↥(step5Vtx X)) : ℕ :=
  (e ⟨A.val,step5Vtx_subset_vtx X A.property⟩).val

/-- Section 9.4, step 5: the raw domain is exactly `step5Vtx`. -/
theorem sbipStep5_domain
    (h : SbipClassNames X (sbipNamedPoint X e) r.1.1)
    (hr : sbipNamedBlock X e '' Set.univ = {a | a ∈ r.1.2})
    (hnd : r.1.1.1.2.Nodup) (hb : 0 < r.1.1.2.2) (hd : ¬ AllClassesSmall X) :
    sbipStep5Name X e '' Set.univ = {a | a ∈ (sbipStep5 r).1.1.1} := by
  ext a
  constructor
  · rintro ⟨⟨A,hA⟩,_,rfl⟩
    rcases hA with ⟨x,hx,rfl⟩ | hA
    · exact List.mem_append_left _ ((sbipDominant_spec h hnd hb hd ⟨x,hx.1⟩).2 hx)
    · apply List.mem_append_right
      have hh := Set.mem_image_of_mem (sbipNamedBlock X e) (Set.mem_univ ⟨A,hA⟩)
      rw [hr] at hh
      exact hh
  · intro ha
    rcases List.mem_append.1 ha with ha | ha
    · obtain ⟨x,rfl⟩ := sbipName_surj h (List.mem_of_mem_filter ha)
      have hx := (sbipDominant_spec h hnd hb hd x).1 ha
      exact ⟨⟨{x.val},Or.inl ⟨x.val,hx,rfl⟩⟩,Set.mem_univ _,rfl⟩
    · have hm : a ∈ sbipNamedBlock X e '' Set.univ := by rw [hr]; exact ha
      obtain ⟨B,_,rfl⟩ := hm
      exact ⟨⟨B.val,Or.inr B.property⟩,Set.mem_univ _,rfl⟩

/-- Section 9.4, step 5: the restricted table has exactly the coloring from
which `step5Config` is built. Its decoder is `ofNamedColoring`, as in that definition. -/
theorem sbipStep5_config
    (h : SbipClassNames X (sbipNamedPoint X e) r.1.1)
    (hr : sbipNamedBlock X e '' Set.univ = {a | a ∈ r.1.2})
    (hnd : r.1.1.1.2.Nodup) (hb : 0 < r.1.1.2.2) (hd : ¬ AllClassesSmall X)
    (hc : ∀ A B : X.obj.1.1.Vtx, binColor (r.1.1.1.1,(e A,e B)) =
      VColBipBlk.wlCaseColor X.obj.1.1 A.val B.val) :
    PartitionStructure.ofNamedColoring (fun A B : ↥(step5Vtx X) =>
      binColor ((sbipStep5 r).1.1,(sbipStep5Name X e A,sbipStep5Name X e B))) =
        step5Config X := by
  have hm (A : ↥(step5Vtx X)) : sbipStep5Name X e A ∈ (sbipStep5 r).1.1.1 := by
    have hh := Set.mem_image_of_mem (sbipStep5Name X e) (Set.mem_univ A)
    rw [sbipStep5_domain X e h hr hnd hb hd] at hh
    exact hh
  have he : (fun A B : ↥(step5Vtx X) =>
      binColor ((sbipStep5 r).1.1,(sbipStep5Name X e A,sbipStep5Name X e B))) =
        (fun A B : ↥(step5Vtx X) => VColBipBlk.wlCaseColor X.obj.1.1 A.val B.val) := by
    funext A B
    rw [sbipStep5_table r (hm A) (hm B)]
    exact hc _ _
  rw [he]
  rfl

end NamedConfiguration
/-- Section 9.4, step 5: the whole result transports. Decorations may use a
separate point dictionary, so its transported value is supplied by the caller. -/
theorem sbipStep5_relabel {n : ℕ} {r : RawSbipStep5Input} {π : RawPerm}
    (hp : RawWL.WF n 2 r.1.1.1.1) (he : RawWL.WF n 2 r.2.1)
    (hπ : RawPerm.WF n π) (hl : ∀ a ∈ r.1.1.1.2, a < n)
    (hr : ∀ a ∈ r.1.2, a < n) (decor : RawSbipDecor) :
    sbipStep5 ((sbipRelabelClasses π r.1.1,permList π r.1.2),
      (relabelWL (π,r.2.1),decor)) =
    ((relabelWL (π,(sbipStep5 r).1.1),(sbipStep5 r).1.2),
      ((permList π (sbipStep5 r).2.1.1,permList π (sbipStep5 r).2.1.2.1,
        (sbipStep5 r).2.1.2.2),decor)) := by
  have hw : ∀ a ∈ sbipDominant r.1.1, a < n :=
    fun a ha => hl a (List.mem_of_mem_filter ha)
  have hboth : ∀ a ∈ sbipDominant r.1.1 ++ r.1.2, a < n := by
    intro a ha
    exact (List.mem_append.1 ha).elim (hw a) (hr a)
  unfold sbipStep5
  rw [sbipDominant_relabel hp hπ hl, sbipClassUpdate_relabel hp hπ hl]
  change ((sbipInduced (relabelWL (π,r.1.1.1.1),
    permList π (sbipDominant r.1.1) ++ permList π r.1.2),_),_) = _
  rw [show permList π (sbipDominant r.1.1) ++ permList π r.1.2 =
    permList π (sbipDominant r.1.1 ++ r.1.2) from (List.map_append).symm]
  dsimp only
  rw [sbipInduced_relabel hp hπ hboth,sbipMatrix_relabel he hπ hw hr]
  rfl

/-- Refine the initial table while carrying the original graph. -/
def sbipPrepare (r : RawSbipStep5Input) : RawSbipStep5Input :=
  ((sbipNamedClasses r.1.1,r.1.2),r.2)

theorem sbipPoly_prepare : PolyFun sbipPrepare :=
  ((((polyFun_fst.comp polyFun_fst).comp sbipPoly_namedClasses).pair
    (polyFun_fst.comp polyFun_snd)).pair polyFun_snd)

/-- Section 9.4, steps 3–5: return a partition, or continue with the restricted input. -/
def sbipSteps35 (r : RawSbipStep5Input) :
    (List ℕ × (RawLab × RawLab)) × Option RawSbipStep5Output :=
  let q := sbipPrepare r
  ((q.1.1.1.2,sbipStep4 q.1.1),
    if sbipNoDominant q.1.1 then none else some (sbipStep5 q))

theorem sbipPoly_steps35 : PolyFun sbipSteps35 := by
  have hc := sbipPoly_prepare.comp (polyFun_fst.comp polyFun_fst)
  have ho := PolyFun.ite (hc.comp sbipPoly_noDominant) (polyFun_const none)
    ((sbipPoly_prepare.comp sbipPoly_step5).comp polyFun_some)
  exact ((hc.comp (polyFun_fst.comp polyFun_snd)).pair (hc.comp sbipPoly_step4)).pair ho

/-- Section 9.4: the procedure exits at step 4 exactly on `AllClassesSmall`. -/
theorem sbipSteps35_exit_iff {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    {X : Pt (BipBlockInputs Ω)} {n : ℕ} {e : X.obj.1.1.Vtx ≃ Fin n}
    {r : RawSbipStep5Input} (h : SbipNamedInput X e r.1.1) :
    (sbipSteps35 r).2 = none ↔ AllClassesSmall X := by
  have hh := sbipNamedClasses_noDominant h
  change (if sbipNoDominant (sbipNamedClasses r.1.1) then none else some _) = none ↔ _
  cases he : sbipNoDominant (sbipNamedClasses r.1.1) <;> simp_all

/-- Section 9.4: in the continuation branch the computed threshold and first
part agree with `step5Obj` and `alphaNew`, starting only from the initial table. -/
theorem sbipSteps35_continue {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    {X : Pt (BipBlockInputs Ω)} {n : ℕ} {e : X.obj.1.1.Vtx ≃ Fin n}
    {r : RawSbipStep5Input} (h : SbipNamedInput X e r.1.1) (hd : ¬ AllClassesSmall X) :
    (sbipSteps35 r).2 = some (sbipStep5 (sbipPrepare r)) ∧
    (sbipStep5 (sbipPrepare r)).2.1.1.length = (step5Obj X).V₁.ncard ∧
    sbipAlphaValue (sbipStep5 (sbipPrepare r)).1.2 = alphaNew X := by
  have hh : sbipNoDominant (sbipNamedClasses r.1.1) = false :=
    Bool.eq_false_iff.2 (fun ht => hd ((sbipNamedClasses_noDominant h).1 ht))
  refine ⟨?_,sbipNamedClasses_update h hd⟩
  simp [sbipSteps35,sbipPrepare,hh]

/-- The step-4 data returned by the procedure is the exact mathematical partition. -/
theorem sbipSteps35_partition {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    {X : Pt (BipBlockInputs Ω)} {n : ℕ} {e : X.obj.1.1.Vtx ≃ Fin n}
    {r : RawSbipStep5Input} (h : SbipNamedInput X e r.1.1)
    (x y : ↥X.obj.1.1.V₁) (i j : Fin r.1.1.1.2.length)
    (hi : r.1.1.1.2[i] = sbipNamedPoint X e x)
    (hj : r.1.1.1.2[j] = sbipNamedPoint X e y) :
    labAt (sbipSteps35 r).1.2.1 i = (kerPartition X.obj.1.1.V₁
      (VColBipBlk.wlDiag X.obj.1.1)).color (mkPt x.property) ∧
    (LabRel (sbipSteps35 r).1.2.2 i j ↔ (kerPartition X.obj.1.1.V₁
      (VColBipBlk.wlDiag X.obj.1.1)).part (mkPt x.property) (mkPt y.property)) :=
  sbipStep4_spec (sbipNamedClasses_names h) x y i j hi hj

/-- The continuation's configuration is `step5Config`, with the step-3 names
proved from the initial input rather than assumed for its output. -/
theorem sbipSteps35_config {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    {X : Pt (BipBlockInputs Ω)} {n : ℕ} {e : X.obj.1.1.Vtx ≃ Fin n}
    {r : RawSbipStep5Input} (h : SbipNamedInput X e r.1.1)
    (hr : sbipNamedBlock X e '' Set.univ = {a | a ∈ r.1.2}) (hd : ¬ AllClassesSmall X) :
    PartitionStructure.ofNamedColoring (fun A B : ↥(step5Vtx X) =>
      binColor ((sbipStep5 (sbipPrepare r)).1.1,
        (sbipStep5Name X e A,sbipStep5Name X e B))) = step5Config X := by
  apply sbipStep5_config X e (r := sbipPrepare r) (sbipNamedClasses_names h) hr h.firstNodup h.denominator hd
  intro A B
  have hh := sbipStep3_named X.obj.1.1 e h.table h.initial A B
  rw [VColBipBlk.wlCaseColor,dif_pos ⟨A.property,B.property⟩]
  exact hh

end Algo
