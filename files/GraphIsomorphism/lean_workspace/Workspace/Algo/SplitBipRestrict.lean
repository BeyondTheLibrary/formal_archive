import Workspace.Algo.SplitBipNamed
import Workspace.SplitOrJohnson.Step6

/-!
# Section 9.4: restrictions and the partition returned at step 4

A restriction keeps its old vertex names. Its domain list records exactly the
retained vertices. Colors are inherited, and the decoder closes gaps in their
names with `ofNamedColoring`. No refinement is run by a restriction.
-/

namespace Algo
open Babai RAM

/-- Read a table on a supplied list of keys. -/
def sbipTabulate (z : RawConfig × List (List ℕ)) : List (List ℕ × ℕ) :=
  z.2.map (fun t => (t, tblGet (z.1.2,t)))

theorem sbipPoly_tabulate : PolyFun sbipTabulate := by
  have hf : PolyFun (fun z : RawConfig × List ℕ => (z.2,tblGet (z.1.2,z.2))) :=
    polyFun_snd.pair (((polyFun_fst.comp polyFun_snd).pair polyFun_snd).comp polyFun_tblGet)
  exact PolyFun.mapParam hf

theorem sbipTabulate_get (p : RawConfig) (l : List (List ℕ)) {t : List ℕ}
    (ht : t ∈ l) : tblGet (sbipTabulate (p,l),t) = tblGet (p.2,t) := by
  have hh := lookup_map_key (fun t => tblGet (p.2,t)) (l.map (fun t => (t,0))) t
  simpa [sbipTabulate, List.map_map, ht, tblGet] using congrArg (fun o => o.getD 0) hh

/-- Section 9.4, steps 5 and 7: the table induced on a vertex list. -/
def sbipInduced (z : RawConfig × List ℕ) : RawConfig :=
  (z.2, sbipTabulate (z.1,tuplesOf z.2 2))

theorem sbipPoly_induced : PolyFun sbipInduced :=
  polyFun_snd.pair ((polyFun_fst.pair
    (polyFun_snd.comp ((polyFun_tuplesOf 2).comp polyFun_snd))).comp sbipPoly_tabulate)

/-- Restriction reads the original color on every retained pair. -/
theorem sbipInduced_spec (p : RawConfig) (l : List ℕ) {u v : ℕ}
    (hu : u ∈ l) (hv : v ∈ l) :
    binColor (sbipInduced (p,l),(u,v)) = binColor (p,(u,v)) := by
  apply sbipTabulate_get
  exact (mem_tuplesOf _ _ _).2 ⟨rfl, by simpa using And.intro hu hv⟩

/-- No pair outside the retained domain is written to the table. -/
theorem sbipInduced_keys (p : RawConfig) (l : List ℕ) :
    (sbipInduced (p,l)).2.map Prod.fst = tuplesOf l 2 := by
  simp [sbipInduced,sbipTabulate,List.map_map,Function.comp_def]

/-- Read one matrix row with the supplied column order. -/
def sbipRow (z : (RawConfig × List ℕ) × ℕ) : List ℕ :=
  z.1.2.map (fun v => binColor (z.1.1,(z.2,v)))

theorem sbipPoly_row : PolyFun sbipRow := by
  have hf : PolyFun (fun z : ((RawConfig × List ℕ) × ℕ) × ℕ =>
      binColor (z.1.1.1,(z.1.2,z.2))) :=
    (((polyFun_fst.comp polyFun_fst).comp polyFun_fst).pair
      ((polyFun_fst.comp polyFun_snd).pair polyFun_snd)).comp polyFun_binColor
  exact (polyFun_id.pair (polyFun_fst.comp polyFun_snd)).comp (PolyFun.mapParam hf)

/-- Section 9.4, step 5: the adjacency matrix on the retained ordered parts. -/
def sbipMatrix (z : RawConfig × (List ℕ × List ℕ)) : RawUpccBip :=
  (z.2.1,z.2.2,z.2.1.map (fun u => sbipRow ((z.1,z.2.2),u)))

theorem sbipPoly_matrix : PolyFun sbipMatrix := by
  have hm : PolyFun (fun z : RawConfig × (List ℕ × List ℕ) =>
      z.2.1.map (fun u => sbipRow ((z.1,z.2.2),u))) :=
    (((polyFun_fst.pair (polyFun_snd.comp polyFun_snd)).pair
      (polyFun_snd.comp polyFun_fst)).comp (PolyFun.mapParam sbipPoly_row))
  exact (polyFun_snd.comp polyFun_fst).pair ((polyFun_snd.comp polyFun_snd).pair hm)

/-- Every stored matrix entry is the corresponding parent entry. -/
theorem sbipMatrix_spec (p : RawConfig) (l r : List ℕ)
    (i : Fin l.length) (j : Fin r.length) :
    ((sbipMatrix (p,(l,r))).2.2.getD i []).getD j 0 =
      binColor (p,(l[i],r[j])) := by
  simp [sbipMatrix,sbipRow,List.getD_eq_getElem,i.isLt,j.isLt]

/-- Section 9.4, step 4: colors and blocks of the returned colored partition.
The labels are indexed by positions in the supplied first-part list. -/
def sbipStep4 (r : RawSbipClasses) : RawLab × RawLab :=
  let l := r.1.2.map (fun u => sbipDiag (r.1.1,u))
  (l,l)

theorem sbipPoly_step4 : PolyFun sbipStep4 := by
  have hm : PolyFun (fun r : RawSbipClasses => r.1.2.map (fun u => sbipDiag (r.1.1,u))) :=
    (polyFun_fst.comp polyFun_fst).pair (polyFun_fst.comp polyFun_snd)
      |>.comp (PolyFun.mapParam sbipPoly_diag)
  exact hm.pair hm

@[simp] theorem sbipStep4_lengths (r : RawSbipClasses) :
    (sbipStep4 r).1.length = r.1.2.length ∧ (sbipStep4 r).2.length = r.1.2.length := by
  simp [sbipStep4]

/-- Section 9.4, step 4: exact read-off of the `kerPartition` in `step_9_4_4`. -/
theorem sbipStep4_spec {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    {X : Pt (BipBlockInputs Ω)} {name : ↥X.obj.1.1.V₁ → ℕ} {r : RawSbipClasses}
    (h : SbipClassNames X name r) (x y : ↥X.obj.1.1.V₁)
    (i j : Fin r.1.2.length) (hi : r.1.2[i] = name x) (hj : r.1.2[j] = name y) :
    labAt (sbipStep4 r).1 i = (kerPartition X.obj.1.1.V₁
      (VColBipBlk.wlDiag X.obj.1.1)).color (mkPt x.property) ∧
    (LabRel (sbipStep4 r).2 i j ↔ (kerPartition X.obj.1.1.V₁
      (VColBipBlk.wlDiag X.obj.1.1)).part (mkPt x.property) (mkPt y.property)) := by
  have hx : labAt (sbipStep4 r).1 i = VColBipBlk.wlDiag X.obj.1.1 x := by
    change (r.1.2.map (fun u => sbipDiag (r.1.1,u))).getD i 0 = _
    rw [List.getD_eq_getElem _ 0 (by simpa using i.isLt),List.getElem_map]
    change r.1.2[i.val] = name x at hi
    rw [hi]
    exact h.diagonal x
  have hy : labAt (sbipStep4 r).1 j = VColBipBlk.wlDiag X.obj.1.1 y := by
    change (r.1.2.map (fun u => sbipDiag (r.1.1,u))).getD j 0 = _
    rw [List.getD_eq_getElem _ 0 (by simpa using j.isLt),List.getElem_map]
    change r.1.2[j.val] = name y at hj
    rw [hj]
    exact h.diagonal y
  refine ⟨hx,?_⟩
  change labAt (sbipStep4 r).1 i = labAt (sbipStep4 r).1 j ↔ _
  rw [hx,hy]
  rfl

/-- The step-4 branch achieves objective (a), with the exact mathematical outcome. -/
theorem sbipStep4_good {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    (X : Pt (BipBlockInputs Ω)) (h : AllClassesSmall X) :
    Good_9_2_2 X ⟨Subtype.val '' X.obj.1.1.V₁,
      Sum.inl (kerPartition X.obj.1.1.V₁ (VColBipBlk.wlDiag X.obj.1.1))⟩ := by
  classical
  refine ⟨rfl,?_⟩
  have hα : 0 ≤ BipBlockInputs.alpha X := le_trans (by norm_num) X.obj.2.1
  have hn : 0 ≤ BipBlockInputs.alpha X * (X.obj.1.1.V₁.ncard : ℝ) := mul_nonneg hα (by positivity)
  exact kerPartition_isAlphaPartition _ _ _ (k := ⌊BipBlockInputs.alpha X *
    (X.obj.1.1.V₁.ncard : ℝ)⌋₊) (fun x hx => Nat.le_floor (h x hx)) (Nat.floor_le hn)

section Transport
variable {n : ℕ} {p : RawConfig} {π : RawPerm}
    (hp : RawWL.WF n 2 p) (hπ : RawPerm.WF n π)
include hp hπ

/-- A restriction transports its ordered domain and all pair keys. -/
theorem sbipInduced_relabel {l : List ℕ} (hl : ∀ a ∈ l, a < n) :
    sbipInduced (relabelWL (π,p),permList π l) = relabelWL (π,sbipInduced (p,l)) := by
  unfold sbipInduced sbipTabulate
  rw [tuplesOf_permList]
  apply Prod.ext
  · rfl
  · simp only [relabelWL,List.map_map]
    apply List.map_congr_left
    intro t ht
    dsimp only [Function.comp_def]
    exact congrArg (fun c => (permList π t,c))
      (tblGet_relabelWL hπ hp (fun a ha => hl a (((mem_tuplesOf _ _ _).1 ht).2 a ha)))

/-- Under transported part orders the two step-4 label lists stay equal. -/
theorem sbipStep4_relabel {l : List ℕ} (hl : ∀ a ∈ l, a < n) (q : ℕ × ℕ) :
    sbipStep4 (sbipRelabelClasses π ((p,l),q)) = sbipStep4 ((p,l),q) := by
  have hh : (permList π l).map (fun u => sbipDiag (relabelWL (π,p),u)) =
      l.map (fun u => sbipDiag (p,u)) := by
    simp only [permList,List.map_map]
    exact List.map_congr_left (fun u hu => sbipDiag_relabel hp hπ (hl u hu))
  exact congrArg (fun l => (l,l)) hh

/-- The matrix is unchanged when both part orders are transported. -/
theorem sbipMatrix_relabel {l r : List ℕ} (hl : ∀ a ∈ l, a < n) (hr : ∀ a ∈ r, a < n) :
    sbipMatrix (relabelWL (π,p),(permList π l,permList π r)) =
      (permList π l,permList π r,(sbipMatrix (p,(l,r))).2.2) := by
  simp only [sbipMatrix,sbipRow,permList,List.map_map,Prod.mk.injEq,true_and]
  apply List.map_congr_left
  intro u hu
  apply List.map_congr_left
  intro v hv
  exact binColor_relabel hp hπ (hl u hu) (hr v hv)

end Transport
end Algo
