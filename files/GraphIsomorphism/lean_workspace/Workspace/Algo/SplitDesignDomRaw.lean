import Workspace.Algo.SplitDesignPair
import Workspace.Algo.SplitDesignJohnson
import Workspace.Algo.SplitNamedLists

/-! # Section 9.7: labelled Johnson data on the dominant class

Read traces in the position order of the large twin class. Complement all
labels when their common size exceeds half that class, as in Case 1.
-/
namespace Algo
open Babai RAM

def designDomFirst (z : RawDesignLocal) : ℕ := upccCaseLeast (designDomPositions z)
def designDomDegree (z : RawDesignLocal) : ℕ := designLocalSize (z.1,designDomFirst z)
def designDomRank (z : RawDesignLocal) : ℕ :=
  min (designDomDegree z) ((designBigPositions z.1).length - designDomDegree z)
def designDomDirect (z : RawDesignLocal) : Bool :=
  decide (2 * designDomDegree z ≤ (designBigPositions z.1).length)

def designTraceRow (z : RawUpccCase × ℕ) : List ℕ :=
  (List.range (designBigPositions z.1).length).filter
    (fun j => decide (labAt (designBigPositions z.1) j ∈ designLocalRow z))

def designDomLabel (z : RawDesignLocal × ℕ) : List ℕ :=
  if designDomDirect z.1 then designTraceRow (z.1.1,z.2)
  else designComplementRow (designBigPositions z.1.1,designTraceRow (z.1.1,z.2))

def designDomLabels (z : RawDesignLocal) : List (List ℕ) :=
  (designDomPositions z).map (fun i => designDomLabel (z,i))

def designDomPoints (z : RawDesignLocal) : List ℕ :=
  (designDomPositions z).map (fun i => labAt z.1.2.1 i)

def designDomJohnson (z : RawDesignLocal) : RawJohnson :=
  (designDomPoints z,designDomRank z,designDomLabels z)

theorem polyFun_designDomFirst : PolyFun designDomFirst :=
  polyFun_designDomPositions.comp upccCasePoly_least

theorem polyFun_designDomDegree : PolyFun designDomDegree :=
  (polyFun_fst.pair polyFun_designDomFirst).comp polyFun_designLocalSize

theorem polyFun_designDomRank : PolyFun designDomRank :=
  polyFun_designDomDegree.min'
    (((polyFun_fst.comp polyFun_designBigPositions).comp polyFun_length).sub polyFun_designDomDegree)

theorem polyFun_designDomDirect : PolyFun designDomDirect :=
  ((polyFun_const 2).mul polyFun_designDomDegree).le
    ((polyFun_fst.comp polyFun_designBigPositions).comp polyFun_length)

theorem polyFun_designTraceRow : PolyFun designTraceRow := by
  have hr : PolyFun (fun z : (RawUpccCase × ℕ) × ℕ =>
      labAt (designBigPositions z.1.1) z.2) :=
    (((polyFun_fst.comp polyFun_fst).comp polyFun_designBigPositions).pair polyFun_snd).comp
      polyFun_labAt
  have ht := (hr.pair (polyFun_fst.comp polyFun_designLocalRow)).comp
    (polyFun_listMem polyFun_natEq)
  exact (polyFun_id.pair ((polyFun_fst.comp polyFun_designBigPositions).comp
    polyFun_rangeLength)).comp (PolyFun.filterParam ht)

theorem polyFun_designDomLabel : PolyFun designDomLabel := by
  have hr : PolyFun (fun z : RawDesignLocal × ℕ => designTraceRow (z.1.1,z.2)) :=
    ((polyFun_fst.comp polyFun_fst).pair polyFun_snd).comp polyFun_designTraceRow
  exact PolyFun.ite (polyFun_fst.comp polyFun_designDomDirect) hr
    ((((polyFun_fst.comp polyFun_fst).comp polyFun_designBigPositions).pair hr).comp
      polyFun_designComplementRow)

theorem polyFun_designDomLabels : PolyFun designDomLabels :=
  (polyFun_id.pair polyFun_designDomPositions).comp (PolyFun.mapParam polyFun_designDomLabel)

theorem polyFun_designDomPoints : PolyFun designDomPoints :=
  (((polyFun_fst.comp polyFun_snd).comp polyFun_fst).pair polyFun_designDomPositions).comp
    (PolyFun.mapParam polyFun_labAt)

theorem polyFun_designDomJohnson : PolyFun designDomJohnson :=
  polyFun_designDomPoints.pair (polyFun_designDomRank.pair polyFun_designDomLabels)

section Specification
variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {s : Set Ω}
    {X : BlkDesignObj s} {name₁ : ↥X.Pt₁ → ℕ} {name₂ : ↥X.blocks → ℕ}
    {r : RawUpccCase} (h : DesignNames X name₁ name₂ r)
    (e₁ : ↥X.Pt₁ ≃ Fin r.2.1.length) (he₁ : ∀ x, r.2.1[(e₁ x).val] = name₁ x)
    (e₂ : ↥X.blocks ≃ Fin r.2.2.length) (he₂ : ∀ B, r.2.2[(e₂ B).val] = name₂ B)
    (p : ℕ × ℕ) (hb : 0 < p.2)
include h he₁ he₂ hb

theorem designDomPositions_nonempty (hd : X.DomHyp (sbipAlphaValue p)) :
    designDomPositions (r,p) ≠ [] := by
  obtain ⟨x,hx⟩ := hd.dom
  exact List.ne_nil_of_mem ((designDomPositions_spec h e₁ he₁ e₂ he₂ p hb ⟨x,hx.1⟩).2 hx)

theorem designDomDegree_spec (hd : X.DomHyp (sbipAlphaValue p))
    (x : ↥(X.domClass (sbipAlphaValue p))) : designDomDegree (r,p) = X.localSize x.val := by
  have hm := (upccCaseLeast_spec _ (designDomPositions_nonempty h e₁ he₁ e₂ he₂ p hb hd)).1
  have hi : designDomFirst (r,p) < r.2.1.length :=
    List.mem_range.1 (List.mem_of_mem_filter hm)
  let y := e₁.symm ⟨designDomFirst (r,p),hi⟩
  have hy : y.val ∈ X.domClass (sbipAlphaValue p) :=
    (designDomPositions_spec h e₁ he₁ e₂ he₂ p hb y).1 (by
      simpa only [y,Equiv.apply_symm_apply] using hm)
  have hh := designLocalSize_spec h e₁ he₁ e₂ he₂ y
  change designLocalSize (r,designDomFirst (r,p)) = _
  rw [show designDomFirst (r,p) = (e₁ y).val by simp only [y,Equiv.apply_symm_apply],hh]
  exact ((hd.domClass_eq x.property) ▸ hy).2

theorem designDomRank_spec (hd : X.DomHyp (sbipAlphaValue p))
    (x : ↥(X.domClass (sbipAlphaValue p))) :
    designDomRank (r,p) = min (X.localSize x.val) (X.bigTwin.ncard - X.localSize x.val) := by
  rw [designDomRank,designDomDegree_spec h e₁ he₁ e₂ he₂ p hb hd x,
    designBigPositions_size h e₁ he₁ e₂ he₂]

variable (eC : ↥X.bigTwin ≃ Fin (designBigPositions r).length)
    (heC : ∀ B, (designBigPositions r)[(eC B).val] =
      (e₂ ⟨B.val,X.bigTwin_subset_blocks B.property⟩).val)
include heC

omit hb in
theorem designTraceRow_mem (x : ↥X.Pt₁) (B : ↥X.bigTwin) :
    (eC B).val ∈ designTraceRow (r,e₁ x) ↔ B.val ∈ X.nbhd x.val := by
  simp only [designTraceRow,List.mem_filter,List.mem_range,(eC B).isLt,true_and,
    decide_eq_true_eq,labAt,List.getD_eq_getElem _ _ (eC B).isLt,heC,
    designLocalRow_mem h e₁ he₁ e₂ he₂,Set.mem_inter_iff,and_iff_left B.property]

theorem designDomLabel_set (hd : X.DomHyp (sbipAlphaValue p))
    (x : ↥(X.domClass (sbipAlphaValue p))) :
    rawJSet (designBigPositions r).length (designDomLabel ((r,p),e₁ ⟨x.val,x.property.1⟩)) =
      if 2 * X.localSize x.val ≤ X.bigTwin.ncard then (X.traceFinset x.val).image eC
      else Finset.univ \ (X.traceFinset x.val).image eC := by
  classical
  have hdir : designDomDirect (r,p) = decide (2 * X.localSize x.val ≤ X.bigTwin.ncard) := by
    rw [designDomDirect,designDomDegree_spec h e₁ he₁ e₂ he₂ p hb hd x,
      designBigPositions_size h e₁ he₁ e₂ he₂]
  ext i
  obtain ⟨B,rfl⟩ := eC.surjective i
  have hm : eC B ∈ (X.traceFinset x.val).image eC ↔ B.val ∈ X.nbhd x.val := by
    rw [Finset.mem_image]
    constructor
    · rintro ⟨D,hD,he⟩
      have : D = B := eC.injective he
      subst D
      exact (X.mem_traceFinset _ _).1 hD
    · intro hB
      exact ⟨B,(X.mem_traceFinset _ _).2 hB,rfl⟩
  rw [mem_rawJSet,designDomLabel,hdir]
  by_cases hh : 2 * X.localSize x.val ≤ X.bigTwin.ncard <;>
    simp [hh,designComplementRow_mem,(eC B).isLt,
      designTraceRow_mem h e₁ he₁ e₂ he₂ p eC heC,hm]

end Specification
end Algo
