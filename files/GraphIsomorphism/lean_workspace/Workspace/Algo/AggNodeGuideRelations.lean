import Workspace.Algo.AggNodeClassReps

/-! # The numbered raw relations of Case 3

Each source representative defines one relation on each input's fixed-point
set. Local tuple labels are pulled back through that set's explicit list.
The two structures therefore share their relation indices, while their
vertices are numbered separately for the recursive design call.
-/
namespace Algo
open RAM RAM.Targets Babai Equiv

abbrev AggnGuideRelCtx := (RawAction × RawAggCompareTable) × (Bool × (List ℕ × List (List ℕ)))

def aggnGuideRelTest (p : (AggnGuideRelCtx × List ℕ) × List ℕ) : Bool :=
  aggnGuideTuple (p.1.1.1,p.1.1.2.1,p.1.2,rawRestrictStr (p.1.1.2.2.1,p.2))

def aggnGuideRel (p : AggnGuideRelCtx × List ℕ) : RawRel :=
  p.1.2.2.2.filter fun row => aggnGuideRelTest (p,row)

def aggnGuideRelations (p : AggnGuideRelCtx × List (List ℕ)) : RawRelStruct :=
  p.2.map fun u => aggnGuideRel (p.1,u)

/-- Every target tuple must meet a class represented in the source. -/
def aggnGuideCovered (p : AggnGuideRelCtx × List (List ℕ)) : Bool :=
  p.1.2.2.2.all fun row => p.2.any fun u => aggnGuideRelTest ((p.1,u),row)

private theorem fstP {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {f : α → β × γ}
    (h : PolyFun f) : PolyFun (fun a => (f a).1) := h.comp polyFun_fst
private theorem sndP {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {f : α → β × γ}
    (h : PolyFun f) : PolyFun (fun a => (f a).2) := h.comp polyFun_snd

theorem aggnPolyFun_guideRelTest : PolyFun aggnGuideRelTest := by
  have hi : PolyFun (fun p : (AggnGuideRelCtx × List ℕ) × List ℕ => p) := polyFun_id
  have hc := fstP (fstP hi)
  exact ((fstP hc).pair ((fstP (sndP hc)).pair ((sndP (fstP hi)).pair
    (((fstP (sndP (sndP hc))).pair (sndP hi)).comp polyFun_rawRestrictStr)))).comp aggnPolyFun_guideTuple

theorem aggnPolyFun_guideRel : PolyFun aggnGuideRel :=
  (polyFun_id.pair (((polyFun_fst.comp polyFun_snd).comp polyFun_snd).comp polyFun_snd)).comp
    (PolyFun.filterParam aggnPolyFun_guideRelTest)

theorem aggnPolyFun_guideRelations : PolyFun aggnGuideRelations :=
  PolyFun.mapParam aggnPolyFun_guideRel

theorem aggnPolyFun_guideCovered : PolyFun aggnGuideCovered := by
  have hi : PolyFun (fun p : ((AggnGuideRelCtx × List (List ℕ)) × List ℕ) × List ℕ => p) := polyFun_id
  have ht : PolyFun (fun p : ((AggnGuideRelCtx × List (List ℕ)) × List ℕ) × List ℕ =>
      aggnGuideRelTest ((p.1.1.1,p.2),p.1.2)) :=
    (((fstP (fstP (fstP hi))).pair (sndP hi)).pair (sndP (fstP hi))).comp aggnPolyFun_guideRelTest
  have hany : PolyFun (fun p : (AggnGuideRelCtx × List (List ℕ)) × List ℕ =>
      p.1.2.any fun u => aggnGuideRelTest ((p.1.1,u),p.2)) :=
    (((polyFun_id.pair (polyFun_fst.comp polyFun_snd)).comp
      (PolyFun.filterParam ht)).comp (wftPolyFun_not polyFun_isEmpty)).of_eq (fun p => by
        change (!(p.1.2.filter (fun u => aggnGuideRelTest ((p.1.1,u),p.2))).isEmpty) = _
        generalize p.1.2 = L
        induction L with
        | nil => rfl
        | cons a L ih =>
          cases he : aggnGuideRelTest ((p.1.1,a),p.2) <;> simp [he,ih])
  exact ((polyFun_id.pair (((polyFun_fst.comp polyFun_snd).comp polyFun_snd).comp polyFun_snd)).comp
    (wftPolyFun_all hany)).of_eq (fun _ => rfl)

theorem aggnGuideRel_mem {p : AggnGuideRelCtx × List ℕ} {row : List ℕ} :
    row ∈ aggnGuideRel p ↔ row ∈ p.1.2.2.2 ∧ aggnGuideRelTest (p,row) = true :=
  List.mem_filter

theorem aggnGuideRelations_length (p : AggnGuideRelCtx × List (List ℕ)) :
    (aggnGuideRelations p).length = p.2.length := by simp [aggnGuideRelations]

theorem aggnGuideCovered_spec (p : AggnGuideRelCtx × List (List ℕ)) :
    aggnGuideCovered p = true ↔
      ∀ row ∈ p.1.2.2.2,∃ u ∈ p.2,aggnGuideRelTest ((p.1,u),row) = true := by
  simp only [aggnGuideCovered,List.all_eq_true,List.any_eq_true]

end Algo
