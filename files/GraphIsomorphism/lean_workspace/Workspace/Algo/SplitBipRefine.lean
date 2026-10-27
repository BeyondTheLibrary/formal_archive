import Workspace.Algo.SplitBipLink

/-!
# Section 9.4, step 8: a constituent and its second refinement

The input carries the old vertex tags and hint. Replacing the edge relation
keeps these fields. We build the initial binary coloring, move to positions in
the retained vertex list, and run the same named refinement as step 3.
-/

namespace Algo
open Babai RAM

/-- The selected constituent is directed from the first part to the second. -/
def sbipStep8EdgeTest (z : RawUpccCase × (ℕ × ℕ)) : Bool :=
  decide (z.2.1 ∈ z.1.2.1) && decide (z.2.2 ∈ z.1.2.2) &&
    decide (binColor (z.1.1,z.2) = sbipFirstInvolved z.1)

theorem sbipPoly_step8EdgeTest : PolyFun sbipStep8EdgeTest := by
  have hl : PolyFun (fun z : RawUpccCase × (ℕ × ℕ) => decide (z.2.1 ∈ z.1.2.1)) :=
    ((polyFun_snd.comp polyFun_fst).pair
    ((polyFun_fst.comp polyFun_snd).comp polyFun_fst)).comp polyFun_natListMem
  have hr : PolyFun (fun z : RawUpccCase × (ℕ × ℕ) => decide (z.2.2 ∈ z.1.2.2)) :=
    ((polyFun_snd.comp polyFun_snd).pair
    ((polyFun_fst.comp polyFun_snd).comp polyFun_snd)).comp polyFun_natListMem
  have hc : PolyFun (fun z : RawUpccCase × (ℕ × ℕ) => decide
    (binColor (z.1.1,z.2) = sbipFirstInvolved z.1)) :=
    (((polyFun_fst.comp polyFun_fst).pair polyFun_snd).comp polyFun_binColor).natEq
    (polyFun_fst.comp sbipPoly_firstInvolved)
  exact polyFun_rawJAnd (polyFun_rawJAnd hl hr) hc

/-- The zero/one adjacency entry of the selected constituent. -/
def sbipStep8Edge (z : RawUpccCase × (ℕ × ℕ)) : ℕ := if sbipStep8EdgeTest z then 1 else 0

theorem sbipPoly_step8Edge : PolyFun sbipStep8Edge :=
  PolyFun.ite sbipPoly_step8EdgeTest (polyFun_const 1) (polyFun_const 0)

/-- The retained link, original vertex tags, and original hint. -/
abbrev RawSbipRefine := RawUpccCase × (RawLab × RawConfig)

/-- Section 9.4, step 8: the exact initial pair name used by `initColor`. -/
def sbipStep8Pair (z : RawSbipRefine × (ℕ × ℕ)) : ℕ :=
  if decide (z.2.1 = z.2.2) then Nat.pair 0 (labAt z.1.2.1 z.2.1)
  else Nat.pair 1 (Nat.pair
    (Nat.pair (sbipStep8Edge (z.1.1,z.2)) (sbipStep8Edge (z.1.1,(z.2.2,z.2.1))))
    (Nat.pair (binColor (z.1.2.2,z.2)) (binColor (z.1.2.2,(z.2.2,z.2.1)))))

theorem sbipPoly_step8Pair : PolyFun sbipStep8Pair := by
  have hu : PolyFun (fun z : RawSbipRefine × (ℕ × ℕ) => z.2.1) := polyFun_snd.comp polyFun_fst
  have hv : PolyFun (fun z : RawSbipRefine × (ℕ × ℕ) => z.2.2) := polyFun_snd.comp polyFun_snd
  have hr : PolyFun (fun z : RawSbipRefine × (ℕ × ℕ) => z.1.1) := polyFun_fst.comp polyFun_fst
  have hh : PolyFun (fun z : RawSbipRefine × (ℕ × ℕ) => z.1.2.2) :=
    (polyFun_fst.comp polyFun_snd).comp polyFun_snd
  have hf := ((((polyFun_fst.comp polyFun_snd).comp polyFun_fst).pair hu).comp polyFun_labAt)
  have he := (((hr.pair (hu.pair hv)).comp sbipPoly_step8Edge).pair
    ((hr.pair (hv.pair hu)).comp sbipPoly_step8Edge)).comp polyFun_upccNatPair
  have hhi := (((hh.pair (hu.pair hv)).comp polyFun_binColor).pair
    ((hh.pair (hv.pair hu)).comp polyFun_binColor)).comp polyFun_upccNatPair
  exact PolyFun.ite (hu.natEq hv) (((polyFun_const 0).pair hf).comp polyFun_upccNatPair)
    (((polyFun_const 1).pair ((he.pair hhi).comp polyFun_upccNatPair)).comp polyFun_upccNatPair)

/-- One row of the initial table. -/
def sbipStep8Row (z : RawSbipRefine × List ℕ) : List ℕ × ℕ :=
  (z.2,sbipStep8Pair (z.1,(rawGet (z.2,0),rawGet (z.2,1))))

theorem sbipPoly_step8Row : PolyFun sbipStep8Row :=
  polyFun_snd.pair ((polyFun_fst.pair
    (((polyFun_snd.pair (polyFun_const 0)).comp polyFun_rawGet).pair
      ((polyFun_snd.pair (polyFun_const 1)).comp polyFun_rawGet))).comp sbipPoly_step8Pair)

/-- Section 9.4, step 8: the initial table on the retained old names. -/
def sbipStep8Initial (r : RawSbipRefine) : RawConfig :=
  let l := r.1.2.1 ++ r.1.2.2
  (l,(tuplesOf l 2).map (fun t => sbipStep8Row (r,t)))

theorem sbipPoly_step8Initial : PolyFun sbipStep8Initial := by
  have hl : PolyFun (fun r : RawSbipRefine => r.1.2.1 ++ r.1.2.2) :=
    (polyFun_fst.comp polyFun_snd).comp polyFun_append
  exact hl.pair ((polyFun_id.pair (hl.comp ((polyFun_tuplesOf 2).comp polyFun_snd))).comp
    (PolyFun.mapParam sbipPoly_step8Row))

theorem sbipStep8Initial_get (r : RawSbipRefine) {u v : ℕ}
    (hu : u ∈ r.1.2.1 ++ r.1.2.2) (hv : v ∈ r.1.2.1 ++ r.1.2.2) :
    binColor (sbipStep8Initial r,(u,v)) = sbipStep8Pair (r,(u,v)) := by
  have ht : [u,v] ∈ tuplesOf (r.1.2.1 ++ r.1.2.2) 2 :=
    (mem_tuplesOf _ _ _).2 ⟨rfl,by simpa using And.intro hu hv⟩
  have hh := congrArg (fun o => o.getD 0) (sbipLookup
    (fun t => sbipStep8Pair (r,(rawGet (t,0),rawGet (t,1)))) _ ht)
  simpa [sbipStep8Initial,sbipStep8Row,rawGet,binColor,tblGet] using hh

/-- Section 9.4, step 8: the second named WL refinement. -/
def sbipStep8Refine (r : RawSbipRefine) : RawConfig :=
  sbipStep3 (sbipIndexed (sbipStep8Initial r,r.1.2.1 ++ r.1.2.2))

theorem sbipPoly_step8Refine : PolyFun sbipStep8Refine :=
  ((sbipPoly_step8Initial.pair ((polyFun_fst.comp polyFun_snd).comp polyFun_append)).comp
    sbipPoly_indexed).comp sbipPoly_step3

section Specification
variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    (X : Pt (BipBlockInputs Ω)) (r : RawSbipRefine)
    (name : (step8Obj X).Vtx → ℕ)

/-- Input names for step 8: the retained vertices and inherited fields are named.
The only selected value in this contract is identified by `sbipFirstInvolved_spec`. -/
structure SbipStep8Names : Prop where
  injective : Function.Injective name
  left : ∀ A, name A ∈ r.1.2.1 ↔ ∃ x, (step8Obj X).part₁ x ∧ A.val = {x}
  right : ∀ A, name A ∈ r.1.2.2 ↔ A.val ∈ (step8Obj X).blocks
  pairColor : ∀ A B, binColor (r.1.1,(name A,name B)) =
    VColBipBlk.wlCaseColor X.obj.1.1 (VColBipBlk.incl (step7Set_subset X) '' A.val)
      (VColBipBlk.incl (step7Set_subset X) '' B.val)
  selected : sbipFirstInvolved r.1 = step8Color X
  vertex : ∀ A, labAt r.2.1 (name A) = VColBipBlk.initVtxColor (step8Obj X) A.val
  hint : ∀ A B, binColor (r.2.2,(name A,name B)) = (step8Obj X).h A.val B.val

variable {X r name} (h : SbipStep8Names X r name)
include h

/-- The computed constituent has exactly the edges of `step8Obj`. -/
theorem sbipStep8Edge_spec (A B : (step8Obj X).Vtx) :
    sbipStep8Edge (r.1,(name A,name B)) = VColBipBlk.initEdge (step8Obj X) A.val B.val := by
  classical
  have he : sbipStep8EdgeTest (r.1,(name A,name B)) = true ↔
      ∃ x, (step8Obj X).part₁ x ∧ A.val = {x} ∧ (x,B.val) ∈ (step8Obj X).E := by
    simp only [sbipStep8EdgeTest,Bool.and_eq_true,decide_eq_true_eq,h.left,h.right,
      h.pairColor,h.selected]
    constructor
    · rintro ⟨⟨⟨x,hx,ha⟩,hb⟩,hc⟩
      refine ⟨x,hx,ha,hx,hb,?_⟩
      rwa [ha,Set.image_singleton] at hc
    · rintro ⟨x,hx,ha,he⟩
      refine ⟨⟨⟨x,hx,ha⟩,he.2.1⟩,?_⟩
      rw [ha,Set.image_singleton]
      exact he.2.2
  simp only [sbipStep8Edge,VColBipBlk.initEdge,he]
  by_cases hh : ∃ x, (step8Obj X).part₁ x ∧ A.val = {x} ∧ (x,B.val) ∈ (step8Obj X).E
  · rw [if_pos hh,if_pos hh]
  · rw [if_neg hh,if_neg hh]

/-- The initial pair names match `vtxInitColor`, including hints in both directions. -/
theorem sbipStep8Pair_spec (A B : (step8Obj X).Vtx) :
    sbipStep8Pair (r,(name A,name B)) = (step8Obj X).vtxInitColor A B := by
  classical
  have he : name A = name B ↔ A.val = B.val := h.injective.eq_iff.trans Subtype.val_inj.symm
  simp only [sbipStep8Pair,VColBipBlk.vtxInitColor,VColBipBlk.initColor,decide_eq_true_eq,he,
    h.vertex,sbipStep8Edge_spec h,h.hint]

/-- Section 9.4, step 8: the second refinement computes exactly `step8Config`.
The enumeration records positions in the retained list, so no output-name
hypothesis is assumed. -/
theorem sbipStep8Refine_spec
    (e : (step8Obj X).Vtx ≃ Fin (r.1.2.1 ++ r.1.2.2).length)
    (hl : ∀ A, (r.1.2.1 ++ r.1.2.2)[(e A).val] = name A)
    (A B : (step8Obj X).Vtx) :
    binColor (sbipStep8Refine r,(e A,e B)) = (step8Config X).natColor A B := by
  have hi : ∀ C D : (step8Obj X).Vtx,
      namedBin (r.1.2.1 ++ r.1.2.2).length
        (sbipIndexed (sbipStep8Initial r,r.1.2.1 ++ r.1.2.2)) (e C) (e D) =
          (step8Obj X).vtxInitColor C D := by
    intro C D
    rw [namedBin,sbipIndexed_get,hl,hl,sbipStep8Initial_get r
      (hl C ▸ List.getElem_mem (e C).isLt) (hl D ▸ List.getElem_mem (e D).isLt)]
    exact sbipStep8Pair_spec h C D
  have hh := sbipStep3_named (step8Obj X) e (sbipIndexed_wf _ _) hi A B
  change binColor (sbipStep8Refine r,(e A,e B)) = ((step8Obj X).wlConfig).natColor A B
  rw [VColBipBlk.natColor_wlConfig,VColBipBlk.wlCaseColor,dif_pos ⟨A.property,B.property⟩]
  exact hh

end Specification
end Algo
