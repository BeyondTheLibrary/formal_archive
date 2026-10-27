import Workspace.Algo.SplitBipLink
import Workspace.SplitOrJohnson.Imprimitive

/-! # Section 9.6: scan the link before choosing a branch

Column cells give the in-degrees in ImprimitiveCase. We scan only colors
present in the link, so a binary color name never sets a loop bound.
-/
namespace Algo
open Babai RAM

/-- Count a predicate through an injective list of names. -/
theorem splitNamedCount {A : Type*} [Finite A] (name : A → ℕ)
    (hinj : Function.Injective name) (l : List ℕ) (hnd : l.Nodup)
    (hcover : ∀ a, a ∈ l ↔ ∃ x, name x = a) (p : ℕ → Bool) :
    (l.filter p).length = {x : A | p (name x) = true}.ncard := by
  classical
  rw [← Set.ncard_image_of_injective _ hinj]
  have he : name '' {x : A | p (name x) = true} =
      (↑(l.filter p).toFinset : Set ℕ) := by
    ext a
    simp only [Set.mem_image, Set.mem_setOf_eq, Finset.mem_coe, List.mem_toFinset,
      List.mem_filter]
    constructor
    · rintro ⟨x, hx, rfl⟩; exact ⟨(hcover _).2 ⟨x,rfl⟩, hx⟩
    · rintro ⟨ha,hp⟩
      obtain ⟨x,rfl⟩ := (hcover _).1 ha
      exact ⟨x,hp,rfl⟩
  rw [he, Set.ncard_coe_finset, List.toFinset_card_of_nodup (hnd.filter _)]

/-- First-part vertices entering one second-part vertex in a given color. -/
def impCell (z : (RawUpccCase × ℕ) × ℕ) : List ℕ :=
  z.1.1.2.1.filter (fun x => decide (binColor (z.1.1.1,(x,z.1.2)) = z.2))

theorem polyFun_impCell : PolyFun impCell := by
  have hp : PolyFun (fun z : ((RawUpccCase × ℕ) × ℕ) × ℕ => z.1.1.1.1) :=
    ((polyFun_fst.comp polyFun_fst).comp polyFun_fst).comp polyFun_fst
  have hb : PolyFun (fun z : ((RawUpccCase × ℕ) × ℕ) × ℕ => z.1.1.2) :=
    (polyFun_fst.comp polyFun_fst).comp polyFun_snd
  have hc := ((hp.pair (polyFun_snd.pair hb)).comp polyFun_binColor).natEq
    (polyFun_fst.comp polyFun_snd)
  exact (polyFun_id.pair
    ((((polyFun_fst.comp polyFun_fst).comp polyFun_snd).comp polyFun_fst))).comp
      (PolyFun.filterParam hc)

/-- The strict majority test in step 2. -/
def impBigCell (z : (RawUpccCase × ℕ) × ℕ) : Bool :=
  decide (z.1.1.2.1.length + 1 ≤ 2 * (impCell z).length)

theorem polyFun_impBigCell : PolyFun impBigCell :=
  (((((polyFun_fst.comp polyFun_fst).comp polyFun_snd).comp polyFun_fst).comp
    polyFun_length).add (polyFun_const 1)).le
      ((polyFun_const 2).mul (polyFun_impCell.comp polyFun_length))

/-- A color is large at some listed second-part vertex. -/
def impBigColor (z : RawUpccCase × ℕ) : Bool :=
  !(z.1.2.2.filter (fun b => impBigCell ((z.1,b),z.2))).isEmpty

theorem polyFun_impBigColor : PolyFun impBigColor := by
  have hf : PolyFun (fun z : (RawUpccCase × ℕ) × ℕ => impBigCell ((z.1.1,z.2),z.1.2)) :=
    (((polyFun_fst.comp polyFun_fst).pair polyFun_snd).pair
      (polyFun_fst.comp polyFun_snd)).comp polyFun_impBigCell
  exact polyFun_rawJNot (((polyFun_id.pair
    ((polyFun_fst.comp polyFun_snd).comp polyFun_snd)).comp
      (PolyFun.filterParam hf)).comp polyFun_isEmpty)

def impBigColors (r : RawUpccCase) : List ℕ :=
  (sbipLinkColors r).filter (fun k => impBigColor (r,k))

theorem polyFun_impBigColors : PolyFun impBigColors :=
  (polyFun_id.pair sbipPoly_linkColors).comp (PolyFun.filterParam polyFun_impBigColor)

/-- Step 1 is taken precisely when there is no majority color. -/
def impSplits (r : RawUpccCase) : Bool := (impBigColors r).isEmpty

theorem polyFun_impSplits : PolyFun impSplits := polyFun_impBigColors.comp polyFun_isEmpty

def impJ (r : RawUpccCase) : ℕ := upccCaseLeast (impBigColors r)

theorem polyFun_impJ : PolyFun impJ := polyFun_impBigColors.comp upccCasePoly_least

def impOtherColors (r : RawUpccCase) : List ℕ :=
  (sbipLinkColors r).filter (fun k => !decide (k = impJ r))

theorem polyFun_impOtherColors : PolyFun impOtherColors :=
  (polyFun_impJ.pair sbipPoly_linkColors).comp
    (PolyFun.filterParam (polyFun_rawJNot (polyFun_snd.natEq polyFun_fst)))

/-- The least other color is the color of the contraction. -/
def impH (r : RawUpccCase) : ℕ := upccCaseLeast (impOtherColors r)

theorem polyFun_impH : PolyFun impH := polyFun_impOtherColors.comp upccCasePoly_least

/-- Step 1: the partition read after individualizing a listed block. -/
def impSplitLab (z : RawUpccCase × ℕ) : RawLab :=
  (List.range z.1.2.1.length).map (fun i =>
    binColor (z.1.1,(z.1.2.1.getD i 0,z.2)))

theorem polyFun_impSplitLab : PolyFun impSplitLab := by
  have hr : PolyFun (fun z : (RawUpccCase × ℕ) × ℕ => z.1.1) :=
    polyFun_fst.comp polyFun_fst
  have hl := ((hr.comp polyFun_snd).comp polyFun_fst)
  have hx := ((hl.pair polyFun_snd).pair (polyFun_const 0)).comp polyFun_getD
  have hf := ((hr.comp polyFun_fst).pair
    (hx.pair (polyFun_fst.comp polyFun_snd))).comp polyFun_binColor
  exact (polyFun_id.pair
    (((polyFun_fst.comp polyFun_snd).comp polyFun_fst).comp polyFun_rangeLength)).comp
      (PolyFun.mapParam hf)

section Specification
variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {s : Set Ω}
    (X : BlkImprimitiveObj s) (name₁ : ↥X.Pt₁ → ℕ) (name₂ : ↥X.blocks → ℕ)
    (r : RawUpccCase)

/-- Names retain the pair colors of the refined table in Section 9.6. -/
structure ImpNames : Prop where
  inj₁ : Function.Injective name₁
  inj₂ : Function.Injective name₂
  left : ∀ a, a ∈ r.2.1 ↔ ∃ x, name₁ x = a
  right : ∀ b, b ∈ r.2.2 ↔ ∃ B, name₂ B = b
  link : ∀ x B, binColor (r.1,(name₁ x,name₂ B)) = X.c {x.val} B.val
  blocks : ∀ B C, binColor (r.1,(name₂ B,name₂ C)) = X.c B.val C.val

variable {X name₁ name₂ r} (h : ImpNames X name₁ name₂ r)
include h

theorem impLinkColors_spec (k : ℕ) : k ∈ sbipLinkColors r ↔ X.HasLinkColor k := by
  rw [sbipLinkColors_mem]
  constructor
  · rintro ⟨a,ha,b,hb,hc⟩
    obtain ⟨x,rfl⟩ := (h.left _).1 ha
    obtain ⟨B,rfl⟩ := (h.right _).1 hb
    exact ⟨x,x.property,B,B.property,(h.link x B).symm.trans hc⟩
  · rintro ⟨x,hx,B,hB,hc⟩
    exact ⟨name₁ ⟨x,hx⟩,(h.left _).2 ⟨_,rfl⟩,name₂ ⟨B,hB⟩,
      (h.right _).2 ⟨_,rfl⟩,(h.link _ _).trans hc⟩

theorem impCell_spec (B : ↥X.blocks) (k : ℕ) (x : ↥X.Pt₁) :
    name₁ x ∈ impCell ((r,name₂ B),k) ↔ X.c {x.val} B.val = k := by
  simp only [impCell,List.mem_filter,decide_eq_true_eq,h.link]
  exact and_iff_right ((h.left _).2 ⟨x,rfl⟩)

/-- The raw count gives the in-degree, including absent colors. -/
theorem impCell_length (hnd : r.2.1.Nodup) (B : ↥X.blocks) (k : ℕ) :
    (impCell ((r,name₂ B),k)).length =
      {x : ↥s | X.part₁ x ∧ X.c {x} B.val = k}.ncard := by
  rw [impCell,splitNamedCount name₁ h.inj₁ _ hnd h.left]
  simp only [h.link,decide_eq_true_eq]
  exact X.ncard_pt₁_setOf (fun x => X.c {x} B.val = k)

theorem impLeft_length (hnd : r.2.1.Nodup) :
    r.2.1.length = {x : ↥s | X.part₁ x}.ncard := by
  have hh := splitNamedCount name₁ h.inj₁ _ hnd h.left (fun _ => true)
  simpa [Nat.card_coe_set_eq,BlkImprimitiveObj.Pt₁] using hh

theorem impBigColor_spec (hnd : r.2.1.Nodup) (k : ℕ) :
    impBigColor (r,k) = true ↔ X.IsBigColor k := by
  simp only [impBigColor,Bool.not_eq_true',Bool.eq_false_iff,ne_eq,List.isEmpty_iff,
    List.eq_nil_iff_forall_not_mem,not_forall,not_not,List.mem_filter]
  constructor
  · rintro ⟨b,hb,hh⟩
    obtain ⟨B,rfl⟩ := (h.right _).1 hb
    simp only [impBigCell,decide_eq_true_eq,Nat.succ_le_iff,
      impCell_length h hnd,impLeft_length h hnd] at hh
    exact ⟨B,B.property,hh⟩
  · rintro ⟨B,hB,hh⟩
    refine ⟨name₂ ⟨B,hB⟩,(h.right _).2 ⟨_,rfl⟩,?_⟩
    simpa only [impBigCell,decide_eq_true_eq,Nat.succ_le_iff,
      impCell_length h hnd,impLeft_length h hnd] using hh

/-- Strict majority implies occurrence, so the finite scan is exhaustive. -/
theorem impBigColors_spec (hnd : r.2.1.Nodup) (k : ℕ) :
    k ∈ impBigColors r ↔ X.IsBigColor k := by
  simp only [impBigColors,List.mem_filter,impLinkColors_spec h,impBigColor_spec h hnd]
  refine ⟨And.right, fun hk => ⟨?_,hk⟩⟩
  obtain ⟨B,hB,hbig⟩ := hk
  have hne : {x : ↥s | X.part₁ x ∧ X.c {x} B = k}.Nonempty :=
    Set.nonempty_of_ncard_ne_zero (by omega)
  obtain ⟨x,hx,hcol⟩ := hne
  exact ⟨x,hx,B,hB,hcol⟩

theorem impSplits_spec (hnd : r.2.1.Nodup) :
    impSplits r = true ↔ ImprimitiveSplits X := by
  simp only [impSplits,List.isEmpty_iff,List.eq_nil_iff_forall_not_mem,
    impBigColors_spec h hnd,BlkImprimitiveObj.IsBigColor,ImprimitiveSplits]
  push Not
  exact ⟨fun hh B hB k => hh k B hB, fun hh k B hB => hh B hB k⟩

theorem impJ_spec (hnd : r.2.1.Nodup) : impJ r = X.jColor :=
  upccCaseLeast_find _ _ (impBigColors_spec h hnd)

theorem impOtherColors_spec (hnd : r.2.1.Nodup) (k : ℕ) :
    k ∈ impOtherColors r ↔ X.IsOtherColor k := by
  simp only [impOtherColors,List.mem_filter,impLinkColors_spec h,
    Bool.not_eq_true',decide_eq_false_iff_not,impJ_spec h hnd]
  exact and_comm

theorem impH_spec (hnd : r.2.1.Nodup) : impH r = X.hColor :=
  upccCaseLeast_find _ _ (impOtherColors_spec h hnd)

theorem impSplitLab_spec (B : ↥X.blocks) (x : ↥X.Pt₁)
    (i : Fin r.2.1.length) (hi : r.2.1[i.val] = name₁ x) :
    labAt (impSplitLab (r,name₂ B)) i = X.c {x.val} B.val := by
  simp [impSplitLab,labAt,i.isLt,hi,h.link]

end Specification
end Algo
