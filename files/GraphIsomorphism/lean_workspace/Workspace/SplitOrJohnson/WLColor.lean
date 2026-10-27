import Workspace.SplitOrJohnson.WLCarrier
import Workspace.Refinement.NamedWL

/-!
# Section 9.4, step 3: the named refinement

Colors are renamed after every round as in Section 4.1.1. Refinement runs on the
actual vertices. `carrier_wlRaw` relates its classes to the older padded carrier.
The value on infinite ambient types only keeps the old total function type.
All inputs in Section 9 have a finite ambient type.
-/

namespace Babai
namespace VColBipBlk

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {s t : Set Ω}

open scoped Classical in
/-- Section 9.4, step 3: run the named refinement on the actual vertices. -/
noncomputable def wlNamed (G : VColBipBlk ↥s ℕ) (A B : Vtx G) : ℕ :=
  if hf : Finite Ω then
    letI := hf
    letI : Fintype (Vtx G) := Fintype.ofFinite _
    WL.namedIter (vtxInitColor G) (wlRounds Ω) A B
  else initColor G A.val B.val

theorem wlNamed_eq (G : VColBipBlk ↥s ℕ) (A B : Vtx G) :
    wlNamed G A B =
      @WL.namedIter (Vtx G) (Fintype.ofFinite _)
        (vtxInitColor G) (wlRounds Ω) A B := by
  classical
  rw [wlNamed, dif_pos (inferInstance : Finite Ω)]

theorem wlNamed_eq_iff (G : VColBipBlk ↥s ℕ) (A B C D : Vtx G) :
    wlNamed G A B = wlNamed G C D ↔ wlRaw G A.val B.val = wlRaw G C.val D.val := by
  classical
  letI : Fintype (Vtx G) := Fintype.ofFinite _
  rw [wlNamed_eq, wlNamed_eq, WL.namedIter_eq_iff]
  exact (carrier_wlRaw G A B C D).symm

/-- The vertex bijection induced by an isomorphism of the bipartite inputs. -/
noncomputable def wlVtxEquiv {G : VColBipBlk ↥s ℕ} {H : VColBipBlk ↥t ℕ}
    {φ : ↥s ≃ ↥t} (h : G.IsIsoTo H φ) : Vtx G ≃ Vtx H where
  toFun A := ⟨φ '' A.val, (isVertexOn_image_iff h.part₁ h.blocks A.val).2 A.property⟩
  invFun B := ⟨φ.symm '' B.val,
    (isVertexOn_image_iff h.symm.part₁ h.symm.blocks B.val).2 B.property⟩
  left_inv A := Subtype.ext (Equiv.symm_image_image φ A.val)
  right_inv B := Subtype.ext (Equiv.image_symm_image φ B.val)

theorem wlNamed_map {G : VColBipBlk ↥s ℕ} {H : VColBipBlk ↥t ℕ}
    {φ : ↥s ≃ ↥t} (h : G.IsIsoTo H φ) (A B : Vtx G) :
    wlNamed H (wlVtxEquiv h A) (wlVtxEquiv h B) = wlNamed G A B := by
  classical
  letI : Fintype (Vtx G) := Fintype.ofFinite _
  letI : Fintype (Vtx H) := Fintype.ofFinite _
  rw [wlNamed_eq, wlNamed_eq]
  exact WL.namedIter_map (wlVtxEquiv h) (fun u v => initColor_map h u.val v.val) _ A B

open scoped Classical in
/-- §9.4, step 3.  **The coloring of the coherent configuration `X`, named by natural
numbers.**  On a pair of vertices the name of the WL color is its rank among the colors
that occur, shifted by one; off the vertex set the color is `0`, the normalization that
`Babai.BlkImprimitiveObj.c_off` and `Babai.BlkCaseObj.c_off` demand.

The shift by one keeps the padding apart from the colors of genuine pairs of vertices. -/
noncomputable def wlColor (G : VColBipBlk ↥s ℕ) (A B : Set ↥s) : ℕ :=
  if hv : IsVertexOn G.part₁ G.blocks A ∧ IsVertexOn G.part₁ G.blocks B then
    wlNamed G ⟨A, hv.1⟩ ⟨B, hv.2⟩ + 1
  else 0

theorem wlColor_off (G : VColBipBlk ↥s ℕ) {A B : Set ↥s}
    (h : ¬ (IsVertexOn G.part₁ G.blocks A ∧ IsVertexOn G.part₁ G.blocks B)) :
    wlColor G A B = 0 := by
  classical
  rw [wlColor, dif_neg h]

/-- On a pair of vertices the `ℕ`-name is not the padding color `0`. -/
theorem wlColor_ne_zero (G : VColBipBlk ↥s ℕ) {A B : Set ↥s}
    (h : IsVertexOn G.part₁ G.blocks A ∧ IsVertexOn G.part₁ G.blocks B) :
    wlColor G A B ≠ 0 := by
  classical
  rw [wlColor, dif_pos h]
  omega

/-- §9.4, step 3.  **The `ℕ`-named coloring is canonical.**  An isomorphism of the inputs
carries the color of a pair of vertices to the color of the image pair — with *equal*
labels, which is what a morphism of the categories of §9.6-§9.8 preserves.

This is the statement for whose sake the number of rounds is fixed in advance and the
colors are named round by round; see the module docstring. -/
theorem wlColor_map {G : VColBipBlk ↥s ℕ} {H : VColBipBlk ↥t ℕ} {φ : ↥s ≃ ↥t}
    (h : G.IsIsoTo H φ) (A B : Set ↥s) : wlColor H (φ '' A) (φ '' B) = wlColor G A B := by
  classical
  have hvA := isVertexOn_image_iff (fun x => h.part₁ x) (fun B => h.blocks B) A
  have hvB := isVertexOn_image_iff (fun x => h.part₁ x) (fun B => h.blocks B) B
  rw [wlColor, wlColor]
  by_cases hv : IsVertexOn G.part₁ G.blocks A ∧ IsVertexOn G.part₁ G.blocks B
  · rw [dif_pos ⟨hvA.2 hv.1, hvB.2 hv.2⟩, dif_pos hv]
    exact congrArg (· + 1) (wlNamed_map h ⟨A, hv.1⟩ ⟨B, hv.2⟩)
  · have hn : ¬ (IsVertexOn H.part₁ H.blocks (φ '' A) ∧
        IsVertexOn H.part₁ H.blocks (φ '' B)) := fun hc => hv ⟨hvA.1 hc.1, hvB.1 hc.2⟩
    rw [dif_neg hn, dif_neg hv]

/-! ### The refined coloring refines the input

*"`X₁₂` is a refinement of `E`"* and *"the vertex-colors discriminate between `V₁` and
`V₂`"* (version 2.5, lines 4098 and 4129).  Both come from one fact: WL refinement only
refines, so equal refined colors force equal initial colors. -/

/-- The refined coloring refines the configuration it started from. -/
theorem initColor_eq_of_wlRaw_eq (G : VColBipBlk ↥s ℕ) {A B A' B' : Set ↥s}
    (h : wlRaw G A B = wlRaw G A' B') : initColor G A B = initColor G A' B' :=
  WL.iter_isRefinement_le (initColor G) (Nat.zero_le _) A B A' B' h

/-- On the pairs of vertices the `ℕ`-name determines the WL color: the naming is injective
on the colors that occur (`Babai.WL.namedIter_eq_iff`). -/
theorem wlRaw_eq_of_wlColor_eq (G : VColBipBlk ↥s ℕ) {A B A' B' : Set ↥s}
    (hv : IsVertexOn G.part₁ G.blocks A ∧ IsVertexOn G.part₁ G.blocks B)
    (hv' : IsVertexOn G.part₁ G.blocks A' ∧ IsVertexOn G.part₁ G.blocks B')
    (h : wlColor G A B = wlColor G A' B') : wlRaw G A B = wlRaw G A' B' := by
  classical
  rw [wlColor, wlColor, dif_pos hv, dif_pos hv'] at h
  exact (wlNamed_eq_iff G ⟨A, hv.1⟩ ⟨B, hv.2⟩ ⟨A', hv'.1⟩ ⟨B', hv'.2⟩).1
    (Nat.add_right_cancel h)

omit [Fintype Ω] [DecidableEq Ω] in
/-- Equal raw colors have equal names, including on the total function's infinite inputs. -/
theorem wlColor_eq_of_raw (G : VColBipBlk ↥s ℕ) {A B A' B' : Set ↥s}
    (hv : IsVertexOn G.part₁ G.blocks A ∧ IsVertexOn G.part₁ G.blocks B)
    (hv' : IsVertexOn G.part₁ G.blocks A' ∧ IsVertexOn G.part₁ G.blocks B')
    (h : wlRaw G A B = wlRaw G A' B') : wlColor G A B = wlColor G A' B' := by
  classical
  rw [wlColor, wlColor, dif_pos hv, dif_pos hv']
  congr 1
  by_cases hf : Finite Ω
  · letI := hf
    letI : Fintype Ω := Fintype.ofFinite _
    exact (wlNamed_eq_iff G ⟨A, hv.1⟩ ⟨B, hv.2⟩ ⟨A', hv'.1⟩ ⟨B', hv'.2⟩).2 h
  · rw [wlNamed, wlNamed, dif_neg hf, dif_neg hf]
    exact WL.iter_isRefinement_le (initColor G) (Nat.zero_le _) A B A' B' h

/-- §9.4, step 3.  Two points of `V₁` with the same vertex color in the coherent
configuration have the same color in the input graph: the refinement refines the input
coloring. -/
theorem f_eq_of_wlColor_eq (G : VColBipBlk ↥s ℕ) {x y : ↥s} (hx : G.part₁ x)
    (hy : G.part₁ y) (h : wlColor G {x} {x} = wlColor G {y} {y}) : G.f x = G.f y := by
  classical
  have hvx : IsVertexOn G.part₁ G.blocks ({x} : Set ↥s) := Or.inl ⟨x, hx, rfl⟩
  have hvy : IsVertexOn G.part₁ G.blocks ({y} : Set ↥s) := Or.inl ⟨y, hy, rfl⟩
  have hraw := wlRaw_eq_of_wlColor_eq G ⟨hvx, hvx⟩ ⟨hvy, hvy⟩ h
  have hinit := initColor_eq_of_wlRaw_eq G hraw
  rw [initColor, initColor, if_pos rfl, if_pos rfl] at hinit
  have hv := (Nat.pair_eq_pair.1 hinit).2
  rw [initVtxColor, initVtxColor, if_pos ⟨x, hx, rfl⟩, if_pos ⟨y, hy, rfl⟩,
    Set.image_singleton, Set.image_singleton, csSup_singleton, csSup_singleton] at hv
  exact (Nat.pair_eq_pair.1 hv).2

/-- §9.4, step 3.  *"the vertex-colors discriminate between `V₁` and `V₂`"*: a point of
`V₁` and a block never carry the same vertex color. -/
theorem wlColor_ne_of_part₁_blocks (G : VColBipBlk ↥s ℕ) {x : ↥s} (hx : G.part₁ x)
    {B : Set ↥s} (hB : B ∈ G.blocks) : wlColor G {x} {x} ≠ wlColor G B B := by
  classical
  intro h
  have hvx : IsVertexOn G.part₁ G.blocks ({x} : Set ↥s) := Or.inl ⟨x, hx, rfl⟩
  have hvB : IsVertexOn G.part₁ G.blocks B := Or.inr hB
  have hnot : ¬ ∃ y, G.part₁ y ∧ B = {y} := by
    rintro ⟨y, hy, rfl⟩
    exact G.blocks_off₁ _ hB y rfl hy
  have hinit := initColor_eq_of_wlRaw_eq G
    (wlRaw_eq_of_wlColor_eq G ⟨hvx, hvx⟩ ⟨hvB, hvB⟩ h)
  rw [initColor, initColor, if_pos rfl, if_pos rfl] at hinit
  have hv := (Nat.pair_eq_pair.1 hinit).2
  rw [initVtxColor, initVtxColor, if_pos ⟨x, hx, rfl⟩, if_neg hnot, if_pos hB] at hv
  exact absurd (Nat.pair_eq_pair.1 hv).1 (by norm_num)

/-! ### The vertex colors of the points of `V₁` -/

/-- §9.4, step 4.  The **vertex color** of a point, read in the coherent configuration of
step 3: the diagonal color of the singleton `{x}`.  Step 4 asks whether all classes of this
coloring inside `V₁` have at most `α n₁` points. -/
noncomputable def wlDiag (G : VColBipBlk ↥s ℕ) (x : ↥s) : ℕ := wlColor G {x} {x}

/-- §9.4, step 4.  The vertex coloring of step 3 is canonical. -/
theorem wlDiag_map {G : VColBipBlk ↥s ℕ} {H : VColBipBlk ↥t ℕ} {φ : ↥s ≃ ↥t}
    (h : G.IsIsoTo H φ) (x : ↥s) : wlDiag H (φ x) = wlDiag G x := by
  have h1 := wlColor_map h {x} {x}
  rwa [Set.image_singleton] at h1

end VColBipBlk

end Babai
