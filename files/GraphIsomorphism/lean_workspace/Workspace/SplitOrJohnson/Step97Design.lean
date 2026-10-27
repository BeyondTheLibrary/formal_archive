/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 9.7, Case 3a, step 2: reading the Design Lemma's answer off a version, and its
equivariance.
-/
import Workspace.SplitOrJohnson.BlockDesignHyper
import Workspace.SplitOrJohnson.BlkRestrictHint

/-!
# §9.7, Case 3a, step 2: the Design Lemma's answer at a version

Version 2.5, lines 4281-4294.

Everything here is written for an arbitrary `Babai.BlkDesignSetup`, so that Case 3b (the
same call on the `t`-skeleton of `H`) reuses it unchanged.

Step 1 (`Babai.blkDesign_step1`) produces the category of versions of
`Babai.NormalRed.comap`, whose object is *the input of §9.7 together with one version of
the Design Lemma's answer on the blocks*.  Step 2 has to read that answer and turn it into
an outcome of §9.7.  This file does the reading, and proves the one equivariance statement
that the rest of step 2 rests on.

The answer lives over the ambient type `Set Ω`, where a block is a **point**
(`Babai.BlkCaseObj.blkAmb`), and a morphism of the category of versions acts on it by
`B ↦ f(B)` (`Babai.BlkDesignSetup.func_isBlockFunc`).  `Babai.mem_designAnswer_image` says that a
block `B` of the input lies in the answer's carrier exactly when `f(B)` lies in the
answer's carrier at the other object — which is what makes
`Babai.BlkCaseObj.blkFam` of the carrier a canonical sub-family of the blocks, and hence
what `Babai.VColBipBlk.restrictBlk_isIsoTo` and
`Babai.VColBipBlk.restrictBlkHint_isIsoTo` ask for.

| Paper | Lean |
|---|---|
| the answer of the Design Lemma at a version | `Babai.designAnswer` |
| *"a canonical colored `3/4`-partition of `V₂`"* / *"a UPCC on `W ⊆ V₂`"* | `Babai.designAnswer_isDesignOutcome` |
| the answer is canonical | `Babai.mem_designAnswer_image` |
-/

namespace Babai

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {N : ℕ}
  {S : BlkDesignSetup Ω N} {N' : NormalRed (DesignInputs (Set Ω) N (3 / 4))}

/-- The object of the fiber `{d' = N}` underlying a version. -/
@[reducible] def comapFib (Y : Pt (NormalRed.comap S.func N').D) : Pt S.C :=
  ⟨Y.car, Y.obj.1⟩

theorem comapBBD_eq_bbd (Y : Pt (NormalRed.comap S.func N').D) :
    comapBBD Y = S.bbdPt (comapFib Y) := rfl

/-- The version itself, as an object of the category of versions of the Design Lemma over
the ambient type `Set Ω`. -/
def comapVer (Y : Pt (NormalRed.comap S.func N').D) : Pt N'.D :=
  ⟨(S.func.obj (comapFib Y)).car, Y.obj.2.1⟩

/-- §9.7, Case 3a, step 2.  **The Design Lemma's answer at a version**: the colored
`3/4`-partition of `V₂`, or the UPCC on a subset `W ⊆ V₂`. -/
noncomputable def designAnswer (G' : Func N'.D (DesignOutcomes (Set Ω)))
    (Y : Pt (NormalRed.comap S.func N').D) : Pt (DesignOutcomes (Set Ω)) :=
  G'.obj (comapVer Y)

/-- §9.7, Case 3a, step 2.  The answer is an outcome of Theorem 8.1.2 for the threshold
`3/4` on the blocks: *"a canonical colored `3/4`-partition of `V₂`"* (Case 3a1) or *"a UPCC
canonically embedded on a subset `W ⊆ V₂` with `|W| ≥ (3/4)n₂`"* (Case 3a2). -/
theorem designAnswer_isDesignOutcome {G' : Func N'.D (DesignOutcomes (Set Ω))}
    (hgood : ∀ (X : Pt (DesignInputs (Set Ω) N (3 / 4))) (A : N'.D.Obj X.car),
      N'.base A = X.obj → IsDesignOutcome (3 / 4) X.car (G'.obj ⟨X.car, A⟩))
    (Y : Pt (NormalRed.comap S.func N').D) :
    IsDesignOutcome (3 / 4) (S.obj (comapFib Y)).blkAmb (designAnswer G' Y) :=
  hgood (S.func.obj (comapFib Y)) Y.obj.2.1 Y.obj.2.2

/-- The answer lives on a set of blocks. -/
theorem designAnswer_car_subset {G' : Func N'.D (DesignOutcomes (Set Ω))}
    (hG' : G'.IsCanonicalEmbedding) (Y : Pt (NormalRed.comap S.func N').D) :
    (designAnswer G' Y).car ⊆ (S.obj (comapFib Y)).blkAmb :=
  hG'.car_subset (comapVer Y)

/-! ### Equivariance -/

variable {Y Z : Pt (NormalRed.comap S.func N').D}

/-- A morphism of the category of versions is a morphism of the fibers. -/
def comapFibHom (f : Hom (NormalRed.comap S.func N').D Y Z) :
    Hom S.C (comapFib Y) (comapFib Z) :=
  ⟨f.1, f.2.choose⟩

/-- A morphism of the category of versions is a morphism of the versions. -/
noncomputable def comapVerHom (f : Hom (NormalRed.comap S.func N').D Y Z) :
    Hom N'.D (comapVer Y) (comapVer Z) :=
  ⟨(S.func.map (comapFibHom f)).1, f.2.choose_spec⟩

theorem comapVerHom_val (f : Hom (NormalRed.comap S.func N').D Y Z) :
    (comapVerHom f).1
      = BlkCaseObj.blkAmbEquiv (S.morph (comapFibHom f)) := rfl

open BlkCaseObj in
/-- The value of the version morphism at the point of `Babai.BlkCaseObj.blkAmb` named by a
block `C` is the point named by `f(C)` (`Babai.BlkDesignSetup.func_isBlockFunc`). -/
theorem comapVerHom_apply_blk (f : Hom (NormalRed.comap S.func N').D Y Z)
    {C : Set ↥Y.car} (hmem : Subtype.val '' C ∈ (S.obj (comapFib Y)).blkAmb) :
    (((comapVerHom f).1 ⟨Subtype.val '' C, hmem⟩ :
        ↥(S.obj (comapFib Z)).blkAmb) : Set Ω)
      = Subtype.val '' (f.1 '' C) := by
  rw [comapVerHom_val]
  show ((blkMap (S.morph (comapFibHom f))
    ⟨Subtype.val '' C, hmem⟩ : ↥(S.obj (comapFib Z)).blkAmb) : Set Ω) = _
  rw [val_blkMap]
  congr 2
  exact Set.preimage_image_eq _ Subtype.val_injective

open BlkCaseObj in
/-- §9.7, Case 3a, step 2.  **The Design Lemma's answer is canonical**, one direction: a
morphism of the category of versions carries a block of the answer's carrier into the
answer's carrier.  This is `hG'.map_restrict` read through
`Babai.BlkCaseObj.blkAmbEquiv`. -/
theorem mem_designAnswer_image_of {G' : Func N'.D (DesignOutcomes (Set Ω))}
    (hG' : G'.IsCanonicalEmbedding)
    (f : Hom (NormalRed.comap S.func N').D Y Z)
    {B : Set ↥Y.car} (hB : B ∈ (S.obj (comapFib Y)).blocks)
    (hmem : Subtype.val '' B ∈ (designAnswer G' Y).car) :
    Subtype.val '' (f.1 '' B) ∈ (designAnswer G' Z).car := by
  set x : ↥(designAnswer G' Y).car := ⟨Subtype.val '' B, hmem⟩ with hx
  have hgo := hG'.map_restrict (comapVerHom f) x
  have hv := comapVerHom_apply_blk f (C := B) (designAnswer_car_subset hG' Y x.2)
  have hfin : (((G'.map (comapVerHom f)).1 x : ↥(designAnswer G' Z).car) : Set Ω)
      = Subtype.val '' (f.1 '' B) := hgo.trans hv
  exact hfin ▸ ((G'.map (comapVerHom f)).1 x).2

open BlkCaseObj in
/-- §9.7, Case 3a, step 2.  **The Design Lemma's answer is canonical.**  A morphism `f` of
the category of versions carries a block `B` of the input into the answer's carrier exactly
when `B` itself lies in it.

This is what `Babai.VColBipBlk.restrictBlk_isIsoTo` and
`Babai.VColBipBlk.restrictBlkHint_isIsoTo` ask of the sub-family of blocks that step 2
selects, through `Babai.BlkCaseObj.blkFam`. -/
theorem mem_designAnswer_image {G' : Func N'.D (DesignOutcomes (Set Ω))}
    (hG' : G'.IsCanonicalEmbedding)
    (f : Hom (NormalRed.comap S.func N').D Y Z)
    {B : Set ↥Y.car} (hB : B ∈ (S.obj (comapFib Y)).blocks) :
    Subtype.val '' (f.1 '' B) ∈ (designAnswer G' Z).car ↔
      Subtype.val '' B ∈ (designAnswer G' Y).car := by
  refine ⟨fun hmem => ?_, mem_designAnswer_image_of hG' f hB⟩
  have hm := S.morph (comapFibHom f)
  have hfB : f.1 '' B ∈ (S.obj (comapFib Z)).blocks := (hm.blocks B).2 hB
  have hback := mem_designAnswer_image_of hG' (Hom.symm f) hfB hmem
  have himg : (Hom.symm f).1 '' (f.1 '' B) = B := by
    show f.1.symm '' (f.1 '' B) = B
    exact Equiv.symm_image_image _ _
  rwa [himg] at hback

open BlkCaseObj in
/-- §9.7, Case 3a, step 2.  The answer's carrier, read as a sub-family of the blocks
(`Babai.BlkCaseObj.blkFam`), is carried onto the answer's carrier at the other object.
This is the hypothesis `hU` of `Babai.VColBipBlk.restrictBlk_isIsoTo` and of
`Babai.VColBipBlk.restrictBlkHint_isIsoTo`. -/
theorem blkFam_designAnswer_image {G' : Func N'.D (DesignOutcomes (Set Ω))}
    (hG' : G'.IsCanonicalEmbedding)
    (f : Hom (NormalRed.comap S.func N').D Y Z) (B : Set ↥Y.car) :
    f.1 '' B ∈ (S.obj (comapFib Z)).blkFam (designAnswer G' Z).car ↔
      B ∈ (S.obj (comapFib Y)).blkFam (designAnswer G' Y).car := by
  have hm := S.morph (comapFibHom f)
  by_cases hB : B ∈ (S.obj (comapFib Y)).blocks
  · exact and_congr (iff_of_true ((hm.blocks B).2 hB) hB)
      (mem_designAnswer_image hG' f hB)
  · refine iff_of_false (fun hc => hB ((hm.blocks B).1 hc.1)) (fun hc => hB hc.1)

open BlkCaseObj in
/-- The same for the complement, the second part of the pair `(W, V₂ ∖ W)` that Cases 3a2
and 2 hand to Procedure Reduce-Part2-by-Color. -/
theorem blkFam_compl_designAnswer_image {G' : Func N'.D (DesignOutcomes (Set Ω))}
    (hG' : G'.IsCanonicalEmbedding)
    (f : Hom (NormalRed.comap S.func N').D Y Z) (B : Set ↥Y.car) :
    f.1 '' B ∈ (S.obj (comapFib Z)).blkFam (designAnswer G' Z).carᶜ ↔
      B ∈ (S.obj (comapFib Y)).blkFam (designAnswer G' Y).carᶜ := by
  have hm := S.morph (comapFibHom f)
  by_cases hB : B ∈ (S.obj (comapFib Y)).blocks
  · exact and_congr (iff_of_true ((hm.blocks B).2 hB) hB)
      (not_congr (mem_designAnswer_image hG' f hB))
  · refine iff_of_false (fun hc => hB ((hm.blocks B).1 hc.1)) (fun hc => hB hc.1)


end Babai
