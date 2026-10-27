/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 9.7, Cases 3a1 and 3a2: which part of `V₂` is handed to Procedure
Reduce-Part2-by-Color, and which structure is left on it.
-/
import Workspace.SplitOrJohnson.Step97Design
import Workspace.SplitOrJohnson.BlkExit
import Workspace.SplitOrJohnson.ColorSplit
import Workspace.SplitOrJohnson.HintBuild
import Workspace.SplitOrJohnson.HintEqvBlocks

/-!
# §9.7, Cases 3a1 and 3a2: the part and the structure on it

Version 2.5, lines 4281-4294; the original, `babai-gi.tex`, lines 3981-3992.

Everything here is written for an arbitrary `Babai.BlkDesignSetup`, so that Case 3b (the
same call on the `t`-skeleton of `H`) reuses it unchanged.

Step 1 hands over one version of the Design Lemma's answer on the blocks
(`Babai.designAnswer`).  Step 2 turns it into an outcome of §9.7, and this file builds the
two data that the common exit (`Babai.findsAtMultCost_restrictHint`) asks for.

* `Babai.designFirst` is the **first of the two parts** handed to Procedure
  Reduce-Part2-by-Color, read on the ambient type `Set Ω` where a block is a point.  In
  Case 3a2, where the answer is a UPCC on `W ⊆ V₂`, it is `W`; in Case 3a1, where the
  answer is a colored `3/4`-partition of `V₂`, it is `Babai.colorSplit` of the
  equipartition refinement of that coloring (Prop. 7.1.3).
* `Babai.designSel` is the part the procedure selects, and `Babai.designHint` is the
  coloring of the ordered pairs of blocks that records the structure found on
  `Babai.designFirst`: the UPCC's own coloring in Case 3a2, and in Case 3a1 the three
  relations *"equal"*, *"different, same block of the partition"*, *"different blocks"*
  of `Babai.eqvConfig`.

Both are named by the answer alone, so a morphism of the category of versions carries them
onto the corresponding data at the other object; that is
`Babai.designFirst_image` and `Babai.designHint_image`.
-/

namespace Babai

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {N : ℕ}
  {S : BlkDesignSetup Ω N} {N' : NormalRed (DesignInputs (Set Ω) N (3 / 4))}

/-! ### The two data -/

/-- The point set of the Design Lemma's answer is finite. -/
@[reducible] noncomputable def ansCarFintype (G' : Func N'.D (DesignOutcomes (Set Ω)))
    (Y : Pt (NormalRed.comap S.func N').D) :
    Fintype ↥(designAnswer G' Y).car := Fintype.ofFinite _

/-- §9.7, Case 3a1.  The coloring of `V₂` by which Case 3a1 splits: the color of the
equipartition refinement of Prop. 7.1.3 — the old color together with the size of the
block — read as one natural number by `Nat.pair`.

The refinement is what makes the blocks inside one color class have **one common size**,
which is the hypothesis `hm` of `Babai.eqvConfig`. -/
noncomputable def equipColor {W : Set (Set Ω)} (P : ColoredPartition ↥W ℕ) (x : ↥W) : ℕ :=
  Nat.pair (P.color x) ((P.block x).ncard)

theorem equipColor_eq_iff {W : Set (Set Ω)} (P : ColoredPartition ↥W ℕ) (x y : ↥W) :
    equipColor P x = equipColor P y ↔
      P.color x = P.color y ∧ (P.block x).ncard = (P.block y).ncard := by
  constructor
  · intro h
    have h1 := congrArg Nat.unpair h
    rw [equipColor, equipColor, Nat.unpair_pair, Nat.unpair_pair] at h1
    exact ⟨congrArg Prod.fst h1, congrArg Prod.snd h1⟩
  · rintro ⟨h1, h2⟩
    rw [equipColor, equipColor, h1, h2]

/-- §9.7, Cases 3a1 and 3a2.  **The first of the two parts handed to Procedure
Reduce-Part2-by-Color**, read on the ambient type `Set Ω`: the carrier `W` of the UPCC in
Case 3a2, and `Babai.colorSplit` of the refined coloring in Case 3a1. -/
noncomputable def designFirst (G' : Func N'.D (DesignOutcomes (Set Ω)))
    (Y : Pt (NormalRed.comap S.func N').D) : Set (Set Ω) :=
  Sum.elim (fun P : ColoredPartition ↥(designAnswer G' Y).car ℕ =>
      Subtype.val '' @colorSplit _ (ansCarFintype G' Y) (equipColor P))
    (fun _ => (designAnswer G' Y).car) (designAnswer G' Y).obj

open scoped Classical in
/-- §9.7, Case 3a1.  The three-color coloring of the equipartition: `0` on the diagonal,
`1` on a pair of different blocks in one block of the partition, `2` on a pair in
different blocks. -/
noncomputable def eqvNat {W : Set (Set Ω)} (P : ColoredPartition ↥W ℕ) (x y : ↥W) : ℕ :=
  if x = y then 0 else if P.part x y then 1 else 2

open scoped Classical in
/-- §9.7, Cases 3a1 and 3a2.  **The structure found on the first part**, as a coloring of
the ordered pairs of points of `Babai.BlkCaseObj.blkAmb`: the UPCC's own coloring in
Case 3a2, the three relations of `Babai.eqvConfig` in Case 3a1.  It is `0` on every pair
that leaves the first part, so that the exit that selects the *other* part carries no
hint. -/
noncomputable def designHintAmb (G' : Func N'.D (DesignOutcomes (Set Ω)))
    (Y : Pt (NormalRed.comap S.func N').D) (A B : Set Ω) : ℕ :=
  if hA : A ∈ (designAnswer G' Y).car then
    if hB : B ∈ (designAnswer G' Y).car then
      Sum.elim (fun P : ColoredPartition ↥(designAnswer G' Y).car ℕ =>
          if (⟨A, hA⟩ : ↥(designAnswer G' Y).car) ∈
              @colorSplit _ (ansCarFintype G' Y) (equipColor P) ∧
              (⟨B, hB⟩ : ↥(designAnswer G' Y).car) ∈
              @colorSplit _ (ansCarFintype G' Y) (equipColor P)
            then eqvNat P ⟨A, hA⟩ ⟨B, hB⟩ else 0)
        (fun u : {c : ↥(designAnswer G' Y).car → ↥(designAnswer G' Y).car → ℕ //
            IsUPCCColoring c} => u.1 ⟨A, hA⟩ ⟨B, hB⟩)
        (designAnswer G' Y).obj
    else 0
  else 0

/-- §9.7, Cases 3a1 and 3a2.  The hint of the exit, as a coloring of the ordered pairs of
blocks. -/
noncomputable def designHint (G' : Func N'.D (DesignOutcomes (Set Ω)))
    (Y : Pt (NormalRed.comap S.func N').D)
    (A B : Set ↥Y.car) : ℕ :=
  designHintAmb G' Y (Subtype.val '' A) (Subtype.val '' B)

/-- §9.7, Cases 3a1 and 3a2.  **The part that Procedure Reduce-Part2-by-Color selects**,
read back as a sub-family of the blocks. -/
noncomputable def designSel (G' : Func N'.D (DesignOutcomes (Set Ω)))
    (Y : Pt (NormalRed.comap S.func N').D) : Set (Set ↥Y.car) :=
  letI : Fintype ↥Y.car := Fintype.ofFinite _
  letI : DecidableEq ↥Y.car := Classical.decEq _
  reducePart2ByColorBlk (s := ↥Y.car) (S.obj (comapFib Y)).linkGraph
    ((S.obj (comapFib Y)).blkFam (designFirst G' Y))
    ((S.obj (comapFib Y)).blkFam (designFirst G' Y)ᶜ)

theorem designSel_subset (G' : Func N'.D (DesignOutcomes (Set Ω)))
    (Y : Pt (NormalRed.comap S.func N').D) :
    designSel G' Y ⊆ (S.obj (comapFib Y)).blocks := by
  letI : Fintype ↥Y.car := Fintype.ofFinite _
  letI : DecidableEq ↥Y.car := Classical.decEq _
  rcases reducePart2ByColorBlk_mem (s := ↥Y.car) (S.obj (comapFib Y)).linkGraph
    ((S.obj (comapFib Y)).blkFam (designFirst G' Y))
    ((S.obj (comapFib Y)).blkFam (designFirst G' Y)ᶜ) with h | h <;>
    · show designSel G' Y ⊆ _
      rw [designSel, h]
      exact BlkCaseObj.blkFam_subset _ _

end Babai

namespace Babai

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {N : ℕ}
  {S : BlkDesignSetup Ω N} {N' : NormalRed (DesignInputs (Set Ω) N (3 / 4))}
  {G' : Func N'.D (DesignOutcomes (Set Ω))}
  {Y Z : Pt (NormalRed.comap S.func N').D}

/-! ### Canonicity -/

/-- Membership in the image of a set of points of the answer's carrier. -/
theorem mem_val_image {W : Set (Set Ω)} {S : Set ↥W} {a : Set Ω} :
    a ∈ Subtype.val '' S ↔ ∃ h : a ∈ W, (⟨a, h⟩ : ↥W) ∈ S := by
  constructor
  · rintro ⟨x, hx, rfl⟩; exact ⟨x.2, by simpa using hx⟩
  · rintro ⟨h, hs⟩; exact ⟨⟨a, h⟩, hs, rfl⟩

/-- §9.7, Case 3a, step 2.  The value of the Design Lemma's answer morphism at the point
named by a block `B` is the point named by `f(B)`. -/
theorem ansHom_val (hG' : G'.IsCanonicalEmbedding)
    (f : Hom (NormalRed.comap S.func N').D Y Z) {B : Set ↥Y.car}
    (hmem : Subtype.val '' B ∈ (designAnswer G' Y).car) :
    (((G'.map (comapVerHom f)).1 ⟨Subtype.val '' B, hmem⟩ :
        ↥(designAnswer G' Z).car) : Set Ω) = Subtype.val '' (f.1 '' B) :=
  (hG'.map_restrict (comapVerHom f) ⟨_, hmem⟩).trans
    (comapVerHom_apply_blk f (C := B) (designAnswer_car_subset hG' Y hmem))

/-- The blocks of the answer's carrier at `Z`, named through `f`. -/
theorem ansHom_mk (hG' : G'.IsCanonicalEmbedding)
    (f : Hom (NormalRed.comap S.func N').D Y Z) {B : Set ↥Y.car}
    (hmem : Subtype.val '' B ∈ (designAnswer G' Y).car)
    (hmem' : Subtype.val '' (f.1 '' B) ∈ (designAnswer G' Z).car) :
    (⟨Subtype.val '' (f.1 '' B), hmem'⟩ : ↥(designAnswer G' Z).car)
      = (G'.map (comapVerHom f)).1 ⟨Subtype.val '' B, hmem⟩ :=
  Subtype.ext (ansHom_val hG' f hmem).symm

/-- §9.7, Case 3a1.  A morphism of colored partitions carries a block onto a block. -/
theorem block_image_of_iso {W W' : Set (Set Ω)} {P : ColoredPartition ↥W ℕ}
    {Q : ColoredPartition ↥W' ℕ} {e : ↥W ≃ ↥W'}
    (hpart : ∀ x y, P.part x y ↔ Q.part (e x) (e y)) (x : ↥W) :
    Q.block (e x) = e '' P.block x := by
  ext z
  constructor
  · intro hz
    refine ⟨e.symm z, ?_, by simp⟩
    have hz' : Q.part (e (e.symm z)) (e x) := by simpa using hz
    exact (hpart (e.symm z) x).2 hz'
  · rintro ⟨w, hw, rfl⟩
    exact (hpart w x).1 hw

/-- §9.7, Case 3a1.  The refined coloring of Prop. 7.1.3 is preserved by a morphism of
colored partitions. -/
theorem equipColor_of_iso {W W' : Set (Set Ω)} {P : ColoredPartition ↥W ℕ}
    {Q : ColoredPartition ↥W' ℕ} {e : ↥W ≃ ↥W'}
    (hcol : ∀ x, Q.color (e x) = P.color x)
    (hpart : ∀ x y, P.part x y ↔ Q.part (e x) (e y)) (x : ↥W) :
    equipColor Q (e x) = equipColor P x := by
  rw [equipColor, equipColor, hcol x, block_image_of_iso hpart x,
    Set.ncard_image_of_injective _ e.injective]

end Babai

namespace Babai

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {N : ℕ}
  {S : BlkDesignSetup Ω N} {N' : NormalRed (DesignInputs (Set Ω) N (3 / 4))}
  {G' : Func N'.D (DesignOutcomes (Set Ω))}
  {Y Z : Pt (NormalRed.comap S.func N').D}

/-- Case 3a1: the first part is `Babai.colorSplit` of the refined coloring. -/
theorem designFirst_inl {P : ColoredPartition ↥(designAnswer G' Y).car ℕ}
    (h : (designAnswer G' Y).obj = Sum.inl P) :
    designFirst G' Y = Subtype.val '' (@colorSplit _ (ansCarFintype G' Y) (equipColor P)) := by
  unfold designFirst; rw [h]; rfl

/-- Case 3a2: the first part is the carrier of the UPCC. -/
theorem designFirst_inr {u : {c : ↥(designAnswer G' Y).car → ↥(designAnswer G' Y).car → ℕ //
      IsUPCCColoring c}} (h : (designAnswer G' Y).obj = Sum.inr u) :
    designFirst G' Y = (designAnswer G' Y).car := by
  unfold designFirst; rw [h]; rfl

/-- §9.7, Cases 3a1 and 3a2.  **The first part is canonical.**  A morphism of the category
of versions carries a block into `Babai.designFirst` exactly when the block itself lies in
it: in Case 3a2 because the carrier of the answer is canonical
(`Babai.mem_designAnswer_image`), in Case 3a1 because `Babai.colorSplit` names its part by
color values only (`Babai.colorSplit_image`) and the refined coloring is preserved
(`Babai.equipColor_of_iso`). -/
theorem designFirst_image (hG' : G'.IsCanonicalEmbedding)
    (f : Hom (NormalRed.comap S.func N').D Y Z) {B : Set ↥Y.car}
    (hB : B ∈ (S.obj (comapFib Y)).blocks) :
    Subtype.val '' (f.1 '' B) ∈ designFirst G' Z ↔
      Subtype.val '' B ∈ designFirst G' Y := by
  classical
  have hiso : (G'.map (comapVerHom f)).1 ∈ (DesignOutcomes (Set Ω)).Iso
      (designAnswer G' Y).obj (designAnswer G' Z).obj := (G'.map (comapVerHom f)).2
  have hcar := mem_designAnswer_image hG' f hB
  rcases hY : (designAnswer G' Y).obj with P | u <;>
    rcases hZ : (designAnswer G' Z).obj with Q | v <;>
    rw [hY, hZ] at hiso
  · -- Case 3a1 at both objects
    rw [designFirst_inl hY, designFirst_inl hZ]
    obtain ⟨hcol, hpart⟩ := hiso
    have hequip : ∀ x, equipColor Q ((G'.map (comapVerHom f)).1 x) = equipColor P x :=
      equipColor_of_iso hcol hpart
    have hsplit : (G'.map (comapVerHom f)).1 ''
          (@colorSplit _ (ansCarFintype G' Y) (equipColor P))
        = @colorSplit _ (ansCarFintype G' Z) (equipColor Q) :=
      @colorSplit_image _ _ (ansCarFintype G' Y) (ansCarFintype G' Z) _ _ _ hequip
    rw [mem_val_image, mem_val_image]
    constructor
    · rintro ⟨h', hs⟩
      refine ⟨hcar.1 h', ?_⟩
      rw [← hsplit] at hs
      obtain ⟨w, hw, hwe⟩ := hs
      have : w = ⟨Subtype.val '' B, hcar.1 h'⟩ := by
        apply (G'.map (comapVerHom f)).1.injective
        rw [hwe]
        exact ansHom_mk hG' f (hcar.1 h') h'
      exact this ▸ hw
    · rintro ⟨h, hs⟩
      refine ⟨hcar.2 h, ?_⟩
      rw [← hsplit]
      exact ⟨⟨Subtype.val '' B, h⟩, hs, (ansHom_mk hG' f h (hcar.2 h)).symm⟩
  · exact absurd hiso (Set.notMem_empty _)
  · exact absurd hiso (Set.notMem_empty _)
  · -- Case 3a2 at both objects
    rw [designFirst_inr hY, designFirst_inr hZ]
    exact hcar

end Babai

namespace Babai

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {N : ℕ}
  {S : BlkDesignSetup Ω N} {N' : NormalRed (DesignInputs (Set Ω) N (3 / 4))}
  {G' : Func N'.D (DesignOutcomes (Set Ω))}
  {Y Z : Pt (NormalRed.comap S.func N').D}

open scoped Classical in
/-- Case 3a1: the hint is the three-color coloring of the partition, on the first part. -/
theorem designHintAmb_inl {P : ColoredPartition ↥(designAnswer G' Y).car ℕ}
    (h : (designAnswer G' Y).obj = Sum.inl P) {A B : Set Ω}
    (hA : A ∈ (designAnswer G' Y).car) (hB : B ∈ (designAnswer G' Y).car) :
    designHintAmb G' Y A B =
      (if (⟨A, hA⟩ : ↥(designAnswer G' Y).car) ∈
            @colorSplit _ (ansCarFintype G' Y) (equipColor P) ∧
          (⟨B, hB⟩ : ↥(designAnswer G' Y).car) ∈
            @colorSplit _ (ansCarFintype G' Y) (equipColor P)
        then eqvNat P ⟨A, hA⟩ ⟨B, hB⟩ else 0) := by
  unfold designHintAmb; rw [dif_pos hA, dif_pos hB, h]; rfl

/-- Case 3a2: the hint is the UPCC's own coloring. -/
theorem designHintAmb_inr {u : {c : ↥(designAnswer G' Y).car → ↥(designAnswer G' Y).car → ℕ //
      IsUPCCColoring c}} (h : (designAnswer G' Y).obj = Sum.inr u) {A B : Set Ω}
    (hA : A ∈ (designAnswer G' Y).car) (hB : B ∈ (designAnswer G' Y).car) :
    designHintAmb G' Y A B = u.1 ⟨A, hA⟩ ⟨B, hB⟩ := by
  unfold designHintAmb; rw [dif_pos hA, dif_pos hB, h]; rfl

/-- The hint is `0` off the answer's carrier. -/
theorem designHintAmb_off₁ {A B : Set Ω} (hA : A ∉ (designAnswer G' Y).car) :
    designHintAmb G' Y A B = 0 := by
  unfold designHintAmb; rw [dif_neg hA]

theorem designHintAmb_off₂ {A B : Set Ω} (hB : B ∉ (designAnswer G' Y).car) :
    designHintAmb G' Y A B = 0 := by
  unfold designHintAmb
  by_cases hA : A ∈ (designAnswer G' Y).car
  · rw [dif_pos hA, dif_neg hB]
  · rw [dif_neg hA]

open scoped Classical in
/-- §9.7, Case 3a1.  The three-color coloring is preserved by a morphism of colored
partitions. -/
theorem eqvNat_of_iso {W W' : Set (Set Ω)} {P : ColoredPartition ↥W ℕ}
    {Q : ColoredPartition ↥W' ℕ} {e : ↥W ≃ ↥W'}
    (hpart : ∀ x y, P.part x y ↔ Q.part (e x) (e y)) (x y : ↥W) :
    eqvNat Q (e x) (e y) = eqvNat P x y := by
  unfold eqvNat
  by_cases h : x = y
  · subst h; simp
  · rw [if_neg h, if_neg (fun hc : e x = e y => h (e.injective hc))]
    by_cases hp : P.part x y
    · rw [if_pos hp, if_pos ((hpart x y).1 hp)]
    · rw [if_neg hp, if_neg (fun hc => hp ((hpart x y).2 hc))]

/-- §9.7, Cases 3a1 and 3a2.  **The hint is canonical.**  A morphism of the category of
versions carries the coloring that records the structure found on the first part onto the
same coloring at the other object: the UPCC's coloring is preserved by a morphism of
`Babai.ColoredEdges` (Case 3a2), and the three relations of `Babai.eqvConfig` are
preserved by a morphism of colored partitions (Case 3a1). -/
theorem designHint_image (hG' : G'.IsCanonicalEmbedding)
    (f : Hom (NormalRed.comap S.func N').D Y Z) {A B : Set ↥Y.car}
    (hA : A ∈ (S.obj (comapFib Y)).blocks)
    (hB : B ∈ (S.obj (comapFib Y)).blocks) :
    designHint G' Z (f.1 '' A) (f.1 '' B) = designHint G' Y A B := by
  classical
  have hiso : (G'.map (comapVerHom f)).1 ∈ (DesignOutcomes (Set Ω)).Iso
      (designAnswer G' Y).obj (designAnswer G' Z).obj := (G'.map (comapVerHom f)).2
  have hcA := mem_designAnswer_image hG' f hA
  have hcB := mem_designAnswer_image hG' f hB
  show designHintAmb G' Z (Subtype.val '' (f.1 '' A)) (Subtype.val '' (f.1 '' B))
    = designHintAmb G' Y (Subtype.val '' A) (Subtype.val '' B)
  by_cases hA' : Subtype.val '' A ∈ (designAnswer G' Y).car
  · by_cases hB' : Subtype.val '' B ∈ (designAnswer G' Y).car
    · have hA'' := hcA.2 hA'
      have hB'' := hcB.2 hB'
      have keyA : (⟨Subtype.val '' (f.1 '' A), hA''⟩ : ↥(designAnswer G' Z).car)
          = (G'.map (comapVerHom f)).1 ⟨Subtype.val '' A, hA'⟩ := ansHom_mk hG' f hA' hA''
      have keyB : (⟨Subtype.val '' (f.1 '' B), hB''⟩ : ↥(designAnswer G' Z).car)
          = (G'.map (comapVerHom f)).1 ⟨Subtype.val '' B, hB'⟩ := ansHom_mk hG' f hB' hB''
      rcases hY : (designAnswer G' Y).obj with P | u <;>
        rcases hZ : (designAnswer G' Z).obj with Q | v <;>
        rw [hY, hZ] at hiso
      · -- Case 3a1
        obtain ⟨hcol, hpart⟩ := hiso
        have hequip : ∀ x, equipColor Q ((G'.map (comapVerHom f)).1 x) = equipColor P x :=
          equipColor_of_iso hcol hpart
        have hsplit : (G'.map (comapVerHom f)).1 ''
              (@colorSplit _ (ansCarFintype G' Y) (equipColor P))
            = @colorSplit _ (ansCarFintype G' Z) (equipColor Q) :=
          @colorSplit_image _ _ (ansCarFintype G' Y) (ansCarFintype G' Z) _ _ _ hequip
        have hmemiff : ∀ x : ↥(designAnswer G' Y).car,
            (G'.map (comapVerHom f)).1 x ∈ @colorSplit _ (ansCarFintype G' Z) (equipColor Q)
              ↔ x ∈ @colorSplit _ (ansCarFintype G' Y) (equipColor P) := by
          intro x
          rw [← hsplit]
          constructor
          · rintro ⟨w, hw, hwe⟩
            rwa [(G'.map (comapVerHom f)).1.injective hwe] at hw
          · intro hx; exact ⟨x, hx, rfl⟩
        rw [designHintAmb_inl hY hA' hB', designHintAmb_inl hZ hA'' hB'', keyA, keyB]
        exact if_congr (and_congr (hmemiff _) (hmemiff _)) (eqvNat_of_iso hpart _ _) rfl
      · exact absurd hiso (Set.notMem_empty _)
      · exact absurd hiso (Set.notMem_empty _)
      · -- Case 3a2
        rw [designHintAmb_inr hY hA' hB', designHintAmb_inr hZ hA'' hB'', keyA, keyB]
        exact hiso _ _
    · rw [designHintAmb_off₂ hB', designHintAmb_off₂ (fun hc => hB' (hcB.1 hc))]
  · rw [designHintAmb_off₁ hA', designHintAmb_off₁ (fun hc => hA' (hcA.1 hc))]

end Babai

namespace Babai

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {N : ℕ}
  {S : BlkDesignSetup Ω N} {N' : NormalRed (DesignInputs (Set Ω) N (3 / 4))}
  {G' : Func N'.D (DesignOutcomes (Set Ω))}
  {Y : Pt (NormalRed.comap S.func N').D}

/-! ### Counting -/

/-- The blocks read back off a set `W` of points of `V₂` are in bijection with `W`. -/
noncomputable def blkFamEquiv {s : Set Ω}
    {Case : (Set ↥s → Set ↥s → ℕ) → Set (Set ↥s) → Set (Set ↥s) → Prop}
    (O : BlkCaseObj s Case) {W : Set (Set Ω)} (hW : W ⊆ O.blkAmb) :
    ↥(O.blkFam W) ≃ ↥W where
  toFun B := ⟨Subtype.val '' (B : Set ↥s), B.2.2⟩
  invFun y := ⟨O.blkOf ⟨(y : Set Ω), hW y.2⟩,
    ⟨O.blkOf_mem _, by rw [O.val_image_blkOf]; exact y.2⟩⟩
  left_inv B := Subtype.ext (Set.preimage_image_eq _ Subtype.val_injective)
  right_inv y := Subtype.ext (O.val_image_blkOf _)

/-- The number of points of the answer's carrier, as a cardinality of a set. -/
theorem card_ansCar (G' : Func N'.D (DesignOutcomes (Set Ω)))
    (Y : Pt (NormalRed.comap S.func N').D) :
    @Fintype.card _ (ansCarFintype G' Y) = (designAnswer G' Y).car.ncard := by
  rw [← @Nat.card_eq_fintype_card _ (ansCarFintype G' Y), Nat.card_coe_set_eq]

/-- The first part lies in `V₂`. -/
theorem designFirst_subset (hG' : G'.IsCanonicalEmbedding)
    (Y : Pt (NormalRed.comap S.func N').D) :
    designFirst G' Y ⊆ (S.obj (comapFib Y)).blkAmb := by
  have hsub := designAnswer_car_subset hG' Y
  rcases hY : (designAnswer G' Y).obj with P | u
  · rw [designFirst_inl hY]
    rintro _ ⟨x, -, rfl⟩
    exact hsub x.2
  · rw [designFirst_inr hY]; exact hsub

/-- The number of blocks selected by the first part is the number of its points. -/
theorem ncard_blkFam_designFirst (hG' : G'.IsCanonicalEmbedding)
    (Y : Pt (NormalRed.comap S.func N').D) :
    ((S.obj (comapFib Y)).blkFam (designFirst G' Y)).ncard
      = (designFirst G' Y).ncard :=
  BlkCaseObj.ncard_blkFam _ (fun A hA => designFirst_subset hG' Y hA)

/-- The number of blocks left by the first part. -/
theorem ncard_blkFam_compl_designFirst (hG' : G'.IsCanonicalEmbedding)
    (Y : Pt (NormalRed.comap S.func N').D) :
    ((S.obj (comapFib Y)).blkFam (designFirst G' Y)ᶜ).ncard
      = (S.obj (comapFib Y)).blocks.ncard - (designFirst G' Y).ncard := by
  rw [BlkCaseObj.blkFam_compl, Set.ncard_diff (BlkCaseObj.blkFam_subset _ _)
    (Set.toFinite _), ncard_blkFam_designFirst hG' Y]

theorem ncard_designFirst_le (hG' : G'.IsCanonicalEmbedding)
    (Y : Pt (NormalRed.comap S.func N').D) :
    (designFirst G' Y).ncard ≤ (S.obj (comapFib Y)).blocks.ncard := by
  have h := Set.ncard_le_ncard (designFirst_subset hG' Y) (Set.toFinite _)
  rwa [BlkCaseObj.ncard_blkAmb] at h

/-- Cases 2 and 3 of §9.7 run with at least four blocks. -/
theorem four_le_numBlocks (Y : Pt (NormalRed.comap S.func N').D) :
    4 ≤ (S.obj (comapFib Y)).blocks.ncard := by
  obtain ⟨h1, h2⟩ := (S.obj (comapFib Y)).two_le_d₁_and_add_two_le
    (S.n₂_lt_n₁ (comapFib Y))
  have : (S.obj (comapFib Y)).n₂ = (S.obj (comapFib Y)).blocks.ncard :=
    rfl
  omega

end Babai

namespace Babai

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {N : ℕ}
  {S : BlkDesignSetup Ω N} {N' : NormalRed (DesignInputs (Set Ω) N (3 / 4))}
  {G' : Func N'.D (DesignOutcomes (Set Ω))}
  {Y : Pt (NormalRed.comap S.func N').D}

/-! ### The hint of Case 3a2 -/

/-- §9.7, Case 3a2.  *"The Design lemma returns a UPCC `Y` canonically embedded on a subset
`W ⊆ V₂`. … If it selects `W`, go to Sec. 9.8."*  When Procedure Reduce-Part2-by-Color
selects `W`, the restricted input carries the hint: the UPCC is homogeneous of rank `≥ 3`
(Def. 3.2.1), and the hint coloring of the exit is its own coloring. -/
theorem hasHint_designSel_upcc (hG' : G'.IsCanonicalEmbedding)
    {u : {c : ↥(designAnswer G' Y).car → ↥(designAnswer G' Y).car → ℕ // IsUPCCColoring c}}
    (hY : (designAnswer G' Y).obj = Sum.inr u)
    (hsel : designSel G' Y
      = (S.obj (comapFib Y)).blkFam (designFirst G' Y)) :
    letI : Fintype ↥Y.car := Fintype.ofFinite _
    letI : DecidableEq ↥Y.car := Classical.decEq _
    ((S.obj (comapFib Y)).linkGraph.restrictBlkHint (designSel G' Y)
      (designHint G' Y)).HasHint := by
  classical
  letI : Fintype ↥Y.car := Fintype.ofFinite _
  letI : DecidableEq ↥Y.car := Classical.decEq _
  have hUsub : designSel G' Y ⊆ (S.obj (comapFib Y)).blocks := designSel_subset G' Y
  have hVb : ((S.obj (comapFib Y)).linkGraph.restrictBlkHint (designSel G' Y)
      (designHint G' Y)).blocks = designSel G' Y :=
    Set.inter_eq_self_of_subset_right hUsub
  have hcarsub : (designAnswer G' Y).car ⊆ (S.obj (comapFib Y)).blkAmb :=
    designAnswer_car_subset hG' Y
  have hUeq : designSel G' Y
      = (S.obj (comapFib Y)).blkFam (designAnswer G' Y).car := by
    rw [hsel, designFirst_inr hY]
  set e : ↥((S.obj (comapFib Y)).linkGraph.restrictBlkHint (designSel G' Y)
      (designHint G' Y)).blocks ≃ ↥(designAnswer G' Y).car :=
    (Equiv.setCongr (hVb.trans hUeq)).trans
      (blkFamEquiv (S.obj (comapFib Y)) hcarsub) with he
  have heval : ∀ A, ((e A : ↥(designAnswer G' Y).car) : Set Ω)
      = Subtype.val '' A.1 := fun A => rfl
  obtain ⟨St, hco, huni, hnat⟩ := u.2
  obtain ⟨hhom, hrank⟩ := PartitionStructure.isHomogeneous_and_rank_of_isUniprimitive huni
  refine VColBipBlk.hasHint_of_structure (St.transport e.symm)
    (PartitionStructure.transport_isCoherent _ hco)
    (PartitionStructure.transport_isHomogeneous _ hhom) hrank (fun A B => ?_)
  have hA : A.1 ∈ (S.obj (comapFib Y)).linkGraph.blocks
      ∩ designSel G' Y := A.2
  have hB : B.1 ∈ (S.obj (comapFib Y)).linkGraph.blocks
      ∩ designSel G' Y := B.2
  rw [VColBipBlk.restrictBlkHint_h hA hB]
  show designHintAmb G' Y (Subtype.val '' A.1)
      (Subtype.val '' B.1) = _
  have hmA : Subtype.val '' A.1 ∈ (designAnswer G' Y).car := (e A).2
  have hmB : Subtype.val '' B.1 ∈ (designAnswer G' Y).car := (e B).2
  have hA' : (⟨Subtype.val '' A.1, hmA⟩ : ↥(designAnswer G' Y).car) = e A :=
    Subtype.ext (heval A).symm
  have hB' : (⟨Subtype.val '' B.1, hmB⟩ : ↥(designAnswer G' Y).car) = e B :=
    Subtype.ext (heval B).symm
  rw [designHintAmb_inr hY hmA hmB, ← hnat, hA', hB']
  rfl

end Babai

namespace Babai

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {N : ℕ}
  {S : BlkDesignSetup Ω N} {N' : NormalRed (DesignInputs (Set Ω) N (3 / 4))}
  {G' : Func N'.D (DesignOutcomes (Set Ω))}
  {Y : Pt (NormalRed.comap S.func N').D}

/-! ### The hint of Case 3a1 -/

/-- §9.7, Case 3a1.  *"If color class selected is greater than `3n₂/4`, this color class is
equipartitioned; apply Procedure ImprimitiveCase."*  (The original, `babai-gi.tex`,
lines 3981-3992.)

When Procedure Reduce-Part2-by-Color selects a part that is a single class `S` of the
**refined** coloring of Prop. 7.1.3 and that class is larger than `3n₂/4`, the restricted
input carries the hint.  The structure is `Babai.eqvConfig`: the blocks of the colored
partition that lie inside `S` all have one common size `m`, which is what the refinement
buys; `m ≥ 2` is admissibility (Def. 7.1.1), and there are at least two of them because
`ρ(Π) ≤ (3/4)n₂ < |S|`. -/
theorem hasHint_designSel_eqv (hG' : G'.IsCanonicalEmbedding)
    (hgood : ∀ (X : Pt (DesignInputs (Set Ω) N (3 / 4))) (A : N'.D.Obj X.car),
      N'.base A = X.obj → IsDesignOutcome (3 / 4) X.car (G'.obj ⟨X.car, A⟩))
    {P : ColoredPartition ↥(designAnswer G' Y).car ℕ}
    (hY : (designAnswer G' Y).obj = Sum.inl P) {k : ℕ}
    (hk : @colorSplit _ (ansCarFintype G' Y) (equipColor P) = colorClassOf (equipColor P) k)
    (hbig : 3 * (S.obj (comapFib Y)).blocks.ncard
      < 4 * (@colorSplit _ (ansCarFintype G' Y) (equipColor P)).ncard)
    (hsel : designSel G' Y
      = (S.obj (comapFib Y)).blkFam (designFirst G' Y)) :
    letI : Fintype ↥Y.car := Fintype.ofFinite _
    letI : DecidableEq ↥Y.car := Classical.decEq _
    ((S.obj (comapFib Y)).linkGraph.restrictBlkHint (designSel G' Y)
      (designHint G' Y)).HasHint := by
  classical
  letI : Fintype ↥Y.car := Fintype.ofFinite _
  letI : DecidableEq ↥Y.car := Classical.decEq _
  letI : Fintype ↥(designAnswer G' Y).car := ansCarFintype G' Y
  -- the answer is a colored `3/4`-partition of the whole of `V₂`
  have hout := designAnswer_isDesignOutcome hgood Y
  unfold IsDesignOutcome at hout
  rw [hY] at hout
  obtain ⟨hcareq, hP⟩ := hout
  set Cls : Set ↥(designAnswer G' Y).car := colorClassOf (equipColor P) k with hS
  rw [hk] at hbig
  have hFeq : designFirst G' Y = Subtype.val '' Cls := by rw [designFirst_inl hY, hk]
  have hSsub : Subtype.val '' Cls ⊆ (S.obj (comapFib Y)).blkAmb := by
    rw [← hFeq]; exact designFirst_subset hG' Y
  have hUeq : designSel G' Y
      = (S.obj (comapFib Y)).blkFam (Subtype.val '' Cls) := by rw [hsel, hFeq]
  have hUsub : designSel G' Y ⊆ (S.obj (comapFib Y)).blocks := designSel_subset G' Y
  have hVb : ((S.obj (comapFib Y)).linkGraph.restrictBlkHint (designSel G' Y)
      (designHint G' Y)).blocks = designSel G' Y :=
    Set.inter_eq_self_of_subset_right hUsub
  -- membership in the selected part
  have hmemU : ∀ A : Set ↥Y.car, A ∈ designSel G' Y ↔
      A ∈ (S.obj (comapFib Y)).blocks ∧
        ∃ h : Subtype.val '' A ∈ (designAnswer G' Y).car,
          (⟨Subtype.val '' A, h⟩ : ↥(designAnswer G' Y).car) ∈ Cls := by
    intro A
    rw [hUeq]
    exact and_congr Iff.rfl mem_val_image
  -- the size of a block of the partition inside `Cls`
  set m : ℕ := (Nat.unpair k).2 with hm
  have hblkm : ∀ x ∈ Cls, (P.block x).ncard = m := by
    intro x hx
    have hxk : equipColor P x = k := hx
    rw [hm, ← hxk, equipColor, Nat.unpair_pair]
  have hcolS : ∀ x ∈ Cls, ∀ y ∈ Cls, P.color x = P.color y := by
    intro x hx y hy
    have h1 : equipColor P x = k := hx
    have h2 : equipColor P y = k := hy
    exact ((equipColor_eq_iff P x y).1 (h1.trans h2.symm)).1
  have hblockS : ∀ x ∈ Cls, P.block x ⊆ Cls := by
    intro x hx y hy
    have hxk : equipColor P x = k := hx
    show equipColor P y = k
    rw [← hxk]
    exact (equipColor_eq_iff P y x).2 ⟨P.part_le_color hy, by rw [P.block_eq_of_part hy]⟩
  -- the numbers
  have hcard : @Fintype.card _ (ansCarFintype G' Y) = (designAnswer G' Y).car.ncard :=
    card_ansCar G' Y
  have hn₂ : (designAnswer G' Y).car.ncard
      = (S.obj (comapFib Y)).blocks.ncard := by
    rw [hcareq, BlkCaseObj.ncard_blkAmb]; rfl
  have hSimg : (Subtype.val '' Cls).ncard = Cls.ncard :=
    Set.ncard_image_of_injective _ Subtype.val_injective
  have h4 : 4 ≤ (S.obj (comapFib Y)).blocks.ncard := four_le_numBlocks Y
  have hSge : 4 ≤ Cls.ncard := by omega
  obtain ⟨x₀, hx₀⟩ : Cls.Nonempty := by
    rw [← Set.ncard_pos (Set.toFinite _)] at *; omega
  -- `m ≥ 2` by admissibility
  have h2m : 2 ≤ m := by
    rw [← hblkm x₀ hx₀]
    refine hP.1 x₀ ?_
    have hsub : Cls ⊆ P.colorClass (P.color x₀) := fun y hy => (hcolS y hy x₀ hx₀)
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    omega
  -- at least two blocks, because `ρ(Π) ≤ (3/4)n₂ < |Cls|`
  have hrho : 4 * P.rho ≤ 3 * (S.obj (comapFib Y)).blocks.ncard := by
    have h := hP.2
    rw [hcard, hn₂] at h
    have : (4 : ℝ) * (P.rho : ℝ)
        ≤ 3 * ((S.obj (comapFib Y)).blocks.ncard : ℝ) := by linarith
    exact_mod_cast this
  have hmrho : m ≤ P.rho := by
    rw [← hblkm x₀ hx₀]; exact P.ncard_block_le_rho x₀
  have hmlt : m < Cls.ncard := by omega
  -- the number of blocks of the restriction
  have hUcard : ((S.obj (comapFib Y)).linkGraph.restrictBlkHint
      (designSel G' Y) (designHint G' Y)).numBlocks = Cls.ncard := by
    rw [VColBipBlk.restrictBlkHint_numBlocks hUsub, hUeq,
      BlkCaseObj.ncard_blkFam _ (fun A hA => hSsub hA), hSimg]
  -- the relation
  refine VColBipBlk.hasHint_of_eqvPart
    (r := fun A B => ∃ (hA : Subtype.val '' A ∈ (designAnswer G' Y).car)
        (hB : Subtype.val '' B ∈ (designAnswer G' Y).car),
      P.part ⟨Subtype.val '' A, hA⟩ ⟨Subtype.val '' B, hB⟩)
    (m := m) (fun A hA => ?_) (fun A hA B hB hr => ?_) (fun A hA B hB C hC hab hbc => ?_)
    (fun A hA => ?_) h2m (by rw [hUcard]; exact hmlt) (fun A hA B hB => ?_)
  · obtain ⟨-, h, -⟩ := (hmemU A).1 hA.2
    exact ⟨h, h, P.part.refl _⟩
  · obtain ⟨hA', hB', hp⟩ := hr
    exact ⟨hB', hA', P.part.symm hp⟩
  · obtain ⟨hA', hB', hp⟩ := hab
    obtain ⟨hB'', hC', hq⟩ := hbc
    exact ⟨hA', hC', P.part.trans hp hq⟩
  · -- the class of `A` inside the selected part has `m` members
    obtain ⟨-, hAc, hAS⟩ := (hmemU A).1 hA.2
    -- every block of the partition inside `Cls` is named by a block of the input
    have hnamed : ∀ y : ↥(designAnswer G' Y).car, y ∈ Cls →
        ∃ B : Set ↥Y.car, B ∈ (S.obj (comapFib Y)).blocks ∧
          Subtype.val '' B = (y : Set Ω) := by
      intro y hy
      have hyamb : (y : Set Ω) ∈ (S.obj (comapFib Y)).blkAmb := hcareq ▸ y.2
      obtain ⟨B, hB, hBy⟩ := hyamb
      exact ⟨B, hB, hBy⟩
    have hgen : ∀ T : Set (Set ↥Y.car),
        (∀ B : Set ↥Y.car, B ∈ T ↔ ∃ y : ↥(designAnswer G' Y).car,
          y ∈ P.block ⟨Subtype.val '' A, hAc⟩ ∧ Subtype.val '' B = (y : Set Ω)) →
        T.ncard = m := by
      intro T hT
      have himg : Set.image Subtype.val '' T
          = Subtype.val '' (P.block ⟨Subtype.val '' A, hAc⟩) := by
        ext C
        constructor
        · rintro ⟨B, hB, rfl⟩
          obtain ⟨y, hy, hyB⟩ := (hT B).1 hB
          exact ⟨y, hy, hyB.symm⟩
        · rintro ⟨y, hy, rfl⟩
          obtain ⟨B, -, hB⟩ := hnamed y (hblockS _ hAS hy)
          exact ⟨B, (hT B).2 ⟨y, hy, hB⟩, hB⟩
      rw [← Set.ncard_image_of_injective T (Set.image_injective.2 Subtype.val_injective),
        himg, Set.ncard_image_of_injective _ Subtype.val_injective]
      exact hblkm _ hAS
    refine hgen _ (fun B => ?_)
    constructor
    · rintro ⟨hBmem, h₁, h₂, hp⟩
      exact ⟨⟨Subtype.val '' B, h₂⟩, P.part.symm hp, rfl⟩
    · rintro ⟨y, hy, hyB⟩
      have hyS : y ∈ Cls := hblockS _ hAS hy
      have hBc : Subtype.val '' B ∈ (designAnswer G' Y).car := hyB ▸ y.2
      have hBy : (⟨Subtype.val '' B, hBc⟩ : ↥(designAnswer G' Y).car) = y :=
        Subtype.ext hyB
      obtain ⟨B', hB', hB'y⟩ := hnamed y hyS
      have hBB' : B = B' :=
        (Set.image_injective.2 Subtype.val_injective) (hyB.trans hB'y.symm)
      have hBU : B ∈ designSel G' Y :=
        (hmemU B).2 ⟨hBB' ▸ hB', hBc, by rw [hBy]; exact hyS⟩
      have hBblk : B ∈ (S.obj (comapFib Y)).blocks := hBB' ▸ hB'
      refine ⟨⟨hBblk, hBU⟩, hAc, hBc, ?_⟩
      have h2 : P.part (⟨Subtype.val '' A, hAc⟩ : ↥(designAnswer G' Y).car) y :=
        P.part.symm hy
      rwa [← hBy] at h2
  · -- the hint coloring is the three-color coloring of the relation
    obtain ⟨-, hAc, hAS⟩ := (hmemU A).1 hA.2
    obtain ⟨-, hBc, hBS⟩ := (hmemU B).1 hB.2
    refine (VColBipBlk.restrictBlkHint_h (X := (S.obj (comapFib Y)).linkGraph)
      hA hB).trans ?_
    refine (designHintAmb_inl hY hAc hBc).trans ?_
    rw [if_pos ⟨hk ▸ hAS, hk ▸ hBS⟩]
    show (if (⟨Subtype.val '' A, hAc⟩ : ↥(designAnswer G' Y).car)
        = ⟨Subtype.val '' B, hBc⟩ then 0
      else if P.part (⟨Subtype.val '' A, hAc⟩ : ↥(designAnswer G' Y).car)
          ⟨Subtype.val '' B, hBc⟩ then 1 else 2) = _
    have hiff : (⟨Subtype.val '' A, hAc⟩ : ↥(designAnswer G' Y).car)
        = ⟨Subtype.val '' B, hBc⟩ ↔ A = B := by
      constructor
      · intro h
        exact Set.image_injective.2 Subtype.val_injective (congrArg Subtype.val h)
      · rintro rfl; rfl
    by_cases hAB : A = B
    · rw [if_pos (hiff.2 hAB), if_pos hAB]
    · rw [if_neg (fun hc => hAB (hiff.1 hc)), if_neg hAB]
      by_cases hp : P.part (⟨Subtype.val '' A, hAc⟩ : ↥(designAnswer G' Y).car)
          ⟨Subtype.val '' B, hBc⟩
      · rw [if_pos hp, if_pos (show ∃ (h₁ : Subtype.val '' A ∈ (designAnswer G' Y).car)
          (h₂ : Subtype.val '' B ∈ (designAnswer G' Y).car),
          P.part ⟨Subtype.val '' A, h₁⟩ ⟨Subtype.val '' B, h₂⟩ from ⟨hAc, hBc, hp⟩)]
      · refine (if_neg hp).trans (if_neg ?_).symm
        rintro ⟨h₁, h₂, hq⟩
        exact hp hq

end Babai

namespace Babai

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {N : ℕ}
  {S : BlkDesignSetup Ω N} {N' : NormalRed (DesignInputs (Set Ω) N (3 / 4))}
  {G' : Func N'.D (DesignOutcomes (Set Ω))}
  {Y : Pt (NormalRed.comap S.func N').D}

/-! ### The progress made -/

/-- Case 3a1: *"a canonical colored `3/4`-partition of `V₂`"* lives on the whole of `V₂`. -/
theorem ansCar_eq_blkAmb
    (hgood : ∀ (X : Pt (DesignInputs (Set Ω) N (3 / 4))) (A : N'.D.Obj X.car),
      N'.base A = X.obj → IsDesignOutcome (3 / 4) X.car (G'.obj ⟨X.car, A⟩))
    {P : ColoredPartition ↥(designAnswer G' Y).car ℕ}
    (hY : (designAnswer G' Y).obj = Sum.inl P) :
    (designAnswer G' Y).car = (S.obj (comapFib Y)).blkAmb := by
  have hout := designAnswer_isDesignOutcome hgood Y
  unfold IsDesignOutcome at hout
  rw [hY] at hout
  exact hout.1

/-- Case 3a2: *"a UPCC canonically embedded on a subset `W ⊆ V₂` with `|W| ≥ (3/4)n₂`"*. -/
theorem three_mul_numBlocks_lt
    (hgood : ∀ (X : Pt (DesignInputs (Set Ω) N (3 / 4))) (A : N'.D.Obj X.car),
      N'.base A = X.obj → IsDesignOutcome (3 / 4) X.car (G'.obj ⟨X.car, A⟩))
    {u : {c : ↥(designAnswer G' Y).car → ↥(designAnswer G' Y).car → ℕ // IsUPCCColoring c}}
    (hY : (designAnswer G' Y).obj = Sum.inr u) :
    3 * (S.obj (comapFib Y)).blocks.ncard < 4 * (designAnswer G' Y).car.ncard := by
  have hout := designAnswer_isDesignOutcome hgood Y
  unfold IsDesignOutcome at hout
  rw [hY] at hout
  obtain ⟨-, hlt⟩ := hout
  rw [BlkCaseObj.ncard_blkAmb] at hlt
  have hlt' : (3 : ℝ) * ((S.obj (comapFib Y)).blocks.ncard : ℝ)
      < 4 * ((designAnswer G' Y).car.ncard : ℝ) := by
    have hn : ((S.obj (comapFib Y)).n₂ : ℝ)
        = ((S.obj (comapFib Y)).blocks.ncard : ℝ) := rfl
    rw [hn] at hlt
    linarith
  exact_mod_cast hlt'

/-- §9.7, Cases 3a1 and 3a2.  **The progress made by the exit.**  Either the selected part
has at most `9n₂/10` blocks — *"significant progress: `n₂` is reduced"* — or it carries the
hint and has at most `n₂` blocks — *"`X₂` moves from clique to UPCC while `n₂` does not
increase"* (§9.5, version 2.5, lines 4176-4181).

The four sub-branches are the paper's: Case 3a2 with `V₂ ∖ W` selected (`|U| ≤ n₂/4`),
Case 3a2 with `W` selected (the UPCC is the hint), Case 3a1 with a selected part of at
most `3n₂/4` blocks, and Case 3a1 with a selected class larger than `3n₂/4`, which
`Babai.colorSplit_alternative` makes a single class of the refined coloring and which is
therefore equipartitioned. -/
theorem designSel_prog (hG' : G'.IsCanonicalEmbedding)
    (hgood : ∀ (X : Pt (DesignInputs (Set Ω) N (3 / 4))) (A : N'.D.Obj X.car),
      N'.base A = X.obj → IsDesignOutcome (3 / 4) X.car (G'.obj ⟨X.car, A⟩))
    (Y : Pt (NormalRed.comap S.func N').D) :
    letI : Fintype ↥Y.car := Fintype.ofFinite _
    letI : DecidableEq ↥Y.car := Classical.decEq _
    10 * (designSel G' Y).ncard ≤ 9 * (S.obj (comapFib Y)).blocks.ncard ∨
      ((designSel G' Y).ncard ≤ (S.obj (comapFib Y)).blocks.ncard ∧
        ((S.obj (comapFib Y)).linkGraph.restrictBlkHint (designSel G' Y)
          (designHint G' Y)).HasHint) := by
  classical
  letI : Fintype ↥Y.car := Fintype.ofFinite _
  letI : DecidableEq ↥Y.car := Classical.decEq _
  letI : Fintype ↥(designAnswer G' Y).car := ansCarFintype G' Y
  have hFle := ncard_designFirst_le hG' Y
  have hF := ncard_blkFam_designFirst hG' Y
  have hFc := ncard_blkFam_compl_designFirst hG' Y
  have hcard : @Fintype.card _ (ansCarFintype G' Y) = (designAnswer G' Y).car.ncard :=
    card_ansCar G' Y
  rcases reducePart2ByColorBlk_mem (s := ↥Y.car) (S.obj (comapFib Y)).linkGraph
      ((S.obj (comapFib Y)).blkFam (designFirst G' Y))
      ((S.obj (comapFib Y)).blkFam (designFirst G' Y)ᶜ) with hsel | hsel
  · -- the first part is selected
    have hUc : (designSel G' Y).ncard = (designFirst G' Y).ncard := by
      rw [show designSel G' Y
        = (S.obj (comapFib Y)).blkFam (designFirst G' Y) from hsel]
      exact hF
    rcases hY : (designAnswer G' Y).obj with P | u
    · -- Case 3a1
      have hFcs : (designFirst G' Y).ncard
          = (@colorSplit _ (ansCarFintype G' Y) (equipColor P)).ncard := by
        rw [designFirst_inl hY, Set.ncard_image_of_injective _ Subtype.val_injective]
      have hn₂ : (designAnswer G' Y).car.ncard
          = (S.obj (comapFib Y)).blocks.ncard := by
        rw [ansCar_eq_blkAmb hgood hY, BlkCaseObj.ncard_blkAmb]; rfl
      by_cases hsm : 4 * (@colorSplit _ (ansCarFintype G' Y) (equipColor P)).ncard
          ≤ 3 * (S.obj (comapFib Y)).blocks.ncard
      · left; omega
      · rcases colorSplit_alternative (α := ↥(designAnswer G' Y).car) (equipColor P) with
          hsmall | ⟨k, hk⟩
        · exact absurd (by omega : 4 * (@colorSplit _ (ansCarFintype G' Y)
            (equipColor P)).ncard ≤ 3 * (S.obj (comapFib Y)).blocks.ncard) hsm
        · exact Or.inr ⟨by omega,
            hasHint_designSel_eqv hG' hgood hY hk (by omega) hsel⟩
    · -- Case 3a2, `W` selected
      have h34 := three_mul_numBlocks_lt hgood hY
      exact Or.inr ⟨by rw [hUc]; exact hFle, hasHint_designSel_upcc hG' hY hsel⟩
  · -- the second part is selected
    left
    have hUc : (designSel G' Y).ncard
        = (S.obj (comapFib Y)).blocks.ncard - (designFirst G' Y).ncard := by
      rw [show designSel G' Y
        = (S.obj (comapFib Y)).blkFam (designFirst G' Y)ᶜ from hsel]
      exact hFc
    rcases hY : (designAnswer G' Y).obj with P | u
    · -- Case 3a1: the complement of `Babai.colorSplit` is at most `3n₂/4`
      have hFcs : (designFirst G' Y).ncard
          = (@colorSplit _ (ansCarFintype G' Y) (equipColor P)).ncard := by
        rw [designFirst_inl hY, Set.ncard_image_of_injective _ Subtype.val_injective]
      have hn₂ : (designAnswer G' Y).car.ncard
          = (S.obj (comapFib Y)).blocks.ncard := by
        rw [ansCar_eq_blkAmb hgood hY, BlkCaseObj.ncard_blkAmb]; rfl
      have hcompl := four_mul_ncard_compl_colorSplit_le
        (α := ↥(designAnswer G' Y).car) (equipColor P)
      have hsum := Set.ncard_add_ncard_compl
        (@colorSplit _ (ansCarFintype G' Y) (equipColor P))
      rw [@Nat.card_eq_fintype_card _ (ansCarFintype G' Y)] at hsum
      omega
    · -- Case 3a2: `|V₂ ∖ W| ≤ n₂/4`
      have h34 := three_mul_numBlocks_lt hgood hY
      have hFcar : (designFirst G' Y).ncard = (designAnswer G' Y).car.ncard := by
        rw [designFirst_inr hY]
      omega

end Babai

namespace Babai

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {N : ℕ}
  {S : BlkDesignSetup Ω N} {N' : NormalRed (DesignInputs (Set Ω) N (3 / 4))}
  {G' : Func N'.D (DesignOutcomes (Set Ω))}
  {Y Z : Pt (NormalRed.comap S.func N').D}

/-! ### The selected part is canonical -/

/-- The first part, read back as a sub-family of the blocks, is canonical. -/
theorem blkFam_designFirst_image (hG' : G'.IsCanonicalEmbedding)
    (f : Hom (NormalRed.comap S.func N').D Y Z) (B : Set ↥Y.car) :
    f.1 '' B ∈ (S.obj (comapFib Z)).blkFam (designFirst G' Z) ↔
      B ∈ (S.obj (comapFib Y)).blkFam (designFirst G' Y) := by
  have hm := S.morph (comapFibHom f)
  by_cases hB : B ∈ (S.obj (comapFib Y)).blocks
  · exact and_congr (iff_of_true ((hm.blocks B).2 hB) hB) (designFirst_image hG' f hB)
  · exact iff_of_false (fun hc => hB ((hm.blocks B).1 hc.1)) (fun hc => hB hc.1)

/-- The same for the second of the two parts. -/
theorem blkFam_compl_designFirst_image (hG' : G'.IsCanonicalEmbedding)
    (f : Hom (NormalRed.comap S.func N').D Y Z) (B : Set ↥Y.car) :
    f.1 '' B ∈ (S.obj (comapFib Z)).blkFam (designFirst G' Z)ᶜ ↔
      B ∈ (S.obj (comapFib Y)).blkFam (designFirst G' Y)ᶜ := by
  have hm := S.morph (comapFibHom f)
  by_cases hB : B ∈ (S.obj (comapFib Y)).blocks
  · exact and_congr (iff_of_true ((hm.blocks B).2 hB) hB)
      (not_congr (designFirst_image hG' f hB))
  · exact iff_of_false (fun hc => hB ((hm.blocks B).1 hc.1)) (fun hc => hB hc.1)

/-- §9.7, Cases 3a1 and 3a2.  **The part selected by Procedure Reduce-Part2-by-Color is
canonical.**  Both parts handed to the procedure are canonical
(`Babai.designFirst_image`), and the procedure itself is
(`Babai.reducePart2ByColorBlk_image`). -/
theorem designSel_image (hG' : G'.IsCanonicalEmbedding)
    (f : Hom (NormalRed.comap S.func N').D Y Z) (B : Set ↥Y.car) :
    f.1 '' B ∈ designSel G' Z ↔ B ∈ designSel G' Y := by
  classical
  letI : Fintype ↥Y.car := Fintype.ofFinite _
  letI : DecidableEq ↥Y.car := Classical.decEq _
  letI : Fintype ↥Z.car := Fintype.ofFinite _
  letI : DecidableEq ↥Z.car := Classical.decEq _
  show f.1 '' B ∈ reducePart2ByColorBlk (s := ↥Z.car)
      (S.obj (comapFib Z)).linkGraph
      ((S.obj (comapFib Z)).blkFam (designFirst G' Z))
      ((S.obj (comapFib Z)).blkFam (designFirst G' Z)ᶜ) ↔
    B ∈ reducePart2ByColorBlk (s := ↥Y.car) (S.obj (comapFib Y)).linkGraph
      ((S.obj (comapFib Y)).blkFam (designFirst G' Y))
      ((S.obj (comapFib Y)).blkFam (designFirst G' Y)ᶜ)
  exact reducePart2ByColorBlk_image
    (BlkCaseObj.linkGraph_isIsoTo (S.morph (comapFibHom f)))
    (blkFam_designFirst_image hG' f) (blkFam_compl_designFirst_image hG' f) B

/-- §9.7, Cases 3a1 and 3a2.  Procedure Reduce-Part2-by-Color leaves a symmetry defect of
`V₁` of at least `(n₁ − 1)/2` on the selected part (Lemma 9.3.2): the two parts cover the
blocks (`Babai.BlkCaseObj.blkFam_union_cover`) and there are no twins in `V₁`
(`Babai.BlkCaseObj.linkGraph_noTwins`). -/
theorem designSel_symDefect (Y : Pt (NormalRed.comap S.func N').D) :
    letI : Fintype ↥Y.car := Fintype.ofFinite _
    letI : DecidableEq ↥Y.car := Classical.decEq _
    (((S.obj (comapFib Y)).n₁ : ℚ) - 1) / 2 ≤
      ((S.obj (comapFib Y)).linkGraph.restrictBlk (designSel G' Y)).symDefect₁ := by
  classical
  letI instF : Fintype ↥Y.car := Fintype.ofFinite _
  letI instD : DecidableEq ↥Y.car := Classical.decEq _
  show (((S.obj (comapFib Y)).n₁ : ℚ) - 1) / 2 ≤
    ((S.obj (comapFib Y)).linkGraph.restrictBlk (designSel G' Y)).symDefect₁
  rw [designSel]
  have he : instD = fun a b => Subtype.instDecidableEq a b :=
    funext fun _ => funext fun _ => Subsingleton.elim _ _
  have hno : ∀ x, (S.obj (comapFib Y)).linkGraph.part₁ x →
      ∀ y, (S.obj (comapFib Y)).linkGraph.part₁ y →
        ¬ @IsTwin ↥Y.car instD (S.obj (comapFib Y)).linkGraph.Aut x y := by
    rw [he]; exact BlkCaseObj.linkGraph_noTwins _
  exact @reducePart2ByColorBlk_spec ↥Y.car instF instD ℕ _
    (S.obj (comapFib Y)).linkGraph hno _ _
    (BlkCaseObj.blkFam_union_cover (S.obj (comapFib Y)) (designFirst G' Y))

end Babai
