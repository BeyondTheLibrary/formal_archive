/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 15, line 4d with a dominant color class: the Master's data of Procedure Align, lines
7–11, built from the machine's computation.
-/
import Workspace.Algo.PrimitiveLine4dDom
import Workspace.Master.AlignDominantKer
import Workspace.Master.AlignOtherClasses
import Workspace.Algo.AlignDomHintPsi

/-!
# Line 4d with a dominant color class: the Master's data from the machine's computation

`Algo.line4dDomOps_match_small` and `Algo.line4dDomOps_match_large` match the carrier of line
4d against the round of any Master data `D` that the machine's header describes
(`Algo.ADDescribes`, `Algo.AVDescribes`). This file builds that `D` from the machine's
computation and proves the descriptions, as `Algo.exists_line4dData` does when line 6 finds no
dominant class.

**What the machine computes, and what it is on the Master's side.**

* The dominant color `dc` of line 6 (`Algo.alignRDomColor`): its class is the Master's dominant
  class `Δ_j` (`Algo.setOf_labAt_eq_domColor`).
* `m*` (`Algo.alignRMs`): in case (A) the size of the class over the size of the block of its
  first point, in case (B) the degree of the Johnson scheme. These are the Master's `m*`
  (`Babai.exists_alignDominantRoundData_A`, `_B`).
* The generators of `ker ϕ*` (`Algo.alignKerGens`): the preimage of the automorphisms of a
  colored partition `K` of `Γ` (`Algo.decGroup_alignKerGens`). In case (A) the automorphisms
  of `K` are the automorphisms of `X'` that map every block inside `Δ_j` to itself
  (`Algo.colPartIso_alignKerPartA_iff`); in case (B) they are the permutations that fix `Δ_j`
  pointwise, and those are automorphisms of `X'` (`Babai.mem_structAut_inr_of_fix`).
* The orbit lists (`Algo.alignDomOrbits`, `Algo.adKO`) and the cosets of `ker ϕ*`
  (`Algo.adReps` at the least element of a coset): these are the fields of the Master's
  `Babai.AlignDominantEnum` (`Algo.line4dDomEnum`), and they meet its specification.

**The nontrivial case.**  Line 7 (A) of Procedure Align asks that `X` give a *nontrivial*
equipartition of `Δ_j`: at least two blocks. The machine's test of line 6
(`Algo.alignRHasDom`) does not look at the blocks. When `Δ_j` is a single block the Master has
no data of lines 7–11 (there is no `Γ*` with a giant representation), and the paper's line 6
only starts the Chain Rule with the window `Ω(Δ_j)`. So the construction here asks for
`2 ≤ m*` (`Algo.line4dDomNontriv`), which holds in case (B) always.
-/

namespace Algo
open RAM RAM.Targets Babai Equiv MulAction
open scoped Pointwise

/-! ## The data of lines 7–11 from the machine's computation -/

section RoundData

variable {n m : ℕ} {A : RawAction} {ϕ : decGroup n A.1.2 →* Perm (Fin m)}
  [MulAction (Perm (Fin m)) (Pt (SplitOutcomes (Fin m)))]

open scoped Classical in
/-- §14.1, **lines 6–10 on the machine**: when line 6 finds a dominant color class and the
structure on it is nontrivial (`2 ≤ m*`), the Master has data of lines 7–11 whose group `G*`
is `ϕ⁻¹(Aut(X'))`, whose window is the machine's dominant window, whose `m*` is the machine's
`m*`, and whose `ker ϕ*` is the group the machine's generators generate.

In case (A) the Master's data is `Babai.exists_alignDominantRoundData_A` at the first dominant
point `x` of the machine and a point `y` of the class outside the block of `x` (there is one,
since `m* ≥ 2`); in case (B) it is `Babai.exists_alignDominantRoundData_B` at the machine's
identification of `Δ_j` with `(Γ* choose t*)`. -/
theorem exists_domRoundData_alpha (hA : RawAction.WF n m A ϕ) (hG : IsTransitive (decGroup n A.1.2))
    (hϕ : IsGiantRep ϕ) (hvl : VeryLargeK m (maxOrbitLength (decGroup n A.1.2))) {t : ℕ}
    (ht : ∀ u : Fin n, tPoint ϕ u = t) (hK : IsCatAction (SplitOutcomes (Fin m)))
    {o : RawAlignOutcome} {X' : Pt (SplitOutcomes (Fin m))} (hX : decAlignOutcome m o = some X')
    {α : ℝ} (hα : 1 / 2 < α)
    (hZ : IsSplitOutcome α (Set.univ : Set (Fin m)) X') (hm : 217 ≤ m) (hmn : m ≤ n)
    (hhd : alignRHasDom (alignRColorOf (A, o)) = true) (hnt : 2 ≤ alignRMs (A, o)) :
    ∃ Dd : AlignDominantRoundData (Fin n),
      Dd.toAlignDominant.m = m ∧
      Dd.toAlignDominant.Gs = preimageSubgroup ϕ (structAut X') ∧
      Dd.toAlignDominant.window = winSet n (alignRDomWindow (alignRColorOf (A, o),
        alignRDomColor (alignRColorOf (A, o)))) ∧
      Dd.toAlignDominant.ms = alignRMs (A, o) ∧
      Dd.ker = decGroup n (alignKerGens (A, o)) ∧
      ∃ f : Fin (alignDomKeys (A, o)).length ≃ Fin Dd.toAlignDominant.ms,
        ∀ τ (hτ : τ ∈ Dd.toAlignDominant.Gs) (hG : τ ∈ decGroup n A.1.2),
          alignDomPsi ((A, o), encPerm m (ϕ ⟨τ, hG⟩)) =
            encPerm _ (Equiv.permCongr f.symm (Dd.toAlignDominant.phis ⟨τ, hτ⟩)) := by
  have hg : A.2.1.length = m := hA.2.1
  have hn96 : 96 ≤ Fintype.card (Fin n) := by rw [Fintype.card_fin]; omega
  set lab := alignOutcomeLab (A.2.1, o) with hlab
  have hhd' : alignRHasDom (A, lab) = true := hhd
  set dc := alignRDomColor (A, lab) with hdcdef
  have hq : alignRColorOf (A, o) = (A, lab) := rfl
  have hwin : winSet n (alignRDomWindow ((A, lab), dc)) =
      omegaOf ϕ {γ : Fin m | labAt lab (γ : ℕ) = dc} :=
    winSet_alignRDomWindow_of_wf hA hϕ hvl lab dc
  have hdomR : m < 2 * {γ : Fin m | labAt lab (γ : ℕ) = dc}.ncard :=
    alignRDomColor_dominant_of_wf hA hhd'
  set γ₀ : Fin m := ⟨(alignRDomPoints (A, lab)).getD 0 0, alignRDomFirst_lt hg hhd'⟩ with hγ₀
  have hdc : dc = labAt lab (γ₀ : ℕ) := rfl
  -- the class of the label `dc` is the class of the color of `γ₀`
  have hcls : ∀ γ : Fin m, labAt lab (γ : ℕ) = dc ↔ alignColor X' γ = alignColor X' γ₀ := by
    intro γ
    rw [hdc]
    exact alignOutcomeLab_eq_iff hg hX γ γ₀
  -- `G* = ϕ⁻¹(Aut(X'))` preserves the dominant class (line 4, *"canonical"*)
  have hpres : ∀ τ (_ : τ ∈ preimageSubgroup ϕ (structAut X')) (hG : τ ∈ decGroup n A.1.2)
      (γ : Fin m), labAt lab ((ϕ ⟨τ, hG⟩ γ : Fin m) : ℕ) = dc ↔ labAt lab (γ : ℕ) = dc := by
    intro τ hτ hG γ
    obtain ⟨_, hS⟩ := mem_preimageSubgroup.1 hτ
    have h1 := congrArg Subtype.val (alignIdx_smul hK (mem_structAut.1 hS) γ)
    simp only [alignIdx_coe] at h1
    rw [hcls, hcls, h1]
  rw [hq]
  rcases decAlignOutcome_cases hX with ⟨P, rfl, rfl⟩ | ⟨J, hJ, rfl, rfl⟩
  · -- case (A): a colored partition
    set P' := decAlignPart m P with hP'
    have hXe : decAlignPartition m P = ⟨Set.univ, Sum.inl P'⟩ := rfl
    have hmem : ∀ γ : Fin m, γ ∈ (Set.univ : Set (Fin m)) := fun γ => Set.mem_univ γ
    have hcolor : ∀ γ : Fin m, alignColor (decAlignPartition m P) γ =
        Sum.inl (P'.equipartRefine.color ⟨γ, hmem γ⟩) := fun γ => by
      rw [hXe]; exact alignColor_inl _ _ (hmem γ)
    -- the block of `γ` has `cpBlockSize` points
    have hblock : ∀ γ : Fin m, (P'.block ⟨γ, hmem γ⟩).ncard = cpBlockSize ((A.2.1, P), (γ : ℕ)) := by
      intro γ
      have h := (hcolor γ).symm.trans (alignColor_decAlignPartition hg P γ)
      exact congrArg Prod.snd (Sum.inl_injective h)
    set x : ↥(Set.univ : Set (Fin m)) := ⟨γ₀, hmem γ₀⟩ with hx
    set j := P'.equipartRefine.color x with hj
    have hcolj : ∀ γ : Fin m, labAt lab (γ : ℕ) = dc ↔
        P'.equipartRefine.color ⟨γ, hmem γ⟩ = j := by
      intro γ
      rw [hcls, hcolor, hcolor, Sum.inl.injEq]
    have hset : ((colorSet (alignColor (⟨Set.univ, Sum.inl P'⟩ : Pt (SplitOutcomes (Fin m))))
        (Sum.inl j) : Finset (Fin m)) : Set (Fin m)) = {γ : Fin m | labAt lab (γ : ℕ) = dc} := by
      ext γ
      simp only [colorSet, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
      rw [← hXe, hcolor, Sum.inl.injEq, hcolj]
    have hcard : (colorSet (alignColor (⟨Set.univ, Sum.inl P'⟩ : Pt (SplitOutcomes (Fin m))))
        (Sum.inl j)).card = {γ : Fin m | labAt lab (γ : ℕ) = dc}.ncard := by
      rw [← hset, Set.ncard_coe_finset]
    have hdom : m < 2 * (colorSet (alignColor (⟨Set.univ, Sum.inl P'⟩ :
        Pt (SplitOutcomes (Fin m)))) (Sum.inl j)).card := by
      rw [hcard]; exact hdomR
    -- `m*` is the size of the class over the size of a block
    have hN : (alignRDomPoints (A, lab)).length = {γ : Fin m | labAt lab (γ : ℕ) = dc}.ncard :=
      length_alignRDomPoints hg hhd'
    have hms : alignRMs (A, rawAlignPartition P) =
        {γ : Fin m | labAt lab (γ : ℕ) = dc}.ncard / (P'.block x).ncard := by
      rw [hblock γ₀, ← hN]
      rfl
    have hb0 : 0 < (P'.block x).ncard :=
      Set.ncard_pos (Set.toFinite _) |>.2 ⟨x, P'.mem_block_self x⟩
    -- a point of the class outside the block of `x`
    obtain ⟨y, hy, hxy⟩ : ∃ y : ↥(Set.univ : Set (Fin m)),
        P'.equipartRefine.color y = j ∧ ¬ P'.part y x := by
      by_contra hno
      push_neg at hno
      have hsub : {γ : Fin m | labAt lab (γ : ℕ) = dc} ⊆
          (fun z : ↥(Set.univ : Set (Fin m)) => (z : Fin m)) '' P'.block x := by
        intro γ hγ
        exact ⟨⟨γ, hmem γ⟩, hno _ ((hcolj γ).1 hγ), rfl⟩
      have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
      rw [Set.ncard_image_of_injective _ Subtype.val_injective] at hle
      have h1 : {γ : Fin m | labAt lab (γ : ℕ) = dc}.ncard / (P'.block x).ncard ≤ 1 :=
        Nat.div_le_of_le_mul (by rw [Nat.mul_one]; exact hle)
      rw [← hms] at h1
      omega
    -- every block of the class has at least two points (admissibility)
    have hadm : P'.IsAdmissible := hZ.2.1
    have hblk : ∀ z : ↥(Set.univ : Set (Fin m)), P'.equipartRefine.color z = j →
        2 ≤ (P'.block z).ncard := by
      intro z hz
      refine hadm z ?_
      have hne : x ≠ y := fun h => hxy (h ▸ P'.part.refl x)
      have hxz : P'.color x = P'.color z := by
        have := congrArg Prod.fst hz; rw [hj] at this; exact this.symm
      have hyz : P'.color y = P'.color z := by
        have := congrArg Prod.fst (hz.trans hy.symm); exact this.symm
      have hsub : ({x, y} : Set ↥(Set.univ : Set (Fin m))) ⊆ P'.colorClass (P'.color z) := by
        intro w hw
        rcases hw with rfl | rfl
        · exact hxz
        · exact hyz
      calc 2 = ({x, y} : Set ↥(Set.univ : Set (Fin m))).ncard := (Set.ncard_pair hne).symm
        _ ≤ _ := Set.ncard_le_ncard hsub (Set.toFinite _)
    obtain ⟨Dd, hDm, hDGs, hDwin, hDms, hDblk, hDker⟩ := exists_alignDominantRoundData_A hK hG ϕ hϕ hvl
      t ht (s := Set.univ) rfl P' hdom (x := x) (y := y) rfl hy hxy hblk hn96
    refine ⟨Dd, hDm, hDGs, ?_, ?_, ?_, ?_⟩
    · rw [hDwin, hset, ← hwin]
    · have h2 := hDms
      rw [hcard] at h2
      rw [hms]
      exact (Nat.div_eq_of_eq_mul_left hb0 h2.symm).symm
    · ext τ
      rw [hDker, decGroup_alignKerGens hA hϕ, mem_preimageSubgroup]
      refine exists_congr fun hτ => ?_
      set f := ϕ ⟨τ, hτ⟩
      have hKe : alignKerPart (A, rawAlignPartition P) =
          alignKerPartA ((lab, dc), (A.2.1, P)) := rfl
      have e1 : f ∈ structAut (decColStruct m (alignKerPartA ((lab, dc), (A.2.1, P)))) ↔
          ColPartIso m P P f ∧ ∀ γ : Fin m, labAt lab (γ : ℕ) = dc →
            cellOf P ((f γ : Fin m) : ℕ) = cellOf P (γ : ℕ) := by
        rw [mem_structAut, ← colPartIso_iff_smul, colPartIso_alignKerPartA_iff hg P dc f]
      have e2 : f ∈ structAut (decAlignPartition m P) ↔ ColPartIso m P P f := by
        rw [structAut_decAlignPartition hK P, mem_structAut, ← colPartIso_iff_smul]
      rw [hKe, e1]
      refine and_congr e2 (forall_congr' fun γ => ?_)
      rw [alignPart_color rfl P' γ (hmem γ), alignPart_part rfl P' (hmem _) (hmem γ),
        decAlignPart_part, ← hcolj]
    · -- line 8: the machine's `ψ` is `ψ*`, up to the numbering of `Γ*`
      obtain ⟨bl, hb1, hb2, hb3⟩ := hDblk
      have hin : ∀ γ : Fin m, alignDomIn (A, rawAlignPartition P) (γ : ℕ) ↔
          (alignPart rfl P').color γ = j := fun γ => by
        rw [alignPart_color rfl P' γ (hmem γ), ← hcolj]
        exact Iff.rfl
      obtain ⟨f, hf⟩ := alignDomPsi_partition hg P hhd bl
        (fun γ δ hγ hδ => by
          rw [hb1 γ δ ((hin γ).1 hγ) ((hin δ).1 hδ), alignPart_part rfl P' (hmem γ) (hmem δ),
            decAlignPart_part])
        (fun i => by
          obtain ⟨γ, hγ, hγi⟩ := hb2 i
          exact ⟨γ, (hin γ).2 hγ, hγi⟩)
      refine ⟨f, fun τ hτ hG' => hf _ _ (fun γ => ?_)
        (fun γ hγ => hb3 τ hτ hG' γ ((hin γ).1 hγ))⟩
      rw [hDGs] at hτ
      exact hpres τ hτ hG' γ
  · -- case (B): a Johnson scheme
    set s := RawJohnson.carrier m J with hs
    set Jo := decAlignJohnsonObj J hJ with hJo
    have hXe : decAlignJohnson J hJ = ⟨s, Sum.inr Jo⟩ := rfl
    have hlab1 : ∀ γ : Fin m, labAt lab (γ : ℕ) = if (γ : ℕ) ∈ J.1 then 1 else 0 :=
      fun γ => labAt_rawOne_map hg _ γ
    have hs1 : {γ : Fin m | labAt lab (γ : ℕ) = 1} = s := by
      ext γ
      simp only [Set.mem_setOf_eq, hlab1, hs, RawJohnson.carrier]
      split_ifs with h <;> simp [h]
    -- the Johnson scheme has more than `m/2` points (`α > 1/2`)
    have hbig : m < 2 * s.ncard := by
      have h := hZ
      rw [hXe] at h
      obtain ⟨-, hα'⟩ := h
      rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] at hα'
      have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
      have : (m : ℝ) < 2 * (s.ncard : ℝ) := by nlinarith
      exact_mod_cast this
    -- so the dominant label is `1`, and its class is the vertex set of the scheme
    have hdc1 : dc = 1 := by
      by_contra hne
      have := ncard_labAt_add_le (m := m) lab hne
      rw [hs1] at this
      omega
    have hsetdc : {γ : Fin m | labAt lab (γ : ℕ) = dc} = s := by rw [hdc1, hs1]
    have hdom : m < 2 * s.ncard := by omega
    obtain ⟨Dd, hDm, hDGs, hDwin, hDms, hDlab, hDker⟩ := exists_alignDominantRoundData_B hK hG ϕ hϕ
      hvl t ht Jo (Equiv.ofBijective _ hJ.toBinom_bijective) hJ.two_le hJ.params
      (decAlignJohnsonObj_apply J hJ) hdom (by omega) hn96
    refine ⟨Dd, hDm, hDGs, ?_, hDms, ?_, ?_⟩
    · rw [hDwin, ← hs, ← hsetdc, ← hwin]
    · ext τ
      rw [hDker, decGroup_alignKerGens hA hϕ, mem_preimageSubgroup]
      refine exists_congr fun hτ => ?_
      set f := ϕ ⟨τ, hτ⟩
      have hKe : alignKerPart (A, rawAlignJohnson J) =
          alignKerPartB ((lab, dc), A.2.1) := rfl
      rw [hKe, mem_structAut_alignKerPartB hg lab dc f]
      constructor
      · rintro ⟨-, hfix⟩ γ hγ
        have h' : γ ∈ {γ : Fin m | labAt lab (γ : ℕ) = dc} := hγ
        rw [hsetdc] at h'
        exact hfix γ h'
      · intro hfix
        have hfix' : ∀ γ ∈ s, f γ = γ := by
          intro γ hγ
          rw [← hsetdc] at hγ
          exact hfix γ hγ
        exact ⟨mem_structAut_inr_of_fix hK Jo hfix', hfix'⟩
    · -- line 8: the machine's `ψ` is `ψ*`, up to the numbering of `Γ*`
      obtain ⟨e, he, heq⟩ := hDlab
      have hsdc : ∀ γ : Fin m, labAt lab (γ : ℕ) = dc ↔ (γ : ℕ) ∈ J.1 := fun γ =>
        Set.ext_iff.1 hsetdc γ
      have hlabel : ∀ (γ : Fin m) (hγ : γ ∈ s) (i : Fin (rawJDeg J)),
          i ∈ johnsonLabel (Equiv.ofBijective _ hJ.toBinom_bijective) γ ↔
            (i : ℕ) ∈ rawJRow (J, (γ : ℕ)) := by
        intro γ hγ i
        rw [johnsonLabel_of_mem _ hγ, Finset.mem_coe]
        exact mem_rawJSet
      obtain ⟨f, hf⟩ := alignDomPsi_johnson (A := A) hJ e he
      refine ⟨f, fun τ hτ hG' => hf _ _ hg (fun w => ?_) (fun w hw a => ?_)⟩
      · rw [← hsdc, ← hsdc]
        rw [hDGs] at hτ
        exact hpres τ hτ hG' w
      · have hw' : w ∈ s := hw
        have hσw : ϕ ⟨τ, hG'⟩ w ∈ s := by
          have h1 := (hpres τ (by rw [hDGs] at hτ; exact hτ) hG' w).2 ((hsdc w).2 hw)
          exact (hsdc _).1 h1
        have hE := heq τ hτ hG' w hw'
        constructor
        · intro ha
          have h1 : e a ∈ e '' johnsonLabel (Equiv.ofBijective _ hJ.toBinom_bijective)
              (ϕ ⟨τ, hG'⟩ w) := ⟨a, (hlabel _ hσw a).2 ha, rfl⟩
          rw [hE] at h1
          obtain ⟨_, ⟨b, hb, rfl⟩, hbe⟩ := h1
          exact ⟨b, (hlabel w hw' b).1 hb, hbe⟩
        · rintro ⟨b, hb, hbe⟩
          have h1 : e a ∈ Dd.toAlignDominant.phis ⟨τ, hτ⟩ ''
              (e '' johnsonLabel (Equiv.ofBijective _ hJ.toBinom_bijective) w) :=
            ⟨e b, ⟨b, (hlabel w hw' b).2 hb, rfl⟩, hbe⟩
          rw [← hE] at h1
          obtain ⟨a', ha', hae⟩ := h1
          rw [he.1 hae] at ha'
          exact (hlabel _ hσw a).1 ha'

open scoped Classical in
/-- `Algo.exists_domRoundData_alpha` at `α = 3/4`, the threshold of line 4c. -/
theorem exists_domRoundData (hA : RawAction.WF n m A ϕ) (hG : IsTransitive (decGroup n A.1.2))
    (hϕ : IsGiantRep ϕ) (hvl : VeryLargeK m (maxOrbitLength (decGroup n A.1.2))) {t : ℕ}
    (ht : ∀ u : Fin n, tPoint ϕ u = t) (hK : IsCatAction (SplitOutcomes (Fin m)))
    {o : RawAlignOutcome} {X' : Pt (SplitOutcomes (Fin m))} (hX : decAlignOutcome m o = some X')
    (hZ : IsSplitOutcome (3 / 4 : ℝ) (Set.univ : Set (Fin m)) X') (hm : 217 ≤ m) (hmn : m ≤ n)
    (hhd : alignRHasDom (alignRColorOf (A, o)) = true) (hnt : 2 ≤ alignRMs (A, o)) :
    ∃ Dd : AlignDominantRoundData (Fin n),
      Dd.toAlignDominant.m = m ∧
      Dd.toAlignDominant.Gs = preimageSubgroup ϕ (structAut X') ∧
      Dd.toAlignDominant.window = winSet n (alignRDomWindow (alignRColorOf (A, o),
        alignRDomColor (alignRColorOf (A, o)))) ∧
      Dd.toAlignDominant.ms = alignRMs (A, o) ∧
      Dd.ker = decGroup n (alignKerGens (A, o)) ∧
      ∃ f : Fin (alignDomKeys (A, o)).length ≃ Fin Dd.toAlignDominant.ms,
        ∀ τ (hτ : τ ∈ Dd.toAlignDominant.Gs) (hG : τ ∈ decGroup n A.1.2),
          alignDomPsi ((A, o), encPerm m (ϕ ⟨τ, hG⟩)) =
            encPerm _ (Equiv.permCongr f.symm (Dd.toAlignDominant.phis ⟨τ, hτ⟩)) :=
  exists_domRoundData_alpha hA hG hϕ hvl ht hK hX (by norm_num) hZ hm hmn hhd hnt

end RoundData

/-! ## The enumerations of lines 9–11 the machine computes -/

section Enum

variable {n : ℕ}

open scoped Classical in
/-- §14.1, lines 9–11, case 1 of the repair: **the cosets of `ker ϕ*` covering a coset `C` of
`G*`**, as the machine lists them: `Algo.adReps` at the lexicographically least element of `C`
(`Algo.aggnCanonCoset`). -/
noncomputable def adRepsOf (n : ℕ) (h : AVHdr) (C : Set (Perm (Fin n))) : List (Perm (Fin n)) :=
  if hC : ∃ c, AggnPrefixMin C c n then
    (adReps ((h.1, h.2.1), encPerm n hC.choose)).map (decPerm n)
  else []

/-- §14.1, lines 9–11: **the Master's enumerations, read off the machine's lists**: the
orbits of `G*` in the window in the machine's order (`Algo.alignDomOrbits`), the orbits of
`ker ϕ*` in it in the machine's order (`Algo.adKO`), and, in case 1 of the repair, the machine's
cosets of `ker ϕ*` (`Algo.adRepsOf`). Outside case 1 the round does not use the cosets, and
the enumeration keeps the default ones of `D`. -/
noncomputable def line4dDomEnum (n : ℕ) (h : AVHdr) (Dd : AlignDominantRoundData (Fin n)) :
    AlignDominantEnum (Fin n) where
  orbits := (alignDomOrbits ((alignPairG1 (h.1, h.2.1), adWindow h), n)).map (winSet n)
  kernelOrbits := (adKO h).map (winSet n)
  reps C := if l57Small h then adRepsOf n h C else Dd.defaultCosetEnum.reps C

variable {h : AVHdr}

/-- The machine's cosets cover a coset of `G*`, once the fuel reaches the index. -/
theorem adRepsOf_cover (hd : h.1.1.1.length = n)
    (hle : decGroup n (adKG h) ≤ decGroup n (alignPairG1 (h.1, h.2.1)))
    (hidx : (decGroup n (adKG h)).relIndex (decGroup n (alignPairG1 (h.1, h.2.1))) ≤
      (adFuel (h.1, h.2.1)).length + 1)
    {C : Set (Perm (Fin n))} {σ : Perm (Fin n)}
    (hC : C = σ • (decGroup n (alignPairG1 (h.1, h.2.1)) : Set (Perm (Fin n)))) :
    C = ⋃ ρ ∈ adRepsOf n h C, ρ • (decGroup n (adKG h) : Set (Perm (Fin n))) := by
  classical
  have hCd : C = decCoset n (some (alignPairG1 (h.1, h.2.1), encPerm n σ)) := by
    rw [decCoset_some, decPerm_encPerm, hC]
  obtain ⟨-, hmin⟩ := aggnCanonCoset_spec hd (alignPairG1 (h.1, h.2.1)) (encPerm n σ)
  have hex : ∃ c, AggnPrefixMin C c n := ⟨_, by rw [hCd]; exact hmin⟩
  unfold adRepsOf
  rw [dif_pos hex]
  have hc := hex.choose_spec
  set c := hex.choose
  -- `C` is the coset of its least element
  have hCc : C = c • (decGroup n (alignPairG1 (h.1, h.2.1)) : Set (Perm (Fin n))) := by
    have hcC := hc.1
    rw [hC] at hcC ⊢
    obtain ⟨g, hg, hgc⟩ := hcC
    rw [← hgc]
    show σ • _ = (σ • g) • _
    rw [smul_eq_mul, mul_smul, leftCoset_mem_leftCoset _ hg]
  have hcov := adReps_cover (p := (h.1, h.2.1)) hd hle hidx (wf_encPerm n c)
  rw [decPerm_encPerm] at hcov
  rw [hCc] at ⊢
  conv_lhs => rw [hcov]
  rfl

theorem length_adRepsOf_le (hd : h.1.1.1.length = n) (C : Set (Perm (Fin n))) :
    (adRepsOf n h C).length ≤
      (decGroup n (adKG h)).relIndex (decGroup n (alignPairG1 (h.1, h.2.1))) := by
  classical
  unfold adRepsOf
  split_ifs with hC
  · rw [List.length_map]
    exact adReps_length_le hd _
  · exact Nat.zero_le _

/-- **The machine's cosets for a version are the cosets of `Algo.adLk`**: the least element of
the transporter of the version is `Algo.adCanon`. -/
theorem adRepsOf_avTr (hx : h.2.2.2.2.1.length = n) {k : ℕ} {g : RawGens} {τ : RawPerm}
    (ht : avTr (h, k) = some (g, τ)) :
    adRepsOf n h (decCoset n (avTr (h, k))) = adLk n h k := by
  classical
  obtain ⟨hw, hmin⟩ := aggnCanonCoset_spec hx g τ
  have hcan : adCanon (h, k) = aggnCanonCoset ((h.2.2.2.2.1, g), τ) := by
    unfold adCanon; rw [ht]; rfl
  rw [ht]
  have hex : ∃ c, AggnPrefixMin (decCoset n (some (g, τ))) c n := ⟨_, hmin⟩
  unfold adRepsOf
  rw [dif_pos hex]
  have hch : hex.choose = decPerm n (aggnCanonCoset ((h.2.2.2.2.1, g), τ)) :=
    hex.choose_spec.unique hmin
  rw [hch, encPerm_decPerm hw, ← hcan]
  rfl

/-- **`Babai.AlignDominantEnum.Spec` for the machine's enumerations**, when the machine's
`G*`, `ker ϕ*`, window and `m*` are those of `Dd`. -/
theorem line4dDomEnum_spec (hd : h.1.1.1.length = n) (hn : 4 ≤ n)
    {Dd : AlignDominantRoundData (Fin n)}
    (hG1 : decGroup n (alignPairG1 (h.1, h.2.1)) = Dd.toAlignDominant.Gs)
    (hker : decGroup n (adKG h) = Dd.ker)
    (hwin : winSet n (adWindow h) = Dd.toAlignDominant.window)
    (hms : Dd.toAlignDominant.ms = alignRMs (h.1, h.2.1))
    (hmsm : alignRMs (h.1, h.2.1) ≤ h.1.2.1.length) :
    (line4dDomEnum n h Dd).Spec Dd := by
  have hgs : RawGens.WF n (alignPairG1 (h.1, h.2.1)) := alignPairG1_wf hd
  have hks : RawGens.WF n (adKG h) := alignKerGens_wf hd h.2.1
  have hlt : ∀ j ∈ adWindow h, j < n := fun j hj => adWindow_lt hd hj
  have hinv : rawIsInvariant (alignPairG1 (h.1, h.2.1), adWindow h) = true := by
    rw [rawIsInvariant_eq_true_iff hgs hlt]
    have := Dd.isInvariant_window
    rw [← hwin, ← hG1] at this
    exact this
  have hkinv : rawIsInvariant (adKG h, adWindow h) = true := by
    rw [rawIsInvariant_eq_true_iff hks hlt]
    have := Dd.isInvariant_window_ker
    rw [← hwin, ← hker] at this
    exact this
  have hle : decGroup n (adKG h) ≤ decGroup n (alignPairG1 (h.1, h.2.1)) := by
    rw [hker, hG1]; exact kerSubgroup_le _
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have := perm_alignDomOrbits hgs hlt hinv
    rw [hG1, hwin] at this
    exact this
  · have := perm_adKO hks hlt hkinv
    change List.Perm _ (orbitListOn (decGroup n (adKG h)) (winSet n (adWindow h))) at this
    rw [hker, hwin] at this
    exact this
  · intro S hS hbig
    rw [Fintype.card_fin] at hbig
    exact alignDomOrbits_first hgs hlt hinv S hS hbig
  · rintro C ⟨σ, hC⟩
    show C = ⋃ ρ ∈ (if l57Small h then adRepsOf n h C else Dd.defaultCosetEnum.reps C),
      ρ • (Dd.ker : Set (Perm (Fin n)))
    split_ifs with hs
    · have hsm : alignRSmall (h.1, h.2.1) = true := alignRSmall_of_l57Small hs
      have hidx : (decGroup n (adKG h)).relIndex (decGroup n (alignPairG1 (h.1, h.2.1))) ≤
          (adFuel (h.1, h.2.1)).length + 1 := by
        rw [adFuel_length_of_small hsm hmsm (by rw [hd]; exact alignRMs_le_guard hd hn hsm),
          hker, hG1, ← hms]
        calc Dd.ker.relIndex Dd.toAlignDominant.Gs ≤ Dd.toAlignDominant.ms.factorial :=
              Algo.relIndex_kerSubgroup_le _
          _ ≤ Dd.toAlignDominant.ms ^ Dd.toAlignDominant.ms := Nat.factorial_le_pow _
          _ ≤ _ := Nat.le_succ _
      rw [← hker]
      exact adRepsOf_cover hd hle hidx (by rw [hG1]; exact hC)
    · exact Dd.defaultCosetEnum_spec.cover C ⟨σ, hC⟩
  · intro C
    show (if l57Small h then adRepsOf n h C else Dd.defaultCosetEnum.reps C).length ≤ _
    split_ifs with hs
    · rw [← hker, ← hG1]
      exact length_adRepsOf_le hd C
    · exact Dd.defaultCosetEnum_spec.length C

end Enum


/-- **The machine's cosets for each version are the Master's**, in case 1 of the repair. -/
theorem line4dDomEnum_reps {n m : ℕ} {h : AVHdr} {ϕ : decGroup n h.1.1.2 →* Perm (Fin m)}
    [MulAction (Perm (Fin m)) (Pt (SplitOutcomes (Fin m)))] (hA : RawAction.WF n m h.1 ϕ)
    (hϕ : IsGiantRep ϕ) (hK : IsCatAction (SplitOutcomes (Fin m)))
    {X' : Pt (SplitOutcomes (Fin m))} (hX : decAlignOutcome m h.2.1 = some X')
    {Ys : List (Pt (SplitOutcomes (Fin m)))} (hYs : h.2.2.1.map (decAlignOutcome m) = Ys.map some)
    (hx : h.2.2.2.2.1.length = n) (hs : l57Small h = true) (Dd : AlignDominantRoundData (Fin n)) :
    ∀ k (hk : k < Ys.length), alignTransporter ϕ X' Ys[k] ≠ ∅ →
      (line4dDomEnum n h Dd).reps (alignTransporter ϕ X' Ys[k]) = adLk n h k := by
  intro k hk hne'
  have htr := decCoset_avTr hA hϕ hK hX hYs hx hk
  show (if l57Small h then adRepsOf n h _ else _) = _
  rw [if_pos hs, ← htr]
  rcases ht : avTr (h, k) with _ | ⟨g, τ⟩
  · exfalso
    rw [ht] at htr
    exact hne' htr.symm
  · rw [← ht]
    exact adRepsOf_avTr hx ht

/-! ## The Master's data the header describes -/

section MasterDom


variable (p : MasterHintInput) {n m : ℕ}
    {ϕ : decGroup n (masterHintTop p).1.1.2 →* Perm (Fin m)}
    (hp : RawAction.WF n m (masterHintTop p).1 ϕ)
    (hG : IsTransitive (decGroup n (masterHintTop p).1.1.2)) (hϕ : IsGiantRep ϕ)
    (hn : 64 ≤ n) (hroute : masterHintRoute p = 4)
    {c tt dd : ℕ} (hb : Line4cBounds c tt dd)
    (hx : (masterHintTop p).2.1.length = n) (hy : (masterHintTop p).2.2.length = n)
    [inst : MulAction (Perm (Fin m)) (Pt (SplitOutcomes (Fin m)))]
    (hK : IsCatAction (SplitOutcomes (Fin m)))

include hp hG hϕ hn hroute hb hx hy hK

set_option maxHeartbeats 1000000 in
open scoped Classical in
/-- **Line 4d with a dominant color class: the header describes the Master's round of
Procedure Align.**  When line 6 finds a dominant color class carrying a nontrivial structure
(`2 ≤ m*`), there is a `Babai.Line4cdData` with data `Dd` of lines 7–11 whose round the
machine's header describes: in case 1 of the repair (`Algo.l57Small`) by the descent over the
cosets of `ker ϕ*` (`Algo.ADDescribes`), and in cases 2 and 3 by Eq. (71) over the orbits of
`G*` in the window and the other classes (`Algo.AVDescribes`).

The data is built as `Algo.exists_line4dData` builds it when there is no dominant class, with
the dominant window first, the data `Dd` of `Algo.exists_domRoundData`, and the enumerations
the machine computes (`Algo.line4dDomEnum`). What it asks of the windows is what the paper asks
of Procedure Align: they are the color classes of `Ω` of line 4, invariant under
`ϕ⁻¹(Aut(X'))`, covering `Ω`, the dominant window first, and every other one of at most
`4n/5` points (Eq. (72) at `α = 1/2`, `Babai.five_mul_ncard_omegaColorClass_le_of_ne_dom`). -/
theorem exists_line4dDomData
    (hhd : alignRHasDom (alignRColorOf ((masterHintTop p).1, line4dFixed c tt dd p)) = true)
    (hnt : 2 ≤ alignRMs ((masterHintTop p).1, line4dFixed c tt dd p)) :
    ∃ D : Line4cdData (Fin n) ℕ (decGroup n (masterHintTop p).1.1.2)
        (decStrN n (masterHintTop p).2.1) (decStrN n (masterHintTop p).2.2) m
        ((line4cVersions c tt dd (masterLine4cInput p)).2.length * (Fintype.card (Fin n) + 1) *
          AlignDominantRoundData.alignDominantRoundCost (Fintype.card (Fin n))),
      ∃ Dd : AlignDominantRoundData (Fin n), D.shape.dom = some Dd ∧
        (l57Small (line4dDomHdr c tt dd p) = true →
          ADDescribes n (line4dDomHdr c tt dd p) D.shape Dd) ∧
        (l57Small (line4dDomHdr c tt dd p) = false → Dd.LargeParam ∧
          AVDescribes n (line4dDomHdr c tt dd p) D.shape
            (D.shape.domEnum.orbits ++ D.shape.tail)) ∧
        (∀ Δ ∈ D.shape.tail, 3 * Δ.ncard ≤ 2 * Fintype.card (Fin n)) ∧
        (decGroup n (alignPairG1 ((masterHintTop p).1, line4dFixed c tt dd p)) =
            Dd.toAlignDominant.Gs ∧
          winSet n (alignRDomWindow (alignRColorOf ((masterHintTop p).1, line4dFixed c tt dd p),
            alignRDomColor (alignRColorOf ((masterHintTop p).1, line4dFixed c tt dd p)))) =
            Dd.toAlignDominant.window) := by
  obtain ⟨hvl, id, ht2, hm, hmn, -⟩ := masterLine4c_facts p hp hG hϕ hn hroute
  obtain ⟨hcan, -, -, -, hfin, -, hgood⟩ :=
    masterLine4c_versions p hp hG hϕ hn hroute hb hx hy hK
  obtain ⟨X', hXdec, hXmem⟩ := line4dFixed_spec p hp hG hϕ hn hroute hb hx hy hK
  obtain ⟨hYmap, hYnd, hYmem⟩ := line4dYs_spec p hp hG hϕ hn hroute hb hx hy hK
  have hZ := hgood _ X' hXmem
  obtain ⟨Dd, hDm, hDGs, hDwin, hDms, hDker, -⟩ :=
    exists_domRoundData hp hG hϕ hvl id.tPointOf_eq hK hXdec hZ hm hmn hhd hnt
  have hd : (masterHintTop p).1.1.1.length = n := hp.1
  have hg : (masterHintTop p).1.2.1.length = m := hp.2.1
  have h4t : 4 * p.2.2 < m := by simpa only [Fintype.card_fin] using id.four_t
  set h : AVHdr := ((masterHintTop p).1, line4dFixed c tt dd p,
    line4dYs c tt dd p, alignL57Windows ((masterHintTop p).1, line4dFixed c tt dd p),
    (masterHintTop p).2.1, (masterHintTop p).2.2) with hhdef
  change ∃ D, ∃ Dd, _ ∧ (l57Small h = true → ADDescribes n h _ Dd) ∧
    (l57Small h = false → _ ∧ AVDescribes n h _ _) ∧ _ ∧ _
  set lab := alignOutcomeLab ((masterHintTop p).1.2.1, line4dFixed c tt dd p) with hlab
  have hq : alignRColorOf ((masterHintTop p).1, line4dFixed c tt dd p) = ((masterHintTop p).1, lab) := rfl
  have hhd' : alignRHasDom ((masterHintTop p).1, lab) = true := hhd
  set dc := alignRDomColor ((masterHintTop p).1, lab) with hdcdef
  set domWin := alignRDomWindow (((masterHintTop p).1, lab), dc) with hdomWin
  have hW : alignRWindows ((masterHintTop p).1, lab) =
      domWin :: (alignRClasses ((masterHintTop p).1, lab)).filter (fun W => alignRNotDom (((masterHintTop p).1, lab), W)) := by
    rw [alignRWindows, if_pos hhd']
  -- the dominant class, as a class of `Babai.alignIdx`
  set γ₀ : Fin m := ⟨(alignRDomPoints ((masterHintTop p).1, lab)).getD 0 0, alignRDomFirst_lt hg hhd'⟩
  haveI : Nonempty (AlignIdx X') := nonempty_alignIdx (by omega)
  set i₀ := alignIdx X' γ₀ with hi₀
  have hset : {γ : Fin m | labAt lab (γ : ℕ) = dc} = {γ : Fin m | alignIdx X' γ = i₀} := by
    ext γ
    simp only [Set.mem_setOf_eq]
    rw [show dc = labAt lab (γ₀ : ℕ) from rfl, alignOutcomeLab_eq_iff hg hXdec γ γ₀, hi₀]
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  have hdomR : m < 2 * {γ : Fin m | labAt lab (γ : ℕ) = dc}.ncard :=
    alignRDomColor_dominant_of_wf hp hhd'
  have hhead : winSet n domWin = omegaOf ϕ {γ : Fin m | alignIdx X' γ = i₀} := by
    rw [hdomWin, winSet_alignRDomWindow_of_wf hp hϕ hvl lab dc, hset]
  have hdomI : m < 2 * (colorSet (alignIdx X') i₀).card := by
    have : ((colorSet (alignIdx X') i₀ : Finset (Fin m)) : Set (Fin m)) =
        {γ : Fin m | alignIdx X' γ = i₀} := by
      ext γ; simp [colorSet]
    rw [← Set.ncard_coe_finset, this, ← hset]
    exact hdomR
  -- the windows
  set head : Set (Fin n) := winSet n domWin with hheaddef
  set tail : List (Set (Fin n)) :=
    ((alignRClasses ((masterHintTop p).1, lab)).filter (fun W => alignRNotDom (((masterHintTop p).1, lab), W))).map (winSet n)
    with htaildef
  have htailmem : ∀ Δ ∈ tail, ∃ u : ℕ, u < n ∧
      alignROmegaClass (((masterHintTop p).1, lab), u) ∈ alignRClasses ((masterHintTop p).1, lab) ∧
      alignROmegaClass (((masterHintTop p).1, lab), u) ≠ domWin ∧ Δ = winSet n (alignROmegaClass (((masterHintTop p).1, lab), u)) := by
    intro Δ hΔ
    obtain ⟨W, hW', rfl⟩ := List.mem_map.1 hΔ
    rw [List.mem_filter, alignRNotDom, decide_eq_true_iff] at hW'
    obtain ⟨u, hu, rfl⟩ := mem_alignRClasses hW'.1
    exact ⟨u, by rw [← hd]; exact hu, hW'.1, hW'.2, rfl⟩
  have hne : head ∉ tail := by
    intro hmem
    obtain ⟨u, -, -, hune, he⟩ := htailmem head hmem
    exact winSet_alignROmegaClass_ne (q := ((masterHintTop p).1, lab)) hd hune he.symm
  have hcover : (⋃ Δ ∈ head :: tail, Δ) = Set.univ := by
    refine Set.eq_univ_of_forall fun u => ?_
    obtain ⟨W, hWm, hu⟩ := alignRWindows_cover (q := ((masterHintTop p).1, lab)) (u := u) (by rw [hd]; exact u.isLt)
    refine Set.mem_iUnion₂.2 ⟨winSet n W, ?_, mem_winSet.2 hu⟩
    rw [hW] at hWm
    rcases List.mem_cons.1 hWm with rfl | hWm
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_map_of_mem hWm)
  have hG1 : decGroup n (alignPairG1 ((masterHintTop p).1, line4dFixed c tt dd p)) = preimageSubgroup ϕ (structAut X') :=
    decGroup_alignPairG1 hp hϕ hK hXdec
  have hinvTail : ∀ Δ ∈ tail, IsInvariant (preimageSubgroup ϕ (structAut X')) Δ := by
    intro Δ hΔ
    obtain ⟨u, -, hcl, -, rfl⟩ := htailmem Δ hΔ
    obtain ⟨v, hv⟩ := winSet_alignRClasses_eq hp hϕ hvl hXdec hcl
    rw [hv]
    exact isInvariant_omegaColorClass_alignIdx hK ϕ hϕ hvl X' _
  have hinv : ∀ Δ ∈ head :: tail, IsInvariant (preimageSubgroup ϕ (structAut X')) Δ := by
    intro Δ hΔ
    rcases List.mem_cons.1 hΔ with rfl | hΔ
    · have := Dd.isInvariant_window
      rw [hDGs, hDwin] at this
      exact this
    · exact hinvTail Δ hΔ
  have hsizes : ∀ Δ ∈ tail, 5 * Δ.ncard ≤ 4 * Fintype.card (Fin n) := by
    intro Δ hΔ
    obtain ⟨u, -, hcl, hune, rfl⟩ := htailmem Δ hΔ
    obtain ⟨v, hv⟩ := winSet_alignRClasses_eq hp hϕ hvl hXdec hcl
    rw [hv]
    refine five_mul_ncard_omegaColorClass_le_of_ne_dom hG ϕ hϕ hvl (by omega) id.tPointOf_eq
      (by omega) (by omega) (alignIdx X') hdomI _ ?_
    rw [← hv, ← hhead]
    exact winSet_alignROmegaClass_ne (q := ((masterHintTop p).1, lab)) hd hune
  have hsizes3 : ∀ Δ ∈ tail, 3 * Δ.ncard ≤ 2 * Fintype.card (Fin n) := by
    intro Δ hΔ
    obtain ⟨u, -, hcl, hune, rfl⟩ := htailmem Δ hΔ
    obtain ⟨v, hv⟩ := winSet_alignRClasses_eq hp hϕ hvl hXdec hcl
    rw [hv]
    refine three_mul_ncard_omegaColorClass_le_of_ne_dom hG ϕ hϕ hvl (by omega) id.tPointOf_eq
      (by omega) (by omega) (alignIdx X') hdomI _ ?_
    rw [← hv, ← hhead]
    exact winSet_alignROmegaClass_ne (q := ((masterHintTop p).1, lab)) hd hune
  have hL : (head :: tail).length ≤ Fintype.card (Fin n) + 1 := by
    have := length_alignRWindows_le ((masterHintTop p).1, lab)
    rw [hW, hd] at this
    rw [Fintype.card_fin, List.length_cons, htaildef, List.length_map]
    simpa using this
  have hc1 : 1 ≤ AlignDominantRoundData.alignDominantRoundCost (Fintype.card (Fin n)) := by
    rw [AlignDominantRoundData.alignDominantRoundCost, Fintype.card_fin]
    omega
  -- the machine's quantities are `Dd`'s
  have hG1' : decGroup n (alignPairG1 (h.1, h.2.1)) = Dd.toAlignDominant.Gs := hG1.trans hDGs.symm
  have hker : decGroup n (adKG h) = Dd.ker := hDker.symm
  have hwin : winSet n (adWindow h) = Dd.toAlignDominant.window := hDwin.symm
  have hmsm : alignRMs (h.1, h.2.1) ≤ h.1.2.1.length := by
    have := Dd.toAlignDominant.param_halved
    rw [hDm, hDms] at this
    show alignRMs ((masterHintTop p).1, line4dFixed c tt dd p) ≤ (masterHintTop p).1.2.1.length
    rw [hg]
    omega
  have hspec := line4dDomEnum_spec (h := h) hd (by omega) hG1' hker hwin hDms hmsm
  let S : AlignShape (Fin n) ℕ (decGroup n (masterHintTop p).1.1.2)
      (decStrN n (masterHintTop p).2.1) (decStrN n (masterHintTop p).2.2) :=
    { m := m, ϕ := ϕ, act := inst,
      Vers := line4cVers c tt dd (masterHintTop p).1 p.2.2 (masterHintTop p).2.1
        (masterHintTop p).2.2 m,
      finY := hfin _, X' := X', head := head, tail := tail, dom := some Dd,
      versions := (line4dYs c tt dd p).filterMap (decAlignOutcome m),
      domEnum := line4dDomEnum n h Dd }
  have hv : S.versions.Perm S.finY.toFinset.toList := by
    refine (List.perm_ext_iff_of_nodup hYnd (Finset.nodup_toList _)).2 fun Z => ?_
    rw [Finset.mem_toList, Set.Finite.mem_toFinset]
    exact hYmem Z
  have hVlen : S.versions.length ≤ (line4cVersions c tt dd (masterLine4cInput p)).2.length :=
    (List.length_filterMap_le _ _).trans (length_line4dYs_le c tt dd p)
  let D := Line4cdData.ofShape S m _ _ _ hv hne hcover hinv
    (fun D' hD' => by
      have he : D' = Dd := (Option.some.inj hD').symm
      subst he
      exact ⟨hDGs, by rw [hDwin]; rfl, hDm⟩)
    (fun D' hD' => by
      have he : D' = Dd := (Option.some.inj hD').symm
      subst he
      exact hspec)
    hcan hXmem hVlen hL hc1 (fun _ _ => le_rfl)
    (fun Δ hΔ hne' => by
      rcases hne' with hne' | hne'
      · rcases List.mem_cons.1 hΔ with rfl | hΔ
        · exact absurd rfl hne'
        · exact hsizes Δ hΔ
      · simp [S] at hne')
  -- the window is not empty
  have hwne : Dd.toAlignDominant.window.Nonempty := by
    rw [← hwin]
    show (winSet n domWin).Nonempty
    rw [hdomWin, winSet_alignRDomWindow_of_wf hp hϕ hvl lab dc]
    exact omegaOf_nonempty id (by omega)
  have htailW : ((alignRWindows (alignRColorOf (h.1, h.2.1))).tail).map (winSet n) = tail := by
    show ((alignRWindows ((masterHintTop p).1, lab)).tail).map (winSet n) = tail
    rw [hW]
    rfl
  refine ⟨D, Dd, rfl, fun hs => ?_, fun hs => ?_, hsizes3, hG1', hwin⟩
  · -- case 1
    have hsmall : ¬ Dd.LargeParam := (l57Small_iff (h := h) hd hhd hDms hG1' hnt).1 hs
    have hnl := alignRLarge_false_of_l57Small hs
    refine ADDescribes.mk' (h := h) (S := D.shape) hd rfl hs hwin hwne rfl hsmall hne hDGs hspec hker rfl ?_ ?_
      hinvTail hp hϕ hK hXdec hYmap D.run_red
    · show (h.2.2.2.1.tail).map (winSet n) = tail
      show ((alignL57Windows (h.1, h.2.1)).tail).map (winSet n) = tail
      rw [alignL57Windows_of_not hnl]
      exact htailW
    · exact line4dDomEnum_reps (h := h) (Ys := (line4dYs c tt dd p).filterMap (decAlignOutcome m)) hp hϕ hK hXdec hYmap hx hs Dd
  · -- cases 2 and 3
    have hlarge : alignRLarge (h.1, h.2.1) = true := by
      have hs' : alignRSmall ((masterHintTop p).1, line4dFixed c tt dd p) = false := by
        rw [← l57Small_eq_of_two_le (h := h) hnt]; exact hs
      unfold alignRSmall at hs'
      unfold alignRLarge
      rw [hhd] at hs' ⊢
      simpa using hs'
    have hdh : (h.1, h.2.1).1.1.1.length = n := hd
    have hhdh : alignRHasDom (alignRColorOf (h.1, h.2.1)) = true := hhd
    have hDmsh : Dd.toAlignDominant.ms = alignRMs (h.1, h.2.1) := hDms
    have hL' : Dd.LargeParam :=
      (largeParam_iff (n := n) (p := (h.1, h.2.1)) (D := Dd) hdh hhdh hDmsh hG1').2 hlarge
    refine ⟨hL', avDescribes_of_domLarge (h := h) (S := D.shape) rfl hlarge rfl hL' hne hDGs hG1' hwin hspec rfl
      htailW ?_ hd ?_ hp hϕ hK hXdec hYmap hinvTail D.run_red⟩
    · obtain ⟨u, hu⟩ := hwne
      have hmem := orbit_mem_orbitListOn Dd.isInvariant_window hu
      have hmem' := hspec.orbits.symm.subset hmem
      intro he
      have he1 : (line4dDomEnum n h Dd).orbits = [] := (List.append_eq_nil_iff.1 he).1
      rw [he1] at hmem'
      exact List.not_mem_nil hmem'
    · intro W hWm u hu
      have := lt_of_mem_of_mem_alignRWindows hWm hu
      rw [← hd]
      exact this

end MasterDom

/-! ## The carrier walks the round of the Master's data it computed -/

section Match

variable {c tt dd : ℕ} {n m : ℕ} {p : MasterHintInput}
    (hx : RawStr.WF n (2 * n + 1) p.1.2.2.2.1)
    (hy : RawStr.WF n (2 * n + 1) p.1.2.2.2.2)
    (hgs : RawGens.WF n p.1.2.1) (hnd : p.1.1.Nodup) (hlt : ∀ z ∈ p.1.1, z < n)
    (hinv : IsInvariant (decGroup n p.1.2.1) (winSet n p.1.1))
    {ϕ : decGroup p.1.1.length (masterHintTop p).1.1.2 →* Perm (Fin m)}
    (hp : RawAction.WF p.1.1.length m (masterHintTop p).1 ϕ)
    (hG : IsTransitive (decGroup p.1.1.length (masterHintTop p).1.1.2))
    (hϕ : IsGiantRep ϕ) (hn : 64 ≤ p.1.1.length) (hr : masterHintRoute p = 4)
    (hb : Line4cBounds c tt dd)

include hx hy hgs hp hG hϕ hn hr hb in
/-- **Section 15, lines 4c–4d with a dominant color class, on the Master's node**, the data
built from the machine's computation. At a node of route `4` where line 6 of Procedure Align
finds a dominant color class with a nontrivial structure (`2 ≤ m*`), there is a round of
Procedure Align of the Master (`Babai.Line4cdData`, with the cost `Babai.Line4cdDataAt` asks at
the witness `(Algo.line4dQ, c923)`) with data `Dd` of lines 7–11 such that
* in case 1 of the repair (`Algo.l57Small`) the carrier `Algo.line4dDomOps` walks its round
  call for call (`Algo.line4dDomOps_match_small`);
* in cases 2 and 3, `m*` is large, and the carrier walks the round whenever the round attaches
  no hint (`Algo.line4dDomOps_match_large`) — which is case 2; case 3 attaches the hint of
  `Babai.AlignDominantRoundData.hint`, which the node carrier does not emit. -/
theorem line4dDomOps_match_built (a b : ℕ) (hhd : line4dHasDom c tt dd p = true) :
    ∃ D : Line4cdData (Fin p.1.1.length) ℕ (decGroup p.1.1.length (masterHintTop p).1.1.2)
        (decStrN p.1.1.length (masterHintTop p).2.1)
        (decStrN p.1.1.length (masterHintTop p).2.2) m
        (line4cdCost (line4dQ c tt dd) c923 (Fintype.card (Fin p.1.1.length))),
      ∃ Dd : AlignDominantRoundData (Fin p.1.1.length), D.shape.dom = some Dd ∧
        (l57Small (line4dDomHdr c tt dd p) = true →
          ADDescribes p.1.1.length (line4dDomHdr c tt dd p) D.shape Dd ∧
          LoopMatch (masterAdmittedRound a b (line4dDomOps c tt dd)) (fun J => decWinSI n J.1)
            (decCoset n) (p.1, some p.2) ((line4dDomOps c tt dd).width (p.1, some p.2)) 0
            ((line4dDomOps c tt dd).init (p.1, some p.2))
            ((top4wTree p.1.1 hnd hlt (decGroup n p.1.2.1) hinv (decStrN n p.1.2.2.2.1)
              D.shape.red).bind (fun A => .done (decPerm n p.1.2.2.1 • A)))) ∧
        (l57Small (line4dDomHdr c tt dd p) = false → Dd.LargeParam ∧
          AVDescribes p.1.1.length (line4dDomHdr c tt dd p) D.shape
            (D.shape.domEnum.orbits ++ D.shape.tail) ∧
          ((∀ J, D.shape.hint J = none) →
            LoopMatch (masterAdmittedRound a b (line4dDomOps c tt dd)) (fun J => decWinSI n J.1)
              (decCoset n) (p.1, some p.2) ((line4dDomOps c tt dd).width (p.1, some p.2)) 0
              ((line4dDomOps c tt dd).init (p.1, some p.2))
              ((top4wTree p.1.1 hnd hlt (decGroup n p.1.2.1) hinv (decStrN n p.1.2.2.2.1)
                D.shape.red).bind (fun A => .done (decPerm n p.1.2.2.1 • A))))) ∧
        (∀ Δ ∈ D.shape.tail, 3 * Δ.ncard ≤ 2 * Fintype.card (Fin p.1.1.length)) ∧
        (decGroup p.1.1.length (alignPairG1 ((masterHintTop p).1, line4dFixed c tt dd p)) =
            Dd.toAlignDominant.Gs ∧
          winSet p.1.1.length (alignRDomWindow (alignRColorOf ((masterHintTop p).1, line4dFixed c tt dd p),
            alignRDomColor (alignRColorOf ((masterHintTop p).1, line4dFixed c tt dd p)))) =
            Dd.toAlignDominant.window) := by
  obtain ⟨inst, hK⟩ := exists_isCatAction_splitOutcomes (Γ := Fin m)
  have hxl : (masterHintTop p).2.1.length = p.1.1.length := by
    show (rawRestrictStr (p.1.2.2.2.1, p.1.1)).length = _
    exact length_rawRestrictStr _ _
  have hyl : (masterHintTop p).2.2.length = p.1.1.length := by
    show (rawRestrictStr (top4aTarget (p.1.2.2.2.1, p.1.2.2.1, p.1.2.2.2.2), p.1.1)).length = _
    exact length_rawRestrictStr _ _
  have hΔ : 0 < p.1.1.length := by omega
  obtain ⟨D₀, Dd, hdom, hsm, hlg, htl, hGs⟩ :=
    exists_line4dDomData p hp hG hϕ hn hr hb hxl hyl hK (Bool.and_eq_true_iff.1 hhd).1
      (of_decide_eq_true (Bool.and_eq_true_iff.1 hhd).2)
  -- the machine's count is below the cost of `Babai.Line4cdDataAt` at `(line4dQ, c923)`
  obtain ⟨-, -, -, -, hmn, -⟩ := masterLine4c_facts p hp hG hϕ hn hr
  have hcnt := ((line4cCountBound_spec c tt dd).2.2 (masterLine4cInput p)
    (by show (masterHintTop p).1.2.1.length ≤ p.1.1.length; rw [hp.2.1]; exact hmn)
    (by show (masterHintTop p).2.1.length ≤ p.1.1.length; rw [hxl])
    (by show (masterHintTop p).2.2.length ≤ p.1.1.length; rw [hyl])).2
  have hle : (line4cVersions c tt dd (masterLine4cInput p)).2.length *
      (Fintype.card (Fin p.1.1.length) + 1) *
      AlignDominantRoundData.alignDominantRoundCost (Fintype.card (Fin p.1.1.length)) ≤
      line4cdCost (line4dQ c tt dd) c923 (Fintype.card (Fin p.1.1.length)) := by
    rw [line4cdCost, Fintype.card_fin]
    refine Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ ?_)
    have hq : line4cCountBound c tt dd p.1.1.length ≤ qMax (line4dQ c tt dd) p.1.1.length :=
      (Nat.le_add_left _ (Babai.q923 p.1.1.length)).trans
        (le_qMax (line4dQ c tt dd) (le_refl p.1.1.length))
    exact (hcnt.trans hq).trans (Nat.le_mul_of_pos_right _ (Nat.pow_pos (by omega)))
  refine ⟨D₀.mono hle, Dd, hdom, fun hs => ?_, fun hs => ?_, htl, hGs⟩
  · have hD := hsm hs
    exact ⟨hD, line4dDomOps_match_small hx hy hgs hnd hlt hinv hΔ (D₀.mono hle) a b hD hs⟩
  · obtain ⟨hL, hD⟩ := hlg hs
    exact ⟨hL, hD, fun hnh =>
      line4dDomOps_match_large hx hy hgs hnd hlt hinv hΔ (D₀.mono hle) a b hdom hL hD hs hnh⟩

end Match

/-! ## In the node carrier -/

section Node

variable {c tt dd : ℕ} {n m : ℕ} {p : MasterHintInput}
    (hx : RawStr.WF n (2 * n + 1) p.1.2.2.2.1)
    (hy : RawStr.WF n (2 * n + 1) p.1.2.2.2.2)
    (hgs : RawGens.WF n p.1.2.1) (hnd : p.1.1.Nodup) (hlt : ∀ z ∈ p.1.1, z < n)
    (hinv : IsInvariant (decGroup n p.1.2.1) (winSet n p.1.1))
    {ϕ : decGroup p.1.1.length (masterHintTop p).1.1.2 →* Perm (Fin m)}
    (hp : RawAction.WF p.1.1.length m (masterHintTop p).1 ϕ)
    (hG : IsTransitive (decGroup p.1.1.length (masterHintTop p).1.1.2))
    (hϕ : IsGiantRep ϕ) (hn : 64 ≤ p.1.1.length) (hr : masterHintRoute p = 4)
    (hb : Line4cBounds c tt dd)

include hx hy hgs hp hG hϕ hn hr hb in
/-- **Section 15, lines 4c–4d with a dominant color class, case 1, in the node carrier**, for
the Master's data built from the machine's computation (`Algo.line4dDomOps_match_built`). -/
theorem masterNodeFull_line4cd_dom_match_built {a b B C₀ : ℕ}
    {cameron : RawGens × List ℕ → Option RawCameron} {e f u v : ℕ} {c' b' t d dc dp E : ℕ}
    (hhd : line4dHasDom c tt dd p = true) :
    ∃ D : Line4cdData (Fin p.1.1.length) ℕ (decGroup p.1.1.length (masterHintTop p).1.1.2)
        (decStrN p.1.1.length (masterHintTop p).2.1)
        (decStrN p.1.1.length (masterHintTop p).2.2) m
        (line4cdCost (line4dQ c tt dd) c923 (Fintype.card (Fin p.1.1.length))),
      ∃ Dd : AlignDominantRoundData (Fin p.1.1.length), D.shape.dom = some Dd ∧
        ((l57Small (line4dDomHdr c tt dd p) = true ∨ ∀ J, D.shape.hint J = none) →
          LoopMatch (masterAdmittedRound a b
              (masterNodeFullOps B C₀ cameron e f u v c tt dd (line4dDomOps c tt dd) default
                c' b' t d dc dp E))
            (fun J => decWinSI n J.1) (decCoset n) (p.1, some p.2)
            ((masterNodeFullOps B C₀ cameron e f u v c tt dd (line4dDomOps c tt dd) default
              c' b' t d dc dp E).width (p.1, some p.2)) 0
            ((masterNodeFullOps B C₀ cameron e f u v c tt dd (line4dDomOps c tt dd) default
              c' b' t d dc dp E).init (p.1, some p.2))
            ((top4wTree p.1.1 hnd hlt (decGroup n p.1.2.1) hinv (decStrN n p.1.2.2.2.1)
              D.shape.red).bind (fun A => .done (decPerm n p.1.2.2.1 • A)))) := by
  obtain ⟨D, Dd, hdom, hsm, hlg, -, -⟩ :=
    line4dDomOps_match_built hx hy hgs hnd hlt hinv hp hG hϕ hn hr hb 0 0 hhd
  have hΔ : 0 < p.1.1.length := by omega
  refine ⟨D, Dd, hdom, fun hcase => ?_⟩
  cases hs : l57Small (line4dDomHdr c tt dd p)
  · have hnh : ∀ J, D.shape.hint J = none := by
      rcases hcase with h | h
      · rw [hs] at h; exact absurd h Bool.false_ne_true
      · exact h
    obtain ⟨hL, hD, -⟩ := hlg hs
    exact masterNodeFull_line4cd_dom_match_large hx hy hgs hnd hlt hinv hΔ hr hhd D hdom hL hD
      hs hnh
  · exact masterNodeFull_line4cd_dom_match_small hx hy hgs hnd hlt hinv hΔ hr hhd D
      (hsm hs).1 hs

end Node

end Algo

#print axioms Algo.exists_domRoundData
#print axioms Algo.exists_line4dDomData
#print axioms Algo.line4dDomOps_match_built
#print axioms Algo.masterNodeFull_line4cd_dom_match_built
