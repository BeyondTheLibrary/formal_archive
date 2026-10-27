/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Tools for the proof of [DiM, Thm. 5.2A,B]: primitive groups of degree 6.
-/
import Workspace.AltQuotients.DM52.Degree6Norm

/-!
# Primitive subgroups of small index in `A_6`

The degree-`6` case of the examination of the primitive groups of small degree in the proof
of [DiM, Thm. 5.2A] (p. 148): a primitive `G < A_6` with `|A_6 : G| < C(6,3) = 20` is
`PSL₂(5)` acting on the projective line over `F₅`; and for [DiM, Thm. 5.2B], a subgroup
`G ≤ S_6` of order `120` whose even part is that group is `PGL₂(5)`.

**Orders.**  Theorem 3.3E (with `p = 3`) makes `3` divide `h = |A : G|`, so `|G|` is one of
`120, 60, 30, 24` (it is divisible by `6`).  The Sylow `5`-count excludes `120` and, for
`60`, puts the normalizer `A ∩ N_S(⟨x⟩)` of a `5`-cycle `x` into `G`.  For `|G| = 30` the
Sylow `3`-count (the elements of order `3` are products of two `3`-cycles, by Jordan's
theorem) gives, by Burnside's theorem, a normal subgroup of order `10`, which is not
divisible by `6`.  For `|G| = 24` a point stabilizer, of order `4`, lies properly inside a
Sylow `2`-subgroup of order `8`, against its maximality (the group is primitive).

**Recognition.**  The model is the image `C6` of `SL₂(5)` acting by Möbius transformations
on `P¹(F₅) = {0,…,4,∞}` (`∞ ↦ 5`).  After relabeling, `G` contains `x ↦ x + 1` and
`x ↦ -x`, and some `g` with `g(∞) = 0`; every even such `g` lies in `C6` or produces a
`3`-cycle, and `⟨x ↦ x + 1, x ↦ -x, g⟩` has order at least `6 · 10 = 60`.
-/

namespace Babai.DM52

open Equiv Equiv.Perm MulAction Nat Subgroup
open scoped MatrixGroups

/-! ### The models -/

set_option maxRecDepth 100000 in
theorem C6data_spec : ∀ e ∈ C6data, e.1.1 * e.1.2.2.2 - e.1.2.1 * e.1.2.2.1 = 1 ∧
    ∀ i, mobF e.1.1 e.1.2.1 e.1.2.2.1 e.1.2.2.2 i = e.2 i := by
  -- stated through `List.all`, so that the check runs over the list and not over the type
  have h : C6data.all (fun e => decide (e.1.1 * e.1.2.2.2 - e.1.2.1 * e.1.2.2.1 = 1 ∧
      ∀ i, mobF e.1.1 e.1.2.1 e.1.2.2.1 e.1.2.2.2 i = e.2 i)) = true := by
    decide +kernel
  intro e he
  exact of_decide_eq_true (List.all_eq_true.mp h e he)

set_option maxRecDepth 100000 in
theorem PGL6data_spec : ∀ e ∈ PGL6data, e.1.1 * e.1.2.2.2 - e.1.2.1 * e.1.2.2.1 ≠ 0 ∧
    ∀ i, mobF e.1.1 e.1.2.1 e.1.2.2.1 e.1.2.2.2 i = e.2 i := by
  have h : PGL6data.all (fun e => decide (e.1.1 * e.1.2.2.2 - e.1.2.1 * e.1.2.2.1 ≠ 0 ∧
      ∀ i, mobF e.1.1 e.1.2.1 e.1.2.2.1 e.1.2.2.2 i = e.2 i)) = true := by
    decide +kernel
  intro e he
  exact of_decide_eq_true (List.all_eq_true.mp h e he)

set_option maxRecDepth 100000 in
theorem inC6_mobF : ∀ a b c d : ZMod 5, a * d - b * c = 1 →
    ∃ e ∈ C6data, ∀ i, mobF a b c d i = e.2 i := by
  have h : ∀ a b c d : ZMod 5, a * d - b * c = 1 →
      (C6data.any fun e => decide (∀ i, mobF a b c d i = e.2 i)) = true := by
    decide +kernel
  intro a b c d habcd
  simpa using h a b c d habcd

theorem mem_C6_of_inC6 {g : Perm (Fin 6)} (h : InC6 g) : g ∈ C6 := by
  obtain ⟨⟨⟨a, b, c, d⟩, v⟩, he, hg⟩ := h
  obtain ⟨hdet, hmob⟩ := C6data_spec _ he
  refine ⟨⟨!![a, b; c, d], by rw [Matrix.det_fin_two_of]; exact hdet⟩, Equiv.ext fun i => ?_⟩
  rw [psiSL_apply]
  simp only at hmob hg
  rw [hg]
  simpa using hmob i

theorem mem_PGL6_of_inPGL6 {g : Perm (Fin 6)} (h : InPGL6 g) : g ∈ PGL6 := by
  obtain ⟨⟨⟨a, b, c, d⟩, v⟩, he, hg⟩ := h
  obtain ⟨hdet, hmob⟩ := PGL6data_spec _ he
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero !![a, b; c, d]
    (by rw [Matrix.det_fin_two_of]; exact hdet), Equiv.ext fun i => ?_⟩
  rw [psiGL_apply]
  simp only at hmob hg
  rw [hg]
  simpa using hmob i

theorem inC6_of_mem {g : Perm (Fin 6)} (h : g ∈ C6) : InC6 g := by
  obtain ⟨A, rfl⟩ := h
  have hdet : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by rw [← Matrix.det_fin_two]; exact A.2
  obtain ⟨e, he, h⟩ := inC6_mobF _ _ _ _ hdet
  exact ⟨e, he, fun i => by rw [psiSL_apply]; exact h i⟩

/-! ### The kernels -/

set_option maxRecDepth 100000 in
theorem mobF_eq_id : ∀ a b c d : ZMod 5, a * d - b * c ≠ 0 → (∀ i, mobF a b c d i = i) →
    b = 0 ∧ c = 0 ∧ a = d := by
  decide +kernel

theorem mobF_scalar : ∀ r : ZMod 5, r ≠ 0 → ∀ i, mobF r 0 0 r i = i := by
  decide

/-- The kernel of `SL₂(5) → Sym(P¹(F₅))` is the centre. -/
theorem ker_psiSL : psiSL.ker = center (Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)) := by
  ext A
  rw [MonoidHom.mem_ker, Matrix.SpecialLinearGroup.mem_center_iff]
  have hdet : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by rw [← Matrix.det_fin_two]; exact A.2
  constructor
  · intro h
    have h' : ∀ i, mobF (A 0 0) (A 0 1) (A 1 0) (A 1 1) i = i := fun i => by
      rw [← psiSL_apply, h]; rfl
    obtain ⟨hb, hc, had⟩ := mobF_eq_id _ _ _ _ (by rw [hdet]; decide) h'
    refine ⟨A 0 0, ?_, ?_⟩
    · have := hdet
      rw [hb, hc, ← had] at this
      rw [Fintype.card_fin]; simpa [sq] using this
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [hb, hc, had]
  · rintro ⟨r, hr, hA⟩
    have hr0 : r ≠ 0 := by rintro rfl; simp at hr
    refine Equiv.ext fun i => ?_
    rw [psiSL_apply, ← hA]
    simpa using mobF_scalar r hr0 i

/-- The kernel of `GL₂(5) → Sym(P¹(F₅))` is the centre. -/
theorem ker_psiGL : psiGL.ker = center (GL (Fin 2) (ZMod 5)) := by
  ext g
  rw [MonoidHom.mem_ker, Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar]
  have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 ≠ 0 := by
    rw [← Matrix.det_fin_two]; exact g.det_ne_zero
  constructor
  · intro h
    have h' : ∀ i, mobF (g 0 0) (g 0 1) (g 1 0) (g 1 1) i = i := fun i => by
      rw [← psiGL_apply, h]; rfl
    obtain ⟨hb, hc, had⟩ := mobF_eq_id _ _ _ _ hdet h'
    refine ⟨g 0 0, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hb, hc, had]
  · rintro ⟨r, hr⟩
    have hg : ∀ i j, g i j = if i = j then r else 0 := fun i j => by
      rw [← hr]; simp [Matrix.scalar_apply, Matrix.diagonal_apply]
    have hr0 : r ≠ 0 := by
      rintro rfl; apply hdet; simp [hg]
    refine Equiv.ext fun i => ?_
    rw [psiGL_apply]
    simpa [hg] using mobF_scalar r hr0 i

/-! ### Orders of the models -/

set_option maxRecDepth 100000 in
theorem card_SL25 : Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)) = 120 := by
  rw [Nat.card_eq_fintype_card]; decide +kernel

theorem card_GL25 : Nat.card (GL (Fin 2) (ZMod 5)) = 480 := by
  rw [Matrix.card_GL_field, ZMod.card]
  decide

theorem card_C6_le : Nat.card C6 ≤ 60 := by
  have h1 : Nat.card psiSL.ker * Nat.card psiSL.range = 120 := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index, card_SL25]
  have h2 : 1 < Nat.card psiSL.ker := by
    rw [Subgroup.one_lt_card_iff_ne_bot, ker_psiSL]
    intro h
    have : (-1 : Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)) ∈
        center (Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)) :=
      Subgroup.mem_center_iff.mpr (fun g => by simp)
    rw [h, Subgroup.mem_bot] at this
    exact absurd this (by decide)
  change Nat.card psiSL.range ≤ 60
  nlinarith

theorem card_center_GL25 : Nat.card (center (GL (Fin 2) (ZMod 5))) = 4 := by
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
  have hinj : Function.Injective (Matrix.GeneralLinearGroup.scalar (Fin 2) (R := ZMod 5)) := by
    intro r s h
    have := congrArg (fun g : GL (Fin 2) (ZMod 5) => (g : Matrix (Fin 2) (Fin 2) (ZMod 5)) 0 0) h
    exact Units.ext (by simpa using this)
  rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_eq_fintype_card]
  decide

theorem card_PGL6_le : Nat.card PGL6 ≤ 120 := by
  have h1 : Nat.card psiGL.ker * Nat.card psiGL.range = 480 := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index, card_GL25]
  rw [ker_psiGL, card_center_GL25] at h1
  change Nat.card psiGL.range ≤ 120
  omega

/-- `C6 ≃* PSL₂(5)`. -/
noncomputable def C6_mulEquiv : C6 ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 5) :=
  ((QuotientGroup.quotientMulEquivOfEq ker_psiSL).symm.trans
    (QuotientGroup.quotientKerEquivRange psiSL)).symm

/-- `PGL6 ≃* PGL₂(5)`. -/
noncomputable def PGL6_mulEquiv : PGL6 ≃* PGL (Fin 2) (ZMod 5) :=
  ((QuotientGroup.quotientMulEquivOfEq ker_psiGL).symm.trans
    (QuotientGroup.quotientKerEquivRange psiGL)).symm

/-! ### Recognition -/

/-- Words in `[c6, nu6, g, g⁻¹]` (indices `0, 1, 2, 3`) one of which is a `3`-cycle for each
even `g` with `g ∞ = 0` outside `C6`. -/
def words6 : List (List ℕ) := [[0, 3, 1, 2], [0, 0, 3, 1, 2], [0, 0, 2, 0, 3], [0, 0, 3, 0, 2]]

set_option maxRecDepth 100000 in
/-- Every even `g` with `g ∞ = 0` lies in `C6` or makes a `3`-cycle with `c6, nu6`. -/
theorem degree_six_candidates : ∀ g : Perm (Fin 6), sign g = 1 → g 5 = 0 →
    InC6 g ∨ Bad3 [c6, nu6, g, g⁻¹] words6 := by
  decide +kernel

theorem c6_orbit : ∀ b : Fin 6, b ≠ 5 → ∃ m : Fin 5, (c6 ^ (m : ℕ)) 0 = b := by decide

/-- **Degree 6** ([DiM, proof of Thm. 5.2A], the examination of the primitive groups of
degree `6`): a primitive `G < A_6` with `|A_6 : G| < 20` is conjugate to the model `C6` of
`PSL₂(5)`. -/
theorem degree_six {G : Subgroup (Perm (Fin 6))} (hGA : G ≤ alternatingGroup (Fin 6))
    (hG : IsPreprimitive G (Fin 6)) (hA : ¬ alternatingGroup (Fin 6) ≤ G)
    (hidx : G.relIndex (alternatingGroup (Fin 6)) < 20) :
    ∃ σ : Perm (Fin 6), relabel σ G = C6 := by
  obtain ⟨hcard, x, hxG, hxc, hGN⟩ := degree_six_order hGA hG hA hidx
  obtain ⟨τ, hτ⟩ := isConj_iff.mp (isConj_iff_cycleType_eq.mpr (cycleType_c6.trans hxc.symm))
  have hν : τ * nu6 * τ⁻¹ ∈ G := by
    have hmem : τ * nu6 * τ⁻¹ ∈ alternatingGroup (Fin 6) ⊓
        normalizer ((zpowers x : Subgroup (Perm (Fin 6))) : Set (Perm (Fin 6))) := by
      refine ⟨by simp [mem_alternatingGroup, nu6_sign], ?_⟩
      apply mem_normalizer_zpowers_of_conj_eq_zpow (k := -1)
      rw [← hτ, conj_zpow, ← nu6_conj]
      group
    rw [← hGN] at hmem
    exact hmem.1
  set G' := relabel τ⁻¹ G with hG'
  have hc' : c6 ∈ G' := by rw [mem_relabel_perm, inv_inv, hτ]; exact hxG
  have hn' : nu6 ∈ G' := by rw [mem_relabel_perm, inv_inv]; exact hν
  have hG'A : G' ≤ alternatingGroup (Fin 6) := relabel_le_alternatingGroup _ hGA
  have hG'p : IsPreprimitive G' (Fin 6) := (isPreprimitive_relabel_iff _ G).mpr hG
  have hA' : ¬ alternatingGroup (Fin 6) ≤ G' := fun h => hA (alternatingGroup_le_of_relabel _ h)
  obtain ⟨⟨g, hg⟩, hg5⟩ := hG'p.toIsPretransitive.exists_smul_eq (5 : Fin 6) 0
  have hg5' : g 5 = 0 := hg5
  have hgs : sign g = 1 := hG'A hg
  rcases degree_six_candidates g hgs hg5' with hin | hbad
  swap
  · exact absurd hbad (not_bad3 hG'p hA' (by simp [hc', hn', hg, inv_mem hg]) words6)
  set K := closure ({c6, nu6, g} : Set (Perm (Fin 6)))
  have hKG : K ≤ G' := by
    rw [closure_le]; intro y hy
    rcases hy with rfl | rfl | rfl <;> assumption
  have hKC : K ≤ C6 := by
    rw [closure_le]; intro y hy
    rcases hy with rfl | rfl | rfl
    · exact mem_C6_of_inC6 (by decide)
    · exact mem_C6_of_inC6 (by decide)
    · exact mem_C6_of_inC6 hin
  have hcK : c6 ∈ K := subset_closure (by simp)
  have hnK : nu6 ∈ K := subset_closure (by simp)
  have hgK : g ∈ K := subset_closure (by simp)
  have hK : 60 ≤ Nat.card K := by
    have hstab : 10 ≤ Nat.card (K ⊓ stabilizer (Perm (Fin 6)) (5 : Fin 6) : Subgroup _) := by
      have hc5 : c6 ∈ K ⊓ stabilizer (Perm (Fin 6)) (5 : Fin 6) :=
        ⟨hcK, MulAction.mem_stabilizer_iff.mpr (by decide)⟩
      have hn5 : nu6 ∈ K ⊓ stabilizer (Perm (Fin 6)) (5 : Fin 6) :=
        ⟨hnK, MulAction.mem_stabilizer_iff.mpr (by decide)⟩
      have := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 5 2)
        (orderOf_c6 ▸ Subgroup.orderOf_dvd_natCard _ hc5)
        (orderOf_nu6 ▸ Subgroup.orderOf_dvd_natCard _ hn5)
      exact Nat.le_of_dvd Nat.card_pos this
    have := card_le_card_of_orbit K 5 Finset.univ (fun b _ => by
      by_cases hb : b = 5
      · exact ⟨1, K.one_mem, by rw [hb]; rfl⟩
      · obtain ⟨m, hm⟩ := c6_orbit b hb
        exact ⟨c6 ^ (m : ℕ) * g, K.mul_mem (K.pow_mem hcK _) hgK,
          by rw [Perm.mul_apply, hg5', hm]⟩) hstab
    simpa using this
  have hKG' : K = G' :=
    Subgroup.eq_of_le_of_card_ge hKG (by rw [hG', card_relabel, hcard]; exact hK)
  have hG'C : G' ≤ C6 := hKG' ▸ hKC
  refine ⟨τ⁻¹, Subgroup.eq_of_le_of_card_ge hG'C ?_⟩
  rw [card_relabel, hcard]; exact card_C6_le

/-- The order of `C6`. -/
theorem card_C6 : Nat.card C6 = 60 := by
  have h1 : Nat.card psiSL.ker * Nat.card psiSL.range = 120 := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index, card_SL25]
  have h2 : Nat.card psiSL.ker = 2 := by
    rw [ker_psiSL, ← Nat.card_congr (Equiv.subtypeEquivRight
      (fun A => (Matrix.SpecialLinearGroup.mem_center_iff (A := A)).symm)),
      Nat.card_eq_fintype_card, Fintype.card_subtype]
    decide
  change Nat.card psiSL.range = 60
  rw [h2] at h1
  omega

/-- The normalizer of `C6` in `S_6` is `PGL6`. -/
theorem inPGL6_of_normalizes : ∀ g : Perm (Fin 6), InC6 (g * c6 * g⁻¹) →
    InC6 (g * nu6 * g⁻¹) → InC6 (g * t6 * g⁻¹) → InPGL6 g := by
  intro g
  rcases fin6_cases (g 0) with h | h | h | h | h | h
  · exact d6norm_0 g h
  · exact d6norm_1 g h
  · exact d6norm_2 g h
  · exact d6norm_3 g h
  · exact d6norm_4 g h
  · exact d6norm_5 g h

/-- **Degree 6, [DiM, Thm. 5.2B]**: a subgroup `G ≤ S_6` of order `120` with
`G ∩ A_6 = C6` is `PGL₂(5)`. -/
theorem degree_six_sym {G : Subgroup (Perm (Fin 6))}
    (h0 : G ⊓ alternatingGroup (Fin 6) = C6) (hcard : Nat.card G = 120) :
    Nonempty (G ≃* PGL (Fin 2) (ZMod 5)) := by
  have hconj : ∀ g ∈ G, ∀ y, InC6 y → InC6 (g * y * g⁻¹) := by
    intro g hg y hy
    apply inC6_of_mem
    rw [← h0] at ⊢
    have hyG : y ∈ G ⊓ alternatingGroup (Fin 6) := h0 ▸ mem_C6_of_inC6 hy
    have hs : sign y = 1 := hyG.2
    exact ⟨G.mul_mem (G.mul_mem hg hyG.1) (G.inv_mem hg), by
      show sign (g * y * g⁻¹) = 1
      simp [hs]⟩
  have hle : G ≤ PGL6 := fun g hg => mem_PGL6_of_inPGL6 (inPGL6_of_normalizes g
    (hconj g hg _ (by decide)) (hconj g hg _ (by decide)) (hconj g hg _ (by decide)))
  have heq : G = PGL6 := Subgroup.eq_of_le_of_card_ge hle (by rw [hcard]; exact card_PGL6_le)
  exact ⟨(MulEquiv.subgroupCongr heq).trans PGL6_mulEquiv⟩

end Babai.DM52
