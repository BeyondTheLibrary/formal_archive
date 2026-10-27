/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 12: Corollary 12.0.10 (TopAction4) and Remark 12.0.11.
-/
import Workspace.Canonical.Align
import Workspace.Luks.Window
import Workspace.TopAction.Classes

/-!
# §12 TopAction4

Corollary 12.0.10 and Remark 12.0.11.

The corollary's hypothesis on `m = |Γ|` is `m ≥ max{16, 4 + 2 log₂ n}`
(`Babai.HugeM`), which is *stronger* than the hypothesis of Cor. 12.0.6 and of
Theorem 10.5.1; the two arithmetic lemmas below check the two implications that the proof
uses:

* `Babai.HugeM.veryLargeK`: `m ≥ max{16, 4 + 2 log₂ n}` gives `m ≥ max{9, 2 log₂ n}`, the
  hypothesis of the Main Structure Theorem (Theorem 10.5.1);
* `Babai.HugeM.largeK_of_two_mul_lt`: if in addition `|C| > m/2` then
  `|C| > max{8, 2 + log₂ n}`, the hypothesis of Cor. 12.0.8, applied to `Ω(C)`.
-/

universe u v

namespace Babai

open MulAction Equiv Equiv.Perm
open scoped Pointwise

/-! ### The threshold arithmetic -/

/-- Cor. 12.0.10's hypothesis on the size of `Γ`: `m ≥ max{16, 4 + 2 log₂ n}`. -/
def HugeM (m n : ℕ) : Prop := max 16 (4 + 2 * Real.logb 2 n) ≤ (m : ℝ)

/-- `m ≥ max{16, 4 + 2 log₂ n}` implies `m ≥ max{9, 2 log₂ n}`: the hypothesis of the Main
Structure Theorem (Theorem 10.5.1), which the proof of Cor. 12.0.10 invokes with the words
"Since `m ≥ max{9, 2 log₂ n}`". -/
theorem HugeM.veryLargeK {m n : ℕ} (h : HugeM m n) : VeryLargeK m n := by
  rw [HugeM, max_le_iff] at h
  rw [VeryLargeK, max_le_iff]
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

/-- `m ≥ max{16, 4 + 2 log₂ n}` and `|C| > m/2` imply `|C| > max{8, 2 + log₂ n}`: the proof
of Cor. 12.0.10 says "This can be done because `|C| > m/2 ≥ max{8, 2 + log₂ n}`", and the
resulting inequality is exactly the hypothesis of Cor. 12.0.8 (and of Cor. 12.0.6) for the
group acting on `Ω(C)` with the giant representation onto `C`.

The hypothesis `|C| > m/2` is stated without division, as `m < 2|C|`. -/
theorem HugeM.largeK_of_two_mul_lt {m n c : ℕ} (h : HugeM m n) (hc : m < 2 * c) :
    LargeK c n := by
  rw [HugeM, max_le_iff] at h
  have hcR : (m : ℝ) < 2 * (c : ℝ) := by exact_mod_cast hc
  rw [LargeK, max_lt_iff]
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

/-! ### `Ω(C)`, the union of the standard blocks labelled inside `C`

§12, proof of Cor. 12.0.10:

> The standard blocks are labeled by `(Γ choose t)` for some `t ≥ 1`; and `Ω(C)` denotes
> the union of the standard blocks labeled by the elements of the set `(C choose t)`.

By Theorem 10.5.1 (e) the label of the standard block containing `u` is `T(u)`
(`Babai.Tpoint`), so a standard block is labelled by a `t`-subset of `C` precisely when
`T(u) ⊆ C` for its points `u`.  That is the label-free description of `Babai.omegaOf`,
which is defined once, for Sec. 14.1 line 4, in `Workspace/Canonical/Defs.lean`. -/

variable {Ω : Type u} {A : Type v} [Fintype Ω] [DecidableEq Ω]

/-! ### `G_C` acts transitively on the window `Ω(C)`

Corollary 12.0.8, which the proof of Cor. 12.0.10 applies to the window `Ω(C)`, requires
the group acting there to be **transitive** on it.  The paper does not check this.  The
argument is recorded here; see the corrected paper. -/

/-- The group of Cor. 12.0.10 on the window: `G_C = ϕ⁻¹((S(Γ))_C)`, viewed inside `S(Ω)`.
By Prop. 12.0.9 (`Babai.Proposition_12_0_9`) this is the setwise stabilizer of `C` through
`ϕ`, and equals `ϕ⁻¹((G^ϕ)_C)`. -/
def stabOn {m : ℕ} {G : Subgroup (Equiv.Perm Ω)} (ϕ : G →* Equiv.Perm (Fin m))
    (C : Set (Fin m)) : Subgroup (Equiv.Perm Ω) :=
  preimageSubgroup ϕ (setwiseStabilizer ⊤ C)

theorem mem_stabOn {m : ℕ} {G : Subgroup (Equiv.Perm Ω)} {ϕ : G →* Equiv.Perm (Fin m)}
    {C : Set (Fin m)} {τ : Equiv.Perm Ω} :
    τ ∈ stabOn ϕ C ↔ ∃ h : τ ∈ G, (ϕ ⟨τ, h⟩) '' C = C := by
  rw [stabOn, mem_preimageSubgroup]
  exact ⟨fun ⟨h, hh⟩ => ⟨h, hh.2⟩, fun ⟨h, hh⟩ => ⟨h, ⟨trivial, hh⟩⟩⟩

theorem stabOn_le {m : ℕ} {G : Subgroup (Equiv.Perm Ω)} (ϕ : G →* Equiv.Perm (Fin m))
    (C : Set (Fin m)) : stabOn ϕ C ≤ G := preimageSubgroup_le ϕ _

/-- `Ω(C)` is `G_C`-invariant: `G_C` really does act on the window. -/
theorem isInvariant_omegaOf_stabOn {m : ℕ} {G : Subgroup (Equiv.Perm Ω)}
    (ϕ : G →* Equiv.Perm (Fin m)) (hϕ : IsGiantRep ϕ)
    (hk : VeryLargeK m (maxOrbitLength G)) (C : Set (Fin m)) :
    IsInvariant (stabOn ϕ C) (omegaOf ϕ C) := by
  refine isInvariant_omegaOf_of_le ϕ hϕ hk C (stabOn ϕ C) (stabOn_le ϕ C) ?_
  intro τ h
  exact (mem_stabOn.1 h).choose_spec

/-- The inequality behind the transitivity argument: `4t < m` (Theorem 10.5.1 (a)) and
`|C| > m/2` give `2t < |C|`, so `t ≤ |C| − 2` as soon as `|C| ≥ 4`.  This is what makes
`Alt(C)` transitive on the `t`-subsets of `C`. -/
theorem two_mul_lt_of_four_mul_lt {m t c : ℕ} (h4 : 4 * t < m) (hc : m < 2 * c) :
    2 * t < c := by omega

/-- §12, the step the proof of Cor. 12.0.10 leaves out: **`G_C` is transitive on `Ω(C)`**,
which is what Cor. 12.0.8 needs of the group acting on the window.

*The argument*.  Let `u, v ∈ Ω(C)`, i.e. `T(u) ⊆ C` and `T(v) ⊆ C`,
and write `T = T(u)`.

1. `G` is transitive on `Ω`, so there is a `τ ∈ G` with `u^τ = v`.  By Eq. (54)
   (`Babai.theorem_10_5_1_c_eq54`), `T(v) = T^{τ^ϕ}`.
2. The correction is made inside `G_u`.  Put `D = (τ^ϕ)^{-1}(C)`.  Then `|D| = |C|`, and
   `T ⊆ D` because `T^{τ^ϕ} = T(v) ⊆ C`; also `T ⊆ C`.  By Theorem 10.5.1 (a) we have
   `4|T| < m`, and `m ≥ 9`, so `|Γ ∖ T| ≥ 3`.  Hence there is an **even** permutation `α`
   of `Γ` fixing `T` pointwise with `α(C) = D`
   (`Babai.exists_alternating_fixing_image_eq`).
3. Theorem 10.5.1 (a), Eq. (52), gives `(A(Γ))_{(T(u))} ≤ G_u^ϕ`, so `α = ρ^ϕ` for some
   `ρ ∈ G_u`.
4. Then `σ = τρ` (Lean: `σ = τ * ρ`) has `σ(u) = τ(ρ(u)) = τ(u) = v` and
   `σ^ϕ(C) = τ^ϕ(α(C)) = τ^ϕ(D) = C`, so `σ ∈ G_C` and `σ` carries `u` to `v`.

The hypothesis `|C| > m/2` of Cor. 12.0.10 is not needed for this step; it is kept in the
statement because that is the situation in which the step is used.

The earlier version of this argument went through the standard blocks (transitivity of
`G_C` on the blocks `B_T` with `T ⊆ C`, then inside one block).  The route above avoids
both the block transitivity and Theorem 10.5.1 (e), (f); see the corrected paper. -/
theorem isTransitive_stabOn_omegaOf {m : ℕ} {G : Subgroup (Equiv.Perm Ω)}
    (hG : IsTransitive G) (ϕ : G →* Equiv.Perm (Fin m)) (hϕ : IsGiantRep ϕ)
    (hk : VeryLargeK m (maxOrbitLength G)) (C : Set (Fin m)) (hC : m < 2 * C.ncard)
    {u v : Ω} (hu : u ∈ omegaOf ϕ C) (hv : v ∈ omegaOf ϕ C) :
    ∃ σ ∈ stabOn ϕ C, (σ : Equiv.Perm Ω) u = v := by
  classical
  -- Step 1: a `τ ∈ G` carrying `u` to `v`.
  obtain ⟨τ, hτ⟩ := hG.isPretransitive.exists_smul_eq u v
  set T : Set (Fin m) := Tpoint ϕ u with hT
  have hTv : Tpoint ϕ v = (ϕ τ) '' T := by rw [← hτ]; exact theorem_10_5_1_c_eq54 ϕ hϕ hk u τ
  -- the arithmetic: `4|T| < m` and `m ≥ 9` give `|Γ ∖ T| ≥ 3`
  have h4 : 4 * T.ncard < m := (theorem_10_5_1_a ϕ hϕ hk u).1.1
  have hm9 : 9 ≤ m := by
    have : (9 : ℝ) ≤ (m : ℝ) := le_trans (le_max_left _ _) hk
    exact_mod_cast this
  have hsum : T.ncard + (Tᶜ : Set (Fin m)).ncard = Nat.card (Fin m) := ncard_add_ncard_compl T
  have hcompl : 3 ≤ (Tᶜ : Set (Fin m)).ncard := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fin] at hsum; omega
  -- Step 2: the corrected target set `D = (τ^ϕ)⁻¹(C)`
  set D : Set (Fin m) := ((ϕ τ)⁻¹ : Equiv.Perm (Fin m)) '' C with hD
  have hTC : T ⊆ C := hu
  have hTD : T ⊆ D := by
    intro γ hγ
    have : (ϕ τ) γ ∈ C := hv (by rw [hTv]; exact ⟨γ, hγ, rfl⟩)
    exact ⟨(ϕ τ) γ, this, by simp⟩
  have hCD : C.ncard = D.ncard := by
    rw [hD, Set.ncard_image_of_injective _ ((ϕ τ)⁻¹ : Equiv.Perm (Fin m)).injective]
  obtain ⟨α, hαalt, hαfix, hαimg⟩ :=
    exists_alternating_fixing_image_eq hTC hTD hCD hcompl
  -- Step 3: `α` comes from `G_u`
  have hsand : IsSandwichSet ((stabilizer G u).map ϕ) T := (theorem_10_5_1_a ϕ hϕ hk u).1.2
  have hαmem : α ∈ (stabilizer G u).map ϕ := hsand.2.1 ⟨hαalt, hαfix⟩
  obtain ⟨ρ, hρstab, hρα⟩ := Subgroup.mem_map.1 hαmem
  -- Step 4: `σ = τ * ρ`
  have hσG : ((τ : Equiv.Perm Ω) * (ρ : Equiv.Perm Ω)) ∈ G := mul_mem τ.2 ρ.2
  refine ⟨(τ : Equiv.Perm Ω) * (ρ : Equiv.Perm Ω), mem_stabOn.2 ⟨hσG, ?_⟩, ?_⟩
  · have hsplit : (⟨(τ : Equiv.Perm Ω) * (ρ : Equiv.Perm Ω), hσG⟩ : G) = τ * ρ := rfl
    rw [hsplit, map_mul, hρα]
    show ((ϕ τ) * α : Equiv.Perm (Fin m)) '' C = C
    rw [show (((ϕ τ) * α : Equiv.Perm (Fin m)) : Fin m → Fin m) =
        ((ϕ τ : Equiv.Perm (Fin m)) : Fin m → Fin m) ∘ ((α : Equiv.Perm (Fin m)) : Fin m → Fin m)
      from rfl, Set.image_comp, hαimg, hD, ← Set.image_comp]
    simpa using Set.image_id C
  · have hρu : (ρ : Equiv.Perm Ω) u = u := hρstab
    show (τ : Equiv.Perm Ω) ((ρ : Equiv.Perm Ω) u) = v
    rw [hρu, ← hτ]; rfl

/-! ### The representation `G_C → S(C)` factors through `S(Ω(C))`

Cor. 12.0.8 is applied on the window `Ω(C)` to the group induced there, `G_C^{Ω(C)}`, with
a giant representation onto `C`.  For that to make sense the representation `G_C → S(C)`
(the restriction to `C` of `ϕ`) must factor through `G_C^{Ω(C)}`, i.e. an element of `G_C`
that fixes `Ω(C)` pointwise must have a `ϕ`-image fixing `C` pointwise.  That is the
content of `Babai.fixes_of_fixes_omegaOf`. -/

/-- §12, proof of Cor. 12.0.10: **an element of `G_C` that fixes `Ω(C)` pointwise has a
`ϕ`-image that fixes `C` pointwise.**  (So the representation `G_C → S(C)` factors through
the image of `G_C` in `S(Ω(C))`.)

*Proof.*  Let `t = t_Ω` be the common size of the labels (`G` is transitive, so there is
one orbit, Theorem 10.5.1 (c)).

* If `t = 0` then every label is empty, so `Ω(C) = Ω`, and an element fixing `Ω` pointwise
  is the identity.
* If `t ≥ 1`, let `T ⊆ C` be any `t`-set.  By Theorem 10.5.1 (e) (`Babai.exists_Tpoint_eq`)
  there is a `u ∈ Ω` with `T(u) = T`; then `T(u) ⊆ C`, so `u ∈ Ω(C)` and `u^σ = u`, and
  Eq. (54) gives `T = T(u) = T(u^σ) = T^{σ^ϕ}`.  So `σ^ϕ` fixes every `t`-subset of `C`
  setwise.  Now fix `γ ∈ C`.  Since `4t < m < 2|C|` we have `t < |C|`, so there are a
  `t`-set `T ⊆ C` with `γ ∈ T` and a point `δ ∈ C ∖ T`; put `T' = (T ∖ {γ}) ∪ {δ}`, again
  a `t`-subset of `C`.  Both are fixed setwise by `σ^ϕ`, hence so is
  `T ∩ T' = T ∖ {γ}`, and therefore so is `{γ}`. -/
theorem fixes_of_fixes_omegaOf {m : ℕ} {G : Subgroup (Equiv.Perm Ω)}
    (hG : IsTransitive G) (ϕ : G →* Equiv.Perm (Fin m)) (hϕ : IsGiantRep ϕ)
    (hk : VeryLargeK m (maxOrbitLength G)) (C : Set (Fin m)) (hC : m < 2 * C.ncard)
    {σ : Equiv.Perm Ω} (hσ : σ ∈ stabOn ϕ C) (hfix : ∀ u ∈ omegaOf ϕ C, σ u = u) :
    ∀ γ ∈ C, ϕ ⟨σ, stabOn_le ϕ C hσ⟩ γ = γ := by
  classical
  obtain ⟨x₀, hx₀⟩ := id hG
  set s : G := ⟨σ, stabOn_le ϕ C hσ⟩ with hs
  set t : ℕ := tPoint ϕ x₀ with ht
  -- `σ^ϕ` fixes every `t`-subset of `C` setwise
  have hkey : ∀ T : Set (Fin m), T ⊆ C → T.ncard = t → (ϕ s) '' T = T := by
    intro T hTC hTt
    obtain ⟨u, -, hTu⟩ := exists_Tpoint_eq ϕ hϕ hk x₀ hTt
    have huΩ : u ∈ omegaOf ϕ C := by rw [mem_omegaOf, hTu]; exact hTC
    have hsu : s • u = u := hfix u huΩ
    have h54 := theorem_10_5_1_c_eq54 ϕ hϕ hk u s
    rw [hsu, hTu] at h54
    exact h54.symm
  rcases Nat.eq_zero_or_pos t with ht0 | ht1
  · -- `t = 0`: `Ω(C) = Ω`, so `σ = 1`
    have hall : ∀ u : Ω, u ∈ omegaOf ϕ C := by
      intro u
      have hu : tPoint ϕ u = 0 := by
        rw [theorem_10_5_1_c ϕ hϕ hk (by rw [hx₀]; trivial : u ∈ orbit G x₀), ← ht, ht0]
      have : Tpoint ϕ u = ∅ := (Set.ncard_eq_zero (Set.toFinite _)).1 hu
      rw [mem_omegaOf, this]
      exact Set.empty_subset _
    have hσ1 : σ = 1 := Equiv.ext fun u => hfix u (hall u)
    have hs1 : s = 1 := Subtype.ext hσ1
    intro γ _
    rw [hs1, map_one]
    rfl
  · -- `t ≥ 1`
    intro γ hγC
    have hfinC : C.ncard = C.toFinset.card := Set.ncard_eq_toFinset_card' C
    have h4 : 4 * t < m := (theorem_10_5_1_a ϕ hϕ hk x₀).1.1
    have htC : t < C.toFinset.card := by rw [← hfinC]; omega
    obtain ⟨T, hsub, hTC, hTcard⟩ := Finset.exists_subsuperset_card_eq
      (s := ({γ} : Finset (Fin m))) (t := C.toFinset)
      (by simpa using Set.mem_toFinset.2 hγC) (by simpa using ht1) (le_of_lt htC)
    have hγT : γ ∈ T := hsub (Finset.mem_singleton_self γ)
    obtain ⟨δ, hδC, hδT⟩ : ∃ δ ∈ C.toFinset, δ ∉ T := by
      by_contra hcon
      push_neg at hcon
      have : C.toFinset ⊆ T := hcon
      have := Finset.card_le_card this
      omega
    set T' : Finset (Fin m) := insert δ (T.erase γ) with hT'
    have hδer : δ ∉ T.erase γ := fun h => hδT (Finset.mem_of_mem_erase h)
    have hT'card : T'.card = t := by
      rw [hT', Finset.card_insert_of_notMem hδer, Finset.card_erase_of_mem hγT, hTcard]
      omega
    have hT'C : T' ⊆ C.toFinset := by
      rw [hT']
      intro a ha
      rcases Finset.mem_insert.1 ha with rfl | ha
      · exact hδC
      · exact hTC (Finset.mem_of_mem_erase ha)
    -- the two `t`-subsets of `C` and their intersection
    have hfixT : (ϕ s) '' (↑T : Set (Fin m)) = ↑T :=
      hkey _ (fun a ha => Set.mem_toFinset.1 (hTC ha)) (by rw [Set.ncard_coe_finset, hTcard])
    have hfixT' : (ϕ s) '' (↑T' : Set (Fin m)) = ↑T' :=
      hkey _ (fun a ha => Set.mem_toFinset.1 (hT'C ha)) (by rw [Set.ncard_coe_finset, hT'card])
    have hinterF : T ∩ T' = T.erase γ := by
      ext a
      simp only [Finset.mem_inter, hT', Finset.mem_insert, Finset.mem_erase]
      constructor
      · rintro ⟨haT, rfl | ⟨hane, -⟩⟩
        · exact absurd haT hδT
        · exact ⟨hane, haT⟩
      · rintro ⟨hane, haT⟩
        exact ⟨haT, Or.inr ⟨hane, haT⟩⟩
    have hinter : (↑T : Set (Fin m)) ∩ (↑T' : Set (Fin m)) = (↑(T.erase γ) : Set (Fin m)) := by
      rw [← Finset.coe_inter, hinterF]
    have hfixer : (ϕ s) '' (↑(T.erase γ) : Set (Fin m)) = (↑(T.erase γ) : Set (Fin m)) := by
      rw [← hinter, Set.image_inter (ϕ s).injective, hfixT, hfixT']
    -- conclude
    by_contra hne
    have hmem : (ϕ s) γ ∈ (↑T : Set (Fin m)) := by
      rw [← hfixT]; exact ⟨γ, hγT, rfl⟩
    have hmem' : (ϕ s) γ ∈ (↑(T.erase γ) : Set (Fin m)) := by
      simp only [Finset.mem_coe, Finset.mem_erase]
      exact ⟨hne, hmem⟩
    rw [← hfixer] at hmem'
    obtain ⟨z, hz, hzγ⟩ := hmem'
    have : z = γ := (ϕ s).injective hzγ
    rw [this] at hz
    exact (Finset.mem_erase.1 hz).1 rfl

/-! ### Corollary 12.0.8 on a window

Cor. 12.0.8 is stated (in the paper and in Lean) for a group transitive on **all** of `Ω`,
computing `Iso_G(x,y)`.  The proof of Cor. 12.0.10 applies it to the window `Ω(C)`, where
the group is `G_C` and the strings are compared only on `Ω(C)`, i.e. the object computed is
`Iso^{Ω(C)}_{G_C}(x,y)`.  This is **not** a weakening of Cor. 12.0.8: it follows from it by
restriction to the window, using the transport of `Workspace/Luks/Window.lean`.  See
the corrected paper. -/

section WindowCor

open scoped Classical

/-- §12, Cor. 12.0.8 on a window: the reduction.

`K̄ = K^Δ` is the group induced on the window by `K`, `ϕ : K̄ → S(Γ)` is the giant
representation there, and the strings are restricted to the window.  Run
`Babai.topAction3Reduction` on `Δ` and transport it to `Ω`
(`Babai.SIReduction.window`); the answer, a subset of `S(Δ)`, is turned back into the
answer on `Ω` by taking its full preimage in `K` (`Babai.windowPreim`), which is exactly
`Iso^Δ_K(x,y)` (`Babai.wIso_eq_windowPreim`). -/
noncomputable def windowTopAction3Reduction {m : ℕ} (K : Subgroup (Equiv.Perm Ω))
    (Δ : Set Ω) (hinv : IsInvariant K Δ)
    (ϕ : restrictTo K Δ hinv →* Equiv.Perm (Fin m)) (x y : Ω → A) :
    SIReduction Ω A (Option (Set (Equiv.Perm Ω))) :=
  (SIReduction.window K Δ hinv x
      (topAction3Reduction ϕ (restrictStr Δ x) (restrictStr Δ y))).bind
    fun r => .done (r.map (windowPreim K Δ hinv))

/-- §12, **Corollary 12.0.8 on a window**.

Let `Δ ⊆ Ω` be `K`-invariant, let `K̄ = K^Δ ≤ S(Δ)` be transitive on `Δ` and let
`ϕ : K̄ → S(Γ)` be a giant representation with `|Γ| = m > max{8, 2 + log₂ |Δ|}`.  Then the
same `≤ 6k` instances of window size `≤ |Δ|/k`, for some `m ≤ k ≤ |Δ|`, decide whether `ϕ`
maps `Aut_{K̄}(x|_Δ)` onto a giant and, if so, find `Iso^Δ_K(x,y)`.

This is Cor. 12.0.8 (`Babai.Corollary_12_0_8`) read on `Δ` and transported to `Ω`: the
window sizes and the number of calls are unchanged by the transport
(`Babai.SIReduction.calls_window`, `Babai.windowSize_windowInstance`), and the value computed
is transported by `Babai.wIso_eq_windowPreim`. -/
theorem Corollary_12_0_8_window {m : ℕ} (K : Subgroup (Equiv.Perm Ω)) (Δ : Set Ω)
    (hinv : IsInvariant K Δ) (hKbar : IsTransitive (restrictTo K Δ hinv))
    (ϕ : restrictTo K Δ hinv →* Equiv.Perm (Fin m)) (hϕ : IsGiantRep ϕ)
    (hm : LargeK m (Nat.card Δ)) (x y : Ω → A) :
    m ≤ orbCount ϕ ∧ orbCount ϕ ≤ Δ.ncard ∧
      (windowTopAction3Reduction K Δ hinv ϕ x y).calls.length ≤ 6 * orbCount ϕ ∧
      (∀ I ∈ (windowTopAction3Reduction K Δ hinv ϕ x y).calls,
        orbCount ϕ * I.windowSize ≤ Δ.ncard) ∧
      (windowTopAction3Reduction K Δ hinv ϕ x y).run =
        if MapsOntoGiant ϕ (restrictStr Δ x) then
          some (wIso Δ (K : Set (Equiv.Perm Ω)) x y) else none := by
  classical
  set x' := restrictStr Δ x with hx'
  set y' := restrictStr Δ y with hy'
  set R := topAction3Reduction ϕ x' y' with hR
  have hcard : Fintype.card (Δ : Set Ω) = Δ.ncard := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
  obtain ⟨hmk, hkn, hlen, hwin, hrun⟩ := Corollary_12_0_8 hKbar ϕ hϕ hm x' y'
  have hP : ∀ J ∈ R.calls, J.K ⊆ ((restrictTo K Δ hinv : Subgroup (Equiv.Perm Δ)) :
      Set (Equiv.Perm Δ)) := calls_topAction3Reduction_K ϕ x' y'
  have hcalls : (windowTopAction3Reduction K Δ hinv ϕ x y).calls =
      R.calls.map (windowInstance K Δ hinv x) := by
    rw [windowTopAction3Reduction, SIReduction.calls_bind, SIReduction.calls_done,
      List.append_nil, ← hR]
    exact SIReduction.calls_window hinv x R hP
  refine ⟨hmk, by rw [← hcard]; exact hkn, ?_, ?_, ?_⟩
  · rw [hcalls, List.length_map]; exact hlen
  · intro I hI
    rw [hcalls, List.mem_map] at hI
    obtain ⟨J, hJ, rfl⟩ := hI
    rw [windowSize_windowInstance hinv x J, ← hcard]
    exact hwin J hJ
  · rw [windowTopAction3Reduction, SIReduction.run_bind, SIReduction.run_done, ← hR,
      SIReduction.run_window hinv x R hP, hrun]
    by_cases hg : MapsOntoGiant ϕ x'
    · rw [if_pos hg, if_pos hg, Option.map_some, wIso_eq_windowPreim hinv x y]
    · rw [if_neg hg, if_neg hg, Option.map_none]

end WindowCor

/-! ### The giant representation `G_C^{Ω(C)} → S(C)` -/

section PhiC

open scoped Classical

variable {m : ℕ} {G : Subgroup (Equiv.Perm Ω)}

/-- `C` is invariant under its own setwise stabilizer in `S(Γ)`. -/
theorem isInvariant_setwiseStabilizer_self (C : Set (Fin m)) :
    IsInvariant (setwiseStabilizer ⊤ C) C := fun _ hσ => hσ.2

/-- The representation `G_C → S(C)`: apply `ϕ` (landing in `(S(Γ))_C` by the definition of
`G_C`) and restrict to `C`. -/
noncomputable def psiC (ϕ : G →* Equiv.Perm (Fin m)) (C : Set (Fin m)) :
    stabOn ϕ C →* Equiv.Perm C :=
  (restrictHom (setwiseStabilizer ⊤ C) C (isInvariant_setwiseStabilizer_self C)).comp
    (phiStar ϕ (setwiseStabilizer ⊤ C))

@[simp] theorem coe_psiC_apply (ϕ : G →* Equiv.Perm (Fin m)) (C : Set (Fin m))
    (σ : stabOn ϕ C) (γ : C) :
    ((psiC ϕ C σ γ : C) : Fin m) =
      ϕ ⟨(σ : Equiv.Perm Ω), stabOn_le ϕ C σ.2⟩ (γ : Fin m) := rfl

/-- §12, proof of Cor. 12.0.10: **the giant representation used on the window.**

`ϕ_C` is the representation `G_C^{Ω(C)} → S(C)` obtained from `Babai.psiC` by factoring
through the restriction `G_C → S(Ω(C))`, which is legitimate by
`Babai.fixes_of_fixes_omegaOf`. -/
noncomputable def phiC (hG : IsTransitive G) (ϕ : G →* Equiv.Perm (Fin m))
    (hϕ : IsGiantRep ϕ) (hk : VeryLargeK m (maxOrbitLength G)) (C : Set (Fin m))
    (hC : m < 2 * C.ncard) :
    restrictTo (stabOn ϕ C) (omegaOf ϕ C) (isInvariant_omegaOf_stabOn ϕ hϕ hk C) →*
      Equiv.Perm C :=
  (QuotientGroup.lift
      (restrictHom (stabOn ϕ C) (omegaOf ϕ C) (isInvariant_omegaOf_stabOn ϕ hϕ hk C)).ker
      (psiC ϕ C)
      (by
        intro σ hσ
        have hfix : ∀ u ∈ omegaOf ϕ C, (σ : Equiv.Perm Ω) u = u := by
          intro u hu
          have := congrArg (fun ρ : Equiv.Perm (omegaOf ϕ C) => (ρ ⟨u, hu⟩ : Ω))
            (MonoidHom.mem_ker.1 hσ)
          simpa using this
        refine Equiv.ext fun γ => Subtype.ext ?_
        rw [coe_psiC_apply]
        exact fixes_of_fixes_omegaOf hG ϕ hϕ hk C hC σ.2 hfix (γ : Fin m) γ.2)).comp
    (QuotientGroup.quotientKerEquivRange
      (restrictHom (stabOn ϕ C) (omegaOf ϕ C)
        (isInvariant_omegaOf_stabOn ϕ hϕ hk C))).symm.toMonoidHom

/-- `ϕ_C` really is the restriction of `ϕ` to `C`, read on the group induced on the
window. -/
theorem phiC_restrictHom (hG : IsTransitive G) (ϕ : G →* Equiv.Perm (Fin m))
    (hϕ : IsGiantRep ϕ) (hk : VeryLargeK m (maxOrbitLength G)) (C : Set (Fin m))
    (hC : m < 2 * C.ncard) (σ : stabOn ϕ C) :
    phiC hG ϕ hϕ hk C hC
        ⟨restrictHom (stabOn ϕ C) (omegaOf ϕ C) (isInvariant_omegaOf_stabOn ϕ hϕ hk C) σ,
          ⟨σ, rfl⟩⟩ = psiC ϕ C σ := by
  have h2 : (⟨restrictHom (stabOn ϕ C) (omegaOf ϕ C)
        (isInvariant_omegaOf_stabOn ϕ hϕ hk C) σ, ⟨σ, rfl⟩⟩ :
      restrictTo (stabOn ϕ C) (omegaOf ϕ C) (isInvariant_omegaOf_stabOn ϕ hϕ hk C)) =
      QuotientGroup.quotientKerEquivRange
        (restrictHom (stabOn ϕ C) (omegaOf ϕ C) (isInvariant_omegaOf_stabOn ϕ hϕ hk C))
        (σ : (stabOn ϕ C) ⧸ (restrictHom (stabOn ϕ C) (omegaOf ϕ C)
          (isInvariant_omegaOf_stabOn ϕ hϕ hk C)).ker) := Subtype.ext rfl
  rw [phiC, MonoidHom.comp_apply, h2]
  show QuotientGroup.lift _ (psiC ϕ C) _
      ((QuotientGroup.quotientKerEquivRange _).symm
        ((QuotientGroup.quotientKerEquivRange _) _)) = psiC ϕ C σ
  rw [MulEquiv.symm_apply_apply]
  rfl

/-- §12, proof of Cor. 12.0.10: **`ϕ_C` is a giant representation.**

Every even permutation `β` of `C` extends by the identity to an even permutation `α` of
`Γ`; `α ∈ A(Γ) ≤ G^ϕ`, and `α` preserves `C`, so its `ϕ`-preimage lies in `G_C` and its
`ϕ_C`-image is `β`. -/
theorem isGiantRep_phiC (hG : IsTransitive G) (ϕ : G →* Equiv.Perm (Fin m))
    (hϕ : IsGiantRep ϕ) (hk : VeryLargeK m (maxOrbitLength G)) (C : Set (Fin m))
    (hC : m < 2 * C.ncard) : IsGiantRep (phiC hG ϕ hϕ hk C hC) := by
  intro β hβ
  set α : Equiv.Perm (Fin m) := Equiv.Perm.ofSubtype β with hα
  have hval : ∀ γ (hγ : γ ∈ C), α γ = ((β ⟨γ, hγ⟩ : C) : Fin m) :=
    fun γ hγ => Equiv.Perm.ofSubtype_apply_of_mem β hγ
  have hαalt : α ∈ alternatingGroup (Fin m) := by
    rw [Equiv.Perm.mem_alternatingGroup, hα, Equiv.Perm.sign_ofSubtype]
    exact hβ
  obtain ⟨g, hg⟩ := hϕ hαalt
  have hsub : α '' C ⊆ C := by
    rintro _ ⟨γ, hγ, rfl⟩
    rw [hval γ hγ]
    exact (β ⟨γ, hγ⟩).2
  have hαimg : α '' C = C :=
    Set.eq_of_subset_of_ncard_le hsub
      (le_of_eq (Set.ncard_image_of_injective _ α.injective).symm) (Set.toFinite _)
  have hgmem : (g : Equiv.Perm Ω) ∈ stabOn ϕ C :=
    mem_stabOn.2 ⟨g.2, by rw [show (⟨(g : Equiv.Perm Ω), g.2⟩ : G) = g from rfl, hg]; exact hαimg⟩
  refine ⟨⟨restrictHom (stabOn ϕ C) (omegaOf ϕ C) (isInvariant_omegaOf_stabOn ϕ hϕ hk C)
      ⟨(g : Equiv.Perm Ω), hgmem⟩, ⟨⟨(g : Equiv.Perm Ω), hgmem⟩, rfl⟩⟩, ?_⟩
  rw [phiC_restrictHom]
  refine Equiv.ext fun γ => Subtype.ext ?_
  rw [coe_psiC_apply, show (⟨(g : Equiv.Perm Ω), stabOn_le ϕ C hgmem⟩ : G) = g from rfl, hg]
  exact hval (γ : Fin m) γ.2

/-- The window `Ω(C)` is nonempty: `4t < m < 2|C|` gives `t ≤ |C|`, so `C` has a `t`-subset
`T`, and by Theorem 10.5.1 (e) (`Babai.exists_Tpoint_eq`) some `u ∈ Ω` has `T(u) = T`. -/
theorem nonempty_omegaOf (hG : IsTransitive G) (ϕ : G →* Equiv.Perm (Fin m))
    (hϕ : IsGiantRep ϕ) (hk : VeryLargeK m (maxOrbitLength G)) (C : Set (Fin m))
    (hC : m < 2 * C.ncard) : (omegaOf ϕ C).Nonempty := by
  classical
  obtain ⟨x₀, -⟩ := id hG
  have h4 : 4 * tPoint ϕ x₀ < m := (theorem_10_5_1_a ϕ hϕ hk x₀).1.1
  have hfinC : C.ncard = C.toFinset.card := Set.ncard_eq_toFinset_card' C
  have htC : tPoint ϕ x₀ ≤ C.toFinset.card := by rw [← hfinC]; omega
  obtain ⟨T, hTC, hTcard⟩ := Finset.exists_subset_card_eq htC
  obtain ⟨u, -, hTu⟩ := exists_Tpoint_eq ϕ hϕ hk x₀
    (T := (↑T : Set (Fin m))) (by rw [Set.ncard_coe_finset, hTcard])
  exact ⟨u, by rw [mem_omegaOf, hTu]; exact fun a ha => Set.mem_toFinset.1 (hTC ha)⟩

/-- §12, proof of Cor. 12.0.10: the group induced by `G_C` on the window `Ω(C)` is
transitive on it (`Babai.isTransitive_stabOn_omegaOf` in the form Cor. 12.0.8 needs). -/
theorem isTransitive_restrictTo_omegaOf (hG : IsTransitive G) (ϕ : G →* Equiv.Perm (Fin m))
    (hϕ : IsGiantRep ϕ) (hk : VeryLargeK m (maxOrbitLength G)) (C : Set (Fin m))
    (hC : m < 2 * C.ncard) :
    IsTransitive (restrictTo (stabOn ϕ C) (omegaOf ϕ C)
      (isInvariant_omegaOf_stabOn ϕ hϕ hk C)) := by
  obtain ⟨u₀, hu₀⟩ := nonempty_omegaOf hG ϕ hϕ hk C hC
  refine (isTransitiveAction_iff _ _).2 ⟨⟨⟨u₀, hu₀⟩⟩, ⟨fun a b => ?_⟩⟩
  obtain ⟨σ, hσ, hab⟩ := isTransitive_stabOn_omegaOf hG ϕ hϕ hk C hC a.2 b.2
  refine ⟨⟨restrictHom (stabOn ϕ C) (omegaOf ϕ C)
    (isInvariant_omegaOf_stabOn ϕ hϕ hk C) ⟨σ, hσ⟩, ⟨⟨σ, hσ⟩, rfl⟩⟩, ?_⟩
  exact Subtype.ext hab

end PhiC

/-! ### Matching `S(C)` with `S([|C|])`

Cor. 12.0.8 (and its window version) asks for a representation onto `S(Fin m')`, while
`Babai.phiC` lands in `S(C)`.  The two are matched by a bijection `C ≃ [|C|]`. -/

section FinTarget

open scoped Classical

variable {m : ℕ} {G : Subgroup (Equiv.Perm Ω)}

/-- A bijection `C ≃ [|C|]`. -/
noncomputable def colorEquivFin (C : Set (Fin m)) : (C : Set (Fin m)) ≃ Fin C.ncard :=
  (Finite.equivFin C).trans (finCongr (Nat.card_coe_set_eq C))

/-- §12, proof of Cor. 12.0.10: the giant representation of the window group with the
target `S([|C|])` that Cor. 12.0.8 asks for — `Babai.phiC` transported along
`Babai.colorEquivFin`. -/
noncomputable def phiCFin (hG : IsTransitive G) (ϕ : G →* Equiv.Perm (Fin m))
    (hϕ : IsGiantRep ϕ) (hk : VeryLargeK m (maxOrbitLength G)) (C : Set (Fin m))
    (hC : m < 2 * C.ncard) :
    restrictTo (stabOn ϕ C) (omegaOf ϕ C) (isInvariant_omegaOf_stabOn ϕ hϕ hk C) →*
      Equiv.Perm (Fin C.ncard) :=
  (Equiv.permCongrHom (colorEquivFin C)).toMonoidHom.comp (phiC hG ϕ hϕ hk C hC)

theorem isGiantRep_phiCFin (hG : IsTransitive G) (ϕ : G →* Equiv.Perm (Fin m))
    (hϕ : IsGiantRep ϕ) (hk : VeryLargeK m (maxOrbitLength G)) (C : Set (Fin m))
    (hC : m < 2 * C.ncard) : IsGiantRep (phiCFin hG ϕ hϕ hk C hC) := by
  intro δ hδ
  set β : Equiv.Perm (C : Set (Fin m)) := (colorEquivFin C).symm.permCongr δ with hβ
  have h1 : β ∈ alternatingGroup (C : Set (Fin m)) := by
    rw [Equiv.Perm.mem_alternatingGroup, hβ, Equiv.Perm.sign_permCongr]
    exact hδ
  obtain ⟨g, hg⟩ := isGiantRep_phiC hG ϕ hϕ hk C hC h1
  refine ⟨g, ?_⟩
  rw [phiCFin, MonoidHom.comp_apply, hg]
  show (colorEquivFin C).permCongr β = δ
  rw [hβ, ← Equiv.permCongr_symm, Equiv.apply_symm_apply]

/-- §12, proof of Cor. 12.0.10: the hypothesis *"the restriction of `Aut_G(x)^ϕ` to `C` is
a giant"* is exactly what Cor. 12.0.8 needs on the window, namely that `ϕ_C` maps
`Aut(x|_{Ω(C)})` onto a giant.

Given an even `δ ∈ A([|C|])`, transport it to `β ∈ A(C)` and extend it by the identity to
an even permutation `α` of `Γ` fixing `Γ ∖ C` pointwise.  The hypothesis produces a
`τ ∈ Aut_G(x)` with `τ^ϕ|_C = α|_C`; then `τ^ϕ` preserves `C`, so `τ ∈ G_C`, its
restriction to `Ω(C)` is an automorphism of `x|_{Ω(C)}`, and its `ϕ_C`-image is `β`,
i.e. its `phiCFin`-image is `δ`. -/
theorem mapsOntoGiant_phiCFin (hG : IsTransitive G) (ϕ : G →* Equiv.Perm (Fin m))
    (hϕ : IsGiantRep ϕ) (hk : VeryLargeK m (maxOrbitLength G)) (C : Set (Fin m))
    (hC : m < 2 * C.ncard) (x : Ω → A)
    (hgiantC : ∀ α : Equiv.Perm (Fin m), α ∈ alternatingGroup (Fin m) →
      (∀ γ, γ ∉ C → α γ = γ) →
      ∃ β ∈ homImage ϕ (strAut (G : Set (Equiv.Perm Ω)) x), ∀ γ ∈ C, β γ = α γ) :
    MapsOntoGiant (phiCFin hG ϕ hϕ hk C hC)
      (restrictStr (omegaOf ϕ C) x) := by
  intro δ hδ
  set β : Equiv.Perm (C : Set (Fin m)) := (colorEquivFin C).symm.permCongr δ with hβdef
  have hβ : β ∈ alternatingGroup (C : Set (Fin m)) := by
    rw [Equiv.Perm.mem_alternatingGroup, hβdef, Equiv.Perm.sign_permCongr]
    exact hδ
  set α : Equiv.Perm (Fin m) := Equiv.Perm.ofSubtype β with hαdef
  have hval : ∀ γ (hγ : γ ∈ C), α γ = ((β ⟨γ, hγ⟩ : C) : Fin m) :=
    fun γ hγ => Equiv.Perm.ofSubtype_apply_of_mem β hγ
  have hαalt : α ∈ alternatingGroup (Fin m) := by
    rw [Equiv.Perm.mem_alternatingGroup, hαdef, Equiv.Perm.sign_ofSubtype]
    exact hβ
  have hαfix : ∀ γ, γ ∉ C → α γ = γ := fun γ hγ =>
    Equiv.Perm.ofSubtype_apply_of_not_mem β hγ
  obtain ⟨b, hbmem, hbC⟩ := hgiantC α hαalt hαfix
  obtain ⟨τ, hτaut, hτG, hτϕ⟩ := hbmem
  -- `τ^ϕ` preserves `C` setwise
  have himgsub : (ϕ ⟨τ, hτG⟩) '' C ⊆ C := by
    rintro _ ⟨γ, hγ, rfl⟩
    rw [hτϕ, hbC γ hγ, hval γ hγ]
    exact (β ⟨γ, hγ⟩).2
  have himg : (ϕ ⟨τ, hτG⟩) '' C = C :=
    Set.eq_of_subset_of_ncard_le himgsub
      (le_of_eq (Set.ncard_image_of_injective _ (ϕ ⟨τ, hτG⟩).injective).symm)
      (Set.toFinite _)
  have hτC : τ ∈ stabOn ϕ C := mem_stabOn.2 ⟨hτG, himg⟩
  -- the restriction of `τ` to the window
  set ρ : restrictTo (stabOn ϕ C) (omegaOf ϕ C)
      (isInvariant_omegaOf_stabOn ϕ hϕ hk C) :=
    ⟨restrictHom (stabOn ϕ C) (omegaOf ϕ C) (isInvariant_omegaOf_stabOn ϕ hϕ hk C)
      ⟨τ, hτC⟩, ⟨⟨τ, hτC⟩, rfl⟩⟩ with hρdef
  refine ⟨(ρ : Equiv.Perm (omegaOf ϕ C)), ⟨ρ.2, ?_⟩, ρ.2, ?_⟩
  · -- `ρ` fixes the restricted string
    have hxτ : strAct x τ = x := hτaut.2
    funext w
    show restrictStr (omegaOf ϕ C) x ((ρ : Equiv.Perm (omegaOf ϕ C))⁻¹ w) =
      restrictStr (omegaOf ϕ C) x w
    have h1 : ((((ρ : Equiv.Perm (omegaOf ϕ C))⁻¹ w) : omegaOf ϕ C) : Ω) =
        (τ : Equiv.Perm Ω)⁻¹ (w : Ω) := by
      have h2 : (ρ : Equiv.Perm (omegaOf ϕ C))
          ((ρ : Equiv.Perm (omegaOf ϕ C))⁻¹ w) = w := by simp
      have h3 : ((((ρ : Equiv.Perm (omegaOf ϕ C))
          ((ρ : Equiv.Perm (omegaOf ϕ C))⁻¹ w)) : omegaOf ϕ C) : Ω) =
          (τ : Equiv.Perm Ω) (((((ρ : Equiv.Perm (omegaOf ϕ C))⁻¹ w)) : omegaOf ϕ C) : Ω) :=
        rfl
      rw [h2] at h3
      rw [h3]
      simp
    show x (((((ρ : Equiv.Perm (omegaOf ϕ C))⁻¹ w)) : omegaOf ϕ C) : Ω) = x (w : Ω)
    rw [h1]
    exact congrFun hxτ (w : Ω)
  · -- the `phiCFin`-image of `ρ` is `δ`
    have hphi : phiC hG ϕ hϕ hk C hC ρ = psiC ϕ C ⟨τ, hτC⟩ :=
      phiC_restrictHom hG ϕ hϕ hk C hC ⟨τ, hτC⟩
    have hpsi : psiC ϕ C ⟨τ, hτC⟩ = β := by
      refine Equiv.ext fun γ => Subtype.ext ?_
      rw [coe_psiC_apply]
      have : (⟨(τ : Equiv.Perm Ω), stabOn_le ϕ C hτC⟩ : G) = ⟨τ, hτG⟩ := rfl
      rw [this, hτϕ, hbC (γ : Fin m) γ.2, hval (γ : Fin m) γ.2]
    rw [phiCFin, MonoidHom.comp_apply, hphi, hpsi]
    show (colorEquivFin C).permCongr β = δ
    rw [hβdef, ← Equiv.permCongr_symm, Equiv.apply_symm_apply]

end FinTarget

/-! ### Procedure Align, lines 1–3, for the structure `X(z) = C_z` -/

section AlignColor

open scoped Classical

variable {Γ κ : Type*} {G : Subgroup (Equiv.Perm Ω)}

/-- Procedure Align, lines 2 (i)–(ii), for the structure `X(z) = C_z`: an element of `G`
whose `ϕ`-image carries the color class of `x` onto the color class of `y` (the
"aligning" permutation `σ`), or `1` if there is none.  When the two classes have the same
size there is one, because `A(Γ) ≤ G^ϕ` is transitive on the subsets of `Γ` of a given
size (`Babai.exists_alignColorElt`). -/
noncomputable def alignColorElt (ϕ : G →* Equiv.Perm Γ) (col : (Ω → A) → Γ → κ)
    (x y : Ω → A) (c : κ) : G :=
  if h : ∃ σ : G, (ϕ σ) '' colorClass col x c = colorClass col y c then h.choose else 1

theorem alignColorElt_spec {ϕ : G →* Equiv.Perm Γ} {col : (Ω → A) → Γ → κ}
    {x y : Ω → A} {c : κ}
    (h : ∃ σ : G, (ϕ σ) '' colorClass col x c = colorClass col y c) :
    (ϕ (alignColorElt ϕ col x y c)) '' colorClass col x c = colorClass col y c := by
  rw [alignColorElt, dif_pos h]
  exact h.choose_spec

/-- Procedure Align, line 1 for `X(z) = C_z`: if the two color classes have the same size
then the aligning permutation exists.  (`A(Γ) ≤ G^ϕ`, and `A(Γ)` is transitive on the
subsets of `Γ` of a given size as soon as `|Γ| ≥ 3`.) -/
theorem exists_alignColorElt {m : ℕ} (ϕ : G →* Equiv.Perm (Fin m)) (hϕ : IsGiantRep ϕ)
    (hm3 : 3 ≤ m) (col : (Ω → A) → Fin m → κ) (x y : Ω → A) (c : κ)
    (hcard : (colorClass col x c).ncard = (colorClass col y c).ncard) :
    ∃ σ : G, (ϕ σ) '' colorClass col x c = colorClass col y c := by
  obtain ⟨α, hα, himg⟩ :=
    exists_alternating_image_eq (Δ := Fin m) (by simpa using hm3) hcard
  obtain ⟨σ, hσ⟩ := hϕ hα
  exact ⟨σ, by rw [hσ]; exact himg⟩

end AlignColor

/-! ### Corollary 12.0.10 (TopAction4) -/

section TopAction4

open scoped Classical

variable {m : ℕ} {κ : Type*} {G : Subgroup (Equiv.Perm Ω)}

/-- The hypothesis of Theorem 10.5.1 for the longest orbit, from the hypothesis
`m ≥ max{16, 4 + 2 log₂ n}` of Cor. 12.0.10: `Babai.HugeM.veryLargeK` followed by
`Babai.veryLargeK_maxOrbitLength` (`G` is transitive, so `Ω` is nonempty).  So the
Lean statement of Cor. 12.0.10 assumes no more than the paper does. -/
theorem veryLargeK_of_hugeM (hG : IsTransitive G) (hm : HugeM m (Nat.card Ω)) :
    VeryLargeK m (maxOrbitLength G) := by
  haveI : Nonempty Ω := hG.nonempty
  exact veryLargeK_maxOrbitLength hm.veryLargeK

/-- `t_Ω`, the common size of the labels `T(u)` for a transitive `G`
(Theorem 10.5.1 (c)). -/
noncomputable def tOf (hG : IsTransitive G) (ϕ : G →* Equiv.Perm (Fin m)) : ℕ :=
  tPoint ϕ hG.nonempty.some

theorem tPoint_eq_tOf (hG : IsTransitive G) (ϕ : G →* Equiv.Perm (Fin m))
    (hϕ : IsGiantRep ϕ) (hk : VeryLargeK m (maxOrbitLength G)) (u : Ω) :
    tPoint ϕ u = tOf hG ϕ := by
  haveI : Nonempty Ω := hG.nonempty
  have horb : orbit G hG.nonempty.some = (Set.univ : Set Ω) :=
    (isTransitive_iff_orbit_eq_univ G).1 hG _
  exact theorem_10_5_1_c ϕ hϕ hk (by rw [horb]; trivial)

/-- §12, the body of Procedure TopAction4 after the alignment, i.e. Procedure Align lines
5–6 for the two-coloring `(C, Γ ∖ C)`:

> Now we process `Ω(C)` via Cor. 12.0.8. … Then proceed to the remaining color classes in
> accordance with the Chain Rule.

The first window `Ω(C)` is handled by the window version of Cor. 12.0.8
(`Babai.windowTopAction3Reduction` with the giant representation `Babai.phiCFin`), and its
answer — a coset of `Aut^{Ω(C)}_{G_C}(x)` — is the starting state of the Chain Rule
(`Babai.chainReduction`) over the remaining color classes
`Ω_j = {u | |T(u) ∩ C| = j}`, `j < t` (`Babai.omegaCut`). -/
noncomputable def topAction4Body (hG : IsTransitive G) (ϕ : G →* Equiv.Perm (Fin m))
    (hϕ : IsGiantRep ϕ) (hk : VeryLargeK m (maxOrbitLength G)) (C : Set (Fin m))
    (hC : m < 2 * C.ncard) (x y' : Ω → A) (t : ℕ) :
    SIReduction Ω A (Set (Equiv.Perm Ω)) :=
  (windowTopAction3Reduction (stabOn ϕ C) (omegaOf ϕ C)
      (isInvariant_omegaOf_stabOn ϕ hϕ hk C) (phiCFin hG ϕ hϕ hk C hC) x y').bind
    fun r =>
      match r with
      | none => .done (∅ : Set (Equiv.Perm Ω))
      | some S =>
          if h : S.Nonempty then
            chainReduction (stabOn ϕ C) x y' ((List.range t).map (omegaCut ϕ C)) h.some
              (stabOn ϕ C ⊓ autWindow (stabOn ϕ C) (omegaOf ϕ C) x)
          else .done ∅

/-- Every call of Cor. 12.0.8 on a window has its candidate set inside `K`: the calls are
the lifted calls of `Babai.topAction3Reduction`, and a lifted call has for candidate set a
full preimage in `K`.  This is what lets the reduction be transported to a window again
(`Workspace/Luks/Window.lean`). -/
theorem calls_windowTopAction3Reduction_K {m : ℕ} (K : Subgroup (Equiv.Perm Ω))
    (Δ : Set Ω) (hinv : IsInvariant K Δ)
    (ϕ : restrictTo K Δ hinv →* Equiv.Perm (Fin m)) (x y : Ω → A) :
    ∀ I ∈ (windowTopAction3Reduction K Δ hinv ϕ x y).calls,
      I.K ⊆ (K : Set (Equiv.Perm Ω)) := by
  classical
  rw [windowTopAction3Reduction, SIReduction.calls_bind, SIReduction.calls_done,
    List.append_nil,
    SIReduction.calls_window hinv x _ (calls_topAction3Reduction_K ϕ _ _)]
  intro J hJ
  rw [List.mem_map] at hJ
  obtain ⟨J', -, rfl⟩ := hJ
  intro τ hτ
  obtain ⟨hK, -⟩ := hτ
  exact hK

/-- Every call of `Babai.topAction4Body` has its candidate set inside `G`: the first family
lives inside `G_C` through a window, and the Chain Rule that follows only shrinks the
group, starting from `G_C ≤ G`. -/
theorem calls_topAction4Body_K (hG : IsTransitive G) (ϕ : G →* Equiv.Perm (Fin m))
    (hϕ : IsGiantRep ϕ) (hk : VeryLargeK m (maxOrbitLength G)) (C : Set (Fin m))
    (hC : m < 2 * C.ncard) (x y' : Ω → A) (t : ℕ) :
    ∀ J ∈ (topAction4Body hG ϕ hϕ hk C hC x y' t).calls,
      J.K ⊆ (G : Set (Equiv.Perm Ω)) := by
  classical
  rw [topAction4Body, SIReduction.calls_bind]
  intro J hJ
  rcases List.mem_append.1 hJ with h | h
  · exact fun τ hτ => stabOn_le ϕ C
      (calls_windowTopAction3Reduction_K _ _ _ _ x y' J h hτ)
  · revert h
    generalize (windowTopAction3Reduction (stabOn ϕ C) (omegaOf ϕ C)
      (isInvariant_omegaOf_stabOn ϕ hϕ hk C) (phiCFin hG ϕ hϕ hk C hC) x y').run = r
    cases r with
    | none => intro h; simp [SIReduction.calls_done] at h
    | some S =>
      by_cases hS : S.Nonempty
      · simp only [dif_pos hS]
        intro h τ hτ
        have hmem := calls_chainReduction_K (stabOn ϕ C) x y' _ _ _ J h hτ
        exact stabOn_le ϕ C (Subgroup.mem_inf.1 (SetLike.mem_coe.1 hmem)).1
      · intro h; simp [dif_neg hS, SIReduction.calls_done] at h

/-- §12, **Procedure TopAction4** as a named reduction: Procedure Align lines 1–3 for the
structure `X(z) = C_z` (reject if the two color classes have different sizes, otherwise
align `y` by `σ` and pass to `G₁ = G_C`), then `Babai.topAction4Body`. -/
noncomputable def topAction4Reduction (hG : IsTransitive G) (ϕ : G →* Equiv.Perm (Fin m))
    (hϕ : IsGiantRep ϕ) (hk : VeryLargeK m (maxOrbitLength G))
    (col : (Ω → A) → Fin m → κ) (c : κ) (x y : Ω → A)
    (hC : m < 2 * (colorClass col x c).ncard) : SIReduction Ω A (Set (Equiv.Perm Ω)) :=
  if (colorClass col x c).ncard = (colorClass col y c).ncard then
    (topAction4Body hG ϕ hϕ hk (colorClass col x c) hC x
        (strAct y ((alignColorElt ϕ col x y c : G) : Equiv.Perm Ω)⁻¹) (tOf hG ϕ)).bind
      fun ans => .done (((alignColorElt ϕ col x y c : G) : Equiv.Perm Ω) • ans)
  else .done ∅

/-- `Iso_K(x,y) ⊆ Iso^Δ_K(x,y)`: an isomorphism is in particular a window isomorphism. -/
theorem strIso_subset_wIso (Δ : Set Ω) (K : Set (Equiv.Perm Ω)) (x y : Ω → A) :
    strIso K x y ⊆ wIso Δ K x y :=
  fun τ hτ => ⟨hτ.1, fun u _ => by rw [← hτ.2]; exact (strAct_apply x τ u).symm⟩

/-- §12, lines 5–6 of the proof of Cor. 12.0.10: the reduction of the *aligned* instance
computes `Iso_{G_C}(x,y')`, and its calls split into the `≤ 6k` calls of Cor. 12.0.8 on the
window `Ω(C)` and one call per remaining color class `Ω_j`, `j < t`.

The Chain Rule visits each of the `t` remaining classes at most once, so the second family
has at most `t` members (`Babai.calls_chainReduction`). -/
theorem topAction4Body_spec (hG : IsTransitive G) (ϕ : G →* Equiv.Perm (Fin m))
    (hϕ : IsGiantRep ϕ) (hk : VeryLargeK m (maxOrbitLength G)) (C : Set (Fin m))
    (hC : m < 2 * C.ncard) (x y' : Ω → A) {t : ℕ} (ht : ∀ u : Ω, tPoint ϕ u = t)
    (hlarge : LargeK C.ncard (Nat.card (omegaOf ϕ C)))
    (hmaps : MapsOntoGiant (phiCFin hG ϕ hϕ hk C hC) (restrictStr (omegaOf ϕ C) x)) :
    (topAction4Body hG ϕ hϕ hk C hC x y' t).run =
        strIso ((stabOn ϕ C : Subgroup (Equiv.Perm Ω)) : Set (Equiv.Perm Ω)) x y' ∧
      ∃ rest : List (SIInstance Ω A),
        (topAction4Body hG ϕ hϕ hk C hC x y' t).calls =
          (windowTopAction3Reduction (stabOn ϕ C) (omegaOf ϕ C)
            (isInvariant_omegaOf_stabOn ϕ hϕ hk C) (phiCFin hG ϕ hϕ hk C hC) x y').calls
            ++ rest ∧
          (∀ I ∈ rest, ∃ j < t, I.Δ = omegaCut ϕ C j) ∧
          rest.length ≤ t ∧
          (rest.map SIInstance.windowSize).sum ≤
            ∑ j ∈ Finset.range t, (omegaCut (Ω := Ω) ϕ C j).ncard := by
  classical
  set G₁ : Subgroup (Equiv.Perm Ω) := stabOn ϕ C with hG₁
  set ΩC : Set Ω := omegaOf ϕ C with hΩCdef
  set hinv : IsInvariant G₁ ΩC := isInvariant_omegaOf_stabOn ϕ hϕ hk C with hinvdef
  set W := windowTopAction3Reduction G₁ ΩC hinv (phiCFin hG ϕ hϕ hk C hC) x y' with hWdef
  set Δs : List (Set Ω) := (List.range t).map (omegaCut ϕ C) with hΔsdef
  set M : Subgroup (Equiv.Perm Ω) := G₁ ⊓ autWindow G₁ ΩC x with hMdef
  -- the window reduction answers `Iso^{Ω(C)}_{G₁}(x,y')`
  obtain ⟨-, -, -, -, hWrun⟩ :=
    Corollary_12_0_8_window G₁ ΩC hinv
      (isTransitive_restrictTo_omegaOf hG ϕ hϕ hk C hC) (phiCFin hG ϕ hϕ hk C hC)
      (isGiantRep_phiCFin hG ϕ hϕ hk C hC) hlarge x y'
  rw [if_pos hmaps] at hWrun
  set S : Set (Equiv.Perm Ω) := wIso ΩC (G₁ : Set (Equiv.Perm Ω)) x y' with hSdef
  -- the continuation, evaluated at the answer
  have hcont : (fun r : Option (Set (Equiv.Perm Ω)) =>
        match r with
        | none => (SIReduction.done (Ω := Ω) (A := A) (∅ : Set (Equiv.Perm Ω)))
        | some S' => if h : S'.Nonempty then
              chainReduction G₁ x y' Δs h.some M else .done ∅) (some S) =
      (if h : S.Nonempty then chainReduction G₁ x y' Δs h.some M else .done ∅) := rfl
  have hbodyrun : (topAction4Body hG ϕ hϕ hk C hC x y' t).run =
      (if h : S.Nonempty then chainReduction G₁ x y' Δs h.some M else .done ∅).run := by
    rw [topAction4Body, SIReduction.run_bind, ← hWdef, hWrun, ← hcont]
  have hbodycalls : (topAction4Body hG ϕ hϕ hk C hC x y' t).calls =
      W.calls ++ (if h : S.Nonempty then chainReduction G₁ x y' Δs h.some M
        else .done ∅).calls := by
    rw [topAction4Body, SIReduction.calls_bind, ← hWdef, hWrun, ← hcont]
  -- the windows of the Chain Rule are `G₁`-invariant
  have hinvΔ : ∀ Δ ∈ Δs, IsInvariant G₁ Δ := by
    intro Δ hΔ
    rw [hΔsdef, List.mem_map] at hΔ
    obtain ⟨j, -, rfl⟩ := hΔ
    refine isInvariant_omegaCut ϕ hϕ hk C j G₁ (stabOn_le ϕ C) ?_
    intro τ hτ
    exact (mem_stabOn.1 hτ).choose_spec
  -- the coverage of `Ω` by `Ω(C)` and the remaining classes
  have hcover : ΩC ∪ ⋃ Δ ∈ Δs, Δ = (Set.univ : Set Ω) := by
    have hmapU : (⋃ Δ ∈ Δs, Δ) = ⋃ j ∈ List.range t, omegaCut (Ω := Ω) ϕ C j := by
      ext u
      simp only [hΔsdef, Set.mem_iUnion, List.mem_map, exists_prop]
      constructor
      · rintro ⟨Δ, ⟨j, hj, rfl⟩, hu⟩; exact ⟨j, hj, hu⟩
      · rintro ⟨j, hj, hu⟩; exact ⟨_, ⟨j, hj, rfl⟩, hu⟩
    rw [hmapU, hΩCdef]
    exact omegaCut_cover ϕ C ht
  by_cases hSne : S.Nonempty
  · rw [dif_pos hSne] at hbodyrun hbodycalls
    have hρ : hSne.some ∈ S := hSne.some_mem
    have hcoset : wIso ΩC (G₁ : Set (Equiv.Perm Ω)) x y' =
        hSne.some • ((M : Subgroup (Equiv.Perm Ω)) : Set (Equiv.Perm Ω)) := by
      rw [wIso_eq_smul_wAut_one hinv hρ, hMdef, ← wAut_eq_inf (le_refl G₁) hinv x]
    have hrun := run_chainReduction (N := G₁) x y' Δs ΩC hSne.some M hinvΔ hinv
      inf_le_left hρ.1 hcoset
    refine ⟨?_, (chainReduction G₁ x y' Δs hSne.some M).calls, hbodycalls, ?_, ?_, ?_⟩
    · rw [hbodyrun, hrun, hcover, wIso_univ]
    · intro I hI
      have hmem := (calls_chainReduction G₁ x y' Δs hSne.some M).2 I hI
      rw [hΔsdef, List.mem_map] at hmem
      obtain ⟨j, hj, hIj⟩ := hmem
      exact ⟨j, List.mem_range.1 hj, hIj.symm⟩
    · have hlen := (calls_chainReduction G₁ x y' Δs hSne.some M).1
      rwa [hΔsdef, List.length_map, List.length_range] at hlen
    · have hsum := sum_windowSize_calls_chainReduction G₁ x y' Δs hSne.some M
      rw [hΔsdef, List.map_map] at hsum
      simp only [Function.comp_def] at hsum
      rw [sum_list_range (fun j => (omegaCut (Ω := Ω) ϕ C j).ncard) t] at hsum
      exact hsum
  · rw [dif_neg hSne] at hbodyrun hbodycalls
    have hSempty : S = ∅ := Set.not_nonempty_iff_eq_empty.1 hSne
    refine ⟨?_, [], by simpa using hbodycalls, by simp, by simp, by simp⟩
    rw [hbodyrun, SIReduction.run_done]
    symm
    rw [Set.eq_empty_iff_forall_notMem]
    intro τ hτ
    have : τ ∈ S := strIso_subset_wIso ΩC _ x y' hτ
    rw [hSempty] at this
    exact this

open Classical in
/-- §12, **Corollary 12.0.10** (TopAction4).

> Let `G ≤ S(Ω)` be a transitive permutation group and `ϕ : G → S(Γ)` a giant
> representation where `|Γ| = m ≥ max{16, 4 + 2 log₂ n}`.  Let `x, y : Ω → Σ` be strings.
> Assume `Γ` has a canonical coloring with respect to `x` with a color class `C` of size
> `|C| > m/2` such that the restriction of `Aut_G(x)^ϕ` to `C` is a giant (includes
> `A(C)`).  Then we can find `Iso_G(x,y)` by recursively calling `≤ 6k` instances of String
> Isomorphism with window size `≤ n/k` for some `|C| ≤ k ≤ n`, plus a number of instances
> of total size `≤ n` and maximum size `≤ 2n/3`.
>
> *Proof.*  Since `m ≥ max{9, 2 log₂ n}`, by the Main Structure Theorem (Theorem 10.5.1)
> `Ω` can be divided into standard blocks on which `G` acts as a Johnson group. […]  Let
> `C_x = C`.  By canonicity, there is a corresponding color class `C_y ⊆ Γ` (which may be
> empty).  Apply items 1 to 6 of Procedure Align (Sec. 14.1) with `X(x) := C_x` and
> `X(y) := C_y`. […]  Now we process `Ω(C)` via Cor. 12.0.8.  This can be done because
> `|C| > m/2 ≥ max{8, 2 + log₂ n}`.  Then proceed to the remaining color classes in
> accordance with the Chain Rule.  The bound `2n/3` on the length of the remaining color
> classes comes from Lemma 7.2.1.

The hypotheses are transcribed as follows.  `m ≥ max{16, 4 + 2 log₂ n}` is `Babai.HugeM`;
"`Γ` has a canonical coloring with respect to `x`" is `Babai.IsCanonicalColoring` (the
fragment of Section 6 that the proof uses, see `Workspace/TopAction/Align.lean`), with `C`
the class of the color `c` for `x`; `|C| > m/2` is `m < 2|C|`.

"The restriction of `Aut_G(x)^ϕ` to `C` is a giant (includes `A(C)`)" is `hgiantC`: it asks
that the *restriction map* `(Aut_G(x)^ϕ)_C → S(C)` have image containing `A(C)`, i.e. that
for every `α ∈ A(C)` — written here as an even permutation of `Γ` fixing `Γ ∖ C`
pointwise, which is the same thing — there be a `β ∈ Aut_G(x)^ϕ` with `β|_C = α|_C`.  The
element `β` may move `Γ ∖ C` arbitrarily.  The window-size bounds are stated without
division: `k·|Δ| ≤ n` for the first family, `3·|Δ| ≤ 2n` for the second, and the total size
of the second family is at most `n`.

**The reduction.**  The statement is about the *named* reduction
`Babai.topAction4Reduction`, built from the paper's steps, not about an existentially
quantified one:

* Procedure Align lines 1–3 with `X(z) = C_z`: if `|C_x| ≠ |C_y|` the answer is `∅`
  (`Babai.Align_reject`); otherwise the aligning `σ` of line 2 exists
  (`Babai.exists_alignColorElt`: `A(Γ) ≤ G^ϕ` is transitive on the subsets of a given
  size), `y' = y^{σ⁻¹}` has `C_{y'} = C_x` and `Iso_G(x,y) = Iso_G(x,y')σ`
  (`Babai.Align_shift`), and `Iso_G(x,y') = Iso_{G₁}(x,y')` for the group
  `G₁ = ϕ⁻¹((S(Γ))_C) = G_C` of line 2 (iv) (`Babai.stabOn`).
* Lines 4–6: the coloring `(C, Γ ∖ C)` of `Γ` lifts to the coloring of `Ω` whose classes
  are `Ω_j = {u | |T(u) ∩ C| = j}` (`Babai.omegaCut`), with `Ω_t = Ω(C)`.  The Chain Rule
  starts with `Ω(C)`, which is processed by the window version of Cor. 12.0.8
  (`Babai.Corollary_12_0_8_window` about `Babai.windowTopAction3Reduction`, with the giant
  representation `Babai.phiCFin` of the group induced on the window), and continues over
  `Ω_0, …, Ω_{t−1}`.
* The `2n/3` bound on the remaining classes is Lemma 7.2.1 (a) multiplied by the common
  size of the standard blocks (`Babai.three_mul_ncard_omegaCut_le`), except for the class
  `Ω_0 = Ω(Γ ∖ C)`, whose color vector is exceptional for Lemma 7.2.1 and which is bounded
  instead by `|Γ ∖ C| ≤ m/2` (`Babai.two_mul_ncard_omegaCut_zero_le`).

**How many instances the second family has.**  The paper bounds the second family by its
total size only.  Sec. 15 also needs their number, so the conclusion records
`rest.length ≤ t` — the Chain Rule visits each of the classes `Ω_0, …, Ω_{t−1}` at most
once — and `t ≤ n`, which follows from `4t < m` (Theorem 10.5.1 (a)) together with
`m < 2|C| ≤ 2k ≤ 2n`.  These are extra true clauses; nothing in the paper's conclusion is
dropped. -/
theorem Corollary_12_0_10 (hG : IsTransitive G) (ϕ : G →* Equiv.Perm (Fin m))
    (hϕ : IsGiantRep ϕ) (hm : HugeM m (Nat.card Ω)) (x y : Ω → A)
    (col : (Ω → A) → Fin m → κ) (hcol : IsCanonicalColoring ϕ col) (c : κ)
    (hC : m < 2 * (colorClass col x c).ncard)
    (hgiantC : ∀ α : Equiv.Perm (Fin m), α ∈ alternatingGroup (Fin m) →
      (∀ γ, γ ∉ colorClass col x c → α γ = γ) →
      ∃ β ∈ homImage ϕ (strAut (G : Set (Equiv.Perm Ω)) x),
        ∀ γ ∈ colorClass col x c, β γ = α γ) :
    ∃ (k : ℕ) (main rest : List (SIInstance Ω A)),
      (colorClass col x c).ncard ≤ k ∧ k ≤ Fintype.card Ω ∧
        (topAction4Reduction hG ϕ hϕ (veryLargeK_of_hugeM hG hm) col c x y hC).calls =
          main ++ rest ∧
        main.length ≤ 6 * k ∧
        (∀ I ∈ main, k * I.windowSize ≤ Fintype.card Ω) ∧
        (rest.map SIInstance.windowSize).sum ≤ Fintype.card Ω ∧
        (∀ I ∈ rest, 3 * I.windowSize ≤ 2 * Fintype.card Ω) ∧
        rest.length ≤ tOf hG ϕ ∧ tOf hG ϕ ≤ Fintype.card Ω ∧
        (topAction4Reduction hG ϕ hϕ (veryLargeK_of_hugeM hG hm) col c x y hC).run =
          strIso (G : Set (Equiv.Perm Ω)) x y := by
  classical
  haveI : Nonempty Ω := hG.nonempty
  set hk : VeryLargeK m (maxOrbitLength G) := veryLargeK_of_hugeM hG hm with hkdef
  set C : Set (Fin m) := colorClass col x c with hCdef
  set G₁ : Subgroup (Equiv.Perm Ω) := stabOn ϕ C with hG₁
  set ΩC : Set Ω := omegaOf ϕ C with hΩCdef
  set t : ℕ := tOf hG ϕ with htdef
  have ht : ∀ u : Ω, tPoint ϕ u = t := fun u => tPoint_eq_tOf hG ϕ hϕ hk u
  -- the numeric hypotheses
  have hm16 : 16 ≤ m := by
    have : (16 : ℝ) ≤ (m : ℝ) := le_trans (le_max_left _ _) hm
    exact_mod_cast this
  have hΩCle : ΩC.ncard ≤ Fintype.card Ω := by
    have h1 : ΩC.ncard ≤ (Set.univ : Set Ω).ncard :=
      Set.ncard_le_ncard (Set.subset_univ _) (Set.toFinite _)
    rwa [Set.ncard_univ, Nat.card_eq_fintype_card] at h1
  have hΩCcard : Nat.card (ΩC : Set Ω) = ΩC.ncard := Nat.card_coe_set_eq ΩC
  have hlarge : LargeK C.ncard (Nat.card (ΩC : Set Ω)) := by
    refine (hm.largeK_of_two_mul_lt hC).mono ?_
    rw [hΩCcard, Nat.card_eq_fintype_card]
    exact hΩCle
  have hmaps : MapsOntoGiant (phiCFin hG ϕ hϕ hk C hC) (restrictStr ΩC x) :=
    mapsOntoGiant_phiCFin hG ϕ hϕ hk C hC x hgiantC
  -- the window part of Cor. 12.0.8, with `k` the number of orbits of the kernel
  obtain ⟨hmk, hkn, hlen, hwin, -⟩ :=
    Corollary_12_0_8_window G₁ ΩC (isInvariant_omegaOf_stabOn ϕ hϕ hk C)
      (isTransitive_restrictTo_omegaOf hG ϕ hϕ hk C hC) (phiCFin hG ϕ hϕ hk C hC)
      (isGiantRep_phiCFin hG ϕ hϕ hk C hC) hlarge x
      (strAct y ((alignColorElt ϕ col x y c : G) : Equiv.Perm Ω)⁻¹)
  set k : ℕ := orbCount (phiCFin hG ϕ hϕ hk C hC) with hkk
  set W := windowTopAction3Reduction G₁ ΩC (isInvariant_omegaOf_stabOn ϕ hϕ hk C)
    (phiCFin hG ϕ hϕ hk C hC) x
    (strAct y ((alignColorElt ϕ col x y c : G) : Equiv.Perm Ω)⁻¹) with hWdef
  have hkle : k ≤ Fintype.card Ω := le_trans hkn hΩCle
  -- the number of remaining color classes is `t`, and `4t < m < 2|C| ≤ 2k ≤ 2n`
  have h4t : 4 * t < m := by
    have := (theorem_10_5_1_a ϕ hϕ hk hG.nonempty.some).1.1
    rw [show (Tpoint ϕ hG.nonempty.some).ncard = t from ht _] at this
    exact this
  have htn : t ≤ Fintype.card Ω := by omega
  by_cases hcard : C.ncard = (colorClass col y c).ncard
  · -- the aligned case
    obtain ⟨σ, hσ⟩ := exists_alignColorElt ϕ hϕ (by omega) col x y c hcard
    have hσspec : (ϕ (alignColorElt ϕ col x y c)) '' C = colorClass col y c :=
      alignColorElt_spec ⟨σ, hσ⟩
    set τ : G := alignColorElt ϕ col x y c with hτdef
    set y' : Ω → A := strAct y ((τ : G) : Equiv.Perm Ω)⁻¹ with hy'def
    obtain ⟨hcoly', hshift⟩ := Align_shift hcol x y c τ hσspec
    -- `Iso_G(x,y') = Iso_{G₁}(x,y')`
    have hG₁iso : strIso (G : Set (Equiv.Perm Ω)) x y' =
        strIso ((G₁ : Subgroup (Equiv.Perm Ω)) : Set (Equiv.Perm Ω)) x y' := by
      refine Set.Subset.antisymm (fun ρ hρ => ⟨?_, hρ.2⟩) (fun ρ hρ => ⟨stabOn_le ϕ C hρ.1, hρ.2⟩)
      refine mem_stabOn.2 ⟨hρ.1, ?_⟩
      have h1 := image_colorClass_of_isIso hcol hρ.1 hρ.2 c
      rw [hcoly'] at h1
      exact h1
    obtain ⟨hbodyrun, rest, hbodycalls, hrestΔ, hrestlen, hrestsum⟩ :=
      topAction4Body_spec hG ϕ hϕ hk C hC x y' ht hlarge hmaps
    refine ⟨k, W.calls, rest, hmk, hkle, ?_, hlen, ?_, ?_, ?_, hrestlen, htn, ?_⟩
    · rw [topAction4Reduction, if_pos hcard, SIReduction.calls_bind,
        SIReduction.calls_done, List.append_nil]
      exact hbodycalls
    · intro I hI
      exact le_trans (hwin I hI) hΩCle
    · refine le_trans hrestsum ?_
      exact sum_ncard_omegaCut_le ϕ C ht t (by omega)
    · intro I hI
      obtain ⟨j, hjt, hIj⟩ := hrestΔ I hI
      have hws : I.windowSize = (omegaCut (Ω := Ω) ϕ C j).ncard := by
        rw [SIInstance.windowSize, hIj]
      rcases Nat.eq_zero_or_pos j with rfl | hj1
      · have hcompl : 2 * (Cᶜ : Set (Fin m)).ncard ≤ m := by
          have hsum := Set.ncard_add_ncard_compl C
          rw [Nat.card_eq_fintype_card, Fintype.card_fin] at hsum
          omega
        have h0 := two_mul_ncard_omegaCut_zero_le hG ϕ hϕ hk (by omega) ht
          (by omega) (by omega) C hcompl
        rw [hws]; omega
      · have h3 := three_mul_ncard_omegaCut_le hG ϕ hϕ hk (by omega) ht (by omega) C
          hj1 hjt
        rw [hws]; exact h3
    · rw [topAction4Reduction, if_pos hcard, SIReduction.run_bind,
        SIReduction.run_done, hbodyrun, ← hG₁iso, ← hshift]
  · -- the rejecting case
    refine ⟨k, [], [], hmk, hkle, ?_, by simp, by simp, by simp, by simp, by simp, htn, ?_⟩
    · rw [topAction4Reduction, if_neg hcard, SIReduction.calls_done, List.append_nil]
    · rw [topAction4Reduction, if_neg hcard, SIReduction.run_done]
      symm
      exact Align_reject hcol c hcard

/-! ### What §15, line 4b takes from Cor. 12.0.10

> 4b. else (: `t ≥ 2` :) view `x, y` as edge-colored `t`-uniform hypergraphs `H(x)` and
>     `H(y)` on vertex set `Γ`; if relative symmetry defect of `H(x)` is `< 1/2` then apply
>     Cor. 12.0.10

The Master Algorithm needs two numbers from the corollary: every instance it produces has a
window of size at most `2n/3` (the progress of `Babai.MasterStep.decreases`), and their
number is at most `7n` (`Babai.MasterStep.calls_length_le`). -/

/-- §15, line 4b: **every call of Cor. 12.0.10 has a window of size at most `2n/3`**, which
is the progress `Babai.MasterStep.decreases` asks for.

*Proof.*  By Cor. 12.0.10 the calls are `main ++ rest`.  A call of `rest` satisfies
`3n' ≤ 2n` by the corollary.  A call of `main` satisfies `k · n' ≤ n` where `k ≥ |C|` and
`m < 2|C|`, and `m ≥ 16` by `HugeM`, so `k ≥ 9` and therefore `3n' ≤ 3n/9 ≤ 2n`. -/
theorem decreases_topAction4Reduction (hG : IsTransitive G) (ϕ : G →* Equiv.Perm (Fin m))
    (hϕ : IsGiantRep ϕ) (hm : HugeM m (Nat.card Ω)) (x y : Ω → A)
    (col : (Ω → A) → Fin m → κ) (hcol : IsCanonicalColoring ϕ col) (c : κ)
    (hC : m < 2 * (colorClass col x c).ncard)
    (hgiantC : ∀ α : Equiv.Perm (Fin m), α ∈ alternatingGroup (Fin m) →
      (∀ γ, γ ∉ colorClass col x c → α γ = γ) →
      ∃ β ∈ homImage ϕ (strAut (G : Set (Equiv.Perm Ω)) x),
        ∀ γ ∈ colorClass col x c, β γ = α γ) :
    ∀ I ∈ (topAction4Reduction hG ϕ hϕ (veryLargeK_of_hugeM hG hm) col c x y hC).calls,
      3 * I.windowSize ≤ 2 * Fintype.card Ω := by
  obtain ⟨k, main, rest, hCk, hkn, hsplit, -, hmain, -, hrest, -, -, -⟩ :=
    Corollary_12_0_10 hG ϕ hϕ hm x y col hcol c hC hgiantC
  have hm16 : 16 ≤ m := by
    have : (16 : ℝ) ≤ (m : ℝ) := le_trans (le_max_left _ _) hm
    exact_mod_cast this
  have hk3 : 3 ≤ k := by omega
  intro I hI
  rw [hsplit] at hI
  rcases List.mem_append.1 hI with h | h
  · have := hmain I h
    nlinarith [this, hk3, Nat.zero_le I.windowSize]
  · exact hrest I h

/-- §15, line 4b: **every call of Cor. 12.0.10 has its candidate set inside `G`**, which is
what lets the branch be read on a window of a larger instance. -/
theorem calls_topAction4Reduction_K (hG : IsTransitive G) (ϕ : G →* Equiv.Perm (Fin m))
    (hϕ : IsGiantRep ϕ) (hk : VeryLargeK m (maxOrbitLength G))
    (col : (Ω → A) → Fin m → κ) (c : κ) (x y : Ω → A)
    (hC : m < 2 * (colorClass col x c).ncard) :
    ∀ J ∈ (topAction4Reduction hG ϕ hϕ hk col c x y hC).calls,
      J.K ⊆ (G : Set (Equiv.Perm Ω)) := by
  classical
  rw [topAction4Reduction]
  by_cases hcard : (colorClass col x c).ncard = (colorClass col y c).ncard
  · rw [if_pos hcard, SIReduction.calls_bind, SIReduction.calls_done, List.append_nil]
    exact calls_topAction4Body_K hG ϕ hϕ hk _ hC x _ (tOf hG ϕ)
  · rw [if_neg hcard, SIReduction.calls_done]
    intro J hJ
    simp at hJ

/-- §15, line 4b: **the number of calls of Cor. 12.0.10 is at most `7n`**.

Cor. 12.0.10 splits the calls into `main` (the window version of Cor. 12.0.8 on `Ω(C)`, at
most `6k ≤ 6n` calls) and `rest` (the Chain Rule over the classes `Ω_0, …, Ω_{t−1}`, so at
most `t ≤ n` calls). -/
theorem calls_length_topAction4Reduction (hG : IsTransitive G) (ϕ : G →* Equiv.Perm (Fin m))
    (hϕ : IsGiantRep ϕ) (hm : HugeM m (Nat.card Ω)) (x y : Ω → A)
    (col : (Ω → A) → Fin m → κ) (hcol : IsCanonicalColoring ϕ col) (c : κ)
    (hC : m < 2 * (colorClass col x c).ncard)
    (hgiantC : ∀ α : Equiv.Perm (Fin m), α ∈ alternatingGroup (Fin m) →
      (∀ γ, γ ∉ colorClass col x c → α γ = γ) →
      ∃ β ∈ homImage ϕ (strAut (G : Set (Equiv.Perm Ω)) x),
        ∀ γ ∈ colorClass col x c, β γ = α γ) :
    ((topAction4Reduction hG ϕ hϕ (veryLargeK_of_hugeM hG hm) col c x y hC).calls).length ≤
      7 * Fintype.card Ω := by
  obtain ⟨k, main, rest, -, hkn, hsplit, hmainlen, -, -, -, hrestlen, htn, -⟩ :=
    Corollary_12_0_10 hG ϕ hϕ hm x y col hcol c hC hgiantC
  rw [hsplit, List.length_append]
  omega

end TopAction4


/-! ### Remark 12.0.11

> The cost of this procedure can generously be overestimated by `6T(2n/3)` where `T(n)` is
> the maximum cost of instances of size `≤ n`.

This is not a precise mathematical claim, so it has no formal statement.  It names no
hypothesis on `T` and no accounting of the procedure's own work, and under the literal
reading it is false: if every instance costs its size, `T(n) = n`, then the `≤ 6k` calls of
window `n/k` in Cor. 12.0.10 may cost `6n` in all, more than `6T(2n/3) = 4n`.  It does
hold for rapidly growing `T` (for instance when `k·T(n/k) ≤ T(2n/3)/2` and
`T(a) + T(b) ≤ T(a + b)`), which is the regime the word "generously" points to; see the
the corrected paper Remark 12.0.11.  The call accounting it summarizes is the
conclusion of `Babai.Corollary_12_0_10` (`≤ 6k` calls of window `≤ n/k`, plus calls of
window `≤ 2n/3` of total size `≤ n`); the RAM round is `Algo.top4Round` with the cost
record `Algo.top4RunCostQ` (`Workspace/Algo/TopFourRound.lean`,
`Workspace/Algo/TopFourCost.lean`).  Nothing later in the paper uses the remark. -/

end Babai
