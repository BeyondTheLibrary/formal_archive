/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 2 facts that Section 10 needs and that `Workspace/Prelim/` does not provide,
together with the textbook background on `A_k` that Section 10 uses without comment and
that Mathlib does not have.
-/
import Workspace.Prelim.PermGroups
import Workspace.Prelim.AlternatingIndex
import Workspace.Prelim.SmallGroups
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Transfer
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.Tactic.NormNum.Prime

/-!
# Helpers for Section 10

Two kinds of material:

* small Section 2 conveniences (the pointwise stabilizer viewed inside `G`, the length of
  the largest orbit), which belong to `Workspace/Prelim/PermGroups.lean` but are added
  here so that the Prelim files stay untouched;
* textbook background about the alternating group that the paper uses as common
  knowledge, inside proofs, without a citation.  Since the paper does **not** cite these to
  the literature, they are not `axiom`s: they are proved.  The proofs live under
  `Workspace/Prelim/`, so that they come before `AltQuotients/SmallIndex.lean` in the
  import graph:
  the simplicity of `A(Ω)` for `|Ω| ≥ 5` in `Prelim/AlternatingSimple.lean`, the index
  bound "for `k ≥ 5` the largest proper subgroup of `A_k` has index `k`, and the largest
  subgroup of `S_k` not containing `A_k` also has index `k`" (proof of Cor. 10.3.7) in
  `Prelim/AlternatingIndex.lean`, and the solvability of `S_4` (base case of
  Prop. 10.2.3) in `Prelim/SmallGroups.lean`.  The last of them, "the smallest nonabelian
  simple group is `A_5`" (`sixty_le_card_of_nonabelian_simple`), is proved in this file.
-/

namespace Babai

open MulAction Equiv Equiv.Perm

variable {Ω : Type*}

/-! ### Factoring a homomorphism across a quotient

Lemma 10.2.5, Lemma 10.3.3 and Theorem 10.3.5 all use the same step: an epimorphism
`ρ : G → P` whose kernel lies in `ker ϕ` makes `ϕ` factor as `G → P → S_k`. -/

/-- If `ρ` is onto and `ker ρ ≤ ker ϕ` then `ϕ` factors across `ρ`. -/
theorem exists_factor_of_ker_le {A B C : Type*} [Group A] [Group B] [Group C] {ρ : A →* B}
    (hρ : Function.Surjective ρ) (ϕ : A →* C) (h : ρ.ker ≤ ϕ.ker) :
    ∃ ψ : B →* C, ψ.comp ρ = ϕ := by
  refine ⟨(QuotientGroup.lift ρ.ker ϕ h).comp
    (QuotientGroup.quotientKerEquivOfSurjective ρ hρ).symm.toMonoidHom,
    MonoidHom.ext fun g => ?_⟩
  show (QuotientGroup.lift ρ.ker ϕ h)
    ((QuotientGroup.quotientKerEquivOfSurjective ρ hρ).symm (ρ g)) = ϕ g
  rw [show (QuotientGroup.quotientKerEquivOfSurjective ρ hρ).symm (ρ g)
      = (QuotientGroup.mk g : A ⧸ ρ.ker) from by rw [MulEquiv.symm_apply_eq]; rfl]
  rfl

/-- A factorization `ψ ∘ ρ = ϕ` with `ρ` onto has `ψ^{range} = ϕ^{range}`. -/
theorem range_of_factor {A B C : Type*} [Group A] [Group B] [Group C] {ρ : A →* B}
    (hρ : Function.Surjective ρ) {ϕ : A →* C} {ψ : B →* C} (hψ : ψ.comp ρ = ϕ) :
    ψ.range = ϕ.range := by
  ext c
  constructor
  · rintro ⟨b, rfl⟩
    obtain ⟨a, rfl⟩ := hρ b
    exact ⟨a, by rw [← hψ]; rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨ρ a, by rw [← hψ]; rfl⟩

/-! ### The pointwise stabilizer inside `G` -/

/-- The pointwise stabilizer `G_(D)` of `D ⊆ Ω` (Eq. (12)), as a subgroup of `G` rather
than of `S(Ω)`.  This is the form needed to apply a homomorphism `ϕ : G → S_k` to it. -/
def pointwiseStab (G : Subgroup (Equiv.Perm Ω)) (D : Set Ω) : Subgroup G :=
  (pointwiseStabilizer G D).subgroupOf G

@[simp] theorem mem_pointwiseStab {G : Subgroup (Equiv.Perm Ω)} {D : Set Ω} {σ : G} :
    σ ∈ pointwiseStab G D ↔ ∀ x ∈ D, (σ : Equiv.Perm Ω) x = x := by
  simp [pointwiseStab, Subgroup.mem_subgroupOf, σ.2]

/-- `G_(D)` is normal in `G` when `D` is `G`-invariant: it is the kernel of the
restriction `G → S(D)`. -/
theorem pointwiseStab_normal {G : Subgroup (Equiv.Perm Ω)} {D : Set Ω}
    (hD : IsInvariant G D) : (pointwiseStab G D).Normal := by
  constructor
  intro σ hσ τ
  rw [mem_pointwiseStab] at hσ ⊢
  intro x hx
  have key := (isInvariant_iff_mem G D).1 hD (τ : Equiv.Perm Ω) τ.2 (((τ : Equiv.Perm Ω)⁻¹) x)
  have hx' : ((τ : Equiv.Perm Ω)⁻¹) x ∈ D := key.2 (by simpa using hx)
  have h1 := hσ _ hx'
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, Equiv.Perm.mul_apply]
  rw [h1]
  simp

/-- The setwise stabilizer `G_B` of `B ⊆ Ω` (Eq. (11)), as a subgroup of `G`. -/
def setwiseStab (G : Subgroup (Equiv.Perm Ω)) (B : Set Ω) : Subgroup G :=
  (setwiseStabilizer G B).subgroupOf G

@[simp] theorem mem_setwiseStab {G : Subgroup (Equiv.Perm Ω)} {B : Set Ω} {σ : G} :
    σ ∈ setwiseStab G B ↔ (σ : Equiv.Perm Ω) '' B = B := by
  simp [setwiseStab, Subgroup.mem_subgroupOf, σ.2]

/-! ### The length of the largest orbit, `n₀` -/

/-- `n₀(G)`, "the length (size) of the largest orbit of `G`" (Sec. 10, opening
paragraph).  For `Ω = ∅` there are no orbits and the supremum is `0`. -/
noncomputable def maxOrbitLength (G : Subgroup (Equiv.Perm Ω)) : ℕ :=
  sSup {m | ∃ x : Ω, Nat.card (orbit G x) = m}

theorem bddAbove_orbitLengths [Finite Ω] (G : Subgroup (Equiv.Perm Ω)) :
    BddAbove {m | ∃ x : Ω, Nat.card (orbit G x) = m} := by
  refine ⟨Nat.card Ω, ?_⟩
  rintro m ⟨x, rfl⟩
  exact Nat.card_le_card_of_injective _ Subtype.val_injective

/-- Every orbit has length at most `n₀(G)`. -/
theorem card_orbit_le_maxOrbitLength [Finite Ω] (G : Subgroup (Equiv.Perm Ω)) (x : Ω) :
    Nat.card (orbit G x) ≤ maxOrbitLength G :=
  le_csSup (bddAbove_orbitLengths G) ⟨x, rfl⟩

/-! ### Conjugation and the alternating group -/

/-- Conjugation fixes the alternating group. -/
theorem map_conj_alternatingGroup [Fintype Ω] [DecidableEq Ω] (c : Equiv.Perm Ω) :
    (alternatingGroup Ω).map (MulAut.conj c).toMonoidHom = alternatingGroup Ω := by
  ext g
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact (alternatingGroup Ω).normal_of_characteristic.conj_mem a ha c
  · intro hg
    refine ⟨c⁻¹ * g * c, ?_, ?_⟩
    · have := (alternatingGroup Ω).normal_of_characteristic.conj_mem g hg c⁻¹
      simpa [MulAut.conj, mul_assoc] using this
    · simp [MulAut.conj, mul_assoc]

/-- `A(Ω) ≤ H` is invariant under conjugating `H`. -/
theorem alternating_le_map_conj_iff [Fintype Ω] [DecidableEq Ω] (c : Equiv.Perm Ω)
    (H : Subgroup (Equiv.Perm Ω)) :
    alternatingGroup Ω ≤ H.map (MulAut.conj c).toMonoidHom ↔ alternatingGroup Ω ≤ H := by
  have hinj : Function.Injective (MulAut.conj c⁻¹ : Equiv.Perm Ω ≃* Equiv.Perm Ω) :=
    (MulAut.conj c⁻¹).injective
  have hmap : (H.map (MulAut.conj c).toMonoidHom).map (MulAut.conj c⁻¹).toMonoidHom = H := by
    rw [Subgroup.map_map]
    convert Subgroup.map_id H using 2
    ext x
    simp [MulAut.conj, mul_assoc]
  constructor
  · intro h
    have := Subgroup.map_mono (f := (MulAut.conj c⁻¹).toMonoidHom) h
    rwa [map_conj_alternatingGroup, hmap] at this
  · intro h
    have := Subgroup.map_mono (f := (MulAut.conj c).toMonoidHom) h
    rwa [map_conj_alternatingGroup] at this

/-- `(Hᵍ)^f = (H^f)^{f g}`. -/
theorem map_map_conj {A B : Type*} [Group A] [Group B] (f : A →* B) (H : Subgroup A) (g : A) :
    (H.map (MulAut.conj g).toMonoidHom).map f
      = (H.map f).map (MulAut.conj (f g)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj, map_mul, map_inv]

/-- Every orbit is no longer than `m` gives `n₀(G) ≤ m`. -/
theorem maxOrbitLength_le [Finite Ω] {G : Subgroup (Equiv.Perm Ω)} {m : ℕ}
    (h : ∀ x : Ω, Nat.card (orbit G x) ≤ m) : maxOrbitLength G ≤ m := by
  rcases isEmpty_or_nonempty Ω with hΩ | hΩ
  · have : {n | ∃ x : Ω, Nat.card (orbit G x) = n} = ∅ := by
      ext n; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨x, -⟩
      exact hΩ.false x
    rw [maxOrbitLength, this]
    simp
  · refine csSup_le ⟨Nat.card (orbit G (Classical.arbitrary Ω)), ⟨_, rfl⟩⟩ ?_
    rintro n ⟨x, rfl⟩
    exact h x

/-- A subgroup has no longer orbits. -/
theorem maxOrbitLength_mono [Finite Ω] {G₁ G : Subgroup (Equiv.Perm Ω)} (h : G₁ ≤ G) :
    maxOrbitLength G₁ ≤ maxOrbitLength G := by
  refine maxOrbitLength_le fun x => ?_
  have hsub : orbit G₁ x ⊆ orbit G x := by
    rintro y hy
    obtain ⟨g, rfl⟩ := mem_orbit_iff.1 hy
    exact mem_orbit_iff.2 ⟨⟨(g : Equiv.Perm Ω), h g.2⟩, rfl⟩
  exact le_trans (Nat.card_le_card_of_injective _ (Set.inclusion_injective hsub))
    (card_orbit_le_maxOrbitLength G x)

/-! ### Background on the alternating group

The paper uses the following two facts as common knowledge, without citation.  They are
not in Mathlib (which proves only `IsSimpleGroup (alternatingGroup (Fin 5))`). -/

/-! `Babai.isSimpleGroup_alternatingGroup` (the simplicity of `A(Ω)` for `|Ω| ≥ 5`) is
proved in `Workspace/Prelim/AlternatingSimple.lean`. -/

/-- `A(Ω)` is nonabelian for `|Ω| ≥ 5`: the two even permutations `(x₀x₁)(x₂x₃)` and
`(x₀x₁)(x₂x₄)` do not commute. -/
theorem alternatingGroup_nonabelian [Fintype Ω] [DecidableEq Ω]
    (h5 : 5 ≤ Fintype.card Ω) :
    ¬ ∀ a b : alternatingGroup Ω, a * b = b * a := by
  obtain ⟨e⟩ : Nonempty (Fin 5 ↪ Ω) :=
    Function.Embedding.nonempty_iff_card_le.2 (by simpa using h5)
  set x : Fin 5 → Ω := fun i => e i with hx
  have hne : ∀ i j : Fin 5, i ≠ j → x i ≠ x j := fun i j hij h => hij (e.injective h)
  set σ : Equiv.Perm Ω := swap (x 0) (x 1) * swap (x 2) (x 3) with hσ
  set τ : Equiv.Perm Ω := swap (x 0) (x 1) * swap (x 2) (x 4) with hτ
  have hσA : σ ∈ alternatingGroup Ω :=
    mul_mem_alternatingGroup_of_isSwap ⟨x 0, x 1, hne 0 1 (by decide), rfl⟩
      ⟨x 2, x 3, hne 2 3 (by decide), rfl⟩
  have hτA : τ ∈ alternatingGroup Ω :=
    mul_mem_alternatingGroup_of_isSwap ⟨x 0, x 1, hne 0 1 (by decide), rfl⟩
      ⟨x 2, x 4, hne 2 4 (by decide), rfl⟩
  intro hcomm
  have h := congrArg (fun p : alternatingGroup Ω => (p : Equiv.Perm Ω) (x 2))
    (hcomm ⟨σ, hσA⟩ ⟨τ, hτA⟩)
  simp only [Subgroup.coe_mul, Equiv.Perm.mul_apply, hσ, hτ] at h
  rw [swap_apply_left, swap_apply_of_ne_of_ne (hne 4 0 (by decide)) (hne 4 1 (by decide)),
    swap_apply_of_ne_of_ne (hne 4 2 (by decide)) (hne 4 3 (by decide)),
    swap_apply_of_ne_of_ne (hne 4 0 (by decide)) (hne 4 1 (by decide))] at h
  rw [swap_apply_left, swap_apply_of_ne_of_ne (hne 3 0 (by decide)) (hne 3 1 (by decide)),
    swap_apply_of_ne_of_ne (hne 3 2 (by decide)) (hne 3 4 (by decide)),
    swap_apply_of_ne_of_ne (hne 3 0 (by decide)) (hne 3 1 (by decide))] at h
  exact hne 4 3 (by decide) h

/-! `Babai.card_le_relIndex_of_not_alternating_le` (for `k ≥ 5` a subgroup of `S_k` that
does not contain `A_k` has index at least `k`, the fact used in the proof of Cor. 10.3.7)
is proved in `Workspace/Prelim/AlternatingIndex.lean`. -/

/-! ### The smallest nonabelian simple group

The paper uses, in the proof of Prop. 10.2.3, the elementary fact that a nonabelian finite
simple group has order at least `60`.  Mathlib has Sylow theory, Burnside's normal
`p`-complement theorem and the simplicity of `A_5`, but not this classification statement,
so it is proved here.

The proof follows the textbook route.  Let `R` be a nonabelian finite simple group and let
`n = |R| < 60`.

* `n` is not a prime power: a `p`-group has a nontrivial center, which is normal, so by
  simplicity the center is everything and `R` is abelian.
* If `H < R` is a proper subgroup of index `m`, the action of `R` on the cosets `R/H` has
  kernel the normal core of `H`, which is normal and inside `H`, hence trivial; so `R`
  embeds in `S_m` and `n ∣ m!`.  Applied to a Sylow `p`-subgroup, whose index is
  `m = n / p^a`, this rules out every non-prime-power `n < 60` except `30`, `40` and `56`.
* `n = 30`: the Sylow `2`-subgroup has order `2`, hence is cyclic, and `2` is the smallest
  prime divisor, so Burnside's normal `p`-complement theorem gives a normal subgroup of
  order `15`.
* `n = 40`: the number of Sylow `5`-subgroups divides `8` and is `≡ 1 mod 5`, so it is `1`
  and the Sylow `5`-subgroup is normal.
* `n = 56`: the number of Sylow `7`-subgroups divides `8` and is `≡ 1 mod 7`, and it is not
  `1`, so it is `8`; then the normalizer of a Sylow `7`-subgroup `P` has order `7`, so it
  equals `P`, which is abelian, so `N(P) ≤ C(P)` and Burnside's theorem gives a normal
  subgroup of order `8`. -/

section SmallestSimple

variable {R : Type*} [Group R] [Finite R] [IsSimpleGroup R]

/-- A nonabelian simple group is not a `p`-group: the center of a `p`-group is nontrivial
and normal, so by simplicity it is the whole group. -/
theorem card_ne_prime_pow_of_nonabelian_simple (hR : ¬ ∀ a b : R, a * b = b * a)
    {p a : ℕ} (hp : p.Prime) : Nat.card R ≠ p ^ a := by
  intro hcard
  haveI : Fact p.Prime := ⟨hp⟩
  have hpg : IsPGroup p R := IsPGroup.of_card hcard
  have hnt : Nontrivial (Subgroup.center R) := hpg.center_nontrivial
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center R) inferInstance with h | h
  · have h1 : 1 < Nat.card (Subgroup.center R) := Finite.one_lt_card_iff_nontrivial.2 hnt
    rw [h, Subgroup.card_bot] at h1
    omega
  · refine hR fun x y => ?_
    have hx : x ∈ Subgroup.center R := by rw [h]; trivial
    exact ((Subgroup.mem_center_iff).1 hx y).symm

/-- The order of a simple group divides `m!`, where `m` is the index of any proper
subgroup: the action on the cosets is faithful because its kernel is the normal core. -/
theorem card_dvd_index_factorial_of_simple {H : Subgroup R} (hH : H ≠ ⊤) :
    Nat.card R ∣ Nat.factorial H.index := by
  classical
  haveI := Fintype.ofFinite (R ⧸ H)
  have hker : (MulAction.toPermHom R (R ⧸ H)).ker = ⊥ := by
    rw [← Subgroup.normalCore_eq_ker]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal H.normalCore inferInstance with h | h
    · exact h
    · exact absurd (top_le_iff.1 (h ▸ H.normalCore_le)) hH
  have hinj : Function.Injective (MulAction.toPermHom R (R ⧸ H)) :=
    (MonoidHom.ker_eq_bot_iff _).1 hker
  have hdvd := Subgroup.card_dvd_of_injective _ hinj
  have hperm : Nat.card (Equiv.Perm (R ⧸ H)) = Nat.factorial H.index := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, ← Nat.card_eq_fintype_card]
    rfl
  rwa [hperm] at hdvd

/-- The Sylow `p`-subgroup of a group of order `n` with `p^a ∥ n` has order `p^a`. -/
theorem card_sylow_subgroup_eq {p a : ℕ} (hp : p.Prime) (hdvd : p ^ a ∣ Nat.card R)
    (hnd : ¬ p ∣ (Nat.card R / p ^ a)) (P : Sylow p R) : Nat.card P = p ^ a := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hn0 : Nat.card R ≠ 0 := Nat.card_pos.ne'
  have hfa : (Nat.card R).factorization p = a := by
    have hle : a ≤ (Nat.card R).factorization p :=
      (Nat.Prime.pow_dvd_iff_le_factorization hp hn0).1 hdvd
    by_contra hne
    have hlt : a + 1 ≤ (Nat.card R).factorization p := by omega
    obtain ⟨c, hc⟩ := (Nat.Prime.pow_dvd_iff_le_factorization hp hn0).2 hlt
    refine hnd ⟨c, ?_⟩
    have hrw : Nat.card R = p ^ a * (p * c) := by rw [hc, pow_succ]; ring
    rw [hrw, Nat.mul_div_cancel_left _ (pow_pos hp.pos a)]
  rw [Sylow.card_eq_multiplicity, hfa]

/-- The main step: for a nonabelian simple group `R` of order `n` and a prime power
`p^a ∥ n`, the order `n` divides `(n / p^a)!`. -/
theorem card_dvd_factorial_div (hR : ¬ ∀ a b : R, a * b = b * a) {p a : ℕ} (hp : p.Prime)
    (hdvd : p ^ a ∣ Nat.card R) (hnd : ¬ p ∣ (Nat.card R / p ^ a)) :
    Nat.card R ∣ Nat.factorial (Nat.card R / p ^ a) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨P⟩ : Nonempty (Sylow p R) := Sylow.nonempty
  have hcardP : Nat.card P = p ^ a := card_sylow_subgroup_eq hp hdvd hnd P
  have hindex : (P : Subgroup R).index = Nat.card R / p ^ a := by
    have hmul := Subgroup.index_mul_card (P : Subgroup R)
    rw [hcardP] at hmul
    rw [← hmul, Nat.mul_div_cancel _ (pow_pos hp.pos a)]
  have hne : (P : Subgroup R) ≠ ⊤ := by
    intro h
    refine card_ne_prime_pow_of_nonabelian_simple hR hp (a := a) ?_
    rw [← hcardP, h, Subgroup.card_top]
  rw [← hindex]
  exact card_dvd_index_factorial_of_simple hne

/-- In a nonabelian simple group the number of Sylow `p`-subgroups is not `1`, for every
prime `p` dividing the order: a unique Sylow subgroup is normal. -/
theorem card_sylow_ne_one (hR : ¬ ∀ a b : R, a * b = b * a) {p : ℕ} (hp : p.Prime)
    (hdvd : p ∣ Nat.card R) : Nat.card (Sylow p R) ≠ 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro h1
  obtain ⟨P⟩ : Nonempty (Sylow p R) := Sylow.nonempty
  haveI : Subsingleton (Sylow p R) := (Nat.card_eq_one_iff_unique.1 h1).1
  have hnormal : (P : Subgroup R).Normal := P.normal_of_subsingleton
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (P : Subgroup R) hnormal with h | h
  · exact P.ne_bot_of_dvd_card hdvd h
  · refine card_ne_prime_pow_of_nonabelian_simple hR hp
      (a := (Nat.card R).factorization p) ?_
    rw [← Sylow.card_eq_multiplicity P, h, Subgroup.card_top]

/-- A normal complement to a Sylow subgroup contradicts simplicity: the complement is
normal, and neither trivial nor everything. -/
theorem no_normal_complement (hR : ¬ ∀ a b : R, a * b = b * a) {p : ℕ} (hp : p.Prime)
    {K P : Subgroup R} (hK : K.Normal) (hcompl : K.IsComplement' P)
    (hPcard : Nat.card P = p) (hRcard : p < Nat.card R) : False := by
  have hmul := hcompl.card_mul
  rw [hPcard] at hmul
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal K hK with h | h
  · rw [h, Subgroup.card_bot, one_mul] at hmul
    omega
  · rw [h, Subgroup.card_top] at hmul
    have hp1 : 1 < p := hp.one_lt
    have hpos : 0 < Nat.card R := Nat.card_pos
    nlinarith

/-- Background, used in the proof of Prop. 10.2.3: "We use the elementary fact that the
smallest nonabelian simple group is `A_5`", i.e. a nonabelian finite simple group has
order at least `|A_5| = 60`. -/
theorem sixty_le_card_of_nonabelian_simple (R : Type*) [Group R] [Finite R]
    [IsSimpleGroup R] (hR : ¬ ∀ a b : R, a * b = b * a) : 60 ≤ Nat.card R := by
  by_contra hlt
  push_neg at hlt
  -- the two workhorses, stated for the order of `R`
  have hpp : ∀ p a : ℕ, p.Prime → Nat.card R ≠ p ^ a := fun p a hp =>
    card_ne_prime_pow_of_nonabelian_simple hR hp
  have hkill : ∀ p a : ℕ, p.Prime → p ^ a ∣ Nat.card R → ¬ p ∣ (Nat.card R / p ^ a) →
      Nat.card R ∣ Nat.factorial (Nat.card R / p ^ a) := fun p a hp =>
    card_dvd_factorial_div hR hp
  have h2 : 2 ≤ Nat.card R := by
    haveI : Nontrivial R := IsSimpleGroup.toNontrivial
    exact Finite.one_lt_card_iff_nontrivial.2 inferInstance
  -- the three orders that the index bound does not rule out
  have h30 : Nat.card R ≠ 30 := by
    intro hn
    haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
    obtain ⟨P⟩ : Nonempty (Sylow 2 R) := Sylow.nonempty
    have hcardP : Nat.card P = 2 ^ 1 :=
      card_sylow_subgroup_eq (by norm_num) (by rw [hn]; norm_num)
        (by rw [hn]; norm_num) P
    haveI hcyc : IsCyclic P := isCyclic_of_prime_card (p := 2) (by simpa using hcardP)
    have hmin : (Nat.card R).minFac = 2 := by rw [hn]; norm_num
    have hcompl := IsCyclic.isComplement' hmin hcyc
    refine no_normal_complement hR (p := 2) (by norm_num) inferInstance hcompl
      (by simpa using hcardP) (by omega)
  have h40 : Nat.card R ≠ 40 := by
    intro hn
    haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    obtain ⟨P⟩ : Nonempty (Sylow 5 R) := Sylow.nonempty
    have hcardP : Nat.card P = 5 ^ 1 :=
      card_sylow_subgroup_eq (by norm_num) (by rw [hn]; norm_num)
        (by rw [hn]; norm_num) P
    have hindex : (P : Subgroup R).index = 8 := by
      have hmul := Subgroup.index_mul_card (P : Subgroup R)
      rw [hcardP, hn] at hmul
      omega
    have hdvd8 : Nat.card (Sylow 5 R) ∣ 8 := by
      have := P.card_dvd_index
      rwa [hindex] at this
    have hmod := card_sylow_modEq_one 5 R
    have hne1 : Nat.card (Sylow 5 R) ≠ 1 :=
      card_sylow_ne_one hR (by norm_num) (by rw [hn]; norm_num)
    have hle : Nat.card (Sylow 5 R) ≤ 8 := Nat.le_of_dvd (by norm_num) hdvd8
    interval_cases hc : (Nat.card (Sylow 5 R)) <;>
      revert hdvd8 hmod hne1 <;> decide
  have h56 : Nat.card R ≠ 56 := by
    intro hn
    haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    obtain ⟨P⟩ : Nonempty (Sylow 7 R) := Sylow.nonempty
    have hcardP : Nat.card P = 7 ^ 1 :=
      card_sylow_subgroup_eq (by norm_num) (by rw [hn]; norm_num)
        (by rw [hn]; norm_num) P
    have hcardP' : Nat.card P = 7 := by simpa using hcardP
    have hindex : (P : Subgroup R).index = 8 := by
      have hmul := Subgroup.index_mul_card (P : Subgroup R)
      rw [hcardP, hn] at hmul
      omega
    have hdvd8 : Nat.card (Sylow 7 R) ∣ 8 := by
      have := P.card_dvd_index
      rwa [hindex] at this
    have hmod := card_sylow_modEq_one 7 R
    have hne1 : Nat.card (Sylow 7 R) ≠ 1 :=
      card_sylow_ne_one hR (by norm_num) (by rw [hn]; norm_num)
    have hle : Nat.card (Sylow 7 R) ≤ 8 := Nat.le_of_dvd (by norm_num) hdvd8
    -- the number of Sylow `7`-subgroups is `8`
    have hcount : Nat.card (Sylow 7 R) = 8 := by
      interval_cases hc : (Nat.card (Sylow 7 R)) <;>
        revert hdvd8 hmod hne1 <;> decide
    -- hence the normalizer of `P` has order `7`, so it is `P` itself
    have hnormindex : (Subgroup.normalizer (P : Set R)).index = 8 := by
      have := P.card_eq_index_normalizer
      rw [hcount] at this
      exact this.symm
    have hnormcard : Nat.card (Subgroup.normalizer (P : Set R)) = 7 := by
      have hmul := Subgroup.index_mul_card (Subgroup.normalizer (P : Set R))
      rw [hnormindex, hn] at hmul
      omega
    have hPN : (P : Subgroup R) = Subgroup.normalizer (P : Set R) :=
      Subgroup.eq_of_le_of_card_ge Subgroup.le_normalizer (by rw [hnormcard, hcardP'])
    haveI hcyc : IsCyclic P := isCyclic_of_prime_card (p := 7) hcardP'
    haveI : IsMulCommutative (P : Subgroup R) :=
      ⟨⟨fun a b => hcyc.commGroup.mul_comm a b⟩⟩
    have hPC : Subgroup.normalizer (P : Set R) ≤ Subgroup.centralizer (P : Set R) := by
      rw [← hPN]
      exact Subgroup.le_centralizer (H := (P : Subgroup R))
    have hcompl := MonoidHom.ker_transferSylow_isComplement' P hPC
    refine no_normal_complement hR (p := 7) (by norm_num) inferInstance hcompl hcardP'
      (by omega)
  -- every other order below `60` is ruled out by the index bound or is a prime power
  obtain ⟨n, hn⟩ : ∃ n, Nat.card R = n := ⟨_, rfl⟩
  rw [hn] at hpp hkill hlt h2 h30 h40 h56
  have p2 : Nat.Prime 2 := by norm_num
  have p3 : Nat.Prime 3 := by norm_num
  have p5 : Nat.Prime 5 := by norm_num
  have p7 : Nat.Prime 7 := by norm_num
  have p11 : Nat.Prime 11 := by norm_num
  have p13 : Nat.Prime 13 := by norm_num
  have p17 : Nat.Prime 17 := by norm_num
  have p19 : Nat.Prime 19 := by norm_num
  have p23 : Nat.Prime 23 := by norm_num
  have p29 : Nat.Prime 29 := by norm_num
  have p31 : Nat.Prime 31 := by norm_num
  have p37 : Nat.Prime 37 := by norm_num
  have p41 : Nat.Prime 41 := by norm_num
  have p43 : Nat.Prime 43 := by norm_num
  have p47 : Nat.Prime 47 := by norm_num
  have p53 : Nat.Prime 53 := by norm_num
  have p59 : Nat.Prime 59 := by norm_num
  interval_cases n
  all_goals first
    | (refine hpp 2 1 p2 ?_ <;> decide)
    | (refine hpp 3 1 p3 ?_ <;> decide)
    | (refine hpp 2 2 p2 ?_ <;> decide)
    | (refine hpp 5 1 p5 ?_ <;> decide)
    | (refine hpp 7 1 p7 ?_ <;> decide)
    | (refine hpp 2 3 p2 ?_ <;> decide)
    | (refine hpp 3 2 p3 ?_ <;> decide)
    | (refine hpp 11 1 p11 ?_ <;> decide)
    | (refine hpp 13 1 p13 ?_ <;> decide)
    | (refine hpp 2 4 p2 ?_ <;> decide)
    | (refine hpp 17 1 p17 ?_ <;> decide)
    | (refine hpp 19 1 p19 ?_ <;> decide)
    | (refine hpp 23 1 p23 ?_ <;> decide)
    | (refine hpp 5 2 p5 ?_ <;> decide)
    | (refine hpp 3 3 p3 ?_ <;> decide)
    | (refine hpp 29 1 p29 ?_ <;> decide)
    | (refine hpp 31 1 p31 ?_ <;> decide)
    | (refine hpp 2 5 p2 ?_ <;> decide)
    | (refine hpp 37 1 p37 ?_ <;> decide)
    | (refine hpp 41 1 p41 ?_ <;> decide)
    | (refine hpp 43 1 p43 ?_ <;> decide)
    | (refine hpp 47 1 p47 ?_ <;> decide)
    | (refine hpp 7 2 p7 ?_ <;> decide)
    | (refine hpp 53 1 p53 ?_ <;> decide)
    | (refine hpp 59 1 p59 ?_ <;> decide)
    | exact h30 rfl
    | exact h40 rfl
    | exact h56 rfl
    | (refine absurd (hkill 2 1 p2 ?_ ?_) ?_ <;> decide)
    | (refine absurd (hkill 2 2 p2 ?_ ?_) ?_ <;> decide)
    | (refine absurd (hkill 2 3 p2 ?_ ?_) ?_ <;> decide)
    | (refine absurd (hkill 2 4 p2 ?_ ?_) ?_ <;> decide)
    | (refine absurd (hkill 3 1 p3 ?_ ?_) ?_ <;> decide)
    | (refine absurd (hkill 3 2 p3 ?_ ?_) ?_ <;> decide)
    | (refine absurd (hkill 3 3 p3 ?_ ?_) ?_ <;> decide)
    | (refine absurd (hkill 5 1 p5 ?_ ?_) ?_ <;> decide)
    | (refine absurd (hkill 5 2 p5 ?_ ?_) ?_ <;> decide)
    | (refine absurd (hkill 7 1 p7 ?_ ?_) ?_ <;> decide)
    | (refine absurd (hkill 11 1 p11 ?_ ?_) ?_ <;> decide)
    | (refine absurd (hkill 13 1 p13 ?_ ?_) ?_ <;> decide)
    | (refine absurd (hkill 17 1 p17 ?_ ?_) ?_ <;> decide)
    | (refine absurd (hkill 19 1 p19 ?_ ?_) ?_ <;> decide)
    | (refine absurd (hkill 23 1 p23 ?_ ?_) ?_ <;> decide)
    | (refine absurd (hkill 29 1 p29 ?_ ?_) ?_ <;> decide)

end SmallestSimple

/-! `Babai.five_le_card_of_involved_nonabelian_simple` (the base case `s = 1` of
Prop. 10.2.3, from the solvability of `S_4`) is proved in
`Workspace/Prelim/SmallGroups.lean`. -/

/-! ### `t`-subsets as sets and as `Finset`s -/

/-- The `t`-subsets of a finite `Ω` described by `Set.ncard`, and the paper's
`Ω choose t` (`Babai.binom`, a `Finset` subtype) are the same thing. -/
noncomputable def setNcardEquivBinom (Ω : Type*) [Finite Ω] (t : ℕ) :
    {T : Set Ω // T.ncard = t} ≃ binom Ω t where
  toFun T := ⟨(Set.toFinite (T : Set Ω)).toFinset, by
    rw [← Set.ncard_eq_toFinset_card]; exact T.2⟩
  invFun s := ⟨((s : Finset Ω) : Set Ω), by rw [Set.ncard_coe_finset]; exact s.2⟩
  left_inv T := Subtype.ext (Set.Finite.coe_toFinset _)
  right_inv s := Subtype.ext (Finset.ext fun a => by
    simp only [Set.Finite.mem_toFinset, Finset.mem_coe])

@[simp] theorem mem_setNcardEquivBinom {Ω : Type*} [Finite Ω] {t : ℕ}
    (T : {T : Set Ω // T.ncard = t}) (a : Ω) :
    a ∈ ((setNcardEquivBinom Ω t T : binom Ω t) : Finset Ω) ↔ a ∈ (T : Set Ω) :=
  Set.Finite.mem_toFinset _

/-- A permutation that fixes every `t`-subset of `Ω` setwise, for `1 ≤ t < |Ω|`, is the
identity: if `π a = b ≠ a`, take a `t`-subset containing `a` but not `b`.

This is the step "`σ` fixes every `t_Δ`-subset of `[k]` setwise, which for
`1 ≤ t_Δ < k` means `σ^ϕ = 1`" in Theorem 10.5.1 (e). -/
theorem eq_one_of_image_eq_of_ncard_eq [Fintype Ω] [DecidableEq Ω] {π : Equiv.Perm Ω}
    {t : ℕ} (ht1 : 1 ≤ t) (htk : t < Nat.card Ω)
    (h : ∀ T : Set Ω, T.ncard = t → (π : Equiv.Perm Ω) '' T = T) : π = 1 := by
  classical
  refine Equiv.ext fun a => ?_
  show π a = a
  by_contra hne
  have hab : ({a} : Finset Ω) ⊆ Finset.univ.erase (π a) := by
    intro z hz
    rw [Finset.mem_singleton] at hz
    subst hz
    exact Finset.mem_erase.2 ⟨fun hh => hne hh.symm, Finset.mem_univ _⟩
  have hcard : t ≤ (Finset.univ.erase (π a)).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
    have : Nat.card Ω = Fintype.card Ω := Nat.card_eq_fintype_card
    omega
  obtain ⟨u, hau, hub, hucard⟩ :=
    Finset.exists_subsuperset_card_eq hab (by simpa using ht1) hcard
  have hT : ((u : Set Ω)).ncard = t := by rw [Set.ncard_coe_finset, hucard]
  have hmem : a ∈ (u : Set Ω) := hau (Finset.mem_singleton_self a)
  have hb : π a ∈ (u : Set Ω) := by
    rw [← h _ hT]
    exact ⟨a, hmem, rfl⟩
  have := hub (by simpa using hb)
  exact (Finset.mem_erase.1 this).1 rfl

/-- Background.  If `3 ≤ |Ω \ T|` then the pointwise stabilizer `A(Ω)_(T)` is transitive
on `Ω \ T`: any two points outside `T` are exchanged by a product of two transpositions
supported outside `T`.  This is the step "`Ω \ T` is an orbit of `A(Ω)_(T)`" in the proof
of Observation 10.4.1. -/
theorem exists_mem_alt_pointwiseStabilizer_apply_eq [Fintype Ω] [DecidableEq Ω]
    {T : Set Ω} (hT : 3 ≤ (Tᶜ : Set Ω).ncard) {a b : Ω} (ha : a ∉ T) (hb : b ∉ T) :
    ∃ σ ∈ pointwiseStabilizer (alternatingGroup Ω) T, σ a = b := by
  rcases eq_or_ne a b with rfl | hab
  · exact ⟨1, ⟨(alternatingGroup Ω).one_mem, fun x _ => rfl⟩, rfl⟩
  · have hc : ∃ c, c ∉ T ∧ c ≠ a ∧ c ≠ b := by
      by_contra h
      push_neg at h
      have hsub : (Tᶜ : Set Ω) ⊆ {a, b} := by
        intro c hc
        rcases eq_or_ne c a with rfl | h1
        · exact Or.inl rfl
        · exact Or.inr (h c hc h1)
      have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
      have h2 : ({a, b} : Set Ω).ncard ≤ 2 :=
        le_trans (Set.ncard_insert_le _ _) (by simp)
      omega
    obtain ⟨c, hcT, hca, hcb⟩ := hc
    refine ⟨swap a c * swap a b, ⟨?_, ?_⟩, ?_⟩
    · exact mul_mem_alternatingGroup_of_isSwap ⟨a, c, Ne.symm hca, rfl⟩ ⟨a, b, hab, rfl⟩
    · intro x hx
      have hxa : x ≠ a := fun h => ha (h ▸ hx)
      have hxb : x ≠ b := fun h => hb (h ▸ hx)
      have hxc : x ≠ c := fun h => hcT (h ▸ hx)
      simp [Equiv.Perm.mul_apply, swap_apply_of_ne_of_ne hxa hxb,
        swap_apply_of_ne_of_ne hxa hxc]
    · simp [Equiv.Perm.mul_apply, swap_apply_left,
        swap_apply_of_ne_of_ne (Ne.symm hab) (Ne.symm hcb)]

end Babai
