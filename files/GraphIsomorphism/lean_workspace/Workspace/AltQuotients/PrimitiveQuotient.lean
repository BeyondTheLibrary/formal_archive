/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 10.2 (Large alternating quotient of a primitive group).
-/
import Workspace.Cited.AltQuotients
import Workspace.AltQuotients.SocleFact
import Workspace.AltQuotients.ONanScott
import Workspace.AltQuotients.Subdirect
import Workspace.Prelim.SocleStructure
import Workspace.Prelim.PrimitiveSocleRegular
import Workspace.Prelim.PrimitiveSocleElem
import Workspace.Prelim.PrimitiveSocleFactors

/-!
# §10.2 Large alternating quotient of a primitive group

Proposition 10.2.3 (proved from the cited Theorem 10.2.4, as the paper does; Theorem 10.2.4 itself is
proved in `Workspace/AltQuotients/ONanScott.lean`), Lemma 10.2.5
(the result of the section), and the two remarks.
-/

universe u v

namespace Babai

open MulAction Equiv Equiv.Perm

/-! ### Fact 10.2.2 (i) -/

/-- **Fact 10.2.2 (i)**, §10.2:

> The socle of any group is a direct product of simple groups.

Cited by the paper (`CITED.md`, C8) but used in **no** proof of the paper: Lemma 10.2.5
(line 4451) and §11.2 (line 4998) both use part (ii) ("isomorphic simple groups"), which
applies because the group there is primitive.  By `PLAN.md` Decision 4 a cited result that
the paper never uses gets no axiom, so part (i) is recorded as a statement only.  Part
(ii) is `Babai.fact_10_2_2_ii`, proved in `Workspace/AltQuotients/SocleFact.lean`. -/
def Fact_10_2_2_i_statement : Prop :=
  ∀ (G : Type u) [Group G] [Finite G],
    ∃ (s : ℕ) (R : Fin s → Subgroup G),
      IsInternalDirectProduct (socle G) R ∧ ∀ i, IsSimpleGroup (R i)

/-! ### Proposition 10.2.3 -/

/-- Proposition 10.2.3 in the form in which the paper's induction on `s` runs: the
statement is quantified over all permutation domains, because case (b) of Theorem 10.2.4
produces a different one. -/
theorem proposition_10_2_3_forall (R : Type v) [Group R] [Finite R] [IsSimpleGroup R]
    (hR : ¬ ∀ a b : R, a * b = b * a) :
    ∀ (s : ℕ) (Ω : Type u) (_ : Finite Ω) (G : Subgroup (Equiv.Perm Ω)), IsPrimitive G →
      Nonempty (socle G ≃* (Fin s → R)) → 5 ^ s ≤ Nat.card Ω := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    intro Ω hΩfin G hG hsoc
    haveI := hΩfin
    -- `Ω` is nonempty: otherwise `S(Ω)` is trivial and `|G| < 2`.
    have hne : Nonempty Ω := by
      by_contra hcon
      rw [not_nonempty_iff] at hcon
      have hsub : Subsingleton G := by
        refine ⟨fun a b => Subtype.ext (Equiv.ext fun x => (hcon.false x).elim)⟩
      have : Nat.card G = 1 := Nat.card_eq_one_iff_unique.2 ⟨hsub, ⟨1⟩⟩
      have := hG.1
      omega
    have hΩpos : 1 ≤ Nat.card Ω := Nat.card_pos
    rcases Nat.lt_or_ge s 2 with hs | hs
    · interval_cases s
      · simpa using hΩpos
      · -- `s = 1`: "This follows from the solvability of `S_4`."
        obtain ⟨e⟩ := hsoc
        have hiso : (↥(socle G)) ≃* R := e.trans (MulEquiv.piUnique fun _ : Fin 1 => R)
        have hinv : Function.Injective (G.subtype) := Subgroup.subtype_injective G
        have hmap : (↥(socle G)) ≃* ((socle G).map G.subtype) :=
          Subgroup.equivMapOfInjective (socle G) G.subtype hinv
        have hfin : 5 ≤ Nat.card Ω :=
          five_le_card_of_involved_nonabelian_simple R hR
            ⟨(socle G).map G.subtype, (hmap.symm.trans hiso).toMonoidHom,
              (hmap.symm.trans hiso).surjective⟩
        simpa using hfin
    · -- `s ≥ 2`
      rcases theorem_10_2_4 G hG R hR hs hsoc with hcase | ⟨d, hdvd, hdlt, Ω', hΩ'fin, U, hU,
        hUsoc, hn⟩
      · -- Case (a): `n ≥ |R|^{s-1} ≥ 60^{s-1} > 5^s`.
        have h60 := sixty_le_card_of_nonabelian_simple R hR
        have h1 : 5 ≤ 12 ^ (s - 1) :=
          le_trans (by norm_num) (Nat.le_self_pow (by omega) 12)
        have h2 : (5 : ℕ) ^ s ≤ 60 ^ (s - 1) := by
          have hss : s = (s - 1) + 1 := by omega
          calc (5 : ℕ) ^ s = 5 ^ (s - 1) * 5 := by
                conv_lhs => rw [hss]
                rw [pow_succ]
            _ ≤ 5 ^ (s - 1) * 12 ^ (s - 1) := Nat.mul_le_mul_left _ h1
            _ = 60 ^ (s - 1) := by rw [← Nat.mul_pow]
        exact le_trans h2 (le_trans (Nat.pow_le_pow_left h60 _) hcase)
      · -- Case (b): `ℓ ≥ 5^d` by induction, so `n = ℓ^{s/d} ≥ 5^s`.
        have hd := ih d hdlt Ω' hΩ'fin U hU hUsoc
        rw [hn]
        have hmul : d * (s / d) = s := Nat.mul_div_cancel' hdvd
        calc (5 : ℕ) ^ s = (5 ^ d) ^ (s / d) := by rw [← pow_mul, hmul]
          _ ≤ Nat.card Ω' ^ (s / d) := Nat.pow_le_pow_left hd _

/-- **Proposition 10.2.3**, §10.2 (pointed out by Luks [Lu82]).

> Let `G ≤ S_n` be a primitive group with socle `Soc(G) ≅ R^s` where `R` is a nonabelian
> simple group.  Then `n ≥ 5^s`.

Proof: the paper's induction on `s`, from the cited Theorem 10.2.4. -/
theorem proposition_10_2_3 {Ω : Type u} [Finite Ω] (G : Subgroup (Equiv.Perm Ω))
    (hG : IsPrimitive G) (R : Type v) [Group R] [Finite R] [IsSimpleGroup R]
    (hR : ¬ ∀ a b : R, a * b = b * a) {s : ℕ}
    (hsoc : Nonempty (socle G ≃* (Fin s → R))) : 5 ^ s ≤ Nat.card Ω :=
  proposition_10_2_3_forall R hR s Ω inferInstance G hG hsoc

/-! ### Background for Lemma 10.2.5: the socle factors are permuted by conjugation

The paper's proof of Lemma 10.2.5, Case 2, speaks of "the induced permutation action
`G → S_s` (permuting the copies of `R` by conjugation by elements of `G`)" and of
`Pker(G) ≤ Aut(R₁) × ⋯ × Aut(R_s)` (see also §11.2, "the induced action `G → S_s` on the
direct factors of the socle").  Fact 10.2.2 does **not** say this, and the paper cites
nothing for it; it is elementary, and it is what makes `Babai.Pker` meaningful.  The two
statements below are that background.  They get no axiom (the paper cites nothing), and
are stated here as theorems to be proved. -/

/-- Background for Lemma 10.2.5, Case 2: in a direct product of *nonabelian* simple
groups, the factors are exactly the minimal normal subgroups of the product, so any
automorphism of the product — in particular conjugation by an element of the ambient group
`G`, which normalizes the socle — permutes them.

Proof (elementary): for `N = R₁ × ⋯ × R_s` with all `Rᵢ` nonabelian simple, a normal
subgroup `M ⊴ N` satisfies `[M, Rᵢ] ≤ M ∩ Rᵢ ∈ {1, Rᵢ}` for each `i`, and `[M, Rᵢ] = 1`
for every `i` would force `M ≤ Z(N) = 1`; hence `M` is a subproduct, the minimal normal
subgroups of `N` are precisely `R₁, …, R_s`, and conjugation permutes them.

**Checked against the textbook and true as stated.**  This is Dixon–Mortimer,
*Permutation Groups*, GTM 163, Springer 1996, **Theorem 4.3A (iv)**, p. 112: "If the
subgroups `Kᵢ` in (ii) are all nonabelian, then `K₁, …, K_m` are the only minimal normal
subgroups of `G`" (with Theorem 4.3A (iii) and Corollary 4.3A, p. 113, for `Z(Kᵢ) = 1`).
Applied here to `N = Soc(G)`: each `Rᵢ` is minimal normal in `N` (it is normal in `N` and
simple), the `Rᵢ` are pairwise distinct (`iSupIndep` plus nontriviality), so by 4.3A (iv)
they are *all* the minimal normal subgroups of `N`; `Soc(G)` is characteristic in `G`, so
conjugation by `g ∈ G` restricts to an automorphism of `N` and therefore permutes them.
The permutation `π` is well defined and bijective because the `Rᵢ` are distinct. -/
theorem exists_conj_perm_of_socle_factors {G : Type u} [Group G] [Finite G] {s : ℕ}
    {R : Fin s → Subgroup G} (hdp : IsInternalDirectProduct (socle G) R)
    (hsimple : ∀ i, IsSimpleGroup (R i))
    (hnonab : ∀ i, ¬ ∀ a b : R i, a * b = b * a) (g : G) :
    ∃ π : Equiv.Perm (Fin s), ∀ i, (R i).map (MulAut.conj g).toMonoidHom = R (π i) := by
  classical
  haveI : ∀ i, IsSimpleGroup (R i) := hsimple
  set φ : G →* G := (MulAut.conj g).toMonoidHom with hφ
  have hφinj : Function.Injective φ := (MulAut.conj g).injective
  -- each conjugate `R i ^ g` is again a nonabelian simple subgroup of the socle,
  -- normalized by the socle, hence is one of the factors
  have hkey : ∀ i, ∃ j, (R i).map φ = R j := by
    intro i
    have hSle : (R i).map φ ≤ socle G := by
      rintro _ ⟨x, hx, rfl⟩
      exact socle_conj_mem g (hdp.le i hx)
    have hSnorm : ∀ n ∈ socle G, ∀ y ∈ (R i).map φ, n * y * n⁻¹ ∈ (R i).map φ := by
      rintro n hn _ ⟨x, hx, rfl⟩
      have hn' : g⁻¹ * n * g ∈ socle G := by
        simpa using socle_conj_mem g⁻¹ hn
      refine ⟨(g⁻¹ * n * g) * x * (g⁻¹ * n * g)⁻¹, hdp.normal i _ hn' x hx, ?_⟩
      show g * ((g⁻¹ * n * g) * x * (g⁻¹ * n * g)⁻¹) * g⁻¹ = n * (g * x * g⁻¹) * n⁻¹
      group
    have e : (R i) ≃* ((R i).map φ) := Subgroup.equivMapOfInjective (R i) φ hφinj
    haveI : IsSimpleGroup ((R i).map φ) := MulEquiv.isSimpleGroup e.symm
    have hSnonab : ¬ ∀ a b : ((R i).map φ), a * b = b * a := by
      intro habel
      refine hnonab i fun a b => ?_
      have := habel (e a) (e b)
      have h1 : e (a * b) = e (b * a) := by
        rw [map_mul, map_mul, this]
      exact e.injective h1
    exact exists_eq_of_simple_normal (N := socle G) hdp.le hdp.normal hdp.independent
      hdp.sup_eq hnonab hSle hSnorm hSnonab
  choose f hf using hkey
  have hRne : ∀ i, R i ≠ ⊥ := fun i => (Subgroup.nontrivial_iff_ne_bot (R i)).1 inferInstance
  have hinj : Function.Injective f := by
    intro i j hij
    have : (R i).map φ = (R j).map φ := by rw [hf i, hf j, hij]
    have hRij : R i = R j := Subgroup.map_injective hφinj this
    exact injective_of_directProduct hdp.independent hRne hRij
  refine ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.1 hinj), fun i => ?_⟩
  simpa using hf i

/-- Background for Lemma 10.2.5, Case 2: for a primitive group `G` whose socle is
nonabelian, `C_G(Soc(G)) = 1`.  This is what makes the map
`Pker(G) → Aut(R₁) × ⋯ × Aut(R_s)` injective, so that
`Pker(G)/Soc(G) ≤ Out(R₁) × ⋯ × Out(R_s)`.

Proof (elementary): `C_G(N) ⊴ G`, so if it were nontrivial it would contain a minimal
normal subgroup `M` of `G`; then `M ≤ Soc(G) = N`, whence `M ≤ C_G(N) ⊓ N = Z(N) = 1`
(the socle of a primitive group is a product of isomorphic simple groups by Fact 10.2.2
(ii), all of them nonabelian here, so its center is trivial) — a contradiction.

**Checked against the textbook and true as stated.**  Dixon–Mortimer, *Permutation
Groups*, GTM 163, Springer 1996, **Theorem 4.3B**, p. 114, splits a finite primitive `G`
with minimal normal subgroup `K` into (i) `K` regular elementary abelian and
`Soc(G) = K = C_G(K)`; (ii) `K` regular nonabelian, `C_G(K)` a second minimal normal
subgroup and `Soc(G) = K × C_G(K)`; (iii) `K` nonabelian, `C_G(K) = 1`, `Soc(G) = K`.
Case (i) is excluded by the hypothesis that `Soc(G)` is nonabelian.  In case (iii)
`C_G(Soc(G)) = C_G(K) = 1`, and in case (ii)
`C_G(Soc(G)) = C_G(K) ⊓ C_G(C_G(K)) = C_G(K) ⊓ K = 1` because `K` and `C_G(K)` are
independent nonabelian simple factors.  The hypothesis of primitivity cannot be dropped:
for `G = A₅ × ℤ₂` the socle is `A₅ × ℤ₂`, nonabelian, and `C_G(Soc G) = ℤ₂ ≠ 1`. -/
theorem centralizer_socle_eq_bot {Ω : Type u} [Finite Ω] (G : Subgroup (Equiv.Perm Ω))
    (hG : IsPrimitive G) (hnonab : ¬ ∀ a b : socle G, a * b = b * a) :
    Subgroup.centralizer ((socle G : Subgroup G) : Set G) = ⊥ := by
  classical
  obtain ⟨s, R, hdp, hsimple, hiso⟩ := fact_10_2_2_ii G hG
  haveI : ∀ i, IsSimpleGroup (R i) := hsimple
  -- every factor is nonabelian: they are pairwise isomorphic, and the socle is nonabelian
  have hnonabR : ∀ i, ¬ ∀ a b : R i, a * b = b * a := by
    intro i habel
    have hall : ∀ j, ∀ a b : R j, a * b = b * a := by
      intro j a b
      obtain ⟨e⟩ := hiso j i
      have := habel (e a) (e b)
      exact e.injective (by rw [map_mul, map_mul, this])
    refine hnonab fun a b => ?_
    have := commute_of_directProduct_of_abelian hdp.le hdp.normal hdp.independent
      hdp.sup_eq hall a a.2 b b.2
    exact Subtype.ext this
  -- the centralizer of the socle is normal
  have hCnorm : ∀ g : G, ∀ x ∈ Subgroup.centralizer ((socle G : Subgroup G) : Set G),
      g * x * g⁻¹ ∈ Subgroup.centralizer ((socle G : Subgroup G) : Set G) := by
    intro g x hx
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro y hy
    have hy' : g⁻¹ * y * g ∈ socle G := by
      simpa using socle_conj_mem g⁻¹ hy
    have := hx _ hy'
    have hcalc : y * (g * x * g⁻¹) = g * ((g⁻¹ * y * g) * x) * g⁻¹ := by group
    rw [hcalc, this]
    group
  by_contra hC
  obtain ⟨M, hM, hMC⟩ := exists_isMinimalNormal_le hCnorm hC
  -- `M` lies in the socle and centralizes it, so `M = 1`
  have hMbot : M = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hzN : z ∈ socle G := le_socle_of_isMinimalNormal hM hz
    have hzC := hMC hz
    rw [Subgroup.mem_centralizer_iff] at hzC
    have hcent : ∀ y ∈ socle G, z * y = y * z := fun y hy => (hzC y hy).symm
    have : z = 1 :=
      eq_one_of_central_of_directProduct hdp.le hdp.normal hdp.independent hdp.sup_eq
        hnonabR hzN hcent
    simpa [this] using Subgroup.mem_bot.2 rfl
  exact hM.2.1 hMbot

/-! ### Small general facts used by the proof of Lemma 10.2.5 -/

/-- The socle is a normal subgroup (it is a supremum of normal subgroups). -/
theorem socle_normal (A : Type*) [Group A] : (socle A).Normal :=
  ⟨fun n hn g => socle_conj_mem g hn⟩

/-- Two subgroups of a finite group with `H ≤ K` and `|K| ≤ |H|` are equal. -/
theorem eq_of_le_of_card_le {A : Type*} [Group A] [Finite A] {H K : Subgroup A}
    (hle : H ≤ K) (hcard : Nat.card K ≤ Nat.card H) : H = K := by
  refine SetLike.coe_injective (Set.eq_of_subset_of_ncard_le hle ?_ (Set.toFinite _))
  simpa only [← Nat.card_coe_set_eq] using hcard

/-- If `A` is involved in `B` (a quotient of a subgroup) then `|A| ≤ |B|`. -/
theorem nat_card_le_of_involved {A B : Type*} [Group A] [Group B] [Finite B]
    (h : Involved A B) : Nat.card A ≤ Nat.card B := by
  obtain ⟨H, f, hf⟩ := h
  exact le_trans (Nat.card_le_card_of_surjective f hf)
    (Nat.card_le_card_of_injective _ Subtype.val_injective)

/-- `2 ^ k ≤ k!` for `k ≥ 4`; used to compare `|A_k| = k!/2` with the bound
`n < 2^{k-2}` coming from `k > 2 + log₂ n`. -/
theorem two_pow_le_factorial {k : ℕ} (hk : 4 ≤ k) : 2 ^ k ≤ Nat.factorial k := by
  induction k with
  | zero => omega
  | succ m ih =>
    rcases Nat.lt_or_ge m 4 with hm | hm
    · interval_cases m
      · omega
      · omega
      · omega
      · decide
    · have := ih (by omega)
      calc 2 ^ (m + 1) = 2 * 2 ^ m := by ring
        _ ≤ (m + 1) * Nat.factorial m := Nat.mul_le_mul (by omega) this
        _ = Nat.factorial (m + 1) := rfl

/-- The image under `ϕ` of a normal subgroup is normal inside `K = ϕ^{range}`. -/
theorem normal_subgroupOf_of_map {A B : Type*} [Group A] [Group B] {ϕ : A →* B}
    {K : Subgroup B} (hϕ : ϕ.range = K) {P : Subgroup A} (hP : P.Normal) :
    ((P.map ϕ).subgroupOf K).Normal := by
  constructor
  intro n hn a
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  obtain ⟨t, ht, htn⟩ := hn
  have ha : (a : B) ∈ ϕ.range := by rw [hϕ]; exact a.2
  obtain ⟨g, hg⟩ := ha
  refine ⟨g * t * g⁻¹, hP.conj_mem t ht g, ?_⟩
  push_cast
  rw [map_mul, map_mul, map_inv, hg, htn]

/-! ### Lemma 10.2.5, Case 2: the induced action on the socle factors

The proof of Case 2 uses "the induced permutation action `G → S_s` (permuting the copies
of `R` by conjugation by elements of `G`)", whose kernel is `Pker(G)`
(`Babai.Pker`), and the map `Pker(G) → Aut(R₁) × ⋯ × Aut(R_s)` with its consequence
`Pker(G)/N ≤ Out(R₁) × ⋯ × Out(R_s)`.  They are built here from
`Babai.exists_conj_perm_of_socle_factors`. -/

section SocleFactors

variable {A : Type u} [Group A] [Finite A] {s : ℕ} {R : Fin s → Subgroup A}
  (hdp : IsInternalDirectProduct (socle A) R) (hsimple : ∀ i, IsSimpleGroup (R i))
  (hnonab : ∀ i, ¬ ∀ a b : R i, a * b = b * a)

include hdp hsimple in
/-- The socle factors are pairwise distinct. -/
theorem socleFactors_injective : Function.Injective R := by
  refine injective_of_directProduct hdp.independent fun i => ?_
  haveI := hsimple i
  exact (Subgroup.nontrivial_iff_ne_bot (R i)).1 inferInstance

/-- The permutation of the socle factors induced by conjugation by `g`. -/
noncomputable def socleFactorPerm (g : A) : Equiv.Perm (Fin s) :=
  (exists_conj_perm_of_socle_factors hdp hsimple hnonab g).choose

theorem socleFactorPerm_spec (g : A) (i : Fin s) :
    (R i).map (MulAut.conj g).toMonoidHom = R (socleFactorPerm hdp hsimple hnonab g i) :=
  (exists_conj_perm_of_socle_factors hdp hsimple hnonab g).choose_spec i

theorem socleFactorPerm_unique {g : A} {π : Equiv.Perm (Fin s)}
    (hπ : ∀ i, (R i).map (MulAut.conj g).toMonoidHom = R (π i)) :
    socleFactorPerm hdp hsimple hnonab g = π :=
  Equiv.ext fun i => socleFactors_injective hdp hsimple
    ((socleFactorPerm_spec hdp hsimple hnonab g i).symm.trans (hπ i))

/-- Conjugation by a product is the composite of the conjugations. -/
theorem conj_mul_toMonoidHom (g h : A) :
    (MulAut.conj (g * h)).toMonoidHom
      = (MulAut.conj g).toMonoidHom.comp (MulAut.conj h).toMonoidHom := by
  ext x
  simp [MulAut.conj, mul_assoc]

/-- §10.2, proof of Lemma 10.2.5, Case 2: "the induced permutation action `G → S_s`
(permuting the copies of `R` by conjugation by elements of `G`)". -/
noncomputable def socleFactorHom : A →* Equiv.Perm (Fin s) where
  toFun := socleFactorPerm hdp hsimple hnonab
  map_one' := socleFactorPerm_unique hdp hsimple hnonab fun i => by
    have h : (MulAut.conj (1 : A)).toMonoidHom = MonoidHom.id A := by ext x; simp
    rw [h, Subgroup.map_id]
    rfl
  map_mul' g h := socleFactorPerm_unique hdp hsimple hnonab fun i => by
    rw [conj_mul_toMonoidHom, ← Subgroup.map_map,
      socleFactorPerm_spec hdp hsimple hnonab h i,
      socleFactorPerm_spec hdp hsimple hnonab g _]
    rfl

/-- The kernel of the action on the socle factors is `Pker(G)`. -/
theorem ker_socleFactorHom : (socleFactorHom hdp hsimple hnonab).ker = Pker R := by
  ext g
  rw [MonoidHom.mem_ker]
  constructor
  · intro hg
    show ∀ i, _
    intro i
    have h := socleFactorPerm_spec hdp hsimple hnonab g i
    rw [show socleFactorPerm hdp hsimple hnonab g = 1 from hg] at h
    simpa using h
  · intro hg
    exact socleFactorPerm_unique hdp hsimple hnonab fun i => by
      simpa using (hg : ∀ i, (R i).map (MulAut.conj g).toMonoidHom = R i) i

/-- For `g ∈ Pker(G)`, conjugation by `g` restricts to an automorphism of the factor
`R i`.  This is the map `Pker(G) → Aut(R₁) × ⋯ × Aut(R_s)` of the paper's proof,
coordinatewise. -/
noncomputable def conjOnFactor (g : ↥(Pker R)) (i : Fin s) : MulAut ↥(R i) :=
  (Subgroup.equivMapOfInjective (R i) (MulAut.conj (g : A)).toMonoidHom
      (MulAut.conj (g : A)).injective).trans
    (MulEquiv.subgroupCongr
      (show (R i).map (MulAut.conj (g : A)).toMonoidHom = R i from g.2 i))

theorem conjOnFactor_coe (g : ↥(Pker R)) (i : Fin s) (x : ↥(R i)) :
    ((conjOnFactor g i x : ↥(R i)) : A) = (g : A) * (x : A) * (g : A)⁻¹ := rfl

/-- `Pker(G) → Aut(R₁) × ⋯ × Aut(R_s)`. -/
noncomputable def conjFactors : ↥(Pker R) →* ∀ i, MulAut ↥(R i) where
  toFun g i := conjOnFactor g i
  map_one' := by
    funext i
    exact MulEquiv.ext fun x => Subtype.ext (by rw [conjOnFactor_coe]; simp)
  map_mul' g h := by
    funext i
    refine MulEquiv.ext fun x => Subtype.ext ?_
    rw [conjOnFactor_coe]
    show (g : A) * (h : A) * (x : A) * ((g : A) * (h : A))⁻¹
      = ((conjOnFactor g i (conjOnFactor h i x) : ↥(R i)) : A)
    rw [conjOnFactor_coe, conjOnFactor_coe]
    group

/-- `Pker(G) → Out(R₁) × ⋯ × Out(R_s)`. -/
noncomputable def outFactors : ↥(Pker R) →* ∀ i, Out ↥(R i) :=
  Pi.monoidHom fun i => (QuotientGroup.mk' (Inn ↥(R i))).comp
    ((Pi.evalMonoidHom (fun j => MulAut ↥(R j)) i).comp (conjFactors (R := R)))

include hdp in
/-- "`Pker(G)/N ≤ Out(R₁) × ⋯ × Out(R_s)`": the kernel of `Pker(G) → ∏ Out(Rᵢ)` is
contained in the socle.  (The reverse inclusion holds too but is not needed.)  The proof:
if conjugation by `g` is inner on every factor, say by `rᵢ ∈ Rᵢ`, then `g` and
`u = r₁ ⋯ r_s ∈ N` induce the same conjugation on every factor, so `u⁻¹g` centralizes the
socle and is trivial by `Babai.centralizer_socle_eq_bot`. -/
theorem ker_outFactors_le
    (hC : Subgroup.centralizer ((socle A : Subgroup A) : Set A) = ⊥) :
    (outFactors (R := R)).ker ≤ (socle A).subgroupOf (Pker R) := by
  classical
  intro g hg
  have hinner : ∀ i, ∃ y : ↥(R i), conjOnFactor g i = MulAut.conj y := by
    intro i
    have h1 : (outFactors (R := R) g) i = 1 := by
      rw [MonoidHom.mem_ker.1 hg]; rfl
    have h2 : conjOnFactor (R := R) g i ∈ Inn ↥(R i) :=
      (QuotientGroup.eq_one_iff (N := Inn ↥(R i)) _).1 h1
    obtain ⟨w, hw⟩ := h2
    exact ⟨w, hw.symm⟩
  choose y hy using hinner
  have hcomm : Pairwise fun i j : Fin s => ∀ x z : A, x ∈ R i → z ∈ R j → Commute x z :=
    fun i j hij x z hx hz =>
      commute_of_directProduct hdp.le hdp.normal hdp.independent hij hx hz
  set u : A := Subgroup.noncommPiCoprod hcomm y with hu
  have humem : u ∈ socle A := by
    have : u ∈ (Subgroup.noncommPiCoprod hcomm).range := ⟨y, rfl⟩
    rwa [Subgroup.noncommPiCoprod_range, hdp.sup_eq] at this
  have hconj : ∀ i, ∀ x ∈ R i, u * x * u⁻¹ = (g : A) * x * (g : A)⁻¹ := by
    intro i x hx
    rw [hu, conj_noncommPiCoprod hcomm y hx]
    have := congrArg (fun f : MulAut ↥(R i) => ((f ⟨x, hx⟩ : ↥(R i)) : A)) (hy i)
    simp only [conjOnFactor_coe] at this
    exact this.symm
  -- `u⁻¹ g` centralizes every factor, hence the socle
  have hcentgen : ∀ i, ∀ x ∈ R i, (u⁻¹ * (g : A)) * x = x * (u⁻¹ * (g : A)) := by
    intro i x hx
    have h := hconj i x hx
    have : u⁻¹ * ((g : A) * x * (g : A)⁻¹) * u = x := by
      rw [← h]; group
    calc (u⁻¹ * (g : A)) * x = (u⁻¹ * ((g : A) * x * (g : A)⁻¹) * u) * (u⁻¹ * (g : A)) := by
          group
      _ = x * (u⁻¹ * (g : A)) := by rw [this]
  have hcent : (u⁻¹ * (g : A)) ∈ Subgroup.centralizer ((socle A : Subgroup A) : Set A) := by
    refine Subgroup.mem_centralizer_iff.2 fun z hz => ?_
    have hz' : z ∈ ⨆ i, R i := by rw [hdp.sup_eq]; exact hz
    refine Subgroup.iSup_induction R
      (C := fun w => w * (u⁻¹ * (g : A)) = (u⁻¹ * (g : A)) * w) hz' ?_ ?_ ?_
    · intro i w hw; exact (hcentgen i w hw).symm
    · simp
    · intro a b ha hb
      calc a * b * (u⁻¹ * (g : A)) = a * ((u⁻¹ * (g : A)) * b) := by rw [mul_assoc, hb]
        _ = (u⁻¹ * (g : A)) * (a * b) := by rw [← mul_assoc, ha, mul_assoc]
  rw [hC, Subgroup.mem_bot] at hcent
  have hgu : (g : A) = u := by
    have := congrArg (fun z => u * z) hcent
    simpa [← mul_assoc] using this
  rw [Subgroup.mem_subgroupOf, hgu]
  exact humem

end SocleFactors

/-! ### Lemma 10.2.5, Case 1: the affine case

> Case 1. `N` is abelian (the "affine case") and therefore regular, i.e. `n = |N|`.  In
> this case `N ≅ ℤ_p^s` and `G/N ≤ GL(s, p)` for some prime `p`, so `n = p^s`.  Moreover
> `A_k` is involved in `GL(s, p)`. … for `k ≥ 9` it follows that `k ≤ s + 2`.  But we have
> `s + 2 ≤ 2 + log_p n < k`, a contradiction, so this case cannot occur.

The paper says "this case cannot occur"; what its argument shows, and what is proved here,
is that the case cannot occur *when `ϕ` is not injective* — which is all the Lemma needs,
and all that is true: `G = A_k` acting on `k` points is primitive with nonabelian socle,
but nothing rules out an abelian socle before `ker ϕ ≠ 1` is used.  The uncited
ingredients are Dixon–Mortimer, *Permutation Groups*, GTM 163, Theorem 4.3B (i), p. 114
(`N` regular, `Soc(G) = N = C_G(N)`, `G/N ≤ GL(s,p)`), proved in
`Workspace/Prelim/PrimitiveSocleRegular.lean` and `Workspace/Prelim/PrimitiveSocleElem.lean`,
and `Babai.le_add_two_of_involved_GL` (cited by the paper). -/
/-- The common core of the two forms of Case 1 of Lemma 10.2.5 (§10.2): if the socle `N` of
the primitive group `G` is abelian and lies in `ker ϕ`, the paper's chain
`k ≤ s + 2 ≤ 2 + log_p n < k` gives a contradiction.

The uncited ingredients are Dixon–Mortimer, *Permutation Groups*, GTM 163, Theorem 4.3B (i),
p. 114 (`N` regular, `Soc(G) = N = C_G(N)`, `G/N ≤ GL(s,p)`), proved in
`Workspace/Prelim/PrimitiveSocleRegular.lean` and `Workspace/Prelim/PrimitiveSocleElem.lean`,
and `Babai.le_add_two_of_involved_GL` (cited by the paper). -/
private theorem affine_case_false {Ω : Type u} [Fintype Ω] [DecidableEq Ω]
    {G : Subgroup (Equiv.Perm Ω)} (hG : IsPrimitive G) {k : ℕ}
    (ϕ : G →* Equiv.Perm (Fin k)) (hϕ : ϕ.range = alternatingGroup (Fin k))
    (hk : LargeK k (Nat.card Ω)) (habel : ∀ a b : socle G, a * b = b * a)
    (hNne : socle G ≠ ⊥) (hNker : socle G ≤ ϕ.ker) : False := by
  classical
  haveI := hG.nontrivial_dom
  obtain ⟨x₀⟩ := hG.nonempty_dom
  have hk8 := hk.eight_lt
  have hn := hk.lt_two_pow
  set N := socle G with hNdef
  haveI hNnorm : N.Normal := socle_normal _
  have habelN : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x := by
    intro x hx y hy
    exact congrArg Subtype.val (habel ⟨x, hx⟩ ⟨y, hy⟩)
  have hNtrans : IsPretransitive ↥N Ω := isPretransitive_of_normal_of_isPrimitive hG N hNne
  have hcardN : Nat.card ↥N = Nat.card Ω :=
    card_eq_of_abelian_of_isPretransitive hNtrans (fun a b => Subtype.ext
      (habelN a a.2 b b.2)) x₀
  -- `N ≅ ℤ_p^s`, so `n = p^s`
  obtain ⟨s, R, hdp, hsimple, hiso⟩ := fact_10_2_2_ii G hG
  have hs : 0 < s := by
    rcases Nat.eq_zero_or_pos s with rfl | h
    · exact absurd (hdp.sup_eq.symm.trans (iSup_of_empty R)) hNne
    · exact h
  obtain ⟨p, hp, ⟨eN⟩, hcardp⟩ :=
    exists_prime_mulEquiv_of_abelian_directProduct hdp.le hdp.independent hdp.sup_eq hsimple
      habelN ⟨0, hs⟩ (fun i => hiso i ⟨0, hs⟩)
  have hnps : Nat.card Ω = p ^ s := by rw [← hcardN, hcardp]
  -- the conjugation action `G → Aut(N) ≅ GL(s, p)`; its kernel is `C_G(N) = N`
  set ψ : ↥G →* Matrix.GeneralLinearGroup (Fin s) (ZMod p) :=
    ((mulAutEquivGL p s).toMonoidHom.comp (MulAut.congr eN).toMonoidHom).comp
      (MulAut.conjNormal (H := N)) with hψdef
  have he : Function.Injective
      ⇑((mulAutEquivGL p s).toMonoidHom.comp (MulAut.congr eN).toMonoidHom) :=
    (mulAutEquivGL p s).injective.comp (MulAut.congr eN).injective
  have hmem : ∀ g : ↥G, g ∈ ψ.ker ↔ ∀ y ∈ N, g * y * g⁻¹ = y := by
    intro g
    rw [hψdef, MonoidHom.mem_ker, MonoidHom.comp_apply]
    constructor
    · intro hg
      have h1 : MulAut.conjNormal (H := N) g = 1 := he (by rw [hg, map_one])
      intro y hy
      have := congrArg (fun f : MulAut ↥N => ((f ⟨y, hy⟩ : ↥N) : ↥G)) h1
      simpa [MulAut.conjNormal_apply] using this
    · intro hg
      have h1 : MulAut.conjNormal (H := N) g = 1 := by
        refine MulEquiv.ext fun y => Subtype.ext ?_
        rw [MulAut.conjNormal_apply]
        simpa using hg (y : ↥G) y.2
      rw [h1, map_one]
  have hkerψ : ψ.ker = N := by
    -- `C_G(N) = N`: `N` is abelian, and the centralizer of a transitive group has order `≤ n`
    have hle : ψ.ker ≤ N := by
      have hcle : Nat.card ↥(Subgroup.centralizer ((N : Subgroup ↥G) : Set ↥G))
          ≤ Nat.card Ω := card_centralizer_le hNtrans x₀
      have hsub : N ≤ Subgroup.centralizer ((N : Subgroup ↥G) : Set ↥G) := by
        intro y hy
        exact Subgroup.mem_centralizer_iff.2 fun z hz => habelN z hz y hy
      have heq : Subgroup.centralizer ((N : Subgroup ↥G) : Set ↥G) = N :=
        (eq_of_le_of_card_le hsub (by rw [hcardN]; exact hcle)).symm
      intro g hg
      rw [← heq]
      exact Subgroup.mem_centralizer_iff.2 fun z hz => by
        have := (hmem g).1 hg z hz
        calc z * g = (g * z * g⁻¹) * g := by rw [this]
          _ = g * z := by group
    refine le_antisymm hle ?_
    intro g hg
    exact (hmem g).2 fun y hy => by
      have := habelN g hg y hy
      calc g * y * g⁻¹ = y * g * g⁻¹ := by rw [this]
        _ = y := by group
  -- `A_k` is involved in `GL(s, p)`
  have hinv : Involved (alternatingGroup (Fin k)) (Matrix.GeneralLinearGroup (Fin s) (ZMod p)) := by
    have hψ'surj : Function.Surjective ψ.rangeRestrict := ψ.rangeRestrict_surjective
    have hψ'ker : ψ.rangeRestrict.ker ≤ ϕ.ker := by
      rw [MonoidHom.ker_rangeRestrict, hkerψ]; exact hNker
    obtain ⟨χ, hχ⟩ := exists_factor_of_ker_le hψ'surj ϕ hψ'ker
    have hχrange : χ.range = alternatingGroup (Fin k) := by
      rw [range_of_factor hψ'surj hχ, hϕ]
    have hmem : ∀ y, χ y ∈ alternatingGroup (Fin k) := fun y => hχrange ▸ ⟨y, rfl⟩
    refine ⟨ψ.range, χ.codRestrict _ hmem, fun a => ?_⟩
    have : (a : Equiv.Perm (Fin k)) ∈ χ.range := by rw [hχrange]; exact a.2
    obtain ⟨y, hy⟩ := this
    exact ⟨y, Subtype.ext hy⟩
  have hks := le_add_two_of_involved_GL hp (by omega) hinv
  -- `2^s ≤ p^s = n < 2^{k-2}`
  have h2p : (2 : ℕ) ^ s ≤ p ^ s := Nat.pow_le_pow_left hp.two_le s
  have : (2 : ℕ) ^ s < 2 ^ (k - 2) := lt_of_le_of_lt (le_trans h2p (le_of_eq hnps.symm)) hn
  have hslt : s < k - 2 := (Nat.pow_lt_pow_iff_right (by norm_num)).1 this
  omega

theorem lemma_10_2_5_affine {Ω : Type u} [Fintype Ω] [DecidableEq Ω]
    {G : Subgroup (Equiv.Perm Ω)} (hG : IsPrimitive G) {k : ℕ}
    (ϕ : G →* Equiv.Perm (Fin k)) (hϕ : ϕ.range = alternatingGroup (Fin k))
    (hk : LargeK k (Nat.card Ω)) (habel : ∀ a b : socle G, a * b = b * a) :
    Function.Injective ϕ := by
  classical
  haveI := hG.nontrivial_dom
  rw [← MonoidHom.ker_eq_bot_iff]
  by_contra hker
  -- a minimal normal subgroup inside `ker ϕ`
  obtain ⟨M, hM, hMker⟩ :=
    exists_isMinimalNormal_le (C := ϕ.ker)
      (fun g y hy => (show (ϕ.ker).Normal from inferInstance).conj_mem y hy g) hker
  haveI : M.Normal := hM.1
  have hMN : M ≤ socle G := le_socle_of_isMinimalNormal hM
  have hNne : socle G ≠ ⊥ := fun h => hM.2.1 (le_bot_iff.1 (h ▸ hMN))
  obtain ⟨x₀⟩ := hG.nonempty_dom
  haveI : (socle ↥G).Normal := socle_normal _
  have habelN : ∀ x ∈ socle G, ∀ y ∈ socle G, x * y = y * x := by
    intro x hx y hy
    exact congrArg Subtype.val (habel ⟨x, hx⟩ ⟨y, hy⟩)
  -- `N` and `M` are abelian and transitive, hence regular of order `n`
  have hMtrans : IsPretransitive ↥M Ω := isPretransitive_of_normal_of_isPrimitive hG M hM.2.1
  have hNtrans : IsPretransitive ↥(socle G) Ω :=
    isPretransitive_of_normal_of_isPrimitive hG (socle G) hNne
  have hcardM : Nat.card ↥M = Nat.card Ω :=
    card_eq_of_abelian_of_isPretransitive hMtrans
      (fun a b => Subtype.ext (habelN a (hMN a.2) b (hMN b.2))) x₀
  have hcardN : Nat.card ↥(socle G) = Nat.card Ω :=
    card_eq_of_abelian_of_isPretransitive hNtrans (fun a b => Subtype.ext
      (habelN a a.2 b b.2)) x₀
  -- so `M = N`: the socle is the *unique* minimal normal subgroup in the affine case
  have hMeqN : M = socle G := eq_of_le_of_card_le hMN (by rw [hcardM, hcardN])
  exact affine_case_false hG ϕ hϕ hk habel hNne (hMeqN ▸ hMker)


/-- §10.2, **Lemma 10.2.5, Case 1** in the paper's own form.

> Case 1.  `N` is abelian (the "affine case") and therefore regular … a contradiction, so
> this case cannot occur.

Under the hypotheses of Lemma 10.2.5 the socle of `G` is **not** abelian, so Case 1 does
not occur.  The paper leaves one step implicit, which is supplied here: `ϕ(N)` is an
abelian normal subgroup of `A_k`, and `A_k` is simple and nonabelian for `k ≥ 5`, so
`ϕ(N) = 1`, i.e. `N ≤ ker ϕ`; this is what makes `A_k` a quotient of `G/N ≤ GL(s,p)`, which
is the paper's "`A_k` is involved in `GL(s,p)`".  See the entry on Lemma 10.2.5, Case 1 in
the corrected paper.

`Babai.lemma_10_2_5_affine` is the weaker form used in the proof of Lemma 10.2.5. -/
theorem lemma_10_2_5_socle_not_abelian {Ω : Type u} [Fintype Ω] [DecidableEq Ω]
    {G : Subgroup (Equiv.Perm Ω)} (hG : IsPrimitive G) {k : ℕ}
    (ϕ : ↥G →* Equiv.Perm (Fin k)) (hϕ : ϕ.range = alternatingGroup (Fin k))
    (hk : LargeK k (Nat.card Ω)) :
    ¬ ∀ a b : socle ↥G, a * b = b * a := by
  classical
  intro habel
  haveI := hG.nontrivial_dom
  have hk8 := hk.eight_lt
  have h5 : 5 ≤ Fintype.card (Fin k) := by
    rw [Fintype.card_fin]; omega
  haveI : IsSimpleGroup (alternatingGroup (Fin k)) := isSimpleGroup_alternatingGroup h5
  have hAnonab := alternatingGroup_nonabelian (Ω := Fin k) h5
  haveI hNnorm : (socle ↥G).Normal := socle_normal _
  -- `G` is nontrivial, so it has a minimal normal subgroup and `N ≠ 1`
  haveI hGnt : Nontrivial ↥G := Finite.one_lt_card_iff_nontrivial.1 hG.1
  have hNne : socle ↥G ≠ ⊥ := by
    obtain ⟨M, hM, -⟩ :=
      exists_isMinimalNormal_le (C := (⊤ : Subgroup ↥G))
        (fun g y _ => Subgroup.mem_top _) (by
          intro h
          obtain ⟨a, b, hab⟩ := hGnt
          exact hab (by
            have ha : a ∈ (⊥ : Subgroup ↥G) := h ▸ Subgroup.mem_top a
            have hb : b ∈ (⊥ : Subgroup ↥G) := h ▸ Subgroup.mem_top b
            rw [Subgroup.mem_bot] at ha hb
            rw [ha, hb]))
    exact fun h => hM.2.1 (le_bot_iff.1 (h ▸ le_socle_of_isMinimalNormal hM))
  -- `ϕ` as a map onto the subgroup `A_k`
  have hmemA : ∀ g : ↥G, ϕ g ∈ alternatingGroup (Fin k) := fun g => hϕ ▸ ⟨g, rfl⟩
  set ϕ' : ↥G →* ↥(alternatingGroup (Fin k)) := ϕ.codRestrict _ hmemA with hϕ'def
  have hϕ'surj : Function.Surjective ϕ' := by
    intro a
    have : (a : Equiv.Perm (Fin k)) ∈ ϕ.range := by rw [hϕ]; exact a.2
    obtain ⟨g, hg⟩ := this
    exact ⟨g, Subtype.ext hg⟩
  -- `ϕ(N)` is a normal subgroup of `A_k`, hence trivial or everything
  have hmapnormal : ((socle ↥G).map ϕ').Normal := hNnorm.map ϕ' hϕ'surj
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal _ hmapnormal with h | h
  · -- `ϕ(N) = 1`, i.e. `N ≤ ker ϕ`: now the paper's chain applies
    refine affine_case_false hG ϕ hϕ hk habel hNne ?_
    intro x hx
    have hmem : ϕ' x ∈ (socle ↥G).map ϕ' := ⟨x, hx, rfl⟩
    rw [h, Subgroup.mem_bot] at hmem
    rw [MonoidHom.mem_ker]
    exact congrArg Subtype.val hmem
  · -- `ϕ(N) = A_k` would make `A_k` abelian
    refine hAnonab fun a b => ?_
    have ha : a ∈ (socle ↥G).map ϕ' := by rw [h]; trivial
    have hb : b ∈ (socle ↥G).map ϕ' := by rw [h]; trivial
    obtain ⟨x, hx, rfl⟩ := ha
    obtain ⟨y, hy, rfl⟩ := hb
    have hxy : x * y = y * x := congrArg Subtype.val (habel ⟨x, hx⟩ ⟨y, hy⟩)
    rw [← map_mul, ← map_mul, hxy]

/-! ### Lemma 10.2.5, Case 2: nonabelian socle

> Case 2. `N` is nonabelian.  By Prop. 10.2.3 we have `s ≤ log₅ n`.  In particular
> `k > s`.  … let `Pker(G)` denote the kernel of the induced permutation action
> `G → S_s`.  Then `Pker(G) ≤ Aut(R₁) × ⋯ × Aut(R_s)`.  It follows that
> `Pker(G)/N ≤ Out(R₁) × ⋯ × Out(R_s)` is solvable by Schreier's Hypothesis.  Now
> `G/Pker G ≤ S_s` and `s < k` so `G/Pker G` cannot involve `A_k`.  The solvable group
> `Pker(G)/N` also does not involve `A_k`.  It follows that `G/N` does not involve `A_k`
> and therefore `ker ϕ ≱ N`.
>
> Let `M` be a minimal normal subgroup of `G`.
> Case 2a. `M ≠ N`.  Then there is a unique other minimal normal subgroup, `M*`, the
> centralizer of `M`, which is isomorphic to `M`.  It follows that `M` is regular, so
> `n = |M|`. … Hence `n ≥ |A_k| > 2^k > n`, a contradiction.  So this case cannot occur.
> Case 2b. `M = N` is the unique minimal normal subgroup of `G`.  Since `N ≰ ker ϕ`, it
> follows that `ker ϕ = 1`.

The formalized proof follows this route.  Two points of presentation:

* "`G/N` does not involve `A_k`" is used only through its consequence `N ≰ ker ϕ`, and is
  established exactly as the paper does, but in the equivalent contrapositive form: if
  `N ≤ ker ϕ` then `ϕ(Pker(G)) ⊴ A_k` is `1` or `A_k`; in the first case `ϕ` factors
  through `G/Pker(G) ≤ S_s` and `|A_k| > s!`, in the second `ϕ|_{Pker(G)}` factors through
  the solvable group `Pker(G)/N`, so `A_k` would be solvable.
* Cases 2a and 2b are merged: a minimal normal subgroup `M ≤ ker ϕ` is produced from
  `ker ϕ ≠ 1`, and the centralizer `C = C_G(M)` is examined.  If `ϕ(C) = A_k` then
  `|A_k| ≤ |C| ≤ n` because `M` is transitive and the centralizer of a transitive group is
  semiregular — this is the paper's "`M` is regular, so `n = |M|`", in the only form the
  contradiction `|A_k| > 2^k > n` needs, and it avoids the part of Dixon–Mortimer,
  *Permutation Groups*, GTM 163, Theorem 4.3B (ii), p. 114–115 (the second minimal normal
  subgroup `M*`, its isomorphism with `M`, and `s` even) which the paper invokes without
  citation and which is not needed here.  If `ϕ(C) = 1` then `N ≤ M ⊔ C ≤ ker ϕ`
  (every minimal normal subgroup either is `M` or centralizes `M`), contradicting
  `N ≰ ker ϕ`.  With `M = N` this is exactly the paper's Case 2b. -/
theorem lemma_10_2_5_nonabelian {Ω : Type u} [Fintype Ω] [DecidableEq Ω]
    {G : Subgroup (Equiv.Perm Ω)} (hG : IsPrimitive G) {k : ℕ}
    (ϕ : G →* Equiv.Perm (Fin k)) (hϕ : ϕ.range = alternatingGroup (Fin k))
    (hk : LargeK k (Nat.card Ω)) (hnonabN : ¬ ∀ a b : socle G, a * b = b * a) :
    Function.Injective ϕ := by
  classical
  haveI := hG.nontrivial_dom
  obtain ⟨x₀⟩ := hG.nonempty_dom
  have hk8 := hk.eight_lt
  have hn := hk.lt_two_pow
  have h5 : 5 ≤ Fintype.card (Fin k) := by simp only [Fintype.card_fin]; omega
  haveI : IsSimpleGroup (alternatingGroup (Fin k)) := isSimpleGroup_alternatingGroup h5
  have hAnonab := alternatingGroup_nonabelian (Ω := Fin k) h5
  have hpk : Nat.card (Equiv.Perm (Fin k)) = Nat.factorial k := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  haveI : Nontrivial (Fin k) :=
    ⟨⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp [Fin.ext_iff]⟩⟩
  have halt : 2 * Nat.card (alternatingGroup (Fin k)) = Nat.card (Equiv.Perm (Fin k)) :=
    two_mul_nat_card_alternatingGroup
  set N := socle ↥G with hNdef
  haveI hNnorm : N.Normal := socle_normal _
  have hC := centralizer_socle_eq_bot G hG hnonabN
  obtain ⟨s, R, hdp, hsimple, hiso⟩ := fact_10_2_2_ii G hG
  haveI : ∀ i, IsSimpleGroup (R i) := hsimple
  -- every socle factor is nonabelian
  have hnonab : ∀ i, ¬ ∀ a b : R i, a * b = b * a := by
    intro i habel
    have hall : ∀ j, ∀ a b : R j, a * b = b * a := by
      intro j a b
      obtain ⟨e⟩ := hiso j i
      have := habel (e a) (e b)
      exact e.injective (by rw [map_mul, map_mul, this])
    refine hnonabN fun a b => ?_
    exact Subtype.ext (commute_of_directProduct_of_abelian hdp.le hdp.normal hdp.independent
      hdp.sup_eq hall a a.2 b b.2)
  -- `s ≥ 1`
  have hs : 0 < s := by
    rcases Nat.eq_zero_or_pos s with rfl | h
    · exfalso
      have hbot : N = ⊥ := hdp.sup_eq.symm.trans (iSup_of_empty R)
      have hsub : Subsingleton ↥N := by rw [hbot]; infer_instance
      exact hnonabN fun a b => Subsingleton.elim _ _
    · exact h
  -- `Soc(G) ≅ R^s`, so `5^s ≤ n` (Prop. 10.2.3) and `s < k - 2`
  set i₀ : Fin s := ⟨0, hs⟩ with hi₀
  have hcomm : Pairwise fun i j : Fin s => ∀ x z : ↥G, x ∈ R i → z ∈ R j → Commute x z :=
    fun i j hij x z hx hz => commute_of_directProduct hdp.le hdp.normal hdp.independent hij hx hz
  have hφinj : Function.Injective (Subgroup.noncommPiCoprod hcomm) :=
    Subgroup.injective_noncommPiCoprod_of_iSupIndep (hcomm := hcomm) hdp.independent
  have hφrange : (Subgroup.noncommPiCoprod hcomm).range = N := by
    rw [Subgroup.noncommPiCoprod_range, hdp.sup_eq]
  have eN : (∀ i, ↥(R i)) ≃* ↥N :=
    (MonoidHom.ofInjective hφinj).trans (MulEquiv.subgroupCongr hφrange)
  have esoc : Nonempty (↥N ≃* (Fin s → ↥(R i₀))) :=
    ⟨eN.symm.trans (MulEquiv.piCongrRight fun i => (hiso i i₀).some)⟩
  have h5s : 5 ^ s ≤ Nat.card Ω := proposition_10_2_3 G hG ↥(R i₀) (hnonab i₀) esoc
  have hslt : s < k - 2 := by
    have h2s : (2 : ℕ) ^ s ≤ 5 ^ s := Nat.pow_le_pow_left (by norm_num) s
    have hlt : (2 : ℕ) ^ s < 2 ^ (k - 2) := lt_of_le_of_lt (le_trans h2s h5s) hn
    exact (Nat.pow_lt_pow_iff_right (by norm_num)).1 hlt
  -- "`ker ϕ ≱ N`"
  have hNnotker : ¬ (N ≤ ϕ.ker) := by
    intro hNker
    have hσker : (socleFactorHom hdp hsimple hnonab).ker = Pker R :=
      ker_socleFactorHom hdp hsimple hnonab
    have hPnorm : (Pker R).Normal := by rw [← hσker]; infer_instance
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
        (((Pker R).map ϕ).subgroupOf (alternatingGroup (Fin k)))
        (normal_subgroupOf_of_map hϕ hPnorm) with hbot | htop
    · -- `Pker(G) ≤ ker ϕ`: then `A_k` is a section of `S_s`, but `|A_k| > s!`
      have hle : (Pker R).map ϕ ≤ alternatingGroup (Fin k) := by
        rw [← hϕ]; rintro _ ⟨t, -, rfl⟩; exact ⟨t, rfl⟩
      have hmapbot : (Pker R).map ϕ = ⊥ := by
        rw [Subgroup.subgroupOf_eq_bot] at hbot
        rw [eq_bot_iff, ← inf_eq_left.2 hle]
        exact hbot.le_bot
      have hPker : Pker R ≤ ϕ.ker := (Subgroup.map_eq_bot_iff _).1 hmapbot
      have hkerle : (socleFactorHom hdp hsimple hnonab).rangeRestrict.ker ≤ ϕ.ker := by
        rw [MonoidHom.ker_rangeRestrict, hσker]; exact hPker
      obtain ⟨χ, hχ⟩ := exists_factor_of_ker_le
        (socleFactorHom hdp hsimple hnonab).rangeRestrict_surjective ϕ hkerle
      have hχr : χ.range = alternatingGroup (Fin k) := by
        rw [range_of_factor (socleFactorHom hdp hsimple hnonab).rangeRestrict_surjective hχ, hϕ]
      have hmemχ : ∀ y, χ y ∈ alternatingGroup (Fin k) := fun y => hχr ▸ ⟨y, rfl⟩
      have hinv : Involved (alternatingGroup (Fin k)) (Equiv.Perm (Fin s)) := by
        refine ⟨(socleFactorHom hdp hsimple hnonab).range, χ.codRestrict _ hmemχ, fun a => ?_⟩
        have hmem : (a : Equiv.Perm (Fin k)) ∈ χ.range := by rw [hχr]; exact a.2
        obtain ⟨y, hy⟩ := hmem
        exact ⟨y, Subtype.ext hy⟩
      have hcard := nat_card_le_of_involved hinv
      have hperm : Nat.card (Equiv.Perm (Fin s)) = Nat.factorial s := by
        rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
      rw [hperm] at hcard
      obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
      have hfac : Nat.factorial s ≤ Nat.factorial m := Nat.factorial_le (by omega)
      have hpos : 0 < Nat.factorial m := Nat.factorial_pos m
      have hchain : (m + 1) * Nat.factorial m ≤ 2 * Nat.factorial m := by
        calc (m + 1) * Nat.factorial m = Nat.factorial (m + 1) := rfl
          _ = Nat.card (Equiv.Perm (Fin (m + 1))) := hpk.symm
          _ = 2 * Nat.card (alternatingGroup (Fin (m + 1))) := halt.symm
          _ ≤ 2 * Nat.factorial s := Nat.mul_le_mul_left _ hcard
          _ ≤ 2 * Nat.factorial m := Nat.mul_le_mul_left _ hfac
      have hle2 : m + 1 ≤ 2 := Nat.le_of_mul_le_mul_right hchain hpos
      omega
    · -- `ϕ(Pker(G)) = A_k`: but `Pker(G)/N` is solvable by Schreier's Hypothesis
      rw [Subgroup.subgroupOf_eq_top] at htop
      have hϕPrange : (ϕ.comp (Pker R).subtype).range = alternatingGroup (Fin k) := by
        have h1 : (ϕ.comp (Pker R).subtype).range = (Pker R).map ϕ := by
          ext z
          constructor
          · rintro ⟨w, rfl⟩; exact ⟨(w : ↥G), w.2, rfl⟩
          · rintro ⟨w, hw, rfl⟩; exact ⟨⟨w, hw⟩, rfl⟩
        rw [h1]
        refine le_antisymm ?_ htop
        rw [← hϕ]; rintro _ ⟨t, -, rfl⟩; exact ⟨t, rfl⟩
      have hθker : (outFactors (R := R)).ker ≤ (ϕ.comp (Pker R).subtype).ker := by
        intro g hg
        have hgN := ker_outFactors_le hdp hC hg
        rw [Subgroup.mem_subgroupOf] at hgN
        exact MonoidHom.mem_ker.2 (MonoidHom.mem_ker.1 (hNker hgN))
      have hkerle : (outFactors (R := R)).rangeRestrict.ker
          ≤ (ϕ.comp (Pker R).subtype).ker := by
        rw [MonoidHom.ker_rangeRestrict]; exact hθker
      obtain ⟨χ, hχ⟩ := exists_factor_of_ker_le
        (outFactors (R := R)).rangeRestrict_surjective (ϕ.comp (Pker R).subtype) hkerle
      have hχr : χ.range = alternatingGroup (Fin k) := by
        rw [range_of_factor (outFactors (R := R)).rangeRestrict_surjective hχ, hϕPrange]
      haveI : ∀ i, IsSolvable (Out ↥(R i)) := fun i => schreierHypothesis ↥(R i)
      haveI : IsSolvable (∀ i, Out ↥(R i)) :=
        isSolvable_pi_fin s (fun i => Out ↥(R i)) fun i => inferInstance
      haveI : IsSolvable ↥(outFactors (R := R)).range := inferInstance
      have hmemχ : ∀ y, χ y ∈ alternatingGroup (Fin k) := fun y => hχr ▸ ⟨y, rfl⟩
      have hsurj : Function.Surjective (χ.codRestrict _ hmemχ) := by
        intro a
        have hmem : (a : Equiv.Perm (Fin k)) ∈ χ.range := by rw [hχr]; exact a.2
        obtain ⟨y, hy⟩ := hmem
        exact ⟨y, Subtype.ext hy⟩
      haveI : IsSolvable ↥(alternatingGroup (Fin k)) := solvable_of_surjective hsurj
      exact hAnonab (IsSimpleGroup.comm_iff_isSolvable.2 inferInstance)
  -- Cases 2a and 2b
  rw [← MonoidHom.ker_eq_bot_iff]
  by_contra hker
  obtain ⟨M, hM, hMker⟩ :=
    exists_isMinimalNormal_le (C := ϕ.ker)
      (fun g y hy => (show (ϕ.ker).Normal from inferInstance).conj_mem y hy g) hker
  haveI hMnorm : M.Normal := hM.1
  have hMtrans : IsPretransitive ↥M Ω := isPretransitive_of_normal_of_isPrimitive hG M hM.2.1
  set C : Subgroup ↥G := Subgroup.centralizer ((M : Subgroup ↥G) : Set ↥G) with hCdef
  have hCnorm : C.Normal := by
    constructor
    intro c hc g
    rw [hCdef, Subgroup.mem_centralizer_iff] at hc ⊢
    intro y hy
    have hy' : g⁻¹ * y * g ∈ M := by
      have h' := hMnorm.conj_mem y hy g⁻¹
      simpa using h'
    have hcy := hc _ hy'
    calc y * (g * c * g⁻¹) = g * ((g⁻¹ * y * g) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * y * g)) * g⁻¹ := by rw [hcy]
      _ = (g * c * g⁻¹) * y := by group
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      ((C.map ϕ).subgroupOf (alternatingGroup (Fin k)))
      (normal_subgroupOf_of_map hϕ hCnorm) with hbot | htop
  · -- `C ≤ ker ϕ`, and `N ≤ M ⊔ C`, contradicting `N ≰ ker ϕ`
    have hle : C.map ϕ ≤ alternatingGroup (Fin k) := by
      rw [← hϕ]; rintro _ ⟨t, -, rfl⟩; exact ⟨t, rfl⟩
    have hmapbot : C.map ϕ = ⊥ := by
      rw [Subgroup.subgroupOf_eq_bot] at hbot
      rw [eq_bot_iff, ← inf_eq_left.2 hle]
      exact hbot.le_bot
    have hCker : C ≤ ϕ.ker := (Subgroup.map_eq_bot_iff _).1 hmapbot
    have hNle : N ≤ M ⊔ C := by
      rw [hNdef, socle]
      refine sSup_le ?_
      intro M' hM'
      by_cases hMM' : M' = M
      · rw [hMM']; exact le_sup_left
      · -- `M' ⊓ M = ⊥`, so `M'` centralizes `M`
        have hinfbot : ∀ z, z ∈ M' → z ∈ M → z = 1 := by
          have hPnorm : (M' ⊓ M).Normal := by
            constructor
            intro z hz g
            exact ⟨hM'.1.conj_mem z hz.1 g, hMnorm.conj_mem z hz.2 g⟩
          by_cases hPbot : (M' ⊓ M : Subgroup ↥G) = ⊥
          · intro z hz1 hz2
            have : z ∈ (M' ⊓ M : Subgroup ↥G) := ⟨hz1, hz2⟩
            rw [hPbot, Subgroup.mem_bot] at this
            exact this
          · exfalso
            have heq : (M' ⊓ M : Subgroup ↥G) = M' := hM'.2.2 _ hPnorm hPbot inf_le_left
            have hsub : M' ≤ M := heq ▸ inf_le_right
            exact hMM' (hM.2.2 M' hM'.1 hM'.2.1 hsub)
        refine le_trans (fun a ha => ?_) le_sup_right
        refine Subgroup.mem_centralizer_iff.2 fun b hb => ?_
        have hz1 : a * b * a⁻¹ * b⁻¹ ∈ M' := by
          have : b * a⁻¹ * b⁻¹ ∈ M' := by
            have h' := hM'.1.conj_mem a⁻¹ (M'.inv_mem ha) b
            simpa [mul_assoc] using h'
          have := M'.mul_mem ha this
          simpa [mul_assoc] using this
        have hz2 : a * b * a⁻¹ * b⁻¹ ∈ M :=
          M.mul_mem (hMnorm.conj_mem b hb a) (M.inv_mem hb)
        have hz := hinfbot _ hz1 hz2
        have : a * b = b * a := by
          have h' : a * b * a⁻¹ = b := by
            have := congrArg (fun w => w * b) hz
            simpa [mul_assoc] using this
          calc a * b = (a * b * a⁻¹) * a := by group
            _ = b * a := by rw [h']
        exact this.symm
    exact hNnotker (le_trans hNle (sup_le hMker hCker))
  · -- `ϕ(C) = A_k`: `|A_k| ≤ |C| ≤ n`, but `|A_k| ≥ 2^{k-1} > 2^{k-2} > n`
    rw [Subgroup.subgroupOf_eq_top] at htop
    have h1 : Nat.card ↥(alternatingGroup (Fin k)) ≤ Nat.card ↥(C.map ϕ) :=
      Nat.card_le_card_of_injective _ (Subgroup.inclusion_injective htop)
    have h2 : Nat.card ↥(C.map ϕ) ≤ Nat.card ↥C := by
      refine Nat.card_le_card_of_surjective
        (f := fun c : ↥C => (⟨ϕ (c : ↥G), ⟨(c : ↥G), c.2, rfl⟩⟩ : ↥(C.map ϕ))) ?_
      rintro ⟨z, w, hw, rfl⟩
      exact ⟨⟨w, hw⟩, rfl⟩
    have h3 : Nat.card ↥C ≤ Nat.card Ω := card_centralizer_le hMtrans x₀
    have hfac : 2 ^ k ≤ Nat.factorial k := two_pow_le_factorial (by omega)
    have hsplit : (2 : ℕ) ^ k = 4 * 2 ^ (k - 2) := by
      conv_lhs => rw [show k = 2 + (k - 2) by omega]
      rw [pow_add]
      norm_num
    rw [hpk] at halt
    omega

/-! ### Lemma 10.2.5 -/

/-- **Lemma 10.2.5**, §10.2 — the result of the section.

> Let `G ≤ S(Ω)` be primitive.  Assume `ϕ : G → A_k` is an epimorphism where
> `k > max{8, 2 + log₂ n}`.  Then `ϕ` is an isomorphism; hence `G ≅ A_k`.

The paper's proof: let `N = Soc(G) = R₁ × ⋯ × R_s` (Fact 10.2.2).  Case 1, `N` abelian:
then `N ≅ ℤ_p^s` is regular, `n = p^s`, `G/N ≤ GL(s,p)` and `A_k` is involved in
`GL(s,p)`, so `k ≤ s + 2 ≤ 2 + log_p n < k`, a contradiction.  Case 2, `N` nonabelian:
`s ≤ log₅ n < k`, `Pker(G)/N ≤ Out(R₁) × ⋯ × Out(R_s)` is solvable by Schreier's
Hypothesis and `G/Pker(G) ≤ S_s` does not involve `A_k`, so `G/N` does not involve `A_k`
and `ker ϕ ≱ N`; a minimal normal subgroup `M ≠ N` would force `n ≥ |A_k| > 2^k > n`, so
`M = N` is the unique minimal normal subgroup and `ker ϕ = 1`.

The proof depends on the CFSG through Schreier's Hypothesis (`Babai.schreierHypothesis`,
`Workspace/Cited/AltQuotients.lean`). -/
theorem lemma_10_2_5 {Ω : Type u} [Fintype Ω] [DecidableEq Ω] {G : Subgroup (Equiv.Perm Ω)}
    (hG : IsPrimitive G) {k : ℕ} (ϕ : G →* Equiv.Perm (Fin k))
    (hϕ : ϕ.range = alternatingGroup (Fin k)) (hk : LargeK k (Nat.card Ω)) :
    Function.Injective ϕ := by
  by_cases habel : ∀ a b : socle G, a * b = b * a
  · exact lemma_10_2_5_affine hG ϕ hϕ hk habel
  · exact lemma_10_2_5_nonabelian hG ϕ hϕ hk habel

/-- **Lemma 10.2.5**, concluding sentence: "hence `G ≅ A_k`." -/
theorem lemma_10_2_5_iso {Ω : Type u} [Fintype Ω] [DecidableEq Ω]
    {G : Subgroup (Equiv.Perm Ω)} (hG : IsPrimitive G) {k : ℕ} (ϕ : G →* Equiv.Perm (Fin k))
    (hϕ : ϕ.range = alternatingGroup (Fin k)) (hk : LargeK k (Nat.card Ω)) :
    Nonempty (G ≃* alternatingGroup (Fin k)) := by
  have hinj := lemma_10_2_5 hG ϕ hϕ hk
  exact ⟨(MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hϕ)⟩

/-! ### Remarks 10.2.6 and 10.2.7 -/

/-- **Remark 10.2.6**, §10.2.

> The assumption `k > 2 + log₂ n` is tight infinitely often, as shown by the affine case of
> even dimension in characteristic 2.  In this case `G = ℤ₂^{k-2} ⋊ A_k` acts primitively
> on `n = 2^{k-2}` elements as follows: `A_k` acts on `ℤ₂^k` by permuting the coordinates;
> restrict this action to the zero-weight subspace `∑ xᵢ = 0`, and then to the quotient
> space by the one-dimensional subspace `x₁ = ⋯ = x_k` (this is contained in the
> zero-weight subspace when the dimension is even).  In this case, `k = 2 + log₂ n`, and
> `A_k` is a proper quotient of `G`.

What the remark asserts is that Lemma 10.2.5 fails at `k = 2 + log₂ n`: for even `k` there
is a primitive group of degree `2^{k-2}` with `A_k` as a *proper* quotient.  The
construction is not used anywhere in the paper, so it is recorded as a statement only. -/
def Remark_10_2_6_statement : Prop :=
  ∀ k : ℕ, 9 ≤ k → Even k →
    ∃ (Ω : Type) (G : Subgroup (Equiv.Perm Ω)) (ϕ : G →* Equiv.Perm (Fin k)),
      IsPrimitive G ∧ Nat.card Ω = 2 ^ (k - 2) ∧
        ϕ.range = alternatingGroup (Fin k) ∧ ¬ Function.Injective ϕ

/-- **Remark 10.2.7**, §10.2.

> Under the stronger assumption `k > (log n)^c` for some constant `c`, Pyber [Py17] gave an
> elementary proof of the conclusion of Lemma 10.2.5.

Cited, and used in no proof of the paper (it records that a CFSG-free proof exists under a
stronger hypothesis), so it gets no axiom and is recorded as a statement only.

*"Stronger"* is read as it is written: the hypothesis `k > max{8, 2 + log₂ n}` of
Lemma 10.2.5 (`Babai.LargeK`) stays, and `k > (log n)^c` is added.  Without the first
hypothesis the statement is false for every `c`: the regular cyclic group on two points
(for `c ≥ 0`) or on three points (for `c < 0`) is primitive, maps onto `A₂ = 1` by the
trivial map, which is not injective, and `(log n)^c ≤ 1 < 2 = k`.  See the corrected paper. -/
-- CITED: László Pyber: A CFSG-free analysis of Babai's quasipolynomial GI algorithm.
-- arXiv:1605.08266 (2016/17), as cited by the paper as [Py17].
def Remark_10_2_7_statement : Prop :=
  ∃ c : ℝ, ∀ (Ω : Type) [Fintype Ω] [DecidableEq Ω] (G : Subgroup (Equiv.Perm Ω)),
    IsPrimitive G → ∀ (k : ℕ) (ϕ : G →* Equiv.Perm (Fin k)),
      ϕ.range = alternatingGroup (Fin k) → LargeK k (Nat.card Ω) →
        (Real.log (Nat.card Ω)) ^ c < (k : ℝ) → Function.Injective ϕ

/-- The statement of Remark 10.2.7 holds, because its hypotheses contain those of
Lemma 10.2.5.  (The content of the remark is that the proof can avoid the CFSG; this proof
does not, it goes through `Babai.lemma_10_2_5`.) -/
theorem remark_10_2_7_statement_of_lemma_10_2_5 : Remark_10_2_7_statement :=
  ⟨0, fun _ _ _ _ hG _ ϕ hϕ hk _ => lemma_10_2_5 hG ϕ hϕ hk⟩

end Babai
