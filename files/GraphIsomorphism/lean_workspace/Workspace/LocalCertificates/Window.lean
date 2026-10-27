/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 13.1: Proposition 13.1.8 (the properties of the set `W(T)`).
-/
import Workspace.LocalCertificates.Correctness
import Workspace.AltQuotients.GeneralTarget
import Workspace.ColoredPartitions.Binomial

/-!
# §13.1 The set `W(T)`

Proposition 13.1.8 collects the properties of the set `W(T)` returned by Procedure
LocalCertificates.

## The face `Ω(T)`

Item (i) of Proposition 13.1.8 (and Notation 13.1.10) uses the set `Ω(T)`, which version
2.5 never defines in Section 13.  It is defined in passing inside the proof of
Corollary 12.0.10:

> Since `m ≥ max{9, 2 log₂ n}`, by the Main Structure Theorem (Theorem 10.5.1) `Ω` can be
> divided into standard blocks on which `G` acts as a Johnson group.  The standard blocks
> are labeled by `(Γ choose t)` for some `t ≥ 1`; and `Ω(C)` denotes the union of the
> standard blocks labeled by the elements of the set `(C choose t)`.

(The letter `t` there is the parameter of the standard blocks, which clashes with the size
`t = |T|` of the test set in Section 13; the original version of the paper uses `k` for the
test set size and `t` for the block parameter.)  By Theorem 10.5.1 (e) the standard block
of `u` is labeled by `T(u)`, so the union of the standard blocks labeled by subsets of `T`
is `{u ∈ Ω | T(u) ⊆ T}`, which is the definition used here (`Babai.face`).  See
the corrected paper.
-/

namespace Babai

open MulAction Equiv Equiv.Perm
open scoped Classical

variable {Ω Γ Λ : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype Γ] [DecidableEq Γ]
  {G : Subgroup (Equiv.Perm Ω)}

/-- Theorem 10.5.1 (a), Eq. (52), for a representation with an arbitrary finite target:
`T(u)` is the unique subset of `Γ` with `|T(u)| < |Γ|/4` and
`A(Γ)_(T(u)) ≤ G_u^ϕ ≤ S(Γ)_{T(u)}`.  (For `Γ = Fin k` this is `Babai.Tpoint`.) -/
noncomputable def TpointOf (ϕ : G →* Equiv.Perm Γ) (u : Ω) : Set Γ :=
  sandwichSet ((stabilizer G u).map ϕ)

/-- §12 (proof of Cor. 12.0.10), used in Prop. 13.1.8 (i) and Notation 13.1.10: the
*face* `Ω(T)` of a test set `T`, the union of the standard blocks labeled by subsets of
`T`.  The standard block of `u` is labeled by `T(u)` (Theorem 10.5.1 (e)). -/
noncomputable def face (ϕ : G →* Equiv.Perm Γ) (T : Set Γ) : Set Ω :=
  {u | TpointOf ϕ u ⊆ T}

/-! ### Two counting facts used by Proposition 13.1.8 (i) -/

/-- `2^t ≤ C(2t, t)`: the central binomial coefficient at least doubles at each step
(`Nat.succ_mul_centralBinom_succ`).  (Also proved, for §11.2, as
`Babai.two_pow_le_centralBinom` in `Workspace/Luks/JohnsonBarrier.lean`; kept private here
so that the two files stay independent.) -/
private theorem two_pow_le_centralBinom (t : ℕ) : 2 ^ t ≤ Nat.centralBinom t := by
  induction t with
  | zero => simp [Nat.centralBinom]
  | succ n ih =>
      have h := Nat.succ_mul_centralBinom_succ n
      have hstep : (n + 1) * (2 * Nat.centralBinom n) ≤ (n + 1) * Nat.centralBinom (n + 1) := by
        calc (n + 1) * (2 * Nat.centralBinom n)
            = (2 * (n + 1)) * Nat.centralBinom n := by ring
          _ ≤ (2 * (2 * n + 1)) * Nat.centralBinom n :=
              Nat.mul_le_mul_right _ (by omega)
          _ = (n + 1) * Nat.centralBinom (n + 1) := h.symm
      have hdouble : 2 * Nat.centralBinom n ≤ Nat.centralBinom (n + 1) :=
        Nat.le_of_mul_le_mul_left hstep (by omega)
      calc 2 ^ (n + 1) = 2 * 2 ^ n := by ring
        _ ≤ 2 * Nat.centralBinom n := Nat.mul_le_mul_left _ ih
        _ ≤ Nat.centralBinom (n + 1) := hdouble

/-- `2^t ≤ C(m, t)` whenever `2t ≤ m`. -/
private theorem two_pow_le_choose {t m : ℕ} (h : 2 * t ≤ m) : 2 ^ t ≤ m.choose t := by
  refine le_trans (two_pow_le_centralBinom t) ?_
  rw [Nat.centralBinom]
  exact Nat.choose_le_choose t h

variable (ϕ : G →* Equiv.Perm Γ) (x : Ω → Λ) (T : Set Γ)

/-- Every `t_Δ`-subset of `Γ` is the label `T(y)` of some point `y`: by Eq. (54) the labels
transform by `ϕ`, and `A(Γ) ≤ G^ϕ` is transitive on the `t_Δ`-subsets.  This is
`Babai.exists_Tpoint_eq` with an arbitrary finite target `S(Γ)`. -/
theorem exists_TpointGen_eq (hϕ : IsGiantRep ϕ)
    (hk : VeryLargeK (Nat.card Γ) (maxOrbitLength G)) (u : Ω) {S : Set Γ}
    (hS : S.ncard = tPointGen ϕ u) : ∃ y ∈ orbit G u, TpointGen ϕ y = S := by
  have h9 : 9 ≤ Nat.card Γ := by
    have : (9 : ℝ) ≤ ((Nat.card Γ : ℕ) : ℝ) := le_trans (le_max_left _ _) hk
    exact_mod_cast this
  have hlt := (theorem_10_5_1_a_gen ϕ hϕ hk u).1.1
  obtain ⟨π, hπ, himg⟩ := exists_mem_image_eq_of_ncard_eq (Ω := Γ)
    (K := alternatingGroup Γ) le_rfl (T := TpointGen ϕ u) (U := S) rfl hS (by omega)
  obtain ⟨σ, hσ⟩ := hϕ hπ
  exact ⟨σ • u, mem_orbit u σ, by rw [theorem_10_5_1_c_eq54_gen ϕ hϕ hk u σ, hσ, himg]⟩

/-- There are `C(m, t_Δ)` standard blocks, and they are disjoint nonempty subsets of `Ω`,
so `C(m, t_Δ) ≤ n`.  Stated as it is used: the map `u ↦ T(u)` from `Ω` onto the
`t_Δ`-subsets of `Γ` is onto (`Babai.exists_TpointGen_eq`), for a transitive `G`. -/
theorem choose_tPointGen_le_card (hϕ : IsGiantRep ϕ)
    (hk : VeryLargeK (Nat.card Γ) (maxOrbitLength G)) (hG : IsTransitive G) (u : Ω) :
    (Nat.card Γ).choose (tPointGen ϕ u) ≤ Nat.card Ω := by
  classical
  haveI := hG.isPretransitive
  have hconst : ∀ v : Ω, (TpointGen ϕ v).ncard = tPointGen ϕ u := by
    intro v
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G u v
    exact theorem_10_5_1_c_gen ϕ hϕ hk (mem_orbit_iff.2 ⟨g, hg⟩)
  set f : Ω → {S : Set Γ // S.ncard = tPointGen ϕ u} :=
    fun v => ⟨TpointGen ϕ v, hconst v⟩ with hf
  have hsurj : Function.Surjective f := by
    rintro ⟨S, hS⟩
    obtain ⟨y, -, hy⟩ := exists_TpointGen_eq ϕ hϕ hk u hS
    exact ⟨y, Subtype.ext hy⟩
  have hcard : Nat.card {S : Set Γ // S.ncard = tPointGen ϕ u}
      = (Nat.card Γ).choose (tPointGen ϕ u) := by
    rw [Nat.card_congr (setNcardEquivBinom Γ (tPointGen ϕ u)), card_binom]
  rw [← hcard]
  exact Nat.card_le_card_of_surjective f hsurj

/-- For `|T| ≥ 3` and two distinct points `p, q ∈ T`, some element of `A(T)` takes `p` to
`q`: the product of the two transpositions `(p r)(p q)` for a third point `r ∈ T`. -/
theorem exists_alternating_move_to {T : Set Γ} (h3 : 3 ≤ T.ncard) {p q : Γ} (hp : p ∈ T)
    (hq : q ∈ T) (hpq : p ≠ q) :
    ∃ c ∈ alternatingGroup (T : Set Γ),
      (c : Equiv.Perm (T : Set Γ)) ⟨p, hp⟩ = ⟨q, hq⟩ := by
  classical
  set P : (T : Set Γ) := ⟨p, hp⟩ with hP
  set Q : (T : Set Γ) := ⟨q, hq⟩ with hQ
  have hPQ : P ≠ Q := fun h => hpq (congrArg Subtype.val h)
  have hcard : 3 ≤ Fintype.card (T : Set Γ) := by
    have h : Nat.card (T : Set Γ) = T.ncard := Nat.card_coe_set_eq T
    rw [Nat.card_eq_fintype_card] at h
    omega
  obtain ⟨R, hR⟩ : (({P, Q} : Set (T : Set Γ))ᶜ).Nonempty := by
    rw [← Set.ncard_pos (Set.toFinite _)]
    have hsum := Set.ncard_add_ncard_compl ({P, Q} : Set (T : Set Γ))
    rw [Set.ncard_pair hPQ, Nat.card_eq_fintype_card] at hsum
    omega
  have hRP : R ≠ P := fun h => hR (by simp [h])
  have hRQ : R ≠ Q := fun h => hR (by simp [h])
  refine ⟨Equiv.swap P R * Equiv.swap P Q, ?_, ?_⟩
  · rw [Equiv.Perm.mem_alternatingGroup, map_mul, Equiv.Perm.sign_swap (Ne.symm hRP),
      Equiv.Perm.sign_swap hPQ]
    simp
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left,
      Equiv.swap_apply_of_ne_of_ne (Ne.symm hPQ) (Ne.symm hRQ)]

/-- The standing hypotheses of §13.1 give the hypothesis of Theorem 10.5.1 for the target
`S(Γ)`: `m ≥ max{9, 2 log₂ n₀}`, since `m ≥ 10 log₂ n ≥ 2 log₂ n₀` for the maximal orbit
length `n₀ ≤ n`. -/
theorem veryLargeK_of_setting (hset : LocalCertSetting G ϕ) (h9 : 9 ≤ Nat.card Γ)
    [Nonempty Ω] : VeryLargeK (Nat.card Γ) (maxOrbitLength G) := by
  refine max_le ?_ ?_
  · exact_mod_cast h9
  · have hpos : 0 < Nat.card Ω := Nat.card_pos
    have hlogn : (0 : ℝ) ≤ Real.logb 2 ((Nat.card Ω : ℕ) : ℝ) :=
      Real.logb_nonneg (by norm_num) (by exact_mod_cast hpos)
    have hle : Real.logb 2 ((maxOrbitLength G : ℕ) : ℝ)
        ≤ Real.logb 2 ((Nat.card Ω : ℕ) : ℝ) := by
      rcases Nat.eq_zero_or_pos (maxOrbitLength G) with h0 | hpos'
      · rw [h0]; simpa using hlogn
      · exact Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast hpos')
          (by exact_mod_cast maxOrbitLength_le_card G)
    have hlarge := hset.large
    linarith

/-- Theorem 10.5.1 (b), (c), (d) and the transitivity of `G`: since `Ω` is a single orbit
and at least one point is affected by `ϕ`, *every* point is, so `T(u) ≠ ∅`. -/
theorem one_le_tPointGen (hset : LocalCertSetting G ϕ)
    (hk : VeryLargeK (Nat.card Γ) (maxOrbitLength G)) (u : Ω) : 1 ≤ tPointGen ϕ u := by
  obtain ⟨⟨z, hz⟩, -⟩ := theorem_10_5_1_d_gen ϕ hset.giant hk
  haveI := hset.transitive.isPretransitive
  have hzu : z ∈ orbit G u := by
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G u z
    exact mem_orbit_iff.2 ⟨g, hg⟩
  have hb : 1 ≤ tPointGen ϕ z := (theorem_10_5_1_b_gen ϕ hset.giant hk z).1 hz
  rw [← theorem_10_5_1_c_gen ϕ hset.giant hk hzu]
  exact hb

/-- `t_Δ < t`: the standard blocks are `C(m, t_Δ)` in number and they are disjoint nonempty
subsets of `Ω`, so `C(m, t_Δ) ≤ n < 2^{t-2}`, while `t ≤ t_Δ` would give
`2^t ≤ C(m,t) ≤ C(m,t_Δ)`. -/
theorem tPointGen_lt (hset : LocalCertSetting G ϕ)
    (hk : VeryLargeK (Nat.card Γ) (maxOrbitLength G))
    (ht : LargeK T.ncard (Nat.card Ω)) (htm : 10 * T.ncard ≤ Nat.card Γ) (u : Ω) :
    tPointGen ϕ u < T.ncard := by
  have h8 : 8 < T.ncard := ht.eight_lt
  have h4 := (theorem_10_5_1_a_gen ϕ hset.giant hk u).1.1
  have hdef : tPointGen ϕ u = (TpointGen ϕ u).ncard := rfl
  by_contra hcon
  push_neg at hcon
  have hA : 2 ^ T.ncard ≤ (Nat.card Γ).choose T.ncard := two_pow_le_choose (by omega)
  have hB : (Nat.card Γ).choose T.ncard ≤ (Nat.card Γ).choose (tPointGen ϕ u) :=
    choose_le_choose_of_le_half hcon (by omega)
  have hC := choose_tPointGen_le_card ϕ hset.giant hk hset.transitive u
  have hD := ht.lt_two_pow
  have hE : (2 : ℕ) ^ (T.ncard - 2) < 2 ^ T.ncard :=
    Nat.pow_lt_pow_right (by norm_num) (by omega)
  omega

/-- Proposition 13.1.8 (i), the substantial half: `Ω(T) ⊆ W(T)`.

The paper's route (the parenthetical remark deleted from version 2.5, present in the
original as a comment): the while loop is executed at least once
(`Babai.one_le_haltIndex`), and after the first round `W ⊇ Aff(G_T, ψ_T) ⊇ Ω(T)`, because
every `u` with `∅ ≠ T(u) ⊆ T` is affected by `(G_T, ψ_T)`: by Eq. (52), `G_u^ϕ` stabilizes
`T(u)` setwise, so `(G_T)_u^{ψ_T} ≤ S(T)_{T(u)}`, which does not contain `A(T)` because
`T(u)` is a nonempty proper subset of `T` (proper since the number `(m choose |T(u)|)` of
standard blocks is at most `n < 2^{t-2}`, so `|T(u)| < t`) and `A(T)` is transitive for
`t ≥ 3`.  That `T(u) ≠ ∅` uses Theorem 10.5.1 (b) and (d) together with the transitivity
of `G`: `Ω` is a single orbit, and at least one orbit is affected.

The items (a), (b), (c), (d) of Theorem 10.5.1 are used in the form they take for a
representation with target `S(Γ)` (`Workspace/AltQuotients/GeneralTarget.lean`). -/
theorem face_subset_windowOut (hset : LocalCertSetting G ϕ)
    (ht : LargeK T.ncard (Nat.card Ω)) (htm : 10 * T.ncard ≤ Nat.card Γ) [Nonempty Ω] :
    face ϕ T ⊆ windowOut ϕ x T := by
  classical
  have h8 : 8 < T.ncard := ht.eight_lt
  have hk : VeryLargeK (Nat.card Γ) (maxOrbitLength G) :=
    veryLargeK_of_setting ϕ hset (by omega)
  intro u hu
  have hTu : TpointGen ϕ u ⊆ T := hu
  have hdef : tPointGen ϕ u = (TpointGen ϕ u).ncard := rfl
  have h1 : 1 ≤ tPointGen ϕ u := one_le_tPointGen ϕ hset hk u
  have h2 : tPointGen ϕ u < T.ncard := tPointGen_lt ϕ T hset hk ht htm u
  -- `T(u)` is a nonempty proper subset of `T`, so `u` is affected by `(G_T, ψ_T)`
  obtain ⟨p, hpT⟩ : (TpointGen ϕ u).Nonempty := by
    rw [← Set.ncard_pos (Set.toFinite _)]
    omega
  have hssub : TpointGen ϕ u ⊂ T := by
    refine ⟨hTu, fun hcon => ?_⟩
    have := Set.ncard_le_ncard hcon (Set.toFinite _)
    omega
  obtain ⟨q, hqT, hqn⟩ := Set.exists_of_ssubset hssub
  have hpTT : p ∈ T := hTu hpT
  have hpq : p ≠ q := fun h => hqn (h ▸ hpT)
  obtain ⟨c, hc, hcval⟩ := exists_alternating_move_to (T := T) (by omega) hpTT hqT hpq
  have haff : u ∈ (Stage.init ϕ x T).aff := by
    intro hle
    obtain ⟨σ, hσstab, hσval⟩ := hle hc
    have hσG : (σ : Equiv.Perm Ω) ∈ G := stabIn_le_top σ.2
    have hσu : (σ : Equiv.Perm Ω) u = u := by
      have := hσstab
      rw [SetLike.mem_coe, mem_stabilizer_iff] at this
      simpa [Subgroup.smul_def] using this
    have hstabG : (⟨(σ : Equiv.Perm Ω), hσG⟩ : G) ∈ stabilizer G u := by
      rw [mem_stabilizer_iff]
      simpa [Subgroup.smul_def] using hσu
    have hsand := (theorem_10_5_1_a_gen ϕ hset.giant hk u).1.2
    have himg : (ϕ ⟨(σ : Equiv.Perm Ω), hσG⟩ : Equiv.Perm Γ) '' TpointGen ϕ u
        = TpointGen ϕ u :=
      (hsand.2.2 ⟨⟨(σ : Equiv.Perm Ω), hσG⟩, hstabG, rfl⟩).2
    have hvalue : ((psiOn ϕ T (Stage.init ϕ x T).le σ ⟨p, hpTT⟩ : (T : Set Γ)) : Γ)
        = ϕ ⟨(σ : Equiv.Perm Ω), hσG⟩ p := rfl
    have hq' : q = ϕ ⟨(σ : Equiv.Perm Ω), hσG⟩ p := by
      rw [← hvalue, hσval]
      exact (congrArg Subtype.val hcval).symm
    exact hqn (by rw [hq', ← himg]; exact ⟨p, hpT, rfl⟩)
  -- the while loop runs at least once, and the windows only grow
  have h1le : 1 ≤ haltIndex ϕ x T := one_le_haltIndex hset.giant ht (by omega)
  exact stages_W_mono ϕ x T h1le haff

/-! ### The face is equivariant and determines the test set -/

/-- `Ω(T)^σ = Ω(T^{σ̄})`: the face is equivariant, by Eq. (54). -/
theorem face_image (hset : LocalCertSetting G ϕ)
    (hk : VeryLargeK (Nat.card Γ) (maxOrbitLength G)) (σ : G) :
    (σ : Equiv.Perm Ω) '' face ϕ T = face ϕ ((ϕ σ : Equiv.Perm Γ) '' T) := by
  have hT : ∀ u : Ω, TpointGen ϕ ((σ : Equiv.Perm Ω) u)
      = (ϕ σ : Equiv.Perm Γ) '' TpointGen ϕ u :=
    fun u => theorem_10_5_1_c_eq54_gen ϕ hset.giant hk u σ
  ext v
  constructor
  · rintro ⟨u, hu, rfl⟩
    have hsub : TpointGen ϕ u ⊆ T := hu
    show TpointGen ϕ ((σ : Equiv.Perm Ω) u) ⊆ (ϕ σ : Equiv.Perm Γ) '' T
    rw [hT u]
    exact Set.image_mono hsub
  · intro hv
    refine ⟨(σ : Equiv.Perm Ω)⁻¹ v, ?_, by simp⟩
    have hval : TpointGen ϕ v
        = (ϕ σ : Equiv.Perm Γ) '' TpointGen ϕ ((σ : Equiv.Perm Ω)⁻¹ v) := by
      rw [← hT ((σ : Equiv.Perm Ω)⁻¹ v)]
      simp
    have hsub : (ϕ σ : Equiv.Perm Γ) '' TpointGen ϕ ((σ : Equiv.Perm Ω)⁻¹ v)
        ⊆ (ϕ σ : Equiv.Perm Γ) '' T := by
      rw [← hval]; exact hv
    show TpointGen ϕ ((σ : Equiv.Perm Ω)⁻¹ v) ⊆ T
    exact (Set.image_subset_image_iff (ϕ σ : Equiv.Perm Γ).injective).1 hsub

/-- `A ↦ Ω(A)` is injective on the subsets of size `t`: every `t_Δ`-subset of `Γ` is a
label `T(u)` (`Babai.exists_TpointGen_eq`), and `1 ≤ t_Δ < t`, so a point of `A ∖ B` is
witnessed by a point of `Ω(A) ∖ Ω(B)`. -/
theorem face_injective (hset : LocalCertSetting G ϕ)
    (hk : VeryLargeK (Nat.card Γ) (maxOrbitLength G))
    (ht : LargeK T.ncard (Nat.card Ω)) (htm : 10 * T.ncard ≤ Nat.card Γ) [Nonempty Ω]
    {A B : Set Γ} (hA : A.ncard = T.ncard) (hB : B.ncard = T.ncard)
    (h : face ϕ A = face ϕ B) : A = B := by
  classical
  have key : ∀ C D : Set Γ, C.ncard = T.ncard → face ϕ C ⊆ face ϕ D → C ⊆ D := by
    intro C D hC hsub γ hγ
    obtain ⟨u₀⟩ := ‹Nonempty Ω›
    have hd1 : 1 ≤ tPointGen ϕ u₀ := one_le_tPointGen ϕ hset hk u₀
    have hdt : tPointGen ϕ u₀ < T.ncard := tPointGen_lt ϕ T hset hk ht htm u₀
    -- a `t_Δ`-subset of `C` containing `γ`
    have hCfin : C.Finite := Set.toFinite C
    have hγf : γ ∈ hCfin.toFinset := hCfin.mem_toFinset.2 hγ
    have hcardf : hCfin.toFinset.card = T.ncard := by
      rw [← Set.ncard_eq_toFinset_card C hCfin]; exact hC
    obtain ⟨Sf, hsub1, hsub2, hcard3⟩ := Finset.exists_subsuperset_card_eq
      (s := ({γ} : Finset Γ)) (t := hCfin.toFinset) (n := tPointGen ϕ u₀)
      (by simpa using hγf) (by simpa using hd1) (by omega)
    have hScard : ((Sf : Set Γ)).ncard = tPointGen ϕ u₀ := by
      rw [Set.ncard_coe_finset]; exact hcard3
    obtain ⟨y, -, hy⟩ := exists_TpointGen_eq ϕ hset.giant hk u₀ (S := (Sf : Set Γ)) hScard
    have hSC : (Sf : Set Γ) ⊆ C := by
      intro z hz
      exact hCfin.mem_toFinset.1 (hsub2 hz)
    have hyC : y ∈ face ϕ C := by
      show TpointGen ϕ y ⊆ C
      rw [hy]; exact hSC
    have hyD : TpointGen ϕ y ⊆ D := hsub hyC
    rw [hy] at hyD
    exact hyD (hsub1 (Finset.mem_singleton_self γ))
  exact Set.Subset.antisymm (key A B hA (le_of_eq h)) (key B A hB (le_of_eq h.symm))

/-- **Proposition 13.1.8**, §13.1.

> As in Theorem 13.1.3, let a test set be a subset `T ⊆ Γ` with `|T| = t` elements where
> `max{8, 2 + log₂ n} < t ≤ m/10`.  For all test sets `T` we have
> (i) `Ω(T) ⊆ W(T) ⊆ Ω`
> (ii) `W(T)` is invariant under `Aut_{G_T}(x)`
> (iii) if `T` is full then `W(T) = Aff(Aut^{W(T)}_{G_T}(x))`
> (iv) if `T` is full then `K(T)` fixes all elements of `Ω ∖ W(T)`
> (v) the assignment `T ↦ W(T)` is canonical.

Item (v) is `Babai.canonical_windowOut` (in `Workspace/LocalCertificates/Canonicity.lean`).

Item (iv) is printed as "`K(T)^T` fixes all elements of `Ω ∖ W(T)`" in both versions of the
paper; `K(T)^T ≤ S(T)` is a group of permutations of `T ⊆ Γ`, which cannot fix or move
elements of `Ω`, so the superscript is a typo for `K(T)`.  In
`Aff(Aut^{W(T)}_{G_T}(x))` of item (iii) the second argument of `Aff` is left implicit by
the paper; it is `ψ_T`, as everywhere else in the procedure. -/
theorem proposition_13_1_8 (hset : LocalCertSetting G ϕ)
    (ht : LargeK T.ncard (Nat.card Ω)) (htm : 10 * T.ncard ≤ Nat.card Γ) [Nonempty Ω] :
    (face ϕ T ⊆ windowOut ϕ x T ∧ windowOut ϕ x T ⊆ Set.univ) ∧
      IsInvariant (autG (bigGT ϕ T) x) (windowOut ϕ x T) ∧
      (IsFull ϕ x T →
        windowOut ϕ x T = {u | AffectedIn (psiOn ϕ T (outStage ϕ x T).le) u}) ∧
      (IsFull ϕ x T → ∀ σ ∈ certK ϕ x T, ∀ u ∉ windowOut ϕ x T, σ u = u) := by
  refine ⟨⟨face_subset_windowOut ϕ x T hset ht htm, Set.subset_univ _⟩, ?_, ?_, ?_⟩
  · -- (ii) `Aut_{G_T}(x) ≤ H(W)` and `W` is `H(W)`-invariant
    intro σ hσ
    refine (outStage ϕ x T).inv σ ?_
    rw [autG_bigGT_eq ϕ x T] at hσ
    exact autStab_le_outStage_H ϕ x T hσ
  · -- (iii) on line 07 we have `Aff(H(W), ψ_T) = W`
    intro hfull
    have h07 : isFullOut ϕ x T := le_trans hfull (imgOn_mono ϕ T (autStab_le_outStage_H ϕ x T))
    exact ((outStage ϕ x T).aff_eq_of_not_loopCond (not_loopCond_outStage ϕ x T) h07).symm
  · -- (iv) `K(T)` is the pointwise stabilizer of `Ω ∖ W(T)`
    intro _ σ hσ u hu
    exact (mem_certK_iff.1 hσ).2 u hu

end Babai
