/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 13.1: Claims 13.1.6 and 13.1.7, Proposition 13.1.8, Theorem 13.1.3.
-/
import Workspace.LocalCertificates.Procedure

/-!
# §13.1 Correctness of Procedure LocalCertificates

Claim 13.1.6 (line 08 produces a certificate of fullness), Claim 13.1.7 (line 10 produces
a certificate of non-fullness), the fact that the while loop is executed at least once,
Proposition 13.1.8 (the properties of `W(T)`), and Theorem 13.1.3 itself.

The call accounting of Theorem 13.1.3 (`≤ t!n²` String Isomorphism instances on domains
of size `≤ n/t`) is in `Workspace/LocalCertificates/Calls.lean`, and the canonicity of the
two families is in `Workspace/LocalCertificates/Canonicity.lean`.
-/

namespace Babai

open MulAction Equiv Equiv.Perm
open scoped Classical

variable {Ω Γ Λ : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype Γ] [DecidableEq Γ]
  {G : Subgroup (Equiv.Perm Ω)}

/-! ### Elementary lemmas -/

/-- `L^T` grows with `L`. -/
theorem imgOn_mono {L L' : Subgroup (Equiv.Perm Ω)} (ϕ : G →* Equiv.Perm Γ) (T : Set Γ)
    {hL : L ≤ bigGT ϕ T} {hL' : L' ≤ bigGT ϕ T} (h : L ≤ L') :
    imgOn ϕ T hL ≤ imgOn ϕ T hL' := by
  rintro g ⟨⟨σ, hσ⟩, rfl⟩
  exact ⟨⟨σ, h hσ⟩, rfl⟩

/-- The hypothesis `k > max{8, 2 + log₂ n}` only gets weaker as `n` decreases. -/
theorem LargeK.mono_card {k n n' : ℕ} (h : n' ≤ n) (hk : LargeK k n) : LargeK k n' := by
  refine lt_of_le_of_lt (max_le_max (le_refl 8) ?_) hk
  have hlog : Real.logb 2 (n' : ℝ) ≤ Real.logb 2 (n : ℝ) := by
    rcases Nat.eq_zero_or_pos n' with rfl | hn'
    · simp only [Nat.cast_zero, Real.logb_zero]
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      · exact Real.logb_nonneg (by norm_num) (by exact_mod_cast hn)
    · exact Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast hn') (by exact_mod_cast h)
  linarith

theorem maxOrbitLength_le_card (H : Subgroup (Equiv.Perm Ω)) :
    maxOrbitLength H ≤ Nat.card Ω := by
  rcases isEmpty_or_nonempty Ω with hΩ | hΩ
  · have hempty : {m | ∃ u : Ω, Nat.card (orbit H u) = m} = ∅ := by
      ext m
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨u, -⟩
      exact IsEmpty.false u
    simp [maxOrbitLength, hempty]
  · refine csSup_le ⟨Nat.card (orbit H (Classical.arbitrary Ω)), ⟨_, rfl⟩⟩ ?_
    rintro m ⟨u, rfl⟩
    have hsub : (orbit H u : Set Ω) ⊆ Set.univ := Set.subset_univ _
    have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
    have h1 : Nat.card (orbit H u) = (orbit H u : Set Ω).ncard := Nat.card_coe_set_eq _
    rw [h1, Set.ncard_univ] at *
    exact hle

/-- `Aut_{G_T}(x) = Aut_G(x)_T`: an automorphism of `x` normalizing `T` is the same thing
as an automorphism of `x` inside `G_T`. -/
theorem autG_bigGT_eq (ϕ : G →* Equiv.Perm Γ) (x : Ω → Λ) (T : Set Γ) :
    autG (bigGT ϕ T) x = stabIn ϕ (autG_le G x) T := by
  ext σ
  constructor
  · intro hσ
    have hmem : σ ∈ bigGT ϕ T := hσ.1
    obtain ⟨hσG, himg⟩ := mem_stabIn.1 hmem
    exact mem_stabIn.2 ⟨⟨hσG, hσ.2⟩, himg⟩
  · intro hσ
    obtain ⟨hσa, himg⟩ := mem_stabIn.1 hσ
    exact ⟨mem_stabIn.2 ⟨hσa.1, himg⟩, hσa.2⟩

variable (ϕ : G →* Equiv.Perm Γ) (x : Ω → Λ) (T : Set Γ)

/-- "the relation `Aut_G(x)_T^T ≤ H(W)` is an invariant of the process" (proof of Claim
13.1.7): `Aut_G(x)_T` is contained in every group of the loop. -/
theorem autStab_le_stages_H (i : ℕ) :
    stabIn ϕ (autG_le G x) T ≤ (stages ϕ x T i).H := by
  induction i with
  | zero =>
      intro σ hσ
      obtain ⟨hσa, himg⟩ := mem_stabIn.1 hσ
      exact mem_stabIn.2 ⟨hσa.1, himg⟩
  | succ i ih =>
      intro σ hσ
      have hmem := ih hσ
      obtain ⟨hσa, -⟩ := mem_stabIn.1 hσ
      exact ⟨hmem, fun u _ => hσa.2 u (Set.mem_univ u)⟩

theorem autStab_le_outStage_H :
    stabIn ϕ (autG_le G x) T ≤ (outStage ϕ x T).H :=
  autStab_le_stages_H ϕ x T _

/-- The windows grow along the loop. -/
theorem stages_W_mono {i j : ℕ} (h : i ≤ j) :
    (stages ϕ x T i).W ⊆ (stages ϕ x T j).W := by
  induction j with
  | zero => simp_all
  | succ j ih =>
      rcases Nat.lt_or_ge i (j + 1) with hlt | hge
      · exact le_trans (ih (by omega)) (stages ϕ x T j).W_subset_step_W
      · have : i = j + 1 := by omega
        subst this
        exact le_refl _

/-! ### Claim 13.1.6 -/

variable {ϕ x T}

theorem certK_le_H : certK ϕ x T ≤ (outStage ϕ x T).H := fun _ hσ => hσ.1

theorem certK_le_bigGT : certK ϕ x T ≤ bigGT ϕ T :=
  le_trans certK_le_H (outStage ϕ x T).le

/-- Every element of `K(T)` fixes `Ω ∖ W(T)` pointwise, and respects `x` on `W(T)`. -/
theorem mem_certK_iff {σ : Equiv.Perm Ω} :
    σ ∈ certK ϕ x T ↔ σ ∈ (outStage ϕ x T).H ∧ ∀ u ∉ windowOut ϕ x T, σ u = u := by
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, fun u hu => h2 u hu⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, fun u hu => h2 u hu⟩

/-- **Claim 13.1.6**, §13.1, first half.

> On line 08, `K(T)^T ≥ A(T)` …

> `K(T)^T ≥ A(T)` is the crucial consequence of Theorem 10.3.5, applied to the giant
> representation `ψ̄_T : H(W_old) → S(T)`.  (`ψ̄_T` denotes the restriction of `ψ_T` to
> `H(W_old)`.)

The set of points *not* affected by `(H(W), ψ_T)` is exactly `W̄ = Ω ∖ W(T)`, because the
loop exited on line 02 with `Aff(H(W), ψ_T) ⊆ W` and the invariant gives the reverse
inclusion; so Theorem 10.3.5 applies to `H(W)_(W̄) = K(T)`. -/
theorem claim_13_1_6_giant (ht : LargeK T.ncard (Nat.card Ω))
    (hline07 : isFullOut ϕ x T) :
    alternatingGroup T ≤ imgOn ϕ T (certK_le_bigGT (ϕ := ϕ) (x := x) (T := T)) := by
  set s := outStage ϕ x T with hs
  -- the unaffected set is the complement of the window
  have haff : s.aff = s.W := s.aff_eq_of_not_loopCond (not_loopCond_outStage ϕ x T) hline07
  have hun : unaffectedIn (psiOn ϕ T s.le) = (windowOut ϕ x T)ᶜ := by
    ext u
    simp only [unaffectedIn, Set.mem_setOf_eq, Set.mem_compl_iff, windowOut, ← hs]
    rw [← haff]
    rfl
  -- Theorem 10.3.5 for `ψ̄_T : H(W) → S(T)`
  have hgiant : IsGiantRep (psiOn ϕ T s.le) := hline07
  have hcard : Nat.card T = T.ncard := Nat.card_coe_set_eq T
  have hk : LargeK (Nat.card T) (maxOrbitLength s.H) := by
    rw [hcard]
    exact LargeK.mono_card (maxOrbitLength_le_card s.H) ht
  have h := theorem_10_3_5_gen (psiOn ϕ T s.le) hgiant hk
  rw [hun] at h
  -- `(H(W)_(W̄))^{ψ_T} = K(T)^T`
  refine le_trans h ?_
  rintro g ⟨⟨σ, hσH⟩, hσ, rfl⟩
  refine ⟨⟨(σ : Equiv.Perm Ω), ?_⟩, rfl⟩
  exact ⟨hσH, fun u hu => (mem_pointwiseStab.1 hσ) u hu⟩

/-- **Claim 13.1.6**, §13.1, second half.

> … and `K(T) ≤ Aut_G(x)`.

> To show that `K(T) ≤ Aut_G(x)` let `σ ∈ K(T)` and `u ∈ Ω`.  We need to show that
> `x(u^σ) = x(u)`.  If `u ∈ W` then this follows because `σ ∈ H(W) = Aut^W_G(x)`.  If
> `u ∈ W̄` then `u^σ = u`. -/
theorem claim_13_1_6_le_aut : certK ϕ x T ≤ autG (bigGT ϕ T) x := by
  intro σ hσ
  obtain ⟨hσH, hfix⟩ := mem_certK_iff.1 hσ
  refine ⟨(outStage ϕ x T).le hσH, fun u _ => ?_⟩
  by_cases hu : u ∈ windowOut ϕ x T
  · -- `σ ∈ H(W) = Aut^W_{G_T}(x)`
    have hmemset : σ ∈ wAut (outStage ϕ x T).W (bigGT ϕ T : Set (Equiv.Perm Ω)) x := by
      rw [← (outStage ϕ x T).isAut]; exact hσH
    exact (mem_wAut.1 hmemset).2 u hu
  · rw [hfix u hu]

/-- **Claim 13.1.6**, §13.1.

> On line 08, `K(T)^T ≥ A(T)` and `K(T) ≤ Aut_G(x)`.  In particular, `T` is full. -/
theorem claim_13_1_6 (ht : LargeK T.ncard (Nat.card Ω)) (hline07 : isFullOut ϕ x T) :
    IsFullnessCertificate ϕ x T (certK ϕ x T) ∧ IsFull ϕ x T := by
  have hcert : IsFullnessCertificate ϕ x T (certK ϕ x T) :=
    { le_stab := certK_le_bigGT
      giant := claim_13_1_6_giant ht hline07
      le_aut := claim_13_1_6_le_aut }
  refine ⟨hcert, ?_⟩
  -- "In particular, `T` is full": `A(T) ≤ K(T)^T ≤ Aut_G(x)_T^T`
  refine le_trans hcert.giant ?_
  refine imgOn_mono ϕ T ?_
  rw [← autG_bigGT_eq ϕ x T]
  exact hcert.le_aut

/-! ### Claim 13.1.7 -/

/-- **Claim 13.1.7**, §13.1.

> If `T` is not full then we reach line 10 with `M(T) ≱ A(T)` and `Aut_G(x)_T^T ≤ M(T)`.

> We reach line 10 by Claim 13.1.6.  We then have `Aut_G(x)_T^T ≤ M(T)` because the
> relation `Aut_G(x)_T^T ≤ H(W)` is an invariant of the process. -/
theorem claim_13_1_7 (ht : LargeK T.ncard (Nat.card Ω)) (hnot : ¬ IsFull ϕ x T) :
    ¬ isFullOut ϕ x T ∧ IsNonFullnessCertificate ϕ x T (certM ϕ x T) := by
  have hline : ¬ isFullOut ϕ x T := fun h => hnot (claim_13_1_6 ht h).2
  refine ⟨hline, ⟨hline, ?_⟩⟩
  exact imgOn_mono ϕ T (autStab_le_outStage_H ϕ x T)

/-! ### The while loop is executed at least once -/

/-- §13.1, the Justification.

> We also note that the while loop will be executed at least once (by the comment on line
> 01).

Line 01 sets `W := ∅` and `H(W) = G_T`.  The loop condition then holds: `G_T^T = S(T)`
because `ψ_T` is an epimorphism for `|T| ≤ m - 2` (Notation 13.1.1), and
`Aff(G_T, ψ_T) ⊄ ∅` because `Aff(G_T, ψ_T)` cannot be empty by Theorem 10.3.5 ("By the
second round `W ≠ ∅` because `Aff(G_T, ψ_T)` cannot be empty (by the Unaffected Stabilizer
Theorem)"). -/
theorem one_le_haltIndex (hϕ : IsGiantRep ϕ) (ht : LargeK T.ncard (Nat.card Ω))
    (htm : T.ncard + 2 ≤ Nat.card Γ) [Nonempty Ω] :
    1 ≤ haltIndex ϕ x T := by
  rcases Nat.eq_zero_or_pos (haltIndex ϕ x T) with h0 | hpos
  swap
  · exact hpos
  exfalso
  have hnot : ¬ (Stage.init ϕ x T).LoopCond := by
    have h := not_loopCond_outStage ϕ x T
    have he : outStage ϕ x T = Stage.init ϕ x T := by
      rw [outStage, h0, stages_zero]
    rwa [he] at h
  -- the first half of the loop condition: `ψ_T` is onto, so `G_T^T = S(T) ≥ A(T)`
  have hsurj : Function.Surjective (psi ϕ T) := psi_surjective ϕ hϕ htm
  have hfull : alternatingGroup T ≤ imgOn ϕ T (Stage.init ϕ x T).le := by
    intro g _
    obtain ⟨σ, rfl⟩ := hsurj g
    exact ⟨σ, rfl⟩
  -- the second half: the affected set is nonempty
  have hcard : Nat.card T = T.ncard := Nat.card_coe_set_eq T
  have hne : ((Stage.init ϕ x T).aff).Nonempty := by
    by_contra hcon
    rw [Set.not_nonempty_iff_eq_empty] at hcon
    -- every point is unaffected, so Theorem 10.3.5 gives `A(T) ≤ (G_T)_(Ω)^{ψ_T} = 1`
    have hgiant : IsGiantRep (psiOn ϕ T (Stage.init ϕ x T).le) := hfull
    have hk : LargeK (Nat.card T) (maxOrbitLength (Stage.init ϕ x T).H) := by
      rw [hcard]
      exact LargeK.mono_card (maxOrbitLength_le_card _) ht
    have h := theorem_10_3_5_gen (psiOn ϕ T (Stage.init ϕ x T).le) hgiant hk
    have huniv : unaffectedIn (psiOn ϕ T (Stage.init ϕ x T).le) = Set.univ := by
      ext u
      simp only [unaffectedIn, Set.mem_setOf_eq, Set.mem_univ, iff_true]
      intro hu
      have : u ∈ (Stage.init ϕ x T).aff := hu
      rw [hcon] at this
      exact this
    rw [huniv] at h
    -- the pointwise stabilizer of all of `Ω` is trivial
    have htriv : pointwiseStab (Stage.init ϕ x T).H (Set.univ : Set Ω) = ⊥ := by
      refine (Subgroup.eq_bot_iff_forall _).2 fun σ hσ => ?_
      have := mem_pointwiseStab.1 hσ
      refine Subtype.ext (Equiv.ext fun u => ?_)
      exact this u (Set.mem_univ u)
    rw [htriv, Subgroup.map_bot] at h
    -- but `A(T)` is nontrivial, as `|T| ≥ 9`
    have h8 : 8 < T.ncard := ht.eight_lt
    have hTcard : 9 ≤ Nat.card T := by rw [hcard]; omega
    haveI : Nontrivial (alternatingGroup (T : Set Γ)) := by
      refine alternatingGroup.nontrivial_of_three_le_card ?_
      have : Nat.card (T : Set Γ) = T.ncard := hcard
      rw [Nat.card_eq_fintype_card] at this
      omega
    obtain ⟨g, hg⟩ := exists_ne (1 : alternatingGroup (T : Set Γ))
    have hgbot : (g : Equiv.Perm (T : Set Γ)) ∈ (⊥ : Subgroup (Equiv.Perm (T : Set Γ))) :=
      h g.2
    rw [Subgroup.mem_bot] at hgbot
    exact hg (Subtype.ext hgbot)
  refine hnot ⟨hfull, ?_⟩
  intro hsub
  obtain ⟨u, hu⟩ := hne
  exact absurd (hsub hu) (by simp [Stage.init])

/-! ### Theorem 13.1.3 -/

/-- **Theorem 13.1.3** (Local certificates), §13.1.

> Let `T ⊆ Γ` where `|T| = t`.  We refer to `T` as our "test set."  Assume
> `max{8, 2 + log₂ n} < t ≤ m/10`.  By making `≤ t!n²` calls to String Isomorphism
> problems on domains of size `≤ n/t` and performing `t! poly(n)` computation we can
> decide whether `T` is full and
> (a) if `T` is full, find a certificate `K(T) ≤ Aut_G(x)` of fullness;
> (b) if `T` is not full, find a certificate `M(T) ≤ S(T)` of non-fullness.

The *decision* is the test on line 07 (`Babai.isFullOut`), the certificates are the
outputs `K(T)` (`Babai.certK`) and `M(T)` (`Babai.certM`) of Procedure LocalCertificates.
The number of String Isomorphism instances and the size of their domains are
`Babai.card_allInstances_le` and `Babai.instance_window_le` in
`Workspace/LocalCertificates/Calls.lean`; the canonicity of the two families is
`Workspace/LocalCertificates/Canonicity.lean`.  The `t! poly(n)` running time is
covered inside the RAM proof of Theorem 1.1.1 (`Algo.theorem_1_1_1`) and not stated as a
separate RAM theorem. -/
theorem theorem_13_1_3 (ht : LargeK T.ncard (Nat.card Ω))
    (htm : 10 * T.ncard ≤ Nat.card Γ) :
    (isFullOut ϕ x T ↔ IsFull ϕ x T) ∧
      (IsFull ϕ x T → IsFullnessCertificate ϕ x T (certK ϕ x T)) ∧
      (¬ IsFull ϕ x T → IsNonFullnessCertificate ϕ x T (certM ϕ x T)) := by
  -- the decision of line 07 is correct: `≥` follows from Claim 13.1.6, and `≤` because
  -- `Aut_G(x)_T ≤ H(W)` throughout the process (the invariant of Claim 13.1.7)
  have hdec : isFullOut ϕ x T ↔ IsFull ϕ x T :=
    ⟨fun h => (claim_13_1_6 ht h).2,
      fun h => le_trans h (imgOn_mono ϕ T (autStab_le_outStage_H ϕ x T))⟩
  refine ⟨hdec, ?_, ?_⟩
  · intro hfull
    exact (claim_13_1_6 ht (hdec.2 hfull)).1
  · intro hnot
    exact (claim_13_1_7 ht hnot).2

/-! ### The hypotheses of Theorem 13.1.3 are satisfiable

A self-audit of the numerical hypotheses: with `n = m = 90` and `t = 9` we have
`max{8, 2 + log₂ n} = 2 + log₂ 90 < 9 = t`, `10t = 90 ≤ 90 = m` (`t ≤ m/10`) and
`10 log₂ n ≤ 90 = m`, and `G = S(Ω) = S(Γ)` with `ϕ = id` is a transitive group with a
giant representation. -/
section Satisfiable

private def T₉ : Set (Fin 90) := ↑((Finset.univ : Finset (Fin 90)).filter fun i => i.val < 9)

private theorem ncard_T₉ : T₉.ncard = 9 := by
  rw [T₉, Set.ncard_coe_finset]
  decide

private theorem logb_90_lt_seven : Real.logb 2 90 < 7 := by
  have h : Real.logb 2 90 < Real.logb 2 128 :=
    Real.logb_lt_logb (by norm_num) (by norm_num) (by norm_num)
  have h2 : Real.logb 2 128 = 7 := by
    rw [show (128 : ℝ) = 2 ^ (7 : ℕ) by norm_num, Real.logb_pow, Real.logb_self_eq_one] <;>
      norm_num
  linarith

/-- The hypotheses of Theorem 13.1.3 (and the standing hypotheses of §13.1) can all hold
at once. -/
example : ∃ (G : Subgroup (Equiv.Perm (Fin 90))) (ϕ : G →* Equiv.Perm (Fin 90))
    (T : Set (Fin 90)),
    LocalCertSetting G ϕ ∧ T.ncard = 9 ∧ LargeK T.ncard (Nat.card (Fin 90)) ∧
      10 * T.ncard ≤ Nat.card (Fin 90) := by
  refine ⟨⊤, (⊤ : Subgroup (Equiv.Perm (Fin 90))).subtype, T₉, ⟨?_, ?_, ?_⟩, ncard_T₉, ?_, ?_⟩
  · -- `S(Ω)` is transitive: the orbit of `0` is everything
    refine ⟨0, ?_⟩
    ext b
    refine ⟨fun _ => trivial, fun _ => ?_⟩
    exact mem_orbit_iff.2 ⟨⟨Equiv.swap 0 b, Subgroup.mem_top _⟩, by simp [Subgroup.smul_def]⟩
  · -- `ϕ = id` is a giant representation
    intro g _
    exact ⟨⟨g, Subgroup.mem_top _⟩, rfl⟩
  · -- `10 log₂ n ≤ m`
    have := logb_90_lt_seven
    rw [Nat.card_eq_fintype_card, Fintype.card_fin]
    push_cast
    linarith
  · -- `max{8, 2 + log₂ n} < t`
    rw [LargeK, ncard_T₉, Nat.card_eq_fintype_card, Fintype.card_fin]
    have := logb_90_lt_seven
    refine max_lt (by norm_num) ?_
    push_cast
    linarith
  · rw [ncard_T₉, Nat.card_eq_fintype_card, Fintype.card_fin]

end Satisfiable

end Babai
