/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 11.2 (Johnson groups are the only barrier).
-/
import Workspace.Luks.Framework
import Workspace.Cited.Luks
import Workspace.Luks.CoordinateBlocks
import Workspace.Luks.JohnsonFacts
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# §11.2 Johnson groups are the only barrier

> The barriers to efficient application of Luks's reductions are large primitive groups
> involved in `G`.  The following result reduces the Luks barriers to the class of Johnson
> groups at a multiplicative cost of `≤ n`.
-/

namespace Babai

open MulAction Equiv Equiv.Perm

variable {Ω : Type*}

/-! ### Minimal systems of imprimitivity -/

/-- §11.2 (the sentence after the proof of Theorem 11.1.9): for a minimal system of
imprimitivity, "`Ḡ` is a primitive group".

The proof: for a block of imprimitivity `𝒞 ⊆ ℬ` of the block action, the union `⋃ 𝒞` is a
block of imprimitivity of `G` inside `Δ` (using that the blocks of `ℬ` are pairwise
disjoint), so by maximality it is a single block or all of `Δ`, i.e. `𝒞` is a singleton or
all of `ℬ`; and `|Ḡ| ≥ 2` because `ℬ` has at least two blocks and `G` is transitive on
them.

The hypothesis `[Finite Ω]` is the paper's standing assumption "All groups in this paper
are finite" (§2.2): the paper's primitivity asks for `|Ḡ| ≥ 2`, and `Nat.card` of an
infinite group is `0`, so without finiteness the conclusion would fail for a purely
Lean-side reason. -/
theorem IsMinimalSystemOfImprimitivity.isPrimitive_onBlocks [Finite Ω]
    {G : Subgroup (Equiv.Perm Ω)}
    {Δ : Set Ω} {ℬ : Set (Set Ω)} (h : IsMinimalSystemOfImprimitivity G Δ ℬ) :
    IsPrimitive (onBlocks G ℬ h.permutes) := by
  classical
  haveI : Finite ℬ := Set.Finite.to_subtype (Set.toFinite ℬ)
  constructor
  · -- `|Ḡ| ≥ 2`: two distinct blocks and transitivity on the blocks give a nonidentity
    -- element of `Ḡ`
    obtain ⟨B₁, hB₁, B₂, hB₂, hne⟩ := (Set.one_lt_ncard (Set.toFinite ℬ)).1 h.two_blocks
    obtain ⟨σ, hσ, hσB⟩ := h.transitiveOnBlocks B₁ hB₁ B₂ hB₂
    have hntriv : Nontrivial (onBlocks G ℬ h.permutes) := by
      refine ⟨⟨⟨blockHom G ℬ h.permutes ⟨σ, hσ⟩, ⟨⟨σ, hσ⟩, rfl⟩⟩, 1, ?_⟩⟩
      intro hcon
      have := congrArg
        (fun g : (onBlocks G ℬ h.permutes) =>
          (((g : Equiv.Perm ℬ) ⟨B₁, hB₁⟩ : ℬ) : Set Ω)) hcon
      simp only [blockHom_apply_coe, OneMemClass.coe_one, Equiv.Perm.coe_one, id_eq] at this
      exact hne (hσB.symm.trans this).symm
    exact Finite.one_lt_card_iff_nontrivial.2 hntriv
  · -- a block of `Ḡ` is a singleton or everything
    rintro 𝒞 ⟨hne𝒞, hblock⟩
    obtain ⟨B₀, hB₀⟩ := hne𝒞
    -- the union of the blocks in `𝒞` is a block of imprimitivity of `G` inside `Δ`
    obtain ⟨C, hCdef⟩ : ∃ C : Set Ω, C = {x : Ω | ∃ B ∈ 𝒞, x ∈ (B : Set Ω)} := ⟨_, rfl⟩
    have hmemC : ∀ x : Ω, x ∈ C ↔ ∃ B ∈ 𝒞, x ∈ (B : Set Ω) := by
      intro x; rw [hCdef]; exact Iff.rfl
    have hsubΔ : ∀ B : ℬ, (B : Set Ω) ⊆ Δ := by
      intro B x hx
      rw [← h.covers]
      exact ⟨(B : Set Ω), B.2, hx⟩
    have hCsub : C ⊆ Δ := by
      intro x hx
      obtain ⟨B, -, hxB⟩ := (hmemC x).1 hx
      exact hsubΔ B hxB
    have hB₀C : (B₀ : Set Ω) ⊆ C := fun x hx => (hmemC x).2 ⟨B₀, hB₀, hx⟩
    -- distinct blocks of `ℬ` sharing a point are equal
    have hblockeq : ∀ B B' : ℬ, ∀ x : Ω, x ∈ (B : Set Ω) → x ∈ (B' : Set Ω) → B = B' := by
      intro B B' x hxB hxB'
      by_contra hne
      have hdisj := h.pairwiseDisjoint (B : Set Ω) B.2 (B' : Set Ω) B'.2
        (fun hcon => hne (Subtype.ext hcon))
      exact (Set.disjoint_left.1 hdisj hxB) hxB'
    have hCblock : IsBlockOfImprimitivity G C := by
      refine ⟨?_, fun σ hσ => ?_⟩
      · obtain ⟨z, hz⟩ := h.nonempty (B₀ : Set Ω) B₀.2
        exact ⟨z, (hmemC z).2 ⟨B₀, hB₀, hz⟩⟩
      · have himg : (σ : Equiv.Perm Ω) '' C =
            {x : Ω | ∃ B ∈ (blockHom G ℬ h.permutes ⟨σ, hσ⟩) '' 𝒞, x ∈ (B : Set Ω)} := by
          ext x
          constructor
          · rintro ⟨y, hy, rfl⟩
            obtain ⟨B, hB, hyB⟩ := (hmemC y).1 hy
            refine ⟨blockHom G ℬ h.permutes ⟨σ, hσ⟩ B, ⟨B, hB, rfl⟩, ?_⟩
            rw [blockHom_apply_coe]
            exact ⟨y, hyB, rfl⟩
          · rintro ⟨_, ⟨B, hB, rfl⟩, hx⟩
            rw [blockHom_apply_coe] at hx
            obtain ⟨y, hyB, rfl⟩ := hx
            exact ⟨y, (hmemC y).2 ⟨B, hB, hyB⟩, rfl⟩
        rcases hblock (blockHom G ℬ h.permutes ⟨σ, hσ⟩) ⟨⟨σ, hσ⟩, rfl⟩ with heq | hdisj
        · left
          rw [himg, heq, ← hCdef]
        · right
          rw [himg]
          ext x
          simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false,
            not_and]
          rintro ⟨B, hB, hxB⟩ hxC
          obtain ⟨B', hB', hxB'⟩ := (hmemC x).1 hxC
          have hBB' : B = B' := hblockeq B B' x hxB hxB'
          have hmem : B ∈ ((blockHom G ℬ h.permutes ⟨σ, hσ⟩) '' 𝒞) ∩ 𝒞 :=
            ⟨hB, hBB' ▸ hB'⟩
          rw [hdisj] at hmem
          exact hmem
    -- maximality of the blocks of `ℬ`
    rcases h.blocks_maximal (B₀ : Set Ω) B₀.2 C hCsub hB₀C hCblock with hCB₀ | hCΔ
    · -- `C` is a single block, so `𝒞 = {B₀}`
      right
      refine ⟨B₀, ?_⟩
      ext B
      simp only [Set.mem_singleton_iff]
      constructor
      · intro hB
        obtain ⟨z, hz⟩ := h.nonempty (B : Set Ω) B.2
        have hzC : z ∈ C := (hmemC z).2 ⟨B, hB, hz⟩
        rw [hCB₀] at hzC
        exact hblockeq B B₀ z hz hzC
      · rintro rfl
        exact hB₀
    · -- `C` is all of `Δ`, so `𝒞` is all of `ℬ`
      left
      ext B
      simp only [Set.mem_univ, iff_true]
      obtain ⟨z, hz⟩ := h.nonempty (B : Set Ω) B.2
      have hzΔ : z ∈ Δ := hsubΔ B hz
      rw [← hCΔ] at hzΔ
      obtain ⟨B', hB', hzB'⟩ := (hmemC z).1 hzΔ
      exact (hblockeq B B' z hz hzB') ▸ hB'

/-! ### Elementary binomial bounds

These are the bounds behind the proof of Proposition 11.2.4; the first of them is also
what shows that the conclusion of Theorem 11.2.1 has content (a Johnson group `A_k^(t)`
with `1 ≤ t` and `2t < k` acts on `C(k,t) ≥ k ≥ 3` blocks). -/

/-- `2^t ≤ C(2t, t)`: the elementary bound behind "`(k/t)^{ts} ≥ 2^{ts}`" in the proof of
Proposition 11.2.4. -/
theorem two_pow_le_centralBinom (t : ℕ) : 2 ^ t ≤ Nat.centralBinom t := by
  induction t with
  | zero => simp [Nat.centralBinom]
  | succ n ih =>
    have h := Nat.succ_mul_centralBinom_succ n
    have h1 : (n + 1) * 2 ^ (n + 1) ≤ (n + 1) * Nat.centralBinom (n + 1) := by
      rw [h]
      calc (n + 1) * 2 ^ (n + 1) = 2 * (n + 1) * 2 ^ n := by ring
        _ ≤ 2 * (2 * n + 1) * 2 ^ n := by
            refine Nat.mul_le_mul_right _ ?_
            omega
        _ ≤ 2 * (2 * n + 1) * Nat.centralBinom n := Nat.mul_le_mul_left _ ih
    exact Nat.le_of_mul_le_mul_left h1 (by omega)

/-- `2^t ≤ C(k,t)` whenever `k ≥ 2t`. -/
theorem two_pow_le_choose {k t : ℕ} (h : 2 * t ≤ k) : 2 ^ t ≤ k.choose t :=
  le_trans (two_pow_le_centralBinom t) (Nat.choose_le_choose t h)

/-- `k ≤ C(k,t)` for `1 ≤ t` and `2t < k`. -/
theorem self_le_choose {k t : ℕ} (ht : 1 ≤ t) (hk : 2 * t < k) : k ≤ k.choose t := by
  have hhalf : t ≤ k / 2 := by omega
  have key : ∀ m : ℕ, m + 1 ≤ t → k.choose 1 ≤ k.choose (m + 1) := by
    intro m
    induction m with
    | zero => intro _; exact le_rfl
    | succ p ih =>
      intro hp
      exact le_trans (ih (by omega)) (Nat.choose_le_succ_of_lt_half_left (by omega))
  have h := key (t - 1) (by omega)
  rwa [Nat.choose_one_right, Nat.sub_add_cancel ht] at h

/-! ### Theorem 11.2.1 -/

universe u


/-! ### Cameron groups with `s = 1` -/

/-- §11.2, after Definition 11.2.2:

> Note that for `k ≥ 5` the Johnson groups `S_k^(t)` and `A_k^(t)` are exactly the Cameron
> groups with `s = 1`.

The paper asserts this without proof and never uses it, so it is recorded as a statement
only.

The Johnson groups are meant in the range of §2.2.1, "the Johnson groups `S_k^(t)` and
`A_k^(t)` for `t ≥ 1` and `k ≥ 2t + 1`", which is also the range of the parameters in
Definition 11.2.2.  Outside it the sentence is false for a reason that has nothing to do
with the paper: for `t = 0` the domain `Fin k choose 0` is a single point, so *every*
subgroup equals `S_k^(0) = A_k^(0) = 1` while no group is a Cameron group with `t = 0`
(Definition 11.2.2 asks `1 ≤ t`); and for `k = 6`, `t = 3` the group `S_6^(3)` is not a
Cameron group with these parameters either (Definition 11.2.2 asks `2t < k`).  Carrying
the two constraints is therefore a matter of stating the paper's sentence in the range it
is about. -/
def Johnson_eq_Cameron_s_one_statement : Prop :=
  ∀ (k t : ℕ), 5 ≤ k → 1 ≤ t → 2 * t < k →
    (∀ G : Subgroup (Equiv.Perm (binom (Fin k) t)),
      IsCameronGroup G 1 t k ↔ (G = JohnsonS k t ∨ G = JohnsonA k t))

/-! ### Propositions 11.2.4 and 11.2.5 -/

/-- §11.2, Proposition 11.2.4, the first inequality of the proof: `n = C(k,t)^s ≥ 2^{ts}`. -/
theorem two_pow_mul_le_card [Fintype Ω] {G : Subgroup (Equiv.Perm Ω)} {s t k : ℕ}
    (h : IsCameronGroup G s t k) : 2 ^ (t * s) ≤ Fintype.card Ω := by
  obtain ⟨-, -, -, hk2t, hn, -⟩ := h
  rw [hn, pow_mul]
  exact Nat.pow_le_pow_left (two_pow_le_choose (by omega)) s

/-- §11.2, Proposition 11.2.4, the second inequality of the proof: `n = C(k,t)^s ≥ k^s`. -/
theorem pow_le_card [Fintype Ω] {G : Subgroup (Equiv.Perm Ω)} {s t k : ℕ}
    (h : IsCameronGroup G s t k) : k ^ s ≤ Fintype.card Ω := by
  obtain ⟨-, ht, -, hk2t, hn, -⟩ := h
  rw [hn]
  exact Nat.pow_le_pow_left (self_le_choose ht hk2t) s

/-- §11.2, **Proposition 11.2.4**.

> If `G ≤ S_n` is a Cameron group with parameters `k, t, s` then `ts ≤ log₂ n`.  Moreover,
> `s ≤ log n / log k ≤ log n / log 5`.
>
> *Proof.* We have `n = C(k,t)^s ≥ (k/t)^{ts} ≥ 2^{ts}`.  Moreover, `n = C(k,t)^s ≥ k^s`. -/
theorem Proposition_11_2_4 [Fintype Ω] {G : Subgroup (Equiv.Perm Ω)} {s t k : ℕ}
    (h : IsCameronGroup G s t k) :
    ((t * s : ℕ) : ℝ) ≤ Real.logb 2 (Fintype.card Ω) ∧
      (s : ℝ) ≤ Real.log (Fintype.card Ω) / Real.log k ∧
        Real.log (Fintype.card Ω) / Real.log k ≤
          Real.log (Fintype.card Ω) / Real.log 5 := by
  have hk5 : 5 ≤ k := by
    obtain ⟨-, -, hmax, -⟩ := h
    omega
  have h2 := two_pow_mul_le_card h
  have hk := pow_le_card h
  have hnpos : (0 : ℝ) < (Fintype.card Ω : ℝ) := by
    have : 0 < Fintype.card Ω := lt_of_lt_of_le (Nat.two_pow_pos _) h2
    exact_mod_cast this
  have hn1 : (1 : ℝ) ≤ (Fintype.card Ω : ℝ) := by
    have : 1 ≤ Fintype.card Ω := le_trans Nat.one_le_two_pow h2
    exact_mod_cast this
  have hlogk : 0 < Real.log k := Real.log_pos (by exact_mod_cast lt_of_lt_of_le (by norm_num) hk5)
  have hlog5 : (0 : ℝ) < Real.log 5 := Real.log_pos (by norm_num)
  refine ⟨?_, ?_, ?_⟩
  · have hcast : ((2 ^ (t * s) : ℕ) : ℝ) ≤ (Fintype.card Ω : ℝ) := by exact_mod_cast h2
    have hpow : ((2 ^ (t * s) : ℕ) : ℝ) = (2 : ℝ) ^ (t * s) := by push_cast; ring
    have hlogb : Real.logb 2 ((2 : ℝ) ^ (t * s)) = ((t * s : ℕ) : ℝ) := by
      rw [Real.logb_pow]
      simp
    calc ((t * s : ℕ) : ℝ) = Real.logb 2 ((2 : ℝ) ^ (t * s)) := hlogb.symm
      _ ≤ Real.logb 2 (Fintype.card Ω) := by
          refine Real.logb_le_logb_of_le (by norm_num) ?_ (by rw [← hpow]; exact hcast)
          positivity
  · rw [le_div_iff₀ hlogk]
    have hcast : ((k ^ s : ℕ) : ℝ) ≤ (Fintype.card Ω : ℝ) := by exact_mod_cast hk
    have hpos : (0 : ℝ) < ((k : ℝ) ^ s) := by positivity
    calc (s : ℝ) * Real.log k = Real.log ((k : ℝ) ^ s) := by rw [Real.log_pow]
      _ ≤ Real.log (Fintype.card Ω) := by
          refine Real.log_le_log hpos ?_
          push_cast at hcast
          exact hcast
  · have hlogn : 0 ≤ Real.log (Fintype.card Ω) := Real.log_nonneg hn1
    have h5k : Real.log 5 ≤ Real.log k := Real.log_le_log (by norm_num) (by exact_mod_cast hk5)
    gcongr

/-! ### The order of a Cameron group

The proof of Proposition 11.2.5 starts from `|G| ≤ (k!)^s s!`, which is the containment
`G ≤ S_k^(t) ≀ S_s` of Definition 11.2.2 read on orders: the wreath product in its product
action is covered by the pairs (tuple of permutations of `Fin k`, permutation of the `s`
coordinates). -/

/-- The order of the wreath product `H ≀ S_s` in its product action is at most
`|H|^s · s!`: the pair `(h, π)` determines `wreathPerm h π`. -/
theorem card_wreathProduct_le {Γ : Type*} [Finite Γ] (H : Subgroup (Equiv.Perm Γ))
    (s : ℕ) : Nat.card (wreathProduct H s) ≤ Nat.card H ^ s * (Nat.factorial s) := by
  classical
  have hsurj : Function.Surjective
      (fun p : (Fin s → H) × Equiv.Perm (Fin s) =>
        (⟨wreathPerm (fun i => ((p.1 i : Equiv.Perm Γ))) p.2,
          ⟨fun i => ((p.1 i : Equiv.Perm Γ)), p.2, fun i => (p.1 i).2, rfl⟩⟩ :
            wreathProduct H s)) := by
    rintro ⟨w, h, π, hh, rfl⟩
    exact ⟨⟨fun i => ⟨h i, hh i⟩, π⟩, rfl⟩
  have hcard := Nat.card_le_card_of_surjective _ hsurj
  refine hcard.trans_eq ?_
  rw [Nat.card_prod, Nat.card_pi]
  simp [Nat.card_eq_fintype_card, Fintype.card_perm]

/-- The order of the Johnson group `S_k^(t)` is at most `k!`: it is a homomorphic image of
`S_k`. -/
theorem card_JohnsonS_le (k t : ℕ) : Nat.card (JohnsonS k t) ≤ Nat.factorial k := by
  classical
  have hsurj : Function.Surjective
      (fun σ : Equiv.Perm (Fin k) =>
        (⟨tAction t σ, ⟨σ, trivial, rfl⟩⟩ : JohnsonS k t)) := by
    rintro ⟨-, σ, -, rfl⟩
    exact ⟨σ, rfl⟩
  have hcard := Nat.card_le_card_of_surjective _ hsurj
  refine hcard.trans_eq ?_
  simp [Nat.card_eq_fintype_card, Fintype.card_perm]

/-- §11.2, the first inequality in the proof of **Proposition 11.2.5**: for a Cameron
group with parameters `s, t, k`, `|G| ≤ (k!)^s · s!`.

This is the containment `G ≤ S_k^(t) ≀ S_s` of Definition 11.2.2, read on orders through
the identification `Ω ≃ (Fin k choose t)^s`. -/
theorem card_le_of_isCameronGroup [Fintype Ω] {G : Subgroup (Equiv.Perm Ω)} {s t k : ℕ}
    (h : IsCameronGroup G s t k) :
    Nat.card G ≤ (Nat.factorial k) ^ s * (Nat.factorial s) := by
  classical
  obtain ⟨-, -, -, -, -, -, e, -, hle⟩ := h
  have hmap : Nat.card (G.map (Equiv.permCongrHom e).toMonoidHom) = Nat.card G :=
    Nat.card_congr
      (Subgroup.equivMapOfInjective G (Equiv.permCongrHom e).toMonoidHom
        (Equiv.permCongrHom e).injective).symm.toEquiv
  have hsub : Nat.card (G.map (Equiv.permCongrHom e).toMonoidHom) ≤
      Nat.card (wreathProduct (JohnsonS k t) s) :=
    Nat.card_le_card_of_injective
      (fun g => (⟨(g : Equiv.Perm (Fin s → binom (Fin k) t)), hle g.2⟩ :
        wreathProduct (JohnsonS k t) s))
      (fun a b hab => Subtype.ext (by simpa using hab))
  calc Nat.card G = Nat.card (G.map (Equiv.permCongrHom e).toMonoidHom) := hmap.symm
    _ ≤ Nat.card (wreathProduct (JohnsonS k t) s) := hsub
    _ ≤ Nat.card (JohnsonS k t) ^ s * (Nat.factorial s) := card_wreathProduct_le _ _
    _ ≤ (Nat.factorial k) ^ s * (Nat.factorial s) := by
        exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (card_JohnsonS_le k t) s)

/-- §11.2, **Proposition 11.2.5**.

> If `G ≤ S_n` is a Cameron group with parameters `k, t, s` and `|G| ≥ n^{1+log₂ n}` then
> `k ≥ log₂ n` and `s! < n`, assuming `n` is greater than an absolute constant.
>
> *Proof.* As before, we have `n ≥ k^s`.  On the other hand
> `n^{1+log₂ n} ≤ |G| ≤ (k!)^s s! < k^{ks} s! ≤ n^k s! < n^k (log₂ n)^{log₂ n} =
> n^{k+log₂ log₂ n}`.  Therefore `k > log₂ n − log₂ log₂ n > log₂ n / log 5 ≥ s`.  Hence,
> `s! < s^s ≤ k^s ≤ n`.  Moreover, `n^{1+log₂ n} < n^k s! < n^{k+1}`, hence `k ≥ log₂ n`.

"assuming `n` is greater than an absolute constant" is the leading `∃ n₀`.  The bound on
`n` is in fact not needed: a Cameron group has `n = C(k,t)^s ≥ 5`, which is all the proof
below uses, so `n₀ = 0` works.  (The paper's chain is followed step by step: `|G| ≤
(k!)^s s!` is `Babai.card_le_of_isCameronGroup`, `(k!)^s < k^{ks} ≤ n^k` is `hfactk`,
`s! ≤ s^s ≤ (log₂ n)^{log₂ n} = n^{log₂ log₂ n}` is `hfacts`/`hLL`, and the two
conclusions come out in the paper's order: first `s ≤ log₂ n/2 < k`, hence `s! < s^s <
k^s ≤ n`, then `n^{1+log₂ n} ≤ |G| < n^{k+1}`, hence `log₂ n ≤ k`.) -/
theorem Proposition_11_2_5 :
    ∃ n₀ : ℕ, ∀ (Ω : Type u) [Fintype Ω] (G : Subgroup (Equiv.Perm Ω)) (s t k : ℕ),
      n₀ ≤ Fintype.card Ω → IsCameronGroup G s t k →
      (Fintype.card Ω : ℝ) ^ (1 + Real.logb 2 (Fintype.card Ω)) ≤ (Nat.card G : ℝ) →
      Real.logb 2 (Fintype.card Ω) ≤ (k : ℝ) ∧
        ((Nat.factorial s : ℕ) : ℝ) < (Fintype.card Ω : ℝ) := by
  refine ⟨0, ?_⟩
  intro Ω _ G s t k _hn₀ hC hGcard
  obtain ⟨hs1, ht1, hmax, hk2t, hn, -⟩ := id hC
  have hk5 : 5 ≤ k := le_trans (le_max_right (2 * t) 5) hmax
  have hks : k ^ s ≤ Fintype.card Ω := pow_le_card hC
  have hn5 : 5 ≤ Fintype.card Ω :=
    le_trans (le_trans (Nat.le_self_pow (by omega) 5) (Nat.pow_le_pow_left hk5 s)) hks
  -- the paper's `|G| ≤ (k!)^s s!`, and `(k!)^s < k^{ks} ≤ n^k`
  have hcardG := card_le_of_isCameronGroup hC
  have hfactk : (Nat.factorial k) ^ s ≤ Fintype.card Ω ^ k := by
    calc (Nat.factorial k) ^ s ≤ (k ^ k) ^ s := Nat.pow_le_pow_left (Nat.factorial_le_pow k) s
      _ = (k ^ s) ^ k := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
      _ ≤ Fintype.card Ω ^ k := Nat.pow_le_pow_left hks k
  -- real-valued notation
  set n : ℕ := Fintype.card Ω with hndef
  set L : ℝ := Real.logb 2 (n : ℝ) with hLdef
  have hnR1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast lt_of_lt_of_le (by norm_num) hn5
  have hnR0 : (0 : ℝ) < (n : ℝ) := lt_trans zero_lt_one hnR1
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hL2 : (2 : ℝ) ≤ L := by
    have h4 : Real.log 4 ≤ Real.log (n : ℝ) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast le_trans (by norm_num) hn5)
    have hlog4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]; push_cast; ring
    rw [hLdef, Real.logb, le_div_iff₀ hlog2pos]
    rw [hlog4] at h4
    linarith
  have hL0 : (0 : ℝ) < L := lt_of_lt_of_le (by norm_num) hL2
  have hL1 : (1 : ℝ) ≤ L := le_trans (by norm_num) hL2
  -- Proposition 11.2.4: `s ≤ log n / log 5 ≤ (log₂ n)/2`
  have hsL : (s : ℝ) ≤ L / 2 := by
    obtain ⟨-, hsk, hk5'⟩ := Proposition_11_2_4 hC
    have hlogn0 : (0 : ℝ) ≤ Real.log (n : ℝ) := Real.log_nonneg (le_of_lt hnR1)
    have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have hlog45 : 2 * Real.log 2 ≤ Real.log 5 := by
      rw [show (2 : ℝ) * Real.log 2 = Real.log 4 by
        rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]; push_cast; ring]
      exact Real.log_le_log (by norm_num) (by norm_num)
    calc (s : ℝ) ≤ Real.log (n : ℝ) / Real.log 5 := le_trans hsk hk5'
      _ ≤ Real.log (n : ℝ) / (2 * Real.log 2) := by
          apply div_le_div_of_nonneg_left hlogn0 (by positivity) hlog45
      _ = L / 2 := by rw [hLdef, Real.logb]; ring
  -- `s! ≤ s^s ≤ L^L`
  have hfacts : ((Nat.factorial s : ℕ) : ℝ) ≤ L ^ L := by
    have hsR1 : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs1
    have h1 : ((Nat.factorial s : ℕ) : ℝ) ≤ (s : ℝ) ^ ((s : ℕ) : ℝ) := by
      rw [Real.rpow_natCast]
      exact_mod_cast Nat.factorial_le_pow s
    have hsLe : (s : ℝ) ≤ L := le_trans hsL (by linarith)
    calc ((Nat.factorial s : ℕ) : ℝ) ≤ (s : ℝ) ^ ((s : ℕ) : ℝ) := h1
      _ ≤ L ^ ((s : ℕ) : ℝ) := Real.rpow_le_rpow (by linarith) hsLe (by positivity)
      _ ≤ L ^ L := Real.rpow_le_rpow_of_exponent_le hL1 hsLe
  -- `L^L = n^{log₂ L}`
  have hLL : L ^ L = (n : ℝ) ^ (Real.logb 2 L) := by
    rw [Real.rpow_def_of_pos hL0, Real.rpow_def_of_pos hnR0, Real.logb, hLdef, Real.logb]
    congr 1
    field_simp
  -- `log₂ L < 1 + L/2`
  have hlogbL : Real.logb 2 L < 1 + L / 2 := by
    have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have hlog2' : (2 : ℝ) / 3 < Real.log 2 := by
      have := Real.log_two_gt_d9
      linarith
    have hlogL : Real.log L ≤ L / 3 + (Real.log 3 - 1) := by
      have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < L / 3 by positivity)
      rw [Real.log_div (by positivity) (by norm_num)] at h
      linarith
    have hlog3 : Real.log 3 - 1 < Real.log 2 := by
      have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (3 : ℝ) / 2 by norm_num)
      rw [Real.log_div (by norm_num) (by norm_num)] at h
      linarith
    have hthird : L / 3 ≤ Real.log 2 / 2 * L := by
      have : (1 : ℝ) / 3 ≤ Real.log 2 / 2 := by linarith
      nlinarith
    have hkey : Real.log L < Real.log 2 + Real.log 2 / 2 * L := by linarith
    rw [Real.logb, div_lt_iff₀ hlog2]
    calc Real.log L < Real.log 2 + Real.log 2 / 2 * L := hkey
      _ = (1 + L / 2) * Real.log 2 := by ring
  -- the paper's chain `n^{1+log₂ n} ≤ |G| ≤ (k!)^s s! < n^k · n^{log₂ log₂ n}`
  have hchain : (n : ℝ) ^ (1 + L) ≤ (n : ℝ) ^ ((k : ℝ) + Real.logb 2 L) := by
    refine le_trans hGcard ?_
    have h1 : (Nat.card G : ℝ) ≤ ((Nat.factorial k : ℕ) : ℝ) ^ (s : ℕ) *
        ((Nat.factorial s : ℕ) : ℝ) := by
      exact_mod_cast hcardG
    have h2 : ((Nat.factorial k : ℕ) : ℝ) ^ (s : ℕ) ≤ (n : ℝ) ^ (k : ℕ) := by
      exact_mod_cast hfactk
    calc (Nat.card G : ℝ) ≤ ((Nat.factorial k : ℕ) : ℝ) ^ (s : ℕ) *
          ((Nat.factorial s : ℕ) : ℝ) := h1
      _ ≤ (n : ℝ) ^ (k : ℕ) * (L ^ L) := by
          refine mul_le_mul h2 hfacts (by positivity) (by positivity)
      _ = (n : ℝ) ^ ((k : ℕ) : ℝ) * (n : ℝ) ^ (Real.logb 2 L) := by
          rw [hLL, Real.rpow_natCast]
      _ = (n : ℝ) ^ ((k : ℝ) + Real.logb 2 L) := by rw [Real.rpow_add hnR0]
  have hexp : 1 + L ≤ (k : ℝ) + Real.logb 2 L :=
    (Real.rpow_le_rpow_left_iff hnR1).1 hchain
  -- hence `s < k`, and `s! < s^s < k^s ≤ n`
  have hsk : s < k := by
    have : (s : ℝ) < (k : ℝ) := by linarith
    exact_mod_cast this
  have hfactn : Nat.factorial s < n :=
    lt_of_le_of_lt (Nat.factorial_le_pow s)
      (lt_of_lt_of_le (Nat.pow_lt_pow_left hsk (by omega)) hks)
  refine ⟨?_, by exact_mod_cast hfactn⟩
  -- and finally `n^{1+log₂ n} ≤ |G| < n^{k+1}`, so `log₂ n ≤ k`
  have hle : Nat.card G ≤ n ^ (k + 1) := by
    calc Nat.card G ≤ (Nat.factorial k) ^ s * (Nat.factorial s) := hcardG
      _ ≤ n ^ k * n := Nat.mul_le_mul hfactk (le_of_lt hfactn)
      _ = n ^ (k + 1) := by ring
  have hchain2 : (n : ℝ) ^ (1 + L) ≤ (n : ℝ) ^ ((k : ℝ) + 1) := by
    refine le_trans hGcard ?_
    have : (Nat.card G : ℝ) ≤ (n : ℝ) ^ (k + 1 : ℕ) := by exact_mod_cast hle
    calc (Nat.card G : ℝ) ≤ (n : ℝ) ^ (k + 1 : ℕ) := this
      _ = (n : ℝ) ^ (((k : ℕ) + 1 : ℕ) : ℝ) := (Real.rpow_natCast _ _).symm
      _ = (n : ℝ) ^ ((k : ℝ) + 1) := by push_cast; ring_nf
  have := (Real.rpow_le_rpow_left_iff hnR1).1 hchain2
  linarith

/-! ### Theorem 11.2.1

The theorem is placed after Propositions 11.2.4 and 11.2.5 because its proof uses them.
-/

/-- §11.2, the consequence of Proposition 11.2.4 used in the proof of Theorem 11.2.1:
`2s ≤ log₂ n`.  Proposition 11.2.4 gives `s ≤ log n / log 5`, and `log 5 ≥ 2 log 2`. -/
theorem two_mul_le_logb [Fintype Ω] {G : Subgroup (Equiv.Perm Ω)} {s t k : ℕ}
    (h : IsCameronGroup G s t k) :
    2 * (s : ℝ) ≤ Real.logb 2 (Fintype.card Ω) := by
  obtain ⟨hs1, ht1, hmax, hk2t, hn, -⟩ := id h
  have hk5 : 5 ≤ k := le_trans (le_max_right (2 * t) 5) hmax
  have hks : k ^ s ≤ Fintype.card Ω := pow_le_card h
  have hn5 : 5 ≤ Fintype.card Ω :=
    le_trans (le_trans (Nat.le_self_pow (by omega) 5) (Nat.pow_le_pow_left hk5 s)) hks
  have hnR1 : (1 : ℝ) < (Fintype.card Ω : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (by norm_num) hn5
  obtain ⟨-, hsk, hk5'⟩ := Proposition_11_2_4 h
  have hlogn0 : (0 : ℝ) ≤ Real.log (Fintype.card Ω) := Real.log_nonneg (le_of_lt hnR1)
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog45 : 2 * Real.log 2 ≤ Real.log 5 := by
    rw [show (2 : ℝ) * Real.log 2 = Real.log 4 by
      rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]; push_cast; ring]
    exact Real.log_le_log (by norm_num) (by norm_num)
  have hhalf : (s : ℝ) ≤ Real.logb 2 (Fintype.card Ω) / 2 := by
    calc (s : ℝ) ≤ Real.log (Fintype.card Ω) / Real.log 5 := le_trans hsk hk5'
      _ ≤ Real.log (Fintype.card Ω) / (2 * Real.log 2) :=
          div_le_div_of_nonneg_left hlogn0 (by positivity) hlog45
      _ = Real.logb 2 (Fintype.card Ω) / 2 := by rw [Real.logb]; ring
  linarith

/-- §11.2, **Theorem 11.2.1**.

> Let `G ≤ S_n` be a primitive group of order `|G| ≥ n^{1+log₂ n}` where `n` is greater
> than some absolute constant.  Then `G` has a normal subgroup `N` of index `≤ n` such
> that `N` has a system of imprimitivity on which `N` acts as a Johnson group `A_k^(t)`
> with `k ≥ log₂ n`.  Moreover, `N` and the system of imprimitivity in question can be
> found in polynomial time.

The mathematical half is stated here.  The algorithmic half ("can be found in polynomial
time") is on the RAM, in `Workspace/Algo/CameronNbar.lean` (`Algo.exists_polyFun_cameronNbarSpec`,
the generators of `N`), `Workspace/Algo/CameronDescent.lean` (`Algo.camRecognize_index`, the
blocks and the bounds) and `Workspace/Algo/CameronJohnson.lean` (the Johnson action); it
rests on the cited recognition of Cameron groups, `Babai.cameronStructure_polyTime`
.  "where `n` is greater than some
absolute constant" is the leading `∃ n₀`.

The paper's proof is: "The mathematical part of this result is an immediate consequence of
Cameron's classification of large primitive groups" (Theorem 11.2.3), completed by
Propositions 11.2.4 and 11.2.5.  The intermediate steps are not spelled out in the paper,
and one of them needs care: if `N` is taken to be the kernel of the action `G → S_s` on the
direct factors of the socle (index `≤ s! < n` by Prop. 11.2.5), then the group `N` induces
on the fibres of one coordinate of `(Fin k choose t)^s` only lies *between* `A_k^(t)` and
`S_k^(t)`, so it need not be `A_k^(t)`, as the conclusion demands.  The route that gives
`A_k^(t)` literally is to take `N` to be the base group `(A_k^(t))^s` of Definition 11.2.2,
which is contained in `G`, normal in `S_k^(t) ≀ S_s` and hence in `G`, and whose index in
`G` is at most `|S_k^(t) ≀ S_s : (A_k^(t))^s| ≤ 2^s s! ≤ (2s)^s ≤ C(k,t)^s = n`, the last
inequality because `2s ≤ log₂ n ≤ k ≤ C(k,t)` by Propositions 11.2.4 and 11.2.5.  The
blocks are the fibres of one coordinate, on which `(A_k^(t))^s` induces exactly `A_k^(t)`,
and `k ≥ log₂ n` is Proposition 11.2.5.

Two points of reading, both forced by the paper's own conventions.

* The system of imprimitivity is on all of `Ω` (`Δ = Set.univ`): a system of imprimitivity
  is a partition of an invariant subset (§2.2.1), and here it is a system for `N`, the
  group on which the reduction continues to run with the *same* permutation domain
  ("`N` has a system of imprimitivity"); `N` is a nontrivial normal subgroup of the
  primitive group `G`, hence transitive on `Ω`.
* "`A_k^(t)`" means a Johnson group in the range of §2.2.1, i.e. `1 ≤ t` and `2t < k`
  (which is also what Definition 11.2.2 requires of the parameters of a Cameron group).
  Without these two constraints the conclusion would be satisfied by the degenerate
  `t = 0`, `ℬ = {Ω}`, for which `A_k^(0)` is the trivial group on one block, so the
  statement would be vacuous. -/
theorem Theorem_11_2_1 :
    ∃ n₀ : ℕ, ∀ (Ω : Type u) [Fintype Ω] (G : Subgroup (Equiv.Perm Ω)),
      n₀ ≤ Fintype.card Ω → IsPrimitive G →
      (Fintype.card Ω : ℝ) ^ (1 + Real.logb 2 (Fintype.card Ω)) ≤ (Nat.card G : ℝ) →
      ∃ N : Subgroup (Equiv.Perm Ω), IsNormalIn N G ∧ N.relIndex G ≤ Fintype.card Ω ∧
        ∃ (ℬ : Set (Set Ω)) (hsys : IsSystemOfImprimitivity N Set.univ ℬ) (k t : ℕ),
          1 ≤ t ∧ 2 * t < k ∧
            ActsAsJohnsonA N ℬ hsys.permutes k t ∧
              Real.logb 2 (Fintype.card Ω) ≤ (k : ℝ) := by
  classical
  obtain ⟨n₁, h1125⟩ := Proposition_11_2_5.{u}
  refine ⟨max 25 n₁, ?_⟩
  intro Ω _ G hn hprim hcard
  have hn25 : 25 ≤ Fintype.card Ω := le_trans (le_max_left _ _) hn
  have hn1 : n₁ ≤ Fintype.card Ω := le_trans (le_max_right _ _) hn
  -- Cameron's theorem (11.2.3): `G` is a Cameron group with parameters `s, t, k`
  obtain ⟨s, t, k, hC⟩ := Theorem_11_2_3 G hn25 hprim hcard
  obtain ⟨hklogb, -⟩ := h1125 Ω G s t k hn1 hC hcard
  obtain ⟨hs1, ht1, hmax, hk2t, hneq, -, e, hbase, hwreath⟩ := id hC
  have hk5 : 5 ≤ k := le_trans (le_max_right (2 * t) 5) hmax
  haveI : Nonempty (binom (Fin k) t) := binom_nonempty (by omega)
  have hΦinj : Function.Injective (Equiv.permCongrHom e).toMonoidHom :=
    (Equiv.permCongrHom e).injective
  have hΦsurj : Function.Surjective (Equiv.permCongrHom e).toMonoidHom :=
    (Equiv.permCongrHom e).surjective
  -- `N` is the base group `(A_k^(t))^s` of Definition 11.2.2, read in `S(Ω)`
  refine ⟨(basePower (JohnsonA k t) s).comap (Equiv.permCongrHom e).toMonoidHom, ?_, ?_, ?_⟩
  · -- `N ◁ G`: the base group is normal in the wreath product, which contains `G`
    have hNG : (basePower (JohnsonA k t) s).comap (Equiv.permCongrHom e).toMonoidHom ≤ G := by
      intro x hx
      obtain ⟨y, hy, hxy⟩ := hbase (Subgroup.mem_comap.1 hx)
      rwa [← hΦinj hxy]
    refine ⟨hNG, fun g hg n hn => ?_⟩
    have hgW : (Equiv.permCongrHom e).toMonoidHom g ∈ wreathProduct (JohnsonS k t) s :=
      hwreath (Subgroup.mem_map_of_mem _ hg)
    have hnP : (Equiv.permCongrHom e).toMonoidHom n ∈ basePower (JohnsonA k t) s :=
      Subgroup.mem_comap.1 hn
    rw [Subgroup.mem_comap, map_mul, map_mul, map_inv]
    exact (basePower_isNormalIn_wreathProduct (johnsonA_le_johnsonS k t)
      (johnsonA_conj_mem k t) s).conj_mem _ hgW _ hnP
  · -- `|G : N| ≤ |S_k^(t) ≀ S_s : (A_k^(t))^s| ≤ 2^s s! ≤ (2s)^s ≤ C(k,t)^s = n`
    have hmapN : ((basePower (JohnsonA k t) s).comap
        (Equiv.permCongrHom e).toMonoidHom).map (Equiv.permCongrHom e).toMonoidHom =
        basePower (JohnsonA k t) s :=
      Subgroup.map_comap_eq_self_of_surjective hΦsurj _
    have hrel := Subgroup.relIndex_map_map_of_injective
      ((basePower (JohnsonA k t) s).comap (Equiv.permCongrHom e).toMonoidHom) G hΦinj
    rw [hmapN] at hrel
    have hPW : basePower (JohnsonA k t) s ≤ wreathProduct (JohnsonS k t) s :=
      le_trans hbase hwreath
    have hmul := Subgroup.relIndex_mul_relIndex (basePower (JohnsonA k t) s)
      (G.map (Equiv.permCongrHom e).toMonoidHom) (wreathProduct (JohnsonS k t) s)
      hbase hwreath
    have hlag := relIndex_mul_card_of_le hPW
    have hcardP : Nat.card (basePower (JohnsonA k t) s) = Nat.card (JohnsonA k t) ^ s :=
      card_basePower _ _
    have hApos : 0 < Nat.card (JohnsonA k t) ^ s := pow_pos Nat.card_pos s
    -- `|W : P| ≤ 2^s s!`
    have hWle : (basePower (JohnsonA k t) s).relIndex (wreathProduct (JohnsonS k t) s) *
        Nat.card (JohnsonA k t) ^ s ≤
        (2 ^ s * Nat.factorial s) * Nat.card (JohnsonA k t) ^ s := by
      calc (basePower (JohnsonA k t) s).relIndex (wreathProduct (JohnsonS k t) s) *
            Nat.card (JohnsonA k t) ^ s
          = Nat.card (wreathProduct (JohnsonS k t) s) := by rw [← hcardP]; exact hlag
        _ ≤ Nat.card (JohnsonS k t) ^ s * Nat.factorial s := card_wreathProduct_le _ _
        _ ≤ (2 * Nat.card (JohnsonA k t)) ^ s * Nat.factorial s :=
            Nat.mul_le_mul_right _
              (Nat.pow_le_pow_left (card_johnsonS_le_two_mul (by omega) t) s)
        _ = (2 ^ s * Nat.factorial s) * Nat.card (JohnsonA k t) ^ s := by
            rw [mul_pow]; ring
    have hPWle : (basePower (JohnsonA k t) s).relIndex (wreathProduct (JohnsonS k t) s) ≤
        2 ^ s * Nat.factorial s := Nat.le_of_mul_le_mul_right hWle hApos
    -- the index in `G` is at most the index in the wreath product
    have hWne : (basePower (JohnsonA k t) s).relIndex
        (wreathProduct (JohnsonS k t) s) ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hlag
      have := Nat.card_pos (α := wreathProduct (JohnsonS k t) s)
      omega
    have hrelle : (basePower (JohnsonA k t) s).relIndex
        (G.map (Equiv.permCongrHom e).toMonoidHom) ≤
        (basePower (JohnsonA k t) s).relIndex (wreathProduct (JohnsonS k t) s) := by
      have hb : 0 < (G.map (Equiv.permCongrHom e).toMonoidHom).relIndex
          (wreathProduct (JohnsonS k t) s) := by
        rcases Nat.eq_zero_or_pos ((G.map (Equiv.permCongrHom e).toMonoidHom).relIndex
          (wreathProduct (JohnsonS k t) s)) with h0 | h
        · exact absurd (by rw [h0, mul_zero] at hmul; exact hmul.symm) hWne
        · exact h
      calc (basePower (JohnsonA k t) s).relIndex
            (G.map (Equiv.permCongrHom e).toMonoidHom)
          ≤ (basePower (JohnsonA k t) s).relIndex
              (G.map (Equiv.permCongrHom e).toMonoidHom) *
            (G.map (Equiv.permCongrHom e).toMonoidHom).relIndex
              (wreathProduct (JohnsonS k t) s) := Nat.le_mul_of_pos_right _ hb
        _ = (basePower (JohnsonA k t) s).relIndex
              (wreathProduct (JohnsonS k t) s) := hmul
    -- `2s ≤ log₂ n ≤ k ≤ C(k,t)`, so `2^s s! ≤ (2s)^s ≤ C(k,t)^s = n`
    have h2sk : 2 * s ≤ k := by
      have h2 : (2 * s : ℝ) ≤ (k : ℝ) := le_trans (two_mul_le_logb hC) hklogb
      exact_mod_cast h2
    have hfin : 2 ^ s * Nat.factorial s ≤ Fintype.card Ω := by
      calc 2 ^ s * Nat.factorial s ≤ 2 ^ s * s ^ s :=
            Nat.mul_le_mul_left _ (Nat.factorial_le_pow s)
        _ = (2 * s) ^ s := (mul_pow 2 s s).symm
        _ ≤ k ^ s := Nat.pow_le_pow_left h2sk s
        _ ≤ (k.choose t) ^ s := Nat.pow_le_pow_left (self_le_choose ht1 hk2t) s
        _ = Fintype.card Ω := hneq.symm
    rw [← hrel]
    exact le_trans (le_trans hrelle hPWle) hfin
  · -- the blocks are the fibres of one coordinate
    have hmapN : ((basePower (JohnsonA k t) s).comap
        (Equiv.permCongrHom e).toMonoidHom).map (Equiv.permCongrHom e).toMonoidHom =
        basePower (JohnsonA k t) s :=
      Subgroup.map_comap_eq_self_of_surjective hΦsurj _
    have htrans : ∀ c c' : binom (Fin k) t, ∃ a ∈ JohnsonA k t, a c = c' :=
      fun c c' => johnsonA_exists_smul ht1 hk2t c c'
    have hsys : IsSystemOfImprimitivity
        ((basePower (JohnsonA k t) s).comap (Equiv.permCongrHom e).toMonoidHom)
        Set.univ (coordFibres e ⟨0, hs1⟩) :=
      coordFibres_isSystemOfImprimitivity e ⟨0, hs1⟩ hmapN htrans
    refine ⟨coordFibres e ⟨0, hs1⟩, hsys, k, t, ht1, hk2t, ?_, hklogb⟩
    exact coordFibres_onBlocks e ⟨0, hs1⟩ hmapN hsys.permutes

/-- Test that the conclusion of `Babai.Theorem_11_2_1` is not vacuous: with the Johnson
parameters in the range of §2.2.1 (`1 ≤ t`, `2t < k`) a group acting on a block system as
`A_k^(t)` has `C(k,t) ≥ k ≥ 3` blocks, so the degenerate witness `ℬ = {Ω}` with `t = 0`
(which satisfies every other clause of the conclusion for `N = G`) is excluded. -/
example {Ω : Type u} {N : Subgroup (Equiv.Perm Ω)} {ℬ : Set (Set Ω)}
    {hperm : ∀ σ ∈ N, ∀ B ∈ ℬ, (σ : Equiv.Perm Ω) '' B ∈ ℬ} {k t : ℕ}
    (ht : 1 ≤ t) (hk : 2 * t < k) (h : ActsAsJohnsonA N ℬ hperm k t) :
    3 ≤ ℬ.ncard := by
  obtain ⟨e, -⟩ := h
  have hcard : Nat.card ℬ = k.choose t := by
    rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_finset_len,
      Fintype.card_fin]
  calc 3 ≤ k := by omega
    _ ≤ k.choose t := self_le_choose ht hk
    _ = ℬ.ncard := by rw [← hcard, Nat.card_coe_set_eq]

end Babai
