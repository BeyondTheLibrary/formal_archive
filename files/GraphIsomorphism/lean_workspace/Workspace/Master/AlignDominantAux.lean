/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Sections 14.1 and 14.2: the shared steps behind the counting lemmas of
`Workspace/Master/AlignDominant.lean`.
-/
import Workspace.TopAction.Classes
import Workspace.Canonical.AlignJohnson

/-!
# Procedure Align, lines 6–11: the shared steps

The statements of `Workspace/Master/AlignDominant.lean` are about the structures
`Babai.AlignDominant`, `Babai.AlignDominantA` and `Babai.AlignDominantB`.  Three steps
recur in their proofs and do not need any of that packaging; they are proved here, in the
plain language of Secs. 10.5 and 14.1.

* `Babai.image_inter_of_preimageSubgroup` — `ϕ(G_u ∩ ϕ⁻¹H) = ϕ(G_u) ∩ H`, the trivial
  identity that lets one read the stabilizer of `u` in `G*` off the stabilizer in `G`.
* `Babai.exists_mem_setwiseStab_map_eq_of_unaffected` — *"if `u` is unaffected by `ϕ*`
  then `A(Γ*) ≤ ψ(H_{T(u)})`"*, which is that identity together with Theorem 10.5.1 (a)
  (`ϕ(G_u) ≤ S(Γ)_{T(u)}`).
* `Babai.three_mul_card_labelFiber_le` — a standard block is at most `2n/3`, from
  `n = C(m,t)·b` (`Babai.card_univ_eq_mul`) and `C(m,t) ≥ m ≥ 9`
  (`Babai.le_choose_of_two_mul_le`).
-/

universe u

namespace Babai

open MulAction Equiv Equiv.Perm

/-! ### Arithmetic: `C(m,t) ≥ m` for `1 ≤ t` and `2t ≤ m` -/

/-- `m ≤ C(m,t)` for `1 ≤ t ≤ m/2`: `C(m,·)` increases up to the middle
(`Nat.choose_le_succ_of_lt_half_left`), and `C(m,1) = m`. -/
theorem le_choose_of_two_mul_le {m t : ℕ} (ht : 1 ≤ t) (h2t : 2 * t ≤ m) :
    m ≤ m.choose t := by
  have hhalf : t ≤ m / 2 := (Nat.le_div_iff_mul_le (by norm_num)).2 (by omega)
  have key : ∀ r : ℕ, 1 ≤ r → r ≤ t → m.choose 1 ≤ m.choose r := by
    intro r
    induction r with
    | zero => omega
    | succ k ih =>
        intro _ hk
        rcases Nat.eq_zero_or_pos k with hk0 | hk1
        · subst hk0; exact le_rfl
        · refine (ih hk1 (by omega)).trans (Nat.choose_le_succ_of_lt_half_left ?_)
          omega
  have := key t ht le_rfl
  rwa [Nat.choose_one_right] at this

/-! ### The centralizer of `A(Γ)` in `S(Γ)` -/

/-- **The centralizer of `A(Γ)` in `S(Γ)` is trivial** for `|Γ| ≥ 4`.

This is the second half of the group-theoretic step behind
`Babai.AlignDominant.pointwiseStab_orbit_le_ker`; the paper uses it as common knowledge.

*Proof.*  Suppose `q ≠ 1` commutes with every even permutation, and let `y = q(x) ≠ x`.
Pick `z, w` outside `{x, y}` and distinct (there is room, because `|Γ| ≥ 4`), and let
`a = (y z w)` be the corresponding `3`-cycle, an even permutation fixing `x`.  Applying
`q ∘ a = a ∘ q` to `x` gives `q(x) = a(q(x))`, that is, `y = a(y) = z`, contradicting
`z ∉ {x, y}`. -/
theorem eq_one_of_commute_alternating {Γ : Type*} [Fintype Γ] [DecidableEq Γ]
    (h4 : 4 ≤ Fintype.card Γ) {q : Equiv.Perm Γ}
    (hq : ∀ a ∈ alternatingGroup Γ, a * q = q * a) : q = 1 := by
  classical
  by_contra hne
  obtain ⟨x, hx⟩ : ∃ x : Γ, q x ≠ x := by
    by_contra hcon
    push_neg at hcon
    exact hne (Equiv.ext fun x => by rw [hcon x]; rfl)
  set y := q x with hy
  -- two further points, distinct from `x`, `y` and from each other
  have hcard : 1 < (({x, y} : Finset Γ)ᶜ).card := by
    have h1 : ({x, y} : Finset Γ).card ≤ 2 :=
      (Finset.card_insert_le _ _).trans (by simp)
    have h2 := Finset.card_compl ({x, y} : Finset Γ)
    omega
  obtain ⟨z, hz, w, hw, hzw⟩ := Finset.one_lt_card.1 hcard
  simp only [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or] at hz hw
  have hxy : x ≠ y := fun h => hx h.symm
  have hxz : x ≠ z := Ne.symm hz.1
  have hxw : x ≠ w := Ne.symm hw.1
  have hyz : y ≠ z := Ne.symm hz.2
  have hyw : y ≠ w := Ne.symm hw.2
  -- the `3`-cycle `(y z w)`
  set a : Equiv.Perm Γ := Equiv.swap y z * Equiv.swap z w with ha
  have hamem : a ∈ alternatingGroup Γ := by
    rw [Equiv.Perm.mem_alternatingGroup, ha, map_mul, Equiv.Perm.sign_swap hyz,
      Equiv.Perm.sign_swap hzw]
    simp
  have hax : a x = x := by
    show Equiv.swap y z (Equiv.swap z w x) = x
    rw [Equiv.swap_apply_of_ne_of_ne hxz hxw, Equiv.swap_apply_of_ne_of_ne hxy hxz]
  have hay : a y = z := by
    show Equiv.swap y z (Equiv.swap z w y) = z
    rw [Equiv.swap_apply_of_ne_of_ne hyz hyw, Equiv.swap_apply_left]
  have key := congrArg (fun f : Equiv.Perm Γ => f x) (hq a hamem)
  simp only [Equiv.Perm.mul_apply, ← hy, hax, hay] at key
  exact hyz key.symm

/-- **A subgroup of `S(Γ)` normalized by `A(Γ)` is trivial or contains `A(Γ)`**, for
`|Γ| ≥ 5`.  This is the group-theoretic step behind
`Babai.AlignDominant.pointwiseStab_orbit_le_ker`; the paper uses it as common knowledge.

*Proof.*  `Q ∩ A(Γ)` is normal in `A(Γ)`, which is simple
(`Babai.isSimpleGroup_alternatingGroup`), so it is trivial or all of `A(Γ)`.  In the second
case `A(Γ) ≤ Q`.  In the first case, for `q ∈ Q` and `a ∈ A(Γ)` the commutator
`q a q⁻¹ a⁻¹` lies in `Q` (because `a q⁻¹ a⁻¹ ∈ Q`) and in `A(Γ)` (because `A(Γ)` is the
kernel of the sign), hence is trivial; so `Q` centralizes `A(Γ)` and
`Babai.eq_one_of_commute_alternating` makes every `q` trivial. -/
theorem eq_one_or_alternating_le_of_conj_mem {Γ : Type*} [Fintype Γ] [DecidableEq Γ]
    (h5 : 5 ≤ Fintype.card Γ) (Q : Subgroup (Equiv.Perm Γ))
    (hQ : ∀ a ∈ alternatingGroup Γ, ∀ q ∈ Q, a * q * a⁻¹ ∈ Q) :
    (∀ q ∈ Q, q = 1) ∨ alternatingGroup Γ ≤ Q := by
  classical
  haveI : IsSimpleGroup (alternatingGroup Γ) := isSimpleGroup_alternatingGroup h5
  set P : Subgroup (alternatingGroup Γ) := Q.subgroupOf (alternatingGroup Γ) with hP
  haveI hPnorm : P.Normal := by
    constructor
    intro n hn g
    rw [hP, Subgroup.mem_subgroupOf] at hn ⊢
    exact hQ (g : Equiv.Perm Γ) g.2 (n : Equiv.Perm Γ) hn
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal P hPnorm with hbot | htop
  · left
    have hint : ∀ q ∈ Q, q ∈ alternatingGroup Γ → q = 1 := by
      intro q hq hqA
      have hmem : (⟨q, hqA⟩ : alternatingGroup Γ) ∈ P := Subgroup.mem_subgroupOf.2 hq
      rw [hbot, Subgroup.mem_bot] at hmem
      exact congrArg Subtype.val hmem
    intro q hq
    refine eq_one_of_commute_alternating (by omega) ?_
    intro a ha
    have hc1 : q * a * q⁻¹ * a⁻¹ ∈ Q := by
      have : q * (a * q⁻¹ * a⁻¹) ∈ Q := Q.mul_mem hq (hQ a ha q⁻¹ (Q.inv_mem hq))
      rwa [show q * (a * q⁻¹ * a⁻¹) = q * a * q⁻¹ * a⁻¹ from by group] at this
    have hc2 : q * a * q⁻¹ * a⁻¹ ∈ alternatingGroup Γ := by
      rw [Equiv.Perm.mem_alternatingGroup] at ha ⊢
      simp [ha]
    have h1 := hint _ hc1 hc2
    have h2 : q * a * q⁻¹ = a := by
      have := congrArg (fun z : Equiv.Perm Γ => z * a) h1
      simpa using this
    have h3 := congrArg (fun z : Equiv.Perm Γ => z * q) h2
    simpa [mul_assoc] using h3.symm
  · right
    intro a ha
    have hmem : (⟨a, ha⟩ : alternatingGroup Γ) ∈ P := by rw [htop]; trivial
    rwa [hP, Subgroup.mem_subgroupOf] at hmem

/-! ### The stabilizer of a point in `G* = ϕ⁻¹(H)` -/

variable {Ω : Type u} [Fintype Ω] [DecidableEq Ω] {m ms : ℕ}
  {G : Subgroup (Equiv.Perm Ω)}

/-- `ϕ(G_u ∩ ϕ⁻¹H) = ϕ(G_u) ∩ H`: an element of `G_u` whose image lies in `H` already lies
in `ϕ⁻¹H`.  Stated in the form the proofs use: every element of `ϕ(G_u) ∩ H` is `ϕ*(σ)` for
some `σ` in the stabilizer of `u` in `G*`. -/
theorem image_inter_of_preimageSubgroup (ϕ : G →* Equiv.Perm (Fin m))
    (H : Subgroup (Equiv.Perm (Fin m))) {u : Ω} {g : Equiv.Perm (Fin m)}
    (hg : g ∈ (stabilizer G u).map ϕ) (hgH : g ∈ H) :
    ∃ σ ∈ stabilizer (preimageSubgroup ϕ H) u,
      ((phiStar ϕ H σ : H) : Equiv.Perm (Fin m)) = g := by
  obtain ⟨τ, hτ, rfl⟩ := hg
  have hmem : (τ : Equiv.Perm Ω) ∈ preimageSubgroup ϕ H :=
    mem_preimageSubgroup.2 ⟨τ.2, hgH⟩
  refine ⟨⟨(τ : Equiv.Perm Ω), hmem⟩, ?_, ?_⟩
  · rw [MulAction.mem_stabilizer_iff]
    exact (MulAction.mem_stabilizer_iff.1 hτ)
  · rw [coe_phiStar]

/-- **The shared first step of case 3** (the corrected paper. 14.1–14.2, Procedure Align,
"Smallest change", item 3): *"a point of `B_T` can be unaffected only if the stabilizer of
`T` in `Aut(Y)` maps onto a group containing `A(Γ*)`"*.

If `u` is unaffected by `ϕ* = ψ ∘ ϕ|_{G*}` then every `π ∈ A(Γ*)` is `ψ(h)` for some
`h ∈ H` that stabilizes the label `T(u)` setwise.

*Proof.*  Unaffected means `A(Γ*) ≤ ϕ*(G*_u)`, so `π = ϕ*(σ) = ψ(ϕ(σ))` for some
`σ ∈ G*_u`.  Then `ϕ(σ) ∈ H` (that is what `σ ∈ G*` says) and `ϕ(σ) ∈ ϕ(G_u)`, and
Theorem 10.5.1 (a) puts `ϕ(G_u)` inside the setwise stabilizer of `T(u)` in `S(Γ)`. -/
theorem exists_mem_setwiseStab_map_eq_of_unaffected (ϕ : G →* Equiv.Perm (Fin m))
    (hϕ : IsGiantRep ϕ) (hk : VeryLargeK m (maxOrbitLength G))
    (H : Subgroup (Equiv.Perm (Fin m))) (ψ : H →* Equiv.Perm (Fin ms)) {u : Ω}
    (hu : u ∈ unaffectedSet (ψ.comp (phiStar ϕ H)))
    {π : Equiv.Perm (Fin ms)} (hπ : π ∈ alternatingGroup (Fin ms)) :
    ∃ h : H, (h : Equiv.Perm (Fin m)) '' Tpoint ϕ u = Tpoint ϕ u ∧ ψ h = π := by
  have hle : alternatingGroup (Fin ms) ≤
      (stabilizer (preimageSubgroup ϕ H) u).map (ψ.comp (phiStar ϕ H)) := not_not.1 hu
  obtain ⟨σ, hσ, hσπ⟩ := hle hπ
  refine ⟨phiStar ϕ H σ, ?_, hσπ⟩
  -- `ϕ(σ)` lies in `ϕ(G_u)`, which Theorem 10.5.1 (a) puts inside `S(Γ)_{T(u)}`.
  have hsand : IsSandwichSet ((stabilizer G u).map ϕ) (Tpoint ϕ u) :=
    (theorem_10_5_1_a ϕ hϕ hk u).1.2
  have hmemG : (⟨(σ : Equiv.Perm Ω), preimageSubgroup_le ϕ H σ.2⟩ : G) ∈ stabilizer G u := by
    rw [MulAction.mem_stabilizer_iff]
    exact MulAction.mem_stabilizer_iff.1 hσ
  have hmap : ((phiStar ϕ H σ : H) : Equiv.Perm (Fin m)) ∈ (stabilizer G u).map ϕ := by
    refine ⟨⟨(σ : Equiv.Perm Ω), preimageSubgroup_le ϕ H σ.2⟩, hmemG, ?_⟩
    rw [coe_phiStar]
  exact (hsand.2.2 hmap).2

/-! ### The size of a standard block -/

open scoped Classical in
/-- A standard block has at most `2n/3` points: `n = C(m,t)·b` with `C(m,t) ≥ m ≥ 9`
(`Babai.card_univ_eq_mul`, `Babai.le_choose_of_two_mul_le`), so `3b ≤ 2n` already because
`C(m,t) ≥ 2`. -/
theorem three_mul_card_labelFiber_le (hG : IsTransitive G) (ϕ : G →* Equiv.Perm (Fin m))
    (hϕ : IsGiantRep ϕ) (hk : VeryLargeK m (maxOrbitLength G)) (hm3 : 3 ≤ m) {t : ℕ}
    (ht : ∀ u : Ω, tPoint ϕ u = t) (ht1 : 1 ≤ t) (h2t : 2 * t ≤ m)
    (T : Finset (Fin m)) (hT : T.card = t) :
    3 * (labelFiber (Ω := Ω) ϕ T).card ≤ 2 * Fintype.card Ω := by
  have hn := card_univ_eq_mul hG ϕ hϕ hk hm3 ht T hT
  have hc : 2 ≤ m.choose t := le_trans (by omega) (le_choose_of_two_mul_le ht1 h2t)
  rw [hn]
  have := Nat.mul_le_mul_right (labelFiber (Ω := Ω) ϕ T).card hc
  nlinarith [(labelFiber (Ω := Ω) ϕ T).card.zero_le]

end Babai
