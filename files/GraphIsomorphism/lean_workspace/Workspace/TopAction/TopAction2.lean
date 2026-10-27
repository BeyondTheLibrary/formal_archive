/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 12: Corollary 12.0.6 (TopAction2), Remark 12.0.7, Corollary 12.0.8 (TopAction3).
-/
import Workspace.TopAction.Lifting
import Workspace.TopAction.PrelimExtra

/-!
# §12 TopAction2 and TopAction3

Corollary 12.0.6, Remark 12.0.7 and Corollary 12.0.8.

The permutation domain of the giant representation is `Fin m` (`|Γ| = m`), as everywhere
in Section 10, so that the results of Section 10 apply verbatim.
-/

universe u v

namespace Babai

open MulAction Equiv Equiv.Perm
open scoped Pointwise

variable {Ω : Type u} {A : Type v}

/-! ### The image of a set of permutations under `ϕ` -/

/-- The image `K^ϕ` of a set `K ⊆ S(Ω)` of permutations under `ϕ : G → S(Γ)` (only the
elements of `K` that lie in `G` contribute). -/
def homImage {Γ : Type*} {G : Subgroup (Equiv.Perm Ω)} (ϕ : G →* Equiv.Perm Γ)
    (K : Set (Equiv.Perm Ω)) : Set (Equiv.Perm Γ) :=
  {α | ∃ τ ∈ K, ∃ h : τ ∈ G, ϕ ⟨τ, h⟩ = α}

/-- Cor. 12.0.6 (i): "`ϕ` maps `Iso_G(x,y)` onto a giant coset, i.e.
`Iso_G(x,y)^ϕ ≥ A(Γ)τ` for some `τ ∈ S(Γ)`".

The paper's right coset `A(Γ)τ` is Lean's left translate `τ • A(Γ)`
(`Babai.mem_perm_smul_set`). -/
def MapsOntoGiantCoset {m : ℕ} {G : Subgroup (Equiv.Perm Ω)}
    (ϕ : G →* Equiv.Perm (Fin m)) (x y : Ω → A) : Prop :=
  ∃ τ : Equiv.Perm (Fin m),
    τ • ((alternatingGroup (Fin m) : Subgroup (Equiv.Perm (Fin m))) :
      Set (Equiv.Perm (Fin m))) ⊆ homImage ϕ (strIso (G : Set (Equiv.Perm Ω)) x y)

/-- Cor. 12.0.8 (i): "`ϕ` maps `Aut_G(x)` onto a giant, i.e. `Aut_G(x)^ϕ ≥ A(Γ)`." -/
def MapsOntoGiant {m : ℕ} {G : Subgroup (Equiv.Perm Ω)} (ϕ : G →* Equiv.Perm (Fin m))
    (x : Ω → A) : Prop :=
  ((alternatingGroup (Fin m) : Subgroup (Equiv.Perm (Fin m))) : Set (Equiv.Perm (Fin m)))
    ⊆ homImage ϕ (strAut (G : Set (Equiv.Perm Ω)) x)

theorem wAut_univ (K : Set (Equiv.Perm Ω)) (x : Ω → A) :
    wAut Set.univ K x = strAut K x := by
  rw [wAut, wIso_univ, strAut]

/-! ### The two cases of the proof of Cor. 12.0.6

The proof of Cor. 12.0.6 splits into two cases.

* `G^ϕ = A(Γ)`.  "Apply Prop. 12.0.5 to `H := A(Γ)` with `S` a pair of generators of `H`.
  This reduces our questions to three instances of `N`-isomorphism where `N = ker(ϕ)`.
  […] so Luks's Chain Rule performs the desired reduction, calling `3k` instances of
  window size `n/k`."  This is `Babai.giantAReduction`.
* `G^ϕ = S(Γ)`.  "Apply Luks descent, reducing `G`-isomorphism to two instances of
  `G₁`-isomorphism where `G₁ = ϕ⁻¹(A(Γ))`", each handled by the previous case; hence the
  bound `6k`.  This is the second branch of `Babai.topAction2Reduction`. -/

section CaseA

variable [Fintype Ω] [DecidableEq Ω] {m : ℕ} {G' : Subgroup (Equiv.Perm Ω)}

/-- `Iso_K(x,y) = σ Aut_K(x)` for `σ ∈ Iso_K(x,y)` (Remark 11.1.5 (ii) for the full
window).  In Lean's convention the paper's right coset `Aut_K(x)σ` is `σ • Aut_K(x)`. -/
theorem strIso_eq_smul_strAut {K : Subgroup (Equiv.Perm Ω)} {x y : Ω → A}
    {σ : Equiv.Perm Ω} (hσ : σ ∈ strIso (K : Set (Equiv.Perm Ω)) x y) :
    strIso (K : Set (Equiv.Perm Ω)) x y = σ • strAut (K : Set (Equiv.Perm Ω)) x := by
  have h := wIso_eq_smul_wAut_one (isInvariant_univ K) (x := x) (y := y) (σ := σ)
    (by rwa [wIso_univ])
  rwa [wIso_univ, wAut_univ] at h

/-- §12, proof of Cor. 12.0.6, the case `G^ϕ = A(Γ)`: Prop. 12.0.5 with `H = A(Γ)` and a
pair of generators of `H`, each of the three resulting `N`-instances expanded by the Chain
Rule over the orbits of `N`. -/
noncomputable def giantAReduction (ψ : G' →* alternatingGroup (Fin m)) (x y : Ω → A) :
    SIReduction Ω A (Option (Set (Equiv.Perm Ω))) :=
  (TopAction1Reduction ψ x y (altGens m)).expand
    (chainOverOrbits (kerSubgroup ψ))

theorem calls_wrt_TopAction1 (ψ : G' →* alternatingGroup (Fin m)) (x y : Ω → A) :
    ∀ I ∈ (TopAction1Reduction ψ x y (altGens m)).calls,
      I.K = ((kerSubgroup ψ : Subgroup (Equiv.Perm Ω)) : Set (Equiv.Perm Ω)) ∧
        I.Δ = Set.univ := by
  intro I hI
  obtain ⟨h1, h2⟩ := calls_TopAction1Reduction_wrt ψ x y (altGens m) I hI
  exact ⟨h1, h2⟩

open Classical in
/-- The case `G^ϕ = A(Γ)` decides (i) and returns `Iso_{G'}(x,y)`. -/
theorem run_giantAReduction (hm : 3 ≤ m) (ψ : G' →* alternatingGroup (Fin m))
    (x y : Ω → A) :
    (giantAReduction ψ x y).run =
      if MapsOnto ψ x y then some (strIso (G' : Set (Equiv.Perm Ω)) x y) else none := by
  classical
  rw [giantAReduction,
    SIReduction.run_expand_of_calls
      (P := fun I => I.K = ((kerSubgroup ψ : Subgroup (Equiv.Perm Ω)) : Set (Equiv.Perm Ω))
        ∧ I.Δ = Set.univ)
      (fun I hI => run_chainOverOrbits hI.1 hI.2) _ (calls_wrt_TopAction1 ψ x y)]
  exact run_TopAction1Reduction ψ x y (altGens m) (altGens_spec m hm).2

/-- The case `G^ϕ = A(Γ)` makes `3k` calls, `k` the number of orbits of `N`. -/
theorem calls_length_giantAReduction (hm : 3 ≤ m) (ψ : G' →* alternatingGroup (Fin m))
    (x y : Ω → A) :
    (giantAReduction ψ x y).calls.length ≤
      3 * (orbitList (kerSubgroup ψ)).length := by
  have h := SIReduction.calls_expand_length_le_of_calls
    (P := fun I => I.K = ((kerSubgroup ψ : Subgroup (Equiv.Perm Ω)) : Set (Equiv.Perm Ω))
      ∧ I.Δ = Set.univ)
    (fun I hI => run_chainOverOrbits hI.1 hI.2)
    (c := (orbitList (kerSubgroup ψ)).length)
    (fun I _ => calls_length_chainOverOrbits _ I)
    (TopAction1Reduction ψ x y (altGens m)) (calls_wrt_TopAction1 ψ x y)
  rw [giantAReduction]
  refine le_trans h ?_
  rw [calls_length_TopAction1Reduction, (altGens_spec m hm).1]

/-- Every call of the case `G^ϕ = A(Γ)` has its candidate set inside `N = ker(ψ)`. -/
theorem calls_giantAReduction_K (ψ : G' →* alternatingGroup (Fin m)) (x y : Ω → A) :
    ∀ J ∈ (giantAReduction ψ x y).calls,
      J.K ⊆ ((kerSubgroup ψ : Subgroup (Equiv.Perm Ω)) : Set (Equiv.Perm Ω)) := by
  rw [giantAReduction]
  exact SIReduction.mem_calls_expand_of_calls
    (P := fun I => I.K = ((kerSubgroup ψ : Subgroup (Equiv.Perm Ω)) : Set (Equiv.Perm Ω))
      ∧ I.Δ = Set.univ)
    (fun I hI => run_chainOverOrbits hI.1 hI.2)
    (fun I _ => calls_chainOverOrbits_K _ I)
    (TopAction1Reduction ψ x y (altGens m)) (calls_wrt_TopAction1 ψ x y)

/-- Every call of the case `G^ϕ = A(Γ)` has an orbit of `N` for its window. -/
theorem calls_giantAReduction_window (ψ : G' →* alternatingGroup (Fin m)) (x y : Ω → A) :
    ∀ J ∈ (giantAReduction ψ x y).calls, J.Δ ∈ orbitList (kerSubgroup ψ) := by
  rw [giantAReduction]
  exact SIReduction.mem_calls_expand_of_calls
    (P := fun I => I.K = ((kerSubgroup ψ : Subgroup (Equiv.Perm Ω)) : Set (Equiv.Perm Ω))
      ∧ I.Δ = Set.univ)
    (fun I hI => run_chainOverOrbits hI.1 hI.2)
    (fun I _ => calls_chainOverOrbits_window _ I)
    (TopAction1Reduction ψ x y (altGens m)) (calls_wrt_TopAction1 ψ x y)

end CaseA

/-! ### The case `G^ϕ = S(Γ)`: Luks descent to `G₁ = ϕ⁻¹(A(Γ))` -/

section CaseB

variable [Fintype Ω] [DecidableEq Ω] {m : ℕ} {G : Subgroup (Equiv.Perm Ω)}

/-- Membership in `G₁ = ϕ⁻¹(A(Γ))` (`Babai.preimageAlt`, defined in the proof of
Theorem 10.3.5, `AltQuotients/Unaffected.lean`), in the form used in §12. -/
theorem mem_preimageAlt' {ϕ : G →* Equiv.Perm (Fin m)} {τ : Equiv.Perm Ω} :
    τ ∈ preimageAlt ϕ ↔ ∃ h : τ ∈ G, ϕ ⟨τ, h⟩ ∈ alternatingGroup (Fin m) := by
  constructor
  · rintro ⟨⟨g, hg⟩, hmem, rfl⟩
    exact ⟨hg, hmem⟩
  · rintro ⟨h, hmem⟩
    exact ⟨⟨τ, h⟩, hmem, rfl⟩

/-- The giant representation `ϕ` restricted to `G₁ = ϕ⁻¹(A(Γ))`, corestricted to
`A(Γ)`. -/
def altHom (ϕ : G →* Equiv.Perm (Fin m)) : preimageAlt ϕ →* alternatingGroup (Fin m) :=
  MonoidHom.codRestrict (ϕ.comp (Subgroup.inclusion (preimageAlt_le ϕ))) _
    (fun τ => (mem_preimageAlt'.1 τ.2).choose_spec)

@[simp] theorem coe_altHom (ϕ : G →* Equiv.Perm (Fin m)) (τ : preimageAlt ϕ) :
    ((altHom ϕ τ : alternatingGroup (Fin m)) : Equiv.Perm (Fin m)) =
      ϕ ⟨(τ : Equiv.Perm Ω), preimageAlt_le ϕ τ.2⟩ := rfl

/-- `ker(ϕ|_{G₁}) = ker(ϕ)`: the kernel is unchanged by the Luks descent, so the two
`G₁`-instances are reduced over the *same* orbits of `N`, with the same `k`. -/
theorem kerSubgroup_altHom (ϕ : G →* Equiv.Perm (Fin m)) :
    kerSubgroup (altHom ϕ) = kerSubgroup ϕ := by
  ext τ
  rw [mem_kerSubgroup, mem_kerSubgroup]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨preimageAlt_le ϕ h1, ?_⟩
    have := congrArg (fun z : alternatingGroup (Fin m) => (z : Equiv.Perm (Fin m))) h2
    simpa using this
  · rintro ⟨h1, h2⟩
    have hmem : τ ∈ preimageAlt ϕ := mem_preimageAlt'.2 ⟨h1, by rw [h2]; exact one_mem _⟩
    refine ⟨hmem, ?_⟩
    apply Subtype.ext
    simpa using h2

/-! #### The two-element cover `G = G₁ ∪ σ₀ G₁` -/

theorem mul_mem_alternating_of_not_mem {a b : Equiv.Perm (Fin m)}
    (ha : a ∉ alternatingGroup (Fin m)) (hb : b ∉ alternatingGroup (Fin m)) :
    a⁻¹ * b ∈ alternatingGroup (Fin m) := by
  have hsign : ∀ c : Equiv.Perm (Fin m), c ∉ alternatingGroup (Fin m) →
      Equiv.Perm.sign c = -1 := by
    intro c hc
    rw [Equiv.Perm.mem_alternatingGroup] at hc
    rcases Int.units_eq_one_or (Equiv.Perm.sign c) with h | h
    · exact absurd h hc
    · exact h
  rw [Equiv.Perm.mem_alternatingGroup, map_mul, map_inv, hsign a ha, hsign b hb]
  decide

/-- The Luks descent decomposition `G = G₁ ∪ σ₀ G₁`, for any `σ₀ ∈ G` with `ϕ(σ₀)` odd. -/
theorem coe_eq_biUnion_preimageAlt (ϕ : G →* Equiv.Perm (Fin m)) {σ₀ : Equiv.Perm Ω}
    (h₀ : σ₀ ∈ G) (hodd : ϕ ⟨σ₀, h₀⟩ ∉ alternatingGroup (Fin m)) :
    (G : Set (Equiv.Perm Ω)) =
      ⋃ σ ∈ ({1, σ₀} : Set (Equiv.Perm Ω)),
        σ • ((preimageAlt ϕ : Subgroup (Equiv.Perm Ω)) : Set (Equiv.Perm Ω)) := by
  ext g
  rw [Set.biUnion_pair, one_smul]
  constructor
  · intro hg
    by_cases hev : ϕ ⟨g, hg⟩ ∈ alternatingGroup (Fin m)
    · exact Or.inl (mem_preimageAlt'.2 ⟨hg, hev⟩)
    · refine Or.inr ⟨σ₀⁻¹ * g, ?_, show σ₀ * (σ₀⁻¹ * g) = g by group⟩
      have hmem : σ₀⁻¹ * g ∈ G := mul_mem (inv_mem h₀) hg
      refine mem_preimageAlt'.2 ⟨hmem, ?_⟩
      have hsplit : (⟨σ₀⁻¹ * g, hmem⟩ : G) = (⟨σ₀, h₀⟩ : G)⁻¹ * ⟨g, hg⟩ := rfl
      rw [hsplit, map_mul, map_inv]
      exact mul_mem_alternating_of_not_mem hodd hev
  · rintro (h | ⟨t, ht, rfl⟩)
    · exact preimageAlt_le ϕ h
    · exact mul_mem h₀ (preimageAlt_le ϕ ht)

/-- §11.1, Prop. 11.1.6 (Descent) applied to `G₁ ≤ G` with the two coset representatives
`1` and `σ₀`: `Iso_G(x,y) = Iso_{G₁}(x,y) ∪ σ₀ Iso_{G₁}(x, y^{σ₀⁻¹})`. -/
theorem strIso_descent (ϕ : G →* Equiv.Perm (Fin m)) {σ₀ : Equiv.Perm Ω} (h₀ : σ₀ ∈ G)
    (hodd : ϕ ⟨σ₀, h₀⟩ ∉ alternatingGroup (Fin m)) (x y : Ω → A) :
    strIso (G : Set (Equiv.Perm Ω)) x y =
      strIso ((preimageAlt ϕ : Subgroup (Equiv.Perm Ω)) : Set (Equiv.Perm Ω)) x y ∪
        σ₀ • strIso ((preimageAlt ϕ : Subgroup (Equiv.Perm Ω)) : Set (Equiv.Perm Ω)) x
          (strAct y σ₀⁻¹) := by
  have h := descent_of_cover (coe_eq_biUnion_preimageAlt ϕ h₀ hodd) Set.univ x y
  rw [wIso_univ] at h
  rw [h, Set.biUnion_pair]
  simp only [wIso_univ, inv_one, strAct_one, one_smul]

end CaseB

/-! ### The orbits of `N = ker(ϕ)` (proof of Cor. 12.0.6) -/

section Orbits

variable [Fintype Ω] [DecidableEq Ω] {m : ℕ} {G : Subgroup (Equiv.Perm Ω)}

/-- The orbits of `ker(ϕ)` (a subgroup of `G`) and of `Babai.kerSubgroup ϕ` (the same
group, viewed inside `S(Ω)`) are the same. -/
theorem orbit_kerSubgroup (ϕ : G →* Equiv.Perm (Fin m)) (u : Ω) :
    orbit (kerSubgroup ϕ) u = orbit ϕ.ker u := by
  ext w
  simp only [mem_orbit_iff]
  constructor
  · rintro ⟨g, rfl⟩
    obtain ⟨⟨τ, hτG⟩, hτker, hτ⟩ := g.2
    refine ⟨⟨⟨τ, hτG⟩, hτker⟩, ?_⟩
    exact congrArg (fun p : Equiv.Perm Ω => p • u) hτ
  · rintro ⟨g, rfl⟩
    have hmem : ((g : G) : Equiv.Perm Ω) ∈ kerSubgroup ϕ := ⟨(g : G), g.2, rfl⟩
    exact ⟨⟨_, hmem⟩, rfl⟩

/-- Proof of Cor. 12.0.6: "Lemma 10.3.1 … says that `Ω` is affected", i.e. every point of
`Ω` is affected by `ϕ`, when `G` is transitive and `G^ϕ = A(Γ)`. -/
theorem affected_of_transitive (hG : IsTransitive G) (ϕ : G →* Equiv.Perm (Fin m))
    (hϕA : ϕ.range = alternatingGroup (Fin m)) (hm : LargeK m (Nat.card Ω)) (z : Ω) :
    Affected ϕ z := by
  intro hle
  refine lemma_10_3_1 hG ϕ hϕA hm z ?_
  refine le_antisymm ?_ hle
  rw [← hϕA]
  rintro _ ⟨t, -, rfl⟩
  exact ⟨t, rfl⟩

/-- Proof of Cor. 12.0.6: `N = ker(ϕ)` is intransitive, it has `k` orbits for some
`m ≤ k ≤ n`, and all its orbits have the common length `n/k`.

> Now `N` is intransitive with `k` orbits for some `k ≤ n`.  Each orbit has equal length
> (because `N ◁ G`) …  We need to justify the inequality `k ≥ m`.  Lemma 10.3.1 … says
> that `Ω` is affected.  Then the Affected Orbit Lemma (Cor. 10.3.7) asserts that each
> orbit of `N` has length `≤ n/m`.

The conclusion `(orbit N u).ncard * k = n` is the paper's "each orbit has length `n/k`",
stated without `Nat` division. -/
theorem Corollary_12_0_6_orbit_count (hG : IsTransitive G) (ϕ : G →* Equiv.Perm (Fin m))
    (hϕA : ϕ.range = alternatingGroup (Fin m)) (hm : LargeK m (Nat.card Ω)) :
    ∃ k : ℕ, m ≤ k ∧ k ≤ Fintype.card Ω ∧
      ∀ u : Ω, (orbit (kerSubgroup ϕ) u).ncard * k = Fintype.card Ω := by
  classical
  obtain ⟨u₀, hu₀⟩ := id hG
  haveI : Nonempty Ω := ⟨u₀⟩
  have hϕ : IsGiantRep ϕ := by rw [IsGiantRep, hϕA]
  have hm8 : 8 < m := hm.eight_lt
  have hm5 : 5 ≤ m := by omega
  -- every point is affected
  have haff : ∀ z ∈ orbit G u₀, Affected ϕ z := fun z _ =>
    affected_of_transitive hG ϕ hϕA hm z
  -- the Affected Orbit Lemma: `m · |orbit N u| ≤ n`
  have horb : ∀ u : Ω, m * Nat.card (orbit (kerSubgroup ϕ) u) ≤ Fintype.card Ω := by
    intro u
    have hu : u ∈ orbit G u₀ := by rw [hu₀]; trivial
    have hle := (corollary_10_3_7 ϕ hϕ hm5 u₀ haff u hu).1
    have hcard : Nat.card (orbit G u₀ : Set Ω) = Fintype.card Ω := by
      rw [hu₀, Nat.card_coe_set_eq, Set.ncard_univ, Nat.card_eq_fintype_card]
    rw [orbit_kerSubgroup]
    calc m * Nat.card (orbit ϕ.ker u : Set Ω) ≤ Nat.card (orbit G u₀ : Set Ω) := hle
      _ = Fintype.card Ω := hcard
  -- `N` is intransitive
  have hNint : ¬ IsTransitive (kerSubgroup ϕ) := by
    rintro ⟨u, hu⟩
    have h1 : Nat.card (orbit (kerSubgroup ϕ) u) = Fintype.card Ω := by
      rw [hu, Nat.card_coe_set_eq, Set.ncard_univ, Nat.card_eq_fintype_card]
    have h2 := horb u
    rw [h1] at h2
    have hpos : 0 < Fintype.card Ω := Fintype.card_pos
    nlinarith
  obtain ⟨k, hk2, hk⟩ :=
    orbit_ncard_mul_eq_card hG (isNormalIn_kerSubgroup ϕ) hNint
  have hlpos : ∀ u : Ω, 0 < (orbit (kerSubgroup ϕ) u).ncard := by
    intro u
    haveI : Nonempty (orbit (kerSubgroup ϕ) u) := ⟨⟨u, mem_orbit_self u⟩⟩
    rw [← Nat.card_coe_set_eq]
    exact Nat.card_pos
  refine ⟨k, ?_, ?_, hk⟩
  · have h1 := horb u₀
    have h2 := hk u₀
    rw [Nat.card_coe_set_eq] at h1
    have hl := hlpos u₀
    nlinarith
  · have h2 := hk u₀
    have hl := hlpos u₀
    nlinarith

end Orbits

/-! ### `Ω` is affected, and the number `k` of orbits of `N` -/

section Orbits2

variable [Fintype Ω] [DecidableEq Ω] {m : ℕ} {G : Subgroup (Equiv.Perm Ω)}

theorem largeK_maxOrbitLength [Nonempty Ω] (hm : LargeK m (Nat.card Ω)) :
    LargeK m (maxOrbitLength G) := by
  refine hm.mono ?_
  refine csSup_le ⟨Nat.card (orbit G (Classical.arbitrary Ω)), ⟨_, rfl⟩⟩ ?_
  rintro c ⟨x, rfl⟩
  exact Nat.card_le_card_of_injective _ Subtype.val_injective

/-- The unaffected set is `G`-invariant (a step of the proof of Theorem 10.3.5; used here
to see that for a transitive `G` it is `∅` or `Ω`). -/
theorem unaffected_of_mem_orbit (ϕ : G →* Equiv.Perm (Fin m)) {z z' : Ω}
    (hz : z ∈ unaffectedSet ϕ) (g : G) (hg : (g : Equiv.Perm Ω) z = z') :
    z' ∈ unaffectedSet ϕ := by
  have hz' : alternatingGroup (Fin m) ≤ (stabilizer G z).map ϕ := not_not.1 hz
  show ¬ Affected ϕ z'
  rw [Affected, not_not]
  intro α hα
  have hconj : (ϕ g)⁻¹ * α * ϕ g ∈ alternatingGroup (Fin m) := by
    rw [Equiv.Perm.mem_alternatingGroup] at hα ⊢
    rw [map_mul, map_mul, map_inv, hα, mul_one, inv_mul_cancel]
  obtain ⟨s, hs, hsϕ⟩ := hz' hconj
  have hsz : (s : Equiv.Perm Ω) z = z := by
    have h := (mem_stabilizer_iff).1 hs
    simpa [Subgroup.smul_def] using h
  refine ⟨g * s * g⁻¹, ?_, ?_⟩
  · rw [SetLike.mem_coe, mem_stabilizer_iff]
    have hg' : ((g : Equiv.Perm Ω))⁻¹ z' = z := by rw [← hg]; simp
    have hkey : ((g * s * g⁻¹ : G) : Equiv.Perm Ω) z' = z' := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Equiv.Perm.coe_mul, Function.comp_apply]
      rw [hg', hsz, hg]
    simpa [Subgroup.smul_def] using hkey
  · rw [map_mul, map_mul, map_inv, hsϕ]
    group

/-- §12, proof of Cor. 12.0.6: "Lemma 10.3.1 … says that `Ω` is affected", for a giant
representation of a transitive group.

The Lean transcription of Lemma 10.3.1 (`Babai.lemma_10_3_1`) assumes `G^ϕ = A(Γ)`, as the
paper's Lemma 10.3.1 does; the proof of Cor. 12.0.6 cites it also in the case `G^ϕ = S(Γ)`,
where it does not literally apply.  The argument used here is instead the paper's own
Theorem 10.3.5 (Unaffected Stabilizers Lemma), which *is* stated for a giant
representation: the unaffected set `D` is `G`-invariant, so for a transitive `G` it is `∅`
or `Ω`; and if it were `Ω` then `G_(D) = 1`, whereas Theorem 10.3.5 gives `G_(D)^ϕ ≥ A(Γ)`,
impossible for `m ≥ 3`. -/
theorem affected_of_transitive_giant (hG : IsTransitive G) (ϕ : G →* Equiv.Perm (Fin m))
    (hϕ : IsGiantRep ϕ) (hm : LargeK m (Nat.card Ω)) (z : Ω) : Affected ϕ z := by
  intro hle
  have hm8 : 8 < m := hm.eight_lt
  haveI : NeZero m := ⟨by omega⟩
  haveI : Nonempty Ω := ⟨z⟩
  have hzU : z ∈ unaffectedSet ϕ := not_not.2 hle
  obtain ⟨u₀, hu₀⟩ := id hG
  have hD : unaffectedSet ϕ = Set.univ := by
    ext w
    refine ⟨fun _ => trivial, fun _ => ?_⟩
    have hzorb : orbit G z = Set.univ := by
      have h1 : z ∈ orbit G u₀ := by rw [hu₀]; trivial
      rw [(MulAction.orbit_eq_iff (a := z) (b := u₀)).2 h1, hu₀]
    have hwz : w ∈ orbit G z := by rw [hzorb]; trivial
    obtain ⟨g, hg⟩ := hwz
    exact unaffected_of_mem_orbit ϕ hzU g (by simpa [Subgroup.smul_def] using hg)
  have hbot : pointwiseStab G (unaffectedSet ϕ) = ⊥ := by
    rw [hD]
    ext σ
    simp only [mem_pointwiseStab, Subgroup.mem_bot]
    constructor
    · intro h
      exact Subtype.ext (Equiv.ext fun w => h w trivial)
    · rintro rfl w -
      rfl
  have hA := theorem_10_3_5 ϕ hϕ (largeK_maxOrbitLength hm)
  rw [hbot, Subgroup.map_bot] at hA
  set a : Fin m := ⟨0, by omega⟩ with ha
  set b : Fin m := ⟨1, by omega⟩ with hb
  set c : Fin m := ⟨2, by omega⟩ with hc'
  have hab : a ≠ b := by simp [ha, hb, Fin.ext_iff]
  have hac : a ≠ c := by simp [ha, hc', Fin.ext_iff]
  have hbc : b ≠ c := by simp [hb, hc', Fin.ext_iff]
  have hc : Equiv.Perm.IsThreeCycle (Equiv.swap a b * Equiv.swap a c) :=
    Equiv.Perm.isThreeCycle_swap_mul_swap_same hab hac hbc
  have hmem := hA hc.mem_alternatingGroup
  rw [Subgroup.mem_bot] at hmem
  have hval : (Equiv.swap a b * Equiv.swap a c) c = b := by
    simp [Equiv.Perm.mul_apply, Equiv.swap_apply_right, Equiv.swap_apply_left]
  rw [hmem] at hval
  exact hbc hval.symm

/-- The number `k` of orbits of `N = ker(ϕ)` (Cor. 12.0.6). -/
noncomputable def orbCount (ϕ : G →* Equiv.Perm (Fin m)) : ℕ :=
  Nat.card (orbitRel.Quotient (kerSubgroup ϕ) Ω)

/-- §12, Cor. 12.0.6: `N = ker(ϕ)` has `k` orbits for some `m ≤ k ≤ n`, all of the common
length `n/k` (stated without division as `|orbit| · k = n`). -/
theorem orbCount_spec (hG : IsTransitive G) (ϕ : G →* Equiv.Perm (Fin m))
    (hϕ : IsGiantRep ϕ) (hm : LargeK m (Nat.card Ω)) :
    m ≤ orbCount ϕ ∧ orbCount ϕ ≤ Fintype.card Ω ∧
      ∀ u : Ω, (orbit (kerSubgroup ϕ) u).ncard * orbCount ϕ = Fintype.card Ω := by
  classical
  obtain ⟨u₀, hu₀⟩ := id hG
  haveI : Nonempty Ω := ⟨u₀⟩
  have hm8 : 8 < m := hm.eight_lt
  have hcount : ∀ u : Ω, (orbit (kerSubgroup ϕ) u).ncard * orbCount ϕ = Fintype.card Ω :=
    fun u => orbit_ncard_mul_orbitCount hG (isNormalIn_kerSubgroup ϕ) u
  have haff : ∀ z ∈ orbit G u₀, Affected ϕ z := fun z _ =>
    affected_of_transitive_giant hG ϕ hϕ hm z
  have hle := (corollary_10_3_7 ϕ hϕ (by omega) u₀ haff u₀ (mem_orbit_self u₀)).1
  have hcardG : Nat.card (orbit G u₀ : Set Ω) = Fintype.card Ω := by
    rw [hu₀, Nat.card_coe_set_eq, Set.ncard_univ, Nat.card_eq_fintype_card]
  rw [hcardG] at hle
  have hl : Nat.card (orbit ϕ.ker u₀ : Set Ω) = (orbit (kerSubgroup ϕ) u₀).ncard := by
    rw [← orbit_kerSubgroup, Nat.card_coe_set_eq]
  rw [hl] at hle
  have hlpos : 0 < (orbit (kerSubgroup ϕ) u₀).ncard := by
    haveI : Nonempty (orbit (kerSubgroup ϕ) u₀) := ⟨⟨u₀, mem_orbit_self u₀⟩⟩
    rw [← Nat.card_coe_set_eq]
    exact Nat.card_pos
  have h2 := hcount u₀
  refine ⟨?_, ?_, hcount⟩
  · nlinarith
  · nlinarith

end Orbits2

/-! ### `ϕ` maps a set onto a giant coset -/

section GiantCoset

variable [Fintype Ω] [DecidableEq Ω] {m : ℕ} {G : Subgroup (Equiv.Perm Ω)}

theorem mem_homImage {ϕ : G →* Equiv.Perm (Fin m)} {K : Set (Equiv.Perm Ω)}
    {α : Equiv.Perm (Fin m)} :
    α ∈ homImage ϕ K ↔ ∃ τ ∈ K, ∃ h : τ ∈ G, ϕ ⟨τ, h⟩ = α := Iff.rfl

/-- "`ϕ` maps `Iso_{G'}(x,y)` onto `S`" in the form Prop. 12.0.5 uses it, for the
corestriction of a homomorphism to a subgroup `S` containing its image. -/
theorem mapsOnto_codRestrict_iff {G' : Subgroup (Equiv.Perm Ω)}
    (ψ : G' →* Equiv.Perm (Fin m)) (S : Subgroup (Equiv.Perm (Fin m)))
    (hS : ∀ g, ψ g ∈ S) (x y : Ω → A) :
    MapsOnto (ψ.codRestrict S hS) x y ↔
      (S : Set (Equiv.Perm (Fin m))) ⊆ homImage ψ (strIso (G' : Set (Equiv.Perm Ω)) x y) := by
  constructor
  · intro h α hα
    obtain ⟨τ, ⟨hpre, hIso⟩⟩ := h ⟨α, hα⟩
    obtain ⟨hτ, hτϕ⟩ := hpre
    exact ⟨τ, hIso, hτ, congrArg Subtype.val hτϕ⟩
  · intro h σ
    obtain ⟨τ, hIso, hτ, hτϕ⟩ := h σ.2
    exact ⟨τ, ⟨hτ, Subtype.ext hτϕ⟩, hIso⟩

theorem homImage_comp_inclusion {G' : Subgroup (Equiv.Perm Ω)} (hle : G' ≤ G)
    (ϕ : G →* Equiv.Perm (Fin m)) {K : Set (Equiv.Perm Ω)}
    (hK : K ⊆ (G' : Set (Equiv.Perm Ω))) :
    homImage (ϕ.comp (Subgroup.inclusion hle)) K = homImage ϕ K := by
  ext α
  constructor
  · rintro ⟨τ, hτK, h, rfl⟩
    exact ⟨τ, hτK, hle h, rfl⟩
  · rintro ⟨τ, hτK, h, rfl⟩
    exact ⟨τ, hτK, hK hτK, rfl⟩

/-- Cor. 12.0.6 (i) in the case `G^ϕ ≤ A(Γ)`: mapping onto a giant coset is mapping onto
`A(Γ)`, because the image is contained in `A(Γ)` and a coset of `A(Γ)` inside `A(Γ)` is
`A(Γ)`. -/
theorem mapsOntoGiantCoset_iff_of_range_le {ϕ : G →* Equiv.Perm (Fin m)}
    (h : ϕ.range ≤ alternatingGroup (Fin m)) (x y : Ω → A) :
    MapsOntoGiantCoset ϕ x y ↔
      (alternatingGroup (Fin m) : Set (Equiv.Perm (Fin m))) ⊆
        homImage ϕ (strIso (G : Set (Equiv.Perm Ω)) x y) := by
  constructor
  · rintro ⟨τ, hτ⟩
    have hτmem : τ ∈ alternatingGroup (Fin m) := by
      have h1 : τ ∈ τ • ((alternatingGroup (Fin m) : Subgroup (Equiv.Perm (Fin m))) :
          Set (Equiv.Perm (Fin m))) := ⟨1, one_mem _, mul_one τ⟩
      obtain ⟨t, -, ht, rfl⟩ := hτ h1
      exact h ⟨⟨t, ht⟩, rfl⟩
    intro α hα
    have hmem : α ∈ τ • ((alternatingGroup (Fin m) : Subgroup (Equiv.Perm (Fin m))) :
        Set (Equiv.Perm (Fin m))) :=
      ⟨τ⁻¹ * α, mul_mem (inv_mem hτmem) hα, mul_inv_cancel_left τ α⟩
    exact hτ hmem
  · intro h
    refine ⟨1, ?_⟩
    intro β hβ
    rw [one_smul] at hβ
    exact h hβ

/-- Proof of Cor. 12.0.6 in the case `G^ϕ = S(Γ)`: if `ϕ` maps `Iso_G(x,y)` onto a giant
coset then `Aut_G(x)^ϕ ≥ A(Γ)`. -/
theorem alt_subset_autImage (ϕ : G →* Equiv.Perm (Fin m)) {x y : Ω → A}
    (h : MapsOntoGiantCoset ϕ x y) :
    (alternatingGroup (Fin m) : Set (Equiv.Perm (Fin m))) ⊆
      homImage ϕ (strAut (G : Set (Equiv.Perm Ω)) x) := by
  obtain ⟨τ, hτ⟩ := h
  intro β hβ
  obtain ⟨a, haIso, haG, haϕ⟩ := hτ (⟨1, one_mem _, mul_one τ⟩ :
    τ ∈ τ • ((alternatingGroup (Fin m) : Subgroup (Equiv.Perm (Fin m))) :
      Set (Equiv.Perm (Fin m))))
  obtain ⟨b, hbIso, hbG, hbϕ⟩ := hτ (⟨β, hβ, rfl⟩ :
    τ * β ∈ τ • ((alternatingGroup (Fin m) : Subgroup (Equiv.Perm (Fin m))) :
      Set (Equiv.Perm (Fin m))))
  rw [strIso_eq_smul_strAut haIso] at hbIso
  obtain ⟨w, hwAut, hw⟩ := hbIso
  have hwG : w ∈ G := hwAut.1
  refine ⟨w, hwAut, hwG, ?_⟩
  have hsplit : (⟨b, hbG⟩ : G) = ⟨a, haG⟩ * ⟨w, hwG⟩ := Subtype.ext hw.symm
  rw [hsplit, map_mul, haϕ] at hbϕ
  have : τ * ϕ ⟨w, hwG⟩ = τ * β := by rw [← hbϕ]; group
  exact mul_left_cancel this

end GiantCoset

/-! ### The two branches of the Luks descent -/

section Branches

variable [Fintype Ω] [DecidableEq Ω] {m : ℕ} {G : Subgroup (Equiv.Perm Ω)}

/-- Proof of Cor. 12.0.6, case `G^ϕ = S(Γ)`: if `Aut_G(x)^ϕ ≥ A(Γ)` and a branch of the
Luks descent is nonempty, then `ϕ` maps that branch onto `A(Γ)`.  (This is the step the
paper leaves implicit: the "affirmative" answer has to be detected on each of the two
`G₁`-instances separately.) -/
theorem alt_subset_branch (ϕ : G →* Equiv.Perm (Fin m)) {x : Ω → A}
    (hgiant : (alternatingGroup (Fin m) : Set (Equiv.Perm (Fin m))) ⊆
      homImage ϕ (strAut (G : Set (Equiv.Perm Ω)) x))
    {y' : Ω → A} {ρ : Equiv.Perm Ω}
    (hρ : ρ ∈ strIso ((preimageAlt ϕ : Subgroup (Equiv.Perm Ω)) :
      Set (Equiv.Perm Ω)) x y') :
    (alternatingGroup (Fin m) : Set (Equiv.Perm (Fin m))) ⊆
      homImage ϕ (strIso ((preimageAlt ϕ : Subgroup (Equiv.Perm Ω)) :
        Set (Equiv.Perm Ω)) x y') := by
  intro α hα
  obtain ⟨hρG, hρA⟩ := mem_preimageAlt'.1 hρ.1
  have htarget : (ϕ ⟨ρ, hρG⟩)⁻¹ * α ∈ alternatingGroup (Fin m) :=
    mul_mem (inv_mem hρA) hα
  obtain ⟨w, hwAut, hwG, hwϕ⟩ := hgiant htarget
  have hwG1 : w ∈ preimageAlt ϕ := mem_preimageAlt'.2 ⟨hwG, by rw [hwϕ]; exact htarget⟩
  have hwAut1 : w ∈ strAut ((preimageAlt ϕ : Subgroup (Equiv.Perm Ω)) :
      Set (Equiv.Perm Ω)) x := ⟨hwG1, hwAut.2⟩
  refine ⟨ρ * w, ?_, mul_mem hρG hwG, ?_⟩
  · rw [strIso_eq_smul_strAut hρ]
    exact ⟨w, hwAut1, rfl⟩
  · rw [show (⟨ρ * w, mul_mem hρG hwG⟩ : G) = ⟨ρ, hρG⟩ * ⟨w, hwG⟩ from rfl, map_mul, hwϕ,
      mul_inv_cancel_left]

/-- Proof of Cor. 12.0.6, case `G^ϕ = S(Γ)`: if `ϕ` maps one branch of the Luks descent
onto `A(Γ)` then it maps `Iso_G(x,y)` onto a giant coset. -/
theorem mapsOntoGiantCoset_of_branch (ϕ : G →* Equiv.Perm (Fin m)) {σ : Equiv.Perm Ω}
    (hσ : σ ∈ G) {x y y' : Ω → A}
    (hsub : σ • strIso ((preimageAlt ϕ : Subgroup (Equiv.Perm Ω)) :
      Set (Equiv.Perm Ω)) x y' ⊆ strIso (G : Set (Equiv.Perm Ω)) x y)
    (h : (alternatingGroup (Fin m) : Set (Equiv.Perm (Fin m))) ⊆
      homImage ϕ (strIso ((preimageAlt ϕ : Subgroup (Equiv.Perm Ω)) :
        Set (Equiv.Perm Ω)) x y')) :
    MapsOntoGiantCoset ϕ x y := by
  refine ⟨ϕ ⟨σ, hσ⟩, ?_⟩
  rintro _ ⟨α, hα, rfl⟩
  obtain ⟨ρ, hρ, hρG, hρϕ⟩ := h hα
  refine ⟨σ * ρ, hsub ⟨ρ, hρ, rfl⟩, mul_mem hσ hρG, ?_⟩
  rw [show (⟨σ * ρ, mul_mem hσ hρG⟩ : G) = ⟨σ, hσ⟩ * ⟨ρ, hρG⟩ from rfl, map_mul, hρϕ]
  rfl

open Classical in
/-- A `σ₀ ∈ G` with `ϕ(σ₀)` odd: the second coset representative of the Luks descent. -/
noncomputable def oddRep (ϕ : G →* Equiv.Perm (Fin m)) : Equiv.Perm Ω :=
  if h : ∃ σ : G, ϕ σ ∉ alternatingGroup (Fin m) then ((h.choose : G) : Equiv.Perm Ω)
  else 1

theorem oddRep_spec (ϕ : G →* Equiv.Perm (Fin m))
    (h : ∃ σ : G, ϕ σ ∉ alternatingGroup (Fin m)) :
    ∃ hG : oddRep ϕ ∈ G, ϕ ⟨oddRep ϕ, hG⟩ ∉ alternatingGroup (Fin m) := by
  classical
  rw [oddRep, dif_pos h]
  refine ⟨h.choose.2, ?_⟩
  have : (⟨((h.choose : G) : Equiv.Perm Ω), h.choose.2⟩ : G) = h.choose := rfl
  rw [this]
  exact h.choose_spec

theorem exists_odd_of_not_range_le {ϕ : G →* Equiv.Perm (Fin m)}
    (h : ¬ ϕ.range ≤ alternatingGroup (Fin m)) :
    ∃ σ : G, ϕ σ ∉ alternatingGroup (Fin m) := by
  by_contra hc
  refine h (fun α hα => ?_)
  obtain ⟨σ, rfl⟩ := hα
  by_contra hmem
  exact hc ⟨σ, hmem⟩

end Branches

/-! ### Corollary 12.0.6 (TopAction2) -/

section Reduction

variable [Fintype Ω] [DecidableEq Ω] {m : ℕ} {G : Subgroup (Equiv.Perm Ω)}

/-- `ker(ϕ)` is unchanged by corestricting `ϕ` to a subgroup containing its image. -/
theorem kerSubgroup_codRestrict (ϕ : G →* Equiv.Perm (Fin m))
    (S : Subgroup (Equiv.Perm (Fin m))) (hS : ∀ g, ϕ g ∈ S) :
    kerSubgroup (ϕ.codRestrict S hS) = kerSubgroup ϕ := by
  ext τ
  rw [mem_kerSubgroup, mem_kerSubgroup]
  exact ⟨fun ⟨h1, h2⟩ => ⟨h1, congrArg Subtype.val h2⟩, fun ⟨h1, h2⟩ => ⟨h1, Subtype.ext h2⟩⟩

open Classical in
/-- §12, **Corollary 12.0.6** (TopAction2): the reduction.

Case `G^ϕ ≤ A(Γ)`: Prop. 12.0.5 with `H = A(Γ)` and a pair of generators, followed by the
Chain Rule over the `k` orbits of `N` (`Babai.giantAReduction`), `3k` calls.

Case `G^ϕ ⊄ A(Γ)`: Luks descent to `G₁ = ϕ⁻¹(A(Γ))` with the two coset representatives `1`
and `σ₀ = oddRep ϕ`, each branch handled by the previous case, `6k` calls. -/
noncomputable def topAction2Reduction (ϕ : G →* Equiv.Perm (Fin m)) (x y : Ω → A) :
    SIReduction Ω A (Option (Set (Equiv.Perm Ω))) :=
  if h : ϕ.range ≤ alternatingGroup (Fin m) then
    giantAReduction (ϕ.codRestrict _ (fun g => h ⟨g, rfl⟩)) x y
  else
    (giantAReduction (altHom ϕ) x y).bind fun r1 =>
      (giantAReduction (altHom ϕ) x (strAct y (oddRep ϕ)⁻¹)).bind fun r2 =>
        .done (if r1 = none ∧ r2 = none then none
          else some (r1.getD ∅ ∪ (oddRep ϕ) • r2.getD ∅))

/-! #### The number of calls and the window sizes -/

theorem orbitList_altHom (ϕ : G →* Equiv.Perm (Fin m)) :
    orbitList (kerSubgroup (altHom ϕ)) = orbitList (kerSubgroup ϕ) := by
  rw [kerSubgroup_altHom]

theorem calls_length_topAction2Reduction (hm3 : 3 ≤ m) (ϕ : G →* Equiv.Perm (Fin m))
    (x y : Ω → A) :
    (topAction2Reduction ϕ x y).calls.length ≤ 6 * orbCount ϕ := by
  classical
  have hk : (orbitList (kerSubgroup ϕ)).length = orbCount ϕ :=
    length_orbitList (kerSubgroup ϕ)
  rw [topAction2Reduction]
  by_cases h : ϕ.range ≤ alternatingGroup (Fin m)
  · rw [dif_pos h]
    have := calls_length_giantAReduction hm3 (ϕ.codRestrict _ (fun g => h ⟨g, rfl⟩)) x y
    rw [kerSubgroup_codRestrict, hk] at this
    omega
  · rw [dif_neg h, SIReduction.calls_bind, SIReduction.calls_bind,
      SIReduction.calls_done, List.length_append, List.length_append]
    have h1 := calls_length_giantAReduction hm3 (altHom ϕ) x y
    have h2 := calls_length_giantAReduction hm3 (altHom ϕ) x (strAct y (oddRep ϕ)⁻¹)
    rw [orbitList_altHom, hk] at h1 h2
    simp only [List.length_nil]
    omega

theorem calls_topAction2Reduction_window (ϕ : G →* Equiv.Perm (Fin m)) (x y : Ω → A) :
    ∀ I ∈ (topAction2Reduction ϕ x y).calls, I.Δ ∈ orbitList (kerSubgroup ϕ) := by
  classical
  rw [topAction2Reduction]
  by_cases h : ϕ.range ≤ alternatingGroup (Fin m)
  · rw [dif_pos h]
    have := calls_giantAReduction_window (ϕ.codRestrict _ (fun g => h ⟨g, rfl⟩)) x y
    rwa [kerSubgroup_codRestrict] at this
  · rw [dif_neg h, SIReduction.calls_bind, SIReduction.calls_bind,
      SIReduction.calls_done]
    have h1 := calls_giantAReduction_window (altHom ϕ) x y
    have h2 := calls_giantAReduction_window (altHom ϕ) x (strAct y (oddRep ϕ)⁻¹)
    rw [orbitList_altHom] at h1 h2
    intro I hI
    simp only [List.append_nil, List.mem_append] at hI
    rcases hI with hI | hI
    · exact h1 I hI
    · exact h2 I hI


/-- `MapsOnto` for the descended representation `ϕ₁ : G₁ → A(Γ)`. -/
theorem mapsOnto_altHom_iff (ϕ : G →* Equiv.Perm (Fin m)) (x y' : Ω → A) :
    MapsOnto (altHom ϕ) x y' ↔
      (alternatingGroup (Fin m) : Set (Equiv.Perm (Fin m))) ⊆
        homImage ϕ (strIso ((preimageAlt ϕ : Subgroup (Equiv.Perm Ω)) :
          Set (Equiv.Perm Ω)) x y') := by
  rw [altHom, mapsOnto_codRestrict_iff,
    homImage_comp_inclusion (preimageAlt_le ϕ) ϕ (fun τ hτ => hτ.1)]

/-- Proof of Cor. 12.0.6, case `G^ϕ = S(Γ)`: `ϕ` maps `Iso_G(x,y)` onto a giant coset
exactly when it maps one of the two branches of the Luks descent onto `A(Γ)`. -/
theorem mapsOntoGiantCoset_iff_branches (ϕ : G →* Equiv.Perm (Fin m))
    {σ₀ : Equiv.Perm Ω} (hσG : σ₀ ∈ G)
    (hσodd : ϕ ⟨σ₀, hσG⟩ ∉ alternatingGroup (Fin m)) (x y : Ω → A) :
    MapsOntoGiantCoset ϕ x y ↔
      ((alternatingGroup (Fin m) : Set (Equiv.Perm (Fin m))) ⊆
          homImage ϕ (strIso ((preimageAlt ϕ : Subgroup (Equiv.Perm Ω)) :
            Set (Equiv.Perm Ω)) x y) ∨
        (alternatingGroup (Fin m) : Set (Equiv.Perm (Fin m))) ⊆
          homImage ϕ (strIso ((preimageAlt ϕ : Subgroup (Equiv.Perm Ω)) :
            Set (Equiv.Perm Ω)) x (strAct y σ₀⁻¹))) := by
  have hdesc := strIso_descent ϕ hσG hσodd x y
  constructor
  · intro hM
    have hgiant := alt_subset_autImage ϕ hM
    obtain ⟨τ, hτ⟩ := hM
    obtain ⟨t, htIso, -, -⟩ := hτ (⟨1, one_mem _, mul_one τ⟩ :
      τ ∈ τ • ((alternatingGroup (Fin m) : Subgroup (Equiv.Perm (Fin m))) :
        Set (Equiv.Perm (Fin m))))
    rw [hdesc] at htIso
    rcases htIso with ht | ⟨s, hs, -⟩
    · exact Or.inl (alt_subset_branch ϕ hgiant ht)
    · exact Or.inr (alt_subset_branch ϕ hgiant hs)
  · rintro (h1 | h2)
    · refine mapsOntoGiantCoset_of_branch ϕ (one_mem G) ?_ h1
      rw [one_smul, hdesc]
      exact Set.subset_union_left
    · refine mapsOntoGiantCoset_of_branch ϕ hσG ?_ h2
      rw [hdesc]
      exact Set.subset_union_right

open Classical in
/-- §12, **Corollary 12.0.6** (TopAction2), items (i) and (ii): the reduction decides
whether `ϕ` maps `Iso_G(x,y)` onto a giant coset, and returns `Iso_G(x,y)` when it does. -/
theorem run_topAction2Reduction (hm3 : 3 ≤ m) (ϕ : G →* Equiv.Perm (Fin m)) (x y : Ω → A) :
    (topAction2Reduction ϕ x y).run =
      if MapsOntoGiantCoset ϕ x y then some (strIso (G : Set (Equiv.Perm Ω)) x y)
      else none := by
  classical
  rw [topAction2Reduction]
  by_cases h : ϕ.range ≤ alternatingGroup (Fin m)
  · rw [dif_pos h, run_giantAReduction hm3]
    have hiff : MapsOnto (ϕ.codRestrict (alternatingGroup (Fin m)) (fun g => h ⟨g, rfl⟩)) x y
        ↔ MapsOntoGiantCoset ϕ x y := by
      rw [mapsOnto_codRestrict_iff, mapsOntoGiantCoset_iff_of_range_le h]
    by_cases hM : MapsOntoGiantCoset ϕ x y
    · rw [if_pos (hiff.2 hM), if_pos hM]
    · rw [if_neg (fun hc => hM (hiff.1 hc)), if_neg hM]
  · obtain ⟨hσG, hσodd⟩ := oddRep_spec ϕ (exists_odd_of_not_range_le h)
    rw [dif_neg h, SIReduction.run_bind, SIReduction.run_bind, SIReduction.run_done,
      run_giantAReduction hm3, run_giantAReduction hm3]
    have hdesc := strIso_descent ϕ hσG hσodd x y
    have hbr := mapsOntoGiantCoset_iff_branches ϕ hσG hσodd x y
    have hA1 := mapsOnto_altHom_iff ϕ x y
    have hA2 := mapsOnto_altHom_iff ϕ x (strAct y (oddRep ϕ)⁻¹)
    by_cases hM : MapsOntoGiantCoset ϕ x y
    · have hgiant := alt_subset_autImage ϕ hM
      have hv1 : (if MapsOnto (altHom ϕ) x y then
          some (strIso ((preimageAlt ϕ : Subgroup (Equiv.Perm Ω)) :
            Set (Equiv.Perm Ω)) x y) else none).getD ∅ =
          strIso ((preimageAlt ϕ : Subgroup (Equiv.Perm Ω)) : Set (Equiv.Perm Ω)) x y := by
        by_cases hp : MapsOnto (altHom ϕ) x y
        · rw [if_pos hp]; rfl
        · rw [if_neg hp]
          rw [Option.getD_none]
          symm
          rw [Set.eq_empty_iff_forall_notMem]
          intro ρ hρ
          exact hp (hA1.2 (alt_subset_branch ϕ hgiant hρ))
      have hv2 : (if MapsOnto (altHom ϕ) x (strAct y (oddRep ϕ)⁻¹) then
          some (strIso ((preimageAlt ϕ : Subgroup (Equiv.Perm Ω)) :
            Set (Equiv.Perm Ω)) x (strAct y (oddRep ϕ)⁻¹)) else none).getD ∅ =
          strIso ((preimageAlt ϕ : Subgroup (Equiv.Perm Ω)) : Set (Equiv.Perm Ω)) x
            (strAct y (oddRep ϕ)⁻¹) := by
        by_cases hp : MapsOnto (altHom ϕ) x (strAct y (oddRep ϕ)⁻¹)
        · rw [if_pos hp]; rfl
        · rw [if_neg hp]
          rw [Option.getD_none]
          symm
          rw [Set.eq_empty_iff_forall_notMem]
          intro ρ hρ
          exact hp (hA2.2 (alt_subset_branch ϕ hgiant hρ))
      have hnn : ¬ ((if MapsOnto (altHom ϕ) x y then
            some (strIso ((preimageAlt ϕ : Subgroup (Equiv.Perm Ω)) :
              Set (Equiv.Perm Ω)) x y) else none) = none ∧
          (if MapsOnto (altHom ϕ) x (strAct y (oddRep ϕ)⁻¹) then
            some (strIso ((preimageAlt ϕ : Subgroup (Equiv.Perm Ω)) :
              Set (Equiv.Perm Ω)) x (strAct y (oddRep ϕ)⁻¹)) else none) = none) := by
        rintro ⟨e1, e2⟩
        rcases hbr.1 hM with hb | hb
        · rw [if_pos (hA1.2 hb)] at e1; exact absurd e1 (by simp)
        · rw [if_pos (hA2.2 hb)] at e2; exact absurd e2 (by simp)
      rw [if_neg hnn, if_pos hM, hv1, hv2, hdesc]
    · have hnone1 : (if MapsOnto (altHom ϕ) x y then
          some (strIso ((preimageAlt ϕ : Subgroup (Equiv.Perm Ω)) :
            Set (Equiv.Perm Ω)) x y) else none) = none := by
        rw [if_neg (fun hp => hM (hbr.2 (Or.inl (hA1.1 hp))))]
      have hnone2 : (if MapsOnto (altHom ϕ) x (strAct y (oddRep ϕ)⁻¹) then
          some (strIso ((preimageAlt ϕ : Subgroup (Equiv.Perm Ω)) :
            Set (Equiv.Perm Ω)) x (strAct y (oddRep ϕ)⁻¹)) else none) = none := by
        rw [if_neg (fun hp => hM (hbr.2 (Or.inr (hA2.1 hp))))]
      rw [if_pos ⟨hnone1, hnone2⟩, if_neg hM]

end Reduction


open Classical in
/-- §12, **Corollary 12.0.6** (TopAction2).

> Let `G ≤ S(Ω)` be a transitive permutation group and `ϕ : G → S(Γ)` a giant
> representation, where `|Γ| = m > max{8, 2 + log₂ n}`.  Given these data and the strings
> `x, y : Ω → Σ`, we can achieve the following by recursively calling `≤ 6k` instances of
> String Isomorphism with window size `≤ n/k` for some `m ≤ k ≤ n`, at polynomial cost per
> instance:
> (i) decide whether `ϕ` maps `Iso_G(x,y)` onto a giant coset, i. e.,
>     `Iso_G(x,y)^ϕ ≥ A(Γ)τ` for some `τ ∈ S(Γ)`;
> (ii) if the answer is affirmative, find `Iso_G(x,y)`.
>
> *Proof.*  First assume `G^ϕ = A(Γ)`.  Apply Prop. 12.0.5 to `H := A(Γ)` with `S` a pair
> of generators of `H`.  This reduces our questions to three instances of `N`-isomorphism
> where `N = ker(ϕ)`.  Now `N` is intransitive with `k` orbits for some `k ≤ n`.  Each
> orbit has equal length (because `N ◁ G`) so Luks's Chain Rule performs the desired
> reduction, calling `3k` instances of window size `n/k`.  We need to justify the
> inequality `k ≥ m`. […]  Now if `G^ϕ = S(Γ)` then apply Luks descent, reducing
> `G`-isomorphism to two instances of `G₁`-isomorphism where `G₁ = ϕ⁻¹(A(Γ))`.

The hypothesis `|Γ| = m > max{8, 2 + log₂ n}` is `Babai.LargeK m n`.  The window-size
bound `≤ n/k` is stated without `Nat` division, as `k · |Δ| ≤ n`.  The value of the
reduction is `none` when the answer to (i) is "no" and `some Iso_G(x,y)` when it is "yes".
The RAM round is `Algo.top2Round` (`Workspace/Algo/TopWindowRound.lean`,
`Algo.implements_top2Round`).

The statement is about the **named** reduction `Babai.topAction2Reduction`, built from the
paper's two cases, and `k = Babai.orbCount ϕ` is the number of orbits of `N = ker(ϕ)`, as
in the proof.  (An earlier version of this file stated the corollary as
`∃ k R, … R.run = …`, which `R := .done answer` satisfies with no calls at all; that form
carries no call accounting.  With a named reduction the trivial witness is not available:
`run_topAction2Reduction` is a theorem about `topAction2Reduction`.)

Ingredients: `Babai.giantAReduction` (Prop. 12.0.5 with `H = A(Γ)` and the two generators
`Babai.altGens`, each of the three `N`-instances expanded by the Chain Rule
`Babai.chainOverOrbits` over the `k` orbits of `N`); `Babai.strIso_descent` (Luks descent
with the two coset representatives `1` and `σ₀ = Babai.oddRep ϕ`);
`Babai.mapsOntoGiantCoset_iff_branches` for the correctness of the descent branch;
`Babai.orbCount_spec` for `m ≤ k ≤ n` and the common orbit length `n/k`.

One step of the paper's proof is replaced: the proof cites Lemma 10.3.1 for "`Ω` is
affected", but that lemma is stated (in the paper and here) for an epimorphism onto
`A(Γ)`, so it does not apply when `G^ϕ = S(Γ)`.  We use the paper's Theorem 10.3.5
instead; see `Babai.affected_of_transitive_giant` and the corresponding the corrected paper
entry. -/
theorem Corollary_12_0_6 [Fintype Ω] [DecidableEq Ω] {m : ℕ}
    {G : Subgroup (Equiv.Perm Ω)} (hG : IsTransitive G) (ϕ : G →* Equiv.Perm (Fin m))
    (hϕ : IsGiantRep ϕ) (hm : LargeK m (Nat.card Ω)) (x y : Ω → A) :
    m ≤ orbCount ϕ ∧ orbCount ϕ ≤ Fintype.card Ω ∧
      (topAction2Reduction ϕ x y).calls.length ≤ 6 * orbCount ϕ ∧
      (∀ I ∈ (topAction2Reduction ϕ x y).calls,
        orbCount ϕ * I.windowSize ≤ Fintype.card Ω) ∧
      (topAction2Reduction ϕ x y).run =
        if MapsOntoGiantCoset ϕ x y then some (strIso (G : Set (Equiv.Perm Ω)) x y)
        else none := by
  classical
  obtain ⟨hmk, hkn, hlen⟩ := orbCount_spec hG ϕ hϕ hm
  have hm3 : 3 ≤ m := by have := hm.eight_lt; omega
  refine ⟨hmk, hkn, calls_length_topAction2Reduction hm3 ϕ x y, ?_,
    run_topAction2Reduction hm3 ϕ x y⟩
  intro I hI
  obtain ⟨u, hu⟩ := mem_orbitList (calls_topAction2Reduction_window ϕ x y I hI)
  rw [SIInstance.windowSize, hu, mul_comm, hlen u]

/-- Self-audit: the hypotheses of Cor. 12.0.6 are simultaneously satisfiable.  Take
`Ω = Γ = [20]`, `G = S(Ω)` and `ϕ` the identity representation: `G` is transitive, `ϕ` is a
giant representation, and `m = 20 > max{8, 2 + log₂ 20}`. -/
example : ∃ (m : ℕ) (G : Subgroup (Equiv.Perm (Fin 20))) (ϕ : G →* Equiv.Perm (Fin m)),
    IsTransitive G ∧ IsGiantRep ϕ ∧ LargeK m (Nat.card (Fin 20)) := by
  refine ⟨20, ⊤, (⊤ : Subgroup (Equiv.Perm (Fin 20))).subtype, ⟨0, ?_⟩, ?_, ?_⟩
  · ext z
    refine ⟨fun _ => trivial, fun _ => ?_⟩
    exact ⟨⟨Equiv.swap 0 z, trivial⟩, by simp [Subgroup.smul_def]⟩
  · rw [IsGiantRep, Subgroup.subtype_range]
    exact le_top
  · rw [LargeK, max_lt_iff]
    refine ⟨by norm_num, ?_⟩
    have hlt : Real.logb 2 (Nat.card (Fin 20)) < 18 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_fin]
      rw [Real.logb_lt_iff_lt_rpow (by norm_num) (by norm_num)]
      have h2 : ((2 : ℝ) ^ (18 : ℝ)) = ((2 : ℝ) ^ (18 : ℕ)) := by
        rw [← Real.rpow_natCast (2 : ℝ) 18]; norm_num
      rw [h2]
      norm_num
    push_cast
    linarith

/-! ### Remark 12.0.7 -/

/-- §12, **Remark 12.0.7**, *as printed*.

> If `m ≥ max{9, 2 log₂ n}` then `n/k = (m choose t)` for some `1 ≤ t < m/4` by item (e) of
> the Main Structure Theorem (Theorem 10.5.1).

Here `k` is the number of orbits of `N = ker(ϕ)` and `n/k` is their common length
(Cor. 12.0.6).  This statement is **false**; see `Babai.not_Remark_12_0_7_as_printed` for a
proved counterexample, and `Babai.Remark_12_0_7_statement` for what item (e) does give. -/
def Remark_12_0_7_as_printed : Prop :=
  ∀ (Ω : Type) [Fintype Ω] [DecidableEq Ω] (m : ℕ) (G : Subgroup (Equiv.Perm Ω))
    (ϕ : G →* Equiv.Perm (Fin m)),
    IsTransitive G → IsGiantRep ϕ → VeryLargeK m (Nat.card Ω) →
    ∀ k : ℕ, (∀ u : Ω, (orbit (kerSubgroup ϕ) u).ncard * k = Fintype.card Ω) →
      ∃ t : ℕ, 1 ≤ t ∧ 4 * t < m ∧
        ∀ u : Ω, (orbit (kerSubgroup ϕ) u).ncard = m.choose t

/-- Remark 12.0.7 is false as printed.

Counterexample: `Ω = Γ = [20]`, `G = S(Ω) = ⊤`, `ϕ` the identity representation, `m = 20`.
Then `G` is transitive, `ϕ` is a giant representation and `m ≥ max{9, 2 log₂ 20}`, while
`N = ker(ϕ) = 1`, so every `N`-orbit is a singleton and `n/k = 1`.  But `1 ≤ t < m/4 = 5`
forces `t ≤ 4`, and `(20 choose t) ≥ 20 > 1` for every such `t`.

What item (e) of Theorem 10.5.1 does give is that `N` fixes every standard block setwise,
so each `N`-orbit lies in one standard block; `G` is transitive on the `(m choose t)`
standard blocks and normalizes `N`, so every block contains the same number of `N`-orbits,
whence `(m choose t)` *divides* `k` — which is `Babai.Remark_12_0_7_statement`.  In the
counterexample the standard blocks are the singletons, `t = 1`, and `(20 choose 1) = 20 = k`.
See the corrected paper. -/
theorem not_Remark_12_0_7_as_printed : ¬ Remark_12_0_7_as_printed := by
  intro h
  have hcard : Nat.card (Fin 20) = 20 := by simp
  have hvl : VeryLargeK 20 (Nat.card (Fin 20)) := by
    rw [VeryLargeK, max_le_iff, hcard]
    refine ⟨by norm_num, ?_⟩
    have hlt : Real.logb 2 (20 : ℕ) ≤ 10 := by
      rw [show ((20 : ℕ) : ℝ) = (20 : ℝ) by norm_num]
      rw [Real.logb_le_iff_le_rpow (by norm_num) (by norm_num)]
      have h2 : ((2 : ℝ) ^ (10 : ℝ)) = ((2 : ℝ) ^ (10 : ℕ)) := by
        rw [← Real.rpow_natCast (2 : ℝ) 10]; norm_num
      rw [h2]; norm_num
    push_cast at hlt ⊢
    linarith
  have htrans : IsTransitive (⊤ : Subgroup (Equiv.Perm (Fin 20))) := by
    refine ⟨0, ?_⟩
    ext z
    refine ⟨fun _ => trivial, fun _ => ?_⟩
    exact ⟨⟨Equiv.swap 0 z, trivial⟩, by simp [Subgroup.smul_def]⟩
  have hgiant : IsGiantRep (⊤ : Subgroup (Equiv.Perm (Fin 20))).subtype := by
    rw [IsGiantRep, Subgroup.subtype_range]
    exact le_top
  -- `N = ker(subtype) = 1`, so every orbit is a singleton
  have hker : ∀ u : Fin 20,
      (orbit (kerSubgroup (⊤ : Subgroup (Equiv.Perm (Fin 20))).subtype) u) = {u} := by
    intro u
    ext w
    simp only [Set.mem_singleton_iff, mem_orbit_iff]
    constructor
    · rintro ⟨⟨τ, hτ⟩, rfl⟩
      obtain ⟨hτG, hτ1⟩ := mem_kerSubgroup.1 hτ
      have hτ' : τ = 1 := hτ1
      rw [Subgroup.smul_def]
      simp only [hτ']
      rfl
    · rintro rfl
      exact ⟨1, by simp⟩
  have hone : ∀ u : Fin 20,
      (orbit (kerSubgroup (⊤ : Subgroup (Equiv.Perm (Fin 20))).subtype) u).ncard = 1 := by
    intro u; rw [hker u, Set.ncard_singleton]
  obtain ⟨t, ht1, ht4, ht⟩ :=
    h (Fin 20) 20 ⊤ (⊤ : Subgroup (Equiv.Perm (Fin 20))).subtype htrans hgiant hvl 20
      (fun u => by rw [hone u]; simp)
  have h1 := ht 0
  rw [hone 0] at h1
  have ht4' : t ≤ 4 := by omega
  interval_cases t <;> exact absurd h1 (by decide)

/-- §12, **Remark 12.0.7**, restated.

The remark is never used, in Section 12 or later, so it is recorded as a statement only
(as `Babai.Remark_10_3_2_statement` is in Section 10).  What is printed is false
(`Babai.not_Remark_12_0_7_as_printed`); what item (e) of Theorem 10.5.1 gives is that
`(m choose t)` divides the number `k` of `N`-orbits, hence `k ≥ (m choose t)` and the
common orbit length `n/k` divides the standard-block size `n/(m choose t)`. -/
def Remark_12_0_7_statement : Prop :=
  ∀ (Ω : Type) [Fintype Ω] [DecidableEq Ω] (m : ℕ) (G : Subgroup (Equiv.Perm Ω))
    (ϕ : G →* Equiv.Perm (Fin m)),
    IsTransitive G → IsGiantRep ϕ → VeryLargeK m (Nat.card Ω) →
    ∀ k : ℕ, (∀ u : Ω, (orbit (kerSubgroup ϕ) u).ncard * k = Fintype.card Ω) →
      ∃ t : ℕ, 1 ≤ t ∧ 4 * t < m ∧ m.choose t ∣ k

/-! ### Corollary 12.0.8 (TopAction3) -/

section TopAction3

variable {m : ℕ} {G : Subgroup (Equiv.Perm Ω)}

/-- The step of the proof of Cor. 12.0.8:

> We claim that if `Iso_G(x,y)^ϕ` is not a giant coset then `x` and `y` are not
> `G`-isomorphic.  Indeed, if `x ≅_G y` then `Iso_G(x,y) = Aut_G(x)σ` where `σ` is any
> element of `Iso_G(x,y)`.  It follows that `Iso_G(x,y)^ϕ = Aut_G(x)^ϕ σ̄` is a giant coset
> (where `σ̄ = σ^ϕ`).

Stated in the contrapositive-free direction: if `Aut_G(x)^ϕ` is a giant and `x` and `y` are
`G`-isomorphic, then `Iso_G(x,y)^ϕ` contains a giant coset. -/
theorem Corollary_12_0_8_giant_coset (ϕ : G →* Equiv.Perm (Fin m)) {x y : Ω → A}
    (haut : MapsOntoGiant ϕ x) (hne : (strIso (G : Set (Equiv.Perm Ω)) x y).Nonempty) :
    MapsOntoGiantCoset ϕ x y := by
  obtain ⟨σ, hσ⟩ := hne
  have hσG : σ ∈ G := hσ.1
  have hcoset : strIso (G : Set (Equiv.Perm Ω)) x y =
      σ • strAut (G : Set (Equiv.Perm Ω)) x := by
    have := wIso_eq_smul_wAut_one (isInvariant_univ G) (x := x) (y := y) (σ := σ)
      (by rwa [wIso_univ])
    rwa [wIso_univ, wAut_univ] at this
  refine ⟨ϕ ⟨σ, hσG⟩, ?_⟩
  rintro α ⟨β, hβ, rfl⟩
  obtain ⟨a, haAut, haG, hϕa⟩ := haut hβ
  refine ⟨σ * a, ?_, mul_mem hσG haG, ?_⟩
  · rw [hcoset]; exact ⟨a, haAut, rfl⟩
  · have hsplit : (⟨σ * a, mul_mem hσG haG⟩ : G) = ⟨σ, hσG⟩ * ⟨a, haG⟩ := rfl
    rw [hsplit, map_mul, hϕa]
    rfl

/-- Cor. 12.0.8: "if `Iso_G(x,y)^ϕ` is not a giant coset then `x` and `y` are not
`G`-isomorphic" (the contrapositive of `Babai.Corollary_12_0_8_giant_coset`). -/
theorem Corollary_12_0_8_not_isomorphic (ϕ : G →* Equiv.Perm (Fin m)) {x y : Ω → A}
    (haut : MapsOntoGiant ϕ x) (h : ¬ MapsOntoGiantCoset ϕ x y) :
    strIso (G : Set (Equiv.Perm Ω)) x y = ∅ :=
  Set.not_nonempty_iff_eq_empty.1 fun hne => h (Corollary_12_0_8_giant_coset ϕ haut hne)

/-! #### The reduction of Cor. 12.0.8

The paper's literal route ("To answer (i), apply Cor. 12.0.6 with `y = x`. […]  If
`Iso_G(x,y)^ϕ` is a giant coset, we are done by Cor. 12.0.6.") makes **two** applications
of Cor. 12.0.6, each costing `6k` calls, so it gives `12k`, not the printed `6k`.  The
printed bound is achievable with a small change of the proof, which is what is built here
(see the entry for Cor. 12.0.8 in the corrected paper):

* **Step (i).**  Since `Aut_{G₁}(x)^ϕ = Aut_G(x)^ϕ ∩ A(Γ)`
  (`Babai.homImage_strAut_preimageAlt`), the group `Aut_G(x)^ϕ` contains `A(Γ)` exactly
  when `Aut_{G₁}(x)^ϕ = A(Γ)`, where `G₁ = ϕ⁻¹(A(Γ))`.  So apply Prop. 12.0.5 to
  `ϕ₁ : G₁ → A(Γ)` with a pair of generators of `A(Γ)` and the pair of strings `(x, x)`:
  three `N`-instances, hence `3k` calls after the Chain Rule
  (`Babai.giantAReduction (altHom ϕ) x x`).  When the answer is affirmative this also
  returns `Aut_{G₁}(x)`.
* **Step (ii).**  Let `τ'` range over the coset representatives of `G₁` in `G` (one when
  `G^ϕ ≤ A(Γ)`, two otherwise).  The set `Iso_{G₁}(x, y^{τ'⁻¹})` is empty or a coset of
  `Aut_{G₁}(x)`; if it is not empty, its image under `ϕ` is a coset of `A(Γ)` inside
  `A(Γ)`, hence all of `A(Γ)`, so it contains `1` and `Iso_N(x, y^{τ'⁻¹})` is not empty
  (`Babai.exists_ker_iso`).  So one `N`-instance per representative — `k` calls each, by
  the Chain Rule — decides emptiness and returns an element `σ`, and then
  `Iso_{G₁}(x, y^{τ'⁻¹}) = Aut_{G₁}(x)σ` (`Babai.cosetUnion`).

Total: `3k + 2k = 5k ≤ 6k` calls, all with an orbit of `N` for their window. -/

section TopAction3Reduction

variable [Fintype Ω] [DecidableEq Ω]

/-- `ϕ` maps `Iso_G(x,x) = Aut_G(x)` onto a giant coset exactly when it maps `Aut_G(x)`
onto a giant: this is the step "to answer (i), apply Cor. 12.0.6 with `y = x`". -/
theorem mapsOntoGiantCoset_self_iff (ϕ : G →* Equiv.Perm (Fin m)) (x : Ω → A) :
    MapsOntoGiantCoset ϕ x x ↔ MapsOntoGiant ϕ x := by
  constructor
  · exact fun h => alt_subset_autImage ϕ h
  · intro h
    exact ⟨1, by rw [one_smul]; exact h⟩

/-- `G₁ = ϕ⁻¹(A(Γ))` is all of `G` when `G^ϕ ≤ A(Γ)`. -/
theorem preimageAlt_eq_of_range_le {ϕ : G →* Equiv.Perm (Fin m)}
    (h : ϕ.range ≤ alternatingGroup (Fin m)) : preimageAlt ϕ = G := by
  ext τ
  rw [mem_preimageAlt']
  exact ⟨fun hτ => hτ.1, fun hG => ⟨hG, h ⟨⟨τ, hG⟩, rfl⟩⟩⟩

/-- `N = ker(ϕ) ≤ G₁ = ϕ⁻¹(A(Γ))`. -/
theorem kerSubgroup_le_preimageAlt (ϕ : G →* Equiv.Perm (Fin m)) :
    kerSubgroup ϕ ≤ preimageAlt ϕ := by
  intro τ hτ
  obtain ⟨hG, h1⟩ := mem_kerSubgroup.1 hτ
  exact mem_preimageAlt'.2 ⟨hG, by rw [h1]; exact one_mem _⟩

/-- Step (i) of the repaired proof of Cor. 12.0.8: `Aut_{G₁}(x)^ϕ = Aut_G(x)^ϕ ∩ A(Γ)`,
where `G₁ = ϕ⁻¹(A(Γ))`. -/
theorem homImage_strAut_preimageAlt (ϕ : G →* Equiv.Perm (Fin m)) (x : Ω → A) :
    homImage ϕ
        (strIso ((preimageAlt ϕ : Subgroup (Equiv.Perm Ω)) : Set (Equiv.Perm Ω)) x x) =
      homImage ϕ (strAut (G : Set (Equiv.Perm Ω)) x) ∩
        (alternatingGroup (Fin m) : Set (Equiv.Perm (Fin m))) := by
  ext α
  constructor
  · rintro ⟨τ, ⟨hτ1, hτ2⟩, hG, rfl⟩
    obtain ⟨hτG, hτA⟩ := mem_preimageAlt'.1 hτ1
    exact ⟨⟨τ, ⟨hτG, hτ2⟩, hτG, rfl⟩, hτA⟩
  · rintro ⟨⟨τ, ⟨hτG, hτ2⟩, hG, rfl⟩, hA⟩
    exact ⟨τ, ⟨mem_preimageAlt'.2 ⟨hG, hA⟩, hτ2⟩, hG, rfl⟩

/-- Step (i) decides item (i) of Cor. 12.0.8: `Aut_G(x)^ϕ ≥ A(Γ)` exactly when `ϕ₁` maps
`Aut_{G₁}(x)` onto `A(Γ)`. -/
theorem mapsOnto_altHom_self_iff (ϕ : G →* Equiv.Perm (Fin m)) (x : Ω → A) :
    MapsOnto (altHom ϕ) x x ↔ MapsOntoGiant ϕ x := by
  rw [mapsOnto_altHom_iff, homImage_strAut_preimageAlt, MapsOntoGiant]
  exact ⟨fun h α hα => (h hα).1, fun h α hα => ⟨h hα, hα⟩⟩

/-! ##### Assembling a coset from one element and the automorphism group -/

/-- The union of the left translates `σ • t` for `σ ∈ s`.  This is how step (ii) of the
repaired proof of Cor. 12.0.8 assembles `Iso_{G₁}(x,y)` from the set `Iso_N(x,y)` returned
by the `N`-instance and the group `Aut_{G₁}(x)` returned by step (i): it is `∅` if
`Iso_N(x,y)` is empty, and otherwise the coset `Aut_{G₁}(x)σ` (in the paper's convention)
through any element `σ` of `Iso_N(x,y)`.  Taking a union avoids having to *choose* such a
`σ`, which would be the same thing. -/
def cosetUnion (s t : Set (Equiv.Perm Ω)) : Set (Equiv.Perm Ω) := ⋃ σ ∈ s, σ • t

/-- `cosetUnion s t = B` when `s ⊆ B`, every `σ ∈ B` has `σ • t = B`, and `s` is nonempty
whenever `B` is. -/
theorem cosetUnion_eq {s t B : Set (Equiv.Perm Ω)} (hsB : s ⊆ B)
    (hcos : ∀ σ ∈ B, σ • t = B) (hne : B.Nonempty → s.Nonempty) :
    cosetUnion s t = B := by
  ext g
  simp only [cosetUnion, Set.mem_iUnion, exists_prop]
  constructor
  · rintro ⟨σ, hσ, hg⟩
    rw [hcos σ (hsB hσ)] at hg
    exact hg
  · intro hg
    obtain ⟨σ, hσ⟩ := hne ⟨g, hg⟩
    exact ⟨σ, hσ, by rw [hcos σ (hsB hσ)]; exact hg⟩

/-- Step (ii) of the repaired proof of Cor. 12.0.8: if `Aut_G(x)^ϕ ≥ A(Γ)` and
`Iso_{G₁}(x,y)` is nonempty then so is `Iso_N(x,y)`.

Indeed, for `ρ ∈ Iso_{G₁}(x,y)` we have `Iso_{G₁}(x,y) = Aut_{G₁}(x)ρ`, so its image under
`ϕ` is the coset `Aut_{G₁}(x)^ϕ ρ^ϕ` of `A(Γ)` inside `A(Γ)`, i.e. all of `A(Γ)`; pick
`a ∈ Aut_G(x)` with `a^ϕ = (ρ^ϕ)⁻¹` (possible since `Aut_G(x)^ϕ ⊇ A(Γ)`), then `a ∈ G₁`
and `ρa ∈ Iso_{G₁}(x,y)` lies in `N = ker(ϕ)`. -/
theorem exists_ker_iso (ϕ : G →* Equiv.Perm (Fin m)) {x y : Ω → A}
    (haut : MapsOntoGiant ϕ x)
    (hne : (strIso ((preimageAlt ϕ : Subgroup (Equiv.Perm Ω)) :
      Set (Equiv.Perm Ω)) x y).Nonempty) :
    (strIso ((kerSubgroup ϕ : Subgroup (Equiv.Perm Ω)) :
      Set (Equiv.Perm Ω)) x y).Nonempty := by
  obtain ⟨ρ, hρ⟩ := hne
  obtain ⟨hρG, hρA⟩ := mem_preimageAlt'.1 hρ.1
  obtain ⟨a, haAut, haG, haϕ⟩ := haut (inv_mem hρA)
  have haG1 : a ∈ preimageAlt ϕ := mem_preimageAlt'.2 ⟨haG, by rw [haϕ]; exact inv_mem hρA⟩
  have hmem : ρ * a ∈ strIso ((preimageAlt ϕ : Subgroup (Equiv.Perm Ω)) :
      Set (Equiv.Perm Ω)) x y := by
    rw [strIso_eq_smul_strAut hρ]
    exact ⟨a, ⟨haG1, haAut.2⟩, rfl⟩
  refine ⟨ρ * a, ?_, hmem.2⟩
  refine mem_kerSubgroup.2 ⟨mul_mem hρG haG, ?_⟩
  rw [show (⟨ρ * a, mul_mem hρG haG⟩ : G) = ⟨ρ, hρG⟩ * ⟨a, haG⟩ from rfl, map_mul, haϕ,
    mul_inv_cancel]

/-- Step (ii): `Iso_{G₁}(x,y)` is recovered from `Iso_N(x,y)` and `Aut_{G₁}(x)`. -/
theorem cosetUnion_strIso_ker (ϕ : G →* Equiv.Perm (Fin m)) {x y : Ω → A}
    (haut : MapsOntoGiant ϕ x) :
    cosetUnion
        (strIso ((kerSubgroup ϕ : Subgroup (Equiv.Perm Ω)) : Set (Equiv.Perm Ω)) x y)
        (strIso ((preimageAlt ϕ : Subgroup (Equiv.Perm Ω)) : Set (Equiv.Perm Ω)) x x) =
      strIso ((preimageAlt ϕ : Subgroup (Equiv.Perm Ω)) : Set (Equiv.Perm Ω)) x y := by
  refine cosetUnion_eq ?_ ?_ (fun h => exists_ker_iso ϕ haut h)
  · rintro τ ⟨hτN, hτx⟩
    exact ⟨kerSubgroup_le_preimageAlt ϕ hτN, hτx⟩
  · intro σ hσ
    exact (strIso_eq_smul_strAut hσ).symm

/-! ##### The single `N`-instance of step (ii), expanded by the Chain Rule -/

/-- The instance `Iso_N(x,y)` with window all of `Ω`, and the Chain Rule reduction of it
over the `k` orbits of `N`: `k` calls, each with an orbit of `N` for its window. -/
noncomputable def nOrbitReduction (N : Subgroup (Equiv.Perm Ω)) (x y : Ω → A) :
    SIReduction Ω A (Set (Equiv.Perm Ω)) :=
  chainOverOrbits N ⟨(N : Set (Equiv.Perm Ω)), Set.univ, x, y⟩

theorem run_nOrbitReduction (N : Subgroup (Equiv.Perm Ω)) (x y : Ω → A) :
    (nOrbitReduction N x y).run = strIso (N : Set (Equiv.Perm Ω)) x y := by
  rw [nOrbitReduction, run_chainOverOrbits rfl rfl, SIInstance.answer, wIso_univ]

theorem calls_length_nOrbitReduction (N : Subgroup (Equiv.Perm Ω)) (x y : Ω → A) :
    (nOrbitReduction N x y).calls.length ≤ (orbitList N).length :=
  calls_length_chainOverOrbits N _

theorem calls_nOrbitReduction_window (N : Subgroup (Equiv.Perm Ω)) (x y : Ω → A) :
    ∀ J ∈ (nOrbitReduction N x y).calls, J.Δ ∈ orbitList N :=
  calls_chainOverOrbits_window N _

theorem calls_nOrbitReduction_K (N : Subgroup (Equiv.Perm Ω)) (x y : Ω → A) :
    ∀ J ∈ (nOrbitReduction N x y).calls, J.K ⊆ (N : Set (Equiv.Perm Ω)) :=
  calls_chainOverOrbits_K N _

/-! ##### The reduction -/

open Classical in
/-- §12, **Corollary 12.0.8** (TopAction3): the reduction, with the printed bound of `6k`
calls.  Step (i) is `Babai.giantAReduction (altHom ϕ) x x` (`3k` calls); step (ii) is one
`Babai.nOrbitReduction` per coset representative of `G₁ = ϕ⁻¹(A(Γ))` in `G` (`k` calls
each, at most two of them). -/
noncomputable def topAction3Reduction (ϕ : G →* Equiv.Perm (Fin m)) (x y : Ω → A) :
    SIReduction Ω A (Option (Set (Equiv.Perm Ω))) :=
  (giantAReduction (altHom ϕ) x x).bind fun r0 =>
    if r0 = none then .done none
    else
      (nOrbitReduction (kerSubgroup ϕ) x y).bind fun s1 =>
        if ϕ.range ≤ alternatingGroup (Fin m) then
          .done (some (cosetUnion s1 (r0.getD ∅)))
        else
          (nOrbitReduction (kerSubgroup ϕ) x (strAct y (oddRep ϕ)⁻¹)).bind fun s2 =>
            .done (some (cosetUnion s1 (r0.getD ∅) ∪
              (oddRep ϕ) • cosetUnion s2 (r0.getD ∅)))

open Classical in
theorem run_topAction3Reduction (hm3 : 3 ≤ m) (ϕ : G →* Equiv.Perm (Fin m)) (x y : Ω → A) :
    (topAction3Reduction ϕ x y).run =
      if MapsOntoGiant ϕ x then some (strIso (G : Set (Equiv.Perm Ω)) x y) else none := by
  classical
  rw [topAction3Reduction, SIReduction.run_bind, run_giantAReduction hm3]
  by_cases hA : MapsOntoGiant ϕ x
  · rw [if_pos ((mapsOnto_altHom_self_iff ϕ x).2 hA), if_pos hA,
      if_neg (by simp : ¬ (some (strIso ((preimageAlt ϕ : Subgroup (Equiv.Perm Ω)) :
        Set (Equiv.Perm Ω)) x x)) = none),
      SIReduction.run_bind, run_nOrbitReduction, Option.getD_some]
    by_cases hr : ϕ.range ≤ alternatingGroup (Fin m)
    · rw [if_pos hr, SIReduction.run_done, cosetUnion_strIso_ker ϕ hA,
        preimageAlt_eq_of_range_le hr]
    · obtain ⟨hσG, hσodd⟩ := oddRep_spec ϕ (exists_odd_of_not_range_le hr)
      rw [if_neg hr, SIReduction.run_bind, SIReduction.run_done, run_nOrbitReduction,
        cosetUnion_strIso_ker ϕ hA, cosetUnion_strIso_ker ϕ hA,
        ← strIso_descent ϕ hσG hσodd x y]
  · rw [if_neg (fun hc => hA ((mapsOnto_altHom_self_iff ϕ x).1 hc)), if_pos rfl,
      SIReduction.run_done, if_neg hA]

open Classical in
/-- Cor. 12.0.8: `3k` calls for step (i) and at most `2k` for step (ii), so `≤ 6k` in
all. -/
theorem calls_length_topAction3Reduction (hm3 : 3 ≤ m) (ϕ : G →* Equiv.Perm (Fin m))
    (x y : Ω → A) :
    (topAction3Reduction ϕ x y).calls.length ≤ 6 * orbCount ϕ := by
  classical
  have hk : (orbitList (kerSubgroup ϕ)).length = orbCount ϕ :=
    length_orbitList (kerSubgroup ϕ)
  have h0 := calls_length_giantAReduction hm3 (altHom ϕ) x x
  rw [orbitList_altHom, hk] at h0
  have h1 := calls_length_nOrbitReduction (kerSubgroup ϕ) x y
  have h2 := calls_length_nOrbitReduction (kerSubgroup ϕ) x (strAct y (oddRep ϕ)⁻¹)
  rw [hk] at h1 h2
  rw [topAction3Reduction, SIReduction.calls_bind, List.length_append]
  by_cases hz : (giantAReduction (altHom ϕ) x x).run = none
  · rw [if_pos hz, SIReduction.calls_done]
    simp only [List.length_nil]
    omega
  · rw [if_neg hz, SIReduction.calls_bind, List.length_append, run_nOrbitReduction]
    by_cases hr : ϕ.range ≤ alternatingGroup (Fin m)
    · rw [if_pos hr, SIReduction.calls_done]
      simp only [List.length_nil]
      omega
    · rw [if_neg hr, SIReduction.calls_bind, SIReduction.calls_done, List.length_append]
      simp only [List.length_nil]
      omega

open Classical in
theorem calls_topAction3Reduction_window (ϕ : G →* Equiv.Perm (Fin m)) (x y : Ω → A) :
    ∀ I ∈ (topAction3Reduction ϕ x y).calls, I.Δ ∈ orbitList (kerSubgroup ϕ) := by
  classical
  have h0 := calls_giantAReduction_window (altHom ϕ) x x
  rw [orbitList_altHom] at h0
  have h1 := calls_nOrbitReduction_window (kerSubgroup ϕ) x y
  have h2 := calls_nOrbitReduction_window (kerSubgroup ϕ) x (strAct y (oddRep ϕ)⁻¹)
  rw [topAction3Reduction, SIReduction.calls_bind]
  intro I hI
  rcases List.mem_append.1 hI with hI | hI
  · exact h0 I hI
  · by_cases hz : (giantAReduction (altHom ϕ) x x).run = none
    · rw [if_pos hz, SIReduction.calls_done] at hI; exact absurd hI (by simp)
    · rw [if_neg hz, SIReduction.calls_bind, run_nOrbitReduction] at hI
      rcases List.mem_append.1 hI with hI | hI
      · exact h1 I hI
      · by_cases hr : ϕ.range ≤ alternatingGroup (Fin m)
        · rw [if_pos hr, SIReduction.calls_done] at hI; exact absurd hI (by simp)
        · rw [if_neg hr, SIReduction.calls_bind, SIReduction.calls_done] at hI
          simp only [List.append_nil] at hI
          exact h2 I hI

open Classical in
/-- Every call of `Babai.topAction3Reduction` has its candidate set inside `G`: all its
instances come from the Chain Rule over the orbits of `N = ker(ϕ)`, whose groups shrink
inside `N ≤ G`.  This is the hypothesis under which the reduction can be transported to a
window (`Workspace/Luks/Window.lean`). -/
theorem calls_topAction3Reduction_K (ϕ : G →* Equiv.Perm (Fin m)) (x y : Ω → A) :
    ∀ I ∈ (topAction3Reduction ϕ x y).calls, I.K ⊆ (G : Set (Equiv.Perm Ω)) := by
  classical
  have hker : ((kerSubgroup ϕ : Subgroup (Equiv.Perm Ω)) : Set (Equiv.Perm Ω)) ⊆
      (G : Set (Equiv.Perm Ω)) := kerSubgroup_le ϕ
  have h0 := calls_giantAReduction_K (altHom ϕ) x x
  rw [kerSubgroup_altHom] at h0
  have h1 := calls_nOrbitReduction_K (kerSubgroup ϕ) x y
  have h2 := calls_nOrbitReduction_K (kerSubgroup ϕ) x (strAct y (oddRep ϕ)⁻¹)
  rw [topAction3Reduction, SIReduction.calls_bind]
  intro I hI
  rcases List.mem_append.1 hI with hI | hI
  · exact le_trans (h0 I hI) hker
  · by_cases hz : (giantAReduction (altHom ϕ) x x).run = none
    · rw [if_pos hz, SIReduction.calls_done] at hI; exact absurd hI (by simp)
    · rw [if_neg hz, SIReduction.calls_bind, run_nOrbitReduction] at hI
      rcases List.mem_append.1 hI with hI | hI
      · exact le_trans (h1 I hI) hker
      · by_cases hr : ϕ.range ≤ alternatingGroup (Fin m)
        · rw [if_pos hr, SIReduction.calls_done] at hI; exact absurd hI (by simp)
        · rw [if_neg hr, SIReduction.calls_bind, SIReduction.calls_done] at hI
          simp only [List.append_nil] at hI
          exact le_trans (h2 I hI) hker

end TopAction3Reduction

open Classical in
/-- §12, **Corollary 12.0.8** (TopAction3).

> Let `G ≤ S(Ω)` be a transitive permutation group and `ϕ : G → S(Γ)` a giant
> representation, where `|Γ| = m > max{8, 2 + log₂ n}`.  Given these data and the strings
> `x, y : Ω → Σ`, we can achieve the following by recursively calling `≤ 6k` instances of
> String Isomorphism with window size `≤ n/k` for some `m ≤ k ≤ n`, at polynomial cost per
> instance:
> (i) decide whether `ϕ` maps `Aut_G(x)` onto a giant, i. e., `Aut_G(x)^ϕ ≥ A(Γ)`;
> (i) if the answer is affirmative, find `Iso_G(x,y)`.
>
> *Proof.*  To answer (i), apply Cor. cor:topaction with `y = x`.  Assume the answer is
> affirmative.  If `Iso_G(x,y)^ϕ` is a giant coset, we are done by Cor. 12.0.6.  We claim
> that if `Iso_G(x,y)^ϕ` is not a giant coset then `x` and `y` are not `G`-isomorphic. […]

Two printing slips in version 2.5, logged in the corrected paper (kind "typo/cross-reference"):
the broken cross-reference "Cor. cor:topaction" is Cor. 12.0.6, and the second item, again
labelled "(i)", is (ii).

Note that applying Cor. 12.0.6 with `y = x` answers (i): `Iso_G(x,x) = Aut_G(x)` and a
giant coset `A(Γ)τ` contained in `Aut_G(x)^ϕ`, a group, forces `A(Γ) ≤ Aut_G(x)^ϕ`
(`Babai.mapsOntoGiantCoset_self_iff`).  The two applications share the value of `k`, since
`k` depends only on `G` and `ϕ` (`Babai.orbCount`), not on the strings.

**Call bound.**  The printed bound `≤ 6k` is kept.  The paper's *route* does not give it:
it makes two applications of Cor. 12.0.6, each costing `6k` in the case `G^ϕ = S(Γ)`
(`3k` for Prop. 12.0.5 plus the Chain Rule, doubled by the Luks descent), so it gives
`12k`.  The second application is avoidable, because step (i) already returns
`Aut_{G₁}(x)`; `Babai.topAction3Reduction` follows the repaired route (`3k + 2k = 5k`
calls) described above it and in the the corrected paper Cor. 12.0.8.  Only the
proof changes; the statement is as printed. -/
theorem Corollary_12_0_8 [Fintype Ω] [DecidableEq Ω] (hG : IsTransitive G)
    (ϕ : G →* Equiv.Perm (Fin m)) (hϕ : IsGiantRep ϕ) (hm : LargeK m (Nat.card Ω))
    (x y : Ω → A) :
    m ≤ orbCount ϕ ∧ orbCount ϕ ≤ Fintype.card Ω ∧
      (topAction3Reduction ϕ x y).calls.length ≤ 6 * orbCount ϕ ∧
      (∀ I ∈ (topAction3Reduction ϕ x y).calls,
        orbCount ϕ * I.windowSize ≤ Fintype.card Ω) ∧
      (topAction3Reduction ϕ x y).run =
        if MapsOntoGiant ϕ x then some (strIso (G : Set (Equiv.Perm Ω)) x y) else none := by
  classical
  obtain ⟨hmk, hkn, hlen⟩ := orbCount_spec hG ϕ hϕ hm
  have hm3 : 3 ≤ m := by have := hm.eight_lt; omega
  refine ⟨hmk, hkn, calls_length_topAction3Reduction hm3 ϕ x y, ?_,
    run_topAction3Reduction hm3 ϕ x y⟩
  intro I hI
  obtain ⟨u, hu⟩ := mem_orbitList (calls_topAction3Reduction_window ϕ x y I hI)
  rw [SIInstance.windowSize, hu, mul_comm, hlen u]

end TopAction3

end Babai
