/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Tools for the proof of [DiM, Thm. 5.2A,B]: the intransitive case.
-/
import Workspace.AltQuotients.DM52.Imprim
import Workspace.AltQuotients.NamedGroups

/-!
# Intransitive subgroups of small index in `A_n`

The last paragraph of the proof of [DiM, Thm. 5.2A] (pp. 148–149):

> There remains the case where `G` is intransitive. […] We first show that `G` has an orbit
> of length greater than `m`.  Suppose the contrary.  If `G` has an orbit `Γ` of length
> exactly `m`, `G ≤ A_{Γ}`, and so `|A : G| ≥ |A : A_{Γ}| = C(n,m)` contrary to hypothesis.
> On the other hand, suppose the orbits of `G` have lengths `n₁, …, n_t` which are all less
> than `m` (so `t ≥ 3`).  Then using Lemma 5.2A (ii) we conclude that
> `|G| ≤ n₁! ⋯ n_t! < ¼ m!(n − m)!`, which again contradicts the condition that
> `|A : G| < C(n,m)`.  Thus `G` has an orbit `Γ`, say, of length `s > m ≥ 3`.
>
> Define `Δ := Ω \ Γ` and `H := G_(Δ) ≤ A_(Δ) = Alt(Γ)`; our object is to show that
> `H = A_(Δ)`.  Put `h' := |A_(Δ) : H|`.  […] we have `h (n − s)! ≥ (n!/s!) h'`.  Thus, if we
> put `t := ⌊s/2⌋`, then the hypothesis on `h` shows that
> `h' < (n−s)! s! / ((n−m)! m!) = (n−s)! t! (s−t)! / ((n−m)! m!) · C(s,t)`.
> Hence Lemma 5.2A (ii) yields `h' ≤ C(s,t)/(n − m) ≤ ¼ C(s,t)`.  Now induction applied to `H`
> acting on `Γ` shows that one of three things can happen: (i) there exists an `H`-invariant
> subset `Σ ⊆ Γ` with `|Σ| < s/2` such that `A_(Δ ∪ Σ) ≤ H`; (ii) `h' = ½ C(s,t)`; or
> (iii) `s ≤ 9`, and `H^Γ` is one of the exceptional groups listed in the theorem.  The
> second of these possibilities cannot hold because of the bound on `h'` given above.  Also,
> […] the bounds for `h'` given above also show that `h'` is at most `3, 5, 8, 14` and `25`
> for `s = 5, 6, 7, 8` and `9`, respectively.  Thus `H^Γ` is not one of the exceptional cases
> in (iii).  Therefore we conclude that (i) holds, […] `Γ \ Σ` is an orbit of `H`.  However,
> `G` acts transitively on `Γ`, and `H = G_(Δ) ⊴ G`, so the lengths of the orbits of `H` on
> `Γ` divide `s` […].  Therefore `Σ = ∅` […].  Thus `A_(Δ) = H ≤ G ≤ A_{Δ}` and the proof of
> the theorem is complete.

(The source leaves the case `n ≤ 6` "as an exercise"; the argument above works verbatim for
`n ≥ 5`: the only place where `n > 6` is used in the source is the constant `¼`, and
`n − m ≥ 3` suffices everywhere below.  For `s ≤ 4` the induction is not needed: the bound
`h' (n − m) < C(s, ⌊s/2⌋)` already gives `h' = 1`.)

Here the group `H` acting on `Γ` is `restrictStab G Γ`, the subgroup of `Sym(Γ)` of the
permutations whose extension by the identity lies in `G`; it is identified with `G_(Δ)` by
the extension.  The last step, `Σ = ∅`, is done with `3`-cycles instead of orbit lengths
(`eq_empty_of_sandwich`): if `z ∈ Σ` and `g ∈ G` maps a point of `Γ \ Σ` to `z`, then
conjugating the `3`-cycles of `Alt(Γ \ Σ) ≤ H` by `g` shows that `g` maps all of `Γ \ Σ`
into `Σ`, which is smaller.

The statement being proved by induction is recorded as `Babai.DM52.Concl52A` (the
conclusion of [DiM, Thm. 5.2A]).
-/

universe u

namespace Babai.DM52

open Equiv Equiv.Perm MulAction Nat Subgroup
open scoped Pointwise

variable {Ω : Type u} [Fintype Ω] [DecidableEq Ω]

/-- The conclusion of [DiM, Thm. 5.2A] for `G ≤ Alt(Ω)` and the integer `r` (the statement
of `Babai.dixonMortimer_5_2A`). -/
def Concl52A (Ω : Type u) [Fintype Ω] [DecidableEq Ω] (r : ℕ) (G : Subgroup (Perm Ω)) :
    Prop :=
  (∃ Δ : Set Ω, Δ.ncard < r ∧
      pointwiseStabilizer (alternatingGroup Ω) Δ ≤ G ∧
      G ≤ setwiseStabilizer (alternatingGroup Ω) Δ) ∨
    (IsTransitive G ∧ PreservesHalvingPartition G ∧
      2 * G.relIndex (alternatingGroup Ω) = (Nat.card Ω).choose (Nat.card Ω / 2)) ∨
    ((IsTransitive G ∧ ¬ IsPrimitive G ∧
        Nat.card Ω = 6 ∧ 3 ≤ r ∧ G.relIndex (alternatingGroup Ω) = 15) ∨
      (IsPrimitive G ∧
        ((Nat.card Ω = 5 ∧ 2 ≤ r ∧ G.relIndex (alternatingGroup Ω) = 6 ∧
            Nonempty (G ≃* Frob_5_2)) ∨
          (Nat.card Ω = 6 ∧ 2 ≤ r ∧ G.relIndex (alternatingGroup Ω) = 6 ∧
            Nonempty (G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 5))) ∨
          (Nat.card Ω = 7 ∧ 2 ≤ r ∧ G.relIndex (alternatingGroup Ω) = 15 ∧
            Nonempty (G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2))) ∨
          (Nat.card Ω = 8 ∧ 2 ≤ r ∧ G.relIndex (alternatingGroup Ω) = 15 ∧
            Nonempty (G ≃* AGL_3_2)) ∨
          (Nat.card Ω = 9 ∧ 4 ≤ r ∧ G.relIndex (alternatingGroup Ω) = 120 ∧
            Nonempty (G ≃* PGammaL_2_8)))))

/-- [DiM, Thm. 5.2A] for the type `Ω`. -/
def Statement52A (Ω : Type u) [Fintype Ω] [DecidableEq Ω] : Prop :=
  5 ≤ Nat.card Ω → ∀ {r : ℕ}, 1 ≤ r → 2 * r ≤ Nat.card Ω → ∀ {G : Subgroup (Perm Ω)},
    G ≤ alternatingGroup Ω → G.relIndex (alternatingGroup Ω) < (Nat.card Ω).choose r →
    Concl52A Ω r G

/-- What the induction gives in the intransitive case: for `r = ⌊s/2⌋`, case (i), or an index
value that the bound on `h'` excludes. -/
theorem concl_cases {Γ : Type u} [Fintype Γ] [DecidableEq Γ] {H : Subgroup (Perm Γ)}
    (h : Concl52A Γ (Nat.card Γ / 2) H) :
    (∃ S : Set Γ, S.ncard < Nat.card Γ / 2 ∧
        pointwiseStabilizer (alternatingGroup Γ) S ≤ H ∧
        H ≤ setwiseStabilizer (alternatingGroup Γ) S) ∨
      2 * H.relIndex (alternatingGroup Γ) = (Nat.card Γ).choose (Nat.card Γ / 2) ∨
      (Nat.card Γ = 6 ∧ H.relIndex (alternatingGroup Γ) = 15) ∨
      (Nat.card Γ = 5 ∧ H.relIndex (alternatingGroup Γ) = 6) ∨
      (Nat.card Γ = 6 ∧ H.relIndex (alternatingGroup Γ) = 6) ∨
      (Nat.card Γ = 7 ∧ H.relIndex (alternatingGroup Γ) = 15) ∨
      (Nat.card Γ = 8 ∧ H.relIndex (alternatingGroup Γ) = 15) ∨
      (Nat.card Γ = 9 ∧ H.relIndex (alternatingGroup Γ) = 120) := by
  rcases h with h | ⟨-, -, h⟩ | ⟨-, -, h6, -, h15⟩ | ⟨-, h⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl ⟨h6, h15⟩))
  · rcases h with ⟨a, -, b, -⟩ | ⟨a, -, b, -⟩ | ⟨a, -, b, -⟩ | ⟨a, -, b, -⟩ | ⟨a, -, b, -⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨a, b⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨a, b⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨a, b⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨a, b⟩))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨a, b⟩))))))

/-! ### Arithmetic -/

/-- `C(n, r) ≤ C(n, d)` for `r ≤ d ≤ n/2`. -/
theorem choose_le_choose_of_le_half {n r d : ℕ} (hrd : r ≤ d) (hd : d ≤ n / 2) :
    n.choose r ≤ n.choose d := by
  induction d, hrd using Nat.le_induction with
  | base => exact le_rfl
  | succ d hrd ih =>
    exact (ih (by omega)).trans (Nat.choose_le_succ_of_lt_half_left (by omega))

/-- `C(n, m) m! (n − m)! = n!` with `m = ⌊n/2⌋`. -/
theorem choose_half_mul (n : ℕ) :
    n.choose (n / 2) * ((n / 2)! * (n - n / 2)!) = n ! := by
  rw [← mul_assoc]; exact Nat.choose_mul_factorial_mul_factorial (Nat.div_le_self n 2)

/-! ### The product of the symmetric groups on the orbits -/

omit [Fintype Ω] [DecidableEq Ω] in
theorem mk_smul_eq (H : Subgroup (Perm Ω)) (σ : H) (x : Ω) :
    (Quotient.mk'' ((σ : Perm Ω) x) : orbitRel.Quotient H Ω) = Quotient.mk'' x :=
  Quotient.sound' (mem_orbit x σ)

omit [DecidableEq Ω] in
/-- `|H| ≤ ∏ |ω|!` over the orbits `ω` of `H`. -/
theorem card_le_prod_orbits (H : Subgroup (Perm Ω)) [Fintype (orbitRel.Quotient H Ω)] :
    Nat.card H ≤ ∏ ω : orbitRel.Quotient H Ω, (Nat.card ω.orbit)! := by
  classical
  have hinv : ∀ (σ : H) (ω : orbitRel.Quotient H Ω) (x : Ω),
      (σ : Perm Ω) x ∈ ω.orbit ↔ x ∈ ω.orbit := by
    intro σ ω x
    rw [orbitRel.Quotient.mem_orbit, orbitRel.Quotient.mem_orbit, mk_smul_eq]
  let ψ : H → ((ω : orbitRel.Quotient H Ω) → Perm ω.orbit) :=
    fun σ ω => (σ : Perm Ω).subtypePerm (hinv σ ω)
  have hψ : Function.Injective ψ := by
    intro σ τ hστ
    apply Subtype.ext
    ext x
    set ω₀ : orbitRel.Quotient H Ω := Quotient.mk'' x
    have hx : x ∈ ω₀.orbit := orbitRel.Quotient.mem_orbit.mpr rfl
    have := congrArg (fun f => ((f ω₀ ⟨x, hx⟩ : _) : Ω)) hστ
    simpa [ψ] using this
  calc Nat.card H ≤ Nat.card ((ω : orbitRel.Quotient H Ω) → Perm ω.orbit) :=
        Nat.card_le_card_of_injective ψ hψ
    _ = ∏ ω : orbitRel.Quotient H Ω, (Nat.card ω.orbit)! := by
        rw [Nat.card_pi]
        exact Finset.prod_congr rfl (fun ω _ => Nat.card_perm)

omit [DecidableEq Ω] in
/-- `∑ |ω| = n` over the orbits `ω` of `H`. -/
theorem sum_card_orbits (H : Subgroup (Perm Ω)) [Fintype (orbitRel.Quotient H Ω)] :
    ∑ ω : orbitRel.Quotient H Ω, Nat.card ω.orbit = Nat.card Ω := by
  classical
  rw [Nat.card_congr (selfEquivSigmaOrbits' H Ω), Nat.card_sigma]

omit [Fintype Ω] [DecidableEq Ω] in
theorem card_orbit_eq (H : Subgroup (Perm Ω)) (ω : orbitRel.Quotient H Ω) :
    Nat.card ω.orbit = (orbit H ω.out).ncard := by
  rw [orbitRel.Quotient.orbit_eq_orbit_out ω Quotient.out_eq', Nat.card_coe_set_eq]

/-! ### An orbit of length greater than `m` -/

omit [Fintype Ω] [DecidableEq Ω] in
theorem mem_orbit_iff_apply {G : Subgroup (Perm Ω)} {x₀ : Ω} {σ : Perm Ω} (hσ : σ ∈ G)
    (x : Ω) : x ∈ orbit G x₀ ↔ σ x ∈ orbit G x₀ := by
  constructor
  · intro hx; exact mem_orbit_of_mem_orbit (⟨σ, hσ⟩ : G) hx
  · intro hx
    have := mem_orbit_of_mem_orbit (⟨σ, hσ⟩⁻¹ : G) hx
    simpa [Subgroup.smul_def] using this

omit [Fintype Ω] [DecidableEq Ω] in
theorem image_orbit_eq {G : Subgroup (Perm Ω)} (x₀ : Ω) {σ : Perm Ω} (hσ : σ ∈ G) :
    σ '' orbit G x₀ = orbit G x₀ := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩; exact (mem_orbit_iff_apply hσ x).mp hx
  · intro hy
    refine ⟨σ⁻¹ y, (mem_orbit_iff_apply hσ _).mpr (by simpa using hy), by simp⟩

/-- **[DiM, proof of Thm. 5.2A]**: an intransitive `G ≤ A` with `|A : G| < C(n, m)` has an
orbit of length greater than `m = ⌊n/2⌋`. -/
theorem exists_large_orbit (hn : 5 ≤ Nat.card Ω) {G : Subgroup (Perm Ω)}
    (hGA : G ≤ alternatingGroup Ω)
    (hindex : G.relIndex (alternatingGroup Ω) < (Nat.card Ω).choose (Nat.card Ω / 2)) :
    ∃ x₀ : Ω, Nat.card Ω / 2 < (orbit G x₀).ncard := by
  classical
  haveI : Nontrivial Ω := by
    rw [← Finite.one_lt_card_iff_nontrivial]; omega
  have hh0 : 0 < G.relIndex (alternatingGroup Ω) := Nat.pos_of_ne_zero (by
    rw [Subgroup.relIndex]; exact Subgroup.index_ne_zero_of_finite)
  set n := Nat.card Ω
  set m := n / 2
  set h := G.relIndex (alternatingGroup Ω)
  by_contra hcon
  push Not at hcon
  by_cases hm : ∃ x₀ : Ω, (orbit G x₀).ncard = m
  · -- `G ≤ A_{Γ}` for an orbit `Γ` of length `m`
    obtain ⟨x₀, hx₀⟩ := hm
    have hle : G ≤ setwiseStabilizer (alternatingGroup Ω) (orbit G x₀) :=
      fun σ hσ => ⟨hGA hσ, image_orbit_eq x₀ hσ⟩
    have hidx := relIndex_setwiseStabilizer (K := alternatingGroup Ω) le_rfl
      (m := m) (by omega) hx₀
    have hdvd := Subgroup.relIndex_dvd_of_le_left (alternatingGroup Ω) hle
    rw [hidx] at hdvd
    have := Nat.le_of_dvd hh0 hdvd
    have hnn : n.choose m = (Nat.card Ω).choose m := rfl
    omega
  · push Not at hm
    -- all orbits are shorter than `m`: Lemma 5.2A (ii)
    set Q := orbitRel.Quotient G Ω
    letI : Fintype Q := Fintype.ofFinite Q
    set P : Multiset ℕ := (Finset.univ : Finset Q).val.map (fun ω => Nat.card ω.orbit)
    have hPmem : ∀ a ∈ P, 1 ≤ a ∧ a ≤ m - 1 := by
      intro a ha
      obtain ⟨ω, -, rfl⟩ := Multiset.mem_map.mp ha
      rw [card_orbit_eq]
      have h1 := hcon ω.out
      have h2 := hm ω.out
      have h3 : 1 ≤ (orbit G ω.out).ncard := by
        rw [Nat.one_le_iff_ne_zero, Ne, Set.ncard_eq_zero]
        exact Set.nonempty_iff_ne_empty.mp ⟨ω.out, mem_orbit_self _⟩
      omega
    have hPsum : P.sum = n := by
      show P.sum = Nat.card Ω
      rw [← sum_card_orbits G, Finset.sum_eq_multiset_sum]
    have hPprod : (P.map Nat.factorial).prod =
        ∏ ω : Q, (Nat.card ω.orbit)! := by
      rw [Finset.prod_eq_multiset_prod, Multiset.map_map]; rfl
    have hPcard : 3 ≤ Multiset.card P := by
      by_contra hc
      have := Multiset.sum_le_card_nsmul P (m - 1) (fun a ha => (hPmem a ha).2)
      rw [hPsum, smul_eq_mul] at this
      have : Multiset.card P * (m - 1) ≤ 2 * (m - 1) := Nat.mul_le_mul_right _ (by omega)
      omega
    have hL := lemma_5_2A_ii m P hPcard (fun a ha => ⟨(hPmem a ha).1, by
      have := (hPmem a ha).2; omega⟩) (by omega)
    rw [hPprod, hPsum] at hL
    have hG := (card_le_prod_orbits G).trans hL
    -- `n! = 2 |G| h ≤ 2 m! (n-m-1)! h < 2 C(n,m) m! (n-m-1)! ≤ n!`
    have hGh : 2 * (Nat.card G * h) = n ! := by
      rw [card_mul_relIndex hGA, two_mul_card_alternatingGroup]
    have hC := choose_half_mul n
    have hf : (n - m)! = (n - m) * (n - m - 1)! := by
      rw [← Nat.mul_factorial_pred (by omega)]
    rw [hf] at hC
    have hnm : 2 ≤ n - m := by omega
    have hpos : 0 < m ! * (n - m - 1)! := by positivity
    have : 2 * (Nat.card G * h) < n ! := by
      calc 2 * (Nat.card G * h) ≤ 2 * (m ! * (n - m - 1)! * h) := by gcongr
        _ < 2 * (m ! * (n - m - 1)! * n.choose m) := by gcongr
        _ ≤ (n - m) * (m ! * (n - m - 1)! * n.choose m) := by gcongr
        _ = n ! := by rw [← hC]; ring
    omega

/-! ### Restriction to an orbit -/

/-- For `Γ ⊆ Ω`, the permutations of `Γ` whose extension by the identity lies in `G`; for an
orbit `Γ` this is `G_(Ω \ Γ)` acting on `Γ`. -/
def restrictStab (G : Subgroup (Perm Ω)) (Γ : Set Ω) [DecidablePred (· ∈ Γ)] :
    Subgroup (Perm Γ) :=
  G.comap (ofSubtype : Perm Γ →* Perm Ω)

omit [Fintype Ω] [DecidableEq Ω] in
theorem mem_restrictStab {G : Subgroup (Perm Ω)} {Γ : Set Ω} [DecidablePred (· ∈ Γ)]
    {τ : Perm Γ} :
    τ ∈ restrictStab G Γ ↔ ofSubtype τ ∈ G := Iff.rfl

omit [Fintype Ω] [DecidableEq Ω] in
/-- Extension by the identity commutes with conjugation by a permutation preserving `Γ`. -/
theorem ofSubtype_conj {Γ : Set Ω} [DecidablePred (· ∈ Γ)] (σ : Perm Ω) (hσ : ∀ x, σ x ∈ Γ ↔ x ∈ Γ) (τ : Perm Γ) :
    ofSubtype (σ.subtypePerm hσ * τ * (σ.subtypePerm hσ)⁻¹) = σ * ofSubtype τ * σ⁻¹ := by
  ext x
  by_cases hx : x ∈ Γ
  · have hx' : σ⁻¹ x ∈ Γ := (hσ _).mp (by simpa using hx)
    rw [ofSubtype_apply_of_mem _ hx]
    simp only [Perm.mul_apply]
    rw [ofSubtype_apply_of_mem _ hx']
    simp [Perm.subtypePerm_apply]
  · have hx' : σ⁻¹ x ∉ Γ := fun h => hx (by simpa using (hσ _).mpr h)
    rw [ofSubtype_apply_of_not_mem _ hx, Perm.mul_apply, Perm.mul_apply,
      ofSubtype_apply_of_not_mem _ hx']
    simp

/-- The `3`-cycle argument for `Σ = ∅`: if `Alt(X)_(Σ) ≤ H ≤ Alt(X)_{Σ}` with
`|Σ| < |X|/2` and `|X| ≥ 5`, and `H` is normalized by a transitive group `N`, then
`Σ = ∅`. -/
theorem eq_empty_of_sandwich {X : Type*} [Fintype X] [DecidableEq X] {H N : Subgroup (Perm X)}
    {S : Set X} (hS : 2 * S.ncard < Nat.card X) (h5 : 5 ≤ Nat.card X)
    (hlow : pointwiseStabilizer (alternatingGroup X) S ≤ H)
    (hup : H ≤ setwiseStabilizer (alternatingGroup X) S) (hN : IsPretransitive N X)
    (hnorm : ∀ g ∈ N, ∀ τ ∈ H, g * τ * g⁻¹ ∈ H) : S = ∅ := by
  classical
  by_contra hne
  obtain ⟨z, hz⟩ := Set.nonempty_iff_ne_empty.mpr hne
  have hR := ncard_add_ncard_compl S
  have hR3 : 3 ≤ (Sᶜ : Set X).ncard := by omega
  obtain ⟨a, ha⟩ : (Sᶜ : Set X).Nonempty := Set.nonempty_of_ncard_ne_zero (by omega)
  obtain ⟨⟨g, hgN⟩, hg⟩ := hN.exists_smul_eq a z
  replace hg : g a = z := hg
  -- `g` maps `Sᶜ` into `S`
  have hmap : ∀ y ∈ (Sᶜ : Set X), g y ∈ S := by
    intro y hy
    by_cases hya : y = a
    · rw [hya, hg]; exact hz
    obtain ⟨w, hw, hwa, hwy⟩ : ∃ w ∈ (Sᶜ : Set X), w ≠ a ∧ w ≠ y := by
      have h1 : (((Sᶜ : Set X) \ {a}) \ {y}).ncard ≥ 1 := by
        have e1 := Set.ncard_diff_singleton_le (Sᶜ \ {a} : Set X) y
        have e2 := Set.ncard_diff_singleton_le (Sᶜ : Set X) a
        have e3 : ((Sᶜ \ {a}) \ {y} : Set X).ncard + 1 ≥ (Sᶜ \ {a} : Set X).ncard :=
          by have := Set.ncard_le_ncard_diff_add_ncard (Sᶜ \ {a} : Set X) {y}
             simp at this; omega
        have e4 : (Sᶜ \ {a} : Set X).ncard + 1 ≥ (Sᶜ : Set X).ncard :=
          by have := Set.ncard_le_ncard_diff_add_ncard (Sᶜ : Set X) {a}
             simp at this; omega
        omega
      obtain ⟨w, hw⟩ := Set.nonempty_of_ncard_ne_zero (by omega : (((Sᶜ : Set X) \ {a}) \ {y}).ncard ≠ 0)
      simp only [Set.mem_diff, Set.mem_singleton_iff] at hw
      exact ⟨w, hw.1.1, hw.1.2, hw.2⟩
    set c := swap a w * swap a y with hc
    have hca : c a = y := by
      rw [hc, Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne hya hwy.symm]
    have hcS : c ∈ pointwiseStabilizer (alternatingGroup X) S := by
      refine ⟨?_, fun x hx => ?_⟩
      · rw [mem_alternatingGroup, hc, Perm.sign_mul, sign_swap hwa.symm, sign_swap (Ne.symm hya)]
        decide
      · have hxa : x ≠ a := fun h => ha (h ▸ hx)
        have hxy : x ≠ y := fun h => hy (h ▸ hx)
        have hxw : x ≠ w := fun h => hw (h ▸ hx)
        rw [hc, Perm.mul_apply, swap_apply_of_ne_of_ne hxa hxy,
          swap_apply_of_ne_of_ne hxa hxw]
    have hconj := hup (hnorm g hgN c (hlow hcS))
    have himg := hconj.2
    have : (g * c * g⁻¹) z ∈ S := by
      rw [← himg]; exact Set.mem_image_of_mem _ hz
    rwa [Perm.mul_apply, Perm.mul_apply, ← hg, show g⁻¹ (g a) = a by simp, hca] at this
  have hsub : g '' (Sᶜ : Set X) ⊆ S := by
    rintro _ ⟨y, hy, rfl⟩; exact hmap y hy
  have := Set.ncard_le_ncard hsub
  rw [Set.ncard_image_of_injective _ g.injective] at this
  omega

/-- `H ≤ Alt(Γ)` when `G ≤ A`. -/
theorem restrictStab_le_alternatingGroup {G : Subgroup (Perm Ω)} (hGA : G ≤ alternatingGroup Ω)
    (Γ : Set Ω) [DecidablePred (· ∈ Γ)] : restrictStab G Γ ≤ alternatingGroup Γ := by
  intro τ hτ
  have := hGA (mem_restrictStab.mp hτ)
  rw [mem_alternatingGroup, sign_ofSubtype] at this
  exact this

omit [DecidableEq Ω] in
/-- `|G| ≤ |Ω \ Γ|! · |H|` for a `G`-invariant `Γ`: the kernel of the restriction of `G` to
`Δ = Ω \ Γ` is `G_(Δ)`, which is identified with `H` by the extension by the identity. -/
theorem card_le_factorial_mul_card_restrictStab {G : Subgroup (Perm Ω)} (Γ : Set Ω)
    [DecidablePred (· ∈ Γ)] (hinv : ∀ σ ∈ G, ∀ x, σ x ∈ Γ ↔ x ∈ Γ) :
    Nat.card G ≤ (Nat.card (Γᶜ : Set Ω))! * Nat.card (restrictStab G Γ) := by
  classical
  have hΔ : ∀ σ ∈ G, ∀ x, σ x ∈ (Γᶜ : Set Ω) ↔ x ∈ (Γᶜ : Set Ω) := fun σ hσ x => by
    simp only [Set.mem_compl_iff]; exact not_congr (hinv σ hσ x)
  let ρ : G →* Perm (Γᶜ : Set Ω) :=
    { toFun := fun σ => (σ : Perm Ω).subtypePerm (hΔ σ σ.2)
      map_one' := by ext; rfl
      map_mul' := by intro a b; ext; rfl }
  have h1 : Nat.card G = Nat.card ρ.range * Nat.card ρ.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ρ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange ρ).toEquiv]
  have h2 : Nat.card ρ.range ≤ (Nat.card (Γᶜ : Set Ω))! := by
    rw [← Nat.card_perm]; exact Nat.card_le_card_of_injective _ Subtype.val_injective
  have hfix : ∀ σ : G, σ ∈ ρ.ker → ∀ x, (σ : Perm Ω) x ≠ x → x ∈ Γ := by
    intro σ hσ x hx
    by_contra hxΓ
    have := congrArg (fun f : Perm (Γᶜ : Set Ω) => ((f ⟨x, hxΓ⟩ : (Γᶜ : Set Ω)) : Ω))
      (MonoidHom.mem_ker.mp hσ)
    exact hx this
  let ψ : ρ.ker → restrictStab G Γ := fun σ =>
    ⟨((σ : G) : Perm Ω).subtypePerm (hinv _ (σ : G).2), by
      rw [mem_restrictStab, ofSubtype_subtypePerm _ (hfix σ σ.2)]; exact (σ : G).2⟩
  have hψ : Function.Injective ψ := by
    intro σ τ hστ
    have e := congrArg (fun f : restrictStab G Γ => ofSubtype (f : Perm Γ)) hστ
    simp only [ψ, ofSubtype_subtypePerm _ (hfix _ σ.2), ofSubtype_subtypePerm _ (hfix _ τ.2)] at e
    exact Subtype.ext (Subtype.ext e)
  have h3 := Nat.card_le_card_of_injective ψ hψ
  rw [h1]
  exact Nat.mul_le_mul h2 h3

/-- The arithmetic of [DiM, proof of Thm. 5.2A]: from `n! h' ≤ h (n−s)! s!`, `h < C(n,m)`
and `m < s < n` (with `m = ⌊n/2⌋`), Lemma 5.2A (ii) gives `h' (n − m) < C(s, ⌊s/2⌋)`. -/
theorem index_bound {n s h h' : ℕ} (hn : 5 ≤ n) (hms : n / 2 < s) (hsn : s < n)
    (hh : h < n.choose (n / 2))
    (hmain : n ! * h' ≤ h * ((n - s)! * s !)) :
    h' * (n - n / 2) < s.choose (s / 2) := by
  set m := n / 2
  set t := s / 2
  have hL := lemma_5_2A_ii m {n - s, t, s - t} (by simp) (by
      intro a ha
      simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at ha
      rcases ha with rfl | rfl | rfl <;> omega) (by simp; omega)
  have hsum : ({n - s, t, s - t} : Multiset ℕ).sum = n := by simp; omega
  rw [hsum] at hL
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.prod_cons,
    Multiset.map_singleton, Multiset.prod_singleton] at hL
  have hC := choose_half_mul n
  have hCs := Nat.choose_mul_factorial_mul_factorial (Nat.div_le_self s 2)
  have hf : (n - m)! = (n - m) * (n - m - 1)! := by
    rw [← Nat.mul_factorial_pred (by omega)]
  have hK : 0 < m ! * (n - m)! := by positivity
  have key : n.choose m * (h' * (n - m)) * (m ! * (n - m)!) ≤
      h * s.choose t * (m ! * (n - m)!) := by
    calc n.choose m * (h' * (n - m)) * (m ! * (n - m)!)
        = n ! * h' * (n - m) := by rw [← hC]; ring
      _ ≤ h * ((n - s)! * s !) * (n - m) := by gcongr
      _ = h * s.choose t * ((n - s)! * (t ! * (s - t)!)) * (n - m) := by rw [← hCs]; ring
      _ ≤ h * s.choose t * (m ! * (n - m - 1)!) * (n - m) := by gcongr
      _ = h * s.choose t * (m ! * (n - m)!) := by rw [hf]; ring
  have k2 := Nat.le_of_mul_le_mul_right key hK
  have hpos : 0 < s.choose t := Nat.choose_pos (Nat.div_le_self s 2)
  have k3 : n.choose m * (h' * (n - m)) < n.choose m * s.choose t :=
    lt_of_le_of_lt k2 (Nat.mul_lt_mul_of_pos_right hh hpos)
  exact Nat.lt_of_mul_lt_mul_left k3

/-- **[DiM, proof of Thm. 5.2A], the intransitive case**, given the theorem for smaller
degrees: an intransitive `G ≤ A` with `|A : G| < C(n, r)` satisfies case (i). -/
theorem intransitive_case
    (IH : ∀ (Γ : Type u) [Fintype Γ] [DecidableEq Γ], Nat.card Γ < Nat.card Ω → Statement52A Γ)
    (hn : 5 ≤ Nat.card Ω) {r : ℕ} (hr1 : 1 ≤ r) (hr2 : 2 * r ≤ Nat.card Ω)
    {G : Subgroup (Perm Ω)} (hGA : G ≤ alternatingGroup Ω)
    (hindex : G.relIndex (alternatingGroup Ω) < (Nat.card Ω).choose r)
    (hT : ¬ IsPretransitive G Ω) :
    ∃ Δ : Set Ω, Δ.ncard < r ∧
      pointwiseStabilizer (alternatingGroup Ω) Δ ≤ G ∧
      G ≤ setwiseStabilizer (alternatingGroup Ω) Δ := by
  classical
  haveI : Nontrivial Ω := by
    rw [← Finite.one_lt_card_iff_nontrivial]; omega
  have hh0 : 0 < G.relIndex (alternatingGroup Ω) := Nat.pos_of_ne_zero (by
    rw [Subgroup.relIndex]; exact Subgroup.index_ne_zero_of_finite)
  have hrm : (Nat.card Ω).choose r ≤ (Nat.card Ω).choose (Nat.card Ω / 2) :=
    choose_le_choose_of_le_half (by omega) le_rfl
  obtain ⟨x₀, hx₀⟩ := exists_large_orbit hn hGA (hindex.trans_le hrm)
  set n := Nat.card Ω with hn_def
  set m := n / 2 with hm_def
  set h := G.relIndex (alternatingGroup Ω) with hh_def
  set Γ : Set Ω := orbit G x₀ with hΓ
  have hinv : ∀ σ ∈ G, ∀ x, σ x ∈ Γ ↔ x ∈ Γ := fun σ hσ x => (mem_orbit_iff_apply hσ x).symm
  -- `s = |Γ| < n`, since `G` is intransitive
  have hsΓ : Nat.card Γ = Γ.ncard := Nat.card_coe_set_eq Γ
  have hΓc : Γ.ncard + Γᶜ.ncard = n := Set.ncard_add_ncard_compl Γ
  have hsn : Γ.ncard < n := by
    by_contra hc
    have h0 : (Γᶜ).ncard = 0 := by omega
    rw [Set.ncard_eq_zero, Set.compl_empty_iff] at h0
    apply hT
    refine ⟨fun a b => ?_⟩
    have ha : a ∈ Γ := h0 ▸ Set.mem_univ a
    have hb : b ∈ Γ := h0 ▸ Set.mem_univ b
    obtain ⟨g, hg⟩ := mem_orbit_iff.mp ha
    obtain ⟨k, hk⟩ := mem_orbit_iff.mp hb
    exact ⟨k * g⁻¹, by rw [mul_smul, ← hg, inv_smul_smul, hk]⟩
  have hΔc : Nat.card (Γᶜ : Set Ω) = n - Γ.ncard := by
    rw [Nat.card_coe_set_eq]; omega
  haveI : Nontrivial Γ := by
    rw [← Finite.one_lt_card_iff_nontrivial]; omega
  -- `H = G_(Δ)` on `Γ`, and `h' = |Alt(Γ) : H|`
  set H := restrictStab G Γ with hH
  have hHA := restrictStab_le_alternatingGroup hGA Γ
  set h' := H.relIndex (alternatingGroup Γ) with hh'_def
  have hG := card_le_factorial_mul_card_restrictStab Γ hinv
  rw [hΔc] at hG
  have e1 : 2 * (Nat.card G * h) = n ! := by
    rw [card_mul_relIndex hGA, two_mul_card_alternatingGroup]
  have e2 : 2 * (Nat.card H * h') = (Γ.ncard)! := by
    rw [card_mul_relIndex hHA, two_mul_card_alternatingGroup, hsΓ]
  have hmain : n ! * h' ≤ h * ((n - Γ.ncard)! * (Γ.ncard)!) := by
    rw [← e1, ← e2]
    calc 2 * (Nat.card G * h) * h' = 2 * Nat.card G * h * h' := by ring
      _ ≤ 2 * ((n - Γ.ncard)! * Nat.card H) * h * h' := by gcongr
      _ = h * ((n - Γ.ncard)! * (2 * (Nat.card H * h'))) := by ring
  have hbound : h' * (n - m) < (Γ.ncard).choose (Γ.ncard / 2) := index_bound hn hx₀ hsn (hindex.trans_le hrm) hmain
  have hnm3 : 3 ≤ n - m := by omega
  have hh'0 : 0 < h' := Nat.pos_of_ne_zero (by
    rw [hh'_def, Subgroup.relIndex]; exact Subgroup.index_ne_zero_of_finite)
  have h3h' : h' * 3 ≤ h' * (n - m) := Nat.mul_le_mul_left _ hnm3
  -- `Alt(Γ) ≤ H`
  have hAH : alternatingGroup Γ ≤ H := by
    by_cases hs4 : Γ.ncard ≤ 4
    · have hc : (Γ.ncard).choose (Γ.ncard / 2) ≤ 6 := by
        have : 3 ≤ Γ.ncard := by omega
        interval_cases (Γ.ncard) <;> decide
      have : h' = 1 := by omega
      exact (Subgroup.relIndex_eq_one).mp this
    · have hlt : h' < (Nat.card Γ).choose (Nat.card Γ / 2) := by rw [hsΓ]; omega
      have hC := IH Γ (by rw [hsΓ]; exact hsn) (by rw [hsΓ]; omega) (r := Nat.card Γ / 2)
        (by rw [hsΓ]; omega) (by omega) hHA hlt
      rcases concl_cases hC with ⟨S, hS, hlow, hup⟩ | h2 | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ |
          ⟨a, b⟩ | ⟨a, b⟩
      · -- `Σ = ∅`, by the transitivity of `G` on `Γ`
        let ρ : G →* Perm Γ :=
          { toFun := fun σ => (σ : Perm Ω).subtypePerm (hinv σ σ.2)
            map_one' := by ext; rfl
            map_mul' := by intro a b; ext; rfl }
        have hN : IsPretransitive ρ.range Γ := by
          refine ⟨fun a b => ?_⟩
          obtain ⟨g, hg⟩ := mem_orbit_iff.mp a.2
          obtain ⟨k, hk⟩ := mem_orbit_iff.mp b.2
          refine ⟨⟨ρ (k * g⁻¹), MonoidHom.mem_range.mpr ⟨_, rfl⟩⟩, Subtype.ext ?_⟩
          show ((k * g⁻¹ : G) : Perm Ω) (a : Ω) = b
          rw [← hg, ← hk]
          show ((k * g⁻¹ : G) : Perm Ω) ((g : Perm Ω) x₀) = (k : Perm Ω) x₀
          simp [Perm.mul_apply]
        have hnorm : ∀ g ∈ ρ.range, ∀ τ ∈ H, g * τ * g⁻¹ ∈ H := by
          rintro _ ⟨σ, rfl⟩ τ hτ
          show ofSubtype (_ * τ * _) ∈ G
          have := ofSubtype_conj (σ : Perm Ω) (hinv σ σ.2) τ
          simp only [ρ, MonoidHom.coe_mk, OneHom.coe_mk] at this ⊢
          rw [this]
          exact G.mul_mem (G.mul_mem σ.2 hτ) (G.inv_mem σ.2)
        have hS0 := eq_empty_of_sandwich (by omega) (by omega) hlow hup hN hnorm
        intro τ hτ
        exact hlow ⟨hτ, by simp [hS0]⟩
      · have h2' : 2 * h' = (Nat.card Γ).choose (Nat.card Γ / 2) := h2
        rw [hsΓ] at h2'
        omega
      all_goals
        exfalso
        have hb : h' = _ := b
        rw [hsΓ] at a
        rw [hb, a] at hbound
        norm_num [Nat.choose] at hbound
        omega
  -- the three conclusions for `Δ = Ω \ Γ`
  have hsub : pointwiseStabilizer (alternatingGroup Ω) Γᶜ ≤ G := by
    rintro σ ⟨hσA, hσΔ⟩
    have hσΓ : ∀ x, σ x ∈ Γ ↔ x ∈ Γ := by
      intro x
      by_cases hx : x ∈ Γ
      · refine iff_of_true ?_ hx
        by_contra hc
        have := hσΔ (σ x) hc
        rw [σ.injective this] at hc; exact hc hx
      · rw [hσΔ x hx]
    have hfix : ∀ x, σ x ≠ x → x ∈ Γ := fun x hx => by
      by_contra hc; exact hx (hσΔ x hc)
    have hτ : σ.subtypePerm hσΓ ∈ alternatingGroup Γ := by
      rw [mem_alternatingGroup, ← sign_ofSubtype, ofSubtype_subtypePerm _ hfix]; exact hσA
    have := hAH hτ
    rwa [hH, mem_restrictStab, ofSubtype_subtypePerm _ hfix] at this
  have hsup : G ≤ setwiseStabilizer (alternatingGroup Ω) Γᶜ := fun σ hσ =>
    ⟨hGA hσ, by rw [Set.image_compl_eq σ.bijective, image_orbit_eq x₀ hσ]⟩
  refine ⟨Γᶜ, ?_, hsub, hsup⟩
  by_contra hc
  push Not at hc
  have hΔn : (Γᶜ).ncard = n - Γ.ncard := by omega
  have hidx := relIndex_setwiseStabilizer (K := alternatingGroup Ω) le_rfl
    (m := (Γᶜ).ncard) (by omega) rfl
  have hdvd := Subgroup.relIndex_dvd_of_le_left (alternatingGroup Ω) hsup
  rw [hidx] at hdvd
  have h1 := Nat.le_of_dvd hh0 hdvd
  have h2 : n.choose r ≤ n.choose (Γᶜ).ncard := choose_le_choose_of_le_half hc (by omega)
  have hnn : n.choose (Γᶜ).ncard = (Nat.card Ω).choose (Γᶜ).ncard := rfl
  omega

end Babai.DM52
