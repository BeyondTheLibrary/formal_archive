/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 10.4, Notation 10.4.3: the orbits of a group that sandwiches a small set.
-/
import Workspace.AltQuotients.SmallIndex

/-!
# The orbits of a sandwiching group (§10.4, Eq. (51))

Notation 10.4.3 writes `T(H)` for the unique set with
`A(Ω)_(T) ≤ H ≤ S(Ω)_T` and `|T| < n/2`, which is `Babai.IsSandwichSet H T`
(Eq. (51)).  This file reads that condition off the **orbits** of `H`.

The proof of Observation 10.4.1 already contains the argument: if `|Ω ∖ T| ≥ 3` then
`Ω ∖ T` is one orbit of `A(Ω)_(T)`, hence one orbit of `H`, because `H` also keeps `T`
fixed setwise.  Every other orbit of `H` lies inside `T`, so it is short.  Since
`2|T| < n`, the orbit `Ω ∖ T` is long and every other orbit is short.  So

> a point lies in `T` exactly when its `H`-orbit is short.

This is what lets a machine find `T` from generators of `H`: compute the orbits and keep
the points whose orbit is shorter than half the domain.  The routine is
`Algo.rawTpoint` (`Workspace/Algo/TpointRaw.lean`).

## Main results

* `Babai.orbit_eq_compl_of_isSandwichSet` — `Ω ∖ T` is an orbit of `H`;
* `Babai.orbit_subset_of_isSandwichSet` — an orbit that meets `T` stays inside `T`;
* `Babai.two_mul_ncard_orbit_lt_iff` — `x ∈ T` exactly when `2 |x^H| < n`;
* `Babai.eq_setOf_two_mul_ncard_orbit_lt` — `T` is the set of points with a short orbit;
* `Babai.three_le_ncard_compl_of_four_mul_lt` — the hypothesis `|Ω ∖ T| ≥ 3` holds in the
  situation of Theorem 10.5.1 (a), where `4|T| < k` and `k ≥ 9`.
-/

namespace Babai

open MulAction Equiv Equiv.Perm

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- A sandwiching group keeps `T` fixed setwise, so it keeps the complement fixed too:
the orbit of a point outside `T` stays outside `T`. -/
theorem orbit_subset_compl_of_isSandwichSet {H : Subgroup (Equiv.Perm Ω)} {T : Set Ω}
    (h : IsSandwichSet H T) {a : Ω} (ha : a ∉ T) : orbit H a ⊆ Tᶜ := by
  rintro _ ⟨σ, rfl⟩
  have himg : (σ : Equiv.Perm Ω) '' T = T := (h.2.2 σ.2).2
  intro hmem
  have hmem' : (σ : Equiv.Perm Ω) a ∈ (σ : Equiv.Perm Ω) '' T := by
    rw [himg]; exact hmem
  obtain ⟨x, hx, hxa⟩ := hmem'
  exact ha ((σ : Equiv.Perm Ω).injective hxa ▸ hx)

/-- A sandwiching group keeps `T` fixed setwise: the orbit of a point of `T` stays
inside `T`. -/
theorem orbit_subset_of_isSandwichSet {H : Subgroup (Equiv.Perm Ω)} {T : Set Ω}
    (h : IsSandwichSet H T) {a : Ω} (ha : a ∈ T) : orbit H a ⊆ T := by
  rintro _ ⟨σ, rfl⟩
  have himg : (σ : Equiv.Perm Ω) '' T = T := (h.2.2 σ.2).2
  rw [← himg]
  exact ⟨a, ha, rfl⟩

/-- `A(Ω)_(T) ≤ H` is transitive on `Ω ∖ T` as soon as `|Ω ∖ T| ≥ 3`, so the complement
of `T` is contained in each of its `H`-orbits. -/
theorem compl_subset_orbit_of_isSandwichSet {H : Subgroup (Equiv.Perm Ω)} {T : Set Ω}
    (h : IsSandwichSet H T) (h3 : 3 ≤ (Tᶜ : Set Ω).ncard) {a : Ω} (ha : a ∉ T) :
    (Tᶜ : Set Ω) ⊆ orbit H a := by
  intro b hb
  obtain ⟨σ, hσ, hσa⟩ :=
    exists_mem_alt_pointwiseStabilizer_apply_eq h3 ha (Set.mem_compl_iff _ _ |>.1 hb)
  exact ⟨⟨σ, h.2.1 hσ⟩, hσa⟩

/-- **`Ω ∖ T` is one orbit of `H`** (§10.4, the step in the proof of Observation 10.4.1).
The hypothesis `|Ω ∖ T| ≥ 3` is what makes `A(Ω)_(T)` transitive there. -/
theorem orbit_eq_compl_of_isSandwichSet {H : Subgroup (Equiv.Perm Ω)} {T : Set Ω}
    (h : IsSandwichSet H T) (h3 : 3 ≤ (Tᶜ : Set Ω).ncard) {a : Ω} (ha : a ∉ T) :
    orbit H a = Tᶜ :=
  le_antisymm (orbit_subset_compl_of_isSandwichSet h ha)
    (compl_subset_orbit_of_isSandwichSet h h3 ha)

/-- **A point lies in `T` exactly when its orbit is short.**  An orbit inside `T` has at
most `|T|` points and `2|T| < n`; the one orbit outside `T` is all of `Ω ∖ T`, which has
more than `n/2` points. -/
theorem two_mul_ncard_orbit_lt_iff {H : Subgroup (Equiv.Perm Ω)} {T : Set Ω}
    (h : IsSandwichSet H T) (h3 : 3 ≤ (Tᶜ : Set Ω).ncard) (a : Ω) :
    2 * (orbit H a).ncard < Nat.card Ω ↔ a ∈ T := by
  have hsum := ncard_add_ncard_compl (Ω := Ω) T
  have h1 := h.1
  constructor
  · intro hlt
    by_contra ha
    rw [orbit_eq_compl_of_isSandwichSet h h3 ha] at hlt
    omega
  · intro ha
    have hle : (orbit H a).ncard ≤ T.ncard :=
      Set.ncard_le_ncard (orbit_subset_of_isSandwichSet h ha) (Set.toFinite _)
    omega

/-- **`T` is the set of points with a short orbit.**  This is the form the routine uses. -/
theorem eq_setOf_two_mul_ncard_orbit_lt {H : Subgroup (Equiv.Perm Ω)} {T : Set Ω}
    (h : IsSandwichSet H T) (h3 : 3 ≤ (Tᶜ : Set Ω).ncard) :
    T = {a : Ω | 2 * (orbit H a).ncard < Nat.card Ω} := by
  ext a
  rw [Set.mem_setOf_eq, two_mul_ncard_orbit_lt_iff h h3]

/-- The hypothesis `|Ω ∖ T| ≥ 3` in the situation of Theorem 10.5.1 (a): there
`4|T| < k = |Ω|` and `k ≥ 9`. -/
theorem three_le_ncard_compl_of_four_mul_lt {T : Set Ω} (h4 : 4 * T.ncard < Nat.card Ω)
    (h9 : 9 ≤ Nat.card Ω) : 3 ≤ (Tᶜ : Set Ω).ncard := by
  have hsum := ncard_add_ncard_compl (Ω := Ω) T
  omega

end Babai
