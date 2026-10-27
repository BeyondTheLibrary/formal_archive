/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 13.2, case (3): the canonical structure as a function of a single string.
-/
import Workspace.LocalCertificates.Aggregate
import Workspace.Master.TestSet

/-!
# Case (3) of Theorem 13.2.1 as a single-string assignment

Sec. 13.2 runs AggregateCertificates on the pair `(x, y)`, and in case (3) it says

> Below we ignore `y` and focus on `x`, omitting it from the notation, so we write
> `F = F(x)`.  But our guide is the above consequence of canonicity.

So the object it builds, the `t`-ary relational structure `𝔷` on `D = D(x)`, is a function
of the single string `x`; what the pair is for is the canonicity clause, which compares
`𝔷(x)` with `𝔷(y)` along an isomorphism `x → y`.

`Babai.claim_13_2_1_3` is already stated for an arbitrary finite family of inputs
`y : I → (Ω → Σ)`, so the single-string form costs nothing but a choice of index set: take
for `I` a **set of strings** `S`, and the family `Subtype.val`.  The result,
`Babai.claim_13_2_1_3_onSet`, is an assignment `z ↦ 𝔷(z)` defined for every `z ∈ S`, with
the equivariance `𝔷(z^σ) = 𝔷(z)^{σ^ϕ}` of `Babai.IsCanonicalVersions` written out on the
sets `D(z)` — the form `Workspace/Master/Bridge.lean` uses, where
`Babai.strIso_eq_iUnion_versionPiece` consults canonicity only at `x` and at the elements
of `Iso_G(x,y)`, that is, only along `G`-translates of `x`.

Which `S`?  The construction needs `S` finite and `4m < 5|D(z)|` for every `z ∈ S`.  Both
are automatic for the union of the `G`-orbits of the two input strings
(`Babai.strOrbit`): the orbit is the image of the finite group `G`, and `|D(z)|` is
constant on an orbit because `D(z^σ) = D(z)^{σ^ϕ}` (`Babai.canonical_fixedGamma`).  That is
`Babai.claim_13_2_1_3_onOrbits`, and the pairwise statement of `Babai.theorem_13_2_1` is
read off from it (`Babai.isCase3Output_pair_of_onOrbits`).

**The choice made.**  Of the two repairs that `Workspace/Master/DESIGN.md` listed for
Mismatch 3 — a single-string restatement of case (3), or a pairwise version of
`Workspace/Master/Bridge.lean` — this is the first.  It is the one the paper's own sentence
points at, it leaves `Master/Bridge.lean` alone, and it is where the existing
`Babai.claim_13_2_1_3` already was: nothing in `Workspace/LocalCertificates/` changes.
-/

universe u v

namespace Babai

open MulAction Equiv Equiv.Perm
open scoped Classical

variable {Ω Γ Λ : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype Γ] [DecidableEq Γ]
  {G : Subgroup (Equiv.Perm Ω)}

/-! ### The `G`-orbit of a string -/

/-- The `G`-orbit of the string `x`: all the strings `x^σ`, `σ ∈ G`.  Canonicity of
case (3) is a statement about these strings only. -/
def strOrbit (G : Subgroup (Equiv.Perm Ω)) (x : Ω → Λ) : Set (Ω → Λ) :=
  {z | ∃ σ : G, z = strAct x (σ : Equiv.Perm Ω)}

theorem mem_strOrbit_self (G : Subgroup (Equiv.Perm Ω)) (x : Ω → Λ) : x ∈ strOrbit G x :=
  ⟨1, by simp [strAct]⟩

/-- The `G`-orbit of a string is finite: it is the image of the finite group `G`. -/
theorem strOrbit_finite (G : Subgroup (Equiv.Perm Ω)) (x : Ω → Λ) :
    (strOrbit G x).Finite := by
  haveI : Finite G := Subtype.finite
  have : strOrbit G x = Set.range (fun σ : G => strAct x (σ : Equiv.Perm Ω)) := by
    ext z; exact ⟨fun ⟨σ, hσ⟩ => ⟨σ, hσ.symm⟩, fun ⟨σ, hσ⟩ => ⟨σ, hσ.symm⟩⟩
  rw [this]
  exact Set.finite_range _

/-- `|D(z)|` is constant on a `G`-orbit of strings: `D(x^σ) = D(x)^{σ^ϕ}`
(`Babai.canonical_fixedGamma`) and `σ^ϕ` is a bijection. -/
theorem ncard_fixedGamma_of_mem_strOrbit (ϕ : G →* Equiv.Perm Γ) (x : Ω → Λ) (t : ℕ)
    {z : Ω → Λ} (hz : z ∈ strOrbit G x) :
    (fixedGamma ϕ z t).ncard = (fixedGamma ϕ x t).ncard := by
  obtain ⟨σ, rfl⟩ := hz
  rw [canonical_fixedGamma ϕ x t σ]
  exact Set.ncard_image_of_injective _ (ϕ σ).injective

/-! ### Case (3) as an assignment on a set of strings -/

/-- §13.2, **case (3) as a single-string assignment**.

For a finite set `S` of strings, each of which lands in case (3), there is one `t`-ary
relational structure `𝔷(z)` on `D(z)` per `z ∈ S`, with symmetry defect `≥ |D(z)| − t + 1`
and `> m/2`, such that every `G`-isomorphism `z → z'` between members of `S` carries `𝔷(z)`
to `𝔷(z')` along the bijection `D(z) → D(z')` induced by `σ^ϕ`.

This is `Babai.claim_13_2_1_3` with the index family `Subtype.val : ↥S → (Ω → Σ)`; the
point is that the structure depends on the one string `z` and on nothing else, which is
what Sec. 15 line 6 and `Workspace/Master/Bridge.lean` ask for. -/
theorem claim_13_2_1_3_onSet (ϕ : G →* Equiv.Perm Γ) (t : ℕ) (S : Set (Ω → Λ))
    (hS : S.Finite) (hset : LocalCertSetting G ϕ) (ht : LargeK t (Nat.card Ω))
    (htm : 10 * t ≤ Fintype.card Γ)
    (hD : ∀ z ∈ S, 4 * Fintype.card Γ < 5 * (fixedGamma ϕ z t).ncard) :
    ∃ 𝔷 : ∀ z : ↥S, RelStructure ↥(fixedGamma ϕ (z : Ω → Λ) t),
      IsCase3Output ϕ t (fun z : ↥S => (z : Ω → Λ)) 𝔷 := by
  haveI : Finite ↥S := hS
  exact claim_13_2_1_3 ϕ t (fun z : ↥S => (z : Ω → Λ)) hset ht htm
    (fun z => hD (z : Ω → Λ) z.2)

/-- §13.2, case (3): the set of strings on which the assignment is built for the pair
`(x, y)` — the union of their `G`-orbits. -/
def strOrbitPair (G : Subgroup (Equiv.Perm Ω)) (x y : Ω → Λ) : Set (Ω → Λ) :=
  strOrbit G x ∪ strOrbit G y

theorem strOrbitPair_finite (G : Subgroup (Equiv.Perm Ω)) (x y : Ω → Λ) :
    (strOrbitPair G x y).Finite :=
  (strOrbit_finite G x).union (strOrbit_finite G y)

theorem mem_strOrbitPair_left (G : Subgroup (Equiv.Perm Ω)) (x y : Ω → Λ) :
    x ∈ strOrbitPair G x y := Or.inl (mem_strOrbit_self G x)

theorem mem_strOrbitPair_right (G : Subgroup (Equiv.Perm Ω)) (x y : Ω → Λ) :
    y ∈ strOrbitPair G x y := Or.inr (mem_strOrbit_self G y)

/-- §13.2, **case (3) for the two input strings and all their translates**.

The hypotheses are the ones the case distinction hands over: both `x` and `y` land in
case (3), `4m < 5|D|`.  Every translate of `x` or of `y` then lands in case (3) as well,
because `|D|` is constant on an orbit, so the assignment of `Babai.claim_13_2_1_3_onSet`
is available on the whole of `strOrbit G x ∪ strOrbit G y`. -/
theorem claim_13_2_1_3_onOrbits (ϕ : G →* Equiv.Perm Γ) (t : ℕ) (x y : Ω → Λ)
    (hset : LocalCertSetting G ϕ) (ht : LargeK t (Nat.card Ω))
    (htm : 10 * t ≤ Fintype.card Γ)
    (hx : 4 * Fintype.card Γ < 5 * (fixedGamma ϕ x t).ncard)
    (hy : 4 * Fintype.card Γ < 5 * (fixedGamma ϕ y t).ncard) :
    ∃ 𝔷 : ∀ z : ↥(strOrbitPair G x y), RelStructure ↥(fixedGamma ϕ (z : Ω → Λ) t),
      IsCase3Output ϕ t (fun z : ↥(strOrbitPair G x y) => (z : Ω → Λ)) 𝔷 := by
  refine claim_13_2_1_3_onSet ϕ t _ (strOrbitPair_finite G x y) hset ht htm ?_
  rintro z (hz | hz)
  · rw [ncard_fixedGamma_of_mem_strOrbit ϕ x t hz]; exact hx
  · rw [ncard_fixedGamma_of_mem_strOrbit ϕ y t hz]; exact hy

/-- §13.2, case (3): **the pairwise statement of Theorem 13.2.1 follows from the
single-string one**.  Restrict the assignment of `Babai.claim_13_2_1_3_onOrbits` to the two
strings `x` and `y`. -/
theorem isCase3Output_pair_of_onOrbits (ϕ : G →* Equiv.Perm Γ) (t : ℕ) (x y : Ω → Λ)
    (hset : LocalCertSetting G ϕ) (ht : LargeK t (Nat.card Ω))
    (htm : 10 * t ≤ Fintype.card Γ)
    (hx : 4 * Fintype.card Γ < 5 * (fixedGamma ϕ x t).ncard)
    (hy : 4 * Fintype.card Γ < 5 * (fixedGamma ϕ y t).ncard) :
    ∃ 𝔷 : ∀ i : Fin 2, RelStructure ↥(fixedGamma ϕ (![x, y] i) t),
      IsCase3Output ϕ t ![x, y] 𝔷 := by
  obtain ⟨𝔷, hkary, hdef, hhalf, hcan⟩ :=
    claim_13_2_1_3_onOrbits ϕ t x y hset ht htm hx hy
  have hmem : ∀ i : Fin 2, ![x, y] i ∈ strOrbitPair G x y := by
    intro i
    match i with
    | 0 => exact mem_strOrbitPair_left G x y
    | 1 => exact mem_strOrbitPair_right G x y
  exact ⟨fun i => 𝔷 ⟨![x, y] i, hmem i⟩, fun i => hkary ⟨![x, y] i, hmem i⟩,
    fun i => hdef ⟨![x, y] i, hmem i⟩, fun i => hhalf ⟨![x, y] i, hmem i⟩,
    fun i j σ hσ => hcan ⟨![x, y] i, hmem i⟩ ⟨![x, y] j, hmem j⟩ σ hσ⟩

end Babai
