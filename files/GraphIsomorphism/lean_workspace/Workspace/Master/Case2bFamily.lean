/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 13.2, case (2b): the family of individualized constituents, and its transport under
isomorphisms of the input.
-/
import Workspace.Master.Line567a

/-!
# Case (2b) of Theorem 13.2.1 as a canonical family

> 2b else let `d` be the degree of transitivity of `F^C` (: so `1 ≤ d ≤ 5` :)
>    individualize the elements of a set `S ∈ (C choose d−1)`
>    (: so `F^C_{(S)}` is transitive but not doubly transitive on `C' := C ∖ S` :)
>    Let `X = (C'; R₁, …, R_r)` be the orbital configuration of `F^C_{(S)}` on `C'`
>    (: **Warning**: the numbering of the `R_i` is not canonical; isomorphisms may permute
>    the `R_i` :)
>    Individualize one of the `X_i` (`i ≥ 2`) (: multiplicative cost `r − 1 ≤ m − 1` :)

`Babai.theorem_13_2_1` gives **one** individualization: some set `S` with `|S| = d − 1`, the
group-theoretic facts (`Babai.case2b_defect`) and the number `Babai.case2b_cost`.  That is
not enough for Sec. 15: the paper's Warning says the chosen constituent is *not* canonical,
and a canonical group does not make a chosen constituent canonical — the reflection of
`ZMod 5` normalizes the translation group and reverses the orbital `v = u + 1`.  What
Procedure Align consumes is the whole family over the individualizations, which is canonical
as a family (`Workspace/Master/Versions.lean`).  See the corrected paper entry on
Theorem 13.2.1 case (2b).

This file builds that family, and reads it **on `Γ`** rather than on the double subtype
`↥(Sᶜ : Set ↥C)` that `Babai.indivGroup` lives on.  Everything is written in terms of `F^Γ`
alone, so the transport under a conjugation of `F^Γ` is a computation and not a transfer
across subtypes:

| paper | Lean |
|---|---|
| the degree of transitivity of `F^C` | `Babai.MultTransOn`, `Babai.degtransOn` |
| `F^C_{(S)}` | `Babai.pointwiseStabilizer H S`, restricted to `C ∖ S` where needed |
| the orbital of `F^C_{(S)}` through `(a, b)` | `Babai.orbitalOn` |
| the individualizations and their constituents | `Babai.case2bFamily` |
| *"isomorphisms may permute the `R_i`"* | `Babai.case2bFamily_map_conj` |
| canonicity in the string | `Babai.case2bFamily_canonical` |

`Babai.case2bFamily H` is a set of pairs `(C', R)`: the vertex set `C' = C ∖ S` of the
constituent and its edge set `R`.  The Warning is absorbed exactly because the family is
transported as a **set**: `σ^ϕ` sends the family of `z` onto the family of `z^σ`, with no
claim about which member goes to which.
-/

universe u v

namespace Babai

open MulAction Equiv Equiv.Perm

section Case2bFamily

variable {Γ : Type*} [Fintype Γ] [DecidableEq Γ]

/-! ### The degree of transitivity of `F^C`, read on `Γ` -/

/-- §13.2, case (2b): **`H` is `d`-transitive on the subset `C`** — every injective `d`-tuple
of points of `C` is carried to every other by an element of `H`.

This is `Babai.IsMultiplyTransitive` for the group induced on `C`, written with tuples in
`Γ` so that a conjugation of `H` moves it by a computation
(`Babai.multTransOn_map_conj`).

The clause `d ≤ C.ncard` is not decoration.  Without it the quantifier over injective
`d`-tuples in `C` is **vacuously true** for every `d > |C|`, so the set of `d` would be
unbounded and `sSup` of an unbounded set of naturals is `0`.  That is exactly the
degenerate-case trap of `Babai.IsTransitiveAction` versus `MulAction.IsPretransitive`:
the paper's "`F^C` is `d`-transitive" asserts that the action on injective `d`-tuples has
*exactly one* orbit, which forces such a tuple to exist.  With the clause,
`Babai.multTransOn_iff_isMultiplyTransitive` is a clean bridge to
`Babai.IsMultiplyTransitive` of the induced group `F^C`. -/
def MultTransOn (H : Subgroup (Equiv.Perm Γ)) (C : Set Γ) (d : ℕ) : Prop :=
  d ≤ C.ncard ∧
  ∀ a b : Fin d → Γ, Function.Injective a → Function.Injective b →
    (∀ i, a i ∈ C) → (∀ i, b i ∈ C) → ∃ h ∈ H, ∀ i, (h : Equiv.Perm Γ) (a i) = b i

/-- §13.2, case (2b): **the degree of transitivity `d` of `F^C`**, read on `Γ`. -/
noncomputable def degtransOn (H : Subgroup (Equiv.Perm Γ)) (C : Set Γ) : ℕ :=
  sSup {d | MultTransOn H C d}

/-- The set of degrees of transitivity on `C` is bounded by `|C|`. -/
theorem bddAbove_multTransOn (H : Subgroup (Equiv.Perm Γ)) (C : Set Γ) :
    BddAbove {d | MultTransOn H C d} :=
  ⟨C.ncard, fun _ hd => hd.1⟩

/-- `H` is always `0`-transitive on a nonempty `C`. -/
theorem multTransOn_zero (H : Subgroup (Equiv.Perm Γ)) (C : Set Γ) : MultTransOn H C 0 :=
  ⟨Nat.zero_le _, fun _ _ _ _ _ _ => ⟨1, one_mem _, fun i => i.elim0⟩⟩

/-- **Regression test for the vacuity trap.**  A group is `1`-transitive on any of its
orbits.  With the old definition of `Babai.MultTransOn` (no `d ≤ C.ncard` clause) the set
`{d | MultTransOn H C d}` was unbounded, `degtransOn` was `sSup` of an unbounded set of
naturals, hence `0`, and this statement was false. -/
theorem one_le_degtransOn_orbit (H : Subgroup (Equiv.Perm Γ)) (γ : Γ) :
    1 ≤ degtransOn H (orbit H γ : Set Γ) := by
  refine le_csSup (bddAbove_multTransOn H _) ?_
  refine ⟨?_, fun a b _ _ haC hbC => ?_⟩
  · exact (Set.ncard_pos (Set.toFinite _)).2 ⟨γ, mem_orbit_self γ⟩
  · obtain ⟨h₁, hh₁⟩ := haC 0
    obtain ⟨h₂, hh₂⟩ := hbC 0
    refine ⟨(h₂ : Equiv.Perm Γ) * (h₁ : Equiv.Perm Γ)⁻¹,
      mul_mem h₂.2 (inv_mem h₁.2), fun i => ?_⟩
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    have hh₁' : (h₁ : Equiv.Perm Γ) γ = a 0 := hh₁
    have hh₂' : (h₂ : Equiv.Perm Γ) γ = b 0 := hh₂
    show ((h₂ : Equiv.Perm Γ) * (h₁ : Equiv.Perm Γ)⁻¹) (a 0) = b 0
    rw [Equiv.Perm.mul_apply, ← hh₁', ← hh₂']
    simp

/-- Conjugating `H` by `p` and moving `C` by `p` does not change `d`-transitivity on `C`. -/
theorem multTransOn_map_conj (H : Subgroup (Equiv.Perm Γ)) (p : Equiv.Perm Γ) (C : Set Γ)
    (d : ℕ) :
    MultTransOn (H.map (MulAut.conj p).toMonoidHom) (p '' C) d ↔ MultTransOn H C d := by
  have hcard : (p '' C).ncard = C.ncard := Set.ncard_image_of_injective C p.injective
  rw [MultTransOn, MultTransOn, hcard]
  refine and_congr_right fun _ => ?_
  constructor
  · intro hc a b ha hb haC hbC
    obtain ⟨h', hh', hval⟩ := hc (fun i => p (a i)) (fun i => p (b i))
      (fun i j hij => ha (p.injective hij)) (fun i j hij => hb (p.injective hij))
      (fun i => ⟨a i, haC i, rfl⟩) (fun i => ⟨b i, hbC i, rfl⟩)
    obtain ⟨g, hg, rfl⟩ := hh'
    refine ⟨g, hg, fun i => ?_⟩
    have h := hval i
    have h2 : p (g (a i)) = p (b i) := by
      simpa [Equiv.Perm.mul_apply] using h
    exact p.injective h2
  · intro hc a b ha hb haC hbC
    obtain ⟨a', ha'⟩ : ∃ a' : Fin d → Γ, ∀ i, a i = p (a' i) :=
      ⟨fun i => p⁻¹ (a i), fun i => by simp⟩
    obtain ⟨b', hb'⟩ : ∃ b' : Fin d → Γ, ∀ i, b i = p (b' i) :=
      ⟨fun i => p⁻¹ (b i), fun i => by simp⟩
    have ha'C : ∀ i, a' i ∈ C := by
      intro i
      obtain ⟨w, hw, hwe⟩ := haC i
      have : p (a' i) = p w := by rw [← ha' i, hwe]
      rw [p.injective this]
      exact hw
    have hb'C : ∀ i, b' i ∈ C := by
      intro i
      obtain ⟨w, hw, hwe⟩ := hbC i
      have : p (b' i) = p w := by rw [← hb' i, hwe]
      rw [p.injective this]
      exact hw
    obtain ⟨g, hg, hval⟩ := hc a' b'
      (fun i j hij => ha (by rw [ha' i, ha' j, hij]))
      (fun i j hij => hb (by rw [hb' i, hb' j, hij])) ha'C hb'C
    refine ⟨p * g * p⁻¹, ⟨g, hg, rfl⟩, fun i => ?_⟩
    rw [ha' i, hb' i]
    show (p * g * p⁻¹) (p (a' i)) = p (b' i)
    simp [Equiv.Perm.mul_apply, hval i]

/-- §13.2, case (2b): **the degree of transitivity of `F^C` is canonical**. -/
theorem degtransOn_map_conj (H : Subgroup (Equiv.Perm Γ)) (p : Equiv.Perm Γ) (C : Set Γ) :
    degtransOn (H.map (MulAut.conj p).toMonoidHom) (p '' C) = degtransOn H C := by
  rw [degtransOn, degtransOn]
  congr 1
  ext d
  exact multTransOn_map_conj H p C d

/-! ### The bridge to `Babai.IsMultiplyTransitive` of the induced group `F^C` -/

section Bridge

open scoped Classical

/-- §13.2, case (2b): **`d`-transitivity on `C`, read on `Γ`, is `d`-transitivity of the
induced group `F^C`.**  This is the sanity check of `Babai.MultTransOn`: the clause
`d ≤ C.ncard` is exactly what `Babai.IsMultiplyTransitive` (one orbit on injective
`d`-tuples, so at least one such tuple) contributes over bare pretransitivity. -/
theorem multTransOn_iff_isMultiplyTransitive (H : Subgroup (Equiv.Perm Γ)) {C : Set Γ}
    (hinv : IsInvariant H C) (d : ℕ) :
    MultTransOn H C d ↔ IsMultiplyTransitive (restrictTo H C hinv) d := by
  have hcard : Fintype.card ↥C = C.ncard := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
  rw [isMultiplyTransitive_iff, hcard]
  refine and_congr_right' ?_
  constructor
  · intro hmt
    refine ⟨fun p q => ?_⟩
    obtain ⟨h, hH, hval⟩ := hmt (fun i => ((p i : ↥C) : Γ)) (fun i => ((q i : ↥C) : Γ))
      (fun i j hij => p.injective (Subtype.ext hij))
      (fun i j hij => q.injective (Subtype.ext hij))
      (fun i => (p i).2) (fun i => (q i).2)
    refine ⟨⟨restrictHom H C hinv ⟨h, hH⟩, ⟨⟨h, hH⟩, rfl⟩⟩, ?_⟩
    ext i
    simpa [Subgroup.smul_def, Equiv.Perm.smul_def, restrictHom] using hval i
  · intro hpre a b ha hb haC hbC
    set p : Fin d ↪ ↥C :=
      ⟨fun i => (⟨a i, haC i⟩ : ↥C), fun i j hij => ha (congrArg Subtype.val hij)⟩ with hp
    set q : Fin d ↪ ↥C :=
      ⟨fun i => (⟨b i, hbC i⟩ : ↥C), fun i j hij => hb (congrArg Subtype.val hij)⟩ with hq
    obtain ⟨g, hg⟩ := hpre.exists_smul_eq p q
    obtain ⟨⟨h, hH⟩, hgh⟩ := g.2
    refine ⟨h, hH, fun i => ?_⟩
    have hi : (g : Equiv.Perm ↥C) (p i) = q i := by
      have := congrArg (fun w : Fin d ↪ ↥C => w i) hg
      simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using this
    rw [← hgh] at hi
    have h2 := congrArg Subtype.val hi
    simpa [hp, hq, restrictHom] using h2

/-- §13.2, case (2b): **the degree of transitivity of `F^C`**, read on `Γ`, is the degree of
transitivity of the induced group. -/
theorem degtransOn_eq_degtrans (H : Subgroup (Equiv.Perm Γ)) {C : Set Γ}
    (hinv : IsInvariant H C) : degtransOn H C = degtrans (restrictTo H C hinv) := by
  rw [degtransOn, degtrans]
  congr 1
  ext d
  exact multTransOn_iff_isMultiplyTransitive H hinv d

/-- §13.2, case (2b): `degtransOn H C` is attained and `degtransOn H C + 1` fails, for a
`H`-invariant `C`. -/
theorem degtransOn_spec (H : Subgroup (Equiv.Perm Γ)) {C : Set Γ} (hinv : IsInvariant H C) :
    MultTransOn H C (degtransOn H C) ∧ ¬ MultTransOn H C (degtransOn H C + 1) := by
  have hb := degtrans_spec (restrictTo H C hinv)
  rw [degtransOn_eq_degtrans H hinv]
  exact ⟨(multTransOn_iff_isMultiplyTransitive H hinv _).2 hb.1,
    fun hc => hb.2 ((multTransOn_iff_isMultiplyTransitive H hinv _).1 hc)⟩

end Bridge

/-! ### The pointwise stabilizer and its orbitals -/

/-- Conjugating `H` by `p` conjugates the pointwise stabilizer of `S` into the pointwise
stabilizer of `p(S)`. -/
theorem pointwiseStabilizer_map_conj (H : Subgroup (Equiv.Perm Γ)) (p : Equiv.Perm Γ)
    (S : Set Γ) :
    pointwiseStabilizer (H.map (MulAut.conj p).toMonoidHom) (p '' S)
      = (pointwiseStabilizer H S).map (MulAut.conj p).toMonoidHom := by
  ext x
  constructor
  · rintro ⟨⟨g, hg, rfl⟩, hfix⟩
    refine ⟨g, ⟨hg, fun s hs => ?_⟩, rfl⟩
    have h := hfix (p s) ⟨s, hs, rfl⟩
    have h2 : p (g s) = p s := by simpa [Equiv.Perm.mul_apply] using h
    exact p.injective h2
  · rintro ⟨g, ⟨hg, hgfix⟩, rfl⟩
    refine ⟨⟨g, hg, rfl⟩, ?_⟩
    rintro _ ⟨s, hs, rfl⟩
    show (p * g * p⁻¹) (p s) = p s
    simp [Equiv.Perm.mul_apply, hgfix s hs]

/-- §13.2, case (2b): **the orbital of `F^C_{(S)}` through the pair `(a, b)`** — the edge
set of the constituent the paper individualizes.  The vertex set `C ∖ S` is invariant under
the stabilizer, so the orbital stays inside `(C ∖ S) × (C ∖ S)` when `a` and `b` are in
`C ∖ S`. -/
def orbitalOn (H : Subgroup (Equiv.Perm Γ)) (S : Set Γ) (a b : Γ) : Set (Γ × Γ) :=
  {q | ∃ h ∈ pointwiseStabilizer H S, ((h : Equiv.Perm Γ) a, (h : Equiv.Perm Γ) b) = q}

/-- The orbital moves by `p` when `H` is conjugated by `p`. -/
theorem orbitalOn_map_conj (H : Subgroup (Equiv.Perm Γ)) (p : Equiv.Perm Γ) (S : Set Γ)
    (a b : Γ) :
    orbitalOn (H.map (MulAut.conj p).toMonoidHom) (p '' S) (p a) (p b)
      = (Prod.map p p) '' orbitalOn H S a b := by
  ext q
  constructor
  · rintro ⟨h, hh, rfl⟩
    rw [pointwiseStabilizer_map_conj] at hh
    obtain ⟨g, hg, rfl⟩ := hh
    refine ⟨((g : Equiv.Perm Γ) a, (g : Equiv.Perm Γ) b), ⟨g, hg, rfl⟩, ?_⟩
    show (p ((g : Equiv.Perm Γ) a), p ((g : Equiv.Perm Γ) b))
      = ((p * g * p⁻¹) (p a), (p * g * p⁻¹) (p b))
    simp [Equiv.Perm.mul_apply]
  · rintro ⟨q₀, ⟨g, hg, rfl⟩, rfl⟩
    refine ⟨p * g * p⁻¹, ?_, ?_⟩
    · rw [pointwiseStabilizer_map_conj]
      exact ⟨g, hg, rfl⟩
    · show ((p * g * p⁻¹) (p a), (p * g * p⁻¹) (p b))
        = Prod.map p p ((g : Equiv.Perm Γ) a, (g : Equiv.Perm Γ) b)
      simp [Equiv.Perm.mul_apply, Prod.map]

/-! ### The family of individualized constituents -/

/-- §13.2, **case (2b) as a family**: the constituents `X_i = (C', R_i)` over all
individualizations, read on `Γ`.

A member is a pair `(C ∖ S, R)` where

* `C` is an orbit of `F^Γ` with `|C| > 4m/5` — case (2)'s orbit, which is unique
  (`Babai.orbit_eq_of_two_large`);
* `S ⊆ C` has `d − 1` points, `d` the degree of transitivity of `F^C`
  (`Babai.degtransOn`) — *"individualize the elements of a set `S ∈ (C choose d−1)`"*;
* `R` is the orbital of `F^C_{(S)}` through a pair `(a, b)` of distinct points of `C ∖ S` —
  an off-diagonal constituent, the paper's `X_i` for `i ≥ 2`.

No member is singled out: the paper's *"Warning: the numbering of the `R_i` is not
canonical"* is why the family, and not one member, is what Sec. 15 line 6a consumes. -/
def case2bFamily (H : Subgroup (Equiv.Perm Γ)) : Set (Set Γ × Set (Γ × Γ)) :=
  {q | ∃ (γ : Γ) (S : Set Γ) (a b : Γ),
      4 * Fintype.card Γ < 5 * (orbit H γ : Set Γ).ncard ∧
      S ⊆ (orbit H γ : Set Γ) ∧ S.ncard = degtransOn H (orbit H γ : Set Γ) - 1 ∧
      a ∈ (orbit H γ : Set Γ) \ S ∧ b ∈ (orbit H γ : Set Γ) \ S ∧ a ≠ b ∧
      q = ((orbit H γ : Set Γ) \ S, orbitalOn H S a b)}

/-- Moving a member of the family by a permutation of `Γ`. -/
def moveCase2b (p : Equiv.Perm Γ) (q : Set Γ × Set (Γ × Γ)) : Set Γ × Set (Γ × Γ) :=
  (p '' q.1, (Prod.map p p) '' q.2)

/-- §13.2, case (2b): **the family is canonical**.  A conjugation of `F^Γ` by `p` carries
the family onto the family, member by member up to the permutation of the members that the
paper's Warning allows.

This is what `Babai.theorem_13_2_1` does not say and what Procedure Align needs: the
individualized constituent is not canonical, but the set of all of them is. -/
theorem case2bFamily_map_conj (H : Subgroup (Equiv.Perm Γ)) (p : Equiv.Perm Γ) :
    case2bFamily (H.map (MulAut.conj p).toMonoidHom) = moveCase2b p '' case2bFamily H := by
  have hcard : ∀ (γ : Γ),
      (orbit (H.map (MulAut.conj p).toMonoidHom) (p γ) : Set Γ).ncard
        = (orbit H γ : Set Γ).ncard := by
    intro γ
    rw [orbit_map_conj H p γ]
    exact Set.ncard_image_of_injective _ p.injective
  ext q
  constructor
  · rintro ⟨δ, S', a', b', hbig, hS'sub, hS'card, ha', hb', hab', rfl⟩
    -- pull `δ`, `S'`, `a'`, `b'` back along `p`
    obtain ⟨γ, rfl⟩ : ∃ γ : Γ, p γ = δ := ⟨p⁻¹ δ, by simp⟩
    set S : Set Γ := p ⁻¹' S' with hSdef
    have hS' : p '' S = S' := Set.image_preimage_eq _ p.surjective
    have horb : (orbit (H.map (MulAut.conj p).toMonoidHom) (p γ) : Set Γ)
        = p '' (orbit H γ : Set Γ) := orbit_map_conj H p γ
    have hSsub : S ⊆ (orbit H γ : Set Γ) := by
      intro s hs
      have : p s ∈ S' := hs
      have h2 : p s ∈ p '' (orbit H γ : Set Γ) := by rw [← horb]; exact hS'sub this
      obtain ⟨w, hw, hwe⟩ := h2
      rw [← p.injective hwe]
      exact hw
    have hSncard : S.ncard = S'.ncard := by
      rw [← hS', Set.ncard_image_of_injective _ p.injective]
    have hdeg : degtransOn (H.map (MulAut.conj p).toMonoidHom)
        (orbit (H.map (MulAut.conj p).toMonoidHom) (p γ) : Set Γ)
        = degtransOn H (orbit H γ : Set Γ) := by
      rw [horb]
      exact degtransOn_map_conj H p _
    obtain ⟨a, rfl⟩ : ∃ a : Γ, p a = a' := ⟨p⁻¹ a', by simp⟩
    obtain ⟨b, rfl⟩ : ∃ b : Γ, p b = b' := ⟨p⁻¹ b', by simp⟩
    have hmem : ∀ w : Γ, p w ∈ (orbit (H.map (MulAut.conj p).toMonoidHom) (p γ) : Set Γ) \ S'
        ↔ w ∈ (orbit H γ : Set Γ) \ S := by
      intro w
      constructor
      · rintro ⟨h1, h2⟩
        rw [horb] at h1
        obtain ⟨u, hu, hue⟩ := h1
        exact ⟨by rw [← p.injective hue]; exact hu, fun hc => h2 hc⟩
      · rintro ⟨h1, h2⟩
        refine ⟨by rw [horb]; exact ⟨w, h1, rfl⟩, fun hc => h2 hc⟩
    have hdiff : (orbit (H.map (MulAut.conj p).toMonoidHom) (p γ) : Set Γ) \ S'
        = p '' ((orbit H γ : Set Γ) \ S) := by
      ext w
      constructor
      · intro hw
        refine ⟨p⁻¹ w, ?_, by simp⟩
        exact (hmem (p⁻¹ w)).1 (by simpa using hw)
      · rintro ⟨u, hu, rfl⟩
        exact (hmem u).2 hu
    refine ⟨((orbit H γ : Set Γ) \ S, orbitalOn H S a b),
      ⟨γ, S, a, b, by rw [← hcard γ]; exact hbig, hSsub, ?_, (hmem a).1 ha', (hmem b).1 hb',
        fun hc => hab' (by rw [hc]), rfl⟩, ?_⟩
    · rw [hSncard, hS'card, hdeg]
    · symm
      show ((orbit (H.map (MulAut.conj p).toMonoidHom) (p γ) : Set Γ) \ S',
        orbitalOn (H.map (MulAut.conj p).toMonoidHom) S' (p a) (p b))
        = moveCase2b p ((orbit H γ : Set Γ) \ S, orbitalOn H S a b)
      rw [moveCase2b, hdiff, ← hS', orbitalOn_map_conj]
  · rintro ⟨q₀, ⟨γ, S, a, b, hbig, hSsub, hScard, ha, hb, hab, rfl⟩, rfl⟩
    have horb : (orbit (H.map (MulAut.conj p).toMonoidHom) (p γ) : Set Γ)
        = p '' (orbit H γ : Set Γ) := orbit_map_conj H p γ
    have hdeg : degtransOn (H.map (MulAut.conj p).toMonoidHom)
        (orbit (H.map (MulAut.conj p).toMonoidHom) (p γ) : Set Γ)
        = degtransOn H (orbit H γ : Set Γ) := by
      rw [horb]
      exact degtransOn_map_conj H p _
    refine ⟨p γ, p '' S, p a, p b, by rw [hcard γ]; exact hbig, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [horb]
      exact Set.image_mono hSsub
    · rw [Set.ncard_image_of_injective _ p.injective, hScard, hdeg]
    · exact ⟨by rw [horb]; exact ⟨a, ha.1, rfl⟩,
        fun ⟨w, hw, hwe⟩ => ha.2 (by rw [← p.injective hwe]; exact hw)⟩
    · exact ⟨by rw [horb]; exact ⟨b, hb.1, rfl⟩,
        fun ⟨w, hw, hwe⟩ => hb.2 (by rw [← p.injective hwe]; exact hw)⟩
    · exact fun hc => hab (p.injective hc)
    · show moveCase2b p ((orbit H γ : Set Γ) \ S, orbitalOn H S a b)
        = ((orbit (H.map (MulAut.conj p).toMonoidHom) (p γ) : Set Γ) \ p '' S,
          orbitalOn (H.map (MulAut.conj p).toMonoidHom) (p '' S) (p a) (p b))
      rw [moveCase2b, orbitalOn_map_conj, horb, Set.image_diff p.injective]

end Case2bFamily

/-! ### Canonicity in the string -/

section Canonical

variable {Ω Γ Λ : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype Γ] [DecidableEq Γ]
  {G : Subgroup (Equiv.Perm Ω)}

open scoped Classical in
/-- Conjugation preserves the alternating subgroup condition on an orbit.
The bijection between the orbits sends `a` to `p a`. -/
theorem alternating_le_restrictTo_orbit_map_conj (H : Subgroup (Equiv.Perm Γ))
    (p : Equiv.Perm Γ) (γ : Γ) :
    alternatingGroup (orbit (H.map (MulAut.conj p).toMonoidHom) (p γ) : Set Γ) ≤
        restrictTo (H.map (MulAut.conj p).toMonoidHom) _ (isInvariant_orbit _ (p γ)) ↔
      alternatingGroup (orbit H γ : Set Γ) ≤ restrictTo H _ (isInvariant_orbit H γ) := by
  classical
  let H' := H.map (MulAut.conj p).toMonoidHom
  let C : Set Γ := orbit H γ
  let C' : Set Γ := orbit H' (p γ)
  have hC : C' = p '' C := orbit_map_conj H p γ
  let e : C ≃ C' := (Equiv.Set.image (p : Γ → Γ) C p.injective).trans
    (Equiv.setCongr hC.symm)
  have he (a : C) : (e a : Γ) = p (a : Γ) := rfl
  have hres (g : H) :
      restrictHom H' C' (isInvariant_orbit H' (p γ))
          ⟨p * (g : Equiv.Perm Γ) * p⁻¹, ⟨g, g.2, rfl⟩⟩ =
        (Equiv.permCongrHom e) (restrictHom H C (isInvariant_orbit H γ) g) := by
    refine Equiv.ext fun b => ?_
    obtain ⟨a, rfl⟩ := e.surjective b
    apply Subtype.ext
    change (p * (g : Equiv.Perm Γ) * p⁻¹) (e a : Γ) =
      (e (restrictHom H C (isInvariant_orbit H γ) g (e.symm (e a))) : Γ)
    rw [Equiv.symm_apply_apply, he, he]
    simp [Equiv.Perm.mul_apply, restrictHom]
  have hmap : restrictTo H' C' (isInvariant_orbit H' (p γ)) =
      (restrictTo H C (isInvariant_orbit H γ)).map (Equiv.permCongrHom e).toMonoidHom := by
    ext k
    constructor
    · rintro ⟨⟨_, g, hg, rfl⟩, rfl⟩
      exact ⟨_, ⟨⟨g, hg⟩, rfl⟩, (hres ⟨g, hg⟩).symm⟩
    · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
      exact ⟨⟨_, ⟨g, g.2, rfl⟩⟩, hres g⟩
  change alternatingGroup C' ≤ restrictTo H' C' _ ↔ alternatingGroup C ≤ restrictTo H C _
  rw [hmap, alternating_le_map_permCongrHom_iff]

/-- §13.2, case (2b): the string's own case test is invariant under `G`-shifts.
Conjugation of `F(z)^Γ` preserves orbit sizes and the alternating subgroup condition. -/
theorem case2b_test_strAct (ϕ : G →* Equiv.Perm Γ) (z : Ω → Λ) (t : ℕ) (σ : G) :
    (Case2 (bigFGamma ϕ (strAct z (σ : Equiv.Perm Ω)) t) ∧
        ¬ AggregateCase2a ϕ (strAct z (σ : Equiv.Perm Ω)) t) ↔
      (Case2 (bigFGamma ϕ z t) ∧ ¬ AggregateCase2a ϕ z t) := by
  classical
  let H := bigFGamma ϕ z t
  let p := ϕ σ
  have hsize (γ : Γ) : (orbit (H.map (MulAut.conj p).toMonoidHom) (p γ) : Set Γ).ncard =
      (orbit H γ : Set Γ).ncard := by
    rw [orbit_map_conj, Set.ncard_image_of_injective _ p.injective]
  have h2 : Case2 (H.map (MulAut.conj p).toMonoidHom) ↔ Case2 H := by
    constructor
    · rintro ⟨δ, hδ⟩
      obtain ⟨γ, rfl⟩ := p.surjective δ
      exact ⟨γ, by rwa [hsize] at hδ⟩
    · rintro ⟨γ, hγ⟩
      exact ⟨p γ, by rwa [hsize]⟩
  have h2a : AggregateCase2a ϕ (strAct z (σ : Equiv.Perm Ω)) t ↔
      AggregateCase2a ϕ z t := by
    let P : Subgroup (Equiv.Perm Γ) → Prop := fun K =>
      ∃ γ : Γ, 4 * Fintype.card Γ < 5 * (orbit K γ : Set Γ).ncard ∧
        alternatingGroup (orbit K γ : Set Γ) ≤ restrictTo K _ (isInvariant_orbit K γ)
    change P (bigFGamma ϕ (strAct z (σ : Equiv.Perm Ω)) t) ↔ P H
    rw [canonical_bigFGamma]
    constructor
    · rintro ⟨δ, hδ, hAlt⟩
      obtain ⟨γ, rfl⟩ := p.surjective δ
      exact ⟨γ, by rwa [hsize] at hδ,
        (alternating_le_restrictTo_orbit_map_conj H p γ).1 hAlt⟩
    · rintro ⟨γ, hγ, hAlt⟩
      exact ⟨p γ, by rwa [hsize],
        (alternating_le_restrictTo_orbit_map_conj H p γ).2 hAlt⟩
  rw [h2a, canonical_bigFGamma]
  exact and_congr h2 Iff.rfl

/-- §13.2, case (2b): **the family is canonically attached to the string**.  A `G`-shift of
the string moves the whole family by the corresponding permutation of `Γ`, which is
canonicity in the sense `Workspace/Master/Versions.lean` asks for — with no claim about
which member goes to which, as the paper's Warning requires. -/
theorem case2bFamily_canonical (ϕ : G →* Equiv.Perm Γ) (z : Ω → Λ) (t : ℕ) (σ : G) :
    case2bFamily (bigFGamma ϕ (strAct z (σ : Equiv.Perm Ω)) t)
      = moveCase2b (ϕ σ) '' case2bFamily (bigFGamma ϕ z t) := by
  rw [canonical_bigFGamma ϕ z t σ]
  exact case2bFamily_map_conj _ _

end Canonical

end Babai
