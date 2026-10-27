/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 13.2, case (2b): the relative symmetry defect of an individualized constituent,
read on `Γ`.
-/
import Workspace.Master.Case2bStruct

/-!
# Case (2b): the constituent has relative symmetry defect `≥ 1/2`

> individualize the elements of a set `S ∈ (C choose d−1)` (: so `F^C_{(S)}` is transitive
> but not doubly transitive on `C' := C ∖ S` :) … Individualize one of the `X_i` (`i ≥ 2`)
> … (: `X_i` has relative symmetry defect `≥ 1/2` by Cor. 2.4.12 :)

`Workspace/LocalCertificates/Aggregate.lean` proves this on the double subtype
`↥(Sᶜ : Set ↥C)` that `Babai.indivGroup` lives on (`Babai.case2b_defect`).  Sec. 15 needs it
on `Γ`, where `Babai.case2bFamily` reads the family.  This file does the second half of that
passage: from the two group facts

* `Babai.TransOnDiff` — `F^C_{(S)}` is transitive on `C ∖ S`, and
* `Babai.NotDoublyTransOnDiff` — it is not doubly transitive on `C ∖ S`,

to `1/2 ≤ defect` of every off-diagonal orbital, by Corollary 2.4.12
(`Babai.Digraph.defect_biregular_ge_half`) exactly as
`Babai.defect_extConstituent_ge_half` does.  The route is shorter than the one through the
orbital configuration, because *"nontrivial"* comes from the failure of double transitivity
directly rather than from the rank being at least `3`.

The first half — the two group facts themselves, which are
`Babai.isTransitive_pointwiseStab_individualize` and
`Babai.not_isDoublyTransitive_pointwiseStab_individualize` transported from the group
induced on `C` to points of `Γ` — is `Babai.case2b_facts_on`.
-/

universe u

namespace Babai

open MulAction Equiv

section Case2bDefect

variable {Γ : Type*} [Fintype Γ] [DecidableEq Γ]

/-! ### The two group facts, written on `Γ` -/

/-- §13.2, case (2b): **`F^C_{(S)}` is transitive on `C' = C ∖ S`**, written with points of
`Γ` instead of points of the double subtype `↥(Sᶜ : Set ↥C)`. -/
def TransOnDiff (H : Subgroup (Equiv.Perm Γ)) (C S : Set Γ) : Prop :=
  ∀ a ∈ C \ S, ∀ b ∈ C \ S, ∃ h ∈ pointwiseStabilizer H S, (h : Equiv.Perm Γ) a = b

/-- §13.2, case (2b): **`F^C_{(S)}` is not doubly transitive on `C' = C ∖ S`**, written with
points of `Γ`: there are two ordered pairs of distinct points of `C'` that no element of the
stabilizer carries onto one another. -/
def NotDoublyTransOnDiff (H : Subgroup (Equiv.Perm Γ)) (C S : Set Γ) : Prop :=
  ∃ a₁ ∈ C \ S, ∃ b₁ ∈ C \ S, ∃ a₂ ∈ C \ S, ∃ b₂ ∈ C \ S, a₁ ≠ b₁ ∧ a₂ ≠ b₂ ∧
    ∀ h ∈ pointwiseStabilizer H S,
      ¬ ((h : Equiv.Perm Γ) a₁ = a₂ ∧ (h : Equiv.Perm Γ) b₁ = b₂)

/-! ### `C ∖ S` is invariant, and the orbital is a union of `F^C_{(S)}`-orbits -/

/-- `C ∖ S` is invariant under the pointwise stabilizer of `S` inside `H`, for `C` an orbit
of `H`: an element of the stabilizer lies in `H`, so it preserves the orbit, and it fixes
`S` pointwise, so it preserves `S`. -/
theorem mem_diff_iff_of_pointwiseStab {H : Subgroup (Equiv.Perm Γ)} {γ : Γ} {S : Set Γ}
    {h : Equiv.Perm Γ} (hh : h ∈ pointwiseStabilizer H S) (u : Γ) :
    u ∈ (orbit H γ : Set Γ) \ S ↔ h u ∈ (orbit H γ : Set Γ) \ S := by
  obtain ⟨hH, hfix⟩ := mem_pointwiseStabilizer.1 hh
  have hC := (isInvariant_iff_mem H (orbit H γ : Set Γ)).1 (isInvariant_orbit H γ) h hH u
  have hS : u ∈ S ↔ h u ∈ S := by
    constructor
    · intro hu; rw [hfix u hu]; exact hu
    · intro hu
      have he : h u = u := h.injective (hfix (h u) hu)
      rw [← he]; exact hu
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨hC.1 h1, fun hc => h2 (hS.2 hc)⟩
  · rintro ⟨h1, h2⟩; exact ⟨hC.2 h1, fun hc => h2 (hS.1 hc)⟩

/-- The orbital of `F^C_{(S)}` through `(a, b)` is a union of orbits of the stabilizer on
pairs, so it is invariant under the stabilizer. -/
theorem orbitalOn_smul_iff (H : Subgroup (Equiv.Perm Γ)) (S : Set Γ) (a b : Γ)
    {h : Equiv.Perm Γ} (hh : h ∈ pointwiseStabilizer H S) (p q : Γ) :
    ((h p, h q) ∈ orbitalOn H S a b) ↔ ((p, q) ∈ orbitalOn H S a b) := by
  have hfwd : ∀ (k : Equiv.Perm Γ), k ∈ pointwiseStabilizer H S → ∀ p q : Γ,
      (p, q) ∈ orbitalOn H S a b → (k p, k q) ∈ orbitalOn H S a b := by
    rintro k hk p q ⟨g, hg, hgeq⟩
    refine ⟨k * g, (pointwiseStabilizer H S).mul_mem hk hg, ?_⟩
    have h1 : (g : Equiv.Perm Γ) a = p := congrArg Prod.fst hgeq
    have h2 : (g : Equiv.Perm Γ) b = q := congrArg Prod.snd hgeq
    show ((k * g) a, (k * g) b) = (k p, k q)
    simp [Equiv.Perm.mul_apply, h1, h2]
  constructor
  · intro hmem
    have := hfwd h⁻¹ ((pointwiseStabilizer H S).inv_mem hh) _ _ hmem
    simpa using this
  · exact hfwd h hh p q

/-- Moving the base pair of an orbital inside the stabilizer does not change the
orbital. -/
theorem orbitalOn_eq_of_stab (H : Subgroup (Equiv.Perm Γ)) (S : Set Γ) (a b : Γ)
    {h : Equiv.Perm Γ} (hh : h ∈ pointwiseStabilizer H S) :
    orbitalOn H S (h a) (h b) = orbitalOn H S a b := by
  ext q
  constructor
  · rintro ⟨g, hg, rfl⟩
    refine ⟨g * h, (pointwiseStabilizer H S).mul_mem hg hh, ?_⟩
    show ((g * h) a, (g * h) b) = ((g : Equiv.Perm Γ) (h a), (g : Equiv.Perm Γ) (h b))
    simp [Equiv.Perm.mul_apply]
  · rintro ⟨g, hg, rfl⟩
    refine ⟨g * h⁻¹, (pointwiseStabilizer H S).mul_mem hg
      ((pointwiseStabilizer H S).inv_mem hh), ?_⟩
    show ((g * h⁻¹) (h a), (g * h⁻¹) (h b)) = ((g : Equiv.Perm Γ) a, (g : Equiv.Perm Γ) b)
    simp [Equiv.Perm.mul_apply]

/-! ### The orbital digraph on `C ∖ S` -/

variable {H : Subgroup (Equiv.Perm Γ)} {γ : Γ} {S : Set Γ} {a b : Γ}

/-- §13.2, case (2b): the off-diagonal constituent `X_i` is an **irreflexive** digraph: a
loop in the orbital of `(a, b)` would make `a = b`. -/
theorem isIrreflexive_binDigraph_orbitalOn (hab : a ≠ b) :
    (binDigraph ((orbit H γ : Set Γ) \ S) (orbitalOn H S a b)).IsIrreflexive := by
  rw [Digraph.IsIrreflexive, IsIrreflexiveRel]
  ext p
  simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
  rintro ⟨g, hg, hgeq⟩ hdiag
  have h1 : (g : Equiv.Perm Γ) a = ((p.1 : ↥((orbit H γ : Set Γ) \ S)) : Γ) :=
    congrArg Prod.fst hgeq
  have h2 : (g : Equiv.Perm Γ) b = ((p.2 : ↥((orbit H γ : Set Γ) \ S)) : Γ) :=
    congrArg Prod.snd hgeq
  have hp : p.1 = p.2 := hdiag
  rw [hp] at h1
  exact hab (g.injective (h1.trans h2.symm))

/-- §13.2, case (2b): the off-diagonal constituent `X_i` is **biregular**: the stabilizer is
transitive on `C'` and carries the neighbourhood of one point onto that of another. -/
theorem isBiregular_binDigraph_orbitalOn [Nonempty ↥((orbit H γ : Set Γ) \ S)]
    (htr : TransOnDiff H (orbit H γ : Set Γ) S) :
    (binDigraph ((orbit H γ : Set Γ) \ S) (orbitalOn H S a b)).IsBiregular := by
  classical
  set C' : Set Γ := (orbit H γ : Set Γ) \ S with hC'
  set R : Set (Γ × Γ) := orbitalOn H S a b with hR
  set D : Digraph ↥C' := binDigraph C' R with hD
  -- the permutation of `↥C'` induced by an element of the stabilizer
  have hperm : ∀ {h : Equiv.Perm Γ}, h ∈ pointwiseStabilizer H S →
      ∃ e : Equiv.Perm ↥C', ∀ w : ↥C', ((e w : ↥C') : Γ) = h (w : Γ) := by
    intro h hh
    refine ⟨h.subtypePerm fun x => (mem_diff_iff_of_pointwiseStab hh x).symm, fun w => rfl⟩
  have hout : ∀ u v : ↥C', D.outDeg u = D.outDeg v := by
    intro u v
    obtain ⟨h, hh, hval⟩ := htr (u : Γ) u.2 (v : Γ) v.2
    obtain ⟨e, he⟩ := hperm hh
    have himg : outNbr D.E v = e '' outNbr D.E u := by
      ext z
      constructor
      · intro hz
        refine ⟨e.symm z, ?_, by simp⟩
        show (((u : ↥C') : Γ), ((e.symm z : ↥C') : Γ)) ∈ R
        have h1 : (((v : ↥C') : Γ), ((z : ↥C') : Γ)) ∈ R := hz
        have h2 : ((h ((u : ↥C') : Γ)), (h ((e.symm z : ↥C') : Γ))) ∈ R := by
          have hz' : ((e (e.symm z) : ↥C') : Γ) = h ((e.symm z : ↥C') : Γ) := he _
          rw [Equiv.apply_symm_apply] at hz'
          rw [hval, ← hz']
          exact h1
        exact (orbitalOn_smul_iff H S a b hh _ _).1 h2
      · rintro ⟨w, hw, rfl⟩
        show (((v : ↥C') : Γ), ((e w : ↥C') : Γ)) ∈ R
        have h1 : (((u : ↥C') : Γ), ((w : ↥C') : Γ)) ∈ R := hw
        have h2 := (orbitalOn_smul_iff H S a b hh ((u : ↥C') : Γ) ((w : ↥C') : Γ)).2 h1
        rw [hval, ← he w] at h2
        exact h2
    show (outNbr D.E u).ncard = (outNbr D.E v).ncard
    rw [himg, Set.ncard_image_of_injective _ e.injective]
  have hin : ∀ u v : ↥C', D.inDeg u = D.inDeg v := by
    intro u v
    obtain ⟨h, hh, hval⟩ := htr (u : Γ) u.2 (v : Γ) v.2
    obtain ⟨e, he⟩ := hperm hh
    have himg : inNbr D.E v = e '' inNbr D.E u := by
      ext z
      constructor
      · intro hz
        refine ⟨e.symm z, ?_, by simp⟩
        show (((e.symm z : ↥C') : Γ), ((u : ↥C') : Γ)) ∈ R
        have h1 : (((z : ↥C') : Γ), ((v : ↥C') : Γ)) ∈ R := hz
        have h2 : ((h ((e.symm z : ↥C') : Γ)), (h ((u : ↥C') : Γ))) ∈ R := by
          have hz' : ((e (e.symm z) : ↥C') : Γ) = h ((e.symm z : ↥C') : Γ) := he _
          rw [Equiv.apply_symm_apply] at hz'
          rw [hval, ← hz']
          exact h1
        exact (orbitalOn_smul_iff H S a b hh _ _).1 h2
      · rintro ⟨w, hw, rfl⟩
        show (((e w : ↥C') : Γ), ((v : ↥C') : Γ)) ∈ R
        have h1 : (((w : ↥C') : Γ), ((u : ↥C') : Γ)) ∈ R := hw
        have h2 := (orbitalOn_smul_iff H S a b hh ((w : ↥C') : Γ) ((u : ↥C') : Γ)).2 h1
        rw [hval, ← he w] at h2
        exact h2
    show (inNbr D.E u).ncard = (inNbr D.E v).ncard
    rw [himg, Set.ncard_image_of_injective _ e.injective]
  obtain ⟨u₀⟩ := ‹Nonempty ↥C'›
  exact ⟨⟨_, fun u => hout u u₀⟩, ⟨_, fun u => hin u u₀⟩⟩

/-- §13.2, case (2b): the off-diagonal constituent `X_i` is a **nontrivial** digraph.

The four trivial digraphs are ruled out one by one: the orbital is non-empty because it
contains `(a, b)`; it is not the diagonal and has no loop because `a ≠ b`; and it is not the
whole off-diagonal because the stabilizer is not doubly transitive — if it were the whole
off-diagonal then the two pairs `NotDoublyTransOnDiff` produces would lie in one orbit of
the stabilizer, hence in the same orbit as one another. -/
theorem not_isTrivial_binDigraph_orbitalOn (ha : a ∈ (orbit H γ : Set Γ) \ S)
    (hb : b ∈ (orbit H γ : Set Γ) \ S) (hab : a ≠ b)
    (h2 : NotDoublyTransOnDiff H (orbit H γ : Set Γ) S) :
    ¬ (binDigraph ((orbit H γ : Set Γ) \ S) (orbitalOn H S a b)).IsTrivial := by
  classical
  set C' : Set Γ := (orbit H γ : Set Γ) \ S with hC'
  set R : Set (Γ × Γ) := orbitalOn H S a b with hR
  have hmem : ((⟨a, ha⟩ : ↥C'), (⟨b, hb⟩ : ↥C')) ∈ (binDigraph C' R).E :=
    ⟨1, (pointwiseStabilizer H S).one_mem, rfl⟩
  have hne : (⟨a, ha⟩ : ↥C') ≠ ⟨b, hb⟩ := fun hc => hab (congrArg Subtype.val hc)
  intro htriv
  rcases (Digraph.isTrivial_iff (binDigraph C' R)).1 htriv with h | h | h | h
  · rw [h] at hmem; exact hmem
  · rw [h] at hmem; exact hne hmem
  · -- the complete reflexive digraph has a loop, which the orbital does not
    have hloop : ((⟨a, ha⟩ : ↥C'), (⟨a, ha⟩ : ↥C')) ∈ (binDigraph C' R).E := by
      rw [h]; trivial
    have hirr := isIrreflexive_binDigraph_orbitalOn (H := H) (γ := γ) (S := S) hab
    rw [Digraph.IsIrreflexive, IsIrreflexiveRel] at hirr
    exact Set.eq_empty_iff_forall_notMem.1 hirr _ ⟨hloop, rfl⟩
  · -- the whole off-diagonal would make the stabilizer doubly transitive
    obtain ⟨a₁, ha₁, b₁, hb₁, a₂, ha₂, b₂, hb₂, hab₁, hab₂, hnd⟩ := h2
    have hE : ∀ (u v : ↥C'), (u : Γ) ≠ (v : Γ) → ((u, v) ∈ (binDigraph C' R).E) := by
      intro u v huv
      rw [h]
      exact ⟨trivial, fun hc => huv (congrArg Subtype.val hc)⟩
    obtain ⟨g₁, hg₁, hg₁eq⟩ := hE ⟨a₁, ha₁⟩ ⟨b₁, hb₁⟩ hab₁
    obtain ⟨g₂, hg₂, hg₂eq⟩ := hE ⟨a₂, ha₂⟩ ⟨b₂, hb₂⟩ hab₂
    have h1a : (g₁ : Equiv.Perm Γ) a = a₁ := congrArg Prod.fst hg₁eq
    have h1b : (g₁ : Equiv.Perm Γ) b = b₁ := congrArg Prod.snd hg₁eq
    have h2a : (g₂ : Equiv.Perm Γ) a = a₂ := congrArg Prod.fst hg₂eq
    have h2b : (g₂ : Equiv.Perm Γ) b = b₂ := congrArg Prod.snd hg₂eq
    refine hnd (g₂ * g₁⁻¹) ((pointwiseStabilizer H S).mul_mem hg₂
      ((pointwiseStabilizer H S).inv_mem hg₁)) ⟨?_, ?_⟩
    · show (g₂ * g₁⁻¹) a₁ = a₂
      rw [← h1a]
      simp [Equiv.Perm.mul_apply, h2a]
    · show (g₂ * g₁⁻¹) b₁ = b₂
      rw [← h1b]
      simp [Equiv.Perm.mul_apply, h2b]

/-- §13.2, case (2b), **Cor. 2.4.12**: every off-diagonal constituent of the orbital
configuration of `F^C_{(S)}` on `C' = C ∖ S` has relative symmetry defect `≥ 1/2`.

This is `Babai.defect_extConstituent_ge_half` for the orbital through a given off-diagonal
pair, read on `Γ`. -/
theorem half_le_defect_binDigraph_orbitalOn
    [Fintype ↥((orbit H γ : Set Γ) \ S)] [DecidableEq ↥((orbit H γ : Set Γ) \ S)]
    (ha : a ∈ (orbit H γ : Set Γ) \ S)
    (hb : b ∈ (orbit H γ : Set Γ) \ S) (hab : a ≠ b)
    (htr : TransOnDiff H (orbit H γ : Set Γ) S)
    (h2 : NotDoublyTransOnDiff H (orbit H γ : Set Γ) S) :
    1 / 2 ≤ defect (Digraph.Aut
      (binDigraph ((orbit H γ : Set Γ) \ S) (orbitalOn H S a b))) := by
  haveI : Nonempty ↥((orbit H γ : Set Γ) \ S) := ⟨⟨a, ha⟩⟩
  exact Digraph.defect_biregular_ge_half
    (not_isTrivial_binDigraph_orbitalOn ha hb hab h2)
    (isIrreflexive_binDigraph_orbitalOn hab)
    (isBiregular_binDigraph_orbitalOn htr)

/-- §13.2, case (2b): the same as a statement about the binary relational structure
`Babai.binStruct`, which is what Theorem 9.2.3 takes as input. -/
theorem half_le_structDefect_binStruct_orbitalOn
    [Fintype ↥((orbit H γ : Set Γ) \ S)] [DecidableEq ↥((orbit H γ : Set Γ) \ S)]
    (ha : a ∈ (orbit H γ : Set Γ) \ S) (hb : b ∈ (orbit H γ : Set Γ) \ S) (hab : a ≠ b)
    (htr : TransOnDiff H (orbit H γ : Set Γ) S)
    (h2 : NotDoublyTransOnDiff H (orbit H γ : Set Γ) S) :
    1 / 2 ≤ structDefect (binStruct ((orbit H γ : Set Γ) \ S) (orbitalOn H S a b)) := by
  rw [structDefect_binStruct]
  exact half_le_defect_binDigraph_orbitalOn ha hb hab htr h2

/-! ### The two group facts themselves -/

section Transport

open scoped Classical

variable {H : Subgroup (Equiv.Perm Γ)}

/-- Reading an element of `F^C_{(S)}` (the pointwise stabilizer inside the induced group
`F^C`) back as an element of `F_{(S)}` on `Γ`.  Here `S ⊆ C`, and `S` is read on `↥C` as
`Subtype.val ⁻¹' S`. -/
theorem exists_mem_pointwiseStabilizer_of_restrict {C : Set Γ} (hinv : IsInvariant H C)
    {S : Set Γ} (hSC : S ⊆ C) {g : Equiv.Perm ↥C}
    (hg : g ∈ pointwiseStabilizer (restrictTo H C hinv) (Subtype.val ⁻¹' S)) :
    ∃ h ∈ pointwiseStabilizer H S, ∀ c : ↥C, ((g c : ↥C) : Γ) = (h : Equiv.Perm Γ) (c : Γ) := by
  obtain ⟨hgK, hgfix⟩ := hg
  obtain ⟨⟨h, hH⟩, hgh⟩ := hgK
  have hval : ∀ c : ↥C, ((g c : ↥C) : Γ) = h (c : Γ) := by
    intro c
    rw [← hgh]
    rfl
  refine ⟨h, ⟨hH, fun s hs => ?_⟩, hval⟩
  have hmem : (⟨s, hSC hs⟩ : ↥C) ∈ (Subtype.val ⁻¹' S : Set ↥C) := hs
  have hfx : ((g ⟨s, hSC hs⟩ : ↥C) : Γ) = s := congrArg Subtype.val (hgfix _ hmem)
  rw [hval ⟨s, hSC hs⟩] at hfx
  exact hfx

/-- The converse direction: an element of `F_{(S)}` on `Γ` restricts to an element of
`F^C_{(S)}`. -/
theorem exists_mem_pointwiseStabilizer_restrict {C : Set Γ} (hinv : IsInvariant H C)
    {S : Set Γ} {h : Equiv.Perm Γ} (hh : h ∈ pointwiseStabilizer H S) :
    ∃ g ∈ pointwiseStabilizer (restrictTo H C hinv) (Subtype.val ⁻¹' S),
      ∀ c : ↥C, ((g c : ↥C) : Γ) = h (c : Γ) := by
  obtain ⟨hH, hfix⟩ := hh
  refine ⟨restrictHom H C hinv ⟨h, hH⟩, ⟨⟨⟨h, hH⟩, rfl⟩, fun c hc => ?_⟩, fun c => rfl⟩
  exact Subtype.ext (hfix (c : Γ) hc)

/-- §13.2, **case (2b): the group facts of the individualization, read on `Γ`.**

`Babai.theorem_13_2_1` and `Babai.case2b_defect` state these on the double subtype
`↥(Sᶜ : Set ↥C)` that `Babai.indivGroup` lives on:

* `1 ≤ d ≤ 5` for `d` the degree of transitivity of `F^C`
  (`Babai.degtrans_restrict_le_five`, with `d ≥ 1` from the transitivity of `F^C` on the
  orbit `C`);
* `F^C_{(S)}` is transitive on `C' = C ∖ S`
  (`Babai.isTransitive_pointwiseStab_individualize`) and not doubly transitive on it
  (`Babai.not_isDoublyTransitive_pointwiseStab_individualize`), for every `S ⊆ C` with
  `|S| = d − 1`.

Here they are written with points of `Γ`, which is where `Babai.case2bFamily` reads the
family, so that a conjugation of `F^Γ` moves everything by a computation.  The transport is
along `Babai.degtransOn_eq_degtrans` and the two lemmas just above, which read
`F^C_{(S)}` on `Γ` instead of on `↥(Sᶜ : Set ↥C)`. -/
theorem case2b_facts_on (H : Subgroup (Equiv.Perm Γ)) (γ : Γ)
    (hgiant : ¬ alternatingGroup ((orbit H γ : Set Γ)) ≤
      restrictTo H _ (isInvariant_orbit H γ))
    (hcard : 6 ≤ (orbit H γ : Set Γ).ncard) :
    1 ≤ degtransOn H (orbit H γ : Set Γ) ∧ degtransOn H (orbit H γ : Set Γ) ≤ 5 ∧
      ∀ S ⊆ (orbit H γ : Set Γ), S.ncard = degtransOn H (orbit H γ : Set Γ) - 1 →
        TransOnDiff H (orbit H γ : Set Γ) S ∧
          NotDoublyTransOnDiff H (orbit H γ : Set Γ) S := by
  set C : Set Γ := (orbit H γ : Set Γ) with hC
  have hinv : IsInvariant H C := isInvariant_orbit H γ
  set K : Subgroup (Equiv.Perm ↥C) := restrictTo H C hinv with hK
  have hdeg : degtransOn H C = degtrans K := degtransOn_eq_degtrans H hinv
  have hd1 : 1 ≤ degtransOn H C := one_le_degtransOn_orbit H γ
  have hd5 : degtransOn H C ≤ 5 := by
    rw [hdeg]; exact degtrans_restrict_le_five (H := H) hinv hgiant
  have hcardC : Fintype.card ↥C = C.ncard := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
  have hcardK : degtransOn H C + 1 ≤ Fintype.card ↥C := by rw [hcardC]; omega
  have hspec := degtrans_spec K
  have hdtr : IsMultiplyTransitive K (degtransOn H C) := by rw [hdeg]; exact hspec.1
  have hnd : ¬ IsMultiplyTransitive K (degtransOn H C + 1) := by rw [hdeg]; exact hspec.2
  refine ⟨hd1, hd5, fun S hSC hScard => ?_⟩
  -- `S`, read on `↥C`
  set S' : Set ↥C := Subtype.val ⁻¹' S with hS'
  have himg : (Subtype.val '' S' : Set Γ) = S := by
    ext x
    constructor
    · rintro ⟨c, hc, rfl⟩; exact hc
    · intro hx; exact ⟨⟨x, hSC hx⟩, hx, rfl⟩
  have hS'card : S'.ncard = degtransOn H C - 1 := by
    have := Set.ncard_image_of_injective S' (Subtype.val_injective (p := fun x => x ∈ C))
    rw [himg] at this
    rw [← this, hScard]
  -- a point of `C ∖ S` is a point of `↥C` outside `S'`
  have hnotS' : ∀ {a : Γ} (ha : a ∈ C \ S), (⟨a, ha.1⟩ : ↥C) ∉ S' := fun ha hc => ha.2 hc
  constructor
  · intro a ha b hb
    obtain ⟨g, hgS, hgab⟩ :=
      isTransitive_pointwiseStab_individualize K hdtr hd1 hS'card (hnotS' ha) (hnotS' hb)
    obtain ⟨h, hhS, hhval⟩ := exists_mem_pointwiseStabilizer_of_restrict hinv hSC hgS
    refine ⟨h, hhS, ?_⟩
    have hfx : ((g ⟨a, ha.1⟩ : ↥C) : Γ) = b := congrArg Subtype.val hgab
    rw [hhval ⟨a, ha.1⟩] at hfx
    exact hfx
  · -- the failure of double transitivity, read on `Γ`
    by_contra hcon
    refine not_isDoublyTransitive_pointwiseStab_individualize K hnd hdtr hd1 hS'card hcardK ?_
    intro u v u' v' hu hv hu' hv' huv huv'
    have hmem : ∀ {w : ↥C}, w ∉ S' → ((w : Γ) ∈ C \ S) := fun {w} hw => ⟨w.2, hw⟩
    -- `hcon` says: for these four points of `C ∖ S` some element of `F_{(S)}` works
    have hex : ∃ h ∈ pointwiseStabilizer H S,
        (h : Equiv.Perm Γ) (u : Γ) = (u' : Γ) ∧ (h : Equiv.Perm Γ) (v : Γ) = (v' : Γ) := by
      by_contra hno
      exact hcon ⟨(u : Γ), hmem hu, (v : Γ), hmem hv, (u' : Γ), hmem hu', (v' : Γ), hmem hv',
        fun hc => huv (Subtype.ext hc), fun hc => huv' (Subtype.ext hc),
        fun h hh hc => hno ⟨h, hh, hc⟩⟩
    obtain ⟨h, hhS, hu1, hv1⟩ := hex
    obtain ⟨g, hgS, hgval⟩ := exists_mem_pointwiseStabilizer_restrict (C := C) hinv hhS
    exact ⟨g, hgS, Subtype.ext (by rw [hgval u, hu1]), Subtype.ext (by rw [hgval v, hv1])⟩

end Transport

end Case2bDefect

end Babai
