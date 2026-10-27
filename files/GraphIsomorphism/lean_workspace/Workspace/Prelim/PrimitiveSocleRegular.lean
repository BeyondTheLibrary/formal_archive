/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Background permutation group theory used by the proof of Lemma 10.2.5 (§10.2): normal
subgroups of a primitive group, semiregularity of centralizers, regularity of abelian
normal subgroups.
-/
import Workspace.Prelim.PermGroups
import Workspace.Prelim.SocleStructure

/-!
# Normal subgroups of a primitive group

The proof of Lemma 10.2.5 uses, without citation, parts of the O'Nan–Scott analysis of a
primitive group in terms of its socle, which is Dixon–Mortimer, *Permutation Groups*,
GTM 163, Springer 1996, **Theorem 4.3B**, pp. 114–115.  The paper cites nothing for it, so
it is proved, not axiomatized.  This file has the elementary permutation-group half:

* `Babai.IsPrimitive.nontrivial_dom`: a primitive group acts on at least two points;
* `Babai.isPretransitive_of_normal_of_isPrimitive`: a nontrivial normal subgroup of a
  primitive group is transitive (Wielandt; in Mathlib as `IsQuasiPreprimitive`);
* `Babai.eq_one_of_centralizes_of_fixed`: an element centralizing a transitive subgroup
  and fixing a point is the identity — "the centralizer of a transitive group is
  semiregular";
* `Babai.card_centralizer_le`: hence the centralizer of a transitive subgroup has order at
  most `n`;
* `Babai.card_eq_of_abelian_of_isPretransitive`: an abelian transitive subgroup is
  regular, so it has order exactly `n` (Dixon–Mortimer 4.3B (i), first clause);
* `Babai.eq_of_isMinimalNormal_of_abelian`: in the affine case the abelian socle is the
  *unique* minimal normal subgroup (Dixon–Mortimer 4.3B (i), `Soc(G) = K = C_G(K)`).

Throughout, `G : Subgroup (Equiv.Perm Ω)` and the subgroups in question are subgroups
`M : Subgroup ↥G` of `G` itself (that is how `Babai.socle G` is stated), acting on `Ω`
through the ambient action of `↥G`.
-/

namespace Babai

open MulAction Equiv Equiv.Perm

variable {Ω : Type*} {G : Subgroup (Equiv.Perm Ω)}

/-! ### A primitive group acts on at least two points -/

/-- A primitive group (`|G| ≥ 2`) acts on a set with at least two elements: on a
subsingleton `Ω` the group `S(Ω)` is trivial. -/
theorem IsPrimitive.nontrivial_dom (hG : IsPrimitive G) : Nontrivial Ω := by
  rcases subsingleton_or_nontrivial Ω with hΩ | hΩ
  · exfalso
    have hsub : Subsingleton G :=
      ⟨fun a b => Subtype.ext (Equiv.ext fun x => Subsingleton.elim _ _)⟩
    have : Nat.card G = 1 := Nat.card_eq_one_iff_unique.2 ⟨hsub, ⟨1⟩⟩
    have := hG.1
    omega
  · exact hΩ

theorem IsPrimitive.nonempty_dom (hG : IsPrimitive G) : Nonempty Ω :=
  have := hG.nontrivial_dom
  inferInstance

/-! ### A nontrivial normal subgroup of a primitive group is transitive -/

/-- Wielandt: in a primitive group every nontrivial normal subgroup is transitive.  This
is the step "`N` is regular, i.e. `n = |N|`" of the proof of Lemma 10.2.5 (Case 1) and the
step "`M` is regular" of Case 2a; it is Dixon–Mortimer, *Permutation Groups*, GTM 163,
Theorem 4.3B, p. 114 (via Theorem 4.3A / Wielandt Thm. 7.1).  Mathlib proves it as
`MulAction.IsPreprimitive.isQuasiPreprimitive`. -/
theorem isPretransitive_of_normal_of_isPrimitive [Finite Ω] (hG : IsPrimitive G)
    (M : Subgroup ↥G) [M.Normal] (hM : M ≠ ⊥) : IsPretransitive ↥M Ω := by
  haveI := hG.nontrivial_dom
  haveI : IsPreprimitive ↥G Ω := (isPrimitive_iff_isPreprimitive G).1 hG
  refine IsQuasiPreprimitive.isPretransitive_of_normal (N := M) ?_
  -- `M` has a nonidentity element, which moves a point
  obtain ⟨m, hm, hm1⟩ : ∃ m, m ∈ M ∧ m ≠ 1 := by
    by_contra hcon
    push_neg at hcon
    exact hM (eq_bot_iff.2 fun z hz => Subgroup.mem_bot.2 (hcon z hz))
  obtain ⟨x, hx⟩ : ∃ x : Ω, ((m : Equiv.Perm Ω)) x ≠ x := by
    by_contra hcon
    push_neg at hcon
    exact hm1 (Subtype.ext (Equiv.ext fun x => hcon x))
  intro hfix
  have : x ∈ fixedPoints ↥M Ω := by rw [hfix]; trivial
  exact hx (this ⟨m, hm⟩)

/-! ### The centralizer of a transitive group is semiregular -/

/-- An element of `S(Ω)` that centralizes a transitive subgroup `M` and fixes a point is
the identity.  ("The centralizer of a transitive group is semiregular.") -/
theorem eq_one_of_centralizes_of_fixed {M : Subgroup ↥G} (hM : IsPretransitive ↥M Ω)
    {c : ↥G} (hc : ∀ m ∈ M, c * m = m * c) {x : Ω} (hcx : (c : Equiv.Perm Ω) x = x) :
    c = 1 := by
  refine Subtype.ext (Equiv.ext fun y => ?_)
  obtain ⟨m, hm⟩ := hM.exists_smul_eq x y
  have hmy : ((m : ↥G) : Equiv.Perm Ω) x = y := hm
  have hcm := hc (m : ↥G) m.2
  have key := congrArg (fun g : ↥G => ((g : Equiv.Perm Ω)) x) hcm
  simp only [Subgroup.coe_mul, Equiv.Perm.mul_apply] at key
  rw [hmy, hcx, hmy] at key
  simpa using key

/-- The centralizer of a transitive subgroup has order at most `n = |Ω|`. -/
theorem card_centralizer_le [Finite Ω] {M : Subgroup ↥G} (hM : IsPretransitive ↥M Ω)
    (x : Ω) :
    Nat.card (Subgroup.centralizer (M : Set ↥G)) ≤ Nat.card Ω := by
  set C := Subgroup.centralizer ((M : Set ↥G)) with hC
  have hstab : stabilizer ↥C x = ⊥ := by
    rw [eq_bot_iff]
    intro c hc
    have hc' : ∀ m ∈ M, (c : ↥G) * m = m * (c : ↥G) := by
      intro m hm
      exact ((Subgroup.mem_centralizer_iff.1 c.2) m hm).symm
    have hcx : ((c : ↥G) : Equiv.Perm Ω) x = x := hc
    exact Subgroup.mem_bot.2 (Subtype.ext (eq_one_of_centralizes_of_fixed hM hc' hcx))
  have hidx : (stabilizer ↥C x).index = Nat.card ↥C := by
    rw [hstab, Subgroup.index_bot]
  have horb : Nat.card (orbit ↥C x) = (stabilizer ↥C x).index :=
    Nat.card_congr (orbitEquivQuotientStabilizer _ x)
  have hle : Nat.card (orbit ↥C x) ≤ Nat.card Ω :=
    Nat.card_le_card_of_injective _ Subtype.val_injective
  rw [horb, hidx] at hle
  exact hle

/-! ### An abelian transitive group is regular -/

/-- An abelian transitive permutation group is regular: its order is `n`.  This is the
step "`N` is abelian … and therefore regular, i.e. `n = |N|`" of the proof of Lemma 10.2.5
(Case 1); Dixon–Mortimer, GTM 163, Theorem 4.3B (i), p. 114. -/
theorem card_eq_of_abelian_of_isPretransitive [Finite Ω] {M : Subgroup ↥G}
    (hM : IsPretransitive ↥M Ω) (habel : ∀ a b : ↥M, a * b = b * a) (x : Ω) :
    Nat.card ↥M = Nat.card Ω := by
  have hstab : stabilizer ↥M x = ⊥ := by
    rw [eq_bot_iff]
    intro m hm
    have hc : ∀ m' ∈ M, (m : ↥G) * m' = m' * (m : ↥G) := by
      intro m' hm'
      have := habel m ⟨m', hm'⟩
      exact congrArg Subtype.val this
    have hmx : ((m : ↥G) : Equiv.Perm Ω) x = x := hm
    exact Subgroup.mem_bot.2 (Subtype.ext (eq_one_of_centralizes_of_fixed hM hc hmx))
  have horb : Nat.card (orbit ↥M x) = (stabilizer ↥M x).index :=
    Nat.card_congr (orbitEquivQuotientStabilizer _ x)
  rw [hstab, Subgroup.index_bot] at horb
  have huniv : orbit ↥M x = Set.univ := by
    ext y
    exact ⟨fun _ => trivial, fun _ => (hM.exists_smul_eq x y).imp fun _ h => h⟩
  have hcard : Nat.card (orbit ↥M x) = Nat.card Ω := by
    rw [Nat.card_coe_set_eq, huniv, Set.ncard_univ]
  rw [← horb]
  exact hcard

end Babai
