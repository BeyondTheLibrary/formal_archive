/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 15, lines 5, 6, 7: the four outcomes of AggregateCertificates (Theorem 13.2.1) as
tests on the instance, and the branch of outcome (2a).
-/
import Workspace.Master.Case3
import Workspace.Master.Line4cdBranch
import Workspace.Master.StrongAggregateAlign

/-!
# Line 5 of Sec. 15: which outcome of Theorem 13.2.1, and the branch of outcome (2a)

> 5. else (: `G` imprimitive, i.e. `|Φ| ≤ (1/2)|Ω|` :)  apply AggregateCertificates
>    (Theorem 13.2.1)
> 6. if AggregateCertificates returns canonically embedded `k`-ary relational structure on
>    `Γ` with relative symmetry defect `≥ 1/2` then
> 6a.  apply Extended Design Lemma (Theorem 9.2.3); `X ←` canonical structure on `Γ`
>      returned
> 7. else (: AggregateCertificates returns canonical colored equipartition on `Γ` :)
>    `X ←` colored equipartition returned
> 7a. apply Procedure Align to `X` (Sec. 14.1)

Theorem 13.2.1 has **four** outcomes (`Babai.theorem_13_2_1`), and the test of line 6 sorts
them into two groups:

| outcome | what it is | line |
|---|---|---|
| (1) | a canonical colored `4/5`-partition of `Γ` | 7, then 7a |
| (2a) | the hypothesis of Cor. 12.0.10 on a canonical orbit `C`, `\|C\| > 4m/5` | *"reduce to `n^{O(1)}` instances of size `≤ 2n/3`"* — the same exit as line 4b |
| (2b) | a binary relational structure on a canonical `C' ⊆ Γ` of defect `≥ 1/2` | 6, then 6a, 7a |
| (3) | a `t`-ary relational structure on `D(x) ⊆ Γ` of defect `> 1/2` | 6, then 6a, 7a |

So `Babai.aggregatesToStructure` — the field `AggregatesToStructure` of
`Babai.Sec15Remaining` — is *"the case distinction of Theorem 13.2.1 lands in (2b) or
(3)"*, and its negation is *"it lands in (1) or (2a)"*.  Both are read off the same object
the theorem's own case distinction is read off, the group `F(x)^Γ` of §13.2
(`Babai.bigFGamma`), at the string of the window and with the test set size of §13.1
(`Babai.testSetSize`).

**Outcome (2a).**  Theorem 13.2.1's third alternative is *"reduce the determination of
`Iso_G(x,y)` to `n^{O(1)}` instances of size `≤ 2n/3`"*, and outcome (2a) reaches it in
exactly the way line 4b does: the canonical set `C` carries at least `A(C)` inside the
automorphism group of `x`, which is the hypothesis of Cor. 12.0.10.  So the branch is
`Babai.line4bBranch`, and the only work is to produce its data
(`Babai.SmallDefectData`) from the outcome: `Babai.nonempty_smallDefectData_case2a`.

The two-coloring the data needs is `Babai.bigOrbitColoring`: the color of `γ` is *"the
orbit of `γ` under `F(z)^Γ` has more than `4m/5` points"*.  It is canonical because
`F(z)^Γ` is (`Babai.canonical_bigFGamma`), and its class of the color `true` is exactly the
orbit `C` of outcome (2), because two orbits of more than `m/2` points cannot be disjoint.
-/

universe u v

namespace Babai

open MulAction Equiv Equiv.Perm

/-! ### Orbits of a conjugated group -/

section OrbitConj

variable {Γ : Type*}

/-- The orbits of `pHp⁻¹` are the `p`-images of the orbits of `H`. -/
theorem orbit_map_conj (H : Subgroup (Equiv.Perm Γ)) (p : Equiv.Perm Γ) (γ : Γ) :
    (orbit (H.map (MulAut.conj p).toMonoidHom) (p γ) : Set Γ) = p '' (orbit H γ : Set Γ) := by
  ext z
  constructor
  · rintro ⟨⟨b, hb⟩, rfl⟩
    obtain ⟨h, hh, rfl⟩ := hb
    refine ⟨(h : Equiv.Perm Γ) γ, ⟨⟨h, hh⟩, rfl⟩, ?_⟩
    show p (h γ) = (p * h * p⁻¹) (p γ)
    simp [Equiv.Perm.mul_apply]
  · rintro ⟨w, ⟨⟨h, hh⟩, rfl⟩, rfl⟩
    refine ⟨⟨p * h * p⁻¹, ⟨h, hh, rfl⟩⟩, ?_⟩
    show (p * (h : Equiv.Perm Γ) * p⁻¹) (p γ) = p ((h : Equiv.Perm Γ) γ)
    simp [Equiv.Perm.mul_apply]

/-- Two orbits of more than half of the points cannot be different. -/
theorem orbit_eq_of_two_large [Fintype Γ] {H : Subgroup (Equiv.Perm Γ)} {γ δ : Γ}
    (hγ : Fintype.card Γ < 2 * (orbit H γ : Set Γ).ncard)
    (hδ : Fintype.card Γ < 2 * (orbit H δ : Set Γ).ncard) :
    (orbit H γ : Set Γ) = (orbit H δ : Set Γ) := by
  classical
  by_contra hne
  have hdisj : Disjoint (orbit H γ : Set Γ) (orbit H δ : Set Γ) := by
    rw [Set.disjoint_left]
    intro z hzγ hzδ
    have e1 : (orbit H z : Set Γ) = (orbit H γ : Set Γ) := orbit_eq_iff.2 hzγ
    have e2 : (orbit H z : Set Γ) = (orbit H δ : Set Γ) := orbit_eq_iff.2 hzδ
    exact hne (e1.symm.trans e2)
  have hun : ((orbit H γ : Set Γ) ∪ (orbit H δ : Set Γ)).ncard
      = (orbit H γ : Set Γ).ncard + (orbit H δ : Set Γ).ncard :=
    Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _)
  have hle : ((orbit H γ : Set Γ) ∪ (orbit H δ : Set Γ)).ncard ≤ Fintype.card Γ := by
    have h := Set.ncard_le_ncard (Set.subset_univ
      ((orbit H γ : Set Γ) ∪ (orbit H δ : Set Γ))) (Set.toFinite _)
    rwa [Set.ncard_univ, Nat.card_eq_fintype_card] at h
  omega

end OrbitConj

/-! ### The canonical two-coloring of the big orbit -/

section BigOrbit

variable {Ω Γ Λ : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype Γ] [DecidableEq Γ]
  {G : Subgroup (Equiv.Perm Ω)}

open scoped Classical in
/-- §13.2, case (2): **the canonical two-coloring that marks the big orbit**.  The color of
`γ` is *"the orbit of `γ` under `F(z)^Γ` has more than `4m/5` points"*. -/
noncomputable def bigOrbitColoring (ϕ : G →* Equiv.Perm Γ) (t : ℕ) :
    (Ω → Λ) → Γ → Bool :=
  fun z γ => decide (4 * Fintype.card Γ < 5 * (orbit (bigFGamma ϕ z t) γ : Set Γ).ncard)

/-- The two-coloring of `Babai.bigOrbitColoring` is canonical: a `G`-shift of the string
shifts it by `σ^ϕ`.  This is canonicity of `F(z)^Γ` (`Babai.canonical_bigFGamma`). -/
theorem isCanonicalColoring_bigOrbitColoring (ϕ : G →* Equiv.Perm Γ) (t : ℕ) :
    IsCanonicalColoring (A := Λ) ϕ (bigOrbitColoring ϕ t) := by
  classical
  intro z σ γ
  have h1 : (orbit (bigFGamma ϕ (strAct z (σ : Equiv.Perm Ω)) t) ((ϕ σ : Equiv.Perm Γ) γ) :
      Set Γ) = (ϕ σ : Equiv.Perm Γ) '' (orbit (bigFGamma ϕ z t) γ : Set Γ) := by
    rw [canonical_bigFGamma ϕ z t σ]
    exact orbit_map_conj _ _ _
  have h2 : (orbit (bigFGamma ϕ (strAct z (σ : Equiv.Perm Ω)) t) ((ϕ σ : Equiv.Perm Γ) γ) :
      Set Γ).ncard = (orbit (bigFGamma ϕ z t) γ : Set Γ).ncard := by
    rw [h1]
    exact Set.ncard_image_of_injective _ (ϕ σ : Equiv.Perm Γ).injective
  show decide _ = decide _
  rw [h2]

open scoped Classical in
/-- The class of the color `true` is the set of points whose orbit is big. -/
theorem colorClass_bigOrbitColoring (ϕ : G →* Equiv.Perm Γ) (t : ℕ) (z : Ω → Λ) :
    colorClass (bigOrbitColoring ϕ t) z true
      = {γ : Γ | 4 * Fintype.card Γ < 5 * (orbit (bigFGamma ϕ z t) γ : Set Γ).ncard} := by
  ext γ
  simp [colorClass, bigOrbitColoring]

/-- §13.2, case (2): the class of the color `true` **is** the big orbit `C`.

*Proof.*  A point of the class has an orbit of more than `4m/5 > m/2` points, and so has
every point of `C`; two such orbits meet, hence are equal
(`Babai.orbit_eq_of_two_large`). -/
theorem colorClass_bigOrbitColoring_eq_orbit (ϕ : G →* Equiv.Perm Γ) (t : ℕ) (z : Ω → Λ)
    {γ₀ : Γ} (hbig : 4 * Fintype.card Γ < 5 * (orbit (bigFGamma ϕ z t) γ₀ : Set Γ).ncard) :
    colorClass (bigOrbitColoring ϕ t) z true = (orbit (bigFGamma ϕ z t) γ₀ : Set Γ) := by
  classical
  rw [colorClass_bigOrbitColoring]
  ext γ
  simp only [Set.mem_setOf_eq]
  constructor
  · intro hγ
    have h := orbit_eq_of_two_large (H := bigFGamma ϕ z t) (γ := γ) (δ := γ₀)
      (by omega) (by omega)
    rw [← h]
    exact mem_orbit_self γ
  · intro hγ
    have h : (orbit (bigFGamma ϕ z t) γ : Set Γ) = (orbit (bigFGamma ϕ z t) γ₀ : Set Γ) :=
      orbit_eq_iff.2 hγ
    rw [h]
    exact hbig

end BigOrbit

/-! ### Outcome (1): the colored `4/5`-partition is canonical -/

section Case1Canonical

open scoped Classical

variable {Γ : Type*} [Fintype Γ] [DecidableEq Γ]

/-- The fixed points of `pHp⁻¹` are the `p`-images of the fixed points of `H`. -/
theorem fixedSet_map_conj (H : Subgroup (Equiv.Perm Γ)) (p : Equiv.Perm Γ) :
    fixedSet (H.map (MulAut.conj p).toMonoidHom) = p '' fixedSet H := by
  ext γ
  constructor
  · intro hγ
    refine ⟨p⁻¹ γ, ?_, by simp⟩
    intro b hb
    have hmem : p * (b : Equiv.Perm Γ) * p⁻¹ ∈ H.map (MulAut.conj p).toMonoidHom :=
      ⟨b, hb, rfl⟩
    have h := hγ _ hmem
    have : p ((b : Equiv.Perm Γ) (p⁻¹ γ)) = γ := by
      simpa [Equiv.Perm.mul_apply] using h
    exact p.injective (by simpa using this)
  · rintro ⟨δ, hδ, rfl⟩
    intro b hb
    obtain ⟨h, hh, rfl⟩ := hb
    show (p * (h : Equiv.Perm Γ) * p⁻¹) (p δ) = p δ
    simp [Equiv.Perm.mul_apply, hδ (h : Equiv.Perm Γ) hh]

/-- §13.2, case (1): **the colored partition by the orbits is canonical**, on colors.  A
conjugation of the group moves the coloring by the same permutation. -/
theorem color_orbitPartition_map_conj (H : Subgroup (Equiv.Perm Γ)) (p : Equiv.Perm Γ)
    (γ : Γ) :
    (orbitPartition (H.map (MulAut.conj p).toMonoidHom)).color (p γ)
      = (orbitPartition H).color γ := by
  show decide _ = decide _
  have hiff : p γ ∈ fixedSet (H.map (MulAut.conj p).toMonoidHom) ↔ γ ∈ fixedSet H := by
    rw [fixedSet_map_conj H p]
    exact ⟨fun ⟨δ, hδ, he⟩ => p.injective he ▸ hδ, fun h => ⟨γ, h, rfl⟩⟩
  simp only [decide_eq_decide]
  exact hiff

/-- §13.2, case (1): **the colored partition by the orbits is canonical**, on blocks. -/
theorem part_orbitPartition_map_conj (H : Subgroup (Equiv.Perm Γ)) (p : Equiv.Perm Γ)
    (a b : Γ) :
    (orbitPartition (H.map (MulAut.conj p).toMonoidHom)).part (p a) (p b)
      ↔ (orbitPartition H).part a b := by
  have hfix : ∀ γ : Γ, p γ ∈ fixedSet (H.map (MulAut.conj p).toMonoidHom) ↔
      γ ∈ fixedSet H := by
    intro γ
    rw [fixedSet_map_conj H p]
    exact ⟨fun ⟨δ, hδ, he⟩ => p.injective he ▸ hδ, fun h => ⟨γ, h, rfl⟩⟩
  have horb : p b ∈ (orbit (H.map (MulAut.conj p).toMonoidHom) (p a) : Set Γ) ↔
      b ∈ (orbit H a : Set Γ) := by
    rw [orbit_map_conj H p a]
    exact ⟨fun ⟨δ, hδ, he⟩ => p.injective he ▸ hδ, fun h => ⟨b, h, rfl⟩⟩
  show ((p a ∈ fixedSet _ ∧ p b ∈ fixedSet _) ∨ p b ∈ (orbit _ (p a) : Set Γ)) ↔
    ((a ∈ fixedSet H ∧ b ∈ fixedSet H) ∨ b ∈ (orbit H a : Set Γ))
  rw [hfix a, hfix b, horb]

end Case1Canonical

/-! ### The four outcomes of Theorem 13.2.1 as tests -/

section Outcomes

open scoped Classical

variable {Ω Γ Λ : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype Γ] [DecidableEq Γ]
  {G : Subgroup (Equiv.Perm Ω)}

/-- §13.2, **outcome (2a)**: *"if `F^C ≥ A(C)` then apply Cor. 12.0.10"* — `F(x)^Γ` has an
orbit `C` of more than `4m/5` points on which it induces at least the alternating group. -/
def AggregateCase2a (ϕ : G →* Equiv.Perm Γ) (x : Ω → Λ) (t : ℕ) : Prop :=
  ∃ γ : Γ, 4 * Fintype.card Γ < 5 * (orbit (bigFGamma ϕ x t) γ : Set Γ).ncard ∧
    alternatingGroup ((orbit (bigFGamma ϕ x t) γ : Set Γ)) ≤
      restrictTo (bigFGamma ϕ x t) _ (isInvariant_orbit (bigFGamma ϕ x t) γ)

/-- §15, **line 6, the test**: *"if AggregateCertificates returns canonically embedded
`k`-ary relational structure on `Γ` with relative symmetry defect `≥ 1/2`"*.

Theorem 13.2.1 returns such a structure in outcomes (2b) and (3), and a colored partition
or a Cor. 12.0.10 reduction in outcomes (1) and (2a), so the test is the negation of the
first two cases of the theorem's own case distinction
(`Babai.theorem_13_2_1_cases`): *"not case (1), and if case (2) then not (2a)"*. -/
def AggregatesToStructureOn (ϕ : G →* Equiv.Perm Γ) (x : Ω → Λ) (t : ℕ) : Prop :=
  ¬ Case1 (bigFGamma ϕ x t) ∧ ¬ AggregateCase2a ϕ x t

/-- §15, lines 6 and 7: the test of line 6 **fails** exactly when the outcome is the
colored `4/5`-partition of case (1) or the Cor. 12.0.10 reduction of case (2a). -/
theorem not_aggregatesToStructureOn_iff (ϕ : G →* Equiv.Perm Γ) (x : Ω → Λ) (t : ℕ) :
    ¬ AggregatesToStructureOn ϕ x t ↔ Case1 (bigFGamma ϕ x t) ∨ AggregateCase2a ϕ x t := by
  classical
  rw [AggregatesToStructureOn, not_and_or, not_not, not_not]

end Outcomes

/-! ### The data of one round of lines 5–7 on the window

Lines 5–7 used to choose a `Babai.Line4cdCore`, whose `red` field was free: `.done ∅` and
`.done (Iso_G(x,y))` filled every field at cost `0`.  `Babai.Line57Shape` is the repair, the
companion of `Babai.AlignShape` for lines 5–7: the round is one of three named things, and
the two that answer `∅` without a call carry the test that justifies the answer.  See
the corrected paper entry on Finding 1 of the audit of Secs. 14–15. -/

section Line57Shape

variable {W : Type u} {A : Type v} [Fintype W] [DecidableEq W]

/-- §13.2, case (3), with the Local guide proposition of the original (the corrected paper,
entries 56 and 121): **some class of `y` meets no tuple of `x`.** The inputs are
`X_false = x` and `X_true = y`, and `∼` is the equivalence of the local guide
`Babai.localGuideData` over both inputs. The condition says that some ordered `t`-tuple of
`D(y)` is `∼` to no ordered `t`-tuple of `D(x)`, that is, some class `Q ∈ Ξ` has
`Q_1 = ∅ ≠ Q_2`. -/
def GuideClassMissing {G : Subgroup (Equiv.Perm W)} {m : ℕ} (ϕ : G →* Equiv.Perm (Fin m))
    (ts : ℕ) (x y : W → A) (hset : LocalCertSetting G ϕ) (ht : LargeK ts (Nat.card W))
    (htm : 10 * ts ≤ Nat.card (Fin m)) (hW : Nonempty W) : Prop :=
  ∃ v : Fin ts ↪ ↥(fixedGamma ϕ y ts), ∀ u : Fin ts ↪ ↥(fixedGamma ϕ x ts),
    (localGuideData ϕ ts (fun b : Bool => cond b y x) hset ht htm).mkClass ⟨false, u⟩ ≠
      (localGuideData ϕ ts (fun b : Bool => cond b y x) hset ht htm).mkClass ⟨true, v⟩

/-- §13.2, case (3): **the missing class is an invariant that differs for the two inputs**,
so `Iso_G(x,y) = ∅`. A `G`-isomorphism `σ : x → y` induces a morphism `f : D(x) → D(y)` of
the category `C` (`Babai.exists_mem_guideMorC`), and `f` carries every tuple of `D(x)` to a
tuple of `D(y)` in the same class (`Babai.LocalGuideData.mkClass_comp`). Applied to
`f⁻¹ ∘ v`, this puts `v` in the class of a tuple of `D(x)`. -/
theorem strIso_eq_empty_of_guideClassMissing {G : Subgroup (Equiv.Perm W)} {m : ℕ}
    {ϕ : G →* Equiv.Perm (Fin m)} {ts : ℕ} {x y : W → A} {hset : LocalCertSetting G ϕ}
    {ht : LargeK ts (Nat.card W)} {htm : 10 * ts ≤ Nat.card (Fin m)} {hW : Nonempty W}
    (h : GuideClassMissing ϕ ts x y hset ht htm hW) :
    strIso (G : Set (Equiv.Perm W)) x y = ∅ := by
  obtain ⟨v, hv⟩ := h
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro σ hσ
  obtain ⟨f, hf, _⟩ := exists_mem_guideMorC ϕ ts (fun b : Bool => cond b y x) false true
    ⟨σ, hσ.1⟩ hσ.2
  let u : Fin ts ↪ ↥(fixedGamma ϕ x ts) := v.trans f.symm.toEmbedding
  have he : u.trans f.toEmbedding = v :=
    Function.Embedding.ext (fun i => f.apply_symm_apply (v i))
  have hc := (localGuideData ϕ ts (fun b : Bool => cond b y x) hset ht htm).mkClass_comp hf u
  exact hv u (hc.symm.trans (congrArg (fun w : Fin ts ↪ ↥(fixedGamma ϕ y ts) =>
    (localGuideData ϕ ts (fun b : Bool => cond b y x) hset ht htm).mkClass ⟨true, w⟩) he))

/-- §15, lines 5–7 on the window: **the data the round after AggregateCertificates runs
on**.

* `align S` is the round of Procedure Align on the data `S` (`Babai.AlignShape`).  It is
  what outcomes (1), (2b) and (3) of Theorem 13.2.1 lead to: the canonical versions of the
  structure, then lines 1–11 of Sec. 14.1.
* `rejectDefect ϕ ts h` is the exit of outcome (3) at the second string: the set `D(z)` of
  fixed points of `F(z)^Γ` is a canonical invariant of the string, so `|D(y)| ≠ |D(x)|`
  means `Iso_G(x,y) = ∅` (`Babai.strIso_eq_empty_of_ncard_fixedGamma_ne`).
* `rejectCase ϕ ts hx hy` is the exit of outcome (2b) at the second string: the case test of
  Theorem 13.2.1 is canonical too (`Babai.case2b_test_strAct`), so a string that fails it
  while `x` passes it is not `G`-isomorphic to `x`.
* `rejectGuide hset ht htm hW h` is the exit of the local guide in outcome (3): some class
  of `∼` meets `y` and not `x` (`Babai.GuideClassMissing`), an invariant that differs for the
  two inputs, so `Iso_G(x,y) = ∅` (`Babai.strIso_eq_empty_of_guideClassMissing`). Version 2.5
  has no exit here; the original's proof of the Local guide proposition does
.

The two reject constructors **carry their test**, so the answer `∅` cannot be given where
the test does not hold.  Both tests read the second string alone against the first, and are
computed from `F(z)^Γ`, which the aggregation of line 5 has already produced. -/
inductive Line57Shape (W : Type u) [Fintype W] [DecidableEq W] (A : Type v)
    (G : Subgroup (Equiv.Perm W)) (x y : W → A) {m : ℕ} (ϕ : G →* Equiv.Perm (Fin m))
    (ts : ℕ) where
  /-- Outcomes (1), (2b) and (3): one round of Procedure Align. -/
  | align (S : AlignShape W A G x y)
  /-- Outcome (3) at the second string: `|D(y)| ≠ |D(x)|`. -/
  | rejectDefect (hne : (fixedGamma ϕ y ts).ncard ≠ (fixedGamma ϕ x ts).ncard)
  /-- Outcome (2b) at the second string: the case test holds at `x` and fails at `y`. -/
  | rejectCase (hx : Case2 (bigFGamma ϕ x ts) ∧ ¬ AggregateCase2a ϕ x ts)
      (hy : ¬ (Case2 (bigFGamma ϕ y ts) ∧ ¬ AggregateCase2a ϕ y ts))
  /-- Outcome (3), the local guide: some class of `∼` meets `y` and no tuple of `x`
  (entry 121). -/
  | rejectGuide (hset : LocalCertSetting G ϕ) (ht : LargeK ts (Nat.card W))
      (htm : 10 * ts ≤ Nat.card (Fin m)) (hW : Nonempty W)
      (h : GuideClassMissing ϕ ts x y hset ht htm hW)

namespace Line57Shape

variable {G : Subgroup (Equiv.Perm W)} {x y : W → A} {m : ℕ} {ϕ : G →* Equiv.Perm (Fin m)}
  {ts : ℕ}

/-- §15, **what the round does after line 5**: Procedure Align at outcomes (1), (2b)
and (3), and the answer `∅` at the two reject exits.  This is not the whole round: line 5
runs AggregateCertificates first, and all three exits read its output. -/
noncomputable def inner : Line57Shape W A G x y ϕ ts → SIReduction W A (Set (Equiv.Perm W))
  | .align S => S.red
  | .rejectDefect _ => .done ∅
  | .rejectCase _ _ => .done ∅
  | .rejectGuide _ _ _ _ _ => .done ∅

/-- §15, **lines 5–7**: the reduction of one round, as a named function of the data — line 5,
Procedure AggregateCertificates (`Babai.aggregateRoundStrong`), then what the outcome of
line 5 leads to.

All three exits come after the two phases, because all three read the aggregated output:
outcomes (1), (2b) and (3) read the structure or the partition the aggregation returns, and
each reject exit reads `F(z)^Γ`, which is built from the certificates. -/
noncomputable def red (S : Line57Shape W A G x y ϕ ts) (E : AggEnum W (Fin m)) :
    SIReduction W A (Set (Equiv.Perm W)) :=
  aggregateRoundStrong ϕ x y E S.inner

/-- Aligning the continuation aligns the whole strong round, as an equality of trees. -/
theorem aligned_red (S : Line57Shape W A G x y ϕ ts) (E : AggEnum W (Fin m))
    (I : SIInstance W A) :
    alignedAggregateRoundStrong ϕ x y E (SIReduction.alignRed I S.inner) =
      SIReduction.alignRed I (S.red E) :=
  alignedAggregateRoundStrong_eq_alignRed E I S.inner

/-- §14.1, line 11: the hint the round attaches to each of its calls.  A reject exit has no
call of its own, so it has no hint; the calls of the two phases of line 5 need none, because
they make the window shrink by a factor `t` and re-enter the recursion at line 1. -/
noncomputable def hint : (S : Line57Shape W A G x y ϕ ts) → (J : SIInstance W A) →
    Option (JohnsonCaseData J)
  | .align S => S.hint
  | .rejectDefect _ => fun _ => none
  | .rejectCase _ _ => fun _ => none
  | .rejectGuide _ _ _ _ _ => fun _ => none

/-- §15, line 5, **the regression**: the round *begins* with the certificate runs of
Theorem 13.1.3, in coset form.  Nothing in `Babai.Line57Data` can be met by a round that skips
Procedure AggregateCertificates; this is what Finding 3 of the audit of Secs. 14–15 asked
for. -/
theorem certPhase_prefix_calls_red (S : Line57Shape W A G x y ϕ ts)
    (E : AggEnum W (Fin m)) :
    (certPhaseStrong ϕ x y E (Λ := A)).calls <+: (S.red E).calls := by
  rw [red, calls_aggregateRoundStrong]
  exact List.prefix_append _ _

/-- §15, line 5, **the regression, as a count**: the round makes at least as many calls as
the two phases of Procedure AggregateCertificates together. -/
theorem calls_length_phases_le_red (S : Line57Shape W A G x y ϕ ts)
    (E : AggEnum W (Fin m)) :
    (certPhaseStrong ϕ x y E (Λ := A)).calls.length
        + (comparePhaseStrong ϕ x y E (Λ := A)).calls.length
      ≤ (S.red E).calls.length := by
  rw [red, calls_aggregateRoundStrong, List.length_append, List.length_append]
  omega

@[simp] theorem inner_align (S : AlignShape W A G x y) :
    (Line57Shape.align (ϕ := ϕ) (ts := ts) S).inner = S.red := rfl

@[simp] theorem hint_align (S : AlignShape W A G x y) :
    (Line57Shape.align (ϕ := ϕ) (ts := ts) S).hint = S.hint := rfl

end Line57Shape

/-- §15, **lines 5–7 on the window**: one round of the branch of lines 5–7, as the data of
`Babai.Line57Shape` together with the five facts the fields of `Babai.Sec15Remaining` ask
for.  The reduction is not a field: it is `Babai.Line57Shape.red`.

* `par` is the Johnson parameter `m` of the ambient instance, which Eq. (73) halves;
* `cost` is the number of instances the round produces. -/
structure Line57Data (W : Type u) [Fintype W] [DecidableEq W] (A : Type v)
    (G : Subgroup (Equiv.Perm W)) (x y : W → A) {m : ℕ} (ϕ : G →* Equiv.Perm (Fin m))
    (ts : ℕ) (par cost : ℕ) where
  /-- The data the round runs on. -/
  shape : Line57Shape W A G x y ϕ ts
  /-- The orders and covers supplied to strong descent in Sec. 13. -/
  enum : AggEnum W (Fin m)
  /-- The supplied lists cover the required cosets and satisfy the call bounds. -/
  enum_spec : enum.Spec ϕ x y ts
  /-- The reduction is correct. -/
  run_red : (shape.red enum).run = strIso (G : Set (Equiv.Perm W)) x y
  /-- Every call is made with respect to a subset of `G`, so the lift to `Ω` applies. -/
  calls_K : ∀ J ∈ (shape.red enum).calls, J.K ⊆ (G : Set (Equiv.Perm W))
  /-- Every call is a coset instance in the ambient group. -/
  calls_coset : ∀ J ∈ (shape.red enum).calls, IsCosetInstance G J
  /-- The number of calls. -/
  calls_length : (shape.red enum).calls.length ≤ cost
  /-- Every hint is with respect to a subgroup of `G`, and its Johnson parameter is at most
  half of `par` — Eq. (73). -/
  hint_le : ∀ (J : SIInstance W A) (d : JohnsonCaseData J), shape.hint J = some d →
    d.K ≤ G ∧ 2 * d.m ≤ par
  /-- Every call either has a window of at most `4n/5` points or carries a hint. -/
  calls_progress : ∀ J ∈ (shape.red enum).calls,
    5 * J.windowSize ≤ 4 * Fintype.card W ∨ (shape.hint (alignInst J)).isSome = true

namespace Line57Data

variable {G : Subgroup (Equiv.Perm W)} {x y : W → A} {m : ℕ} {ϕ : G →* Equiv.Perm (Fin m)}
  {ts : ℕ} {par cost cost' : ℕ}

/-- Legacy group interface. Live branches use `toCosetCore` and align after lifting. -/
noncomputable def toCore (C : Line57Data W A G x y ϕ ts par cost) :
    Line4cdCore W A G x y par cost where
  red := (C.shape.red C.enum).alignCalls
  hint := C.shape.hint
  run_red := by rw [run_alignCalls]; exact C.run_red
  calls_K := by
    intro J hJ
    rw [calls_alignCalls, List.mem_map] at hJ
    obtain ⟨J', hJ', rfl⟩ := hJ
    exact K_alignInst_subset (C.calls_coset J' hJ')
  calls_group := by
    intro J hJ
    rw [calls_alignCalls, List.mem_map] at hJ
    obtain ⟨J', hJ', rfl⟩ := hJ
    exact isGroupInstance_alignInst (C.calls_coset J' hJ')
  calls_length := by rw [calls_alignCalls, List.length_map]; exact C.calls_length
  hint_le := C.hint_le
  calls_progress := by
    intro J hJ
    rw [calls_alignCalls, List.mem_map] at hJ
    obtain ⟨J', hJ', rfl⟩ := hJ
    exact C.calls_progress J' hJ'

/-- The live round is lifted through this coset interface. -/
noncomputable def toCosetCore (C : Line57Data W A G x y ϕ ts par cost) :
    CosetCore W A G x y par cost where
  red := C.shape.red C.enum
  hint := C.shape.hint
  run_red := C.run_red
  calls_coset := C.calls_coset
  calls_length := C.calls_length
  hint_le := C.hint_le
  calls_progress := C.calls_progress

/-- A round that produces at most `cost` instances produces at most `cost'` for every
`cost' ≥ cost`. -/
def mono (C : Line57Data W A G x y ϕ ts par cost) (h : cost ≤ cost') :
    Line57Data W A G x y ϕ ts par cost' :=
  { C with calls_length := le_trans C.calls_length h }

/-- §15, lines 5–7: **the five facts for the whole round, from the five facts for what comes
after line 5.**

The calls of the round are the calls of the two phases of Procedure AggregateCertificates,
then the calls of what the outcome leads to (`Babai.calls_aggregateRoundStrong`).  The value
is unchanged (`Babai.run_aggregateRoundStrong`).  For the phase calls the three remaining
facts are Theorem 13.1.3 and Prop. 13.1.11 read through the alignment step of
`Babai.window_calls_aggregateRoundStrong`: each candidate set is a coset inside `G`,
and each call has `t·|Δ| ≤ n`, which with `t ≥ 5` is
the window alternative of `Babai.MakesProgress`.  Their number is
`Babai.aggregateRoundCost`. -/
noncomputable def ofInnerWithEnum (S : Line57Shape W A G x y ϕ ts)
    (E : AggEnum W (Fin m)) (hE : E.Spec ϕ x y ts) (h5 : 5 ≤ ts)
    (run_inner : S.inner.run = strIso (G : Set (Equiv.Perm W)) x y)
    (K_inner : ∀ J ∈ S.inner.calls, J.K ⊆ (G : Set (Equiv.Perm W)))
    (group_inner : ∀ J ∈ S.inner.calls, IsCosetInstance G J)
    (length_inner : S.inner.calls.length ≤ cost)
    (hint_inner : ∀ (J : SIInstance W A) (d : JohnsonCaseData J), S.hint J = some d →
      d.K ≤ G ∧ 2 * d.m ≤ par)
    (progress_inner : ∀ J ∈ S.inner.calls,
      5 * J.windowSize ≤ 4 * Fintype.card W ∨ (S.hint (alignInst J)).isSome = true) :
    Line57Data W A G x y ϕ ts par (cost + aggregateRoundCost m ts (Fintype.card W)) where
  shape := S
  enum := E
  enum_spec := hE
  run_red := by rw [Line57Shape.red, run_aggregateRoundStrong, run_inner]
  calls_K := by
    intro J hJ
    exact (isCosetInstance_calls_aggregateRoundStrong E hE.toCover hE.toBound.invariant
      S.inner group_inner hJ).K_subset
  calls_coset := by
    intro J hJ
    exact isCosetInstance_calls_aggregateRoundStrong E hE.toCover hE.toBound.invariant
      S.inner group_inner hJ
  calls_length := by
    rw [Line57Shape.red]
    refine le_trans (calls_length_aggregateRoundStrong E hE.toBound h5 _) ?_
    rw [Fintype.card_fin, Nat.card_eq_fintype_card]
    exact Nat.add_le_add_right length_inner _
  hint_le := hint_inner
  calls_progress := by
    intro J hJ
    rw [Line57Shape.red] at hJ
    rcases window_calls_aggregateRoundStrong E hE.toBound h5 _ hJ with h | h
    · refine Or.inl ?_
      have := five_mul_ncard_le_of_window_le h5 h
      rwa [Nat.card_eq_fintype_card] at this
    · exact progress_inner J h

/-- The existing existence constructors use the finite-list witnesses. The returned
data still exposes the lists, so a family of choices can supply a different order. -/
noncomputable def ofInner (S : Line57Shape W A G x y ϕ ts) (h5 : 5 ≤ ts)
    (run_inner : S.inner.run = strIso (G : Set (Equiv.Perm W)) x y)
    (K_inner : ∀ J ∈ S.inner.calls, J.K ⊆ (G : Set (Equiv.Perm W)))
    (group_inner : ∀ J ∈ S.inner.calls, IsCosetInstance G J)
    (length_inner : S.inner.calls.length ≤ cost)
    (hint_inner : ∀ (J : SIInstance W A) (d : JohnsonCaseData J), S.hint J = some d →
      d.K ≤ G ∧ 2 * d.m ≤ par)
    (progress_inner : ∀ J ∈ S.inner.calls,
      5 * J.windowSize ≤ 4 * Fintype.card W ∨ (S.hint (alignInst J)).isSome = true) :
    Line57Data W A G x y ϕ ts par (cost + aggregateRoundCost m ts (Fintype.card W)) :=
  let E := Classical.choice (aggEnum_nonempty ϕ x y ts)
  ofInnerWithEnum S E.val E.property h5 run_inner K_inner group_inner length_inner
    hint_inner progress_inner

end Line57Data

/-- One round of Procedure Align, read as a round of lines 5–7, with the two phases of
Procedure AggregateCertificates in front.  This is how outcomes (1), (2b) and (3) of
Theorem 13.2.1 reach `Babai.Line57Data`. -/
noncomputable def Line4cdData.toLine57 {G : Subgroup (Equiv.Perm W)} {x y : W → A} {m : ℕ}
    (ϕ : G →* Equiv.Perm (Fin m)) (ts : ℕ) (h5 : 5 ≤ ts)
    {par cost : ℕ} (C : Line4cdData W A G x y par cost) :
    Line57Data W A G x y ϕ ts par (cost + aggregateRoundCost m ts (Fintype.card W)) :=
  Line57Data.ofInner (.align C.shape) h5 C.run_red C.calls_K
    C.calls_coset C.calls_length C.hint_le C.calls_progress

end Line57Shape

/-! ### Outcome (2a): the data of Cor. 12.0.10 -/

section Case2a

open scoped Classical

variable {Ω : Type u} {A : Type v} [Fintype Ω] [DecidableEq Ω] {I : SIInstance Ω A}

/-- §15, line 5, **outcome (2a) of Theorem 13.2.1 gives the data of line 4b**.

The canonical two-coloring is `Babai.bigOrbitColoring`, its class of the color `true` is
the orbit `C` of outcome (2) (`Babai.colorClass_bigOrbitColoring_eq_orbit`), it has more
than `m/2` points because it has more than `4m/5`, and the last field is Cor. 12.0.10's
hypothesis (`Babai.corollary_12_0_10_hypothesis_of_giant`) together with
`F(x) ≤ Aut_G(x)` (`Babai.bigF_le_autG`).

So outcome (2a) is dispatched by `Babai.line4bBranch`, exactly as line 4b is; this is
Theorem 13.2.1's third alternative, *"reduce the determination of `Iso_G(x,y)` to `n^{O(1)}`
instances of size `≤ 2n/3`"*. -/
theorem nonempty_smallDefectData_case2a (d : JohnsonCaseData I) (t : ℕ)
    (h2a : AggregateCase2a d.ϕ (restrictStr I.Δ I.x) t) :
    Nonempty (SmallDefectData d) := by
  classical
  set x : I.Δ → A := restrictStr I.Δ I.x with hx
  obtain ⟨γ₀, hbig, hgiant⟩ := h2a
  set H := bigFGamma d.ϕ x t with hH
  set C : Set (Fin d.m) := (orbit H γ₀ : Set (Fin d.m)) with hC
  have hcard : Fintype.card (Fin d.m) = d.m := Fintype.card_fin _
  have hcls : colorClass (bigOrbitColoring d.ϕ t) x true = C :=
    colorClass_bigOrbitColoring_eq_orbit d.ϕ t x hbig
  have hbig' : 4 * d.m < 5 * C.ncard := by simpa using hbig
  refine ⟨{
    col := bigOrbitColoring d.ϕ t
    canonical := isCanonicalColoring_bigOrbitColoring d.ϕ t
    c := true
    large := by rw [hcls]; omega
    giantOn := ?_ }⟩
  intro α hα hfix
  rw [hcls] at hfix ⊢
  obtain ⟨b, hb, hval⟩ :=
    corollary_12_0_10_hypothesis_of_giant H (isInvariant_orbit H γ₀) hgiant α hα hfix
  refine ⟨b, ?_, hval⟩
  obtain ⟨⟨σ, hσ⟩, rfl⟩ := hb
  refine ⟨(σ : Equiv.Perm I.Δ), ?_, bigF_le hσ, rfl⟩
  have hmem : (σ : Equiv.Perm I.Δ) ∈ autG d.windowGroup x := bigF_le_autG hσ
  have : (σ : Equiv.Perm I.Δ) ∈ wAut Set.univ (d.windowGroup : Set (Equiv.Perm I.Δ)) x :=
    hmem
  rwa [wAut, wIso_univ] at this

end Case2a

/-! ### The test of line 6, and the branch of outcome (2a), at a hinted instance -/

section Branch

open scoped Classical

variable {Ω : Type u} {A : Type v} [Fintype Ω] [DecidableEq Ω]

/-- §15, **the test of line 6** at a hinted instance: *"if AggregateCertificates returns
canonically embedded `k`-ary relational structure on `Γ` with relative symmetry defect
`≥ 1/2`"*.

This is the definition meant for the field `AggregatesToStructure` of
`Babai.Sec15Remaining`.  It is a test on the instance alone — the group `G = K^Δ` and the
giant representation `ϕ` of line 3 are the ones the hint carries (`Babai.johnsonData`), the
string is the string of the window, and the test set size is the `t = O(log n)` of §13.1
(`Babai.testSetSize`).  Like `Babai.SmallDefect`, it reads the instance through the *chosen*
Johnson data, so both strings of one instance are read through the same `(G, ϕ)`. -/
def aggregatesToStructure (i : HintedInstance Ω A) : Prop :=
  ∃ hJ : IsJohnson i, AggregatesToStructureOn (johnsonData hJ).ϕ
    (restrictStr i.inst.Δ i.inst.x) (testSetSize i.inst.windowSize)

/-- §15, line 5, **outcome (2a)** at a hinted instance. -/
def Case2aInstance (i : HintedInstance Ω A) : Prop :=
  ∃ hJ : IsJohnson i, AggregateCase2a (johnsonData hJ).ϕ
    (restrictStr i.inst.Δ i.inst.x) (testSetSize i.inst.windowSize)

/-- §15, line 5, outcome (2a): **the tests the branch is taken after** — the instance is in
the Johnson case, the test of line 2 has failed, and Theorem 13.2.1 lands in case (2a). -/
def Line5Case2aTest (i : HintedInstance Ω A) : Prop :=
  (IsJohnson i ∧ ¬ param i ≤ ellOf i.inst.windowSize) ∧ Case2aInstance i

/-- Sec. 15, line 5, outcome (2a): the two-coloring and the inputs to strong descent. -/
structure Line5Case2aData (i : HintedInstance Ω A) (h : Line5Case2aTest i) where
  data : SmallDefectData (johnsonData h.1.1)
  enum : AggEnum i.inst.Δ (Fin (johnsonData h.1.1).m)
  enum_spec : enum.Spec (johnsonData h.1.1).ϕ (restrictStr i.inst.Δ i.inst.x)
    (restrictStr i.inst.Δ i.inst.y) (testSetSize i.inst.windowSize)

namespace Line5Case2aData

variable {i : HintedInstance Ω A} {h : Line5Case2aTest i} (D : Line5Case2aData i h)

/-- The two strong-descent phases, before any call is aligned. -/
noncomputable def prefixCosetOnWindow : SIReduction i.inst.Δ A (Set (Equiv.Perm i.inst.Δ)) :=
  aggregateRoundStrong (johnsonData h.1.1).ϕ
    (restrictStr i.inst.Δ i.inst.x) (restrictStr i.inst.Δ i.inst.y) D.enum (.done ∅)

/-- The phase calls are lifted in coset form. -/
noncomputable def phaseCoset : SIReduction Ω A (Set (Equiv.Perm Ω)) :=
  liftWindow (johnsonData h.1.1).K i.inst.Δ (johnsonData h.1.1).invariant i.inst.x
    D.prefixCosetOnWindow

/-- Line 5 runs before the outcome-(2a) reduction reads its certificates. -/
noncomputable def prefixOnWindow : SIReduction i.inst.Δ A (Set (Equiv.Perm i.inst.Δ)) :=
  D.prefixCosetOnWindow

theorem prefixOnWindow_spec : ∀ J ∈ D.prefixOnWindow.calls,
    J.K ⊆ ((johnsonData h.1.1).windowGroup : Set (Equiv.Perm i.inst.Δ)) ∧
      IsCosetInstance (johnsonData h.1.1).windowGroup J ∧
      testSetSize i.inst.windowSize * J.windowSize ≤ Nat.card i.inst.Δ := by
  intro J hJ
  have hc := isCosetInstance_calls_aggregateRoundStrong D.enum D.enum_spec.toCover
    D.enum_spec.toBound.invariant (.done ∅) (by simp) hJ
  refine ⟨hc.K_subset, hc, ?_⟩
  rcases window_calls_aggregateRoundStrong D.enum D.enum_spec.toBound
    (five_le_testSetSize _) (.done ∅) hJ with hw | he
  · exact hw
  · simp at he

/-- This interface is the aligned prefix after the window lift. -/
noncomputable def phaseRound : SIReduction Ω A (Set (Equiv.Perm Ω)) :=
  D.phaseCoset.alignCalls

theorem prefix_group : ∀ J ∈ D.phaseRound.calls, IsGroupInstance J := by
  intro J hJ
  rw [phaseRound, calls_alignCalls, List.mem_map] at hJ
  obtain ⟨J₀, hJ, rfl⟩ := hJ
  exact isGroupInstance_alignInst
    (calls_liftWindow_isCosetInstance (johnsonData h.1.1).invariant i.inst.x _
      (fun J hJ => (D.prefixOnWindow_spec J hJ).1)
      (fun J hJ => (D.prefixOnWindow_spec J hJ).2.1) J₀ hJ)

theorem prefix_window : ∀ J ∈ D.phaseRound.calls,
    5 * J.windowSize ≤ 4 * i.inst.windowSize := by
  intro J hJ
  rw [phaseRound, calls_alignCalls, List.mem_map] at hJ
  obtain ⟨J₀, hJ, rfl⟩ := hJ
  obtain ⟨J', hJ', hsize⟩ := calls_liftWindow_windowSize (johnsonData h.1.1).invariant
    i.inst.x _ (fun J hJ => (D.prefixOnWindow_spec J hJ).1) J₀ hJ
  have hwin := five_mul_ncard_le_of_window_le (five_le_testSetSize _)
    (D.prefixOnWindow_spec J' hJ').2.2
  rw [Nat.card_eq_fintype_card, card_window (johnsonData h.1.1)] at hwin
  rw [windowSize_alignInst, hsize]
  exact hwin

theorem prefix_length : D.phaseRound.calls.length ≤
    aggregateRoundCost (johnsonData h.1.1).m (testSetSize i.inst.windowSize)
      i.inst.windowSize := by
  rw [phaseRound, calls_alignCalls, List.length_map, phaseCoset,
    calls_length_liftWindow (johnsonData h.1.1).invariant i.inst.x D.prefixCosetOnWindow
      (fun J hJ => (D.prefixOnWindow_spec J hJ).1)]
  have hc := calls_length_aggregateRoundStrong D.enum D.enum_spec.toBound
    (five_le_testSetSize _) (SIReduction.done (Ω := i.inst.Δ) (A := A) (∅ : Set (Equiv.Perm i.inst.Δ)))
  simpa only [SIReduction.calls_done, List.length_nil, zero_add,
    Fintype.card_fin, Nat.card_eq_fintype_card, card_window (johnsonData h.1.1)] using hc

end Line5Case2aData

/-- Each raw node can supply its own valid orders for outcome (2a). -/
def Line5Case2aChoice (Ω : Type u) (A : Type v) [Fintype Ω] [DecidableEq Ω] :=
  ∀ (i : HintedInstance Ω A) (h : Line5Case2aTest i), Line5Case2aData i h

/-- Outcome (2a) keeps both phases and its continuation in coset form. -/
noncomputable def line5Case2aFunCoset (S : Line5Case2aChoice Ω A) (i : HintedInstance Ω A) :
    SIReduction Ω A (Set (Equiv.Perm Ω)) :=
  if h : Line5Case2aTest i then
    (S i h).phaseCoset.bind fun _ =>
      line4bBranchCoset (johnsonData h.1.1) (S i h).data (hugeM_of_data h.1.1 h.1.2)
  else cosetLeaf i.inst i.inst.answer

/-- Sec. 15, line 5, outcome (2a): aggregate first, then apply Cor. 12.0.10. -/
noncomputable def line5Case2aFun (S : Line5Case2aChoice Ω A) (i : HintedInstance Ω A) :
    SIReduction Ω A (Set (Equiv.Perm Ω)) :=
  SIReduction.alignRed i.inst (line5Case2aFunCoset S i)

/-- Alignment distributes over the two phases and their continuation as a tree. -/
theorem line5Case2aFun_of_test (S : Line5Case2aChoice Ω A) (i : HintedInstance Ω A)
    (h : Line5Case2aTest i) :
    line5Case2aFun S i = (S i h).phaseRound.bind fun _ =>
      line4bBranch (johnsonData h.1.1) (S i h).data (hugeM_of_data h.1.1 h.1.2) := by
  rw [line5Case2aFun, line5Case2aFunCoset, dif_pos h, SIReduction.alignRed_bind]
  rfl

/-- Sec. 15, outcome (2a): the branch returns the window isomorphisms. -/
theorem line5Case2a_run (S : Line5Case2aChoice Ω A) (i : HintedInstance Ω A)
    (hJ : IsJohnson i)
    (hell : ¬ param i ≤ ellOf i.inst.windowSize) (h2a : Case2aInstance i) :
    (line5Case2aFun S i).run = i.inst.answer := by
  have h : Line5Case2aTest i := ⟨⟨hJ, hell⟩, h2a⟩
  rw [line5Case2aFun_of_test S i h, SIReduction.run_bind]
  exact run_line4bBranch _ _ _

/-- Sec. 15, outcome (2a): the phase calls and the final calls shrink the window. -/
theorem line5Case2a_decreases (S : Line5Case2aChoice Ω A) (i : HintedInstance Ω A)
    (hJ : IsJohnson i)
    (hell : ¬ param i ≤ ellOf i.inst.windowSize) (h2a : Case2aInstance i) :
    ∀ J ∈ (line5Case2aFun S i).calls,
      MakesProgress HintedInstance.win param i (⟨J, none⟩ : HintedInstance Ω A) := by
  have h : Line5Case2aTest i := ⟨⟨hJ, hell⟩, h2a⟩
  intro J hJmem
  rw [line5Case2aFun_of_test S i h, SIReduction.calls_bind, List.mem_append] at hJmem
  refine Or.inl ⟨(johnsonData hJ).one_le_windowSize, ?_⟩
  rcases hJmem with hJmem | hJmem
  · exact (S i h).prefix_window J hJmem
  · have := decreases_line4bBranch _ _ _ J hJmem
    show 5 * J.windowSize ≤ 4 * i.inst.windowSize
    omega

/-- Sec. 15, outcome (2a): charge the two phases and the Cor. 12.0.10 reduction. -/
theorem line5Case2a_calls (S : Line5Case2aChoice Ω A) (i : HintedInstance Ω A)
    (hJ : IsJohnson i)
    (hell : ¬ param i ≤ ellOf i.inst.windowSize) (h2a : Case2aInstance i) :
    ((line5Case2aFun S i).calls).length ≤ masterRoundCost i.inst.windowSize +
      aggregateRoundCost (johnsonData hJ).m (testSetSize i.inst.windowSize)
        i.inst.windowSize := by
  have h : Line5Case2aTest i := ⟨⟨hJ, hell⟩, h2a⟩
  rw [line5Case2aFun_of_test S i h, SIReduction.calls_bind, List.length_append]
  have hc := calls_length_line4bBranch (johnsonData h.1.1) (S i h).data
    (hugeM_of_data h.1.1 h.1.2)
  have hp := (S i h).prefix_length
  rw [masterRoundCost]
  omega

/-- Sec. 15, outcome (2a): every aligned call is a group instance. -/
theorem line5Case2a_group (S : Line5Case2aChoice Ω A) (i : HintedInstance Ω A)
    (hJ : IsJohnson i)
    (hell : ¬ param i ≤ ellOf i.inst.windowSize) (h2a : Case2aInstance i) :
    ∀ J ∈ (line5Case2aFun S i).calls, IsGroupInstance J := by
  have h : Line5Case2aTest i := ⟨⟨hJ, hell⟩, h2a⟩
  intro J hJmem
  rw [line5Case2aFun_of_test S i h, SIReduction.calls_bind, List.mem_append] at hJmem
  rcases hJmem with hJmem | hJmem
  · exact (S i h).prefix_group J hJmem
  · exact calls_line4bBranch_isGroupInstance _ _ _ J hJmem

/-- Sec. 15, line 5: outcome (2a) includes both strong-descent phases. -/
theorem line5Case2a_calls_ge_phases (S : Line5Case2aChoice Ω A) (i : HintedInstance Ω A)
    (h : Line5Case2aTest i) :
    (certPhaseStrong (johnsonData h.1.1).ϕ (restrictStr i.inst.Δ i.inst.x)
        (restrictStr i.inst.Δ i.inst.y) (S i h).enum).calls.length +
      (comparePhaseStrong (johnsonData h.1.1).ϕ (restrictStr i.inst.Δ i.inst.x)
        (restrictStr i.inst.Δ i.inst.y) (S i h).enum).calls.length ≤
      (line5Case2aFun S i).calls.length := by
  rw [line5Case2aFun_of_test S i h, SIReduction.calls_bind, List.length_append,
    Line5Case2aData.phaseRound, calls_alignCalls, List.length_map,
    Line5Case2aData.phaseCoset, calls_length_liftWindow (johnsonData h.1.1).invariant
      i.inst.x (S i h).prefixCosetOnWindow (fun J hJ => ((S i h).prefixOnWindow_spec J hJ).1),
    Line5Case2aData.prefixCosetOnWindow, calls_aggregateRoundStrong,
    List.length_append, List.length_append,
    SIReduction.calls_done, List.length_nil]
  omega

end Branch

/-! ### Outcome (1) as an object of the outcome category

Theorem 13.2.1's case (1) returns `Babai.orbitPartition`, a colored partition of `Γ` with
`Bool` colors.  Procedure Align reads its input as a point of `Babai.SplitOutcomes (Fin m)`:
a colored partition of `↥(□X)` with `ℕ` colors, together with its underlying set.  The
passage is a change of the index type of the points (`Γ` against
`↥(Set.univ : Set Γ)`) and a renaming of the two colors, neither of which touches the
blocks.  `Babai.univColoredPartition` does both at once. -/

section Outcome1

variable {Γ : Type} [Fintype Γ] [DecidableEq Γ]

/-- The number of points of a subset of `Γ`, read on `↥(Set.univ : Set Γ)`. -/
theorem ncard_preimage_val_univ (S : Set Γ) :
    (Subtype.val ⁻¹' S : Set ↥(Set.univ : Set Γ)).ncard = S.ncard := by
  have hinj : Function.Injective (Subtype.val : ↥(Set.univ : Set Γ) → Γ) :=
    Subtype.val_injective
  have himg : (Subtype.val : ↥(Set.univ : Set Γ) → Γ) '' (Subtype.val ⁻¹' S) = S := by
    refine Set.image_preimage_eq_of_subset fun γ _ => ⟨⟨γ, trivial⟩, rfl⟩
  calc (Subtype.val ⁻¹' S : Set ↥(Set.univ : Set Γ)).ncard
      = ((Subtype.val : ↥(Set.univ : Set Γ) → Γ) '' (Subtype.val ⁻¹' S)).ncard :=
        (Set.ncard_image_of_injective _ hinj).symm
    _ = S.ncard := by rw [himg]

/-- §13.2, case (1): `Babai.orbitPartition` read on `↥(Set.univ : Set Γ)` with `ℕ` colors —
the shape an object of `Babai.ColoredPartitions` has.  The color of a point is `1` if it is
a fixed point of `H` and `0` otherwise, and the blocks are the blocks of
`Babai.orbitPartition`. -/
noncomputable def univColoredPartition (H : Subgroup (Equiv.Perm Γ)) :
    ColoredPartition ↥(Set.univ : Set Γ) ℕ where
  color x := cond ((orbitPartition H).color (x : Γ)) 1 0
  part := Setoid.comap (fun x : ↥(Set.univ : Set Γ) => (x : Γ)) (orbitPartition H).part
  part_le_color h := congrArg (fun b : Bool => cond b 1 0)
    ((orbitPartition H).part_le_color h)

theorem color_univColoredPartition (H : Subgroup (Equiv.Perm Γ))
    (x : ↥(Set.univ : Set Γ)) :
    (univColoredPartition H).color x = cond ((orbitPartition H).color (x : Γ)) 1 0 := rfl

theorem part_univColoredPartition (H : Subgroup (Equiv.Perm Γ))
    (x y : ↥(Set.univ : Set Γ)) :
    (univColoredPartition H).part x y ↔ (orbitPartition H).part (x : Γ) (y : Γ) := Iff.rfl

theorem block_univColoredPartition (H : Subgroup (Equiv.Perm Γ))
    (x : ↥(Set.univ : Set Γ)) :
    (univColoredPartition H).block x = Subtype.val ⁻¹' ((orbitPartition H).block (x : Γ)) :=
  rfl

theorem colorClass_univColoredPartition (H : Subgroup (Equiv.Perm Γ))
    (x : ↥(Set.univ : Set Γ)) :
    (univColoredPartition H).colorClass ((univColoredPartition H).color x)
      = Subtype.val ⁻¹'
        ((orbitPartition H).colorClass ((orbitPartition H).color (x : Γ))) := by
  ext y
  show ((univColoredPartition H).color y = (univColoredPartition H).color x) ↔
    ((orbitPartition H).color (y : Γ) = (orbitPartition H).color (x : Γ))
  rw [color_univColoredPartition, color_univColoredPartition]
  cases hx : (orbitPartition H).color (x : Γ) <;>
    cases hy : (orbitPartition H).color (y : Γ) <;> simp

/-- §13.2, case (1): the colored partition of `↥(Set.univ : Set Γ)` by the orbits of `F^Γ`
is a colored `4/5`-partition.  This is `Babai.orbitPartition_isAlphaPartition` read through
the bijection `↥(Set.univ : Set Γ) ≃ Γ`, which preserves both the blocks and the color
classes. -/
theorem isAlphaPartition_univColoredPartition (H : Subgroup (Equiv.Perm Γ)) (h : Case1 H)
    (inst : Fintype ↥(Set.univ : Set Γ)) :
    @ColoredPartition.IsAlphaPartition _ _ (univColoredPartition H) inst (4 / 5 : ℝ) := by
  obtain ⟨hadm, hrho⟩ := orbitPartition_isAlphaPartition H h
  have hblk : ∀ x : ↥(Set.univ : Set Γ),
      ((univColoredPartition H).block x).ncard
        = ((orbitPartition H).block (x : Γ)).ncard := by
    intro x
    rw [block_univColoredPartition, ncard_preimage_val_univ]
  have hcls : ∀ x : ↥(Set.univ : Set Γ),
      ((univColoredPartition H).colorClass ((univColoredPartition H).color x)).ncard
        = ((orbitPartition H).colorClass ((orbitPartition H).color (x : Γ))).ncard := by
    intro x
    rw [colorClass_univColoredPartition, ncard_preimage_val_univ]
  refine ⟨?_, ?_⟩
  · intro x hx
    rw [hblk x]
    exact hadm (x : Γ) (by rw [← hcls x]; exact hx)
  · have hle : @ColoredPartition.rho _ _ (univColoredPartition H) inst
        ≤ (orbitPartition H).rho := by
      refine @ColoredPartition.rho_le _ _ (univColoredPartition H) inst _ (fun x => ?_)
      rw [hblk x]
      exact ColoredPartition.ncard_block_le_rho _ _
    have hleR : (@ColoredPartition.rho _ _ (univColoredPartition H) inst : ℝ)
        ≤ ((orbitPartition H).rho : ℝ) := by exact_mod_cast hle
    have hcardN : @Fintype.card ↥(Set.univ : Set Γ) inst = Fintype.card Γ :=
      Fintype.card_congr (Equiv.Set.univ Γ)
    have hcard : (@Fintype.card ↥(Set.univ : Set Γ) inst : ℝ) = (Fintype.card Γ : ℝ) := by
      exact_mod_cast hcardN
    rw [hcard]
    linarith

end Outcome1

/-! ### Outcome (1) as the canonical versions Procedure Align consumes -/

section Outcome1Versions

variable {Γ : Type} [Fintype Γ] [DecidableEq Γ]

/-- §13.2, case (1), and §15, line 7: the outcome of Theorem 13.2.1 as a point of the
outcome category of Theorem 9.2.3 — alternative (a), a colored partition, on all of `Γ`. -/
noncomputable def orbitSplitOutcome (H : Subgroup (Equiv.Perm Γ)) :
    Pt (SplitOutcomes Γ) :=
  ⟨Set.univ, Sum.inl (univColoredPartition H)⟩

/-- §15, line 7: the outcome of case (1) is alternative (a) of Theorem 9.2.3 at the
threshold `4/5` — *"a canonical colored `4/5`-partition of `Γ`"*. -/
theorem isSplitOutcome_orbitSplitOutcome (H : Subgroup (Equiv.Perm Γ)) (h : Case1 H) :
    IsSplitOutcome (4 / 5 : ℝ) (Set.univ : Set Γ) (orbitSplitOutcome H) :=
  ⟨rfl, isAlphaPartition_univColoredPartition H h _⟩

variable {Ω Λ : Type*} [Fintype Ω] [DecidableEq Ω] {G : Subgroup (Equiv.Perm Ω)}

/-- §13.2, case (1): **the colored `4/5`-partition of `Γ` is canonical**, as a point of the
outcome category.

The underlying set is all of `Γ` in both cases, and the permutation `σ^ϕ` is a morphism of
colored partitions from the outcome at `z` to the outcome at `z^σ`: `F(z^σ)^Γ` is
`F(z)^Γ` conjugated by `σ^ϕ` (`Babai.canonical_bigFGamma`), and conjugation moves the colors
and the blocks of `Babai.orbitPartition` by the same permutation
(`Babai.color_orbitPartition_map_conj`, `Babai.part_orbitPartition_map_conj`).  The moved
object is unique (`Babai.Cat.eq_of_transport`), so it **is** `σ^ϕ • X(z)`. -/
theorem isCanonicalStructure_orbitSplitOutcome
    [MulAction (Equiv.Perm Γ) (Pt (SplitOutcomes Γ))]
    (hK : IsCatAction (SplitOutcomes Γ)) (ϕ : G →* Equiv.Perm Γ) (t : ℕ) :
    IsCanonicalStructure (A := Λ) ϕ
      (fun z => orbitSplitOutcome (bigFGamma ϕ z t)) := by
  intro z σ
  set p : Equiv.Perm Γ := (ϕ σ : Equiv.Perm Γ) with hp
  set H : Subgroup (Equiv.Perm Γ) := bigFGamma ϕ z t with hHdef
  have hH : bigFGamma ϕ (strAct z (σ : Equiv.Perm Ω)) t
      = H.map (MulAut.conj p).toMonoidHom := canonical_bigFGamma ϕ z t σ
  have hcar : (orbitSplitOutcome (bigFGamma ϕ (strAct z (σ : Equiv.Perm Ω)) t)).car
      = p '' (orbitSplitOutcome H).car := by
    show (Set.univ : Set Γ) = p '' (Set.univ : Set Γ)
    rw [Set.image_univ, Equiv.range_eq_univ]
  refine hK.eq_smul hcar ?_
  set X : Pt (SplitOutcomes Γ) := orbitSplitOutcome H with hX
  set Y : Pt (SplitOutcomes Γ) :=
    orbitSplitOutcome (bigFGamma ϕ (strAct z (σ : Equiv.Perm Ω)) t) with hY
  show permHom p X Y hcar ∈
    (ColoredPartitions Γ ℕ).Iso (univColoredPartition H)
      (univColoredPartition (bigFGamma ϕ (strAct z (σ : Equiv.Perm Ω)) t))
  have hval : ∀ x : ↥X.car, ((permHom p X Y hcar x : ↥Y.car) : Γ) = p (x : Γ) :=
    fun x => rfl
  constructor
  · intro x
    show cond ((orbitPartition (bigFGamma ϕ (strAct z (σ : Equiv.Perm Ω)) t)).color
        ((permHom p X Y hcar x : ↥Y.car) : Γ)) 1 0
      = cond ((orbitPartition H).color ((x : ↥X.car) : Γ)) 1 0
    rw [hval x, hH, color_orbitPartition_map_conj H p ((x : ↥X.car) : Γ)]
  · intro x y
    show (orbitPartition H).part ((x : ↥X.car) : Γ) ((y : ↥X.car) : Γ) ↔
      (orbitPartition (bigFGamma ϕ (strAct z (σ : Equiv.Perm Ω)) t)).part
        ((permHom p X Y hcar x : ↥Y.car) : Γ) ((permHom p X Y hcar y : ↥Y.car) : Γ)
    rw [hval x, hval y, hH,
      part_orbitPartition_map_conj H p ((x : ↥X.car) : Γ) ((y : ↥X.car) : Γ)]

/-- §15, line 7: **the outcome of case (1) is a canonical family of versions** — a family
of one version per string, which is what Procedure Align consumes
(`Babai.IsCanonicalVersions`). -/
theorem isCanonicalVersions_orbitSplitOutcome
    [MulAction (Equiv.Perm Γ) (Pt (SplitOutcomes Γ))]
    (hK : IsCatAction (SplitOutcomes Γ)) (ϕ : G →* Equiv.Perm Γ) (t : ℕ) :
    IsCanonicalVersions (A := Λ) ϕ
      (fun z => ({orbitSplitOutcome (bigFGamma ϕ z t)} : Set (Pt (SplitOutcomes Γ)))) :=
  isCanonicalVersions_singleton (isCanonicalStructure_orbitSplitOutcome hK ϕ t)

end Outcome1Versions

/-! ### The label size at line 5

`Babai.nonempty_line7Core` asks for a common size `tlab` of the labels `T(u)` of
Theorem 10.5.1, with `1 ≤ tlab` and `4·tlab < m`.  At line 4c these come from the
identification of line 4 (`Babai.PrimitiveCaseId`), which line 5 does not have.  They are
available at line 5 all the same, from Theorem 10.5.1 itself: (c) says `|T(u)|` is constant
on an orbit and `G` is transitive on the window, (a) says `4|T(u)| < m`, and (d) says some
point is affected, which by (b) and (c) makes every point affected.  So nothing beyond the
Johnson data of line 3 is needed. -/

section LabelSize

variable {W : Type*} [Fintype W] [DecidableEq W] {G : Subgroup (Equiv.Perm W)}
  {m : ℕ} {ϕ : G →* Equiv.Perm (Fin m)}

/-- **Theorem 10.5.1 (c)** for a transitive group: all labels have the same size. -/
theorem tPoint_eq_of_transitive (hG : IsTransitive G) (hgiant : IsGiantRep ϕ)
    (hvl : VeryLargeK m (maxOrbitLength G)) (u₀ : W) (u : W) :
    tPoint ϕ u = tPoint ϕ u₀ := by
  haveI : Nonempty W := hG.nonempty
  have horb : orbit G u₀ = Set.univ := (isTransitive_iff_orbit_eq_univ G).1 hG u₀
  exact theorem_10_5_1_c ϕ hgiant hvl (by rw [horb]; trivial)

/-- **Theorem 10.5.1 (a)**: `4|T(u)| < m`. -/
theorem four_mul_tPoint_lt (hgiant : IsGiantRep ϕ)
    (hvl : VeryLargeK m (maxOrbitLength G)) (u : W) : 4 * tPoint ϕ u < m := by
  have h := (theorem_10_5_1_a ϕ hgiant hvl u).1.1
  rwa [show (Tpoint ϕ u).ncard = tPoint ϕ u from rfl] at h

/-- **Theorem 10.5.1 (b), (c), (d)** for a transitive group: every point is affected, so
every label has at least one point.

*Proof.*  Item (d) gives a point `x` with `Affected ϕ x`, item (b) turns that into
`1 ≤ |T(x)|`, and item (c) carries it to every point, because `G` is transitive. -/
theorem one_le_tPoint_of_transitive (hG : IsTransitive G) (hgiant : IsGiantRep ϕ)
    (hvl : VeryLargeK m (maxOrbitLength G)) (u : W) : 1 ≤ tPoint ϕ u := by
  obtain ⟨⟨x, hx⟩, -⟩ := theorem_10_5_1_d ϕ hgiant hvl
  have h1 : 1 ≤ (Tpoint ϕ x).ncard := (theorem_10_5_1_b ϕ hgiant hvl x).1 hx
  have h2 : tPoint ϕ u = tPoint ϕ x := by
    rw [tPoint_eq_of_transitive hG hgiant hvl x u]
  rw [h2]
  exact h1

end LabelSize

/-! ### Lines 7 and 7a on the window: outcome (1) fed to Procedure Align -/

section Line7Core

open scoped Classical

variable {W : Type u} {A : Type v} [Fintype W] [DecidableEq W]

/-- §15, **lines 7 and 7a on the window**: outcome (1) of Theorem 13.2.1 — the canonical
colored `4/5`-partition of `Γ` — handed to Procedure Align.

The family of versions has one member per string (`Babai.isCanonicalVersions_orbitSplitOutcome`),
so the multiplicative cost of line 7 is `1`: Theorem 13.2.1 returns a single structure,
not a list of individualizations, which is why the `q(m)·m^{O(t)}` of line 4c does not
appear here.

Two parameters named `t` meet here and are kept apart: the size `tlab` of the labels
`T(u)` of Theorem 10.5.1 (c), the one Eq. (72) reads, and `ts`, the test set size of §13.1,
the one `F(x)^Γ` is built with.  Only `ts` is a parameter of the statement: `tlab` is read
off `ϕ` itself, and the three facts Eq. (72) needs about it come from Theorem 10.5.1
(`Babai.tPoint_eq_of_transitive`, `Babai.one_le_tPoint_of_transitive`,
`Babai.four_mul_tPoint_lt`).

The threshold is `4/5`, the one of Theorem 13.2.1; `5 · (4/5) ≤ 4`, so the window
alternative of `Babai.MakesProgress` holds for every `tlab ≥ 1` (see the corrected paper
entry on Sec. 15 lines 5–7a). -/
theorem nonempty_line7Core {G : Subgroup (Equiv.Perm W)} (hG : IsTransitive G)
    {m : ℕ} {ϕ : G →* Equiv.Perm (Fin m)} (hgiant : IsGiantRep ϕ)
    (hvl : VeryLargeK m (maxOrbitLength G)) (hm : 217 ≤ m) (hmn : m ≤ Fintype.card W)
    {x y : W → A} (ts : ℕ) (h5 : 5 ≤ ts) (h1 : Case1 (bigFGamma ϕ x ts)) :
    Nonempty (Line57Data W A G x y ϕ ts m
      (1 * (Fintype.card W + 1) *
        AlignDominantRoundData.alignDominantRoundCost (Fintype.card W)
        + aggregateRoundCost (Fintype.card W) ts (Fintype.card W))) := by
  classical
  haveI : Nonempty W := hG.nonempty
  obtain ⟨u₀⟩ := ‹Nonempty W›
  set tlab : ℕ := tPoint ϕ u₀ with htlab
  have ht : ∀ u : W, tPoint ϕ u = tlab := fun u =>
    tPoint_eq_of_transitive hG hgiant hvl u₀ u
  have ht1 : 1 ≤ tlab := one_le_tPoint_of_transitive hG hgiant hvl u₀
  have h4t : 4 * tlab < m := four_mul_tPoint_lt hgiant hvl u₀
  obtain ⟨inst, hK⟩ := exists_isCatAction_splitOutcomes (Γ := Fin m)
  letI := inst
  refine Nonempty.map (fun C => (Line4cdData.toLine57 ϕ ts h5 C).mono
    (Nat.add_le_add_left (aggregateRoundCost_mono_left hmn) _)) ?_
  refine nonempty_alignData_of_versions hG hgiant hvl ht ht1 h4t hm hmn hK
    (Vers := fun z => ({orbitSplitOutcome (bigFGamma ϕ z ts)} :
      Set (Pt (SplitOutcomes (Fin m)))))
    (isCanonicalVersions_orbitSplitOutcome hK ϕ ts) (Set.finite_singleton _)
    (V := 1) (by rw [Set.ncard_singleton]) (X' := orbitSplitOutcome (bigFGamma ϕ x ts))
    rfl (by norm_num) (by norm_num) (by norm_num)
    (isSplitOutcome_orbitSplitOutcome _ h1)

end Line7Core

/-! ### Lines 5, 7 and 7a as a branch of the round

Line 6's test fails exactly when Theorem 13.2.1 lands in case (1) or in case (2a)
(`Babai.not_aggregatesToStructureOn_iff`).  Case (2a) is `Babai.line5Case2aFun`, the branch
of line 4b; case (1) is line 7 — the colored `4/5`-partition — followed by line 7a,
Procedure Align, which is `Babai.nonempty_line7Core` read on `Ω`. -/

section Line567aBranch

open scoped Classical

variable {Ω : Type u} {A : Type v} [Fintype Ω] [DecidableEq Ω]

/-- §15, line 5, **outcome (1)** at a hinted instance. -/
def Case1Instance (i : HintedInstance Ω A) : Prop :=
  ∃ hJ : IsJohnson i, Case1 (bigFGamma (johnsonData hJ).ϕ
    (restrictStr i.inst.Δ i.inst.x) (testSetSize i.inst.windowSize))

/-- §15, lines 6 and 7: **the test of line 6 fails** exactly when the outcome is the
colored `4/5`-partition of case (1) or the Cor. 12.0.10 reduction of case (2a). -/
theorem not_aggregatesToStructure_iff {i : HintedInstance Ω A} (hJ : IsJohnson i) :
    ¬ aggregatesToStructure i ↔ Case1Instance i ∨ Case2aInstance i := by
  constructor
  · intro h
    have h' : ¬ AggregatesToStructureOn (johnsonData hJ).ϕ
        (restrictStr i.inst.Δ i.inst.x) (testSetSize i.inst.windowSize) := fun hc =>
      h ⟨hJ, hc⟩
    rcases (not_aggregatesToStructureOn_iff _ _ _).1 h' with h1 | h2
    · exact Or.inl ⟨hJ, h1⟩
    · exact Or.inr ⟨hJ, h2⟩
  · rintro (⟨hJ', h1⟩ | ⟨hJ', h2⟩) ⟨hJ'', hc⟩
    · exact hc.1 h1
    · exact hc.2 h2

/-- §15, lines 5, 7 and 7a, **outcome (1)**: the tests the branch of line 7 is taken
after — lines 1, 2 and 4 have failed, line 6's test has failed, and Theorem 13.2.1 lands in
case (1). -/
def Line7Test (i : HintedInstance Ω A) : Prop :=
  ((IsGroupInstance i.inst ∧ IsJohnson i) ∧ ¬ param i ≤ ellOf i.inst.windowSize) ∧
    Case1Instance i

variable [Fintype A] [DecidableEq A]

/-- §15, lines 7 and 7a: **the type of one round on the window**, at an instance that
lands in outcome (1) of Theorem 13.2.1. -/
abbrev Line7DataAt (i : HintedInstance Ω A) (h : Line7Test i) :=
  Line57Data i.inst.Δ A
    (restrictTo (johnsonData h.1.1.2).K i.inst.Δ (johnsonData h.1.1.2).invariant)
    (restrictStr i.inst.Δ i.inst.x) (restrictStr i.inst.Δ i.inst.y)
    (johnsonData h.1.1.2).ϕ (testSetSize i.inst.windowSize)
    (johnsonData h.1.1.2).m
    (1 * (Fintype.card i.inst.Δ + 1) *
      AlignDominantRoundData.alignDominantRoundCost (Fintype.card i.inst.Δ)
      + aggregateRoundCost (Fintype.card i.inst.Δ) (testSetSize i.inst.windowSize)
        (Fintype.card i.inst.Δ))

/-- §15, **lines 5, 7 and 7a: what the branch chooses**.

Line 6's test fails in two ways, and each has its own data.  Outcome (1) of
Theorem 13.2.1 is the colored `4/5`-partition, handed to Procedure Align: what is chosen is
the data of that round (`Babai.Line57Data`).  Outcome (2a) is the Cor. 12.0.10 reduction on
the canonical orbit `C`: what is chosen is the canonical two-coloring and the giant
hypothesis (`Babai.SmallDefectData`), which `Babai.line4bBranch` runs on.  Both are choices
of data; the reduction each outcome runs is a named function of it. -/
structure Line567aChoice (Ω : Type u) (A : Type v) [Fintype Ω] [DecidableEq Ω] [Fintype A]
    [DecidableEq A] where
  /-- Outcome (1): one round of lines 7 and 7a on the window. -/
  outcome1 : ∀ (i : HintedInstance Ω A) (h : Line7Test i), Line7DataAt i h
  /-- Outcome (2a): the data of Cor. 12.0.10, as line 4b uses it. -/
  outcome2a : Line5Case2aChoice Ω A

/-- §15, lines 7 and 7a: **the round on the window at outcome (1)**, chosen once. -/
noncomputable def line7DataOf {i : HintedInstance Ω A} (h : Line7Test i) :
    Line7DataAt i h :=
  Classical.choice (nonempty_line7Core (johnsonData h.1.1.2).transitive
    (johnsonData h.1.1.2).giant
    (veryLargeK_of_hugeM (johnsonData h.1.1.2).transitive (hugeM_of_data h.1.1.2 h.1.2))
    (by have := le_param_of_line4c h.1.1.2 h.1.2; rwa [param_eq h.1.1.2] at this)
    (by
      have h1 := (johnsonData h.1.1.2).param_le
      have h2 := card_window (johnsonData h.1.1.2)
      omega)
    (testSetSize i.inst.windowSize) (five_le_testSetSize _) h.2.choose_spec)

/-- §15, lines 7 and 7a: **`Babai.Line567aChoice` is inhabited** — outcome (1) by
`Babai.nonempty_line7Core`, outcome (2a) by `Babai.nonempty_smallDefectData_case2a`.  This
is the only place where `Classical.choice` enters lines 5, 7 and 7a. -/
noncomputable def line567aChoiceOf : Line567aChoice Ω A where
  outcome1 := fun _ h => line7DataOf h
  outcome2a := fun i h =>
    let E := Classical.choice (aggEnum_nonempty (johnsonData h.1.1).ϕ
      (restrictStr i.inst.Δ i.inst.x) (restrictStr i.inst.Δ i.inst.y)
      (testSetSize i.inst.windowSize))
    { data := Classical.choice (nonempty_smallDefectData_case2a (johnsonData h.1.1)
        (testSetSize i.inst.windowSize) h.2.choose_spec)
      enum := E.val
      enum_spec := E.property }

/-- §15, **lines 5, 7 and 7a** as a branch of the round: outcome (1) is line 7 followed by
Procedure Align, outcome (2a) is the branch of line 4b.  Outside the tests of line 5 the
branch is never taken, and `Babai.line5Case2aFun` leaves `.done I.answer` there. -/
noncomputable def line567aFunCoset (C : Line567aChoice Ω A) (i : HintedInstance Ω A) :
    SIReduction Ω A (Set (Equiv.Perm Ω)) :=
  if h : Line7Test i then
    liftWindow (johnsonData h.1.1.2).K i.inst.Δ (johnsonData h.1.1.2).invariant i.inst.x
      (C.outcome1 i h).toCosetCore.red
  else line5Case2aFunCoset C.outcome2a i

noncomputable def line567aFun (C : Line567aChoice Ω A) (i : HintedInstance Ω A) :
    SIReduction Ω A (Set (Equiv.Perm Ω)) :=
  SIReduction.alignRed i.inst (line567aFunCoset C i)

/-- §15, lines 7 and 7a, **line 11 of Procedure Align**: the hint the branch hands to each
of its calls.  The branch of outcome (2a) shrinks the window and hands down nothing. -/
noncomputable def line567aLift (C : Line567aChoice Ω A) (i : HintedInstance Ω A)
    (J : SIInstance Ω A) : HintedInstance Ω A :=
  if h : Line7Test i then
    ⟨J, cosetWindowHintLift (johnsonData h.1.1.2).invariant i.inst.x
      (C.outcome1 i h).shape.hint J⟩
  else ⟨J, none⟩

@[simp] theorem inst_line567aLift (C : Line567aChoice Ω A) (i : HintedInstance Ω A)
    (J : SIInstance Ω A) : (line567aLift C i J).inst = J := by
  rw [line567aLift]
  split <;> rfl

/-! ### The allowance of line 5: the calls of Procedure AggregateCertificates

`Babai.aggregateRoundCost m t n` is the exact count of Theorem 13.1.3 and Prop. 13.1.11.
The cost of a round of the Master Algorithm has to be a function of the window size alone,
non-decreasing and quasipolynomial, so line 5 is charged a plain bound for it at `m = n` and
`t = Babai.testSetSize n`:

> `6·n^{2t}·t!·n²`.

It dominates because `C(n,t) ≤ n^t`.  Nothing here needs `t ≤ n`: when `t > n` the binomial
coefficient is `0` and the round makes no call at all. -/

section Allowance

/-- `n ↦ n^{c·t(n)}` with `t(n) = 10 + ⌊log₂ n⌋` the test set size of §13.1 is
non-decreasing. -/
theorem pow_mul_testSetSize_mono (c : ℕ) :
    Monotone fun n : ℕ => n ^ (c * testSetSize n) := by
  intro a b hab
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · have : a = 0 := Nat.le_zero.1 hab
    subst this
    exact le_rfl
  · rcases Nat.eq_zero_or_pos a with rfl | ha
    · rcases Nat.eq_zero_or_pos (c * testSetSize 0) with h0 | h0
      · show (0 : ℕ) ^ (c * testSetSize 0) ≤ _
        rw [h0, pow_zero]
        exact Nat.one_le_pow _ _ hb
      · show (0 : ℕ) ^ (c * testSetSize 0) ≤ _
        rw [Nat.zero_pow (by omega)]
        exact Nat.zero_le _
    · have hts : testSetSize a ≤ testSetSize b := by
        rw [testSetSize, testSetSize]
        exact Nat.add_le_add_left (Nat.log_mono_right hab) 10
      calc a ^ (c * testSetSize a) ≤ b ^ (c * testSetSize a) := Nat.pow_le_pow_left hab _
        _ ≤ b ^ (c * testSetSize b) :=
            Nat.pow_le_pow_right hb (Nat.mul_le_mul_left _ hts)

/-- `n^{c·t(n)}` with `t(n) = 10 + ⌊log₂ n⌋` is quasipolynomial: `n ≤ 2^{log₂ n + 2}` and
`t(n) ≤ 10(log₂ n + 2)`, so the exponent is at most `10c·(log₂ n + 2)² ≤
(log₂ n + 2)^{10c+2}`. -/
theorem quasiPolyBound_pow_testSetSize (c : ℕ) :
    RAM.QuasiPolyBound (fun n => n ^ (c * testSetSize n)) := by
  refine ⟨10 * c + 2, fun n => ?_⟩
  set M := Nat.log 2 n + 2 with hM
  have hM2 : 2 ≤ M := by omega
  have hn : n ≤ 2 ^ M := by
    have h := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) n
    exact le_trans (le_of_lt h) (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hstep : n ^ (c * testSetSize n) ≤ 2 ^ (M * (c * testSetSize n)) := by
    calc n ^ (c * testSetSize n) ≤ (2 ^ M) ^ (c * testSetSize n) :=
          Nat.pow_le_pow_left hn _
      _ = 2 ^ (M * (c * testSetSize n)) := by rw [← pow_mul]
  refine le_trans hstep (Nat.pow_le_pow_right (by norm_num) ?_)
  have hts : testSetSize n ≤ 10 * M := by rw [testSetSize, hM]; omega
  have hcM : 10 * c ≤ M ^ (10 * c) :=
    le_trans (le_of_lt Nat.lt_two_pow_self) (Nat.pow_le_pow_left hM2 _)
  calc M * (c * testSetSize n) ≤ M * (c * (10 * M)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hts)
    _ = 10 * c * (M * M) := by ring
    _ ≤ M ^ (10 * c) * (M * M) := Nat.mul_le_mul_right _ hcM
    _ = M ^ (10 * c + 2) := by rw [pow_add]; ring


/-- §15, line 5: **what line 5 is charged** for the certificate and comparison runs of
Procedure AggregateCertificates. -/
def aggregateAllowance (n : ℕ) : ℕ :=
  6 * n ^ (2 * testSetSize n) * (Nat.factorial (testSetSize n) * n ^ 2)

/-- §13.2: the allowance covers the exact count, because `C(n,t) ≤ n^t`. -/
theorem aggregateRoundCost_le_aggregateAllowance (n : ℕ) :
    aggregateRoundCost n (testSetSize n) n ≤ aggregateAllowance n := by
  set t := testSetSize n with ht
  have hc : n.choose t ≤ n ^ t := Nat.choose_le_pow n t
  have hsq : (n.choose t) ^ 2 ≤ n ^ (2 * t) := by
    rw [two_mul, pow_add, pow_two]
    exact Nat.mul_le_mul hc hc
  have h1 : n ^ t ≤ n ^ (2 * t) := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rcases Nat.eq_zero_or_pos t with h0 | h0
      · simp [h0]
      · rw [Nat.zero_pow (by omega)]; exact Nat.zero_le _
    · exact Nat.pow_le_pow_right hn (by omega)
  rw [aggregateRoundCost, aggregateAllowance]
  have hA : 2 * n.choose t * (Nat.factorial t * n ^ 2)
      ≤ 2 * n ^ (2 * t) * (Nat.factorial t * n ^ 2) :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (le_trans hc h1))
  have hB : 2 * (n.choose t) ^ 2 * (2 * Nat.factorial t * n ^ 2)
      ≤ 4 * n ^ (2 * t) * (Nat.factorial t * n ^ 2) := by
    have : 2 * (n.choose t) ^ 2 * (2 * Nat.factorial t * n ^ 2)
        = 4 * (n.choose t) ^ 2 * (Nat.factorial t * n ^ 2) := by ring
    rw [this]
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hsq)
  calc 2 * n.choose t * (Nat.factorial t * n ^ 2)
        + 2 * (n.choose t) ^ 2 * (2 * Nat.factorial t * n ^ 2)
      ≤ 2 * n ^ (2 * t) * (Nat.factorial t * n ^ 2)
        + 4 * n ^ (2 * t) * (Nat.factorial t * n ^ 2) := Nat.add_le_add hA hB
    _ = 6 * n ^ (2 * t) * (Nat.factorial t * n ^ 2) := by ring

theorem testSetSize_mono : Monotone testSetSize := fun _ _ hab => by
  rw [testSetSize, testSetSize]
  exact Nat.add_le_add_left (Nat.log_mono_right hab) 10

/-- §15, line 5: the allowance is non-decreasing. -/
theorem aggregateAllowance_mono : Monotone aggregateAllowance := by
  intro a b hab
  have h1 : a ^ (2 * testSetSize a) ≤ b ^ (2 * testSetSize b) :=
    pow_mul_testSetSize_mono 2 hab
  have h2 : Nat.factorial (testSetSize a) ≤ Nat.factorial (testSetSize b) :=
    Nat.factorial_le (testSetSize_mono hab)
  have h3 : a ^ 2 ≤ b ^ 2 := Nat.pow_le_pow_left hab 2
  rw [aggregateAllowance, aggregateAllowance]
  exact Nat.mul_le_mul (Nat.mul_le_mul_left _ h1) (Nat.mul_le_mul h2 h3)

/-- `t(n)! ≤ 2^{t(n)²}` and `t(n) ≤ 10(log₂ n + 2)`, so `t(n)!` is quasipolynomial. -/
theorem quasiPolyBound_factorial_testSetSize :
    RAM.QuasiPolyBound (fun n => Nat.factorial (testSetSize n)) := by
  refine ⟨9, fun n => ?_⟩
  set L := Nat.log 2 n + 2 with hL
  have hL2 : 2 ≤ L := by omega
  refine le_trans (factorial_le_two_pow_sq (testSetSize n)) ?_
  refine Nat.pow_le_pow_right (by norm_num) ?_
  have ht : testSetSize n ≤ 10 * L := by rw [testSetSize, hL]; omega
  have hsq : testSetSize n * testSetSize n ≤ (10 * L) * (10 * L) :=
    Nat.mul_le_mul ht ht
  have h7 : (128 : ℕ) ≤ L ^ 7 := by
    have := Nat.pow_le_pow_left hL2 7
    simpa using this
  calc testSetSize n * testSetSize n ≤ (10 * L) * (10 * L) := hsq
    _ = 100 * L ^ 2 := by ring
    _ ≤ L ^ 7 * L ^ 2 := Nat.mul_le_mul_right _ (by omega)
    _ = L ^ 9 := by ring

/-- §15, line 5: the allowance is quasipolynomial. -/
theorem quasiPolyBound_aggregateAllowance : RAM.QuasiPolyBound aggregateAllowance := by
  have h : RAM.QuasiPolyBound (fun n =>
      6 * n ^ (2 * testSetSize n) * (Nat.factorial (testSetSize n) * n ^ 2)) :=
    (((RAM.polyBound_const 6).quasiPoly.mul (quasiPolyBound_pow_testSetSize 2)).mul
      (quasiPolyBound_factorial_testSetSize.mul
        ((quasiPolyBound_id.mul quasiPolyBound_id).mono
          (fun n => by rw [pow_two]))))
  exact h.mono fun n => le_of_eq rfl

end Allowance

/-- The number of instances lines 5, 7 and 7a produce: the cost of Procedure Align on the
window, or the cost of the branch of line 4b. -/
def line567aCost (n : ℕ) : ℕ :=
  masterRoundCost n + (n + 1) * AlignDominantRoundData.alignDominantRoundCost n
    + aggregateAllowance n

end Line567aBranch

/-! ### The four facts of lines 5, 7 and 7a

These are the fields `line567a_run`, `line567a_decreases`, `line567a_calls` and
`line567a_group` of `Babai.Sec15Remaining`, with `Babai.line567aFun` for the branch,
`Babai.line567aLift` for the lift and `Babai.line567aCost` for the cost. -/

section Line567aFields

open scoped Classical

variable {Ω : Type u} {A : Type v} [Fintype Ω] [DecidableEq Ω] [Fintype A] [DecidableEq A]

/-- The tests of line 5 that reach outcome (2a) rather than outcome (1). -/
private theorem line5Case2aTest_of {i : HintedInstance Ω A}
    (hgrp : IsGroupInstance i.inst) (hJ : IsJohnson i)
    (hell : ¬ param i ≤ ellOf i.inst.windowSize) (ha : ¬ aggregatesToStructure i)
    (h7 : ¬ Line7Test i) : Case2aInstance i := by
  rcases (not_aggregatesToStructure_iff hJ).1 ha with h1 | h2
  · exact absurd (⟨⟨⟨hgrp, hJ⟩, hell⟩, h1⟩ : Line7Test i) h7
  · exact h2

/-- §15, lines 5, 7 and 7a, **correct**: the branch returns `Iso^Δ_K(x,y)`. -/
theorem line567a_run (C : Line567aChoice Ω A) (i : HintedInstance Ω A) (hgrp : IsGroupInstance i.inst)
    (hJ : IsJohnson i) (hell : ¬ param i ≤ ellOf i.inst.windowSize)
    (hp : ¬ IsPrimitiveCase i) (ha : ¬ aggregatesToStructure i) :
    (line567aFun C i).run = i.inst.answer := by
  by_cases h : Line7Test i
  · rw [line567aFun, line567aFunCoset, dif_pos h]
    exact run_alignLiftWindow_core (C.outcome1 i h).toCosetCore i.inst
      (johnsonData h.1.1.2).isGroup rfl rfl rfl
  · rw [line567aFun, line567aFunCoset, dif_neg h]
    exact line5Case2a_run C.outcome2a i hJ hell
      (line5Case2aTest_of hgrp hJ hell ha h)

/-- §15, lines 5, 7 and 7a: **every call is a group instance**. -/
theorem line567a_group (C : Line567aChoice Ω A) (i : HintedInstance Ω A) (hgrp : IsGroupInstance i.inst)
    (hJ : IsJohnson i) (hell : ¬ param i ≤ ellOf i.inst.windowSize)
    (hp : ¬ IsPrimitiveCase i) (ha : ¬ aggregatesToStructure i) :
    ∀ J ∈ (line567aFun C i).calls, IsGroupInstance J := by
  by_cases h : Line7Test i
  · rw [line567aFun, line567aFunCoset, dif_pos h]
    exact calls_alignLiftWindow_core_group (C.outcome1 i h).toCosetCore i.inst i.inst.x
  · rw [line567aFun, line567aFunCoset, dif_neg h]
    exact line5Case2a_group C.outcome2a i hJ hell
      (line5Case2aTest_of hgrp hJ hell ha h)

/-- §15, lines 5, 7 and 7a, **the progress**: every call has a window of at most `4n/5`
points, or the same window and a Johnson parameter of at most `m/2` — Eq. (73). -/
theorem line567a_decreases (C : Line567aChoice Ω A) (i : HintedInstance Ω A) (hgrp : IsGroupInstance i.inst)
    (hJ : IsJohnson i) (hell : ¬ param i ≤ ellOf i.inst.windowSize)
    (hp : ¬ IsPrimitiveCase i) (ha : ¬ aggregatesToStructure i) :
    ∀ J ∈ (line567aFun C i).calls,
      MakesProgress HintedInstance.win param i (line567aLift C i J) := by
  by_cases h : Line7Test i
  · intro J hJmem
    rw [line567aFun, line567aFunCoset, dif_pos h] at hJmem
    have hcard : Fintype.card i.inst.Δ = i.inst.Δ.ncard := card_window (johnsonData hJ)
    have hwin : HintedInstance.win i = i.inst.Δ.ncard := rfl
    have hwinJ : HintedInstance.win (line567aLift C i J) = J.windowSize :=
      congrArg SIInstance.windowSize (inst_line567aLift C i J)
    have hpar : param i = (johnsonData hJ).m := param_eq hJ
    have hd := decreases_alignLiftWindow_core (C.outcome1 i h).toCosetCore i.inst i.inst.x hcard J hJmem
    rw [show (C.outcome1 i h).toCosetCore.hint = (C.outcome1 i h).shape.hint from rfl] at hd
    have hliftJ : line567aLift C i J =
        ⟨J, cosetWindowHintLift (johnsonData h.1.1.2).invariant i.inst.x
          (C.outcome1 i h).shape.hint J⟩ := by rw [line567aLift, dif_pos h]
    have h217 : 217 ≤ (johnsonData hJ).m := by
      have := le_param_of_line4c hJ hell
      rwa [param_eq hJ] at this
    rcases hd with hsmall | ⟨hle, hpar2⟩
    · exact Or.inl ⟨by rw [hwin]; exact (johnsonData hJ).one_le_windowSize,
        by rw [hwinJ, hwin]; exact hsmall⟩
    · refine Or.inr ⟨by rw [hwinJ, hwin]; exact hle, by omega, ?_⟩
      rw [hliftJ]
      omega
  · intro J hJmem
    rw [line567aFun, line567aFunCoset, dif_neg h] at hJmem
    have hlift : line567aLift C i J = (⟨J, none⟩ : HintedInstance Ω A) := by
      rw [line567aLift, dif_neg h]
    rw [hlift]
    exact line5Case2a_decreases C.outcome2a i hJ hell
      (line5Case2aTest_of hgrp hJ hell ha h) J hJmem

/-- §15, lines 5, 7 and 7a, **the number of instances one round produces**.  Outcome (1)
costs one run of Procedure Align on the window, because Theorem 13.2.1 returns a single
colored partition; outcome (2a) costs what line 4b costs. -/
theorem line567a_calls (C : Line567aChoice Ω A) (i : HintedInstance Ω A) (hgrp : IsGroupInstance i.inst)
    (hJ : IsJohnson i) (hell : ¬ param i ≤ ellOf i.inst.windowSize)
    (hp : ¬ IsPrimitiveCase i) (ha : ¬ aggregatesToStructure i) :
    ((line567aFun C i).calls).length ≤ line567aCost i.inst.windowSize := by
  have hcard : Fintype.card i.inst.Δ = i.inst.windowSize := card_window (johnsonData hJ)
  by_cases h : Line7Test i
  · rw [line567aFun, line567aFunCoset, dif_pos h]
    refine le_trans (calls_length_alignLiftWindow_core (C.outcome1 i h).toCosetCore i.inst i.inst.x) ?_
    rw [hcard, line567aCost, one_mul]
    have := aggregateRoundCost_le_aggregateAllowance i.inst.windowSize
    omega
  · rw [line567aFun, line567aFunCoset, dif_neg h]
    refine le_trans (line5Case2a_calls C.outcome2a i hJ hell
      (line5Case2aTest_of hgrp hJ hell ha h)) ?_
    rw [line567aCost]
    have ha := (aggregateRoundCost_mono_left (johnsonData hJ).param_le
      (t := testSetSize i.inst.windowSize) (n := i.inst.windowSize)).trans
        (aggregateRoundCost_le_aggregateAllowance i.inst.windowSize)
    omega

/-- §15, lines 5, 7 and 7a, **the regression of Finding 3**: when the tests of line 5 lead
to outcome (1), the branch makes at least as many calls as the two phases of Procedure
AggregateCertificates together, on the window.  A branch that read the aggregated objects
without asking String Isomorphism for them would not satisfy `Babai.Line57Data`. -/
theorem line567a_calls_ge_phases (C : Line567aChoice Ω A) (i : HintedInstance Ω A)
    (h : Line7Test i) :
    (certPhaseStrong (johnsonData h.1.1.2).ϕ (restrictStr i.inst.Δ i.inst.x)
          (restrictStr i.inst.Δ i.inst.y) (C.outcome1 i h).enum (Λ := A)).calls.length
        + (comparePhaseStrong (johnsonData h.1.1.2).ϕ (restrictStr i.inst.Δ i.inst.x)
          (restrictStr i.inst.Δ i.inst.y) (C.outcome1 i h).enum
          (Λ := A)).calls.length
      ≤ ((line567aFun C i).calls).length := by
  rw [line567aFun, line567aFunCoset, dif_pos h,
    calls_length_alignRed, calls_liftWindow (johnsonData h.1.1.2).invariant i.inst.x _ (C.outcome1 i h).toCosetCore.calls_K,
    List.length_map]
  exact Line57Shape.calls_length_phases_le_red _ _

end Line567aFields

end Babai

