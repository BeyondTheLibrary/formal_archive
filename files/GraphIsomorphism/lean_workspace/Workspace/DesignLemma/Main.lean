/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 8.1: the Design Lemma (Theorems 8.1.2 and 8.1.5) and canonicity.
-/
import Workspace.DesignLemma.Correctness
import Workspace.DesignLemma.Canonical
import Workspace.Higher.WLCanonical
import Workspace.Coherent.Classes
import Workspace.Coherent.Constituents

/-!
# §8.1 The Design Lemma

Version 2.5, Section 8.1 (lines 3680–3760 of `babai-gi-source/quasi25.txt`).

## Numbering map

| Paper | Lean |
|---|---|
| Procedure "Design Lemma", line 01 | `Babai.KAryRelStruct.kWL`, `.kWL_isCoherent`, `.aut_kWL` |
| Theorem 8.1.5 (Design lemma, rephrased) | `Babai.KAryRelStruct.theorem_8_1_5` |
| Theorem 8.1.5, "canonicity is relative to `x⃗`" | `Babai.KAryPartStruct.restrTo_canonical`, `.vcolor_canonical`, `.dominantClass_canonical`, `.noDominantColor_canonical`, `.skel2_canonical` (in `DesignLemma/Canonical.lean`) |
| Theorem 8.1.2, "canonicity is relative to `x⃗`", across vertex sets | `Babai.KAryRelStruct.kWL_vcolor_canonical`, `.kWL_dominantClass_canonical`, `.kWL_noDominantColor_canonical`, `.kWL_skel2_canonical`, `.kWL_designPartition_canonical` |
| Theorem 8.1.2, outcome (b), "the connected components of its first disconnected non-diagonal constituent" | `Babai.KAryPartStruct.designPartition` (in `DesignLemma/Canonical.lean`) |
| Observation 8.1.3 | `Babai.DesignAbstract.observation_8_1_3` (in `DesignLemma/Abstract.lean`); for the `k`-WL objects, `Babai.DesignAbstract.observation_8_1_3_kWL` (in `DesignLemma/AbstractKWL.lean`) |
| "Proof of equivalence", 8.1.2 ⇒ 8.1.5 | `Babai.DesignAbstract.theorem_8_1_2_imp_8_1_5` (in `DesignLemma/Abstract.lean`) |
| Theorem 8.1.2 as the statement `DL(α)` | `Babai.DesignAbstract.kwlAssign_canonical`, `.kwlAssign_reaches`, `.theorem_8_1_2_DL` (in `DesignLemma/AbstractKWL.lean`) |
| Theorem 8.1.5 with the objects of the "Proof of equivalence" | `Babai.DesignAbstract.theorem_8_1_5_kWL`, `.theorem_8_1_5_DL` (in `DesignLemma/AbstractKWL.lean`) |
| Remark 8.1.4 | `Babai.KAryRelStruct.remark_8_1_4` |
| Theorem 8.1.2 (Design lemma) | `Babai.KAryRelStruct.theorem_8_1_2` |
| Theorem 8.1.2 as a reduction at a multiplicative cost (§6) | `Babai.designLemma_finds` (in `DesignLemma/Reduction.lean`) |

## Encoding notes

* Line 01 of the procedure, *"apply `k`-WL to `X`"*, is the composite
  `F3 ∘ F2 ∘ F1` of §5.1.3, §5.1.5 and §5.2: `F1` turns the `k`-ary relational structure
  into a `k`-ary partition structure, `F2` into a `k`-ary configuration, and `F3` runs
  `k`-ary WL to stability, producing a `k`-ary coherent configuration.  Each of the three
  preserves isomorphism (`iso_F1`, `iso_F2`, `iso_F3`), so `Aut(kWL(X)) = Aut(X)`
  (`aut_kWL`); this is what licenses the parenthetical remark of line 01, *"henceforth we
  assume `X` is `k`-ary coherent"*, and it is also what transfers the hypothesis
  "symmetry defect `≥ 1 - α`" from `X` to `kWL(X)`.

* *"Canonicity in the above statements is relative to `x⃗`"* is formalized exactly as in
  Prop. 5.2.6 (b) (`Babai.KAryPartStruct.restrict_canonical`): an isomorphism
  `f : X → Y` of the inputs is an isomorphism of the outputs computed at `x⃗` and at
  `x⃗^f`.  The outputs are the vertex-coloring of `X_x⃗` (outcome (i)) and the
  configuration `X* = (X_x⃗)^{(2)}` (outcome (ii)); `restrTo_canonical`,
  `vcolor_canonical` and `skel2_canonical` are the three statements, and
  `dominantClass_canonical`, `noDominantColor_canonical` say that the objects named in
  the two outcomes correspond as well.  §6 needs this for inputs on *different* vertex
  sets; since the `k`-WL color type depends on `|Ω|`, that case goes through a transport
  of the color type (`Workspace/Higher/WLCanonical.lean`) and is the section
  "Canonicity relative to `x⃗` across different vertex sets" below.

* Outcome (b) of Theorem 8.1.2 asks for *a canonical* equipartition, and the paper names
  it: *"the connected components of its first disconnected non-diagonal constituent"*.  It
  is `Babai.KAryPartStruct.designPartition` (`DesignLemma/Canonical.lean`), not an
  existential quantifier: an unnamed nontrivial equipartition of the dominant class exists
  whenever that class has composite size, so the existential form would be too weak.

* The running-time clause *"in time `n^{O(k)}`"* of Theorems 8.1.2 and 8.1.5 is **not**
  stated here; see the corrected paper "pending" entry for §8.

* Observation 8.1.3 (*"if `1 > α' ≥ α ≥ 1/2` then `DL(α')` follows from `DL(α)`"*) and the
  first half of the "Proof of equivalence" (8.1.2 ⇒ 8.1.5) are statements about the
  *abstract* statement `DL(α)`, whose outcomes are "a canonical coloring with …".  They are
  formalized in `Workspace/DesignLemma/Abstract.lean`, which quantifies over canonical
  assignments of colorings, equipartitions and configurations.  The objects of this file
  are such an assignment (`Babai.DesignAbstract.kwlAssign`, colors named by `natRank`), so
  Theorem 8.1.2 here is an instance of `DL(α)` (`theorem_8_1_2_DL`), and Observation 8.1.3
  and Theorem 8.1.5 hold for the objects the paper builds from it
  (`Workspace/DesignLemma/AbstractKWL.lean`).  The observation is used
  nowhere: the paper draws from it only the remark *"it would suffice to prove the Design
  Lemma for `α = 1/2`"*, and Thm. 8.2.1 is proved here for every `α` with `1/2 ≤ α < 1`
  directly.
-/

open scoped Classical

namespace Babai

/-! ### Line 01 of the procedure: `k`-ary Weisfeiler–Leman -/

namespace KAryRelStruct

variable {Ω : Type*} {C : Type} {k : ℕ}

/-- Line 01 of Procedure "Design Lemma" (§8.2): *"apply `k`-WL to `X`"*.  This is the
composite of the three functors of §5: `F1` (§5.1.3) turns the `k`-ary relational
structure into a `k`-ary partition structure, `F2` (§5.1.5) into a `k`-ary configuration,
and `F3` (§5.2, §5.4.1) is `k`-ary WL refinement run to stability. -/
noncomputable def kWL [Fintype Ω] (X : KAryRelStruct Ω C k) :=
  X.F1.F2.F3

/-- Line 01: *"henceforth we assume `X` is `k`-ary coherent"*. -/
theorem kWL_isCoherent [Fintype Ω] (X : KAryRelStruct Ω C k) : X.kWL.IsCoherent :=
  KAryPartStruct.F3_isCoherent _ (KAryPartStruct.F2_isConfiguration _)

/-- Line 01 does not change the automorphism group: `Aut(kWL(X)) = Aut(X)`.  This is
`Iso(X, Y) = Iso(F1 X, F1 Y) = Iso(F2 F1 X, F2 F1 Y) = Iso(F3 F2 F1 X, F3 F2 F1 Y)`
(`iso_F1`, `iso_F2`, `iso_F3`) at `Y = X`. -/
theorem aut_kWL [Fintype Ω] (X : KAryRelStruct Ω C k) : X.kWL.Aut = X.Aut := by
  have h3 : KAryPartStruct.Iso X.F1.F2.F3 X.F1.F2.F3
      = KAryPartStruct.Iso X.F1.F2 X.F1.F2 := KAryPartStruct.iso_F3 X.F1.F2 X.F1.F2
  have h2 : KAryPartStruct.Iso X.F1.F2 X.F1.F2 = KAryPartStruct.Iso X.F1 X.F1 :=
    KAryPartStruct.iso_F2 X.F1 X.F1
  have h1 : KAryPartStruct.Iso X.F1 X.F1 = Iso X X := iso_F1 X X
  ext f
  have hmem : f ∈ KAryPartStruct.Iso X.F1.F2.F3 X.F1.F2.F3 ↔ f ∈ Iso X X := by
    rw [h3, h2, h1]
  constructor
  · intro hf
    exact (hmem.1 hf)
  · intro hf
    exact hmem.2 hf

/-- Remark 8.1.4, §8.1.  *"Let `X*` denote the UPCC obtained in case (c).  If we can
compute `Aut(X*)` then we achieve a major reduction in `Aut(X)` because
`|Aut(X*)| ≤ exp(Õ(√n))` [Ba81].  … Direct computation of `Aut(X*)` can be done in
`exp(Õ(n^{1/3}))` (Sun–Wilmes).  … Rather than relying on the Sun–Wilmes theorem …, we
shall further reduce the UPCC case to Johnson schemes (Split-or-Johnson routine, Sec 9) at
a quasipolynomial multiplicative cost."*

The remark states no mathematical claim that is used: it compares two routes to `Aut(X*)`
and announces §9.  The bound `|Aut(X*)| ≤ exp(Õ(√n))` for a UPCC is Thm. 3.2.4 of §3
([Ba81]), already recorded there; the Sun–Wilmes bound is cited but never used (the paper
explicitly declines to rely on it).  The reference *"(cf. ****)"* for the claim that the
automorphism group of the Johnson scheme `J(k,t)` is the Johnson group `S_k^{(t)}` is a
hole in version 2.5; the intended item is Prop. 3.2.11 (§3.2), `Aut(J(Γ,t)) = S^{(t)}(Γ)`
for the Johnson *graph*, whose metric scheme is the Johnson scheme (Def. 3.2.13).  See
the corrected paper. -/
theorem remark_8_1_4 : True := trivial

/-! ### Theorem 8.1.5 -/

variable [Fintype Ω] [DecidableEq Ω]

/-- Theorem 8.1.5 (Design lemma, rephrased), §8.1.

*"Let `1/2 ≤ α < 1` be a threshold parameter.  Let `X = (Ω, R)` be a `k`-ary relational
structure with `n = |Ω|` vertices, `2 ≤ k ≤ n/2`, and symmetry defect `≥ 1 − α`.  Then in
time `n^{O(k)}` we can find a value `ℓ ≤ k − 1` and a string `x⃗ = x₁ … x_ℓ ∈ Ω^⟨ℓ⟩` of `ℓ`
distinct vertices such that by individualizing each `x_j` we obtain either*

*(i) a canonical coloring of `Ω` with no dominant color, or*

*(ii) a canonical (classical) coherent configuration `X*` on vertex set `Ω` such that the
subconfiguration induced on the dominant vertex-color class of `X*` is not a clique.*

*Canonicity in the above statements is relative to `x⃗`."*

Here the coloring of (i) is the vertex-coloring of the restriction `X_x⃗` of the `k`-ary
coherent configuration `kWL(X)`, and the configuration of (ii) is `X* = (X_x⃗)^{(2)}`; the
disjunction (i) ∨ (ii) is `Returns` (§8.2, lines 04–08).  Canonicity relative to `x⃗` is
`restrTo_canonical`, `vcolor_canonical` and `skel2_canonical`; that the objects named in
(i) and (ii) correspond is `noDominantColor_canonical` and `dominantClass_canonical`.
The `2`-skeleton is a classical coherent configuration by `skel2_isCoherent`.

The running-time clause is pending; see the corrected paper. -/
theorem theorem_8_1_5 {α : ℝ} (hα : 1 / 2 ≤ α) (hα1 : α < 1) (X : KAryRelStruct Ω C k)
    (hk2 : 2 ≤ k) (hkn : 2 * k ≤ Fintype.card Ω)
    (hdef : (1 : ℝ) - α ≤ (defect X.Aut : ℝ)) :
    ∃ (l : ℕ) (hl : l ≤ k - 1) (x : Str Ω l),
      KAryPartStruct.Returns α X.kWL (by omega) x := by
  have hdef' : (1 : ℝ) - α ≤ (defect X.kWL.Aut : ℝ) := by rw [aut_kWL]; exact hdef
  obtain ⟨l, hl, x, hx⟩ :=
    KAryPartStruct.theorem_8_2_1 hα hα1 X.kWL (X.kWL_isCoherent) hk2 hkn hdef'
  exact ⟨l, by omega, x, hx⟩

/-- Theorem 8.1.5, the objects of outcome (ii): `X* = (X_x⃗)^{(2)}` is a classical coherent
configuration on the vertex set `Ω`. -/
theorem skel2_kWL_isCoherent {l : ℕ} (X : KAryRelStruct Ω C k) (hl : l ≤ k)
    (x : Str Ω l) (h2 : 2 ≤ k - l) :
    ((X.kWL.restrTo hl x).skel2 h2).IsCoherent :=
  KAryPartStruct.skel2_isCoherent _ (X.kWL.restrTo_isCoherent X.kWL_isCoherent hl x) h2

end KAryRelStruct

/-! ### Non-vacuity of the hypotheses of Theorems 8.1.2 and 8.1.5 -/

namespace KAryRelStruct

/-- The hypotheses of Theorems 8.1.2 and 8.1.5 are satisfiable: on `Ω = Fin 4` with
`k = 2` and `α = 1/2` the binary structure `Rᵢ = {(i,i)}` has trivial automorphism group,
hence symmetricity `1` and symmetry defect `3/4 ≥ 1 - α`, while `2 ≤ k` and
`2k = 4 ≤ 4 = n`. -/
theorem hypotheses_satisfiable :
    ∃ X : KAryRelStruct (Fin 4) (Fin 4) 2,
      2 ≤ 2 ∧ 2 * 2 ≤ Fintype.card (Fin 4) ∧
        (1 : ℝ) - 1 / 2 ≤ (defect X.Aut : ℝ) := by
  classical
  refine ⟨⟨fun i => {x : Str (Fin 4) 2 | x 0 = i ∧ x 1 = i}⟩, le_rfl, by simp, ?_⟩
  set X : KAryRelStruct (Fin 4) (Fin 4) 2 :=
    ⟨fun i => {x : Str (Fin 4) 2 | x 0 = i ∧ x 1 = i}⟩ with hX
  have haut : ∀ f : Equiv.Perm (Fin 4), f ∈ X.Aut → ∀ v, f v = v := by
    intro f hf v
    have hf' : ∀ (i : Fin 4) (x : Str (Fin 4) 2), x ∈ X.rel i ↔ tupleMap f x ∈ X.rel i := hf
    exact ((hf' v (fun _ => v)).1 ⟨rfl, rfl⟩).1
  have hs : symmetricity X.Aut ≤ 1 := by
    refine Finset.sup_le fun Ψ hΨ => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hΨ
    refine Finset.card_le_one.2 fun a ha b hb => ?_
    by_contra hab
    have h := hΨ a (by simpa using ha) b (by simpa using hb) hab
    have hswap := haut _ h.2 a
    rw [Equiv.swap_apply_left] at hswap
    exact hab hswap.symm
  have hsR : (symmetricity X.Aut : ℝ) ≤ 1 := by exact_mod_cast hs
  unfold defect relSymmetricity
  push_cast
  have hcard : ((Fintype.card (Fin 4) : ℕ) : ℝ) = 4 := by simp
  rw [hcard]
  linarith

end KAryRelStruct

/-! ### Theorem 8.1.2 -/

variable {Ω : Type*}

namespace KAryPartStruct

variable {C : Type*} {m : ℕ} [Fintype Ω] [DecidableEq Ω]

/-- §8.1, second half of the "Proof of equivalence": the dichotomy that turns outcome (ii)
of Theorem 8.1.5 into outcome (b) or (c) of Theorem 8.1.2.

*"In case (ii), let `X* = (Ω, c'')` be the coherent configuration obtained.  If `X*` has no
dominant vertex-color class, we are in case (a).  Otherwise, let `C` denote the dominant
vertex-color class of `X*`.  If `X*[C]` is a UPCC, we are in case (c).  Otherwise, `X*[C]`
is imprimitive; the connected components of its first disconnected non-diagonal
constituent form the required canonical equipartition (Prop. 3.4.4)."*

Here `X* = Y^{(2)}` and `C` is the dominant class of `Y`, which is a vertex-color class of
`X*` (`skel2_vertexClass_eq`), hence a stable set, so `X*[C]` is a homogeneous coherent
configuration (Obs. 3.3.2).  Since `X*[C]` is not a clique and `|C| ≥ 2`, its rank is
`≥ 3` (`three_le_rank_induced`); so `X*[C]` is a UPCC as soon as it is primitive, and
otherwise one of its off-diagonal constituents is disconnected and Prop. 3.4.4 applies
(`homogeneous_disconnected_weakComponents`). -/
theorem imprimitive_or_uniprimitive {α : ℝ} (hα : 1 / 2 ≤ α) (Y : KAryPartStruct Ω C m)
    (hY : Y.IsCoherent) (hm : 2 ≤ m) (hn : 4 ≤ Fintype.card Ω)
    (hdom : HasDominantClass α Y)
    (hclq : ¬ (Y.skel2 hm).IsCliqueOn (dominantClass α Y)) :
    (IsEquipartitionOn (designPartition α Y hm) (dominantClass α Y) ∧
        IsNontrivialPartition (designPartition α Y hm))
      ∨ ((Y.skel2 hm).induced (dominantClass α Y)).IsUniprimitive := by
  classical
  obtain ⟨i, hi⟩ := hdom
  have hCi : dominantClass α Y = Y.vclass i := dominantClass_eq hα Y hi
  -- `|C| > αn ≥ n/2 ≥ 2`
  have hcard : 2 < (dominantClass α Y).ncard := by
    have hn' : (4 : ℝ) ≤ (Fintype.card Ω : ℝ) := by exact_mod_cast hn
    have hmul : (1 / 2 : ℝ) * (Fintype.card Ω : ℝ) ≤ α * (Fintype.card Ω : ℝ) :=
      mul_le_mul_of_nonneg_right hα (by linarith)
    have hlt : α * (Fintype.card Ω : ℝ) < ((dominantClass α Y).ncard : ℝ) := by
      rw [hCi]; exact hi
    have : (2 : ℝ) < ((dominantClass α Y).ncard : ℝ) := by linarith
    exact_mod_cast this
  obtain ⟨u₀, hu₀⟩ : (dominantClass α Y).Nonempty :=
    (Set.ncard_pos (Set.toFinite _)).1 (by omega)
  have hu₀' : Y.vcolor u₀ = i := by rw [hCi] at hu₀; exact hu₀
  -- `C` is a vertex-color class of `X* = Y^{(2)}`, hence stable
  have hC : dominantClass α Y
      = (Y.skel2 hm).vertexClass ((Y.skel2 hm).vcolor u₀) := by
    rw [skel2_vertexClass_eq, hCi, hu₀']
  have hstable : (Y.skel2 hm).IsStable (dominantClass α Y) := by
    rw [hC]; exact PartitionStructure.isStable_vertexClass _ _
  have hScoh : (Y.skel2 hm).IsCoherent := skel2_isCoherent Y hY hm
  have hZcoh : ((Y.skel2 hm).induced (dominantClass α Y)).IsCoherent :=
    PartitionStructure.induced_isCoherent _ hScoh hstable
  have hZhom : ((Y.skel2 hm).induced (dominantClass α Y)).IsHomogeneous := by
    refine PartitionStructure.induced_isHomogeneous _ (fun a ha b hb => ?_)
    rw [hC] at ha hb
    exact ha.trans hb.symm
  have hnt : (dominantClass α Y).Nontrivial := by
    rw [← Set.one_lt_ncard_iff_nontrivial]; omega
  have hrk : ((Y.skel2 hm).induced (dominantClass α Y)).rank ≠ 2 := by
    intro hc
    exact hclq ((PartitionStructure.isCliqueOn_iff _ _ _).2 hc)
  have hrank : 3 ≤ ((Y.skel2 hm).induced (dominantClass α Y)).rank :=
    PartitionStructure.three_le_rank_induced _ hScoh.toIsConfiguration hnt hrk
  by_cases hprim : ∀ j : Fin ((Y.skel2 hm).induced (dominantClass α Y)).rank,
      ((Y.skel2 hm).induced (dominantClass α Y)).IsOffDiagonalColor j →
      (((Y.skel2 hm).induced (dominantClass α Y)).extConstituent j).IsWeaklyConnected
  · exact Or.inr ⟨⟨hZhom, hprim⟩, hrank⟩
  · push_neg at hprim
    obtain ⟨j, hoff, hdisc⟩ := hprim
    exact Or.inl (designPartition_isEquipartitionOn α Y hm hZcoh hZhom
      (exists_isDesignColor α Y hm hoff hdisc))

end KAryPartStruct

namespace KAryRelStruct

variable {C : Type} {k : ℕ} [Fintype Ω] [DecidableEq Ω]

/-- Theorem 8.1.2 (Design lemma), §8.1.

*"Let `1/2 ≤ α < 1` be a threshold parameter.  Let `X = (Ω, R)` be a `k`-ary relational
structure with `n = |Ω|` vertices, `2 ≤ k ≤ n/2`, and symmetry defect `≥ 1 − α`.  Then in
time `n^{O(k)}` we can find a value `ℓ ≤ k − 1` and a string `x⃗ = x₁ … x_ℓ ∈ Ω^⟨ℓ⟩` of `ℓ`
distinct vertices such that by individualizing each `x_j` we obtain either*

*(a) a canonical coloring of `Ω` with no dominant color, or*

*(b) a canonical coloring of `Ω` and a nontrivial canonical equipartition of the dominant
color class, or*

*(c) a canonical coloring of `Ω` and a canonically embedded uniprimitive coherent
configuration (UPCC) whose vertex set is the dominant color class.*

*Canonicity in the above statements is relative to `x⃗`."*

The canonical coloring is in all three cases the vertex-coloring of the restriction
`X_x⃗` of `kWL(X)` (canonical by `restrTo_canonical` and `vcolor_canonical`); the dominant
color class is `dominantClass` (canonical by `dominantClass_canonical`), and the UPCC of
(c) is the subconfiguration of `X* = (X_x⃗)^{(2)}` induced on it (canonical by
`skel2_canonical`).

The running-time clause is pending; see the corrected paper.

The proof is the paper's "proof of equivalence" in §8.1, second half: outcome (i) of
Thm. 8.1.5 is outcome (a), and in case (ii) one splits according to whether the induced
subconfiguration `X*[C]` on the dominant class `C` is uniprimitive — outcome (c) — or
imprimitive, in which case *"the connected components of its first disconnected
non-diagonal constituent form the required canonical equipartition (Prop. 3.4.4)"* —
outcome (b).  The dichotomy is `KAryPartStruct.imprimitive_or_uniprimitive`. -/
theorem theorem_8_1_2 {α : ℝ} (hα : 1 / 2 ≤ α) (hα1 : α < 1) (X : KAryRelStruct Ω C k)
    (hk2 : 2 ≤ k) (hkn : 2 * k ≤ Fintype.card Ω)
    (hdef : (1 : ℝ) - α ≤ (defect X.Aut : ℝ)) :
    ∃ (l : ℕ) (_hl : l ≤ k - 1) (x : Str Ω l), Str.Distinct x ∧
      (KAryPartStruct.NoDominantColor α (X.kWL.restrTo (by omega : l ≤ k) x) ∨
        (∃ _h2 : l + 2 ≤ k,
            KAryPartStruct.HasDominantClass α (X.kWL.restrTo (by omega : l ≤ k) x) ∧
            IsEquipartitionOn
                (KAryPartStruct.designPartition α
                  (X.kWL.restrTo (by omega : l ≤ k) x) (by omega))
                (KAryPartStruct.dominantClass α (X.kWL.restrTo (by omega : l ≤ k) x)) ∧
            IsNontrivialPartition
              (KAryPartStruct.designPartition α
                (X.kWL.restrTo (by omega : l ≤ k) x) (by omega))) ∨
        (∃ _h2 : l + 2 ≤ k,
            KAryPartStruct.HasDominantClass α (X.kWL.restrTo (by omega : l ≤ k) x) ∧
            (((X.kWL.restrTo (by omega : l ≤ k) x).skel2 (by omega)).induced
              (KAryPartStruct.dominantClass α
                (X.kWL.restrTo (by omega : l ≤ k) x))).IsUniprimitive)) := by
  classical
  obtain ⟨l, hl, x, hx⟩ := theorem_8_1_5 hα hα1 X hk2 hkn hdef
  refine ⟨l, hl, x, hx.1, ?_⟩
  rcases hx.2 with hnd | ⟨h2, hdom, hclq⟩
  · exact Or.inl hnd
  have hcoh : (X.kWL.restrTo (by omega : l ≤ k) x).IsCoherent :=
    X.kWL.restrTo_isCoherent X.kWL_isCoherent _ x
  have hn : 4 ≤ Fintype.card Ω := by omega
  rcases KAryPartStruct.imprimitive_or_uniprimitive hα _ hcoh (by omega) hn hdom hclq with
    ⟨hP, hPnt⟩ | huni
  · exact Or.inr (Or.inl ⟨h2, hdom, hP, hPnt⟩)
  · exact Or.inr (Or.inr ⟨h2, hdom, huni⟩)

/-! ### Canonicity relative to `x⃗` across different vertex sets

Theorems 8.1.2 and 8.1.5 end with *"Canonicity in the above statements is relative to
`x⃗`"*.  §6 uses this for inputs on *different* vertex sets: the categories of §9 have
objects over subsets `s, t ⊆ Ω` and morphisms `f : s ≃ t`.  The statements below are
exactly the canonicity statements of `Workspace/DesignLemma/Canonical.lean` for an
isomorphism `f : X → Y` of `k`-ary relational structures with different vertex sets.

The `k`-WL color type depends on `|Ω|` (the number of rounds), so the colors of `kWL(X)`
and of `kWL(Y)` live in types that are equal only propositionally.  Each proof goes
through the run of `k`-WL on `Y` with the number of rounds computed from `Ω`
(`Y.F1.F2.wlIter (Fintype.card (Str Ω k × Str Ω k))`): an isomorphism carries `kWL(X)` to
that structure on the nose (`kWL_iso_aux`, §5.4.1 Eq. (26)), and that structure differs
from `kWL(Y)` only by the transport of `Workspace/Higher/WLCanonical.lean`. -/

section AcrossVertexSets

variable {Ω Ω' : Type*} {C : Type} {k l : ℕ} [Fintype Ω] [DecidableEq Ω]
  [Fintype Ω'] [DecidableEq Ω']

theorem kWL_eq (X : KAryRelStruct Ω C k) :
    X.kWL = X.F1.F2.wlIter (Fintype.card (Str Ω k × Str Ω k)) := rfl

/-- §5.4.1, Eq. (26) for the composite of line 01: an isomorphism `f : X → Y` carries
`kWL(X)` to the `k`-WL refinement of `Y` run for the number of rounds of `Ω`. -/
theorem kWL_iso_aux (X : KAryRelStruct Ω C k) (Y : KAryRelStruct Ω' C k) {f : Ω ≃ Ω'}
    (hf : f ∈ Iso X Y) :
    f ∈ KAryPartStruct.Iso X.kWL
      (Y.F1.F2.wlIter (Fintype.card (Str Ω k × Str Ω k))) := by
  have h12 : f ∈ KAryPartStruct.Iso X.F1.F2 Y.F1.F2 := by
    rw [KAryPartStruct.iso_F2, iso_F1]; exact hf
  have h3 := KAryPartStruct.iso_wlIter X.F1.F2 Y.F1.F2 (Fintype.card (Str Ω k × Str Ω k))
  show f ∈ KAryPartStruct.Iso (X.F1.F2.wlIter (Fintype.card (Str Ω k × Str Ω k))) _
  rw [h3]
  exact h12

/-- The colors of `kWL(Y)` are the colors of the run with the rounds of `Ω`, transported
along the equality of the two round counts. -/
theorem kWL_color_cast (Y : KAryRelStruct Ω' C k)
    (hN : Fintype.card (Str Ω k × Str Ω k) = Fintype.card (Str Ω' k × Str Ω' k))
    (z : Str Ω' k) :
    Y.kWL.color z = cast (congrArg (KAryPartStruct.wlColorType _ k) hN)
      ((Y.F1.F2.wlIter (Fintype.card (Str Ω k × Str Ω k))).color z) :=
  Y.F1.F2.wlIter_color_cast hN z

/-- §8.1: an isomorphism `f : X → Y` is an isomorphism `X_x⃗ → Y_{x⃗^f}` of the two
restrictions, after the transport of the color type. -/
theorem kWL_iso_restrTo (X : KAryRelStruct Ω C k) (Y : KAryRelStruct Ω' C k) {f : Ω ≃ Ω'}
    (hf : f ∈ Iso X Y) (hl : l ≤ k) (x : Str Ω l) :
    f ∈ KAryPartStruct.Iso (X.kWL.restrTo hl x)
      ((Y.F1.F2.wlIter (Fintype.card (Str Ω k × Str Ω k))).restrTo hl (tupleMap f x)) :=
  KAryPartStruct.restrTo_canonical _ _ hl x (kWL_iso_aux X Y hf)

theorem kWL_restrTo_color_cast (Y : KAryRelStruct Ω' C k)
    (hN : Fintype.card (Str Ω k × Str Ω k) = Fintype.card (Str Ω' k × Str Ω' k))
    (hl : l ≤ k) (x' : Str Ω' l) (y : Str Ω' (k - l)) :
    (Y.kWL.restrTo hl x').color y
      = cast (congrArg (KAryPartStruct.wlColorType _ k) hN)
          (((Y.F1.F2.wlIter (Fintype.card (Str Ω k × Str Ω k))).restrTo hl x').color y) :=
  KAryPartStruct.restrTo_color_cast _ (fun z => kWL_color_cast (Ω := Ω) Y hN z) hl x' y

/-- Theorem 8.1.5, outcome (i), across vertex sets: the vertex-coloring of `X_x⃗` is
canonical, in the kernel form (the two colorings take values in different types). -/
theorem kWL_vcolor_canonical (X : KAryRelStruct Ω C k) (Y : KAryRelStruct Ω' C k)
    {f : Ω ≃ Ω'} (hf : f ∈ Iso X Y) (hl : l ≤ k) (x : Str Ω l) (u v : Ω) :
    (Y.kWL.restrTo hl (tupleMap f x)).vcolor (f u)
        = (Y.kWL.restrTo hl (tupleMap f x)).vcolor (f v)
      ↔ (X.kWL.restrTo hl x).vcolor u = (X.kWL.restrTo hl x).vcolor v := by
  have hN := KAryPartStruct.card_str_prod_eq (Ω := Ω) (Ω' := Ω') (k := k) f
  rw [KAryPartStruct.vcolor_cast _ (fun y => kWL_restrTo_color_cast (Ω := Ω) Y hN hl _ y)]
  have hiso := kWL_iso_restrTo X Y hf hl x
  rw [KAryPartStruct.vcolor_canonical _ _ hiso u, KAryPartStruct.vcolor_canonical _ _ hiso v]

/-- Theorem 8.1.2, the dominant color class, across vertex sets. -/
theorem kWL_dominantClass_canonical {α : ℝ} (X : KAryRelStruct Ω C k)
    (Y : KAryRelStruct Ω' C k) {f : Ω ≃ Ω'} (hf : f ∈ Iso X Y) (hl : l ≤ k) (x : Str Ω l) :
    f '' KAryPartStruct.dominantClass α (X.kWL.restrTo hl x)
      = KAryPartStruct.dominantClass α (Y.kWL.restrTo hl (tupleMap f x)) := by
  have hN := KAryPartStruct.card_str_prod_eq (Ω := Ω) (Ω' := Ω') (k := k) f
  rw [KAryPartStruct.dominantClass_cast _
    (fun y => kWL_restrTo_color_cast (Ω := Ω) Y hN hl _ y)]
  exact KAryPartStruct.dominantClass_canonical _ _ (kWL_iso_restrTo X Y hf hl x)

/-- Theorem 8.1.2, outcome (a), across vertex sets: `X_x⃗` has no dominant color exactly
when `Y_{x⃗^f}` has none. -/
theorem kWL_noDominantColor_canonical {α : ℝ} (X : KAryRelStruct Ω C k)
    (Y : KAryRelStruct Ω' C k) {f : Ω ≃ Ω'} (hf : f ∈ Iso X Y) (hl : l ≤ k) (x : Str Ω l) :
    KAryPartStruct.NoDominantColor α (Y.kWL.restrTo hl (tupleMap f x))
      ↔ KAryPartStruct.NoDominantColor α (X.kWL.restrTo hl x) := by
  have hN := KAryPartStruct.card_str_prod_eq (Ω := Ω) (Ω' := Ω') (k := k) f
  rw [KAryPartStruct.noDominantColor_cast _
    (fun y => kWL_restrTo_color_cast (Ω := Ω) Y hN hl _ y)]
  exact (KAryPartStruct.noDominantColor_canonical _ _ (kWL_iso_restrTo X Y hf hl x)).symm

/-- Theorem 8.1.5, outcome (ii), across vertex sets: the configuration
`X* = (X_x⃗)^{(2)}` is canonical. -/
theorem kWL_skel2_canonical (X : KAryRelStruct Ω C k) (Y : KAryRelStruct Ω' C k)
    {f : Ω ≃ Ω'} (hf : f ∈ Iso X Y) (hl : l ≤ k) (h2 : 2 ≤ k - l) (x : Str Ω l) :
    ((X.kWL.restrTo hl x).skel2 h2).IsColorIso
      ((Y.kWL.restrTo hl (tupleMap f x)).skel2 h2) f := by
  have hN := KAryPartStruct.card_str_prod_eq (Ω := Ω) (Ω' := Ω') (k := k) f
  rw [KAryPartStruct.skel2_cast _ (fun y => kWL_restrTo_color_cast (Ω := Ω) Y hN hl _ y)]
  exact KAryPartStruct.skel2_canonical _ _ h2 (kWL_iso_restrTo X Y hf hl x)

/-- Theorem 8.1.2, outcome (b), across vertex sets: the equipartition of the dominant
class is canonical.  `f` carries the blocks of the design partition of `X_x⃗` onto the
blocks of the design partition of `Y_{x⃗^f}`. -/
theorem kWL_designPartition_canonical {α : ℝ} (X : KAryRelStruct Ω C k)
    (Y : KAryRelStruct Ω' C k) {f : Ω ≃ Ω'} (hf : f ∈ Iso X Y) (hl : l ≤ k) (h2 : 2 ≤ k - l)
    (x : Str Ω l) :
    KAryPartStruct.designPartition α (Y.kWL.restrTo hl (tupleMap f x)) h2
      = (fun A : Set Ω => f '' A) ''
          KAryPartStruct.designPartition α (X.kWL.restrTo hl x) h2 := by
  have hN := KAryPartStruct.card_str_prod_eq (Ω := Ω) (Ω' := Ω') (k := k) f
  rw [KAryPartStruct.designPartition_cast _
    (fun y => kWL_restrTo_color_cast (Ω := Ω) Y hN hl _ y)]
  exact KAryPartStruct.designPartition_canonical (kWL_iso_restrTo X Y hf hl x)

end AcrossVertexSets

end KAryRelStruct

end Babai
