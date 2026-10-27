/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 5.4: the superseded definitions, compared with the revised ones of §5.1–§5.2.
-/
import Workspace.Higher.Coherent

/-!
# §5.4 `k`-ary configurations — the superseded definitions

Version 2.5 carries §5.4 under the heading *"k-ary configurations — OLD — REMOVE THIS
SUBSECTION"*.  Its Definitions 5.4.1, 5.4.3 and 5.4.4 are superseded by Definitions 5.1.7,
5.1.8 and 5.2.2, and §5.4 is not formalized as definitions.  This file records how the two
sets of definitions compare, because §5.4 is still referred to elsewhere in the paper
(Prop. 5.1.11 cites Def. 5.4.1, and Obs. 5.4.5 is the old form of Prop. 5.2.3).  See
the corrected paper, §5.4.

Summary of the comparison, proved below.

* **Skeleton.**  Def. 5.4.1 sets `R^{(t)} = {(x₁,…,x_t) | (x₁,…,x_t,x_t,…,x_t) ∈ R}`.  The
  padding of Def. 5.1.6 is exactly `(x₁,…,x_t,x_t,…,x_t)`, so the old and the new skeleton
  (Def. 5.1.7) are the same map (`skeleton_color_eq_old`).  The two definitions differ only
  in that Def. 5.1.7 requires `1 ≤ ℓ`, which Def. 5.4.1 does not: for `t = 0` the old
  definition is empty of content.
* **Configuration.**  Def. 5.4.3(ii) is Def. 5.1.8(i) (`old_axiom_ii_iff_rho`).
  Def. 5.4.3(iii) quantifies over `π ∈ S_k`, i.e. over the *permutations* of the
  coordinates, while Def. 5.1.8(ii) quantifies over the whole monoid `𝔐_k` of maps
  `[k] → [k]`.  So Def. 5.1.8 is the stronger axiom: `isConfiguration_old_axiom_iii` gives
  one implication, and the other fails (a coloring can be invariant under all coordinate
  permutations without the color of `x⃗` determining the color of a repeated-coordinate
  string `τ(x⃗)`; this is the mismatch the revision repairs, and it is why Def. 5.4.3 is
  the obsolete one).  Def. 5.4.3(i) ("the `Rᵢ` partition `Ω^k` and all the `Rᵢ` are
  nonempty") is `KAryPartStruct` together with `IsFull`.
* **Coherence.**  Def. 5.4.4(iv) and Def. 5.2.2(iii) are the same condition, written with
  the parameters indexed as `p(i₀,…,i_k)` and as `γ(i⃗ j)` respectively
  (`oldCoherentAxiom_iff`).
* **Observation 5.4.5** ("for all `t ≤ k`, the `t`-skeleton of a `k`-ary coherent
  configuration is a `t`-ary coherent configuration") is Prop. 5.2.3 for the revised
  definitions, proved as `Babai.KAryPartStruct.skeleton_isCoherent`; `observation_5_4_5`
  below is that statement under the old numbering.

## Numbering map

| Paper | Lean |
|---|---|
| Definition 5.4.1 (`t`-skeleton) | `Babai.KAryPartStruct.skeleton_color_eq_old` |
| Definition 5.4.3(ii) | `Babai.KAryPartStruct.old_axiom_ii_iff_rho` |
| Definition 5.4.3(iii) | `Babai.KAryPartStruct.OldAxiomIII`, `.isConfiguration_old_axiom_iii` |
| Definition 5.4.4(iv), Eq. (39) | `Babai.KAryPartStruct.OldCoherentAxiom`, `.oldCoherentAxiom_iff` |
| Observation 5.4.5 | `Babai.KAryPartStruct.observation_5_4_5` |
-/

namespace Babai

namespace KAryPartStruct

variable {Ω : Type*} {C : Type*} {k l : ℕ}

/-- Definition 5.4.1 (`t`-skeleton).  "For `R ⊆ Ω^k` and `t ≤ k` let
`R^{(t)} = {(x₁,…,x_t) | (x₁,…,x_t,x_t,…,x_t) ∈ R}`."

The string `(x₁,…,x_t,x_t,…,x_t)` is the padding of Def. 5.1.6, so the `t`-skeleton of
Def. 5.4.1 is the skeleton of Def. 5.1.7. -/
theorem skeleton_color_eq_old (X : KAryPartStruct Ω C k) (hl : 0 < l) (hlk : l ≤ k)
    (x : Str Ω l) :
    (X.skeleton hl hlk).color x
      = X.color (fun j : Fin k =>
          if hj : (j : ℕ) < l then x ⟨j, hj⟩ else x ⟨l - 1, by omega⟩) := by
  refine congrArg X.color (funext fun j => ?_)
  by_cases hj : (j : ℕ) < l
  · rw [dif_pos hj]
    exact Str.pad_apply_of_lt hl x hj
  · rw [dif_neg hj]
    exact Str.pad_apply_of_ge hl x (by omega)

/-- Definition 5.4.3(ii).  "If `c(x₁,…,x_k) = c(x'₁,…,x'_k)` then
`(∀i,j ≤ k)(xᵢ = xⱼ ⟺ x'ᵢ = x'ⱼ)`."  This is axiom (i) of Def. 5.1.8. -/
theorem old_axiom_ii_iff_rho {X : KAryPartStruct Ω C k} (h : X.IsConfiguration)
    (x y : Str Ω k) (hxy : X.color x = X.color y) (i j : Fin k) :
    x i = x j ↔ y i = y j :=
  h.rho x y hxy i j

/-- Definition 5.4.3(iii).  "`(∀π ∈ S_k)(∀i ≤ r)(∃j ≤ r)(Rᵢ^π = Rⱼ)`", written for the
coloring: the color of `x⃗` determines the color of `x⃗` with its coordinates permuted. -/
def OldAxiomIII (X : KAryPartStruct Ω C k) : Prop :=
  ∀ (x y : Str Ω k) (π : Equiv.Perm (Fin k)), X.color x = X.color y →
    X.color (Str.idx π x) = X.color (Str.idx π y)

/-- Definition 5.4.3(iii) follows from Definition 5.1.8(ii): the latter quantifies over the
whole monoid `𝔐_k`, the former only over the permutations `S_k ⊆ 𝔐_k`. -/
theorem isConfiguration_old_axiom_iii {X : KAryPartStruct Ω C k} (h : X.IsConfiguration) :
    X.OldAxiomIII := fun x y π hxy => h.idx x y (fun j => π j) hxy

/-- Definition 5.4.4(iv), Eq. (39).  "There exists a family of `r^{k+1}` nonnegative
integer intersection numbers `p(i₀,…,i_k)` such that for all `x⃗ ∈ R_{i₀}` we have
`|{y ∈ Ω | (∀j ≤ k)(c(x⃗ʲ(y)) = iⱼ)}| = p(i₀,…,i_k)`." -/
def OldCoherentAxiom (X : KAryPartStruct Ω C k) : Prop :=
  ∃ p : C → Str C k → ℕ, ∀ (i₀ : C) (i : Str C k) (x : Str Ω k), X.color x = i₀ →
    {y : Ω | ∀ j : Fin k, X.color (Str.subst x j y) = i j}.ncard = p i₀ i

/-- Definition 5.4.4(iv) and Definition 5.2.2(iii) are the same condition: the families
`p(i₀, i⃗)` and `γ(i⃗ i₀)` differ only in the order of the arguments. -/
theorem oldCoherentAxiom_iff (X : KAryPartStruct Ω C k) :
    X.OldCoherentAxiom ↔ ∃ γ : Str C k → C → ℕ, ∀ (i : Str C k) (j : C) (x : Str Ω k),
      X.color x = j → {z : Ω | ∀ t : Fin k, X.color (Str.subst x t z) = i t}.ncard = γ i j := by
  constructor
  · rintro ⟨p, hp⟩
    exact ⟨fun i j => p j i, fun i j x hx => hp j i x hx⟩
  · rintro ⟨γ, hγ⟩
    exact ⟨fun j i => γ i j, fun i₀ i x hx => hγ i i₀ x hx⟩

/-- Observation 5.4.5.  "For all `t ≤ k`, the `t`-skeleton of a `k`-ary coherent
configuration is a `t`-ary coherent configuration."

Restated for the revised definitions (Def. 5.1.7 and Def. 5.2.2), where it is Prop. 5.2.3;
the hypothesis `1 ≤ t` is the one Def. 5.1.7 carries. -/
theorem observation_5_4_5 [Fintype Ω] [Fintype C] {X : KAryPartStruct Ω C k}
    (h : X.IsCoherent) (hl : 0 < l) (hlk : l ≤ k) : (X.skeleton hl hlk).IsCoherent :=
  X.skeleton_isCoherent h hl hlk

end KAryPartStruct

end Babai
