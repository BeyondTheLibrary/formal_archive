/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 5.2, "Classical coherent configurations": the case k = 2 of §5 is the notion of §3.
-/
import Workspace.Higher.Coherent
import Workspace.Coherent.Basic

/-!
# `k = 2`: the bridge between §5 and §3

§5.2 says: *"Classical coherent configurations.  We refer to the case `k = 2` (2-ary
coherent configurations, the case studied by Weisfeiler and Leman) as 'classical coherent
configurations'.  So for `k ≥ 2`, the 2-skeleton `X^{(2)}` of a `k`-ary coherent
configuration `X` is a classical coherent configuration."*

This file proves that assertion: the `2`-ary coherent configurations of Def. 5.2.2 are
exactly the coherent configurations of Def. 3.1.11 (`isCoherent_toKAry_iff`), and
therefore the `2`-skeleton of a `k`-ary coherent configuration is one
(`skeleton_two_isCoherent`).

## Configurations do *not* correspond

For *configurations* the two definitions differ, and Def. 5.1.8 is strictly the stronger
one: Def. 3.1.2 has only the two axioms "a diagonal color forces `x = y`" and "the color
of `(x,y)` determines the color of `(y,x)`", while Def. 5.1.8 (ii) applied to the constant
maps `τᵢ ∈ 𝔐₂` also forces vertex-color awareness (Obs. 5.1.10), which for classical
configurations is *not* an axiom but a theorem about *coherent* configurations
(Obs. 3.3.4, `Babai.PartitionStructure.vcolor_eq_of_color_eq`).
`twoVertexExample` is a two-vertex counterexample, checked by `decide`:
`Ω = {0,1}`, `c(0,0) = 0`, `c(1,1) = 1`, `c(0,1) = c(1,0) = 2`.  See the corrected paper
(cross-section mismatch in 2.5, Def. 3.1.2 vs Def. 5.1.8).

## Numbering map

| Paper | Lean |
|---|---|
| §5.2 "classical coherent configurations", `k = 2` | `Babai.PartitionStructure.isCoherent_toKAry_iff` |
| §5.2 "the 2-skeleton of a `k`-ary coherent configuration is a classical coherent configuration" | `Babai.KAryPartStruct.skeleton_two_isCoherent` |
| Def. 3.1.2 vs Def. 5.1.8 | `Babai.twoVertexExample`, `.isConfiguration`, `.not_isKAryConfiguration` |
-/

namespace Babai

variable {Ω C C' : Type*} {k : ℕ}

/-! ### The two definitions at `k = 2` -/

namespace PartitionStructure

variable (X : PartitionStructure Ω)

/-- A binary partition structure (Def. 3.1.1) read as a `2`-ary partition structure
(§5.1.3): the color of the string `x₁x₂` is the color of the edge `(x₁, x₂)`. -/
def toKAry : KAryPartStruct Ω (Fin X.rank) 2 := ⟨fun x => X.color (x 0) (x 1)⟩

@[simp] theorem toKAry_color (x : Str Ω 2) : X.toKAry.color x = X.color (x 0) (x 1) := rfl

theorem toKAry_isFull : X.toKAry.IsFull := by
  intro i
  obtain ⟨x, y, hxy⟩ := X.color_surjective i
  exact ⟨![x, y], hxy⟩

@[simp] theorem toKAry_subst_zero (x : Str Ω 2) (z : Ω) :
    X.toKAry.color (Str.subst x 0 z) = X.color z (x 1) := by
  rw [toKAry_color, Str.subst_same, Str.subst_of_ne _ (by decide)]

@[simp] theorem toKAry_subst_one (x : Str Ω 2) (z : Ω) :
    X.toKAry.color (Str.subst x 1 z) = X.color (x 0) z := by
  rw [toKAry_color, Str.subst_same, Str.subst_of_ne _ (by decide)]

/-- The counting condition of Def. 5.2.2 (iii) at `k = 2` is the counting condition of
Def. 3.1.11 (iii), with the two colors exchanged: `x⃗¹(z) = (z, x₂)` and
`x⃗²(z) = (x₁, z)`. -/
theorem toKAry_count_set (x : Str Ω 2) (i : Str (Fin X.rank) 2) :
    {z : Ω | ∀ t : Fin 2, X.toKAry.color (Str.subst x t z) = i t}
      = {z : Ω | X.color (x 0) z = i 1 ∧ X.color z (x 1) = i 0} := by
  ext z
  simp only [Set.mem_setOf_eq, Fin.forall_fin_two, toKAry_subst_zero, toKAry_subst_one]
  exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

/-- Every `2`-ary configuration (Def. 5.1.8) is a configuration in the sense of
Def. 3.1.2. -/
theorem isConfiguration_of_toKAry (h : X.toKAry.IsConfiguration) : X.IsConfiguration where
  diag x y z hxyz := by
    have hc : X.toKAry.color ![x, y] = X.toKAry.color ![z, z] := hxyz
    have := (h.rho _ _ hc 0 1).2 rfl
    simpa using this
  converse u v x y huv := by
    have hc : X.toKAry.color ![u, v] = X.toKAry.color ![x, y] := huv
    have := h.idx ![u, v] ![x, y] ![1, 0] hc
    simpa [Str.idx] using this

/-- Every coherent configuration (Def. 3.1.11) is a `2`-ary configuration (Def. 5.1.8).
Axiom (ii) for the constant maps `τ ∈ 𝔐₂` is vertex-color awareness, which for classical
configurations needs coherence (Obs. 3.3.4). -/
theorem toKAry_isConfiguration (h : X.IsCoherent) : X.toKAry.IsConfiguration where
  rho x y hxy i j := by
    have hc : X.color (x 0) (x 1) = X.color (y 0) (y 1) := hxy
    have key : ∀ (u v : Str Ω 2), X.color (u 0) (u 1) = X.color (v 0) (v 1) →
        u 0 = u 1 → v 0 = v 1 := by
      intro u v huv h01
      refine h.diag (v 0) (v 1) (u 0) ?_
      rw [← huv, h01]
    have hiff : (x 0 = x 1) ↔ (y 0 = y 1) := ⟨key x y hc, key y x hc.symm⟩
    have hcase : ∀ a : Fin 2, a = 0 ∨ a = 1 := by decide
    rcases hcase i with rfl | rfl <;> rcases hcase j with rfl | rfl
    · exact ⟨fun _ => rfl, fun _ => rfl⟩
    · exact hiff
    · exact ⟨fun h1 => (hiff.1 h1.symm).symm, fun h1 => (hiff.2 h1.symm).symm⟩
    · exact ⟨fun _ => rfl, fun _ => rfl⟩
  idx x y τ hxy := by
    have hc : X.color (x 0) (x 1) = X.color (y 0) (y 1) := hxy
    have hv := X.vcolor_eq_of_color_eq h hc
    have hconv : X.color (x 1) (x 0) = X.color (y 1) (y 0) :=
      h.converse _ _ _ _ hc
    have h2 : ∀ a b : Fin 2, X.color (x a) (x b) = X.color (y a) (y b) := by
      intro a b
      fin_cases a <;> fin_cases b
      · exact hv.1
      · exact hc
      · exact hconv
      · exact hv.2
    exact h2 (τ 0) (τ 1)

/-- The `k = 2` bridge.  A binary partition structure is a coherent configuration in the
sense of Def. 3.1.11 if and only if it is a `2`-ary coherent configuration in the sense of
Def. 5.2.2.  This is the paper's identification of the case `k = 2` of §5 with the
classical notion of §3. -/
theorem isCoherent_toKAry_iff : X.toKAry.IsCoherent ↔ X.IsCoherent := by
  constructor
  · intro h
    refine ⟨X.isConfiguration_of_toKAry h.toIsConfiguration, ?_⟩
    obtain ⟨γ, hγ⟩ := h.intersection
    refine ⟨fun a b k => γ ![b, a] k, ?_⟩
    intro a b kk x y hxy
    have hc : X.toKAry.color ![x, y] = kk := hxy
    have hcount := hγ ![b, a] kk ![x, y] hc
    rw [X.toKAry_count_set ![x, y] ![b, a]] at hcount
    show {z : Ω | X.color x z = a ∧ X.color z y = b}.ncard = γ ![b, a] kk
    rw [← hcount]
    norm_num
  · intro h
    refine ⟨X.toKAry_isConfiguration h, ?_⟩
    obtain ⟨p, hp⟩ := h.intersection
    refine ⟨fun i j => p (i 1) (i 0) j, ?_⟩
    intro i j x hx
    rw [X.toKAry_count_set x i]
    have hc : X.color (x 0) (x 1) = j := hx
    have hcount := hp (i 1) (i 0) j (x 0) (x 1) hc
    show {z : Ω | X.color (x 0) z = i 1 ∧ X.color z (x 1) = i 0}.ncard = p (i 1) (i 0) j
    rw [← hcount]

end PartitionStructure

namespace KAryPartStruct

/-- §5.2, "Classical coherent configurations": *"So for `k ≥ 2`, the 2-skeleton `X^{(2)}`
of a `k`-ary coherent configuration `X` is a classical coherent configuration."*

The `2`-skeleton is a `2`-ary partition structure; read as a binary partition structure
(Def. 3.1.1) by renaming its colors, `Babai.PartitionStructure.ofColoring`, it is a
coherent configuration in the sense of Def. 3.1.11. -/
theorem skeleton_two_isCoherent [Fintype Ω] [Fintype C] [DecidableEq C]
    (X : KAryPartStruct Ω C k) (h : X.IsCoherent) (hk : 2 ≤ k) :
    (PartitionStructure.ofColoring
      (fun u v : Ω => (X.skeleton (by norm_num) hk).color ![u, v])).IsCoherent := by
  classical
  set Y := X.skeleton (by norm_num : (0:ℕ) < 2) hk with hY
  set Z := PartitionStructure.ofColoring
    (fun u v : Ω => Y.color ![u, v]) with hZ
  have hYc : Y.IsCoherent := X.skeleton_isCoherent h (by norm_num) hk
  have heta : ∀ x : Str Ω 2, x = ![x 0, x 1] := by
    intro x
    funext i
    fin_cases i <;> rfl
  have hker : ∀ x y : Str Ω 2, Y.color x = Y.color y ↔ Z.toKAry.color x = Z.toKAry.color y := by
    intro x y
    show Y.color x = Y.color y ↔ Z.color (x 0) (x 1) = Z.color (y 0) (y 1)
    rw [hZ, PartitionStructure.ofColoring_color_eq_iff, ← heta x, ← heta y]
  exact (Z.isCoherent_toKAry_iff).1 (isCoherent_congr hker hYc)

end KAryPartStruct

/-! ### Def. 3.1.2 is strictly weaker than Def. 5.1.8 -/

/-- Two vertices, three colors: `c(0,0) = 0`, `c(1,1) = 1`, `c(0,1) = c(1,0) = 2`.  This is
a configuration in the sense of Def. 3.1.2 but not a `2`-ary configuration in the sense of
Def. 5.1.8. -/
def twoVertexExample : PartitionStructure (Fin 2) where
  rank := 3
  color x y := if x = y then (if x = 0 then 0 else 1) else 2
  color_surjective := by decide

theorem twoVertexExample_isConfiguration : twoVertexExample.IsConfiguration where
  diag := by decide
  converse := by decide

/-- The coloring of `twoVertexExample` is not vertex-color aware: the two edges `(0,1)` and
`(1,0)` have the same color while their tails have different colors.  So Def. 5.1.8 is
strictly stronger than Def. 3.1.2 at `k = 2`. -/
theorem twoVertexExample_not_isKAryConfiguration :
    ¬ twoVertexExample.toKAry.IsConfiguration := by
  intro h
  have hc : twoVertexExample.toKAry.color ![0, 1] = twoVertexExample.toKAry.color ![1, 0] := by
    decide
  have hidx := h.idx ![0, 1] ![1, 0] ![0, 0] hc
  revert hidx
  decide

end Babai
