/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 2.5: the complement of a uniform hypergraph.
-/
import Workspace.Prelim.Hypergraphs

/-!
# §2.5  The complement of a uniform hypergraph

The paper never names this operation, but §9.7 needs it.  Case 3 of §9.7 applies the
Design Lemma (Theorem 8.1.2) to the neighborhood hypergraph `H` *"viewed as a `d₁`-ary
relational structure"*, and Theorem 8.1.2 requires the arity to be at most half the number
of vertices — a check §9.7 does not make, and which `d₁` need not satisfy.  The repair is
to run Case 3 on the **complement**

`H^c = (V, 𝓔^c)`,  `𝓔^c = {V ∖ E | E ∈ 𝓔}`,

whenever `d₁ > |V|/2`.  See the entry *"§9.7 Case 3: the Design Lemma is applied at rank
`d₁` without checking `d₁ ≤ n₂/2`"* in the corrected paper.

What this file proves is exactly what that repair uses: `H^c` is `(|V| − d)`-uniform
(`Babai.Hypergraph.compl_isUniform`), it is simple when `H` is
(`Babai.Hypergraph.compl_isSimple`), and it has the **same automorphism group** as `H`
(`Babai.Hypergraph.aut_compl`), hence the same twins and the same symmetry defect
(`Babai.Hypergraph.isTwin_compl`, `Babai.Hypergraph.defect_compl`).

## Numbering map

| Paper | Lean |
|---|---|
| `H^c = {V ∖ E | E ∈ 𝓔}` (unnamed; §9.7, Case 3) | `Babai.Hypergraph.compl` |
| `Aut(H^c) = Aut(H)` | `Babai.Hypergraph.aut_compl` |
| Def. 2.5.6 for `H^c` | `Babai.Hypergraph.isTwin_compl`, `Babai.Hypergraph.defect_compl` |
-/

namespace Babai

namespace Hypergraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The **complement** of a hypergraph on a finite vertex set: the same index set of
edges, with each edge `E` replaced by `V ∖ E`. -/
def compl (H : Hypergraph V) : Hypergraph V where
  numEdges := H.numEdges
  edge i := Finset.univ \ H.edge i

@[simp] theorem compl_numEdges (H : Hypergraph V) : (compl H).numEdges = H.numEdges := rfl

@[simp] theorem compl_edge (H : Hypergraph V) (i : Fin H.numEdges) :
    (compl H).edge i = Finset.univ \ H.edge i := rfl

/-- Complementing is an involution. -/
theorem compl_compl (H : Hypergraph V) : compl (compl H) = H := by
  obtain ⟨n, e⟩ := H
  refine congrArg (Hypergraph.mk n) (funext fun i => ?_)
  ext x
  simp [compl]

/-- The complement of a `d`-uniform hypergraph is `(|V| − d)`-uniform. -/
theorem compl_isUniform {H : Hypergraph V} {d : ℕ} (hu : H.IsUniform d) :
    (compl H).IsUniform (Fintype.card V - d) := by
  intro i
  show (Finset.univ \ H.edge i).card = Fintype.card V - d
  rw [Finset.card_univ_diff, hu i]

/-- The complement of a simple hypergraph is simple: `E ↦ V ∖ E` is injective. -/
theorem compl_isSimple {H : Hypergraph V} (hs : H.IsSimple) : (compl H).IsSimple := by
  intro i j hij
  refine hs ?_
  have h : Finset.univ \ H.edge i = Finset.univ \ H.edge j := hij
  ext x
  have hx := Finset.ext_iff.1 h x
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hx
  exact not_iff_not.1 hx

/-- Complementing an edge commutes with a permutation of the vertices. -/
theorem image_sdiff_univ (σ : Equiv.Perm V) (A : Finset V) :
    (Finset.univ \ A).image σ = Finset.univ \ A.image σ := by
  ext x
  simp only [Finset.mem_image, Finset.mem_sdiff, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rintro ⟨z, hz, hzy⟩
    exact hy (by rwa [← σ.injective hzy])
  · intro hx
    exact ⟨σ.symm x, fun h => hx ⟨σ.symm x, h, by simp⟩, by simp⟩

/-- The multiplicity of `A` in the complement is the multiplicity of `V ∖ A` in `H`. -/
theorem mult_compl (H : Hypergraph V) (A : Finset V) :
    (compl H).mult A = H.mult (Finset.univ \ A) := by
  have h : ∀ i : Fin H.numEdges,
      (Finset.univ \ H.edge i = A) ↔ (H.edge i = Finset.univ \ A) := by
    intro i
    constructor
    · intro hA; subst hA; ext x; simp
    · intro hA; rw [hA]; ext x; simp
  classical
  rw [mult, mult]
  congr 1
  exact Finset.filter_congr fun i _ => h i

/-- **`Aut(H^c) = Aut(H)`.**  A permutation of the vertices commutes with complementation
inside `V`, so it preserves the multiplicity function of `H^c` exactly when it preserves
that of `H`. -/
theorem aut_compl (H : Hypergraph V) : (compl H).Aut = H.Aut := by
  ext σ
  constructor
  · intro hσ A
    have h := hσ (Finset.univ \ A)
    rw [mult_compl, mult_compl, image_sdiff_univ] at h
    have hAA : Finset.univ \ (Finset.univ \ A.image σ) = A.image σ := by ext x; simp
    have hBB : Finset.univ \ (Finset.univ \ A) = A := by ext x; simp
    rwa [hAA, hBB] at h
  · intro hσ A
    rw [mult_compl, mult_compl, ← image_sdiff_univ]
    exact hσ (Finset.univ \ A)

/-- Def. 2.5.6 for the complement: `H` and `H^c` have the same twins. -/
theorem isTwin_compl (H : Hypergraph V) (x y : V) :
    (compl H).IsTwin x y ↔ H.IsTwin x y := by
  rw [Hypergraph.IsTwin, Hypergraph.IsTwin, aut_compl]

/-- Def. 2.5.6 for the complement: `H` and `H^c` have the same relative symmetry
defect. -/
theorem defect_compl (H : Hypergraph V) : (compl H).defect = H.defect := by
  rw [Hypergraph.defect, Hypergraph.defect, aut_compl]

end Hypergraph

end Babai
