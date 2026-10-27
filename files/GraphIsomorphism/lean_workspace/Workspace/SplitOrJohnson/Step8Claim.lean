/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 9.4, step 8: the Claim *"There are no `X`-twins in `V₁`"*.
-/
import Workspace.SplitOrJohnson.Step8
import Workspace.SplitOrJohnson.BlkCases

/-!
# §9.4, step 8, the Claim

Version 2.5, lines 4161-4163 of `babai-gi-source/quasi25.txt`.

> *"Claim.  There are no `X`-twins in `V₁`.  Proof.  This follows from the 'no twins in
> primitive color' theorem (Theorem 3.4.11), given that `X₁` is primitive."*

## What the Claim says here

At this point of §9.4 the configuration `X` lives on the vertex set `V₁ ∪ V₂`, it is
bihomogeneous, `X₁` is a UPCC and the link `X₁₂` is nontrivial.  *"`X`-twins"* are twins of
`Aut(X)`, the group of the permutations of the vertex set that preserve the coloring of
`X`; that group is `Babai.ColorAut` of the coloring, which is exactly the group in which
the field `Babai.IsBlockDesignCase.noTwins₁` reads its twins.

Theorem 3.4.11 (`Babai.PartitionStructure.no_twins_in_primitive_color`) forbids twins of a
single bipartite **constituent** `X_k = (V₁, V₂; R_k)`, provided `X_k` is nontrivial and
`X₁` is primitive.  The two statements meet in one step: a permutation that preserves the
whole coloring preserves each constituent, so an `X`-twin pair is an `X_k`-twin pair for
every `k`.  The `k` to use is the color of any pair of the link: it is nonempty by
construction, and it is not all of `V₁ × V₂` because the link carries a second color —
which is what *"the link `X₁₂` is nontrivial"* says.  So the Claim needs nothing beyond the
`Case` heading of step 9 together with the primitivity of `X₁`.

| Paper | Lean |
|---|---|
| §9.4, step 8, the Claim, in the `Case` of step 9 | `Babai.claim_9_4_step8_case` |
| §9.4, step 8, the Claim, at the instance step 8 leaves | `Babai.claim_9_4_step8_at` |

`Babai.claim_9_4_step8_at` is the hypothesis `hnoTwins` of
`Babai.isBlockDesignCase_induced`, the `Case` of §9.7.
-/

namespace Babai

/-! ### The Claim in the `Case` of step 9 -/

section Case

variable {V : Type} [Fintype V] [DecidableEq V] (P : PartitionStructure V)

/-- §9.4, step 8.  **The Claim of step 8**: *"There are no `X`-twins in `V₁`."*  Stated for
a coherent configuration `P` with two distinct vertex-color classes `Ω_i`, `Ω_j` such that
the link between them is nontrivial (two pairs of `Ω_i × Ω_j` get different colors) and the
induced configuration `P[Ω_i]` is primitive.

*"Proof.  This follows from the 'no twins in primitive color' theorem (Theorem 3.4.11),
given that `X₁` is primitive."*

The color `k` of Theorem 3.4.11 is the color of the pair `(x₁, y₁)` of the link.  Its
constituent is nonempty, since it holds that pair, and it is not all of `Ω_i × Ω_j`, since
the pair `(x₂, y₂)` has another color; that is the nontriviality that Theorem 3.4.11 asks
for.  A permutation that preserves the coloring of `P` preserves the constituent `R_k` and
fixes `Ω_j` pointwise when it is the transposition of two points of `Ω_i`, so a twin pair
of `Aut(P)` inside `Ω_i` has the same `R_k`-neighbourhood, hence is a twin pair of the
bipartite constituent, which Theorem 3.4.11 forbids. -/
theorem claim_9_4_step8_case (hP : P.IsCoherent) {i j : Fin P.rank} (hij : i ≠ j)
    [instV : Fintype ↥(P.vertexClass i)]
    (hprim : (P.induced (P.vertexClass i)).IsPrimitive)
    {x₁ x₂ : ↥(P.vertexClass i)} {y₁ y₂ : ↥(P.vertexClass j)}
    (hlink : P.natColor (x₁ : V) (y₁ : V) ≠ P.natColor (x₂ : V) (y₂ : V)) :
    ∀ x ∈ P.vertexClass i, ∀ y ∈ P.vertexClass i,
      ¬ IsTwin (ColorAut P.natColor) x y := by
  classical
  -- the color of the link pair `(x₁, y₁)`
  set k : Fin P.rank := P.color (x₁ : V) (y₁ : V) with hk
  have hti : P.tailColor k = i := by
    have := P.vcolor_fst_eq hP (y := (y₁ : V)) (k := k) rfl
    rw [← this]; exact x₁.2
  have hhd : P.headColor k = j := by
    have := P.vcolor_snd_eq hP (x := (x₁ : V)) (k := k) rfl
    rw [← this]; exact y₁.2
  have hij' : P.tailColor k ≠ P.headColor k := by rw [hti, hhd]; exact hij
  -- `x₁` and `y₁` seen in the tail and head classes of `k`
  have hx₁ : (x₁ : V) ∈ P.vertexClass (P.tailColor k) := by rw [hti]; exact x₁.2
  have hy₁ : (y₁ : V) ∈ P.vertexClass (P.headColor k) := by rw [hhd]; exact y₁.2
  have hx₂ : (x₂ : V) ∈ P.vertexClass (P.tailColor k) := by rw [hti]; exact x₂.2
  have hy₂ : (y₂ : V) ∈ P.vertexClass (P.headColor k) := by rw [hhd]; exact y₂.2
  -- the constituent of `k` is nontrivial: it holds `(x₁, y₁)` and misses `(x₂, y₂)`
  have hcol₂ : P.color (x₂ : V) (y₂ : V) ≠ k := by
    intro hc
    exact hlink ((P.natColor_eq_iff (x₁ : V) (y₁ : V) (x₂ : V) (y₂ : V)).2 (hc.symm ▸ hk).symm)
  have hnt : ¬ (P.bipConstituent k).IsTrivial := by
    rintro (hemp | huniv)
    · have hmem : ((⟨(x₁ : V), hx₁⟩ : P.vertexClass (P.tailColor k)),
          (⟨(y₁ : V), hy₁⟩ : P.vertexClass (P.headColor k))) ∈ (P.bipConstituent k).E :=
        P.mem_bipConstituent.2 rfl
      rw [hemp] at hmem
      exact hmem
    · have hmem : ((⟨(x₂ : V), hx₂⟩ : P.vertexClass (P.tailColor k)),
          (⟨(y₂ : V), hy₂⟩ : P.vertexClass (P.headColor k))) ∈ (P.bipConstituent k).E := by
        rw [huniv]; trivial
      exact hcol₂ (P.mem_bipConstituent.1 hmem)
  -- the primitivity of `X₁`, read at the tail class of `k`
  have hprim' : ∀ inst : Fintype ↥(P.vertexClass (P.tailColor k)),
      (@PartitionStructure.induced V P (P.vertexClass (P.tailColor k)) inst).IsPrimitive := by
    rw [hti]
    intro inst
    have hinst : inst = instV := Subsingleton.elim _ _
    subst hinst
    exact hprim
  -- now the Claim
  rintro x hx y hy ⟨hxy, hswap⟩
  have hxk : x ∈ P.vertexClass (P.tailColor k) := by rw [hti]; exact hx
  have hyk : y ∈ P.vertexClass (P.tailColor k) := by rw [hti]; exact hy
  -- the transposition preserves the coloring, hence the colors of `P`
  have hcolor : ∀ a b : V,
      P.color (Equiv.swap x y a) (Equiv.swap x y b) = P.color a b := by
    intro a b
    exact (P.natColor_eq_iff _ _ a b).1 (hswap a b)
  -- it fixes `Ω_j` pointwise, so the two `R_k`-neighbourhoods agree
  have hfix : ∀ z : V, z ∈ P.vertexClass (P.headColor k) → Equiv.swap x y z = z := by
    intro z hz
    have hzj : P.vcolor z = j := by rw [← hhd]; exact hz
    refine Equiv.swap_apply_of_ne_of_ne ?_ ?_
    · intro hc
      refine hij ?_
      have h1 : P.vcolor z = i := by rw [hc]; exact hx
      rw [← h1]; exact hzj
    · intro hc
      refine hij ?_
      have h1 : P.vcolor z = i := by rw [hc]; exact hy
      rw [← h1]; exact hzj
  have hnbr : P.nbr k x = P.nbr k y := by
    have key : ∀ a b : V, a ∈ P.vertexClass (P.tailColor k) →
        b ∈ P.vertexClass (P.tailColor k) → Equiv.swap x y a = b →
        P.nbr k a ⊆ P.nbr k b := by
      intro a b _ _ hab z hz
      have hzhd : z ∈ P.vertexClass (P.headColor k) := P.vcolor_snd_eq hP hz
      have := hcolor a z
      rw [hab, hfix z hzhd] at this
      show P.color b z = k
      rw [this]; exact hz
    refine Set.Subset.antisymm ?_ ?_
    · exact key x y hxk hyk (Equiv.swap_apply_left x y)
    · exact key y x hyk hxk (Equiv.swap_apply_right x y)
  exact P.no_twins_in_primitive_color hP k hij' hnt (hprim' _) hxk hyk hxy
    ((P.isTwin_bipConstituent_iff hP k hxk hyk hxy).2 hnbr)

end Case

/-! ### The Claim at the instance that step 8 leaves -/

section Step8

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] (X : Pt (BipBlockInputs Ω))

/-- §9.4, step 8.  **The Claim of step 8 at the instance step 8 leaves**: *"There are no
`X`-twins in `V₁`."*

The three inputs of `Babai.claim_9_4_step8_case` are available after step 8: the two parts
are the two vertex-color classes of the new configuration (`Babai.step8Config_parts`), the
link is still nontrivial (`Babai.step8_link_nontrivial`), and `X₁` is still primitive
(`Babai.step8_induced_isUniprimitive`, whose first half is the primitivity).

This is the hypothesis `hnoTwins` of `Babai.isBlockDesignCase_induced`, the `Case` of
§9.7. -/
theorem claim_9_4_step8_at (h : ¬ AllClassesSmall X) (himp : ¬ Step6Imprimitive X)
    [Fintype ↥(step7Set X)] [Fintype ↥((step8Obj X).vtx)]
    {i₀ j₀ : Fin (step8Config X).rank} (hij : i₀ ≠ j₀)
    (hV₁ : step8Pts X = (step8Config X).vertexClass i₀)
    (hV₂ : step8Blks X = (step8Config X).vertexClass j₀)
    (hcover : ∀ u : ↥((step8Obj X).vtx), u ∈ (step8Config X).vertexClass i₀
      ∨ u ∈ (step8Config X).vertexClass j₀) :
    ∀ u ∈ (step8Config X).vertexClass i₀, ∀ v ∈ (step8Config X).vertexClass i₀,
      ¬ IsTwin (ColorAut (step8Config X).natColor) u v := by
  classical
  obtain ⟨u₁, hu₁, v₁, hv₁, u₂, hu₂, v₂, hv₂, hne⟩ := step8_link_nontrivial X h
  have hprim : ((step8Config X).induced ((step8Config X).vertexClass i₀)).IsPrimitive :=
    (step8_induced_isUniprimitive X h himp hV₁ hV₂ hcover).1
  refine claim_9_4_step8_case (step8Config X) (step8Config_isCoherent X) hij hprim
    (x₁ := ⟨u₁, hV₁ ▸ hu₁⟩) (y₁ := ⟨v₁, hV₂ ▸ hv₁⟩)
    (x₂ := ⟨u₂, hV₁ ▸ hu₂⟩) (y₂ := ⟨v₂, hV₂ ▸ hv₂⟩) ?_
  intro hc
  exact hne ((step8Config_color_eq_iff X u₁ v₁ u₂ v₂).1 hc)

end Step8

end Babai
