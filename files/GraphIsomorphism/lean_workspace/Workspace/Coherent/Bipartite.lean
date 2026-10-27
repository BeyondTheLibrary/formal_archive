/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 3.4.4: Bipartite configurations, sections, links, bihomogeneous coherent
configurations.
-/
import Workspace.Coherent.Basic

/-!
# §3.4.4 Bipartite configurations, sections, links

## Numbering map

| Paper | Lean |
|---|---|
| Definition 3.4.20 | `Babai.BipConfiguration`, `.rel`, `.constituent`, `.IsTrivial`, `.inv` |
| Definition 3.4.21 | `Babai.PartitionStructure.inducedBipConfig`, `.IsInvolved` |
| §3.4.4 homogeneous section, link | `Babai.PartitionStructure.homogeneousSection`, `.link` |
| Observation 3.4.22 | `.isInvolved_link_iff`, `.link_isTrivial_iff` |
| Notation 3.4.23 | `.homogeneousSection` (`Xᵢ`), `.link` (`X_ij`) |
| Definition 3.4.24 | `.IsBihomogeneous` |
-/

namespace Babai

/-- Definition 3.4.20 (Bipartite configuration).  "By a (binary) *bipartite
configuration* `X = (Ω₁, Ω₂; R₁,…,R_t)` we mean a binary relational structure on the
disjoint union `Ω = Ω₁ ∪̇ Ω₂` such that the relations `Rᵢ` are non-empty and they
partition `Ω₁ × Ω₂`.  This is equivalent to coloring the edges of the complete bipartite
graph `(Ω₁, Ω₂; Ω₁ × Ω₂)`, i.e., a function `c : Ω₁ × Ω₂ → [t]`; here `c(x,y) = i`
exactly if `(x,y) ∈ Rᵢ`." -/
structure BipConfiguration (A B : Type*) where
  /-- The number `t` of colors. -/
  rank : ℕ
  /-- The coloring `c : Ω₁ × Ω₂ → [t]`. -/
  color : A → B → Fin rank
  /-- "the relations `Rᵢ` are non-empty". -/
  color_surjective : ∀ i : Fin rank, ∃ a b, color a b = i

namespace BipConfiguration

variable {A B : Type*} (X : BipConfiguration A B)

/-- Definition 3.4.20.  `Rᵢ = c⁻¹(i) ⊆ Ω₁ × Ω₂`. -/
def rel (i : Fin X.rank) : Set (A × B) := {p | X.color p.1 p.2 = i}

/-- Definition 3.4.20.  "We call the bipartite graph `Xᵢ = (Ω₁, Ω₂; Rᵢ)` the *color-`i`
constituent* of `X`." -/
def constituent (i : Fin X.rank) : BipGraph A B := ⟨X.rel i⟩

/-- Definition 3.4.20.  "We say that the bipartite configuration `X` is *trivial* if
`t = 1` (there is just one color)." -/
def IsTrivial : Prop := X.rank = 1

/-- Definition 3.4.20, restated: a bipartite configuration is trivial exactly if both
sides are nonempty and the coloring is constant. -/
theorem isTrivial_iff_color_const : X.IsTrivial ↔
    ((Nonempty A ∧ Nonempty B) ∧ ∀ (a a' : A) (b b' : B), X.color a b = X.color a' b') := by
  constructor
  · intro h
    have h0 : (0 : ℕ) < X.rank := by rw [h]; norm_num
    obtain ⟨a, b, -⟩ := X.color_surjective ⟨0, h0⟩
    have h1 : X.rank = 1 := h
    have hsub : Subsingleton (Fin X.rank) := by rw [h1]; infer_instance
    exact ⟨⟨⟨a⟩, ⟨b⟩⟩, fun a a' b b' => Subsingleton.elim _ _⟩
  · rintro ⟨⟨⟨a⟩, ⟨b⟩⟩, hconst⟩
    have hle : ∀ i : Fin X.rank, i = X.color a b := by
      intro i
      obtain ⟨a', b', hab'⟩ := X.color_surjective i
      rw [← hab']
      exact hconst a' a b' b
    have hne : Nonempty (Fin X.rank) := ⟨X.color a b⟩
    have hsub : Subsingleton (Fin X.rank) := ⟨fun x y => (hle x).trans (hle y).symm⟩
    rw [IsTrivial, ← Fintype.card_fin X.rank]
    exact Fintype.card_eq_one_iff.2 ⟨X.color a b, hle⟩

/-- Definition 3.4.20.  "If we reverse every edge, we obtain the bipartite configuration
`X⁻ = (Ω₂, Ω₁; R₁⁻,…,R_t⁻)`." -/
def inv : BipConfiguration B A where
  rank := X.rank
  color b a := X.color a b
  color_surjective i := by
    obtain ⟨a, b, hab⟩ := X.color_surjective i
    exact ⟨b, a, hab⟩

end BipConfiguration

namespace PartitionStructure

variable {Ω : Type*} (X : PartitionStructure Ω) [Fintype Ω] [DecidableEq Ω]

open scoped Classical in
/-- Definition 3.4.21 (Induced bipartite subconfiguration).  "Let `X = (Ω; R₁,…,R_r)` be a
configuration.  Let `A` and `B` be disjoint subsets of `Ω` and let
`K = {k ∈ [r] | R_k ∩ (A × B) ≠ ∅}`.  We define the *induced bipartite
subconfiguration* `X[A,B]` as the bipartite configuration
`X[A,B] = (A, B; R_k ∩ (A × B) | k ∈ K)`, Eq. (20)."

Dropping the colors outside `K` is exactly what the renumbering below does: the colors of
`X[A,B]` are the colors of `X` that occur on `A × B`. -/
noncomputable def inducedBipConfig (A B : Set Ω) : BipConfiguration A B where
  rank := (Finset.univ.image fun p : A × B => X.color (p.1 : Ω) (p.2 : Ω)).card
  color a b := (Finset.univ.image fun p : A × B => X.color (p.1 : Ω) (p.2 : Ω)).equivFin
    ⟨X.color (a : Ω) (b : Ω), Finset.mem_image.2 ⟨(a, b), Finset.mem_univ _, rfl⟩⟩
  color_surjective i := by
    obtain ⟨⟨c, hc⟩, hci⟩ :=
      (Finset.univ.image fun p : A × B => X.color (p.1 : Ω) (p.2 : Ω)).equivFin.surjective i
    obtain ⟨⟨a, b⟩, -, rfl⟩ := Finset.mem_image.1 hc
    exact ⟨a, b, hci⟩

/-- The colors of `X[A,B]` are exactly the colors of `X` restricted to `A × B`. -/
theorem inducedBipConfig_color_eq_iff (A B : Set Ω) (a a' : A) (b b' : B) :
    (X.inducedBipConfig A B).color a b = (X.inducedBipConfig A B).color a' b' ↔
      X.color (a : Ω) (b : Ω) = X.color (a' : Ω) (b' : Ω) := by
  classical
  constructor
  · intro hc
    exact congrArg Subtype.val
      ((Finset.univ.image fun p : A × B =>
        X.color (p.1 : Ω) (p.2 : Ω)).equivFin.injective hc)
  · intro hc
    exact congrArg (Finset.univ.image fun p : A × B =>
      X.color (p.1 : Ω) (p.2 : Ω)).equivFin (Subtype.ext hc)

/-- Definition 3.4.21.  "We say that `R_k` (or the color `k`) is *involved* in `X[A,B]`
if `k ∈ K`", i.e. if `R_k ∩ (A × B) ≠ ∅`. -/
def IsInvolved (A B : Set Ω) (k : Fin X.rank) : Prop :=
  (X.rel k ∩ (A ×ˢ B)).Nonempty

/-- §3.4.4, Notation 3.4.23.  "We call the induced homogeneous coherent configuration
`X[Ωᵢ]` the *homogeneous section* of `X` in color `i`"; written `Xᵢ`. -/
noncomputable def homogeneousSection (i : Fin X.rank) :
    PartitionStructure (X.vertexClass i) :=
  X.induced (X.vertexClass i)

/-- §3.4.4, Notation 3.4.23.  "We call the induced bipartite subconfiguration
`X[Ωᵢ, Ω_j]` the *link* between the two homogeneous sections `X[Ωᵢ]` and `X[Ω_j]`, or the
link between vertex colors `i` and `j`"; written `X_ij`. -/
noncomputable def link (i j : Fin X.rank) :
    BipConfiguration (X.vertexClass i) (X.vertexClass j) :=
  X.inducedBipConfig (X.vertexClass i) (X.vertexClass j)

/-- Observation 3.4.22.  "Let `X` be a coherent configuration.  The color `k` is involved
in the link between vertex colors `i` and `j` if and only if `R_k ⊆ Ωᵢ × Ω_j`." -/
theorem isInvolved_link_iff (h : X.IsCoherent) (i j : Fin X.rank) (k : Fin X.rank) :
    X.IsInvolved (X.vertexClass i) (X.vertexClass j) k ↔
      X.rel k ⊆ X.vertexClass i ×ˢ X.vertexClass j := by
  constructor
  · rintro ⟨⟨a, b⟩, hab, ha, hb⟩
    rintro ⟨x, y⟩ hxy
    have hc : X.color x y = X.color a b := by
      rw [show X.color x y = k from hxy, show X.color a b = k from hab]
    obtain ⟨h1, h2⟩ := X.vcolor_eq_of_color_eq h hc
    exact ⟨show X.vcolor x = i by rw [show X.vcolor x = X.vcolor a from h1]; exact ha,
      show X.vcolor y = j by rw [show X.vcolor y = X.vcolor b from h2]; exact hb⟩
  · intro hsub
    obtain ⟨p, hp⟩ := X.rel_nonempty k
    exact ⟨p, hp, hsub hp⟩

/-- Observation 3.4.22.  "The link is trivial exactly if
`(∃k ∈ [r])(R_k = Ωᵢ × Ω_j)`." -/
theorem link_isTrivial_iff (h : X.IsCoherent) (i j : Fin X.rank) (hij : i ≠ j) :
    (X.link i j).IsTrivial ↔ ∃ k : Fin X.rank, X.rel k = X.vertexClass i ×ˢ X.vertexClass j := by
  rw [link, BipConfiguration.isTrivial_iff_color_const]
  constructor
  · rintro ⟨⟨⟨a⟩, ⟨b⟩⟩, hconst⟩
    -- the color `k = c(a,b)` of the (unique) color class of the link
    refine ⟨X.color (a : Ω) (b : Ω), ?_⟩
    have hsub : X.rel (X.color (a : Ω) (b : Ω)) ⊆ X.vertexClass i ×ˢ X.vertexClass j :=
      (X.isInvolved_link_iff h i j _).1 ⟨((a : Ω), (b : Ω)), rfl, a.2, b.2⟩
    refine Set.Subset.antisymm hsub ?_
    rintro ⟨u, v⟩ ⟨hu, hv⟩
    exact ((X.inducedBipConfig_color_eq_iff (X.vertexClass i) (X.vertexClass j)
      ⟨u, hu⟩ a ⟨v, hv⟩ b).1 (hconst ⟨u, hu⟩ a ⟨v, hv⟩ b) :
      X.color u v = X.color (a : Ω) (b : Ω))
  · rintro ⟨k, hk⟩
    have hne : (X.vertexClass i ×ˢ X.vertexClass j).Nonempty := by
      rw [← hk]; exact X.rel_nonempty k
    obtain ⟨⟨a, b⟩, ha, hb⟩ := hne
    refine ⟨⟨⟨⟨a, ha⟩⟩, ⟨⟨b, hb⟩⟩⟩, fun u u' v v' => ?_⟩
    rw [X.inducedBipConfig_color_eq_iff]
    have hcol : ∀ (p : X.vertexClass i) (q : X.vertexClass j), X.color (p : Ω) (q : Ω) = k :=
      fun p q => (hk ▸ ⟨p.2, q.2⟩ : ((p : Ω), (q : Ω)) ∈ X.rel k)
    rw [hcol u v, hcol u' v']

/-- Definition 3.4.24 (Bihomogeneous coherent configuration).  "We say that the coherent
configuration is *bihomogeneous* if it has two vertex-color classes." -/
def IsBihomogeneous : Prop :=
  {i : Fin X.rank | (X.vertexClass i).Nonempty}.ncard = 2

end PartitionStructure

end Babai
