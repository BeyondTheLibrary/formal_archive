import Workspace.Luks.Defs
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Fintype.Powerset

/-!
# Graph Isomorphism as String Isomorphism

The reduction in Sec. 1.1, just before Corollary 1.1.2, records one bit for each
unordered pair of distinct vertices. A vertex permutation acts on these pairs by
`tAction 2`. We use the same direction as `strIso`: the source bit at `p` equals
the target bit at the image of `p`.

The decision equivalence holds for every number of vertices. The map on witnesses
is a bijection except at degree two, where both vertex permutations fix the only pair.
-/

namespace Babai.GraphToString

open Equiv

/-- The domain has one point for each unordered pair of distinct vertices. -/
abbrev Pairs (n : ℕ) := binom (Fin n) 2

/-- Graph isomorphisms, written as permutations preserving adjacency in both directions. -/
def Iso {n : ℕ} (X Y : SimpleGraph (Fin n)) : Set (Perm (Fin n)) :=
  {σ | ∀ u v, X.Adj u v ↔ Y.Adj (σ u) (σ v)}

/-- A two-element set is an edge when two of its vertices are adjacent. -/
def IsEdge {n : ℕ} (X : SimpleGraph (Fin n)) (p : Pairs n) : Prop :=
  ∃ u ∈ p.val, ∃ v ∈ p.val, X.Adj u v

open Classical in
/-- The binary edge string of a graph. -/
noncomputable def edgeString {n : ℕ} (X : SimpleGraph (Fin n)) (p : Pairs n) : Fin 2 :=
  if IsEdge X p then 1 else 0

/-- The pair with endpoints `u` and `v`. -/
def pair {n : ℕ} (u v : Fin n) (h : u ≠ v) : Pairs n :=
  ⟨{u, v}, by simp [h]⟩

theorem isEdge_pair {n : ℕ} (X : SimpleGraph (Fin n)) (u v : Fin n) (h : u ≠ v) :
    IsEdge X (pair u v h) ↔ X.Adj u v := by
  simp only [IsEdge, pair, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨a, rfl | rfl, b, rfl | rfl, hab⟩
    · exact False.elim (X.irrefl hab)
    · exact hab
    · exact hab.symm
    · exact False.elim (X.irrefl hab)
  · exact fun h => ⟨u, Or.inl rfl, v, Or.inr rfl, h⟩

@[simp] theorem action_pair {n : ℕ} (σ : Perm (Fin n)) (u v : Fin n) (h : u ≠ v) :
    tAction 2 σ (pair u v h) = pair (σ u) (σ v) (σ.injective.ne h) := by
  apply Subtype.ext
  simp [pair, tAction_apply_coe]

theorem edgeString_eq_iff {n : ℕ} (X Y : SimpleGraph (Fin n)) (p q : Pairs n) :
    edgeString X p = edgeString Y q ↔ (IsEdge X p ↔ IsEdge Y q) := by
  classical
  by_cases h : IsEdge X p <;> by_cases h' : IsEdge Y q <;>
    simp [edgeString, h, h']

/-- A permutation preserves adjacency exactly when its action preserves the edge bits. -/
theorem iso_iff_preserves_string {n : ℕ} (X Y : SimpleGraph (Fin n)) (σ : Perm (Fin n)) :
    σ ∈ Iso X Y ↔ ∀ p, edgeString X p = edgeString Y (tAction 2 σ p) := by
  constructor
  · intro h p
    rw [edgeString_eq_iff]
    obtain ⟨u, v, huv, hp⟩ := Finset.card_eq_two.mp p.property
    have hp' : p = pair u v huv := Subtype.ext hp
    rw [hp', action_pair, isEdge_pair, isEdge_pair]
    exact h u v
  · intro h u v
    by_cases huv : u = v
    · subst v
      simp
    · have := h (pair u v huv)
      rwa [action_pair, edgeString_eq_iff, isEdge_pair, isEdge_pair] at this

theorem mem_strIso_iff {n : ℕ} (X Y : SimpleGraph (Fin n)) (π : Perm (Pairs n)) :
    π ∈ strIso (JohnsonS n 2) (edgeString X) (edgeString Y) ↔
      π ∈ JohnsonS n 2 ∧ ∀ p, edgeString X p = edgeString Y (π p) := by
  constructor
  · rintro ⟨hπ, h⟩
    refine ⟨hπ, fun p => ?_⟩
    have := congrFun h (π p)
    simpa [strAct] using this
  · rintro ⟨hπ, h⟩
    refine ⟨hπ, funext fun p => ?_⟩
    simpa [strAct] using h (π⁻¹ p)

/-- The reduction maps a vertex isomorphism to its induced permutation of pairs. -/
def isoMap {n : ℕ} (X Y : SimpleGraph (Fin n)) :
    Iso X Y → strIso (JohnsonS n 2) (edgeString X) (edgeString Y) := fun σ =>
  ⟨tAction 2 σ.val, (mem_strIso_iff X Y _).mpr
    ⟨Subgroup.mem_map.mpr ⟨σ.val, Subgroup.mem_top _, rfl⟩,
      (iso_iff_preserves_string X Y σ.val).mp σ.property⟩⟩

/-- Every string isomorphism in the induced group lifts to a vertex isomorphism. -/
theorem isoMap_surjective {n : ℕ} (X Y : SimpleGraph (Fin n)) :
    Function.Surjective (isoMap X Y) := by
  rintro ⟨π, hπ⟩
  obtain ⟨hG, hstr⟩ := (mem_strIso_iff X Y π).mp hπ
  obtain ⟨σ, _, rfl⟩ := hG
  exact ⟨⟨σ, (iso_iff_preserves_string X Y σ).mpr hstr⟩, rfl⟩

/-- **Corollary 1.1.2, Sec. 1.1, mathematical GI reduction.** For every `n`,
two graphs are isomorphic exactly when their binary strings are isomorphic under
the induced action of the symmetric group on unordered pairs. -/
theorem decision {n : ℕ} (X Y : SimpleGraph (Fin n)) :
    (Iso X Y).Nonempty ↔
      (strIso (JohnsonS n 2) (edgeString X) (edgeString Y)).Nonempty := by
  constructor
  · rintro ⟨σ, hσ⟩
    exact ⟨(isoMap X Y ⟨σ, hσ⟩).val, (isoMap X Y ⟨σ, hσ⟩).property⟩
  · rintro ⟨π, hπ⟩
    obtain ⟨σ, _⟩ := isoMap_surjective X Y ⟨π, hπ⟩
    exact ⟨σ.val, σ.property⟩

/-- The action on pairs is faithful except at degree two. For at least three
vertices, the pairs containing a fixed vertex determine that vertex. -/
theorem action_injective {n : ℕ} (hn : n ≠ 2) :
    Function.Injective (tAction 2 : Perm (Fin n) → Perm (Pairs n)) := by
  intro σ τ hστ
  apply Equiv.ext
  intro u
  by_cases hn' : n ≤ 1
  · apply Fin.ext
    have := (σ u).isLt
    have := (τ u).isLt
    omega
  · have hn3 : 2 < n := by omega
    by_contra hu
    let a := τ⁻¹ (σ u)
    have hau : a ≠ u := by
      intro h
      apply hu
      have := congrArg τ h
      simpa [a] using this
    have hcard : ({u, a} : Finset (Fin n)).card < (Finset.univ : Finset (Fin n)).card := by
      simp [Finset.card_pair (Ne.symm hau), hn3]
    obtain ⟨v, _, hv⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hv
    have hvu : v ≠ u := hv.1
    have hva : v ≠ a := hv.2
    have hp := congrArg (fun π : Perm (Pairs n) => (π (pair u v hvu.symm)).val) hστ
    have hm : σ u ∈ ({τ u, τ v} : Finset (Fin n)) := by
      have hm' : σ u ∈ (tAction 2 σ (pair u v hvu.symm)).val := by simp [pair]
      dsimp only at hp
      rw [hp] at hm'
      simpa [pair] using hm'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with h | h
    · exact hu h
    · exact hva (τ.injective (by simpa [a] using h.symm))

/-- **Corollary 1.1.2, Sec. 1.1, map on GI witnesses.** If `n ≠ 2`, the map
`σ ↦ σ⁽²⁾` is a bijection from graph isomorphisms onto the string isomorphisms.
The decision theorem has no restriction on `n`. -/
theorem isoMap_bijective {n : ℕ} (hn : n ≠ 2) (X Y : SimpleGraph (Fin n)) :
    Function.Bijective (isoMap X Y) := by
  refine ⟨?_, isoMap_surjective X Y⟩
  intro σ τ h
  exact Subtype.ext (action_injective hn (congrArg Subtype.val h))

/-- The string has the number of positions stated in Sec. 1.1. -/
theorem card_pairs (n : ℕ) : Nat.card (Pairs n) = n.choose 2 := by
  rw [Nat.card_congr (binomEquiv (Fin n) 2), Set.powersetCard.card]
  simp

/-- At degree two every vertex permutation fixes the only pair. -/
theorem action_two (σ : Perm (Fin 2)) : tAction 2 σ = 1 := by
  have hp : ∀ p : Pairs 2, p.val = Finset.univ := fun p =>
    p.val.eq_univ_of_card (by simpa using p.property)
  apply Equiv.ext
  intro p
  apply Subtype.ext
  exact (hp _).trans (hp _).symm

/-- The degree-two exception is real: the transposition and identity have the same image. -/
theorem action_two_not_injective :
    ¬Function.Injective (tAction 2 : Perm (Fin 2) → Perm (Pairs 2)) := by
  intro h
  have heq : (Equiv.swap 0 1 : Perm (Fin 2)) = 1 :=
    h ((action_two _).trans (action_two _).symm)
  have := congrArg (fun σ : Perm (Fin 2) => σ 0) heq
  simp at this

end Babai.GraphToString

#print axioms Babai.GraphToString.decision
#print axioms Babai.GraphToString.isoMap_bijective
