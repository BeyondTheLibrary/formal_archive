/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Sections 2.3 and 5.1.2: the two readings of "`k`-ary relational structure".
-/
import Workspace.Higher.Configurations
import Workspace.Prelim.Structures

/-!
# From `RelStructure` to `KAryRelStruct`

Definition 2.3.1 writes a relational structure as `X = (Ω; R₁,…,R_r)`: a *list* of
relations, each with its own arity (`Babai.RelStructure`).  §5.1.2 writes a `k`-ary
relational structure as `X = (Ω, R)` with `R = (Rᵢ : i ∈ C)`: a family of `k`-ary
relations indexed by a fixed color set `C` (`Babai.KAryRelStruct`).  §8 and §9 are about
the same objects, but the two theorems are stated in the two different readings:
`Babai.KAryStructures` (the category of §9.2) has the first, `Babai.KAryRelStruct.theorem_8_1_2`
has the second.

This file is the translation.  The color set is taken to be `ℕ`, the *same* for every
object: the color `i` names the `i`-th relation of the list when `i < r`, and the empty
relation when `i ≥ r`.  Taking `C := Fin r` would make the color type depend on the
object, and then two isomorphic objects would have color types that are equal only
propositionally; with `C := ℕ` there is nothing to transport.  The padding by empty
relations changes nothing: it is preserved by every bijection, so the automorphism group
is unchanged (`toKAry_aut`), which is what carries the hypothesis "symmetry defect
`≥ 1 − α`" of Theorems 8.1.2 and 8.1.5 from one reading to the other.

## Numbering map

| Paper | Lean |
|---|---|
| Def. 2.3.1 read as §5.1.2 | `Babai.RelStructure.toKAry` |
| Def. 2.3.4 in the two readings agree | `Babai.RelStructure.toKAry_iso` |
| Def. 2.3.16: `Aut`, hence `defect`, is unchanged | `Babai.RelStructure.toKAry_aut`, `.defect_toKAry` |
-/

namespace Babai

namespace RelStructure

variable {Ω Ω' : Type*} {k : ℕ}

/-- A relation of arity `m` read as a relation of arity `k`, when `m = k`.  This is a
reindexing of the coordinates, not a transport of the type of sets, so it needs no
`cast`. -/
def reindexRel {m k : ℕ} (h : m = k) (R : Set (Str Ω m)) : Set (Str Ω k) :=
  {x | (fun j : Fin m => x (Fin.cast h j)) ∈ R}

@[simp] theorem mem_reindexRel {m k : ℕ} (h : m = k) (R : Set (Str Ω m)) (x : Str Ω k) :
    x ∈ reindexRel h R ↔ (fun j : Fin m => x (Fin.cast h j)) ∈ R := Iff.rfl

/-- The inverse reindexing: a string of length `m` read as a string of length `k`. -/
theorem reindexRel_mem_iff {m k : ℕ} (h : m = k) (R : Set (Str Ω m)) (y : Str Ω m) :
    (fun j : Fin k => y (Fin.cast h.symm j)) ∈ reindexRel h R ↔ y ∈ R := by
  have : (fun j : Fin m => (fun j' : Fin k => y (Fin.cast h.symm j')) (Fin.cast h j)) = y := by
    funext j
    exact congrArg y (Fin.ext rfl)
  rw [mem_reindexRel, this]

/-- Definition 2.3.1 read in the form of §5.1.2: a `k`-ary relational structure
`X = (Ω; R₁,…,R_r)` as a family of `k`-ary relations indexed by `ℕ`, the color `i` naming
`Rᵢ₊₁` for `i < r` and the empty relation for `i ≥ r`. -/
def toKAry (X : RelStructure Ω) (h : X.IsKAry k) : KAryRelStruct Ω ℕ k where
  rel i := if hi : i < X.numRel then reindexRel (h ⟨i, hi⟩) (X.rel ⟨i, hi⟩) else ∅

theorem toKAry_rel_of_lt (X : RelStructure Ω) (h : X.IsKAry k) {i : ℕ}
    (hi : i < X.numRel) :
    (X.toKAry h).rel i = reindexRel (h ⟨i, hi⟩) (X.rel ⟨i, hi⟩) := dif_pos hi

theorem toKAry_rel_of_ge (X : RelStructure Ω) (h : X.IsKAry k) {i : ℕ}
    (hi : ¬ i < X.numRel) : (X.toKAry h).rel i = ∅ := dif_neg hi

/-- Definition 2.3.4 in the two readings agree: a bijection `σ` with `X^σ = Y` is an
isomorphism of the two `k`-ary structures of §5.1.2. -/
theorem toKAry_iso {X : RelStructure Ω} {Y : RelStructure Ω'} (hX : X.IsKAry k)
    (hY : Y.IsKAry k) {f : Ω ≃ Ω'} (hf : X.map (f : Ω → Ω') = Y) :
    f ∈ KAryRelStruct.Iso (X.toKAry hX) (Y.toKAry hY) := by
  subst hf
  intro i x
  by_cases hi : i < X.numRel
  · have hi' : i < (X.map (f : Ω → Ω')).numRel := hi
    rw [toKAry_rel_of_lt X hX hi, toKAry_rel_of_lt _ hY hi']
    show (fun j => x (Fin.cast (hX ⟨i, hi⟩) j)) ∈ X.rel ⟨i, hi⟩ ↔
      (fun j => (tupleMap (f : Ω → Ω') x) (Fin.cast (hY ⟨i, hi'⟩) j))
        ∈ mapRel (f : Ω → Ω') (X.rel ⟨i, hi⟩)
    have hfun : (fun j => (tupleMap (f : Ω → Ω') x) (Fin.cast (hY ⟨i, hi'⟩) j))
        = tupleMap (f : Ω → Ω') (fun j => x (Fin.cast (hX ⟨i, hi⟩) j)) := by
      funext j
      rfl
    rw [hfun]
    constructor
    · intro hmem; exact ⟨_, hmem, rfl⟩
    · rintro ⟨y, hy, hxy⟩
      have : y = (fun j => x (Fin.cast (hX ⟨i, hi⟩) j)) := by
        funext j
        exact f.injective (congrFun hxy j)
      rwa [this] at hy
  · have hi' : ¬ i < (X.map (f : Ω → Ω')).numRel := hi
    rw [toKAry_rel_of_ge X hX hi, toKAry_rel_of_ge _ hY hi']
    simp

/-- Definition 2.3.16: the automorphism group does not change, so neither does the
symmetricity nor the symmetry defect. -/
theorem toKAry_aut (X : RelStructure Ω) (h : X.IsKAry k) : (X.toKAry h).Aut = X.Aut := by
  ext σ
  constructor
  · intro hσ
    show X.map (σ : Ω → Ω) = X
    obtain ⟨r, a, R⟩ := X
    simp only [map, mk.injEq, heq_eq_eq, true_and]
    funext i
    have hi : (i : ℕ) < r := i.isLt
    have hrel := hσ (i : ℕ)
    rw [toKAry_rel_of_lt _ h hi] at hrel
    have hik : (⟨(i : ℕ), hi⟩ : Fin r) = i := Fin.ext rfl
    rw [hik] at hrel
    -- the reindexing is a bijection, so `σ`-invariance of the reindexed relation is
    -- `σ`-invariance of the relation itself
    have key : ∀ z : Fin (a i) → Ω, z ∈ R i ↔ tupleMap (σ : Ω → Ω) z ∈ R i := by
      intro z
      have h1 := hrel (fun j : Fin k => z (Fin.cast (h i).symm j))
      have h2 : (fun j : Fin (a i) =>
          (tupleMap (σ : Ω → Ω) (fun j' : Fin k => z (Fin.cast (h i).symm j')))
            (Fin.cast (h i) j)) = tupleMap (σ : Ω → Ω) z := by
        funext j
        exact congrArg (σ : Ω → Ω) (congrArg z (Fin.ext rfl))
      rw [reindexRel_mem_iff, mem_reindexRel, h2] at h1
      exact h1
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact (key z).1 hz
    · intro hy
      refine ⟨tupleMap ((σ⁻¹ : Equiv.Perm Ω) : Ω → Ω) y, ?_, ?_⟩
      · refine (key _).2 ?_
        have : tupleMap (σ : Ω → Ω) (tupleMap ((σ⁻¹ : Equiv.Perm Ω) : Ω → Ω) y) = y := by
          funext j; simp
        rwa [this]
      · funext j; simp
  · intro hσ
    have hmap : X.map ((σ : Equiv.Perm Ω) : Ω → Ω) = X := hσ
    exact toKAry_iso h h hmap

/-- Definition 2.3.16: the relative symmetry defect is the same in the two readings. -/
theorem defect_toKAry [Fintype Ω] [DecidableEq Ω] (X : RelStructure Ω) (h : X.IsKAry k) :
    defect (X.toKAry h).Aut = structDefect X := by
  rw [toKAry_aut]
  rfl

end RelStructure

end Babai
