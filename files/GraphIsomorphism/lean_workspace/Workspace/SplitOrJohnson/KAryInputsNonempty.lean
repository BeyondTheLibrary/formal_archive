import Workspace.SplitOrJohnson.Main

/-! # The input category of Theorem 9.2.3 has objects

Theorem 9.2.3 (Sec. 9.2, v2.5) is stated for a `k`-ary relational structure on `n` points with
`2 ≤ k ≤ n/4` and relative symmetry defect `> 1 - α`. This file checks that the category
`Babai.KAryInputs Ω k α` of those inputs is not empty, so the theorem is not vacuous. The
example is on `Fin 8` with `k = 2` and `α = 3/4`: the rigid structure with one binary
relation `Rᵢ = {(i,i)}` for each point `i`. Its only automorphism is the identity, so no two
points are twins, the symmetricity is `1`, and the relative symmetry defect is `7/8 > 1/4`.
-/
namespace Babai

/-- The points of `Fin 8` as elements of the full subset. -/
abbrev rigidPt (i : Fin 8) : ↥(Set.univ : Set (Fin 8)) := ⟨i,Set.mem_univ i⟩

/-- The rigid binary structure on `Fin 8`: relation `i` is `{(i,i)}`. -/
def rigidStruct8 : RelStructure ↥(Set.univ : Set (Fin 8)) where
  numRel := 8
  arity _ := 2
  rel i := {fun _ => rigidPt i}

theorem rigidStruct8_isKAry : rigidStruct8.IsKAry 2 := fun _ => rfl

/-- An automorphism of the rigid structure fixes every point. -/
theorem rigidStruct8_aut_fix {σ : Equiv.Perm ↥(Set.univ : Set (Fin 8))}
    (hσ : σ ∈ RelStructure.Aut rigidStruct8) (x : ↥(Set.univ : Set (Fin 8))) : σ x = x := by
  have h : rigidStruct8.map σ = rigidStruct8 := hσ
  simp only [rigidStruct8,RelStructure.map,RelStructure.mk.injEq,heq_eq_eq,true_and] at h
  have hi := congrFun h ⟨x.val.val,x.val.isLt⟩
  have hin : (fun _ => σ x : Fin 2 → ↥(Set.univ : Set (Fin 8))) ∈
      mapRel σ {fun _ => rigidPt ⟨x.val.val,x.val.isLt⟩} :=
    ⟨fun _ => rigidPt ⟨x.val.val,x.val.isLt⟩,rfl,rfl⟩
  rw [hi] at hin
  have := congrFun hin 0
  exact this.trans (Subtype.ext rfl)

/-- No two points of the rigid structure are twins. -/
theorem rigidStruct8_not_twin [DecidableEq ↥(Set.univ : Set (Fin 8))] (x y : ↥(Set.univ : Set (Fin 8))) :
    ¬ IsTwin (RelStructure.Aut rigidStruct8) x y := by
  rintro ⟨hxy,hs⟩
  have := rigidStruct8_aut_fix hs x
  rw [Equiv.swap_apply_left] at this
  exact hxy this.symm

/-- **The input category of Theorem 9.2.3 has an object** (Sec. 9.2): the rigid binary
structure on `Fin 8` is an admissible input for `k = 2` and `α = 3/4`. -/
noncomputable def kAryInputs_example : (KAryInputs (Fin 8) 2 (3/4)).Obj Set.univ :=
  ⟨⟨rigidStruct8,rigidStruct8_isKAry⟩,by
    letI : Fintype ↥(Set.univ : Set (Fin 8)) := Fintype.ofFinite _
    letI : DecidableEq ↥(Set.univ : Set (Fin 8)) := Classical.decEq _
    have hcard : Fintype.card ↥(Set.univ : Set (Fin 8)) = 8 := by
      rw [Fintype.card_eq_nat_card,Nat.card_coe_set_eq,Set.ncard_univ,Nat.card_eq_fintype_card,
        Fintype.card_fin]
    have hsym : symmetricity (IsStructure.autGroup rigidStruct8) ≤ 1 := by
      classical
      refine Finset.sup_le fun Ψ hΨ => ?_
      simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hΨ
      refine Finset.card_le_one.2 fun a ha b hb => ?_
      by_contra hab
      exact rigidStruct8_not_twin a b (hΨ a ha b hb hab)
    refine ⟨le_rfl,?_,?_⟩
    · rw [Set.ncard_univ,Nat.card_eq_fintype_card,Fintype.card_fin]
    · change (1 : ℝ) - 3/4 < ((1 - (symmetricity (IsStructure.autGroup rigidStruct8) : ℚ) /
        (Fintype.card ↥(Set.univ : Set (Fin 8)) : ℚ) : ℚ) : ℝ)
      rw [hcard]
      have : (symmetricity (IsStructure.autGroup rigidStruct8) : ℚ) ≤ 1 := by exact_mod_cast hsym
      have h2 : (1 : ℚ) / 4 < 1 - (symmetricity (IsStructure.autGroup rigidStruct8) : ℚ) / 8 := by
        linarith
      have h3 := (Rat.cast_lt (K := ℝ)).2 h2
      push_cast at h3 ⊢
      linarith⟩

/-- Sec. 9.2: the category of admissible inputs of Theorem 9.2.3 is not empty. -/
theorem kAryInputs_nonempty : Nonempty ((KAryInputs (Fin 8) 2 (3/4)).Obj Set.univ) :=
  ⟨kAryInputs_example⟩

end Babai
