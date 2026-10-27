/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Background used by the proof of Lemma 10.2.5, Case 2 (nonabelian socle).
-/
import Workspace.Prelim.SocleStructure
import Mathlib.GroupTheory.Solvable

/-!
# Two facts for the nonabelian case of Lemma 10.2.5

* `Babai.conj_noncommPiCoprod`: in an internal direct product, conjugation by a product
  `r₁ ⋯ r_s` of elements of the factors acts on the factor `R i` as conjugation by `r i`.
  This is what makes the map "`Pker(G)/N ≤ Out(R₁) × ⋯ × Out(R_s)`" of the proof of
  Lemma 10.2.5 injective.
* `Babai.isSolvable_pi_fin`: a finite direct product of solvable groups is solvable
  (Mathlib has only the two-factor `solvable_prod`).  This turns Schreier's Hypothesis,
  applied to each `R i`, into the solvability of `Out(R₁) × ⋯ × Out(R_s)`.
-/

namespace Babai

/-! ### Conjugation by an element of an internal direct product -/

section Conj

variable {G : Type*} [Group G] {ι : Type*} [Fintype ι] [DecidableEq ι]
  {R : ι → Subgroup G}

/-- In an internal direct product, conjugation by `r₁ ⋯ r_s` acts on the factor `R i` as
conjugation by `r i`: the other factors commute with `R i` elementwise. -/
theorem conj_noncommPiCoprod
    (hcomm : Pairwise fun i j : ι => ∀ x y : G, x ∈ R i → y ∈ R j → Commute x y)
    (r : ∀ i, ↥(R i)) {i : ι} {x : G} (hx : x ∈ R i) :
    (Subgroup.noncommPiCoprod hcomm r : G) * x * (Subgroup.noncommPiCoprod hcomm r : G)⁻¹
      = (r i : G) * x * (r i : G)⁻¹ := by
  classical
  set φ := Subgroup.noncommPiCoprod hcomm with hφ
  have hsplit : r = Function.update r i 1 * Pi.mulSingle i (r i) := by
    funext j
    by_cases hij : j = i
    · subst hij; simp
    · simp [Function.update_of_ne hij, Pi.mulSingle_eq_of_ne hij]
  -- the other factors commute with everything in `R i`
  have hcomm' : ∀ y ∈ R i, Commute y (φ (Function.update r i 1)) := by
    intro y hy
    refine Commute.symm ?_
    have hall : ∀ j, Commute ((Function.update r i 1 j : R j) : G) y := by
      intro j
      by_cases hij : j = i
      · subst hij; simp [Commute, SemiconjBy]
      · exact hcomm hij _ _ (Function.update r i 1 j).2 hy
    rw [hφ, Subgroup.noncommPiCoprod_apply]
    refine Commute.symm (Finset.noncommProd_commute _ _ _ _ ?_)
    intro j _
    exact (hall j).symm
  set a : G := φ (Function.update r i 1) with ha
  set b : G := (r i : G) with hb
  have hbx : b * x * b⁻¹ ∈ R i := mul_mem (mul_mem (r i).2 hx) (inv_mem (r i).2)
  have hcomm2 : a * (b * x * b⁻¹) * a⁻¹ = b * x * b⁻¹ := by
    have := (hcomm' _ hbx).symm
    have h2 : a * (b * x * b⁻¹) = (b * x * b⁻¹) * a := this
    rw [h2, mul_assoc, mul_inv_cancel, mul_one]
  have hval : (φ r : G) = a * b := by
    conv_lhs => rw [hsplit]
    rw [map_mul, Subgroup.noncommPiCoprod_mulSingle]
  rw [hval]
  calc a * b * x * (a * b)⁻¹ = a * (b * x * b⁻¹) * a⁻¹ := by group
    _ = b * x * b⁻¹ := hcomm2

end Conj

/-! ### Finite products of solvable groups -/

section Solvable

universe v

/-- `(∀ i : Fin (n+1), H i) ≃* H 0 × (∀ i : Fin n, H i.succ)`. -/
def piFinSuccMulEquiv (n : ℕ) (H : Fin (n + 1) → Type v) [∀ i, Group (H i)] :
    (∀ i, H i) ≃* H 0 × (∀ i : Fin n, H i.succ) where
  toFun f := (f 0, fun i => f i.succ)
  invFun p := Fin.cases p.1 p.2
  left_inv f := by
    funext i
    refine Fin.cases ?_ ?_ i
    · simp
    · intro j; simp
  right_inv p := by
    refine Prod.ext ?_ ?_
    · simp
    · funext j; simp
  map_mul' _ _ := rfl

/-- A finite direct product of solvable groups is solvable. -/
theorem isSolvable_pi_fin : ∀ (n : ℕ) (H : Fin n → Type v) [∀ i, Group (H i)],
    (∀ i, IsSolvable (H i)) → IsSolvable (∀ i, H i) := by
  intro n
  induction n with
  | zero =>
    intro H _ _
    haveI : Subsingleton (∀ i : Fin 0, H i) := ⟨fun f g => funext fun i => i.elim0⟩
    infer_instance
  | succ m ih =>
    intro H _ hH
    haveI : IsSolvable (H 0) := hH 0
    haveI : IsSolvable (∀ i : Fin m, H i.succ) := ih (fun i => H i.succ) (fun i => hH i.succ)
    haveI : IsSolvable (H 0 × (∀ i : Fin m, H i.succ)) := inferInstance
    exact solvable_of_solvable_injective (f := (piFinSuccMulEquiv m H).toMonoidHom)
      (piFinSuccMulEquiv m H).injective

end Solvable

end Babai
