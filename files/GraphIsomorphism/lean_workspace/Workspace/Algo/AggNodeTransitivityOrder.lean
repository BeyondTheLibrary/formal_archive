import Workspace.Algo.AggNodeAggregateMajority
import Mathlib.Data.Fintype.CardEmbedding

/-! # Computing the degree of transitivity by group orders

An ordered tuple has one orbit precisely when its orbit has the size of
all injective tuples. Orbit-stabilizer turns this into two group-order
computations, using the pointwise stabilizer of an initial segment. This
is the group calculation used before the individualization in Case 2b.
-/
namespace Algo
open RAM RAM.Targets Babai Equiv MulAction
open scoped Classical

private theorem prefixStab_mem {m d : ℕ} (hd : d ≤ m)
    (G : Subgroup (Perm (Fin m))) (g : G) :
    g ∈ stabilizer G (Fin.castLEEmb hd) ↔ ∀ u : Fin m, u.val < d → g.val u = u := by
  change (g • Fin.castLEEmb hd) = Fin.castLEEmb hd ↔ _
  constructor
  · intro h u hu
    have hh := congrArg (fun f : Fin d ↪ Fin m => f ⟨u.val, hu⟩) h
    exact hh
  · intro h
    apply DFunLike.ext
    intro u
    exact h (Fin.castLE hd u) u.isLt

private noncomputable def prefixStabEquiv {m d : ℕ} (hd : d ≤ m)
    (G : Subgroup (Perm (Fin m))) :
    stabilizer G (Fin.castLEEmb hd) ≃ pointwiseStabilizer G {u : Fin m | u.val < d} where
  toFun g := ⟨g.val.val, (mem_pointwiseStabilizer).mpr ⟨g.val.property, (prefixStab_mem hd G g.val).mp g.property⟩⟩
  invFun g := ⟨⟨g.val, (mem_pointwiseStabilizer.mp g.property).1⟩,
    (prefixStab_mem hd G _).mpr (mem_pointwiseStabilizer.mp g.property).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The orbit-stabilizer order test for a valid tuple length. -/
theorem aggnMultipleTransitive_card {m d : ℕ} (hd : d ≤ m) (G : Subgroup (Perm (Fin m))) :
    IsMultiplyTransitive G d ↔ Nat.card G =
      m.descFactorial d * Nat.card (pointwiseStabilizer G {u : Fin m | u.val < d}) := by
  let e := Fin.castLEEmb hd
  have hstab := Nat.card_congr (prefixStabEquiv hd G)
  have hord := Nat.card_congr (orbitProdStabilizerEquivGroup G e)
  rw [Nat.card_prod, hstab, Nat.card_coe_set_eq] at hord
  have htuples : Nat.card (Fin d ↪ Fin m) = m.descFactorial d := by
    simp only [Nat.card_eq_fintype_card, Fintype.card_embedding_eq, Fintype.card_fin]
  constructor
  · intro h
    have hp := h.isPretransitive
    have he : orbit G e = Set.univ := by
      ext f
      exact ⟨fun _ => trivial, fun _ => hp.exists_smul_eq e f⟩
    have hc := congrArg Set.ncard he
    rw [Set.ncard_univ, htuples] at hc
    exact hord.symm.trans (congrArg (fun k => k * Nat.card (pointwiseStabilizer G {u : Fin m | u.val < d})) hc)
  · intro h
    have hc : (orbit G e).ncard = Nat.card (Fin d ↪ Fin m) := by
      rw [htuples]
      apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := pointwiseStabilizer G {u : Fin m | u.val < d}))
      exact hord.trans h
    exact ⟨e, (Set.eq_univ_iff_ncard _).mpr hc⟩

end Algo
