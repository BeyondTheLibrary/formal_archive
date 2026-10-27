import Workspace.Master.PrimitiveCaseIdUnique

/-! # Section 15, lines 3–4: constructing the standard-block identification

The test `Ω = Φ` says that the labels `T(u)` distinguish the points of `Ω`.
Theorem 10.5.1(e) supplies every subset of the common label size. Thus an
injectivity test and a check of that size suffice to build `PrimitiveCaseId`.
The proof uses the paper's standard-block labels throughout.
-/

namespace Babai
open Equiv MulAction

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {m t : ℕ}
    {G : Subgroup (Perm Ω)} (ϕ : G →* Perm (Fin m))

/-- Section 15, lines 3–4: distinct labels of size `t` identify the points
with the `t`-subsets, by Theorem 10.5.1(c) and (e). -/
theorem nonempty_primitiveCaseId_iff (hΩ : Nonempty Ω) (hϕ : IsGiantRep ϕ)
    (hk : VeryLargeK m (maxOrbitLength G)) :
    Nonempty (PrimitiveCaseId ϕ t) ↔
      Function.Injective (Tpoint ϕ) ∧ ∀ u : Ω, tPoint ϕ u = t := by
  classical
  constructor
  · rintro ⟨id⟩
    refine ⟨?_, id.tPointOf_eq⟩
    intro u v huv
    apply id.label.injective
    apply Subtype.ext
    apply Finset.coe_injective
    exact (id.label_eq u).trans (huv.trans (id.label_eq v).symm)
  · rintro ⟨hinj, ht⟩
    let f : Ω → binom (Fin m) t := fun u =>
      ⟨(Tpoint ϕ u).toFinset, by rw [← Set.ncard_eq_toFinset_card']; exact ht u⟩
    have hf : ∀ u, ((f u : Finset (Fin m)) : Set (Fin m)) = Tpoint ϕ u :=
      fun u => Set.coe_toFinset _
    have hfi : Function.Injective f := by
      intro u v huv
      apply hinj
      rw [← hf u, ← hf v, huv]
    let u₀ : Ω := Classical.choice hΩ
    have hfs : Function.Surjective f := by
      intro T
      obtain ⟨u, _, hu⟩ := exists_Tpoint_eq ϕ hϕ hk u₀
        (T := (T : Finset (Fin m))) (by rw [Set.ncard_coe_finset, T.property, ht])
      refine ⟨u, Subtype.ext (Finset.coe_injective ?_)⟩
      exact (hf u).trans hu
    let e := Equiv.ofBijective f ⟨hfi, hfs⟩
    refine ⟨{ label := e, equivariant := ?_, four_t := ?_, label_eq := hf }⟩
    · intro σ u
      apply Subtype.ext
      apply Finset.coe_injective
      change ((f ((σ : Perm Ω) u) : Finset (Fin m)) : Set (Fin m)) =
        ((tAction t (ϕ σ) (f u) : Finset (Fin m)) : Set (Fin m))
      rw [hf, tAction_apply_coe, Finset.coe_image, hf]
      exact theorem_10_5_1_c_eq54 ϕ hϕ hk u σ
    · have ha := (theorem_10_5_1_a ϕ hϕ hk u₀).1.1
      change 4 * tPoint ϕ u₀ < m at ha
      simpa only [ht, Fintype.card_fin] using ha

end Babai

#print axioms Babai.nonempty_primitiveCaseId_iff
