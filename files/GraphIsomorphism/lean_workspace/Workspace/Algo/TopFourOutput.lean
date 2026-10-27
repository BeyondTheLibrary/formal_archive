import Workspace.Algo.TopFourAutomatic

/-! # The checked result of the automatic top-action entry
The supplied choices are the values computed by the entry routine. The
correctness and shrinking-call bounds therefore apply to that exact tree.
-/
namespace Algo
open RAM RAM.Targets Babai Equiv
open scoped Classical

namespace Top4Source
variable {n m : ℕ} (F : Top4Source n m)

theorem degree_ge_three (hm : HugeM m (Nat.card (Fin n))) : 3 ≤ m := by
  have hh : (16 : ℝ) ≤ (m : ℝ) := le_trans (le_max_left _ _) hm
  have : 16 ≤ m := by exact_mod_cast hh
  omega

theorem color_ge_three (hm : HugeM m (Nat.card (Fin n))) :
    3 ≤ (winSet m F.color).ncard := by
  have hh : (16 : ℝ) ≤ (m : ℝ) := le_trans (le_max_left _ _) hm
  have : 16 ≤ m := by exact_mod_cast hh
  have := F.color_large
  omega

noncomputable def autoTree {κ : Type*} (hm : HugeM m (Nat.card (Fin n)))
    (x y : RawStr) (Cy : List ℕ) (col : (Fin n → ℕ) → Fin m → κ) (color : κ)
    (hCx : colorClass col (decStrN n x) color = winSet m F.color)
    (hCy : colorClass col (decStrN n y) color = winSet m Cy) :
    SIReduction (Fin n) ℕ (Set (Perm (Fin n))) :=
  let hC := hCx.symm ▸ F.color_large
  cosetTopAction4With F.transitive F.hom F.giant F.large col color (decStrN n x) (decStrN n y)
    hC (F.dataForClass _ hCx hC (F.color_ge_three hm))
    (F.alignment (degree_ge_three hm) x y Cy col color hCx hCy).element

theorem autoTree_loop {c d e f : ℕ} {κ : Type*} (hm : HugeM m (Nat.card (Fin n)))
    (hcap : TopwpCap e f) (x y : RawStr) (Cy : List ℕ)
    (hCy : Cy.Nodup) (hCylt : ∀ u ∈ Cy, u < m)
    (col : (Fin n → ℕ) → Fin m → κ) (color : κ)
    (hCx : colorClass col (decStrN n x) color = winSet m F.color)
    (hCyset : colorClass col (decStrN n y) color = winSet m Cy) (solve : RawWinSI → RawCoset) :
    let I := top4AutoEnter (((F.action, x, y), F.color), Cy)
    LoopMatch (top4aRound c d e f solve) (top4aDecode n) (decCoset n) I
      ((top4aRound c d e f solve).width I) 0 (top4aInit I)
      (F.autoTree hm x y Cy col color hCx hCyset) :=
  F.auto_loop (degree_ge_three hm) (F.color_ge_three hm) hcap x y Cy hCy hCylt
    col color hCx hCyset solve

theorem autoTree_spec {κ : Type*} (hm : HugeM m (Nat.card (Fin n)))
    (x y : RawStr) (Cy : List ℕ) (col : (Fin n → ℕ) → Fin m → κ) (color : κ)
    (hCx : colorClass col (decStrN n x) color = winSet m F.color)
    (hCy : colorClass col (decStrN n y) color = winSet m Cy)
    (hcol : IsCanonicalColoring F.hom col)
    (hgiant : ∀ α : Perm (Fin m), α ∈ alternatingGroup (Fin m) →
      (∀ γ, γ ∉ colorClass col (decStrN n x) color → α γ = γ) →
      ∃ β ∈ homImage F.hom (strAut (genGroup F.gens : Set (Perm (Fin n))) (decStrN n x)),
        ∀ γ ∈ colorClass col (decStrN n x) color, β γ = α γ) :
    let T := F.autoTree hm x y Cy col color hCx hCy
    T.run = strIso (genGroup F.gens : Set (Perm (Fin n))) (decStrN n x) (decStrN n y) ∧
      T.calls.length ≤ 7 * n ∧ (∀ J ∈ T.calls, 3 * J.windowSize ≤ 2 * n) := by
  let hC := hCx.symm ▸ F.color_large
  let E := F.dataForClass _ hCx hC (F.color_ge_three hm)
  let a := F.alignment (degree_ge_three hm) x y Cy col color hCx hCy
  obtain ⟨k, main, rest, _, _, _, _, _, _, _, _, _, hr⟩ :=
    cosetCorollary_12_0_10_with F.transitive F.hom F.giant hm (decStrN n x) (decStrN n y)
      col hcol color hC hgiant E a.element a.spec
  refine ⟨hr, ?_, ?_⟩
  · simpa only [Fintype.card_fin] using calls_length_cosetTopAction4With F.transitive
      F.hom F.giant hm (decStrN n x) (decStrN n y) col hcol color hC hgiant E a.element a.spec
  · simpa only [Fintype.card_fin] using decreases_cosetTopAction4With F.transitive
      F.hom F.giant hm (decStrN n x) (decStrN n y) col hcol color hC hgiant E a.element a.spec

end Top4Source
end Algo
