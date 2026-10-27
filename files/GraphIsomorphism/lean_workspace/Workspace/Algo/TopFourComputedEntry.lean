import Workspace.Algo.TopFourComputed

/-! # Entry and exit for the computed top-action data
The machine's class-size guard and aligning permutation enclose the literal
paper body with the computed `TopAction4Data` record. Preparation remains a
polynomial computation on one carrier over every input degree.
-/
namespace Algo
open RAM RAM.Targets Babai Equiv
open scoped Pointwise Classical

 theorem top4InputContext_source (q : Top4Input) :
    (top4X (top4InputContext q)).length = q.1.1.1.1.1.length := by
  simp only [top4InputContext, top4WindowContext, top4X, length_fixStr, topRAction]

 theorem top4InputEnter_uniform_wf (C D e f : ℕ) : ∃ c d : ℕ, ∀ (n : ℕ) (q : Top4Input),
    q.1.1.1.1.1.length = n → Enc.size q ≤ topcsContextCap C D n →
      Top4aWF c d e f (top4InputEnter q) := by
  obtain ⟨c, d, hcd⟩ := top4InputContext_uniform_cap C D
  refine ⟨c, d, fun n q hn hq => ?_⟩
  apply top4aEnter_wf
  rw [top4InputContext_source, hn]
  exact hcd n q hq

namespace Top4Source
variable {n m : ℕ} (F : Top4Source n m)

 theorem input_loop {c d e f : ℕ} (hm3 : 3 ≤ (winSet m F.color).ncard)
    (hcap : TopwpCap e f) (x y : RawStr) (α : RawPerm) (Cy : List ℕ) (solve : RawWinSI → RawCoset) :
    let I := top4InputEnter (((F.action, x, y), F.color), α, Cy)
    LoopMatch (top4aRound c d e f solve) (top4aDecode n) (decCoset n) I
      ((top4aRound c d e f solve).width I) 0 (top4aInit I)
      (if F.color.length = Cy.length then
        (cosetTopAction4BodyWith F.transitive F.hom F.giant F.large (winSet m F.color) F.color_large
          (F.data hm3) (decStrN n x) (strAct (decStrN n y) (decPerm n α)⁻¹)).bind
          (fun A => .done (decPerm n α • A))
       else .done ∅) := by
  intro I
  have hx : (top4X (top4InputContext (((F.action, x, y), F.color), α, Cy))).length = n :=
    (top4InputContext_source _).trans F.dom_length
  exact top4aEnter_loopMatch hx solve (F.body_loop hm3 hcap x y α Cy solve)

noncomputable def dataForClass (D : Set (Fin m)) (hD : D = winSet m F.color)
    (hlarge : m < 2 * D.ncard) (hm3 : 3 ≤ (winSet m F.color).ncard) :
    TopAction4Data F.transitive F.hom F.giant F.large D hlarge := by
  subst D
  exact F.data hm3

 theorem body_dataForClass (D : Set (Fin m)) (hD : D = winSet m F.color)
    (hlarge : m < 2 * D.ncard) (hm3 : 3 ≤ (winSet m F.color).ncard) (x y : Fin n → ℕ) :
    cosetTopAction4BodyWith F.transitive F.hom F.giant F.large D hlarge
      (F.dataForClass D hD hlarge hm3) x y =
    cosetTopAction4BodyWith F.transitive F.hom F.giant F.large (winSet m F.color) F.color_large
      (F.data hm3) x y := by
  subst D
  rfl

 theorem top_loop {c d e f : ℕ} {κ : Type*} (hm3 : 3 ≤ (winSet m F.color).ncard)
    (hcap : TopwpCap e f) (x y : RawStr) (α : RawPerm) (Cy : List ℕ)
    (hCy : Cy.Nodup) (hCylt : ∀ u ∈ Cy, u < m) (hα : decPerm n α ∈ genGroup F.gens)
    (col : (Fin n → ℕ) → Fin m → κ) (color : κ)
    (hCx : colorClass col (decStrN n x) color = winSet m F.color)
    (hCyset : colorClass col (decStrN n y) color = winSet m Cy) (solve : RawWinSI → RawCoset) :
    let hC : m < 2 * (colorClass col (decStrN n x) color).ncard := hCx.symm ▸ F.color_large
    let I := top4InputEnter (((F.action, x, y), F.color), α, Cy)
    LoopMatch (top4aRound c d e f solve) (top4aDecode n) (decCoset n) I
      ((top4aRound c d e f solve).width I) 0 (top4aInit I)
      (cosetTopAction4With F.transitive F.hom F.giant F.large col color (decStrN n x) (decStrN n y)
        hC (F.dataForClass _ hCx hC hm3) ⟨decPerm n α, hα⟩) := by
  intro hC I
  rw [cosetTopAction4With, F.body_dataForClass _ hCx hC hm3]
  rw [hCx, hCyset, ncard_winSet F.color F.color_nodup F.color_lt, ncard_winSet Cy hCy hCylt]
  exact F.input_loop hm3 hcap x y α Cy solve

end Top4Source
end Algo
