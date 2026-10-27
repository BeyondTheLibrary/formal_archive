import Workspace.Algo.TopFourAlignLift

/-! # The automatic top-action 4 entry
The supplied data of the paper's tree now come from the original raw action
and the two computed color classes. The aligning group element is computed
as well. This is the entry used by the master and aggregation branches.
-/
namespace Algo
open RAM RAM.Targets Babai Equiv
open scoped Classical

abbrev Top4AutoInput := (RawTop3 × List ℕ) × List ℕ

def top4AutoEntryData (q : Top4AutoInput) : Top4Input :=
  (q.1, top4AlignElement (q.1.1.1, q.1.2, q.2), q.2)

def top4AutoEnter (q : Top4AutoInput) : Top4aNode := top4InputEnter (top4AutoEntryData q)

 theorem polyFun_top4AutoEntryData : PolyFun top4AutoEntryData :=
  polyFun_fst.pair (((((polyFun_fst.comp polyFun_fst).comp polyFun_fst).pair
    ((polyFun_fst.comp polyFun_snd).pair polyFun_snd)).comp polyFun_top4AlignElement).pair polyFun_snd)

 theorem polyFun_top4AutoEnter : PolyFun top4AutoEnter :=
  polyFun_top4AutoEntryData.comp polyFun_top4InputEnter

 theorem top4AutoEnter_uniform_wf (C D e f : ℕ) : ∃ c d : ℕ, ∀ (n : ℕ) (q : Top4AutoInput),
    q.1.1.1.1.1.length = n → Enc.size q ≤ topcsContextCap C D n → Top4aWF c d e f (top4AutoEnter q) := by
  obtain ⟨F, hF, hmF, hsF⟩ := polyFun_top4AutoEntryData.size.exists_polyBound
  obtain ⟨a, b, hab⟩ := hF.comp (polyBound_topcsContextCap C D)
  obtain ⟨c, d, hcd⟩ := top4InputEnter_uniform_wf a b e f
  refine ⟨c, d, fun n q hn hq => ?_⟩
  exact hcd n (top4AutoEntryData q) hn ((hsF q).trans ((hmF _ _ hq).trans (hab n)))

namespace Top4Source
variable {n m : ℕ} (F : Top4Source n m)

noncomputable def alignment {κ : Type*} (hm : 3 ≤ m) (x y : RawStr) (Cy : List ℕ)
    (col : (Fin n → ℕ) → Fin m → κ) (color : κ)
    (hCx : colorClass col (decStrN n x) color = winSet m F.color)
    (hCy : colorClass col (decStrN n y) color = winSet m Cy) :
    TopActionAlignment F.hom col color (decStrN n x) (decStrN n y) where
  element := ⟨decPerm n (top4AlignElement (F.action, F.color, Cy)),
    top4AlignElement_mem F.dom_length F.gdom_length F.images⟩
  spec := by
    intro hc
    rw [hCx, hCy] at hc ⊢
    exact top4AlignElement_spec F.dom_length F.gdom_length F.images F.giant hm hc

 theorem auto_loop {c d e f : ℕ} {κ : Type*} (hm : 3 ≤ m) (hm3 : 3 ≤ (winSet m F.color).ncard)
    (hcap : TopwpCap e f) (x y : RawStr) (Cy : List ℕ)
    (hCy : Cy.Nodup) (hCylt : ∀ u ∈ Cy, u < m)
    (col : (Fin n → ℕ) → Fin m → κ) (color : κ)
    (hCx : colorClass col (decStrN n x) color = winSet m F.color)
    (hCyset : colorClass col (decStrN n y) color = winSet m Cy) (solve : RawWinSI → RawCoset) :
    let hC : m < 2 * (colorClass col (decStrN n x) color).ncard := hCx.symm ▸ F.color_large
    let I := top4AutoEnter (((F.action, x, y), F.color), Cy)
    LoopMatch (top4aRound c d e f solve) (top4aDecode n) (decCoset n) I
      ((top4aRound c d e f solve).width I) 0 (top4aInit I)
      (cosetTopAction4With F.transitive F.hom F.giant F.large col color (decStrN n x) (decStrN n y)
        hC (F.dataForClass _ hCx hC hm3) (F.alignment hm x y Cy col color hCx hCyset).element) := by
  intro hC I
  exact F.top_loop hm3 hcap x y (top4AlignElement (F.action, F.color, Cy)) Cy hCy hCylt
    (top4AlignElement_mem F.dom_length F.gdom_length F.images) col color hCx hCyset solve

end Top4Source
end Algo
