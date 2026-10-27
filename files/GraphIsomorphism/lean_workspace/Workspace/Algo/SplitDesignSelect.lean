import Workspace.Algo.SplitDesignDomNames
import Workspace.Algo.SplitBipSymmetricity

/-! # Section 9.7: selecting the large twin class

Procedure Reduce-Part2-by-Color tests the absolute defect on the large
class first. If that class fails, Lemma 9.3.2 supplies the complement.
-/
namespace Algo
open Babai RAM

def designRestricted (z : RawUpccCase × List ℕ) : RawBipConstituent :=
  ((z.1.1,sbipFirstInvolved z.1),(z.1.2.1,z.2))

def designBigNames (r : RawUpccCase) : List ℕ :=
  (designBigPositions r).map (fun i => labAt r.2.2 i)

def designSelectC (r : RawUpccCase) : Bool :=
  bipCoverDefect (designRestricted (r,designBigNames r))

theorem polyFun_designRestricted : PolyFun designRestricted :=
  ((polyFun_fst.comp polyFun_fst).pair (polyFun_fst.comp sbipPoly_firstInvolved)).pair
    (((polyFun_fst.comp polyFun_snd).comp polyFun_fst).pair polyFun_snd)

theorem polyFun_designBigNames : PolyFun designBigNames :=
  ((polyFun_snd.comp polyFun_snd).pair polyFun_designBigPositions).comp
    (PolyFun.mapParam polyFun_labAt)

theorem polyFun_designSelectC : PolyFun designSelectC :=
  ((polyFun_id.pair polyFun_designBigNames).comp polyFun_designRestricted).comp polyFun_bipCoverDefect

section
variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {s : Set Ω}
    {X : BlkDesignObj s} {name₁ : ↥X.Pt₁ → ℕ} {name₂ : ↥X.blocks → ℕ}
    {r : RawUpccCase} (h : DesignNames X name₁ name₂ r)
    (e₁ : ↥X.Pt₁ ≃ Fin r.2.1.length) (he₁ : ∀ x, r.2.1[(e₁ x).val] = name₁ x)
    (e₂ : ↥X.blocks ≃ Fin r.2.2.length) (he₂ : ∀ B, r.2.2[(e₂ B).val] = name₂ B)
include h he₁

theorem designRestricted_adj {S : Set (Set ↥s)} (hS : S ⊆ X.blocks) (g : List ℕ)
    (eG : ↥S ≃ Fin g.length)
    (heG : ∀ B, g[(eG B).val] = name₂ ⟨B.val,hS B.property⟩)
    (x : ↥X.Pt₁) (B : ↥S) :
    bipAdjRaw (designRestricted (r,g),(e₁ x,eG B)) = true ↔
      X.c {x.val} B.val = X.linkColor := by
  simp [designRestricted,bipAdjRaw,constituentAdj,labAt,(e₁ x).isLt,(eG B).isLt,
    he₁,heG,h.link,designFirst_spec h]

open scoped Classical in
theorem designRestricted_symmetricity {S : Set (Set ↥s)} (hS : S ⊆ X.blocks) (g : List ℕ)
    (eG : ↥S ≃ Fin g.length)
    (heG : ∀ B, g[(eG B).val] = name₂ ⟨B.val,hS B.property⟩) :
    letI : Fintype ↥s := Fintype.ofFinite _
    letI : DecidableEq ↥s := Classical.decEq _
    (decBipConstituent (designRestricted (r,g))).symmetricity₁ =
      (X.linkGraph.restrictBlk S).symmetricity₁ := by
  classical
  letI : Fintype ↥s := Fintype.ofFinite _
  letI : DecidableEq ↥s := Classical.decEq _
  let Z : BipGraph ↥X.Pt₁ ↥S := ⟨{q | X.c {q.1.val} q.2.val = X.linkColor}⟩
  let Y := X.linkGraph.restrictBlk S
  have hr : (decBipConstituent (designRestricted (r,g))).symmetricity₁ = Z.symmetricity₁ := by
    apply BipGraph.symmetricity₁_congr e₁ eG
    exact designRestricted_adj h e₁ he₁ hS g eG heG
  have hblocks : Y.blocks = S := by
    change X.blocks ∩ S = S
    exact Set.inter_eq_self_of_subset_right hS
  let d : ↥S ≃ ↥Y.blocks := Equiv.setCongr hblocks.symm
  have hm : Y.toBip.symmetricity₁ = Z.symmetricity₁ := by
    apply BipGraph.symmetricity₁_congr (X := Z) (Y := Y.toBip) (Equiv.setCongr rfl) d
    intro x B
    change (X.part₁ x.val ∧ B.val ∈ X.blocks ∧ X.c {x.val} B.val = X.linkColor) ∧
      B.val ∈ S ↔ _
    exact ⟨fun hh => hh.1.2.2,fun hh => ⟨⟨x.property,hS B.property,hh⟩,B.property⟩⟩
  have hf : ∀ x, Y.part₁ x → ∀ y, Y.part₁ y → Y.f x = Y.f y := by
    intro x hx y hy
    change X.c {x} {x} = X.c {y} {y}
    change X.vc (X.vtxPt hx) (X.vtxPt hx) = X.vc (X.vtxPt hy) (X.vtxPt hy)
    apply (X.bipData.color_eq_iff _ _ _ _).2
    exact ((X.bipData.mem_part₁_iff _).1 (X.vtxPt_mem₁ hx)).trans
      ((X.bipData.mem_part₁_iff _).1 (X.vtxPt_mem₁ hy)).symm
  rw [bipBlockSymmetricity Y hf] at hm
  exact hr.trans hm.symm

open scoped Classical in
theorem designRestricted_test {S : Set (Set ↥s)} (hS : S ⊆ X.blocks) (g : List ℕ)
    (eG : ↥S ≃ Fin g.length)
    (heG : ∀ B, g[(eG B).val] = name₂ ⟨B.val,hS B.property⟩) :
    letI : Fintype ↥s := Fintype.ofFinite _
    letI : DecidableEq ↥s := Classical.decEq _
    bipCoverDefect (designRestricted (r,g)) = true ↔
      ((X.n₁ : ℚ) - 1) / 2 ≤ (X.linkGraph.restrictBlk S).symDefect₁ := by
  rw [bipCoverDefect_spec,designRestricted_symmetricity h e₁ he₁ hS g eG heG]
  change ((r.2.1.length : ℚ) - 1) / 2 ≤ (r.2.1.length : ℚ) - _ ↔ _
  rw [designLeft_length e₁]
  rfl

include he₂

open scoped Classical in
theorem designSelectC_spec :
    letI : Fintype ↥s := Fintype.ofFinite _
    letI : DecidableEq ↥s := Classical.decEq _
    designSelectC r = true ↔
      ((X.n₁ : ℚ) - 1) / 2 ≤ (X.linkGraph.restrictBlk X.bigTwin).symDefect₁ := by
  obtain ⟨eC,heC⟩ := designBigEquiv_exists h e₁ he₁ e₂ he₂
  have hlen : (designBigNames r).length = (designBigPositions r).length := by
    simp [designBigNames]
  let eG := eC.trans (finCongr hlen.symm)
  apply designRestricted_test h e₁ he₁ X.bigTwin_subset_blocks (designBigNames r) eG
  intro B
  simp only [designBigNames,List.getElem_map]
  change labAt r.2.2 ((designBigPositions r)[(eC B).val]) = _
  rw [heC,labAt,List.getD_eq_getElem _ _ (e₂ ⟨B.val,X.bigTwin_subset_blocks B.property⟩).isLt,he₂]

open scoped Classical in
theorem designSelectC_complement (hn : designSelectC r ≠ true) :
    letI : Fintype ↥s := Fintype.ofFinite _
    letI : DecidableEq ↥s := Classical.decEq _
    ((X.n₁ : ℚ) - 1) / 2 ≤
      (X.linkGraph.restrictBlk (X.blocks \ X.bigTwin)).symDefect₁ := by
  classical
  letI : Fintype ↥s := Fintype.ofFinite _
  letI : DecidableEq ↥s := Classical.decEq _
  apply X.symDefect₁_compl_bigTwin
  exact fun hh => hn ((designSelectC_spec h e₁ he₁ e₂ he₂).2 hh)

end
end Algo
