import Workspace.Algo.SplitImprimitiveGroups
import Workspace.Algo.SplitNamedLists

/-! # Section 9.6: the block-restriction branch test

The stored component lists give the second part of each restricted graph.
The following proof identifies its entire adjacency relation, then transports
the symmetry defect through the two list-position bijections.
-/
set_option maxHeartbeats 1000000
set_option synthInstance.maxSize 1024
namespace Algo
open Babai RAM

section Specification
variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {s : Set Ω}
    {X : BlkImprimitiveObj s} {name₁ : ↥X.Pt₁ → ℕ} {name₂ : ↥X.blocks → ℕ}
    {r : RawUpccCase} (h : ImpNames X name₁ name₂ r) (hnd : r.2.1.Nodup)
    {G : Set ↥X.blocks} {g : List ℕ}
    (e₁ : ↥X.Pt₁ ≃ Fin r.2.1.length) (he₁ : ∀ x, r.2.1[(e₁ x).val] = name₁ x)
    (eG : ↥G ≃ Fin g.length) (heG : ∀ B, g[(eG B).val] = name₂ B.val)

include h hnd he₁ heG

theorem impRestricted_adj (x : ↥X.Pt₁) (B : ↥G) :
    bipAdjRaw (impRestricted (r,g),(e₁ x,eG B)) = true ↔
      X.c {x.val} B.val.val = X.jColor := by
  simp [impRestricted,bipAdjRaw,constituentAdj,labAt,(e₁ x).isLt,(eG B).isLt,
    he₁,heG,h.link,impJ_spec h hnd]

open scoped Classical in
/-- The raw defect is the defect of the paper's whole block restriction. -/
theorem impRestricted_defect :
    letI : Fintype ↥s := Fintype.ofFinite _
    letI : DecidableEq ↥s := Classical.decEq _
    (decBipConstituent (impRestricted (r,g))).defect₁ = (X.blkZ G).defect₁ := by
  classical
  letI : Fintype ↥s := Fintype.ofFinite _
  letI : DecidableEq ↥s := Classical.decEq _
  let Z : BipGraph ↥X.Pt₁ ↥G := ⟨{q | X.c {q.1.val} q.2.val.val = X.jColor}⟩
  have hr : (decBipConstituent (impRestricted (r,g))).defect₁ = Z.defect₁ := by
    apply BipGraph.defect₁_congr e₁ eG
    exact impRestricted_adj h hnd e₁ he₁ eG heG
  have hm : (X.blkZ G).toBip.defect₁ = Z.defect₁ := by
    let d : ↥G ≃ ↥(X.blkZ G).blocks :=
      Equiv.Set.image (Subtype.val : ↥X.blocks → Set ↥s) G Subtype.val_injective
    exact BipGraph.defect₁_congr (X := Z) (Y := (X.blkZ G).toBip)
      (Equiv.setCongr rfl) d (by
        intro x B
        change (_ ∈ Subtype.val '' G ∧ X.part₁ x.val ∧
          X.c {x.val} B.val.val = X.jColor) ↔ X.c {x.val} B.val.val = X.jColor
        exact ⟨fun hh => hh.2.2,fun hc => ⟨⟨B.val,B.property,rfl⟩,x.property,hc⟩⟩)
  rw [VColBipBlk.defect₁_toBip _ (fun _ _ => rfl)] at hm
  exact hr.trans hm.symm

end Specification

section Selection
variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {s : Set Ω}
    {X : BlkImprimitiveObj s} {name₁ : ↥X.Pt₁ → ℕ} {name₂ : ↥X.blocks → ℕ}
    {r : RawUpccCase} (h : ImpNames X name₁ name₂ r)
    (hleft : r.2.1.Nodup) (hright : r.2.2.Nodup)

include h hleft

open scoped Classical in
/-- Any duplicate-free list of a group gives the same defect test. -/
theorem impGoodGroup_iff (G : Set ↥X.blocks) (g : List ℕ) (hnd : g.Nodup)
    (hg : ∀ a, a ∈ g ↔ ∃ C ∈ G, name₂ C = a) :
    letI : Fintype ↥s := Fintype.ofFinite _
    letI : DecidableEq ↥s := Classical.decEq _
    bipHalfDefect (impRestricted (r,g)) = true ↔ 1 / 2 ≤ (X.blkZ G).defect₁ := by
  classical
  obtain ⟨e₁,he₁⟩ := splitNameEquiv_exists name₁ h.inj₁ _ hleft h.left
  obtain ⟨eG,heG⟩ := splitNameEquiv_exists (fun C : ↥G => name₂ C.val)
    (h.inj₂.comp Subtype.val_injective) g hnd (by
      intro a
      rw [hg]
      exact ⟨fun ⟨C,hC,hname⟩ => ⟨⟨C,hC⟩,hname⟩,
        fun ⟨C,hname⟩ => ⟨C.val,C.property,hname⟩⟩)
  rw [bipHalfDefect_spec,impRestricted_defect h hleft e₁ he₁ eG heG]

include hright

/-- The machine takes step 2(i) exactly when the mathematical family does. -/
theorem impGoodGroups_nonempty
    (e : ↥X.blocks ≃ Fin r.2.2.length) (he : ∀ B, r.2.2[(e B).val] = name₂ B) :
    (∃ g, g ∈ impGoodGroups r) ↔ X.hasGoodBlock := by
  classical
  constructor
  · rintro ⟨g,hg⟩
    obtain ⟨hmem,hpass⟩ := List.mem_filter.1 hg
    obtain ⟨G,hG,hrep⟩ := impGroups_spec h e he g hmem
    exact ⟨G,hG,(impGoodGroup_iff h hleft G g
      (impGroups_members_nodup hright hmem) hrep).1 hpass⟩
  · rintro ⟨G,hG,hpass⟩
    obtain ⟨g,hmem,hrep⟩ := impGroups_complete h e he G hG
    exact ⟨g,List.mem_filter.2 ⟨hmem,(impGoodGroup_iff h hleft G g
      (impGroups_members_nodup hright hmem) hrep).2 hpass⟩⟩

end Selection
end Algo
