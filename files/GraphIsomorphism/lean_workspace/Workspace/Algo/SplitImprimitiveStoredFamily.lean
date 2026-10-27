import Workspace.Algo.SplitImprimitiveStoredBridge

/-! Store every graph in the selected §9.6 step-2 family. The adapter
keeps the family order and its exact mathematical choices. Its running
time is polynomial on all raw inputs, including malformed dictionaries.
-/
namespace Algo
open Babai RAM
open scoped Classical

def impStoredGraphs (z : (List ℕ × List (List ℕ)) × RawUpccCase) :
    List RawSbipStored :=
  (impStep2Graphs z.2).map (fun q => impStoredGraph (z.1,q))

theorem polyFun_impStoredGraphs : PolyFun impStoredGraphs :=
  (polyFun_fst.pair (polyFun_snd.comp polyFun_impStep2Graphs)).comp
    (PolyFun.mapParam polyFun_impStoredGraph)

theorem impStoredGraphs_mem (z : (List ℕ × List (List ℕ)) × RawUpccCase)
    (g : RawSbipStored) :
    g ∈ impStoredGraphs z ↔ ∃ q ∈ impStep2Graphs z.2,impStoredGraph (z.1,q) = g :=
  List.mem_map

theorem impStoredGraphs_nonempty (z : (List ℕ × List (List ℕ)) × RawUpccCase) :
    ∃ g,g ∈ impStoredGraphs z := by
  obtain ⟨q,hq⟩ := impStep2Graphs_nonempty (r := z.2)
  exact ⟨_,(impStoredGraphs_mem z _).2 ⟨q,hq,rfl⟩⟩

@[simp] theorem impStoredGraphs_length (z : (List ℕ × List (List ℕ)) × RawUpccCase) :
    (impStoredGraphs z).length = (impStep2Graphs z.2).length := List.length_map _

section
variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {s : Set Ω}
    {X : BlkImprimitiveObj s} {name₁ : ↥X.Pt₁ → ℕ} {name₂ : ↥X.blocks → ℕ}
    {r : RawUpccCase} (hn : ImpNames X name₁ name₂ r)
    (hleft : r.2.1.Nodup) (hright : r.2.2.Nodup)
    (e₂ : ↥X.blocks ≃ Fin r.2.2.length) (he₂ : ∀ B,r.2.2[(e₂ B).val] = name₂ B)
    (dom : List ℕ) (d : List (List ℕ))
include hn hleft hright he₂

/-- Each stored graph has an exact step-2 witness, sufficient defect, and
at most half the former number of blocks. `impStoredGraph_colorNames` and
the member-row lemmas transfer every field of this witness to storage. -/
theorem impStoredGraphs_spec (hsplit : ¬ ImprimitiveSplits X)
    (g : RawSbipStored) (hg : g ∈ impStoredGraphs ((dom,d),r)) :
    letI : Fintype ↥s := Fintype.ofFinite _
    letI : DecidableEq ↥s := Classical.decEq _
    ∃ q ∈ impStep2Graphs r,∃ Y : VColBipBlk ↥s ℕ,
      ImpGraphRep X name₁ name₂ r q Y ∧ impStoredGraph ((dom,d),q) = g ∧
      Y ∈ X.step2Cands ∧ 1/2 ≤ Y.defect₁ ∧
      (X.hasGoodBlock → Y ∈ X.blkZ '' X.groups) ∧
      2*g.1.1.2.1.length ≤ X.blocks.ncard := by
  obtain ⟨q,hq,rfl⟩ := (impStoredGraphs_mem _ _).1 hg
  obtain ⟨Y,hr,hY,hdef,hbranch,hsize⟩ :=
    impStep2Graphs_spec hn hleft hright e₂ he₂ hsplit q hq
  exact ⟨q,hq,Y,hr,rfl,hY,hdef,hbranch,by simpa using hsize⟩

/-- Storing the family loses no mathematical choice in the selected branch. -/
theorem impStoredGraphs_covers (Y : VColBipBlk ↥s ℕ)
    (hY : Y ∈ X.step2Cands)
    (hdef : letI : Fintype ↥s := Fintype.ofFinite _
      letI : DecidableEq ↥s := Classical.decEq _
      1/2 ≤ Y.defect₁)
    (hbranch : X.hasGoodBlock → Y ∈ X.blkZ '' X.groups) :
    ∃ g ∈ impStoredGraphs ((dom,d),r),∃ q ∈ impStep2Graphs r,
      ImpGraphRep X name₁ name₂ r q Y ∧ impStoredGraph ((dom,d),q) = g := by
  obtain ⟨q,hq,hr⟩ := impStep2Graphs_covers hn hleft hright e₂ he₂ Y hY hdef hbranch
  exact ⟨_,(impStoredGraphs_mem _ _).2 ⟨q,hq,rfl⟩,q,hq,hr,rfl⟩

end
end Algo
