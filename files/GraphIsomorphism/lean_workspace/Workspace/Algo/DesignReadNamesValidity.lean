import Workspace.Algo.DesignReadExitValidity

/-! # UPCC validity on the retained old names

The table's local positions are converted back by the retained subset
list. This gives an exact UPCC coloring on a dominant subset of the
original vertex set, as required by Theorem 8.1.2(c).
-/
namespace Algo
open Babai RAM Equiv
open scoped Classical
set_option quotPrecheck false

/-- Interpret a returned table on its stored original names. -/
def designReadNamedColor (n : ℕ) (L : List ℕ) (q : RawConfig)
    (u v : winSet n L) : ℕ :=
  binColor (q,(rawLetterIndex (L,u.val.val),rawLetterIndex (L,v.val.val)))

section
variable {n k l a b : ℕ} {ks : List ℕ} {p : RawWL}
  (hw : RawWL.WF n k p) (hk : ks.length = k) (hl : l ≤ k) (x : Str (Fin n) l)
  {α : ℝ} (hb : 0 < b) (hab : α = (a:ℝ)/b)
local notation "z" => (((ks,tupleOf x),p),(a,b))
local notation "Y" => ((decWL n k p).restrTo hl x)
local notation "D" => (KAryPartStruct.dominantClass α Y)
local notation "e" => (designDominantEquiv hw hk hl x hb hab)
include hw hk hl hb hab

theorem designReadIndex_on_dominant (u : D) :
    rawLetterIndex (dominantList z,u.val.val) = (e u).val := by
  change designReadIndex (z,u.val.val) = _
  rw [← designDominantEquiv_name hw hk hl x hb hab u]
  exact designReadIndex_spec z (designDominant_nodup hw x) (e u)

/-- The actual output is a UPCC on its old vertex names. -/
theorem designReadExit_named_upcc (hα : 1/2 ≤ α) (hcoh : (decWL n k p).IsCoherent)
    {q : RawConfig} (hq : (designReadExit z).2.2 = some q) :
    IsUPCCColoring (designReadNamedColor n (designReadExit z).2.1 q) := by
  obtain ⟨hn,hU⟩ := designReadExit_upcc_valid hw hk hl x hb hab hα hcoh hq
  rw [hn]
  apply isUPCCColoring_congr (Equiv.setCongr (designDominant_set hw hk hl x hb hab).symm) _ hU
  intro u v
  change binColor (q,(rawLetterIndex (dominantList z,u.val.val),
    rawLetterIndex (dominantList z,v.val.val))) = _
  rw [designReadIndex_on_dominant hw hk hl x hb hab u,
    designReadIndex_on_dominant hw hk hl x hb hab v]

/-- The exact locally numbered table is the natural coloring of a UPCC. -/
theorem designReadExit_position_upcc (hα : 1/2 ≤ α) (hcoh : (decWL n k p).IsCoherent)
    {q : RawConfig} (hq : (designReadExit z).2.2 = some q) :
    ∃ Z : PartitionStructure (Fin (designReadExit z).2.1.length),
      Z.IsCoherent ∧ Z.IsUniprimitive ∧ ∀ u v : Fin (designReadExit z).2.1.length,binColor (q,(u,v)) = Z.natColor u v := by
  obtain ⟨hn,⟨P,hPcoh,hPuni,hPnat⟩⟩ := designReadExit_upcc_valid hw hk hl x hb hab hα hcoh hq
  rw [hn]
  refine ⟨P.congrEquiv e,PartitionStructure.congrEquiv_isCoherent e hPcoh,
    PartitionStructure.congrEquiv_isUniprimitive e hPuni,?_⟩
  intro u v
  change binColor (q,(u,v)) = P.natColor ((e).symm u) ((e).symm v)
  rw [hPnat]
  simp only [Equiv.apply_symm_apply]

/-- A UPCC exit retains strictly more than the threshold fraction of vertices. -/
theorem designReadExit_upcc_dominant (hα : 1/2 ≤ α) (hcoh : (decWL n k p).IsCoherent)
    {q : RawConfig} (hq : (designReadExit z).2.2 = some q) :
    IsDominant α (winSet n (designReadExit z).2.1) := by
  obtain ⟨hn,hU⟩ := designReadExit_upcc_valid hw hk hl x hb hab hα hcoh hq
  obtain ⟨u,_,_⟩ := natColor_nontrivial hU
  rw [hn,designDominant_set hw hk hl x hb hab,
    KAryPartStruct.dominantClass_eq hα Y u.property]
  exact u.property

end
end Algo
