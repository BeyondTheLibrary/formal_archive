import Workspace.Algo.DesignReadComponentValidity

/-! # Validity of every returning Design Lemma exit

The component and UPCC branches use their actual computed tests. If neither
passes at a returning tuple, the restriction has no dominant color, so the
plain coloring branch is a valid alpha-partition.
-/
namespace Algo
open Babai RAM Equiv
open scoped Classical
set_option quotPrecheck false

section
variable {n k l a b : ℕ} {ks : List ℕ} {p : RawWL}
  (hw : RawWL.WF n k p) (hk : ks.length = k) (hl : l ≤ k) (x : Str (Fin n) l)
  {α : ℝ} (hb : 0 < b) (hab : α = (a:ℝ)/b)
local notation "z" => (((ks,tupleOf x),p),(a,b))
local notation "Y" => ((decWL n k p).restrTo hl x)
local notation "D" => (KAryPartStruct.dominantClass α Y)
local notation "e" => (designDominantEquiv hw hk hl x hb hab)

include hw hk hl hb hab

/-- A returning non-clique dominant skeleton has rank at least three. -/
theorem designReadHasUpcc_of_returns (hα : 1/2 ≤ α) (hn : 4 ≤ n)
    (hcoh : (decWL n k p).IsCoherent)
    (hr : KAryPartStruct.Returns α (decWL n k p) hl x)
    (hno : ¬ KAryPartStruct.NoDominantColor α Y) : designReadHasUpcc z = true := by
  obtain ⟨h2,hdom,hclq⟩ := hr.2.resolve_left hno
  obtain ⟨j,hj⟩ := hdom
  have hDj : D = (Y).vclass j := KAryPartStruct.dominantClass_eq hα Y hj
  have hnt : (D).Nontrivial := by
    apply Set.one_lt_ncard_iff_nontrivial.mp
    have hlt : α * (n:ℝ) < ((D).ncard:ℝ) := by
      rw [hDj]
      simpa only [IsDominant,Fintype.card_fin,Nat.card_eq_fintype_card] using hj
    have hn' : (4:ℝ) ≤ n := by exact_mod_cast hn
    have hn0 : (0:ℝ) ≤ n := by positivity
    have hcard : (1:ℝ) < ((D).ncard:ℝ) := by nlinarith
    exact_mod_cast hcard
  have hY := (decWL n k p).restrTo_isCoherent hcoh hl x
  have hrank : 3 ≤ (((Y).skel2 (by omega)).induced D).rank :=
    PartitionStructure.three_le_rank_induced _ ((Y).skel2_isCoherent hY (by omega)).toIsConfiguration hnt hclq
  have hcount := cliqueRank_spec hw hk hl h2 x hb hab
  simp only [designReadHasUpcc,designReadHasSkeleton,length_tupleOf,hk,
    Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨h2,by omega⟩

/-- Every actual partition exit at a returning tuple satisfies Definition 7.1.1. -/
theorem designReadExit_partition_valid (hα : 1/2 ≤ α) (hn : 4 ≤ n)
    (hcoh : (decWL n k p).IsCoherent) (hr : returnsB z = true)
    {P : RawColPart} (hP : (designReadExit z).1 = some P) :
    (decColPartition n P).IsAlphaPartition α := by
  have hret := (returnsB_spec hw hk hl x hb hab).mp hr
  unfold designReadExit at hP
  split at hP
  · rename_i hc
    have he : designReadPart z = P := Option.some.inj hP
    rw [← he]
    exact designReadPart_isAlphaPartition hw hk hl x hb hab hα hcoh hc
  · split at hP
    · simp [designReadUpccExit] at hP
    · rename_i hc hu
      have he : designReadPlain z = P := Option.some.inj hP
      rw [← he]
      apply designReadPlain_isAlphaPartition hw hk hl x hα
      by_contra hno
      exact hu (designReadHasUpcc_of_returns hw hk hl x hb hab hα hn hcoh hret hno)

/-- The exact recoded coloring returned by the UPCC branch is a UPCC coloring. -/
theorem designReadExit_upcc_valid (hα : 1/2 ≤ α) (hcoh : (decWL n k p).IsCoherent)
    {q : RawConfig} (hq : (designReadExit z).2.2 = some q) :
    (designReadExit z).2.1 = dominantList z ∧
      IsUPCCColoring (fun u v : D => binColor (q,(e u,e v))) := by
  obtain ⟨hc,hu,hnames,rfl⟩ := designReadExit_upcc hq
  exact ⟨hnames,designReadUpcc_isUPCCColoring hw hk hl x hb hab hα hcoh hc hu⟩

end
end Algo
