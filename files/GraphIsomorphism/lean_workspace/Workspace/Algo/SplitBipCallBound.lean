import Workspace.Algo.SplitBipResources
import Workspace.Algo.SplitBipBudget

/-! Count the actual stored call list with the progress alternatives of
Section 9.5. The fixed per-turn base bounds every materialized family in
the initial input size, including repeated versions. -/
namespace Algo
open RAM Babai

theorem sbip_nodes_budget (c m n base : ℕ) (hb : 1 ≤ base)
    (hwidth : ∀ I,SbipResources m n I → (sbipNodeGraphs c I).length ≤ base)
    (f : ℕ) (I : RawSbipNode) (hI : SbipResources m n I) :
    (sbipRound c).nodes f I ≤ sbipNodeMeasure I *
      sbipBudget base (sbipNodeBlocks I) (sbipNodeBit I) := by
  let R := sbipRound c
  let P := SbipResources m n
  let B := fun I => sbipBudget base (sbipNodeBlocks I) (sbipNodeBit I)
  have hpres : ∀ f I J,P I → J ∈ R.roundCalls f I → P J := by
    intro f I J hI hJ
    obtain ⟨j,s,hc⟩ := R.mem_roundCalls_child hJ
    exact hI.child hc
  have hchild : ∀ f I J,P I → J ∈ R.roundCalls f I → base * B J ≤ B I := by
    intro f I J hI hJ
    obtain ⟨j,s,hc⟩ := R.mem_roundCalls_child hJ
    obtain ⟨X,hX⟩ := hI.valid
    obtain ⟨Y,hY,hV,ha,hpaper,hraw⟩ := hX.nodeChild_good hc
    rcases hraw with ⟨hpos,hred⟩ | ⟨hcount,hbitI,hbitJ⟩
    · exact sbipBudget_drop hb hpos hred (sbipNodeBit_le J)
    · dsimp only [B]
      rw [hbitI,hbitJ]
      exact sbipBudget_hint hb hcount
  have hsum : ∀ f I,P I → ((R.roundCalls f I).map B).sum ≤ B I :=
    R.roundBudget_sum_le_on P B (fun _ => base) (fun _ _ => hb)
      hwidth hchild
  exact R.nodes_le_budget_on P B (fun _ _ => trivial) hpres
    (fun I _ => sbipBudget_pos hb _ _) hsum f I hI

theorem exists_sbipSubSteps_bound (c : ℕ) :
    ∃ q : ℕ → ℕ,QuasiPolyBound q ∧
      ∀ m I,SbipNodeValid m I → ∀ f,(sbipRound c).subSteps f I ≤ q (Enc.size I) := by
  obtain ⟨K,hK,hmK,hk⟩ := exists_sbipNodeGraphs_bound
  let base := fun n => K n+1
  have hbase : QuasiPolyBound base := hK.add (polyBound_const 1).quasiPoly
  let q := fun n => 3*((2*n+1)*sbipBudgetBound (base n) n)+1
  have hq : QuasiPolyBound q :=
    (((polyBound_const 3).quasiPoly).mul
      (((((polyBound_const 2).quasiPoly).mul polyBound_id.quasiPoly).add
        (polyBound_const 1).quasiPoly).mul (quasiPolyBound_sbipBudgetBound hbase))).add
      (polyBound_const 1).quasiPoly
  refine ⟨q,hq,?_⟩
  intro m I hI f
  obtain ⟨X,hX⟩ := hI
  let N := Enc.size I
  have hres := hX.resources
  have hb : 1 ≤ base N := by dsimp [base]; omega
  have hw : ∀ J,SbipResources m N J → (sbipNodeGraphs c J).length ≤ base N := by
    intro J hJ
    obtain ⟨Y,hY⟩ := hJ.valid
    exact ((length_le_size _).trans (hk c N m J Y hY hJ.degree hJ.witness hJ.alpha)).trans
      (Nat.le_add_right _ _)
  have hn := sbip_nodes_budget c m N (base N) hb hw f I hres
  have hm : sbipNodeMeasure I ≤ 2*N+1 := by
    have hh := hX.blocks_le.trans hres.degree
    have hi := sbipNodeBit_le I
    unfold sbipNodeMeasure
    omega
  have hbudget := sbipBudget_le hb (hX.blocks_le.trans hres.degree) (sbipNodeBit_le I)
  have hnodes := hn.trans (Nat.mul_le_mul hm hbudget)
  change (sbipRound c).nodes f I ≤ (2*N+1)*sbipBudgetBound (base N) N at hnodes
  have hs := (sbipRound c).subSteps_le f I
  change (sbipRound c).subSteps f I ≤ 3*((2*N+1)*sbipBudgetBound (base N) N)+1
  omega

theorem exists_sbipRun_count (c : ℕ) :
    ∃ t,∀ m I,SbipNodeValid m I → ∀ f,
      (sbipRound c).subSteps f I ≤ Round.roundCount t (Enc.size I) := by
  obtain ⟨q,hq,hbound⟩ := exists_sbipSubSteps_bound c
  obtain ⟨t,ht⟩ := exists_roundCount_of_quasiPolyBound hq
  exact ⟨t,fun m I hI f => (hbound m I hI f).trans (ht _)⟩

end Algo
