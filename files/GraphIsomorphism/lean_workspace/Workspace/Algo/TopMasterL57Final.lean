/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: Theorem 1.1.1 on the RAM with route 5 of the Master Algorithm supplied.
-/
import Workspace.Algo.TopMasterL57Supply
import Workspace.Algo.TopMasterHintedFinal
import Workspace.Algo.TopMasterRoute4Dom

/-!
# Route 5 supplied

`Algo.siWorkspaceRoutine_of_openRoutes` asks for route 4 with a dominant class
(`Algo.MasterRoute4Dom`) and route 5 (`Algo.MasterL57SupplyH`). This file discharges route 5
with the hint routine `Algo.masterL57Hint` (`Algo.exists_masterL57SupplyH`), for constants of
the round of lines 5–7 that meet their specifications (`Algo.exists_l57Constants`), so that
Theorem 1.1.1 on the RAM is left with route 4 with a dominant class only
(`Algo.siWorkspaceRoutine_of_route4Dom`).
-/

set_option synthInstance.maxSize 4096

namespace Algo
open RAM RAM.Targets Babai Equiv

/-- The evaluators of Theorem 9.2.3 (`Algo.exists_extendedSplitFamily_valid_canonical`): for
every `b` there are `t d` for which the run on bipartite inputs is canonical and the restored
entry families are valid for every `c`. -/
theorem exists_restoredEntry_good_bip (b : ℕ) :
    ∃ t d, BipInputRunCanonical b t d ∧ ∀ c, AggnRestoredEntryGood c b t d := by
  obtain ⟨t, d, hcan, hfam⟩ := exists_extendedSplitFamily_valid_canonical b
  refine ⟨t, d, hcan, fun c => ?_⟩
  intro m dom a hdom hnd hlt hlarge hI
  obtain ⟨-, hsolver, -⟩ := hfam (c + 1)
  obtain ⟨hne, hgood⟩ := hsolver a.1.length (a.2, (3, 4)) hI
  constructor
  · obtain ⟨o, ho⟩ := hne
    exact ⟨_, List.mem_map_of_mem ho⟩
  · intro o ho
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 ho
    obtain ⟨Z, hdec, hZ⟩ := hgood p hp
    exact aggnRestoreOutcome_valid hnd hlt hlarge dom hdom hdec hZ

/-- **Constants of the round of lines 5–7** that meet the specifications of
`Algo.exists_masterL57SupplyH`. -/
theorem exists_l57Constants : ∃ c' b' t d dc dp : ℕ, 2 ≤ c' ∧ AggnPhasesOK c' dc dp ∧
    AggnRestoredEntryGood c' b' t d ∧ BipInputRunCanonical b' t d := by
  obtain ⟨dc, dp, -, hok⟩ := exists_aggnPhasesOK 2
  obtain ⟨t, d, hbip, hgood⟩ := exists_restoredEntry_good_bip 0
  exact ⟨2, 0, t, d, dc, dp, le_rfl, hok, hgood 2, hbip⟩

set_option synthInstance.maxSize 4096 in
/-- **Theorem 1.1.1 on the RAM, from route 4 with a dominant class only.** As
`Algo.siWorkspaceRoutine_of_openRoutes`, with route 5 supplied for the hint routine
`Algo.masterL57Hint` (`Algo.exists_masterL57SupplyH`), at constants `c' b' t d dc dp` of the
round of lines 5–7 that meet their specifications (`Algo.exists_l57Constants` gives some). -/
theorem siWorkspaceRoutine_of_route4Dom {c c' b' t d dc dp : ℕ} (hc2 : 2 ≤ c')
    (hok : AggnPhasesOK c' dc dp) (hsolver : AggnRestoredEntryGood c' b' t d)
    (hbip : BipInputRunCanonical b' t d)
    {H4 : (RawMasterSI × ℕ × ADState) × RawMasterSI → Option RawMasterHint}
    (hH4 : QuasiFun H4) {q4 : ℕ → ℕ} (hq4m : Monotone q4) (hq4 : QuasiPolyBound q4)
    (h4 : ∀ n, MasterRoute4Dom (masterAdmittedRound masterCapA masterCapB
      (masterFinalOps c c' b' t d dc dp H4
        (masterL57Hint c' b' t d dc dp (l57UV masterTopE masterTopF).1
          (l57UV masterTopE masterTopF).2 masterTopE masterTopF)))
      n q4 c (masterLine4TT c) (masterLine4DD c)) :
    SIWorkspaceRoutine := by
  obtain ⟨q5, hq5m, hq5, h5⟩ := exists_masterL57SupplyH (E := masterL57E c' b' t d dc dp) hok
    masterTopEF_spec hsolver hbip hc2 (masterL57E_spec c' b' t d dc dp)
  refine siWorkspaceRoutine_of_openRoutes (c := c) (q45 := fun k => q4 k + q5 k) hH4
    (quasiFun_masterL57Hint _ _ _ _ _ _ _ _ _ _) (hq4m.add hq5m) (hq4.add hq5) (fun n => ?_)
    (fun n => (h5 n).mono_q fun k => Nat.le_add_left _ _)
  intro W h hg hwf hr hd
  obtain ⟨T, hT⟩ := h4 n W h hg hwf hr hd
  exact ⟨T, hT.mono_q fun k => Nat.le_add_right _ _⟩

end Algo
