import Workspace.Algo.AggNodeCert

/-! # The raw representative order depends on the encoding

Shortening generators preserves their group, but does not pick a fixed list
for that group. These small examples are checked by the kernel. They concern
the raw enumeration interface, not a claim in the paper.
-/

namespace Algo

open Babai Equiv
open scoped Classical Pointwise

def aggnOrderCycle : RawPerm := [1, 2, 0]
def aggnOrderInv : RawPerm := [2, 0, 1]

def aggnOrderGens (b : Bool) : RawGens :=
  [if b then aggnOrderInv else aggnOrderCycle]

/-- Two encodings of the action of the cyclic group on three points. -/
def aggnOrderInput (b : Bool) : AggrInput :=
  (([0, 1, 2], aggnOrderGens b, [0, 1, 2], [0, 0, 0], [0, 0, 0]),
    ([0, 1, 2], aggnOrderGens b), 3)

theorem aggnOrder_wf (b : Bool) : RawGens.WF 3 (aggnOrderGens b) := by
  cases b <;> decide

theorem aggnOrder_inverse : decPerm 3 aggnOrderInv = (decPerm 3 aggnOrderCycle)⁻¹ := by
  have hw : RawPerm.WF 3 aggnOrderCycle := by decide
  have he : rawInv aggnOrderCycle = aggnOrderInv := by decide
  rw [← he, rawInv_of_wf hw, decPerm_encPerm]

/-- The generator lists describe exactly the same subgroup. -/
theorem aggnOrder_group : decGroup 3 (aggnOrderGens false) =
    decGroup 3 (aggnOrderGens true) := by
  have hc : decPerm 3 aggnOrderCycle ∈ decGroup 3 (aggnOrderGens false) :=
    Subgroup.subset_closure (by simp [aggnOrderGens])
  have hi : decPerm 3 aggnOrderInv ∈ decGroup 3 (aggnOrderGens true) :=
    Subgroup.subset_closure (by simp [aggnOrderGens])
  apply le_antisymm
  · apply (Subgroup.closure_le _).2
    intro σ hσ
    have he : σ = decPerm 3 aggnOrderCycle := by
      simpa [aggnOrderGens] using hσ
    rw [he, ← inv_inv (decPerm 3 aggnOrderCycle), ← aggnOrder_inverse]
    exact Subgroup.inv_mem _ hi
  · apply (Subgroup.closure_le _).2
    intro σ hσ
    have he : σ = decPerm 3 aggnOrderInv := by simpa [aggnOrderGens] using hσ
    rw [he, aggnOrder_inverse]
    exact Subgroup.inv_mem _ hc

def aggnOrderCtx : LCCtxWF 3 3 [0, 0, 0] [0, 1, 2] :=
  ⟨rfl, by decide, by decide, by decide, by decide⟩

noncomputable def aggnOrderPhi : decGroup 3 (aggnOrderGens false) →* Perm (Fin 3) :=
  (decGroup 3 (aggnOrderGens false)).subtype

def aggnOrderState (b : Bool) : RawLCSt := ([], aggnOrderGens b, aggnOrderGens b)

theorem aggnOrder_whole : winSet 3 [0, 1, 2] = Set.univ := by
  ext v
  fin_cases v <;> simp [winSet]

theorem aggnOrder_bigGT : bigGT aggnOrderPhi (winSet 3 [0, 1, 2]) =
    decGroup 3 (aggnOrderGens false) := by
  ext σ
  rw [mem_stabIn, aggnOrder_whole]
  exact ⟨fun ⟨h, _⟩ => h, fun h => ⟨h, Set.image_univ_of_surjective σ.surjective⟩⟩

theorem aggnOrder_psi (b : Bool)
    (hle : decGroup 3 (aggnOrderGens b) ≤ bigGT aggnOrderPhi (winSet 3 [0, 1, 2]))
    (g : decGroup 3 (aggnOrderGens b)) :
    psiFin aggnOrderPhi [0, 1, 2] aggnOrderCtx.nodup aggnOrderCtx.ltM hle g =
      (g : Perm (Fin 3)) := by
  apply Equiv.ext
  intro k
  apply Fin.ext
  have he := psiFin_val (ϕ := aggnOrderPhi) (hH := hle)
    (hnd := aggnOrderCtx.nodup) (hlt := aggnOrderCtx.ltM) g k.isLt
  have hget (v : Fin 3) : ([0, 1, 2] : List ℕ).getD (v : ℕ) 0 = (v : ℕ) := by
    fin_cases v <;> rfl
  rw [hget] at he
  convert he using 1
  congr 2
  apply Fin.ext
  fin_cases k <;> rfl

/-- Both raw states satisfy `StateFor` for exactly the same initial stage. -/
theorem aggnOrder_stateFor (b : Bool) :
    StateFor aggnOrderCtx
      (stages aggnOrderPhi (decStrN 3 [0, 0, 0]) (winSet 3 [0, 1, 2]) 0)
      (aggnOrderState b) := by
  refine ⟨by change ([] : List ℕ).Nodup; decide, by simp [aggnOrderState],
    by change winSet 3 [] = ∅; ext v; simp [winSet], aggnOrder_wf b,
    by cases b <;> decide, ?_, aggnOrder_wf b, ?_⟩
  · change decGroup 3 (aggnOrderGens b) = bigGT aggnOrderPhi (winSet 3 [0, 1, 2])
    rw [aggnOrder_bigGT]
    cases b
    · rfl
    · exact aggnOrder_group.symm
  · intro hle
    refine ⟨rfl, ?_⟩
    intro i hi hi'
    exact (aggnOrder_psi b hle
      ⟨((aggnOrderGens b).map (decPerm 3))[i],
        Subgroup.subset_closure (List.getElem_mem hi)⟩).symm

/-- Once the work list is empty, the remaining table-building fuel does nothing. -/
theorem aggnBuild_stops (p : List ℕ × RawGens) (k : ℕ) (t : RawTable)
    (hk : k ≤ (rawFuelList p).length)
    (hs : (rawBuildRound^[k]) (rawInitTable p.1, p.2) = (t, [])) :
    rawBuildTable p = t := by
  have hf : ∀ q, (rawBuildRound^[q]) (t, []) = (t, []) := by
    intro q
    induction q with
    | zero => rfl
    | succ q ih => rw [Function.iterate_succ_apply', ih]; rfl
  rw [rawBuildTable, foldl_const_eq, ← Nat.sub_add_cancel hk,
    Function.iterate_add_apply, hs, hf]

theorem aggnBuild_flush (t : RawTable) (q : RawGens)
    (hq : ∀ g ∈ q, rawSiftStuck (t, g) = none) :
    (rawBuildRound^[q.length]) (t, q) = (t, []) := by
  induction q with
  | nil => rfl
  | cons g q ih =>
    rw [List.length_cons, Function.iterate_succ_apply,
      rawBuildRound_cons_none (hq g List.mem_cons_self)]
    exact ih (fun g hg => hq g (List.mem_cons_of_mem _ hg))

theorem aggnBuild_ready (p : List ℕ × RawGens) (t : RawTable) (q : RawGens)
    (hk : q.length + 2 ≤ (rawFuelList p).length)
    (hs : (rawBuildRound^[2]) (rawInitTable p.1, p.2) = (t, q))
    (hq : ∀ g ∈ q, rawSiftStuck (t, g) = none) : rawBuildTable p = t := by
  apply aggnBuild_stops p (q.length + 2) t hk
  rw [Function.iterate_add_apply, hs]
  exact aggnBuild_flush t q hq

def aggnOrderExtTable (b : Bool) : RawTable :=
  [(if b then [(1, [1, 2, 0, 4, 5, 3]), (2, [2, 0, 1, 5, 3, 4]),
      (0, [0, 1, 2, 3, 4, 5])] else
    [(2, [2, 0, 1, 5, 3, 4]), (1, [1, 2, 0, 4, 5, 3]), (0, [0, 1, 2, 3, 4, 5])]),
    [(1, [0, 1, 2, 3, 4, 5])], [(2, [0, 1, 2, 3, 4, 5])],
    [(3, [0, 1, 2, 3, 4, 5])], [(4, [0, 1, 2, 3, 4, 5])], [(5, [0, 1, 2, 3, 4, 5])]]

def aggnOrderExtQueue (b : Bool) : RawGens :=
  let g := if b then [2, 0, 1, 5, 3, 4] else [1, 2, 0, 4, 5, 3]
  let gi := if b then [1, 2, 0, 4, 5, 3] else [2, 0, 1, 5, 3, 4]
  [gi] ++ List.replicate 14 g ++ List.replicate 2 [0, 1, 2, 3, 4, 5] ++ List.replicate 12 gi

def aggnOrderExtFirst (b : Bool) : RawTable × RawGens :=
  let g := if b then [2, 0, 1, 5, 3, 4] else [1, 2, 0, 4, 5, 3]
  let gi := if b then [1, 2, 0, 4, 5, 3] else [2, 0, 1, 5, 3, 4]
  ([[(if b then 2 else 1, g), (0, [0, 1, 2, 3, 4, 5])],
    [(1, [0, 1, 2, 3, 4, 5])], [(2, [0, 1, 2, 3, 4, 5])],
    [(3, [0, 1, 2, 3, 4, 5])], [(4, [0, 1, 2, 3, 4, 5])], [(5, [0, 1, 2, 3, 4, 5])]],
    List.replicate 2 gi ++ List.replicate 12 g)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem aggnOrder_extTable (b : Bool) :
    rawWinTable ((rawExtDom ([0, 0, 0], [0, 1, 2]),
      rawExtGens (aggnOrderGens b, aggnOrderGens b)),
        rawExtWin ([0, 0, 0], [0, 1, 2])) = aggnOrderExtTable b := by
  unfold rawWinTable
  have hin : rawConj (rawOrd (rawExtDom ([0, 0, 0], [0, 1, 2]),
      rawExtWin ([0, 0, 0], [0, 1, 2])), rawExtGens (aggnOrderGens b, aggnOrderGens b)) =
      [if b then [2, 0, 1, 5, 3, 4] else [1, 2, 0, 4, 5, 3]] := by
    cases b <;> decide +kernel
  rw [hin]
  apply aggnBuild_ready _ _ (aggnOrderExtQueue b)
  · cases b <;> decide +kernel
  · have h1 : rawBuildRound (rawInitTable (rawExtDom ([0, 0, 0], [0, 1, 2])),
        [if b then [2, 0, 1, 5, 3, 4] else [1, 2, 0, 4, 5, 3]]) = aggnOrderExtFirst b := by
      cases b <;> decide +kernel
    rw [show (rawBuildRound^[2]) _ = rawBuildRound (rawBuildRound _) from rfl, h1]
    cases b <;> decide +kernel
  · cases b <;> decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem aggnOrder_chainRep (b : Bool) :
    rawWinChainRep ((rawExtDom ([0, 0, 0], [0, 1, 2]),
      rawExtGens (aggnOrderGens b, aggnOrderGens b)),
      (rawExtWin ([0, 0, 0], [0, 1, 2]), 0)) =
        (if b then [1, 2, 0, 4, 5, 3] else [2, 0, 1, 5, 3, 4]) := by
  rw [rawWinChainRep, aggnOrder_extTable]
  cases b <;> decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem aggnOrder_cosetRep (b : Bool) :
    rawCosetRepBin ((rawExtDom ([0, 0, 0], [0, 1, 2]),
      rawExtGens (aggnOrderGens b, aggnOrderGens b)),
      (rawExtWin ([0, 0, 0], [0, 1, 2]), 0)) =
        (if b then [1, 2, 0, 4, 5, 3] else [2, 0, 1, 5, 3, 4]) := by
  rw [rawCosetRepBin, aggnOrder_chainRep]
  have ho : rawOrd (rawExtDom ([0, 0, 0], [0, 1, 2]),
      rawExtWin ([0, 0, 0], [0, 1, 2])) = [3, 4, 5, 0, 1, 2] := by decide +kernel
  rw [ho]
  cases b <;> decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem aggnOrder_actionRep (b : Bool) :
    actCosetRep ((([0, 0, 0], aggnOrderGens b), ([0, 1, 2], aggnOrderGens b)), 0) =
      (if b then aggnOrderCycle else aggnOrderInv) := by
  unfold actCosetRep
  rw [aggnOrder_cosetRep]
  cases b <;> decide +kernel

/-- The first raw representative in the first encoding is the inverse cycle. -/
theorem aggnOrder_rep_false :
    lcRep (aggnOrderInput false).1 (aggnOrderInput false).2.1 0 = aggnOrderInv := by
  simp only [lcRep, aggnOrderInput]
  rw [aggnOrder_actionRep false]
  decide +kernel

/-- The first raw representative in the second encoding is the forward cycle. -/
theorem aggnOrder_rep_true :
    lcRep (aggnOrderInput true).1 (aggnOrderInput true).2.1 0 = aggnOrderCycle := by
  simp only [lcRep, aggnOrderInput]
  rw [aggnOrder_actionRep true]
  decide +kernel

theorem aggnOrder_perm_ne : decPerm 3 aggnOrderCycle ≠ decPerm 3 aggnOrderInv := by
  intro h
  have he := congrArg (fun σ : Perm (Fin 3) => (σ 0 : ℕ)) h
  dsimp only at he
  rw [decPerm_val_of_wf (by decide : RawPerm.WF 3 aggnOrderCycle),
    decPerm_val_of_wf (by decide : RawPerm.WF 3 aggnOrderInv)] at he
  exact (by decide : (1 : ℕ) ≠ 2) he

theorem aggnOrder_kernel (b : Bool) :
    decGroup 3 (lcKer (aggnOrderInput b).1 (aggnOrderInput b).2.1) = ⊥ := by
  have hs := aggnOrder_stateFor b
  have hk := aggrKernel_eq hs
  simp only [aggrInputOf, lcInst, lcKer, aggnOrderState] at hk
  simp only [aggnOrderInput, lcKer]
  apply hk.trans
  ext σ
  rw [mem_kerN, Subgroup.mem_bot]
  constructor
  · rintro ⟨hσ, hσker⟩
    have hG : σ ∈ decGroup 3 (aggnOrderGens false) := aggnOrder_bigGT ▸ hσ
    have hle : decGroup 3 (aggnOrderGens false) ≤
        bigGT aggnOrderPhi (winSet 3 [0, 1, 2]) := le_of_eq aggnOrder_bigGT.symm
    refine (aggnOrder_psi false hle ⟨σ, hG⟩).symm.trans ?_
    change (tName 3 [0, 1, 2] aggnOrderCtx.nodup aggnOrderCtx.ltM).symm.permCongrHom
      (psiOn aggnOrderPhi (winSet 3 [0, 1, 2])
        (stages aggnOrderPhi (decStrN 3 [0, 0, 0]) (winSet 3 [0, 1, 2]) 0).le
        ⟨σ, hσ⟩) = 1
    rw [hσker, map_one]
  · rintro rfl
    exact ⟨one_mem _, map_one _⟩

/-- The first representatives even give different candidate cosets. The
difference is not just the choice of a representative inside one coset. -/
theorem aggnOrder_firstCoset_ne :
    decCoset 3 (aggrBegin (aggnOrderInput false) 0) ≠
      decCoset 3 (aggrBegin (aggnOrderInput true) 0) := by
  have he (b : Bool) : decCoset 3 (aggrBegin (aggnOrderInput b) 0) =
      {decPerm 3 (lcRep (aggnOrderInput b).1 (aggnOrderInput b).2.1 0)} := by
    ext σ
    simp [aggrBegin, decCoset, aggnOrder_kernel]
  rw [he false, he true, aggnOrder_rep_false, aggnOrder_rep_true]
  intro h
  exact aggnOrder_perm_ne (Set.singleton_injective h).symm

/-- Equal lists give equal first representatives, without unfolding the raw routines. -/
theorem aggnReps_first {n : ℕ} {p q : AggrInput}
    (hp : 0 < (aggrReps n p).length) (he : aggrReps n p = aggrReps n q) :
    decPerm n (lcRep p.1 p.2.1 0) = decPerm n (lcRep q.1 q.2.1 0) := by
  have hq : 0 < (aggrReps n q).length := he ▸ hp
  exact (getElem_lcPerms n p.1 p.2 hp).symm.trans
    ((List.getElem_of_eq he hp).trans (getElem_lcPerms n q.1 q.2 hq))

/-- Even the decoded representative lists depend on the generator encoding. -/
theorem aggnOrder_reps_ne : aggrReps 3 (aggnOrderInput false) ≠
    aggrReps 3 (aggnOrderInput true) := by
  intro he
  have hp : 0 < (aggrReps 3 (aggnOrderInput false)).length := by
    rw [aggrReps, length_lcPerms]
    decide
  have he' := aggnReps_first hp he
  rw [aggnOrder_rep_false, aggnOrder_rep_true] at he'
  exact aggnOrder_perm_ne he'.symm

def aggnOrderBaseTable (b : Bool) : RawTable :=
  [(if b then [(1, aggnOrderCycle), (2, aggnOrderInv), (0, [0, 1, 2])] else
    [(2, aggnOrderInv), (1, aggnOrderCycle), (0, [0, 1, 2])]),
    [(1, [0, 1, 2])], [(2, [0, 1, 2])]]

def aggnOrderBaseQueue (b : Bool) : RawGens :=
  let g := if b then aggnOrderInv else aggnOrderCycle
  let gi := if b then aggnOrderCycle else aggnOrderInv
  [gi] ++ List.replicate 8 g ++ List.replicate 2 [0, 1, 2] ++ List.replicate 6 gi

def aggnOrderBaseFirst (b : Bool) : RawTable × RawGens :=
  let g := if b then aggnOrderInv else aggnOrderCycle
  let gi := if b then aggnOrderCycle else aggnOrderInv
  ([[(if b then 2 else 1, g), (0, [0, 1, 2])], [(1, [0, 1, 2])], [(2, [0, 1, 2])]],
    List.replicate 2 gi ++ List.replicate 6 g)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem aggnOrder_baseTable (b : Bool) :
    rawBuildTable ([0, 0, 0], aggnOrderGens b) = aggnOrderBaseTable b := by
  apply aggnBuild_ready _ _ (aggnOrderBaseQueue b)
  · cases b <;> decide +kernel
  · have h1 : rawBuildRound (rawInitTable [0, 0, 0], aggnOrderGens b) =
        aggnOrderBaseFirst b := by cases b <;> decide +kernel
    rw [show (rawBuildRound^[2]) _ = rawBuildRound (rawBuildRound _) from rfl, h1]
    cases b <;> decide +kernel
  · cases b <;> decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- The normalizer used by `lcStepWith` does not erase this difference. -/
theorem aggnOrder_tidy :
    tidyGens ([0, 0, 0], aggnOrderGens false) =
      [aggnOrderInv, aggnOrderCycle, [0, 1, 2], [0, 1, 2], [0, 1, 2]] ∧
    tidyGens ([0, 0, 0], aggnOrderGens true) =
      [aggnOrderCycle, aggnOrderInv, [0, 1, 2], [0, 1, 2], [0, 1, 2]] := by
  have he (b : Bool) : normGens ([0, 0, 0], aggnOrderGens b) = aggnOrderGens b := by
    cases b <;> decide +kernel
  simp only [tidyGens, rawShorten, he, aggnOrder_baseTable]
  decide +kernel

/-- Equal decoded groups do not determine the order required by a fixed `E`. -/
theorem aggnOrder_no_group_factor :
    ¬ ∃ f : Subgroup (Perm (Fin 3)) → List (Perm (Fin 3)),
      ∀ b, aggrReps 3 (aggnOrderInput b) = f (decGroup 3 (aggnOrderGens b)) := by
  rintro ⟨f, hf⟩
  apply aggnOrder_reps_ne
  rw [hf false, hf true, aggnOrder_group]

theorem aggnOrder_index_pos (b : Bool) :
    0 < (aggrReps 3 (aggrInputOf (([0, 0, 0], [0, 1, 2]), aggnOrderState b))).length := by
  simp only [aggrReps, length_lcPerms, aggrInputOf]
  have hI := lcwf_lcInst (aggnOrder_stateFor b)
  obtain ⟨_, _, ⟨ψ, hψ⟩, _⟩ := hI.2 ([0, 1, 2], aggnOrderGens b)
    (lcIdx (([0, 0, 0], [0, 1, 2]), aggnOrderState b)) rfl
  rw [lcWidth_eq_card_range hI rfl hψ]
  exact Nat.card_pos

theorem aggnOrder_loop_rep (b : Bool) :
    lcRep (aggrInputOf (([0, 0, 0], [0, 1, 2]), aggnOrderState b)).1
      (aggrInputOf (([0, 0, 0], [0, 1, 2]), aggnOrderState b)).2.1 0 =
        (if b then aggnOrderCycle else aggnOrderInv) := by
  simp only [aggrInputOf, lcInst, lcRep, aggnOrderState]
  rw [aggnOrder_actionRep]
  cases b <;> decide +kernel

/-- `StateFor` alone cannot identify a stage's list with one fixed list.
Both witnesses encode the same stage and the same action on the test set. -/
theorem aggnOrder_no_stateFor_factor :
    ¬ ∃ L : List (Perm (Fin 3)), ∀ st,
      StateFor aggnOrderCtx
        (stages aggnOrderPhi (decStrN 3 [0, 0, 0]) (winSet 3 [0, 1, 2]) 0) st →
      aggrReps 3 (aggrInputOf (([0, 0, 0], [0, 1, 2]), st)) = L := by
  rintro ⟨L, hL⟩
  have he := (hL _ (aggnOrder_stateFor false)).trans (hL _ (aggnOrder_stateFor true)).symm
  have he' := aggnReps_first (aggnOrder_index_pos false) he
  rw [aggnOrder_loop_rep false, aggnOrder_loop_rep true] at he'
  exact aggnOrder_perm_ne he'.symm

end Algo
