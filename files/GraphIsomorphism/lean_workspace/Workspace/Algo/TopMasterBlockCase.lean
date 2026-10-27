import Workspace.Algo.TopMasterBlockRoute

/-! # The block route supplies the step-5 case of line 1
The route test of step 5 says that the window group is transitive and that
its action on the computed minimal blocks is small. This file builds the
paper's `Line1Case.block` evidence from the computed blocks, with the
machine's image and orbit enumerations installed in the record, and shows
that the step-5 carrier runs its coset branch followed by the shift back to
the node's candidate coset.
-/
set_option maxHeartbeats 1200000
namespace Algo
open RAM RAM.Targets Babai Equiv
open scoped Classical Pointwise

/-- The one-element subsets of a type, numbered by the type. -/
noncomputable def binomOneEquiv (α : Type*) [DecidableEq α] : α ≃ binom α 1 where
  toFun a := ⟨{a}, Finset.card_singleton a⟩
  invFun s := (Finset.card_eq_one.mp s.2).choose
  left_inv a := by
    have h := (Finset.card_eq_one.mp (Finset.card_singleton a)).choose_spec
    exact (Finset.singleton_inj.mp h).symm
  right_inv s := Subtype.ext (Finset.card_eq_one.mp s.2).choose_spec.symm

@[simp] theorem binomOneEquiv_coe {α : Type*} [DecidableEq α] (a : α) :
    ((binomOneEquiv α a : binom α 1) : Finset α) = {a} := rfl

/-- **A numbering of the blocks is a link with `t = 1`.** If the action `φ`
is the block action read through a numbering `e` of the blocks, then the
blocks, labelled by the one-element subsets of the numbers, carry `φ` as the
induced action on `1`-sets. -/
noncomputable def blockNumberingLink {Ω : Type*} {G : Subgroup (Perm Ω)} {B : Set (Set Ω)}
    (hB : ∀ g ∈ G, ∀ U ∈ B, (g : Perm Ω) '' U ∈ B) {m : ℕ} (e : Fin m ≃ B) :
    MasterHintBlockLink (t := 1) hB
      (((permCongrHom e).symm.toMonoidHom).comp (blockHom G B hB)) where
  label := e.symm.trans (binomOneEquiv (Fin m))
  action g := by
    refine Equiv.ext fun s => Subtype.ext ?_
    obtain ⟨i, rfl⟩ := (binomOneEquiv (Fin m)).surjective s
    change (((e.symm.trans (binomOneEquiv (Fin m))) (blockHom G B hB g
      ((e.symm.trans (binomOneEquiv (Fin m))).symm (binomOneEquiv (Fin m) i))) : binom (Fin m) 1) :
        Finset (Fin m)) = _
    rw [tAction_apply_coe, binomOneEquiv_coe, Finset.image_singleton]
    simp only [Equiv.trans_apply, Equiv.symm_trans_apply, Equiv.symm_apply_apply,
      binomOneEquiv_coe]
    rfl

section Route
variable {n B C₀ : ℕ} {W : RawWinSI} (hW : AggnCheckedWindowWF n W)
    (hx : W.2.2.2.1.length = n)
    (hinv : IsInvariant (decGroup n W.2.1) (winSet n W.1))
    (hC : (max 64 B.factorial).factorial < C₀) (hr : masterReduceRoute B C₀ W = 3)

include hW hinv hC hr in
/-- The route test of step 5 leaves a window above `max 64 B!`. -/
theorem masterBlockRoute_window : max 64 B.factorial < W.1.length :=
  masterReduceRoute_large_window hW.2.2.1 hW.1 hW.2.1 hinv hC (by rw [hr]; decide)
    (by rw [hr]; decide)

include hW hinv hC hr in
theorem masterBlockRoute_two : 2 ≤ W.1.length := by
  have := masterBlockRoute_window hW hinv hC hr
  have := le_max_left 64 B.factorial
  omega

include hW hinv hr in
/-- The route test of step 5 includes the transitivity test of step 3. -/
theorem masterBlockRoute_transitive :
    IsTransitive (decGroup W.1.length (primitiveWindowInput W).1) := by
  obtain ⟨_, _, ht, _⟩ := (masterReduceRoute_block B C₀ W).mp hr
  exact (rawIsTransitive_eq_true_iff (rawRestrictGens_wf_of_raw hW.2.2.1 hW.1 hW.2.1 hinv)
    rfl).mp ht

/-- The computed minimal blocks of step 4, as a block record of the group frame. -/
noncomputable def masterBlockBase : Babai.BlockData (masterGroupInstance n W) :=
  masterCamBlockData hW.2.2.1 hW.1 hW.2.1 hinv (masterBlockRoute_transitive hW hinv hr)
    (masterBlockRoute_two hW hinv hC hr)

/-- The numbering of the computed minimal blocks. -/
noncomputable def masterBlockNumbering :
    Fin (rawMinBlocks ((primitiveWindowInput W).1, W.1)).length ≃
      (masterBlockBase hW hinv hC hr).ℬ :=
  masterCamBlockEquiv hW.2.2.1 hW.1 hW.2.1 hinv (masterBlockRoute_transitive hW hinv hr)
    (masterBlockRoute_two hW hinv hC hr)

/-- The block action of the window group, read through the numbering. -/
noncomputable def masterStepFiveHom :
    restrictTo (decGroup n W.2.1) (winSet n W.1) hinv →*
      Perm (Fin (rawMinBlocks ((primitiveWindowInput W).1, W.1)).length) :=
  ((permCongrHom (masterBlockNumbering hW hinv hC hr)).symm.toMonoidHom).comp
    (blockHom (masterBlockBase hW hinv hC hr).windowGroup (masterBlockBase hW hinv hC hr).ℬ
      (masterBlockBase hW hinv hC hr).system.permutes)

include hx in
/-- Read through the numbering, the block action of the restriction is the
action the machine computed. -/
theorem masterStepFiveHom_restrict :
    (masterStepFiveHom hW hinv hC hr).comp (restrictOnto hinv) =
      masterWindowBlockHom hx hW.2.2.1 hW.1 hW.2.1 hinv (masterBlockRoute_transitive hW hinv hr)
        (masterBlockRoute_two hW hinv hC hr) := by
  ext g : 1
  have hrow := masterCamBlockHom_row hx hW.2.2.1 hW.1 hW.2.1 hinv
    (masterBlockRoute_transitive hW hinv hr) (masterBlockRoute_two hW hinv hC hr) g
  change (permCongrHom (masterBlockNumbering hW hinv hC hr)).symm
    (blockHom _ _ _ (restrictOnto hinv g)) = _
  exact (MulEquiv.symm_apply_eq _).mpr hrow.symm

include hx in
theorem masterStepFiveHom_wf :
    RawAction.WF n (rawMinBlocks ((primitiveWindowInput W).1, W.1)).length
      (masterDescAction (masterWindowBlockInput W))
      ((masterStepFiveHom hW hinv hC hr).comp (restrictOnto hinv)) := by
  have h := masterWindowBlockAction_wf hx hW.2.2.1 hW.1 hW.2.1 hinv
    (masterBlockRoute_transitive hW hinv hr) (masterBlockRoute_two hW hinv hC hr)
  rw [← masterStepFiveHom_restrict hW hx hinv hC hr] at h
  exact h

/-- The numbering, as the `t = 1` link of the line-2 matching. -/
noncomputable def masterBlockLink :
    MasterHintBlockLink (t := 1)
      (masterBlockBase hW hinv hC hr).system.isInvariantPartitionOn.permutes
      (masterStepFiveHom hW hinv hC hr) :=
  blockNumberingLink _ (masterBlockNumbering hW hinv hC hr)

include hW hinv hC hr in
theorem masterBlockBase_two :
    ∃ U ∈ (masterBlockBase hW hinv hC hr).ℬ, ∃ V ∈ (masterBlockBase hW hinv hC hr).ℬ, U ≠ V :=
  (masterBlockBase hW hinv hC hr).two_blocks

include hW hinv hC hr in
theorem masterBlockRoute_blocks : 1 < (rawMinBlocks ((primitiveWindowInput W).1, W.1)).length := by
  obtain ⟨U, hU, V, hV, hne⟩ := masterBlockBase_two hW hinv hC hr
  let e := masterBlockNumbering hW hinv hC hr
  by_contra h
  have hsub : Subsingleton (Fin (rawMinBlocks ((primitiveWindowInput W).1, W.1)).length) :=
    Fin.subsingleton_iff_le_one.mpr (by omega)
  have h := Subsingleton.elim (e.symm ⟨U, hU⟩) (e.symm ⟨V, hV⟩)
  rw [e.symm_apply_eq, Equiv.apply_symm_apply] at h
  exact hne (congrArg Subtype.val h)

include hW hx hinv hC hr in
/-- **The scan of step 5 is complete.** The route test bounds `|Ḡ|` by
`line1Cost |Δ|`, which the ground table covers. -/
theorem masterBlockRoute_fuel :
    masterDescFuel 3 (masterWindowBlockInput W) =
      List.range (masterDescWidth (masterWindowBlockInput W)) := by
  have hwin := masterBlockRoute_window hW hinv hC hr
  have h64 := le_max_left 64 B.factorial
  have hlen : W.1.length ≤ n := length_le_of_nodup_lt hW.1 hW.2.1
  have hc := masterReduceRoute_block_cost hx hW.2.2.1 hW.1 hW.2.1 hinv hC hr
  have hp := masterWindowBlockAction_wf hx hW.2.2.1 hW.1 hW.2.1 hinv
    (masterBlockRoute_transitive hW hinv hr) (masterBlockRoute_two hW hinv hC hr)
  apply masterDescFuel_eq_of_ground
  · change 4 ≤ W.2.2.2.1.length
    omega
  · have hbound : W.1.length ^ (2 + Nat.log 2 W.1.length) ≤
        W.2.2.2.1.length ^ (Nat.log 2 W.2.2.2.1.length + 2) := by
      rw [hx, Nat.add_comm 2]
      exact (Nat.pow_le_pow_left hlen _).trans
        (Nat.pow_le_pow_right (by omega) (by have := Nat.log_mono_right (b := 2) hlen; omega))
    have hgs : RawGens.WF (masterWindowBlockAction W).2.1.length (masterWindowBlockAction W).2.2 :=
      hp.2.1 ▸ hp.2.2.2.1
    change rawOrder ((masterWindowBlockAction W).2.1, (masterWindowBlockAction W).2.2) ≤ _
    change Nat.card (decGroup (masterWindowBlockAction W).2.1.length
      (masterWindowBlockAction W).2.2) ≤ line1Cost W.1.length at hc
    generalize masterWindowBlockAction W = A at hgs hc ⊢
    have he := rawOrder_spec A.2.1 rfl (A.2.2.map (decPerm A.2.1.length))
    rw [map_encPerm_decPerm hgs] at he
    rw [he]
    exact hc.trans hbound
/-- **§11.3, step 5, from the machine's route.** The block record of the group
frame: the computed minimal blocks, with the machine's image elements and
kernel-orbit order installed as its enumeration. -/
noncomputable def masterStepFiveData : Babai.BlockData (masterGroupInstance n W) :=
  { masterBlockBase hW hinv hC hr with
    enum := masterDescPreparedEnum (p := masterWindowBlockInput W) hinv
      (masterStepFiveHom hW hinv hC hr) (masterStepFiveHom_wf hW hx hinv hC hr) hW.2.1
      (masterBlockBase hW hinv hC hr).system.isInvariantPartitionOn
      (masterBlockLink hW hinv hC hr) le_rfl (masterBlockRoute_blocks hW hinv hC hr)
      hW.2.2.2.2.2.1 (masterBlockRoute_fuel hW hx hinv hC hr) }

include hW hx hinv hC hr in
/-- The test of step 5 at the allowance of `Babai.Line1Choice`: `|Ḡ| ≤ line1Cost |Δ|`. -/
theorem masterStepFive_cost :
    Nat.card (onBlocks (masterStepFiveData hW hx hinv hC hr).windowGroup
      (masterStepFiveData hW hx hinv hC hr).ℬ
      (masterStepFiveData hW hx hinv hC hr).system.permutes) ≤
        line1Cost (masterGroupInstance n W).windowSize := by
  have hsize : (masterGroupInstance n W).windowSize = W.1.length := ncard_winSet W.1 hW.1 hW.2.1
  have hg := masterCamBlockEquiv_group hW.2.2.1 hW.1 hW.2.1 hinv
    (masterBlockRoute_transitive hW hinv hr) (masterBlockRoute_two hW hinv hC hr)
  have hc := masterReduceRoute_block_cost hx hW.2.2.1 hW.1 hW.2.1 hinv hC hr
  have hp := masterWindowBlockAction_wf hx hW.2.2.1 hW.1 hW.2.1 hinv
    (masterBlockRoute_transitive hW hinv hr) (masterBlockRoute_two hW hinv hC hr)
  change Nat.card (onBlocks (masterBlockBase hW hinv hC hr).windowGroup
    (masterBlockBase hW hinv hC hr).ℬ (masterBlockBase hW hinv hC hr).system.permutes) ≤ _
  change _ = onBlocks (masterBlockBase hW hinv hC hr).windowGroup
    (masterBlockBase hW hinv hC hr).ℬ (masterBlockBase hW hinv hC hr).system.permutes at hg
  rw [hsize, ← hg]
  refine le_of_eq_of_le (Subgroup.card_map_of_injective ?_) ?_
  · exact MulEquiv.injective _
  change Nat.card (decGroup (masterWindowBlockAction W).2.1.length
    (masterWindowBlockAction W).2.2) ≤ line1Cost W.1.length at hc
  have h1 := hp.2.1
  clear hg
  revert hc
  generalize (masterWindowBlockAction W).2.2 = gs
  intro hc
  rw [h1] at hc
  exact hc

/-- **Section 15, line 1, step 5 from the machine's route.** The paper's
`Line1Case.block` evidence at the group frame of the node. -/
noncomputable def masterStepFiveCase :
    Line1Case (masterGroupInstance n W) (line1Cost (masterGroupInstance n W).windowSize) :=
  .block (masterStepFiveData hW hx hinv hC hr) (masterStepFive_cost hW hx hinv hC hr)

/-- **Section 15, line 1, step 5 on the RAM.** At a block-route node, the
step-5 carrier runs the coset branch of the paper's step-5 case in the group
frame of the node, followed by the shift back to its candidate coset. -/
theorem masterStepFiveCase_loop (a b : ℕ) :
    LoopMatch (masterAdmittedRound a b masterBlockOps) (fun J => decWinSI n J.1) (decCoset n)
      (W, none) (masterBlockOps.width (W, none)) 0 (masterBlockOps.init (W, none))
      ((masterStepFiveCase hW hx hinv hC hr).cosetBranch.bind
        (fun A : Set (Perm (Fin n)) => .done (decPerm n W.2.2.1 • A))) :=
  masterBlock_match (p := masterWindowBlockInput W) hinv
    (masterStepFiveHom hW hinv hC hr) (masterStepFiveHom_wf hW hx hinv hC hr) hW.2.1
    (masterBlockBase hW hinv hC hr).system.isInvariantPartitionOn
    (masterBlockLink hW hinv hC hr) (masterBlockRoute_blocks hW hinv hC hr)
    (masterBlockBase_two hW hinv hC hr) hW.2.2.2.2.2.1 hW.2.2.2.2.2.2
    (masterBlockRoute_fuel hW hx hinv hC hr) hW.1 rfl a b
end Route
end Algo
