import Workspace.Algo.TopMasterCameronSelectMatch
import Workspace.Algo.TopMasterDescentPrepared

/-! # The Cameron branch in the group frame of its node
Remark 11.1.4 reads a coset node in the frame of its group. The branch
moves the candidate to the identity and shifts the target string by the
inverse candidate. The transitive case keeps that whole target, as the
step-6 calls of Eq. (62) do. The intransitive case restores the source
outside the window, as the window lift of step 3 does. The final shift
returns the answer to the candidate coset of the node.
-/
namespace Algo
open RAM RAM.Targets Babai Equiv
open scoped Pointwise

/-- The node in its group frame. The target depends on the case of step 6. -/
def masterCamPrepared (q : RawCameron × MasterDescInput) : RawCameron × MasterDescInput :=
  (q.1, ((q.2.1.1, q.2.1.2.1, rawOne q.2.1.2.2.2.1, q.2.1.2.2.2.1,
    if masterCamHasHint q then top4aTarget (q.2.1.2.2.2.1, q.2.1.2.2.1, q.2.1.2.2.2.2)
    else (masterChainPrepared q.2.1).2.2.2.2), q.2.2))

theorem polyFun_masterCamPrepared : PolyFun masterCamPrepared := by
  have hW : PolyFun (fun q : RawCameron × MasterDescInput => q.2.1) := polyFun_snd.comp polyFun_fst
  have hx : PolyFun (fun q : RawCameron × MasterDescInput => q.2.1.2.2.2.1) :=
    (((hW.comp polyFun_snd).comp polyFun_snd).comp polyFun_snd).comp polyFun_fst
  have hr : PolyFun (fun q : RawCameron × MasterDescInput => q.2.1.2.2.1) :=
    ((hW.comp polyFun_snd).comp polyFun_snd).comp polyFun_fst
  have hy : PolyFun (fun q : RawCameron × MasterDescInput => q.2.1.2.2.2.2) :=
    (((hW.comp polyFun_snd).comp polyFun_snd).comp polyFun_snd).comp polyFun_snd
  have ht := (hx.pair (hr.pair hy)).comp polyFun_top4aTarget
  have he : PolyFun (fun q : RawCameron × MasterDescInput => (masterChainPrepared q.2.1).2.2.2.2) :=
    (((((hW.comp polyFun_masterChainPrepared).comp polyFun_snd).comp polyFun_snd).comp
      polyFun_snd).comp polyFun_snd)
  exact polyFun_fst.pair ((((hW.comp polyFun_fst).pair ((hW.comp (polyFun_snd.comp polyFun_fst)).pair
    ((hx.comp polyFun_rawOne).pair (hx.pair
      (PolyFun.ite polyFun_masterCamHasHint ht he))))).pair (polyFun_snd.comp polyFun_snd)))

/-- The preparation keeps the window, the generators, the source and the action rows. -/
theorem masterCamPrepared_action (q : RawCameron × MasterDescInput) :
    masterDescAction (masterCamPrepared q).2 = masterDescAction q.2 := rfl

theorem masterCamPrepared_hint (q : RawCameron × MasterDescInput) :
    masterCamHasHint (masterCamPrepared q) = masterCamHasHint q := rfl

/-- The group-frame Cameron carrier with its final representative shift. -/
def masterCamPreparedOps (g : RawMasterSI → RawCameron × MasterDescInput) :
    MasterOps AggnRecomputeState :=
  masterShiftOps (masterCamSelectOps (fun p => masterCamPrepared (g p)))

set_option maxHeartbeats 1200000 in
/-- The local cost data of the prepared Cameron branch, uniform in the degree. -/
theorem masterCamPrepared_cost (a b : ℕ) (g : RawMasterSI → RawCameron × MasterDescInput)
    (hg : PolyFun g) (hsource : ∀ p, (g p).2.1.2.2.2.1 = p.1.2.2.2.1) :
    Nonempty (MasterOpsCost a b (masterCamPreparedOps g)) := by
  let f := fun p => masterCamPrepared (g p)
  have hf : PolyFun f := hg.comp polyFun_masterCamPrepared
  have hsf : ∀ p, (f p).2.1.2.2.2.1 = p.1.2.2.2.1 := hsource
  obtain ⟨B, hB, hmB, hb⟩ := masterStoredDesc_uniform_bounds a b
    (fun p => masterCamLists (f p)) (hf.comp polyFun_masterCamLists).quasiFun hsf
  let C := fun n => 16 * (B n + chainBound n + n + 10)
  have hC : QuasiPolyBound C := (polyBound_const 16).quasiPoly.mul
    (((hB.add polyBound_chainBound.quasiPoly).add polyBound_id.quasiPoly).add
      (polyBound_const 10).quasiPoly)
  have hmC : Monotone C := by
    intro i j hij
    have h1 := hmB hij
    have h2 := mono_chainBound hij
    dsimp only [C]
    omega
  obtain ⟨hw, hc, hi, hu, hfin⟩ := masterCamSelect_polyFun f hf
  refine ⟨⟨C, C, hC, hmC, hC,
    hw.quasiFun, hc.quasiFun, hi.quasiFun, hu.quasiFun,
    (quasiFun_masterShiftFinish hfin.quasiFun), ?_, ?_, ?_, ?_⟩⟩
  · intro p hp
    have h0 := masterCamFoldEmbed_size none
    rw [size_none] at h0
    have h1 : Enc.size (masterDescFoldInit (masterCamLists (f p))) ≤ B (masterDegree p) :=
      (hb p hp).1
    change Enc.size ((masterCamSelectOps f).init p) ≤ _
    dsimp only [masterCamSelectOps]
    split <;> dsimp only [C] <;> omega
  · intro p j s A hp _
    have h0 := masterCamFoldEmbed_size (masterDescJoin (p.1.2.2.2.1, s.2.2.2, A))
    have h1 := size_top2NormC_le (dom := p.1.2.2.2.1) rfl le_rfl
      (rawCosetJoin (p.1.2.2.2.1, s.2.2.2, A))
    change Enc.size (masterDescJoin (p.1.2.2.2.1, s.2.2.2, A)) ≤ chainBound (masterDegree p) at h1
    have h2 : Enc.size (masterDescFoldCombine (masterCamLists (f p), j, s, A)) ≤
        B (masterDegree p) := (hb p hp).2.1 j s A
    change Enc.size ((masterCamSelectOps f).combine (p, j, s, A)) ≤ _
    dsimp only [masterCamSelectOps]
    split <;> dsimp only [C] <;> omega
  · intro p s _
    exact (masterShiftOps_finish_size _ p s).trans (by unfold masterInputCap; omega)
  · intro p hp
    have h0 : masterCamOpenWidth (f p) ≤ masterDegree p :=
      (Nat.min_le_right _ _).trans_eq (congrArg List.length (hsf p))
    have h1 : masterDescFoldWidth (masterCamLists (f p)) ≤ B (masterDegree p) := (hb p hp).2.2
    change (masterCamSelectOps f).width p ≤ _
    dsimp only [masterCamSelectOps]
    split <;> dsimp only [C] <;> omega

/-- One raw carrier for the prepared Cameron branch at all ambient degrees. -/
theorem masterCamPrepared_runCostQ (a b : ℕ) (g : RawMasterSI → RawCameron × MasterDescInput)
    (hg : PolyFun g) (hsource : ∀ p, (g p).2.1.2.2.2.1 = p.1.2.2.2.1) :
    Nonempty (Round.RunCostQ (masterAdmittedRound a b (masterCamPreparedOps g))) :=
  (masterCamPrepared_cost a b g hg hsource).map MasterOpsCost.runCostQ

section Frame
variable {n : ℕ} {W : RawWinSI} (hx : W.2.2.2.1.length = n)

/-- In the transitive case the prepared target is the group-frame target. -/
theorem masterCamPrepared_target_hint (c : RawCameron) (u : List ℕ × RawGens)
    (hh : masterCamHasHint (c, (W, u)) = true) :
    decStrN n (masterCamPrepared (c, (W, u))).2.1.2.2.2.2 = (masterGroupInstance n W).y := by
  change decStrN n (if masterCamHasHint (c, (W, u)) then _ else _) = _
  rw [if_pos hh]
  rfl

include hx in
/-- In the intransitive case the prepared target is the window extension of step 3. -/
theorem masterCamPrepared_target_chain (hnd : W.1.Nodup) (hlt : ∀ u ∈ W.1, u < n)
    (c : RawCameron) (u : List ℕ × RawGens)
    (hh : masterCamHasHint (c, (W, u)) = false) :
    decStrN n (masterCamPrepared (c, (W, u))).2.1.2.2.2.2 =
      extendStr (winSet n W.1) (masterGroupInstance n W).x
        (restrictStr (winSet n W.1) (masterGroupInstance n W).y) := by
  change decStrN n (if masterCamHasHint (c, (W, u)) then _ else _) = _
  rw [if_neg (by simp [hh])]
  exact masterChainPrepared_target hx hnd hlt

include hx in
theorem masterCamPrepared_id (c : RawCameron) (u : List ℕ × RawGens) :
    decPerm n (masterCamPrepared (c, (W, u))).2.1.2.2.1 = 1 := decPerm_rawOne hx

include hx in
/-- The preparation keeps the checked window shape. -/
theorem masterCamPrepared_wf (c : RawCameron) (u : List ℕ × RawGens)
    (hW : AggnCheckedWindowWF n W) :
    AggnCheckedWindowWF n (masterCamPrepared (c, (W, u))).2.1 := by
  refine ⟨hW.1, hW.2.1, hW.2.2.1, hW.2.2.2.1, ?_, hW.2.2.2.2.2.1, ?_⟩
  · have h := wf_rawOne W.2.2.2.1
    rw [hx] at h
    exact h
  · change RawStr.WF n (2 * n + 1) (if masterCamHasHint (c, (W, u)) then _ else _)
    split
    · have hy := hW.2.2.2.2.2.2
      refine (masterStrWF_iff (by rw [top4aTarget_length]; exact hx)).mpr ?_
      intro i
      rw [top4aTarget_spec hx]
      exact (masterStrWF_iff hy.1).mp hy _
    · exact (masterChainPrepared_strings hW.2.2.2.2.2.1 hW.2.2.2.2.2.2 hW.1 hW.2.1).2
end Frame

section Match
variable {n m a b : ℕ} {p : MasterDescInput} {c : RawCameron}
    {φ : decGroup n p.1.2.1 →* Perm (Fin m)}
    (hp : RawAction.WF n m (masterDescAction p) φ) (h : c.WF m)
    (hhi : (decGroup m p.2.2).map (permCongrHom (decCameron c h)).toMonoidHom ≤
      wreathProduct (JohnsonS c.k c.t) c.s)
    (hW : AggnCheckedWindowWF n p.1) (hm : m ≤ p.1.1.length)
    (hidx : (camNbar c h).relIndex (decGroup m p.2.2) ≤ m)
    (hinv : IsInvariant (decGroup n p.1.2.1) (winSet n p.1.1))
    (hcap : masterCameronChildBound n ≤ masterInputCap a b n)
    (g : RawMasterSI → RawCameron × MasterDescInput) (hgp : g (p.1, none) = (c, p))

/-- The tree the prepared node runs: the step-6 tree in the group frame, and
the final shift back to the candidate coset. -/
noncomputable def masterCamPreparedTree (n : ℕ) (c : RawCameron) (p : MasterDescInput) :
    SIReduction (Fin n) ℕ (Set (Perm (Fin n))) :=
  (masterCamSelectTree n c (masterCamPrepared (c, p)).2).bind
    (fun A => .done (decPerm n p.1.2.2.1 • A))

include hp h hhi hW hm hidx hinv hcap hgp in
/-- **Section 11.3, steps 6–7, at a coset node.** The prepared carrier runs the
exact step-6 tree in the group frame and returns to the candidate coset. -/
theorem masterCamPrepared_match :
    LoopMatch (masterAdmittedRound a b (masterCamPreparedOps g)) (fun J => decWinSI n J.1)
      (decCoset n) (p.1, none) ((masterCamPreparedOps g).width (p.1, none)) 0
      ((masterCamPreparedOps g).init (p.1, none)) (masterCamPreparedTree n c p) := by
  apply masterShiftOps_match a b _ hW.2.2.2.2.2.1.1
  have hW' := masterCamPrepared_wf hW.2.2.2.2.2.1.1 c p.2 hW
  have hfp : (fun q => masterCamPrepared (g q)) (p.1, none) = masterCamPrepared (c, p) := by
    simp only [hgp]
  exact masterCamSelect_match_at (p := (masterCamPrepared (c, p)).2) hp h hhi hW' hm hidx hinv hcap
    _ (p.1, none) rfl rfl rfl hfp
end Match
end Algo
