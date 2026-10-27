import Workspace.Algo.AggCanonRecompute
import Workspace.LocalCertificates.StrongAggregate

/-! # A certificate run with fixed stage trees

The state keeps the current local-certificate state and the prepared lists of
its Recompute. The last answer of a Recompute opens the next stage at once.
-/

namespace Algo

open Babai Equiv
open scoped Classical Pointwise

section Transport

variable {ι ω ι' ω' α Ω Λ β : Type*}
  {R : Round ι ω α} {M : Round ι' ω' α}
  {decI : ι → SIInstance Ω Λ} {decI' : ι' → SIInstance Ω Λ}
  {decA : α → Set (Perm Ω)} {I : ι} {I' : ι'}

/-- Transport only actual calls. A phase endpoint may already open the next job. -/
theorem aggnLoopMatchK_sim
    (Rel : ℕ → ω → ℕ → ω' → Prop)
    (hc : ∀ j s k t, Rel j s k t → ∀ J, R.child (I, j, s) = some J →
      ∃ J', M.child (I', k, t) = some J' ∧ decI' J' = decI J ∧
        ∀ a, Rel (j + 1) (R.combine (I, j, s, a)) (k + 1) (M.combine (I', k, t, a)))
    {w j : ℕ} {s : ω} {S : SIReduction Ω Λ β}
    {Q : β → ℕ → ℕ → ω → Prop} (h : LoopMatchK R decI decA I w j s S Q) :
    ∀ k t, Rel j s k t → LoopMatchK M decI' decA I' w k t S
      (fun b w' k' t' => ∃ j' s', Q b w' j' s' ∧ Rel j' s' k' t') := by
  induction h with
  | done w j s b Q hQ =>
    intro k t hr
    exact .done w k t b _ ⟨j, s, hQ, hr⟩
  | call w j s J cont Q hJ hn ih =>
    intro k t hr
    obtain ⟨J', hc', hd, hnext⟩ := hc j s k t hr J hJ
    have hh := LoopMatchK.call (R := M) (decI := decI') (decA := decA) (I := I')
      w k t J' cont (fun b w' k' t' => ∃ j' s', Q b w' j' s' ∧ Rel j' s' k' t') hc' (fun a ha => by
        rw [hd] at ha ⊢
        exact ih a ha (k + 1) _ (hnext a))
    simpa only [hd] using hh

theorem aggnPhaseMatch_sim
    (Rel : ℕ → ω → ℕ → ω' → Prop)
    (hc : ∀ j s k t, Rel j s k t → ∀ J, R.child (I, j, s) = some J →
      ∃ J', M.child (I', k, t) = some J' ∧ decI' J' = decI J ∧
        ∀ a, Rel (j + 1) (R.combine (I, j, s, a)) (k + 1) (M.combine (I', k, t, a)))
    {c j k : ℕ} {s : ω} {t : ω'} {S : SIReduction Ω Λ β}
    {Q : β → ℕ → ω → Prop} (h : PhaseMatch R decI decA I c j s S Q)
    (hr : Rel j s k t) :
    PhaseMatch M decI' decA I' c k t S
      (fun b k' t' => ∃ j' s', Q b j' s' ∧ Rel j' s' k' t') := by
  intro r
  apply loopMatchK_mono_Q _ (aggnLoopMatchK_sim Rel hc (h r) k t hr)
  rintro b w' k' t' ⟨j', s', ⟨hw, hq⟩, hr'⟩
  exact ⟨hw, j', s', hq, hr'⟩

end Transport

/-- Current loop, prepared Recompute, local call count, chain state. -/
abbrev AggnCertState := RawLCLoop × AggnRecomputeInput × ℕ × AggnRecomputeState

abbrev AggnCertNode := RawLCLoop × Option RawWinSI

/-- A fixed call budget for one stage. -/
def aggnCertStageWidth (p : RawLCLoop) : ℕ := Nat.factorial p.1.2.length * p.1.1.length

def aggnCertWidth (p : RawLCLoop) : ℕ := p.1.1.length * aggnCertStageWidth p

def aggnCertOpen (c : ℕ) (p : RawLCLoop) : AggnCertState :=
  (p, aggnrInputOf c p, 0, aggnrInit (aggnrInputOf c p, none))

/-- Opening the next stage is part of the last combine of this stage. -/
def aggnCertPack (c : ℕ) (p : RawLCLoop) (j : ℕ) (v : AggnRecomputeState) : AggnCertState :=
  if v.1 < aggnrCount (aggnrInputOf c p) then (p, aggnrInputOf c p, j, v)
  else aggnCertOpen c (lcStepWith v.2.2.2 p)

def aggnCertChild (z : AggnCertNode × ℕ × AggnCertState) : Option AggnCertNode :=
  z.1.2.elim
    (if lcCond z.2.2.1 = true ∧ z.2.1 < aggnCertWidth z.1.1 then
      (aggnrChild ((z.2.2.2.1, none), z.2.2.2.2.1, z.2.2.2.2.2)).map
        (fun J => (z.1.1, J.2))
    else none) (fun _ => none)

def aggnCertCombine (c : ℕ) (z : AggnCertNode × ℕ × AggnCertState × RawCoset) : AggnCertState :=
  aggnCertPack c z.2.2.1.1 (z.2.2.1.2.2.1 + 1)
    (aggnrCombine ((z.2.2.1.2.1, none), z.2.2.1.2.2.1, z.2.2.1.2.2.2, z.2.2.2))

noncomputable def aggnCertDecode (n : ℕ) (I : AggnCertNode) : SIInstance (Fin n) ℕ :=
  I.2.elim (decLCSI n (lcInst I.1)) (decWinSI n)

theorem aggnCertChild_some {z : AggnCertNode × ℕ × AggnCertState} {J : AggnCertNode}
    (h : aggnCertChild z = some J) :
    z.1.2 = none ∧ ∃ W, J = (z.1.1, some W) := by
  cases ho : z.1.2 with
  | some W => simp [aggnCertChild, ho] at h
  | none =>
    simp only [aggnCertChild, ho, Option.elim_none] at h
    split at h
    next hg =>
      obtain ⟨J', hJ', he⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨q, _, _, _, _, _, hq⟩ := aggnrChild_some hJ'
      rw [hq] at he
      exact ⟨rfl, _, he.symm⟩
    next => simp at h

/-- The root is a phase carrier. Only its window children are SI instances. -/
def aggnCertRound (c n : ℕ) (solve : RawWinSI → RawCoset) :
    Round AggnCertNode AggnCertState RawCoset where
  WF := fun I => I.1.1.1.length = n
  ground := fun I => I.1.1.1.length
  measure := fun I => I.2.elim 1 (fun _ => 0)
  width := fun I => I.2.elim (aggnCertWidth I.1) (fun _ => 0)
  child := aggnCertChild
  init := fun I => aggnCertOpen c I.1
  combine := aggnCertCombine c
  finish := fun z => z.1.2.elim none solve
  bot := none
  child_eq_none := by
    intro I j v hj
    cases ho : I.2 with
    | some W => simp [aggnCertChild, ho]
    | none =>
      simp only [ho, Option.elim_none] at hj
      simp only [aggnCertChild, ho, Option.elim_none]
      exact if_neg (fun h => Nat.not_lt_of_ge hj h.2)
  child_wf := by
    intro I j v J hI hJ
    obtain ⟨_, W, rfl⟩ := aggnCertChild_some hJ
    exact hI
  child_measure := by
    intro I j v J _ hJ
    obtain ⟨ho, W, rfl⟩ := aggnCertChild_some hJ
    rw [ho]
    exact Nat.zero_lt_one
  child_ground := by
    intro I j v J _ hJ
    obtain ⟨_, W, rfl⟩ := aggnCertChild_some hJ
    exact le_rfl

section Stage

variable {n m : ℕ} {G : Subgroup (Perm (Fin n))} {ϕ : G →* Perm (Fin m)}
  {xs : RawStr} {tdom : List ℕ} {hc : LCCtxWF n m xs tdom}
  {s : Stage ϕ (decStrN n xs) (winSet m tdom)} {st st0 : RawLCSt}

set_option maxHeartbeats 1000000 in
/-- One stage advances the loop before the next child is requested. -/
theorem aggnCertPhase_stage (c : ℕ) (solve : RawWinSI → RawCoset)
    (h : StateFor hc s st) (hg : tdom.length ≤ guardBound c xs.length)
    (hrun : s.LoopCond) {i start : ℕ} (hi : i < n)
    (hstart : start ≤ i * (Nat.factorial tdom.length * n)) :
    PhaseMatch (aggnCertRound c n solve) (aggnCertDecode n) (decCoset n)
      (((xs, tdom), st0), none) (Nat.factorial tdom.length * n)
      start (aggnCertOpen c ((xs, tdom), st))
      (recomputeStrong s (aggkCanonReps s (aggkTypedT hc)) (aggkCanonWindows s))
      (fun B j v => ∃ st', StateFor hc s.step st' ∧
        v = aggnCertOpen c ((xs, tdom), st') ∧ B = (s.step.H : Set (Perm (Fin n))) ∧
        j ≤ (i + 1) * (Nat.factorial tdom.length * n)) := by
  let p : RawLCLoop := ((xs, tdom), st)
  let root : AggnCertNode := (((xs, tdom), st0), none)
  let P := aggnrInputOf c p
  let Rel := fun jR vR jM vM => jM = start + jR ∧ vM = aggnCertPack c p jR vR
  have hcond : lcCond p = true := (lcCond_eq_true_iff h).mpr hrun
  have hwidth : aggnrCount P * (aggnrWindows P).length ≤ Nat.factorial tdom.length * n :=
    aggnrWidth_le c h hg
  have hpos : 0 < aggnrCount P := by
    rw [aggnrCount_eq c h hg, aggkIdx_eq_card h]
    exact Nat.card_pos
  have hinit : Rel 0 (aggnrInit (P, none)) start (aggnCertOpen c p) := by
    refine ⟨by omega, ?_⟩
    symm
    simp only [aggnCertPack, aggnrInit]
    rw [if_pos hpos]
    rfl
  have hm := aggnPhaseMatch_sim (R := aggnrRound n solve)
    (M := aggnCertRound c n solve) (decI := aggnrDecode n) (decI' := aggnCertDecode n)
    (decA := decCoset n) (I := (P, none)) (I' := root) Rel (by
      intro jR vR jM vM hr J hJ
      obtain ⟨hjM, rfl⟩ := hr
      dsimp only [aggnrRound] at hJ
      obtain ⟨q, _, hq, ht, hiw, hjR, hJdef⟩ :=
        aggnrChild_some (z := ((P, none), jR, vR)) hJ
      dsimp only at hq ht hiw hjR hJdef
      have hglobal : jM < aggnCertWidth ((xs, tdom), st0) := by
        have hmul := Nat.mul_le_mul_right (Nat.factorial tdom.length * n) hi
        rw [Nat.succ_mul] at hmul
        simp only [aggnCertWidth, aggnCertStageWidth, hc.lenStr]
        omega
      refine ⟨(((xs, tdom), st0), J.2), ?_, ?_, ?_⟩
      · dsimp only [aggnCertRound]
        rw [aggnCertPack, if_pos ht]
        simp only [aggnCertChild, root, Option.elim_none]
        rw [if_pos ⟨hcond, hglobal⟩, hJ]
        rfl
      · rw [hJdef]
        rfl
      · intro a
        refine ⟨by omega, ?_⟩
        dsimp only [aggnCertRound, aggnrRound]
        rw [aggnCertPack, if_pos ht]
        rfl)
    (aggnrPhase_recompute c solve h hg hrun) hinit
  apply phaseMatch_mono (phaseMatch_weaken hm ?_) hwidth
  rintro B j v ⟨jR, vR, hresult, hj, hv⟩
  have hstop : ¬vR.1 < aggnrCount P := Nat.not_lt.mpr hresult.1.ge
  rw [aggnCertPack, if_neg hstop] at hv
  have ha : decCoset n vR.2.2.2 = (s.step.H : Set (Perm (Fin n))) :=
    hresult.2.2.1.trans hresult.2.1
  have hs' := aggrStateFor_step h hcond ha
  refine ⟨(lcStepWith vR.2.2.2 p).2, hs', ?_, hresult.2.1, ?_⟩
  · rw [hv]
    congr 1
    exact Prod.ext (lcwStep_fst _ _) rfl
  · have hjR := hresult.2.2.2
    change jR ≤ aggnrCount P * (aggnrWindows P).length at hjR
    rw [Nat.succ_mul]
    omega

end Stage

section Run

variable {n m : ℕ} {G : Subgroup (Perm (Fin n))} {ϕ : G →* Perm (Fin m)}
  {xs : RawStr} {tdom : List ℕ} {hc : LCCtxWF n m xs tdom} {st0 : RawLCSt}

/-- The invariant at a stage boundary includes the complete decoded value. -/
def aggnCertInv (c : ℕ) (hc : LCCtxWF n m xs tdom) (ϕ : G →* Perm (Fin m))
    (i : ℕ) (b : Set (Fin n) × Set (Perm (Fin n))) (j : ℕ) (v : AggnCertState) : Prop :=
  ∃ st, StateFor hc (stages ϕ (decStrN n xs) (winSet m tdom) i) st ∧
    v = aggnCertOpen c ((xs, tdom), st) ∧
    b = ((stages ϕ (decStrN n xs) (winSet m tdom) i).W,
      ((stages ϕ (decStrN n xs) (winSet m tdom) i).H : Set (Perm (Fin n)))) ∧
    j ≤ i * (Nat.factorial tdom.length * n)

/-- All raw encodings of correct answers match the same prefix of the certificate tree. -/
theorem aggnCertPhase_loop (c : ℕ) (solve : RawWinSI → RawCoset)
    (h0 : StateFor hc (stages ϕ (decStrN n xs) (winSet m tdom) 0) st0)
    (hg : tdom.length ≤ guardBound c xs.length) :
    ∀ i, i ≤ haltIndex ϕ (decStrN n xs) (winSet m tdom) →
    PhaseMatch (aggnCertRound c n solve) (aggnCertDecode n) (decCoset n)
      (((xs, tdom), st0), none) (i * (Nat.factorial tdom.length * n))
      0 (aggnCertOpen c ((xs, tdom), st0))
      (loopStrong ϕ (decStrN n xs) (winSet m tdom)
        (fun i => aggkCanonReps (stages ϕ (decStrN n xs) (winSet m tdom) i) (aggkTypedT hc))
        (fun i => aggkCanonWindows (stages ϕ (decStrN n xs) (winSet m tdom) i)) i)
      (aggnCertInv c hc ϕ i) := by
  intro i
  induction i with
  | zero =>
    intro hi
    rw [Nat.zero_mul, loopStrong]
    apply phaseMatch_done
    exact ⟨st0, h0, rfl, rfl, Nat.zero_le _⟩
  | succ i ih =>
    intro hi
    rw [loopStrong, Nat.succ_mul]
    apply phaseMatch_bind (ih (by omega))
    rintro b j v ⟨st, hs, rfl, rfl, hj⟩
    have hir : i < haltIndex ϕ (decStrN n xs) (winSet m tdom) := by omega
    have hin : i < n := hir.trans_le (by simpa only [Nat.card_fin] using
      (haltIndex_le_card (ϕ := ϕ) (x := decStrN n xs) (T := winSet m tdom)))
    have hm := aggnCertPhase_stage (st0 := st0) c solve hs hg
      (loopCond_of_lt_haltIndex _ _ _ hir) hin hj
    have hm' := phaseMatch_bind (P' := aggnCertInv c hc ϕ (i + 1))
      (k := fun cur => .done
        (affOf ϕ (winSet m tdom) ((stages ϕ (decStrN n xs) (winSet m tdom) i).H : Set (Perm (Fin n))),
          ((stages ϕ (decStrN n xs) (winSet m tdom) i).H : Set (Perm (Fin n))) ∩ cur)) hm
      (fun H j' v' hH => phaseMatch_done (by
      obtain ⟨st', hs', hv', hval, hj'⟩ := hH
      refine ⟨st', hs', hv', ?_, hj'⟩
      apply Prod.ext
      · exact affOf_coe _
      · rw [hval]
        exact Set.inter_eq_self_of_subset_right (stages ϕ (decStrN n xs) (winSet m tdom) i).step_H_le))
    simpa only [Nat.add_zero] using hm'

/-- Read the certificate from the final loop state. -/
def aggnCertOut (v : AggnCertState) : RawLCOut := lcOutOf v.1

noncomputable def aggnCertRead (n : ℕ) (v : AggnCertState) :
    Set (Fin n) × Subgroup (Perm (Fin n)) :=
  (winSet n (aggnCertOut v).1, decGroup n (aggnCertOut v).2.2.1)

/-- The final state of the inlined run contains the paper's window and certificate. -/
def aggnCertPost (c : ℕ) (hc : LCCtxWF n m xs tdom) (ϕ : G →* Perm (Fin m))
    (b : Set (Fin n) × Subgroup (Perm (Fin n))) (j : ℕ) (v : AggnCertState) : Prop :=
  ∃ st, StateFor hc (outStage ϕ (decStrN n xs) (winSet m tdom)) st ∧
    v = aggnCertOpen c ((xs, tdom), st) ∧ aggnCertRead n v = b ∧
    b = (windowOut ϕ (decStrN n xs) (winSet m tdom), certK ϕ (decStrN n xs) (winSet m tdom)) ∧
    j ≤ n * (Nat.factorial tdom.length * n)

/-- Sec. 13.1, the complete certificate run with one fixed tree per raw node. -/
theorem aggnCertPhase_run (c : ℕ) (solve : RawWinSI → RawCoset)
    (h0 : StateFor hc (stages ϕ (decStrN n xs) (winSet m tdom) 0) st0)
    (hg : tdom.length ≤ guardBound c xs.length) :
    PhaseMatch (aggnCertRound c n solve) (aggnCertDecode n) (decCoset n)
      (((xs, tdom), st0), none) (n * (Nat.factorial tdom.length * n))
      0 (aggnCertOpen c ((xs, tdom), st0))
      (certRunStrong ϕ (decStrN n xs) (winSet m tdom)
        (fun i => aggkCanonReps (stages ϕ (decStrN n xs) (winSet m tdom) i) (aggkTypedT hc))
        (fun i => aggkCanonWindows (stages ϕ (decStrN n xs) (winSet m tdom) i)))
      (aggnCertPost c hc ϕ) := by
  rw [certRunStrong, localCertStrong, aggrBind_assoc]
  simp only [SIReduction.bind]
  have hm := aggnCertPhase_loop c solve h0 hg
    (haltIndex ϕ (decStrN n xs) (winSet m tdom)) (le_refl _)
  have hm' := phaseMatch_mono hm (Nat.mul_le_mul_right (Nat.factorial tdom.length * n)
    (by simpa only [Nat.card_fin] using
      (haltIndex_le_card (ϕ := ϕ) (x := decStrN n xs) (T := winSet m tdom))))
  have hout := phaseMatch_bind (P' := aggnCertPost c hc ϕ)
    (k := fun b => .done (b.1, certKOf ϕ (winSet m tdom) b.1 b.2)) hm' (by
    rintro b j v ⟨st, hs, rfl, rfl, hj⟩
    apply phaseMatch_done
    have hval :
        ((outStage ϕ (decStrN n xs) (winSet m tdom)).W,
          certKOf ϕ (winSet m tdom) (outStage ϕ (decStrN n xs) (winSet m tdom)).W
            ((outStage ϕ (decStrN n xs) (winSet m tdom)).H : Set (Perm (Fin n)))) =
        (windowOut ϕ (decStrN n xs) (winSet m tdom), certK ϕ (decStrN n xs) (winSet m tdom)) :=
      Prod.ext rfl (certKOf_coe _ _)
    refine ⟨st, hs, rfl, ?_, hval, ?_⟩
    · exact (Prod.ext (lcwOut_window hs) (lcwOut_certK hs)).trans hval.symm
    · exact hj.trans (Nat.mul_le_mul_right _ (by simpa only [Nat.card_fin] using
        (haltIndex_le_card (ϕ := ϕ) (x := decStrN n xs) (T := winSet m tdom)))))
  simpa only [Nat.add_zero] using hout

end Run

end Algo
