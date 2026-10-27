import Workspace.Algo.TopMasterOpsIte
import Workspace.Algo.TopFourAmbientMatch
import Workspace.Algo.TopMasterCheckedCall
import Workspace.Algo.PhaseMatch
import Workspace.Algo.TopMasterDescentPrepared

/-! # A window round on the master carrier
Lines 4b–7 of the Master Algorithm run on the window `Δ` of a hinted node: the group is
restricted to `Δ`, and the calls the round makes are instances on `Δ`. The master carrier
works on the ambient domain. This file lifts any raw round `R` on the window to the master
carrier, as line 4b already does for its own round (`top4wLoopMatch`): each call is lifted to
a full coset instance on the ambient domain (`topwRawInstance`), each answer is restricted
back before `R` continues (`topwCosetImage`), and the final answer is the full preimage
(`topwCosetPreimage`). A computed test `g` guards the node: where it fails the carrier asks
nothing.
-/
namespace Algo
open RAM RAM.Targets Babai Equiv

/-- The window context of a node: its source string, its generators, its window, and its
source string again (as the string the lifted calls carry outside the window). -/
def masterWinCtx (P : RawMasterSI) : TopwContext :=
  ((P.1.2.2.2.1, P.1.2.1), P.1.1, P.1.2.2.2.1)

theorem polyFun_masterWinCtx : PolyFun masterWinCtx := by
  have hx : PolyFun (fun P : RawMasterSI => P.1.2.2.2.1) :=
    (((polyFun_fst.comp polyFun_snd).comp polyFun_snd).comp polyFun_snd).comp polyFun_fst
  exact ((hx.pair ((polyFun_fst.comp polyFun_snd).comp polyFun_fst)).pair
    ((polyFun_fst.comp polyFun_fst).pair hx))

/-- A window round `R`, entered at `enter P`, on the master carrier. The fold of `R` may
have a width that is only an analysis bound; the carrier runs with a computed width `wd P`
instead, which is at least that of `R` (a larger budget does not change the fold, since the
children of `R` stop first). At nodes that fail `g`, the carrier has no child and keeps the
default state `d`. -/
def masterWinLiftOps {ι ω : Type} (R : Round ι ω RawCoset) (read : RawMasterSI → ι → RawWinSI)
    (enter : RawMasterSI → ι) (g : RawMasterSI → Bool) (wd : RawMasterSI → ℕ) (d : ω) :
    MasterOps ω where
  width P := if g P then wd P else 0
  child z := if g z.1 then (R.child (enter z.1, z.2.1, z.2.2)).bind (fun J =>
      (topwRawInstance (masterWinCtx z.1, read z.1 J)).map
        (fun V => masterCheckedCall (z.1.1.2.2.2.1, V))) else none
  init P := if g P then R.init (enter P) else d
  combine z := if g z.1 then R.combine (enter z.1, z.2.1, z.2.2.1,
    topwCosetImage (z.1.1.2.2.2.1, z.1.1.1, z.2.2.2)) else d
  finish z := top2NormC z.1.1.2.2.2.1
    (topwCosetPreimage ((z.1.1.2.2.2.1, z.1.1.2.1), z.1.1.1, R.finish (enter z.1, z.2)))

section Match
variable {ι ω : Type} {R : Round ι ω RawCoset} {read : RawMasterSI → ι → RawWinSI}
    {enter : RawMasterSI → ι} {g : RawMasterSI → Bool} {wd : RawMasterSI → ℕ} {d : ω}
    {n : ℕ} {P : RawMasterSI} {gens : List (Perm (Fin n))}
    (hgP : g P = true) (hwd : R.width (enter P) ≤ wd P) (hx : P.1.2.2.2.1.length = n) (hgens : P.1.2.1 = gens.map (encPerm n))
    (hnd : P.1.1.Nodup) (hlt : ∀ u ∈ P.1.1, u < n)
    (hinv : IsInvariant (genGroup gens) (winSet n P.1.1))
    (decR : ι → SIInstance (Fin P.1.1.length) ℕ)
    (hread : ∀ j s J, R.child (enter P, j, s) = some J →
      decR J = decWinSI P.1.1.length (read P J))

include hgP hwd hx hgens hread in
/-- **The window round, lifted.** A fold of `R` on the window that walks `T` lifts to a fold
of the master carrier that walks the lift of `T` to the ambient domain, followed by the full
preimage of the answer (`top4wTree`), provided the calls of `T` are with respect to the
restricted group, its answer lies there too, and every lifted call is admitted (its letters
are bounded and its window is smaller than `Δ`). -/
theorem masterWinLift_match (a b : ℕ) :
    ∀ {w j : ℕ} {s : ω} {T : SIReduction (Fin P.1.1.length) ℕ (Set (Perm (Fin P.1.1.length)))},
      LoopMatch R decR (decCoset P.1.1.length) (enter P) w j s T →
      (∀ J ∈ T.calls, J.K ⊆ ((winRestrictHom n P.1.1 hnd hlt (genGroup gens) hinv).range :
        Set (Perm (Fin P.1.1.length)))) →
      T.run ⊆ ((winRestrictHom n P.1.1 hnd hlt (genGroup gens) hinv).range :
        Set (Perm (Fin P.1.1.length))) →
      (∀ J ∈ (top4wTree P.1.1 hnd hlt (genGroup gens) hinv (decStrN n P.1.2.2.2.1) T).calls,
        MasterCallLetters (2 * n + 1) J ∧ J.windowSize < P.1.1.length ∧
          ∃ G : Subgroup (Perm (Fin n)), IsCosetInstance G J) →
      LoopMatch (masterAdmittedRound a b (masterWinLiftOps R read enter g wd d))
        (fun J => decWinSI n J.1) (decCoset n) P w j s
        (top4wTree P.1.1 hnd hlt (genGroup gens) hinv (decStrN n P.1.2.2.2.1) T) := by
  have hwsize : masterWindowSize P ≤ masterDegree P := by
    change P.1.1.length ≤ P.1.2.2.2.1.length
    rw [hx]
    exact length_le_of_nodup_lt hnd hlt
  have hctx : masterWinCtx P =
      ((P.1.2.2.2.1, gens.map (encPerm n)), P.1.1, P.1.2.2.2.1) := by
    rw [masterWinCtx, hgens]
  intro w j s T h
  induction h with
  | done w j s A hc ha =>
    intro _ hA _
    refine .done w j s _ ?_ ?_
    · change masterGuardedChild a b _ (P, j, s) = none
      unfold masterGuardedChild
      split_ifs
      · change masterAdmitChild a b (P, if g P then (R.child (enter P, j, s)).bind _ else none) = none
        rw [if_pos hgP, hc]
        rfl
      · rfl
    · change decCoset n (top2NormC P.1.2.2.2.1 (topwCosetPreimage
        ((P.1.2.2.2.1, P.1.2.1), P.1.1, R.finish (enter P, s)))) = _
      rw [decCoset_top2NormC hx, hgens,
        topwCosetPreimage_spec hx hnd hlt hinv _ (ha.symm ▸ hA), ha]
  | call w j s J k hc hn ih =>
    intro hT hRun hL
    have hJ := hT (decR J) (by simp [SIReduction.calls])
    have hdJ := hread j s J hc
    rw [hdJ] at hJ
    obtain ⟨V, hV, hdec⟩ := topwRawInstance_spec (dom := P.1.2.2.2.1) (x := P.1.2.2.2.1)
      hx hx hnd hlt hinv (read P J) hJ
    have hLV : MasterCallLetters (2 * n + 1) (decWinSI n V) ∧
        (decWinSI n V).windowSize < P.1.1.length ∧
          ∃ G : Subgroup (Perm (Fin n)), IsCosetInstance G (decWinSI n V) := by
      rw [hdec, ← hdJ]
      exact hL _ (by simp [top4wTree, topwReduction, SIReduction.calls])
    have hchild : masterGuardedChild a b (masterWinLiftOps R read enter g wd d) (P, j, s) =
        some (masterCheckedCall (P.1.2.2.2.1, V)) := by
      have hj : j < R.width (enter P) := by
        by_contra hj
        have hnone := R.child_eq_none (enter P) j s (Nat.le_of_not_gt hj)
        rw [hc] at hnone
        contradiction
      unfold masterGuardedChild
      rw [if_pos (by change j < (if g P then _ else 0); rw [if_pos hgP]; exact hj.trans_le hwd)]
      change masterAdmitChild a b (P, if g P then (R.child (enter P, j, s)).bind _ else none) = _
      rw [if_pos hgP, hc, Option.bind_some, hctx, hV, Option.map_some]
      obtain ⟨hL1, hL2, G, hG⟩ := hLV
      subst hx
      exact masterCheckedCall_admitted a b V hwsize hL2 hL1 hG
    have hDV : decWinSI n (masterCheckedCall (P.1.2.2.2.1, V)).1 =
        topwInstance P.1.1 hnd hlt (genGroup gens) hinv (decStrN n P.1.2.2.2.1) (decR J) := by
      rw [masterCheckedCall_decode hx V hLV.1, hdec, hdJ]
    change LoopMatch _ _ _ _ (w + 1) j s (.call
      (topwInstance P.1.1 hnd hlt (genGroup gens) hinv (decStrN n P.1.2.2.2.1) (decR J)) _)
    rw [← hDV]
    refine .call w j s _ _ hchild ?_
    intro z hz
    have hzsub : decCoset n z ⊆ (genGroup gens : Set (Perm (Fin n))) := by
      rw [hz, hDV, topwInstance_answer]
      rintro u ⟨hu, _⟩
      exact hu
    have hanswer : decCoset P.1.1.length (topwCosetImage (P.1.2.2.2.1, P.1.1, z)) =
        (decR J).answer := by
      rw [topwCosetImage_spec hx hnd hlt hinv z hzsub, hz, hDV,
        topwImage_answer hnd hlt hinv (decStrN n P.1.2.2.2.1) _ (hdJ ▸ hJ)]
    have htail := ih (topwCosetImage (P.1.2.2.2.1, P.1.1, z)) hanswer
      (fun J' hJ' => hT J' (by simp [SIReduction.calls, hJ'])) hRun
      (fun J' hJ' => hL J' (by
        simp only [top4wTree, topwReduction, SIReduction.calls_bind, SIReduction.calls_call,
          List.mem_cons, SIReduction.calls_done, List.append_nil] at hJ' ⊢
        right
        rw [topwImage_answer hnd hlt hinv (decStrN n P.1.2.2.2.1) _ (hdJ ▸ hJ)]
        exact hJ'))
    have hcomb : (masterAdmittedRound a b (masterWinLiftOps R read enter g wd d)).combine
        (P, j, s, z) = R.combine (enter P, j, s, topwCosetImage (P.1.2.2.2.1, P.1.1, z)) :=
      if_pos hgP
    rw [hcomb]
    change LoopMatch _ _ _ _ w (j + 1)
      (R.combine (enter P, j, s, topwCosetImage (P.1.2.2.2.1, P.1.1, z)))
      (top4wTree P.1.1 hnd hlt (genGroup gens) hinv (decStrN n P.1.2.2.2.1)
        (k (topwImageSet P.1.1 hnd hlt (genGroup gens) hinv
          (decWinSI n (masterCheckedCall (P.1.2.2.2.1, V)).1).answer)))
    rw [hDV, topwImage_answer hnd hlt hinv (decStrN n P.1.2.2.2.1) _ (hdJ ▸ hJ)]
    exact htail

include hgP hwd hx hgens hread in
/-- The start of the lifted fold: the fold of `R` from its own start, at its own width, gives
the fold of the carrier from its start, at the computed width. -/
theorem masterWinLift_start (a b : ℕ)
    {T : SIReduction (Fin P.1.1.length) ℕ (Set (Perm (Fin P.1.1.length)))}
    (h : LoopMatch R decR (decCoset P.1.1.length) (enter P) (R.width (enter P)) 0
      (R.init (enter P)) T)
    (hK : ∀ J ∈ T.calls, J.K ⊆ ((winRestrictHom n P.1.1 hnd hlt (genGroup gens) hinv).range :
      Set (Perm (Fin P.1.1.length))))
    (hRun : T.run ⊆ ((winRestrictHom n P.1.1 hnd hlt (genGroup gens) hinv).range :
      Set (Perm (Fin P.1.1.length))))
    (hL : ∀ J ∈ (top4wTree P.1.1 hnd hlt (genGroup gens) hinv (decStrN n P.1.2.2.2.1) T).calls,
      MasterCallLetters (2 * n + 1) J ∧ J.windowSize < P.1.1.length ∧
        ∃ G : Subgroup (Perm (Fin n)), IsCosetInstance G J) :
    LoopMatch (masterAdmittedRound a b (masterWinLiftOps R read enter g wd d))
      (fun J => decWinSI n J.1) (decCoset n) P
      ((masterWinLiftOps R read enter g wd d).width P) 0
      ((masterWinLiftOps R read enter g wd d).init P)
      (top4wTree P.1.1 hnd hlt (genGroup gens) hinv (decStrN n P.1.2.2.2.1) T) := by
  have hw : (masterWinLiftOps R read enter g wd d).width P = wd P := if_pos hgP
  have hi : (masterWinLiftOps R read enter g wd d).init P = R.init (enter P) := if_pos hgP
  rw [hw, hi]
  exact loopMatch_mono (masterWinLift_match hgP hwd hx hgens hnd hlt hinv decR hread a b h hK
    hRun hL) hwd
end Match

/-! ### The local costs of the lifted round -/

section Cost
variable {ι ω : Type} [Enc ι] [Enc ω] {R : Round ι ω RawCoset}
    {read : RawMasterSI → ι → RawWinSI}
    {enter : RawMasterSI → ι} {g : RawMasterSI → Bool} {wd : RawMasterSI → ℕ} {d : ω}

private theorem pfst' {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {f : α → β × γ}
    (h : PolyFun f) : PolyFun (fun a => (f a).1) := h.comp polyFun_fst
private theorem psnd' {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {f : α → β × γ}
    (h : PolyFun f) : PolyFun (fun a => (f a).2) := h.comp polyFun_snd

/-- **The lifted round has local costs** as soon as the round's routines are
quasipolynomial, its states are bounded at the guarded nodes uniformly in the fold state and
the answer, and the computed width is quasipolynomial. The answers need no bound: the
shifted final routine keeps them small in any case. -/
theorem masterWinLift_cost (a b : ℕ)
    (hc : QuasiFun R.child) (hi : QuasiFun R.init) (hu : QuasiFun R.combine)
    (hf : QuasiFun R.finish) (hread : PolyFun (fun q : RawMasterSI × ι => read q.1 q.2))
    (henter : PolyFun enter) (hg : PolyFun g)
    (hwq : QuasiFun wd) (S Wb : ℕ → ℕ) (hS : QuasiPolyBound S) (hSm : Monotone S)
    (hWb : QuasiPolyBound Wb)
    (hinit : ∀ P, MasterInputWF a b P → g P = true →
      Enc.size (R.init (enter P)) ≤ S (masterDegree P))
    (hcomb : ∀ P j s A, MasterInputWF a b P → g P = true →
      Enc.size (R.combine (enter P, j, s, A)) ≤ S (masterDegree P))
    (hwidth : ∀ P, MasterInputWF a b P → g P = true → wd P ≤ Wb (masterDegree P)) :
    Nonempty (MasterOpsCost a b (masterShiftOps (masterWinLiftOps R read enter g wd d))) := by
  let F := masterWinLiftOps R read enter g wd d
  have hx : PolyFun (fun P : RawMasterSI => P.1.2.2.2.1) :=
    (((polyFun_fst.comp polyFun_snd).comp polyFun_snd).comp polyFun_snd).comp polyFun_fst
  have hΔ : PolyFun (fun P : RawMasterSI => P.1.1) := polyFun_fst.comp polyFun_fst
  have hgens : PolyFun (fun P : RawMasterSI => P.1.2.1) :=
    (polyFun_fst.comp polyFun_snd).comp polyFun_fst
  -- the width
  have hW : QuasiFun F.width :=
    aggnQuasiFun_ite hg.quasiFun hwq (quasiFun_const 0)
  -- the child
  have hC : QuasiFun F.child := by
    let Z := RawMasterSI × ℕ × ω
    have hP : PolyFun (fun z : Z => z.1) := polyFun_fst
    have hin : QuasiFun (fun z : Z => (enter z.1, z.2.1, z.2.2)) :=
      ((hP.comp henter).pair (psnd' polyFun_id)).quasiFun
    have hRc : QuasiFun (fun z : Z => R.child (enter z.1, z.2.1, z.2.2)) := hin.comp hc
    have hlift : PolyFun (fun q : ι × Z =>
        (topwRawInstance (masterWinCtx q.2.1, read q.2.1 q.1)).map
          (fun V => masterCheckedCall (q.2.1.1.2.2.2.1, V))) := by
      have h1 : PolyFun (fun q : ι × Z =>
          topwRawInstance (masterWinCtx q.2.1, read q.2.1 q.1)) :=
        (((psnd' polyFun_id).comp (hP.comp polyFun_masterWinCtx)).pair
          ((((psnd' polyFun_id).comp hP).pair polyFun_fst).comp hread)).comp
            polyFun_topwRawInstance
      have hh : PolyFun (fun r : RawWinSI × (ι × Z) =>
          (some (masterCheckedCall (r.2.2.1.1.2.2.2.1, r.1)) : Option RawMasterSI)) :=
        ((((psnd' (psnd' polyFun_id)).comp (hP.comp hx)).pair polyFun_fst).comp
          polyFun_masterCheckedCall).comp polyFun_some
      have h3 := PolyFun.optionElim (β := RawWinSI) (σ := ι × Z) (polyFun_const none) hh
      exact ((h1.pair polyFun_id).comp h3).of_eq (fun q => by
        cases topwRawInstance (masterWinCtx q.2.1, read q.2.1 q.1) <;> rfl)
    have hbind : QuasiFun (fun z : Z => (R.child (enter z.1, z.2.1, z.2.2)).bind (fun J =>
        (topwRawInstance (masterWinCtx z.1, read z.1 J)).map
          (fun V => masterCheckedCall (z.1.1.2.2.2.1, V)))) := by
      refine ((hRc.pair quasiFun_id).comp (QuasiFun.optionElim (quasiFun_const none)
        hlift.quasiFun)).of_eq (fun z => ?_)
      cases R.child (enter z.1, z.2.1, z.2.2) <;> rfl
    exact aggnQuasiFun_ite (hP.comp hg).quasiFun hbind (quasiFun_const none)
  -- the start
  have hI : QuasiFun F.init :=
    aggnQuasiFun_ite hg.quasiFun (henter.quasiFun.comp hi) (quasiFun_const d)
  -- the update
  have hU : QuasiFun F.combine := by
    let Z := RawMasterSI × ℕ × ω × RawCoset
    have hP : PolyFun (fun z : Z => z.1) := polyFun_fst
    have himg : PolyFun (fun z : Z => topwCosetImage (z.1.1.2.2.2.1, z.1.1.1, z.2.2.2)) :=
      ((hP.comp hx).pair ((hP.comp hΔ).pair (psnd' (psnd' (psnd' polyFun_id))))).comp
        polyFun_topwCosetImage
    have hin : PolyFun (fun z : Z => (enter z.1, z.2.1, z.2.2.1,
        topwCosetImage (z.1.1.2.2.2.1, z.1.1.1, z.2.2.2))) :=
      (hP.comp henter).pair ((psnd' polyFun_id).comp polyFun_fst |>.pair
        ((psnd' (psnd' polyFun_id)).comp polyFun_fst |>.pair himg))
    exact aggnQuasiFun_ite (hP.comp hg).quasiFun (hin.quasiFun.comp hu) (quasiFun_const d)
  -- the answer
  have hF : QuasiFun F.finish := by
    let Z := RawMasterSI × ω
    have hP : PolyFun (fun z : Z => z.1) := polyFun_fst
    have hRf : QuasiFun (fun z : Z => R.finish (enter z.1, z.2)) :=
      ((hP.comp henter).pair polyFun_snd).quasiFun.comp hf
    have hpre : QuasiFun (fun z : Z =>
        topwCosetPreimage ((z.1.1.2.2.2.1, z.1.1.2.1), z.1.1.1, R.finish (enter z.1, z.2))) :=
      (((hP.comp hx).pair (hP.comp hgens)).quasiFun.pair ((hP.comp hΔ).quasiFun.pair hRf)).comp_poly
        polyFun_topwCosetPreimage
    exact ((hP.comp hx).quasiFun.pair hpre).comp_poly polyFun_top2NormC
  refine ⟨⟨fun n => S n + Enc.size d, Wb, hS.add (polyBound_const _).quasiPoly,
    fun _ _ h => Nat.add_le_add_right (hSm h) _, hWb, hW, hC, hI, hU,
    quasiFun_masterShiftFinish hF, ?_, ?_, ?_, ?_⟩⟩
  · intro P hP
    change Enc.size (if g P then R.init (enter P) else d) ≤ _
    split
    · exact (hinit P hP (by assumption)).trans (Nat.le_add_right _ _)
    · exact Nat.le_add_left _ _
  · intro P j s A hP _
    change Enc.size (if g P then R.combine (enter P, j, s, _) else d) ≤ _
    split
    · exact (hcomb P j s _ hP (by assumption)).trans (Nat.le_add_right _ _)
    · exact Nat.le_add_left _ _
  · intro P s _
    exact (masterShiftOps_finish_size _ P s).trans (by unfold masterInputCap; omega)
  · intro P hP
    change (if g P then wd P else 0) ≤ _
    split
    · exact hwidth P hP (by assumption)
    · exact Nat.zero_le _
end Cost
end Algo
