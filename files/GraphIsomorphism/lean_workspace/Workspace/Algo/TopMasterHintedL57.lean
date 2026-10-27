import Workspace.Algo.TopMasterHintedNode
import Workspace.Algo.TopMasterL57CtxGood

/-! # Route 5 of the hinted node carrier: lines 5–7 with the hinted call of line 11

Section 15, lines 5–7, with Procedure Align lines 7–11 as repaired in the corrected paper. The round
of lines 5–7 on the window (`Algo.masterL57Round`) is lifted to the node's domain; at each of
its calls the hint routine `H5` may attach a hint (`Algo.MasterOps.withHint`). A call either
has a window of at most `4/5` of the node's and no hint, or it is the hinted call of line 11
on the dominant orbit of `G*`: its hint has its meaning for the call (`Algo.MasterHintGood`,
the action of `G*` on `Γ*` through `ϕ*`), and its Johnson parameter `m*` is at most half of
the node's (Eq. (73)); its window need not shrink.

Whether a call is hinted depends on the fold state of the round (the routine reads the data of
Procedure Align there), so the condition is stated at each step of the fold, with its state:

* `Algo.LoopMatchS`: `Algo.LoopMatch` with a condition on the index, the state and the child
  at every call (`Algo.LoopMatch.toS` from a condition on all steps);
* `Algo.MasterHintStepOK`: the condition on one lifted call and its hint;
* `Algo.masterWinLiftH_match`: the lift of a window fold with conditions at its steps is a
  match, with a condition on the children, of the lifted carrier with hints;
* `Algo.masterNodeH_hint_line57_matchGood`: at a node of route 5, the hinted node carrier
  walks the lift with good children that make progress;
* `Algo.MasterL57SupplyH` and `Algo.masterParamRoute5H_of_supply`: the obligation of route 5
  of the hinted node carrier from a window tree at every node, with the hinted call allowed.
-/
set_option synthInstance.maxSize 2048
namespace Algo
open RAM RAM.Targets Babai Equiv
open scoped Pointwise

/-! ### Matches with a condition on the steps -/

section MatchS
variable {ι ω α Ω A : Type} [Fintype Ω] [DecidableEq Ω]

/-- `Algo.LoopMatch` in which every call satisfies a condition `C j s J` on its index `j`, the
fold state `s` it is made from, and the child `J`. -/
inductive LoopMatchS (R : Round ι ω α) (C : ℕ → ω → ι → Prop) (decI : ι → SIInstance Ω A)
    (decA : α → Set (Equiv.Perm Ω)) (I : ι) :
    ℕ → ℕ → ω → SIReduction Ω A (Set (Equiv.Perm Ω)) → Prop where
  | done (w j : ℕ) (s : ω) (a : Set (Equiv.Perm Ω)) (hc : R.child (I, j, s) = none)
      (ha : decA (R.finish (I, s)) = a) : LoopMatchS R C decI decA I w j s (.done a)
  | call (w j : ℕ) (s : ω) (J : ι)
      (k : Set (Equiv.Perm Ω) → SIReduction Ω A (Set (Equiv.Perm Ω)))
      (hc : R.child (I, j, s) = some J) (hC : C j s J)
      (hnext : ∀ a : α, decA a = (decI J).answer →
        LoopMatchS R C decI decA I w (j + 1) (R.combine (I, j, s, a)) (k (decI J).answer)) :
      LoopMatchS R C decI decA I (w + 1) j s (.call (decI J) k)

/-- A match gives a match with a condition on the steps, when the condition holds at every
step whose call has the property `V`, and every call of the tree has `V`. -/
theorem LoopMatch.toS {R : Round ι ω α} {C : ℕ → ω → ι → Prop} {decI : ι → SIInstance Ω A}
    {decA : α → Set (Equiv.Perm Ω)} {I : ι} (V : SIInstance Ω A → Prop)
    (hC : ∀ j s J, R.child (I, j, s) = some J → V (decI J) → C j s J) :
    ∀ {w j : ℕ} {s : ω} {T : SIReduction Ω A (Set (Equiv.Perm Ω))},
      LoopMatch R decI decA I w j s T → (∀ K ∈ T.calls, V K) →
        LoopMatchS R C decI decA I w j s T := by
  intro w j s T h
  induction h with
  | done w j s a hc ha => exact fun _ => .done w j s a hc ha
  | call w j s J k hc _ ih =>
    intro hV
    have hvJ : V (decI J) := hV _ (by simp [SIReduction.calls])
    refine .call w j s J k hc (hC j s J hc hvJ) fun a ha => ih a ha fun K hK => ?_
    apply hV K
    simp only [SIReduction.calls, List.mem_cons]
    right
    exact hK

theorem LoopMatchS.mono {R : Round ι ω α} {C C' : ℕ → ω → ι → Prop}
    {decI : ι → SIInstance Ω A} {decA : α → Set (Equiv.Perm Ω)} {I : ι}
    (hCC : ∀ j s J, C j s J → C' j s J) :
    ∀ {w j : ℕ} {s : ω} {T : SIReduction Ω A (Set (Equiv.Perm Ω))},
      LoopMatchS R C decI decA I w j s T → LoopMatchS R C' decI decA I w j s T := by
  intro w j s T h
  induction h with
  | done w j s a hc ha => exact .done w j s a hc ha
  | call w j s J k hc hC _ ih => exact .call w j s J k hc (hCC j s J hC) ih

theorem LoopMatchS.mono_width {R : Round ι ω α} {C : ℕ → ω → ι → Prop}
    {decI : ι → SIInstance Ω A} {decA : α → Set (Equiv.Perm Ω)} {I : ι} :
    ∀ {w w' j : ℕ} {s : ω} {T : SIReduction Ω A (Set (Equiv.Perm Ω))},
      LoopMatchS R C decI decA I w j s T → w ≤ w' → LoopMatchS R C decI decA I w' j s T := by
  intro w w' j s T h
  induction h generalizing w' with
  | done w j s a hc ha => exact fun _ => .done w' j s a hc ha
  | call w j s J k hc hC _ ih =>
    intro hw
    obtain ⟨w'', rfl⟩ : ∃ w'', w' = w'' + 1 := ⟨w' - 1, by omega⟩
    exact .call w'' j s J k hc hC fun a ha => ih a ha (by omega)
/-- `Algo.loopMatch_redMapCalls` for a match with a condition on the steps. -/
theorem LoopMatchS.redMapCalls {β : Type} {R : Round ι ω β} {C : ℕ → ω → ι → Prop}
    {dec₁ dec₂ : ι → SIInstance Ω ℕ} {decA : β → Set (Equiv.Perm Ω)} {I : ι}
    (f : SIInstance Ω ℕ → SIInstance Ω ℕ)
    (hf : ∀ j s J, R.child (I, j, s) = some J →
      dec₂ J = f (dec₁ J) ∧ (f (dec₁ J)).answer = (dec₁ J).answer) :
    ∀ {w j : ℕ} {s : ω} {T : SIReduction Ω ℕ (Set (Equiv.Perm Ω))},
      LoopMatchS R C dec₁ decA I w j s T →
        LoopMatchS R C dec₂ decA I w j s (Algo.redMapCalls f T) := by
  intro w j s T h
  induction h with
  | done w j s a hc ha => exact .done w j s a hc ha
  | call w j s J k hc hC _ ih =>
    obtain ⟨h2, hans⟩ := hf j s J hc
    have hans' : (dec₂ J).answer = (dec₁ J).answer := by rw [h2, hans]
    change LoopMatchS R C dec₂ decA I (w + 1) j s (.call (f (dec₁ J)) _)
    rw [← h2]
    refine .call w j s J _ hc hC fun a ha => ?_
    rw [hans'] at ha ⊢
    exact ih a ha
end MatchS

/-! ### The lifted round with hints -/

section Match
variable {ι ω : Type} {R : Round ι ω RawCoset} {read : RawMasterSI → ι → RawWinSI}
    {enter : RawMasterSI → ι} {g : RawMasterSI → Bool} {wd : RawMasterSI → ℕ} {d : ω}
    {H : (RawMasterSI × ℕ × ω) × RawMasterSI → Option RawMasterHint}
    {n : ℕ} {P : RawMasterSI} {gens : List (Perm (Fin n))}
    (hgP : g P = true) (hwd : R.width (enter P) ≤ wd P) (hx : P.1.2.2.2.1.length = n)
    (hgens : P.1.2.1 = gens.map (encPerm n))
    (hnd : P.1.1.Nodup) (hlt : ∀ u ∈ P.1.1, u < n)
    (hinv : IsInvariant (genGroup gens) (winSet n P.1.1))
    (decR : ι → SIInstance (Fin P.1.1.length) ℕ)
    (hread : ∀ j s J, R.child (enter P, j, s) = some J →
      decR J = decWinSI P.1.1.length (read P J))

/-- The lifted call a step proposes, with the hint `H` attaches. -/
def masterLiftHinted (H : (RawMasterSI × ℕ × ω) × RawMasterSI → Option RawMasterHint)
    (P : RawMasterSI) (j : ℕ) (s : ω) (V : RawWinSI) : RawMasterSI :=
  masterAttachHint (masterCheckedCall (P.1.2.2.2.1, V),
    H ((P, j, s), masterCheckedCall (P.1.2.2.2.1, V)))

/-- **The condition at a step of the window fold**: every lifted call it proposes (with bounded
letters, a coset instance, and a window inside the node's) is admitted at the node with the
hint `H` attaches, and satisfies the condition `Cg` on the children. -/
def MasterLiftStepOK (a b n : ℕ) (H : (RawMasterSI × ℕ × ω) × RawMasterSI → Option RawMasterHint)
    (read : RawMasterSI → ι → RawWinSI) (Cg : RawMasterSI → Prop) (P : RawMasterSI) (j : ℕ)
    (s : ω) (J : ι) : Prop :=
  ∀ V, topwRawInstance (masterWinCtx P, read P J) = some V →
    MasterCallLetters (2 * n + 1) (decWinSI n V) →
    (∃ G : Subgroup (Perm (Fin n)), IsCosetInstance G (decWinSI n V)) →
    (decWinSI n V).windowSize ≤ P.1.1.length →
    masterAdmitChild a b (P, some (masterLiftHinted H P j s V)) =
        some (masterLiftHinted H P j s V) ∧ Cg (masterLiftHinted H P j s V)

include hgP hwd hx hgens hread in
/-- **The window round, lifted, with hints.** `Algo.masterWinLift_match` for the lifted carrier
with the hints of `H`: a fold of `R` on the window that walks `T`, with the condition
`Algo.MasterLiftStepOK` at every step, lifts to a fold of the carrier with hints that walks the
lift of `T`, every child of which satisfies `Cg`. -/
theorem masterWinLiftH_match (a b : ℕ) (Cg : RawMasterSI → Prop) :
    ∀ {w j : ℕ} {s : ω} {T : SIReduction (Fin P.1.1.length) ℕ (Set (Perm (Fin P.1.1.length)))},
      LoopMatchS R (MasterLiftStepOK a b n H read Cg P) decR (decCoset P.1.1.length)
        (enter P) w j s T →
      (∀ J ∈ T.calls, J.K ⊆ ((winRestrictHom n P.1.1 hnd hlt (genGroup gens) hinv).range :
        Set (Perm (Fin P.1.1.length)))) →
      T.run ⊆ ((winRestrictHom n P.1.1 hnd hlt (genGroup gens) hinv).range :
        Set (Perm (Fin P.1.1.length))) →
      (∀ J ∈ (top4wTree P.1.1 hnd hlt (genGroup gens) hinv (decStrN n P.1.2.2.2.1) T).calls,
        MasterCallLetters (2 * n + 1) J ∧ ∃ G : Subgroup (Perm (Fin n)), IsCosetInstance G J) →
      LoopMatchG (masterAdmittedRound a b ((masterWinLiftOps R read enter g wd d).withHint H))
        Cg (fun J => decWinSI n J.1) (fun _ => decCoset n) P w j s
        (top4wTree P.1.1 hnd hlt (genGroup gens) hinv (decStrN n P.1.2.2.2.1) T) := by
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
      · rw [MasterOps.withHint_child]
        change masterAdmitChild a b (P, (if g P then (R.child (enter P, j, s)).bind _
          else none).map _) = none
        rw [if_pos hgP, hc]
        rfl
      · rfl
    · change decCoset n (top2NormC P.1.2.2.2.1 (topwCosetPreimage
        ((P.1.2.2.2.1, P.1.2.1), P.1.1, R.finish (enter P, s)))) = _
      rw [decCoset_top2NormC hx, hgens,
        topwCosetPreimage_spec hx hnd hlt hinv _ (ha.symm ▸ hA), ha]
  | call w j s J k hc hC hn ih =>
    intro hT hRun hL
    have hJ := hT (decR J) (by simp [SIReduction.calls])
    have hdJ := hread j s J hc
    rw [hdJ] at hJ
    obtain ⟨V, hV, hdec⟩ := topwRawInstance_spec (dom := P.1.2.2.2.1) (x := P.1.2.2.2.1)
      hx hx hnd hlt hinv (read P J) hJ
    have hLV : MasterCallLetters (2 * n + 1) (decWinSI n V) ∧
          ∃ G : Subgroup (Perm (Fin n)), IsCosetInstance G (decWinSI n V) := by
      rw [hdec, ← hdJ]
      exact hL _ (by simp [top4wTree, topwReduction, SIReduction.calls])
    have hwinV : (decWinSI n V).windowSize ≤ P.1.1.length := by
      rw [hdec, topwInstance_windowSize]
      calc (decWinSI P.1.1.length (read P J)).windowSize
          ≤ (Set.univ : Set (Fin P.1.1.length)).ncard :=
            Set.ncard_le_ncard (Set.subset_univ _)
        _ = P.1.1.length := by rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]
    have hV' : topwRawInstance (masterWinCtx P, read P J) = some V := by rw [hctx]; exact hV
    obtain ⟨hadm, hCg⟩ := hC V hV' hLV.1 hLV.2 hwinV
    have hchild : masterGuardedChild a b ((masterWinLiftOps R read enter g wd d).withHint H)
        (P, j, s) = some (masterLiftHinted H P j s V) := by
      have hj : j < R.width (enter P) := by
        by_contra hj
        have hnone := R.child_eq_none (enter P) j s (Nat.le_of_not_gt hj)
        rw [hc] at hnone
        contradiction
      unfold masterGuardedChild
      rw [if_pos (by change j < (if g P then _ else 0); rw [if_pos hgP]; exact hj.trans_le hwd),
        MasterOps.withHint_child]
      change masterAdmitChild a b (P, (if g P then (R.child (enter P, j, s)).bind _
        else none).map _) = _
      rw [if_pos hgP, hc, Option.bind_some, hctx, hV, Option.map_some, Option.map_some]
      exact hadm
    have hDV : decWinSI n (masterLiftHinted H P j s V).1 =
        topwInstance P.1.1 hnd hlt (genGroup gens) hinv (decStrN n P.1.2.2.2.1) (decR J) := by
      rw [masterLiftHinted, masterAttachHint_fst, masterCheckedCall_decode hx V hLV.1, hdec, hdJ]
    change LoopMatchG _ _ _ _ _ (w + 1) j s (.call
      (topwInstance P.1.1 hnd hlt (genGroup gens) hinv (decStrN n P.1.2.2.2.1) (decR J)) _)
    rw [← hDV]
    refine .call w j s _ _ hchild hCg ?_
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
    have hcomb : (masterAdmittedRound a b ((masterWinLiftOps R read enter g wd d).withHint H)).combine
        (P, j, s, z) = R.combine (enter P, j, s, topwCosetImage (P.1.2.2.2.1, P.1.1, z)) :=
      if_pos hgP
    rw [hcomb]
    change LoopMatchG _ _ _ _ _ w (j + 1)
      (R.combine (enter P, j, s, topwCosetImage (P.1.2.2.2.1, P.1.1, z)))
      (top4wTree P.1.1 hnd hlt (genGroup gens) hinv (decStrN n P.1.2.2.2.1)
        (k (topwImageSet P.1.1 hnd hlt (genGroup gens) hinv
          (decWinSI n (masterLiftHinted H P j s V).1).answer)))
    rw [hDV, topwImage_answer hnd hlt hinv (decStrN n P.1.2.2.2.1) _ (hdJ ▸ hJ)]
    exact htail

include hgP hwd hx hgens hread in
/-- The start of the lifted fold with hints. -/
theorem masterWinLiftH_start (a b : ℕ) (Cg : RawMasterSI → Prop)
    {T : SIReduction (Fin P.1.1.length) ℕ (Set (Perm (Fin P.1.1.length)))}
    (h : LoopMatchS R (MasterLiftStepOK a b n H read Cg P) decR (decCoset P.1.1.length)
      (enter P) (R.width (enter P)) 0 (R.init (enter P)) T)
    (hK : ∀ J ∈ T.calls, J.K ⊆ ((winRestrictHom n P.1.1 hnd hlt (genGroup gens) hinv).range :
      Set (Perm (Fin P.1.1.length))))
    (hRun : T.run ⊆ ((winRestrictHom n P.1.1 hnd hlt (genGroup gens) hinv).range :
      Set (Perm (Fin P.1.1.length))))
    (hL : ∀ J ∈ (top4wTree P.1.1 hnd hlt (genGroup gens) hinv (decStrN n P.1.2.2.2.1) T).calls,
      MasterCallLetters (2 * n + 1) J ∧ ∃ G : Subgroup (Perm (Fin n)), IsCosetInstance G J) :
    LoopMatchG (masterAdmittedRound a b ((masterWinLiftOps R read enter g wd d).withHint H))
      Cg (fun J => decWinSI n J.1) (fun _ => decCoset n) P
      (((masterWinLiftOps R read enter g wd d).withHint H).width P) 0
      (((masterWinLiftOps R read enter g wd d).withHint H).init P)
      (top4wTree P.1.1 hnd hlt (genGroup gens) hinv (decStrN n P.1.2.2.2.1) T) := by
  have hw : ((masterWinLiftOps R read enter g wd d).withHint H).width P = wd P := if_pos hgP
  have hi : ((masterWinLiftOps R read enter g wd d).withHint H).init P = R.init (enter P) :=
    if_pos hgP
  rw [hw, hi]
  exact masterWinLiftH_match hgP hwd hx hgens hnd hlt hinv decR hread a b Cg
    (h.mono_width hwd) hK hRun hL
end Match

/-! ### The condition on one lifted call of lines 5–7 -/

/-- **The condition on a lifted call of lines 5–7 and its hint** at a node `P` of degree `n`:
without a hint the window has at most `4/5` of the node's points; with a hint `h`, the call is
the hinted call of Procedure Align, line 11: `h` has its meaning for the call
(`Algo.MasterHintGood`), its labels are below `n`, and its Johnson parameter is at most half
of the node's (Eq. (73)). -/
def MasterHintStepOK (n : ℕ) (P : RawMasterSI) (V : RawWinSI) (o : Option RawMasterHint) :
    Prop :=
  o.elim (5 * (decWinSI n V).windowSize ≤ 4 * P.1.1.length) (fun h =>
    MasterHintGood ((masterCheckedCall (P.1.2.2.2.1, V)).1, h) ∧ (∀ i ∈ h.1.1, i < n) ∧
      2 * h.1.1.length ≤ masterParameter P)

/-- The condition at a step of the fold of lines 5–7, for the hint routine `H5`. -/
def MasterL57StepOK (n : ℕ)
    (H5 : (RawMasterSI × ℕ × AggnL57GState) × RawMasterSI → Option RawMasterHint)
    (P : RawMasterSI) (j : ℕ) (s : AggnL57GState) (J : AggnPhaseNode) : Prop :=
  ∀ V, topwRawInstance (masterWinCtx P, masterL57Read P J) = some V →
    MasterHintStepOK n P V (H5 ((P, j, s), masterCheckedCall (P.1.2.2.2.1, V)))

/-- **A lifted call with the condition of `Algo.MasterHintStepOK` is admitted, good, and makes
progress** at a hinted node `P = (W, some h)` whose hint has its meaning. -/
theorem masterLiftStepOK_of_hintStep {a b n : ℕ} {ω : Type}
    {H : (RawMasterSI × ℕ × ω) × RawMasterSI → Option RawMasterHint}
    {W : RawWinSI} {h : RawMasterHint} (hW : AggnCheckedWindowWF n W)
    (hg : MasterHintGood (W, h)) (hcap : masterCameronChildBound n ≤ masterInputCap a b n)
    (j : ℕ) (s : ω) (V : RawWinSI)
    (hok : MasterHintStepOK n (W, some h) V (H (((W, some h), j, s),
      masterCheckedCall (W.2.2.2.1, V))))
    (hL : MasterCallLetters (2 * n + 1) (decWinSI n V))
    (hC : ∃ G : Subgroup (Perm (Fin n)), IsCosetInstance G (decWinSI n V))
    (hwin : (decWinSI n V).windowSize ≤ W.1.length) :
    masterAdmitChild a b ((W, some h), some (masterLiftHinted H (W, some h) j s V)) =
        some (masterLiftHinted H (W, some h) j s V) ∧
      (MasterNodeGood n (masterLiftHinted H (W, some h) j s V) ∧
        MasterStepProgress (W, some h) (masterLiftHinted H (W, some h) j s V)) := by
  have hx : W.2.2.2.1.length = n := hW.2.2.2.2.2.1.1
  have hdegP : masterDegree ((W, some h) : RawMasterSI) = n := hx
  have hwP : masterWindowSize ((W, some h) : RawMasterSI) ≤ masterDegree ((W, some h) : RawMasterSI) := by
    change W.1.length ≤ W.2.2.2.1.length
    rw [hx]
    exact length_le_of_nodup_lt hW.1 hW.2.1
  have hCW := aggnCheckedWindow_wf W.2.2.2.1 V
  rw [hx] at hCW
  obtain ⟨G, hG⟩ := hC
  have hinvC := masterCheckedCall_rawIsInvariant hx V hL hG
  have hCwin : masterWindowSize (masterCheckedCall (W.2.2.2.1, V)) = (decWinSI n V).windowSize :=
    masterCheckedCall_window hx V
  have hdegC : masterDegree (masterCheckedCall (W.2.2.2.1, V)) = n :=
    (masterCheckedCall_degree _ _).trans hx
  have hpw := masterParameter_le_of_hintGood hg
  obtain ⟨m, ϕ, B, hB, hp, -, -, -, -, -, ht, -, -⟩ := hg
  have hm1 : 1 ≤ masterParameter ((W, some h) : RawMasterSI) := by
    have h1 : h.1.1.length = m := hp.2.1
    change 1 ≤ h.1.1.length
    have : 2 * h.2 < m := ht
    omega
  have hnot : ¬ MasterChainRuleNode ((W, some h) : RawMasterSI) := not_masterChainRuleNode_hint
  unfold masterLiftHinted
  unfold MasterHintStepOK at hok
  cases hH : H (((W, some h), j, s), masterCheckedCall (W.2.2.2.1, V)) with
  | none =>
    rw [hH] at hok
    simp only [Option.elim_none] at hok
    simp only [masterAttachHint_none]
    have hlt : (decWinSI (masterDegree ((W, some h) : RawMasterSI)) V).windowSize <
        masterWindowSize ((W, some h) : RawMasterSI) := by
      rw [hdegP]
      change _ < W.1.length
      have : 1 ≤ W.1.length := le_trans hm1 hpw
      omega
    refine ⟨masterCheckedCall_admitted a b V hwP hlt (by rw [hdegP]; exact hL)
      (G := hdegP ▸ G) (by subst hdegP; exact hG), ?_⟩
    have hJ : MasterRawNode n (masterCheckedCall (W.2.2.2.1, V)) :=
      ⟨hdegC, hCW, (rawIsInvariant_eq_true_iff hCW.2.2.1 hCW.2.1).mp hinvC⟩
    refine ⟨⟨hJ, fun h' hh' => by cases hh'⟩, masterStepProgress_hint_of_window ?_ ?_⟩
    · exact le_trans hm1 hpw
    · rw [hCwin]
      exact hok
  | some h' =>
    rw [hH] at hok
    obtain ⟨hg', hrows, hpar⟩ := hok
    simp only [masterAttachHint_some]
    have hwin' : (masterCheckedCall (W.2.2.2.1, V)).1.1.length ≤
        masterWindowSize ((W, some h) : RawMasterSI) := by
      change masterWindowSize (masterCheckedCall (W.2.2.2.1, V)) ≤ W.1.length
      rw [hCwin]
      exact hwin
    exact ⟨masterHintedCall_admitted hCW hg' hrows hinvC hdegP hwin' hpar hm1 hcap,
      masterHintedCall_good hCW hg' hinvC hdegP hwin' hpar hm1 hnot⟩

/-! ### Route 5 of the hinted node carrier -/

section Full
variable {TD : Type} {cameron : RawGens × List ℕ → Option RawCameron}
    {e f u v c tt dd : ℕ} {GD : MasterOps TD} {dD : TD} {c' b' t d dc dp E : ℕ}
    {H4 : (RawMasterSI × ℕ × TD) × RawMasterSI → Option RawMasterHint}
    {H5 : (RawMasterSI × ℕ × AggnL57GState) × RawMasterSI → Option RawMasterHint}

section Node
variable {n : ℕ} {W : RawWinSI} {h : RawMasterHint} (hW : AggnCheckedWindowWF n W)
    (hinv : IsInvariant (decGroup n W.2.1) (winSet n W.1))

include hW hinv in
set_option maxHeartbeats 1000000 in
/-- **Section 15, lines 5–7, with the hinted call of Procedure Align line 11, in the hinted
node carrier, with its children.** Let `T₀` be a tree on the window of a good node of route 5
that the round of lines 5–7 walks from the node's lines-5–7 node, on the node's context
(`Algo.masterL57Ctx`), with the condition `Algo.MasterL57StepOK` at every step: each lifted
call either has at most `4/5` of the window and no hint, or carries a hint with its meaning,
labels below `n`, and a Johnson parameter at most half of the node's. If the calls of `T₀` are
coset instances in the window's group `G_Δ` with letters at most `2|Δ|`, and `T₀` returns
`Iso_{G_Δ}` of the context's strings, then the hinted node carrier walks the lift of `T₀` with
its letters renamed back (`Algo.masterL57Unl`), shifted to the node's frame, with as many
calls; it returns `Iso_G(x,y)`, and every child it produces is a
good node that makes the progress of Sec. 11.4 (recurrence (ii) for the hinted call). -/
theorem masterNodeH_hint_line57_matchGood {a b : ℕ}
    (hcap : masterCameronChildBound n ≤ masterInputCap a b n)
    (hE : MasterL57EOK c' b' t d dc dp e f E) (hr : masterHintRoute (W, h) = 5)
    (hg : MasterHintGood (W, h))
    (T₀ : SIReduction (Fin W.1.length) ℕ (Set (Perm (Fin W.1.length))))
    (hm : LoopMatchS (masterL57Round c' b' t d dc dp e f) (MasterL57StepOK n H5 (W, some h))
      (aggnPhaseDecode W.1.length) (decCoset W.1.length) (masterL57Enter (W, some h))
      ((masterL57Round c' b' t d dc dp e f).width (masterL57Enter (W, some h))) 0
      ((masterL57Round c' b' t d dc dp e f).init (masterL57Enter (W, some h))) T₀)
    (hK : ∀ J ∈ T₀.calls, J.K ⊆
      (decGroup W.1.length (masterL57Ctx (W, some h)).1.1.2 : Set (Perm (Fin W.1.length))))
    (hcos : ∀ J ∈ T₀.calls,
      IsCosetInstance (decGroup W.1.length (masterL57Ctx (W, some h)).1.1.2) J)
    (hrun : T₀.run = strIso
      (decGroup W.1.length (masterL57Ctx (W, some h)).1.1.2 : Set (Perm (Fin W.1.length)))
      (decStrN W.1.length (masterL57Ctx (W, some h)).2.1)
      (decStrN W.1.length (masterL57Ctx (W, some h)).2.2.1))
    (hlet : ∀ J ∈ T₀.calls, MasterCallLetters (2 * W.1.length + 1) J) :
    ∃ T : SIReduction (Fin n) ℕ (Set (Perm (Fin n))),
      LoopMatchG (masterAdmittedRound a b
          (masterNodeHOps masterLine1B masterLine1C₀ cameron e f u v c tt dd GD dD
            c' b' t d dc dp E H4 H5))
        (fun J => MasterNodeGood n J ∧ MasterStepProgress (W, some h) J)
        (fun J => decWinSI n J.1) (fun _ => decCoset n) (W, some h)
        ((masterNodeHOps masterLine1B masterLine1C₀ cameron e f u v c tt dd GD dD
            c' b' t d dc dp E H4 H5).width (W, some h)) 0
        ((masterNodeHOps masterLine1B masterLine1C₀ cameron e f u v c tt dd GD dD
            c' b' t d dc dp E H4 H5).init (W, some h)) T ∧
      T.run = (decWinSI n W).answer ∧ T.calls.length = T₀.calls.length := by
  have hx := hW.2.2.2.2.2.1
  have hy := hW.2.2.2.2.2.2
  have hgs := hW.2.2.1
  have hnd := hW.1
  have hlt := hW.2.1
  have hgrp := masterLine4b_group (p := (W, h)) hgs hnd hlt hinv
  have hgrp' : decGroup W.1.length (masterL57Ctx (W, some h)).1.1.2 =
      (winRestrictHom n W.1 hnd hlt (decGroup n W.2.1) hinv).range :=
    (masterL57Ctx_group' W h).trans hgrp
  have hN : W.1.length ≤ W.2.2.2.1.length := by
    rw [hx.1]; exact length_le_of_nodup_lt hnd hlt
  have hK' : ∀ J ∈ T₀.calls, J.K ⊆
      ((winRestrictHom n W.1 hnd hlt (decGroup n W.2.1) hinv).range :
        Set (Perm (Fin W.1.length))) := by
    rw [← hgrp']
    exact hK
  have hcalls' := masterL57Unl_lifted_calls (p := (W, h)) hx hy hnd hlt hinv hlet
    (fun J hJ => (hcos J hJ).of_K_subset (hK' J hJ))
  have hKU : ∀ J ∈ (masterL57Unl (W, some h) T₀).calls, J.K ⊆
      ((winRestrictHom n W.1 hnd hlt (decGroup n W.2.1) hinv).range :
        Set (Perm (Fin W.1.length))) := by
    rw [masterL57Unl_calls (P := (W, some h)) hN hlet]
    intro J hJ
    obtain ⟨J₀, hJ₀, rfl⟩ := List.mem_map.1 hJ
    exact hK' J₀ hJ₀
  have hR' : (masterL57Unl (W, some h) T₀).run ⊆
      ((winRestrictHom n W.1 hnd hlt (decGroup n W.2.1) hinv).range :
        Set (Perm (Fin W.1.length))) := by
    rw [masterL57Unl_run (P := (W, some h)) hN hlet, hrun, ← hgrp']
    exact fun _ h => h.1
  have hL : ∀ J ∈ (top4wTree W.1 hnd hlt (decGroup n W.2.1) hinv (decStrN n W.2.2.2.1)
      (masterL57Unl (W, some h) T₀)).calls,
      MasterCallLetters (2 * n + 1) J ∧ ∃ G₀ : Subgroup (Perm (Fin n)), IsCosetInstance G₀ J :=
    fun J hJ => ⟨(hcalls' J hJ).1, _, (hcalls' J hJ).2.1⟩
  have hgd : masterL57Guard (W, some h) = true := masterL57Guard_of_good hg
  have hmU := LoopMatchS.redMapCalls (dec₂ := fun J => decWinSI W.1.length
      (masterL57Read (W, some h) J)) (siUnlabel (masterL57Order (W, some h)))
    (fun _ _ _ hJ => by
      obtain ⟨h1, h2⟩ := masterL57_child_decode hJ
      exact ⟨h1, masterL57_unlabel_answer hN h2⟩) hm
  have hm' := LoopMatchS.mono (C' := MasterLiftStepOK a b n H5 masterL57Read
      (fun J => MasterNodeGood n J ∧ MasterStepProgress (W, some h) J) (W, some h))
    (fun j s J hs V hV hLV hCV hwV =>
      masterLiftStepOK_of_hintStep hW hg hcap j s V (hs V hV) hLV hCV hwV) hmU
  have h1 := masterWinLiftH_start (d := (default : AggnL57GState)) (H := H5) hgd
    (masterL57Width_ge hE hgd) hx.1 (map_encPerm_decPerm hgs).symm hnd hlt hinv
    (fun J => decWinSI W.1.length (masterL57Read (W, some h) J)) (fun _ _ _ _ => rfl) a b _
    hm' hKU hR' hL
  have h2 := masterShiftOps_matchG a b _ hx.1 h1
  have h3 := masterPairIte_matchG_neg (sel := masterRouteAt 4)
    (F := masterLine4cdOps c tt dd (GD.withHint H4) dD) (dS := (dD, default)) (dT := default)
    a b (masterRouteAt_false (p := (W, h)) (by omega)) h2
  have h4 := masterPairIte_matchG_neg (sel := masterRouteAt 3) (F := master4bOps e f u v)
    (dS := default) (dT := ((dD, default), default))
    a b (masterRouteAt_false (p := (W, h)) (by omega)) h3
  have h5 := masterPairIte_matchG_neg (sel := masterRouteAt 2)
    (F := masterLeafOps primitiveWindowLeaf) (dS := masterCamFoldEmbed none)
    (dT := (default, (dD, default), default))
    a b (masterRouteAt_false (p := (W, h)) (by omega)) h4
  have h6 := masterPairIte_matchG_neg (sel := masterRouteAt 1)
    (F := masterDescPreparedOps 3) (dS := masterCamFoldEmbed none)
    (dT := (masterCamFoldEmbed none, default, (dD, default), default))
    a b (masterRouteAt_false (p := (W, h)) (by omega)) h5
  have hl1 : masterIsLine1 ((W, some h) : RawMasterSI) = false := by
    cases hq : masterIsLine1 ((W, some h) : RawMasterSI)
    · rfl
    · exact absurd ((masterIsLine1_iff _).mp hq) (by simp)
  have h7 := masterPairIte_matchG_neg (sel := masterIsLine1)
    (F := masterLine1Ops masterLine1B masterLine1C₀ cameron)
    (dS := masterCamFoldEmbed none)
    (dT := (masterCamFoldEmbed none, masterCamFoldEmbed none, default, (dD, default), default))
    a b hl1 h6
  refine ⟨(top4wTree W.1 hnd hlt (decGroup n W.2.1) hinv (decStrN n W.2.2.2.1)
    (masterL57Unl (W, some h) T₀)).bind (fun A => .done (decPerm n W.2.2.1 • A)), h7, ?_, ?_⟩
  · have hix : decStrN W.1.length (masterHintTop (W, h)).2.1 =
        fun i => decStrN n W.2.2.2.1 (winEquiv n W.1 hnd hlt i) :=
      topwRestrictStr_decode hnd hlt _
    have hiy : decStrN W.1.length (masterHintTop (W, h)).2.2 =
        fun i => strAct (decStrN n W.2.2.2.2) (decPerm n W.2.2.1)⁻¹ (winEquiv n W.1 hnd hlt i) :=
      top4aTarget_restrict hx.1 hnd hlt _ _
    rw [SIReduction.run_bind, SIReduction.run_done, top4wTree_run hnd hlt hinv _ _ hKU,
      masterL57Unl_run (P := (W, some h)) hN hlet, hrun, masterL57Ctx_strIso', hgrp', hix, hiy,
      topwPreimage_strIso hnd hlt hinv]
    change _ = wIso (winSet n W.1) (decCoset n (some (W.2.1, W.2.2.1))) _ _
    rw [decCoset_some, wIso_smul]
    rfl
  · simp only [top4wTree, SIReduction.calls_bind, SIReduction.calls_done, List.append_nil]
    rw [calls_topwReduction hnd hlt hinv _ _ hKU, List.length_map,
      masterL57Unl_calls (P := (W, some h)) hN hlet, List.length_map]
end Node

/-- **What the Section 13 track supplies at a node of route 5, with the hinted call of line 11
allowed**: the round of lines 5–7 walks, from the node's lines-5–7 node, a tree `T₀` on the
window with the condition `Algo.MasterL57StepOK` of the hint routine `H5` at every step, stated
on the node's context (`Algo.masterL57Ctx`: the group `G_Δ`, and the two strings on the window
with their letters renamed): its calls are coset instances in `G_Δ` with letters at most
`2|Δ|`, and it returns `Iso_{G_Δ}` of the context's strings, in at most `q45 |Δ|` calls. (The
node of lines 5–7 is well formed at every good node, `Algo.masterL57Guard_of_good`.) -/
def MasterL57SupplyH (c' b' t d dc dp e f n : ℕ) (q45 : ℕ → ℕ)
    (H5 : (RawMasterSI × ℕ × AggnL57GState) × RawMasterSI → Option RawMasterHint) : Prop :=
  ∀ (W : RawWinSI) (h : RawMasterHint), MasterNodeGood n (W, some h) →
    masterHintRoute (W, h) = 5 →
    ∃ T₀ : SIReduction (Fin W.1.length) ℕ (Set (Perm (Fin W.1.length))),
      LoopMatchS (masterL57Round c' b' t d dc dp e f) (MasterL57StepOK n H5 (W, some h))
        (aggnPhaseDecode W.1.length) (decCoset W.1.length) (masterL57Enter (W, some h))
        ((masterL57Round c' b' t d dc dp e f).width (masterL57Enter (W, some h))) 0
        ((masterL57Round c' b' t d dc dp e f).init (masterL57Enter (W, some h))) T₀ ∧
      (∀ J ∈ T₀.calls, J.K ⊆
        (decGroup W.1.length (masterL57Ctx (W, some h)).1.1.2 : Set (Perm (Fin W.1.length)))) ∧
      (∀ J ∈ T₀.calls,
        IsCosetInstance (decGroup W.1.length (masterL57Ctx (W, some h)).1.1.2) J) ∧
      T₀.run = strIso
        (decGroup W.1.length (masterL57Ctx (W, some h)).1.1.2 : Set (Perm (Fin W.1.length)))
        (decStrN W.1.length (masterL57Ctx (W, some h)).2.1)
        (decStrN W.1.length (masterL57Ctx (W, some h)).2.2.1) ∧
      (∀ J ∈ T₀.calls, MasterCallLetters (2 * W.1.length + 1) J) ∧
      T₀.calls.length ≤ q45 W.1.length

/-- **The obligation of route 5 of the hinted node carrier from the supply of Section 13.** -/
theorem masterParamRoute5H_of_supply {a b n : ℕ} {q45 : ℕ → ℕ}
    (hcap : masterCameronChildBound n ≤ masterInputCap a b n)
    (hE : MasterL57EOK c' b' t d dc dp e f E) (hS : MasterL57SupplyH c' b' t d dc dp e f n q45 H5) :
    MasterParamRoute (masterAdmittedRound a b
      (masterNodeHOps masterLine1B masterLine1C₀ cameron e f u v c tt dd GD dD
        c' b' t d dc dp E H4 H5)) n q45 5 := by
  intro W h hG _ hr
  obtain ⟨⟨-, hW, hinv⟩, hgood⟩ := id hG
  obtain ⟨T₀, hm, hK, hcos, hrun, hlet, hlen⟩ := hS W h hG hr
  obtain ⟨T, hT, hTrun, hTlen⟩ := masterNodeH_hint_line57_matchGood (cameron := cameron)
    (u := u) (v := v) (c := c) (tt := tt) (dd := dd) (GD := GD) (dD := dD) (H4 := H4)
    hW hinv hcap hE hr (hgood h rfl) T₀ hm hK hcos hrun hlet
  refine ⟨T, hT, hTrun, ?_, fun hch => absurd hch not_masterChainRuleNode_hint⟩
  change T.calls.length ≤ q45 W.1.length
  rw [hTlen]
  exact hlen

/-- **The current form of the supply gives the relaxed one, without hints.** A tree of
`Algo.MasterL57Supply` (every call with at most `4/5` of the window) is a tree of
`Algo.MasterL57SupplyH` for the hint routine that attaches no hint. -/
theorem masterL57SupplyH_of_supply {c' b' t d dc dp e f n : ℕ} {q45 : ℕ → ℕ}
    (hS : MasterL57Supply c' b' t d dc dp e f n q45) :
    MasterL57SupplyH c' b' t d dc dp e f n q45 (fun _ => none) := by
  intro W h hG hr
  obtain ⟨⟨-, hW, hinv⟩, -⟩ := id hG
  obtain ⟨T₀, hm, hK, hcos, hrun, hcalls, hlen⟩ := hS W h hG hr
  refine ⟨T₀, ?_, hK, hcos, hrun, fun J hJ => (hcalls J hJ).1, hlen⟩
  have hx := hW.2.2.2.2.2.1
  have hgs := hW.2.2.1
  have hnd := hW.1
  have hlt := hW.2.1
  have hgrp := masterLine4b_group (p := (W, h)) hgs hnd hlt hinv
  have hgrp' : decGroup W.1.length (masterL57Ctx (W, some h)).1.1.2 =
      (winRestrictHom n W.1 hnd hlt (decGroup n W.2.1) hinv).range :=
    (masterL57Ctx_group' W h).trans hgrp
  refine LoopMatch.toS (fun K => K.K ⊆
      (decGroup W.1.length (masterL57Ctx (W, some h)).1.1.2 : Set (Perm (Fin W.1.length))) ∧
      5 * K.windowSize ≤ 4 * W.1.length) ?_ hm (fun K hK' => ⟨hK K hK', (hcalls K hK').2⟩)
  rintro j s J hc ⟨hKJ, h5⟩ V hV
  obtain ⟨hrd, -⟩ := masterL57_child_decode hc
  set Wc := masterL57Read (W, some h) J
  rw [hgrp'] at hKJ
  have hKJ' : (decWinSI W.1.length Wc).K ⊆
      ((winRestrictHom n W.1 hnd hlt (decGroup n W.2.1) hinv).range :
        Set (Perm (Fin W.1.length))) := by
    rw [hrd]; exact hKJ
  have h5' : 5 * (decWinSI W.1.length Wc).windowSize ≤ 4 * W.1.length := by
    rw [hrd]; exact h5
  have hctx : masterWinCtx ((W, some h) : RawMasterSI) =
      ((W.2.2.2.1, (W.2.1.map (decPerm n)).map (encPerm n)), W.1, W.2.2.2.1) := by
    rw [masterWinCtx, map_encPerm_decPerm hgs]
  obtain ⟨Z, hZ, hdec⟩ := topwRawInstance_spec (dom := W.2.2.2.1) (x := W.2.2.2.1)
    (gens := W.2.1.map (decPerm n)) hx.1 hx.1 hnd hlt hinv Wc hKJ'
  change topwRawInstance (masterWinCtx ((W, some h) : RawMasterSI), Wc) = some V at hV
  rw [hctx, hZ] at hV
  have hVZ : V = Z := (Option.some.inj hV).symm
  change 5 * (decWinSI n V).windowSize ≤ 4 * W.1.length
  rw [hVZ, hdec, topwInstance_windowSize]
  exact h5'

set_option synthInstance.maxSize 2048 in
/-- **Theorem 1.1.1 on the RAM with the hinted children of line 11, route 5 reduced to the
window.** As `Algo.siWorkspaceRoutine_of_hintedRoutes`, with route 5 supplied as a tree on the
window at every node (`Algo.MasterL57SupplyH`, which allows the hinted call), for a reserve
exponent `E` that bounds the reserves of the round of lines 5–7 (`Algo.MasterL57EOK`). -/
theorem siWorkspaceRoutine_of_hintedSupply [Enc TD]
    (hc : PolyFun cameron) (hs : CameronSpec cameron) (hTc : TopwpCap e f)
    (hTo : Top4wCap e f u v) (dD : TD) (CD : MasterOpsCost masterCapA masterCapB GD)
    (hH4 : QuasiFun H4) (hH5 : QuasiFun H5) (hE : MasterL57EOK c' b' t d dc dp e f E)
    {q45 : ℕ → ℕ} (hq45 : Monotone q45) (hq : QuasiPolyBound q45)
    (hGD : ∀ n P s, masterDegree P = n → RawCoset.WF n (GD.finish (P, s)))
    (h4 : ∀ n, MasterParamRoute (masterAdmittedRound masterCapA masterCapB
      (masterNodeHOps masterLine1B masterLine1C₀ cameron e f u v c tt dd GD dD
        c' b' t d dc dp E H4 H5)) n q45 4)
    (h5 : ∀ n, MasterL57SupplyH c' b' t d dc dp e f n q45 H5) : SIWorkspaceRoutine :=
  siWorkspaceRoutine_of_hintedRoutes hc hs hTc hTo dD CD hH4 hH5 hq45 hq hGD h4
    (fun n => masterParamRoute5H_of_supply (masterCap_spec n) hE (h5 n))
end Full

end Algo
