/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: the round of Sec. 15, lines 5–7 (`Algo.aggnL57Round`) matches the
Master's reduction `Babai.Line57Shape.red` at the Align exit with no dominant color class.
-/
import Workspace.Algo.AggNodeLine57Round
import Workspace.Algo.AlignDescentShape

/-!
# The round of lines 5–7 matches `Babai.Line57Shape.red`

At the Align exit of Sec. 15, lines 5–7 (outcomes (1), (2b) and (3) of Theorem 13.2.1, with no
reject), the Master's reduction is `Babai.Line57Shape.red` at the shape `.align S`: the two
phases of Procedure AggregateCertificates, then `S.red`, Procedure Align over the versions of
`X(y)`. This file proves that `Algo.aggnL57Round` walks this tree call for call and returns
its answer: with the plain loop of Eq. (71) when line 6 found no dominant color class or `m*`
is large (`Algo.aggnL57_align_match`), and with the strong descent to `ker ϕ*` of case 1 of
the repair of lines 7–11 when `m*` is small
(`Algo.aggnL57_align_match_small`, with the description `Algo.ADDescribes`).

The hypothesis on `S` is that the header the round computes after the two phases describes
`S` (`Algo.AVDescribes`): the action is `S.ϕ`, the first version of `X(x)` decodes to `S.X'`,
the versions of `X(y)` decode to `S.versions`, the windows decode to `S.head :: S.tail`, and the
facts `Babai.Line4cdData` asks of the shape (invariance, correctness) hold. It is asked of
every state the two phases may end in; these states are exactly those that
`Algo.aggnAggregate_phases` describes (completed stores and comparison table), and on them
the tags and versions of `Algo.aggnContinuation` are specified in
`Workspace/Algo/AggNodeContinuation.lean`.

The count of the calls uses `Algo.avRem`, an upper bound on the calls the loop over the
versions still makes, which drops at every call; so the index of every call stays below the
width of the node.
-/
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 2000000
namespace Algo
open RAM RAM.Targets Babai Equiv

/-! ## The index of a phase -/

section Index

variable {ι ω α Ω A β : Type*} {R : Round ι ω α} {decI : ι → SIInstance Ω A}
  {decA : α → Set (Perm Ω)} {I : ι}

/-- Along a matching derivation, index plus remaining budget stays the same. -/
theorem loopMatchK_index {Q : β → ℕ → ℕ → ω → Prop} :
    ∀ {w j : ℕ} {s : ω} {T : SIReduction Ω A β}, LoopMatchK R decI decA I w j s T Q →
      LoopMatchK R decI decA I w j s T (fun b w' j' s' => Q b w' j' s' ∧ j' + w' = j + w) := by
  intro w j s T h
  induction h with
  | done w j s b Q hq => exact .done w j s b _ ⟨hq, rfl⟩
  | call w j s J k Q hc hn ih =>
    exact .call w j s J k _ hc fun a ha =>
      loopMatchK_mono_Q (fun b w' j' s' hb => ⟨hb.1, by omega⟩) (ih a ha)

/-- **A phase with call bound `c` ends at an index at most `c` past its start.** -/
theorem phaseMatch_index {P : β → ℕ → ω → Prop} {c j : ℕ} {s : ω} {T : SIReduction Ω A β}
    (h : PhaseMatch R decI decA I c j s T P) :
    PhaseMatch R decI decA I c j s T (fun b j' s' => P b j' s' ∧ j' ≤ j + c) := by
  intro r
  refine loopMatchK_mono_Q ?_ (loopMatchK_index (h r))
  rintro b w' j' s' ⟨⟨hr, hp⟩, he⟩
  exact ⟨hr, hp, by omega⟩

end Index

/-! ## The calls the loop over the versions still makes -/

/-- An upper bound on the calls the loop still makes from a state: the windows left in the
current version, and all windows of every later version. -/
def avRem (p : AVHdr × AVState) : ℕ :=
  p.2.2.2.1.elim 0 fun _ =>
    (p.1.2.2.2.1.length - p.2.2.1) + (p.1.2.2.1.length - (p.2.1 + 1)) * p.1.2.2.2.1.length

theorem avTr_isSome_lt {h : AVHdr} {k : ℕ} (hs : (avTr (h, k)).isSome) :
    k < h.2.2.1.length := by
  by_contra hc
  rw [avTr_end (by omega)] at hs
  exact absurd hs (by simp)

theorem avRem_avPos (h : AVHdr) (k : ℕ) (acc : RawCoset) :
    avRem (h, avPos (h, k, acc)) ≤ (h.2.2.1.length - k) * h.2.2.2.1.length := by
  unfold avPos avRem
  dsimp only
  rcases hc : avTr (h, avNext (h, k)) with _ | gt
  · exact Nat.zero_le _
  · have hsome : (avTr (h, avNext (h, k))).isSome := by rw [hc]; rfl
    have hlt := avTr_isSome_lt hsome
    have hge : k ≤ avNext (h, k) := by
      rcases avNext_spec h k with ⟨he, _⟩ | ⟨hle, _⟩
      · omega
      · exact hle
    simp only [Option.elim]
    generalize avNext (h, k) = k' at hlt hge
    generalize h.2.2.1.length = L at hlt ⊢
    generalize h.2.2.2.1.length = W
    obtain ⟨e, rfl⟩ : ∃ e, L = k' + 1 + e := ⟨L - (k' + 1), by omega⟩
    have h1 : k' + 1 + e - (k' + 1) = e := by omega
    have h2 : k' + 1 + e - k = (e + 1) + (k' - k) := by omega
    rw [h1, h2, Nat.sub_zero]
    nlinarith

theorem avRem_init (h : AVHdr) : avRem (h, avInit h) ≤ avCalls h := by
  have := avRem_avPos h 0 none
  simpa [avInit, avCalls] using this

theorem avChild_some_cur {h : AVHdr} {st : AVState} {J : RawWinSI}
    (hJ : avChild (h, st) = some J) :
    ∃ gt, st.2.2.1 = some gt ∧ st.2.1 < h.2.2.2.1.length := by
  obtain ⟨k, w, cur, acc⟩ := st
  cases cur with
  | none => simp [avChild] at hJ
  | some gt =>
    refine ⟨gt, rfl, ?_⟩
    simp only [avChild, Option.bind_some] at hJ
    split_ifs at hJ with hc
    exact hc.1

theorem avRem_pos {h : AVHdr} {st : AVState} {J : RawWinSI} (hJ : avChild (h, st) = some J) :
    1 ≤ avRem (h, st) := by
  obtain ⟨gt, hcur, hw⟩ := avChild_some_cur hJ
  unfold avRem
  dsimp only
  rw [hcur]
  simp only [Option.elim]
  omega

/-- **Every call makes the count drop.** -/
theorem avRem_combine {h : AVHdr} {st : AVState} {J : RawWinSI} (hJ : avChild (h, st) = some J)
    (a : RawCoset) : avRem (h, avCombine (h, st, a)) + 1 ≤ avRem (h, st) := by
  obtain ⟨gt, hcur, hw⟩ := avChild_some_cur hJ
  obtain ⟨k, w, cur, acc⟩ := st
  dsimp only at hcur hw
  subst hcur
  have hrem : avRem (h, (k, w, some gt, acc)) =
      (h.2.2.2.1.length - w) + (h.2.2.1.length - (k + 1)) * h.2.2.2.1.length := rfl
  rw [hrem]
  rcases a with _ | a
  · have := avRem_avPos h (k + 1) acc
    show avRem (h, avPos (h, k + 1, acc)) + 1 ≤ _
    omega
  · unfold avCombine
    dsimp only
    simp only [Option.elim]
    split_ifs with hw'
    · show (h.2.2.2.1.length - (w + 1)) +
          (h.2.2.1.length - (min k h.2.2.1.length + 1)) * h.2.2.2.1.length + 1 ≤ _
      have hm : h.2.2.1.length - (min k h.2.2.1.length + 1) = h.2.2.1.length - (k + 1) := by
        omega
      rw [hm]
      omega
    · have := avRem_avPos h (k + 1) (rawCosetJoin (h.2.2.2.2.1, acc, some a))
      omega

/-! ## The caps change nothing on the states of the carrier -/

theorem aggnAggregatePack_idem (c dc dp : ℕ) (C : AggnPhaseCtx) (s : AggnAggregateState) :
    aggnAggregatePack c dc dp C (aggnAggregatePack c dc dp C s) = aggnAggregatePack c dc dp C s :=
  aggnAggregatePack_eq (aggnCapState_size dc _ _) (Nat.min_le_right _ _)
    (aggnCompareCapState_size dp _ _)

theorem aggnAggregateInit_pack (c dc dp : ℕ) (C : AggnPhaseCtx) :
    aggnAggregatePack c dc dp C (aggnAggregateInit c dc dp (C, none)) =
      aggnAggregateInit c dc dp (C, none) := by
  refine aggnAggregatePack_eq ?_ (Nat.zero_le _) ?_
  · dsimp only [aggnAggregateInit, aggnUniformRound]
    unfold aggnBoundedInit
    exact aggnCapState_size dc _ _
  · dsimp only [aggnAggregateInit, aggnCompareBoundedRound]
    unfold aggnCompareBoundedInit
    exact aggnCompareCapState_size dp _ _

theorem aggnAggregateCombine_pack (c dc dp : ℕ) (z : AggnPhaseNode × ℕ × AggnAggregateState × RawCoset) :
    aggnAggregatePack c dc dp z.1.1 (aggnAggregateCombine c dc dp z) = aggnAggregateCombine c dc dp z := by
  unfold aggnAggregateCombine
  exact aggnAggregatePack_idem c dc dp _ _

/-! ## The match -/

/-- The header of Eq. (71) describes the Align shape `S` of the Master side, whose round is
the union of Eq. (71) with the Chain Rule over the list `Ws` of windows: the action is
`S.ϕ`, the fixed version decodes to `S.X'`, the versions to `S.versions` in their order, the
windows to `Ws`, the windows are invariant under `ϕ⁻¹(Aut(X'))`, and the round of Procedure
Align is correct. With no dominant color class `Ws` is `S.head :: S.tail`
(`Algo.alignShape_red_of_dom_none`); with a dominant class and `m*` large it is the orbits of
`G*` in the dominant window followed by `S.tail` (`Algo.alignShape_red_of_dom_large`). -/
structure AVDescribes (n : ℕ) (h : AVHdr)
    (S : AlignShape (Fin n) ℕ (decGroup n h.1.1.2) (decStrN n h.2.2.2.2.1)
      (decStrN n h.2.2.2.2.2)) (Ws : List (Set (Fin n))) : Prop where
  red : S.red = (letI := S.act; cosetDesignAlign S.ϕ (decStrN n h.2.2.2.2.1)
    (decStrN n h.2.2.2.2.2) S.X' S.versions Ws)
  action : RawAction.WF n S.m h.1 S.ϕ
  giant : IsGiantRep S.ϕ
  cat : letI := S.act; IsCatAction (SplitOutcomes (Fin S.m))
  fixed : decAlignOutcome S.m h.2.1 = some S.X'
  versions : h.2.2.1.map (decAlignOutcome S.m) = S.versions.map some
  windows : h.2.2.2.1.map (winSet n) = Ws
  nonempty : Ws ≠ []
  lt : ∀ W ∈ h.2.2.2.1, ∀ u ∈ W, u < n
  inv : letI := S.act;
    ∀ Δ ∈ Ws, IsInvariant (preimageSubgroup S.ϕ (structAut S.X')) Δ
  run : S.red.run = strIso ((decGroup n h.1.1.2 : Subgroup (Perm (Fin n))) :
    Set (Perm (Fin n))) (decStrN n h.2.2.2.2.1) (decStrN n h.2.2.2.2.2)

/-- The two phases of AggregateCertificates on the aggregate carrier with the caps `dc`,
`dp`, as `Algo.aggnAggregate_phases` gives them. -/
def AggnPhasesOK (c dc dp : ℕ) : Prop :=
  ∀ (n m : ℕ) (C : AggnPhaseCtx) (ϕ : decGroup n C.1.1.2 →* Perm (Fin m)),
    (aggnAggregateRound c dc dp).WF (C, none) → AggnPhaseCtxWF c n m C ϕ →
    LocalCertSetting (decGroup n C.1.1.2) ϕ →
    LargeK C.2.2.2.length (Nat.card (Fin n)) → 10 * C.2.2.2.length ≤ m →
    RawStr.WF n (2 * n) C.2.1 → RawStr.WF n (2 * n) C.2.2.1 →
    PhaseMatch (aggnAggregateRound c dc dp) (aggnPhaseDecode n) (decCoset n) (C, none)
      (aggnAggregateWidth c C) 0 ((aggnAggregateRound c dc dp).init (C, none))
      (aggregateRoundStrong ϕ (decStrN n C.2.1) (decStrN n C.2.2.1)
        (aggnFullEnum ϕ (decStrN n C.2.1) (decStrN n C.2.2.1)
          ((aggnPhaseRows c C).map (winSet m))) (.done ()))
      (fun _ _ v => v.1.1 = [] ∧ AggnStoresComplete c ϕ v.1.2.1 ∧
        v.2.2.1 = [] ∧ AggnCompareTableFor c ϕ (aggnCompareTable c (C, v.2.2.2.1)))

theorem exists_aggnPhasesOK (c : ℕ) : ∃ dc dp : ℕ,
    Nonempty (Round.RunCostQ (aggnAggregateRound c dc dp)) ∧ AggnPhasesOK c dc dp :=
  aggnAggregate_phases c

section Match

variable {c b t d dc dp n m : ℕ} {C : AggnPhaseCtx} {ϕ : decGroup n C.1.1.2 →* Perm (Fin m)}

/-- A state the two phases end in: capped, both pending lists empty, the stores complete and
the comparison table correct. -/
def AggnL57Post (c dc dp : ℕ) (C : AggnPhaseCtx) (ϕ : decGroup n C.1.1.2 →* Perm (Fin m))
    (s : AggnAggregateState) : Prop :=
  aggnAggregatePack c dc dp C s = s ∧ s.1.1 = [] ∧ AggnStoresComplete c ϕ s.1.2.1 ∧
    s.2.2.1 = [] ∧ AggnCompareTableFor c ϕ (aggnCompareTable c (C, s.2.2.2.1))

/-- §15, line 5, **stretch 1**: the round runs the two phases of AggregateCertificates as the
aggregate carrier does, and ends them in a state `(s, none)` with `s` a state the phases end
in, at an index at most the width of the carrier. -/
theorem aggnL57_stretch1 (hok : AggnPhasesOK c dc dp)
    (hI : (aggnL57Round c b t d dc dp).WF (C, none)) (hC : AggnPhaseCtxWF c n m C ϕ)
    (hset : LocalCertSetting (decGroup n C.1.1.2) ϕ)
    (ht : LargeK C.2.2.2.length (Nat.card (Fin n))) (htm : 10 * C.2.2.2.length ≤ m)
    (hx : RawStr.WF n (2 * n) C.2.1) (hy : RawStr.WF n (2 * n) C.2.2.1) :
    PhaseMatch (aggnL57Round c b t d dc dp) (aggnPhaseDecode n) (decCoset n) (C, none)
      (aggnAggregateWidth c C) 0 ((aggnL57Round c b t d dc dp).init (C, none))
      (aggregateRoundStrong ϕ (decStrN n C.2.1) (decStrN n C.2.2.1)
        (aggnFullEnum ϕ (decStrN n C.2.1) (decStrN n C.2.2.1)
          ((aggnPhaseRows c C).map (winSet m))) (.done ()))
      (fun _ j v => j ≤ aggnAggregateWidth c C ∧ v.2 = none ∧ AggnL57Post c dc dp C ϕ v.1) := by
  set M := aggnL57Round c b t d dc dp with hM
  have hP := phaseMatch_index (hok n m C ϕ hI hC hset ht htm hx hy)
  let Rel : ℕ → AggnAggregateState → ℕ → AggnL57State → Prop := fun jR vR jM vM =>
    jM = jR ∧ vM = (vR, none) ∧ aggnAggregatePack c dc dp C vR = vR
  have h1 := aggnPhaseMatch_sim (M := M) (decI' := aggnPhaseDecode n)
    (I' := ((C, none) : AggnPhaseNode)) Rel ?sim hP (k := 0) (t := M.init (C, none))
    ⟨rfl, rfl, aggnAggregateInit_pack c dc dp C⟩
  case sim =>
    rintro jR vR jM vM ⟨hj, hv, hpk⟩ J hJ
    subst jM vM
    have hJ' : aggnAggregateChild c ((C, none), jR, vR) = some J := hJ
    refine ⟨J, ?_, rfl, fun a => ⟨rfl, ?_, ?_⟩⟩
    · show aggnL57Child c b t d dc dp ((C, none), jR, (vR, none)) = some J
      unfold aggnL57Child
      rw [hJ']
      rfl
    · show aggnL57Combine c b t d dc dp ((C, none), jR, (vR, none), a) =
        (aggnAggregateCombine c dc dp ((C, none), jR, vR, a), none)
      unfold aggnL57Combine
      rw [hJ']
      rfl
    · exact aggnAggregateCombine_pack c dc dp ((C, none), jR, vR, a)
  refine phaseMatch_weaken h1 ?_
  rintro u j v ⟨jR, sR, ⟨⟨hq1, hstores, hq2, htbl⟩, hjle⟩, hj, hv, hpk⟩
  subst j v
  exact ⟨by omega, rfl, hpk, hq1, hstores, hq2, htbl⟩

/-- After the two phases the carrier makes no call. -/
theorem aggnL57_agg_done {s : AggnAggregateState} (hs : AggnL57Post c dc dp C ϕ s) (j : ℕ) :
    aggnAggregateChild c ((C, none), j, s) = none :=
  aggnAggregateChild_done c _ j s hs.2.1 hs.2.2.2.1

/-- §15, lines 5–7, **stretch 3 of the Align exit** (no dominant class, or `m*` large):
from a state the two phases end in, the round runs `S.red` with the cap of stretch 3 as call
bound, and stops with its answer. -/
theorem aggnL57_align_stretch3 (hx : RawStr.WF n (2 * n) C.2.1) (hy : RawStr.WF n (2 * n) C.2.2.1)
    (S : AlignShape (Fin n) ℕ (decGroup n C.1.1.2) (decStrN n C.2.1) (decStrN n C.2.2.1))
    (Ws : List (Set (Fin n)))
    (hS : ∀ s, AggnL57Post c dc dp C ϕ s →
      AVDescribes n (aggnL57Hdr c b t d dc dp (C, s)) S Ws)
    (hsmall : ∀ s, AggnL57Post c dc dp C ϕ s →
      l57Small (aggnL57Hdr c b t d dc dp (C, s)) = false) {sR : AggnAggregateState}
    (hpost : AggnL57Post c dc dp C ϕ sR) {jR : ℕ} (hjle : jR ≤ aggnAggregateWidth c C) :
    PhaseMatch (aggnL57Round c b t d dc dp) (aggnPhaseDecode n) (decCoset n) (C, none)
      (aggnL57Cap c b t d dc dp C) jR (sR, none) S.red
      (fun B j v => (aggnL57Round c b t d dc dp).child ((C, none), j, v) = none ∧
        decCoset n ((aggnL57Round c b t d dc dp).finish ((C, none), v)) = B) := by
  set M := aggnL57Round c b t d dc dp with hM
  set h0 := aggnL57Hdr c b t d dc dp (C, sR) with hh0
  have hD : AVDescribes n h0 S Ws := hS sR hpost
  have hagg : ∀ j, aggnAggregateChild c ((C, none), j, sR) = none := aggnL57_agg_done hpost
  have hsm : l57Small h0 = false := hsmall sR hpost
  have hcalls : l57Calls h0 = avCalls h0 := by unfold l57Calls; rw [hsm]; rfl
  have hinit : l57Init h0 = (avInit h0, 0, none) := by unfold l57Init; rw [hsm]; rfl
  have hl57child : ∀ st, l57Child (h0, st) = avChild (h0, st.1) := by
    intro st; unfold l57Child; rw [hsm]; rfl
  have hl57step : ∀ st a, l57Step (h0, st, a) = (avCombine (h0, st.1, a), 0, none) := by
    intro st a; unfold l57Step; rw [hsm]; rfl
  let pr : AggnL57State → AVState := fun v => (v.2.getD (l57Init h0)).1
  let Good : ℕ → AggnL57State → Prop := fun j v =>
    v.1 = sR ∧ j + avRem (h0, pr v) ≤ aggnAggregateWidth c C + avCalls h0
  have hlenV : h0.2.2.1.length = S.versions.length := by
    simpa only [List.length_map] using congrArg List.length hD.versions
  have hxn : C.2.1.length = n := hx.1
  have hdec : ∀ W g τ, aggnPhaseDecode n (avEmb (C, (W, g, τ, h0.2.2.2.2.1, h0.2.2.2.2.2))) =
      decWinSI n (W, g, τ, h0.2.2.2.2.1, h0.2.2.2.2.2) := by
    intro W g τ
    exact aggnCheckedWindow_decode hxn _ (fun i => aggnDecodedStr_le hx i)
      (fun i => aggnDecodedStr_le hy i)
  have hchild : ∀ j v J, Good j v → avChild (h0, pr v) = some J →
      M.child ((C, none), j, v) = some (avEmb (C, J)) := by
    rintro j ⟨s1, o⟩ J ⟨hs1, hle⟩ hav
    dsimp only at hs1
    subst hs1
    have hgate : j < aggnAggregateWidth c C + avCalls h0 := by
      have := avRem_pos hav
      omega
    show aggnL57Child c b t d dc dp ((C, none), j, (s1, o)) = some (avEmb (C, J))
    unfold aggnL57Child
    rw [hagg j, Option.elim_none]
    unfold aggnL57AlignChild
    dsimp only
    rw [Option.elim_none, hcalls, if_pos hgate]
    change (l57Child (h0, o.getD (l57Init h0))).map (fun J => avEmb (C, J)) = _
    rw [hl57child]
    change (avChild (h0, pr (s1, o))).map (fun J => avEmb (C, J)) = _
    rw [hav]
    rfl
  have hcombEq : ∀ j v a, v.1 = sR →
      M.combine ((C, none), j, v, a) = (v.1, some (avCombine (h0, pr v, a), 0, none)) := by
    rintro j ⟨s1, o⟩ a hs1
    dsimp only at hs1
    subst hs1
    show aggnL57Combine c b t d dc dp ((C, none), j, (s1, o), a) = _
    unfold aggnL57Combine
    rw [hagg j, Option.elim_none, hpost.1]
    change (s1, some (l57Step (h0, o.getD (l57Init h0), a))) = _
    rw [hl57step]
  have hcomb : ∀ j v a J, Good j v → avChild (h0, pr v) = some J →
      pr (M.combine ((C, none), j, v, a)) = avCombine (h0, pr v, a) ∧
        Good (j + 1) (M.combine ((C, none), j, v, a)) := by
    intro j v a J ⟨hs1, hle⟩ hav
    rw [hcombEq j v a hs1]
    refine ⟨rfl, hs1, ?_⟩
    have := avRem_combine hav a
    show j + 1 + avRem (h0, avCombine (h0, pr v, a)) ≤ _
    omega
  have hstart : Good jR (sR, none) := by
    refine ⟨rfl, ?_⟩
    have := avRem_init h0
    show jR + avRem (h0, (l57Init h0).1) ≤ _
    rw [hinit]
    show jR + avRem (h0, avInit h0) ≤ _
    omega
  have hmain := phaseMatch_alignShape_value_of (R := M) (decI := aggnPhaseDecode n)
    (I := ((C, none) : AggnPhaseNode)) (h := h0) (pr := pr) (emb := fun J => avEmb (C, J))
    (Good := Good) S Ws hD.red hdec hchild hcomb hD.action hD.giant hD.cat hD.fixed hD.versions
    hD.windows hD.nonempty hxn hD.lt hD.inv hD.run jR (sR, none)
    (show (l57Init h0).1 = avInit h0 by rw [hinit]) hstart
  have hcap : S.versions.length * h0.2.2.2.1.length ≤ aggnL57Cap c b t d dc dp C := by
    rw [← hlenV]
    show avCalls h0 ≤ _
    rw [← hcalls]
    exact l57Calls_le_cap c b t d dc dp C sR
  refine phaseMatch_weaken (phaseMatch_mono hmain hcap) ?_
  rintro B j' ⟨s1, o⟩ ⟨⟨hs1, -⟩, a, hpos, ha⟩
  dsimp only at hs1
  subst hs1
  have hpr : (o.getD (l57Init h0)).1 = (h0.2.2.1.length, 0, none, a) := hpos
  refine ⟨?_, ?_⟩
  · show aggnL57Child c b t d dc dp ((C, none), j', (s1, o)) = none
    unfold aggnL57Child
    rw [hagg j', Option.elim_none]
    unfold aggnL57AlignChild
    dsimp only
    rw [Option.elim_none]
    split_ifs
    · change (l57Child (h0, o.getD (l57Init h0))).map (fun J => avEmb (C, J)) = none
      rw [hl57child, hpr]
      rfl
    · rfl
  · show decCoset n (aggnL57Finish ((C, none), (s1, o))) = B
    unfold aggnL57Finish
    dsimp only
    rw [decCoset_rawCosetNorm hxn]
    cases o with
    | none =>
      have hacc : (l57Init h0).1.2.2.2 = a := by rw [Option.getD_none] at hpr; rw [hpr]
      rw [← ha, ← hacc, hinit]
      rfl
    | some st =>
      rw [Option.getD_some] at hpr
      rw [← ha]
      show decCoset n st.1.2.2.2 = _
      rw [hpr]

/-- §15, lines 5–7, **the Align exit on the RAM**: the round `Algo.aggnL57Round` matches
`Babai.Line57Shape.red` at the shape `.align S` call for call, with the width of the node as
budget, and returns its answer — provided the header the round computes after the two phases
of AggregateCertificates describes `S` with a list `Ws` of windows (`Algo.AVDescribes`). This
covers line 6 with no dominant color class, and lines 7–11 with `m*` large. -/
theorem aggnL57_align_match (hok : AggnPhasesOK c dc dp)
    (hI : (aggnL57Round c b t d dc dp).WF (C, none)) (hC : AggnPhaseCtxWF c n m C ϕ)
    (hset : LocalCertSetting (decGroup n C.1.1.2) ϕ)
    (ht : LargeK C.2.2.2.length (Nat.card (Fin n))) (htm : 10 * C.2.2.2.length ≤ m)
    (hx : RawStr.WF n (2 * n) C.2.1) (hy : RawStr.WF n (2 * n) C.2.2.1)
    (S : AlignShape (Fin n) ℕ (decGroup n C.1.1.2) (decStrN n C.2.1) (decStrN n C.2.2.1))
    (Ws : List (Set (Fin n)))
    (hS : ∀ s, AggnL57Post c dc dp C ϕ s →
      AVDescribes n (aggnL57Hdr c b t d dc dp (C, s)) S Ws)
    (hsmall : ∀ s, AggnL57Post c dc dp C ϕ s →
      l57Small (aggnL57Hdr c b t d dc dp (C, s)) = false) :
    LoopMatch (aggnL57Round c b t d dc dp) (aggnPhaseDecode n) (decCoset n) (C, none)
      ((aggnL57Round c b t d dc dp).width (C, none)) 0
      ((aggnL57Round c b t d dc dp).init (C, none))
      ((Line57Shape.align (ϕ := ϕ) (ts := C.2.2.2.length) S).red
        (aggnFullEnum ϕ (decStrN n C.2.1) (decStrN n C.2.2.1)
          ((aggnPhaseRows c C).map (winSet m)))) := by
  set M := aggnL57Round c b t d dc dp with hM
  set E := aggnFullEnum ϕ (decStrN n C.2.1) (decStrN n C.2.2.1)
    ((aggnPhaseRows c C).map (winSet m)) with hE
  have h1 := aggnL57_stretch1 (b := b) (t := t) (d := d) hok hI hC hset ht htm hx hy
  -- the tree
  have htree : (Line57Shape.align (ϕ := ϕ) (ts := C.2.2.2.length) S).red E =
      (aggregateRoundStrong ϕ (decStrN n C.2.1) (decStrN n C.2.2.1) E (.done ())).bind
        (fun _ => S.red) := by
    change aggregateRoundStrong ϕ (decStrN n C.2.1) (decStrN n C.2.2.1) E S.red = _
    simp only [aggregateRoundStrong, SIReduction.bind_assoc]
    rfl
  rw [htree]
  have hW : M.width (C, none) = aggnAggregateWidth c C + aggnL57Cap c b t d dc dp C := rfl
  refine loopMatch_of_phaseMatch
    (P := fun B j v => M.child ((C, none), j, v) = none ∧ decCoset n (M.finish ((C, none), v)) = B)
    (phaseMatch_bind h1 ?_) (fun B j v hv => hv) (by rw [hW])
  -- stretch 3: Procedure Align over the versions
  rintro u jR ⟨sR, o⟩ ⟨hjle, ho, hpost⟩
  dsimp only at ho hpost
  subst ho
  exact aggnL57_align_stretch3 hx hy S Ws hS hsmall hpost hjle

/-- §15, lines 5–7, **stretch 3 of the Align exit in case 1 of the repair of lines 7–11**
from a state the two phases end in, the round runs `S.red` with the cap of
stretch 3 as call bound, and stops with its answer. -/
theorem aggnL57_align_small_stretch3 (hx : RawStr.WF n (2 * n) C.2.1) (hy : RawStr.WF n (2 * n) C.2.2.1)
    (S : AlignShape (Fin n) ℕ (decGroup n C.1.1.2) (decStrN n C.2.1) (decStrN n C.2.2.1))
    (D : AlignDominantRoundData (Fin n))
    (hS : ∀ s, AggnL57Post c dc dp C ϕ s →
      ADDescribes n (aggnL57Hdr c b t d dc dp (C, s)) S D)
    (hsmall : ∀ s, AggnL57Post c dc dp C ϕ s →
      l57Small (aggnL57Hdr c b t d dc dp (C, s)) = true) {sR : AggnAggregateState}
    (hpost : AggnL57Post c dc dp C ϕ sR) {jR : ℕ} (hjle : jR ≤ aggnAggregateWidth c C) :
    PhaseMatch (aggnL57Round c b t d dc dp) (aggnPhaseDecode n) (decCoset n) (C, none)
      (aggnL57Cap c b t d dc dp C) jR (sR, none) S.red
      (fun B j v => (aggnL57Round c b t d dc dp).child ((C, none), j, v) = none ∧
        decCoset n ((aggnL57Round c b t d dc dp).finish ((C, none), v)) = B) := by
  set M := aggnL57Round c b t d dc dp with hM
  set h0 := aggnL57Hdr c b t d dc dp (C, sR) with hh0
  have hD : ADDescribes n h0 S D := hS sR hpost
  have hagg : ∀ j, aggnAggregateChild c ((C, none), j, sR) = none := aggnL57_agg_done hpost
  have hsm : l57Small h0 = true := hsmall sR hpost
  have hcalls : l57Calls h0 = adCalls h0 := by unfold l57Calls; rw [hsm]; rfl
  have hinit : l57Init h0 = adInit h0 := by unfold l57Init; rw [hsm]; rfl
  have hl57child : ∀ st, l57Child (h0, st) = adChild (h0, st) := by
    intro st; unfold l57Child; rw [hsm]; rfl
  have hl57step : ∀ st a, l57Step (h0, st, a) = adCombine (h0, st, a) := by
    intro st a; unfold l57Step; rw [hsm]; rfl
  let pr : AggnL57State → ADState := fun v => v.2.getD (l57Init h0)
  let Good : ℕ → AggnL57State → Prop := fun j v =>
    v.1 = sR ∧ j + adRem (h0, pr v) ≤ aggnAggregateWidth c C + adCalls h0
  have hxn : C.2.1.length = n := hx.1
  have hdec : ∀ W g τ, aggnPhaseDecode n (avEmb (C, (W, g, τ, h0.2.2.2.2.1, h0.2.2.2.2.2))) =
      decWinSI n (W, g, τ, h0.2.2.2.2.1, h0.2.2.2.2.2) := by
    intro W g τ
    exact aggnCheckedWindow_decode hxn _ (fun i => aggnDecodedStr_le hx i)
      (fun i => aggnDecodedStr_le hy i)
  have hchild : ∀ j v J, Good j v → adChild (h0, pr v) = some J →
      M.child ((C, none), j, v) = some (avEmb (C, J)) := by
    rintro j ⟨s1, o⟩ J ⟨hs1, hle⟩ hav
    dsimp only at hs1
    subst hs1
    have hgate : j < aggnAggregateWidth c C + adCalls h0 := by
      have := adRem_pos hav
      omega
    show aggnL57Child c b t d dc dp ((C, none), j, (s1, o)) = some (avEmb (C, J))
    unfold aggnL57Child
    rw [hagg j, Option.elim_none]
    unfold aggnL57AlignChild
    dsimp only
    rw [Option.elim_none, hcalls, if_pos hgate]
    change (l57Child (h0, o.getD (l57Init h0))).map (fun J => avEmb (C, J)) = _
    rw [hl57child]
    change (adChild (h0, pr (s1, o))).map (fun J => avEmb (C, J)) = _
    rw [hav]
    rfl
  have hcombEq : ∀ j v a, v.1 = sR →
      M.combine ((C, none), j, v, a) = (v.1, some (adCombine (h0, pr v, a))) := by
    rintro j ⟨s1, o⟩ a hs1
    dsimp only at hs1
    subst hs1
    show aggnL57Combine c b t d dc dp ((C, none), j, (s1, o), a) = _
    unfold aggnL57Combine
    rw [hagg j, Option.elim_none, hpost.1]
    change (s1, some (l57Step (h0, o.getD (l57Init h0), a))) = _
    rw [hl57step]
  have hcomb : ∀ j v a J, Good j v → adChild (h0, pr v) = some J →
      pr (M.combine ((C, none), j, v, a)) = adCombine (h0, pr v, a) ∧
        Good (j + 1) (M.combine ((C, none), j, v, a)) := by
    intro j v a J ⟨hs1, hle⟩ hav
    rw [hcombEq j v a hs1]
    refine ⟨rfl, hs1, ?_⟩
    have := adRem_combine hav a
    show j + 1 + adRem (h0, adCombine (h0, pr v, a)) ≤ _
    omega
  have hstart : Good jR (sR, none) := by
    refine ⟨rfl, ?_⟩
    have := adRem_init (h := h0)
    show jR + adRem (h0, l57Init h0) ≤ _
    rw [hinit]
    omega
  have hmain := phaseMatch_adShape (R := M) (decI := aggnPhaseDecode n)
    (I := ((C, none) : AggnPhaseNode)) (h := h0) (pr := pr) (emb := fun J => avEmb (C, J))
    (Good := Good) hD hdec hchild hcomb hxn jR (sR, none)
    (show l57Init h0 = adInit h0 from hinit) hstart
  have hcap : adCalls h0 ≤ aggnL57Cap c b t d dc dp C := by
    rw [← hcalls]
    exact l57Calls_le_cap c b t d dc dp C sR
  refine phaseMatch_weaken (phaseMatch_mono hmain hcap) ?_
  rintro B j' ⟨s1, o⟩ ⟨⟨hs1, -⟩, a, hpos, ha⟩
  dsimp only at hs1
  subst hs1
  have hpr : o.getD (l57Init h0) = ((h0.2.2.1.length, 0, none, a), (0, none)) := hpos
  refine ⟨?_, ?_⟩
  · show aggnL57Child c b t d dc dp ((C, none), j', (s1, o)) = none
    unfold aggnL57Child
    rw [hagg j', Option.elim_none]
    unfold aggnL57AlignChild
    dsimp only
    rw [Option.elim_none]
    split_ifs
    · change (l57Child (h0, o.getD (l57Init h0))).map (fun J => avEmb (C, J)) = none
      rw [hl57child, hpr]
      rfl
    · rfl
  · show decCoset n (aggnL57Finish ((C, none), (s1, o))) = B
    unfold aggnL57Finish
    dsimp only
    rw [decCoset_rawCosetNorm hxn]
    cases o with
    | none =>
      have hacc : (l57Init h0).1.2.2.2 = a := by rw [Option.getD_none] at hpr; rw [hpr]
      have hacc0 : (adInit h0).1.2.2.2 = none := by
        unfold adInit adPos; dsimp only; split_ifs <;> rfl
      rw [← ha, ← hacc, hinit, hacc0]
      rfl
    | some st =>
      rw [Option.getD_some] at hpr
      rw [← ha]
      show decCoset n st.1.2.2.2 = _
      rw [hpr]

/-- §15, lines 5–7, **the Align exit on the RAM in case 1 of the repair of lines 7–11**
when line 6 found a dominant class `D` and `m*` is small, the round
`Algo.aggnL57Round` matches `Babai.Line57Shape.red` at the shape `.align S` call for call,
with the width of the node as budget, and returns its answer — provided the header the
round computes after the two phases of AggregateCertificates, with the machine's lists of
case 1, describes `S` and `D` (`Algo.ADDescribes`), and the machine's test `Algo.l57Small`
holds there. -/
theorem aggnL57_align_match_small (hok : AggnPhasesOK c dc dp)
    (hI : (aggnL57Round c b t d dc dp).WF (C, none)) (hC : AggnPhaseCtxWF c n m C ϕ)
    (hset : LocalCertSetting (decGroup n C.1.1.2) ϕ)
    (ht : LargeK C.2.2.2.length (Nat.card (Fin n))) (htm : 10 * C.2.2.2.length ≤ m)
    (hx : RawStr.WF n (2 * n) C.2.1) (hy : RawStr.WF n (2 * n) C.2.2.1)
    (S : AlignShape (Fin n) ℕ (decGroup n C.1.1.2) (decStrN n C.2.1) (decStrN n C.2.2.1))
    (D : AlignDominantRoundData (Fin n))
    (hS : ∀ s, AggnL57Post c dc dp C ϕ s →
      ADDescribes n (aggnL57Hdr c b t d dc dp (C, s)) S D)
    (hsmall : ∀ s, AggnL57Post c dc dp C ϕ s →
      l57Small (aggnL57Hdr c b t d dc dp (C, s)) = true) :
    LoopMatch (aggnL57Round c b t d dc dp) (aggnPhaseDecode n) (decCoset n) (C, none)
      ((aggnL57Round c b t d dc dp).width (C, none)) 0
      ((aggnL57Round c b t d dc dp).init (C, none))
      ((Line57Shape.align (ϕ := ϕ) (ts := C.2.2.2.length) S).red
        (aggnFullEnum ϕ (decStrN n C.2.1) (decStrN n C.2.2.1)
          ((aggnPhaseRows c C).map (winSet m)))) := by
  set M := aggnL57Round c b t d dc dp with hM
  set E := aggnFullEnum ϕ (decStrN n C.2.1) (decStrN n C.2.2.1)
    ((aggnPhaseRows c C).map (winSet m)) with hE
  have h1 := aggnL57_stretch1 (b := b) (t := t) (d := d) hok hI hC hset ht htm hx hy
  -- the tree
  have htree : (Line57Shape.align (ϕ := ϕ) (ts := C.2.2.2.length) S).red E =
      (aggregateRoundStrong ϕ (decStrN n C.2.1) (decStrN n C.2.2.1) E (.done ())).bind
        (fun _ => S.red) := by
    change aggregateRoundStrong ϕ (decStrN n C.2.1) (decStrN n C.2.2.1) E S.red = _
    simp only [aggregateRoundStrong, SIReduction.bind_assoc]
    rfl
  rw [htree]
  have hW : M.width (C, none) = aggnAggregateWidth c C + aggnL57Cap c b t d dc dp C := rfl
  refine loopMatch_of_phaseMatch
    (P := fun B j v => M.child ((C, none), j, v) = none ∧ decCoset n (M.finish ((C, none), v)) = B)
    (phaseMatch_bind h1 ?_) (fun B j v hv => hv) (by rw [hW])
  -- stretch 3: the strong descent to `ker ϕ*`, version by version
  rintro u jR ⟨sR, o⟩ ⟨hjle, ho, hpost⟩
  dsimp only at ho hpost
  subst ho
  exact aggnL57_align_small_stretch3 hx hy S D hS hsmall hpost hjle

/-- At the exits with no versions of `X(y)` (tags `0`, `2`, `5` and `6`) both lists are
empty. -/
theorem aggnContinuation_versions_nil (z : AggnPhaseCtx × AggnAggregateState)
    (h : (aggnContinuation c b t d z).1 ≠ 1 ∧ (aggnContinuation c b t d z).1 ≠ 3 ∧
      (aggnContinuation c b t d z).1 ≠ 4) :
    (aggnContinuation c b t d z).2.2 = [] := by
  rcases aggnAggregateDispatch_cases z with hd | hd | hd
  · rw [aggnContinuation_of_one hd] at h; exact absurd rfl h.1
  · cases hg : aggnAggregateGiantBranch z
    · cases hr : aggnRejectCase z
      · rw [aggnContinuation_of_case2b hd hg hr] at h; exact absurd rfl h.2.1
      · rw [aggnContinuation_of_rejectCase hd hg hr]
    · rw [aggnContinuation_of_giant hd hg]
  · cases hr : aggnRejectDefect z
    · rw [aggnContinuation_of_case3 hd hr] at h ⊢
      unfold aggnContCase3 at h ⊢
      cases hf : aggnGuideSplitFamilies c b t d z
      · rfl
      · rw [hf] at h; exact absurd rfl h.2.2
    · rw [aggnContinuation_of_rejectDefect hd hr]

/-- §15, lines 5–7, **stretch 3 at the exits with no versions**: from a state the two phases
end in, stretch 3 makes no call and the round stops with the answer `∅`. -/
theorem aggnL57_nil_stretch3
    (htag : ∀ s, AggnL57Post c dc dp C ϕ s →
      (aggnContinuation c b t d (C, s)).1 ≠ 1 ∧ (aggnContinuation c b t d (C, s)).1 ≠ 3 ∧
        (aggnContinuation c b t d (C, s)).1 ≠ 4)
    {sR : AggnAggregateState} (hpost : AggnL57Post c dc dp C ϕ sR) (jR : ℕ) :
    PhaseMatch (aggnL57Round c b t d dc dp) (aggnPhaseDecode n) (decCoset n) (C, none)
      0 jR (sR, none) (.done ∅)
      (fun B j v => (aggnL57Round c b t d dc dp).child ((C, none), j, v) = none ∧
        decCoset n ((aggnL57Round c b t d dc dp).finish ((C, none), v)) = B) := by
  refine phaseMatch_done ⟨?_, rfl⟩
  have hnil : (aggnL57Hdr c b t d dc dp (C, sR)).2.2.1 = [] := by
    show (aggnContinuation c b t d (C, aggnAggregatePack c dc dp C sR)).2.2 = []
    rw [hpost.1]
    exact aggnContinuation_versions_nil _ (htag sR hpost)
  have hinit : l57Child (aggnL57Hdr c b t d dc dp (C, sR),
      l57Init (aggnL57Hdr c b t d dc dp (C, sR))) = none := by
    unfold l57Child l57Init
    cases l57Small (aggnL57Hdr c b t d dc dp (C, sR))
    · have hend := avPos_end (h := aggnL57Hdr c b t d dc dp (C, sR)) (k := 0) none
        (by rw [hnil]; exact le_rfl)
      simp only [Bool.false_eq_true, if_false]
      unfold avInit
      rw [hend]
      rfl
    · have hend := adPos_end (h := aggnL57Hdr c b t d dc dp (C, sR)) (k := 0) none
        (by rw [hnil]; exact le_rfl)
      simp only [if_true]
      unfold adInit
      rw [hend]
      rfl
  show aggnL57Child c b t d dc dp ((C, none), jR, (sR, none)) = none
  unfold aggnL57Child
  rw [aggnL57_agg_done hpost jR, Option.elim_none]
  unfold aggnL57AlignChild
  dsimp only
  rw [Option.elim_none]
  split_ifs
  · change (l57Child (aggnL57Hdr c b t d dc dp (C, sR),
      l57Init (aggnL57Hdr c b t d dc dp (C, sR)))).map _ = none
    rw [hinit]
    rfl
  · rfl

/-- §15, lines 5–7, **the exits with no versions on the RAM**: when the tag the round
computes after the two phases is not an Align tag, stretch 3 makes no call and the round
matches the two phases followed by the answer `∅`. -/
theorem aggnL57_nil_match (hok : AggnPhasesOK c dc dp)
    (hI : (aggnL57Round c b t d dc dp).WF (C, none)) (hC : AggnPhaseCtxWF c n m C ϕ)
    (hset : LocalCertSetting (decGroup n C.1.1.2) ϕ)
    (ht : LargeK C.2.2.2.length (Nat.card (Fin n))) (htm : 10 * C.2.2.2.length ≤ m)
    (hx : RawStr.WF n (2 * n) C.2.1) (hy : RawStr.WF n (2 * n) C.2.2.1)
    (htag : ∀ s, AggnL57Post c dc dp C ϕ s →
      (aggnContinuation c b t d (C, s)).1 ≠ 1 ∧ (aggnContinuation c b t d (C, s)).1 ≠ 3 ∧
        (aggnContinuation c b t d (C, s)).1 ≠ 4) :
    LoopMatch (aggnL57Round c b t d dc dp) (aggnPhaseDecode n) (decCoset n) (C, none)
      ((aggnL57Round c b t d dc dp).width (C, none)) 0
      ((aggnL57Round c b t d dc dp).init (C, none))
      (aggregateRoundStrong ϕ (decStrN n C.2.1) (decStrN n C.2.2.1)
        (aggnFullEnum ϕ (decStrN n C.2.1) (decStrN n C.2.2.1)
          ((aggnPhaseRows c C).map (winSet m))) (.done ∅)) := by
  set M := aggnL57Round c b t d dc dp with hM
  have h1 := aggnL57_stretch1 (b := b) (t := t) (d := d) hok hI hC hset ht htm hx hy
  have he : (aggregateRoundStrong ϕ (decStrN n C.2.1) (decStrN n C.2.2.1)
      (aggnFullEnum ϕ (decStrN n C.2.1) (decStrN n C.2.2.1) ((aggnPhaseRows c C).map (winSet m)))
      (.done ())).bind (fun _ => (.done ∅ : SIReduction (Fin n) ℕ (Set (Perm (Fin n))))) =
      aggregateRoundStrong ϕ (decStrN n C.2.1) (decStrN n C.2.2.1)
      (aggnFullEnum ϕ (decStrN n C.2.1) (decStrN n C.2.2.1) ((aggnPhaseRows c C).map (winSet m)))
      (.done ∅) := by
    simp only [aggregateRoundStrong, SIReduction.bind_assoc]
    rfl
  rw [← he]
  refine loopMatch_of_phaseMatch
    (P := fun B j v => M.child ((C, none), j, v) = none ∧ decCoset n (M.finish ((C, none), v)) = B)
    (c := aggnAggregateWidth c C + 0)
    (phaseMatch_bind h1 ?_) (fun B j v hv => hv) (Nat.add_le_add_left (Nat.zero_le _) _)
  rintro u jR ⟨sR, o⟩ ⟨-, ho, hpost⟩
  dsimp only at ho hpost
  subst ho
  exact aggnL57_nil_stretch3 htag hpost jR

/-- §15, lines 5–7, **the reject exit of outcome (2b) on the RAM**, for the round of lines
5–7: under the test of `Babai.Line57Data.rejectCase` (tag `0`), the round matches the Master's
reduction of that exit. -/
theorem aggnL57_rejectCase_match (hok : AggnPhasesOK c dc dp)
    (hI : (aggnL57Round c b t d dc dp).WF (C, none)) (hC : AggnPhaseCtxWF c n m C ϕ)
    (hset : LocalCertSetting (decGroup n C.1.1.2) ϕ)
    (ht : LargeK C.2.2.2.length (Nat.card (Fin n))) (htm : 10 * C.2.2.2.length ≤ m)
    (hx : RawStr.WF n (2 * n) C.2.1) (hy : RawStr.WF n (2 * n) C.2.2.1)
    (hcx : Case2 (bigFGamma ϕ (decStrN n C.2.1) C.2.2.2.length) ∧
      ¬ AggregateCase2a ϕ (decStrN n C.2.1) C.2.2.2.length)
    (hcy : ¬ (Case2 (bigFGamma ϕ (decStrN n C.2.2.1) C.2.2.2.length) ∧
      ¬ AggregateCase2a ϕ (decStrN n C.2.2.1) C.2.2.2.length))
    (htag : ∀ s, AggnL57Post c dc dp C ϕ s → (aggnContinuation c b t d (C, s)).1 = 0) :
    LoopMatch (aggnL57Round c b t d dc dp) (aggnPhaseDecode n) (decCoset n) (C, none)
      ((aggnL57Round c b t d dc dp).width (C, none)) 0
      ((aggnL57Round c b t d dc dp).init (C, none))
      ((Line57Shape.rejectCase (ϕ := ϕ) (ts := C.2.2.2.length) hcx hcy).red
        (aggnFullEnum ϕ (decStrN n C.2.1) (decStrN n C.2.2.1)
          ((aggnPhaseRows c C).map (winSet m)))) :=
  aggnL57_nil_match hok hI hC hset ht htm hx hy (fun s hs => by
    have := htag s hs
    omega)

/-- §15, lines 5–7, **the reject exit of outcome (3) on the RAM**, for the round of lines
5–7: under the test of `Babai.Line57Data.rejectDefect` (tag `5`), the round matches the
Master's reduction of that exit. -/
theorem aggnL57_rejectDefect_match (hok : AggnPhasesOK c dc dp)
    (hI : (aggnL57Round c b t d dc dp).WF (C, none)) (hC : AggnPhaseCtxWF c n m C ϕ)
    (hset : LocalCertSetting (decGroup n C.1.1.2) ϕ)
    (ht : LargeK C.2.2.2.length (Nat.card (Fin n))) (htm : 10 * C.2.2.2.length ≤ m)
    (hx : RawStr.WF n (2 * n) C.2.1) (hy : RawStr.WF n (2 * n) C.2.2.1)
    (hne : (fixedGamma ϕ (decStrN n C.2.2.1) C.2.2.2.length).ncard ≠
      (fixedGamma ϕ (decStrN n C.2.1) C.2.2.2.length).ncard)
    (htag : ∀ s, AggnL57Post c dc dp C ϕ s → (aggnContinuation c b t d (C, s)).1 = 5) :
    LoopMatch (aggnL57Round c b t d dc dp) (aggnPhaseDecode n) (decCoset n) (C, none)
      ((aggnL57Round c b t d dc dp).width (C, none)) 0
      ((aggnL57Round c b t d dc dp).init (C, none))
      ((Line57Shape.rejectDefect (ϕ := ϕ) (ts := C.2.2.2.length) hne).red
        (aggnFullEnum ϕ (decStrN n C.2.1) (decStrN n C.2.2.1)
          ((aggnPhaseRows c C).map (winSet m)))) :=
  aggnL57_nil_match hok hI hC hset ht htm hx hy (fun s hs => by
    have := htag s hs
    omega)

end Match

end Algo
