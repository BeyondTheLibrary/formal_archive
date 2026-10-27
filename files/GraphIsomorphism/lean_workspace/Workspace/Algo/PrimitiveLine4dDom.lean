/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 15, line 4d on the RAM when line 6 of Procedure Align finds a dominant color class:
lines 7–11 of Procedure Align (§14.1, as repaired in the corrected paper) as the carrier `GD` of
`Algo.masterNodeFullOps`.
-/
import Workspace.Algo.TopMasterL57Calls
import Workspace.Algo.AlignDescentFacts
import Workspace.Algo.AlignDomLargeMatch

/-!
# Section 15, line 4d with a dominant color class

> 4d. apply Procedure Align to `X` (Sec. 14.1)

`Workspace/Algo/PrimitiveLine4dCarrier.lean` runs line 4d when line 6 of Procedure Align finds
no dominant color class. When it finds one, lines 7–11 of Procedure Align (as repaired in
the corrected paper) replace the call on the dominant window by a round that depends on `m* = |Γ*|`:

* case 1 (`m*` small): the strong descent to `ker ϕ*` over the cosets of `ker ϕ*` covering the
  transporter, then the Chain Rule over the other color classes (`Algo.adChild`,
  `Algo.adCombine`, `Workspace/Algo/AlignDescentLoop.lean`);
* cases 2 and 3 (`m*` large): the Chain Rule of Eq. (71) over the orbits of `G*` in the
  dominant window, then over the other classes (`Algo.alignL57Windows`).

The round of lines 5–7 already runs both (stretch 3 of `Algo.aggnL57Round`: `Algo.l57Child`,
`Algo.l57Step`, `Algo.l57Init`, `Algo.l57Calls`). This file runs the same steps at line 4d:

* `Algo.line4dDomHdr` is the header of line 4d (`Algo.line4dHdr`) with the windows of
  `Algo.alignL57Windows`; without the test of the repair these are the windows of
  `Algo.line4dHdr`;
* `Algo.line4dDomOps` is the carrier: every call is lifted to the node's domain and its
  answer restricted back to the window, and the answer is lifted and shifted by the node's
  representative (Eq. (59)), as `Algo.line4dOps` does;
* `Algo.line4dDomOps_cost` is its local cost data (`Algo.MasterOpsCost`);
* `Algo.line4dDomOps_match_small` (case 1) and `Algo.line4dDomOps_match_large` (cases 2 and 3)
  say that at a node of route `4` the carrier walks the lift of the Master's round
  `Babai.AlignShape.red` of a `Babai.Line4cdData` call for call;
* `Algo.masterNodeFull_line4cd_dom_match_small` and `_large` say the same of the node carrier
  `Algo.masterNodeFullOps` with `GD = Algo.line4dDomOps` at a node where line 6 finds a
  dominant class.

**What the match assumes.** As for lines 5–7 (`Algo.aggnL57_align_match`,
`Algo.aggnL57_align_match_small`), the Master side chooses the dominant data `D` existentially
and does not compute `m*`, `ker ϕ*` or the orbit and coset lists, so the match takes the
description of the Master's shape by the machine's header as a hypothesis
(`Algo.ADDescribes` in case 1, `Algo.AVDescribes` in cases 2 and 3; `Algo.ADDescribes.mk'`
and `Algo.avDescribes_of_domLarge` build them from the fields that involve the Master's
choices).

**Hinted calls.** The node carrier asks each child to have a smaller window than the node
(`Algo.masterAdmittedRound_checked_match`), and the children of this carrier carry no hint
(`Algo.masterCheckedCall`). In case 1 no call of the round carries a hint
(`Babai.AlignDominantRoundData.HasHint` needs `D.LargeParam`), so Eq. (72) gives every call at
most `4|Δ|/5` points. In case 3 the call on a dominant orbit of `G*` carries the Johnson hint
of line 11 and may have the whole window; a child with that hint is not built on the RAM yet
(it needs the action of `G*` on `Γ*`). So the match in cases 2 and 3 assumes that the round
attaches no hint, as the lifted round of lines 5–7 does (`Algo.line57NoDom`).
-/

set_option synthInstance.maxSize 4096

namespace Algo
open RAM RAM.Targets Babai Equiv
open scoped Pointwise

private theorem pfst {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {f : α → β × γ}
    (h : PolyFun f) : PolyFun (fun a => (f a).1) := h.comp polyFun_fst
private theorem psnd {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {f : α → β × γ}
    (h : PolyFun f) : PolyFun (fun a => (f a).2) := h.comp polyFun_snd

/-! ## The header -/

section Header

variable (c tt dd : ℕ)

/-- **Line 4d with the windows of lines 7–11**: the header of `Algo.line4dHdr`, with the
dominant window replaced by the orbits of `G*` in it when the test of the repair holds
(`Algo.alignL57Windows`). -/
def line4dDomHdr (p : MasterHintInput) : AVHdr :=
  ((masterHintTop p).1, line4dFixed c tt dd p, line4dYs c tt dd p,
    alignL57Windows ((masterHintTop p).1, line4dFixed c tt dd p),
    (masterHintTop p).2.1, (masterHintTop p).2.2)

/-- Without the test of the repair (no dominant class, or case 1) the windows are those of
lines 5 and 6. -/
theorem line4dDomHdr_eq_of_not_large (p : MasterHintInput)
    (h : alignRLarge ((masterHintTop p).1, line4dFixed c tt dd p) = false) :
    line4dDomHdr c tt dd p = line4dHdr c tt dd p := by
  unfold line4dDomHdr line4dHdr
  rw [alignL57Windows_of_not h]
  rfl

theorem quasiFun_line4dDomHdr : QuasiFun (line4dDomHdr c tt dd) := by
  have hT := polyFun_masterHintTop
  have hA : PolyFun (fun p : MasterHintInput => (masterHintTop p).1) := hT.comp polyFun_fst
  have hW : QuasiFun (fun p : MasterHintInput =>
      alignL57Windows ((masterHintTop p).1, line4dFixed c tt dd p)) :=
    (hA.quasiFun.pair (quasiFun_line4dFixed c tt dd)).comp_poly polyFun_alignL57Windows
  exact (hA.quasiFun.pair ((quasiFun_line4dFixed c tt dd).pair ((quasiFun_line4dYs c tt dd).pair
    (hW.pair ((hT.comp (polyFun_snd.comp polyFun_fst)).quasiFun.pair
      (hT.comp (polyFun_snd.comp polyFun_snd)).quasiFun))))).of_eq (fun _ => rfl)

end Header

/-! ## Stretch 3 on the window -/

/-- The steps of lines 5–11 of Procedure Align on the window of the node, as a round (the
steps of stretch 3 of `Algo.aggnL57Round`). A device of the proofs only (`WF` is `False`). -/
def line4dDomInnerRound : Round Line4dInnerNode ADState RawCoset where
  WF _ := False
  ground _ := 0
  measure _ := 0
  width I := l57Calls I.1
  child z := z.1.2.elim
    (if z.2.1 < l57Calls z.1.1 then (l57Child (z.1.1, z.2.2)).map (fun J => (z.1.1, some J))
      else none) (fun _ => none)
  init I := l57Init I.1
  combine z := l57Step (z.1.1, z.2.2.1, z.2.2.2)
  finish z := z.2.1.2.2.2
  bot := none
  child_eq_none := by
    rintro ⟨h, _ | J⟩ j s hj
    · exact if_neg (Nat.not_lt.2 hj)
    · rfl
  child_wf := by
    intro _ _ _ _ h
    exact h.elim
  child_measure := by
    intro _ _ _ _ h
    exact h.elim
  child_ground := by
    intro _ _ _ _ h
    exact h.elim

section Inner

variable {n : ℕ} {h : AVHdr}
  {S : AlignShape (Fin n) ℕ (decGroup n h.1.1.2) (decStrN n h.2.2.2.2.1)
    (decStrN n h.2.2.2.2.2)}

/-- §14.1, lines 7–11, **case 1 on the window**: when the header describes `S`
with the dominant class `D` and `m*` small, the steps of stretch 3 walk `S.red` call for call
within `l57Calls h` calls, and the accumulator decodes to the answer of `S.red`. -/
theorem line4dDomInner_loopMatch_small {D : AlignDominantRoundData (Fin n)}
    (hD : ADDescribes n h S D) (hs : l57Small h = true) (hx : h.2.2.2.2.1.length = n) :
    LoopMatch line4dDomInnerRound (line4dInnerDecode n) (decCoset n) (h, none) (l57Calls h) 0
      (l57Init h) S.red := by
  have hcalls : l57Calls h = adCalls h := by unfold l57Calls; rw [hs]; rfl
  have hinit : l57Init h = adInit h := by unfold l57Init; rw [hs]; rfl
  have hl57child : ∀ st, l57Child (h, st) = adChild (h, st) := by
    intro st; unfold l57Child; rw [hs]; rfl
  have hl57step : ∀ st a, l57Step (h, st, a) = adCombine (h, st, a) := by
    intro st a; unfold l57Step; rw [hs]; rfl
  let Good : ℕ → ADState → Prop := fun j s => j + adRem (h, s) ≤ adCalls h
  have hchild : ∀ j s J, Good j s → adChild (h, id s) = some J →
      line4dDomInnerRound.child ((h, none), j, s) = some (h, some J) := by
    intro j s J hg hav
    have h1 := adRem_pos hav
    have hj : j < l57Calls h := by
      rw [hcalls]; simp only [Good, id] at hg h1; omega
    show (if j < l57Calls h then (l57Child (h, s)).map (fun J => (h, some J)) else none) =
      some (h, some J)
    rw [if_pos hj, hl57child, show adChild (h, s) = some J from hav]
    rfl
  have hcomb : ∀ j s a J, Good j s → adChild (h, id s) = some J →
      id (line4dDomInnerRound.combine ((h, none), j, s, a)) = adCombine (h, id s, a) ∧
        Good (j + 1) (line4dDomInnerRound.combine ((h, none), j, s, a)) := by
    intro j s a J hg hav
    have hc : line4dDomInnerRound.combine ((h, none), j, s, a) = adCombine (h, s, a) :=
      hl57step s a
    rw [hc]
    refine ⟨rfl, ?_⟩
    have h1 := adRem_combine hav a
    show j + 1 + adRem (h, adCombine (h, s, a)) ≤ adCalls h
    simp only [Good, id] at hg h1
    omega
  have hstart : Good 0 (l57Init h) := by
    have h1 := adRem_init (h := h)
    show 0 + adRem (h, l57Init h) ≤ adCalls h
    rw [hinit]
    omega
  have hmain := phaseMatch_adShape (R := line4dDomInnerRound) (decI := line4dInnerDecode n)
    (I := ((h, none) : Line4dInnerNode)) (h := h) (pr := id) (emb := fun J => (h, some J))
    (Good := Good) hD (fun _ _ _ => rfl) hchild hcomb hx 0 (l57Init h) hinit hstart
  refine loopMatch_of_phaseMatch hmain ?_ (le_of_eq hcalls.symm)
  rintro b j' s' ⟨-, a, hs', ha⟩
  simp only [id] at hs'
  subst hs'
  refine ⟨?_, ha⟩
  show (if j' < l57Calls h then (l57Child (h, ((h.2.2.1.length, 0, none, a), (0, none)))).map
    (fun J => (h, some J)) else none) = none
  split_ifs
  · rw [hl57child]; rfl
  · rfl

/-- §14.1, lines 5–11, **cases 2 and 3 on the window** (and line 6 with no dominant class):
when line 6's test of case 1 fails and the header describes `S` with the windows `Ws`, the
steps of stretch 3 walk `S.red` call for call within `l57Calls h` calls, and the accumulator
decodes to the answer of `S.red`. -/
theorem line4dDomInner_loopMatch_large {Ws : List (Set (Fin n))}
    (hD : AVDescribes n h S Ws) (hs : l57Small h = false) (hx : h.2.2.2.2.1.length = n) :
    LoopMatch line4dDomInnerRound (line4dInnerDecode n) (decCoset n) (h, none) (l57Calls h) 0
      (l57Init h) S.red := by
  have hcalls : l57Calls h = avCalls h := by unfold l57Calls; rw [hs]; rfl
  have hinit : l57Init h = (avInit h, 0, none) := by unfold l57Init; rw [hs]; rfl
  have hl57child : ∀ st, l57Child (h, st) = avChild (h, st.1) := by
    intro st; unfold l57Child; rw [hs]; rfl
  have hl57step : ∀ st a, l57Step (h, st, a) = (avCombine (h, st.1, a), 0, none) := by
    intro st a; unfold l57Step; rw [hs]; rfl
  let pr : ADState → AVState := fun s => s.1
  let Good : ℕ → ADState → Prop := fun j s => j + avRem (h, s.1) ≤ avCalls h
  have hchild : ∀ j s J, Good j s → avChild (h, pr s) = some J →
      line4dDomInnerRound.child ((h, none), j, s) = some (h, some J) := by
    intro j s J hg hav
    have h1 := avRem_pos hav
    have hj : j < l57Calls h := by
      rw [hcalls]; simp only [Good, pr] at hg h1; omega
    show (if j < l57Calls h then (l57Child (h, s)).map (fun J => (h, some J)) else none) =
      some (h, some J)
    rw [if_pos hj, hl57child, show avChild (h, s.1) = some J from hav]
    rfl
  have hcomb : ∀ j s a J, Good j s → avChild (h, pr s) = some J →
      pr (line4dDomInnerRound.combine ((h, none), j, s, a)) = avCombine (h, pr s, a) ∧
        Good (j + 1) (line4dDomInnerRound.combine ((h, none), j, s, a)) := by
    intro j s a J hg hav
    have hc : line4dDomInnerRound.combine ((h, none), j, s, a) =
        (avCombine (h, s.1, a), 0, none) := hl57step s a
    rw [hc]
    refine ⟨rfl, ?_⟩
    have h1 := avRem_combine hav a
    show j + 1 + avRem (h, avCombine (h, s.1, a)) ≤ avCalls h
    simp only [Good, pr] at hg h1
    omega
  have hstart : Good 0 (l57Init h) := by
    have h1 := avRem_init h
    show 0 + avRem (h, (l57Init h).1) ≤ avCalls h
    rw [hinit]
    show 0 + avRem (h, avInit h) ≤ avCalls h
    omega
  have hmain := phaseMatch_alignShape_value_of (R := line4dDomInnerRound)
    (decI := line4dInnerDecode n) (I := ((h, none) : Line4dInnerNode)) (h := h) (pr := pr)
    (emb := fun J => (h, some J)) (Good := Good) S Ws hD.red (fun _ _ _ => rfl) hchild hcomb
    hD.action hD.giant hD.cat hD.fixed hD.versions hD.windows hD.nonempty hx hD.lt hD.inv hD.run
    0 (l57Init h) (show (l57Init h).1 = avInit h by rw [hinit]) hstart
  have hlenV : h.2.2.1.length = S.versions.length := by
    simpa only [List.length_map] using congrArg List.length hD.versions
  refine loopMatch_of_phaseMatch hmain ?_ (by rw [hcalls, avCalls, hlenV])
  rintro b j' ⟨st, r, racc⟩ ⟨-, a, hs', ha⟩
  simp only [pr] at hs'
  subst hs'
  refine ⟨?_, ha⟩
  show (if j' < l57Calls h then (l57Child (h, ((h.2.2.1.length, 0, none, a), r, racc))).map
    (fun J => (h, some J)) else none) = none
  split_ifs
  · rw [hl57child]; rfl
  · rfl

end Inner

/-! ## Stretch 3 on the node -/

section Loop

variable (c tt dd : ℕ)

/-- Line 4d with a dominant class: the next call of stretch 3, lifted to the node's domain. -/
def line4dDomChild (z : Line4dNode × ℕ × ADState) : Option Line4dNode :=
  z.1.2.elim
    (if z.2.1 < l57Calls (line4dDomHdr c tt dd z.1.1) then
      (l57Child (line4dDomHdr c tt dd z.1.1, z.2.2)).bind fun W =>
        (topwRawInstance (line4dCtx z.1.1, W)).map fun V => (z.1.1, some V)
    else none)
    (fun _ => none)

/-- Line 4d with a dominant class: stretch 3 takes the answer of a lifted call, restricted to
the window. -/
def line4dDomCombine (z : MasterHintInput × ℕ × ADState × RawCoset) : ADState :=
  l57Step (line4dDomHdr c tt dd z.1, z.2.2.1,
    topwCosetImage (z.1.1.2.2.2.1, z.1.1.1, z.2.2.2))

/-- Stretch 3 lifted to the node, as a round. A device of the proofs only (`WF` is `False`):
the carrier `Algo.line4dDomOps` runs these steps. -/
def line4dDomRound : Round Line4dNode ADState RawCoset where
  WF _ := False
  ground _ := 0
  measure _ := 0
  width I := I.2.elim (l57Calls (line4dDomHdr c tt dd I.1)) (fun _ => 0)
  child := line4dDomChild c tt dd
  init I := l57Init (line4dDomHdr c tt dd I.1)
  combine z := line4dDomCombine c tt dd (z.1.1, z.2)
  finish z := line4dFinish (z.1.1, z.2.1)
  bot := none
  child_eq_none := by
    rintro ⟨q, _ | W⟩ j s hj
    · exact if_neg (Nat.not_lt.2 hj)
    · rfl
  child_wf := by
    intro _ _ _ _ h
    exact h.elim
  child_measure := by
    intro _ _ _ _ h
    exact h.elim
  child_ground := by
    intro _ _ _ _ h
    exact h.elim

/-- **Stretch 3 lifted walks the lift of stretch 3 on the window** (as
`Algo.line4dRound_lift` for the loop of Eq. (71)). -/
theorem line4dDomRound_lift {n : ℕ} {q : MasterHintInput} {gens : List (Perm (Fin n))}
    (hg : q.1.2.1 = gens.map (encPerm n)) (hd : q.1.2.2.2.1.length = n)
    (hnd : q.1.1.Nodup) (hlt : ∀ i ∈ q.1.1, i < n)
    (hinv : IsInvariant (genGroup gens) (winSet n q.1.1)) :
    ∀ {w j : ℕ} {s : ADState}
      {T : SIReduction (Fin q.1.1.length) ℕ (Set (Perm (Fin q.1.1.length)))},
      LoopMatch line4dDomInnerRound (line4dInnerDecode q.1.1.length) (decCoset q.1.1.length)
        (line4dDomHdr c tt dd q, none) w j s T →
      (∀ J ∈ T.calls, J.K ⊆ ((winRestrictHom n q.1.1 hnd hlt (genGroup gens) hinv).range :
        Set (Perm (Fin q.1.1.length)))) →
      T.run ⊆ ((winRestrictHom n q.1.1 hnd hlt (genGroup gens) hinv).range :
        Set (Perm (Fin q.1.1.length))) →
      LoopMatch (line4dDomRound c tt dd) (line4dDecode n) (decCoset n) (q, none) w j s
        ((top4wTree q.1.1 hnd hlt (genGroup gens) hinv (decStrN n q.1.2.2.2.1) T).bind
          (fun A => .done (decPerm n q.1.2.2.1 • A))) := by
  have hctx : line4dCtx q = (((q.1.2.2.2.1, gens.map (encPerm n)), q.1.1, q.1.2.2.2.1) :
      TopwContext) := by
    rw [line4dCtx, hg]
  intro w j s T h
  induction h with
  | done w j s A hc ha =>
    intro _ hA
    refine .done w j s _ ?_ ?_
    · change line4dDomChild c tt dd ((q, none), j, s) = none
      change (if j < l57Calls (line4dDomHdr c tt dd q) then
        (l57Child (line4dDomHdr c tt dd q, s)).map (fun J => (line4dDomHdr c tt dd q, some J))
        else none) = none at hc
      change (if j < l57Calls (line4dDomHdr c tt dd q) then _ else none) = none
      split_ifs at hc ⊢ with hj
      · rw [Option.map_eq_none_iff] at hc
        rw [hc]
        rfl
      · rfl
    · change decCoset q.1.1.length s.1.2.2.2 = A at ha
      change decCoset n (top3Shift (q.1.2.2.2.1, normPerm (q.1.2.2.2.1, q.1.2.2.1),
        top2NormC q.1.2.2.2.1 (topwCosetPreimage ((q.1.2.2.2.1, q.1.2.1), q.1.1, s.1.2.2.2)))) = _
      rw [decCoset_top3Shift hd, decPerm_normPerm hd, decCoset_top2NormC hd, hg,
        topwCosetPreimage_spec hd hnd hlt hinv _ (ha.symm ▸ hA), ha]
  | call w j s J k hc hn ih =>
    intro hT hR
    have hJ := hT (line4dInnerDecode q.1.1.length J) (by simp [SIReduction.calls])
    change (if j < l57Calls (line4dDomHdr c tt dd q) then
      (l57Child (line4dDomHdr c tt dd q, s)).map (fun J => (line4dDomHdr c tt dd q, some J))
      else none) = some J at hc
    split_ifs at hc with hj
    obtain ⟨W, hW, rfl⟩ := Option.map_eq_some_iff.mp hc
    obtain ⟨V, hV, hdec⟩ := topwRawInstance_spec hd hd hnd hlt hinv W hJ
    have hchild : line4dDomChild c tt dd ((q, none), j, s) = some (q, some V) := by
      change (if j < l57Calls (line4dDomHdr c tt dd q) then
        (l57Child (line4dDomHdr c tt dd q, s)).bind (fun W =>
          (topwRawInstance (line4dCtx q, W)).map fun V => (q, some V)) else none) = _
      rw [if_pos hj, hW, Option.bind_some, hctx, hV]
      rfl
    have hDV : line4dDecode n (q, some V) =
        topwInstance q.1.1 hnd hlt (genGroup gens) hinv (decStrN n q.1.2.2.2.1)
          (line4dInnerDecode q.1.1.length (line4dDomHdr c tt dd q, some W)) := hdec
    change LoopMatch _ _ _ _ (w + 1) j s (.call
      (topwInstance q.1.1 hnd hlt (genGroup gens) hinv (decStrN n q.1.2.2.2.1)
        (line4dInnerDecode q.1.1.length (line4dDomHdr c tt dd q, some W))) _)
    rw [← hDV]
    refine .call w j s (q, some V) _ hchild ?_
    intro z hz
    have hzsub : decCoset n z ⊆ (genGroup gens : Set (Perm (Fin n))) := by
      rw [hz, hDV, topwInstance_answer]
      rintro g ⟨hg, _⟩
      exact hg
    have hanswer : decCoset q.1.1.length (topwCosetImage (q.1.2.2.2.1, q.1.1, z)) =
        (line4dInnerDecode q.1.1.length (line4dDomHdr c tt dd q, some W)).answer := by
      rw [topwCosetImage_spec hd hnd hlt hinv z hzsub, hz, hDV,
        topwImage_answer hnd hlt hinv (decStrN n q.1.2.2.2.1) _ hJ]
    have htail := ih (topwCosetImage (q.1.2.2.2.1, q.1.1, z)) hanswer
      (fun J' hJ' => hT J' (by simp [SIReduction.calls, hJ'])) hR
    change LoopMatch _ _ _ _ w (j + 1)
      (l57Step (line4dDomHdr c tt dd q, s, topwCosetImage (q.1.2.2.2.1, q.1.1, z)))
      ((top4wTree q.1.1 hnd hlt (genGroup gens) hinv (decStrN n q.1.2.2.2.1)
        (k (topwImageSet q.1.1 hnd hlt (genGroup gens) hinv
          (line4dDecode n (q, some V)).answer))).bind
        (fun A => .done (decPerm n q.1.2.2.1 • A)))
    rw [hDV, topwImage_answer hnd hlt hinv (decStrN n q.1.2.2.2.1) _ hJ]
    exact htail

end Loop

/-! ## The carrier -/

section Carrier

variable (c tt dd : ℕ)

/-- **Section 15, line 4d with a dominant color class: the carrier `GD` of the Master's
node.** It runs lines 5–11 of Procedure Align (stretch 3 of the round of lines 5–7) on the
versions line 4c found, with every call lifted to the node's domain. -/
def line4dDomOps : MasterOps ADState where
  width p := l57Calls (line4dDomHdr c tt dd (line4dHint p))
  child z := (line4dDomChild c tt dd ((line4dHint z.1, none), z.2)).map
    (fun J => masterCheckedCall (z.1.1.2.2.2.1, line4dNodeRead J))
  init p := l57Init (line4dDomHdr c tt dd (line4dHint p))
  combine z := line4dDomCombine c tt dd (line4dHint z.1, z.2)
  finish z := line4dFinish (line4dHint z.1, z.2.1)

/-! ### Running time -/

theorem quasiFun_line4dDomHdrAt :
    QuasiFun (fun p : RawMasterSI => line4dDomHdr c tt dd (line4dHint p)) :=
  polyFun_line4dHint.comp_quasiFun (quasiFun_line4dDomHdr c tt dd)

/-- The child of the carrier, once the header, the call bound and the next call on the window
are computed. -/
def line4dDomPost (u : (AVHdr × (RawMasterSI × ℕ × ADState)) × ℕ × Option RawWinSI) :
    Option RawMasterSI :=
  if u.1.2.2.1 < u.2.1 then
    (u.2.2.bind fun W => topwRawInstance (line4dCtx (line4dHint u.1.2.1), W)).map
      fun V => masterCheckedCall (u.1.2.1.1.2.2.2.1, V)
  else none

theorem polyFun_line4dDomPost : PolyFun line4dDomPost := by
  let Z := (AVHdr × (RawMasterSI × ℕ × ADState)) × ℕ × Option RawWinSI
  have z : PolyFun (fun u : Z => u) := polyFun_id
  have hp := pfst (psnd (pfst z))
  have hj := pfst (psnd (psnd (pfst z)))
  have hK := pfst (psnd z)
  have ho := psnd (psnd z)
  have hlt : PolyFun (fun u : Z => decide (u.1.2.2.1 < u.2.1)) :=
    (hj.add (polyFun_const 1)).le hK
  have hctx : PolyFun (fun u : Z => line4dCtx (line4dHint u.1.2.1)) :=
    (hp.comp polyFun_line4dHint).comp polyFun_line4dCtx
  have hx : PolyFun (fun u : Z => u.1.2.1.1.2.2.2.1) := pfst (psnd (psnd (psnd (pfst hp))))
  have hlift : PolyFun (fun v : RawWinSI × Z =>
      topwRawInstance (line4dCtx (line4dHint v.2.1.2.1), v.1)) :=
    (((psnd polyFun_id).comp hctx).pair polyFun_fst).comp polyFun_topwRawInstance
  have hbind : PolyFun (fun u : Z =>
      u.2.2.bind fun W => topwRawInstance (line4dCtx (line4dHint u.1.2.1), W)) :=
    ((ho.pair z).comp (PolyFun.optionElim (polyFun_const none) hlift)).of_eq (fun u => by
      cases u.2.2 <;> rfl)
  have hmk : PolyFun (fun v : RawWinSI × Z =>
      some (masterCheckedCall (v.2.1.2.1.1.2.2.2.1, v.1))) :=
    (((psnd polyFun_id).comp hx).pair polyFun_fst).comp polyFun_masterCheckedCall |>.comp
      polyFun_some
  have hmap : PolyFun (fun u : Z => (u.2.2.bind fun W =>
      topwRawInstance (line4dCtx (line4dHint u.1.2.1), W)).map
        fun V => masterCheckedCall (u.1.2.1.1.2.2.2.1, V)) :=
    ((hbind.pair z).comp (PolyFun.optionElim (polyFun_const none) hmk)).of_eq (fun u => by
      cases (u.2.2.bind fun W => topwRawInstance (line4dCtx (line4dHint u.1.2.1), W)) <;> rfl)
  exact (PolyFun.ite hlt hmap (polyFun_const none)).of_eq (fun u => by
    unfold line4dDomPost
    by_cases h : u.1.2.2.1 < u.2.1 <;> simp [h])

theorem line4dDomOps_child_eq (z : RawMasterSI × ℕ × ADState) :
    (line4dDomOps c tt dd).child z =
      line4dDomPost ((line4dDomHdr c tt dd (line4dHint z.1), z),
        l57Calls (line4dDomHdr c tt dd (line4dHint z.1)),
        l57Child (line4dDomHdr c tt dd (line4dHint z.1), z.2.2)) := by
  change (line4dDomChild c tt dd ((line4dHint z.1, none), z.2)).map _ = _
  unfold line4dDomPost
  change (if z.2.1 < l57Calls (line4dDomHdr c tt dd (line4dHint z.1)) then _ else none).map _ = _
  split_ifs
  · cases (l57Child (line4dDomHdr c tt dd (line4dHint z.1), z.2.2)) with
    | none => rfl
    | some W =>
      simp only [Option.bind_some]
      cases topwRawInstance (line4dCtx (line4dHint z.1), W) <;> rfl
  · rfl

theorem quasiFun_line4dDomOps_child : QuasiFun (line4dDomOps c tt dd).child := by
  have hH : QuasiFun (fun z : RawMasterSI × ℕ × ADState => line4dDomHdr c tt dd (line4dHint z.1)) :=
    polyFun_fst.quasiFun.comp (quasiFun_line4dDomHdrAt c tt dd)
  have hK := hH.comp quasiFun_l57Calls
  have hC := (hH.pair (psnd (psnd polyFun_id)).quasiFun).comp quasiFun_l57Child
  exact (((hH.pair quasiFun_id).pair (hK.pair hC)).comp_poly polyFun_line4dDomPost).of_eq
    (fun z => (line4dDomOps_child_eq c tt dd z).symm)

theorem quasiFun_line4dDomOps_combine : QuasiFun (line4dDomOps c tt dd).combine := by
  have i : PolyFun (fun z : RawMasterSI × ℕ × ADState × RawCoset => z) := polyFun_id
  have hq := pfst i
  have himg : PolyFun (fun z : RawMasterSI × ℕ × ADState × RawCoset =>
      topwCosetImage (z.1.1.2.2.2.1, z.1.1.1, z.2.2.2)) :=
    ((pfst (psnd (psnd (psnd (pfst hq))))).pair ((pfst (pfst hq)).pair
      (psnd (psnd (psnd i))))).comp polyFun_topwCosetImage
  exact (((pfst i).quasiFun.comp (quasiFun_line4dDomHdrAt c tt dd)).pair
    ((pfst (psnd (psnd i))).pair himg).quasiFun).comp quasiFun_l57Step |>.of_eq
      (fun _ => rfl)

/-- The first state of stretch 3 is no larger than a step's bound. -/
theorem l57Init_size {F : ℕ → ℕ}
    (hF : ∀ (n : ℕ) (h : AVHdr), h.2.2.2.2.1.length ≤ n →
      (∀ k acc, Enc.size (adPos (h, k, acc)) ≤ F (Enc.size h + chainBound n)) ∧
      (∀ st a, Enc.size (adCombine (h, st, a)) ≤ F (Enc.size h + chainBound n)))
    {n : ℕ} (h : AVHdr) (hx : h.2.2.2.2.1.length ≤ n) :
    Enc.size (l57Init h) ≤
      F (Enc.size h + chainBound n) + 32 * (Enc.size h + chainBound n + 2) + 20 := by
  unfold l57Init
  split_ifs
  · have := (hF n h hx).1 0 none
    unfold adInit
    omega
  · have h1 := avInit_size h hx
    have h2 := Combine.size_pair_le (avInit h) ((0, none) : ℕ × RawCoset)
    have h3 := Combine.size_pair_le (0 : ℕ) (none : RawCoset)
    have h4 : Enc.size (0 : ℕ) = 2 := by rw [Small.size_nat]; rfl
    have h5 : Enc.size (none : RawCoset) = 2 := size_none
    omega

/-- **Section 15, line 4d with a dominant class: the carrier's local cost data.** The state
and the width are bounded by quasipolynomials of the node's degree, fixed before the degree is
given; the answer fits the Master's input cap. -/
theorem line4dDomOps_cost (a b : ℕ) : Nonempty (MasterOpsCost a b (line4dDomOps c tt dd)) := by
  have hH := quasiFun_line4dDomHdrAt c tt dd
  obtain ⟨G, hGq, hGm, hGs⟩ := hH.size.exists_quasiPolyBound
  obtain ⟨F, hFq, hFm, hF⟩ := adStep_size_bdd
  obtain ⟨K, hKq, hKm, hK⟩ := l57Calls_bdd
  let B : ℕ → ℕ := fun n => G (masterInputCap a b n)
  have hBq : QuasiPolyBound B := hGq.comp_poly (polyBound_masterInputCap a b)
  have hBm : Monotone B := fun _ _ h => hGm _ _ (mono_masterInputCap a b h)
  have hhdr : ∀ p, MasterInputWF a b p →
      Enc.size (line4dDomHdr c tt dd (line4dHint p)) ≤ B (masterDegree p) :=
    fun p hp => (hGs p).trans (hGm _ _ hp.1)
  let SB : ℕ → ℕ := fun N => F (N + chainBound N) + 32 * (N + chainBound N + 2) + 20
  have hSBm : Monotone SB := by
    intro x y hxy
    have h1 := mono_chainBound hxy
    have h2 := hFm (Nat.add_le_add hxy h1)
    dsimp only [SB]
    omega
  have hCq : QuasiPolyBound (fun N => N + chainBound N) :=
    polyBound_id.quasiPoly.add polyBound_chainBound.quasiPoly
  have hSBq : QuasiPolyBound SB :=
    ((hFq.comp hCq).add ((polyBound_const 32).quasiPoly.mul
      (hCq.add (polyBound_const 2).quasiPoly))).add (polyBound_const 20).quasiPoly
  have hstate : ∀ p, MasterInputWF a b p → ∀ (st : ADState) (A : RawCoset),
      Enc.size (l57Step (line4dDomHdr c tt dd (line4dHint p), st, A)) ≤ SB (B (masterDegree p)) := by
    intro p hp st A
    set h := line4dDomHdr c tt dd (line4dHint p)
    exact (l57Step_size hF h (length_hdrX_le_size h) st A).trans (hSBm (hhdr p hp))
  refine ⟨{
    stateBound := fun n => SB (B n)
    widthBound := fun n => K (B n)
    quasiPoly_state := hSBq.comp hBq
    mono_state := fun _ _ h => hSBm (hBm h)
    quasiPoly_width := hKq.comp hBq
    quasiFun_width := hH.comp quasiFun_l57Calls
    quasiFun_child := quasiFun_line4dDomOps_child c tt dd
    quasiFun_init := hH.comp quasiFun_l57Init
    quasiFun_combine := quasiFun_line4dDomOps_combine c tt dd
    quasiFun_finish := (((polyFun_fst.comp polyFun_line4dHint).pair
      (pfst polyFun_snd)).comp polyFun_line4dFinish).quasiFun
    init_le := ?_
    combine_le := ?_
    finish_le := ?_
    width_le := ?_ }⟩
  · intro p hp
    set h := line4dDomHdr c tt dd (line4dHint p)
    exact (l57Init_size hF h (length_hdrX_le_size h)).trans (hSBm (hhdr p hp))
  · intro p j s A hp _
    exact hstate p hp s _
  · intro p s _
    have hs := size_top3Shift_le (n := p.1.2.2.2.1.length) rfl le_rfl
      (normPerm (p.1.2.2.2.1, p.1.2.2.1))
      (top2NormC p.1.2.2.2.1 (topwCosetPreimage ((p.1.2.2.2.1, p.1.2.1), p.1.1, s.1.2.2.2)))
    change Enc.size (top3Shift _) ≤ _
    refine hs.trans ?_
    unfold masterInputCap
    change chainBound (masterDegree p) ≤ _
    omega
  · intro p hp
    exact (hK _).trans (hKm (hhdr p hp))

end Carrier

/-! ## The calls of the round with a dominant class -/

section Shape

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- §14.1, lines 7–11, **case 1: every call has the letters of the two strings**: it is a call
of the strong descent or of the Chain Rule on `x` and `y`. -/
theorem alignShape_letters_of_dom_small {k : ℕ} {x y : W → ℕ} {G : Subgroup (Perm W)}
    (S : AlignShape W ℕ G x y) (hn : S.head ∉ S.tail) {D : AlignDominantRoundData W}
    (hD : S.dom = some D) (hL : ¬ D.LargeParam) (hx : ∀ u, x u < k) (hy : ∀ u, y u < k) :
    ∀ J ∈ S.red.calls, MasterCallLetters k J := by
  rw [alignShape_red_of_dom_small S hn hD hL]
  refine SIReduction.mem_calls_unionOver _ (fun Y J hJ => ?_) _
  split at hJ
  · simp at hJ
  · rw [SIReduction.calls_bind, List.mem_append] at hJ
    rcases hJ with hJ | hJ
    · exact masterLetters_strongDescent _ hx hy _ _ J hJ
    · exact masterLetters_cosetChain k x y hx hy _ _ J hJ

/-- §14.1, lines 7–11, **cases 2 and 3: every call has the letters of the two strings**: it
is a call of the Chain Rule of Eq. (71) on `x` and `y`. -/
theorem alignShape_letters_of_dom_large {k : ℕ} {x y : W → ℕ} {G : Subgroup (Perm W)}
    (S : AlignShape W ℕ G x y) (hn : S.head ∉ S.tail) {D : AlignDominantRoundData W}
    (hD : S.dom = some D) (hL : D.LargeParam) (hx : ∀ u, x u < k) (hy : ∀ u, y u < k) :
    ∀ J ∈ S.red.calls, MasterCallLetters k J := by
  rw [alignShape_red_of_dom_large S hn hD hL]
  exact SIReduction.mem_calls_unionOver _
    (fun _ J hJ => masterLetters_cosetChain k x y hx hy _ _ J hJ) _

/-- §14.1, line 11: **in case 1 no call carries a hint** (the hint of line 11 is attached only
when `m*` is large, `Babai.AlignDominantRoundData.HasHint`). -/
theorem alignShape_hint_eq_none_of_dom_small {A : Type*} {G : Subgroup (Perm W)} {x y : W → A}
    (S : AlignShape W A G x y) {D : AlignDominantRoundData W} (hD : S.dom = some D)
    (hL : ¬ D.LargeParam) (J : SIInstance W A) : S.hint J = none := by
  simp only [AlignShape.hint, hD]
  unfold AlignDominantRoundData.hint
  rw [dif_neg (fun h => hL h.1)]

end Shape

/-- §14.1 and Eq. (72): **without a hint, every call of the round has a window of at most
`4n/5` points.** -/
theorem line4cdData_five_mul_windowSize_of_noHint {N : ℕ} {A : Type*}
    {G : Subgroup (Perm (Fin N))} {x y : Fin N → A} {par cost : ℕ}
    (D : Line4cdData (Fin N) A G x y par cost) (h : ∀ J, D.shape.hint J = none) :
    ∀ J ∈ D.shape.red.calls, 5 * J.windowSize ≤ 4 * N := by
  intro J hJ
  rcases D.calls_progress J hJ with hs | hs
  · rwa [Fintype.card_fin] at hs
  · rw [h] at hs
    exact absurd hs (by simp)

/-! ## The carrier walks the Master's round -/

section Match

variable {c tt dd : ℕ} {n m : ℕ} {p : MasterHintInput}
    (hx : RawStr.WF n (2 * n + 1) p.1.2.2.2.1)
    (hy : RawStr.WF n (2 * n + 1) p.1.2.2.2.2)
    (hgs : RawGens.WF n p.1.2.1) (hnd : p.1.1.Nodup) (hlt : ∀ z ∈ p.1.1, z < n)
    (hinv : IsInvariant (decGroup n p.1.2.1) (winSet n p.1.1))
    (hΔ : 0 < p.1.1.length)
    {par cost : ℕ}
    (D : Line4cdData (Fin p.1.1.length) ℕ (decGroup p.1.1.length (masterHintTop p).1.1.2)
      (decStrN p.1.1.length (masterHintTop p).2.1)
      (decStrN p.1.1.length (masterHintTop p).2.2) par cost)

include hx hy hgs hΔ in
/-- The step shared by both cases: a match of stretch 3 on the window, for a round of the
Master with no hint and the letters of the two strings, lifts to the carrier. -/
theorem line4dDomOps_match_of_inner (a b : ℕ)
    (hin : LoopMatch line4dDomInnerRound (line4dInnerDecode p.1.1.length)
      (decCoset p.1.1.length) (line4dDomHdr c tt dd p, none)
      (l57Calls (line4dDomHdr c tt dd p)) 0 (l57Init (line4dDomHdr c tt dd p)) D.shape.red)
    (hnh : ∀ J, D.shape.hint J = none)
    (hlet : ∀ k : ℕ, (∀ u, decStrN p.1.1.length (masterHintTop p).2.1 u < k) →
      (∀ u, decStrN p.1.1.length (masterHintTop p).2.2 u < k) →
      ∀ J ∈ D.shape.red.calls, MasterCallLetters k J) :
    LoopMatch (masterAdmittedRound a b (line4dDomOps c tt dd)) (fun J => decWinSI n J.1)
      (decCoset n) (p.1, some p.2) ((line4dDomOps c tt dd).width (p.1, some p.2)) 0
      ((line4dDomOps c tt dd).init (p.1, some p.2))
      ((top4wTree p.1.1 hnd hlt (decGroup n p.1.2.1) hinv (decStrN n p.1.2.2.2.1)
        D.shape.red).bind (fun A => .done (decPerm n p.1.2.2.1 • A))) := by
  have hgrp := masterLine4b_group hgs hnd hlt hinv
  have hK' : ∀ J ∈ D.shape.red.calls, J.K ⊆
      ((winRestrictHom n p.1.1 hnd hlt (decGroup n p.1.2.1) hinv).range :
        Set (Perm (Fin p.1.1.length))) := by
    rw [← hgrp]
    exact D.calls_K
  have hR : D.shape.red.run ⊆
      ((winRestrictHom n p.1.1 hnd hlt (decGroup n p.1.2.1) hinv).range :
        Set (Perm (Fin p.1.1.length))) := by
    rw [D.run_red, ← hgrp]
    exact fun _ h => h.1
  have hlift := line4dDomRound_lift c tt dd (gens := p.1.2.1.map (decPerm n))
    (map_encPerm_decPerm hgs).symm hx.1 hnd hlt hinv hin hK' hR
  have hwsize : masterWindowSize (p.1, some p.2) ≤ masterDegree (p.1, some p.2) := by
    change p.1.1.length ≤ p.1.2.2.2.1.length
    rw [hx.1]
    exact length_le_of_nodup_lt hnd hlt
  refine masterAdmittedRound_checked_match a b (R := line4dDomRound c tt dd)
    (F := line4dDomOps c tt dd) (I := (p, none)) (p := (p.1, some p.2)) hx.1 hwsize
    line4dNodeRead id (line4dDecode n) (fun _ _ _ _ => rfl) rfl (fun _ _ => rfl) rfl
    (fun _ _ _ => rfl) (fun _ => rfl) hlift ?_
  -- the calls: letters of the node's strings, and windows of at most `4|Δ|/5` points
  have hxx := (masterStrWF_iff hx.1).mp hx
  obtain ⟨hix, hiy⟩ := masterHintTop_letters hx hy hnd hlt (p := p)
  have hlet' := hlet _ hix hiy
  have hwin := line4cdData_five_mul_windowSize_of_noHint D hnh
  have hcos := top4wTree_calls_isCosetInstance hnd hlt hinv (decStrN n p.1.2.2.2.1) D.shape.red
    (by rw [← hgrp]; exact D.calls_coset)
  intro J hJ
  simp only [SIReduction.calls_bind, SIReduction.calls_done, List.append_nil] at hJ
  have hJc := hcos J hJ
  simp only [top4wTree, SIReduction.calls_bind, SIReduction.calls_done, List.append_nil] at hJ
  rw [calls_topwReduction hnd hlt hinv _ _ hK'] at hJ
  obtain ⟨K, hKm, rfl⟩ := List.mem_map.mp hJ
  refine ⟨masterLetters_topwInstance p.1.1 hnd hlt _ hinv _ hxx K (hlet' K hKm), ?_, _, hJc⟩
  rw [topwInstance_windowSize]
  have := hwin K hKm
  change K.windowSize < p.1.1.length
  omega

include hx hy hgs hΔ in
/-- **Section 15, line 4d, case 1 of lines 7–11, on the Master's node.** At a
node where line 6 of Procedure Align finds a dominant color class `Dd` and `m*` is small
(the machine's test `Algo.l57Small`), if the machine's header and lists describe the Master's
round `Babai.AlignShape.red` of `D` (`Algo.ADDescribes`), the carrier `Algo.line4dDomOps`
walks it call for call on the window, read on the node's domain and shifted by the node's
representative (Eq. (59)), exactly as line 4b reads its round. -/
theorem line4dDomOps_match_small (a b : ℕ) {Dd : AlignDominantRoundData (Fin p.1.1.length)}
    (hD : ADDescribes p.1.1.length (line4dDomHdr c tt dd p) D.shape Dd)
    (hs : l57Small (line4dDomHdr c tt dd p) = true) :
    LoopMatch (masterAdmittedRound a b (line4dDomOps c tt dd)) (fun J => decWinSI n J.1)
      (decCoset n) (p.1, some p.2) ((line4dDomOps c tt dd).width (p.1, some p.2)) 0
      ((line4dDomOps c tt dd).init (p.1, some p.2))
      ((top4wTree p.1.1 hnd hlt (decGroup n p.1.2.1) hinv (decStrN n p.1.2.2.2.1)
        D.shape.red).bind (fun A => .done (decPerm n p.1.2.2.1 • A))) := by
  have hxl : (masterHintTop p).2.1.length = p.1.1.length := length_rawRestrictStr _ _
  refine line4dDomOps_match_of_inner hx hy hgs hnd hlt hinv hΔ D a b
    (line4dDomInner_loopMatch_small hD hs hxl)
    (alignShape_hint_eq_none_of_dom_small D.shape hD.dom hD.small) ?_
  intro k hkx hky
  exact alignShape_letters_of_dom_small D.shape D.head_not_mem hD.dom hD.small hkx hky

include hx hy hgs hΔ in
/-- **Section 15, line 4d, cases 2 and 3 of lines 7–11, on the Master's
node.** At a node where line 6 of Procedure Align finds a dominant color class `Dd` with `m*`
large, if the machine's header describes the Master's round `Babai.AlignShape.red` of `D`
(`Algo.AVDescribes`, for instance by `Algo.avDescribes_of_domLarge`) and the round attaches no
hint, the carrier `Algo.line4dDomOps` walks it call for call, as in
`Algo.line4dDomOps_match_small`. -/
theorem line4dDomOps_match_large (a b : ℕ) {Dd : AlignDominantRoundData (Fin p.1.1.length)}
    (hdom : D.shape.dom = some Dd) (hL : Dd.LargeParam) {Ws : List (Set (Fin p.1.1.length))}
    (hD : AVDescribes p.1.1.length (line4dDomHdr c tt dd p) D.shape Ws)
    (hs : l57Small (line4dDomHdr c tt dd p) = false)
    (hnh : ∀ J, D.shape.hint J = none) :
    LoopMatch (masterAdmittedRound a b (line4dDomOps c tt dd)) (fun J => decWinSI n J.1)
      (decCoset n) (p.1, some p.2) ((line4dDomOps c tt dd).width (p.1, some p.2)) 0
      ((line4dDomOps c tt dd).init (p.1, some p.2))
      ((top4wTree p.1.1 hnd hlt (decGroup n p.1.2.1) hinv (decStrN n p.1.2.2.2.1)
        D.shape.red).bind (fun A => .done (decPerm n p.1.2.2.1 • A))) := by
  have hxl : (masterHintTop p).2.1.length = p.1.1.length := length_rawRestrictStr _ _
  refine line4dDomOps_match_of_inner hx hy hgs hnd hlt hinv hΔ D a b
    (line4dDomInner_loopMatch_large hD hs hxl) hnh ?_
  intro k hkx hky
  exact alignShape_letters_of_dom_large D.shape D.head_not_mem hdom hL hkx hky

end Match

/-! ## In the node carrier -/

section Node

variable {c tt dd : ℕ} {n m : ℕ} {p : MasterHintInput}
    (hx : RawStr.WF n (2 * n + 1) p.1.2.2.2.1)
    (hy : RawStr.WF n (2 * n + 1) p.1.2.2.2.2)
    (hgs : RawGens.WF n p.1.2.1) (hnd : p.1.1.Nodup) (hlt : ∀ z ∈ p.1.1, z < n)
    (hinv : IsInvariant (decGroup n p.1.2.1) (winSet n p.1.1))
    (hΔ : 0 < p.1.1.length) (hr : masterHintRoute p = 4)
    (hhd : line4dHasDom c tt dd p = true)
    {par cost : ℕ}
    (D : Line4cdData (Fin p.1.1.length) ℕ (decGroup p.1.1.length (masterHintTop p).1.1.2)
      (decStrN p.1.1.length (masterHintTop p).2.1)
      (decStrN p.1.1.length (masterHintTop p).2.2) par cost)

/-- **The node carrier of Section 15 with `GD = Algo.line4dDomOps`** has local cost data. -/
theorem masterNodeFullDom_cost (a b B C₀ : ℕ)
    {cameron : RawGens × List ℕ → Option RawCameron} (hc : PolyFun cameron)
    (e f u v c tt dd c' b' t d dc dp E : ℕ) :
    Nonempty (MasterOpsCost a b (masterNodeFullOps B C₀ cameron e f u v c tt dd
      (line4dDomOps c tt dd) (default : ADState) c' b' t d dc dp E)) := by
  obtain ⟨CD⟩ := line4dDomOps_cost c tt dd a b
  exact masterNodeFull_cost a b B C₀ hc e f u v c tt dd default CD c' b' t d dc dp E

theorem masterNodeFullDom_runCostQ (a b B C₀ : ℕ)
    {cameron : RawGens × List ℕ → Option RawCameron} (hc : PolyFun cameron)
    (e f u v c tt dd c' b' t d dc dp E : ℕ) :
    Nonempty (Round.RunCostQ (masterAdmittedRound a b
      (masterNodeFullOps B C₀ cameron e f u v c tt dd (line4dDomOps c tt dd) (default : ADState)
        c' b' t d dc dp E))) :=
  (masterNodeFullDom_cost a b B C₀ hc e f u v c tt dd c' b' t d dc dp E).map
    MasterOpsCost.runCostQ

include hx hy hgs hΔ hr hhd in
/-- **Section 15, lines 4c–4d with a dominant color class, case 1, in the node carrier.** At
a node of route `4` where line 6 of Procedure Align finds a dominant color class and `m*` is
small, the node carrier with `GD = Algo.line4dDomOps` walks the lift of the Master's round of
`D` (`Algo.line4dDomOps_match_small`). -/
theorem masterNodeFull_line4cd_dom_match_small {a b B C₀ : ℕ}
    {cameron : RawGens × List ℕ → Option RawCameron} {e f u v : ℕ} {c' b' t d dc dp E : ℕ}
    {Dd : AlignDominantRoundData (Fin p.1.1.length)}
    (hD : ADDescribes p.1.1.length (line4dDomHdr c tt dd p) D.shape Dd)
    (hs : l57Small (line4dDomHdr c tt dd p) = true) :
    LoopMatch (masterAdmittedRound a b
        (masterNodeFullOps B C₀ cameron e f u v c tt dd (line4dDomOps c tt dd) default
          c' b' t d dc dp E))
      (fun J => decWinSI n J.1) (decCoset n) (p.1, some p.2)
      ((masterNodeFullOps B C₀ cameron e f u v c tt dd (line4dDomOps c tt dd) default
        c' b' t d dc dp E).width (p.1, some p.2)) 0
      ((masterNodeFullOps B C₀ cameron e f u v c tt dd (line4dDomOps c tt dd) default
        c' b' t d dc dp E).init (p.1, some p.2))
      ((top4wTree p.1.1 hnd hlt (decGroup n p.1.2.1) hinv (decStrN n p.1.2.2.2.1)
        D.shape.red).bind (fun A => .done (decPerm n p.1.2.2.1 • A))) :=
  masterTop_hinted_match (by simp) <| masterHint_line4cd_match hr <|
    masterPairIte_start_pos a b (show masterHasDom c tt dd (p.1, some p.2) = true from hhd)
      (line4dDomOps_match_small hx hy hgs hnd hlt hinv hΔ D a b hD hs)

include hx hy hgs hΔ hr hhd in
/-- **Section 15, lines 4c–4d with a dominant color class, cases 2 and 3, in the node
carrier**, when the Master's round attaches no hint (`Algo.line4dDomOps_match_large`). -/
theorem masterNodeFull_line4cd_dom_match_large {a b B C₀ : ℕ}
    {cameron : RawGens × List ℕ → Option RawCameron} {e f u v : ℕ} {c' b' t d dc dp E : ℕ}
    {Dd : AlignDominantRoundData (Fin p.1.1.length)}
    (hdom : D.shape.dom = some Dd) (hL : Dd.LargeParam) {Ws : List (Set (Fin p.1.1.length))}
    (hD : AVDescribes p.1.1.length (line4dDomHdr c tt dd p) D.shape Ws)
    (hs : l57Small (line4dDomHdr c tt dd p) = false)
    (hnh : ∀ J, D.shape.hint J = none) :
    LoopMatch (masterAdmittedRound a b
        (masterNodeFullOps B C₀ cameron e f u v c tt dd (line4dDomOps c tt dd) default
          c' b' t d dc dp E))
      (fun J => decWinSI n J.1) (decCoset n) (p.1, some p.2)
      ((masterNodeFullOps B C₀ cameron e f u v c tt dd (line4dDomOps c tt dd) default
        c' b' t d dc dp E).width (p.1, some p.2)) 0
      ((masterNodeFullOps B C₀ cameron e f u v c tt dd (line4dDomOps c tt dd) default
        c' b' t d dc dp E).init (p.1, some p.2))
      ((top4wTree p.1.1 hnd hlt (decGroup n p.1.2.1) hinv (decStrN n p.1.2.2.2.1)
        D.shape.red).bind (fun A => .done (decPerm n p.1.2.2.1 • A))) :=
  masterTop_hinted_match (by simp) <| masterHint_line4cd_match hr <|
    masterPairIte_start_pos a b (show masterHasDom c tt dd (p.1, some p.2) = true from hhd)
      (line4dDomOps_match_large hx hy hgs hnd hlt hinv hΔ D a b hdom hL hD hs hnh)

end Node

end Algo

#print axioms Algo.line4dDomOps_cost
#print axioms Algo.masterNodeFull_line4cd_dom_match_small
#print axioms Algo.masterNodeFull_line4cd_dom_match_large
#print axioms Algo.masterNodeFullDom_runCostQ
