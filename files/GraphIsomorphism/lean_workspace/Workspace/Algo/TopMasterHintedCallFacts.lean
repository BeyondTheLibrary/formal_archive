import Workspace.Algo.AlignDomHintL57
import Workspace.Algo.TopMasterHintedFinal
import Workspace.Algo.AlignDomHintLift
import Workspace.Algo.TopMasterL57CtxGood

/-! # The dominant-orbit call of Procedure Align, lifted to the Master's node

§14.1, lines 7–11 (case 3 of the repair), at a node of the Master Algorithm
(Section 15, line 4d and lines 5–7). The hint of line 11 has its meaning for a lifted call
(`Algo.alignDomHintAt_good`) once

* (`hKW`) the group of the call is the full preimage of `G*` in the node's group,
* (`hwinW`) the window of the call is the image of an orbit `u^{G*}` with `u` in the dominant
  window, and
* (`hAgrp`) the group of the action of Align is the group the node induces on its window.

This file proves these facts from the specifications of the machine's routines:

* `Algo.masterLiftCall_facts`: a window call `J` lifted to the node by `Algo.topwRawInstance`
  and normalized by `Algo.masterCheckedCall` has as group the full preimage of the group of `J`,
  and as window the image of the window of `J` (§11.1, Observation 11.1.11);
* `Algo.avChild_dom_call`: in cases 2 and 3 of the repair, the call of the loop of Eq. (71) at
  the first window of a version has the group `G* = ϕ⁻¹(Aut(X'))` and, as window, an orbit of
  `G*` through a point of the dominant window; `Algo.avChild_dom_index` shows that a call with
  more than `2|Δ|/3` points is at that window when the other color classes are small;
* `Algo.AVFirstOK` with `Algo.avFirstOK_avInit` and `Algo.avFirstOK_avCombine`: the state
  invariant that the first window of a version starts from the transporter of lines 1–3;
* `Algo.masterAV_dom_facts`: the chain of the three above at a node;
* `Algo.line4dDomOps_dom_call` (route 4) and `Algo.masterL57_dom_call` (route 5): the three
  facts for the children of the two carriers;
* `Algo.masterHintStepOK_masterL57Hint`: the hinted branch of `Algo.MasterHintStepOK` for the
  hint routine `Algo.masterL57Hint` of Section 13, from `Algo.alignDomHintAt_good`.

**What is asked of the Master side.** Besides the hypotheses of `Algo.alignDomHintAt_good`,
these lemmas ask that every color class other than the dominant one has at most `2|Δ|/3`
points (`htail`). The hint test of Section 13 (`Algo.masterL57HintTest`) identifies the
dominant-orbit call by its size (more than `2|Δ|/3` points), not by its position in the chain,
so a call on another class of that size would be hinted too. In the primitive case the classes
other than the dominant one have at most `|Δ|/2` points (`|Ω(Δ_i)| = C(|Δ_i|, t)` with
`|Δ_i| < m/2`), but the Master side proves only `4|Δ|/5`
(`Babai.five_mul_ncard_omegaColorClass_le_of_ne_dom`).
-/
set_option synthInstance.maxSize 4096
namespace Algo
open RAM RAM.Targets Babai Equiv MulAction
open scoped Pointwise

/-! ### A window call lifted to the node -/

section Lift

variable {n : ℕ} {W : RawWinSI}

/-- The window of a window call lifted to the node: the image of the window of the call, and
the lifted call is well formed. -/
theorem masterLiftCall_window (o : Option RawMasterHint) (hx : W.2.2.2.1.length = n)
    (hnd : W.1.Nodup) (hlt : ∀ u ∈ W.1, u < n) {J V : RawWinSI}
    (hV : topwRawInstance (masterWinCtx ((W, o) : RawMasterSI), J) = some V) :
    (masterCheckedCall (W.2.2.2.1, V)).1.1.Nodup ∧
      (∀ x ∈ (masterCheckedCall (W.2.2.2.1, V)).1.1, x < n) ∧
      RawGens.WF n (masterCheckedCall (W.2.2.2.1, V)).1.2.1 ∧
      winSet n (masterCheckedCall (W.2.2.2.1, V)).1.1 =
        (fun k : Fin W.1.length => ((winEquiv n W.1 hnd hlt k : ↥(winSet n W.1)) : Fin n)) ''
          winSet W.1.length J.1 := by
  have hwf := aggnCheckedWindow_wf W.2.2.2.1 V
  rw [hx] at hwf
  obtain ⟨q, -, rfl⟩ := Option.map_eq_some_iff.1 hV
  refine ⟨hwf.1, hwf.2.1, hwf.2.2.1, ?_⟩
  change winSet n (aggnCheckedWin (W.2.2.2.1, topw3LiftWindow (W.1, J.1))) = _
  rw [aggnCheckedWin_decode hx, topw3LiftWindow_spec W.1 J.1 hnd hlt]

/-- §11.1, Observation 11.1.11, **a window call lifted to the node**. Let `W` be a node with
degree `n` whose window is invariant under its group, and let the window call `J` have a group
inside the group the node induces on its window. Then the call the Master makes
(`Algo.topwRawInstance`, then `Algo.masterCheckedCall`) is a well-formed window of the node's
domain, its group is the full preimage of the group of `J`, and its window is the image of the
window of `J`. -/
theorem masterLiftCall_facts (o : Option RawMasterHint) (hx : W.2.2.2.1.length = n)
    (hgs : RawGens.WF n W.2.1) (hnd : W.1.Nodup) (hlt : ∀ u ∈ W.1, u < n)
    (hinv : IsInvariant (decGroup n W.2.1) (winSet n W.1)) {J V : RawWinSI}
    (hJ : decGroup W.1.length J.2.1 ≤
      (winRestrictHom n W.1 hnd hlt (decGroup n W.2.1) hinv).range)
    (hV : topwRawInstance (masterWinCtx ((W, o) : RawMasterSI), J) = some V) :
    (masterCheckedCall (W.2.2.2.1, V)).1.1.Nodup ∧
      (∀ x ∈ (masterCheckedCall (W.2.2.2.1, V)).1.1, x < n) ∧
      RawGens.WF n (masterCheckedCall (W.2.2.2.1, V)).1.2.1 ∧
      (∀ g, g ∈ decGroup n (masterCheckedCall (W.2.2.2.1, V)).1.2.1 ↔
        ∃ h : g ∈ decGroup n W.2.1,
          winRestrictHom n W.1 hnd hlt (decGroup n W.2.1) hinv ⟨g, h⟩ ∈
            decGroup W.1.length J.2.1) ∧
      (∀ x : Fin n, x ∈ winSet n (masterCheckedCall (W.2.2.2.1, V)).1.1 ↔
        ∃ k ∈ winSet W.1.length J.1,
          ((winEquiv n W.1 hnd hlt k : ↥(winSet n W.1)) : Fin n) = x) := by
  have hwf := aggnCheckedWindow_wf W.2.2.2.1 V
  rw [hx] at hwf
  obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.1 hV
  change (rawPreimage (((W.2.2.2.1, W.2.1)), (W.1, normPerm (W.1, J.2.2.1)))).map
    (fun r => (tidyGens (W.2.2.2.1, rawLiftGens ((W.2.2.2.1, W.2.1),
      (W.1, normGens (W.1, J.2.1)))), normPerm (W.2.2.2.1, r))) = some q at hq
  obtain ⟨r, -, rfl⟩ := Option.map_eq_some_iff.1 hq
  refine ⟨hwf.1, hwf.2.1, hwf.2.2.1, ?_, ?_⟩
  · intro g
    have hL := decGroup_rawLiftGens (dom := W.2.2.2.1) (gens := W.2.1.map (decPerm n)) hx hnd hlt
      hinv (J.2.1.map (decPerm W.1.length)) hJ
    rw [map_encPerm_decPerm hgs] at hL
    change g ∈ decGroup n (tidyGens (W.2.2.2.1, tidyGens (W.2.2.2.1, rawLiftGens
      ((W.2.2.2.1, W.2.1), (W.1, normGens (W.1, J.2.1)))))) ↔ _
    rw [decGroup_tidyGens hx, decGroup_tidyGens hx, normGens_eq_enc rfl, hL]
    exact mem_winPreimage hnd hlt hinv _ g
  · intro x
    change x ∈ winSet n (aggnCheckedWin (W.2.2.2.1, topw3LiftWindow (W.1, J.1))) ↔ _
    rw [aggnCheckedWin_decode hx, topw3LiftWindow_spec W.1 J.1 hnd hlt, Set.mem_image]

/-- **The carrier obligation `Algo.MasterL57LiftFacts` of Section 13 holds**: it is
`Algo.masterLiftCall_facts` at a raw node. -/
theorem masterL57LiftFacts (n : ℕ) : MasterL57LiftFacts n := by
  intro P J V hnd hlt hinv hP _ _ _ hJ hV
  obtain ⟨hdeg, hWwf, -⟩ := hP
  obtain ⟨-, -, -, h4, h5⟩ := masterLiftCall_facts (W := P.1) P.2 hdeg hWwf.2.2.1 hnd hlt hinv
    hJ hV
  exact ⟨h4, h5⟩

end Lift

/-! ### The call of Eq. (71) at the first window of a version -/

section Window

/-- The invariant of the loop of Eq. (71) (`Algo.avCombine`): at the first window of a
version, the coset the chain has reached is the transporter of lines 1–3 for that version
(`Algo.avTr`). -/
def AVFirstOK (h : AVHdr) (s : AVState) : Prop := s.2.1 = 0 → s.2.2.1 = avTr (h, s.1)

theorem avFirstOK_avPos (h : AVHdr) (k : ℕ) (acc : RawCoset) :
    AVFirstOK h (avPos (h, k, acc)) := fun _ => rfl

theorem avFirstOK_avInit (h : AVHdr) : AVFirstOK h (avInit h) := avFirstOK_avPos h 0 none

/-- Every state `Algo.avCombine` produces has the invariant. -/
theorem avFirstOK_avCombine (h : AVHdr) (s : AVState) (a : RawCoset) :
    AVFirstOK h (avCombine (h, s, a)) := by
  unfold avCombine
  cases a with
  | none => exact avFirstOK_avPos _ _ _
  | some a =>
    simp only [Option.elim]
    split_ifs
    · intro h0
      exact absurd h0 (Nat.succ_ne_zero _)
    · exact avFirstOK_avPos _ _ _

/-- In cases 2 and 3 (no case 1), the loop of stretch 3 starts with the invariant. -/
theorem avFirstOK_l57Init {h : AVHdr} (hs : l57Small h = false) :
    AVFirstOK h (l57Init h).1 := by
  unfold l57Init
  rw [hs]
  exact avFirstOK_avInit h

/-- In cases 2 and 3 (no case 1), every step of stretch 3 keeps the invariant. -/
theorem avFirstOK_l57Step {h : AVHdr} (hs : l57Small h = false) (st : ADState) (a : RawCoset) :
    AVFirstOK h (l57Step (h, st, a)).1 := by
  unfold l57Step
  rw [hs]
  exact avFirstOK_avCombine h _ _

/-- The generators of the transporter of lines 1–3 are those of `G₁ = ϕ⁻¹(Aut(X'))`. -/
theorem avTr_gens {h : AVHdr} {k : ℕ} {gt : RawGens × RawPerm} (hk : avTr (h, k) = some gt) :
    gt.1 = tidyGens (h.2.2.2.2.1, alignPairG1 (h.1, h.2.1)) := by
  unfold avTr rawCosetNorm at hk
  obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.1 hk
  unfold alignPairCoset at hq
  obtain ⟨s, -, hs⟩ := Option.bind_eq_some_iff.1 hq
  obtain ⟨σ, -, rfl⟩ := Option.map_eq_some_iff.1 hs
  rfl

/-- The dominant window of Procedure Align for the header `h`. -/
def avDomWindow (h : AVHdr) : List ℕ :=
  alignRDomWindow (alignRColorOf (h.1, h.2.1), alignRDomColor (alignRColorOf (h.1, h.2.1)))

/-- An entry of a list `a :: r` at a positive index is an entry of `r`. -/
theorem getElem_mem_of_eq_cons {α : Type*} {a : α} {r L : List α} (hL : L = a :: r) {i : ℕ}
    (hi : i < L.length) (h0 : i ≠ 0) : L[i] ∈ r := by
  subst hL
  cases i with
  | zero => exact absurd rfl h0
  | succ k => exact List.getElem_mem _

variable {n : ℕ} {h : AVHdr} {s : AVState} {J : RawWinSI}

/-- The call of `Algo.avChild`, read off. -/
theorem avChild_some (hJ : avChild (h, s) = some J) :
    s.2.1 < h.2.2.2.1.length ∧ J.1 = h.2.2.2.1.getD s.2.1 [] ∧
      ∃ gt, s.2.2.1 = some gt ∧ J.2.1 = tidyGens (h.2.2.2.2.1, gt.1) := by
  unfold avChild at hJ
  obtain ⟨gt, hgt, hJ⟩ := Option.bind_eq_some_iff.1 hJ
  split_ifs at hJ with hc
  cases hJ
  exact ⟨hc.1, rfl, gt, hgt, rfl⟩

/-- §14.1, lines 7–11, cases 2 and 3 of the repair: **the call at the first
window of a version.** When the windows of the header are those of `Algo.alignL57Windows` and
the test of the repair holds, the call of the loop of Eq. (71) at the first window of a version
has the group `G* = ϕ⁻¹(Aut(X'))` (the group of `Algo.alignPairG1`), and its window is an orbit
of `G*` through a point of the dominant window (the first entry of `Algo.alignDomOrbits`). -/
theorem avChild_dom_call (hd : h.1.1.1.length = n) (hx : h.2.2.2.2.1.length = n)
    (hw : h.2.2.2.1 = alignL57Windows (h.1, h.2.1)) (hl : alignRLarge (h.1, h.2.1) = true)
    (hs : AVFirstOK h s) (hs0 : s.2.1 = 0)
    (hne : alignDomOrbits ((alignPairG1 (h.1, h.2.1), avDomWindow h), n) ≠ [])
    (hJ : avChild (h, s) = some J) :
    decGroup n J.2.1 = decGroup n (alignPairG1 (h.1, h.2.1)) ∧
      ∃ u ∈ winSet n (avDomWindow h),
        winSet n J.1 = orbit (decGroup n (alignPairG1 (h.1, h.2.1))) u := by
  obtain ⟨-, hJ1, gt, hgt, hJ2⟩ := avChild_some hJ
  refine ⟨?_, ?_⟩
  · rw [hJ2, avTr_gens ((hs hs0).symm.trans hgt), decGroup_tidyGens hx, decGroup_tidyGens hx]
  · have hgs : RawGens.WF n (alignPairG1 (h.1, h.2.1)) := alignPairG1_wf hd
    set O := alignDomOrbits ((alignPairG1 (h.1, h.2.1), avDomWindow h), n) with hO
    have hwin : h.2.2.2.1 = O ++ (alignRWindows (alignRColorOf (h.1, h.2.1))).tail := by
      rw [hw, alignL57Windows_of_large hl, hd]
      rfl
    have hpos : 0 < O.length := List.length_pos_iff.2 hne
    have hJO : J.1 = O[0] := by
      rw [hJ1, hs0, hwin, List.getD_eq_getElem _ _ (by rw [List.length_append]; omega),
        List.getElem_append_left hpos]
    have hmem : J.1 ∈ winOrbits (alignPairG1 (h.1, h.2.1), avDomWindow h) :=
      (perm_alignDomFirst _).subset (hJO ▸ List.getElem_mem hpos)
    obtain ⟨j, hj, hJj⟩ := winOrbits_mem hmem
    have hjn : j < n := by
      have := (mem_alignRDomWindow.1 hj).1
      change j < h.1.1.1.length at this
      omega
    refine ⟨⟨j, hjn⟩, hj, ?_⟩
    rw [hJj]
    exact winSet_rawOrbit hgs ⟨j, hjn⟩

/-- §14.1, lines 7–11, case 3: **a call of more than `2|Δ|/3` points is at the first window of
its version.** In cases 2 and 3 the windows are the orbits of `G*` in the dominant window, a
dominant orbit first (`Algo.alignDomOrbits_first`: at most one orbit is that large, and it
heads the list), then the other color classes. When the other classes have at most `2|Δ|/3`
points each, a call with more is at the first window, and the orbit list is not empty. -/
theorem avChild_dom_index (hd : h.1.1.1.length = n)
    (hw : h.2.2.2.1 = alignL57Windows (h.1, h.2.1)) (hl : alignRLarge (h.1, h.2.1) = true)
    (hinvD : rawIsInvariant (alignPairG1 (h.1, h.2.1), avDomWindow h) = true)
    (htail : ∀ S ∈ (alignRWindows (alignRColorOf (h.1, h.2.1))).tail,
      3 * (winSet n S).ncard ≤ 2 * n)
    (hJ : avChild (h, s) = some J) (hbig : 2 * n < 3 * (winSet n J.1).ncard) :
    s.2.1 = 0 ∧ alignDomOrbits ((alignPairG1 (h.1, h.2.1), avDomWindow h), n) ≠ [] := by
  obtain ⟨hlen, hJ1, -⟩ := avChild_some hJ
  have hgs : RawGens.WF n (alignPairG1 (h.1, h.2.1)) := alignPairG1_wf hd
  have hltD : ∀ j ∈ avDomWindow h, j < n := fun j hj => by
    have := (mem_alignRDomWindow.1 hj).1
    change j < h.1.1.1.length at this
    omega
  set O := alignDomOrbits ((alignPairG1 (h.1, h.2.1), avDomWindow h), n) with hO
  set T := (alignRWindows (alignRColorOf (h.1, h.2.1))).tail with hT
  have hwin : h.2.2.2.1 = O ++ T := by
    rw [hw, alignL57Windows_of_large hl, hd]
    rfl
  rw [hwin] at hlen hJ1
  rw [List.getD_eq_getElem _ _ hlen] at hJ1
  by_cases hwO : s.2.1 < O.length
  · rw [List.getElem_append_left hwO] at hJ1
    refine ⟨?_, List.ne_nil_of_length_pos (by omega)⟩
    have hSmem : winSet n J.1 ∈ O.map (winSet n) := by
      rw [hJ1]
      exact List.mem_map_of_mem (List.getElem_mem hwO)
    obtain ⟨rest, hrest, hnot⟩ := alignDomOrbits_first hgs hltD hinvD _ hSmem hbig
    by_contra hne0
    have hlt' : s.2.1 < (O.map (winSet n)).length := by rw [List.length_map]; exact hwO
    have hget : (O.map (winSet n))[s.2.1] = winSet n J.1 := by
      rw [List.getElem_map, hJ1]
    exact hnot (hget ▸ getElem_mem_of_eq_cons hrest hlt' hne0)
  · exfalso
    rw [Nat.not_lt] at hwO
    rw [List.getElem_append_right hwO] at hJ1
    have hmem : J.1 ∈ T := hJ1 ▸ List.getElem_mem _
    have := htail J.1 hmem
    omega

end Window

/-! ### The dominant-orbit call of a carrier, at the node -/

section Node

variable {n : ℕ} {W : RawWinSI}

/-- §14.1, line 11, case 3, **the facts of `Algo.alignDomHintAt_good` for a lifted call of the
loop of Eq. (71).** Let the node `W` (degree `n`, window `Δ = W.1` invariant under its group)
run the loop of Eq. (71) with a header `hdr` on its window, in cases 2 and 3 of the repair,
with the group of the action the group the node induces on `Δ` (`hAgrp`). Let the loop make the
call `Jw` from a state with the invariant `Algo.AVFirstOK`, read by the carrier as a call `J'`
with the same group and window, lifted to the node as `V`. If the lifted call has more than
`2|Δ|/3` points and the other color classes have at most `2|Δ|/3` points, then the lifted call
is well formed, its group is the full preimage of `G*` in the node's group (`hKW`), and its
window is the image of an orbit of `G*` through a point of the dominant window (`hwinW`). -/
theorem masterAV_dom_facts (o' : Option RawMasterHint) (hx : W.2.2.2.1.length = n)
    (hgs : RawGens.WF n W.2.1) (hnd : W.1.Nodup) (hlt : ∀ u ∈ W.1, u < n)
    (hinv : IsInvariant (decGroup n W.2.1) (winSet n W.1)) {hdr : AVHdr} {st : AVState}
    (hd : hdr.1.1.1.length = W.1.length) (hxh : hdr.2.2.2.2.1.length = W.1.length)
    (hw : hdr.2.2.2.1 = alignL57Windows (hdr.1, hdr.2.1))
    (hl : alignRLarge (hdr.1, hdr.2.1) = true) (hs : AVFirstOK hdr st)
    (hinvD : rawIsInvariant (alignPairG1 (hdr.1, hdr.2.1), avDomWindow hdr) = true)
    (htail : ∀ S ∈ (alignRWindows (alignRColorOf (hdr.1, hdr.2.1))).tail,
      3 * (winSet W.1.length S).ncard ≤ 2 * W.1.length)
    (hAgrp : decGroup W.1.length hdr.1.1.2 =
      (winRestrictHom n W.1 hnd hlt (decGroup n W.2.1) hinv).range)
    (hG1 : decGroup W.1.length (alignPairG1 (hdr.1, hdr.2.1)) ≤ decGroup W.1.length hdr.1.1.2)
    {Jw J' V : RawWinSI} (hJ : avChild (hdr, st) = some Jw)
    (hJ'g : decGroup W.1.length J'.2.1 = decGroup W.1.length Jw.2.1)
    (hJ'w : winSet W.1.length J'.1 = winSet W.1.length Jw.1)
    (hV : topwRawInstance (masterWinCtx ((W, o') : RawMasterSI), J') = some V)
    (hbig : 2 * W.1.length < 3 * (masterCheckedCall (W.2.2.2.1, V)).1.1.length) :
    (masterCheckedCall (W.2.2.2.1, V)).1.1.Nodup ∧
      (∀ x ∈ (masterCheckedCall (W.2.2.2.1, V)).1.1, x < n) ∧
      RawGens.WF n (masterCheckedCall (W.2.2.2.1, V)).1.2.1 ∧
      (∀ g, g ∈ decGroup n (masterCheckedCall (W.2.2.2.1, V)).1.2.1 ↔
        ∃ h : g ∈ decGroup n W.2.1,
          winRestrictHom n W.1 hnd hlt (decGroup n W.2.1) hinv ⟨g, h⟩ ∈
            decGroup W.1.length (alignPairG1 (hdr.1, hdr.2.1))) ∧
      ∃ u ∈ winSet W.1.length (avDomWindow hdr), ∀ x : Fin n,
        x ∈ winSet n (masterCheckedCall (W.2.2.2.1, V)).1.1 ↔
          ∃ k ∈ orbit (decGroup W.1.length (alignPairG1 (hdr.1, hdr.2.1))) u,
            ((winEquiv n W.1 hnd hlt k : ↥(winSet n W.1)) : Fin n) = x := by
  obtain ⟨hndC, hltC, -, hwinC⟩ := masterLiftCall_window o' hx hnd hlt hV
  have he_inj : Function.Injective
      (fun k : Fin W.1.length => ((winEquiv n W.1 hnd hlt k : ↥(winSet n W.1)) : Fin n)) :=
    Subtype.val_injective.comp (winEquiv n W.1 hnd hlt).injective
  have hbig' : 2 * W.1.length < 3 * (winSet W.1.length Jw.1).ncard := by
    rw [← hJ'w, ← Set.ncard_image_of_injective _ he_inj, ← hwinC, ncard_winSet _ hndC hltC]
    exact hbig
  obtain ⟨hs0, hne⟩ := avChild_dom_index hd hw hl hinvD htail hJ hbig'
  obtain ⟨hg, u, hu, hJo⟩ := avChild_dom_call hd hxh hw hl hs hs0 hne hJ
  have hJle : decGroup W.1.length J'.2.1 ≤
      (winRestrictHom n W.1 hnd hlt (decGroup n W.2.1) hinv).range := by
    rw [hJ'g, hg, ← hAgrp]
    exact hG1
  obtain ⟨h1, h2, h3, h4, h5⟩ := masterLiftCall_facts o' hx hgs hnd hlt hinv hJle hV
  refine ⟨h1, h2, h3, ?_, u, hu, ?_⟩
  · intro g
    rw [h4 g, hJ'g, hg]
  · intro x
    rw [h5 x, hJ'w, hJo]

end Node

/-! ### Route 4: line 4d with a dominant class -/

section Route4

variable {c tt dd n j : ℕ} {W : RawWinSI} {hh : RawMasterHint}

/-- §14.1, lines 7–11, case 3, at line 4d of the Master (route `4`, `Algo.line4dDomOps`):
**the facts of `Algo.alignDomHintAt_good` for a child of the carrier** of more than `2|Δ|/3`
points, with `A` the action of the node's top (`Algo.masterHintTop`) and `o` the fixed version
of line 4c (`Algo.line4dFixed`). The hypotheses on the Master side are the test of the repair
(`hl`), `G* ≤ G` (`hG1`), the invariance of the dominant window under `G*` (`hinvD`), the
bound `2|Δ|/3` on the other color classes (`htail`), and the invariant of the loop
(`Algo.AVFirstOK`, kept by every step: `Algo.avFirstOK_l57Init`, `Algo.avFirstOK_l57Step`). -/
theorem line4dDomOps_dom_call (hx : W.2.2.2.1.length = n) (hgs : RawGens.WF n W.2.1)
    (hnd : W.1.Nodup) (hlt : ∀ u ∈ W.1, u < n)
    (hinv : IsInvariant (decGroup n W.2.1) (winSet n W.1)) {s : ADState} {C : RawMasterSI}
    (hl : alignRLarge ((masterHintTop (W, hh)).1, line4dFixed c tt dd (W, hh)) = true)
    (hG1 : decGroup W.1.length (alignPairG1 ((masterHintTop (W, hh)).1,
      line4dFixed c tt dd (W, hh))) ≤ decGroup W.1.length (masterHintTop (W, hh)).1.1.2)
    (hinvD : rawIsInvariant (alignPairG1 ((masterHintTop (W, hh)).1,
      line4dFixed c tt dd (W, hh)), avDomWindow (line4dDomHdr c tt dd (W, hh))) = true)
    (htail : ∀ S ∈ (alignRWindows (alignRColorOf ((masterHintTop (W, hh)).1,
      line4dFixed c tt dd (W, hh)))).tail, 3 * (winSet W.1.length S).ncard ≤ 2 * W.1.length)
    (hs : AVFirstOK (line4dDomHdr c tt dd (W, hh)) s.1)
    (hC : (line4dDomOps c tt dd).child ((W, some hh), j, s) = some C)
    (hbig : 2 * W.1.length < 3 * C.1.1.length) :
    C.2 = none ∧
      decGroup W.1.length (masterHintTop (W, hh)).1.1.2 =
        (winRestrictHom n W.1 hnd hlt (decGroup n W.2.1) hinv).range ∧
      C.1.1.Nodup ∧ (∀ x ∈ C.1.1, x < n) ∧ RawGens.WF n C.1.2.1 ∧
      (∀ g, g ∈ decGroup n C.1.2.1 ↔ ∃ h : g ∈ decGroup n W.2.1,
          winRestrictHom n W.1 hnd hlt (decGroup n W.2.1) hinv ⟨g, h⟩ ∈
            decGroup W.1.length (alignPairG1 ((masterHintTop (W, hh)).1,
              line4dFixed c tt dd (W, hh)))) ∧
      ∃ u ∈ winSet W.1.length (alignRDomWindow (alignRColorOf ((masterHintTop (W, hh)).1,
          line4dFixed c tt dd (W, hh)), alignRDomColor (alignRColorOf
            ((masterHintTop (W, hh)).1, line4dFixed c tt dd (W, hh))))), ∀ x : Fin n,
        x ∈ winSet n C.1.1 ↔
          ∃ k ∈ orbit (decGroup W.1.length (alignPairG1 ((masterHintTop (W, hh)).1,
              line4dFixed c tt dd (W, hh)))) u,
            ((winEquiv n W.1 hnd hlt k : ↥(winSet n W.1)) : Fin n) = x := by
  set hdr := line4dDomHdr c tt dd (W, hh) with hhdr
  have hAgrp : decGroup W.1.length (masterHintTop (W, hh)).1.1.2 =
      (winRestrictHom n W.1 hnd hlt (decGroup n W.2.1) hinv).range :=
    decGroup_rawRestrictGens_of_raw hgs hnd hlt hinv
  have hsm : l57Small hdr = false := l57Small_false_of_large hl
  -- the child, read off
  have hC' : (if j < l57Calls hdr then (l57Child (hdr, s)).bind (fun Wj =>
      (topwRawInstance (line4dCtx (W, hh), Wj)).map fun V => (((W, hh) : MasterHintInput), some V))
      else none).map (fun J => masterCheckedCall (W.2.2.2.1, line4dNodeRead J)) = some C := hC
  split_ifs at hC' with hj
  swap
  · simp at hC'
  obtain ⟨J, hJ, rfl⟩ := Option.map_eq_some_iff.1 hC'
  obtain ⟨Jw, hJw, hJ⟩ := Option.bind_eq_some_iff.1 hJ
  obtain ⟨V, hV, rfl⟩ := Option.map_eq_some_iff.1 hJ
  have hJw' : avChild (hdr, s.1) = some Jw := by
    unfold l57Child at hJw
    rw [hsm] at hJw
    exact hJw
  obtain ⟨h1, h2, h3, h4, h5⟩ := masterAV_dom_facts (some hh) hx hgs hnd hlt hinv
    (hdr := hdr) (st := s.1) rfl (by simp [hhdr, line4dDomHdr, masterHintTop,
      primitiveWindowInput]) rfl hl hs hinvD htail hAgrp hG1 hJw' rfl rfl hV hbig
  exact ⟨rfl, hAgrp, h1, h2, h3, h4, h5⟩

end Route4

/-! ### Route 5: lines 5–7 -/

section Route5

variable {c b t d dc dp e f E n j : ℕ} {W : RawWinSI} {hh : RawMasterHint}

/-- The header of Procedure Align at a fold state of the round of lines 5–7. -/
abbrev masterL57HdrAt (c b t d dc dp : ℕ) (P : RawMasterSI) (s : AggnL57GState) : AVHdr :=
  masterL57HintHdr c b t d dc dp (P, 0, s)

set_option maxHeartbeats 1000000 in
/-- §14.1, lines 7–11, case 3, at lines 5–7 of the Master (route `5`, `Algo.masterL57Ops`):
**the facts of `Algo.alignDomHintAt_good` for a child to which the hint routine
`Algo.masterL57Hint` attaches a hint** (its test `Algo.masterL57HintTest` holds: stretch 3,
case 3 of the repair, and more than `2|Δ|/3` points), with `A` and `o` the action and the
fixed version of Procedure Align that the routine reads (`Algo.masterL57HintHdr`). The
hypotheses on the Master side are as for `Algo.line4dDomOps_dom_call`; the invariant of the
loop is asked of the state of stretch 3 that the round reads. -/
theorem masterL57_dom_call (hx : W.2.2.2.1.length = n) (hgs : RawGens.WF n W.2.1)
    (hnd : W.1.Nodup) (hlt : ∀ u ∈ W.1, u < n)
    (hinv : IsInvariant (decGroup n W.2.1) (winSet n W.1)) {s : AggnL57GState}
    {C : RawMasterSI}
    (hT : masterL57HintTest c b t d dc dp (l57UV e f).1 (l57UV e f).2 e f
      ((((W, some hh) : RawMasterSI), j, s), C) = true)
    (hG1 : decGroup W.1.length (alignPairG1 ((masterL57HdrAt c b t d dc dp (W, some hh) s).1,
      (masterL57HdrAt c b t d dc dp (W, some hh) s).2.1)) ≤
        decGroup W.1.length (masterL57Ctx (W, some hh)).1.1.2)
    (hinvD : rawIsInvariant (alignPairG1 ((masterL57HdrAt c b t d dc dp (W, some hh) s).1,
      (masterL57HdrAt c b t d dc dp (W, some hh) s).2.1),
        avDomWindow (masterL57HdrAt c b t d dc dp (W, some hh) s)) = true)
    (htail : ∀ S ∈ (alignRWindows (alignRColorOf
      ((masterL57HdrAt c b t d dc dp (W, some hh) s).1,
        (masterL57HdrAt c b t d dc dp (W, some hh) s).2.1))).tail,
      3 * (winSet W.1.length S).ncard ≤ 2 * W.1.length)
    (hs : AVFirstOK (masterL57HdrAt c b t d dc dp (W, some hh) s)
      (s.1.2.getD (l57Init (masterL57HdrAt c b t d dc dp (W, some hh) s))).1)
    (hC : (masterL57Ops c b t d dc dp e f E).child ((W, some hh), j, s) = some C) :
    C.2 = none ∧
      (masterL57HdrAt c b t d dc dp (W, some hh) s).1 = (masterL57Ctx (W, some hh)).1 ∧
      decGroup W.1.length (masterL57Ctx (W, some hh)).1.1.2 =
        (winRestrictHom n W.1 hnd hlt (decGroup n W.2.1) hinv).range ∧
      C.1.1.Nodup ∧ (∀ x ∈ C.1.1, x < n) ∧ RawGens.WF n C.1.2.1 ∧
      (∀ g, g ∈ decGroup n C.1.2.1 ↔ ∃ h : g ∈ decGroup n W.2.1,
          winRestrictHom n W.1 hnd hlt (decGroup n W.2.1) hinv ⟨g, h⟩ ∈
            decGroup W.1.length (alignPairG1 ((masterL57HdrAt c b t d dc dp (W, some hh) s).1,
              (masterL57HdrAt c b t d dc dp (W, some hh) s).2.1))) ∧
      ∃ u ∈ winSet W.1.length (avDomWindow (masterL57HdrAt c b t d dc dp (W, some hh) s)),
        ∀ x : Fin n, x ∈ winSet n C.1.1 ↔
          ∃ k ∈ orbit (decGroup W.1.length (alignPairG1
              ((masterL57HdrAt c b t d dc dp (W, some hh) s).1,
                (masterL57HdrAt c b t d dc dp (W, some hh) s).2.1))) u,
            ((winEquiv n W.1 hnd hlt k : ↥(winSet n W.1)) : Fin n) = x := by
  set hdr := masterL57HdrAt c b t d dc dp (W, some hh) s with hhdr
  have hA : hdr.1 = (masterL57Ctx (W, some hh)).1 := rfl
  have hAgrp : decGroup W.1.length (masterL57Ctx (W, some hh)).1.1.2 =
      (winRestrictHom n W.1 hnd hlt (decGroup n W.2.1) hinv).range :=
    (masterL57Ctx_group' W hh).trans (decGroup_rawRestrictGens_of_raw hgs hnd hlt hinv)
  -- the test, read
  simp only [masterL57HintTest, Bool.and_eq_true, Bool.not_eq_true',
    Option.isNone_iff_eq_none, decide_eq_true_eq] at hT
  obtain ⟨⟨⟨hnA, hagg⟩, hl⟩, hbig⟩ := hT
  have hl' : alignRLarge (hdr.1, hdr.2.1) = true := hl
  have hsm : l57Small hdr = false := l57Small_false_of_large hl'
  -- the child, read off
  have hguard : masterL57Guard ((W, some hh) : RawMasterSI) = true := by
    by_contra hg
    rw [Bool.not_eq_true] at hg
    have : (masterL57Ops c b t d dc dp e f E).child ((W, some hh), j, s) = none := by
      change (if masterL57Guard ((W, some hh) : RawMasterSI) then _ else none) = none
      rw [hg]
      rfl
    rw [this] at hC
    cases hC
  change (if masterL57Guard ((W, some hh) : RawMasterSI) then
    ((masterL57Round c b t d dc dp e f).child (masterL57Enter (W, some hh), j, s)).bind
      (fun J => (topwRawInstance (masterWinCtx (W, some hh), masterL57Read (W, some hh) J)).map
        (fun V => masterCheckedCall (W.2.2.2.1, V))) else none) = some C at hC
  rw [if_pos hguard] at hC
  obtain ⟨J, hJ, hC⟩ := Option.bind_eq_some_iff.1 hC
  obtain ⟨V, hV, rfl⟩ := Option.map_eq_some_iff.1 hC
  change aggnL57GChild c b t d dc dp (l57UV e f).1 (l57UV e f).2 e f
    (masterL57Enter (W, some hh), j, s) = some J at hJ
  unfold aggnL57GChild at hJ
  rw [if_neg (by rw [hnA]; exact Bool.false_ne_true)] at hJ
  unfold aggnL57Child at hJ
  rw [hagg] at hJ
  change (if j < aggnAggregateWidth c (masterL57Ctx (W, some hh)) +
      l57Calls (aggnL57Hdr c b t d dc dp (masterL57Ctx (W, some hh), s.1.1)) then
      (l57Child (aggnL57Hdr c b t d dc dp (masterL57Ctx (W, some hh), s.1.1),
        s.1.2.getD (l57Init (aggnL57Hdr c b t d dc dp (masterL57Ctx (W, some hh), s.1.1))))).map
        (fun J => avEmb (masterL57Ctx (W, some hh), J))
    else none) = some J at hJ
  split_ifs at hJ with hj
  obtain ⟨Jw, hJw, rfl⟩ := Option.map_eq_some_iff.1 hJ
  have hJw' : avChild (hdr, (s.1.2.getD (l57Init hdr)).1) = some Jw := by
    change l57Child (hdr, s.1.2.getD (l57Init hdr)) = some Jw at hJw
    unfold l57Child at hJw
    rw [hsm] at hJw
    exact hJw
  have hxl : (masterL57Ctx ((W, some hh) : RawMasterSI)).2.1.length = W.1.length :=
    masterL57Ctx_length _
  have hJ'g : decGroup W.1.length (masterL57Read (W, some hh) (avEmb (masterL57Ctx (W, some hh), Jw))).2.1 =
      decGroup W.1.length Jw.2.1 := by
    change decGroup W.1.length (tidyGens ((masterL57Ctx (W, some hh)).2.1, Jw.2.1)) = _
    rw [decGroup_tidyGens hxl]
  have hJ'w : winSet W.1.length (masterL57Read (W, some hh) (avEmb (masterL57Ctx (W, some hh), Jw))).1 =
      winSet W.1.length Jw.1 := by
    change winSet W.1.length (aggnCheckedWin ((masterL57Ctx (W, some hh)).2.1, Jw.1)) = _
    rw [aggnCheckedWin_decode hxl]
  obtain ⟨h1, h2, h3, h4, h5⟩ := masterAV_dom_facts (some hh) hx hgs hnd hlt hinv
    (hdr := hdr) (st := (s.1.2.getD (l57Init hdr)).1)
    (by rw [hA]; exact List.length_range) hxl rfl hl' hs hinvD htail
    (hA ▸ hAgrp) (hA ▸ hG1) hJw' hJ'g hJ'w hV hbig
  exact ⟨rfl, hA, hAgrp, h1, h2, h3, h4, h5⟩

end Route5

/-! ### The hinted branch of the step condition of route 5 -/

section Step5

variable {c b t d dc dp e f n j : ℕ} {W : RawWinSI} {hh : RawMasterHint}

set_option maxHeartbeats 1000000 in
/-- §14.1, line 11, case 3, at lines 5–7 of the Master, for a fixed version that is a split
outcome at any threshold `α > 1/2` (`4/5` at outcome (1), Line 7a of §15; the statement of
`Algo.masterHintStepOK_masterL57Hint` is at `3/4`): **the hinted branch of the step
condition `Algo.MasterHintStepOK` for the hint routine `Algo.masterL57Hint`.** At a call of the
round of lines 5–7 (`hc`, `hV`) to which the routine attaches a hint (its test holds, `hT`),
the hint has its meaning for the lifted call, its points are below `n`, and its parameter is
at most half the node's (Eq. (73)). The hypotheses on the Master side are those of
`Algo.alignDomHintAt_good` for the action `A` of the context of lines 5–7
(`Algo.masterL57Ctx`, which the round and the routine read; `Algo.masterL57Ctx_hintFacts`
gives its hint facts at a good node) and the fixed version `o` the round reads, and those of
`Algo.masterL57_dom_call`. -/
theorem masterHintStepOK_masterL57Hint_alpha (hx : W.2.2.2.1.length = n) (hgs : RawGens.WF n W.2.1)
    (hnd : W.1.Nodup) (hlt : ∀ u ∈ W.1, u < n)
    (hinv : IsInvariant (decGroup n W.2.1) (winSet n W.1)) {s : AggnL57GState}
    {J : AggnPhaseNode} {V : RawWinSI}
    (hguard : masterL57Guard ((W, some hh) : RawMasterSI) = true)
    (hc : (masterL57Round c b t d dc dp e f).child (masterL57Enter (W, some hh), j, s) = some J)
    (hV : topwRawInstance (masterWinCtx ((W, some hh) : RawMasterSI), masterL57Read (W, some hh) J) = some V)
    (hT : masterL57HintTest c b t d dc dp (l57UV e f).1 (l57UV e f).2 e f
      ((((W, some hh) : RawMasterSI), j, s), masterCheckedCall (W.2.2.2.1, V)) = true)
    (hG1 : decGroup W.1.length (alignPairG1 ((masterL57HdrAt c b t d dc dp (W, some hh) s).1,
      (masterL57HdrAt c b t d dc dp (W, some hh) s).2.1)) ≤
        decGroup W.1.length (masterL57Ctx (W, some hh)).1.1.2)
    (hinvD : rawIsInvariant (alignPairG1 ((masterL57HdrAt c b t d dc dp (W, some hh) s).1,
      (masterL57HdrAt c b t d dc dp (W, some hh) s).2.1),
        avDomWindow (masterL57HdrAt c b t d dc dp (W, some hh) s)) = true)
    (htail : ∀ S ∈ (alignRWindows (alignRColorOf
      ((masterL57HdrAt c b t d dc dp (W, some hh) s).1,
        (masterL57HdrAt c b t d dc dp (W, some hh) s).2.1))).tail,
      3 * (winSet W.1.length S).ncard ≤ 2 * W.1.length)
    (hs : AVFirstOK (masterL57HdrAt c b t d dc dp (W, some hh) s)
      (s.1.2.getD (l57Init (masterL57HdrAt c b t d dc dp (W, some hh) s))).1)
    {m : ℕ} [MulAction (Perm (Fin m)) (Pt (SplitOutcomes (Fin m)))]
    {ϕ : decGroup W.1.length (masterL57Ctx (W, some hh)).1.1.2 →* Perm (Fin m)}
    (hA : RawAction.WF W.1.length m (masterL57Ctx (W, some hh)).1 ϕ)
    (hG : IsTransitive (decGroup W.1.length (masterL57Ctx (W, some hh)).1.1.2))
    (hϕ : IsGiantRep ϕ)
    (hvl : VeryLargeK m (maxOrbitLength (decGroup W.1.length (masterL57Ctx (W, some hh)).1.1.2)))
    {tt : ℕ} (ht : ∀ u : Fin W.1.length, tPoint ϕ u = tt)
    (hK : IsCatAction (SplitOutcomes (Fin m))) {X' : Pt (SplitOutcomes (Fin m))}
    (hX : decAlignOutcome m (masterL57HdrAt c b t d dc dp (W, some hh) s).2.1 = some X')
    {α : ℝ} (hα : 1 / 2 < α)
    (hZ : IsSplitOutcome α (Set.univ : Set (Fin m)) X') (hm : 217 ≤ m)
    (hmn : m ≤ W.1.length)
    (hnt : 2 ≤ alignRMs ((masterL57Ctx (W, some hh)).1,
      (masterL57HdrAt c b t d dc dp (W, some hh) s).2.1))
    (hLP : VeryLargeK (alignRMs ((masterL57Ctx (W, some hh)).1,
        (masterL57HdrAt c b t d dc dp (W, some hh) s).2.1))
      (maxOrbitLength (decGroup W.1.length (alignPairG1 ((masterL57Ctx (W, some hh)).1,
        (masterL57HdrAt c b t d dc dp (W, some hh) s).2.1))))) :
    MasterHintStepOK n ((W, some hh) : RawMasterSI) V
      (masterL57Hint c b t d dc dp (l57UV e f).1 (l57UV e f).2 e f
        ((((W, some hh) : RawMasterSI), j, s), masterCheckedCall (W.2.2.2.1, V))) := by
  have hC : (masterL57Ops c b t d dc dp e f 0).child ((W, some hh), j, s) =
      some (masterCheckedCall (W.2.2.2.1, V)) := by
    change (if masterL57Guard ((W, some hh) : RawMasterSI) then
      ((masterL57Round c b t d dc dp e f).child (masterL57Enter (W, some hh), j, s)).bind
        (fun J => (topwRawInstance (masterWinCtx (W, some hh), masterL57Read (W, some hh) J)).map
          (fun V => masterCheckedCall (W.2.2.2.1, V))) else none) = _
    rw [if_pos hguard, hc, Option.bind_some, hV]
    rfl
  obtain ⟨-, -, hAgrp, hndW, hltW, hwfW, hKW, u, hu, hwinW⟩ :=
    masterL57_dom_call hx hgs hnd hlt hinv hT hG1 hinvD htail hs hC
  have hT' := hT
  simp only [masterL57HintTest, Bool.and_eq_true, decide_eq_true_eq] at hT'
  have hbig : 2 * W.1.length < 3 * (masterCheckedCall (W.2.2.2.1, V)).1.1.length := hT'.2
  have hhd : alignRHasDom (alignRColorOf ((masterL57Ctx (W, some hh)).1,
      (masterL57HdrAt c b t d dc dp (W, some hh) s).2.1)) = true :=
    alignRHasDom_of_large hT'.1.2
  obtain ⟨hgood, hlen, hhalf, hlab⟩ := alignDomHintAt_good_alpha (Δ := W.1) (gN := W.2.1) hnd hlt hinv
    hAgrp hA hG hϕ hvl ht hK hX hα hZ hm hmn hhd hnt hLP hndW hltW hwfW hKW hu hwinW hbig
  have hmA : hh.1.1.length = m := by
    have h := hA.2.1
    change (List.range hh.1.1.length).length = m at h
    rwa [List.length_range] at h
  have hΔn : W.1.length ≤ n := length_le_of_nodup_lt hnd hlt
  unfold masterL57Hint
  rw [if_pos hT]
  refine ⟨hgood, fun i hi => by have := hlab i hi; omega, ?_⟩
  change 2 * (alignDomHintAt ((((masterL57Ctx (W, some hh)).1,
    (masterL57HdrAt c b t d dc dp (W, some hh) s).2.1), W.1),
      (masterCheckedCall (W.2.2.2.1, V)).1)).1.1.length ≤ hh.1.1.length
  rw [hlen, hmA]
  exact hhalf

/-- §14.1, line 11, case 3, at lines 5–7 of the Master: **the hinted branch of the step
condition `Algo.MasterHintStepOK` for the hint routine `Algo.masterL57Hint`.** At a call of the
round of lines 5–7 (`hc`, `hV`) to which the routine attaches a hint (its test holds, `hT`),
the hint has its meaning for the lifted call, its points are below `n`, and its parameter is
at most half the node's (Eq. (73)). The hypotheses on the Master side are those of
`Algo.alignDomHintAt_good` for the action `A` of the context of lines 5–7
(`Algo.masterL57Ctx`, which the round and the routine read; `Algo.masterL57Ctx_hintFacts`
gives its hint facts at a good node) and the fixed version `o` the round reads, and those of
`Algo.masterL57_dom_call`. -/
theorem masterHintStepOK_masterL57Hint (hx : W.2.2.2.1.length = n) (hgs : RawGens.WF n W.2.1)
    (hnd : W.1.Nodup) (hlt : ∀ u ∈ W.1, u < n)
    (hinv : IsInvariant (decGroup n W.2.1) (winSet n W.1)) {s : AggnL57GState}
    {J : AggnPhaseNode} {V : RawWinSI}
    (hguard : masterL57Guard ((W, some hh) : RawMasterSI) = true)
    (hc : (masterL57Round c b t d dc dp e f).child (masterL57Enter (W, some hh), j, s) = some J)
    (hV : topwRawInstance (masterWinCtx ((W, some hh) : RawMasterSI), masterL57Read (W, some hh) J) = some V)
    (hT : masterL57HintTest c b t d dc dp (l57UV e f).1 (l57UV e f).2 e f
      ((((W, some hh) : RawMasterSI), j, s), masterCheckedCall (W.2.2.2.1, V)) = true)
    (hG1 : decGroup W.1.length (alignPairG1 ((masterL57HdrAt c b t d dc dp (W, some hh) s).1,
      (masterL57HdrAt c b t d dc dp (W, some hh) s).2.1)) ≤
        decGroup W.1.length (masterL57Ctx (W, some hh)).1.1.2)
    (hinvD : rawIsInvariant (alignPairG1 ((masterL57HdrAt c b t d dc dp (W, some hh) s).1,
      (masterL57HdrAt c b t d dc dp (W, some hh) s).2.1),
        avDomWindow (masterL57HdrAt c b t d dc dp (W, some hh) s)) = true)
    (htail : ∀ S ∈ (alignRWindows (alignRColorOf
      ((masterL57HdrAt c b t d dc dp (W, some hh) s).1,
        (masterL57HdrAt c b t d dc dp (W, some hh) s).2.1))).tail,
      3 * (winSet W.1.length S).ncard ≤ 2 * W.1.length)
    (hs : AVFirstOK (masterL57HdrAt c b t d dc dp (W, some hh) s)
      (s.1.2.getD (l57Init (masterL57HdrAt c b t d dc dp (W, some hh) s))).1)
    {m : ℕ} [MulAction (Perm (Fin m)) (Pt (SplitOutcomes (Fin m)))]
    {ϕ : decGroup W.1.length (masterL57Ctx (W, some hh)).1.1.2 →* Perm (Fin m)}
    (hA : RawAction.WF W.1.length m (masterL57Ctx (W, some hh)).1 ϕ)
    (hG : IsTransitive (decGroup W.1.length (masterL57Ctx (W, some hh)).1.1.2))
    (hϕ : IsGiantRep ϕ)
    (hvl : VeryLargeK m (maxOrbitLength (decGroup W.1.length (masterL57Ctx (W, some hh)).1.1.2)))
    {tt : ℕ} (ht : ∀ u : Fin W.1.length, tPoint ϕ u = tt)
    (hK : IsCatAction (SplitOutcomes (Fin m))) {X' : Pt (SplitOutcomes (Fin m))}
    (hX : decAlignOutcome m (masterL57HdrAt c b t d dc dp (W, some hh) s).2.1 = some X')
    (hZ : IsSplitOutcome (3 / 4 : ℝ) (Set.univ : Set (Fin m)) X') (hm : 217 ≤ m)
    (hmn : m ≤ W.1.length)
    (hnt : 2 ≤ alignRMs ((masterL57Ctx (W, some hh)).1,
      (masterL57HdrAt c b t d dc dp (W, some hh) s).2.1))
    (hLP : VeryLargeK (alignRMs ((masterL57Ctx (W, some hh)).1,
        (masterL57HdrAt c b t d dc dp (W, some hh) s).2.1))
      (maxOrbitLength (decGroup W.1.length (alignPairG1 ((masterL57Ctx (W, some hh)).1,
        (masterL57HdrAt c b t d dc dp (W, some hh) s).2.1))))) :
    MasterHintStepOK n ((W, some hh) : RawMasterSI) V
      (masterL57Hint c b t d dc dp (l57UV e f).1 (l57UV e f).2 e f
        ((((W, some hh) : RawMasterSI), j, s), masterCheckedCall (W.2.2.2.1, V))) :=
  masterHintStepOK_masterL57Hint_alpha hx hgs hnd hlt hinv hguard hc hV hT hG1 hinvD htail hs hA hG
    hϕ hvl ht hK hX (by norm_num) hZ hm hmn hnt hLP

end Step5

end Algo
