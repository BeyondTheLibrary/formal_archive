/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: Procedure Align over the versions of `X(y)` (Eq. (71), §14.1) when
line 6 finds a dominant color class and `m*` is small — case 1 of the repair of lines 7–11
 as a phase of a round.
-/
import Workspace.Algo.AlignDomReps
import Workspace.Algo.AlignVersions
import Workspace.Algo.AggNodeCosetCanon

/-!
# Eq. (71) with the strong descent to `ker ϕ*` on the dominant window

For each version `Y` of `X(y)` with a nonempty transporter `C = alignTransporter ϕ X' Y`,
the Master side runs (`Algo.alignShape_red_of_dom_small`)

* the strong descent to `N = ker ϕ*` on the dominant window: for each listed left coset
  `ρ N ⊆ C`, the Chain Rule over the orbits of `N` in the window, and the union of the
  answers (`Babai.strongDescent`);
* then the Chain Rule over the other color classes, started from that union.

This file gives the step functions of that loop.

## The state

`((v, w, cur, acc), (r, racc))`: the version `v`, the window `w` the current chain has
reached, the coset `cur` it has reached, the answer `acc` gathered from the versions before
`v`, the coset `r` of `N` being run (`r` equal to the number of cosets means that the descent
is over and the chain over the other classes runs), and the hull `racc` of the answers of the
cosets before `r`.

The cosets of `N` are those of `Algo.adReps`, taken for the lexicographically least element
of `C` (`Algo.adCanon`), so they depend on the set `C` only.
-/

namespace Algo
open RAM RAM.Targets Babai Equiv
open scoped Pointwise

/-- The state of the loop: the state of `Algo.AVState`, with the index of the coset of
`ker ϕ*` and the hull of the answers of the cosets done so far. -/
abbrev ADState := AVState × ℕ × RawCoset

/-- The orbits of `ker ϕ*` in the dominant window. -/
def adKO (h : AVHdr) : List (List ℕ) := alignKerOrbits (h.1, h.2.1)

/-- The other color classes: the windows of lines 5 and 6 after the dominant one. -/
def adTW (h : AVHdr) : List (List ℕ) := h.2.2.2.1.tail

/-- The generators of `ker ϕ*`. -/
def adKG (h : AVHdr) : RawGens := alignKerGens (h.1, h.2.1)

/-- The number of cosets of `ker ϕ*` listed for a version. -/
def adRN (h : AVHdr) : ℕ := (adRightReps (h.1, h.2.1)).length

/-- The lexicographically least element of the transporter of the version `v`. -/
def adCanon (p : AVHdr × ℕ) : RawPerm :=
  (avTr p).elim [] (fun gt => aggnCanonCoset ((p.1.2.2.2.2.1, gt.1), gt.2))

/-- The coset `ρ_r N` of the version `v`: the start of the chain of the coset `r`. -/
def adBegin (p : AVHdr × ℕ × ℕ) : RawCoset :=
  some (adKG p.1, (adReps ((p.1.1, p.1.2.1), adCanon (p.1, p.2.1))).getD p.2.2 [])

/-- The start of version `k`, with the gathered answer `acc`: the versions with an empty
transporter are skipped, and the chain of the first coset of `N` opens. -/
def adPos (p : AVHdr × ℕ × RawCoset) : ADState :=
  if avNext (p.1, p.2.1) < p.1.2.2.1.length then
    if (adKO p.1).isEmpty then
      ((avNext (p.1, p.2.1), 0, avTr (p.1, avNext (p.1, p.2.1)),
        rawCosetNorm (p.1.2.2.2.2.1, p.2.2)), (adRN p.1, none))
    else
      ((avNext (p.1, p.2.1), 0, adBegin (p.1, avNext (p.1, p.2.1), 0),
        rawCosetNorm (p.1.2.2.2.2.1, p.2.2)), (0, none))
  else ((p.1.2.2.1.length, 0, none, rawCosetNorm (p.1.2.2.2.2.1, p.2.2)), (0, none))

/-- After the descent of the version `v`, with the hull `racc` of its answers: the chain over
the other classes starts from it, or, when it is empty or there are no other classes, the
version is done. -/
def adAfter (p : AVHdr × ℕ × RawCoset × RawCoset) : ADState :=
  if (adTW p.1).isEmpty then
    adPos (p.1, p.2.1 + 1, rawCosetJoin (p.1.2.2.2.2.1, p.2.2.2, p.2.2.1))
  else
    p.2.2.1.elim (adPos (p.1, p.2.1 + 1, p.2.2.2))
      (fun _ => ((p.2.1, 0, rawCosetNorm (p.1.2.2.2.2.1, p.2.2.1), p.2.2.2), (adRN p.1, none)))

/-- The chain of the coset `r` of the version `v` opens, or the descent is over. -/
def adOpen (p : AVHdr × ℕ × ℕ × RawCoset × RawCoset) : ADState :=
  if p.2.2.1 < adRN p.1 then
    ((p.2.1, 0, adBegin (p.1, p.2.1, p.2.2.1), p.2.2.2.2), (p.2.2.1, p.2.2.2.1))
  else adAfter (p.1, p.2.1, p.2.2.2.1, p.2.2.2.2)

/-- The number of windows of the current chain: the orbits of `N` during the descent, the
other classes afterwards. -/
def adSegLen (p : AVHdr × ℕ) : ℕ :=
  if p.2 < adRN p.1 then (adKO p.1).length else (adTW p.1).length

/-- The window `w` of the current chain. -/
def adSegWin (p : AVHdr × ℕ × ℕ) : List ℕ :=
  if p.2.1 < adRN p.1 then (adKO p.1).getD p.2.2 [] else (adTW p.1).getD p.2.2 []

/-- §14.1, lines 5 and 9–11: **the next call**, the window `w` of the current chain with the
coset `cur` it has reached. The window is checked to be invariant under the group of the
coset. -/
def adChild (p : AVHdr × ADState) : Option RawWinSI :=
  p.2.1.2.2.1.bind fun gt =>
    if p.2.1.2.1 < adSegLen (p.1, p.2.2.1) ∧
        rawIsInvariant (tidyGens (p.1.2.2.2.2.1, gt.1),
          adSegWin (p.1, p.2.2.1, p.2.1.2.1)) = true then
      some (adSegWin (p.1, p.2.2.1, p.2.1.2.1), tidyGens (p.1.2.2.2.2.1, gt.1),
        normPerm (p.1.2.2.2.2.1, gt.2), p.1.2.2.2.2.1, p.1.2.2.2.2.2)
    else none

/-- One step after the answer `a` of a call. An empty answer ends the current chain with the
piece `∅`. Otherwise the chain goes on, or it ends: the chain of a coset of `N` adds its
answer to `racc` and the next coset opens; the chain over the other classes adds its answer
to `acc` and the next version starts. -/
def adCombine (p : AVHdr × ADState × RawCoset) : ADState :=
  p.2.2.elim
    (if p.2.1.2.1 < adRN p.1 then
      adOpen (p.1, min p.2.1.1.1 p.1.2.2.1.length, p.2.1.2.1 + 1,
        rawCosetNorm (p.1.2.2.2.2.1, p.2.1.2.2), rawCosetNorm (p.1.2.2.2.2.1, p.2.1.1.2.2.2))
    else adPos (p.1, min p.2.1.1.1 p.1.2.2.1.length + 1, p.2.1.1.2.2.2))
    fun _ =>
      if p.2.1.1.2.1 + 1 < adSegLen (p.1, p.2.1.2.1) then
        ((min p.2.1.1.1 p.1.2.2.1.length, p.2.1.1.2.1 + 1, rawCosetNorm (p.1.2.2.2.2.1, p.2.2),
          rawCosetNorm (p.1.2.2.2.2.1, p.2.1.1.2.2.2)),
          (min p.2.1.2.1 (adRN p.1), rawCosetNorm (p.1.2.2.2.2.1, p.2.1.2.2)))
      else if p.2.1.2.1 < adRN p.1 then
        adOpen (p.1, min p.2.1.1.1 p.1.2.2.1.length, p.2.1.2.1 + 1,
          rawCosetNorm (p.1.2.2.2.2.1, rawCosetJoin (p.1.2.2.2.2.1, p.2.1.2.2, p.2.2)),
          rawCosetNorm (p.1.2.2.2.2.1, p.2.1.1.2.2.2))
      else adPos (p.1, min p.2.1.1.1 p.1.2.2.1.length + 1,
        rawCosetJoin (p.1.2.2.2.2.1, p.2.1.1.2.2.2, p.2.2))

/-- The state before the first version. -/
def adInit (h : AVHdr) : ADState := adPos (h, 0, none)

/-- The number of calls the loop may make: for each version, one chain over the orbits of
`N` per coset of `N`, and one chain over the other classes. -/
def adCalls (h : AVHdr) : ℕ :=
  h.2.2.1.length * (adRN h * (adKO h).length + (adTW h).length)

/-! ## The skip rule -/

section Next

variable {h : AVHdr}

theorem adPos_skip {k : ℕ} (acc : RawCoset) (hs : avTr (h, k) = none) :
    adPos (h, k, acc) = adPos (h, k + 1, acc) := by
  unfold adPos
  simp only
  rw [avNext_skip hs]

theorem adPos_self {k : ℕ} (acc : RawCoset) (hk : k < h.2.2.1.length)
    (hs : (avTr (h, k)).isSome) (hKO : adKO h ≠ []) :
    adPos (h, k, acc) =
      ((k, 0, adBegin (h, k, 0), rawCosetNorm (h.2.2.2.2.1, acc)), (0, none)) := by
  unfold adPos
  simp only
  rw [avNext_self hk hs, if_pos hk, if_neg (by simpa using hKO)]

theorem adPos_end {k : ℕ} (acc : RawCoset) (hk : h.2.2.1.length ≤ k) :
    adPos (h, k, acc) =
      ((h.2.2.1.length, 0, none, rawCosetNorm (h.2.2.2.2.1, acc)), (0, none)) := by
  unfold adPos
  simp only
  rw [avNext_end hk, if_neg (lt_irrefl _)]

theorem adOpen_lt {v r : ℕ} (racc acc : RawCoset) (hr : r < adRN h) :
    adOpen (h, v, r, racc, acc) = ((v, 0, adBegin (h, v, r), acc), (r, racc)) := by
  rw [adOpen, if_pos hr]

theorem adOpen_ge {v r : ℕ} (racc acc : RawCoset) (hr : adRN h ≤ r) :
    adOpen (h, v, r, racc, acc) = adAfter (h, v, racc, acc) := by
  rw [adOpen, if_neg (Nat.not_lt.2 hr)]

end Next

end Algo
