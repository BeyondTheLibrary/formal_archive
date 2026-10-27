/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: Procedure Align, lines 5–11 (§14.1) — the list of
windows of the round in cases 2 and 3 of the repair, where the round on the dominant window
is the Chain Rule over the orbits of `G*`.
-/
import Workspace.Algo.AlignDomOrbits
import Workspace.Algo.AlignPairCoset
import Workspace.Algo.AlignOutcomeLab
import Workspace.Algo.AlignColorRaw

/-!
# The windows of Procedure Align, with the orbits of `G*` on the dominant window

Line 6 of Procedure Align looks for a dominant color class `Δ_j` of the coloring of `X'`.
When there is one, lines 7–11 (as repaired in the corrected paper) replace the call on the window
`Ω(Δ_j)` by a round that depends on the size of `m* = |Γ*|`:

* cases 2 and 3 (`m*` large, `Babai.VeryLargeK m* L` with `L` the longest orbit of `G*`):
  the Chain Rule over the orbits of `G*` inside `Ω(Δ_j)`, a dominant orbit first;
* case 1 (`m*` small): the strong descent to `ker ϕ*` (not handled in this file).

In cases 2 and 3 the round of one version is the plain Chain Rule of Eq. (71) over a longer
list of windows: the orbits of `G*` in `Ω(Δ_j)`, then the other color classes
(`Algo.alignShape_red_of_dom_large`). This file computes that list.

* `Algo.alignRMs` computes `m*`: in case (A) of line 7 (an equipartition of `Δ_j`), the
  number of blocks, `|Δ_j|` divided by the common block size; in case (B) (a Johnson scheme
  on `Δ_j`), the degree of the scheme.
* `Algo.alignRLarge` is the test of the repair: a dominant color exists and
  `Babai.VeryLargeK m* L` holds.
* `Algo.alignL57Windows` is the list of windows: `Algo.alignRWindows` unless the test holds,
  and otherwise the orbits of `G*` in the dominant window (`Algo.alignDomOrbits`) followed by
  the other classes.
-/

namespace Algo
open RAM RAM.Targets Babai Equiv MulAction

/-- The coloring data of line 4 for the fixed version: the action and the labels of `Γ`. -/
def alignRColorOf (p : RawAction × RawAlignOutcome) : RawAction × RawLab :=
  (p.1, alignOutcomeLab (p.1.2.1, p.2))

/-- §14.1, **line 7: `m* = |Γ*|`**. In case (A) the dominant class is a union of blocks of
equal size, so the number of blocks is the size of the class divided by the size of the block
of any of its points; in case (B) it is the degree of the Johnson scheme. -/
def alignRMs (p : RawAction × RawAlignOutcome) : ℕ :=
  p.2.1.elim (p.2.2.elim 0 rawJDeg) (fun P =>
    (alignRDomPoints (alignRColorOf p)).length /
      cpBlockSize ((p.1.2.1, P), (alignRDomPoints (alignRColorOf p)).getD 0 0))

/-- §14.1, lines 7–11, **the test of the repair**: line 6 found a dominant
color, and `m*` is large for `G* = ϕ⁻¹(Aut(X'))`, that is `Babai.VeryLargeK m* L` with `L`
the length of a longest orbit of `G*`. -/
def alignRLarge (p : RawAction × RawAlignOutcome) : Bool :=
  alignRHasDom (alignRColorOf p) &&
    rawVeryLarge (alignRMs p, rawMaxOrbit (alignPairG1 p, p.1.1.1))

/-- §14.1, **lines 5–11, the windows of the round**. Without the test of the repair they are
the windows of lines 5 and 6 (`Algo.alignRWindows`); with it, the dominant window is replaced
by the orbits of `G*` inside it, a dominant orbit first. -/
def alignL57Windows (p : RawAction × RawAlignOutcome) : List (List ℕ) :=
  if alignRLarge p then
    alignDomOrbits ((alignPairG1 p,
        alignRDomWindow (alignRColorOf p, alignRDomColor (alignRColorOf p))), p.1.1.1.length) ++
      (alignRWindows (alignRColorOf p)).tail
  else alignRWindows (alignRColorOf p)

/-! ## The list, read -/

theorem alignL57Windows_of_not {p : RawAction × RawAlignOutcome} (h : alignRLarge p = false) :
    alignL57Windows p = alignRWindows (alignRColorOf p) := by
  rw [alignL57Windows, if_neg (by rw [h]; exact Bool.false_ne_true)]

theorem alignL57Windows_of_large {p : RawAction × RawAlignOutcome} (h : alignRLarge p = true) :
    alignL57Windows p = alignDomOrbits ((alignPairG1 p,
        alignRDomWindow (alignRColorOf p, alignRDomColor (alignRColorOf p))), p.1.1.1.length) ++
      (alignRWindows (alignRColorOf p)).tail := by
  rw [alignL57Windows, if_pos h]

theorem alignRHasDom_of_large {p : RawAction × RawAlignOutcome} (h : alignRLarge p = true) :
    alignRHasDom (alignRColorOf p) = true := by
  rw [alignRLarge, Bool.and_eq_true] at h
  exact h.1

/-- With a dominant color, the windows of lines 5 and 6 are the dominant window and the rest. -/
theorem alignRWindows_eq_cons {q : RawAction × RawLab} (h : alignRHasDom q = true) :
    alignRWindows q = alignRDomWindow (q, alignRDomColor q) :: (alignRWindows q).tail := by
  rw [alignRWindows, if_pos h]
  rfl

/-- **The test, read.** With `G* = decGroup n (alignPairG1 p)` and `m* = alignRMs p`, the
test holds exactly when line 6 found a dominant color and `Babai.VeryLargeK m* L` holds for
the longest orbit `L` of `G*`. -/
theorem alignRLarge_iff {n : ℕ} {p : RawAction × RawAlignOutcome}
    (hgs : RawGens.WF n (alignPairG1 p)) (hd : p.1.1.1.length = n) :
    alignRLarge p = true ↔ alignRHasDom (alignRColorOf p) = true ∧
      VeryLargeK (alignRMs p) (maxOrbitLength (decGroup n (alignPairG1 p))) := by
  rw [alignRLarge, Bool.and_eq_true, ← rawMaxOrbit_eq hgs hd, rawVeryLarge_iff]

/-- The generators of `G₁ = ϕ⁻¹(Aut(X'))` are permutations of `Ω`. -/
theorem alignPairG1_wf {n : ℕ} {A : RawAction} {o : RawAlignOutcome} (hd : A.1.1.length = n) :
    RawGens.WF n (alignPairG1 (A, o)) := by
  rcases o with ⟨_ | P, _ | J⟩
  · intro g hg; simp [alignPairG1] at hg
  · exact (alignJG1_wf (p := (A, J)) hd).1
  · exact (alignG1_wf (p := (A, cpNorm (A.2.1, P))) hd).1
  · exact (alignG1_wf (p := (A, cpNorm (A.2.1, P))) hd).1

section Decode

variable {n : ℕ} {p : RawAction × RawAlignOutcome}

/-- **The windows of the round in cases 2 and 3, decoded**: the orbits of `G*` inside the
dominant window, a dominant orbit first, then the other classes. -/
theorem map_winSet_alignL57Windows_of_large (h : alignRLarge p = true)
    (hgs : RawGens.WF n (alignPairG1 p)) (hd : p.1.1.1.length = n)
    (hlt : ∀ j ∈ alignRDomWindow (alignRColorOf p, alignRDomColor (alignRColorOf p)), j < n)
    (hinv : rawIsInvariant (alignPairG1 p,
      alignRDomWindow (alignRColorOf p, alignRDomColor (alignRColorOf p))) = true) :
    ∃ O : List (Set (Fin n)),
      (alignL57Windows p).map (winSet n) = O ++ (alignRWindows (alignRColorOf p)).tail.map
        (winSet n) ∧
      O.Perm (orbitListOn (decGroup n (alignPairG1 p))
        (winSet n (alignRDomWindow (alignRColorOf p, alignRDomColor (alignRColorOf p))))) ∧
      (∀ S ∈ O, 2 * n < 3 * S.ncard → ∃ rest, O = S :: rest ∧ S ∉ rest) := by
  refine ⟨(alignDomOrbits ((alignPairG1 p,
    alignRDomWindow (alignRColorOf p, alignRDomColor (alignRColorOf p))), n)).map (winSet n),
    ?_, perm_alignDomOrbits hgs hlt hinv, alignDomOrbits_first hgs hlt hinv⟩
  rw [alignL57Windows_of_large h, List.map_append, hd]

end Decode

/-! ## Running time -/

private theorem pfst {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {f : α → β × γ}
    (h : PolyFun f) : PolyFun (fun a => (f a).1) := h.comp polyFun_fst
private theorem psnd {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {f : α → β × γ}
    (h : PolyFun f) : PolyFun (fun a => (f a).2) := h.comp polyFun_snd
private theorem pelim {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {f : α → Option β}
    {g : α → γ} {h : β × α → γ} (hf : PolyFun f) (hg : PolyFun g) (hh : PolyFun h) :
    PolyFun (fun a => (f a).elim (g a) (fun b => h (b, a))) :=
  (hf.pair polyFun_id).comp (PolyFun.optionElim hg hh)

theorem polyFun_alignRColorOf : PolyFun alignRColorOf := by
  have i : PolyFun (fun p : RawAction × RawAlignOutcome => p) := polyFun_id
  exact (pfst i).pair (((pfst (psnd (pfst i))).pair (psnd i)).comp
    polyFun_alignOutcomeLab)

set_option maxHeartbeats 1000000 in
theorem polyFun_alignRMs : PolyFun alignRMs := by
  let T := RawAction × RawAlignOutcome
  have i0 : PolyFun (fun p : T => p) := polyFun_id
  have hJ : PolyFun (fun p : T => p.2.2.elim 0 rawJDeg) :=
    (pelim (psnd (psnd i0)) (polyFun_const 0) (polyFun_fst.comp polyFun_rawJDeg)).of_eq
      (fun p => by cases p.2.2 <;> rfl)
  have i : PolyFun (fun r : RawColPart × T => r) := polyFun_id
  have hpts : PolyFun (fun r : RawColPart × T => alignRDomPoints (alignRColorOf r.2)) :=
    ((psnd i).comp polyFun_alignRColorOf).comp polyFun_alignRDomPoints
  have hbs : PolyFun (fun r : RawColPart × T =>
      cpBlockSize ((r.2.1.2.1, r.1), (alignRDomPoints (alignRColorOf r.2)).getD 0 0)) :=
    ((((pfst (psnd (pfst (psnd i)))).pair (pfst i)).pair
      ((hpts.pair (polyFun_const 0)).comp polyFun_rawGet)).comp
      polyFun_cpBlockSize).of_eq (fun _ => rfl)
  exact pelim (pfst (psnd i0)) hJ ((hpts.comp polyFun_length).div hbs)

theorem polyFun_alignRLarge : PolyFun alignRLarge := by
  have i : PolyFun (fun p : RawAction × RawAlignOutcome => p) := polyFun_id
  have h1 := polyFun_alignRColorOf.comp polyFun_alignRHasDom
  have h2 : PolyFun (fun p : RawAction × RawAlignOutcome =>
      rawVeryLarge (alignRMs p, rawMaxOrbit (alignPairG1 p, p.1.1.1))) :=
    (polyFun_alignRMs.pair ((polyFun_alignPairG1.pair (pfst (pfst (pfst i)))).comp
      polyFun_rawMaxOrbit)).comp polyFun_rawVeryLarge
  exact polyFun_and h1 h2

set_option maxHeartbeats 1000000 in
theorem polyFun_alignL57Windows : PolyFun alignL57Windows := by
  have i : PolyFun (fun p : RawAction × RawAlignOutcome => p) := polyFun_id
  have hq := polyFun_alignRColorOf
  have hwin : PolyFun (fun p : RawAction × RawAlignOutcome =>
      alignRDomWindow (alignRColorOf p, alignRDomColor (alignRColorOf p))) :=
    (hq.pair (hq.comp polyFun_alignRDomColor)).comp polyFun_alignRDomWindow
  have hn : PolyFun (fun p : RawAction × RawAlignOutcome => p.1.1.1.length) :=
    (pfst (pfst (pfst i))).comp polyFun_length
  have hdo : PolyFun (fun p : RawAction × RawAlignOutcome =>
      alignDomOrbits ((alignPairG1 p,
        alignRDomWindow (alignRColorOf p, alignRDomColor (alignRColorOf p))), p.1.1.1.length)) :=
    ((polyFun_alignPairG1.pair hwin).pair hn).comp polyFun_alignDomOrbits
  have hws := hq.comp polyFun_alignRWindows
  exact (PolyFun.ite polyFun_alignRLarge ((hdo.pair (hws.comp polyFun_tail)).comp polyFun_append)
    hws).of_eq (fun p => by
      by_cases h : alignRLarge p = true <;> simp [alignL57Windows, h])

end Algo
