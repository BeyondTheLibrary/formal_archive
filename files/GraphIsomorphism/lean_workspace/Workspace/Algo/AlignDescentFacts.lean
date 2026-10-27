/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: the small hypotheses of `Algo.ADDescribes` (§14.1, lines 7–11, case 1
of the repair) proved from the header.
-/
import Workspace.Algo.AlignDescentShape
import Workspace.Algo.AggNodeLine57Round

/-!
# The machine's lists of case 1 are well formed

`Algo.ADDescribes` asks four facts of the machine's lists that do not involve the Master's
choices:

* `koNe`: the orbits of `ker ϕ*` in the dominant window are not an empty list. This holds as
  soon as the window has a point (`Algo.adKO_ne_nil`); the Master side takes the same fact
  about its window as a hypothesis (`Workspace/Master/Line4cdCore.lean`), and
  `Algo.adKO_ne_nil_of_window` reads it from there;
* `koLt`: every point of an orbit of `ker ϕ*` is below `n` (`Algo.adKO_lt`);
* `twLt`: every point of an other color class is below `n` (`Algo.adTW_lt`), when the header's
  windows are those of the round of lines 5–7 and `m*` is small.

`Algo.ADDescribes.mk'` builds the description from the remaining fields.
-/

namespace Algo
open RAM RAM.Targets Babai Equiv

variable {n : ℕ} {h : AVHdr}

/-- The dominant window of the header. -/
def adWindow (h : AVHdr) : List ℕ :=
  alignRDomWindow (alignRColorOf (h.1, h.2.1), alignRDomColor (alignRColorOf (h.1, h.2.1)))

theorem adWindow_lt (hd : h.1.1.1.length = n) {u : ℕ} (hu : u ∈ adWindow h) : u < n := by
  have := (mem_alignRDomWindow.1 hu).1
  rw [← hd]
  exact this

/-- **Every point of an orbit of `ker ϕ*` is a point of `Ω`.** -/
theorem adKO_lt (hd : h.1.1.1.length = n) : ∀ W ∈ adKO h, ∀ u ∈ W, u < n := by
  intro W hW u hu
  have hgs : RawGens.WF n (adKG h) := alignKerGens_wf hd h.2.1
  obtain ⟨j, hj, rfl⟩ := winOrbits_mem hW
  exact ((mem_rawOrbit_iff hgs (adWindow_lt hd hj) u).1 hu).1

/-- **A window with a point has an orbit.** The orbits of `ker ϕ*` cover the window, so they
are not an empty list when the window has a point. -/
theorem adKO_ne_nil (hd : h.1.1.1.length = n) (hne : adWindow h ≠ []) : adKO h ≠ [] := by
  have hgs : RawGens.WF n (adKG h) := alignKerGens_wf hd h.2.1
  obtain ⟨j, hj⟩ := List.exists_mem_of_ne_nil _ hne
  have hc := winOrbits_cover hgs (fun u hu => adWindow_lt hd hu) hj
  intro he
  have he' : winOrbits (adKG h, adWindow h) = [] := he
  rw [he', List.flatten_nil] at hc
  exact List.not_mem_nil hc

/-- The window of the header decoded is the Master's window, and the Master's window is
nonempty: then the orbits of `ker ϕ*` are not an empty list. -/
theorem adKO_ne_nil_of_window (hd : h.1.1.1.length = n) {D : AlignDominantRoundData (Fin n)}
    (hwin : winSet n (adWindow h) = D.toAlignDominant.window)
    (hw : D.toAlignDominant.window.Nonempty) : adKO h ≠ [] := by
  refine adKO_ne_nil hd ?_
  intro he
  obtain ⟨u, hu⟩ := hw
  rw [← hwin, he] at hu
  exact List.not_mem_nil hu

/-- **Every point of an other color class is a point of `Ω`**, when the windows of the header
are those of the round of lines 5–7 and `m*` is not large. -/
theorem adTW_lt (hd : h.1.1.1.length = n) (hw : h.2.2.2.1 = alignL57Windows (h.1, h.2.1))
    (hl : alignRLarge (h.1, h.2.1) = false) : ∀ W ∈ adTW h, ∀ u ∈ W, u < n := by
  intro W hW u hu
  have hW' : W ∈ alignRWindows (alignRColorOf (h.1, h.2.1)) := by
    have : W ∈ h.2.2.2.1.tail := hW
    rw [hw, alignL57Windows_of_not hl] at this
    exact List.mem_of_mem_tail this
  have := lt_of_mem_of_mem_alignRWindows hW' hu
  rw [← hd]
  exact this

/-- In case 1 `m*` is not large. -/
theorem alignRLarge_false_of_l57Small (hs : l57Small h = true) :
    alignRLarge (h.1, h.2.1) = false := by
  have hs := alignRSmall_of_l57Small hs
  unfold alignRSmall at hs
  unfold alignRLarge
  cases hd : alignRHasDom (alignRColorOf (h.1, h.2.1)) <;>
    cases hv : rawVeryLarge (alignRMs (h.1, h.2.1), rawMaxOrbit (alignPairG1 (h.1, h.2.1),
      h.1.1.1)) <;> simp_all

/-- **`Algo.ADDescribes` from the fields that involve the Master's choices**: the small
fields `koNe`, `koLt` and `twLt` are proved from the header, whose windows are those of the
round of lines 5–7 and whose test of case 1 holds, and from the Master's nonempty window. -/
theorem ADDescribes.mk' {S : AlignShape (Fin n) ℕ (decGroup n h.1.1.2) (decStrN n h.2.2.2.2.1)
      (decStrN n h.2.2.2.2.2)} {D : AlignDominantRoundData (Fin n)}
    (hd : h.1.1.1.length = n) (hw : h.2.2.2.1 = alignL57Windows (h.1, h.2.1))
    (hs : l57Small h = true)
    (hwin : winSet n (adWindow h) = D.toAlignDominant.window)
    (hwne : D.toAlignDominant.window.Nonempty)
    (dom : S.dom = some D) (small : ¬ D.LargeParam) (head : S.head ∉ S.tail)
    (gs : D.toAlignDominant.Gs = (letI := S.act; preimageSubgroup S.ϕ (structAut S.X')))
    (spec : S.domEnum.Spec D) (ker : decGroup n (adKG h) = D.ker)
    (kernelOrbits : (adKO h).map (winSet n) = S.domEnum.kernelOrbits)
    (tail : (adTW h).map (winSet n) = S.tail)
    (reps : letI := S.act; ∀ k (hk : k < S.versions.length),
      alignTransporter S.ϕ S.X' S.versions[k] ≠ ∅ →
        S.domEnum.reps (alignTransporter S.ϕ S.X' S.versions[k]) = adLk n h k)
    (invTail : letI := S.act;
      ∀ Δ ∈ S.tail, IsInvariant (preimageSubgroup S.ϕ (structAut S.X')) Δ)
    (action : RawAction.WF n S.m h.1 S.ϕ) (giant : IsGiantRep S.ϕ)
    (cat : letI := S.act; IsCatAction (SplitOutcomes (Fin S.m)))
    (fixed : decAlignOutcome S.m h.2.1 = some S.X')
    (versions : h.2.2.1.map (decAlignOutcome S.m) = S.versions.map some)
    (run : S.red.run = strIso ((decGroup n h.1.1.2 : Subgroup (Perm (Fin n))) :
      Set (Perm (Fin n))) (decStrN n h.2.2.2.2.1) (decStrN n h.2.2.2.2.2)) :
    ADDescribes n h S D :=
  ⟨dom, small, head, gs, spec, ker, kernelOrbits, tail, reps,
    adKO_ne_nil_of_window hd hwin hwne, adKO_lt hd,
    adTW_lt hd hw (alignRLarge_false_of_l57Small hs), invTail, action, giant, cat, fixed,
    versions, run⟩

end Algo
