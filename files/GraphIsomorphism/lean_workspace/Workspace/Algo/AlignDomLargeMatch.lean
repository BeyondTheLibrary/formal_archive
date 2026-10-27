/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: Sec. 15, lines 5–7, matched against the Master side when line 6 of
Procedure Align finds a dominant color class and `m*` is large (§14.1, lines 7–11, cases 2
and 3 of the repair).
-/
import Workspace.Algo.AggNodeLine57Match
import Workspace.Algo.AlignDomShape
import Workspace.Algo.AlignDomWindows

/-!
# Lines 5–7 with a dominant class and `m*` large

`Algo.aggnL57_align_match` matches the round of lines 5–7 against `Line57Shape.align S` for
any list `Ws` of windows that the header describes (`Algo.AVDescribes`). This file supplies
that description when `S` has a dominant class (`S.dom = some D`) and `m*` is large
(`D.LargeParam`):

* `Algo.largeParam_iff`: the machine's test `Algo.alignRLarge` is the Master's test
  `D.LargeParam`, once `m*` and `G*` are the same on both sides;
* `Algo.avDescribes_of_domLarge`: the header describes `S` with the windows
  `S.domEnum.orbits ++ S.tail`, the list `Algo.alignShape_red_of_dom_large` rewrites `S.red`
  to.

The Master side fixes `G* = ϕ⁻¹(Aut(X'))` and the window `Ω(Δ_j)` of `D`
(`Babai.Line4cdData.dom_spec`), but not `m*`, and it lists the orbits of `G*` in an order it
does not compute (`Babai.AlignDominantEnum.Spec` asks only for a permutation of the orbits with
a dominant orbit first). So `m*` and the order of the orbits are hypotheses here: the round
matches every `S` whose `m*` is the one the machine computes and whose orbit list is the one
the machine lists. `Algo.perm_alignDomOrbits` and `Algo.alignDomOrbits_first` show that the
machine's list meets `Babai.AlignDominantEnum.Spec`.
-/

namespace Algo
open RAM RAM.Targets Babai Equiv MulAction

section G1

variable {n m : ℕ} {A : RawAction} {ϕ : decGroup n A.1.2 →* Perm (Fin m)}

variable [MulAction (Perm (Fin m)) (Pt (SplitOutcomes (Fin m)))]

/-- §14.1, line 2 (iv): **the machine's `G₁` is `ϕ⁻¹(Aut(X'))`**. -/
theorem decGroup_alignPairG1 (hA : RawAction.WF n m A ϕ) (hgiant : IsGiantRep ϕ)
    (hK : IsCatAction (SplitOutcomes (Fin m))) {o : RawAlignOutcome}
    {Z : Pt (SplitOutcomes (Fin m))} (hz : decAlignOutcome m o = some Z) :
    decGroup n (alignPairG1 (A, o)) = preimageSubgroup ϕ (structAut Z) := by
  have hdm : A.2.1.length = m := hA.2.1
  rcases decAlignOutcome_cases hz with ⟨P, rfl, rfl⟩ | ⟨J, hJ, rfl, rfl⟩
  · change decGroup n (alignG1 (A, cpNorm (A.2.1, P))) = _
    rw [decGroup_alignG1_raw hA hgiant (cpNorm_length hdm P),
      ← decAlignPartition_cpNorm hdm P, structAut_decAlignPartition hK]
  · change decGroup n (alignJG1 (A, J)) = _
    rw [decGroup_alignJG1_raw hA hgiant hJ, structAut_decAlignJohnson hK hJ]

end G1

/-- §14.1, lines 7–11: **the machine's test is the Master's test**: with a
dominant color, `Algo.alignRLarge` holds exactly when `D.LargeParam` does, once the machine's
`m*` is `D`'s and the machine's `G₁` is `D`'s group `G*`. -/
theorem largeParam_iff {n : ℕ} {p : RawAction × RawAlignOutcome}
    {D : AlignDominantRoundData (Fin n)} (hd : p.1.1.1.length = n)
    (hdom : alignRHasDom (alignRColorOf p) = true) (hms : D.toAlignDominant.ms = alignRMs p)
    (hG : decGroup n (alignPairG1 p) = D.toAlignDominant.Gs) :
    D.LargeParam ↔ alignRLarge p = true := by
  obtain ⟨A, o⟩ := p
  rw [alignRLarge_iff (alignPairG1_wf hd) hd, AlignDominantRoundData.LargeParam, hms, hG]
  exact ⟨fun h => ⟨hdom, h⟩, fun h => h.2⟩

/-- In cases 2 and 3 the loop of case 1 does not run. -/
theorem l57Small_false_of_large {h : AVHdr} (hl : alignRLarge (h.1, h.2.1) = true) :
    l57Small h = false := by
  unfold l57Small alignRSmall
  unfold alignRLarge at hl
  rw [Bool.and_eq_false_iff]
  left
  cases hd : alignRHasDom (alignRColorOf (h.1, h.2.1)) <;>
    cases hv : rawVeryLarge (alignRMs (h.1, h.2.1), rawMaxOrbit (alignPairG1 (h.1, h.2.1),
      h.1.1.1)) <;> simp_all

/-- With no dominant class the loop of case 1 does not run. -/
theorem l57Small_false_of_noDom {h : AVHdr}
    (hd : alignRHasDom (alignRColorOf (h.1, h.2.1)) = false) : l57Small h = false := by
  unfold l57Small alignRSmall
  rw [hd, Bool.false_and, Bool.false_and]

/-- §14.1, lines 7–11: **the machine's test of case 1 is the Master's test**:
with a dominant color, `Algo.l57Small` holds exactly when `D.LargeParam` fails, once the
machine's `m*` is `D`'s and the machine's `G₁` is `D`'s group `G*`. -/
theorem l57Small_iff {n : ℕ} {h : AVHdr} {D : AlignDominantRoundData (Fin n)}
    (hd : h.1.1.1.length = n) (hdom : alignRHasDom (alignRColorOf (h.1, h.2.1)) = true)
    (hms : D.toAlignDominant.ms = alignRMs (h.1, h.2.1))
    (hG : decGroup n (alignPairG1 (h.1, h.2.1)) = D.toAlignDominant.Gs)
    (h2 : 2 ≤ alignRMs (h.1, h.2.1)) :
    l57Small h = true ↔ ¬ D.LargeParam := by
  rw [largeParam_iff (p := (h.1, h.2.1)) hd hdom hms hG, l57Small_eq_of_two_le h2]
  unfold alignRSmall alignRLarge
  rw [hdom]
  cases rawVeryLarge (alignRMs (h.1, h.2.1), rawMaxOrbit (alignPairG1 (h.1, h.2.1), h.1.1.1)) <;>
    simp

section Describe

variable {n : ℕ} {h : AVHdr}
  {S : AlignShape (Fin n) ℕ (decGroup n h.1.1.2) (decStrN n h.2.2.2.2.1)
    (decStrN n h.2.2.2.2.2)} {D : AlignDominantRoundData (Fin n)}

/-- §14.1, lines 5–11, **cases 2 and 3 of the repair, described by the header**. When the
header's windows are those of `Algo.alignL57Windows`, the machine's test holds, `S` has the
dominant class `D` with `m*` large, and the orbits and the other classes of `S` are the ones
the machine lists, the header describes `S` with the windows `S.domEnum.orbits ++ S.tail`
(Eq. (71) over the orbits of `G*` in the dominant window, then the other classes). -/
theorem avDescribes_of_domLarge
    (hw : h.2.2.2.1 = alignL57Windows (h.1, h.2.1))
    (hlarge : alignRLarge (h.1, h.2.1) = true)
    (hD : S.dom = some D) (hL : D.LargeParam) (hn : S.head ∉ S.tail)
    (hGs : D.toAlignDominant.Gs = (letI := S.act; preimageSubgroup S.ϕ (structAut S.X')))
    (hG1 : decGroup n (alignPairG1 (h.1, h.2.1)) = D.toAlignDominant.Gs)
    (hwin : winSet n (alignRDomWindow (alignRColorOf (h.1, h.2.1),
      alignRDomColor (alignRColorOf (h.1, h.2.1)))) = D.toAlignDominant.window)
    (hspec : S.domEnum.Spec D)
    (horbits : S.domEnum.orbits = (alignDomOrbits ((alignPairG1 (h.1, h.2.1),
      alignRDomWindow (alignRColorOf (h.1, h.2.1), alignRDomColor (alignRColorOf (h.1, h.2.1)))),
        n)).map (winSet n))
    (htail : (alignRWindows (alignRColorOf (h.1, h.2.1))).tail.map (winSet n) = S.tail)
    (hne : S.domEnum.orbits ++ S.tail ≠ [])
    (hd : h.1.1.1.length = n)
    (hltw : ∀ W ∈ alignRWindows (alignRColorOf (h.1, h.2.1)), ∀ u ∈ W, u < n)
    (haction : RawAction.WF n S.m h.1 S.ϕ) (hgiant : IsGiantRep S.ϕ)
    (hcat : letI := S.act; IsCatAction (SplitOutcomes (Fin S.m)))
    (hfixed : decAlignOutcome S.m h.2.1 = some S.X')
    (hversions : h.2.2.1.map (decAlignOutcome S.m) = S.versions.map some)
    (hinvTail : letI := S.act;
      ∀ Δ ∈ S.tail, IsInvariant (preimageSubgroup S.ϕ (structAut S.X')) Δ)
    (hrun : S.red.run = strIso ((decGroup n h.1.1.2 : Subgroup (Perm (Fin n))) :
      Set (Perm (Fin n))) (decStrN n h.2.2.2.2.1) (decStrN n h.2.2.2.2.2)) :
    AVDescribes n h S (S.domEnum.orbits ++ S.tail) := by
  set p : RawAction × RawAlignOutcome := (h.1, h.2.1) with hp
  set q := alignRColorOf p with hq
  set w := alignRDomWindow (q, alignRDomColor q) with hwdef
  have hdom : alignRHasDom q = true := alignRHasDom_of_large hlarge
  have hwmem : w ∈ alignRWindows q := by
    rw [alignRWindows_eq_cons hdom]; exact List.mem_cons_self
  have hgs : RawGens.WF n (alignPairG1 p) := alignPairG1_wf hd
  have hlt : ∀ j ∈ w, j < n := hltw w hwmem
  have hinv : rawIsInvariant (alignPairG1 p, w) = true := by
    rw [rawIsInvariant_eq_true_iff hgs hlt, hG1]
    have := D.isInvariant_window
    rw [← hwin] at this
    exact this
  have hmemTail : ∀ W ∈ (alignRWindows q).tail, W ∈ alignRWindows q := by
    intro W hW
    rw [alignRWindows_eq_cons hdom]
    exact List.mem_cons_of_mem _ hW
  refine ⟨alignShape_red_of_dom_large S hn hD hL, haction, hgiant, hcat, hfixed, hversions,
    ?_, hne, ?_, ?_, hrun⟩
  · rw [hw, alignL57Windows_of_large hlarge, List.map_append, hd, ← horbits, htail]
  · rw [hw, alignL57Windows_of_large hlarge, hd]
    intro W hW
    rcases List.mem_append.1 hW with hW | hW
    · exact winOrbits_lt hgs hlt hinv ((perm_alignDomFirst _).subset hW)
    · exact hltw W (hmemTail W hW)
  · intro Δ hΔ
    rcases List.mem_append.1 hΔ with hΔ | hΔ
    · have hmem := hspec.orbits.subset hΔ
      have := isInvariant_of_mem_orbitListOn hmem
      rw [hGs] at this
      exact this
    · exact hinvTail Δ hΔ

end Describe

end Algo
