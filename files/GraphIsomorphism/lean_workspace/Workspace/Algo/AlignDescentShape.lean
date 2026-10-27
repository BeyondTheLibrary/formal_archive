/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: the loop of case 1 of the repair of §14.1, lines 7–11,
matched against the round of the Master side, `Babai.AlignShape.red`.
-/
import Workspace.Algo.AlignDescentMatch
import Workspace.Algo.AlignDomShape
import Workspace.Algo.AlignDomOrbits

/-!
# Case 1 of lines 7–11 is `Babai.AlignShape.red`

When line 6 found a dominant class `D` and `m*` is small (`¬ D.LargeParam`), the Master's
round is the union over the versions `Y` of the strong descent to `ker ϕ*` over the cosets
`S.domEnum.reps C_Y`, followed by the Chain Rule over the other classes
(`Algo.alignShape_red_of_dom_small`). `Algo.phaseMatch_adShape` shows that a round whose steps
are those of `Workspace/Algo/AlignDescentLoop.lean` walks that tree call for call, and that at
the end its raw accumulator decodes to the answer of the round.

The hypothesis is `Algo.ADDescribes`: the header and the machine's lists describe `S` and
`D`. The Master side fixes `G* = ϕ⁻¹(Aut(X'))` and the window of `D`, but chooses `ker ϕ*`
only through `m*`, which it does not compute, and lists the orbits of `ker ϕ*` and the cosets
in an order it does not compute (`Babai.AlignDominantEnum.Spec`). So the description asks
that the kernel, the orbit list, the other classes and the coset lists of `S` be the ones the
machine computes. Everything else the loop needs (the invariance of the windows, the cover of
each transporter by the cosets) is derived here from `Babai.AlignDominantEnum.Spec`.
-/

namespace Algo
open RAM RAM.Targets Babai Equiv
open scoped Pointwise

private theorem hull_strIso' {Ω A : Type*} [Fintype Ω] [DecidableEq Ω] (K : Subgroup (Perm Ω))
    (x y : Ω → A) :
    cosetHull (strIso (K : Set (Perm Ω)) x y) = strIso (K : Set (Perm Ω)) x y := by
  rcases Set.eq_empty_or_nonempty (strIso (K : Set (Perm Ω)) x y) with h | ⟨σ, hσ⟩
  · rw [h, cosetHull_empty]
  · have hc : ((strAutSubgroup K x : Subgroup (Perm Ω)) : Set (Perm Ω)) =
        strAut (K : Set (Perm Ω)) x := by
      rw [strAutSubgroup, coe_wAutSubgroup, wAut_univ]
    rw [strIso_eq_smul_strAut hσ, ← hc, cosetHull_smul_subgroup]

/-- The header `h` and the machine's lists of case 1 describe the Align shape `S` with the
dominant class `D`, `m*` small: the action, `X'` and the versions decode as in
`Algo.AVDescribes`; `G*` is `ϕ⁻¹(Aut(X'))`; the machine's generators of `ker ϕ*` generate
`D`'s kernel; the orbits of `ker ϕ*` in the window, the other classes and the cosets of
`ker ϕ*` listed for each nonempty transporter are those of `S`; and the round of Procedure
Align is correct. -/
structure ADDescribes (n : ℕ) (h : AVHdr)
    (S : AlignShape (Fin n) ℕ (decGroup n h.1.1.2) (decStrN n h.2.2.2.2.1)
      (decStrN n h.2.2.2.2.2)) (D : AlignDominantRoundData (Fin n)) : Prop where
  dom : S.dom = some D
  small : ¬ D.LargeParam
  head : S.head ∉ S.tail
  gs : D.toAlignDominant.Gs = (letI := S.act; preimageSubgroup S.ϕ (structAut S.X'))
  spec : S.domEnum.Spec D
  ker : decGroup n (adKG h) = D.ker
  kernelOrbits : (adKO h).map (winSet n) = S.domEnum.kernelOrbits
  tail : (adTW h).map (winSet n) = S.tail
  reps : letI := S.act; ∀ k (hk : k < S.versions.length),
    alignTransporter S.ϕ S.X' S.versions[k] ≠ ∅ →
      S.domEnum.reps (alignTransporter S.ϕ S.X' S.versions[k]) = adLk n h k
  koNe : adKO h ≠ []
  koLt : ∀ W ∈ adKO h, ∀ u ∈ W, u < n
  twLt : ∀ W ∈ adTW h, ∀ u ∈ W, u < n
  invTail : letI := S.act;
    ∀ Δ ∈ S.tail, IsInvariant (preimageSubgroup S.ϕ (structAut S.X')) Δ
  action : RawAction.WF n S.m h.1 S.ϕ
  giant : IsGiantRep S.ϕ
  cat : letI := S.act; IsCatAction (SplitOutcomes (Fin S.m))
  fixed : decAlignOutcome S.m h.2.1 = some S.X'
  versions : h.2.2.1.map (decAlignOutcome S.m) = S.versions.map some
  run : S.red.run = strIso ((decGroup n h.1.1.2 : Subgroup (Perm (Fin n))) :
    Set (Perm (Fin n))) (decStrN n h.2.2.2.2.1) (decStrN n h.2.2.2.2.2)

/-- **The orbits of `ker ϕ*` in the window, listed once each** (the clause `kernelOrbits` of
`Babai.AlignDominantEnum.Spec`, for the machine's list `Algo.adKO`). -/
theorem perm_adKO {n : ℕ} {h : AVHdr} (hgs : RawGens.WF n (adKG h))
    (hlt : ∀ j ∈ alignRDomWindow (alignRColorOf (h.1, h.2.1),
      alignRDomColor (alignRColorOf (h.1, h.2.1))), j < n)
    (hinv : rawIsInvariant (adKG h, alignRDomWindow (alignRColorOf (h.1, h.2.1),
      alignRDomColor (alignRColorOf (h.1, h.2.1)))) = true) :
    ((adKO h).map (winSet n)).Perm (orbitListOn (decGroup n (adKG h))
      (winSet n (alignRDomWindow (alignRColorOf (h.1, h.2.1),
        alignRDomColor (alignRColorOf (h.1, h.2.1)))))) :=
  ((perm_alignDomFirst (n, adKO h)).symm.map (winSet n)).trans (perm_alignDomOrbits hgs hlt hinv)

section Phase

variable {ι ω : Type*} {n : ℕ} {R : Round ι ω RawCoset} {decI : ι → SIInstance (Fin n) ℕ}
  {I : ι} {h : AVHdr} {pr : ω → ADState} {emb : RawWinSI → ι} {Good : ℕ → ω → Prop}
  {S : AlignShape (Fin n) ℕ (decGroup n h.1.1.2) (decStrN n h.2.2.2.2.1)
    (decStrN n h.2.2.2.2.2)} {D : AlignDominantRoundData (Fin n)}

/-- §14.1, lines 7–11, **case 1 of the repair on the RAM**: when the header
describes `S` with a dominant class and `m*` small, a round whose child and combine are
`Algo.adChild` and `Algo.adCombine` walks `S.red` call for call from the state `adInit h`,
with at most `Algo.adCalls h` calls, and at the end its raw accumulator decodes to the answer
of the round. -/
theorem phaseMatch_adShape (hD : ADDescribes n h S D)
    (hdec : ∀ W g τ, decI (emb (W, g, τ, h.2.2.2.2.1, h.2.2.2.2.2)) =
      decWinSI n (W, g, τ, h.2.2.2.2.1, h.2.2.2.2.2))
    (hchild : ∀ j s J, Good j s → adChild (h, pr s) = some J →
      R.child (I, j, s) = some (emb J))
    (hcomb : ∀ j s a J, Good j s → adChild (h, pr s) = some J →
      pr (R.combine (I, j, s, a)) = adCombine (h, pr s, a) ∧
        Good (j + 1) (R.combine (I, j, s, a)))
    (hx : h.2.2.2.2.1.length = n)
    (j : ℕ) (s : ω) (hs : pr s = adInit h) (hgs : Good j s) :
    PhaseMatch R decI (decCoset n) I (adCalls h) j s S.red
      (fun b j' s' => Good j' s' ∧ ∃ a, pr s' = ((h.2.2.1.length, 0, none, a), (0, none)) ∧
        decCoset n a = b) := by
  letI := S.act
  set G₁ := preimageSubgroup S.ϕ (structAut S.X') with hG₁
  have hNle : decGroup n (adKG h) ≤ G₁ := by
    rw [hD.ker, hG₁, ← hD.gs]; exact D.ker_le
  have hKOinv : ∀ W ∈ adKO h, IsInvariant (decGroup n (adKG h)) (winSet n W) := by
    intro W hW
    have hmem : winSet n W ∈ S.domEnum.kernelOrbits :=
      hD.kernelOrbits ▸ List.mem_map_of_mem hW
    rw [hD.ker]
    exact isInvariant_of_mem_orbitListOn (hD.spec.kernelOrbits.subset hmem)
  have hUinv : IsInvariant G₁ (⋃ W ∈ (adKO h).map (winSet n), W) := by
    have hU : (⋃ W ∈ (adKO h).map (winSet n), W) = D.toAlignDominant.window := by
      rw [hD.kernelOrbits, ← iUnion_orbitListOn D.isInvariant_window_ker]
      ext u
      simp only [Set.mem_iUnion, exists_prop]
      exact ⟨fun ⟨T, hT, hu⟩ => ⟨T, hD.spec.kernelOrbits.subset hT, hu⟩,
        fun ⟨T, hT, hu⟩ => ⟨T, hD.spec.kernelOrbits.symm.subset hT, hu⟩⟩
    rw [hU, hG₁, ← hD.gs]
    exact D.isInvariant_window
  have hTWinv : ∀ W ∈ adTW h, IsInvariant G₁ (winSet n W) := by
    intro W hW
    exact hD.invTail _ (hD.tail ▸ List.mem_map_of_mem hW)
  have hcover : ∀ k (hk : k < S.versions.length),
      alignTransporter S.ϕ S.X' S.versions[k] ≠ ∅ →
      alignTransporter S.ϕ S.X' S.versions[k] =
        ⋃ σ ∈ adLk n h k, σ • (decGroup n (adKG h) : Set (Perm (Fin n))) := by
    intro k hk hne
    obtain ⟨τ, hτ⟩ := Set.nonempty_iff_ne_empty.2 hne
    have hC := alignTransporter_eq_smul S.ϕ S.X' S.versions[k] ⟨τ, hτ.1⟩ hτ.2
    rw [← hD.reps k hk hne, hD.ker]
    refine hD.spec.cover _ ⟨τ, ?_⟩
    rw [hC, hD.gs]
  have hm := phaseMatch_adVersions (Ys := S.versions) (ϕ := S.ϕ) (X := S.X') hdec hchild hcomb
    hD.action hD.giant hD.cat hD.fixed hD.versions hx hNle hD.koNe hD.koLt hKOinv hUinv
    hD.twLt hTWinv hcover (fun Y => S.domEnum.reps (alignTransporter S.ϕ S.X' Y)) hD.reps
    j s hs hgs
  have hred : S.red = SIReduction.unionOver S.versions fun Y =>
      adBranch (decGroup n (adKG h)) (decStrN n h.2.2.2.2.1) (decStrN n h.2.2.2.2.2)
        ((adKO h).map (winSet n)) ((adTW h).map (winSet n)) (alignTransporter S.ϕ S.X' Y)
        (S.domEnum.reps (alignTransporter S.ϕ S.X' Y)) := by
    rw [alignShape_red_of_dom_small S hD.head hD.dom hD.small, hD.ker, hD.kernelOrbits,
      hD.tail]
    rfl
  rw [hred]
  have hv := aggrPhaseMatch_value hm
  rw [← hred] at hv ⊢
  refine phaseMatch_weaken hv ?_
  rintro b j' s' ⟨⟨hg, a, h1, h2⟩, hb⟩
  refine ⟨hg, a, h1, ?_⟩
  rw [h2, hb, hD.run, hull_strIso']

end Phase

end Algo
