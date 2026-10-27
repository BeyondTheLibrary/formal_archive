/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: the loop of Procedure Align over the versions (Eq. (71)) matched
against the round of the Master side, `Babai.AlignShape.red`.
-/
import Workspace.Algo.AlignVersions
import Workspace.Algo.AggNodeRejectMatch

/-!
# The loop over the versions is `Babai.AlignShape.red`

`Babai.AlignShape.red` is the round of Procedure Align on the Master side (§14.1 and
§15, lines 4d and 7a): the branching over the versions of `X(y)` (Eq. (71)), lines 1–3 on each
pair of versions, the Chain Rule of line 5 over the color classes with the window of line 6
first, and the round of lines 7–11 on that window when line 6 found a dominant color class.

When line 6 found no dominant color class, lines 7–11 do not run, and the round is
`Babai.cosetDesignAlign` over the listed windows (`Algo.alignShape_red_of_dom_none`). This is
exactly the tree the loop of `Workspace/Algo/AlignVersions.lean` walks. So any round whose
child and combine are the step functions of that loop matches `S.red`
(`Algo.phaseMatch_alignShape`), and at the end its raw accumulator decodes to the answer of
the round (`Algo.phaseMatch_alignShape_value`): the loop gathers the coset hull of the union
of Eq. (71), and that union is the coset `Iso_G(x,y)` or empty.

The dominant case (lines 7–11) is not on the RAM yet.
-/

namespace Algo
open RAM RAM.Targets Babai Equiv

/-- §14.1, lines 6–11: **with no dominant color class there is no expansion.** Line 6 found
no dominant class, so lines 7–11 do not run, and the round of Procedure Align is the union of
Eq. (71) over the versions, each followed by the Chain Rule over the listed windows. -/
theorem alignShape_red_of_dom_none {W : Type} [Fintype W] [DecidableEq W] {A : Type}
    {G : Subgroup (Perm W)} {x y : W → A} (S : AlignShape W A G x y) (hS : S.dom = none) :
    S.red = (letI := S.act; cosetDesignAlign S.ϕ x y S.X' S.versions (S.head :: S.tail)) := by
  letI := S.act
  change cosetAlignExpand S.ϕ x y S.X' S.versions S.head S.tail S.dominantRound = _
  unfold cosetAlignExpand
  have he : (fun J : SIInstance W A =>
      if J.Δ = S.head then S.dominantRound J else SIReduction.call J SIReduction.done) =
      fun J => SIReduction.call J SIReduction.done := by
    funext J
    have hd : S.dominantRound J = SIReduction.call J SIReduction.done := by
      unfold AlignShape.dominantRound
      rw [hS]
    rw [hd, ite_self]
  rw [he, SIReduction.expand_call_done]

/-- The set of isomorphisms is empty or a coset of `Aut_K(x)`, so it is its own hull (a copy
of `Algo.cosetHull_strIso`, which lives in a file this one does not import). -/
private theorem hull_strIso {Ω A : Type*} [Fintype Ω] [DecidableEq Ω] (K : Subgroup (Perm Ω))
    (x y : Ω → A) :
    cosetHull (strIso (K : Set (Perm Ω)) x y) = strIso (K : Set (Perm Ω)) x y := by
  rcases Set.eq_empty_or_nonempty (strIso (K : Set (Perm Ω)) x y) with h | ⟨σ, hσ⟩
  · rw [h, cosetHull_empty]
  · have hc : ((strAutSubgroup K x : Subgroup (Perm Ω)) : Set (Perm Ω)) =
        strAut (K : Set (Perm Ω)) x := by
      rw [strAutSubgroup, coe_wAutSubgroup, wAut_univ]
    rw [strIso_eq_smul_strAut hσ, ← hc, cosetHull_smul_subgroup]

section Phase

variable {ι ω : Type*} {n : ℕ} {R : Round ι ω RawCoset} {decI : ι → SIInstance (Fin n) ℕ}
  {I : ι} {h : AVHdr} {pr : ω → AVState} {emb : RawWinSI → ι} {Good : ℕ → ω → Prop}
  (S : AlignShape (Fin n) ℕ (decGroup n h.1.1.2) (decStrN n h.2.2.2.2.1)
    (decStrN n h.2.2.2.2.2))

/-- §14.1 and Eq. (71), **the loop over the versions walks the Master's round** whenever
that round is the union of Eq. (71) over the versions with the Chain Rule over a list `Ws`
of windows (`Babai.cosetDesignAlign`), provided the raw header describes the data: the action
is `S.ϕ`, the fixed version of `X(x)` decodes to `S.X'`, the versions of `X(y)` decode to
`S.versions` in their order, and the windows decode to `Ws`. -/
theorem phaseMatch_alignShape_of (Ws : List (Set (Fin n)))
    (hred : S.red = (letI := S.act; cosetDesignAlign S.ϕ (decStrN n h.2.2.2.2.1)
      (decStrN n h.2.2.2.2.2) S.X' S.versions Ws))
    (hdec : ∀ W g τ, decI (emb (W, g, τ, h.2.2.2.2.1, h.2.2.2.2.2)) =
      decWinSI n (W, g, τ, h.2.2.2.2.1, h.2.2.2.2.2))
    (hchild : ∀ j s J, Good j s → avChild (h, pr s) = some J →
      R.child (I, j, s) = some (emb J))
    (hcomb : ∀ j s a J, Good j s → avChild (h, pr s) = some J →
      pr (R.combine (I, j, s, a)) = avCombine (h, pr s, a) ∧ Good (j + 1) (R.combine (I, j, s, a)))
    (hA : RawAction.WF n S.m h.1 S.ϕ) (hgiant : IsGiantRep S.ϕ)
    (hK : letI := S.act; IsCatAction (SplitOutcomes (Fin S.m)))
    (hX : decAlignOutcome S.m h.2.1 = some S.X')
    (hYs : h.2.2.1.map (decAlignOutcome S.m) = S.versions.map some)
    (hwins : h.2.2.2.1.map (winSet n) = Ws) (hws : Ws ≠ [])
    (hx : h.2.2.2.2.1.length = n)
    (hlt : ∀ W ∈ h.2.2.2.1, ∀ u ∈ W, u < n)
    (hinv : letI := S.act;
      ∀ Δ ∈ Ws, IsInvariant (preimageSubgroup S.ϕ (structAut S.X')) Δ)
    (j : ℕ) (s : ω) (hs : pr s = avInit h) (hgs : Good j s) :
    PhaseMatch R decI (decCoset n) I (S.versions.length * h.2.2.2.1.length) j s S.red
      (fun b j' s' => Good j' s' ∧ ∃ a, pr s' = (h.2.2.1.length, 0, none, a) ∧
        decCoset n a = cosetHull b) := by
  letI := S.act
  have hws' : h.2.2.2.1 ≠ [] := by
    intro he
    rw [he, List.map_nil] at hwins
    exact hws hwins.symm
  have hinv' : ∀ W ∈ h.2.2.2.1,
      IsInvariant (preimageSubgroup S.ϕ (structAut S.X')) (winSet n W) := by
    intro W hW
    exact hinv _ (hwins ▸ List.mem_map_of_mem hW)
  rw [hred, ← hwins]
  exact phaseMatch_alignVersions hdec hchild hcomb hA hgiant hK hX hYs hx hws' hlt hinv' j s hs hgs

/-- The value at the end, in the setting of `Algo.phaseMatch_alignShape_of`: if the round of
Procedure Align is correct, the raw accumulator the loop ends with decodes to its answer. -/
theorem phaseMatch_alignShape_value_of (Ws : List (Set (Fin n)))
    (hred : S.red = (letI := S.act; cosetDesignAlign S.ϕ (decStrN n h.2.2.2.2.1)
      (decStrN n h.2.2.2.2.2) S.X' S.versions Ws))
    (hdec : ∀ W g τ, decI (emb (W, g, τ, h.2.2.2.2.1, h.2.2.2.2.2)) =
      decWinSI n (W, g, τ, h.2.2.2.2.1, h.2.2.2.2.2))
    (hchild : ∀ j s J, Good j s → avChild (h, pr s) = some J →
      R.child (I, j, s) = some (emb J))
    (hcomb : ∀ j s a J, Good j s → avChild (h, pr s) = some J →
      pr (R.combine (I, j, s, a)) = avCombine (h, pr s, a) ∧ Good (j + 1) (R.combine (I, j, s, a)))
    (hA : RawAction.WF n S.m h.1 S.ϕ) (hgiant : IsGiantRep S.ϕ)
    (hK : letI := S.act; IsCatAction (SplitOutcomes (Fin S.m)))
    (hX : decAlignOutcome S.m h.2.1 = some S.X')
    (hYs : h.2.2.1.map (decAlignOutcome S.m) = S.versions.map some)
    (hwins : h.2.2.2.1.map (winSet n) = Ws) (hws : Ws ≠ [])
    (hx : h.2.2.2.2.1.length = n)
    (hlt : ∀ W ∈ h.2.2.2.1, ∀ u ∈ W, u < n)
    (hinv : letI := S.act;
      ∀ Δ ∈ Ws, IsInvariant (preimageSubgroup S.ϕ (structAut S.X')) Δ)
    (hrun : S.red.run = strIso ((decGroup n h.1.1.2 : Subgroup (Perm (Fin n))) :
      Set (Perm (Fin n))) (decStrN n h.2.2.2.2.1) (decStrN n h.2.2.2.2.2))
    (j : ℕ) (s : ω) (hs : pr s = avInit h) (hgs : Good j s) :
    PhaseMatch R decI (decCoset n) I (S.versions.length * h.2.2.2.1.length) j s S.red
      (fun b j' s' => Good j' s' ∧ ∃ a, pr s' = (h.2.2.1.length, 0, none, a) ∧ decCoset n a = b) := by
  have hm := aggrPhaseMatch_value (phaseMatch_alignShape_of S Ws hred hdec hchild hcomb hA hgiant
    hK hX hYs hwins hws hx hlt hinv j s hs hgs)
  refine phaseMatch_weaken hm ?_
  rintro b j' s' ⟨⟨hg, a, h1, h2⟩, hb⟩
  refine ⟨hg, a, h1, ?_⟩
  rw [h2, hb, hrun, hull_strIso]

/-- §14.1 and Eq. (71), **the loop over the versions is the Master's round**: when line 6
found no dominant color class, a round whose child and combine are the step functions of the
loop walks `S.red` call for call, provided the raw header describes `S`. -/
theorem phaseMatch_alignShape (hdom : S.dom = none)
    (hdec : ∀ W g τ, decI (emb (W, g, τ, h.2.2.2.2.1, h.2.2.2.2.2)) =
      decWinSI n (W, g, τ, h.2.2.2.2.1, h.2.2.2.2.2))
    (hchild : ∀ j s J, Good j s → avChild (h, pr s) = some J →
      R.child (I, j, s) = some (emb J))
    (hcomb : ∀ j s a J, Good j s → avChild (h, pr s) = some J →
      pr (R.combine (I, j, s, a)) = avCombine (h, pr s, a) ∧ Good (j + 1) (R.combine (I, j, s, a)))
    (hA : RawAction.WF n S.m h.1 S.ϕ) (hgiant : IsGiantRep S.ϕ)
    (hK : letI := S.act; IsCatAction (SplitOutcomes (Fin S.m)))
    (hX : decAlignOutcome S.m h.2.1 = some S.X')
    (hYs : h.2.2.1.map (decAlignOutcome S.m) = S.versions.map some)
    (hwins : h.2.2.2.1.map (winSet n) = S.head :: S.tail)
    (hx : h.2.2.2.2.1.length = n)
    (hlt : ∀ W ∈ h.2.2.2.1, ∀ u ∈ W, u < n)
    (hinv : letI := S.act;
      ∀ Δ ∈ S.head :: S.tail, IsInvariant (preimageSubgroup S.ϕ (structAut S.X')) Δ)
    (j : ℕ) (s : ω) (hs : pr s = avInit h) (hgs : Good j s) :
    PhaseMatch R decI (decCoset n) I (S.versions.length * h.2.2.2.1.length) j s S.red
      (fun b j' s' => Good j' s' ∧ ∃ a, pr s' = (h.2.2.1.length, 0, none, a) ∧
        decCoset n a = cosetHull b) :=
  phaseMatch_alignShape_of S _ (alignShape_red_of_dom_none S hdom) hdec hchild hcomb hA hgiant
    hK hX hYs hwins (List.cons_ne_nil _ _) hx hlt hinv j s hs hgs

/-- §14.1 and Eq. (71), **the value at the end**, with no dominant color class. -/
theorem phaseMatch_alignShape_value (hdom : S.dom = none)
    (hdec : ∀ W g τ, decI (emb (W, g, τ, h.2.2.2.2.1, h.2.2.2.2.2)) =
      decWinSI n (W, g, τ, h.2.2.2.2.1, h.2.2.2.2.2))
    (hchild : ∀ j s J, Good j s → avChild (h, pr s) = some J →
      R.child (I, j, s) = some (emb J))
    (hcomb : ∀ j s a J, Good j s → avChild (h, pr s) = some J →
      pr (R.combine (I, j, s, a)) = avCombine (h, pr s, a) ∧ Good (j + 1) (R.combine (I, j, s, a)))
    (hA : RawAction.WF n S.m h.1 S.ϕ) (hgiant : IsGiantRep S.ϕ)
    (hK : letI := S.act; IsCatAction (SplitOutcomes (Fin S.m)))
    (hX : decAlignOutcome S.m h.2.1 = some S.X')
    (hYs : h.2.2.1.map (decAlignOutcome S.m) = S.versions.map some)
    (hwins : h.2.2.2.1.map (winSet n) = S.head :: S.tail)
    (hx : h.2.2.2.2.1.length = n)
    (hlt : ∀ W ∈ h.2.2.2.1, ∀ u ∈ W, u < n)
    (hinv : letI := S.act;
      ∀ Δ ∈ S.head :: S.tail, IsInvariant (preimageSubgroup S.ϕ (structAut S.X')) Δ)
    (hrun : S.red.run = strIso ((decGroup n h.1.1.2 : Subgroup (Perm (Fin n))) :
      Set (Perm (Fin n))) (decStrN n h.2.2.2.2.1) (decStrN n h.2.2.2.2.2))
    (j : ℕ) (s : ω) (hs : pr s = avInit h) (hgs : Good j s) :
    PhaseMatch R decI (decCoset n) I (S.versions.length * h.2.2.2.1.length) j s S.red
      (fun b j' s' => Good j' s' ∧ ∃ a, pr s' = (h.2.2.1.length, 0, none, a) ∧ decCoset n a = b) :=
  phaseMatch_alignShape_value_of S _ (alignShape_red_of_dom_none S hdom) hdec hchild hcomb hA
    hgiant hK hX hYs hwins (List.cons_ne_nil _ _) hx hlt hinv hrun j s hs hgs

end Phase

end Algo
