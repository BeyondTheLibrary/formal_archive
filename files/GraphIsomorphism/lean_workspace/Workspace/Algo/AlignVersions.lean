/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: Procedure Align (§14.1) over all versions of `X(y)`, Eq. (71), as a
phase of a round.
-/
import Workspace.Algo.AlignPairCoset
import Workspace.Algo.PhaseUnion
import Workspace.Algo.Descent

/-!
# Eq. (71): Procedure Align over the versions of `X(y)`

> `Iso_G(x,y) = ⋃_{Y} Iso_{G}(x,y) ∩ {τ : X'^{ϕ(τ)} = Y}`,  (71)

where `X'` is a fixed version of `X(x)` and `Y` runs over the versions of `X(y)`. For each
pair `(X', Y)` Procedure Align runs lines 1–3 (`Algo.alignPairCoset`) and then the Chain Rule
of line 5 over the color classes of `Ω`. In coset form this is
`Babai.cosetDesignAlign ϕ x y X' versions windows`, a union over the versions of
`Babai.cosetChain` started from the transporter `Babai.alignTransporter ϕ X' Y`.

This file gives the step functions of that loop and proves that **any** round whose child and
combine are these step functions, read through a projection of its state on the states of a
predicate `Good` of the index and the state that every call keeps, walks the tree of
`Babai.cosetDesignAlign` call for call (`Algo.phaseMatch_alignVersions`). The round of
Sec. 15, lines 5–7 is such a round after the two phases of AggregateCertificates.

## The state

`(v, w, cur, acc)`: the version `v` being aligned, the window `w` of line 5 the chain has
reached, the coset `cur` the chain has reached, and the answer `acc` gathered from the versions
before `v`. A version whose transporter is empty makes no call (line 1 rejects, and
`Babai.cosetChain` stops at `∅`), so the machine skips it without a call: `Algo.avNext` is the
next version with a nonempty transporter.

The answers of the versions are gathered with `Algo.rawCosetJoin`, the smallest coset
containing both (§11.1). That is not the union of two cosets, but the union of *all* the
pieces of Eq. (71) is `Iso_G(x,y)`, which is empty or a coset, so the join of all of them is
their union (`Algo.cosetHull_hull_union`, `Workspace/Algo/Descent.lean`, and the final read-off in the users of this file).

## Main results

* `Algo.avNext_self`, `Algo.avNext_skip`, `Algo.avNext_end` — the skip rule;
* `Algo.phaseMatch_alignVersions` — **the link**: the fold walks `Babai.cosetDesignAlign`.
-/

namespace Algo
open RAM RAM.Targets Babai Equiv
open scoped Pointwise

/-- The fixed data of Eq. (71): the raw action `(G, ϕ)`, the fixed version `X'` of `X(x)`,
the versions of `X(y)`, the color classes of `Ω` in the order of line 6, and the two strings. -/
abbrev AVHdr := RawAction × RawAlignOutcome × List RawAlignOutcome × List (List ℕ) ×
  RawStr × RawStr

/-- The state of the loop: version, window, current coset, gathered answer. -/
abbrev AVState := ℕ × ℕ × RawCoset × RawCoset

/-- A raw coset with its generators shortened and its representative normalized, for the
domain of the first string. Every coset the loop keeps is stored in this form, so that its
state stays small. -/
def rawCosetNorm (p : RawStr × RawCoset) : RawCoset :=
  p.2.map fun q => (tidyGens (p.1, q.1), normPerm (p.1, q.2))

theorem decCoset_rawCosetNorm {n : ℕ} {x : RawStr} (hx : x.length = n) (a : RawCoset) :
    decCoset n (rawCosetNorm (x, a)) = decCoset n a := by
  rcases a with _ | ⟨g, τ⟩
  · rfl
  · simp only [rawCosetNorm, Option.map_some, decCoset_some, decGroup_tidyGens hx,
      decPerm_normPerm hx]

/-- Lines 1–3 for the version with index `i` (`none` past the end of the list). -/
def avTr (p : AVHdr × ℕ) : RawCoset :=
  rawCosetNorm (p.1.2.2.2.2.1, alignPairCoset (p.1.1, p.1.2.1, p.1.2.2.1.getD p.2 (none, none)))

/-- The first version with index `≥ k` whose transporter is not empty, or the number of
versions when there is none. -/
def avNext (p : AVHdr × ℕ) : ℕ :=
  ((List.range p.1.2.2.1.length).filter
    (fun i => decide (p.2 ≤ i) && (avTr (p.1, i)).isSome)).headD p.1.2.2.1.length

/-- The state at the start of version `k`, with the gathered answer `acc`: the versions with
an empty transporter are skipped. -/
def avPos (p : AVHdr × ℕ × RawCoset) : AVState :=
  (avNext (p.1, p.2.1), 0, avTr (p.1, avNext (p.1, p.2.1)), rawCosetNorm (p.1.2.2.2.2.1, p.2.2))

/-- §14.1, **line 5**: the next call, the window `w` with the coset `cur` the chain has
reached. The window is checked to be invariant under the group of the coset, as in
`Algo.alignChild`. -/
def avChild (p : AVHdr × AVState) : Option RawWinSI :=
  p.2.2.2.1.bind fun gt =>
    if p.2.2.1 < p.1.2.2.2.1.length ∧
        rawIsInvariant (tidyGens (p.1.2.2.2.2.1, gt.1), p.1.2.2.2.1.getD p.2.2.1 []) = true then
      some (p.1.2.2.2.1.getD p.2.2.1 [], tidyGens (p.1.2.2.2.2.1, gt.1),
        normPerm (p.1.2.2.2.2.1, gt.2), p.1.2.2.2.2.1, p.1.2.2.2.2.2)
    else none

/-- One step after the answer `a` of a call: the chain goes on to the next window, or the
version is finished and its piece joins the gathered answer. An empty answer ends the chain
of this version with the piece `∅`. -/
def avCombine (p : AVHdr × AVState × RawCoset) : AVState :=
  p.2.2.elim (avPos (p.1, p.2.1.1 + 1, p.2.1.2.2.2)) fun _ =>
    if p.2.1.2.1 + 1 < p.1.2.2.2.1.length then
      (min p.2.1.1 p.1.2.2.1.length, p.2.1.2.1 + 1, rawCosetNorm (p.1.2.2.2.2.1, p.2.2),
        rawCosetNorm (p.1.2.2.2.2.1, p.2.1.2.2.2))
    else avPos (p.1, p.2.1.1 + 1, rawCosetJoin (p.1.2.2.2.2.1, p.2.1.2.2.2, p.2.2))

/-- The state before the first version. -/
def avInit (h : AVHdr) : AVState := avPos (h, 0, none)

/-! ## The skip rule -/

section Next

variable {h : AVHdr}

theorem avNext_spec (h : AVHdr) (k : ℕ) :
    (avNext (h, k) = h.2.2.1.length ∧
        ∀ i, k ≤ i → i < h.2.2.1.length → avTr (h, i) = none) ∨
      (k ≤ avNext (h, k) ∧ avNext (h, k) < h.2.2.1.length ∧
        (avTr (h, avNext (h, k))).isSome ∧
        ∀ i, k ≤ i → i < avNext (h, k) → avTr (h, i) = none) := by
  set N := h.2.2.1.length
  set l := (List.range N).filter (fun i => decide (k ≤ i) && (avTr (h, i)).isSome) with hl
  have hmem : ∀ i, i ∈ l ↔ i < N ∧ k ≤ i ∧ (avTr (h, i)).isSome := by
    intro i
    simp [hl, List.mem_filter, List.mem_range]
  have hsort : l.Pairwise (· < ·) := List.pairwise_lt_range.filter _
  have hdef : avNext (h, k) = l.headD N := rfl
  cases hc : l with
  | nil =>
    left
    refine ⟨by rw [hdef, hc]; rfl, fun i hki hiN => ?_⟩
    by_contra hne
    have : i ∈ l := (hmem i).2 ⟨hiN, hki, Option.ne_none_iff_isSome.mp hne⟩
    rw [hc] at this
    exact absurd this List.not_mem_nil
  | cons a t =>
    right
    have ha : avNext (h, k) = a := by rw [hdef, hc]; rfl
    have hal : a ∈ l := by rw [hc]; exact List.mem_cons_self
    obtain ⟨haN, hka, hsome⟩ := (hmem a).1 hal
    rw [ha]
    refine ⟨hka, haN, hsome, fun i hki hia => ?_⟩
    by_contra hne
    have hil : i ∈ l := (hmem i).2 ⟨lt_trans hia haN, hki, Option.ne_none_iff_isSome.mp hne⟩
    rw [hc] at hil hsort
    rcases List.mem_cons.1 hil with rfl | hit
    · exact absurd hia (lt_irrefl _)
    · exact absurd (List.rel_of_pairwise_cons hsort hit) (by omega)

/-- A version with a nonempty transporter is not skipped. -/
theorem avNext_self {k : ℕ} (hk : k < h.2.2.1.length) (hs : (avTr (h, k)).isSome) :
    avNext (h, k) = k := by
  rcases avNext_spec h k with ⟨_, hnone⟩ | ⟨hle, _, _, hbelow⟩
  · rw [hnone k le_rfl hk] at hs; exact absurd hs (by simp)
  · by_contra hne
    rw [hbelow k le_rfl (by omega)] at hs
    exact absurd hs (by simp)

/-- A version with an empty transporter is skipped. -/
theorem avNext_skip {k : ℕ} (hs : avTr (h, k) = none) : avNext (h, k) = avNext (h, k + 1) := by
  unfold avNext
  congr 1
  apply List.filter_congr
  intro i _
  by_cases hik : i = k
  · subst hik; simp [hs]
  · have : (k ≤ i) ↔ (k + 1 ≤ i) := by omega
    simp only [this]

/-- Past the last version nothing is left. -/
theorem avNext_end {k : ℕ} (hk : h.2.2.1.length ≤ k) : avNext (h, k) = h.2.2.1.length := by
  rcases avNext_spec h k with ⟨he, _⟩ | ⟨hle, hlt, _, _⟩
  · exact he
  · omega

theorem avTr_end {k : ℕ} (hk : h.2.2.1.length ≤ k) : avTr (h, k) = none := by
  unfold avTr
  rw [List.getD_eq_default _ _ hk]
  unfold alignPairCoset alignPairIso
  rcases h.2.1 with ⟨_ | P, _ | J⟩ <;> rfl

theorem avPos_skip {k : ℕ} (acc : RawCoset) (hs : avTr (h, k) = none) :
    avPos (h, k, acc) = avPos (h, k + 1, acc) := by
  unfold avPos
  simp only
  rw [avNext_skip hs]

theorem avPos_self {k : ℕ} (acc : RawCoset) (hk : k < h.2.2.1.length)
    (hs : (avTr (h, k)).isSome) :
    avPos (h, k, acc) = (k, 0, avTr (h, k), rawCosetNorm (h.2.2.2.2.1, acc)) := by
  unfold avPos
  simp only
  rw [avNext_self hk hs]

theorem avPos_end {k : ℕ} (acc : RawCoset) (hk : h.2.2.1.length ≤ k) :
    avPos (h, k, acc) = (h.2.2.1.length, 0, none, rawCosetNorm (h.2.2.2.2.1, acc)) := by
  unfold avPos
  simp only
  rw [avNext_end hk, avTr_end le_rfl]

end Next

/-! ## The link -/

section Phase

variable {ι ω : Type*} {n m : ℕ} {R : Round ι ω RawCoset} {decI : ι → SIInstance (Fin n) ℕ}
  {I : ι} {h : AVHdr} {pr : ω → AVState} {emb : RawWinSI → ι} {Good : ℕ → ω → Prop}
  {ϕ : decGroup n h.1.1.2 →* Perm (Fin m)}
  [MulAction (Perm (Fin m)) (Pt (SplitOutcomes (Fin m)))]
  {X : Pt (SplitOutcomes (Fin m))} {Ys : List (Pt (SplitOutcomes (Fin m)))}

/-- A raw coset that is not `none` describes a nonempty set. -/
theorem decCoset_some_ne_empty (g : RawGens) (τ : RawPerm) :
    decCoset n (some (g, τ)) ≠ ∅ := by
  intro he
  have : decPerm n τ ∈ decCoset n (some (g, τ)) := ⟨1, one_mem _, by rw [mul_one]⟩
  rw [he] at this
  exact this

/-- The transporter of the version with index `i`. -/
theorem decCoset_avTr (hA : RawAction.WF n m h.1 ϕ) (hgiant : IsGiantRep ϕ)
    (hK : IsCatAction (SplitOutcomes (Fin m))) (hX : decAlignOutcome m h.2.1 = some X)
    (hYs : h.2.2.1.map (decAlignOutcome m) = Ys.map some) (hx : h.2.2.2.2.1.length = n)
    {i : ℕ} (hi : i < Ys.length) :
    decCoset n (avTr (h, i)) = alignTransporter ϕ X Ys[i] := by
  have hlen : h.2.2.1.length = Ys.length := by
    simpa only [List.length_map] using congrArg List.length hYs
  have hi' : i < h.2.2.1.length := by omega
  have hdec : decAlignOutcome m h.2.2.1[i] = some Ys[i] := by
    have := congrArg (fun l => l[i]?) hYs
    simp only [List.getElem?_map, List.getElem?_eq_getElem hi', List.getElem?_eq_getElem hi,
      Option.map_some] at this
    exact Option.some.inj this
  unfold avTr
  rw [decCoset_rawCosetNorm hx, List.getD_eq_getElem _ _ hi']
  exact decCoset_alignPairCoset hA hgiant hK hX hdec

/-- A subset of a left coset `σ • H`, read as the set of `decCoset`. -/
theorem smul_subgroup_eq_setOf (σ : Perm (Fin n)) (H : Subgroup (Perm (Fin n))) :
    σ • (H : Set (Perm (Fin n))) = {ρ | ∃ u ∈ H, ρ = σ * u} := by
  ext ρ
  simp only [Set.mem_smul_set, SetLike.mem_coe, smul_eq_mul, Set.mem_setOf_eq]
  exact ⟨fun ⟨u, hu, he⟩ => ⟨u, hu, he.symm⟩, fun ⟨u, hu, he⟩ => ⟨u, hu, he.symm⟩⟩

variable (hdec : ∀ W g τ, decI (emb (W, g, τ, h.2.2.2.2.1, h.2.2.2.2.2)) =
    decWinSI n (W, g, τ, h.2.2.2.2.1, h.2.2.2.2.2))
  (hchild : ∀ j s J, Good j s → avChild (h, pr s) = some J → R.child (I, j, s) = some (emb J))
  (hcomb : ∀ j s a J, Good j s → avChild (h, pr s) = some J →
    pr (R.combine (I, j, s, a)) = avCombine (h, pr s, a) ∧ Good (j + 1) (R.combine (I, j, s, a)))
  (hA : RawAction.WF n m h.1 ϕ) (hgiant : IsGiantRep ϕ)
  (hK : IsCatAction (SplitOutcomes (Fin m))) (hX : decAlignOutcome m h.2.1 = some X)
  (hYs : h.2.2.1.map (decAlignOutcome m) = Ys.map some)
  (hx : h.2.2.2.2.1.length = n) (hws : h.2.2.2.1 ≠ [])
  (hlt : ∀ W ∈ h.2.2.2.1, ∀ u ∈ W, u < n)
  (hinv : ∀ W ∈ h.2.2.2.1, IsInvariant (preimageSubgroup ϕ (structAut X)) (winSet n W))
include hdec hchild hcomb hA hgiant hK hX hYs hx hws hlt hinv

/-- One version: the chain of line 5 started from the transporter of the version with
index `k`, from the state `avPos (h, k, accRaw)`. At the end the state is at the next version,
and the gathered answer is the hull of the old one and the piece of this version. -/
theorem phaseMatch_alignVersion {k : ℕ} (hk : k < Ys.length) (acc : Set (Perm (Fin n)))
    (accRaw : RawCoset) (hacc : decCoset n accRaw = cosetHull acc) (j : ℕ) (s : ω)
    (hs : pr s = avPos (h, k, accRaw)) (hgs : Good j s) :
    PhaseMatch R decI (decCoset n) I h.2.2.2.1.length j s
      (cosetAlignChain ϕ (decStrN n h.2.2.2.2.1) (decStrN n h.2.2.2.2.2) X Ys[k]
        (h.2.2.2.1.map (winSet n)))
      (fun S j' s' => Good j' s' ∧ ∃ a, pr s' = avPos (h, k + 1, a) ∧
        decCoset n a = cosetHull (acc ∪ S)) := by
  set wins := h.2.2.2.1 with hwins
  set x := h.2.2.2.2.1 with hxdef
  set y := h.2.2.2.2.2 with hydef
  set G₁ := preimageSubgroup ϕ (structAut X) with hG₁
  have hlen : h.2.2.1.length = Ys.length := by
    simpa only [List.length_map] using congrArg List.length hYs
  have hk' : k < h.2.2.1.length := by omega
  set Inv : List (Set (Fin n)) → Set (Perm (Fin n)) → ℕ → ω → Prop := fun Δs C j s =>
    Good j s ∧ (C = ∅ → ∃ b, decCoset n b = decCoset n accRaw ∧ pr s = avPos (h, k + 1, b)) ∧
    (C ≠ ∅ → Δs = [] → ∃ a b, decCoset n a = C ∧ decCoset n b = decCoset n accRaw ∧
      pr s = avPos (h, k + 1, rawCosetJoin (x, b, a))) ∧
    (C ≠ ∅ → Δs ≠ [] → ∃ w g τ b, Δs = (wins.drop w).map (winSet n) ∧
      pr s = (k, w, some (g, τ), b) ∧ decCoset n (some (g, τ)) = C ∧ decGroup n g ≤ G₁ ∧
      decCoset n b = decCoset n accRaw)
    with hInv
  have hmain := phaseMatch_cosetChain (R := R) (decI := decI) (decA := decCoset n) (I := I)
    (decStrN n x) (decStrN n y) Inv ?step ?stop
  case step =>
    rintro Δ Δs C j s ⟨hgood, -, -, h3⟩ hCne
    obtain ⟨w, g, τ, b, hdrop, hsw, hC, hg, hb⟩ := h3 hCne (List.cons_ne_nil _ _)
    have hw : w < wins.length := by
      by_contra hcon
      rw [List.drop_eq_nil_of_le (by omega), List.map_nil] at hdrop
      exact absurd hdrop (List.cons_ne_nil _ _)
    rw [List.drop_eq_getElem_cons hw, List.map_cons] at hdrop
    obtain ⟨hΔ, hΔs⟩ := List.cons.inj hdrop
    have hgetD : wins.getD w [] = wins[w] := List.getD_eq_getElem _ _ hw
    have hmemw : wins[w] ∈ wins := List.getElem_mem hw
    have hltw : ∀ u ∈ wins.getD w [], u < n := by rw [hgetD]; exact hlt _ hmemw
    have htidy : decGroup n (tidyGens (x, g)) = decGroup n g := decGroup_tidyGens hx g
    have hinvw : rawIsInvariant (tidyGens (x, g), wins.getD w []) = true := by
      rw [rawIsInvariant_eq_true_iff (wf_tidyGens hx g) hltw, htidy]
      have := hinv _ hmemw
      rw [← hgetD] at this
      exact isInvariant_of_le this hg
    set J : RawWinSI := (wins.getD w [], tidyGens (x, g), normPerm (x, τ), x, y) with hJ
    have hav : avChild (h, pr s) = some J := by
      rw [hsw]
      unfold avChild
      simp only [Option.bind_some]
      rw [if_pos ⟨hw, hinvw⟩]
    have hdecJ : decI (emb J) = ⟨C, Δ, decStrN n x, decStrN n y⟩ := by
      rw [hJ, hdec]
      have hK' : decCoset n (some (tidyGens (x, g), normPerm (x, τ))) = C := by
        rw [← hC]
        show {ρ | ∃ u ∈ decGroup n (tidyGens (x, g)), ρ = decPerm n (normPerm (x, τ)) * u} = _
        rw [htidy, decPerm_normPerm hx τ]
        rfl
      simp only [decWinSI, hJ]
      rw [hK', hgetD, hΔ]
    refine ⟨emb J, hchild _ _ _ hgood hav, hdecJ, fun a ha => ?_⟩
    have hsub : (decI (emb J)).answer ⊆ C := by
      rw [hdecJ]; exact fun ρ hρ => hρ.1
    rw [hInv]
    beta_reduce
    obtain ⟨hcomb1, hgood'⟩ := hcomb j s a J hgood hav
    refine ⟨hgood', ?_⟩
    rw [hcomb1, hsw]
    rcases a with _ | ⟨g', τ'⟩
    · -- the chain of this version gives up
      have hempty : (decI (emb J)).answer = ∅ := by rw [← ha]; rfl
      rw [hempty]
      exact ⟨fun _ => ⟨b, hb, rfl⟩, fun hne => absurd rfl hne, fun hne => absurd rfl hne⟩
    · have hne : (decI (emb J)).answer ≠ ∅ := by rw [← ha]; exact decCoset_some_ne_empty g' τ'
      have hg' : decGroup n g' ≤ G₁ := by
        refine le_trans (decGroup_le_of_subset (σ₀ := decPerm n τ) (τ := decPerm n τ') ?_) hg
        have h1 : decCoset n (some (g', τ')) ⊆ decCoset n (some (g, τ)) := by
          rw [ha, hC]; exact hsub
        exact h1
      refine ⟨fun he => absurd he hne, ?_, ?_⟩
      · intro _ hnil
        have hge : wins.length ≤ w + 1 := by
          by_contra hcon
          have hne' : (wins.drop (w + 1)).map (winSet n) ≠ [] := by
            simp only [ne_eq, List.map_eq_nil_iff, List.drop_eq_nil_iff]
            omega
          exact hne' (hΔs ▸ hnil)
        refine ⟨some (g', τ'), b, ha, hb, ?_⟩
        show avCombine (h, (k, w, some (g, τ), b), some (g', τ')) = _
        unfold avCombine
        simp only [Option.elim]
        rw [if_neg (Nat.not_lt.2 hge)]
      · intro _ hnil
        have hlt' : w + 1 < wins.length := by
          by_contra hcon
          rw [hΔs, List.drop_eq_nil_of_le (by omega), List.map_nil] at hnil
          exact hnil rfl
        refine ⟨w + 1, tidyGens (x, g'), normPerm (x, τ'), rawCosetNorm (x, b), hΔs, ?_, ?_,
          by rw [decGroup_tidyGens hx]; exact hg', by rw [decCoset_rawCosetNorm hx, hb]⟩
        · show avCombine (h, (k, w, some (g, τ), b), some (g', τ')) = _
          unfold avCombine
          simp only [Option.elim]
          rw [if_pos hlt', Nat.min_eq_left (by omega)]
          rfl
        · have := decCoset_rawCosetNorm hx (some (g', τ'))
          rw [ha] at this
          exact this
  case stop =>
    rintro Δs C j s ⟨hgood, h1, -, -⟩ hCe
    rw [hInv]
    beta_reduce
    exact ⟨hgood, fun _ => h1 hCe, fun hne => absurd rfl hne, fun hne => absurd rfl hne⟩
  have htr := decCoset_avTr hA hgiant hK hX hYs hx hk
  have h0 : Inv (wins.map (winSet n)) (alignTransporter ϕ X Ys[k]) j s := by
    rcases htk : avTr (h, k) with _ | ⟨g, τ⟩
    · have hC0 : alignTransporter ϕ X Ys[k] = ∅ := by rw [← htr, htk]; rfl
      rw [hC0]
      refine ⟨hgs, fun _ => ⟨accRaw, rfl, ?_⟩, fun hne => absurd rfl hne,
        fun hne => absurd rfl hne⟩
      rw [hs, avPos_skip accRaw htk]
    · have hsome : (avTr (h, k)).isSome := by rw [htk]; rfl
      refine ⟨hgs, fun he => absurd (htr ▸ he) (by rw [htk]; exact decCoset_some_ne_empty g τ),
        fun _ hnil => absurd hnil (by simpa using hws), fun hne _ => ?_⟩
      obtain ⟨τ0, hτ0⟩ := Set.nonempty_iff_ne_empty.2 hne
      obtain ⟨hτG, hτX⟩ := hτ0
      have hco := alignTransporter_eq_smul ϕ X Ys[k] ⟨τ0, hτG⟩ hτX
      refine ⟨0, g, τ, rawCosetNorm (x, accRaw), by rw [List.drop_zero], ?_,
        by rw [← htk]; exact htr, ?_, decCoset_rawCosetNorm hx accRaw⟩
      · rw [hs, avPos_self accRaw hk' hsome, htk]
      · refine decGroup_le_of_subset (σ₀ := τ0) (τ := decPerm n τ) ?_
        have h1 : decCoset n (some (g, τ)) = τ0 • (G₁ : Set (Perm (Fin n))) := by
          rw [← htk, htr, hco]
        rw [smul_subgroup_eq_setOf] at h1
        exact le_of_eq h1
  have hrun := hmain (wins.map (winSet n)) (alignTransporter ϕ X Ys[k]) j s h0
  rw [List.length_map] at hrun
  unfold cosetAlignChain
  rw [← aggrCosetChain_eq]
  refine phaseMatch_weaken hrun ?_
  rintro S j' s' ⟨hgood, h1, h2, -⟩
  by_cases hS : S = ∅
  · obtain ⟨b, hb, hpos⟩ := h1 hS
    refine ⟨hgood, b, hpos, ?_⟩
    rw [hb, hacc, hS, Set.union_empty]
  · obtain ⟨a, b, ha, hb, hpos⟩ := h2 hS rfl
    refine ⟨hgood, rawCosetJoin (x, b, a), hpos, ?_⟩
    rw [decCoset_rawCosetJoin hx, hb, hacc, ha, cosetHull_hull_union]

/-- The versions from index `k` on, from the state `avPos (h, k, accRaw)`. -/
theorem phaseMatch_alignVersions_from :
    ∀ (rest : List (Pt (SplitOutcomes (Fin m)))) (k : ℕ), Ys.drop k = rest →
      ∀ (acc : Set (Perm (Fin n))) (accRaw : RawCoset), decCoset n accRaw = cosetHull acc →
      ∀ (j : ℕ) (s : ω), pr s = avPos (h, k, accRaw) → Good j s →
      PhaseMatch R decI (decCoset n) I (rest.length * h.2.2.2.1.length) j s
        (SIReduction.unionOver rest fun Y =>
          cosetAlignChain ϕ (decStrN n h.2.2.2.2.1) (decStrN n h.2.2.2.2.2) X Y
            (h.2.2.2.1.map (winSet n)))
        (fun S j' s' => Good j' s' ∧ ∃ a, pr s' = (h.2.2.1.length, 0, none, a) ∧
          decCoset n a = cosetHull (acc ∪ S)) := by
  have hlen : h.2.2.1.length = Ys.length := by
    simpa only [List.length_map] using congrArg List.length hYs
  intro rest
  induction rest with
  | nil =>
    intro k hk acc accRaw hacc j s hs hgs
    have hle : Ys.length ≤ k := List.drop_eq_nil_iff.1 hk
    rw [SIReduction.unionOver, List.length_nil, Nat.zero_mul]
    refine phaseMatch_done ?_
    exact ⟨hgs, rawCosetNorm (h.2.2.2.2.1, accRaw), by rw [hs, avPos_end accRaw (by omega)],
      by rw [decCoset_rawCosetNorm hx, hacc, Set.union_empty]⟩
  | cons Y rest ih =>
    intro k hk acc accRaw hacc j s hs hgs
    have hkl : k < Ys.length := by
      by_contra hcon
      rw [List.drop_eq_nil_of_le (by omega)] at hk
      exact List.cons_ne_nil _ _ hk.symm
    rw [List.drop_eq_getElem_cons hkl] at hk
    obtain ⟨rfl, hrest⟩ := List.cons.inj hk
    have hc : (Ys[k] :: rest).length * h.2.2.2.1.length =
        h.2.2.2.1.length + (rest.length * h.2.2.2.1.length + 0) := by
      rw [List.length_cons, Nat.succ_mul]; omega
    rw [hc, SIReduction.unionOver]
    refine phaseMatch_bind (phaseMatch_alignVersion hdec hchild hcomb hA hgiant hK hX hYs hx hws
      hlt hinv hkl acc accRaw hacc j s hs hgs) ?_
    rintro S j' s' ⟨hg', a, hpos, ha⟩
    refine phaseMatch_bind (ih (k + 1) hrest (acc ∪ S) a ha j' s' hpos hg') ?_
    rintro S' j'' s'' ⟨hg'', a', hend, ha'⟩
    refine phaseMatch_done ?_
    exact ⟨hg'', a', hend, by rw [ha', Set.union_assoc]⟩

/-- §14.1 and Eq. (71), **the link**: a round whose steps are `avChild` and `avCombine`
walks the tree of `Babai.cosetDesignAlign` call for call, from the state `avInit h`, with at
most (number of versions) × (number of windows) calls. At the end no version is left, and the
gathered raw answer describes the smallest coset containing the value of the tree. -/
theorem phaseMatch_alignVersions (j : ℕ) (s : ω) (hs : pr s = avInit h) (hgs : Good j s) :
    PhaseMatch R decI (decCoset n) I (Ys.length * h.2.2.2.1.length) j s
      (cosetDesignAlign ϕ (decStrN n h.2.2.2.2.1) (decStrN n h.2.2.2.2.2) X Ys
        (h.2.2.2.1.map (winSet n)))
      (fun S j' s' => Good j' s' ∧ ∃ a, pr s' = (h.2.2.1.length, 0, none, a) ∧
        decCoset n a = cosetHull S) := by
  have := phaseMatch_alignVersions_from hdec hchild hcomb hA hgiant hK hX hYs hx hws hlt hinv
    Ys 0 List.drop_zero ∅ none (by rw [cosetHull_empty]; rfl) j s hs hgs
  unfold cosetDesignAlign
  refine phaseMatch_weaken this ?_
  rintro S j' s' ⟨hg, a, h1, h2⟩
  exact ⟨hg, a, h1, by rw [h2, Set.empty_union]⟩

end Phase

end Algo
