/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: Luks's reductions of §11.1 on the RAM, with call bounds and step
bounds.
-/
import Workspace.Algo.LocalCertRAM
import Workspace.Algo.Imprimitive
import Workspace.Algo.ListMapRAM

/-!
# Luks's reductions (§11.1) on the RAM: the Chain Rule over a list of windows

The reductions of §11.1 are stated in the paper as "finding `Iso^Δ_G(x,y)` reduces to so many
instances of …", sometimes with the remark "(The cost of the reduction is polynomial per
instance.)".  On the RAM such a claim is a statement about a program transformer `F`: for
every program `Q` that answers the instances handed on, `F Q` answers the original instance,
its calls to `Q` are the stated instances, and its running time is at most a constant times
the time `Q` spends on the calls plus the number of calls times a polynomial in the input.
This is the form of `Algo.theorem_13_1_3_ram` (§13.1).

This file gives the building block every reduction of §11.1 ends with: **the Chain Rule over a
given list of windows** (Prop. 11.1.7 iterated, Eq. (63)).  An instance `Algo.RawWinList` is an
instance `(Δ, G, σ, x, y)` together with a list `[Δ₁, …, Δ_k]` of `G`-invariant windows; the
fold processes the windows in succession, each call's candidate set being the answer of the
previous call.  It returns `Iso^{Δ₁ ∪ … ∪ Δ_k}_{σG}(x, y)` (`Algo.wl_spec`), makes at most `k`
calls, each on one of the windows with a subgroup of `G` (`Algo.wl_spec`), and runs within
`1000 · ∑ τ + (k + 2) · poly(size)` steps (`Algo.exists_wlProg`).

The fold is an `Algo.Round` used only for its fold (its recursion fields are vacuous, `WF` is
`False`), as in `Algo.MapFold`.  Its child carries the invariance test of `Algo.winChild`, so
that every child it can produce, from any state, is a well-formed instance; on the runs that
matter the test succeeds (`Algo.loopMatch_wl`).
-/

namespace Algo

open RAM RAM.Targets
open Equiv (Perm)
open scoped Pointwise

variable {n : ℕ}

/-! ## The round -/

/-- A chain instance: an instance with a window, and the list of windows to process in
succession. -/
abbrev RawWinList := RawWinSI × RawBlocks

/-- The `j`-th child of a chain instance: the `j`-th window, with the coset reached so far as
its candidate set. -/
def wlChild (p : RawWinList × ℕ × RawCoset) : Option RawWinList :=
  p.2.2.elim none fun q =>
    if p.2.1 < p.1.2.length then
      if rawIsInvariant (tidyGens (p.1.1.2.2.2.1, q.1), p.1.2.getD p.2.1 []) then
        some ((p.1.2.getD p.2.1 [], tidyGens (p.1.1.2.2.2.1, q.1),
          normPerm (p.1.1.2.2.2.1, q.2), p.1.1.2.2.2.1, p.1.1.2.2.2.2), [])
      else none
    else none

/-- **The Chain Rule over a list of windows**, as a fold.  The state is the coset reached so
far; the answer of a child replaces it. -/
def wlRound : Round RawWinList RawCoset RawCoset where
  WF _ := False
  ground _ := 0
  measure _ := 0
  width I := I.2.length
  child := wlChild
  init I := some (I.1.2.1, I.1.2.2.1)
  combine p := p.2.2.2
  finish p := p.2
  bot := none
  child_eq_none I j s h := by
    cases s with
    | none => rfl
    | some q =>
      show (if j < I.2.length then _ else none) = none
      rw [if_neg (by omega)]
  child_wf _ _ _ _ h := h.elim
  child_measure _ _ _ _ h := h.elim
  child_ground _ _ _ _ h := h.elim

theorem wlChild_eq_some {p : RawWinList × ℕ × RawCoset} {J : RawWinList} (h : wlChild p = some J) :
    ∃ g τ, p.2.2 = some (g, τ) ∧ p.2.1 < p.1.2.length ∧
      rawIsInvariant (tidyGens (p.1.1.2.2.2.1, g), p.1.2.getD p.2.1 []) = true ∧
      J = ((p.1.2.getD p.2.1 [], tidyGens (p.1.1.2.2.2.1, g), normPerm (p.1.1.2.2.2.1, τ),
        p.1.1.2.2.2.1, p.1.1.2.2.2.2), []) := by
  obtain ⟨I, j, s⟩ := p
  cases s with
  | none => exact absurd h (by simp [wlChild])
  | some q =>
    obtain ⟨g, τ⟩ := q
    have h' : (if j < I.2.length then
        if rawIsInvariant (tidyGens (I.1.2.2.2.1, g), I.2.getD j []) then
          some ((I.2.getD j [], tidyGens (I.1.2.2.2.1, g), normPerm (I.1.2.2.2.1, τ),
            I.1.2.2.2.1, I.1.2.2.2.2), ([] : RawBlocks))
        else none
      else none) = some J := h
    by_cases h1 : j < I.2.length
    · rw [if_pos h1] at h'
      by_cases h2 : rawIsInvariant (tidyGens (I.1.2.2.2.1, g), I.2.getD j []) = true
      · rw [if_pos h2] at h'
        exact ⟨g, τ, rfl, h1, h2, (Option.some.inj h').symm⟩
      · rw [if_neg h2] at h'; exact absurd h' (by simp)
    · rw [if_neg h1] at h'; exact absurd h' (by simp)

theorem wlChild_eq_some_of {I : RawWinList} {j : ℕ} {g : RawGens} {τ : RawPerm}
    (hj : j < I.2.length)
    (hinv : rawIsInvariant (tidyGens (I.1.2.2.2.1, g), I.2.getD j []) = true) :
    wlChild (I, j, some (g, τ)) = some ((I.2.getD j [], tidyGens (I.1.2.2.2.1, g),
      normPerm (I.1.2.2.2.1, τ), I.1.2.2.2.1, I.1.2.2.2.2), []) := by
  show (if j < I.2.length then
      if rawIsInvariant (tidyGens (I.1.2.2.2.1, g), I.2.getD j []) then _ else none
    else none) = _
  rw [if_pos hj, if_pos hinv]

/-! ## Well-formed chain instances -/

/-- **Well-formed chain instances**: a well-formed instance, and windows that are lists of
distinct points of the domain, each invariant under the group `G` of the instance (the
hypothesis of the Chain Rule, Prop. 11.1.7). -/
def WLWF (n : ℕ) (I : RawWinList) : Prop :=
  WinWF n I.1 ∧ ∀ B ∈ I.2, B.Nodup ∧ (∀ u ∈ B, u < n) ∧
    Babai.IsInvariant (decGroup n I.1.2.1) (winSet n B)

/-- Every child of a well-formed chain instance, from any state, is a well-formed instance on
one of the windows. -/
theorem wlChild_wf {I : RawWinList} (hI : WLWF n I) {j : ℕ} {s : RawCoset} {J : RawWinList}
    (hc : wlChild (I, j, s) = some J) :
    WinWF n J.1 ∧ J.1.1 ∈ I.2 ∧ J.1.2.2.2 = I.1.2.2.2 := by
  obtain ⟨g, τ, -, hj, hinv, rfl⟩ := wlChild_eq_some hc
  have hx : I.1.2.2.2.1.length = n := hI.1.1
  have hmem : I.2.getD j [] ∈ I.2 := by
    rw [List.getD_eq_getElem _ _ hj]; exact List.getElem_mem hj
  obtain ⟨hnd, hlt, -⟩ := hI.2 _ hmem
  exact ⟨⟨hx, hI.1.2.1, hnd, hlt, wf_tidyGens hx g, length_tidyGens hx g, wf_normPerm hx τ,
    hinv⟩, hmem, rfl⟩

/-! ## The link to the Chain Rule -/

/-- **The fold walks the chain of Eq. (63)** over the given windows. -/
theorem loopMatch_wl {I : RawWinList} (hI : WLWF n I) :
    ∀ (k j : ℕ), j + k = I.2.length →
      ∀ (C : Set (Perm (Fin n))) (s : RawCoset), StateOK n I.1 C s →
        LoopMatch wlRound (fun J => decWinSI n J.1) (decCoset n) I k j s
          (cosetChain (decStrN n I.1.2.2.2.1) (decStrN n I.1.2.2.2.2)
            ((I.2.drop j).map (winSet n)) C) := by
  have hx : I.1.2.2.2.1.length = n := hI.1.1
  intro k
  induction k with
  | zero =>
      intro j hj C s hs
      have hdrop : I.2.drop j = [] := List.drop_eq_nil_of_le (by omega)
      rw [hdrop, List.map_nil, cosetChain]
      exact LoopMatch.done 0 j s C (wlRound.child_eq_none I j s (by show I.2.length ≤ j; omega))
        hs.1
  | succ k ih =>
      intro j hj C s hs
      have hjl : j < I.2.length := by omega
      rw [List.drop_eq_getElem_cons hjl, List.map_cons, cosetChain]
      cases s with
      | none =>
        have hCe : C = ∅ := by rw [← hs.1]; rfl
        rw [if_pos hCe]
        exact LoopMatch.done (k + 1) j none ∅ rfl rfl
      | some gτ =>
        obtain ⟨g, τ⟩ := gτ
        have hCne : C ≠ ∅ := by
          rw [← hs.1]
          intro hc
          have : decPerm n τ ∈ decCoset n (some (g, τ)) := ⟨1, one_mem _, by rw [mul_one]⟩
          rw [hc] at this
          exact this
        rw [if_neg hCne]
        have hgetd : I.2.getD j [] = I.2[j] := List.getD_eq_getElem _ _ hjl
        have hmem : I.2[j] ∈ I.2 := List.getElem_mem hjl
        obtain ⟨-, hlt, hGinv⟩ := hI.2 _ hmem
        have hgle : decGroup n g ≤ decGroup n I.1.2.1 := hs.2.2 g τ rfl
        have htidy : decGroup n (tidyGens (I.1.2.2.2.1, g)) = decGroup n g :=
          decGroup_tidyGens hx g
        have hinvw : rawIsInvariant (tidyGens (I.1.2.2.2.1, g), I.2.getD j []) = true := by
          rw [hgetd, rawIsInvariant_eq_true_iff (wf_tidyGens hx g) hlt, htidy]
          exact isInvariant_of_le hGinv hgle
        have hchild := wlChild_eq_some_of (τ := τ) hjl hinvw
        set J : RawWinList := ((I.2.getD j [], tidyGens (I.1.2.2.2.1, g),
          normPerm (I.1.2.2.2.1, τ), I.1.2.2.2.1, I.1.2.2.2.2), []) with hJ
        have hdec : decWinSI n J.1
            = ⟨C, winSet n I.2[j], decStrN n I.1.2.2.2.1, decStrN n I.1.2.2.2.2⟩ := by
          have hK : decCoset n (some (tidyGens (I.1.2.2.2.1, g),
              normPerm (I.1.2.2.2.1, τ))) = C := by
            rw [← hs.1]
            show {ρ | ∃ u ∈ decGroup n (tidyGens (I.1.2.2.2.1, g)),
              ρ = decPerm n (normPerm (I.1.2.2.2.1, τ)) * u} = _
            rw [htidy, decPerm_normPerm hx τ]
            rfl
          rw [decWinSI, hJ]
          simp only
          rw [hK, hgetd]
        rw [← hdec]
        refine LoopMatch.call k j (some (g, τ)) J _ hchild ?_
        intro a ha
        have hans : (decWinSI n J.1).answer
            = Babai.wIso (winSet n I.2[j]) C (decStrN n I.1.2.2.2.1)
                (decStrN n I.1.2.2.2.2) := by
          rw [Babai.SIInstance.answer, hdec]
        have hsub : (decWinSI n J.1).answer ⊆ C := by
          rw [hans]; exact fun ρ hρ => hρ.1
        refine ih (j + 1) (by omega) ((decWinSI n J.1).answer) a ?_
        refine ⟨ha, le_trans hsub hs.2.1, ?_⟩
        intro g₂ τ₂ ha2
        refine decGroup_le_of_subset (σ₀ := decPerm n I.1.2.2.1) (τ := decPerm n τ₂) ?_
        have h1 : decCoset n (some (g₂, τ₂)) ⊆ (decWinSI n I.1).K := by
          rw [← ha2, ha]
          exact le_trans hsub hs.2.1
        exact h1

/-! ## What the fold computes -/

/-- The normalized answer to a chain call. -/
def wlAns (ansQ : RawWinSI → RawCoset) (J : RawWinList) : RawCoset := lcAnsN ansQ J.1

/-- The output of the chain, with the calls answered by `ansQ` (normalized). -/
def wlOut (ansQ : RawWinSI → RawCoset) (I : RawWinList) : RawCoset :=
  wlRound.loopAux (wlAns ansQ) I.2.length I 0 (wlRound.init I)

/-- The calls of the chain. -/
def wlCalls (ansQ : RawWinSI → RawCoset) (I : RawWinList) : List RawWinSI :=
  (wlRound.loopCalls (wlAns ansQ) I.2.length I 0 (wlRound.init I)).map Prod.fst

theorem biUnion_map_winSet (l : RawBlocks) :
    (⋃ Δ ∈ l.map (winSet n), Δ) = ⋃ B ∈ l, winSet n B := by
  ext u
  simp only [Set.mem_iUnion, List.mem_map, exists_prop]
  constructor
  · rintro ⟨Δ, ⟨B, hB, rfl⟩, hu⟩; exact ⟨B, hB, hu⟩
  · rintro ⟨B, hB, hu⟩; exact ⟨_, ⟨B, hB, rfl⟩, hu⟩

/-- The state invariant used to describe the calls: the coset reached so far lies in the
candidate set of the instance, and its group lies in `G`. -/
def WLState (n : ℕ) (I : RawWinList) (s : RawCoset) : Prop :=
  ∀ g τ, s = some (g, τ) → decGroup n g ≤ decGroup n I.1.2.1 ∧
    decPerm n τ ∈ (decWinSI n I.1).K

/-- The coset of a call lies in the coset of the state it was made from. -/
theorem wl_child_K_sub {I : RawWinList} (hI : WLWF n I) {j : ℕ} {g : RawGens} {τ : RawPerm}
    {J : RawWinList} (hs : WLState n I (some (g, τ))) (hc : wlChild (I, j, some (g, τ)) = some J) :
    (decWinSI n J.1).K ⊆ (decWinSI n I.1).K ∧ decGroup n J.1.2.1 ≤ decGroup n I.1.2.1 ∧
      decPerm n J.1.2.2.1 ∈ (decWinSI n I.1).K := by
  have hx : I.1.2.2.2.1.length = n := hI.1.1
  obtain ⟨g', τ', hq, -, -, rfl⟩ := wlChild_eq_some hc
  simp only [Option.some.injEq, Prod.mk.injEq] at hq
  obtain ⟨rfl, rfl⟩ := hq
  obtain ⟨hgle, hτK⟩ := hs g τ rfl
  obtain ⟨v, hv, hτv⟩ := hτK
  have htidy : decGroup n (tidyGens (I.1.2.2.2.1, g)) = decGroup n g := decGroup_tidyGens hx g
  refine ⟨?_, ?_, ?_⟩
  · rintro ρ ⟨u, hu, rfl⟩
    show ∃ w ∈ decGroup n I.1.2.1, _ = decPerm n I.1.2.2.1 * w
    simp only at hu ⊢
    rw [htidy] at hu
    rw [decPerm_normPerm hx τ, hτv]
    exact ⟨v * u, mul_mem hv (hgle hu), by rw [mul_assoc]⟩
  · show decGroup n (tidyGens (I.1.2.2.2.1, g)) ≤ _
    rw [htidy]; exact hgle
  · show decPerm n (normPerm (I.1.2.2.2.1, τ)) ∈ _
    rw [decPerm_normPerm hx τ]
    exact ⟨v, hv, hτv⟩

/-- **The Chain Rule over a list of windows, what it computes** (Prop. 11.1.7 iterated,
Eq. (63)).  If `ansQ` answers every well-formed instance, the fold returns
`Iso^{Δ₁ ∪ … ∪ Δ_k}_{σG}(x, y)`; it makes at most `k` calls, each a well-formed instance on
one of the windows `Δᵢ`, with a subgroup of `G` and a representative in `σG`. -/
theorem wl_spec {ansQ : RawWinSI → RawCoset} {I : RawWinList} (hI : WLWF n I)
    (hQ : ∀ W, WinWF n W → decCoset n (ansQ W) = (decWinSI n W).answer) :
    decCoset n (wlOut ansQ I) = Babai.wIso (⋃ B ∈ I.2, winSet n B) (decWinSI n I.1).K
        (decStrN n I.1.2.2.2.1) (decStrN n I.1.2.2.2.2) ∧
      (wlCalls ansQ I).length ≤ I.2.length ∧
      ∀ W ∈ wlCalls ansQ I, WinWF n W ∧ W.1 ∈ I.2 ∧ W.2.2.2 = I.1.2.2.2 ∧
        decGroup n W.2.1 ≤ decGroup n I.1.2.1 ∧ decPerm n W.2.2.1 ∈ (decWinSI n I.1).K := by
  have hx : I.1.2.2.2.1.length = n := hI.1.1
  have hlm := loopMatch_wl hI I.2.length 0 (by omega) (decWinSI n I.1).K (wlRound.init I)
    ⟨rfl, le_refl _, fun g τ h => by
      have : g = I.1.2.1 := (Prod.mk.inj (Option.some.inj h)).1.symm
      rw [this]⟩
  have hgood : ∀ (j : ℕ) (s : RawCoset) (J : RawWinList), wlRound.child (I, j, s) = some J →
      WinWF n J.1 := fun j s J hc => (wlChild_wf hI hc).1
  have hrec : ∀ J, WinWF n J.1 → decCoset n (wlAns ansQ J) = (decWinSI n J.1).answer :=
    fun J hJ => lcAnsN_correct hQ hJ
  obtain ⟨hval, -⟩ := wlRound.loopAux_eq hgood hrec _ _ _ _ hlm
  refine ⟨?_, ?_, ?_⟩
  · rw [wlOut, hval, List.drop_zero, run_cosetChain, biUnion_map_winSet]
  · rw [wlCalls, List.length_map]
    exact wlRound.length_loopCalls_le _ I _ 0 _
  · intro W hW
    rw [wlCalls, List.mem_map] at hW
    obtain ⟨J, hJ, rfl⟩ := hW
    have hinv : ∀ j s J, WLState n I s → wlRound.child (I, j, s) = some J →
        WLState n I (wlRound.combine (I, j, s, wlAns ansQ J)) := by
      intro j s J hs hc
      obtain ⟨g, τ, hq, -, -, -⟩ := wlChild_eq_some hc
      simp only at hq
      subst hq
      have hc' : wlChild (I, j, some (g, τ)) = some J := hc
      obtain ⟨hKsub, -, -⟩ := wl_child_K_sub hI hs hc'
      have hJwf := (wlChild_wf hI hc').1
      intro g₂ τ₂ ha2
      have ha : decCoset n (wlAns ansQ J) = (decWinSI n J.1).answer := hrec J hJwf
      have hsub : decCoset n (some (g₂, τ₂)) ⊆ (decWinSI n I.1).K := by
        have e : wlRound.combine (I, j, some (g, τ), wlAns ansQ J) = wlAns ansQ J := rfl
        rw [e] at ha2
        rw [← ha2, ha]
        exact le_trans (fun ρ hρ => hρ.1) hKsub
      refine ⟨decGroup_le_of_subset (σ₀ := decPerm n I.1.2.2.1) (τ := decPerm n τ₂) hsub, ?_⟩
      exact hsub ⟨1, one_mem _, by rw [mul_one]⟩
    obtain ⟨j', s', hs', hc⟩ := wlRound.mem_loopCalls_inv (wlAns ansQ) I
      (fun _ s => WLState n I s) (fun j s J hs hc => hinv j s J hs hc) I.2.length 0
      (wlRound.init I) (fun g τ h => by
        have e := Option.some.inj h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
        exact ⟨le_refl _, ⟨1, one_mem _, by rw [mul_one]⟩⟩) J hJ
    obtain ⟨hJwf, hJmem, hJstr⟩ := wlChild_wf hI hc
    obtain ⟨g, τ, hq, -, -, -⟩ := wlChild_eq_some hc
    simp only at hq
    subst hq
    obtain ⟨-, hgle, hrep⟩ := wl_child_K_sub hI hs' hc
    exact ⟨hJwf, hJmem, hJstr, hgle, hrep⟩

/-! ## The routines are machine routines -/

theorem polyFun_wlChild : PolyFun wlChild := by
  have hx : PolyFun (fun z : (RawGens × RawPerm) × (RawWinList × ℕ) => z.2.1.1.2.2.2.1) :=
    ((((polyFun_snd.comp polyFun_fst).comp polyFun_fst).comp polyFun_snd).comp
      polyFun_snd).comp polyFun_snd |>.comp polyFun_fst
  have hy : PolyFun (fun z : (RawGens × RawPerm) × (RawWinList × ℕ) => z.2.1.1.2.2.2.2) :=
    ((((polyFun_snd.comp polyFun_fst).comp polyFun_fst).comp polyFun_snd).comp
      polyFun_snd).comp polyFun_snd |>.comp polyFun_snd
  have hwin : PolyFun (fun z : (RawGens × RawPerm) × (RawWinList × ℕ) => z.2.1.2.getD z.2.2 []) :=
    ((((polyFun_snd.comp polyFun_fst).comp polyFun_snd).pair (polyFun_snd.comp polyFun_snd)).pair
      (polyFun_const ([] : List ℕ))).comp polyFun_getD
  have htg : PolyFun (fun z : (RawGens × RawPerm) × (RawWinList × ℕ) =>
      tidyGens (z.2.1.1.2.2.2.1, z.1.1)) :=
    (hx.pair (polyFun_fst.comp polyFun_fst)).comp polyFun_tidyGens
  have hnp : PolyFun (fun z : (RawGens × RawPerm) × (RawWinList × ℕ) =>
      normPerm (z.2.1.1.2.2.2.1, z.1.2)) :=
    (hx.pair (polyFun_fst.comp polyFun_snd)).comp polyFun_normPerm
  have hc1 : PolyFun (fun z : (RawGens × RawPerm) × (RawWinList × ℕ) =>
      decide (z.2.2 < z.2.1.2.length)) :=
    (((polyFun_snd.comp polyFun_snd).add (polyFun_const 1)).le
      (((polyFun_snd.comp polyFun_fst).comp polyFun_snd).comp polyFun_length)).of_eq
      (fun z => by simp [Nat.succ_le_iff])
  have hc2 : PolyFun (fun z : (RawGens × RawPerm) × (RawWinList × ℕ) =>
      rawIsInvariant (tidyGens (z.2.1.1.2.2.2.1, z.1.1), z.2.1.2.getD z.2.2 [])) :=
    (htg.pair hwin).comp polyFun_rawIsInvariant
  have hsome : PolyFun (fun z : (RawGens × RawPerm) × (RawWinList × ℕ) =>
      (some ((z.2.1.2.getD z.2.2 [], tidyGens (z.2.1.1.2.2.2.1, z.1.1),
        normPerm (z.2.1.1.2.2.2.1, z.1.2), z.2.1.1.2.2.2.1, z.2.1.1.2.2.2.2),
        ([] : RawBlocks)) : Option RawWinList)) :=
    ((hwin.pair (htg.pair (hnp.pair (hx.pair hy)))).pair (polyFun_const ([] : RawBlocks))).comp
      polyFun_some
  have hbody : PolyFun (fun z : (RawGens × RawPerm) × (RawWinList × ℕ) =>
      if z.2.2 < z.2.1.2.length then
        if rawIsInvariant (tidyGens (z.2.1.1.2.2.2.1, z.1.1), z.2.1.2.getD z.2.2 []) then
          (some ((z.2.1.2.getD z.2.2 [], tidyGens (z.2.1.1.2.2.2.1, z.1.1),
            normPerm (z.2.1.1.2.2.2.1, z.1.2), z.2.1.1.2.2.2.1, z.2.1.1.2.2.2.2),
            ([] : RawBlocks)) : Option RawWinList)
        else none
      else none) :=
    (PolyFun.ite hc1 (PolyFun.ite hc2 hsome (polyFun_const (none : Option RawWinList)))
      (polyFun_const (none : Option RawWinList))).of_eq (fun z => by
        by_cases h1 : z.2.2 < z.2.1.2.length <;> simp [h1])
  have hopt := PolyFun.optionElim (polyFun_const (none : Option RawWinList)) hbody
  have hin : PolyFun (fun p : RawWinList × ℕ × RawCoset =>
      ((p.2.2, ((p.1, p.2.1) : RawWinList × ℕ)) : RawCoset × (RawWinList × ℕ))) :=
    (polyFun_snd.comp polyFun_snd).pair (polyFun_fst.pair (polyFun_snd.comp polyFun_fst))
  refine (hin.comp hopt).of_eq (fun p => ?_)
  obtain ⟨I, j, s⟩ := p
  cases s with
  | none => rfl
  | some q => rfl

theorem polyFun_wlCombine : PolyFun wlRound.combine :=
  ((polyFun_snd.comp polyFun_snd).comp polyFun_snd).of_eq (fun _ => rfl)

theorem polyFun_wlInit : PolyFun wlRound.init :=
  ((((polyFun_fst.comp polyFun_snd).comp polyFun_fst).pair
    (((polyFun_fst.comp polyFun_snd).comp polyFun_snd).comp polyFun_fst)).comp polyFun_some).of_eq
    (fun _ => rfl)

theorem polyFun_wlFinish : PolyFun wlRound.finish := polyFun_snd.of_eq (fun _ => rfl)

theorem polyFun_wlWidth : PolyFun (fun I : RawWinList => I.2.length) := polyFun_snd.comp polyFun_length

/-! ## Sizes -/

/-- The size bound of the states and calls of the chain, in the size of the instance. -/
def wlBound (m : ℕ) : ℕ := 12 * m + 8 * (chainBound m + 4 * m + 2) + 30

theorem polyBound_wlBound : PolyBound wlBound :=
  ((((polyBound_const 12).mul polyBound_id).add ((polyBound_const 8).mul
    ((polyBound_chainBound.add ((polyBound_const 4).mul polyBound_id)).add
      (polyBound_const 2)))).add (polyBound_const 30))

theorem mono_wlBound : Monotone wlBound := by
  intro a b hab
  have := mono_chainBound hab
  unfold wlBound
  omega

theorem size_wlInit_le (I : RawWinList) : Enc.size (wlRound.init I) ≤ 4 * Enc.size I + 2 := by
  have h1 : Enc.size (some (I.1.2.1, I.1.2.2.1) : RawCoset)
      = Enc.size ((I.1.2.1, I.1.2.2.1) : RawGens × RawPerm) + 2 := size_some_eq _
  have h2 : Enc.size ((I.1.2.1, I.1.2.2.1) : RawGens × RawPerm)
      ≤ 2 * Enc.size I.1.2.1 + 2 * Enc.size I.1.2.2.1 := size_pair_le' _
  have h3 : Enc.size I.1.2.1 ≤ Enc.size I :=
    le_trans (size_fst_le' _) (le_trans (size_snd_le' _) (size_fst_le' _))
  have h4 : Enc.size I.1.2.2.1 ≤ Enc.size I :=
    le_trans (size_fst_le' _) (le_trans (size_snd_le' _) (le_trans (size_snd_le' _)
      (size_fst_le' _)))
  show Enc.size (some (I.1.2.1, I.1.2.2.1) : RawCoset) ≤ _
  omega

theorem size_strings_le (I : RawWinList) : Enc.size I.1.2.2.2 ≤ Enc.size I :=
  le_trans (size_snd_le' _) (le_trans (size_snd_le' _) (le_trans (size_snd_le' _)
    (size_fst_le' _)))

/-! ## The Chain Rule over a list of windows on the RAM -/

set_option maxHeartbeats 4000000 in
/-- **The Chain Rule over a list of windows on the RAM.**  One program transformer `F`: for
every program `Q` that runs on the well-formed instances with polynomially small answers, `F Q`
runs the chain (`Algo.wlOut`, correct by `Algo.wl_spec`) within
`1000 · ∑_{W ∈ calls} τ(W) + (k + 2) · poly(size)` steps, `k` the number of windows. -/
theorem exists_wlProg (S : ℕ → ℕ) (hS : PolyBound S) :
    ∃ (F : Program → Program) (c d : ℕ), ∀ Q : Program, Wf Q → Wf (F Q) ∧
      ∀ (n : ℕ) (ansQ : RawWinSI → RawCoset) (τ : RawWinSI → ℕ) (I : RawWinList), WLWF n I →
        (∀ W, WinWF n W → RunsOn 16 Q W (ansQ W) (τ W) ∧ Enc.size (ansQ W) ≤ S (Enc.size W)) →
        RunsOn 16 (F Q) I (wlOut ansQ I)
          (1000 * ((wlCalls ansQ I).map τ).sum + (I.2.length + 2) * pw c d (Enc.size I)) := by
  obtain ⟨N, cN, dN, hN⟩ := exists_normProg S hS
  obtain ⟨F0, c0, d0, hF0⟩ := wlRound.exists_foldProg polyFun_wlChild polyFun_wlCombine
    polyFun_wlInit polyFun_wlFinish polyFun_wlWidth
  obtain ⟨Pf, cf, df, hPf, -⟩ :=
    polyFun_witness (polyFun_fst : PolyFun (fun I : RawWinList => I.1))
  obtain ⟨G, hGd⟩ : ∃ G : ℕ → ℕ, ∀ m, G m = 100 * (pw cf df (wlBound m) + pw cN dN (wlBound m))
      + pw c0 d0 (wlBound m) := ⟨_, fun _ => rfl⟩
  have hG : PolyBound G := by
    rw [show G = fun m => 100 * (pw cf df (wlBound m) + pw cN dN (wlBound m))
      + pw c0 d0 (wlBound m) from funext hGd]
    exact ((polyBound_const 100).mul (((polyBound_pw cf df).comp polyBound_wlBound).add
      ((polyBound_pw cN dN).comp polyBound_wlBound))).add
      ((polyBound_pw c0 d0).comp polyBound_wlBound)
  obtain ⟨c, d, hcd⟩ := hG
  let L : Program → Program := fun Q => RAM.seq Pf (N Q)
  refine ⟨fun Q => F0 (L Q), c, d, fun Q hQwf => ?_⟩
  have hNwf := (hN Q hQwf).1
  have hLwf : Wf (L Q) := wf_seq (CleanComputeAt.wf' hPf) hNwf
  obtain ⟨hFwf, hFrun⟩ := hF0 (L Q) hLwf
  refine ⟨hFwf default, ?_⟩
  intro n ansQ τ I hI hQ
  obtain ⟨m, hm⟩ : ∃ m, m = Enc.size I := ⟨_, rfl⟩
  have hGm := hcd m
  rw [hGd] at hGm
  have hsm : Enc.size I.1.2.2.2 ≤ m := hm ▸ size_strings_le I
  have hcb : chainBound (Enc.size I.1.2.2.2) ≤ chainBound m := mono_chainBound hsm
  have hBm : wlBound m = 12 * m + 8 * (chainBound m + 4 * m + 2) + 30 := rfl
  have epc : c * (m + 1) ^ d = pw c d m := rfl
  let ans : RawWinList → RawCoset := wlAns ansQ
  let τ' : RawWinList → ℕ := fun J =>
    cf * (Enc.size J + 1) ^ df + (10 * τ J.1 + pw cN dN (Enc.size J.1))
  have hJsize : ∀ J ∈ wlRound.loopCalls ans (I.2.length) I 0 (wlRound.init I),
      WinWF n J.1 ∧ Enc.size J.1 ≤ chainBound m ∧ Enc.size J ≤ wlBound m ∧
        Enc.size (ans J) ≤ chainBound m := by
    intro J hJ
    obtain ⟨j', s', -, hc⟩ := wlRound.mem_loopCalls_inv ans I (fun _ _ => True)
      (fun _ _ _ _ _ => trivial) _ 0 _ trivial J hJ
    obtain ⟨hJwf, -, hJstr⟩ := wlChild_wf hI hc
    have h1 : Enc.size J.1 ≤ chainBound (Enc.size J.1.2.2.2) := size_winSI_le hJwf
    rw [hJstr] at h1
    have h2 : Enc.size J ≤ 2 * Enc.size J.1 + 2 * Enc.size J.2 := size_pair_le' J
    obtain ⟨g, τ0, -, -, -, hJe⟩ := wlChild_eq_some hc
    have hJ2 : J.2 = [] := by rw [hJe]
    have h3 : Enc.size J.2 = 1 := by rw [hJ2]; exact size_nil
    have h4 : Enc.size (ans J) ≤ chainBound (Enc.size J.1.2.2.2) := size_lcAnsN_le hJwf
    rw [hJstr] at h4
    refine ⟨hJwf, le_trans h1 hcb, ?_, le_trans h4 hcb⟩
    rw [hBm]
    omega
  have hcallsF : ∀ J ∈ wlRound.loopCalls ans (I.2.length) I 0 (wlRound.init I),
      RunsOn 16 (L Q) J (ans J) (τ' J) ∧ Enc.size J ≤ wlBound m ∧
        Enc.size (ans J) ≤ wlBound m := by
    intro J hJ
    obtain ⟨hJwf, -, hJs, hJa⟩ := hJsize J hJ
    obtain ⟨hQrun, hQsz⟩ := hQ J.1 hJwf
    refine ⟨(hPf.runsOn J).seq ((hN Q hQwf).2 ansQ J.1 (τ J.1) hQrun hQsz), hJs, ?_⟩
    rw [hBm]; omega
  have hstatesF : ∀ k ≤ I.2.length,
      Enc.size ((wlRound.foldStep ans)^[k] ((I, 0, wlRound.init I), false)) ≤ wlBound m := by
    intro k _
    obtain ⟨j', s', b', he, hj', hs'⟩ := wlRound.foldStep_iterate_inv ans I
      (fun j s => j ≤ I.2.length ∧ Enc.size s ≤ chainBound m + 4 * m + 2)
      (fun j s J _ hc => ⟨wlRound.lt_width_of_child hc, by
        show Enc.size (ans J) ≤ _
        obtain ⟨hJwf, -, hJstr⟩ := wlChild_wf hI hc
        have h4 : Enc.size (ans J) ≤ chainBound (Enc.size J.1.2.2.2) := size_lcAnsN_le hJwf
        rw [hJstr] at h4
        omega⟩)
      k 0 (wlRound.init I) false ⟨Nat.zero_le _, by
        have := size_wlInit_le I
        omega⟩
    rw [he]
    have h1 := Round.size_foldSt_le I j' s' b'
    have h2 : Enc.size j' ≤ Enc.size I.2 + 2 := MapFold.size_nat_le_of_le_length hj'
    have h3 : Enc.size I.2 ≤ Enc.size I := size_snd_le' I
    rw [hBm]
    omega
  have r := hFrun ans τ' I (wlBound m) hcallsF hstatesF
  refine r.mono ?_
  set l := wlRound.loopCalls ans (I.2.length) I 0 (wlRound.init I) with hl
  have hsum := sum_map_le_of_le l τ' (fun J => τ J.1) 10
    (pw cf df (wlBound m) + pw cN dN (wlBound m)) (fun J hJ => by
      obtain ⟨-, hJ1, hJs, -⟩ := hJsize J hJ
      have e1 : cf * (Enc.size J + 1) ^ df ≤ pw cf df (wlBound m) := pw_mono cf df hJs
      have e2 : pw cN dN (Enc.size J.1) ≤ pw cN dN (wlBound m) :=
        pw_mono cN dN (le_trans hJ1 (by rw [hBm]; omega))
      show cf * (Enc.size J + 1) ^ df + (10 * τ J.1 + pw cN dN (Enc.size J.1))
        ≤ 10 * τ J.1 + (pw cf df (wlBound m) + pw cN dN (wlBound m))
      omega)
  have hmap : (wlCalls ansQ I).map τ = l.map (fun J => τ J.1) := by
    rw [wlCalls, List.map_map]; rfl
  rw [hmap, ← hm]
  have hlen : l.length ≤ I.2.length := wlRound.length_loopCalls_le ans I _ 0 _
  set K := pw cf df (wlBound m) + pw cN dN (wlBound m)
  have e1 : l.length * K ≤ (I.2.length + 2) * K := Nat.mul_le_mul_right _ (by omega)
  have e3 : (I.2.length + 2) * (100 * K + pw c0 d0 (wlBound m)) ≤ (I.2.length + 2) * pw c d m :=
    Nat.mul_le_mul_left _ (by omega)
  have e4 : (I.2.length + 2) * (100 * K + pw c0 d0 (wlBound m))
      = 100 * ((I.2.length + 2) * K) + (I.2.length + 2) * pw c0 d0 (wlBound m) := by ring
  have hw : wlRound.width I = I.2.length := rfl
  rw [hw] at *
  omega

/-! # Descent over indexed coset representatives (Prop. 11.1.6, Eq. (62))

A descent instance `Algo.RawDS P Rp` is an instance `(Δ, G, σ, x, y)`, a payload of type `P`
handed on unchanged to every call, the generators of the subgroup `H` descended to, a
parameter `ρ : Rp` and a count `k`, such that the representatives `r_j = repOf (ρ, j)`,
`j < k`, satisfy `G = ⋃_j r_j H`.  The `j`-th call is the instance `(Δ, H, σr_j, x, y)` with
the payload (`Algo.dsCall`); the answers are joined into one coset.  This is Eq. (62) with the
shift identity: the candidate set `σG` is the union of the `σr_jH`, and
`Iso^Δ_{σr_jH}(x,y) = σr_j Iso^Δ_H(x, y^{(σr_j)⁻¹})`.

The representatives are produced by a routine `repOf` from the index `j`, so the list of all
`k` representatives never has to be written down: for the block kernel of Theorem 11.1.9 the
index is binary and `repOf` is `Algo.blockCosetRep`; for a list of representatives computed
beforehand `repOf` reads the list. -/

section Descent

variable {P Rp : Type} [Enc P] [Inhabited P] [Enc Rp] [Inhabited Rp]
  (repOf : Rp × ℕ → RawPerm)

/-- A descent instance: an instance with a window and a payload, the generators of the
subgroup `H` descended to, and the parameter and number of the coset representatives. -/
abbrev RawDS (P Rp : Type) := (RawWinSI × P) × (RawGens × (Rp × ℕ))

/-- **The call for the `j`-th representative**: the instance `(Δ, H, σr_j, x, y)` with the
payload. -/
def dsCall (I : RawDS P Rp) (j : ℕ) : RawWinSI × P :=
  ((I.1.1.1, tidyGens (I.1.1.2.2.2.1, I.2.1),
    rawMul (I.1.1.2.2.1, normPerm (I.1.1.2.2.2.1, repOf (I.2.2.1, j))), I.1.1.2.2.2.1,
    I.1.1.2.2.2.2), I.1.2)

/-- The descent data of a child: never read. -/
def dsJunk : RawGens × (Rp × ℕ) := ([], (default, 0))

/-- The `j`-th child of a descent instance. -/
def dsChild (p : RawDS P Rp × ℕ × RawCoset) : Option (RawDS P Rp) :=
  if p.2.1 < p.1.2.2.2 then some (dsCall repOf p.1 p.2.1, dsJunk) else none

/-- **The descent**, as a fold: the state is the coset hull of the answers so far
(`Algo.rawCosetJoin`). -/
def dsRound : Round (RawDS P Rp) RawCoset RawCoset where
  WF _ := False
  ground _ := 0
  measure _ := 0
  width I := I.2.2.2
  child := dsChild repOf
  init _ := none
  combine p := rawCosetJoin (p.1.1.1.2.2.2.1, p.2.2.1, p.2.2.2)
  finish p := p.2
  bot := none
  child_eq_none I j s h := by
    show (if j < I.2.2.2 then _ else none) = none
    rw [if_neg (by omega)]
  child_wf _ _ _ _ h := h.elim
  child_measure _ _ _ _ h := h.elim
  child_ground _ _ _ _ h := h.elim

theorem dsChild_of_lt {I : RawDS P Rp} {j : ℕ} (s : RawCoset) (hj : j < I.2.2.2) :
    (dsRound repOf).child (I, j, s) = some (dsCall repOf I j, dsJunk) := by
  show (if j < I.2.2.2 then _ else none) = _
  rw [if_pos hj]

theorem dsChild_of_le {I : RawDS P Rp} {j : ℕ} (s : RawCoset) (hj : I.2.2.2 ≤ j) :
    (dsRound repOf).child (I, j, s) = none :=
  (dsRound repOf).child_eq_none I j s hj

/-- **The calls of the descent are the representatives**, one call each. -/
theorem ds_loopCalls (ans : RawDS P Rp → RawCoset) (I : RawDS P Rp) :
    ∀ (w j : ℕ) (s : RawCoset), I.2.2.2 ≤ j + w →
      (dsRound repOf).loopCalls ans w I j s
        = ((List.range I.2.2.2).drop j).map (fun i => (dsCall repOf I i, dsJunk)) := by
  intro w
  induction w with
  | zero =>
    intro j s h
    simp [List.drop_eq_nil_of_le (show (List.range I.2.2.2).length ≤ j by simp; omega)]
  | succ w ih =>
    intro j s h
    by_cases hj : j < I.2.2.2
    · have hj' : j < (List.range I.2.2.2).length := by simpa using hj
      rw [(dsRound repOf).loopCalls_succ_some (dsChild_of_lt repOf s hj), ih (j + 1) _ (by omega),
        List.drop_eq_getElem_cons hj', List.getElem_range]
      rfl
    · rw [(dsRound repOf).loopCalls_succ_none (dsChild_of_le repOf s (by omega))]
      simp [List.drop_eq_nil_of_le (show (List.range I.2.2.2).length ≤ j by simp; omega)]

/-- **Well-formed descent instances**: a well-formed instance, a subgroup `H ≤ G`, and
representatives whose left cosets of `H` cover `G` (Prop. 11.1.6, "`G = ⋃_σ Hσ`" in the
paper's right-action notation). -/
structure DSWF (n : ℕ) (I : RawDS P Rp) : Prop where
  win : WinWF n I.1.1
  le : decGroup n I.2.1 ≤ decGroup n I.1.1.2.1
  cover : (decGroup n I.1.1.2.1 : Set (Perm (Fin n)))
    = ⋃ j ∈ List.range I.2.2.2, decPerm n (repOf (I.2.2.1, j)) •
      (decGroup n I.2.1 : Set (Perm (Fin n)))

/-- The representatives of the calls, decoded: `σ r_j`. -/
noncomputable def dsPerms (n : ℕ) (I : RawDS P Rp) : List (Perm (Fin n)) :=
  (List.range I.2.2.2).map (fun j => decPerm n I.1.1.2.2.1 * decPerm n (repOf (I.2.2.1, j)))

variable {repOf}

theorem decPerm_dsCall {I : RawDS P Rp} (hI : DSWF repOf n I) (j : ℕ) :
    decPerm n (dsCall repOf I j).1.2.2.1
      = decPerm n I.1.1.2.2.1 * decPerm n (repOf (I.2.2.1, j)) := by
  have hx : I.1.1.2.2.2.1.length = n := hI.win.1
  show decPerm n (rawMul (I.1.1.2.2.1, normPerm (I.1.1.2.2.2.1, repOf (I.2.2.1, j)))) = _
  rw [rawMul_of_wf hI.win.2.2.2.2.2.2.1 (wf_normPerm hx _), decPerm_encPerm,
    decPerm_normPerm hx]

theorem decGroup_dsCall {I : RawDS P Rp} (hI : DSWF repOf n I) (j : ℕ) :
    decGroup n (dsCall repOf I j).1.2.1 = decGroup n I.2.1 :=
  decGroup_tidyGens hI.win.1 _

/-- **Every call is a well-formed instance.** -/
theorem dsCall_wf {I : RawDS P Rp} (hI : DSWF repOf n I) (j : ℕ) :
    WinWF n (dsCall repOf I j).1 := by
  obtain ⟨hx, hy, hnd, hlt, hgs, -, hσ, hinv⟩ := hI.win
  refine ⟨hx, hy, hnd, hlt, wf_tidyGens hx _, length_tidyGens hx _,
    wf_rawMul hσ (wf_normPerm hx _), ?_⟩
  show rawIsInvariant (tidyGens (I.1.1.2.2.2.1, I.2.1), I.1.1.1) = true
  rw [rawIsInvariant_eq_true_iff (wf_tidyGens hx _) hlt, decGroup_tidyGens hx]
  exact isInvariant_of_le ((rawIsInvariant_eq_true_iff hgs hlt).1 hinv) hI.le

theorem decWinSI_dsCall {I : RawDS P Rp} (hI : DSWF repOf n I) (j : ℕ) :
    decWinSI n (dsCall repOf I j).1 = ⟨(decPerm n I.1.1.2.2.1 * decPerm n (repOf (I.2.2.1, j))) •
      (decGroup n I.2.1 : Set (Perm (Fin n))), winSet n I.1.1.1, decStrN n I.1.1.2.2.2.1,
      decStrN n I.1.1.2.2.2.2⟩ := by
  rw [decWinSI]
  congr 1
  rw [decCoset_some, decPerm_dsCall hI, decGroup_dsCall hI]

/-- **The fold of the descent walks the descent chain.** -/
theorem loopMatch_ds {I : RawDS P Rp} (hI : DSWF repOf n I) :
    ∀ (k j : ℕ), j + k = I.2.2.2 →
      ∀ (acc : Set (Perm (Fin n))) (s : RawCoset), decCoset n s = acc →
        LoopMatch (dsRound repOf) (fun J => decWinSI n J.1.1) (decCoset n) I k j s
          (descentChain (decGroup n I.2.1 : Set (Perm (Fin n))) (winSet n I.1.1.1)
            (decStrN n I.1.1.2.2.2.1) (decStrN n I.1.1.2.2.2.2) acc
            ((dsPerms repOf n I).drop j)) := by
  have hx : I.1.1.2.2.2.1.length = n := hI.win.1
  intro k
  induction k with
  | zero =>
      intro j hj acc s hs
      have hdrop : (dsPerms repOf n I).drop j = [] := by
        apply List.drop_eq_nil_of_le
        rw [dsPerms, List.length_map, List.length_range]; omega
      rw [hdrop, descentChain]
      exact LoopMatch.done 0 j s acc (dsChild_of_le repOf s (by omega)) hs
  | succ k ih =>
      intro j hj acc s hs
      have hjl : j < I.2.2.2 := by omega
      have hjl' : j < (dsPerms repOf n I).length := by
        rw [dsPerms, List.length_map, List.length_range]; exact hjl
      rw [List.drop_eq_getElem_cons hjl', descentChain]
      have hget : (dsPerms repOf n I)[j]
          = decPerm n I.1.1.2.2.1 * decPerm n (repOf (I.2.2.1, j)) := by
        simp [dsPerms]
      have hdec : decWinSI n (dsCall repOf I j, (dsJunk : RawGens × (Rp × ℕ))).1.1
          = ⟨(dsPerms repOf n I)[j] • (decGroup n I.2.1 : Set (Perm (Fin n))),
              winSet n I.1.1.1, decStrN n I.1.1.2.2.2.1, decStrN n I.1.1.2.2.2.2⟩ := by
        rw [hget]; exact decWinSI_dsCall hI _
      rw [← hdec]
      refine LoopMatch.call k j s _ _ (dsChild_of_lt repOf s hjl) ?_
      intro a ha
      refine ih (j + 1) (by omega) _ ((dsRound repOf).combine (I, j, s, a)) ?_
      show decCoset n (rawCosetJoin (I.1.1.2.2.2.1, s, a)) = _
      rw [decCoset_rawCosetJoin hx, hs, ha]

/-- `σ • ⋃ r H = ⋃ (σ r) H`, over a list of indices. -/
theorem smul_biUnion_list {Γ β : Type*} [Group Γ] (σ₀ : Γ) (L : List β) (f : β → Γ)
    (H : Set Γ) :
    σ₀ • (⋃ j ∈ L, f j • H) = ⋃ σ ∈ L.map (fun j => σ₀ * f j), σ • H := by
  ext u
  have key : ∀ j : β, ((σ₀ * f j)⁻¹ * u ∈ H) ↔ ((f j)⁻¹ * (σ₀⁻¹ * u) ∈ H) := by
    intro j
    rw [show (σ₀ * f j)⁻¹ * u = (f j)⁻¹ * (σ₀⁻¹ * u) by group]
  simp only [Set.mem_smul_set_iff_inv_smul_mem, Set.mem_iUnion, exists_prop, List.mem_map,
    smul_eq_mul]
  constructor
  · rintro ⟨j, hj, hu⟩
    exact ⟨σ₀ * f j, ⟨j, hj, rfl⟩, (key j).2 hu⟩
  · rintro ⟨ρ, ⟨j, hj, rfl⟩, hu⟩
    exact ⟨j, hj, (key j).1 hu⟩

variable (repOf)

/-- The normalized answer to a descent call. -/
def dsAns (ansQ : RawWinSI × P → RawCoset) (J : RawDS P Rp) : RawCoset :=
  lcNormAns (J.1.1.2.2.2.1, ansQ J.1)

/-- The output of the descent, with the calls answered by `ansQ` (normalized). -/
def dsOut (ansQ : RawWinSI × P → RawCoset) (I : RawDS P Rp) : RawCoset :=
  (dsRound repOf).loopAux (dsAns ansQ) I.2.2.2 I 0 none

variable {repOf}

/-- **The descent, what it computes** (Prop. 11.1.6, Eq. (62)).  If `ansQ` answers every call,
the fold returns `Iso^Δ_{σG}(x, y)`, and its calls are exactly the `k` instances
`(Δ, H, σr_j, x, y)`. -/
theorem ds_spec {ansQ : RawWinSI × P → RawCoset} {I : RawDS P Rp} (hI : DSWF repOf n I)
    (hQ : ∀ j < I.2.2.2, decCoset n (ansQ (dsCall repOf I j))
      = (decWinSI n (dsCall repOf I j).1).answer) :
    decCoset n (dsOut repOf ansQ I) = (decWinSI n I.1.1).answer ∧
      ((dsRound repOf).loopCalls (dsAns ansQ) I.2.2.2 I 0 none).map Prod.fst
        = (List.range I.2.2.2).map (dsCall repOf I) := by
  have hx : I.1.1.2.2.2.1.length = n := hI.win.1
  have hcalls := ds_loopCalls repOf (dsAns ansQ) I I.2.2.2 0 none (by omega)
  refine ⟨?_, by rw [hcalls, List.drop_zero, List.map_map]; rfl⟩
  have hlm := loopMatch_ds hI I.2.2.2 0 (by omega) ∅ none rfl
  rw [List.drop_zero] at hlm
  have hgood : ∀ (j : ℕ) (s : RawCoset) (J : RawDS P Rp), (dsRound repOf).child (I, j, s) = some J →
      ∃ i < I.2.2.2, J = (dsCall repOf I i, dsJunk) := by
    intro j s J hc
    by_cases hj : j < I.2.2.2
    · rw [dsChild_of_lt repOf s hj] at hc
      exact ⟨j, hj, (Option.some.inj hc).symm⟩
    · rw [dsChild_of_le repOf s (by omega)] at hc; exact absurd hc (by simp)
  have hrec : ∀ J, (∃ i < I.2.2.2, J = (dsCall repOf I i, (dsJunk : RawGens × (Rp × ℕ)))) →
      decCoset n (dsAns ansQ J) = (decWinSI n J.1.1).answer := by
    rintro J ⟨i, hi, rfl⟩
    show decCoset n (lcNormAns (I.1.1.2.2.2.1, ansQ (dsCall repOf I i)))
      = (decWinSI n (dsCall repOf I i).1).answer
    rw [decCoset_lcNormAns hx]
    exact hQ i hi
  obtain ⟨hval, -⟩ := (dsRound repOf).loopAux_eq hgood hrec _ _ _ _ hlm
  rw [dsOut, hval]
  have hinv : Babai.IsInvariant (decGroup n I.1.1.2.1) (winSet n I.1.1.1) :=
    (rawIsInvariant_eq_true_iff hI.win.2.2.2.2.1 hI.win.2.2.2.1).1 hI.win.2.2.2.2.2.2.2
  have hK : (decWinSI n I.1.1).K
      = decPerm n I.1.1.2.2.1 • (decGroup n I.1.1.2.1 : Set (Perm (Fin n))) := by
    rw [decWinSI, decCoset_some]
  refine run_descentChain _ _ _ _ _ _ ?_ ?_
  · rw [hK, hI.cover, smul_biUnion_list]
    rfl
  · intro τ hτ
    refine ⟨Babai.wAutSubgroup (decGroup n I.1.1.2.1) (winSet n I.1.1.1) hinv
      (decStrN n I.1.1.2.2.2.1), ?_⟩
    have h := Babai.wIso_eq_smul_wAut (G := decGroup n I.1.1.2.1) (Δ := winSet n I.1.1.1) hinv
      (decPerm n I.1.1.2.2.1) (σ' := τ) (x := decStrN n I.1.1.2.2.2.1)
      (y := decStrN n I.1.1.2.2.2.2) (by rwa [← hK])
    rw [hK, h]
    rfl

end Descent

/-! ## The descent on the RAM -/

/-- **One call, normalized**, for calls of any type carrying the string `x`: the version of
`Algo.exists_normProg` for an arbitrary call type. -/
theorem exists_normProgG {β : Type} [Enc β] [Inhabited β] (xf : β → RawStr) (hxf : PolyFun xf)
    (hxs : ∀ b, Enc.size (xf b) ≤ Enc.size b) (S : ℕ → ℕ) (hS : PolyBound S) :
    ∃ (N : Program → Program) (c d : ℕ), ∀ Q : Program, Wf Q → Wf (N Q) ∧
      ∀ (ansQ : β → RawCoset) (W : β) (τ : ℕ),
        RunsOn 16 Q W (ansQ W) τ → Enc.size (ansQ W) ≤ S (Enc.size W) →
        RunsOn 16 (N Q) W (lcNormAns (xf W, ansQ W)) (10 * τ + pw c d (Enc.size W)) := by
  obtain ⟨Px, c1, d1, hPx, -⟩ := polyFun_witness hxf
  obtain ⟨Pn, c2, d2, hPn, -⟩ := polyFun_witness polyFun_lcNormAns
  obtain ⟨G, hGd⟩ : ∃ G : ℕ → ℕ, ∀ m, G m = 19 * m + 19 * m + 19 * S m + 10 * pw c1 d1 m + 376
      + pw c2 d2 (2 * m + 2 * S m) := ⟨_, fun _ => rfl⟩
  have hG : PolyBound G := by
    have e : G = fun m => 19 * m + 19 * m + 19 * S m + 10 * pw c1 d1 m + 376
        + pw c2 d2 (2 * m + 2 * S m) := funext hGd
    rw [e]
    exact (((((polyBound_const 19).mul polyBound_id).add ((polyBound_const 19).mul polyBound_id)).add
      ((polyBound_const 19).mul hS)).add ((polyBound_const 10).mul (polyBound_pw c1 d1))).add
      (polyBound_const 376) |>.add ((polyBound_pw c2 d2).comp
        (((polyBound_const 2).mul polyBound_id).add ((polyBound_const 2).mul hS)))
  obtain ⟨c, d, hcd⟩ := hG
  refine ⟨fun Q => RAM.seq (Pairing.pairProg 16 Px Q) Pn, c, d, fun Q hQ =>
    ⟨wf_seq (Pairing.wf_pairProg 16 (CleanComputeAt.wf' hPx) hQ) (CleanComputeAt.wf' hPn), ?_⟩⟩
  intro ansQ W τ hrun hsz
  have r := (RunsOn.pair (K := 16) (by omega) (hPx.runsOn W) hrun).seq
    (hPn.runsOn ((xf W, ansQ W) : RawStr × RawCoset))
  refine r.mono ?_
  have hxW : Enc.size (xf W) ≤ Enc.size W := hxs W
  have hp : Enc.size ((xf W, ansQ W) : RawStr × RawCoset)
      ≤ 2 * Enc.size W + 2 * S (Enc.size W) := by
    have := size_pair_le' ((xf W, ansQ W) : RawStr × RawCoset)
    simp only at this
    omega
  have e1 : c2 * (Enc.size ((xf W, ansQ W) : RawStr × RawCoset) + 1) ^ d2
      ≤ pw c2 d2 (2 * Enc.size W + 2 * S (Enc.size W)) := pw_mono c2 d2 hp
  have e2 := hcd (Enc.size W)
  rw [hGd] at e2
  have e3 : c1 * (Enc.size W + 1) ^ d1 = pw c1 d1 (Enc.size W) := rfl
  have e4 : c * (Enc.size W + 1) ^ d = pw c d (Enc.size W) := rfl
  simp only at e1
  omega


section DescentRAM

variable {P Rp : Type} [Enc P] [Inhabited P] [Enc Rp] [Inhabited Rp]
  {repOf : Rp × ℕ → RawPerm}

theorem polyFun_dsCall (hrep : PolyFun repOf) :
    PolyFun (fun z : RawDS P Rp × ℕ => dsCall repOf z.1 z.2) := by
  have hW : PolyFun (fun z : RawDS P Rp × ℕ => z.1.1.1) :=
    (polyFun_fst.comp polyFun_fst).comp polyFun_fst
  have hx : PolyFun (fun z : RawDS P Rp × ℕ => z.1.1.1.2.2.2.1) :=
    hW.comp (((polyFun_snd.comp polyFun_snd).comp polyFun_snd).comp polyFun_fst)
  have hy : PolyFun (fun z : RawDS P Rp × ℕ => z.1.1.1.2.2.2.2) :=
    hW.comp (((polyFun_snd.comp polyFun_snd).comp polyFun_snd).comp polyFun_snd)
  have hΔ : PolyFun (fun z : RawDS P Rp × ℕ => z.1.1.1.1) := hW.comp polyFun_fst
  have hσ : PolyFun (fun z : RawDS P Rp × ℕ => z.1.1.1.2.2.1) :=
    hW.comp ((polyFun_snd.comp polyFun_snd).comp polyFun_fst)
  have hH : PolyFun (fun z : RawDS P Rp × ℕ => z.1.2.1) :=
    (polyFun_fst.comp polyFun_snd).comp polyFun_fst
  have hpay : PolyFun (fun z : RawDS P Rp × ℕ => z.1.1.2) :=
    (polyFun_fst.comp polyFun_fst).comp polyFun_snd
  have hρ : PolyFun (fun z : RawDS P Rp × ℕ => repOf (z.1.2.2.1, z.2)) :=
    ((((polyFun_fst.comp polyFun_snd).comp polyFun_snd).comp polyFun_fst).pair polyFun_snd).comp
      hrep
  have htg : PolyFun (fun z : RawDS P Rp × ℕ => tidyGens (z.1.1.1.2.2.2.1, z.1.2.1)) :=
    (hx.pair hH).comp polyFun_tidyGens
  have hrp : PolyFun (fun z : RawDS P Rp × ℕ =>
      rawMul (z.1.1.1.2.2.1, normPerm (z.1.1.1.2.2.2.1, repOf (z.1.2.2.1, z.2)))) :=
    (hσ.pair ((hx.pair hρ).comp polyFun_normPerm)).comp polyFun_rawMul
  exact ((hΔ.pair (htg.pair (hrp.pair (hx.pair hy)))).pair hpay).of_eq (fun _ => rfl)

theorem polyFun_dsChild (hrep : PolyFun repOf) :
    PolyFun (dsChild repOf : RawDS P Rp × ℕ × RawCoset → Option (RawDS P Rp)) := by
  have hc : PolyFun (fun p : RawDS P Rp × ℕ × RawCoset => decide (p.2.1 < p.1.2.2.2)) :=
    (((polyFun_snd.comp polyFun_fst).add (polyFun_const 1)).le
      (((polyFun_fst.comp polyFun_snd).comp polyFun_snd).comp polyFun_snd)).of_eq
      (fun p => by simp [Nat.succ_le_iff])
  have hcall : PolyFun (fun p : RawDS P Rp × ℕ × RawCoset => dsCall repOf p.1 p.2.1) :=
    (polyFun_fst.pair (polyFun_snd.comp polyFun_fst)).comp (polyFun_dsCall hrep)
  have hsome : PolyFun (fun p : RawDS P Rp × ℕ × RawCoset =>
      (some (dsCall repOf p.1 p.2.1, (dsJunk : RawGens × (Rp × ℕ))) : Option (RawDS P Rp))) :=
    (hcall.pair (polyFun_const (dsJunk : RawGens × (Rp × ℕ)))).comp polyFun_some
  exact (PolyFun.ite hc hsome (polyFun_const (none : Option (RawDS P Rp)))).of_eq (fun p => by
    by_cases h : p.2.1 < p.1.2.2.2 <;> simp [dsChild, h])

theorem polyFun_dsCombine : PolyFun (dsRound (P := P) repOf).combine :=
  ((((((polyFun_fst.comp polyFun_fst).comp polyFun_fst).comp polyFun_snd).comp
    polyFun_snd).comp polyFun_snd |>.comp polyFun_fst).pair
    (((polyFun_snd.comp polyFun_snd).comp polyFun_fst).pair
      ((polyFun_snd.comp polyFun_snd).comp polyFun_snd))).comp polyFun_rawCosetJoin |>.of_eq
    (fun _ => rfl)

theorem polyFun_dsInit : PolyFun (dsRound (P := P) repOf).init :=
  (polyFun_none : PolyFun (fun _ : RawDS P Rp => (none : RawCoset))).of_eq (fun _ => rfl)

theorem polyFun_dsFinish : PolyFun (dsRound (P := P) repOf).finish := polyFun_snd.of_eq (fun _ => rfl)

theorem polyFun_dsWidth : PolyFun (fun I : RawDS P Rp => I.2.2.2) :=
  ((polyFun_snd.comp polyFun_snd).comp polyFun_snd)

theorem two_le_chainBound (m : ℕ) : 2 ≤ chainBound m := by
  unfold chainBound; omega

set_option maxHeartbeats 4000000 in
/-- **The descent on the RAM** (Prop. 11.1.6, Eq. (62)).  One program transformer `F`: for
every program `Q` that runs on the calls `(Δ, H, σr_j, x, y)` with polynomially small answers,
`F Q` runs the descent (`Algo.dsOut`, correct by `Algo.ds_spec`) within
`1000 · ∑_j τ(call j) + (k + 2) · poly(size)` steps, `k` the number of representatives. -/
theorem exists_dsProg (hrep : PolyFun repOf) (S : ℕ → ℕ) (hS : PolyBound S) :
    ∃ (F : Program → Program) (c d : ℕ), ∀ Q : Program, Wf Q → Wf (F Q) ∧
      ∀ (n : ℕ) (ansQ : RawWinSI × P → RawCoset) (τ : RawWinSI × P → ℕ) (I : RawDS P Rp),
        DSWF repOf n I →
        (∀ j < I.2.2.2, RunsOn 16 Q (dsCall repOf I j) (ansQ (dsCall repOf I j))
            (τ (dsCall repOf I j)) ∧
          Enc.size (ansQ (dsCall repOf I j)) ≤ S (Enc.size (dsCall repOf I j))) →
        RunsOn 16 (F Q) I (dsOut repOf ansQ I)
          (1000 * (((List.range I.2.2.2).map (dsCall repOf I)).map τ).sum
            + (I.2.2.2 + 2) * pw c d (Enc.size I)) := by
  obtain ⟨N, cN, dN, hN⟩ := exists_normProgG (β := RawWinSI × P) (fun W => W.1.2.2.2.1)
    (polyFun_fst.comp (((polyFun_snd.comp polyFun_snd).comp polyFun_snd).comp polyFun_fst))
    (fun W => le_trans (size_fst_le' _) (le_trans (size_snd_le' _) (le_trans (size_snd_le' _)
      (le_trans (size_snd_le' _) (size_fst_le' W))))) S hS
  obtain ⟨F0, c0, d0, hF0⟩ := (dsRound (P := P) repOf).exists_foldProg (polyFun_dsChild hrep)
    polyFun_dsCombine polyFun_dsInit polyFun_dsFinish polyFun_dsWidth
  obtain ⟨Pf, cf, df, hPf, -⟩ :=
    polyFun_witness (polyFun_fst : PolyFun (fun I : RawDS P Rp => I.1))
  obtain ⟨D, hD⟩ : ∃ D, D = Enc.size (dsJunk : RawGens × (Rp × ℕ)) := ⟨_, rfl⟩
  obtain ⟨B, hBd⟩ : ∃ B : ℕ → ℕ, ∀ m, B m = 16 * (chainBound m + m + 2) + 2 * D :=
    ⟨_, fun _ => rfl⟩
  have hB : PolyBound B := by
    rw [show B = fun m => 16 * (chainBound m + m + 2) + 2 * D from funext hBd]
    exact ((polyBound_const 16).mul ((polyBound_chainBound.add polyBound_id).add
      (polyBound_const 2))).add (polyBound_const _)
  obtain ⟨G, hGd⟩ : ∃ G : ℕ → ℕ, ∀ m, G m = 100 * (pw cf df (B m) + pw cN dN (B m))
      + pw c0 d0 (B m) := ⟨_, fun _ => rfl⟩
  have hG : PolyBound G := by
    rw [show G = fun m => 100 * (pw cf df (B m) + pw cN dN (B m))
      + pw c0 d0 (B m) from funext hGd]
    exact ((polyBound_const 100).mul (((polyBound_pw cf df).comp hB).add
      ((polyBound_pw cN dN).comp hB))).add ((polyBound_pw c0 d0).comp hB)
  obtain ⟨c, d, hcd⟩ := hG
  let L : Program → Program := fun Q => RAM.seq Pf (N Q)
  refine ⟨fun Q => F0 (L Q), c, d, fun Q hQwf => ?_⟩
  have hNwf := (hN Q hQwf).1
  have hLwf : Wf (L Q) := wf_seq (CleanComputeAt.wf' hPf) hNwf
  obtain ⟨hFwf, hFrun⟩ := hF0 (L Q) hLwf
  refine ⟨hFwf default, ?_⟩
  intro n ansQ τ I hI hQ
  obtain ⟨m, hm⟩ : ∃ m, m = Enc.size I := ⟨_, rfl⟩
  have hGm := hcd m
  rw [hGd] at hGm
  have hx : I.1.1.2.2.2.1.length = n := hI.win.1
  have hsm : Enc.size I.1.1.2.2.2 ≤ m :=
    hm ▸ le_trans (size_snd_le' _) (le_trans (size_snd_le' _) (le_trans (size_snd_le' _)
      (le_trans (size_fst_le' _) (size_fst_le' I))))
  have hnm : n ≤ m := le_trans (le_size_strings hI.win) hsm
  have hcbn : chainBound n ≤ chainBound m := mono_chainBound hnm
  have hBm : B m = 16 * (chainBound m + m + 2) + 2 * D := hBd m
  have epc : c * (m + 1) ^ d = pw c d m := rfl
  let ans : RawDS P Rp → RawCoset := dsAns ansQ
  let τ' : RawDS P Rp → ℕ := fun J =>
    cf * (Enc.size J + 1) ^ df + (10 * τ J.1 + pw cN dN (Enc.size J.1))
  have hcalls := ds_loopCalls repOf ans I I.2.2.2 0 none (by omega)
  rw [List.drop_zero] at hcalls
  have hcallSize : ∀ j, Enc.size (dsCall repOf I j) ≤ 2 * chainBound m + 2 * m := by
    intro j
    have h1 : Enc.size (dsCall repOf I j).1
        ≤ chainBound (Enc.size (dsCall repOf I j).1.2.2.2) := size_winSI_le (dsCall_wf hI j)
    have h1' : (dsCall repOf I j).1.2.2.2 = I.1.1.2.2.2 := rfl
    rw [h1'] at h1
    have h1'' := mono_chainBound hsm
    have h2 := size_pair_le' (dsCall repOf I j)
    have h3 : Enc.size (dsCall repOf I j).2 ≤ m := by
      show Enc.size I.1.2 ≤ m
      rw [hm]; exact le_trans (size_snd_le' _) (size_fst_le' I)
    omega
  have hJsize : ∀ j, Enc.size ((dsCall repOf I j, dsJunk) : RawDS P Rp) ≤ B m ∧
      Enc.size (dsCall repOf I j) ≤ B m := by
    intro j
    have h1 := size_pair_le' ((dsCall repOf I j, dsJunk) : RawDS P Rp)
    have h3 := hcallSize j
    simp only at h1
    rw [hBm, hD]
    omega
  have hansSize : ∀ j, Enc.size (ans (dsCall repOf I j, dsJunk)) ≤ chainBound m := by
    intro j
    show Enc.size (lcNormAns (I.1.1.2.2.2.1, ansQ (dsCall repOf I j))) ≤ _
    exact le_trans (size_lcNormAns_le (le_of_eq hx) _) hcbn
  have hcallsF : ∀ J ∈ (dsRound repOf).loopCalls ans (I.2.2.2) I 0 ((dsRound repOf).init I),
      RunsOn 16 (L Q) J (ans J) (τ' J) ∧ Enc.size J ≤ B m ∧ Enc.size (ans J) ≤ B m := by
    intro J hJ
    rw [show (dsRound repOf).init I = none from rfl, hcalls, List.mem_map] at hJ
    obtain ⟨j, hj, rfl⟩ := hJ
    obtain ⟨hQrun, hQsz⟩ := hQ j (List.mem_range.1 hj)
    refine ⟨(hPf.runsOn _).seq ((hN Q hQwf).2 ansQ _ _ hQrun hQsz), (hJsize j).1, ?_⟩
    have := hansSize j
    rw [hBm]; omega
  have hstatesF : ∀ k ≤ I.2.2.2,
      Enc.size (((dsRound repOf).foldStep ans)^[k] ((I, 0, (dsRound repOf).init I), false))
        ≤ B m := by
    intro k _
    obtain ⟨j', s', b', he, hj', hs'⟩ := (dsRound repOf).foldStep_iterate_inv ans I
      (fun j s => j ≤ I.2.2.2 ∧ Enc.size s ≤ chainBound (Enc.size I.1.1.2.2.2))
      (fun j s J hP hc => ⟨(dsRound repOf).lt_width_of_child hc, by
        show Enc.size (rawCosetJoin (I.1.1.2.2.2.1, s, ans J)) ≤ _
        have hj : j < I.2.2.2 := (dsRound repOf).lt_width_of_child hc
        rw [dsChild_of_lt repOf s hj] at hc
        have hJ := (Option.some.inj hc).symm
        have ha : Enc.size (ans J) ≤ chainBound (Enc.size I.1.1.2.2.2) := by
          rw [hJ]
          show Enc.size (lcNormAns (I.1.1.2.2.2.1, ansQ (dsCall repOf I j))) ≤ _
          exact le_trans (size_lcNormAns_le (le_of_eq hx) _)
            (mono_chainBound (le_size_strings hI.win))
        exact size_rawCosetJoin_le hx (le_size_strings hI.win) (le_refl _) hP.2 ha⟩)
      k 0 ((dsRound repOf).init I) false ⟨Nat.zero_le _, by
        show Enc.size (none : RawCoset) ≤ _
        rw [size_none]; exact two_le_chainBound _⟩
    rw [he]
    have h1 := Round.size_foldSt_le I j' s' b'
    have h2 : Enc.size j' ≤ Enc.size I.2.2.2 := size_nat_le_of_le hj'
    have h3 : Enc.size I.2.2.2 ≤ Enc.size I :=
      le_trans (size_snd_le' _) (le_trans (size_snd_le' _) (size_snd_le' I))
    have h4 := mono_chainBound hsm
    rw [hBm]
    omega
  have r := hFrun ans τ' I (B m) hcallsF hstatesF
  refine r.mono ?_
  rw [show (dsRound repOf).init I = none from rfl, hcalls]
  have hsum := sum_map_le_of_le ((List.range I.2.2.2).map
    (fun j => ((dsCall repOf I j, dsJunk) : RawDS P Rp))) τ'
    (fun J => τ J.1) 10 (pw cf df (B m) + pw cN dN (B m)) (fun J hJ => by
      rw [List.mem_map] at hJ
      obtain ⟨j, -, rfl⟩ := hJ
      obtain ⟨hJs, hJ1⟩ := hJsize j
      have e1 : cf * (Enc.size ((dsCall repOf I j, dsJunk) : RawDS P Rp) + 1) ^ df
          ≤ pw cf df (B m) := pw_mono cf df hJs
      have e2 : pw cN dN (Enc.size (dsCall repOf I j)) ≤ pw cN dN (B m) := pw_mono cN dN hJ1
      show cf * (Enc.size ((dsCall repOf I j, dsJunk) : RawDS P Rp) + 1) ^ df
          + (10 * τ (dsCall repOf I j) + pw cN dN (Enc.size (dsCall repOf I j)))
        ≤ 10 * τ (dsCall repOf I j) + (pw cf df (B m) + pw cN dN (B m))
      omega)
  have hmap : ((List.range I.2.2.2).map (dsCall repOf I)).map τ
      = ((List.range I.2.2.2).map (fun j => ((dsCall repOf I j, dsJunk) : RawDS P Rp))).map
          (fun J => τ J.1) := by
    simp only [List.map_map]; rfl
  rw [hmap, ← hm]
  simp only [List.length_map, List.length_range] at hsum ⊢
  set K := pw cf df (B m) + pw cN dN (B m)
  have e1 : I.2.2.2 * K ≤ (I.2.2.2 + 2) * K := Nat.mul_le_mul_right _ (by omega)
  have e3 : (I.2.2.2 + 2) * (100 * K + pw c0 d0 (B m))
      ≤ (I.2.2.2 + 2) * pw c d m := Nat.mul_le_mul_left _ (by omega)
  have e4 : (I.2.2.2 + 2) * (100 * K + pw c0 d0 (B m))
      = 100 * ((I.2.2.2 + 2) * K) + (I.2.2.2 + 2) * pw c0 d0 (B m) := by ring
  omega

end DescentRAM

/-! # Theorem 11.1.9 (Imprimitive Luks reduction) on the RAM

> Let `G ≤ S(Ω)` and let `Δ ⊆ Ω` be a `G`-invariant subset.  Let `{B₁,…,B_m}` be a
> `G`-invariant partition of `Δ`.  Let `ψ : G → Ḡ ≤ S_m` be the induced action of `G` on the
> set of blocks and let `N = ker(ψ)`.  Then finding `Iso^Δ_G(x,y)` reduces to `m|Ḡ| = m|G/N|`
> instances of finding `Iso^{B_i}_{M_i}(x, y^{σ_i})` for the blocks `B_i` and certain
> subgroups `M_i ≤ N` and `σ_i ∈ G`.  (The cost of the reduction is polynomial per instance.)
>
> *Proof.*  First descend to `N = ker ψ`.  Then consider each `B_i` to be the window in
> succession, reducing the group at each round, following the Chain Rule.  In the end, combine
> all the results into a single coset.

The program follows the proof: it computes generators of `N` (Prop. 2.2.6 (a) for the block
action, `Algo.impKer`) and `|Ḡ|` (`Algo.rawOrder` of the images of the generators on the
blocks), descends to `N` over the `|Ḡ|` coset representatives (`Algo.dsRound` with
`Algo.blockCosetRep`), and answers each coset by the Chain Rule over the `m` blocks
(`Algo.wlRound`).  The instances it hands on are the calls of the Chain Rule: at most `m|Ḡ|`
of them, each on a block `B_i` with a subgroup `M_i ≤ N` and a representative in `σG`
(`Algo.theorem_11_1_9_ram_spec`).  Its running time is at most `10⁶` times the time spent in
the calls plus `(m|Ḡ| + 1)` times a polynomial in the input (`Algo.theorem_11_1_9_ram`). -/

/-- The input of Theorem 11.1.9: an instance with its window `Δ`, and the list of blocks. -/
abbrev RawImpIn := RawWinSI × RawBlocks

/-- **The hypotheses of Theorem 11.1.9** on a raw input: a well-formed instance (the window `Δ`
is `G`-invariant), a list of distinct nonempty disjoint blocks, and the blocks form a
`G`-invariant partition of `Δ`. -/
def ImpInWF (n : ℕ) (I : RawImpIn) : Prop :=
  WinWF n I.1 ∧ BlocksWF n I.2 ∧
    Babai.IsInvariantPartitionOn (decGroup n I.1.2.1) (winSet n I.1.1) (blockSets n I.2)

/-- `|Ḡ|`: the order of the group generated by the images of the generators on the blocks. -/
def impIdx (I : RawImpIn) : ℕ := rawOrder (blkDom I.2, rawBlockImgs (I.2, I.1.2.1))

/-- The parameter of the coset representatives of `N`. -/
abbrev ImpRp := (List ℕ × RawGens) × RawBlocks

/-- **The descent to `N`**: the descent instance whose calls are the `|Ḡ|` cosets of `N`, each
carrying the blocks. -/
def impPrep (I : RawImpIn) : RawDS RawBlocks ImpRp :=
  (I, (impKer I.1 I.2, (((I.1.2.2.2.1, I.1.2.1), I.2), impIdx I)))

/-- The output of the reduction, with the instances answered by `ansQ`. -/
def impOut (ansQ : RawWinSI → RawCoset) (I : RawImpIn) : RawCoset :=
  dsOut blockCosetRep (wlOut ansQ) (impPrep I)

/-- The coset calls of the descent. -/
def impCosets (I : RawImpIn) : List RawWinList :=
  (List.range (impIdx I)).map (dsCall blockCosetRep (impPrep I))

/-- **The instances handed on**: the calls of the Chain Rule in every coset. -/
def impCalls (ansQ : RawWinSI → RawCoset) (I : RawImpIn) : List RawWinSI :=
  (impCosets I).flatMap (wlCalls ansQ)

theorem size_wlOut_le (ansQ : RawWinSI → RawCoset) (J : RawWinList) :
    Enc.size (wlOut ansQ J) ≤ chainBound (Enc.size J) + 4 * Enc.size J + 2 := by
  obtain ⟨s', hs', he⟩ := wlRound.loopAux_inv (wlAns ansQ) J
    (fun s => Enc.size s ≤ chainBound (Enc.size J) + 4 * Enc.size J + 2)
    (fun j s J' _ hc => by
      obtain ⟨g, τ, -, -, -, rfl⟩ := wlChild_eq_some hc
      show Enc.size (lcNormAns (J.1.2.2.2.1, ansQ _)) ≤ _
      refine le_trans (size_lcNormAns_le (le_refl J.1.2.2.2.1.length) _) ?_
      have h2 : J.1.2.2.2.1.length ≤ Enc.size J :=
        le_trans (length_le_size _) (le_trans (size_fst_le' _) (le_trans (size_snd_le' _)
          (le_trans (size_snd_le' _) (le_trans (size_snd_le' _) (size_fst_le' J)))))
      have h3 := mono_chainBound h2
      omega)
    J.2.length 0 (wlRound.init J) (by have := size_wlInit_le J; omega)
  rw [wlOut, he]
  exact hs'

section Spec

variable {I : RawImpIn}

theorem ImpInWF.hperm (hI : ImpInWF n I) :
    ∀ σ ∈ genGroup (descGens n I.1), ∀ B ∈ blockSets n I.2,
      (σ : Perm (Fin n)) '' B ∈ blockSets n I.2 := hI.2.2.permutes

/-- The action `ψ` on the blocks, read through the numbering of the blocks. -/
noncomputable def ImpInWF.phi (hI : ImpInWF n I) : genGroup (descGens n I.1) →* Perm (Fin I.2.length) :=
  blockPhi n I.2 hI.2.1 (descGens n I.1) hI.hperm

theorem ImpInWF.imgs (hI : ImpInWF n I) :
    ImgsOf (descGens n I.1) (blockImgsOf n I.2 (descGens n I.1)) hI.phi :=
  imgsOf_blockPhi hI.2.1 hI.hperm

theorem ImpInWF.blockData (hI : ImpInWF n I) : BlockData n I.2 (descGens n I.1) :=
  (blockData_of_permutes hI.2.1 hI.hperm).1

theorem ImpInWF.gens_eq (hI : ImpInWF n I) : I.1.2.1 = (descGens n I.1).map (encPerm n) :=
  (map_encPerm_decPerm hI.1.2.2.2.2.1).symm

/-- `impIdx` is the number of cosets of `N` the transversal produces. -/
theorem impIdx_eq (hI : ImpInWF n I) :
    impIdx I = blockCosetIndex n I.1.2.2.2.1 I.2 (descGens n I.1) := by
  have hwf := hI.blockData.1
  have e : impIdx I = rawOrder (blkDom I.2, rawBlockImgs (I.2, (descGens n I.1).map (encPerm n))) := by
    rw [impIdx, ← hI.gens_eq]
  rw [e, rawBlockImgs_eq_map_encPerm hwf, rawOrder_spec _ (length_blkDom _),
    ← hI.imgs.range_eq_genGroup, blockCosetIndex_eq_card_range hI.1.1 hI.imgs]

/-- **`impIdx` is `|Ḡ|`**, the order of the group induced on the blocks. -/
theorem impIdx_eq_card (hI : ImpInWF n I) :
    impIdx I = Nat.card (Babai.onBlocks (decGroup n I.1.2.1) (blockSets n I.2) hI.2.2.permutes) := by
  rw [impIdx_eq hI]
  exact blockCosetIndex_eq_card_onBlocks hI.1.1 hI.2.1 hI.hperm

theorem impIdx_le_one (hI : ImpInWF n I) (h0 : I.2.length = 0) : impIdx I ≤ 1 := by
  rw [impIdx_eq hI, blockCosetIndex_eq_card_range hI.1.1 hI.imgs]
  have h1 : Nat.card hI.phi.range ≤ Nat.card (Perm (Fin I.2.length)) :=
    Subgroup.card_le_card_group _
  have h2 : Nat.card (Perm (Fin I.2.length)) = 1 := by rw [h0]; simp
  omega

/-- The instance with its phase marker, to reuse `Algo.impKer_le` and
`Algo.decGroup_impKer`. -/
theorem ImpInWF.impWF (hI : ImpInWF n I) : ImpWF n (I.1, some (I.2, impIdx I)) := by
  refine ⟨hI.1, ?_⟩
  intro bl idx h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  exact ⟨hI.2.1, hI.blockData, impIdx_eq hI⟩

/-- **`N = ker ψ`**: the subgroup descended to. -/
theorem decGroup_impKer_eq (hI : ImpInWF n I) :
    decGroup n (impKer I.1 I.2)
      = Babai.blockKernel (decGroup n I.1.2.1) (blockSets n I.2) hI.2.2.permutes := by
  rw [decGroup_impKer hI.impWF rfl hI.imgs]
  exact actKer_blockPhi hI.2.1 hI.hperm

/-- The descent instance is well formed. -/
theorem impPrep_wf (hI : ImpInWF n I) : DSWF blockCosetRep n (impPrep I) := by
  refine ⟨hI.1, ?_, ?_⟩
  · show decGroup n (impKer I.1 I.2) ≤ decGroup n I.1.2.1
    exact impKer_le (I := (I.1, some (I.2, impIdx I))) (bl := I.2) (idx := impIdx I)
      hI.impWF rfl
  show (decGroup n I.1.2.1 : Set (Perm (Fin n))) = ⋃ j ∈ List.range (impIdx I),
    decPerm n (blockCosetRep (((I.1.2.2.2.1, I.1.2.1), I.2), j)) •
      (decGroup n (impKer I.1 I.2) : Set (Perm (Fin n)))
  have hcov := cover_blockCosetRep hI.1.1 hI.blockData.1 hI.imgs
  rw [← hI.gens_eq, ← impIdx_eq hI, ← decGroup_impKer hI.impWF rfl hI.imgs] at hcov
  exact hcov

/-- Each coset call, with the blocks, is a well-formed chain instance. -/
theorem impCoset_wf (hI : ImpInWF n I) (j : ℕ) :
    WLWF n (dsCall blockCosetRep (impPrep I) j) := by
  refine ⟨dsCall_wf (impPrep_wf hI) j, ?_⟩
  intro B hB
  have hb := hI.2.1
  refine ⟨(List.nodup_flatten.1 hb.nodup).1 B hB,
    fun u hu => hb.lt u (List.mem_flatten.2 ⟨B, hB, hu⟩), ?_⟩
  show Babai.IsInvariant (decGroup n (dsCall blockCosetRep (impPrep I) j).1.2.1) (winSet n B)
  rw [decGroup_dsCall (impPrep_wf hI), show (impPrep I).2.1 = impKer I.1 I.2 from rfl,
    decGroup_impKer_eq hI]
  exact Babai.isInvariant_blockKernel ⟨B, hB, rfl⟩

theorem biUnion_blocks (hI : ImpInWF n I) : (⋃ B ∈ I.2, winSet n B) = winSet n I.1.1 := by
  rw [← hI.2.2.covers]
  ext u
  simp only [Set.mem_iUnion, Set.mem_sUnion, exists_prop, blockSets, Set.mem_image,
    Set.mem_setOf_eq]
  constructor
  · rintro ⟨B, hB, hu⟩; exact ⟨_, ⟨B, hB, rfl⟩, hu⟩
  · rintro ⟨_, ⟨B, hB, rfl⟩, hu⟩; exact ⟨B, hB, hu⟩

/-- The candidate set of each coset call lies in the candidate set of the input. -/
theorem impCoset_K_sub (hI : ImpInWF n I) (j : ℕ) (hj : j < impIdx I) :
    (decWinSI n (dsCall blockCosetRep (impPrep I) j).1).K ⊆ (decWinSI n I.1).K := by
  have hDS := impPrep_wf hI
  rw [decWinSI_dsCall hDS j]
  show _ ⊆ decCoset n (some (I.1.2.1, I.1.2.2.1))
  rw [decCoset_some]
  rintro ρ hρ
  rw [Set.mem_smul_set] at hρ ⊢
  obtain ⟨u, hu, rfl⟩ := hρ
  have hsub : decPerm n (blockCosetRep ((impPrep I).2.2.1, j)) •
      (decGroup n (impPrep I).2.1 : Set (Perm (Fin n))) ⊆ (decGroup n I.1.2.1 : Set _) := by
    have hc : (decGroup n I.1.2.1 : Set (Perm (Fin n))) = _ := hDS.cover
    rw [hc]
    exact Set.subset_biUnion_of_mem (u := fun j => decPerm n (blockCosetRep ((impPrep I).2.2.1, j)) •
      (decGroup n (impPrep I).2.1 : Set (Perm (Fin n)))) (List.mem_range.2 hj)
  refine ⟨decPerm n (blockCosetRep ((impPrep I).2.2.1, j)) * u, hsub ⟨u, hu, rfl⟩, ?_⟩
  simp only [smul_eq_mul, mul_assoc]
  rfl

/-- **Theorem 11.1.9 on the RAM, what the reduction computes.**  If `ansQ` answers every
well-formed instance, the reduction returns `Iso^Δ_{σG}(x, y)`; `impIdx I` is `|Ḡ|`; and the
instances handed on are at most `m|Ḡ|` well-formed instances, each on a block `B_i`, with a
subgroup `M_i ≤ N = ker ψ`, a representative in `σG`, and the strings `x, y`. -/
theorem theorem_11_1_9_ram_spec {ansQ : RawWinSI → RawCoset} (hI : ImpInWF n I)
    (hQ : ∀ W, WinWF n W → decCoset n (ansQ W) = (decWinSI n W).answer) :
    decCoset n (impOut ansQ I) = (decWinSI n I.1).answer ∧
      impIdx I = Nat.card (Babai.onBlocks (decGroup n I.1.2.1) (blockSets n I.2)
        hI.2.2.permutes) ∧
      (impCalls ansQ I).length ≤ I.2.length * impIdx I ∧
      ∀ W ∈ impCalls ansQ I, WinWF n W ∧ W.1 ∈ I.2 ∧
        decGroup n W.2.1 ≤ Babai.blockKernel (decGroup n I.1.2.1) (blockSets n I.2)
          hI.2.2.permutes ∧
        decPerm n W.2.2.1 ∈ (decWinSI n I.1).K ∧ W.2.2.2 = I.1.2.2.2 := by
  have hDS := impPrep_wf hI
  refine ⟨?_, impIdx_eq_card hI, ?_, ?_⟩
  · refine (ds_spec hDS (fun j _ => ?_)).1
    rw [(wl_spec (impCoset_wf hI j) hQ).1]
    show Babai.wIso (⋃ B ∈ I.2, winSet n B) _ _ _ = _
    rw [biUnion_blocks hI]
    rfl
  · rw [impCalls, List.length_flatMap]
    have h := sum_map_le_of_le (impCosets I) (fun J => (wlCalls ansQ J).length) (fun _ => 0) 0
      I.2.length (fun J hJ => by
        rw [impCosets, List.mem_map] at hJ
        obtain ⟨j, -, rfl⟩ := hJ
        have := (wl_spec (impCoset_wf hI j) hQ).2.1
        simpa using this)
    have hl : (impCosets I).length = impIdx I := by simp [impCosets]
    rw [hl, zero_mul, zero_add] at h
    rw [Nat.mul_comm]
    exact h
  · intro W hW
    rw [impCalls, List.mem_flatMap] at hW
    obtain ⟨J, hJ, hW⟩ := hW
    rw [impCosets, List.mem_map] at hJ
    obtain ⟨j, hj, rfl⟩ := hJ
    obtain ⟨hWf, hWmem, hWstr, hWle, hWrep⟩ := (wl_spec (impCoset_wf hI j) hQ).2.2 W hW
    refine ⟨hWf, hWmem, ?_, impCoset_K_sub hI j (List.mem_range.1 hj) hWrep, hWstr⟩
    have e : decGroup n (dsCall blockCosetRep (impPrep I) j).1.2.1
        = Babai.blockKernel (decGroup n I.1.2.1) (blockSets n I.2) hI.2.2.permutes := by
      rw [decGroup_dsCall hDS, show (impPrep I).2.1 = impKer I.1 I.2 from rfl,
        decGroup_impKer_eq hI]
    exact e ▸ hWle

end Spec

theorem polyFun_impPrep : PolyFun impPrep := by
  have hx : PolyFun (fun I : RawImpIn => I.1.2.2.2.1) :=
    (((polyFun_fst.comp polyFun_snd).comp polyFun_snd).comp polyFun_snd).comp polyFun_fst
  have hG : PolyFun (fun I : RawImpIn => I.1.2.1) := (polyFun_fst.comp polyFun_snd).comp polyFun_fst
  have hker : PolyFun (fun I : RawImpIn => impKer I.1 I.2) :=
    (polyFun_snd.pair polyFun_fst).comp polyFun_impKer
  have hidx : PolyFun impIdx :=
    ((polyFun_snd.comp polyFun_blkDom).pair ((polyFun_snd.pair hG).comp polyFun_rawBlockImgs)).comp
      polyFun_rawOrder
  exact (polyFun_id.pair (hker.pair (((hx.pair hG).pair polyFun_snd).pair hidx))).of_eq
    (fun _ => rfl)

theorem impIdx_mul_le {I : RawImpIn} (hI : ImpInWF n I) :
    impIdx I * (I.2.length + 2) ≤ 3 * (I.2.length * impIdx I + 1) ∧
      impIdx I + 2 ≤ 3 * (I.2.length * impIdx I + 1) := by
  rcases Nat.eq_zero_or_pos I.2.length with h0 | hpos
  · have := impIdx_le_one hI h0
    rw [h0]
    constructor <;> nlinarith
  · constructor <;> nlinarith

set_option maxHeartbeats 8000000 in
/-- **Theorem 11.1.9 on the RAM** (§11.1), the cost: "(The cost of the reduction is polynomial
per instance.)"  One program transformer `F`: for every program `Q` that answers the
well-formed instances with polynomially small answers, `F Q` runs the Imprimitive Luks
reduction within

  `10⁶ · ∑_{W ∈ calls} τ(W) + (m|Ḡ| + 1) · poly(size of the input)`

steps, where `τ(W)` is the number of steps of `Q` on the call `W`, `m` is the number of blocks
and `|Ḡ| = impIdx I` (`Algo.impIdx_eq_card`).  The calls are `Algo.impCalls`: at most `m|Ḡ|`
instances `Iso^{B_i}_{M_i}` with `M_i ≤ N`, and the output is `Iso^Δ_{σG}(x, y)`
(`Algo.theorem_11_1_9_ram_spec`). -/
theorem theorem_11_1_9_ram (S : ℕ → ℕ) (hS : PolyBound S) :
    ∃ (F : Program → Program) (c d : ℕ), ∀ Q : Program, Wf Q → Wf (F Q) ∧
      ∀ (n : ℕ) (ansQ : RawWinSI → RawCoset) (τ : RawWinSI → ℕ) (I : RawImpIn), ImpInWF n I →
        (∀ W, WinWF n W → RunsOn 16 Q W (ansQ W) (τ W) ∧ Enc.size (ansQ W) ≤ S (Enc.size W)) →
        RunsOn 16 (F Q) I (impOut ansQ I)
          (10 ^ 6 * ((impCalls ansQ I).map τ).sum
            + (I.2.length * impIdx I + 1) * pw c d (Enc.size I)) := by
  obtain ⟨FA, cA, dA, hFA⟩ := exists_wlProg S hS
  have hSB : PolyBound (fun m => chainBound m + 4 * m + 2) :=
    (polyBound_chainBound.add ((polyBound_const 4).mul polyBound_id)).add (polyBound_const 2)
  obtain ⟨FB, cB, dB, hFB⟩ := exists_dsProg (P := RawBlocks) (Rp := ImpRp)
    (repOf := blockCosetRep) polyFun_blockCosetRep (fun m => chainBound m + 4 * m + 2) hSB
  obtain ⟨Pp, cp, dp, hPp, hPps⟩ := polyFun_witness polyFun_impPrep
  obtain ⟨G, hGd⟩ : ∃ G : ℕ → ℕ, ∀ m, G m = pw cp dp m
      + 3000 * pw cA dA (2 * chainBound m + 2 * m) + 3 * pw cB dB (pw cp dp m) :=
    ⟨_, fun _ => rfl⟩
  have hG : PolyBound G := by
    rw [show G = fun m => pw cp dp m + 3000 * pw cA dA (2 * chainBound m + 2 * m)
      + 3 * pw cB dB (pw cp dp m) from funext hGd]
    exact ((polyBound_pw cp dp).add ((polyBound_const 3000).mul ((polyBound_pw cA dA).comp
      (((polyBound_const 2).mul polyBound_chainBound).add
        ((polyBound_const 2).mul polyBound_id))))).add
      ((polyBound_const 3).mul ((polyBound_pw cB dB).comp (polyBound_pw cp dp)))
  obtain ⟨c, d, hcd⟩ := hG
  refine ⟨fun Q => RAM.seq Pp (FB (FA Q)), c, d, fun Q hQwf => ?_⟩
  obtain ⟨hAwf, hArun⟩ := hFA Q hQwf
  obtain ⟨hBwf, hBrun⟩ := hFB (FA Q) hAwf
  refine ⟨wf_seq (CleanComputeAt.wf' hPp) hBwf, ?_⟩
  intro n ansQ τ I hI hQ
  obtain ⟨m, hm⟩ : ∃ m, m = Enc.size I := ⟨_, rfl⟩
  have hDS := impPrep_wf hI
  let τB : RawWinSI × RawBlocks → ℕ := fun J =>
    1000 * ((wlCalls ansQ J).map τ).sum + (J.2.length + 2) * pw cA dA (Enc.size J)
  have hB := hBrun n (wlOut ansQ) τB (impPrep I) hDS (fun j _ =>
    ⟨hArun n ansQ τ _ (impCoset_wf hI j) hQ, size_wlOut_le ansQ _⟩)
  have r := (hPp.runsOn I).seq hB
  refine r.mono ?_
  -- sizes
  have hsm : Enc.size I.1.2.2.2 ≤ m := hm ▸ le_trans (size_snd_le' _) (le_trans (size_snd_le' _)
    (le_trans (size_snd_le' _) (size_fst_le' I)))
  have hcallSize : ∀ j, Enc.size (dsCall blockCosetRep (impPrep I) j)
      ≤ 2 * chainBound m + 2 * m := by
    intro j
    have h1 : Enc.size (dsCall blockCosetRep (impPrep I) j).1
        ≤ chainBound (Enc.size (dsCall blockCosetRep (impPrep I) j).1.2.2.2) :=
      size_winSI_le (dsCall_wf hDS j)
    have h1' : (dsCall blockCosetRep (impPrep I) j).1.2.2.2 = I.1.2.2.2 := rfl
    rw [h1'] at h1
    have h1'' := mono_chainBound hsm
    have h2 := size_pair_le' (dsCall blockCosetRep (impPrep I) j)
    have h3 : Enc.size (dsCall blockCosetRep (impPrep I) j).2 ≤ m := by
      show Enc.size I.2 ≤ m
      rw [hm]; exact size_snd_le' I
    omega
  set idx := impIdx I with hidx
  set len := I.2.length with hlen
  set A := pw cA dA (2 * chainBound m + 2 * m) with hA
  have hsum := sum_map_le_of_le ((List.range idx).map (dsCall blockCosetRep (impPrep I))) τB
    (fun J => ((wlCalls ansQ J).map τ).sum) 1000 ((len + 2) * A) (fun J hJ => by
      rw [List.mem_map] at hJ
      obtain ⟨j, -, rfl⟩ := hJ
      have e1 : pw cA dA (Enc.size (dsCall blockCosetRep (impPrep I) j)) ≤ A :=
        pw_mono cA dA (hcallSize j)
      have e2 : (dsCall blockCosetRep (impPrep I) j).2.length = len := rfl
      show 1000 * ((wlCalls ansQ (dsCall blockCosetRep (impPrep I) j)).map τ).sum
          + ((dsCall blockCosetRep (impPrep I) j).2.length + 2)
            * pw cA dA (Enc.size (dsCall blockCosetRep (impPrep I) j))
        ≤ 1000 * ((wlCalls ansQ (dsCall blockCosetRep (impPrep I) j)).map τ).sum
          + (len + 2) * A
      rw [e2]
      exact Nat.add_le_add_left (Nat.mul_le_mul_left _ e1) _)
  have hflat : ((impCalls ansQ I).map τ).sum
      = (((List.range idx).map (dsCall blockCosetRep (impPrep I))).map
          (fun J => ((wlCalls ansQ J).map τ).sum)).sum :=
    sum_map_flatMap _ (wlCalls ansQ) τ
  simp only [List.length_map, List.length_range] at hsum
  have hprep : Enc.size (impPrep I) ≤ pw cp dp m := by rw [hm]; exact hPps I
  have eB : pw cB dB (Enc.size (impPrep I)) ≤ pw cB dB (pw cp dp m) := pw_mono cB dB hprep
  have eP : cp * (Enc.size I + 1) ^ dp = pw cp dp m := by rw [hm]; rfl
  have hGm := hcd m
  rw [hGd] at hGm
  have epc : c * (m + 1) ^ d = pw c d m := rfl
  obtain ⟨k1, k2⟩ := impIdx_mul_le hI
  rw [← hidx, ← hlen] at k1 k2
  have w1 : 1000 * (idx * ((len + 2) * A)) ≤ 3000 * ((len * idx + 1) * A) := by
    have := Nat.mul_le_mul_right A k1
    nlinarith
  have w2 : (idx + 2) * pw cB dB (Enc.size (impPrep I))
      ≤ 3 * ((len * idx + 1) * pw cB dB (pw cp dp m)) := by
    have := Nat.mul_le_mul k2 eB
    nlinarith
  have w3 : pw cp dp m ≤ (len * idx + 1) * pw cp dp m := Nat.le_mul_of_pos_left _ (by omega)
  have w4 : (len * idx + 1) * G m ≤ (len * idx + 1) * pw c d m :=
    Nat.mul_le_mul_left _ (by rw [hGd]; omega)
  have w5 : (len * idx + 1) * G m = (len * idx + 1) * pw cp dp m
      + 3000 * ((len * idx + 1) * A) + 3 * ((len * idx + 1) * pw cB dB (pw cp dp m)) := by
    rw [hGd]; ring
  rw [hflat, ← hm]
  have e6 : (impPrep I).2.2.2 = idx := rfl
  rw [e6]
  have eP' : cp * (m + 1) ^ dp = pw cp dp m := rfl
  rw [eP', show (10 : ℕ) ^ 6 = 1000000 by norm_num]
  generalize (((List.range idx).map (dsCall blockCosetRep (impPrep I))).map
    (fun J => ((wlCalls ansQ J).map τ).sum)).sum = S1 at hsum ⊢
  generalize (len * idx + 1) * pw cp dp m = Z at w3 w5
  generalize (len * idx + 1) * G m = X at w4 w5
  generalize (len * idx + 1) * A = T at w1 w5
  generalize (len * idx + 1) * pw cB dB (pw cp dp m) = U at w2 w5
  generalize idx * ((len + 2) * A) = Ii at w1 hsum
  generalize (len * idx + 1) * pw c d m = W at w4 ⊢
  generalize (idx + 2) * pw cB dB (Enc.size (impPrep I)) = V at w2 ⊢
  generalize pw cp dp m = z at w3 ⊢
  omega

end Algo
