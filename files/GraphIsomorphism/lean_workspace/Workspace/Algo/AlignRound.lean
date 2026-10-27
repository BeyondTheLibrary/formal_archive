/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: Procedure Align, lines 4-6 — the Chain Rule over the color classes
of `Ω`, as one round of the machine.
-/
import Workspace.Algo.AlignColorRaw
import Workspace.Algo.LocalCertLoop
import Workspace.Algo.PhaseChain
import Workspace.Canonical.Align

/-!
# Procedure Align, lines 4-6, as a round (§14.1)

> 4. … This coloring in turn lifts to a canonical coloring of `Ω` with corresponding color
>    classes `Ω₁, …, Ω_s`.
> 5. Apply the Chain Rule to the color classes `Ω_i`.
> 6. If `(∃ j)(|Δ_j| > m/2)` ("dominant color") then start the application of the Chain Rule
>    with the window `Ω(Δ_j)`.

Line 4's windows are `Workspace/Algo/AlignColorRaw.lean`; this file turns lines 5 and 6 into
an `Algo.Round`.

**The node.**  A node is a pair: an optional *header* and an ordinary window instance
(`Algo.RawWinSI`).  With a header — the giant representation `(G, ϕ)` as an
`Algo.RawAction`, and the coloring of `Γ` as an `Algo.RawLab` — the node runs lines 4-6: it
computes the windows and walks them with the Chain Rule.  Without a header the node is a
leaf: it is one of the instances line 5 calls, and the rest of Procedure
String-Isomorphism, the parameter `solve`, answers it.  So the children of an Align node
are ordinary window instances, as §14.1 asks, and they are nodes of this round only because
`Algo.Round` gives every node the same type.

**The form of the calls.**  The machine stays in *coset form*: a child is the instance
`⟨C, Ω_i ∩ Δ, x, y⟩` with the strings unshifted, where `C` is the coset the Chain Rule has
reached.  That is `Algo.cosetChain`, Eq. (63).  The paper's `Babai.alignChainReduction`
prints the same chain in the aligned group form; the two have the same value
(`Algo.run_alignRoundReduction_eq`), and `Algo.alignRed`
(`Workspace/Algo/AlignTransfer.lean`) is what turns one list of calls into the other.

**Why the windows are cut down to the window of the instance.**  At line 3 the window is
all of `Ω`, and there `Ω_i ∩ Ω = Ω_i`, so nothing is lost.  Cutting keeps the routine total
and makes the measure drop at every child.

## Main results

* `Algo.alignWins` — lines 4-6's list of windows, cut to the window of the instance;
* `Algo.alignRound` — the round, with `Algo.alignChild` for line 5's calls;
* `Algo.implements_alignRound` — **the link**: the fold of the round walks the chain,
  proved with the phase rule `Algo.phaseMatch_cosetChain`;
* `Algo.run_alignRoundReduction` — the chain computes the answer of the instance;
* `Algo.run_alignRoundReduction_eq` — its value is the value of
  `Babai.alignChainReduction`;
* `Algo.length_alignWins_le` — the number of calls lines 5-6 make;
* `Algo.alignCost` — the cost data of the round.

No axiom, no `sorry`.
-/

namespace Algo

open RAM RAM.Targets
open Equiv (Perm)

variable {n : ℕ}

/-! ## The node -/

/-- A node of the round: the header of lines 4-6 — the giant representation and the
coloring of `Γ` — and the window instance.  Without a header the node is one of the
instances line 5 calls. -/
abbrev RawAlignSI := Option (RawAction × RawLab) × RawWinSI

/-- The instance a node describes.  The header plays no part in it: it says which windows
the round walks, not which strings it compares. -/
noncomputable def decAlignSI (n : ℕ) (I : RawAlignSI) : Babai.SIInstance (Fin n) ℕ :=
  decWinSI n I.2

/-- Is this node an Align node (lines 4-6), or one of the instances it calls? -/
def alignIsNode (I : RawAlignSI) : Bool := I.1.elim false (fun _ => true)

theorem alignIsNode_eq_false_iff {I : RawAlignSI} : alignIsNode I = false ↔ I.1 = none := by
  cases h : I.1 <;> simp [alignIsNode, h]

theorem alignIsNode_eq_true_iff {I : RawAlignSI} :
    alignIsNode I = true ↔ ∃ q, I.1 = some q := by
  cases h : I.1 <;> simp [alignIsNode, h]

/-! ## Lines 4-6: the windows of one node -/

/-- A window of `Ω`, cut down to the window of the instance. -/
def alignCut (z : List ℕ × List ℕ) : List ℕ := z.1.filter (fun u => decide (u ∈ z.2))

theorem mem_alignCut {z : List ℕ × List ℕ} {u : ℕ} :
    u ∈ alignCut z ↔ u ∈ z.1 ∧ u ∈ z.2 := by
  rw [alignCut, List.mem_filter, decide_eq_true_iff]

theorem nodup_alignCut {z : List ℕ × List ℕ} (h : z.1.Nodup) : (alignCut z).Nodup :=
  List.Nodup.filter _ h

/-- Lines 4-6's windows for a header and a window. -/
def alignWinsOf (z : (RawAction × RawLab) × List ℕ) : List (List ℕ) :=
  (alignRWindows z.1).map (fun W => alignCut (W, z.2))

/-- §14.1, **lines 5 and 6**: the list of windows the Chain Rule of this node walks.  A
node with no header calls nothing. -/
def alignWins (I : RawAlignSI) : List (List ℕ) :=
  I.1.elim [] (fun q => alignWinsOf (q, I.2.1))

theorem alignWins_of_none {I : RawAlignSI} (h : I.1 = none) : alignWins I = [] := by
  rw [alignWins, h]; rfl

theorem alignWins_of_some {I : RawAlignSI} {q : RawAction × RawLab} (h : I.1 = some q) :
    alignWins I = (alignRWindows q).map (fun W => alignCut (W, I.2.1)) := by
  rw [alignWins, h]; rfl

/-- **The call bound of lines 5-6**: one call per color class of `Ω`, plus the window of
line 6. -/
theorem length_alignWins_le {I : RawAlignSI} {q : RawAction × RawLab} (h : I.1 = some q) :
    (alignWins I).length ≤ q.1.1.1.length + 1 := by
  rw [alignWins_of_some h, List.length_map]
  exact length_alignRWindows_le q

/-- What the `j`-th window is: a window of line 5 or 6, cut to the window of the
instance. -/
theorem getD_alignWins {I : RawAlignSI} {j : ℕ} (hj : j < (alignWins I).length) :
    ∃ q W, I.1 = some q ∧ W ∈ alignRWindows q ∧
      (alignWins I).getD j [] = alignCut (W, I.2.1) := by
  rcases hq : I.1 with _ | q
  · rw [alignWins_of_none hq] at hj; exact absurd hj (by simp)
  · have hw := alignWins_of_some hq
    rw [hw] at hj ⊢
    rw [List.length_map] at hj
    refine ⟨q, (alignRWindows q)[j]'hj, rfl, List.getElem_mem hj, ?_⟩
    rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map]

/-- Every window of the node is a repetition-free list of points of the instance's
window. -/
theorem alignWins_props {I : RawAlignSI} {j : ℕ} (hj : j < (alignWins I).length) :
    ((alignWins I).getD j []).Nodup ∧ ∀ u ∈ (alignWins I).getD j [], u ∈ I.2.1 := by
  obtain ⟨q, W, -, hW, hget⟩ := getD_alignWins hj
  rw [hget]
  exact ⟨nodup_alignCut (nodup_of_mem_alignRWindows hW), fun u hu => (mem_alignCut.1 hu).2⟩

/-! ## Well-formedness -/

/-- The header of an Align node is well formed for the degree `n` and the window instance
`J`: the two domain witnesses and the two generator lists are well formed, the coloring has
one entry per point of `Γ`, and — this is what line 4's canonicity gives
(`Babai.isInvariant_omegaColorClass`) — every window of lines 5-6 is invariant under the
group of the instance. -/
def AlignHdrWF (n : ℕ) (q : RawAction × RawLab) (J : RawWinSI) : Prop :=
  q.1.1.1.length = n ∧ (∀ a ∈ q.1.1.1, a < n) ∧
    q.1.2.1.length ≤ n ∧ (∀ a ∈ q.1.2.1, a < n) ∧
    RawGens.WF n q.1.1.2 ∧ q.1.1.2.length ≤ n * n ∧
    RawGens.WF q.1.2.1.length q.1.2.2 ∧ q.1.2.2.length ≤ n * n ∧
    q.2.length = q.1.2.1.length ∧ (∀ k ∈ q.2, k < n) ∧
    (∀ W ∈ alignRWindows q, rawIsInvariant (J.2.1, alignCut (W, J.1)) = true)

/-- A well-formed node: a well-formed window instance, and a well-formed header when there
is one. -/
def AlignWF (n : ℕ) (I : RawAlignSI) : Prop :=
  WinWF n I.2 ∧ ∀ q, I.1 = some q → AlignHdrWF n q I.2

/-! ## The round -/

/-- §14.1, **line 5**: the `j`-th child of an Align node — the instance whose window is the
`j`-th color class and whose candidate set is the coset the Chain Rule has reached.  It is
`none` past the last window, when the fold has already failed, and when the state is so
malformed that the window is not invariant under the group it names. -/
def alignChild (p : RawAlignSI × ℕ × RawCoset) : Option RawAlignSI :=
  p.2.2.bind fun g =>
    if p.2.1 < (alignWins p.1).length then
      if rawIsInvariant (tidyGens (p.1.2.2.2.2.1, g.1), (alignWins p.1).getD p.2.1 []) then
        some (none, ((alignWins p.1).getD p.2.1 [], tidyGens (p.1.2.2.2.2.1, g.1),
          normPerm (p.1.2.2.2.2.1, g.2), p.1.2.2.2.2.1, p.1.2.2.2.2.2))
      else none
    else none

theorem alignChild_eq_some {p : RawAlignSI × ℕ × RawCoset} {J : RawAlignSI}
    (h : alignChild p = some J) :
    ∃ g τ, p.2.2 = some (g, τ) ∧ p.2.1 < (alignWins p.1).length ∧
      rawIsInvariant (tidyGens (p.1.2.2.2.2.1, g), (alignWins p.1).getD p.2.1 []) = true ∧
      J = (none, ((alignWins p.1).getD p.2.1 [], tidyGens (p.1.2.2.2.2.1, g),
        normPerm (p.1.2.2.2.2.1, τ), p.1.2.2.2.2.1, p.1.2.2.2.2.2)) := by
  rw [alignChild] at h
  rcases hs : p.2.2 with _ | ⟨g, τ⟩
  · rw [hs, Option.bind_none] at h; exact absurd h (by simp)
  · rw [hs, Option.bind_some] at h
    by_cases h1 : p.2.1 < (alignWins p.1).length
    · rw [if_pos h1] at h
      by_cases h2 : rawIsInvariant (tidyGens (p.1.2.2.2.2.1, g),
          (alignWins p.1).getD p.2.1 []) = true
      · rw [if_pos h2] at h
        exact ⟨g, τ, rfl, h1, h2, by injection h with h; exact h.symm⟩
      · rw [if_neg h2] at h; exact absurd h (by simp)
    · rw [if_neg h1] at h; exact absurd h (by simp)

theorem alignChild_eq_some_of {p : RawAlignSI × ℕ × RawCoset} {g : RawGens} {τ : RawPerm}
    (hs : p.2.2 = some (g, τ)) (h1 : p.2.1 < (alignWins p.1).length)
    (h2 : rawIsInvariant (tidyGens (p.1.2.2.2.2.1, g),
      (alignWins p.1).getD p.2.1 []) = true) :
    alignChild p = some (none, ((alignWins p.1).getD p.2.1 [], tidyGens (p.1.2.2.2.2.1, g),
      normPerm (p.1.2.2.2.2.1, τ), p.1.2.2.2.2.1, p.1.2.2.2.2.2)) := by
  rw [alignChild, hs, Option.bind_some, if_pos h1, if_pos h2]

/-- §14.1, **lines 4-6 as one round**.  `solve` is the rest of Procedure
String-Isomorphism: it answers the instances line 5 calls.

`ground` is the size of the pair of strings, as in `Algo.chainRound`: the strings are
copied unchanged into every child, so it is constant along the recursion.  The measure is
the size of the window plus one for the header, so an Align node is strictly above every
instance it calls. -/
def alignRound (n : ℕ) (solve : RawWinSI → RawCoset) : Round RawAlignSI RawCoset RawCoset where
  WF := AlignWF n
  ground := fun I => Enc.size I.2.2.2.2
  measure := fun I => I.2.1.length + (if alignIsNode I then 1 else 0)
  width := fun I => (alignWins I).length
  child := alignChild
  init := fun I => some (I.2.2.1, I.2.2.2.1)
  combine := fun p => p.2.2.2
  finish := fun p => if alignIsNode p.1 then p.2 else solve p.1.2
  bot := none
  child_eq_none := by
    intro I j s hj
    rw [alignChild]
    cases s with
    | none => rw [Option.bind_none]
    | some gt => rw [Option.bind_some, if_neg (by simpa using hj)]
  child_wf := by
    rintro I j s J hI hc
    obtain ⟨g, τ, -, h1, h2, rfl⟩ := alignChild_eq_some (p := (I, j, s)) hc
    obtain ⟨hx, hy, hnd, hlt, hgs, hgl, hσ, -⟩ := hI.1
    obtain ⟨hwnd, hwmem⟩ := alignWins_props (I := I) h1
    refine ⟨⟨hx, hy, hwnd, fun u hu => hlt u (hwmem u hu), wf_tidyGens hx g,
      length_tidyGens hx g, wf_normPerm hx τ, h2⟩, ?_⟩
    intro q hq
    exact absurd hq (by simp)
  child_measure := by
    rintro I j s J hI hc
    obtain ⟨g, τ, -, h1, -, rfl⟩ := alignChild_eq_some (p := (I, j, s)) hc
    obtain ⟨-, -, hnd, -, -, -, -, -⟩ := hI.1
    obtain ⟨hwnd, hwmem⟩ := alignWins_props (I := I) h1
    have hle : ((alignWins I).getD j []).length ≤ I.2.1.length :=
      (List.Nodup.subperm hwnd (fun u hu => hwmem u hu)).length_le
    show ((alignWins I).getD j []).length + (if alignIsNode
      ((none, ((alignWins I).getD j [], tidyGens (I.2.2.2.2.1, g),
        normPerm (I.2.2.2.2.1, τ), I.2.2.2.2.1, I.2.2.2.2.2)) : RawAlignSI) then 1 else 0)
      < I.2.1.length + (if alignIsNode I then 1 else 0)
    have hnode : alignIsNode ((none, ((alignWins I).getD j [], tidyGens (I.2.2.2.2.1, g),
        normPerm (I.2.2.2.2.1, τ), I.2.2.2.2.1, I.2.2.2.2.2)) : RawAlignSI) = false := rfl
    have hI1 : alignIsNode I = true := by
      rw [alignIsNode_eq_true_iff]
      rcases hq : I.1 with _ | q
      · rw [alignWins_of_none hq] at h1; exact absurd h1 (by simp)
      · exact ⟨q, rfl⟩
    have he0 : (if (false : Bool) = true then 1 else 0) = 0 := by simp
    have he1 : (if (true : Bool) = true then 1 else 0) = 1 := by simp
    rw [hnode, hI1, he0, he1]
    omega
  child_ground := by
    rintro I j s J hI hc
    obtain ⟨g, τ, -, -, -, rfl⟩ := alignChild_eq_some (p := (I, j, s)) hc
    exact le_refl _

/-! ## The mathematical round: the chain in coset form -/

/-- **The coset form of `Babai.alignChainReduction`**: the Chain Rule, Eq. (63), over the
windows of lines 5-6, started from the candidate set of the instance.  A node with no
header is a leaf and hands its instance to `solve`. -/
noncomputable def alignRoundReduction (n : ℕ) (solve : RawWinSI → RawCoset)
    (I : RawAlignSI) : Babai.SIReduction (Fin n) ℕ (Set (Perm (Fin n))) :=
  if alignIsNode I then
    cosetChain (decStrN n I.2.2.2.2.1) (decStrN n I.2.2.2.2.2)
      ((alignWins I).map (winSet n)) (decAlignSI n I).K
  else .done (decCoset n (solve I.2))

/-- **The windows of lines 5-6 cut the window of the instance exactly.**  Line 4's classes
cover `Ω`, so their traces on the window cover the window, and each of them is inside
it. -/
theorem iUnion_alignWins {I : RawAlignSI} {q : RawAction × RawLab} (hq : I.1 = some q)
    (hqn : q.1.1.1.length = n) (hlt : ∀ u ∈ I.2.1, u < n) :
    (⋃ S ∈ ((alignWins I).map (winSet n)), S) = winSet n I.2.1 := by
  ext u
  simp only [Set.mem_iUnion, List.mem_map, exists_prop]
  constructor
  · rintro ⟨S, ⟨W, hW, rfl⟩, hu⟩
    rw [alignWins_of_some hq, List.mem_map] at hW
    obtain ⟨W₀, -, rfl⟩ := hW
    exact (mem_alignCut.1 hu).2
  · intro hu
    have hun : (u : ℕ) < q.1.1.1.length := by rw [hqn]; exact hlt (u : ℕ) hu
    obtain ⟨W₀, hW₀, huW₀⟩ := alignRWindows_cover (q := q) hun
    refine ⟨winSet n (alignCut (W₀, I.2.1)), ⟨alignCut (W₀, I.2.1), ?_, rfl⟩, ?_⟩
    · rw [alignWins_of_some hq, List.mem_map]
      exact ⟨W₀, hW₀, rfl⟩
    · exact mem_alignCut.2 ⟨huW₀, hu⟩

/-- **The mathematical round is correct**: its value is the answer of the instance,
provided `solve` answers the instances that lines 5-6 call. -/
theorem run_alignRoundReduction (n : ℕ) (solve : RawWinSI → RawCoset) {I : RawAlignSI}
    (hI : AlignWF n I)
    (hsolve : I.1 = none → decCoset n (solve I.2) = (decAlignSI n I).answer) :
    (alignRoundReduction n solve I).run = (decAlignSI n I).answer := by
  rw [alignRoundReduction]
  by_cases hnode : alignIsNode I = true
  · rw [if_pos hnode]
    obtain ⟨q, hq⟩ := alignIsNode_eq_true_iff.1 hnode
    obtain ⟨-, -, -, hlt, -, -, -, -⟩ := hI.1
    have hhdr := hI.2 q hq
    rw [run_cosetChain, iUnion_alignWins hq hhdr.1 hlt]
    rfl
  · rw [if_neg hnode, Babai.SIReduction.run_done]
    exact hsolve (alignIsNode_eq_false_iff.1 (by simpa using hnode))

/-- **The coset form and the printed form of lines 5-6 have the same value.**  The paper's
`Babai.alignChainReduction` (Eq. (63) in the aligned group form) and the coset form the
machine runs both compute `Iso_N(x, y)`, provided the windows are `N`-invariant and the
instance's window is all of `Ω` — which is the situation of line 3, after *"Update: …
`G ← G₁`"*. -/
theorem run_alignRoundReduction_eq (n : ℕ) (solve : RawWinSI → RawCoset) {I : RawAlignSI}
    {q : RawAction × RawLab} {N : Subgroup (Perm (Fin n))} (hI : AlignWF n I)
    (hq : I.1 = some q) (hK : (decAlignSI n I).K = (N : Set (Perm (Fin n))))
    (huniv : winSet n I.2.1 = Set.univ)
    (hinv : ∀ Δ ∈ ((alignWins I).map (winSet n)), Babai.IsInvariant N Δ) :
    (alignRoundReduction n solve I).run
      = (Babai.alignChainReduction N ((alignWins I).map (winSet n))
          (decStrN n I.2.2.2.2.1) (decStrN n I.2.2.2.2.2)).run := by
  obtain ⟨-, -, -, hlt, -, -, -, -⟩ := hI.1
  have hhdr := hI.2 q hq
  have hcov : (⋃ Δ ∈ ((alignWins I).map (winSet n)), Δ) = (Set.univ : Set (Fin n)) := by
    rw [iUnion_alignWins hq hhdr.1 hlt, huniv]
  rw [Babai.run_alignChainReduction _ _ hinv hcov,
    run_alignRoundReduction n solve hI (fun h => absurd (h ▸ hq) (by simp))]
  show Babai.wIso (winSet n I.2.1) (decAlignSI n I).K _ _ = _
  rw [huniv, hK, Babai.wIso_univ]
  rfl

/-! ## The link: the fold of the round walks the chain -/

/-- The invariant carried along the fold: the raw state decodes to the coset the chain has
reached, that coset lies inside the candidate set of the instance, and the group the state
names lies inside the group of the instance. -/
def AlignStateOK (n : ℕ) (I : RawAlignSI) (C : Set (Perm (Fin n))) (s : RawCoset) : Prop :=
  decCoset n s = C ∧ C ⊆ (decAlignSI n I).K ∧
    ∀ g τ, s = some (g, τ) → decGroup n g ≤ decGroup n I.2.2.1

/-- A raw coset that decodes to the empty set is the failed state. -/
theorem eq_none_of_decCoset_eq_empty {s : RawCoset} (h : decCoset n s = ∅) : s = none := by
  cases s with
  | none => rfl
  | some gt =>
      exfalso
      have : decPerm n gt.2 ∈ decCoset n (some (gt.1, gt.2)) := ⟨1, one_mem _, by rw [mul_one]⟩
      rw [show (some (gt.1, gt.2) : RawCoset) = some gt from rfl, h] at this
      exact this

section Phase

variable (n : ℕ) (solve : RawWinSI → RawCoset)

/-- **Lines 5-6 are one phase of the round**, of cost the number of windows.  The proof is
the phase rule `Algo.phaseMatch_cosetChain`: what is left to check is one step of the loop,
namely that the round's next child is the instance Eq. (63) asks for. -/
theorem phaseMatch_alignRound {I : RawAlignSI} (hI : AlignWF n I)
    {q : RawAction × RawLab} (hq : I.1 = some q) :
    PhaseMatch (alignRound n solve) (decAlignSI n) (decCoset n) I
      (alignWins I).length 0 ((alignRound n solve).init I)
      (cosetChain (decStrN n I.2.2.2.2.1) (decStrN n I.2.2.2.2.2)
        ((alignWins I).map (winSet n)) (decAlignSI n I).K)
      (fun C' j' s' => AlignStateOK n I C' s' ∧
        (C' = ∅ ∨ (alignWins I).length ≤ j')) := by
  obtain ⟨hx, hy, hnd, hlt, hgs, hgl, hσ, hinvI⟩ := hI.1
  have hhdr := hI.2 q hq
  set Inv : List (Set (Fin n)) → Set (Perm (Fin n)) → ℕ → RawCoset → Prop :=
    fun Δs C j s => AlignStateOK n I C s ∧
      (C = ∅ ∨ Δs = ((alignWins I).drop j).map (winSet n)) with hInv
  have hmain := phaseMatch_cosetChain (R := alignRound n solve) (decI := decAlignSI n)
    (decA := decCoset n) (I := I) (decStrN n I.2.2.2.2.1) (decStrN n I.2.2.2.2.2) Inv ?_ ?_
  · have h0 := hmain ((alignWins I).map (winSet n)) (decAlignSI n I).K 0
      ((alignRound n solve).init I) ?_
    · rw [List.length_map] at h0
      refine phaseMatch_weaken h0 (fun b j' s' hb => ⟨hb.1, hb.2.imp id ?_⟩)
      intro hnil
      have hlen0 : ((alignWins I).drop j').length = 0 := by
        have hc := congrArg List.length hnil
        simpa using hc.symm
      rw [List.length_drop] at hlen0
      omega
    · refine ⟨⟨rfl, le_refl _, ?_⟩, Or.inr (by rw [List.drop_zero])⟩
      intro g τ hgt
      have : g = I.2.2.1 := congrArg (fun z => (Option.getD z (I.2.2.1, I.2.2.2.1)).1) hgt.symm
      rw [this]
  -- the step of the loop
  · rintro Δ Δs C j s ⟨hstate, hcase⟩ hCne
    have hdrop : Δ :: Δs = ((alignWins I).drop j).map (winSet n) := by
      rcases hcase with h | h
      · exact absurd h hCne
      · exact h
    have hjl : j < (alignWins I).length := by
      by_contra hcon
      rw [List.drop_eq_nil_of_le (by omega), List.map_nil] at hdrop
      exact absurd hdrop (by simp)
    have hdrop' : (alignWins I).drop j
        = ((alignWins I)[j]'hjl) :: (alignWins I).drop (j + 1) :=
      List.drop_eq_getElem_cons hjl
    rw [hdrop', List.map_cons] at hdrop
    have hΔ : Δ = winSet n ((alignWins I)[j]'hjl) := (List.cons.injEq _ _ _ _ ▸ hdrop).1
    have hΔs : Δs = ((alignWins I).drop (j + 1)).map (winSet n) :=
      (List.cons.injEq _ _ _ _ ▸ hdrop).2
    -- the state is alive
    have hsne : s ≠ none := by
      intro h
      apply hCne
      rw [← hstate.1, h]; rfl
    obtain ⟨g, τ, rfl⟩ : ∃ g τ, s = some (g, τ) := by
      cases s with
      | none => exact absurd rfl hsne
      | some gt => exact ⟨gt.1, gt.2, rfl⟩
    have hgetd : (alignWins I).getD j [] = (alignWins I)[j]'hjl :=
      List.getD_eq_getElem _ _ hjl
    obtain ⟨hwnd, hwmem⟩ := alignWins_props (I := I) hjl
    have hgle : decGroup n g ≤ decGroup n I.2.2.1 := hstate.2.2 g τ rfl
    have htidy : decGroup n (tidyGens (I.2.2.2.2.1, g)) = decGroup n g :=
      decGroup_tidyGens hx g
    -- the window is invariant
    have hinvw : rawIsInvariant (tidyGens (I.2.2.2.2.1, g), (alignWins I).getD j []) = true := by
      obtain ⟨q', W, hq', hW, hgetq⟩ := getD_alignWins (I := I) hjl
      have hqq : q = q' := by
        have hqe : (some q : Option (RawAction × RawLab)) = some q' := by rw [← hq]; exact hq'
        exact Option.some_injective _ hqe
      have hW' : W ∈ alignRWindows q := by rw [hqq]; exact hW
      have hbase : rawIsInvariant (I.2.2.1, (alignWins I).getD j []) = true := by
        rw [hgetq]
        exact hhdr.2.2.2.2.2.2.2.2.2.2 W hW'
      have hlt' : ∀ u ∈ (alignWins I).getD j [], u < n := fun u hu => hlt u (hwmem u hu)
      rw [rawIsInvariant_eq_true_iff (wf_tidyGens hx g) hlt', htidy]
      exact isInvariant_of_le
        ((rawIsInvariant_eq_true_iff hgs hlt').1 hbase) hgle
    set J : RawAlignSI := (none, ((alignWins I).getD j [], tidyGens (I.2.2.2.2.1, g),
      normPerm (I.2.2.2.2.1, τ), I.2.2.2.2.1, I.2.2.2.2.2)) with hJ
    have hchild : (alignRound n solve).child (I, j, (some (g, τ) : RawCoset)) = some J :=
      alignChild_eq_some_of (p := (I, j, (some (g, τ) : RawCoset))) rfl hjl hinvw
    have hdec : decAlignSI n J
        = ⟨C, Δ, decStrN n I.2.2.2.2.1, decStrN n I.2.2.2.2.2⟩ := by
      have hK : decCoset n (some (tidyGens (I.2.2.2.2.1, g), normPerm (I.2.2.2.2.1, τ))) = C := by
        rw [← hstate.1]
        show {ρ | ∃ u ∈ decGroup n (tidyGens (I.2.2.2.2.1, g)),
          ρ = decPerm n (normPerm (I.2.2.2.2.1, τ)) * u} = _
        rw [htidy, decPerm_normPerm hx τ]
        rfl
      rw [decAlignSI, hJ, decWinSI]
      simp only
      rw [hK, hgetd, hΔ]
    refine ⟨J, hchild, hdec, ?_⟩
    intro a ha
    have hans : (decAlignSI n J).answer
        = Babai.wIso Δ C (decStrN n I.2.2.2.2.1) (decStrN n I.2.2.2.2.2) := by
      rw [Babai.SIInstance.answer, hdec]
    have hsub : (decAlignSI n J).answer ⊆ C := by
      rw [hans]; exact fun ρ hρ => hρ.1
    refine ⟨⟨ha, le_trans hsub hstate.2.1, ?_⟩, Or.inr ?_⟩
    · intro g₂ τ₂ ha2
      refine decGroup_le_of_subset (σ₀ := decPerm n I.2.2.2.1) (τ := decPerm n τ₂) ?_
      have h1 : decCoset n (some (g₂, τ₂)) ⊆ (decAlignSI n I).K := by
        rw [← ha2]
        show decCoset n a ⊆ (decAlignSI n I).K
        rw [ha]
        exact le_trans hsub hstate.2.1
      exact h1
    · exact hΔs
  -- the chain gives up
  · rintro Δs C j s ⟨hstate, -⟩ hCe
    exact ⟨by rw [← hCe]; exact hstate, Or.inl rfl⟩

/-! ## The link -/

/-- **The link (Procedure Align, lines 4-6)**: the fold of the round walks the chain of
Eq. (63) over the windows of lines 5 and 6.

The proof is the phase rule: `Algo.phaseMatch_alignRound` is the phase, and
`Algo.loopMatch_of_phaseMatch` reads it off as the round's `Implements` statement.  A node
with no header makes no call and hands its instance to `solve`. -/
theorem implements_alignRound (n : ℕ) (solve : RawWinSI → RawCoset) :
    Implements (alignRound n solve) id (decAlignSI n) (decCoset n)
      (alignRoundReduction n solve) := by
  intro I hI
  show LoopMatch (alignRound n solve) (decAlignSI n) (decCoset n) I
    (alignWins I).length 0 (some (I.2.2.1, I.2.2.2.1)) (alignRoundReduction n solve I)
  rw [alignRoundReduction]
  by_cases hnode : alignIsNode I = true
  · rw [if_pos hnode]
    obtain ⟨q, hq⟩ := alignIsNode_eq_true_iff.1 hnode
    refine loopMatch_of_phaseMatch (phaseMatch_alignRound n solve hI hq) ?_ (le_refl _)
    rintro b j' s' ⟨hstate, hcase⟩
    constructor
    · rcases hcase with hb | hj
      · have hs : s' = none := eq_none_of_decCoset_eq_empty (by rw [hstate.1, hb])
        rw [hs]
        show alignChild (I, j', (none : RawCoset)) = none
        rw [alignChild, Option.bind_none]
      · show alignChild (I, j', s') = none
        rw [alignChild]
        cases s' with
        | none => rw [Option.bind_none]
        | some gt => rw [Option.bind_some, if_neg (by simpa using hj)]
    · show decCoset n (if alignIsNode I then s' else solve I.2) = b
      rw [if_pos hnode]
      exact hstate.1
  · rw [if_neg hnode]
    have hnone : I.1 = none := alignIsNode_eq_false_iff.1 (by simpa using hnode)
    refine LoopMatch.done _ 0 _ _ ?_ ?_
    · show alignChild (I, 0, (some (I.2.2.1, I.2.2.2.1) : RawCoset)) = none
      rw [alignChild, Option.bind_some, if_neg (by rw [alignWins_of_none hnone]; simp)]
    · show decCoset n (if alignIsNode I then _ else solve I.2) = decCoset n (solve I.2)
      rw [if_neg hnode]

end Phase

/-! ## What one window of the round is

The two windows of lines 5 and 6, read as sets: a color class of `Ω`, or the window
`Ω(Δ_j)` of line 6, in both cases cut down to the window of the instance.  This is what a
bound on the size of a window — Lemma 7.2.1 through
`Babai.three_mul_ncard_omegaColorClass_le`, Cor. 12.0.8 for the dominant window — applies
to. -/

theorem winSet_alignCut (n : ℕ) (W Δ : List ℕ) :
    winSet n (alignCut (W, Δ)) = winSet n W ∩ winSet n Δ := by
  ext u
  rw [Set.mem_inter_iff, mem_winSet, mem_winSet, mem_winSet, mem_alignCut]

section WinSpec

variable {n m : ℕ} {gens : List (Perm (Fin n))} {imgs : List (Perm (Fin m))}
  {ϕ : genGroup gens →* Perm (Fin m)} {dom gdom lab : List ℕ} {I : RawAlignSI}

/-- **Every window of lines 5-6 is a color class of `Ω`, or line 6's window `Ω(Δ_j)`, cut to
the window of the instance.** -/
theorem winSet_getD_alignWins (hd : dom.length = n) (hg : gdom.length = m)
    (hI : ImgsOf gens imgs ϕ) (hϕ : Babai.IsGiantRep ϕ)
    (hk : Babai.VeryLargeK m (Babai.maxOrbitLength (genGroup gens)))
    (hq : I.1 = some ((((dom, gens.map (encPerm n)),
      (gdom, imgs.map (encPerm m))) : RawAction), lab))
    {j : ℕ} (hj : j < (alignWins I).length) :
    (∃ u : Fin n, winSet n ((alignWins I).getD j [])
        = {v : Fin n | Babai.omegaColor ϕ (fun γ : Fin m => labAt lab (γ : ℕ)) v
            = Babai.omegaColor ϕ (fun γ : Fin m => labAt lab (γ : ℕ)) u} ∩ winSet n I.2.1)
      ∨ winSet n ((alignWins I).getD j [])
        = Babai.omegaOf ϕ {γ : Fin m | labAt lab (γ : ℕ)
            = alignRDomColor ((((dom, gens.map (encPerm n)),
              (gdom, imgs.map (encPerm m))) : RawAction), lab)} ∩ winSet n I.2.1 := by
  obtain ⟨q, W, hq', hW, hget⟩ := getD_alignWins hj
  have hqq : q = ((((dom, gens.map (encPerm n)),
      (gdom, imgs.map (encPerm m))) : RawAction), lab) := by
    have hqe : (some q : Option (RawAction × RawLab))
        = some ((((dom, gens.map (encPerm n)),
          (gdom, imgs.map (encPerm m))) : RawAction), lab) := by rw [← hq']; exact hq
    exact Option.some_injective _ hqe
  subst hqq
  rw [hget, winSet_alignCut]
  rcases alignRWindows_mem hW with hdom | hcl
  · exact Or.inr (by rw [hdom, winSet_alignRDomWindow hd hg hI hϕ hk])
  · obtain ⟨u, hu, rfl⟩ := mem_alignRClasses hcl
    have hun : u < n := by rw [← hd]; exact hu
    refine Or.inl ⟨⟨u, hun⟩, ?_⟩
    rw [winSet_alignROmegaClass hd hg hI hϕ hk ⟨u, hun⟩]

end WinSpec

/-! ## The time classes -/

theorem polyFun_alignIsNode : PolyFun alignIsNode :=
  ((polyFun_fst.pair polyFun_id).comp
    (PolyFun.optionElim (g := fun _ : RawAlignSI => false) (polyFun_const false)
      (polyFun_const true))).of_eq (fun _ => rfl)

set_option maxHeartbeats 1000000 in
theorem polyFun_alignCut : PolyFun alignCut := by
  have hmem : PolyFun (fun w : (List ℕ × List ℕ) × ℕ => decide (w.2 ∈ w.1.2)) :=
    (polyFun_snd.pair (polyFun_fst.comp polyFun_snd)).comp polyFun_natListMem
  exact ((polyFun_id.pair polyFun_fst).comp (PolyFun.filterParam hmem)).of_eq (fun _ => rfl)

set_option maxHeartbeats 1000000 in
theorem polyFun_alignWinsOf : PolyFun alignWinsOf := by
  have hcut : PolyFun (fun w : ((RawAction × RawLab) × List ℕ) × List ℕ =>
      alignCut (w.2, w.1.2)) :=
    (polyFun_snd.pair (polyFun_fst.comp polyFun_snd)).comp polyFun_alignCut
  exact ((polyFun_id.pair (polyFun_fst.comp polyFun_alignRWindows)).comp
    (PolyFun.mapParam hcut)).of_eq (fun _ => rfl)

set_option maxHeartbeats 1000000 in
theorem polyFun_alignWins : PolyFun alignWins := by
  have hbody : PolyFun (fun z : (RawAction × RawLab) × RawAlignSI =>
      alignWinsOf (z.1, z.2.2.1)) :=
    (polyFun_fst.pair ((polyFun_snd.comp polyFun_snd).comp polyFun_fst)).comp
      polyFun_alignWinsOf
  exact ((polyFun_fst.pair polyFun_id).comp
    (PolyFun.optionElim (g := fun _ : RawAlignSI => ([] : List (List ℕ)))
      (polyFun_const []) hbody)).of_eq (fun _ => rfl)

set_option maxHeartbeats 2000000 in
theorem polyFun_alignChild : PolyFun alignChild := by
  -- the projections of the pair `((g, τ), (I, j, s))`
  have hI : PolyFun (fun z : (RawGens × RawPerm) × (RawAlignSI × ℕ × RawCoset) => z.2.1) :=
    polyFun_snd.comp polyFun_fst
  have hj : PolyFun (fun z : (RawGens × RawPerm) × (RawAlignSI × ℕ × RawCoset) => z.2.2.1) :=
    (polyFun_snd.comp polyFun_snd).comp polyFun_fst
  have hg : PolyFun (fun z : (RawGens × RawPerm) × (RawAlignSI × ℕ × RawCoset) => z.1.1) :=
    polyFun_fst.comp polyFun_fst
  have hτ : PolyFun (fun z : (RawGens × RawPerm) × (RawAlignSI × ℕ × RawCoset) => z.1.2) :=
    polyFun_fst.comp polyFun_snd
  have hx : PolyFun (fun z : (RawGens × RawPerm) × (RawAlignSI × ℕ × RawCoset) =>
      z.2.1.2.2.2.2.1) :=
    (((((hI.comp polyFun_snd).comp polyFun_snd).comp polyFun_snd).comp polyFun_snd).comp
      polyFun_fst)
  have hy : PolyFun (fun z : (RawGens × RawPerm) × (RawAlignSI × ℕ × RawCoset) =>
      z.2.1.2.2.2.2.2) :=
    (((((hI.comp polyFun_snd).comp polyFun_snd).comp polyFun_snd).comp polyFun_snd).comp
      polyFun_snd)
  have hwins : PolyFun (fun z : (RawGens × RawPerm) × (RawAlignSI × ℕ × RawCoset) =>
      alignWins z.2.1) := hI.comp polyFun_alignWins
  have hwin : PolyFun (fun z : (RawGens × RawPerm) × (RawAlignSI × ℕ × RawCoset) =>
      (alignWins z.2.1).getD z.2.2.1 []) :=
    ((hwins.pair hj).pair (polyFun_const [])).comp polyFun_getD
  have htidy : PolyFun (fun z : (RawGens × RawPerm) × (RawAlignSI × ℕ × RawCoset) =>
      tidyGens (z.2.1.2.2.2.2.1, z.1.1)) := (hx.pair hg).comp polyFun_tidyGens
  have htest1 : PolyFun (fun z : (RawGens × RawPerm) × (RawAlignSI × ℕ × RawCoset) =>
      decide (z.2.2.1 < (alignWins z.2.1).length)) :=
    (hj.add (polyFun_const 1)).le (hwins.comp polyFun_length)
  have htest2 : PolyFun (fun z : (RawGens × RawPerm) × (RawAlignSI × ℕ × RawCoset) =>
      rawIsInvariant (tidyGens (z.2.1.2.2.2.2.1, z.1.1),
        (alignWins z.2.1).getD z.2.2.1 [])) :=
    (htidy.pair hwin).comp polyFun_rawIsInvariant
  have hnorm : PolyFun (fun z : (RawGens × RawPerm) × (RawAlignSI × ℕ × RawCoset) =>
      normPerm (z.2.1.2.2.2.2.1, z.1.2)) := (hx.pair hτ).comp polyFun_normPerm
  have hsome : PolyFun (fun z : (RawGens × RawPerm) × (RawAlignSI × ℕ × RawCoset) =>
      (some (none, ((alignWins z.2.1).getD z.2.2.1 [], tidyGens (z.2.1.2.2.2.2.1, z.1.1),
        normPerm (z.2.1.2.2.2.2.1, z.1.2), z.2.1.2.2.2.2.1, z.2.1.2.2.2.2.2)) :
          Option RawAlignSI)) :=
    ((polyFun_const (none : Option (RawAction × RawLab))).pair
      (hwin.pair (htidy.pair (hnorm.pair (hx.pair hy))))).comp polyFun_some
  have hbody : PolyFun (fun z : (RawGens × RawPerm) × (RawAlignSI × ℕ × RawCoset) =>
      if z.2.2.1 < (alignWins z.2.1).length then
        (if rawIsInvariant (tidyGens (z.2.1.2.2.2.2.1, z.1.1),
            (alignWins z.2.1).getD z.2.2.1 []) then
          (some (none, ((alignWins z.2.1).getD z.2.2.1 [], tidyGens (z.2.1.2.2.2.2.1, z.1.1),
            normPerm (z.2.1.2.2.2.2.1, z.1.2), z.2.1.2.2.2.2.1, z.2.1.2.2.2.2.2)) :
              Option RawAlignSI)
        else none)
      else none) := by
    refine (PolyFun.ite htest1 (PolyFun.ite htest2 hsome (polyFun_const none))
      (polyFun_const none)).of_eq (fun z => ?_)
    by_cases h1 : z.2.2.1 < (alignWins z.2.1).length
    · by_cases h2 : rawIsInvariant (tidyGens (z.2.1.2.2.2.2.1, z.1.1),
        (alignWins z.2.1).getD z.2.2.1 []) = true <;> simp [h1, h2]
    · simp [h1]
  refine (((polyFun_snd.comp polyFun_snd).pair polyFun_id).comp
    (PolyFun.optionElim (g := fun _ : RawAlignSI × ℕ × RawCoset => (none : Option RawAlignSI))
      (polyFun_const none) hbody)).of_eq (fun p => ?_)
  rw [alignChild]
  cases hs : p.2.2 with
  | none => simp [hs]
  | some gt => simp [hs]

/-! ## The size bound -/

/-- **The size bound of the round of lines 4-6**: `Algo.chainBound` for the window
instance, with room for the header — two domain witnesses, two generator lists and the
coloring. -/
def alignBound (v : ℕ) : ℕ := 64 * (chainBound v + gensBound v + strBound v + 1)

theorem polyBound_alignBound : PolyBound alignBound := by
  have hS : PolyBound strBound :=
    (polyBound_const 1).add (polyBound_id.mul
      (((polyBound_const 2).mul (polyBound_id.add (polyBound_const 2))).add
        (polyBound_const 1)))
  have hG : PolyBound gensBound :=
    (polyBound_const 1).add ((polyBound_id.mul polyBound_id).mul
      (((polyBound_const 2).mul hS).add (polyBound_const 1)))
  exact (polyBound_const 64).mul (((polyBound_chainBound.add hG).add hS).add
    (polyBound_const 1))

theorem mono_alignBound : Monotone alignBound := by
  intro a b hab
  have h1 := mono_chainBound hab
  have h2 := mono_gensBound hab
  have h3 := mono_strBound hab
  simp only [alignBound]
  omega

theorem chainBound_le_alignBound (v : ℕ) : chainBound v ≤ alignBound v := by
  simp only [alignBound]; omega

section Size

variable {I : RawAlignSI}

/-- The size of the header of a well-formed node. -/
theorem size_alignHdr_le (hI : AlignWF n I) :
    Enc.size I.1 ≤ 18 * strBound (Enc.size I.2.2.2.2)
      + 16 * gensBound (Enc.size I.2.2.2.2) + 2 := by
  set v : ℕ := Enc.size I.2.2.2.2 with hv
  have hnv : n ≤ v := le_size_strings hI.1
  rcases hq : I.1 with _ | q
  · have hnone : Enc.size (none : Option (RawAction × RawLab)) = 2 := size_none
    omega
  · obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, -⟩ := hI.2 q hq
    have hdom : Enc.size q.1.1.1 ≤ strBound v :=
      size_natList_le (by rw [h1]; exact hnv) (fun a ha => lt_of_lt_of_le (h2 a ha) hnv)
    have hgdom : Enc.size q.1.2.1 ≤ strBound v :=
      size_natList_le (le_trans h3 hnv) (fun a ha => lt_of_lt_of_le (h4 a ha) hnv)
    have hlab : Enc.size q.2 ≤ strBound v :=
      size_natList_le (by rw [h9]; exact le_trans h3 hnv)
        (fun a ha => lt_of_lt_of_le (h10 a ha) hnv)
    have hgens : Enc.size q.1.1.2 ≤ gensBound v := by
      have hentry : ∀ g ∈ q.1.1.2, Enc.size g ≤ strBound v := by
        intro g hg
        exact size_natList_le (by rw [(h5 g hg).length]; exact hnv)
          (fun a ha => lt_of_lt_of_le ((h5 g hg).lt ha) hnv)
      have ha := size_list_le_of_entries q.1.1.2 (strBound v) hentry
      have hb : q.1.1.2.length * (2 * strBound v + 1) ≤ v * v * (2 * strBound v + 1) :=
        Nat.mul_le_mul_right _ (le_trans h6 (Nat.mul_le_mul hnv hnv))
      have hc : gensBound v = 1 + v * v * (2 * strBound v + 1) := rfl
      omega
    have himgs : Enc.size q.1.2.2 ≤ gensBound v := by
      have hentry : ∀ g ∈ q.1.2.2, Enc.size g ≤ strBound v := by
        intro g hg
        exact size_natList_le
          (by rw [(h7 g hg).length]; exact le_trans h3 hnv)
          (fun a ha => lt_of_lt_of_le ((h7 g hg).lt ha) (le_trans h3 hnv))
      have ha := size_list_le_of_entries q.1.2.2 (strBound v) hentry
      have hb : q.1.2.2.length * (2 * strBound v + 1) ≤ v * v * (2 * strBound v + 1) :=
        Nat.mul_le_mul_right _ (le_trans h8 (Nat.mul_le_mul hnv hnv))
      have hc : gensBound v = 1 + v * v * (2 * strBound v + 1) := rfl
      omega
    have hp1 : Enc.size q.1.1 ≤ 2 * Enc.size q.1.1.1 + 2 * Enc.size q.1.1.2 :=
      Combine.size_pair_le q.1.1.1 q.1.1.2
    have hp2 : Enc.size q.1.2 ≤ 2 * Enc.size q.1.2.1 + 2 * Enc.size q.1.2.2 :=
      Combine.size_pair_le q.1.2.1 q.1.2.2
    have hp3 : Enc.size q.1 ≤ 2 * Enc.size q.1.1 + 2 * Enc.size q.1.2 :=
      Combine.size_pair_le q.1.1 q.1.2
    have hp4 : Enc.size q ≤ 2 * Enc.size q.1 + 2 * Enc.size q.2 :=
      Combine.size_pair_le q.1 q.2
    rw [size_some_eq]
    omega

/-- **A well-formed node is small.** -/
theorem size_alignSI_le (hI : AlignWF n I) :
    Enc.size I ≤ alignBound (Enc.size I.2.2.2.2) := by
  have hhdr := size_alignHdr_le hI
  have hwin : Enc.size I.2 ≤ chainBound (Enc.size I.2.2.2.2) := size_winSI_le hI.1
  have hp : Enc.size I ≤ 2 * Enc.size I.1 + 2 * Enc.size I.2 :=
    Combine.size_pair_le I.1 I.2
  have hb : alignBound (Enc.size I.2.2.2.2)
      = 64 * (chainBound (Enc.size I.2.2.2.2) + gensBound (Enc.size I.2.2.2.2)
        + strBound (Enc.size I.2.2.2.2) + 1) := rfl
  omega

end Size

/-! ## The cost data -/

/-- **The cost data of the round of lines 4-6.**  `solve` is charged for, as in
`Algo.chainCost`: it has to be a `RAM.QuasiPolyFun` and to answer within the same bound. -/
def alignCost (n : ℕ) (solve : RawWinSI → RawCoset) (hsolve : QuasiPolyFun solve)
    (hsize : ∀ I : RawAlignSI, AlignWF n I →
      Enc.size (solve I.2) ≤ alignBound (Enc.size I.2.2.2.2)) :
    Round.Cost (alignRound n solve) where
  bound := alignBound
  polyBound_bound := polyBound_alignBound
  mono_bound := mono_alignBound
  widthBound := fun v => v + 1
  quasiPolyBound_widthBound := (polyBound_id.add (polyBound_const 1)).quasiPoly
  quasiPolyFun_child := polyFun_alignChild.quasiPolyFun
  quasiPolyFun_init :=
    ((((polyFun_snd.comp polyFun_snd).comp polyFun_fst).pair
      (((polyFun_snd.comp polyFun_snd).comp polyFun_snd).comp polyFun_fst)).comp
        polyFun_some).quasiPolyFun
  quasiPolyFun_combine :=
    ((polyFun_snd.comp polyFun_snd).comp polyFun_snd).quasiPolyFun
  quasiPolyFun_finish := by
    have hnode : PolyFun (fun p : RawAlignSI × RawCoset => alignIsNode p.1) :=
      polyFun_fst.comp polyFun_alignIsNode
    exact (QuasiPolyFun.ite hnode polyFun_snd.quasiPolyFun
      ((polyFun_fst.comp polyFun_snd).comp_quasi hsolve)).of_eq (fun p => by
        by_cases h : alignIsNode p.1 = true <;> simp [alignRound, h])
  ground_le := fun I =>
    le_trans (size_snd_le' I.2.2.2) (le_trans (size_snd_le' I.2.2)
      (le_trans (size_snd_le' I.2) (size_snd_le' I)))
  size_le := fun _ hI => size_alignSI_le hI
  init_le := by
    intro I hI
    have h0 : Enc.size ((alignRound n solve).init I)
        = Enc.size ((I.2.2.1, I.2.2.2.1) : RawGens × RawPerm) + 2 := size_some_eq _
    have h1 : Enc.size ((I.2.2.1, I.2.2.2.1) : RawGens × RawPerm)
        ≤ 2 * Enc.size I.2.2.1 + 2 * Enc.size I.2.2.2.1 := Combine.size_pair_le _ _
    have h3 : Enc.size I.2.2.1 ≤ gensBound (Enc.size I.2.2.2.2) := size_gens_le hI.1
    have h4 : Enc.size I.2.2.2.1 ≤ strBound (Enc.size I.2.2.2.2) := size_rep_le hI.1
    have hb : alignBound (Enc.size I.2.2.2.2)
        = 64 * (chainBound (Enc.size I.2.2.2.2) + gensBound (Enc.size I.2.2.2.2)
          + strBound (Enc.size I.2.2.2.2) + 1) := rfl
    show Enc.size ((alignRound n solve).init I) ≤ alignBound (Enc.size I.2.2.2.2)
    omega
  combine_le := fun _ _ _ _ _ _ ha => ha
  finish_le := by
    intro I s hI hs
    show Enc.size (if alignIsNode I then s else solve I.2) ≤ alignBound (Enc.size I.2.2.2.2)
    by_cases h : alignIsNode I = true
    · rw [if_pos h]; exact hs
    · rw [if_neg h]; exact hsize I hI
  bot_le := by
    intro v
    have h1 : Enc.size (none : RawCoset) = 2 := size_none
    have h2 : alignBound v = 64 * (chainBound v + gensBound v + strBound v + 1) := rfl
    show Enc.size (none : RawCoset) ≤ alignBound v
    omega
  width_le := by
    intro I hI
    show (alignWins I).length ≤ Enc.size I.2.2.2.2 + 1
    rcases hq : I.1 with _ | q
    · rw [alignWins_of_none hq]; simp
    · have h1 := length_alignWins_le (I := I) hq
      have h2 : q.1.1.1.length = n := (hI.2 q hq).1
      have h3 : n ≤ Enc.size I.2.2.2.2 := le_size_strings hI.1
      omega


end Algo
