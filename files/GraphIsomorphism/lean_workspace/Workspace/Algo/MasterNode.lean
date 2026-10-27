/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: the master node, and the first three kinds of the master round.
-/
import Workspace.Algo.A15KindsCostS
import Workspace.Algo.A15Test
import Workspace.Algo.Descent
import Workspace.Algo.WFTestsSI

/-!
# The master node, and the three kinds that exist

`Workspace/Algo/A15Kinds.lean` builds the master round of Sec. 15 out of a **list of kinds**
over a fixed node type `N`, a fixed state type `S` and three global data `WF`, `ground`,
`measure`.  `Workspace/Algo/A15Test.lean` checked that interface on a toy family.  This file
fixes `N`, `S`, `WF`, `ground` and `measure` once and for all, and puts in the three kinds
that the `Algo` track has actually built:

* the **dispatch** kind — line 1 of Sec. 15: test the instance, and branch;
* the **Chain Rule** kind — Prop. 11.1.7 with Eq. (64), `Algo.chainRound`;
* the **descent** kind — Prop. 11.1.6 with Eq. (62), `Algo.descentRound`.

## The node

`Algo.A15.MNode = Option RawSI × Option RawWinSI × Option RawWinSI × Option RawDescSI`, one
slot per kind, plus a first slot held open for the **entry** kind, which is the one node of a
run that is a plain `Algo.RawSI`.  A later kind is a further `Option` component appended at
the end; the docstrings below say what that costs.

The dispatch kind runs on `Algo.RawWinSI` and not on `Algo.RawSI`.  It has to: a leaf of the
Chain Rule and a leaf of the descent hand the dispatch the instance they were about to give
to `solve`, and that instance carries a **window** and a **representative**, which a `RawSI`
has no room for.  Restricting the instance to its window instead would change the domain,
and every node of one run of the master recursion has to live on one domain, because
`Babai.MasterStep Ω A κ` fixes `Ω`.  The entry kind is where a `RawSI` enters: its one child
is the window instance with the full domain for a window and the identity for a
representative.

## The state

`Algo.A15.MState = Algo.RawCoset`: all three kinds fold a coset, as `Algo.chainRound` and
`Algo.descentRound` do.  A later kind that needs more has to change `S` to a product, and
then the three `u`/`projω` pairs and the three `u_projω_le` clauses below change with it —
nothing else does.

## The three global data

* `Algo.A15.mnGround x` is the **domain size** `n`, read off the node as the length of its
  first string.  It has to be a `RAM.PolyFun` (`Algo.Round.RunCostQ.polyFun_ground`), so it
  cannot be the encoding size of the strings, which is what the local rounds
  `Algo.chainRound` and `Algo.descentRound` use for their own `ground`.  Every bound of this
  file is therefore a polynomial of `n`, and that is what forces the letter bound into the
  master well-formedness (`Algo.A15.MWinWF`): with an unbounded alphabet the encoding of a
  string of length `n` is not bounded by any polynomial of `n`.  This is the hand-over of the
  note "A6 repair: input normalization".
* `Algo.A15.MWF` — one disjunct per kind, "exactly this slot is filled and its payload is
  well formed".  The semantic part of every disjunct is the invariant
  **every orbit of the node's group inside its window has at most one point**
  (`Algo.A15.TChainWF`, from `Workspace/Algo/A15Test.lean`).  It is preserved by every child
  of every kind, and it is what makes the dispatch kind *honest*: under it a transitive
  instance has a window of at most one point, which the dispatch answers outright, so the
  dispatch never meets the branches of Sec. 15 that are not built yet.
* `Algo.A15.mnMeasure` — the recipe of item 7, `rank * 5 + local`, with `rank` the length of
  the window and `local` a number in `[0,5)` that orders the three kinds around the cycle
  dispatch → Chain Rule → dispatch.  It is not computable and does not have to be:
  `Algo.Round.measure` is used only in proofs and in `Algo.Round.RunCostQS.measure_le`.

## Main definitions

* `Algo.A15.MNode`, `Algo.A15.MWF`, `Algo.A15.mnGround`, `Algo.A15.mnMeasure`;
* `Algo.A15.mnDispKind`, `Algo.A15.mnChainKind`, `Algo.A15.mnDescKind`, `Algo.A15.mnKinds`;
* `Algo.A15.mnRound` — the master round of the three kinds;
* `Algo.A15.mnRed` — the coset-form reduction it implements.

## Main results

* `Algo.A15.implements_mnRound` — the master round implements `Algo.A15.mnRed`;
* `Algo.A15.run_mnRed` — that reduction computes `Iso^Δ_K(x,y)`;
* `Algo.A15.mnRound_value` — hence the value of the round is the answer;
* `Algo.A15.mnCostQ`, `Algo.A15.mnRunCostQS` — the cost data, with a sound master test.

No axiom, no `sorry`.
-/

namespace Algo.A15

open RAM Babai

noncomputable section

variable {n : ℕ}

/-! ## The node and the state -/

/-- **The master node.**  One slot per kind: the entry (`Algo.RawSI`, no kind yet), the
dispatch of Sec. 15 line 1, the Chain Rule, the descent.  A later kind appends one more
`Option` component. -/
abbrev MNode := Option RawSI × Option RawWinSI × Option RawWinSI × Option RawDescSI

/-- **The master fold state**: the coset reached so far.  All three kinds fold this. -/
abbrev MState := RawCoset

/-- A node of the dispatch kind. -/
def mnDisp (i : RawWinSI) : MNode := (none, some i, none, none)

/-- A node of the Chain Rule kind. -/
def mnChain (i : RawWinSI) : MNode := (none, none, some i, none)

/-- A node of the descent kind. -/
def mnDesc (I : RawDescSI) : MNode := (none, none, none, some I)

/-! ## The three global data -/

/-- **The domain size**, read off the node as the length of its first string.  A node no kind
claims gets `0`. -/
def mnGround (x : MNode) : ℕ :=
  match x.2.1 with
  | some i => i.2.2.2.1.length
  | none =>
      match x.2.2.1 with
      | some i => i.2.2.2.1.length
      | none =>
          match x.2.2.2 with
          | some I => I.1.2.2.2.1.length
          | none => 0

/-- The window of a node. -/
def mnWin (x : MNode) : List ℕ :=
  match x.2.1 with
  | some i => i.1
  | none =>
      match x.2.2.1 with
      | some i => i.1
      | none =>
          match x.2.2.2 with
          | some I => I.1.1
          | none => []

/-- The first component of the measure of item 7: the number of points of the window, which
is what the Chain Rule cuts. -/
def mnRank (x : MNode) : ℕ := (mnWin x).length

/-- The local component of the measure of item 7.  It orders the cycle of Sec. 15: a
dispatch node with more than one orbit is above the Chain Rule node it calls (`2 > 1`), and a
Chain Rule node at a leaf is above the dispatch node it calls, whose window has then at most
one point (`1 > 0`).  A descent node is above everything it calls. -/
def mnLoc (x : MNode) : ℕ :=
  match x.2.1 with
  | some i => if i.1.length ≤ 1 then 0 else 2
  | none =>
      match x.2.2.1 with
      | some _ => 1
      | none =>
          match x.2.2.2 with
          | some I => if I.2.isSome then 4 else 3
          | none => 0

/-- **The master measure**, by the recipe of item 7 with `K = 5`. -/
def mnMeasure (x : MNode) : ℕ := measureOfRank mnRank (fun _ => 5) mnLoc mnGround x

theorem mnLoc_lt (x : MNode) : mnLoc x < 5 := by
  obtain ⟨o1, o2, o3, o4⟩ := x
  cases o2 with
  | some i => by_cases h : i.1.length ≤ 1 <;> simp [mnLoc, h]
  | none =>
      cases o3 with
      | some i => simp [mnLoc]
      | none =>
          cases o4 with
          | some I => by_cases h : I.2.isSome = true <;> simp [mnLoc, h]
          | none => simp [mnLoc]

/-! ### The measure at a node of each kind -/

theorem mnMeasure_disp (i : RawWinSI) :
    mnMeasure (mnDisp i) = i.1.length * 5 + (if i.1.length ≤ 1 then 0 else 2) := rfl

theorem mnMeasure_chain (i : RawWinSI) : mnMeasure (mnChain i) = i.1.length * 5 + 1 := rfl

theorem mnMeasure_desc (I : RawDescSI) :
    mnMeasure (mnDesc I) = I.1.1.length * 5 + (if I.2.isSome then 4 else 3) := rfl

theorem mnGround_disp (i : RawWinSI) : mnGround (mnDisp i) = i.2.2.2.1.length := rfl
theorem mnGround_chain (i : RawWinSI) : mnGround (mnChain i) = i.2.2.2.1.length := rfl
theorem mnGround_desc (I : RawDescSI) : mnGround (mnDesc I) = I.1.2.2.2.1.length := rfl

/-! ## Well-formedness

The semantic part of every disjunct is `Algo.A15.TChainWF`: every orbit of the node's group
inside its window has at most one point.  `Algo.A15.tChainWF_child` (Chain Rule children) and
`Algo.A15.mnTriv_of_le` (descent children) are the two proofs that it is preserved.

The rest is the size invariant of the note "A6 repair": the generators are shortened
(`Algo.WinWF` carries `I.2.1.length ≤ n * n`) and the letters of both strings are below
`2 * n`.  Without the letter bound the encoding of a node is not bounded by any polynomial of
the domain size, and `Algo.Round.CostQ.size_le` fails. -/

/-- **A well-formed window instance of the master round.**  `Algo.WinWF` (the window is a
repetition-free list of points, invariant under the group; the generators are shortened; the
representative is a permutation), the letter bound of both strings, and the invariant. -/
def MWinWF (n : ℕ) (i : RawWinSI) : Prop :=
  WinWF n i ∧ RawStr.WF n (2 * n) i.2.2.2.1 ∧ RawStr.WF n (2 * n) i.2.2.2.2 ∧
    ∀ o ∈ winOrbits (i.2.1, i.1), o.length ≤ 1

/-- A well-formed window instance carries the toy invariant of `Workspace/Algo/A15Test.lean`,
so every lemma proved there applies to it. -/
theorem MWinWF.toTChainWF {i : RawWinSI} (h : MWinWF n i) : TChainWF n i := ⟨h.1, h.2.2.2⟩

/-- **A well-formed descent instance.**  `Algo.DescWF` (the descent data names a
repetition-free list of points and the true index of its pointwise stabilizer), the invariant
and the letter bound of the window instance inside it, and a bound on the number of cosets:
the descent kind claims only descents of at most `n` cosets.  Prop. 11.1.6 says nothing about
`|G : H|`, so some bound has to be asked for, and it is asked for here rather than hidden in
a width bound. -/
def MDescWF (n : ℕ) (I : RawDescSI) : Prop :=
  DescWF n I ∧ MWinWF n I.1 ∧ ∀ d idx, I.2 = some (d, idx) → idx ≤ n

/-- **The master well-formedness.**  Exactly one slot is filled, and its payload is well
formed.  Nothing is claimed about a node in the entry slot: that kind is not built. -/
def MWF (n : ℕ) (x : MNode) : Prop :=
  (∃ i, x = mnDisp i ∧ MWinWF n i) ∨ (∃ i, x = mnChain i ∧ MWinWF n i) ∨
    (∃ I, x = mnDesc I ∧ MDescWF n I)

theorem mnWF_disp {i : RawWinSI} (h : MWF n (mnDisp i)) : MWinWF n i := by
  rcases h with ⟨i', he, hw⟩ | ⟨i', he, -⟩ | ⟨I', he, -⟩
  · have : i' = i := by simpa [mnDisp] using he.symm
    rw [← this]; exact hw
  · exact absurd he.symm (by simp [mnDisp, mnChain])
  · exact absurd he.symm (by simp [mnDisp, mnDesc])

theorem mnWF_chain {i : RawWinSI} (h : MWF n (mnChain i)) : MWinWF n i := by
  rcases h with ⟨i', he, -⟩ | ⟨i', he, hw⟩ | ⟨I', he, -⟩
  · exact absurd he.symm (by simp [mnDisp, mnChain])
  · have : i' = i := by simpa [mnChain] using he.symm
    rw [← this]; exact hw
  · exact absurd he.symm (by simp [mnChain, mnDesc])

theorem mnWF_desc {I : RawDescSI} (h : MWF n (mnDesc I)) : MDescWF n I := by
  rcases h with ⟨i', he, -⟩ | ⟨i', he, -⟩ | ⟨I', he, hw⟩
  · exact absurd he.symm (by simp [mnDisp, mnDesc])
  · exact absurd he.symm (by simp [mnChain, mnDesc])
  · have : I' = I := by simpa [mnDesc] using he.symm
    rw [← this]; exact hw

/-! ## The invariant, and what it gives

Under the invariant the group of a node **fixes its window pointwise**, so an instance the
dispatch finds transitive has a window of at most one point, and a subgroup inherits the
invariant. -/

/-- **A group with singleton orbits inside its window fixes the window pointwise.** -/
theorem mnFix {i : RawWinSI} (hI : TChainWF n i) {g : Equiv.Perm (Fin n)}
    (hg : g ∈ decGroup n i.2.1) {v : Fin n} (hv : (v : ℕ) ∈ i.1) : g v = v := by
  obtain ⟨⟨hx, hy, hnd, hlt, hgs, hgl, hσ, hinv⟩, horb⟩ := hI
  have hflat : (v : ℕ) ∈ (winOrbits (i.2.1, i.1)).flatten := winOrbits_cover hgs hlt hv
  obtain ⟨o, ho, hvo⟩ := List.mem_flatten.1 hflat
  obtain ⟨j, hj, rfl⟩ := winOrbits_mem ho
  have hjn : j < n := hlt j hj
  obtain ⟨hvn, hvorb⟩ := (mem_rawOrbit_iff hgs hjn (v : ℕ)).1 hvo
  obtain ⟨a, ha⟩ := MulAction.mem_orbit_iff.1 hvorb
  have hgvn : (g v : ℕ) < n := (g v).isLt
  have hgorb : (⟨(g v : ℕ), hgvn⟩ : Fin n) ∈ MulAction.orbit (decGroup n i.2.1) ⟨j, hjn⟩ := by
    refine MulAction.mem_orbit_iff.2 ⟨(⟨g, hg⟩ : decGroup n i.2.1) * a, ?_⟩
    rw [mul_smul, ha]
    refine Fin.ext ?_
    have : ((⟨g, hg⟩ : decGroup n i.2.1) • (⟨(v : ℕ), hvn⟩ : Fin n)) = g ⟨(v : ℕ), hvn⟩ := rfl
    rw [this]
  have hgmem : (g v : ℕ) ∈ rawOrbit (i.2.1, j) :=
    (mem_rawOrbit_iff hgs hjn _).2 ⟨hgvn, hgorb⟩
  exact Fin.ext (eq_of_mem_of_length_le_one (horb _ ho) hgmem hvo)

/-- **A subgroup inherits the invariant** on the same window: its orbits sit inside the
orbits of the bigger group, which have one point. -/
theorem mnTriv_of_le {i : RawWinSI} (hI : TChainWF n i) {gs : RawGens}
    (hgs : RawGens.WF n gs) (hle : decGroup n gs ≤ decGroup n i.2.1)
    {o : List ℕ} (ho : o ∈ winOrbits (gs, i.1)) : o.length ≤ 1 := by
  obtain ⟨⟨hx, hy, hnd, hlt, hgs0, hgl, hσ, hinv⟩, horb⟩ := hI
  obtain ⟨j, hj, rfl⟩ := winOrbits_mem ho
  have hjn : j < n := hlt j hj
  refine length_le_one_of_subset (winOrbits_nodup ho) ?_ (m := [j]) (by simp)
  intro k hk
  obtain ⟨hkn, hkorb⟩ := (mem_rawOrbit_iff hgs hjn k).1 hk
  obtain ⟨a, ha⟩ := MulAction.mem_orbit_iff.1 hkorb
  have hfix : (a : Equiv.Perm (Fin n)) ⟨j, hjn⟩ = ⟨j, hjn⟩ :=
    mnFix ⟨⟨hx, hy, hnd, hlt, hgs0, hgl, hσ, hinv⟩, horb⟩ (hle a.2) hj
  have : (⟨k, hkn⟩ : Fin n) = ⟨j, hjn⟩ := by rw [← ha]; exact hfix
  have hkj : k = j := congrArg Fin.val this
  simp [hkj]

/-! ## The dispatch kind — line 1 of Sec. 15

The decision tree of Sec. 15 will live in `Algo.A15.mnDispChild`.  What is there now is the
part the `Algo` track has built:

* **the leaf.**  A window of at most one point is answered outright.  Under the invariant the
  group fixes such a window pointwise (`Algo.A15.mnFix`), so the window condition of Eq. (58)
  does not depend on the candidate, and the answer is the whole candidate set or the empty
  set — `Algo.A15.tStubAns`, proved correct in `Workspace/Algo/A15Test.lean`.
  `Algo.rawBrute` cannot be used here: it answers `Iso_G(x,y)` for the **whole** domain, it
  takes an enumeration list of `G` as an argument, and it reads the strings over a finite
  alphabet `Fin s`.  None of the three is available at a window node.
* **the intransitive case**, Sec. 15 line 1 step 3: more than one orbit inside the window,
  one child, the Chain Rule node on the same instance.
* **everything else**: the answer `none`, and `Algo.A15.MWF` does not claim it.  Under the
  invariant "everything else" is empty, because an instance with at most one orbit has a
  window of at most one point (`Algo.A15.length_le_one_of_leaf`).

There is no off-group exit.  The candidate set of a raw node is a coset `σ · G`, which is
never empty; the empty answer arises inside the Chain Rule, where `Algo.cosetChain` stops at
`C = ∅`. -/

/-- The test of line 1: is the group intransitive on the window? -/
def mnDispTest (i : RawWinSI) : Bool := decide (1 < (winOrbits (i.2.1, i.1)).length)

/-- The answer of a dispatch node that is not intransitive: the one-point leaf, and the
clearly marked default `none` on a node the dispatch cannot handle. -/
def mnLeafAns (i : RawWinSI) : RawCoset := if i.1.length ≤ 1 then tStubAns i else none

/-- The `j`-th child of a dispatch node: in the intransitive case one Chain Rule node, and
otherwise none. -/
def mnDispChild (p : RawWinSI × ℕ × RawCoset) : Option MNode :=
  if mnDispTest p.1 then (if p.2.1 = 0 then some (mnChain p.1) else none) else none

/-- The number of children of a dispatch node. -/
def mnDispWidth (i : RawWinSI) : ℕ := if mnDispTest i then 1 else 0

/-- The answer of a dispatch node: the child's answer in the intransitive case, and the leaf
answer otherwise. -/
def mnDispFinish (p : RawWinSI × RawCoset) : RawCoset :=
  if mnDispTest p.1 then p.2 else mnLeafAns p.1

/-- **An intransitive window has at least two points.**  The orbits are nonempty and
disjoint, so there are at most as many of them as there are points
(`Algo.length_winOrbits_le`). -/
theorem two_le_of_mnDispTest {i : RawWinSI} (h : mnDispTest i = true) : 2 ≤ i.1.length := by
  have h1 : 1 < (winOrbits (i.2.1, i.1)).length := of_decide_eq_true h
  have h2 := length_winOrbits_le i.2.1 i.1
  omega

/-- **The dispatch kind.** -/
def mnDispKind (n : ℕ) : Kind MNode MState RawCoset (MWF n) mnGround mnMeasure where
  ι := RawWinSI
  ω := RawCoset
  encι := inferInstance
  encω := inferInstance
  e := mnDisp
  proj := fun x => x.2.1
  u := id
  projω := some
  proj_e := fun _ => rfl
  projω_u := fun _ => rfl
  eq_e_of_proj := by
    rintro x i (⟨i', rfl, -⟩ | ⟨i', rfl, -⟩ | ⟨I', rfl, -⟩) h
    · have : i' = i := by simpa [mnDisp] using h
      rw [this]
    · exact absurd h (by simp [mnChain])
    · exact absurd h (by simp [mnDesc])
  width := mnDispWidth
  child := mnDispChild
  init := fun _ => none
  combine := fun p => p.2.2.2
  finish := mnDispFinish
  child_eq_none := by
    intro i j w hj
    rw [mnDispChild]
    by_cases h : mnDispTest i = true
    · rw [if_pos h]
      rw [mnDispWidth, if_pos h] at hj
      rw [if_neg (by omega : ¬ j = 0)]
    · rw [if_neg h]
  child_wf := by
    intro i j w y hi hc
    have hI : MWinWF n i := mnWF_disp hi
    rw [mnDispChild] at hc
    by_cases h : mnDispTest i = true
    · rw [if_pos h] at hc
      by_cases hj : j = 0
      · rw [if_pos hj] at hc
        have : y = mnChain i := (Option.some.inj hc).symm
        rw [this]
        exact Or.inr (Or.inl ⟨i, rfl, hI⟩)
      · rw [if_neg hj] at hc; exact absurd hc (by simp)
    · rw [if_neg h] at hc; exact absurd hc (by simp)
  child_measure := by
    intro i j w y hi hc
    rw [mnDispChild] at hc
    by_cases h : mnDispTest i = true
    · rw [if_pos h] at hc
      by_cases hj : j = 0
      · rw [if_pos hj] at hc
        have hy : y = mnChain i := (Option.some.inj hc).symm
        have h2 := two_le_of_mnDispTest h
        rw [hy, mnMeasure_chain, mnMeasure_disp, if_neg (by omega : ¬ i.1.length ≤ 1)]
        omega
      · rw [if_neg hj] at hc; exact absurd hc (by simp)
    · rw [if_neg h] at hc; exact absurd hc (by simp)
  child_ground := by
    intro i j w y hi hc
    rw [mnDispChild] at hc
    by_cases h : mnDispTest i = true
    · rw [if_pos h] at hc
      by_cases hj : j = 0
      · rw [if_pos hj] at hc
        have hy : y = mnChain i := (Option.some.inj hc).symm
        rw [hy]; exact le_refl _
      · rw [if_neg hj] at hc; exact absurd hc (by simp)
    · rw [if_neg h] at hc; exact absurd hc (by simp)

/-! ## The Chain Rule kind

`Algo.chainRound` (Prop. 11.1.7 with Eq. (64)) with the abstract `solve` removed: at a leaf
the node grows **one child**, the dispatch node on the very instance `Algo.chainRound` would
have handed to `solve`.  Away from the leaf the children are `Algo.winChild`, whose window is
one orbit — and shortening matters here: `Algo.winChild` puts `Algo.tidyGens` of the current
answer group into the child, so the child's generator list is again at most `n * n` long, and
`Algo.Round.CostQ.size_le` holds at the child. -/

/-- The `j`-th child of a Chain Rule node. -/
def mnChainChild (p : RawWinSI × ℕ × RawCoset) : Option MNode :=
  if (winOrbits (p.1.2.1, p.1.1)).length ≤ 1 then
    (if p.2.1 = 0 then some (mnDisp p.1) else none)
  else (winChild p).map mnChain

/-- **The letters of a child of the Chain Rule round are the letters of its parent**: the two
strings are copied unchanged. -/
theorem mnStr_winChild {p : RawWinSI × ℕ × RawCoset} {J : RawWinSI}
    (hc : winChild p = some J) : J.2.2.2 = p.1.2.2.2 := by
  obtain ⟨g, τ, -, -, -, -, rfl⟩ := winChild_eq_some hc
  rfl

/-- **The Chain Rule kind.** -/
def mnChainKind (n : ℕ) : Kind MNode MState RawCoset (MWF n) mnGround mnMeasure where
  ι := RawWinSI
  ω := RawCoset
  encι := inferInstance
  encω := inferInstance
  e := mnChain
  proj := fun x => x.2.2.1
  u := id
  projω := some
  proj_e := fun _ => rfl
  projω_u := fun _ => rfl
  eq_e_of_proj := by
    rintro x i (⟨i', rfl, -⟩ | ⟨i', rfl, -⟩ | ⟨I', rfl, -⟩) h
    · exact absurd h (by simp [mnDisp])
    · have : i' = i := by simpa [mnChain] using h
      rw [this]
    · exact absurd h (by simp [mnDesc])
  width := fun i => (winOrbits (i.2.1, i.1)).length + 1
  child := mnChainChild
  init := fun i => some (i.2.1, i.2.2.1)
  combine := fun p => p.2.2.2
  finish := fun p => p.2
  child_eq_none := by
    intro i j w hj
    rw [mnChainChild]
    by_cases h : (winOrbits (i.2.1, i.1)).length ≤ 1
    · rw [if_pos h, if_neg (by omega : ¬ j = 0)]
    · rw [if_neg h]
      have hnone : winChild (i, j, w) = none :=
        (chainRound n (fun _ => none)).child_eq_none i j w
          (by show (winOrbits (i.2.1, i.1)).length ≤ j; omega)
      rw [hnone]
      rfl
  child_wf := by
    intro i j w y hi hc
    have hI : MWinWF n i := mnWF_chain hi
    rw [mnChainChild] at hc
    by_cases h : (winOrbits (i.2.1, i.1)).length ≤ 1
    · rw [if_pos h] at hc
      by_cases hj : j = 0
      · rw [if_pos hj] at hc
        have : y = mnDisp i := (Option.some.inj hc).symm
        rw [this]
        exact Or.inl ⟨i, rfl, hI⟩
      · rw [if_neg hj] at hc; exact absurd hc (by simp)
    · rw [if_neg h] at hc
      cases hw : winChild (i, j, w) with
      | none => rw [hw] at hc; exact absurd hc (by simp)
      | some J =>
          rw [hw] at hc
          have hy : y = mnChain J := (Option.some.inj hc).symm
          have hstr : J.2.2.2 = i.2.2.2 := mnStr_winChild hw
          have hJ : TChainWF n J := tChainWF_child hI.toTChainWF hw
          rw [hy]
          refine Or.inr (Or.inl ⟨J, rfl, ⟨hJ.1, ?_, ?_, hJ.2⟩⟩)
          · rw [show J.2.2.2.1 = i.2.2.2.1 from congrArg Prod.fst hstr]; exact hI.2.1
          · rw [show J.2.2.2.2 = i.2.2.2.2 from congrArg Prod.snd hstr]; exact hI.2.2.1
  child_measure := by
    intro i j w y hi hc
    have hI : MWinWF n i := mnWF_chain hi
    rw [mnChainChild] at hc
    by_cases h : (winOrbits (i.2.1, i.1)).length ≤ 1
    · rw [if_pos h] at hc
      by_cases hj : j = 0
      · rw [if_pos hj] at hc
        have hy : y = mnDisp i := (Option.some.inj hc).symm
        have hlen : i.1.length ≤ 1 := length_le_one_of_leaf hI.toTChainWF h
        rw [hy, mnMeasure_disp, mnMeasure_chain, if_pos hlen]
        omega
      · rw [if_neg hj] at hc; exact absurd hc (by simp)
    · rw [if_neg h] at hc
      cases hw : winChild (i, j, w) with
      | none => rw [hw] at hc; exact absurd hc (by simp)
      | some J =>
          rw [hw] at hc
          have hy : y = mnChain J := (Option.some.inj hc).symm
          have hlt : J.1.length < i.1.length :=
            (chainRound n (fun _ => none)).child_measure i j w J hI.1 hw
          rw [hy, mnMeasure_chain, mnMeasure_chain]
          omega
  child_ground := by
    intro i j w y hi hc
    rw [mnChainChild] at hc
    by_cases h : (winOrbits (i.2.1, i.1)).length ≤ 1
    · rw [if_pos h] at hc
      by_cases hj : j = 0
      · rw [if_pos hj] at hc
        have hy : y = mnDisp i := (Option.some.inj hc).symm
        rw [hy]; exact le_refl _
      · rw [if_neg hj] at hc; exact absurd hc (by simp)
    · rw [if_neg h] at hc
      cases hw : winChild (i, j, w) with
      | none => rw [hw] at hc; exact absurd hc (by simp)
      | some J =>
          rw [hw] at hc
          have hy : y = mnChain J := (Option.some.inj hc).symm
          have hstr : J.2.2.2 = i.2.2.2 := mnStr_winChild hw
          rw [hy, mnGround_chain, mnGround_chain,
            show J.2.2.2.1 = i.2.2.2.1 from congrArg Prod.fst hstr]

/-! ## The descent kind

`Algo.descentRound` (Prop. 11.1.6 with Eq. (62)) with the abstract `solve` removed.  A node
that carries descent data has one child per coset of the kernel, each a descent node that
does not descend again; a node that carries none has **one child**, the dispatch node on the
instance `Algo.descentRound` would have handed to `solve`.

Shortening again matters at the children: `Algo.descKer` goes through `Algo.rawKerGens` and
`Algo.rawShorten`, so the kernel is given by at most `n * n` generators
(`Algo.length_descKer_le`), and the two strings are copied unchanged. -/

/-- The child of a descent node that does not descend: the dispatch node on its own window
instance. -/
def mnDescLeafChild (p : RawDescSI × ℕ × RawCoset) : Option MNode :=
  if p.2.1 = 0 then some (mnDisp p.1.1) else none

/-- The `j`-th child of a descent node. -/
def mnDescChild (p : RawDescSI × ℕ × RawCoset) : Option MNode :=
  p.1.2.elim (mnDescLeafChild p) (fun _ => (descChild p).map mnDesc)

/-- The number of children of a descent node. -/
def mnDescWidth (I : RawDescSI) : ℕ := I.2.elim 1 (fun q => q.2)

/-- The fold of a descent node: the child's answer at a node that does not descend, and the
join of Eq. (62) at one that does. -/
def mnDescCombine (p : RawDescSI × ℕ × RawCoset × RawCoset) : RawCoset :=
  p.1.2.elim p.2.2.2 (fun _ => descCombine p)

/-- **The descent kind.** -/
def mnDescKind (n : ℕ) : Kind MNode MState RawCoset (MWF n) mnGround mnMeasure where
  ι := RawDescSI
  ω := RawCoset
  encι := inferInstance
  encω := inferInstance
  e := mnDesc
  proj := fun x => x.2.2.2
  u := id
  projω := some
  proj_e := fun _ => rfl
  projω_u := fun _ => rfl
  eq_e_of_proj := by
    rintro x i (⟨i', rfl, -⟩ | ⟨i', rfl, -⟩ | ⟨I', rfl, -⟩) h
    · exact absurd h (by simp [mnDisp])
    · exact absurd h (by simp [mnChain])
    · have : I' = i := by simpa [mnDesc] using h
      rw [this]
  width := mnDescWidth
  child := mnDescChild
  init := fun _ => none
  combine := mnDescCombine
  finish := fun p => p.2
  child_eq_none := by
    intro I j w hj
    have hj' : mnDescWidth I ≤ j := hj
    show mnDescChild (I, j, w) = none
    rw [mnDescChild]
    cases hq : I.2 with
    | none =>
        rw [mnDescWidth, hq] at hj'
        simp only [Option.elim] at hj' ⊢
        rw [mnDescLeafChild, if_neg (by omega : ¬ j = 0)]
    | some q =>
        rw [mnDescWidth, hq] at hj'
        simp only [Option.elim] at hj' ⊢
        have hnone : descChild (I, j, w) = none :=
          (descentRound n (fun _ => none)).child_eq_none I j w
            (by show I.2.elim 0 (fun q => q.2) ≤ j; rw [hq]; simp only [Option.elim]; omega)
        rw [hnone]
        rfl
  child_wf := by
    intro I j w y hI hc
    have hID : MDescWF n I := mnWF_desc hI
    rw [mnDescChild] at hc
    cases hq : I.2 with
    | none =>
        rw [hq] at hc
        simp only [Option.elim] at hc
        rw [mnDescLeafChild] at hc
        by_cases hj : j = 0
        · rw [if_pos hj] at hc
          have : y = mnDisp I.1 := (Option.some.inj hc).symm
          rw [this]
          exact Or.inl ⟨I.1, rfl, hID.2.1⟩
        · rw [if_neg hj] at hc; exact absurd hc (by simp)
    | some q =>
        rw [hq] at hc
        simp only [Option.elim] at hc
        cases hw : descChild (I, j, w) with
        | none => rw [hw] at hc; exact absurd hc (by simp)
        | some J =>
            rw [hw] at hc
            have hy : y = mnDesc J := (Option.some.inj hc).symm
            obtain ⟨q', hq', -, hJ⟩ := descChild_eq_some (p := (I, j, w)) hw
            have hqq : q' = q := by
              have : I.2 = some q' := hq'
              rw [hq] at this
              exact (Option.some.inj this).symm
            subst hqq
            have hDJ : DescWF n J :=
              (descentRound n (fun _ => none)).child_wf I j w J hID.1 hw
            have hwin : MWinWF n J.1 := by
              refine ⟨hDJ.1, ?_, ?_, ?_⟩
              · rw [show J.1.2.2.2.1 = I.1.2.2.2.1 from by rw [hJ]]; exact hID.2.1.2.1
              · rw [show J.1.2.2.2.2 = I.1.2.2.2.2 from by rw [hJ]]; exact hID.2.1.2.2.1
              · intro o ho
                have hgs : RawGens.WF n (descKer I.1 q'.1) := wf_descKer hID.1 hq'
                have hle : decGroup n (descKer I.1 q'.1) ≤ decGroup n I.1.2.1 :=
                  descKer_le hID.1 hq'
                refine mnTriv_of_le hID.2.1.toTChainWF hgs hle (o := o) ?_
                have h1 : J.1.2.1 = descKer I.1 q'.1 := by rw [hJ]
                have h2 : J.1.1 = I.1.1 := by rw [hJ]
                rw [h1, h2] at ho
                exact ho
            rw [hy]
            refine Or.inr (Or.inr ⟨J, rfl, ⟨hDJ, hwin, ?_⟩⟩)
            intro d' idx' hcon
            rw [hJ] at hcon
            exact absurd hcon (by simp)
  child_measure := by
    intro I j w y hI hc
    rw [mnDescChild] at hc
    cases hq : I.2 with
    | none =>
        rw [hq] at hc
        simp only [Option.elim] at hc
        rw [mnDescLeafChild] at hc
        by_cases hj : j = 0
        · rw [if_pos hj] at hc
          have hy : y = mnDisp I.1 := (Option.some.inj hc).symm
          rw [hy, mnMeasure_disp, mnMeasure_desc, hq]
          by_cases hlen : I.1.1.length ≤ 1 <;> simp [hlen]
        · rw [if_neg hj] at hc; exact absurd hc (by simp)
    | some q =>
        rw [hq] at hc
        simp only [Option.elim] at hc
        cases hw : descChild (I, j, w) with
        | none => rw [hw] at hc; exact absurd hc (by simp)
        | some J =>
            rw [hw] at hc
            have hy : y = mnDesc J := (Option.some.inj hc).symm
            obtain ⟨q', hq', -, hJ⟩ := descChild_eq_some (p := (I, j, w)) hw
            have hw1 : J.1.1 = I.1.1 := by rw [hJ]
            have hs2 : J.2 = none := by rw [hJ]
            rw [hy, mnMeasure_desc, mnMeasure_desc, hw1, hs2, hq]
            simp
  child_ground := by
    intro I j w y hI hc
    rw [mnDescChild] at hc
    cases hq : I.2 with
    | none =>
        rw [hq] at hc
        simp only [Option.elim] at hc
        rw [mnDescLeafChild] at hc
        by_cases hj : j = 0
        · rw [if_pos hj] at hc
          have hy : y = mnDisp I.1 := (Option.some.inj hc).symm
          rw [hy]; exact le_refl _
        · rw [if_neg hj] at hc; exact absurd hc (by simp)
    | some q =>
        rw [hq] at hc
        simp only [Option.elim] at hc
        cases hw : descChild (I, j, w) with
        | none => rw [hw] at hc; exact absurd hc (by simp)
        | some J =>
            rw [hw] at hc
            have hy : y = mnDesc J := (Option.some.inj hc).symm
            obtain ⟨q', hq', -, hJ⟩ := descChild_eq_some (p := (I, j, w)) hw
            rw [hy, mnGround_desc, mnGround_desc, show J.1.2.2.2.1 = I.1.2.2.2.1 from by rw [hJ]]

/-! ## The master round -/

/-- The kinds of the master round, in the order the dispatch tries them. -/
def mnKinds (n : ℕ) : List (Kind MNode MState RawCoset (MWF n) mnGround mnMeasure) :=
  [mnDispKind n, mnChainKind n, mnDescKind n]

/-- **The master round of the three kinds.** -/
def mnRound (n : ℕ) : Round MNode MState RawCoset := famRound none none (mnKinds n)

theorem mnKinds_disp (n : ℕ) :
    mnKinds n = [] ++ mnDispKind n :: [mnChainKind n, mnDescKind n] := rfl

theorem mnKinds_chain (n : ℕ) :
    mnKinds n = [mnDispKind n] ++ mnChainKind n :: [mnDescKind n] := rfl

theorem mnKinds_desc (n : ℕ) :
    mnKinds n = [mnDispKind n, mnChainKind n] ++ mnDescKind n :: [] := rfl

theorem mnMisses_disp (i : RawWinSI) :
    Misses ([] : List (Kind MNode MState RawCoset (MWF n) mnGround mnMeasure)) (mnDisp i) :=
  misses_nil _

theorem mnMisses_chain (i : RawWinSI) : Misses [mnDispKind n] (mnChain i) := by
  intro k hk
  have : k = mnDispKind n := by simpa using hk
  rw [this]; rfl

theorem mnMisses_desc (I : RawDescSI) : Misses [mnDispKind n, mnChainKind n] (mnDesc I) := by
  intro k hk
  have hk' : k = mnDispKind n ∨ k = mnChainKind n := by simpa using hk
  rcases hk' with rfl | rfl <;> rfl

/-! ### The five routines at a node of each kind -/

theorem mnRound_width_disp (i : RawWinSI) :
    (mnRound n).width (mnDisp i) = mnDispWidth i :=
  famWidth_eq [] (mnDispKind n) [mnChainKind n, mnDescKind n] i (mnMisses_disp i)

theorem mnRound_init_disp (i : RawWinSI) : (mnRound n).init (mnDisp i) = none :=
  famInit_eq none [] (mnDispKind n) [mnChainKind n, mnDescKind n] i (mnMisses_disp i)

theorem mnRound_child_disp (i : RawWinSI) (j : ℕ) (s : RawCoset) :
    (mnRound n).child (mnDisp i, j, s) = mnDispChild (i, j, s) :=
  famChild_eq [] (mnDispKind n) [mnChainKind n, mnDescKind n] i j s (mnMisses_disp i)

theorem mnRound_combine_disp (i : RawWinSI) (j : ℕ) (s a : RawCoset) :
    (mnRound n).combine (mnDisp i, j, s, a) = a :=
  famCombine_eq [] (mnDispKind n) [mnChainKind n, mnDescKind n] i j s a (mnMisses_disp i)

theorem mnRound_finish_disp (i : RawWinSI) (s : RawCoset) :
    (mnRound n).finish (mnDisp i, s) = mnDispFinish (i, s) :=
  famFinish_eq none [] (mnDispKind n) [mnChainKind n, mnDescKind n] i s (mnMisses_disp i)

theorem mnRound_width_chain (i : RawWinSI) :
    (mnRound n).width (mnChain i) = (winOrbits (i.2.1, i.1)).length + 1 :=
  famWidth_eq [mnDispKind n] (mnChainKind n) [mnDescKind n] i (mnMisses_chain i)

theorem mnRound_init_chain (i : RawWinSI) :
    (mnRound n).init (mnChain i) = some (i.2.1, i.2.2.1) :=
  famInit_eq none [mnDispKind n] (mnChainKind n) [mnDescKind n] i (mnMisses_chain i)

theorem mnRound_child_chain (i : RawWinSI) (j : ℕ) (s : RawCoset) :
    (mnRound n).child (mnChain i, j, s) = mnChainChild (i, j, s) :=
  famChild_eq [mnDispKind n] (mnChainKind n) [mnDescKind n] i j s (mnMisses_chain i)

theorem mnRound_combine_chain (i : RawWinSI) (j : ℕ) (s a : RawCoset) :
    (mnRound n).combine (mnChain i, j, s, a) = a :=
  famCombine_eq [mnDispKind n] (mnChainKind n) [mnDescKind n] i j s a (mnMisses_chain i)

theorem mnRound_finish_chain (i : RawWinSI) (s : RawCoset) :
    (mnRound n).finish (mnChain i, s) = s :=
  famFinish_eq none [mnDispKind n] (mnChainKind n) [mnDescKind n] i s (mnMisses_chain i)

theorem mnRound_width_desc (I : RawDescSI) :
    (mnRound n).width (mnDesc I) = mnDescWidth I :=
  famWidth_eq [mnDispKind n, mnChainKind n] (mnDescKind n) [] I (mnMisses_desc I)

theorem mnRound_init_desc (I : RawDescSI) : (mnRound n).init (mnDesc I) = none :=
  famInit_eq none [mnDispKind n, mnChainKind n] (mnDescKind n) [] I (mnMisses_desc I)

theorem mnRound_child_desc (I : RawDescSI) (j : ℕ) (s : RawCoset) :
    (mnRound n).child (mnDesc I, j, s) = mnDescChild (I, j, s) :=
  famChild_eq [mnDispKind n, mnChainKind n] (mnDescKind n) [] I j s (mnMisses_desc I)

theorem mnRound_combine_desc (I : RawDescSI) (j : ℕ) (s a : RawCoset) :
    (mnRound n).combine (mnDesc I, j, s, a) = mnDescCombine (I, j, s, a) :=
  famCombine_eq [mnDispKind n, mnChainKind n] (mnDescKind n) [] I j s a (mnMisses_desc I)

theorem mnRound_finish_desc (I : RawDescSI) (s : RawCoset) :
    (mnRound n).finish (mnDesc I, s) = s :=
  famFinish_eq none [mnDispKind n, mnChainKind n] (mnDescKind n) [] I s (mnMisses_desc I)

/-! ## The link to the mathematics

Every node decodes to the instance `Iso^Δ_{σG}(x,y)` of Definition 11.1.2 that it holds, and
the reduction below is the **coset form** of Remark 11.1.4 throughout: the instances are
`⟨σH, Δ, x, y⟩` with the strings unshifted.  The group form of Sec. 15 is
`Algo.alignRed` of it, applied once at the top by
`Algo.Round.runQS_eq_answer_align`. -/

/-- The instance a master node describes.  Paper: Definition 11.1.2. -/
def mnDec (n : ℕ) (x : MNode) : Babai.SIInstance (Fin n) ℕ :=
  match x.2.1 with
  | some i => decWinSI n i
  | none =>
      match x.2.2.1 with
      | some i => decWinSI n i
      | none =>
          match x.2.2.2 with
          | some I => decWinSI n I.1
          | none => ⟨∅, ∅, fun _ => 0, fun _ => 0⟩

theorem mnDec_disp (i : RawWinSI) : mnDec n (mnDisp i) = decWinSI n i := rfl
theorem mnDec_chain (i : RawWinSI) : mnDec n (mnChain i) = decWinSI n i := rfl
theorem mnDec_desc (I : RawDescSI) : mnDec n (mnDesc I) = decDescSI n I := rfl

/-- **The mathematical round of the master round**, in coset form.

* A dispatch node: one call, to the Chain Rule node on the same instance, in the
  intransitive case (Sec. 15, line 1 step 3); and the leaf answer otherwise (Eq. (58) on a
  window of at most one point).
* A Chain Rule node: the chain of Eq. (63) over the orbits of Eq. (64) when there are at
  least two of them, and one call otherwise — the very instance `Algo.chainRound` handed to
  `solve`.
* A descent node: the chain of Eq. (62) over the coset representatives of the kernel, and
  one call when there is no descent datum. -/
def mnRed (n : ℕ) (x : MNode) : Babai.SIReduction (Fin n) ℕ (Set (Equiv.Perm (Fin n))) :=
  match x.2.1 with
  | some i =>
      if mnDispTest i then .call (decWinSI n i) (fun b => .done b)
      else .done (decCoset n (mnLeafAns i))
  | none =>
      match x.2.2.1 with
      | some i =>
          if (winOrbits (i.2.1, i.1)).length ≤ 1 then .call (decWinSI n i) (fun b => .done b)
          else cosetChain (decStrN n i.2.2.2.1) (decStrN n i.2.2.2.2)
            ((winOrbits (i.2.1, i.1)).map (winSet n)) (decWinSI n i).K
      | none =>
          match x.2.2.2 with
          | some I =>
              I.2.elim (.call (decWinSI n I.1) (fun b => .done b))
                (fun q => descentChain (decGroup n (descKer I.1 q.1) : Set (Equiv.Perm (Fin n)))
                  (winSet n I.1.1) (decStrN n I.1.2.2.2.1) (decStrN n I.1.2.2.2.2) ∅
                  (descPerms n I.1 q))
          | none => .done ∅

theorem mnRed_disp (i : RawWinSI) :
    mnRed n (mnDisp i) =
      (if mnDispTest i then .call (decWinSI n i) (fun b => .done b)
        else .done (decCoset n (mnLeafAns i))) := rfl

theorem mnRed_chain (i : RawWinSI) :
    mnRed n (mnChain i) =
      (if (winOrbits (i.2.1, i.1)).length ≤ 1 then .call (decWinSI n i) (fun b => .done b)
        else cosetChain (decStrN n i.2.2.2.1) (decStrN n i.2.2.2.2)
          ((winOrbits (i.2.1, i.1)).map (winSet n)) (decWinSI n i).K) := rfl

theorem mnRed_desc (I : RawDescSI) :
    mnRed n (mnDesc I) =
      I.2.elim (.call (decWinSI n I.1) (fun b => .done b))
        (fun q => descentChain (decGroup n (descKer I.1 q.1) : Set (Equiv.Perm (Fin n)))
          (winSet n I.1.1) (decStrN n I.1.2.2.2.1) (decStrN n I.1.2.2.2.2) ∅
          (descPerms n I.1 q)) := rfl

/-- **The master round implements the master reduction.** -/
theorem implements_mnRound (n : ℕ) :
    Implements (mnRound n) id (mnDec n) (decCoset n) (mnRed n) := by
  intro x hx
  rcases hx with ⟨i, rfl, hI⟩ | ⟨i, rfl, hI⟩ | ⟨I, rfl, hI⟩
  · -- a dispatch node
    simp only [id_eq]
    rw [mnRound_width_disp, mnRound_init_disp, mnRed_disp, mnDispWidth]
    by_cases h : mnDispTest i = true
    · rw [if_pos h, if_pos h]
      refine loopMatch_oneCall (M := mnRound n) (decI' := fun y => mnDec n y)
        (decA := decCoset n) (mnDisp i) 0 0 none (mnChain i) ?_ ?_ ?_
      · rw [mnRound_child_disp]
        show mnDispChild (i, 0, none) = some (mnChain i)
        rw [mnDispChild, if_pos h, if_pos rfl]
      · intro a ha
        rw [mnRound_combine_disp, mnRound_child_disp]
        show mnDispChild (i, 0 + 1, a) = none
        rw [mnDispChild, if_pos h, if_neg (by omega : ¬ (0 : ℕ) + 1 = 0)]
      · intro a ha
        rw [mnRound_combine_disp, mnRound_finish_disp]
        show decCoset n (mnDispFinish (i, a)) = _
        rw [mnDispFinish, if_pos h]
        exact ha
    · rw [if_neg h, if_neg h]
      refine LoopMatch.done 0 0 none _ ?_ ?_
      · rw [mnRound_child_disp]
        show mnDispChild (i, 0, none) = none
        rw [mnDispChild, if_neg h]
      · rw [mnRound_finish_disp]
        show decCoset n (mnDispFinish (i, none)) = _
        rw [mnDispFinish, if_neg h]
  · -- a Chain Rule node
    simp only [id_eq]
    rw [mnRound_width_chain, mnRound_init_chain, mnRed_chain]
    by_cases hleaf : (winOrbits (i.2.1, i.1)).length ≤ 1
    · rw [if_pos hleaf]
      refine loopMatch_oneCall (M := mnRound n) (decI' := fun y => mnDec n y)
        (decA := decCoset n) (mnChain i) ((winOrbits (i.2.1, i.1)).length) 0
        (some (i.2.1, i.2.2.1)) (mnDisp i) ?_ ?_ ?_
      · rw [mnRound_child_chain]
        show mnChainChild (i, 0, some (i.2.1, i.2.2.1)) = some (mnDisp i)
        rw [mnChainChild, if_pos hleaf, if_pos rfl]
      · intro a ha
        rw [mnRound_combine_chain, mnRound_child_chain]
        show mnChainChild (i, 0 + 1, a) = none
        rw [mnChainChild, if_pos hleaf, if_neg (by omega : ¬ (0 : ℕ) + 1 = 0)]
      · intro a ha
        rw [mnRound_combine_chain, mnRound_finish_chain]
        exact ha
    · rw [if_neg hleaf]
      have h2 : 1 < (winOrbits (i.2.1, i.1)).length := by omega
      have hstate : StateOK n i (decWinSI n i).K (some (i.2.1, i.2.2.1)) := by
        refine ⟨rfl, le_refl _, ?_⟩
        intro g τ hgt
        have hg : g = i.2.1 :=
          congrArg (fun z => (Option.getD z (i.2.1, i.2.2.1)).1) hgt.symm
        rw [hg]
      have hcore := loopMatch_chainRound n (fun _ => none) hI.1 h2
        (winOrbits (i.2.1, i.1)).length 0 (by omega) (decWinSI n i).K
        (some (i.2.1, i.2.2.1)) hstate
      rw [List.drop_zero] at hcore
      have htrans := loopMatch_famRound (N := MNode) (S := MState) (α := RawCoset)
        (WF := MWF n) (ground := mnGround) (measure := mnMeasure)
        (bot := (none : RawCoset)) (botS := (none : MState))
        [mnDispKind n] (mnChainKind n) [mnDescKind n]
        (R := chainRound n (fun _ => none)) i
        (fun j w => by
          show mnChainChild (i, j, w) = Option.map mnChain (winChild (i, j, w))
          rw [mnChainChild, if_neg hleaf])
        (fun j w a => rfl)
        (fun w => by
          show w = (if (winOrbits (i.2.1, i.1)).length ≤ 1 then (none : RawCoset) else w)
          rw [if_neg hleaf])
        (decI := decWinSI n) (decI' := fun y => mnDec n y) (decA := decCoset n)
        (fun _ => rfl) (mnMisses_chain i)
        (winOrbits (i.2.1, i.1)).length 0 (some (i.2.1, i.2.2.1)) _ hcore
      have h3 : LoopMatch (mnRound n) (fun y => mnDec n y) (decCoset n) (mnChain i)
          (winOrbits (i.2.1, i.1)).length 0 (some (i.2.1, i.2.2.1))
          (cosetChain (decStrN n i.2.2.2.1) (decStrN n i.2.2.2.2)
            ((winOrbits (i.2.1, i.1)).map (winSet n)) (decWinSI n i).K) := htrans
      exact loopMatch_mono h3 _ (by omega)
  · -- a descent node
    simp only [id_eq]
    rw [mnRound_width_desc, mnRound_init_desc, mnRed_desc, mnDescWidth]
    cases hq : I.2 with
    | none =>
        simp only [Option.elim]
        refine loopMatch_oneCall (M := mnRound n) (decI' := fun y => mnDec n y)
          (decA := decCoset n) (mnDesc I) 0 0 none (mnDisp I.1) ?_ ?_ ?_
        · rw [mnRound_child_desc]
          show mnDescChild (I, 0, none) = some (mnDisp I.1)
          rw [mnDescChild, hq]
          simp only [Option.elim]
          rw [mnDescLeafChild, if_pos rfl]
        · intro a ha
          rw [mnRound_combine_desc, mnRound_child_desc]
          show mnDescChild (I, 0 + 1, mnDescCombine (I, 0, none, a)) = none
          rw [mnDescChild, hq]
          simp only [Option.elim]
          rw [mnDescLeafChild, if_neg (by omega : ¬ (0 : ℕ) + 1 = 0)]
        · intro a ha
          rw [mnRound_combine_desc, mnRound_finish_desc]
          show decCoset n (mnDescCombine (I, 0, none, a)) = _
          rw [mnDescCombine, hq]
          simp only [Option.elim]
          exact ha
    | some q =>
        simp only [Option.elim]
        have hcore := loopMatch_descentRound n (fun _ => none) hI.1 hq q.2 0 (by omega)
          ∅ none rfl
        rw [List.drop_zero] at hcore
        have htrans := loopMatch_famRound (N := MNode) (S := MState) (α := RawCoset)
          (WF := MWF n) (ground := mnGround) (measure := mnMeasure)
          (bot := (none : RawCoset)) (botS := (none : MState))
          [mnDispKind n, mnChainKind n] (mnDescKind n) []
          (R := descentRound n (fun _ => none)) I
          (fun j w => by
            show mnDescChild (I, j, w) = Option.map mnDesc (descChild (I, j, w))
            rw [mnDescChild, hq]
            simp only [Option.elim])
          (fun j w a => by
            show mnDescCombine (I, j, w, a) = descCombine (I, j, w, a)
            rw [mnDescCombine, hq]
            simp only [Option.elim])
          (fun w => by
            show w = I.2.elim (none : RawCoset) (fun _ => w)
            rw [hq]
            simp only [Option.elim])
          (decI := decDescSI n) (decI' := fun y => mnDec n y) (decA := decCoset n)
          (fun _ => rfl) (mnMisses_desc I)
          q.2 0 none _ hcore
        exact htrans

/-! ## The reduction is correct -/

/-- **The leaf of the dispatch is correct.**  Paper: Eq. (58) on a window of at most one
point, `Algo.A15.decCoset_tStubAns`. -/
theorem decCoset_mnLeafAns {i : RawWinSI} (hI : MWinWF n i)
    (h : ¬ mnDispTest i = true) : decCoset n (mnLeafAns i) = (decWinSI n i).answer := by
  have h1 : (winOrbits (i.2.1, i.1)).length ≤ 1 := by
    have := h
    simp only [mnDispTest, decide_eq_true_eq] at this
    omega
  have hlen : i.1.length ≤ 1 := length_le_one_of_leaf hI.toTChainWF h1
  rw [mnLeafAns, if_pos hlen]
  exact decCoset_tStubAns ⟨hI.1, hlen⟩

/-- **The master reduction computes the answer of the instance.** -/
theorem run_mnRed (n : ℕ) (x : MNode) (hx : MWF n x) :
    (mnRed n x).run = (mnDec n x).answer := by
  rcases hx with ⟨i, rfl, hI⟩ | ⟨i, rfl, hI⟩ | ⟨I, rfl, hI⟩
  · rw [mnRed_disp, mnDec_disp]
    by_cases h : mnDispTest i = true
    · rw [if_pos h]; rfl
    · rw [if_neg h, Babai.SIReduction.run_done]
      exact decCoset_mnLeafAns hI h
  · rw [mnRed_chain, mnDec_chain]
    by_cases hleaf : (winOrbits (i.2.1, i.1)).length ≤ 1
    · rw [if_pos hleaf]; rfl
    · rw [if_neg hleaf]
      have := run_chainRoundReduction n (fun _ => none) hI.1 (fun h => absurd h hleaf)
      rwa [chainRoundReduction, if_neg hleaf] at this
  · rw [mnRed_desc, mnDec_desc]
    cases hq : I.2 with
    | none => simp only [Option.elim]; rfl
    | some q =>
        simp only [Option.elim]
        have := run_descentRoundReduction n (fun _ => none) hI.1
          (fun hcon => absurd (hq ▸ hcon) (by simp))
        rwa [descentRoundReduction, hq] at this

/-- **The master round computes the answer.** -/
theorem mnRound_value (n : ℕ) (f : ℕ) (x : MNode) (hx : MWF n x) (hf : mnMeasure x < f) :
    decCoset n ((mnRound n).value f x) = (mnDec n x).answer :=
  roundValue_eq (mnRound n) (implements_mnRound n) (fun y hy => run_mnRed n y hy) f x hx hf

/-- **The machine computes the answer.**  `Algo.Round.evaluate` is the depth-first evaluator
of `Workspace/Algo/Evaluator.lean`, run for enough steps. -/
theorem mnRound_evaluate (n : ℕ) (f N : ℕ) (x : MNode) (hx : MWF n x) (hf : mnMeasure x < f)
    (hN : (mnRound n).subSteps f x ≤ N) :
    ∃ a : RawCoset, (mnRound n).evaluate N x = some a ∧ decCoset n a = (mnDec n x).answer :=
  ⟨(mnRound n).value f x, (mnRound n).evaluate_eq_value f N x hx hf hN,
    mnRound_value n f x hx hf⟩

/-! ## The cost of the master round

`Algo.A15.famCostQ` asks for one `Algo.A15.KindCost` per kind and three clauses about the
node type.  Every bound is a polynomial of `Algo.A15.mnGround`, the **domain size** `n`, so
the letter bound of `Algo.A15.MWinWF` is what carries the size clauses: a string of length
`n` over letters below `2 * n` has an encoding of at most `Algo.strBound (2 * n)` bits, and
everything else in a well-formed node is bounded in terms of the pair of strings by
`Algo.size_winSI_le` and `Algo.size_descSI_le`. -/

/-- The size of the pair of strings of a well-formed node. -/
def mnStrsBound (m : ℕ) : ℕ := 4 * strBound (2 * m)

/-- **The size bound of the master round**, a polynomial of the domain size. -/
def mnBound (m : ℕ) : ℕ := 64 * (chainBound (mnStrsBound m) + descBound (mnStrsBound m) + 1)

/-- The number of children of a node, bounded in the domain size. -/
def mnWidthBound (m : ℕ) : ℕ := m + 1

/-- The measure of a node, bounded in the domain size. -/
def mnMeasureBound (m : ℕ) : ℕ := 5 * m + 4

theorem mono_strBound : Monotone strBound := by
  intro a b hab
  have h : a * (2 * (a + 2) + 1) ≤ b * (2 * (b + 2) + 1) :=
    Nat.mul_le_mul hab (by omega)
  show 1 + a * (2 * (a + 2) + 1) ≤ 1 + b * (2 * (b + 2) + 1)
  omega

theorem polyBound_strBound : PolyBound strBound :=
  (polyBound_const 1).add (polyBound_id.mul
    (((polyBound_const 2).mul (polyBound_id.add (polyBound_const 2))).add (polyBound_const 1)))

theorem mono_mnStrsBound : Monotone mnStrsBound := by
  intro a b hab
  have := mono_strBound (show 2 * a ≤ 2 * b by omega)
  show 4 * strBound (2 * a) ≤ 4 * strBound (2 * b)
  omega

theorem polyBound_mnStrsBound : PolyBound mnStrsBound :=
  (polyBound_const 4).mul (polyBound_strBound.comp ((polyBound_const 2).mul polyBound_id))

theorem mono_mnBound : Monotone mnBound := by
  intro a b hab
  have h1 := mono_chainBound (mono_mnStrsBound hab)
  have h2 := mono_descBound (mono_mnStrsBound hab)
  show 64 * (chainBound (mnStrsBound a) + descBound (mnStrsBound a) + 1)
    ≤ 64 * (chainBound (mnStrsBound b) + descBound (mnStrsBound b) + 1)
  omega

theorem polyBound_mnBound : PolyBound mnBound :=
  (polyBound_const 64).mul
    (((polyBound_chainBound.comp polyBound_mnStrsBound).add
      (polyBound_descBound.comp polyBound_mnStrsBound)).add (polyBound_const 1))

theorem le_mnStrsBound (m : ℕ) : m ≤ mnStrsBound m := by
  have h : 2 * m * 1 ≤ 2 * m * (2 * (2 * m + 2) + 1) := Nat.mul_le_mul_left _ (by omega)
  show m ≤ 4 * (1 + 2 * m * (2 * (2 * m + 2) + 1))
  omega

theorem chainBound_le_mnBound (m : ℕ) : chainBound (mnStrsBound m) ≤ mnBound m := by
  show chainBound (mnStrsBound m)
    ≤ 64 * (chainBound (mnStrsBound m) + descBound (mnStrsBound m) + 1)
  omega

theorem descBound_le_mnBound (m : ℕ) : descBound (mnStrsBound m) ≤ mnBound m := by
  show descBound (mnStrsBound m)
    ≤ 64 * (chainBound (mnStrsBound m) + descBound (mnStrsBound m) + 1)
  omega

theorem sixtyfour_le_mnBound (m : ℕ) : 64 ≤ mnBound m := by
  show 64 ≤ 64 * (chainBound (mnStrsBound m) + descBound (mnStrsBound m) + 1)
  omega

/-- **The two strings of a well-formed node are small**, because their letters are below
`2 * n`.  This is the clause the note "A6 repair" asks every child to keep. -/
theorem mnSize_strs {i : RawWinSI} (hI : MWinWF n i) : Enc.size i.2.2.2 ≤ mnStrsBound n := by
  have hx : Enc.size i.2.2.2.1 ≤ strBound (2 * n) :=
    size_natList_le (by rw [hI.2.1.1]; omega) hI.2.1.2
  have hy : Enc.size i.2.2.2.2 ≤ strBound (2 * n) :=
    size_natList_le (by rw [hI.2.2.1.1]; omega) hI.2.2.1.2
  have hp : Enc.size i.2.2.2 ≤ 2 * Enc.size i.2.2.2.1 + 2 * Enc.size i.2.2.2.2 :=
    Combine.size_pair_le _ _
  show Enc.size i.2.2.2 ≤ 4 * strBound (2 * n)
  omega

theorem mnChainBound_le {i : RawWinSI} (hI : MWinWF n i) :
    chainBound (Enc.size i.2.2.2) ≤ mnBound n :=
  le_trans (mono_chainBound (mnSize_strs hI)) (chainBound_le_mnBound n)

theorem mnDescBound_le {I : RawDescSI} (hI : MDescWF n I) :
    descBound (Enc.size I.1.2.2.2) ≤ mnBound n :=
  le_trans (mono_descBound (mnSize_strs hI.2.1)) (descBound_le_mnBound n)

/-! ### The three clauses that belong to no kind -/

theorem mnLen_le_size (i : RawWinSI) : i.2.2.2.1.length ≤ Enc.size i := by
  have h1 := length_le_size i.2.2.2.1
  have h2 : Enc.size i.2.2.2.1 ≤ Enc.size i.2.2.2 := size_fst_le' i.2.2.2
  have h3 : Enc.size i.2.2.2 ≤ Enc.size i :=
    le_trans (size_snd_le' i.2.2) (le_trans (size_snd_le' i.2) (size_snd_le' i))
  omega

theorem mnGround_le (x : MNode) : mnGround x ≤ Enc.size x := by
  obtain ⟨o1, o2, o3, o4⟩ := x
  have h2 : Enc.size ((o2, o3, o4) : Option RawWinSI × Option RawWinSI × Option RawDescSI)
      ≤ Enc.size ((o1, o2, o3, o4) : MNode) := size_snd_le' ((o1, o2, o3, o4) : MNode)
  cases o2 with
  | some i =>
      have h3 : Enc.size (some i : Option RawWinSI)
          ≤ Enc.size ((some i, o3, o4) : Option RawWinSI × Option RawWinSI × Option RawDescSI) :=
        size_fst_le' ((some i, o3, o4) : Option RawWinSI × Option RawWinSI × Option RawDescSI)
      have h4 : Enc.size (some i : Option RawWinSI) = Enc.size i + 2 := size_some_eq i
      have h5 := mnLen_le_size i
      show i.2.2.2.1.length ≤ Enc.size ((o1, some i, o3, o4) : MNode)
      omega
  | none =>
      have h3 : Enc.size ((o3, o4) : Option RawWinSI × Option RawDescSI)
          ≤ Enc.size ((none, o3, o4) : Option RawWinSI × Option RawWinSI × Option RawDescSI) :=
        size_snd_le' ((none, o3, o4) : Option RawWinSI × Option RawWinSI × Option RawDescSI)
      cases o3 with
      | some i =>
          have h6 : Enc.size (some i : Option RawWinSI)
              ≤ Enc.size ((some i, o4) : Option RawWinSI × Option RawDescSI) :=
            size_fst_le' ((some i, o4) : Option RawWinSI × Option RawDescSI)
          have h7 : Enc.size (some i : Option RawWinSI) = Enc.size i + 2 := size_some_eq i
          have h8 := mnLen_le_size i
          show i.2.2.2.1.length ≤ Enc.size ((o1, none, some i, o4) : MNode)
          omega
      | none =>
          cases o4 with
          | some I =>
              have h6 : Enc.size (some I : Option RawDescSI)
                  ≤ Enc.size ((none, some I) : Option RawWinSI × Option RawDescSI) :=
                size_snd_le' ((none, some I) : Option RawWinSI × Option RawDescSI)
              have h7 : Enc.size (some I : Option RawDescSI) = Enc.size I + 2 := size_some_eq I
              have h8 := mnLen_le_size I.1
              have h9 : Enc.size I.1 ≤ Enc.size I := size_fst_le' I
              show I.1.2.2.2.1.length ≤ Enc.size ((o1, none, none, some I) : MNode)
              omega
          | none => exact Nat.zero_le _

/-- The size of a master node, in terms of the size of its payload. -/
theorem mnSize_node_le (o1 : Option RawSI) (o2 o3 : Option RawWinSI) (o4 : Option RawDescSI) :
    Enc.size ((o1, o2, o3, o4) : MNode)
      ≤ 2 * Enc.size o1 + 4 * Enc.size o2 + 8 * Enc.size o3 + 8 * Enc.size o4 := by
  have h1 : Enc.size ((o1, o2, o3, o4) : MNode)
      ≤ 2 * Enc.size o1
        + 2 * Enc.size ((o2, o3, o4) : Option RawWinSI × Option RawWinSI × Option RawDescSI) :=
    Combine.size_pair_le _ _
  have h2 : Enc.size ((o2, o3, o4) : Option RawWinSI × Option RawWinSI × Option RawDescSI)
      ≤ 2 * Enc.size o2 + 2 * Enc.size ((o3, o4) : Option RawWinSI × Option RawDescSI) :=
    Combine.size_pair_le _ _
  have h3 : Enc.size ((o3, o4) : Option RawWinSI × Option RawDescSI)
      ≤ 2 * Enc.size o3 + 2 * Enc.size o4 := Combine.size_pair_le _ _
  omega

theorem mnSize_le (x : MNode) (hx : MWF n x) : Enc.size x ≤ mnBound (mnGround x) := by
  have hnoneSI : Enc.size (none : Option RawSI) = 2 := size_none
  have hnoneW : Enc.size (none : Option RawWinSI) = 2 := size_none
  have hnoneD : Enc.size (none : Option RawDescSI) = 2 := size_none
  rcases hx with ⟨i, rfl, hI⟩ | ⟨i, rfl, hI⟩ | ⟨I, hI2, hI⟩
  · have hg : mnGround (mnDisp i) = n := hI.1.1
    have h1 : Enc.size i ≤ chainBound (Enc.size i.2.2.2) := size_winSI_le hI.1
    have h2 : chainBound (Enc.size i.2.2.2) ≤ chainBound (mnStrsBound n) :=
      mono_chainBound (mnSize_strs hI)
    have h3 : Enc.size (some i : Option RawWinSI) = Enc.size i + 2 := size_some_eq i
    have h4 := mnSize_node_le none (some i) none none
    have h5 := sixtyfour_le_mnBound n
    show Enc.size (mnDisp i) ≤ mnBound (mnGround (mnDisp i))
    rw [hg]
    show Enc.size ((none, some i, none, none) : MNode) ≤ mnBound n
    have h7 : 64 * (chainBound (mnStrsBound n) + descBound (mnStrsBound n) + 1) = mnBound n := rfl
    have h8 : chainBound (mnStrsBound n) ≤ mnBound n := chainBound_le_mnBound n
    omega
  · have hg : mnGround (mnChain i) = n := hI.1.1
    have h1 : Enc.size i ≤ chainBound (Enc.size i.2.2.2) := size_winSI_le hI.1
    have h2 : chainBound (Enc.size i.2.2.2) ≤ chainBound (mnStrsBound n) :=
      mono_chainBound (mnSize_strs hI)
    have h3 : Enc.size (some i : Option RawWinSI) = Enc.size i + 2 := size_some_eq i
    have h4 := mnSize_node_le none none (some i) none
    have h5 := sixtyfour_le_mnBound n
    have h7 : 64 * (chainBound (mnStrsBound n) + descBound (mnStrsBound n) + 1) = mnBound n := rfl
    have h8 : chainBound (mnStrsBound n) ≤ mnBound n := chainBound_le_mnBound n
    show Enc.size (mnChain i) ≤ mnBound (mnGround (mnChain i))
    rw [hg]
    show Enc.size ((none, none, some i, none) : MNode) ≤ mnBound n
    omega
  · subst hI2
    have hg : mnGround (mnDesc I) = n := hI.2.1.1.1
    have h1 : Enc.size I ≤ descBound (Enc.size I.1.2.2.2) := size_descSI_le hI.1
    have h2 : descBound (Enc.size I.1.2.2.2) ≤ descBound (mnStrsBound n) :=
      mono_descBound (mnSize_strs hI.2.1)
    have h3 : Enc.size (some I : Option RawDescSI) = Enc.size I + 2 := size_some_eq I
    have h4 := mnSize_node_le none none none (some I)
    have h5 := sixtyfour_le_mnBound n
    have h7 : 64 * (chainBound (mnStrsBound n) + descBound (mnStrsBound n) + 1) = mnBound n := rfl
    have h8 : descBound (mnStrsBound n) ≤ mnBound n := descBound_le_mnBound n
    show Enc.size (mnDesc I) ≤ mnBound (mnGround (mnDesc I))
    rw [hg]
    show Enc.size ((none, none, none, some I) : MNode) ≤ mnBound n
    omega

theorem mnBot_le (m : ℕ) : Enc.size (none : RawCoset) ≤ mnBound m := by
  have h1 : Enc.size (none : RawCoset) = 2 := size_none
  have h2 := sixtyfour_le_mnBound m
  omega

/-! ### The routines are routines

The predicates are named `def`s and the tests are put together with the `RAM` combinators;
an inline lambda inside a `List.filter` or a `List.map` makes these proofs very slow. -/

/-- Building a dispatch node out of the instance of a window node. -/
theorem mnPolyFun_dispOf {γ : Type} [Enc γ] {f : γ → RawWinSI} (hf : PolyFun f) :
    PolyFun (fun z : γ => (some (mnDisp (f z)) : Option MNode)) :=
  (((polyFun_const (none : Option RawSI)).pair
    (((hf.comp polyFun_some).pair
      ((polyFun_const (none : Option RawWinSI)).pair
        (polyFun_const (none : Option RawDescSI))))))).comp polyFun_some

/-- Building a Chain Rule node. -/
theorem mnPolyFun_chainOf {γ : Type} [Enc γ] {f : γ → RawWinSI} (hf : PolyFun f) :
    PolyFun (fun z : γ => (some (mnChain (f z)) : Option MNode)) :=
  (((polyFun_const (none : Option RawSI)).pair
    (((polyFun_const (none : Option RawWinSI)).pair
      ((hf.comp polyFun_some).pair (polyFun_const (none : Option RawDescSI))))))).comp
    polyFun_some

/-- Building a descent node. -/
theorem mnPolyFun_descOf {γ : Type} [Enc γ] {f : γ → RawDescSI} (hf : PolyFun f) :
    PolyFun (fun z : γ => (some (mnDesc (f z)) : Option MNode)) :=
  (((polyFun_const (none : Option RawSI)).pair
    (((polyFun_const (none : Option RawWinSI)).pair
      ((polyFun_const (none : Option RawWinSI)).pair (hf.comp polyFun_some)))))).comp
    polyFun_some

theorem mnDispTest_eq (i : RawWinSI) :
    mnDispTest i = !decide ((winOrbits (i.2.1, i.1)).length ≤ 1) := by
  by_cases h : 1 < (winOrbits (i.2.1, i.1)).length
  · rw [mnDispTest, decide_eq_true h,
      decide_eq_false (by omega : ¬ (winOrbits (i.2.1, i.1)).length ≤ 1)]
    rfl
  · rw [mnDispTest, decide_eq_false h,
      decide_eq_true (by omega : (winOrbits (i.2.1, i.1)).length ≤ 1)]
    rfl

theorem mnPolyFun_orbits : PolyFun (fun i : RawWinSI => winOrbits (i.2.1, i.1)) :=
  ((polyFun_snd.comp polyFun_fst).pair polyFun_fst).comp polyFun_winOrbits

theorem mnPolyFun_leafTest :
    PolyFun (fun i : RawWinSI => decide ((winOrbits (i.2.1, i.1)).length ≤ 1)) :=
  ((mnPolyFun_orbits.comp polyFun_length).pair (polyFun_const 1)).comp polyFun_le

theorem polyFun_mnDispTest : PolyFun mnDispTest :=
  (wftPolyFun_not mnPolyFun_leafTest).of_eq (fun i => (mnDispTest_eq i).symm)

theorem polyFun_mnLeafAns : PolyFun mnLeafAns := by
  have hlen : PolyFun (fun i : RawWinSI => decide (i.1.length ≤ 1)) :=
    ((polyFun_fst.comp polyFun_length).pair (polyFun_const 1)).comp polyFun_le
  refine (PolyFun.ite hlen polyFun_tStubAns (polyFun_const none)).of_eq (fun i => ?_)
  rw [mnLeafAns]
  by_cases h : i.1.length ≤ 1 <;> simp [h]

theorem polyFun_mnDispChild : PolyFun mnDispChild := by
  have htest : PolyFun (fun p : RawWinSI × ℕ × RawCoset => mnDispTest p.1) :=
    polyFun_fst.comp polyFun_mnDispTest
  have hzero : PolyFun (fun p : RawWinSI × ℕ × RawCoset => decide (p.2.1 = 0)) :=
    ((polyFun_snd.comp polyFun_fst).pair (polyFun_const 0)).comp polyFun_natEq
  have hchain : PolyFun (fun p : RawWinSI × ℕ × RawCoset =>
      (some (mnChain p.1) : Option MNode)) := mnPolyFun_chainOf polyFun_fst
  refine (PolyFun.ite htest (PolyFun.ite hzero hchain (polyFun_const none))
    (polyFun_const none)).of_eq (fun p => ?_)
  rw [mnDispChild]
  by_cases h1 : mnDispTest p.1 = true
  · by_cases h2 : p.2.1 = 0 <;> simp [h1, h2]
  · simp [h1]

theorem polyFun_mnDispFinish : PolyFun mnDispFinish := by
  have htest : PolyFun (fun p : RawWinSI × RawCoset => mnDispTest p.1) :=
    polyFun_fst.comp polyFun_mnDispTest
  refine (PolyFun.ite htest polyFun_snd (polyFun_fst.comp polyFun_mnLeafAns)).of_eq
    (fun p => ?_)
  rw [mnDispFinish]

theorem polyFun_mnChainChild : PolyFun mnChainChild := by
  have hleaf : PolyFun (fun p : RawWinSI × ℕ × RawCoset =>
      decide ((winOrbits (p.1.2.1, p.1.1)).length ≤ 1)) :=
    polyFun_fst.comp mnPolyFun_leafTest
  have hzero : PolyFun (fun p : RawWinSI × ℕ × RawCoset => decide (p.2.1 = 0)) :=
    ((polyFun_snd.comp polyFun_fst).pair (polyFun_const 0)).comp polyFun_natEq
  have hdisp : PolyFun (fun p : RawWinSI × ℕ × RawCoset =>
      (some (mnDisp p.1) : Option MNode)) := mnPolyFun_dispOf polyFun_fst
  have hsome2 : PolyFun (fun z : RawWinSI × (RawWinSI × ℕ × RawCoset) =>
      (some (mnChain z.1) : Option MNode)) := mnPolyFun_chainOf polyFun_fst
  have hmap : PolyFun (fun p : RawWinSI × ℕ × RawCoset => (winChild p).map mnChain) := by
    have hpair : PolyFun (fun p : RawWinSI × ℕ × RawCoset =>
        ((winChild p, p) : Option RawWinSI × (RawWinSI × ℕ × RawCoset))) :=
      polyFun_winChild.pair polyFun_id
    refine (hpair.comp (PolyFun.optionElim
      (g := fun _ : RawWinSI × ℕ × RawCoset => (none : Option MNode))
      (polyFun_const _) hsome2)).of_eq (fun p => ?_)
    cases hw : winChild p with
    | none => simp [hw]
    | some J => simp [hw]
  refine (PolyFun.ite hleaf (PolyFun.ite hzero hdisp (polyFun_const none)) hmap).of_eq
    (fun p => ?_)
  rw [mnChainChild]
  by_cases h1 : (winOrbits (p.1.2.1, p.1.1)).length ≤ 1
  · by_cases h2 : p.2.1 = 0 <;> simp [h1, h2]
  · simp [h1]

theorem polyFun_mnDescLeafChild : PolyFun mnDescLeafChild := by
  have hzero : PolyFun (fun p : RawDescSI × ℕ × RawCoset => decide (p.2.1 = 0)) :=
    ((polyFun_snd.comp polyFun_fst).pair (polyFun_const 0)).comp polyFun_natEq
  have hdisp : PolyFun (fun p : RawDescSI × ℕ × RawCoset =>
      (some (mnDisp p.1.1) : Option MNode)) :=
    mnPolyFun_dispOf (polyFun_fst.comp polyFun_fst)
  refine (PolyFun.ite hzero hdisp (polyFun_const none)).of_eq (fun p => ?_)
  rw [mnDescLeafChild]
  by_cases h : p.2.1 = 0 <;> simp [h]

theorem polyFun_mnDescChild : PolyFun mnDescChild := by
  have hsomeD : PolyFun (fun z : RawDescSI × (RawDescSI × ℕ × RawCoset) =>
      (some (mnDesc z.1) : Option MNode)) := mnPolyFun_descOf polyFun_fst
  have hmap : PolyFun (fun p : RawDescSI × ℕ × RawCoset => (descChild p).map mnDesc) := by
    have hpair : PolyFun (fun p : RawDescSI × ℕ × RawCoset =>
        ((descChild p, p) : Option RawDescSI × (RawDescSI × ℕ × RawCoset))) :=
      polyFun_descChild.pair polyFun_id
    refine (hpair.comp (PolyFun.optionElim
      (g := fun _ : RawDescSI × ℕ × RawCoset => (none : Option MNode))
      (polyFun_const _) hsomeD)).of_eq (fun p => ?_)
    cases hw : descChild p with
    | none => simp [hw]
    | some J => simp [hw]
  have hpair2 : PolyFun (fun p : RawDescSI × ℕ × RawCoset =>
      ((p.1.2, p) : Option (List ℕ × ℕ) × (RawDescSI × ℕ × RawCoset))) :=
    (polyFun_fst.comp polyFun_snd).pair polyFun_id
  refine (hpair2.comp (PolyFun.optionElim (g := mnDescLeafChild)
    polyFun_mnDescLeafChild (polyFun_snd.comp hmap))).of_eq (fun p => ?_)
  rw [mnDescChild]

theorem polyFun_mnDescCombine : PolyFun mnDescCombine := by
  have hpair : PolyFun (fun p : RawDescSI × ℕ × RawCoset × RawCoset =>
      ((p.1.2, p) : Option (List ℕ × ℕ) × (RawDescSI × ℕ × RawCoset × RawCoset))) :=
    (polyFun_fst.comp polyFun_snd).pair polyFun_id
  refine (hpair.comp (PolyFun.optionElim
    (g := fun p : RawDescSI × ℕ × RawCoset × RawCoset => p.2.2.2)
    (polyFun_snd.comp (polyFun_snd.comp polyFun_snd))
    (polyFun_snd.comp polyFun_descCombine))).of_eq (fun p => ?_)
  rw [mnDescCombine]

/-! ### The cost of each kind -/

/-- The cost data of the Chain Rule round with the abstract solver removed, reused from
`Workspace/Algo/A15Test.lean` for the size of the coset a node starts from. -/
theorem mnInit_le {i : RawWinSI} (hI : MWinWF n i) :
    Enc.size (some (i.2.1, i.2.2.1) : RawCoset) ≤ mnBound n :=
  le_trans ((tChainCost n).init_le i hI.1) (mnChainBound_le hI)

theorem mnWidth_le {i : RawWinSI} (hI : MWinWF n i) :
    (winOrbits (i.2.1, i.1)).length ≤ n := by
  have h1 : (winOrbits (i.2.1, i.1)).length ≤ i.1.length := length_winOrbits_le _ _
  have h2 : i.1.length ≤ n := length_le_of_nodup_lt hI.1.2.2.1 hI.1.2.2.2.1
  omega

theorem mnKindCost_disp (n : ℕ) : KindCost mnBound mnBound mnWidthBound (mnDispKind n) where
  polyFun_proj := polyFun_snd.comp polyFun_fst
  polyFun_projω := polyFun_some
  quasiFun_child := polyFun_mnDispChild.quasiFun
  quasiFun_init := (polyFun_const (none : RawCoset)).quasiFun
  quasiFun_combine := (polyFun_snd.comp (polyFun_snd.comp polyFun_snd)).quasiFun
  quasiFun_finish := polyFun_mnDispFinish.quasiFun
  u_projω_le := by
    intro s w h
    have hws : w = s := (Option.some.inj h).symm
    rw [hws]
    exact le_refl _
  init_le := by
    intro i hi
    have h1 : Enc.size (none : RawCoset) = 2 := size_none
    have h2 := sixtyfour_le_mnBound (mnGround ((mnDispKind n).e i))
    show Enc.size (none : RawCoset) ≤ mnBound (mnGround ((mnDispKind n).e i))
    omega
  combine_le := fun _ _ _ _ _ _ ha => ha
  finish_le := by
    intro i w hi hs
    have hI : MWinWF n i := mnWF_disp hi
    have hg : mnGround ((mnDispKind n).e i) = n := hI.1.1
    rw [hg] at hs ⊢
    show Enc.size (mnDispFinish (i, w)) ≤ mnBound n
    rw [mnDispFinish]
    by_cases h : mnDispTest i = true
    · rw [if_pos h]; exact hs
    · rw [if_neg h, mnLeafAns]
      have h1 : Enc.size (none : RawCoset) = 2 := size_none
      have h2 := sixtyfour_le_mnBound n
      have h3 := mnInit_le hI
      by_cases hlen : i.1.length ≤ 1
      · rw [if_pos hlen, tStubAns]
        by_cases ht : tStubTest i = true
        · rw [if_pos ht]; exact h3
        · rw [if_neg ht]; omega
      · rw [if_neg hlen]; omega
  width_le := by
    intro i hi
    have h1 : mnDispWidth i ≤ 1 := by
      rw [mnDispWidth]; by_cases h : mnDispTest i = true <;> simp [h]
    show mnDispWidth i ≤ mnWidthBound (mnGround ((mnDispKind n).e i))
    have h2 : mnWidthBound (mnGround ((mnDispKind n).e i))
        = mnGround ((mnDispKind n).e i) + 1 := rfl
    omega

theorem mnKindCost_chain (n : ℕ) : KindCost mnBound mnBound mnWidthBound (mnChainKind n) where
  polyFun_proj := polyFun_snd.comp (polyFun_snd.comp polyFun_fst)
  polyFun_projω := polyFun_some
  quasiFun_child := polyFun_mnChainChild.quasiFun
  quasiFun_init :=
    (((polyFun_snd.comp polyFun_fst).pair
      (polyFun_snd.comp (polyFun_snd.comp polyFun_fst))).comp polyFun_some).quasiFun
  quasiFun_combine := (polyFun_snd.comp (polyFun_snd.comp polyFun_snd)).quasiFun
  quasiFun_finish := polyFun_snd.quasiFun
  u_projω_le := by
    intro s w h
    have hws : w = s := (Option.some.inj h).symm
    rw [hws]
    exact le_refl _
  init_le := by
    intro i hi
    have hI : MWinWF n i := mnWF_chain hi
    have hg : mnGround ((mnChainKind n).e i) = n := hI.1.1
    rw [hg]
    show Enc.size (some (i.2.1, i.2.2.1) : RawCoset) ≤ mnBound n
    exact mnInit_le hI
  combine_le := fun _ _ _ _ _ _ ha => ha
  finish_le := fun _ _ _ hs => hs
  width_le := by
    intro i hi
    have hI : MWinWF n i := mnWF_chain hi
    have hg : mnGround ((mnChainKind n).e i) = n := hI.1.1
    have h1 := mnWidth_le hI
    show (winOrbits (i.2.1, i.1)).length + 1 ≤ mnWidthBound (mnGround ((mnChainKind n).e i))
    rw [hg]
    show (winOrbits (i.2.1, i.1)).length + 1 ≤ n + 1
    omega

theorem mnKindCost_desc (n : ℕ) : KindCost mnBound mnBound mnWidthBound (mnDescKind n) where
  polyFun_proj := polyFun_snd.comp (polyFun_snd.comp polyFun_snd)
  polyFun_projω := polyFun_some
  quasiFun_child := polyFun_mnDescChild.quasiFun
  quasiFun_init := (polyFun_const (none : RawCoset)).quasiFun
  quasiFun_combine := polyFun_mnDescCombine.quasiFun
  quasiFun_finish := polyFun_snd.quasiFun
  u_projω_le := by
    intro s w h
    have hws : w = s := (Option.some.inj h).symm
    rw [hws]
    exact le_refl _
  init_le := by
    intro I hi
    have h1 : Enc.size (none : RawCoset) = 2 := size_none
    have h2 := sixtyfour_le_mnBound (mnGround ((mnDescKind n).e I))
    show Enc.size (none : RawCoset) ≤ mnBound (mnGround ((mnDescKind n).e I))
    omega
  combine_le := by
    intro I j w a hi hs ha
    have hI : MDescWF n I := mnWF_desc hi
    have hg : mnGround ((mnDescKind n).e I) = n := hI.2.1.1.1
    rw [hg] at hs ha ⊢
    show Enc.size (mnDescCombine (I, j, w, a)) ≤ mnBound n
    rw [mnDescCombine]
    cases hq : I.2 with
    | none => simpa using ha
    | some q =>
        simp only [Option.elim]
        rw [descCombine]
        exact size_rawCosetJoin_le (n := n) hI.2.1.1.1 (le_mnStrsBound n)
          (chainBound_le_mnBound n) hs ha
  finish_le := fun _ _ _ hs => hs
  width_le := by
    intro I hi
    have hI : MDescWF n I := mnWF_desc hi
    have hg : mnGround ((mnDescKind n).e I) = n := hI.2.1.1.1
    show mnDescWidth I ≤ mnWidthBound (mnGround ((mnDescKind n).e I))
    rw [hg]
    show mnDescWidth I ≤ n + 1
    rw [mnDescWidth]
    cases hq : I.2 with
    | none => simp
    | some q =>
        simp only [Option.elim]
        have := hI.2.2 q.1 q.2 (by rw [hq])
        omega

/-! ### The cost of the master round -/

theorem polyBound_mnWidthBound : PolyBound mnWidthBound :=
  polyBound_id.add (polyBound_const 1)

theorem mono_mnWidthBound : Monotone mnWidthBound := by
  intro a b hab
  show a + 1 ≤ b + 1
  omega

/-- **The cost data of the master round.** -/
def mnCostQ (n : ℕ) : Round.CostQ (mnRound n) :=
  famCostQ (WF := MWF n) (ground := mnGround) (measure := mnMeasure)
    none none (mnKinds n) mnBound mnBound mnWidthBound
    polyBound_mnBound mono_mnBound polyBound_mnBound.quasiPoly mono_mnBound
    polyBound_mnWidthBound.quasiPoly mnGround_le mnSize_le mnBot_le mnBot_le
    (by
      intro k hk
      have hk' : k = mnDispKind n ∨ k = mnChainKind n ∨ k = mnDescKind n := by
        simpa [mnKinds] using hk
      rcases hk' with rfl | rfl | rfl
      · exact mnKindCost_disp n
      · exact mnKindCost_chain n
      · exact mnKindCost_desc n)

/-! ## The master test

`Algo.Round.RunCostQS` asks for a **sound** test: what it accepts is well formed.  The test
below accepts exactly the dispatch nodes whose payload passes `Algo.wftWinWF` (all of
`Algo.WinWF`), the letter bound, and the invariant, and it rejects every other node.  That is
what the master round needs at its root, and it is honest: a Chain Rule node or a descent
node is not a root of a run.

`Algo.wftRootCheck` (`Workspace/Algo/WFTestsSI.lean`) is the test of `Algo.NormSIWF` on a
plain `Algo.RawSI`.  It belongs at the **entry** slot, which has no kind yet; the test of the
dispatch slot is its counterpart for a window instance. -/

/-- "The list is at most as long as the parameter." -/
def mnLenLe (z : ℕ × List ℕ) : Bool := decide (z.2.length ≤ z.1)

theorem polyFun_mnLenLe : PolyFun mnLenLe :=
  ((polyFun_snd.comp polyFun_length).pair polyFun_fst).comp polyFun_le

/-- The test of the invariant: every orbit inside the window has at most one point. -/
def mnTrivTest (i : RawWinSI) : Bool := wftAll mnLenLe (1, winOrbits (i.2.1, i.1))

theorem mnTrivTest_eq_true_iff (i : RawWinSI) :
    mnTrivTest i = true ↔ ∀ o ∈ winOrbits (i.2.1, i.1), o.length ≤ 1 := by
  rw [mnTrivTest, wftAll_eq_true_iff]
  constructor
  · intro h o ho
    have := h o ho
    rw [mnLenLe] at this
    exact of_decide_eq_true this
  · intro h o ho
    rw [mnLenLe]
    exact decide_eq_true (h o ho)

theorem polyFun_mnTrivTest : PolyFun mnTrivTest :=
  ((polyFun_const 1).pair mnPolyFun_orbits).comp (wftPolyFun_all polyFun_mnLenLe)

/-- The test of `Algo.A15.MWinWF`. -/
def mnWinCheck (n : ℕ) (i : RawWinSI) : Bool :=
  (wftWinWF (n, i) && mnTrivTest i) &&
    (wftAllLt (2 * n, i.2.2.2.1) && wftAllLt (2 * n, i.2.2.2.2))

theorem mnWinCheck_sound (n : ℕ) (i : RawWinSI) (h : mnWinCheck n i = true) : MWinWF n i := by
  rw [mnWinCheck, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨hw, ht⟩, hx, hy⟩ := h
  have hW : WinWF n i := (wftWinWF_eq_true_iff n i).1 hw
  exact ⟨hW, ⟨hW.1, (wftAllLt_eq_true_iff _ _).1 hx⟩,
    ⟨hW.2.1, (wftAllLt_eq_true_iff _ _).1 hy⟩, (mnTrivTest_eq_true_iff i).1 ht⟩

theorem polyFun_mnWinCheck (n : ℕ) : PolyFun (mnWinCheck n) := by
  have hw : PolyFun (fun i : RawWinSI => wftWinWF (n, i)) :=
    ((polyFun_const n).pair polyFun_id).comp wftPolyFun_winWF
  have hx : PolyFun (fun i : RawWinSI => wftAllLt (2 * n, i.2.2.2.1)) :=
    ((polyFun_const (2 * n)).pair
      (polyFun_snd.comp (polyFun_snd.comp (polyFun_snd.comp polyFun_fst)))).comp
      wftPolyFun_allLt
  have hy : PolyFun (fun i : RawWinSI => wftAllLt (2 * n, i.2.2.2.2)) :=
    ((polyFun_const (2 * n)).pair
      (polyFun_snd.comp (polyFun_snd.comp (polyFun_snd.comp polyFun_snd)))).comp
      wftPolyFun_allLt
  exact (wftPolyFun_and (wftPolyFun_and hw polyFun_mnTrivTest) (wftPolyFun_and hx hy)).of_eq
    (fun i => rfl)

/-- "The slot is empty." -/
def mnIsNone {α : Type} (o : Option α) : Bool := o.elim true (fun _ => false)

theorem polyFun_mnIsNone {α : Type} [Enc α] : PolyFun (mnIsNone (α := α)) :=
  ((polyFun_id.pair polyFun_id).comp (PolyFun.optionElim
    (g := fun _ : Option α => true) (polyFun_const true) (polyFun_const false))).of_eq
    (fun o => by cases o <;> rfl)

/-- **The master test**: the node is a dispatch node and its payload is well formed. -/
def mnWfCheck (n : ℕ) (x : MNode) : Bool :=
  (x.2.1.elim false (fun i => mnWinCheck n i) && mnIsNone x.1) &&
    (mnIsNone x.2.2.1 && mnIsNone x.2.2.2)

theorem mnWfCheck_sound (n : ℕ) (x : MNode) (h : mnWfCheck n x = true) : MWF n x := by
  rw [mnWfCheck, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨h2, h1⟩, h3, h4⟩ := h
  obtain ⟨o1, o2, o3, o4⟩ := x
  have e1 : o1 = none := by cases o1 with
    | none => rfl
    | some a => exact absurd h1 (by simp [mnIsNone])
  have e3 : o3 = none := by cases o3 with
    | none => rfl
    | some a => exact absurd h3 (by simp [mnIsNone])
  have e4 : o4 = none := by cases o4 with
    | none => rfl
    | some a => exact absurd h4 (by simp [mnIsNone])
  subst e1; subst e3; subst e4
  cases o2 with
  | none => exact absurd h2 (by simp)
  | some i =>
      have : mnWinCheck n i = true := h2
      exact Or.inl ⟨i, rfl, mnWinCheck_sound n i this⟩

theorem polyFun_mnWfCheck (n : ℕ) : PolyFun (mnWfCheck n) := by
  have hdisp : PolyFun (fun x : MNode => x.2.1.elim false (fun i => mnWinCheck n i)) := by
    have hpair : PolyFun (fun x : MNode => ((x.2.1, x) : Option RawWinSI × MNode)) :=
      (polyFun_snd.comp polyFun_fst).pair polyFun_id
    exact (hpair.comp (PolyFun.optionElim (g := fun _ : MNode => false)
      (polyFun_const false) (polyFun_fst.comp (polyFun_mnWinCheck n)))).of_eq (fun x => rfl)
  have h1 : PolyFun (fun x : MNode => mnIsNone x.1) := polyFun_fst.comp polyFun_mnIsNone
  have h3 : PolyFun (fun x : MNode => mnIsNone x.2.2.1) :=
    (polyFun_snd.comp (polyFun_snd.comp polyFun_fst)).comp polyFun_mnIsNone
  have h4 : PolyFun (fun x : MNode => mnIsNone x.2.2.2) :=
    (polyFun_snd.comp (polyFun_snd.comp polyFun_snd)).comp polyFun_mnIsNone
  exact (wftPolyFun_and (wftPolyFun_and hdisp h1) (wftPolyFun_and h3 h4)).of_eq (fun x => rfl)

/-- **The domain size is a routine.**  This is the clause that rules out the encoding size of
the strings as the master `ground`: `Algo.RAM.Enc.size` is not a routine
(`Workspace/Algo/EvaluatorRAM.lean`, the remark before `Algo.Round.testRunCost`). -/
theorem polyFun_mnGround : PolyFun mnGround := by
  have hlenW : PolyFun (fun z : RawWinSI × MNode => z.1.2.2.2.1.length) :=
    ((polyFun_fst.comp (polyFun_snd.comp (polyFun_snd.comp (polyFun_snd.comp polyFun_fst))))).comp
      polyFun_length
  have hlenD : PolyFun (fun z : RawDescSI × MNode => z.1.1.2.2.2.1.length) :=
    ((polyFun_fst.comp (polyFun_fst.comp
      (polyFun_snd.comp (polyFun_snd.comp (polyFun_snd.comp polyFun_fst)))))).comp polyFun_length
  have h3 : PolyFun (fun x : MNode =>
      x.2.2.2.elim 0 (fun I => I.1.2.2.2.1.length)) := by
    have hpair : PolyFun (fun x : MNode => ((x.2.2.2, x) : Option RawDescSI × MNode)) :=
      (polyFun_snd.comp (polyFun_snd.comp polyFun_snd)).pair polyFun_id
    exact (hpair.comp (PolyFun.optionElim (g := fun _ : MNode => 0)
      (polyFun_const 0) hlenD)).of_eq (fun x => by cases x.2.2.2 <;> rfl)
  have h2 : PolyFun (fun x : MNode =>
      x.2.2.1.elim (x.2.2.2.elim 0 (fun I => I.1.2.2.2.1.length))
        (fun i => i.2.2.2.1.length)) := by
    have hpair : PolyFun (fun x : MNode => ((x.2.2.1, x) : Option RawWinSI × MNode)) :=
      (polyFun_snd.comp (polyFun_snd.comp polyFun_fst)).pair polyFun_id
    exact (hpair.comp (PolyFun.optionElim (g := fun x : MNode =>
      x.2.2.2.elim 0 (fun I => I.1.2.2.2.1.length)) h3 hlenW)).of_eq
      (fun x => by cases x.2.2.1 <;> rfl)
  have h1 : PolyFun (fun x : MNode =>
      x.2.1.elim (x.2.2.1.elim (x.2.2.2.elim 0 (fun I => I.1.2.2.2.1.length))
        (fun i => i.2.2.2.1.length)) (fun i => i.2.2.2.1.length)) := by
    have hpair : PolyFun (fun x : MNode => ((x.2.1, x) : Option RawWinSI × MNode)) :=
      (polyFun_snd.comp polyFun_fst).pair polyFun_id
    exact (hpair.comp (PolyFun.optionElim (g := fun x : MNode =>
      x.2.2.1.elim (x.2.2.2.elim 0 (fun I => I.1.2.2.2.1.length))
        (fun i => i.2.2.2.1.length)) h2 hlenW)).of_eq (fun x => by cases x.2.1 <;> rfl)
  refine h1.of_eq (fun x => ?_)
  rw [mnGround]
  cases x.2.1 with
  | some i => rfl
  | none =>
      cases x.2.2.1 with
      | some i => rfl
      | none => cases x.2.2.2 <;> rfl

/-! ### The measure is polynomially bounded -/

theorem polyBound_mnMeasureBound : PolyBound mnMeasureBound :=
  ((polyBound_const 5).mul polyBound_id).add (polyBound_const 4)

theorem mono_mnMeasureBound : Monotone mnMeasureBound := by
  intro a b hab
  show 5 * a + 4 ≤ 5 * b + 4
  omega

theorem mnMeasure_le (x : MNode) (hx : MWF n x) :
    mnMeasure x ≤ mnMeasureBound (mnGround x) := by
  have hloc := mnLoc_lt x
  have hrank : mnRank x ≤ mnGround x := by
    rcases hx with ⟨i, rfl, hI⟩ | ⟨i, rfl, hI⟩ | ⟨I, rfl, hI⟩
    · show i.1.length ≤ i.2.2.2.1.length
      rw [hI.1.1]
      exact length_le_of_nodup_lt hI.1.2.2.1 hI.1.2.2.2.1
    · show i.1.length ≤ i.2.2.2.1.length
      rw [hI.1.1]
      exact length_le_of_nodup_lt hI.1.2.2.1 hI.1.2.2.2.1
    · show I.1.1.length ≤ I.1.2.2.2.1.length
      rw [hI.2.1.1.1]
      exact length_le_of_nodup_lt hI.2.1.1.2.2.1 hI.2.1.1.2.2.2.1
  have hm : mnMeasure x = mnRank x * 5 + mnLoc x := rfl
  have hb : mnMeasureBound (mnGround x) = 5 * mnGround x + 4 := rfl
  omega

/-- **The cost data of the master round, with a sound test.**  This is what
`Algo.Round.runQS_eq_answer_align` (`Workspace/Algo/EvaluatorQSAlign.lean`) consumes. -/
def mnRunCostQS (n : ℕ) : Round.RunCostQS (mnRound n) :=
  famRunCostQS (WF := MWF n) (ground := mnGround) (measure := mnMeasure)
    none none (mnKinds n) mnBound mnBound mnWidthBound
    polyBound_mnBound mono_mnBound polyBound_mnBound.quasiPoly mono_mnBound
    polyBound_mnWidthBound.quasiPoly mnGround_le mnSize_le mnBot_le mnBot_le
    (by
      intro k hk
      have hk' : k = mnDispKind n ∨ k = mnChainKind n ∨ k = mnDescKind n := by
        simpa [mnKinds] using hk
      rcases hk' with rfl | rfl | rfl
      · exact mnKindCost_disp n
      · exact mnKindCost_chain n
      · exact mnKindCost_desc n)
    polyFun_mnGround (mnWfCheck n) (polyFun_mnWfCheck n) (mnWfCheck_sound n)
    mnMeasureBound polyBound_mnMeasureBound mono_mnMeasureBound
    (fun x hx => mnMeasure_le x hx)

/-! ## The family is not vacuous

A trivial group on an empty window is a well-formed node of each of the three kinds.  So
`Algo.A15.MWF`, `Algo.A15.MWinWF` and `Algo.A15.MDescWF` are satisfiable, and the three
`Algo.A15.Kind` records and their `Algo.A15.KindCost` proofs are statements about nodes that
exist.  The recursion itself is not trivial: a dispatch node with several one-point orbits
inside its window grows a Chain Rule node, which grows one child per orbit, each of which is
a dispatch node again. -/

/-- The empty instance on the empty domain. -/
def mnTrivial : RawWinSI := ([], [], [], [], [])

theorem mnWinWF_trivial : MWinWF 0 mnTrivial := by
  refine ⟨⟨rfl, rfl, List.nodup_nil, by simp [mnTrivial], ?_, by simp [mnTrivial],
    ⟨rfl, by simp [mnTrivial], List.nodup_nil⟩, ?_⟩, ⟨rfl, by simp [mnTrivial]⟩,
    ⟨rfl, by simp [mnTrivial]⟩, ?_⟩
  · intro g hg; exact absurd hg (by simp [mnTrivial])
  · rw [rawIsInvariant_eq_true_iff']
    intro j hj
    exact absurd hj (by simp [mnTrivial])
  · intro o ho
    exact absurd ho (by simp [mnTrivial, winOrbits])

theorem mnWF_trivial_disp : MWF 0 (mnDisp mnTrivial) := Or.inl ⟨mnTrivial, rfl, mnWinWF_trivial⟩

theorem mnWF_trivial_chain : MWF 0 (mnChain mnTrivial) :=
  Or.inr (Or.inl ⟨mnTrivial, rfl, mnWinWF_trivial⟩)

theorem mnWF_trivial_desc : MWF 0 (mnDesc (mnTrivial, none)) :=
  Or.inr (Or.inr ⟨(mnTrivial, none), rfl,
    ⟨⟨mnWinWF_trivial.1, fun d idx h => absurd h (by simp)⟩, mnWinWF_trivial,
      fun d idx h => absurd h (by simp)⟩⟩)

end

end Algo.A15

#print axioms Algo.A15.implements_mnRound
#print axioms Algo.A15.run_mnRed
#print axioms Algo.A15.mnRound_value
#print axioms Algo.A15.mnRound_evaluate
#print axioms Algo.A15.mnCostQ
#print axioms Algo.A15.mnRunCostQS
#print axioms Algo.A15.mnWF_trivial_disp
