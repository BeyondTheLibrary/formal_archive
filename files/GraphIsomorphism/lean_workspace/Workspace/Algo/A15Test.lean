/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: the kind interface, tested on two real kinds.
-/
import Workspace.Algo.A15KindsMatch
import Workspace.Algo.Luks

/-!
# Two kinds, end to end

The interface of `Workspace/Algo/A15Kinds.lean` is worth nothing if no real round fits it.
This file puts two kinds in one master round and runs the whole chain on them: the four laws
of `Algo.Round`, `Algo.Implements` against a mathematical reduction, the correctness of the
value, and `Algo.Round.CostQ`.

## The two kinds

* **The Chain Rule kind.**  `Algo.chainRound` (`Workspace/Algo/Luks.lean`), Prop. 11.1.7 with
  Eq. (64): fold over the orbits of the group inside the window, each child carrying the
  coset the fold has reached.  In `Algo.chainRound` the leaf — a window the group is
  transitive on — is answered by the abstract parameter `solve`.  Here `solve` disappears, as
  item 1 of the note "A15 session 0" says it must: the leaf grows **one child**, of the second
  kind, and returns that child's answer.  That is `Algo.loopMatch_oneCall`.
* **The stub kind.**  A leaf that answers its instance outright.  It is honest: its
  well-formedness asks the window to have at most one point.  A window of at most one point
  that is invariant under the group is fixed pointwise by it (`Algo.A15.tFix`), so the answer
  is the whole candidate set when the strings agree at that point and empty otherwise.  This
  is `Algo.A15.tStubAns`, and `Algo.A15.decCoset_tStubAns` proves it is `Iso^Δ_K(x,y)`.

## What closes the recursion

The two kinds fit together because of one invariant, carried by
`Algo.A15.TChainWF`: **every orbit of the node's group inside its window has at most one
point**.  A child of the Chain Rule kind has an orbit for a window, so at most one point, and
`Algo.winChild` hands it a group under which that window is invariant, so the invariant holds
again.  And a node with at most one orbit, all orbits being single points, has a window of at
most one point, which is what the stub kind solves.  So the toy family is the Chain Rule run
on a group whose orbits inside the window are singletons — a genuine recursion, with children
of both kinds, that ends in a case the stub really answers.

## What is checked

* `Algo.A15.tRound` — the master round, from `Algo.A15.famRound`;
* `Algo.A15.implements_tRound` — it implements `Algo.A15.tRed`;
* `Algo.A15.tRound_value` — hence its value is `Iso^Δ_K(x,y)`;
* `Algo.A15.tCostQ` — its `Algo.Round.CostQ`;
* `Algo.A15.tRound_evaluate` — hence the machine of `Workspace/Algo/Evaluator.lean` returns
  a raw coset decoding to the answer.

No axiom, no `sorry`.
-/

namespace Algo.A15

open RAM Babai

noncomputable section

variable {n : ℕ}

/-! ## The master node and state -/

/-- The master node of the toy family: the Chain Rule slot and the stub slot. -/
abbrev TNode := Option RawWinSI × Option RawWinSI

/-- The master state: the coset the fold has reached.  Both kinds use it. -/
abbrev TState := RawCoset

/-- A Chain Rule node. -/
def tChain (i : RawWinSI) : TNode := (some i, none)

/-- A stub node. -/
def tStub (i : RawWinSI) : TNode := (none, some i)

/-- The window of a master node. -/
def tWin (x : TNode) : List ℕ :=
  match x.1 with
  | some i => i.1
  | none => match x.2 with
      | some i => i.1
      | none => []

/-- The master domain size: the size of the pair of strings, which every child copies
unchanged.  A node no kind claims gets `0`, so that `Algo.Round.CostQ.ground_le` holds on
junk as well. -/
def tGround (x : TNode) : ℕ :=
  match x.1 with
  | some i => Enc.size i.2.2.2
  | none => match x.2 with
      | some i => Enc.size i.2.2.2
      | none => 0

/-- The first component of the measure of item 7: here the window length, which is what the
Chain Rule shrinks. -/
def tRank (x : TNode) : ℕ := (tWin x).length

/-- The local measure of item 7: a Chain Rule node is above the stub node it calls. -/
def tLoc (x : TNode) : ℕ := match x.1 with | some _ => 1 | none => 0

/-- The master measure, by the recipe of item 7 with `K = 2`. -/
def tMeasure (x : TNode) : ℕ := measureOfRank tRank (fun _ => 2) tLoc tGround x

theorem tLoc_lt (x : TNode) : tLoc x < 2 := by
  rcases hx : x.1 with _ | i <;> simp [tLoc, hx]

/-! ## Well-formedness -/

/-- A stub node is well formed when its window has at most one point. -/
def TStubWF (n : ℕ) (i : RawWinSI) : Prop := WinWF n i ∧ i.1.length ≤ 1

/-- A Chain Rule node is well formed when every orbit of its group inside its window has at
most one point.  This is the invariant that closes the recursion. -/
def TChainWF (n : ℕ) (i : RawWinSI) : Prop :=
  WinWF n i ∧ ∀ o ∈ winOrbits (i.2.1, i.1), o.length ≤ 1

/-- The master well-formedness. -/
def TWF (n : ℕ) (x : TNode) : Prop :=
  (∃ i, x = tChain i ∧ TChainWF n i) ∨ (∃ i, x = tStub i ∧ TStubWF n i)

theorem tChainWF_of_TWF {i : RawWinSI} (h : TWF n (tChain i)) : TChainWF n i := by
  rcases h with ⟨i', he, hw⟩ | ⟨i', he, -⟩
  · have hii : i' = i := by simpa [tChain] using he.symm
    rw [← hii]; exact hw
  · exact absurd he.symm (by simp [tChain, tStub])

theorem tStubWF_of_TWF {i : RawWinSI} (h : TWF n (tStub i)) : TStubWF n i := by
  rcases h with ⟨i', he, -⟩ | ⟨i', he, hw⟩
  · exact absurd he.symm (by simp [tChain, tStub])
  · have hii : i' = i := by simpa [tStub] using he.symm
    rw [← hii]; exact hw

/-! ## Small list facts -/

theorem eq_of_mem_of_length_le_one {l : List ℕ} (h : l.length ≤ 1) {a b : ℕ}
    (ha : a ∈ l) (hb : b ∈ l) : a = b := by
  match l with
  | [] => exact absurd ha (by simp)
  | [c] =>
      have h1 : a = c := by simpa using ha
      have h2 : b = c := by simpa using hb
      rw [h1, h2]
  | a' :: b' :: t => exact absurd h (by simp)

theorem length_le_one_of_subset {l m : List ℕ} (hnd : l.Nodup) (hsub : ∀ a ∈ l, a ∈ m)
    (hm : m.length ≤ 1) : l.length ≤ 1 := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨a, b, t, hl⟩ : ∃ a b t, l = a :: b :: t := by
    match l with
    | [] => exact absurd hcon (by simp)
    | [c] => exact absurd hcon (by simp)
    | a :: b :: t => exact ⟨a, b, t, rfl⟩
  have hab : a ≠ b := by
    rw [hl] at hnd
    have hna : a ∉ b :: t := (List.nodup_cons.1 hnd).1
    intro hEq
    exact hna (by rw [hEq]; simp)
  exact hab (eq_of_mem_of_length_le_one hm (hsub a (by rw [hl]; simp))
    (hsub b (by rw [hl]; simp)))

/-! ## The stub answers its instance

A window of at most one point, invariant under the group, is fixed pointwise by the group.
So the window condition of Eq. (58) does not depend on which element of the candidate set is
tested, and the answer is the candidate set or the empty set. -/

/-- **A group is trivial on a window of at most one point.** -/
theorem tFix {i : RawWinSI} (hI : TStubWF n i) {g : Equiv.Perm (Fin n)}
    (hg : g ∈ decGroup n i.2.1) {v : Fin n} (hv : v ∈ winSet n i.1) : g v = v := by
  obtain ⟨⟨hx, hy, hnd, hlt, hgs, hgl, hσ, hinv⟩, hlen⟩ := hI
  have hIinv : Babai.IsInvariant (decGroup n i.2.1) (winSet n i.1) :=
    (rawIsInvariant_eq_true_iff hgs hlt).1 hinv
  have hmem : g v ∈ winSet n i.1 :=
    ((Babai.isInvariant_iff_mem _ _).1 hIinv g hg v).1 hv
  exact Fin.ext (eq_of_mem_of_length_le_one hlen hmem hv)

/-- The test the stub performs: the two strings agree at the one point of the window, if the
window has a point at all.  The window has at most one point on a well-formed instance, so
looking at the head of the list is looking at the whole window. -/
def tStubTest (i : RawWinSI) : Bool :=
  match i.1 with
  | [] => true
  | u :: _ => decide (rawGet (i.2.2.2.1, u) = rawGet (i.2.2.2.2, rawGet (i.2.2.1, u)))

/-- The raw answer of the stub: the candidate set when the two strings agree at the window,
and the empty answer otherwise. -/
def tStubAns (i : RawWinSI) : RawCoset :=
  if tStubTest i then some (i.2.1, i.2.2.1) else none

/-- **The stub is correct.**  Paper: Eq. (58), on a window of at most one point. -/
theorem decCoset_tStubAns {i : RawWinSI} (hI : TStubWF n i) :
    decCoset n (tStubAns i) = (decWinSI n i).answer := by
  obtain ⟨hWF, hlen⟩ := hI
  obtain ⟨hx, hy, hnd, hlt, hgs, hgl, hσ, hinv⟩ := hWF
  set K := decCoset n (some (i.2.1, i.2.2.1)) with hK
  have hans : (decWinSI n i).answer
      = {τ ∈ K | ∀ v ∈ winSet n i.1,
          decStrN n i.2.2.2.1 v = decStrN n i.2.2.2.2 (τ v)} := rfl
  -- the raw test and the typed condition agree, for every candidate
  have hpt : ∀ τ ∈ K, ∀ u ∈ i.1, ∀ hun : u < n,
      (decStrN n i.2.2.2.1 ⟨u, hun⟩ = decStrN n i.2.2.2.2 (τ ⟨u, hun⟩))
        ↔ rawGet (i.2.2.2.1, u) = rawGet (i.2.2.2.2, rawGet (i.2.2.1, u)) := by
    intro τ hτ u hu hun
    obtain ⟨g, hg, rfl⟩ : ∃ g ∈ decGroup n i.2.1, τ = decPerm n i.2.2.1 * g := hτ
    have hv : (⟨u, hun⟩ : Fin n) ∈ winSet n i.1 := hu
    have hgv : g ⟨u, hun⟩ = ⟨u, hun⟩ :=
      tFix ⟨⟨hx, hy, hnd, hlt, hgs, hgl, hσ, hinv⟩, hlen⟩ hg hv
    have h2 : (decPerm n i.2.2.1 * g) ⟨u, hun⟩ = decPerm n i.2.2.1 ⟨u, hun⟩ := by
      show decPerm n i.2.2.1 (g ⟨u, hun⟩) = _
      rw [hgv]
    have h3 : (decPerm n i.2.2.1 ⟨u, hun⟩ : ℕ) = rawGet (i.2.2.1, u) := by
      show (decPerm n i.2.2.1 ⟨u, hun⟩ : ℕ) = i.2.2.1.getD u 0
      rw [decPerm_val_of_wf hσ ⟨u, hun⟩,
        List.getD_eq_getElem _ _ (by rw [hσ.length]; exact hun)]
    rw [h2]
    show i.2.2.2.1.getD u 0 = i.2.2.2.2.getD (decPerm n i.2.2.1 ⟨u, hun⟩ : ℕ) 0 ↔ _
    rw [h3]
    exact Iff.rfl
  have hcond : ∀ τ ∈ K,
      (∀ v ∈ winSet n i.1, decStrN n i.2.2.2.1 v = decStrN n i.2.2.2.2 (τ v))
        ↔ tStubTest i = true := by
    intro τ hτ
    constructor
    · intro h
      show (match i.1 with
        | [] => true
        | u :: _ =>
          decide (rawGet (i.2.2.2.1, u) = rawGet (i.2.2.2.2, rawGet (i.2.2.1, u)))) = true
      cases hw : i.1 with
      | nil => rfl
      | cons u t =>
          have hu : u ∈ i.1 := by rw [hw]; simp
          have hun : u < n := hlt u hu
          have := (hpt τ hτ u hu hun).1 (h ⟨u, hun⟩ hu)
          simpa using this
    · intro h v hv
      have hvm : (v : ℕ) ∈ i.1 := hv
      have hvn : (v : ℕ) < n := hlt (v : ℕ) hvm
      have hfin : (⟨(v : ℕ), hvn⟩ : Fin n) = v := Fin.ext rfl
      refine (hfin ▸ (hpt τ hτ (v : ℕ) hvm hvn)).2 ?_
      cases hw : i.1 with
      | nil => rw [hw] at hvm; exact absurd hvm (by simp)
      | cons u t =>
          have hu : u ∈ i.1 := by rw [hw]; simp
          have heq : (v : ℕ) = u := eq_of_mem_of_length_le_one hlen hvm hu
          have h' : (match i.1 with
            | [] => true
            | u :: _ =>
              decide (rawGet (i.2.2.2.1, u)
                = rawGet (i.2.2.2.2, rawGet (i.2.2.1, u)))) = true := h
          rw [hw] at h'
          rw [heq]
          simpa using h'
  by_cases hall : tStubTest i = true
  · rw [tStubAns, if_pos hall, hans]
    ext τ
    constructor
    · intro hτ; exact ⟨hτ, (hcond τ hτ).2 hall⟩
    · intro hτ; exact hτ.1
  · rw [tStubAns, if_neg hall, hans]
    ext τ
    constructor
    · intro hτ; exact absurd hτ (by simp [decCoset])
    · intro hτ; exact absurd ((hcond τ hτ.1).1 hτ.2) hall

/-! ## The stub kind -/

/-- The stub kind: no children, the answer of `Algo.A15.tStubAns`. -/
def stubKind (n : ℕ) : Kind TNode TState RawCoset (TWF n) tGround tMeasure where
  ι := RawWinSI
  ω := RawCoset
  encι := inferInstance
  encω := inferInstance
  e := tStub
  proj := fun x => x.2
  u := id
  projω := some
  proj_e := fun _ => rfl
  projω_u := fun _ => rfl
  eq_e_of_proj := by
    rintro x i (⟨i', rfl, -⟩ | ⟨i', rfl, -⟩) h
    · exact absurd h (by simp [tChain])
    · have : i' = i := by simpa [tStub] using h
      rw [this]
  width := fun _ => 0
  child := fun _ => none
  init := fun _ => none
  combine := fun p => p.2.2.1
  finish := fun p => tStubAns p.1
  child_eq_none := fun _ _ _ _ => rfl
  child_wf := fun _ _ _ _ _ h => by simp at h
  child_measure := fun _ _ _ _ _ h => by simp at h
  child_ground := fun _ _ _ _ _ h => by simp at h

/-! ## The Chain Rule kind -/

/-- The `j`-th child of a Chain Rule node.  Away from the leaf it is `Algo.winChild`, with
the child made a master node; at the leaf it is one child of the stub kind, the instance
`Algo.chainRound` would have handed to `solve`. -/
def tChainChild (p : RawWinSI × ℕ × RawCoset) : Option TNode :=
  if (winOrbits (p.1.2.1, p.1.1)).length ≤ 1 then
    (if p.2.1 = 0 then some (tStub p.1) else none)
  else (winChild p).map tChain

theorem tWin_tChain (i : RawWinSI) : tWin (tChain i) = i.1 := rfl
theorem tWin_tStub (i : RawWinSI) : tWin (tStub i) = i.1 := rfl
theorem tGround_tChain (i : RawWinSI) : tGround (tChain i) = Enc.size i.2.2.2 := rfl
theorem tGround_tStub (i : RawWinSI) : tGround (tStub i) = Enc.size i.2.2.2 := rfl

theorem tMeasure_tChain (i : RawWinSI) :
    tMeasure (tChain i) = i.1.length * 2 + 1 := rfl

theorem tMeasure_tStub (i : RawWinSI) : tMeasure (tStub i) = i.1.length * 2 := rfl

/-- **The window of a leaf has at most one point**, which is what the stub kind solves. -/
theorem length_le_one_of_leaf {i : RawWinSI} (hI : TChainWF n i)
    (h1 : (winOrbits (i.2.1, i.1)).length ≤ 1) : i.1.length ≤ 1 := by
  obtain ⟨⟨hx, hy, hnd, hlt, hgs, hgl, hσ, hinv⟩, horb⟩ := hI
  have hsub : ∀ a ∈ i.1, a ∈ (winOrbits (i.2.1, i.1)).flatten :=
    fun a ha => winOrbits_cover hgs hlt ha
  have hflat : (winOrbits (i.2.1, i.1)).flatten.length ≤ 1 := by
    match hw : winOrbits (i.2.1, i.1) with
    | [] => simp
    | [o] =>
        have ho : o ∈ winOrbits (i.2.1, i.1) := by rw [hw]; simp
        have := horb o ho
        simpa using this
    | o :: o' :: t => rw [hw] at h1; simp at h1
  exact length_le_one_of_subset hnd hsub hflat

/-- **The invariant is preserved**: a child of a Chain Rule node has singleton orbits again,
because its window is one orbit of its parent and the guard of `Algo.winChild` makes that
window invariant under the child's group. -/
theorem tChainWF_child {i : RawWinSI} (hI : TChainWF n i) {j : ℕ} {s : RawCoset}
    {J : RawWinSI} (hc : winChild (i, j, s) = some J) : TChainWF n J := by
  obtain ⟨hWF, horb⟩ := hI
  have hJwf : WinWF n J := (chainRound n (fun _ => none)).child_wf i j s J hWF hc
  refine ⟨hJwf, ?_⟩
  obtain ⟨g, τ, -, h1, h2, h3, rfl⟩ := winChild_eq_some (p := (i, j, s)) hc
  obtain ⟨hx, hy, hnd, hlt, hgs, hgl, hσ, hinv⟩ := hWF
  have hjl : j < (winOrbits (i.2.1, i.1)).length := winChild_index_lt (p := (i, j, s)) hc
  have hmem : (winOrbits (i.2.1, i.1)).getD j [] ∈ winOrbits (i.2.1, i.1) := by
    rw [List.getD_eq_getElem _ _ hjl]; exact List.getElem_mem hjl
  have hlen1 : ((winOrbits (i.2.1, i.1)).getD j []).length ≤ 1 := horb _ hmem
  obtain ⟨hJx, hJy, hJnd, hJlt, hJgs, hJgl, hJσ, hJinv⟩ := hJwf
  intro o ho
  exact length_le_one_of_subset (winOrbits_nodup ho)
    (fun a ha => winOrbits_subset hJgs hJlt hJinv ho a ha) hlen1

/-- The Chain Rule kind. -/
def chainKind (n : ℕ) : Kind TNode TState RawCoset (TWF n) tGround tMeasure where
  ι := RawWinSI
  ω := RawCoset
  encι := inferInstance
  encω := inferInstance
  e := tChain
  proj := fun x => x.1
  u := id
  projω := some
  proj_e := fun _ => rfl
  projω_u := fun _ => rfl
  eq_e_of_proj := by
    rintro x i (⟨i', rfl, -⟩ | ⟨i', rfl, -⟩) h
    · have : i' = i := by simpa [tChain] using h
      rw [this]
    · exact absurd h (by simp [tStub])
  width := fun i => (winOrbits (i.2.1, i.1)).length + 1
  child := tChainChild
  init := fun i => some (i.2.1, i.2.2.1)
  combine := fun p => p.2.2.2
  finish := fun p => p.2
  child_eq_none := by
    intro i j w hj
    rw [tChainChild]
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
    have hI : TChainWF n i := by
      rcases hi with ⟨i', h, hw⟩ | ⟨i', h, -⟩
      · have : i' = i := by simpa [tChain] using h.symm
        rw [← this]; exact hw
      · exact absurd h.symm (by simp [tChain, tStub])
    rw [tChainChild] at hc
    by_cases h : (winOrbits (i.2.1, i.1)).length ≤ 1
    · rw [if_pos h] at hc
      by_cases hj : j = 0
      · rw [if_pos hj] at hc
        have : y = tStub i := (Option.some.inj hc).symm
        rw [this]
        exact Or.inr ⟨i, rfl, ⟨hI.1, length_le_one_of_leaf hI h⟩⟩
      · rw [if_neg hj] at hc; exact absurd hc (by simp)
    · rw [if_neg h] at hc
      cases hw : winChild (i, j, w) with
      | none => rw [hw] at hc; exact absurd hc (by simp)
      | some J =>
          rw [hw] at hc
          have : y = tChain J := (Option.some.inj hc).symm
          rw [this]
          exact Or.inl ⟨J, rfl, tChainWF_child hI hw⟩
  child_measure := by
    intro i j w y hi hc
    have hI : TChainWF n i := by
      rcases hi with ⟨i', h, hw⟩ | ⟨i', h, -⟩
      · have : i' = i := by simpa [tChain] using h.symm
        rw [← this]; exact hw
      · exact absurd h.symm (by simp [tChain, tStub])
    rw [tChainChild] at hc
    by_cases h : (winOrbits (i.2.1, i.1)).length ≤ 1
    · rw [if_pos h] at hc
      by_cases hj : j = 0
      · rw [if_pos hj] at hc
        have : y = tStub i := (Option.some.inj hc).symm
        rw [this, tMeasure_tStub, tMeasure_tChain]
        omega
      · rw [if_neg hj] at hc; exact absurd hc (by simp)
    · rw [if_neg h] at hc
      cases hw : winChild (i, j, w) with
      | none => rw [hw] at hc; exact absurd hc (by simp)
      | some J =>
          rw [hw] at hc
          have hy : y = tChain J := (Option.some.inj hc).symm
          have hlt : J.1.length < i.1.length :=
            (chainRound n (fun _ => none)).child_measure i j w J hI.1 hw
          rw [hy, tMeasure_tChain, tMeasure_tChain]
          omega
  child_ground := by
    intro i j w y hi hc
    rw [tChainChild] at hc
    by_cases h : (winOrbits (i.2.1, i.1)).length ≤ 1
    · rw [if_pos h] at hc
      by_cases hj : j = 0
      · rw [if_pos hj] at hc
        have : y = tStub i := (Option.some.inj hc).symm
        rw [this]; exact le_refl _
      · rw [if_neg hj] at hc; exact absurd hc (by simp)
    · rw [if_neg h] at hc
      cases hw : winChild (i, j, w) with
      | none => rw [hw] at hc; exact absurd hc (by simp)
      | some J =>
          rw [hw] at hc
          have hy : y = tChain J := (Option.some.inj hc).symm
          obtain ⟨g, τ, -, -, -, -, rfl⟩ := winChild_eq_some (p := (i, j, w)) hw
          rw [hy]
          exact le_refl _

/-! ## The master round -/

/-- The kinds of the toy family: the Chain Rule first, the stub second. -/
def tKinds (n : ℕ) : List (Kind TNode TState RawCoset (TWF n) tGround tMeasure) :=
  [chainKind n, stubKind n]

/-- **The master round of the toy family.** -/
def tRound (n : ℕ) : Round TNode TState RawCoset := famRound none none (tKinds n)

theorem misses_chain (i : RawWinSI) : Misses ([] : List (Kind TNode TState RawCoset
    (TWF n) tGround tMeasure)) (tChain i) := misses_nil _

theorem misses_stub (i : RawWinSI) : Misses [chainKind n] (tStub i) := by
  intro k hk
  have : k = chainKind n := by simpa using hk
  rw [this]
  rfl

theorem tKinds_chain (n : ℕ) : tKinds n = [] ++ chainKind n :: [stubKind n] := rfl

theorem tKinds_stub (n : ℕ) : tKinds n = [chainKind n] ++ stubKind n :: [] := rfl

theorem tRound_width_chain (i : RawWinSI) :
    (tRound n).width (tChain i) = (winOrbits (i.2.1, i.1)).length + 1 := by
  show famWidth (tKinds n) (tChain i) = _
  rw [tKinds_chain]
  exact famWidth_eq [] (chainKind n) [stubKind n] i (misses_chain i)

theorem tRound_init_chain (i : RawWinSI) :
    (tRound n).init (tChain i) = some (i.2.1, i.2.2.1) := by
  show famInit none (tKinds n) (tChain i) = _
  rw [tKinds_chain]
  exact famInit_eq none [] (chainKind n) [stubKind n] i (misses_chain i)

theorem tRound_child_chain (i : RawWinSI) (j : ℕ) (s : RawCoset) :
    (tRound n).child (tChain i, j, s) = tChainChild (i, j, s) := by
  show famChild (tKinds n) (tChain i, j, s) = _
  rw [tKinds_chain]
  exact famChild_eq [] (chainKind n) [stubKind n] i j s (misses_chain i)

theorem tRound_combine_chain (i : RawWinSI) (j : ℕ) (s : RawCoset) (a : RawCoset) :
    (tRound n).combine (tChain i, j, s, a) = a := by
  show famCombine (tKinds n) (tChain i, j, s, a) = _
  rw [tKinds_chain]
  exact famCombine_eq [] (chainKind n) [stubKind n] i j s a (misses_chain i)

theorem tRound_finish_chain (i : RawWinSI) (s : RawCoset) :
    (tRound n).finish (tChain i, s) = s := by
  show famFinish none (tKinds n) (tChain i, s) = _
  rw [tKinds_chain]
  exact famFinish_eq none [] (chainKind n) [stubKind n] i s (misses_chain i)

theorem tRound_width_stub (i : RawWinSI) : (tRound n).width (tStub i) = 0 := by
  show famWidth (tKinds n) (tStub i) = _
  rw [tKinds_stub]
  exact famWidth_eq [chainKind n] (stubKind n) [] i (misses_stub i)

theorem tRound_init_stub (i : RawWinSI) : (tRound n).init (tStub i) = none := by
  show famInit none (tKinds n) (tStub i) = _
  rw [tKinds_stub]
  exact famInit_eq none [chainKind n] (stubKind n) [] i (misses_stub i)

theorem tRound_child_stub (i : RawWinSI) (j : ℕ) (s : RawCoset) :
    (tRound n).child (tStub i, j, s) = none := by
  show famChild (tKinds n) (tStub i, j, s) = _
  rw [tKinds_stub]
  exact famChild_eq [chainKind n] (stubKind n) [] i j s (misses_stub i)

theorem tRound_finish_stub (i : RawWinSI) (s : RawCoset) :
    (tRound n).finish (tStub i, s) = tStubAns i := by
  show famFinish none (tKinds n) (tStub i, s) = _
  rw [tKinds_stub]
  exact famFinish_eq none [chainKind n] (stubKind n) [] i s (misses_stub i)

/-! ## The link to the mathematics -/

/-- The instance a master node describes. -/
def tDec (n : ℕ) (x : TNode) : SIInstance (Fin n) ℕ :=
  match x.1 with
  | some i => decWinSI n i
  | none => match x.2 with
      | some i => decWinSI n i
      | none => ⟨∅, ∅, fun _ => 0, fun _ => 0⟩

theorem tDec_tChain (i : RawWinSI) : tDec n (tChain i) = decWinSI n i := rfl
theorem tDec_tStub (i : RawWinSI) : tDec n (tStub i) = decWinSI n i := rfl

/-- The mathematical round of the toy family.  A Chain Rule node away from the leaf is the
chain of Eq. (63) over the orbits of Eq. (64); at the leaf it is **one call**, the very
instance `Algo.chainRound` would have handed to `solve`; a stub node answers outright. -/
def tRed (n : ℕ) (x : TNode) : SIReduction (Fin n) ℕ (Set (Equiv.Perm (Fin n))) :=
  match x.1 with
  | some i =>
      if (winOrbits (i.2.1, i.1)).length ≤ 1 then
        .call (decWinSI n i) (fun b => .done b)
      else cosetChain (decStrN n i.2.2.2.1) (decStrN n i.2.2.2.2)
        ((winOrbits (i.2.1, i.1)).map (winSet n)) (decWinSI n i).K
  | none => match x.2 with
      | some i => .done (decCoset n (tStubAns i))
      | none => .done ∅

theorem tRed_tStub (i : RawWinSI) : tRed n (tStub i) = .done (decCoset n (tStubAns i)) := rfl

theorem tRed_tChain (i : RawWinSI) :
    tRed n (tChain i) =
      (if (winOrbits (i.2.1, i.1)).length ≤ 1 then
        .call (decWinSI n i) (fun b => .done b)
      else cosetChain (decStrN n i.2.2.2.1) (decStrN n i.2.2.2.2)
        ((winOrbits (i.2.1, i.1)).map (winSet n)) (decWinSI n i).K) := rfl

/-- **The toy master round implements the toy reduction.** -/
theorem implements_tRound (n : ℕ) :
    Implements (tRound n) id (tDec n) (decCoset n) (tRed n) := by
  intro x hx
  rcases hx with ⟨i, rfl, hI⟩ | ⟨i, rfl, hI⟩
  · -- a Chain Rule node
    simp only [id_eq]
    rw [tRound_width_chain, tRound_init_chain, tRed_tChain]
    by_cases hleaf : (winOrbits (i.2.1, i.1)).length ≤ 1
    · -- the leaf: one child, of the stub kind
      rw [if_pos hleaf]
      refine loopMatch_oneCall (M := tRound n) (decI' := fun y => tDec n y)
        (decA := decCoset n) (tChain i) ((winOrbits (i.2.1, i.1)).length) 0
        (some (i.2.1, i.2.2.1)) (tStub i) ?_ ?_ ?_
      · rw [tRound_child_chain]
        show tChainChild (i, 0, some (i.2.1, i.2.2.1)) = some (tStub i)
        rw [tChainChild, if_pos hleaf, if_pos rfl]
      · intro a ha
        rw [tRound_combine_chain, tRound_child_chain]
        show tChainChild (i, 0 + 1, a) = none
        rw [tChainChild, if_pos hleaf, if_neg (by omega : ¬ (0 : ℕ) + 1 = 0)]
      · intro a ha
        rw [tRound_combine_chain, tRound_finish_chain]
        exact ha
    · -- away from the leaf: the Chain Rule
      rw [if_neg hleaf]
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
      have htrans := loopMatch_famRound (N := TNode) (S := TState) (α := RawCoset)
        (WF := TWF n) (ground := tGround) (measure := tMeasure)
        (bot := (none : RawCoset)) (botS := (none : TState))
        [] (chainKind n) [stubKind n]
        (R := chainRound n (fun _ => none)) i
        (fun j w => by
          show tChainChild (i, j, w) = Option.map tChain (winChild (i, j, w))
          rw [tChainChild, if_neg hleaf])
        (fun j w a => rfl)
        (fun w => by
          show w = (if (winOrbits (i.2.1, i.1)).length ≤ 1 then (none : RawCoset) else w)
          rw [if_neg hleaf])
        (decI := decWinSI n) (decI' := fun y => tDec n y) (decA := decCoset n)
        (fun _ => rfl) (misses_chain i)
        (winOrbits (i.2.1, i.1)).length 0 (some (i.2.1, i.2.2.1)) _ hcore
      have h3 : LoopMatch (tRound n) (fun y => tDec n y) (decCoset n) (tChain i)
          (winOrbits (i.2.1, i.1)).length 0 (some (i.2.1, i.2.2.1))
          (cosetChain (decStrN n i.2.2.2.1) (decStrN n i.2.2.2.2)
            ((winOrbits (i.2.1, i.1)).map (winSet n)) (decWinSI n i).K) := htrans
      exact loopMatch_mono h3 _ (by omega)
  · -- a stub node
    simp only [id_eq]
    rw [tRound_width_stub, tRound_init_stub, tRed_tStub]
    exact LoopMatch.done 0 0 none _ (tRound_child_stub i 0 none) (by
      rw [tRound_finish_stub])

/-- **The toy reduction is correct.** -/
theorem run_tRed (n : ℕ) (x : TNode) (hx : TWF n x) : (tRed n x).run = (tDec n x).answer := by
  rcases hx with ⟨i, rfl, hI⟩ | ⟨i, rfl, hI⟩
  · rw [tRed_tChain, tDec_tChain]
    by_cases hleaf : (winOrbits (i.2.1, i.1)).length ≤ 1
    · rw [if_pos hleaf]; rfl
    · rw [if_neg hleaf]
      have := run_chainRoundReduction n (fun _ => none) hI.1 (fun h => absurd h hleaf)
      rwa [chainRoundReduction, if_neg hleaf] at this
  · rw [tRed_tStub, tDec_tStub, SIReduction.run_done]
    exact decCoset_tStubAns hI

/-- **The toy master round computes the answer.** -/
theorem tRound_value (n : ℕ) (f : ℕ) (x : TNode) (hx : TWF n x) (hf : tMeasure x < f) :
    decCoset n ((tRound n).value f x) = (tDec n x).answer :=
  roundValue_eq (tRound n) (implements_tRound n) (fun y hy => run_tRed n y hy) f x hx hf

/-- **The machine computes the answer.**  `Algo.Round.evaluate` is the depth-first evaluator
of `Workspace/Algo/Evaluator.lean`, run for enough steps. -/
theorem tRound_evaluate (n : ℕ) (f N : ℕ) (x : TNode) (hx : TWF n x) (hf : tMeasure x < f)
    (hN : (tRound n).subSteps f x ≤ N) :
    ∃ a : RawCoset, (tRound n).evaluate N x = some a ∧ decCoset n a = (tDec n x).answer :=
  ⟨(tRound n).value f x, (tRound n).evaluate_eq_value f N x hx hf hN,
    tRound_value n f x hx hf⟩


/-! ## The cost of the toy family

`Algo.A15.famCostQ` needs one `Algo.A15.KindCost` per kind, and three clauses about the
master node type that belong to no kind.  The bound is `Algo.chainBound` — the bound of
`Algo.chainCost` — with room for the tag a master node carries on top of its payload. -/

/-- The size bound of the toy family. -/
def tBound (m : ℕ) : ℕ := 4 * chainBound m + 8

theorem polyBound_tBound : PolyBound tBound :=
  ((polyBound_const 4).mul polyBound_chainBound).add (polyBound_const 8)

theorem mono_tBound : Monotone tBound := by
  intro a b hab
  have := mono_chainBound hab
  simp only [tBound]
  omega

theorem succ_le_chainBound (m : ℕ) : m + 1 ≤ chainBound m := by
  have h : chainBound m = 16 * (gensBound m + m + 1) := rfl
  omega

theorem chainBound_le_tBound (m : ℕ) : chainBound m ≤ tBound m := by
  simp only [tBound]; omega

/-- The cost data of the Chain Rule round with the abstract solver removed: the solver is
never called, so the constant answer `none` pays for it. -/
def tChainCost (n : ℕ) : Round.Cost (chainRound n (fun _ => none)) :=
  chainCost n (fun _ => none) (quasiPolyFun_const _) (fun I _ => by
    show Enc.size (none : RawCoset) ≤ chainBound (Enc.size I.2.2.2)
    have h1 : Enc.size (none : RawCoset) = 2 := size_none
    have h2 : chainBound (Enc.size I.2.2.2)
        = 16 * (gensBound (Enc.size I.2.2.2) + Enc.size I.2.2.2 + 1) := rfl
    omega)

/-! ### The two routines that are new -/

theorem polyFun_tStubTest : PolyFun tStubTest := by
  have hu : PolyFun (fun z : (ℕ × List ℕ) × RawWinSI => z.1.1) :=
    polyFun_fst.comp polyFun_fst
  have hx : PolyFun (fun z : (ℕ × List ℕ) × RawWinSI => z.2.2.2.2.1) :=
    polyFun_snd.comp (polyFun_snd.comp (polyFun_snd.comp (polyFun_snd.comp polyFun_fst)))
  have hy : PolyFun (fun z : (ℕ × List ℕ) × RawWinSI => z.2.2.2.2.2) :=
    polyFun_snd.comp (polyFun_snd.comp (polyFun_snd.comp (polyFun_snd.comp polyFun_snd)))
  have hr : PolyFun (fun z : (ℕ × List ℕ) × RawWinSI => z.2.2.2.1) :=
    polyFun_snd.comp (polyFun_snd.comp (polyFun_snd.comp polyFun_fst))
  have hh : PolyFun (fun z : (ℕ × List ℕ) × RawWinSI =>
      decide (rawGet (z.2.2.2.2.1, z.1.1)
        = rawGet (z.2.2.2.2.2, rawGet (z.2.2.2.1, z.1.1)))) :=
    (((hx.pair hu).comp polyFun_rawGet).pair
      ((hy.pair ((hr.pair hu).comp polyFun_rawGet)).comp polyFun_rawGet)).comp polyFun_natEq
  have hcases := PolyFun.listCases (g := fun _ : RawWinSI => true) (h := _)
    (polyFun_const true) hh
  refine ((polyFun_fst.pair polyFun_id).comp hcases).of_eq (fun i => ?_)
  cases hw : i.1 <;> simp [tStubTest, hw]

theorem polyFun_tStubAns : PolyFun tStubAns := by
  have hsome : PolyFun (fun i : RawWinSI => (some (i.2.1, i.2.2.1) : RawCoset)) :=
    ((polyFun_snd.comp polyFun_fst).pair
      (polyFun_snd.comp (polyFun_snd.comp polyFun_fst))).comp polyFun_some
  refine (PolyFun.ite polyFun_tStubTest hsome (polyFun_const none)).of_eq (fun i => ?_)
  rw [tStubAns]

theorem polyFun_tChainChild : PolyFun tChainChild := by
  have horb : PolyFun (fun p : RawWinSI × ℕ × RawCoset => winOrbits (p.1.2.1, p.1.1)) :=
    ((polyFun_fst.comp (polyFun_snd.comp polyFun_fst)).pair
      (polyFun_fst.comp polyFun_fst)).comp polyFun_winOrbits
  have hleaf : PolyFun (fun p : RawWinSI × ℕ × RawCoset =>
      decide ((winOrbits (p.1.2.1, p.1.1)).length ≤ 1)) :=
    ((horb.comp polyFun_length).pair (polyFun_const 1)).comp polyFun_le
  have hzero : PolyFun (fun p : RawWinSI × ℕ × RawCoset => decide (p.2.1 = 0)) :=
    ((polyFun_snd.comp polyFun_fst).pair (polyFun_const 0)).comp polyFun_natEq
  have hstub : PolyFun (fun p : RawWinSI × ℕ × RawCoset =>
      (some (tStub p.1) : Option TNode)) :=
    ((polyFun_const (none : Option RawWinSI)).pair
      (polyFun_fst.comp polyFun_some)).comp polyFun_some
  have hsome2 : PolyFun (fun z : RawWinSI × (RawWinSI × ℕ × RawCoset) =>
      (some (tChain z.1) : Option TNode)) :=
    ((polyFun_fst.comp polyFun_some).pair
      (polyFun_const (none : Option RawWinSI))).comp polyFun_some
  have hmap : PolyFun (fun p : RawWinSI × ℕ × RawCoset =>
      (winChild p).map tChain) := by
    have hpair : PolyFun (fun p : RawWinSI × ℕ × RawCoset =>
        ((winChild p, p) : Option RawWinSI × (RawWinSI × ℕ × RawCoset))) :=
      polyFun_winChild.pair polyFun_id
    refine (hpair.comp (PolyFun.optionElim
      (g := fun _ : RawWinSI × ℕ × RawCoset => (none : Option TNode))
      (polyFun_const _) hsome2)).of_eq (fun p => ?_)
    cases hw : winChild p with
    | none => simp [hw]
    | some J => simp [hw]
  refine (PolyFun.ite hleaf (PolyFun.ite hzero hstub (polyFun_const none)) hmap).of_eq
    (fun p => ?_)
  rw [tChainChild]
  by_cases h1 : (winOrbits (p.1.2.1, p.1.1)).length ≤ 1
  · by_cases h2 : p.2.1 = 0 <;> simp [h1, h2]
  · simp [h1]

/-! ### The cost of each kind -/

theorem tKindCost_chain (n : ℕ) : KindCost tBound tBound tBound (chainKind n) where
  polyFun_proj := polyFun_fst
  polyFun_projω := polyFun_some
  quasiFun_child := polyFun_tChainChild.quasiFun
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
    have hI : WinWF n i := (tChainWF_of_TWF hi).1
    have h : Enc.size (some (i.2.1, i.2.2.1) : RawCoset)
        ≤ chainBound (Enc.size i.2.2.2) := (tChainCost n).init_le i hI
    exact le_trans h (chainBound_le_tBound _)
  combine_le := fun _ _ _ _ _ _ ha => ha
  finish_le := fun _ _ _ hs => hs
  width_le := by
    intro i hi
    have hI : WinWF n i := (tChainWF_of_TWF hi).1
    have h : (winOrbits (i.2.1, i.1)).length ≤ Enc.size i.2.2.2 :=
      (tChainCost n).width_le i hI
    have h2 := succ_le_chainBound (Enc.size i.2.2.2)
    have h3 := chainBound_le_tBound (Enc.size i.2.2.2)
    show (winOrbits (i.2.1, i.1)).length + 1 ≤ tBound (Enc.size i.2.2.2)
    omega

theorem tKindCost_stub (n : ℕ) : KindCost tBound tBound tBound (stubKind n) where
  polyFun_proj := polyFun_snd
  polyFun_projω := polyFun_some
  quasiFun_child := quasiFun_const _
  quasiFun_init := quasiFun_const _
  quasiFun_combine := (polyFun_snd.comp (polyFun_snd.comp polyFun_fst)).quasiFun
  quasiFun_finish := (polyFun_fst.comp polyFun_tStubAns).quasiFun
  u_projω_le := by
    intro s w h
    have hws : w = s := (Option.some.inj h).symm
    rw [hws]
    exact le_refl _
  init_le := by
    intro i _
    have h1 : Enc.size (none : RawCoset) = 2 := size_none
    show Enc.size (none : RawCoset) ≤ tBound (Enc.size i.2.2.2)
    simp only [tBound]
    omega
  combine_le := fun _ _ _ _ _ hs _ => hs
  finish_le := by
    intro i w hi _
    have hI : WinWF n i := (tStubWF_of_TWF hi).1
    have h : Enc.size (some (i.2.1, i.2.2.1) : RawCoset)
        ≤ chainBound (Enc.size i.2.2.2) := (tChainCost n).init_le i hI
    have h1 : Enc.size (none : RawCoset) = 2 := size_none
    show Enc.size (tStubAns i) ≤ tBound (Enc.size i.2.2.2)
    rw [tStubAns]
    by_cases ht : tStubTest i = true
    · rw [if_pos ht]; simp only [tBound]; omega
    · rw [if_neg ht]; simp only [tBound]; omega
  width_le := fun _ _ => Nat.zero_le _

/-! ### The three clauses that belong to no kind -/

theorem tGround_le (x : TNode) : tGround x ≤ Enc.size x := by
  obtain ⟨o1, o2⟩ := x
  cases o1 with
  | some i =>
      have h1 : Enc.size i.2.2.2 ≤ Enc.size i :=
        le_trans (size_snd_le' i.2.2) (le_trans (size_snd_le' i.2) (size_snd_le' i))
      have h2 : Enc.size (some i : Option RawWinSI) = Enc.size i + 2 := size_some_eq i
      have h3 : Enc.size (some i : Option RawWinSI)
          ≤ Enc.size ((some i, o2) : TNode) := Combine.size_fst_le _ _
      show Enc.size i.2.2.2 ≤ Enc.size ((some i, o2) : TNode)
      omega
  | none =>
      cases o2 with
      | some i =>
          have h1 : Enc.size i.2.2.2 ≤ Enc.size i :=
            le_trans (size_snd_le' i.2.2) (le_trans (size_snd_le' i.2) (size_snd_le' i))
          have h2 : Enc.size (some i : Option RawWinSI) = Enc.size i + 2 := size_some_eq i
          have h3 : Enc.size (some i : Option RawWinSI)
              ≤ Enc.size ((none, some i) : TNode) := Combine.size_snd_le _ _
          show Enc.size i.2.2.2 ≤ Enc.size ((none, some i) : TNode)
          omega
      | none => exact Nat.zero_le _

theorem tSize_le (x : TNode) (hx : TWF n x) : Enc.size x ≤ tBound (tGround x) := by
  have hnone : Enc.size (none : Option RawWinSI) = 2 := size_none
  rcases hx with ⟨i, rfl, hI⟩ | ⟨i, rfl, hI⟩
  · have h1 : Enc.size i ≤ chainBound (Enc.size i.2.2.2) := size_winSI_le hI.1
    have h2 : Enc.size (tChain i) ≤ 2 * Enc.size (some i : Option RawWinSI)
        + 2 * Enc.size (none : Option RawWinSI) := Combine.size_pair_le _ _
    have h3 : Enc.size (some i : Option RawWinSI) = Enc.size i + 2 := size_some_eq i
    show Enc.size (tChain i) ≤ tBound (Enc.size i.2.2.2)
    simp only [tBound]
    omega
  · have h1 : Enc.size i ≤ chainBound (Enc.size i.2.2.2) := size_winSI_le hI.1
    have h2 : Enc.size (tStub i) ≤ 2 * Enc.size (none : Option RawWinSI)
        + 2 * Enc.size (some i : Option RawWinSI) := Combine.size_pair_le _ _
    have h3 : Enc.size (some i : Option RawWinSI) = Enc.size i + 2 := size_some_eq i
    show Enc.size (tStub i) ≤ tBound (Enc.size i.2.2.2)
    simp only [tBound]
    omega

theorem tBot_le (m : ℕ) : Enc.size (none : RawCoset) ≤ tBound m := by
  have h1 : Enc.size (none : RawCoset) = 2 := size_none
  simp only [tBound]
  omega

/-- **The cost data of the toy master round.** -/
def tCostQ (n : ℕ) : Round.CostQ (tRound n) :=
  famCostQ (WF := TWF n) (ground := tGround) (measure := tMeasure)
    none none (tKinds n) tBound tBound tBound
    polyBound_tBound mono_tBound polyBound_tBound.quasiPoly mono_tBound
    polyBound_tBound.quasiPoly tGround_le tSize_le tBot_le tBot_le
    (by
      intro k hk
      have hk' : k = chainKind n ∨ k = stubKind n := by
        simpa [tKinds] using hk
      rcases hk' with rfl | rfl
      · exact tKindCost_chain n
      · exact tKindCost_stub n)

end

end Algo.A15

#print axioms Algo.A15.implements_tRound
#print axioms Algo.A15.tRound_value
#print axioms Algo.A15.tRound_evaluate
#print axioms Algo.A15.tCostQ
