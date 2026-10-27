import Workspace.Algo.TopWindowReduction

/-!
# Sec. 12, Corollary 12.0.6: the window round of the top action

`Workspace/Algo/TopRound.lean` (T3, Prop. 12.0.5) turns the top-action tests into
`|S| + 1` *full-window* instances for the kernel `N`.  Corollary 12.0.6 expands each of
them by Luks's Chain Rule over the `k` orbits of `N`, so that every recursive call has a
window of size `n/k`.  `Workspace/Algo/TopWindowReduction.lean` (A12 session 3) did that on
the *mathematical* side, with the choices the RAM routines make as data.

This file writes the composite as one `Algo.Round`: a flat, adaptive loop whose state is

```
(t, i, c, acc) : ℕ × ℕ × RawCoset × Option RawCoset
```

— the index `t` of the current top test, the index `i` of the current orbit of `N`, the
coset `c` the Chain Rule has reached inside that test, and the accumulated answer `acc` of
the tests closed so far.  The loop is adaptive in two ways: `child` stops the current chain
as soon as `c` is empty (Eq. (63) has nothing left to say), and `combine` then *closes the
test and opens the next one*, which is the step A12 session 3 could not fit into
`Algo.LoopMatch`.  It fits because `Algo.Round.child` sees the state: the transition is
carried out by `Algo.top2Combine` in one step, and `Algo.top2Child` reads the next
instance off the new state.

## Main definitions

* `Algo.top2Tail`, `Algo.top2Branch` — the mathematical round with the computed choices,
  written as a recursion over the remaining tests so that the matching induction is
  structural;
* `Algo.top2Round` — the computable round;
* `Algo.top2RoundReduction` — what it implements.

## Main results

* `Algo.implements_top2Round` — **the link**;
* `Algo.calls_top2Tail` — the calls are exactly the calls of
  `Algo.top1WindowReduction`, so the bounds of A12 session 3 apply unchanged: `3k` calls
  for the alternating branch, windows of size `n/k`;
* `Algo.run_top2RoundReduction_eq_giantA` — the run is the run of
  `Babai.giantAReduction (Babai.altHom ϕ) x y`, the case `G^ϕ = A(Γ)` of Cor. 12.0.6;
* `Algo.top2Cost` — the `Algo.Round.Cost` of the round.

No axiom, no `sorry`.
-/

namespace Algo

open RAM RAM.Targets
open Equiv (Perm)
open Babai (SIReduction SIInstance)

/-! ## Forcing the shape of a computed string

`Algo.topLiftPrepare` shifts the source string by the lift it computed.  On well-formed
input the result again has length `n`, but a round is a total function and the raw
input may be junk, so the round normalises the two strings of a kernel child to the length
of the domain.  This changes nothing after decoding. -/

/-- The raw string cut and padded to the length of the domain list. -/
def fixStr (p : List ℕ × RawStr) : RawStr := (rawOne p.1).map (fun i => rawGet (p.2, i))

@[simp] theorem length_fixStr (p : List ℕ × RawStr) : (fixStr p).length = p.1.length := by
  simp [fixStr, rawOne]

theorem decStrN_fixStr {n : ℕ} {dom : List ℕ} (hd : dom.length = n) (s : RawStr) :
    decStrN n (fixStr (dom, s)) = decStrN n s := by
  funext i
  have hi : (i : ℕ) < (fixStr (dom, s)).length := by
    rw [length_fixStr, hd]; exact i.isLt
  show (fixStr (dom, s)).getD (i : ℕ) 0 = s.getD (i : ℕ) 0
  rw [List.getD_eq_getElem _ _ hi]
  simp only [fixStr, List.getElem_map, rawOne]
  rw [List.getElem_range]
  rfl

theorem polyFun_fixStr : PolyFun fixStr := by
  have hs : PolyFun (fun z : (List ℕ × RawStr) × ℕ => rawGet (z.1.2, z.2)) :=
    ((polyFun_fst.comp polyFun_snd).pair polyFun_snd).comp polyFun_rawGet
  exact (polyFun_id.pair (polyFun_fst.comp polyFun_rawOne)).comp (PolyFun.mapParam hs)

/-! ## The kernel child of one top test, in a normalised shape -/

/-- The generators of the kernel instance a top test produces. -/
def topWinGens (q : RawTopLift) : RawGens := (topLiftChild q).1

/-- The source string of the kernel instance, forced to the length of the domain. -/
def topWinSrc (q : RawTopLift) : RawStr := fixStr (q.1.1.1, (topLiftChild q).2.1)

/-- The target string of the kernel instance, forced to the length of the domain. -/
def topWinTgt (q : RawTopLift) : RawStr := fixStr (q.1.1.1, (topLiftChild q).2.2)

/-- The candidate set the Chain Rule starts from inside one top test: the kernel itself,
written as a coset with the identity as representative.  The generators are tidied, so that
the coset the round carries in its state is well formed whatever the raw input is; this
changes nothing after decoding (`Algo.decCoset_topWinStart`). -/
def topWinStart (q : RawTopLift) : RawCoset :=
  some (tidyGens (q.1.1.1, topWinGens q), rawOne q.1.1.1)

theorem decCoset_topWinStart {n : ℕ} {q : RawTopLift} (hd : q.1.1.1.length = n) :
    decCoset n (topWinStart q) = (decGroup n (topWinGens q) : Set (Perm (Fin n))) := by
  have h1 : decPerm n (rawOne q.1.1.1) = 1 := by rw [rawOne_eq, hd, decPerm_encPerm]
  show {τ | ∃ g ∈ decGroup n (tidyGens (q.1.1.1, topWinGens q)),
    τ = decPerm n (rawOne q.1.1.1) * g} = _
  rw [h1, decGroup_tidyGens hd]
  ext τ
  simp

/-- The starting coset is well formed: at most `n²` generators on `n` points, and the
identity as representative. -/
theorem size_topWinStart_le {n m : ℕ} {q : RawTopLift} (hd : q.1.1.1.length = n)
    (hm : n ≤ m) : Enc.size (topWinStart q) ≤ chainBound m :=
  size_coset_le' (n := n) hm (wf_tidyGens hd _) (length_tidyGens hd _)
    (by rw [← hd]; exact wf_rawOne _)

theorem decStrN_topWinSrc {n : ℕ} {q : RawTopLift} (hd : q.1.1.1.length = n) :
    decStrN n (topWinSrc q) = decStrN n (topLiftChild q).2.1 :=
  decStrN_fixStr hd _

theorem decStrN_topWinTgt {n : ℕ} {q : RawTopLift} (hd : q.1.1.1.length = n) :
    decStrN n (topWinTgt q) = decStrN n (topLiftChild q).2.2 :=
  decStrN_fixStr hd _

/-! ## Normalising the answer of a child

`Algo.Round.Cost` asks that the state of the fold does not grow: everything the round stores
has to stay below *one* polynomial in the size of the instance, although the fold has
quasipolynomially many steps.  The answer of a child is only known to be below that
polynomial, so storing it unchanged would double the bound at every step.  The round
therefore stores the answer in the normal form of `Algo.rawRightTranslate` — right
translation by the identity, which leaves the coset alone and returns at most `n²`
well-formed generators with a well-formed representative. -/

/-- The raw answer of a child, rewritten in normal form. -/
def top2NormC (dom : List ℕ) (c : RawCoset) : RawCoset := rawRightTranslate (dom, rawOne dom, c)

/-- The accumulator, rewritten in normal form. -/
def top2NormS (dom : List ℕ) (s : Top1State) : Top1State := s.map (top2NormC dom)

@[simp] theorem isSome_top2NormC (dom : List ℕ) (c : RawCoset) :
    (top2NormC dom c).isSome = c.isSome := by
  cases c <;> rfl

theorem decCoset_top2NormC {n : ℕ} {dom : List ℕ} (hd : dom.length = n) (c : RawCoset) :
    decCoset n (top2NormC dom c) = decCoset n c := by
  have h1 : decPerm n (rawOne dom) = 1 := by rw [rawOne_eq, hd, decPerm_encPerm]
  have h2 : (fun σ : Perm (Fin n) => σ * 1) = id := by funext σ; simp
  rw [top2NormC, decCoset_rawRightTranslate hd, h1, Babai.rightTranslate, h2, Set.image_id]

theorem decTop1State_top2NormS {n : ℕ} {dom : List ℕ} (hd : dom.length = n) (s : Top1State) :
    decTop1State n (top2NormS dom s) = decTop1State n s := by
  cases s with
  | none => rfl
  | some c =>
      show some (decCoset n (top2NormC dom c)) = some (decCoset n c)
      rw [decCoset_top2NormC hd]

theorem size_top2NormC_le {n m : ℕ} {dom : List ℕ} (hd : dom.length = n) (hm : n ≤ m)
    (c : RawCoset) : Enc.size (top2NormC dom c) ≤ chainBound m := by
  have h0 : 16 * (m + 1) ≤ chainBound m := by
    have : chainBound m = 16 * (gensBound m + m + 1) := rfl
    omega
  rcases h : top2NormC dom c with _ | ⟨gs, ρ⟩
  · rw [size_none]; omega
  · obtain ⟨hw, hl, hr⟩ := rawRightTranslate_wf hd (rawOne dom) c h
    exact size_coset_le' (n := n) hm hw hl hr

theorem size_top2NormS_le {n m : ℕ} {dom : List ℕ} (hd : dom.length = n) (hm : n ≤ m)
    (s : Top1State) : Enc.size (top2NormS dom s) ≤ chainBound m + 2 := by
  have h0 : 16 * (m + 1) ≤ chainBound m := by
    have : chainBound m = 16 * (gensBound m + m + 1) := rfl
    omega
  cases s with
  | none => rw [show top2NormS dom none = none from rfl, size_none]; omega
  | some c =>
      have h1 : Enc.size (top2NormS dom (some c)) = Enc.size (top2NormC dom c) + 2 :=
        size_some_eq _
      have h2 := size_top2NormC_le hd hm c
      omega

theorem polyFun_top2NormC : PolyFun (fun z : List ℕ × RawCoset => top2NormC z.1 z.2) :=
  (polyFun_fst.pair ((polyFun_fst.comp polyFun_rawOne).pair polyFun_snd)).comp
    polyFun_rawRightTranslate

theorem polyFun_top2NormS : PolyFun (fun z : List ℕ × Top1State => top2NormS z.1 z.2) := by
  have h : PolyFun (fun y : RawCoset × (List ℕ × Top1State) =>
      (some (top2NormC y.2.1 y.1) : Top1State)) :=
    ((polyFun_snd.comp polyFun_fst).pair polyFun_fst).comp
      (polyFun_top2NormC.comp polyFun_some)
  exact ((polyFun_snd.pair polyFun_id).comp
    (PolyFun.optionElim (polyFun_const (none : Top1State)) h)).of_eq (fun z => by
      cases z.2 <;> rfl)

/-- The chain of Cor. 12.0.6 attached to one top test: the full-window kernel instance
`Iso_N(x^σ, y)` is cut into the orbits of `N`. -/
theorem topKernelReduction_eq {n : ℕ} (p : RawAction) {q : RawTopLift}
    (hd : q.1.1.1.length = n) :
    topKernelReduction n p (decFullSI n (topLiftChild q)) =
      cosetChain (decStrN n (topWinSrc q)) (decStrN n (topWinTgt q))
        ((topKernelWindows p).map (winSet n)) (decCoset n (topWinStart q)) := by
  rw [topKernelReduction, decCoset_topWinStart hd, decStrN_topWinSrc hd,
    decStrN_topWinTgt hd]
  rfl

/-! ## The mathematical round with the computed choices

`Algo.top1WindowReduction` (A12 session 3) is `Algo.top1Fold` expanded by the Chain Rule.
That shape is built by `Babai.SIReduction.expand`, which recurses on the *tree*; the
matching induction of `Algo.LoopMatch` needs a recursion on the **remaining tests**, so the
same tree is written again here as `Algo.top2Tail`, and `Algo.calls_top2Tail` and
`Algo.run_top2Tail` identify it with the session 3 object. -/

/-- One top test as a `.call`: the lifting reduction asks for the kernel instance and the
rest of the fold continues with the translated answer. -/
theorem top1Fold_cons (n : ℕ) (q : RawTopLift) (qs : List RawTopLift)
    (acc : Option (Set (Perm (Fin n)))) :
    top1Fold n (q :: qs) acc =
      .call (decFullSI n (topLiftChild q))
        (fun a => top1Fold n qs (top1JoinSet acc (topLiftAnswer n q a))) := rfl

/-- **Corollary 12.0.6 with the computed choices**: over the remaining top tests `qs`, run
Luks's Chain Rule (Eq. (63)) over the computed orbits `ws` of `N`, translate the answer of
each test back by its computed lift, and join it into the accumulator. -/
noncomputable def top2Tail (n : ℕ) (ws : List (List ℕ)) :
    List RawTopLift → Option (Set (Perm (Fin n))) →
    SIReduction (Fin n) ℕ (Set (Perm (Fin n)))
  | [], acc => .done (acc.getD ∅)
  | q :: qs, acc =>
      (cosetChain (decStrN n (topWinSrc q)) (decStrN n (topWinTgt q)) (ws.map (winSet n))
        (decCoset n (topWinStart q))).bind
          (fun ans => top2Tail n ws qs (top1JoinSet acc (topLiftAnswer n q ans)))

/-- The same reduction in the middle of a test: the chain of the current test has the
windows `rest` left and has reached the coset `C`. -/
noncomputable def top2Branch (n : ℕ) (ws : List (List ℕ)) (qs : List RawTopLift)
    (rest : List (List ℕ)) (C : Set (Perm (Fin n))) (acc : Option (Set (Perm (Fin n)))) :
    SIReduction (Fin n) ℕ (Set (Perm (Fin n))) :=
  match qs with
  | [] => .done (acc.getD ∅)
  | q :: qs' =>
      (cosetChain (decStrN n (topWinSrc q)) (decStrN n (topWinTgt q)) (rest.map (winSet n))
        C).bind (fun ans => top2Tail n ws qs' (top1JoinSet acc (topLiftAnswer n q ans)))

@[simp] theorem top2Branch_nil (n : ℕ) (ws rest : List (List ℕ)) (C : Set (Perm (Fin n)))
    (acc : Option (Set (Perm (Fin n)))) :
    top2Branch n ws [] rest C acc = .done (acc.getD ∅) := rfl

theorem top2Branch_cons (n : ℕ) (ws : List (List ℕ)) (q : RawTopLift)
    (qs : List RawTopLift) (rest : List (List ℕ)) (C : Set (Perm (Fin n)))
    (acc : Option (Set (Perm (Fin n)))) :
    top2Branch n ws (q :: qs) rest C acc =
      (cosetChain (decStrN n (topWinSrc q)) (decStrN n (topWinTgt q)) (rest.map (winSet n))
        C).bind (fun ans => top2Tail n ws qs (top1JoinSet acc (topLiftAnswer n q ans))) := rfl

/-- At the start of a test the middle form is the tail form. -/
theorem top2Branch_start (n : ℕ) (ws : List (List ℕ)) (q : RawTopLift)
    (qs : List RawTopLift) (acc : Option (Set (Perm (Fin n)))) :
    top2Branch n ws (q :: qs) ws (decCoset n (topWinStart q)) acc =
      top2Tail n ws (q :: qs) acc := rfl

section Link

variable {n : ℕ} {p : RawAction}

/-- The chain of one test computes the answer of its full-window kernel instance. -/
theorem run_chain_test (hd : p.1.1.length = n) {q : RawTopLift} (hq : q.1 = p) :
    (cosetChain (decStrN n (topWinSrc q)) (decStrN n (topWinTgt q))
      ((topKernelWindows p).map (winSet n)) (decCoset n (topWinStart q))).run =
      (decFullSI n (topLiftChild q)).answer := by
  have hd' : q.1.1.1.length = n := by rw [hq]; exact hd
  rw [← topKernelReduction_eq p hd']
  exact run_topKernelReduction p hd _ rfl

/-- **The computed round has the value of `Algo.top1Fold`.** -/
theorem run_top2Tail (hd : p.1.1.length = n) :
    ∀ (qs : List RawTopLift), (∀ q ∈ qs, q.1 = p) →
      ∀ acc : Option (Set (Perm (Fin n))),
        (top2Tail n (topKernelWindows p) qs acc).run = ((top1Fold n qs acc).run).getD ∅ := by
  intro qs
  induction qs with
  | nil => intro _ acc; rfl
  | cons q qs ih =>
      intro hqs acc
      rw [top2Tail, SIReduction.run_bind, run_chain_test hd (hqs q List.mem_cons_self),
        ih (fun r hr => hqs r (List.mem_cons_of_mem _ hr)), top1Fold_cons,
        SIReduction.run_call]

/-- **The computed round makes exactly the calls of `Algo.top1WindowReduction`.** -/
theorem calls_top2Tail (hd : p.1.1.length = n) :
    ∀ (qs : List RawTopLift), (∀ q ∈ qs, q.1 = p) →
      ∀ acc : Option (Set (Perm (Fin n))),
        (top2Tail n (topKernelWindows p) qs acc).calls =
          ((top1Fold n qs acc).expand (topKernelReduction n p)).calls := by
  intro qs
  induction qs with
  | nil => intro _ acc; rfl
  | cons q qs ih =>
      intro hqs acc
      have hq : q.1 = p := hqs q List.mem_cons_self
      have hd' : q.1.1.1.length = n := by rw [hq]; exact hd
      have hchain := topKernelReduction_eq (n := n) p hd'
      rw [top2Tail, SIReduction.calls_bind, top1Fold_cons, SIReduction.expand,
        SIReduction.calls_bind, hchain, run_chain_test hd hq,
        ih (fun r hr => hqs r (List.mem_cons_of_mem _ hr))]

end Link

/-! ## The computable round

A node is either the top-action node `(p, none)` or one of its children, a window instance
`(p, some W)`.  The state of the loop is `(t, i, c, acc)`: the index `t` of the current top
test, the index `i` of the current orbit of `N`, the coset `c` the Chain Rule has reached
inside the test, and the answer `acc` accumulated over the tests already closed. -/

/-- A node of the window round: the top-action node, or one window instance. -/
abbrev RawTop2Node := RawTop1 × Option RawWinSI

/-- The state of the loop: current test, current orbit, current chain coset, accumulator. -/
abbrev Top2State := ℕ × ℕ × RawCoset × Top1State

/-- The `|S| + 1` top tests of Prop. 12.0.5. -/
def top2Tests (p : RawTop1) : List RawTopLift := top1Inputs p

/-- The computed orbits of `N = ker ϕ`, the `k` windows of Cor. 12.0.6. -/
def top2Wins (p : RawTop1) : List (List ℕ) := topKernelWindows p.1

/-- The `t`-th top test. -/
def top2Test (p : RawTop1) (t : ℕ) : RawTopLift := top1Request (p, t)

theorem top2Test_eq_getElem (p : RawTop1) {t : ℕ} (ht : t < (top2Tests p).length) :
    top2Test p t = (top2Tests p)[t] := top1Request_eq_getElem p ht

@[simp] theorem top2Test_dom (p : RawTop1) (t : ℕ) : (top2Test p t).1.1.1 = p.1.1.1 := rfl

@[simp] theorem top2Test_action (p : RawTop1) (t : ℕ) : (top2Test p t).1 = p.1 := rfl

/-- The instance a node describes: the whole group on the full window at the top node, and
the window instance stored at a child. -/
noncomputable def decTop2Node (n : ℕ) (I : RawTop2Node) : SIInstance (Fin n) ℕ :=
  I.2.elim (decFullSI n (I.1.1.1.2, I.1.2.2.1, I.1.2.2.2)) (decWinSI n)

/-- The window instance the round hands on at the state `(t, i, c)`. -/
def top2Leaf (p : RawTop1) (t i : ℕ) (c : RawGens × RawPerm) : RawWinSI :=
  ((top2Wins p).getD i [], tidyGens (topWinSrc (top2Test p t), c.1),
    normPerm (topWinSrc (top2Test p t), c.2),
    topWinSrc (top2Test p t), topWinTgt (top2Test p t))

/-- The `j`-th child of the top node: the `i`-th orbit of `N` inside the `t`-th top test,
with the coset the chain has reached as its candidate set.  It is `none` once the tests are
exhausted, and the chain of a test is stopped by `Algo.top2Combine`, never here. -/
def top2Child (z : RawTop2Node × ℕ × Top2State) : Option RawTop2Node :=
  z.1.2.elim
    (if z.2.2.1 < (top2Tests z.1.1).length ∧ z.2.2.2.1 < (top2Wins z.1.1).length ∧
        z.2.1 < (top2Tests z.1.1).length * (top2Wins z.1.1).length then
      (z.2.2.2.2.1).map (fun c => (z.1.1, some (top2Leaf z.1.1 z.2.2.1 z.2.2.2.1 c)))
     else none)
    (fun _ => none)

/-- **The adaptive step.**  While the chain of the current test is alive and has orbits
left, the answer becomes the next candidate set.  Otherwise the test is *closed*: its answer
is translated back by the computed lift, joined into the accumulator, and the next test is
opened with the kernel as its candidate set.  Closing and opening happen in one step, which
is what lets the flat loop of `Algo.Round` walk the two nested recursions. -/
def top2Combine (z : RawTop2Node × ℕ × Top2State × RawCoset) : Top2State :=
  if z.2.2.2.isSome = true ∧ z.2.2.1.2.1 + 1 < (top2Wins z.1.1).length then
    (min z.2.2.1.1 (top2Tests z.1.1).length,
      min (z.2.2.1.2.1 + 1) (top2Wins z.1.1).length,
      top2NormC z.1.1.1.1.1 z.2.2.2, top2NormS z.1.1.1.1.1 z.2.2.1.2.2.2)
  else
    (min (z.2.2.1.1 + 1) (top2Tests z.1.1).length, 0,
      topWinStart (top2Test z.1.1 (min (z.2.2.1.1 + 1) (top2Tests z.1.1).length)),
      top2NormS z.1.1.1.1.1 (top1Join (z.1.1.1.1.1, z.2.2.1.2.2.2,
        topLiftFinish (z.1.1.1.1.1, topLiftPrepare (top2Test z.1.1 z.2.2.1.1), z.2.2.2))))

/-- The answer of a node: the accumulated coset at the top node, the solver at a child. -/
def top2Finish (solve : RawWinSI → RawCoset) (z : RawTop2Node × Top2State) : RawCoset :=
  z.1.2.elim (z.2.2.2.2.getD none) solve

/-- A window instance handed on by the round is well formed. -/
def Top2LeafWF (n : ℕ) (W : RawWinSI) : Prop :=
  W.2.2.2.1.length = n ∧ W.2.2.2.2.length = n ∧ W.1.Nodup ∧ (∀ u ∈ W.1, u < n) ∧
    RawGens.WF n W.2.1 ∧ W.2.1.length ≤ n * n ∧ RawPerm.WF n W.2.2.1

/-- Well-formed nodes.  The round is a total function; nothing is claimed off this
predicate.  A child records *which* window instance of the top node it is — the `t`-th top
test and the `i`-th orbit of `N` — which is what bounds its size in terms of the size of the
top node (`Algo.top2Cost`). -/
def Top2WF (n : ℕ) (I : RawTop2Node) : Prop :=
  0 < n ∧ I.1.1.1.1.length = n ∧
    ∀ W, I.2 = some W → ∃ t, ∃ i, ∃ c : RawGens × RawPerm,
      t < (top2Tests I.1).length ∧ W = top2Leaf I.1 t i c

section Windows

variable {n : ℕ} {p : RawTop1}

theorem wf_topKernel (hd : p.1.1.1.length = n) : RawGens.WF n (topKernel p.1) :=
  wf_tidyGens hd _

theorem lt_rawOne (hd : p.1.1.1.length = n) : ∀ j ∈ rawOne p.1.1.1, j < n := by
  intro j hj
  simpa [rawOne, hd] using hj

theorem rawIsInvariant_top2 (hd : p.1.1.1.length = n) :
    rawIsInvariant (topKernel p.1, rawOne p.1.1.1) = true := by
  have he : winSet n (rawOne p.1.1.1) = Set.univ := by
    ext j; simp [winSet, rawOne, hd]
  rw [rawIsInvariant_eq_true_iff (wf_topKernel hd) (lt_rawOne hd)]
  rw [show {j : Fin n | j.val ∈ rawOne p.1.1.1} = Set.univ from he]
  exact Babai.isInvariant_univ _

/-- Every computed window is a repetition-free list of points of the domain, whatever the
index. -/
theorem top2Wins_getD_wf (hd : p.1.1.1.length = n) (i : ℕ) :
    ((top2Wins p).getD i []).Nodup ∧ ∀ u ∈ (top2Wins p).getD i [], u < n := by
  by_cases hi : i < (top2Wins p).length
  · rw [List.getD_eq_getElem _ _ hi]
    have hmem : (top2Wins p)[i] ∈ top2Wins p := List.getElem_mem hi
    exact ⟨winOrbits_nodup hmem,
      winOrbits_lt (wf_topKernel hd) (lt_rawOne hd) (rawIsInvariant_top2 hd) hmem⟩
  · rw [List.getD_eq_default _ _ (by omega)]
    exact ⟨List.nodup_nil, by simp⟩

/-- There is at least one orbit as soon as the domain is nonempty. -/
theorem top2Wins_ne_nil (hn : 0 < n) (hd : p.1.1.1.length = n) : 0 < (top2Wins p).length := by
  have hne : rawOne p.1.1.1 ≠ [] := by
    intro hc
    have : (rawOne p.1.1.1).length = n := by simp [rawOne, hd]
    rw [hc] at this
    simp at this
    omega
  obtain ⟨j, hj⟩ := List.exists_mem_of_ne_nil _ hne
  have hcov := winOrbits_cover (wf_topKernel hd) (lt_rawOne hd) hj
  rcases hw : top2Wins p with _ | ⟨u, us⟩
  · exfalso
    have he : winOrbits (topKernel p.1, rawOne p.1.1.1) = [] := hw
    rw [he] at hcov
    simp at hcov
  · simp

theorem length_topWinSrc (hd : p.1.1.1.length = n) (t : ℕ) :
    (topWinSrc (top2Test p t)).length = n := by
  rw [topWinSrc, length_fixStr, top2Test_dom, hd]

theorem length_topWinTgt (hd : p.1.1.1.length = n) (t : ℕ) :
    (topWinTgt (top2Test p t)).length = n := by
  rw [topWinTgt, length_fixStr, top2Test_dom, hd]

/-- The window instances the round produces are well formed. -/
theorem top2LeafWF_leaf (hd : p.1.1.1.length = n) (t i : ℕ) (c : RawGens × RawPerm) :
    Top2LeafWF n (top2Leaf p t i c) := by
  have hs := length_topWinSrc hd t
  exact ⟨hs, length_topWinTgt hd t, (top2Wins_getD_wf hd i).1, (top2Wins_getD_wf hd i).2,
    wf_tidyGens hs _, length_tidyGens hs _, wf_normPerm hs _⟩

/-- The decoded window instance is the instance the Chain Rule asks for: the coset reached
so far, the `i`-th orbit of `N`, and the two strings of the test. -/
theorem decTop2Node_leaf (hd : p.1.1.1.length = n) (t i : ℕ) (c : RawGens × RawPerm) :
    decTop2Node n (p, some (top2Leaf p t i c)) =
      ⟨decCoset n (some c), winSet n ((top2Wins p).getD i []),
        decStrN n (topWinSrc (top2Test p t)), decStrN n (topWinTgt (top2Test p t))⟩ := by
  have hs := length_topWinSrc hd t
  show decWinSI n (top2Leaf p t i c) = _
  rw [decWinSI, top2Leaf]
  simp only
  rw [decCoset_some, decGroup_tidyGens hs, decPerm_normPerm hs, ← decCoset_some]

end Windows

/-- **What `Algo.top2Child` returns.**  There is a child only at the top node, while the
tests and the orbits are not exhausted and the chain of the current test is alive. -/
theorem top2Child_eq_some {z : RawTop2Node × ℕ × Top2State} {J : RawTop2Node}
    (h : top2Child z = some J) :
    ∃ c : RawGens × RawPerm, z.1.2 = none ∧ z.2.2.2.2.1 = some c ∧
      z.2.2.1 < (top2Tests z.1.1).length ∧ z.2.2.2.1 < (top2Wins z.1.1).length ∧
      z.2.1 < (top2Tests z.1.1).length * (top2Wins z.1.1).length ∧
      J = (z.1.1, some (top2Leaf z.1.1 z.2.2.1 z.2.2.2.1 c)) := by
  rcases ho : z.1.2 with _ | W
  · rw [top2Child, ho, Option.elim_none] at h
    by_cases hcond : z.2.2.1 < (top2Tests z.1.1).length ∧ z.2.2.2.1 < (top2Wins z.1.1).length ∧
        z.2.1 < (top2Tests z.1.1).length * (top2Wins z.1.1).length
    · rw [if_pos hcond] at h
      rcases hs : z.2.2.2.2.1 with _ | c
      · rw [hs] at h; simp at h
      · rw [hs] at h
        simp only [Option.map_some] at h
        exact ⟨c, rfl, rfl, hcond.1, hcond.2.1, hcond.2.2, (Option.some.inj h).symm⟩
    · rw [if_neg hcond] at h; simp at h
  · rw [top2Child, ho] at h; simp at h

/-- The child exists when everything the round tests is in order. -/
theorem top2Child_eq_some_of {p : RawTop1} {j t i : ℕ} {c : RawGens × RawPerm}
    {acc : Top1State} (ht : t < (top2Tests p).length) (hi : i < (top2Wins p).length)
    (hj : j < (top2Tests p).length * (top2Wins p).length) :
    top2Child (((p, none) : RawTop2Node), j, (t, i, (some c : RawCoset), acc)) =
      some (p, some (top2Leaf p t i c)) := by
  rw [top2Child]
  simp only [Option.elim_none]
  rw [if_pos ⟨ht, hi, hj⟩]
  rfl

/-- **Corollary 12.0.6 as a computable round.**  The top node runs the `|S| + 1` top tests
of Prop. 12.0.5, each expanded by Luks's Chain Rule over the `k` orbits of `N`; a child is
one window instance and is handed to `solve`. -/
def top2Round (n : ℕ) (solve : RawWinSI → RawCoset) :
    Round RawTop2Node Top2State RawCoset where
  WF := Top2WF n
  ground := fun I => Enc.size I.1
  measure := fun I => I.2.elim 1 (fun _ => 0)
  width := fun I => I.2.elim ((top2Tests I.1).length * (top2Wins I.1).length) (fun _ => 0)
  child := top2Child
  init := fun I => (0, 0, topWinStart (top2Test I.1 0), some none)
  combine := top2Combine
  finish := top2Finish solve
  bot := none
  child_eq_none := by
    rintro ⟨p, o⟩ j s hj
    cases o with
    | some W => rfl
    | none =>
        simp only [Option.elim_none] at hj
        show top2Child ((p, none), j, s) = none
        simp only [top2Child, Option.elim_none]
        rw [if_neg (fun h => absurd h.2.2 (by omega))]
  child_wf := by
    intro I j s J hI hc
    obtain ⟨c, ho, -, ht, -, -, rfl⟩ := top2Child_eq_some (z := (I, j, s)) hc
    refine ⟨hI.1, hI.2.1, fun W hW => ⟨s.1, s.2.1, c, ht, ?_⟩⟩
    cases hW
    rfl
  child_measure := by
    intro I j s J hI hc
    obtain ⟨c, ho, -, -, -, -, rfl⟩ := top2Child_eq_some (z := (I, j, s)) hc
    show (0 : ℕ) < I.2.elim 1 (fun _ => 0)
    rw [ho]
    exact Nat.zero_lt_one
  child_ground := by
    intro I j s J hI hc
    obtain ⟨c, ho, -, -, -, -, rfl⟩ := top2Child_eq_some (z := (I, j, s)) hc
    exact le_refl _

/-! ## The link to the mathematical layer -/

/-- The mathematical round the window round implements: at the top node, Cor. 12.0.6 with
the computed choices; at a child, the answer of the solver. -/
noncomputable def top2RoundReduction (n : ℕ) (solve : RawWinSI → RawCoset)
    (I : RawTop2Node) : SIReduction (Fin n) ℕ (Set (Perm (Fin n))) :=
  I.2.elim (top2Tail n (top2Wins I.1) (top2Tests I.1) (some ∅))
    (fun W => .done (decCoset n (solve W)))

theorem bind_call {Ω A : Type*} {α β : Type*} (I : SIInstance Ω A)
    (k : Set (Perm Ω) → SIReduction Ω A β) (g : β → SIReduction Ω A α) :
    (SIReduction.call I k).bind g = .call I (fun a => (k a).bind g) := rfl

/-- The Chain Rule gives up on an empty candidate set (Eq. (63)). -/
theorem cosetChain_empty {Ω A : Type*} (x y : Ω → A) (ws : List (Set Ω)) :
    cosetChain x y ws (∅ : Set (Perm Ω)) = .done ∅ := by
  cases ws with
  | nil => rfl
  | cons w ws => rw [cosetChain, if_pos rfl]

theorem decCoset_top2Finish (n : ℕ) (solve : RawWinSI → RawCoset) (p : RawTop1)
    (t i : ℕ) (c : RawCoset) (acc : Top1State) :
    decCoset n (top2Finish solve (((p, none) : RawTop2Node), (t, i, c, acc))) =
      (decTop1State n acc).getD ∅ := by
  cases acc <;> rfl

/-- At the start of a test the middle form of the tree is the tail form, whatever the
index. -/
theorem top2Branch_start_index (n : ℕ) (p : RawTop1) (t : ℕ)
    (acc : Option (Set (Perm (Fin n)))) :
    top2Branch n (top2Wins p) ((top2Tests p).drop t) (top2Wins p)
        (decCoset n (topWinStart (top2Test p t))) acc =
      top2Tail n (top2Wins p) ((top2Tests p).drop t) acc := by
  by_cases ht : t < (top2Tests p).length
  · rw [List.drop_eq_getElem_cons ht, ← top2Test_eq_getElem p ht]
    exact top2Branch_start _ _ _ _ _
  · rw [List.drop_eq_nil_of_le (by omega)]
    rfl

/-- The tree at the very start of the round. -/
theorem top2Branch_start_zero (n : ℕ) (p : RawTop1) (acc : Option (Set (Perm (Fin n)))) :
    top2Branch n (top2Wins p) (top2Tests p) (top2Wins p)
        (decCoset n (topWinStart (top2Test p 0))) acc =
      top2Tail n (top2Wins p) (top2Tests p) acc := by
  have h := top2Branch_start_index n p 0 acc
  rwa [List.drop_zero] at h

section Match

variable {n : ℕ} {p : RawTop1}

/-- **The fold of the window round walks the tree of Cor. 12.0.6.**

The induction is on the remaining budget `w`.  At a state `(t, i, c, acc)` the tree is the
chain of the `t`-th test with its last `k - i` orbits left, followed by the remaining tests.
There are three steps.  If the tests are exhausted both sides stop.  Otherwise the round
asks for the `i`-th orbit of `N` with `c` as its candidate set, which is what Eq. (63) asks
for; then either the chain of the test goes on with the answer as its candidate set, or the
test is *closed* — its answer is translated back by the computed lift and joined into `acc`
— and the next test is opened.  In the second case the tree of the current test has become
`done`, either because the answer was empty (Eq. (63) gives up) or because the orbits ran
out, and `Babai.SIReduction.bind` hands the accumulated value straight to the next test. -/
theorem loopMatch_top2 (solve : RawWinSI → RawCoset) (hn : 0 < n)
    (hd : p.1.1.1.length = n) :
    ∀ (w t i j : ℕ) (c : RawCoset) (acc : Top1State),
      c.isSome = true → i < (top2Wins p).length →
      j ≤ t * (top2Wins p).length + i →
      ((top2Tests p).length - t) * (top2Wins p).length ≤ w + i →
      LoopMatch (top2Round n solve) (decTop2Node n) (decCoset n) (p, none) w j
        (t, i, c, acc)
        (top2Branch n (top2Wins p) ((top2Tests p).drop t) ((top2Wins p).drop i)
          (decCoset n c) (decTop1State n acc)) := by
  have hk : 0 < (top2Wins p).length := top2Wins_ne_nil hn hd
  have hdone : ∀ (w t i j : ℕ) (c : RawCoset) (acc : Top1State),
      (top2Tests p).length ≤ t →
      LoopMatch (top2Round n solve) (decTop2Node n) (decCoset n) (p, none) w j
        (t, i, c, acc)
        (top2Branch n (top2Wins p) ((top2Tests p).drop t) ((top2Wins p).drop i)
          (decCoset n c) (decTop1State n acc)) := by
    intro w t i j c acc ht
    rw [List.drop_eq_nil_of_le ht, top2Branch_nil]
    refine LoopMatch.done w j (t, i, c, acc) _ ?_ ?_
    · show top2Child (((p, none) : RawTop2Node), j, (t, i, c, acc)) = none
      simp only [top2Child, Option.elim_none]
      rw [if_neg (fun h => absurd h.1 (by omega))]
    · exact decCoset_top2Finish n solve p t i c acc
  intro w
  induction w with
  | zero =>
      intro t i j c acc _ hi _ hb
      refine hdone 0 t i j c acc ?_
      by_contra ht
      push_neg at ht
      have h2 : 1 * (top2Wins p).length
          ≤ ((top2Tests p).length - t) * (top2Wins p).length :=
        Nat.mul_le_mul_right _ (by omega)
      omega
  | succ w ih =>
      intro t i j c acc hc hi hj hb
      by_cases ht : t < (top2Tests p).length
      · -- the tree and the round both ask for the `i`-th orbit of the `t`-th test
        have hexp : (t + 1) * (top2Wins p).length
            = t * (top2Wins p).length + (top2Wins p).length := by ring
        have hmul : (t + 1) * (top2Wins p).length
            ≤ (top2Tests p).length * (top2Wins p).length :=
          Nat.mul_le_mul_right _ (by omega)
        have hjlt : j < (top2Tests p).length * (top2Wins p).length := by omega
        have hstep : ((top2Tests p).length - t) * (top2Wins p).length
            = ((top2Tests p).length - (t + 1)) * (top2Wins p).length
              + (top2Wins p).length := by
          have he : (top2Tests p).length - t = ((top2Tests p).length - (t + 1)) + 1 := by omega
          rw [he]; ring
        obtain ⟨q, hq⟩ : ∃ q, c = some q := Option.isSome_iff_exists.1 hc
        subst hq
        have hCne : decCoset n (some q) ≠ ∅ := by
          intro h
          exact absurd ((decCoset_eq_empty_iff n _).1 h) (by simp)
        have hL : (top2Tests p).drop t = top2Test p t :: (top2Tests p).drop (t + 1) := by
          rw [List.drop_eq_getElem_cons ht, ← top2Test_eq_getElem p ht]
        have hW : (top2Wins p).drop i
            = ((top2Wins p)[i]'hi) :: (top2Wins p).drop (i + 1) :=
          List.drop_eq_getElem_cons hi
        have hgetd : (top2Wins p).getD i [] = (top2Wins p)[i]'hi :=
          List.getD_eq_getElem _ _ hi
        set J : RawTop2Node := (p, some (top2Leaf p t i q)) with hJ
        have hdec : decTop2Node n J
            = ⟨decCoset n (some q), winSet n ((top2Wins p)[i]'hi),
                decStrN n (topWinSrc (top2Test p t)),
                decStrN n (topWinTgt (top2Test p t))⟩ := by
          rw [hJ, decTop2Node_leaf hd t i q, hgetd]
        have hchild : (top2Round n solve).child
            (((p, none) : RawTop2Node), j, (t, i, (some q : RawCoset), acc)) = some J :=
          top2Child_eq_some_of ht hi hjlt
        rw [hL, top2Branch_cons, hW, List.map_cons, cosetChain, if_neg hCne, bind_call,
          ← hdec]
        refine LoopMatch.call w j (t, i, (some q : RawCoset), acc) J _ hchild ?_
        intro a ha
        by_cases hA : a.isSome = true ∧ i + 1 < (top2Wins p).length
        · -- the chain of the current test goes on
          have hcomb : (top2Round n solve).combine
              (((p, none) : RawTop2Node), j, (t, i, (some q : RawCoset), acc), a)
                = (t, i + 1, top2NormC p.1.1.1 a, top2NormS p.1.1.1 acc) := by
            show top2Combine _ = _
            rw [top2Combine]
            dsimp only
            rw [if_pos hA, Nat.min_eq_left (le_of_lt ht),
              Nat.min_eq_left (show i + 1 ≤ (top2Wins p).length by omega)]
          rw [hcomb]
          have hnext := ih t (i + 1) (j + 1) (top2NormC p.1.1.1 a) (top2NormS p.1.1.1 acc)
            (by rw [isSome_top2NormC]; exact hA.1) hA.2 (by omega) (by omega)
          rw [decCoset_top2NormC hd, decTop1State_top2NormS hd, hL, top2Branch_cons, ha]
            at hnext
          exact hnext
        · -- the test is closed and the next one is opened
          have hcomb : (top2Round n solve).combine
              (((p, none) : RawTop2Node), j, (t, i, (some q : RawCoset), acc), a)
                = (t + 1, 0, topWinStart (top2Test p (t + 1)),
                    top2NormS p.1.1.1 (top1Join (p.1.1.1, acc,
                      topLiftFinish (p.1.1.1, topLiftPrepare (top2Test p t), a)))) := by
            show top2Combine _ = _
            rw [top2Combine]
            dsimp only
            rw [if_neg hA, Nat.min_eq_left (by omega)]
          rw [hcomb]
          have hacc : decTop1State n (top2NormS p.1.1.1 (top1Join (p.1.1.1, acc,
                topLiftFinish (p.1.1.1, topLiftPrepare (top2Test p t), a))))
              = top1JoinSet (decTop1State n acc)
                  (topLiftAnswer n (top2Test p t) (decCoset n a)) := by
            rw [decTop1State_top2NormS hd, decTop1State_top1Join hd]
            exact congrArg (top1JoinSet (decTop1State n acc))
              (decCoset_topLiftFinish (top2Test p t) hd a)
          have hnext := ih (t + 1) 0 (j + 1) (topWinStart (top2Test p (t + 1)))
            (top2NormS p.1.1.1 (top1Join (p.1.1.1, acc,
              topLiftFinish (p.1.1.1, topLiftPrepare (top2Test p t), a))))
            rfl hk (by omega) (by omega)
          rw [List.drop_zero, top2Branch_start_index, hacc, ha] at hnext
          -- the tree of the current test has become `done`
          have hstop : (cosetChain (decStrN n (topWinSrc (top2Test p t)))
              (decStrN n (topWinTgt (top2Test p t)))
              (((top2Wins p).drop (i + 1)).map (winSet n))
              (decTop2Node n J).answer) = .done (decTop2Node n J).answer := by
            rcases ha' : a with _ | q'
            · have hz : (decTop2Node n J).answer = ∅ := by
                rw [← ha, ha']; rfl
              rw [hz, cosetChain_empty]
            · have hik : (top2Wins p).drop (i + 1) = [] :=
                List.drop_eq_nil_of_le (by
                  have : ¬ (i + 1 < (top2Wins p).length) := by
                    intro hlt; exact hA ⟨by rw [ha']; rfl, hlt⟩
                  omega)
              rw [hik, List.map_nil, cosetChain]
          show LoopMatch _ _ _ _ _ _ _ ((cosetChain _ _ _ (decTop2Node n J).answer).bind _)
          rw [hstop]
          exact hnext
      · exact hdone (w + 1) t i j c acc (by omega)

/-- **The link (Cor. 12.0.6).**  The window round implements the reduction of
`Algo.top2Tail`: Prop. 12.0.5 with the computed lifts, each of its `|S| + 1` kernel
instances expanded by Luks's Chain Rule over the computed orbits of `N`. -/
theorem implements_top2Round (solve : RawWinSI → RawCoset) :
    Implements (top2Round n solve) id (decTop2Node n) (decCoset n)
      (top2RoundReduction n solve) := by
  rintro ⟨p', o⟩ hI
  cases o with
  | some W => exact LoopMatch.done 0 0 _ _ rfl rfl
  | none =>
      have h := loopMatch_top2 (p := p') solve hI.1 hI.2.1
        ((top2Tests p').length * (top2Wins p').length) 0 0 0
        (topWinStart (top2Test p' 0)) (some none) rfl
        (top2Wins_ne_nil hI.1 hI.2.1) (by omega) (by simp)
      simp only [List.drop_zero] at h
      rw [top2Branch_start_zero] at h
      exact h

end Match

/-! ## The value, the calls and the window sizes

Every statement here is read off the session 3 results through `Algo.run_top2Tail` and
`Algo.calls_top2Tail`: the round is the same tree as `Algo.top1WindowReduction`, only
written as a recursion on the remaining tests. -/

section Value

variable {n : ℕ} {p : RawTop1}

/-- Every top test carries the action of the instance. -/
theorem top2Tests_action {q : RawTopLift} (hq : q ∈ top2Tests p) : q.1 = p.1 := by
  obtain ⟨r, -, rfl⟩ := List.mem_map.1 hq
  rfl

/-- **The round computes what Prop. 12.0.5 computes**, the negative decision read as the
empty answer. -/
theorem run_top2RoundReduction (hd : p.1.1.1.length = n) (solve : RawWinSI → RawCoset) :
    (top2RoundReduction n solve (p, none)).run
      = ((top1Fold n (top1Inputs p) (some ∅)).run).getD ∅ :=
  run_top2Tail hd (top2Tests p) (fun q hq => top2Tests_action hq) (some ∅)

/-- **The round makes exactly the calls of `Algo.top1WindowReduction`.** -/
theorem calls_top2RoundReduction (hd : p.1.1.1.length = n) (solve : RawWinSI → RawCoset) :
    (top2RoundReduction n solve (p, none)).calls = (top1WindowReduction n p).calls :=
  calls_top2Tail hd (top2Tests p) (fun q hq => top2Tests_action hq) (some ∅)

/-- Cor. 12.0.6: every call of the round has an orbit of `N` for its window. -/
theorem calls_top2RoundReduction_window (hd : p.1.1.1.length = n)
    (solve : RawWinSI → RawCoset) :
    ∀ J ∈ (top2RoundReduction n solve (p, none)).calls,
      J.Δ ∈ (topKernelWindows p.1).map (winSet n) := by
  rw [calls_top2RoundReduction hd]
  exact calls_top1WindowReduction_window n p hd

end Value

section Giant

variable {n m : ℕ} {dom gdom : List ℕ} {gens : List (Perm (Fin n))}
  {imgs : List (Perm (Fin m))} {ϕ : genGroup gens →* Perm (Fin m)}

/-- Cor. 12.0.6, the case `G^ϕ = A(Γ)`: the alternating branch makes at most `3k` calls,
`k` the number of orbits of `N = ker ϕ`. -/
theorem calls_length_top2RoundReduction_three (hd : dom.length = n) (hm : gdom.length = m)
    (hI : ImgsOf gens imgs ϕ) (x y : RawStr) (solve : RawWinSI → RawCoset) :
    (top2RoundReduction n solve
      ((((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m))),
        topAltGens gdom, x, y), none)).calls.length ≤ 3 * Babai.orbCount ϕ := by
  rw [calls_top2RoundReduction hd]
  exact calls_length_top1WindowReduction_three hd hm hI x y

/-- Cor. 12.0.6: the two branches of the Luks descent together make at most `6k` calls. -/
theorem calls_length_top2RoundReduction_pair (hd : dom.length = n) (hm : gdom.length = m)
    (hI : ImgsOf gens imgs ϕ) (x y y' : RawStr) (solve : RawWinSI → RawCoset) :
    (top2RoundReduction n solve
      ((((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m))),
        topAltGens gdom, x, y), none)).calls.length +
    (top2RoundReduction n solve
      ((((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m))),
        topAltGens gdom, x, y'), none)).calls.length ≤ 6 * Babai.orbCount ϕ := by
  have h1 := calls_length_top2RoundReduction_three hd hm hI x y solve
  have h2 := calls_length_top2RoundReduction_three hd hm hI x y' solve
  omega

/-- Cor. 12.0.6: every call of the round has a window of size `n/k`. -/
theorem calls_top2RoundReduction_size (hd : dom.length = n) (hm : gdom.length = m)
    (hI : ImgsOf gens imgs ϕ) (S : RawGens) (x y : RawStr) (solve : RawWinSI → RawCoset)
    (hG : Babai.IsTransitive (genGroup gens)) (hgiant : Babai.IsGiantRep ϕ)
    (hlarge : Babai.LargeK m (Nat.card (Fin n))) :
    ∀ I ∈ (top2RoundReduction n solve
      ((((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m))), S, x, y),
        none)).calls, Babai.orbCount ϕ * I.windowSize = n := by
  rw [calls_top2RoundReduction hd]
  exact calls_top1WindowReduction_size hd hm hI S x y hG hgiant hlarge

/-- **Cor. 12.0.6, the case `G^ϕ = A(Γ)`**: the run of the round is the run of
`Babai.giantAReduction` for the descended representation `ϕ₁ : G₁ → A(Γ)`, with the
negative decision read as the empty answer. -/
theorem run_top2RoundReduction_eq_giantA (hd : dom.length = n) (hm : gdom.length = m)
    (hI : ImgsOf gens imgs ϕ) (hm3 : 3 ≤ m) (x y : Fin n → ℕ)
    (solve : RawWinSI → RawCoset) :
    (top2RoundReduction n solve
      ((((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m))),
        topAltGens gdom, encStrN x, encStrN y), none)).run
      = ((Babai.giantAReduction (Babai.altHom ϕ) x y).run).getD ∅ := by
  rw [run_top2RoundReduction hd, ← run_top1WindowReduction n _ hd,
    run_top1WindowReduction_eq_giantA hd hm hI hm3 x y]

/-- **Cor. 12.0.6 for an arbitrary target subgroup**: the run of the round is the run of
Prop. 12.0.5 with the supplied generators. -/
theorem run_top2RoundReduction_eq {H : Subgroup (Perm (Fin m))}
    (ψ : genGroup gens →* H) (hd : dom.length = n) (hm : gdom.length = m)
    (hI : ImgsOf gens imgs (H.subtype.comp ψ)) (S : List H) (x y : Fin n → ℕ)
    (solve : RawWinSI → RawCoset) :
    (top2RoundReduction n solve
      ((((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m))),
        S.map (fun τ => encPerm m τ.val), encStrN x, encStrN y), none)).run
      = ((Babai.TopAction1Reduction ψ x y S).run).getD ∅ := by
  rw [run_top2RoundReduction hd, run_top1Fold_eq_targetReduction ψ hd hm hI S x y]

end Giant

section RoundValue

variable {n : ℕ}

/-- **One complete run of the round**, when the solver answers each window instance
correctly. -/
theorem top2Round_value_two (solve : RawWinSI → RawCoset)
    (hs : ∀ W, decCoset n (solve W) = (decWinSI n W).answer)
    (p : RawTop1) (hn : 0 < n) (hd : p.1.1.1.length = n) :
    decCoset n ((top2Round n solve).value 2 (p, none))
      = (top2RoundReduction n solve (p, none)).run := by
  have hI : Top2WF n ((p, none) : RawTop2Node) := ⟨hn, hd, by simp⟩
  have himpl := implements_top2Round (n := n) solve (p, none) hI
  have h := (top2Round n solve).loopAux_eq
    (rec := (top2Round n solve).value 1)
    (Good := fun J : RawTop2Node => ∃ W, J.2 = some W)
    (fun j s J hc => by
      obtain ⟨c, -, -, -, -, -, rfl⟩ := top2Child_eq_some (z := ((p, none), j, s)) hc
      exact ⟨_, rfl⟩)
    (fun J hJ => by
      obtain ⟨W, hW⟩ := hJ
      have hv : (top2Round n solve).value 1 J = solve W := by
        rw [Round.value_succ]
        change (top2Round n solve).loopAux _ (J.2.elim _ _) J 0 _ = _
        rw [hW]
        change top2Finish solve (J, _) = solve W
        rw [top2Finish, hW]
        rfl
      rw [hv]
      simp only [id_eq]
      rw [decTop2Node, hW]
      exact hs W)
    _ _ _ _ himpl
  exact h.1

end RoundValue

/-! ## The running time of the four routines -/

theorem polyFun_isSome {β : Type*} [Enc β] : PolyFun (fun o : Option β => o.isSome) :=
  ((polyFun_id.pair polyFun_id).comp
    (PolyFun.optionElim (polyFun_const false) (polyFun_const true))).of_eq
      (fun o => by cases o <;> rfl)

theorem polyFun_band {α : Type*} [Enc α] {f g : α → Bool} (hf : PolyFun f) (hg : PolyFun g) :
    PolyFun (fun a => f a && g a) :=
  (PolyFun.ite hf hg (polyFun_const false)).of_eq (fun a => by
    cases hfa : f a <;> simp [hfa])

theorem polyFun_topWinGens : PolyFun topWinGens := polyFun_topLiftChild.comp polyFun_fst

theorem polyFun_topWinSrc : PolyFun topWinSrc :=
  ((((polyFun_fst.comp polyFun_fst).comp polyFun_fst)).pair
    ((polyFun_topLiftChild.comp polyFun_snd).comp polyFun_fst)).comp polyFun_fixStr

theorem polyFun_topWinTgt : PolyFun topWinTgt :=
  ((((polyFun_fst.comp polyFun_fst).comp polyFun_fst)).pair
    ((polyFun_topLiftChild.comp polyFun_snd).comp polyFun_snd)).comp polyFun_fixStr

theorem polyFun_topWinStart : PolyFun topWinStart :=
  (((((polyFun_fst.comp polyFun_fst).comp polyFun_fst).pair polyFun_topWinGens).comp
    polyFun_tidyGens).pair
      (((polyFun_fst.comp polyFun_fst).comp polyFun_fst).comp polyFun_rawOne)).comp
      polyFun_some

theorem polyFun_top2Tests : PolyFun top2Tests := polyFun_top1Inputs

theorem polyFun_top2Wins : PolyFun top2Wins := polyFun_fst.comp polyFun_topKernelWindows

theorem polyFun_top2Test : PolyFun (fun z : RawTop1 × ℕ => top2Test z.1 z.2) :=
  polyFun_top1Request

/-- The guard of the loop, as a machine test. -/
def top2Go (z : RawTop2Node × ℕ × Top2State) : Bool :=
  (decide (z.2.2.1 + 1 ≤ (top2Tests z.1.1).length) &&
    decide (z.2.2.2.1 + 1 ≤ (top2Wins z.1.1).length)) &&
      decide (z.2.1 + 1 ≤ (top2Tests z.1.1).length * (top2Wins z.1.1).length)

theorem top2Go_eq_true (z : RawTop2Node × ℕ × Top2State) :
    top2Go z = true ↔
      (z.2.2.1 < (top2Tests z.1.1).length ∧ z.2.2.2.1 < (top2Wins z.1.1).length ∧
        z.2.1 < (top2Tests z.1.1).length * (top2Wins z.1.1).length) := by
  simp only [top2Go, Bool.and_eq_true, decide_eq_true_eq]
  omega

/-- The second guard: the chain of the current test is alive and has orbits left. -/
def top2GoChain (z : RawTop2Node × ℕ × Top2State × RawCoset) : Bool :=
  z.2.2.2.isSome && decide (z.2.2.1.2.1 + 1 + 1 ≤ (top2Wins z.1.1).length)

theorem top2GoChain_eq_true (z : RawTop2Node × ℕ × Top2State × RawCoset) :
    top2GoChain z = true ↔
      (z.2.2.2.isSome = true ∧ z.2.2.1.2.1 + 1 < (top2Wins z.1.1).length) := by
  simp only [top2GoChain, Bool.and_eq_true, decide_eq_true_eq]
  exact and_congr_right (fun _ => by omega)

section Cost

/-- The projections of the input of `Algo.top2Child`. -/
private theorem polyFun_topOf : PolyFun (fun z : RawTop2Node × ℕ × Top2State => z.1.1) :=
  polyFun_fst.comp polyFun_fst

theorem polyFun_top2Go : PolyFun top2Go := by
  have hp : PolyFun (fun z : RawTop2Node × ℕ × Top2State => z.1.1) := polyFun_topOf
  have hT : PolyFun (fun z : RawTop2Node × ℕ × Top2State => (top2Tests z.1.1).length) :=
    (hp.comp polyFun_top2Tests).comp polyFun_length
  have hK : PolyFun (fun z : RawTop2Node × ℕ × Top2State => (top2Wins z.1.1).length) :=
    (hp.comp polyFun_top2Wins).comp polyFun_length
  have ht : PolyFun (fun z : RawTop2Node × ℕ × Top2State => z.2.2.1) :=
    (polyFun_snd.comp polyFun_snd).comp polyFun_fst
  have hi : PolyFun (fun z : RawTop2Node × ℕ × Top2State => z.2.2.2.1) :=
    ((polyFun_snd.comp polyFun_snd).comp polyFun_snd).comp polyFun_fst
  have hj : PolyFun (fun z : RawTop2Node × ℕ × Top2State => z.2.1) :=
    polyFun_snd.comp polyFun_fst
  exact polyFun_band (polyFun_band ((ht.add (polyFun_const 1)).le hT)
    ((hi.add (polyFun_const 1)).le hK))
    ((hj.add (polyFun_const 1)).le (hT.mul hK))

theorem polyFun_top2Leaf :
    PolyFun (fun z : (RawTop1 × ℕ × ℕ) × (RawGens × RawPerm) =>
      top2Leaf z.1.1 z.1.2.1 z.1.2.2 z.2) := by
  have hp : PolyFun (fun z : (RawTop1 × ℕ × ℕ) × (RawGens × RawPerm) => z.1.1) :=
    polyFun_fst.comp polyFun_fst
  have ht : PolyFun (fun z : (RawTop1 × ℕ × ℕ) × (RawGens × RawPerm) => z.1.2.1) :=
    (polyFun_fst.comp polyFun_snd).comp polyFun_fst
  have hi : PolyFun (fun z : (RawTop1 × ℕ × ℕ) × (RawGens × RawPerm) => z.1.2.2) :=
    (polyFun_fst.comp polyFun_snd).comp polyFun_snd
  have hq : PolyFun (fun z : (RawTop1 × ℕ × ℕ) × (RawGens × RawPerm) =>
      top2Test z.1.1 z.1.2.1) := (hp.pair ht).comp polyFun_top2Test
  have hsrc : PolyFun (fun z : (RawTop1 × ℕ × ℕ) × (RawGens × RawPerm) =>
      topWinSrc (top2Test z.1.1 z.1.2.1)) := hq.comp polyFun_topWinSrc
  have htgt : PolyFun (fun z : (RawTop1 × ℕ × ℕ) × (RawGens × RawPerm) =>
      topWinTgt (top2Test z.1.1 z.1.2.1)) := hq.comp polyFun_topWinTgt
  have hwin : PolyFun (fun z : (RawTop1 × ℕ × ℕ) × (RawGens × RawPerm) =>
      (top2Wins z.1.1).getD z.1.2.2 []) :=
    (((hp.comp polyFun_top2Wins).pair hi).pair (polyFun_const ([] : List ℕ))).comp
      polyFun_getD
  have hg : PolyFun (fun z : (RawTop1 × ℕ × ℕ) × (RawGens × RawPerm) =>
      tidyGens (topWinSrc (top2Test z.1.1 z.1.2.1), z.2.1)) :=
    (hsrc.pair (polyFun_snd.comp polyFun_fst)).comp polyFun_tidyGens
  have hr : PolyFun (fun z : (RawTop1 × ℕ × ℕ) × (RawGens × RawPerm) =>
      normPerm (topWinSrc (top2Test z.1.1 z.1.2.1), z.2.2)) :=
    (hsrc.pair (polyFun_snd.comp polyFun_snd)).comp polyFun_normPerm
  exact hwin.pair (hg.pair (hr.pair (hsrc.pair htgt)))

theorem polyFun_top2Child : PolyFun top2Child := by
  have hp : PolyFun (fun z : RawTop2Node × ℕ × Top2State => z.1.1) := polyFun_topOf
  have ht : PolyFun (fun z : RawTop2Node × ℕ × Top2State => z.2.2.1) :=
    (polyFun_snd.comp polyFun_snd).comp polyFun_fst
  have hi : PolyFun (fun z : RawTop2Node × ℕ × Top2State => z.2.2.2.1) :=
    ((polyFun_snd.comp polyFun_snd).comp polyFun_snd).comp polyFun_fst
  have hc : PolyFun (fun z : RawTop2Node × ℕ × Top2State => z.2.2.2.2.1) :=
    (((polyFun_snd.comp polyFun_snd).comp polyFun_snd).comp polyFun_snd).comp polyFun_fst
  have hsome : PolyFun (fun y : (RawGens × RawPerm) × (RawTop2Node × ℕ × Top2State) =>
      (some (y.2.1.1, some (top2Leaf y.2.1.1 y.2.2.2.1 y.2.2.2.2.1 y.1))
        : Option RawTop2Node)) := by
    have hp' : PolyFun (fun y : (RawGens × RawPerm) × (RawTop2Node × ℕ × Top2State) =>
        y.2.1.1) := polyFun_snd.comp hp
    have ht' : PolyFun (fun y : (RawGens × RawPerm) × (RawTop2Node × ℕ × Top2State) =>
        y.2.2.2.1) := polyFun_snd.comp ht
    have hi' : PolyFun (fun y : (RawGens × RawPerm) × (RawTop2Node × ℕ × Top2State) =>
        y.2.2.2.2.1) := polyFun_snd.comp hi
    have hleaf := ((hp'.pair (ht'.pair hi')).pair polyFun_fst).comp polyFun_top2Leaf
    exact (hp'.pair (hleaf.comp polyFun_some)).comp polyFun_some
  have hmap : PolyFun (fun z : RawTop2Node × ℕ × Top2State =>
      (z.2.2.2.2.1).map (fun c => (z.1.1, some (top2Leaf z.1.1 z.2.2.1 z.2.2.2.1 c)))) :=
    ((hc.pair polyFun_id).comp
      (PolyFun.optionElim (polyFun_const (none : Option RawTop2Node)) hsome)).of_eq
        (fun z => by cases hcz : z.2.2.2.2.1 <;> simp [hcz])
  have hbody : PolyFun (fun z : RawTop2Node × ℕ × Top2State =>
      if z.2.2.1 < (top2Tests z.1.1).length ∧ z.2.2.2.1 < (top2Wins z.1.1).length ∧
          z.2.1 < (top2Tests z.1.1).length * (top2Wins z.1.1).length then
        (z.2.2.2.2.1).map (fun c => (z.1.1, some (top2Leaf z.1.1 z.2.2.1 z.2.2.2.1 c)))
      else none) :=
    (PolyFun.ite polyFun_top2Go hmap (polyFun_const none)).of_eq (fun z => by
      by_cases h : z.2.2.1 < (top2Tests z.1.1).length ∧ z.2.2.2.1 < (top2Wins z.1.1).length ∧
          z.2.1 < (top2Tests z.1.1).length * (top2Wins z.1.1).length
      · rw [if_pos ((top2Go_eq_true z).2 h), if_pos h]
      · rw [if_neg (fun hcon => h ((top2Go_eq_true z).1 hcon)), if_neg h])
  have hleafcase : PolyFun (fun y : RawWinSI × (RawTop2Node × ℕ × Top2State) =>
      (none : Option RawTop2Node)) := polyFun_const none
  exact ((((polyFun_fst.comp polyFun_snd).pair polyFun_id).comp
    (PolyFun.optionElim hbody hleafcase))).of_eq (fun z => by
      cases hoz : z.1.2 <;> simp [top2Child, hoz])

theorem polyFun_top2Combine : PolyFun top2Combine := by
  have hp : PolyFun (fun z : RawTop2Node × ℕ × Top2State × RawCoset => z.1.1) :=
    polyFun_fst.comp polyFun_fst
  have ht : PolyFun (fun z : RawTop2Node × ℕ × Top2State × RawCoset => z.2.2.1.1) :=
    ((polyFun_snd.comp polyFun_snd).comp polyFun_fst).comp polyFun_fst
  have hi : PolyFun (fun z : RawTop2Node × ℕ × Top2State × RawCoset => z.2.2.1.2.1) :=
    (((polyFun_snd.comp polyFun_snd).comp polyFun_fst).comp polyFun_snd).comp polyFun_fst
  have hacc : PolyFun (fun z : RawTop2Node × ℕ × Top2State × RawCoset => z.2.2.1.2.2.2) :=
    ((((polyFun_snd.comp polyFun_snd).comp polyFun_fst).comp polyFun_snd).comp
      polyFun_snd).comp polyFun_snd
  have ha : PolyFun (fun z : RawTop2Node × ℕ × Top2State × RawCoset => z.2.2.2) :=
    (polyFun_snd.comp polyFun_snd).comp polyFun_snd
  have hdom : PolyFun (fun z : RawTop2Node × ℕ × Top2State × RawCoset => z.1.1.1.1.1) :=
    (hp.comp polyFun_fst).comp (polyFun_fst.comp polyFun_fst)
  have hTl : PolyFun (fun z : RawTop2Node × ℕ × Top2State × RawCoset =>
      (top2Tests z.1.1).length) := (hp.comp polyFun_top2Tests).comp polyFun_length
  have hKl : PolyFun (fun z : RawTop2Node × ℕ × Top2State × RawCoset =>
      (top2Wins z.1.1).length) := (hp.comp polyFun_top2Wins).comp polyFun_length
  have hgo : PolyFun top2GoChain := polyFun_band (ha.comp polyFun_isSome)
    (((hi.add (polyFun_const 1)).add (polyFun_const 1)).le hKl)
  have hnormC : PolyFun (fun z : RawTop2Node × ℕ × Top2State × RawCoset =>
      top2NormC z.1.1.1.1.1 z.2.2.2) := (hdom.pair ha).comp polyFun_top2NormC
  have hnormAcc : PolyFun (fun z : RawTop2Node × ℕ × Top2State × RawCoset =>
      top2NormS z.1.1.1.1.1 z.2.2.1.2.2.2) := (hdom.pair hacc).comp polyFun_top2NormS
  have hminT : PolyFun (fun z : RawTop2Node × ℕ × Top2State × RawCoset =>
      min z.2.2.1.1 (top2Tests z.1.1).length) := (ht.pair hTl).comp polyFun_min
  have hA : PolyFun (fun z : RawTop2Node × ℕ × Top2State × RawCoset =>
      ((min z.2.2.1.1 (top2Tests z.1.1).length,
        min (z.2.2.1.2.1 + 1) (top2Wins z.1.1).length,
        top2NormC z.1.1.1.1.1 z.2.2.2,
        top2NormS z.1.1.1.1.1 z.2.2.1.2.2.2) : Top2State)) :=
    hminT.pair ((((hi.add (polyFun_const 1)).pair hKl).comp polyFun_min).pair
      (hnormC.pair hnormAcc))
  have hmin : PolyFun (fun z : RawTop2Node × ℕ × Top2State × RawCoset =>
      min (z.2.2.1.1 + 1) (top2Tests z.1.1).length) :=
    ((ht.add (polyFun_const 1)).pair hTl).comp polyFun_min
  have hstart : PolyFun (fun z : RawTop2Node × ℕ × Top2State × RawCoset =>
      topWinStart (top2Test z.1.1 (min (z.2.2.1.1 + 1) (top2Tests z.1.1).length))) :=
    ((hp.pair hmin).comp polyFun_top2Test).comp polyFun_topWinStart
  have hprep : PolyFun (fun z : RawTop2Node × ℕ × Top2State × RawCoset =>
      topLiftPrepare (top2Test z.1.1 z.2.2.1.1)) :=
    ((hp.pair ht).comp polyFun_top2Test).comp polyFun_topLiftPrepare
  have hfin : PolyFun (fun z : RawTop2Node × ℕ × Top2State × RawCoset =>
      topLiftFinish (z.1.1.1.1.1, topLiftPrepare (top2Test z.1.1 z.2.2.1.1), z.2.2.2)) :=
    (hdom.pair (hprep.pair ha)).comp polyFun_topLiftFinish
  have hjoin : PolyFun (fun z : RawTop2Node × ℕ × Top2State × RawCoset =>
      top1Join (z.1.1.1.1.1, z.2.2.1.2.2.2,
        topLiftFinish (z.1.1.1.1.1, topLiftPrepare (top2Test z.1.1 z.2.2.1.1), z.2.2.2))) :=
    (hdom.pair (hacc.pair hfin)).comp polyFun_top1Join
  have hnormJoin : PolyFun (fun z : RawTop2Node × ℕ × Top2State × RawCoset =>
      top2NormS z.1.1.1.1.1 (top1Join (z.1.1.1.1.1, z.2.2.1.2.2.2,
        topLiftFinish (z.1.1.1.1.1, topLiftPrepare (top2Test z.1.1 z.2.2.1.1), z.2.2.2)))) :=
    (hdom.pair hjoin).comp polyFun_top2NormS
  have hB : PolyFun (fun z : RawTop2Node × ℕ × Top2State × RawCoset =>
      ((min (z.2.2.1.1 + 1) (top2Tests z.1.1).length, 0,
        topWinStart (top2Test z.1.1 (min (z.2.2.1.1 + 1) (top2Tests z.1.1).length)),
        top2NormS z.1.1.1.1.1 (top1Join (z.1.1.1.1.1, z.2.2.1.2.2.2,
          topLiftFinish (z.1.1.1.1.1, topLiftPrepare (top2Test z.1.1 z.2.2.1.1), z.2.2.2))))
        : Top2State)) :=
    hmin.pair ((polyFun_const 0).pair (hstart.pair hnormJoin))
  exact (PolyFun.ite hgo hA hB).of_eq (fun z => by
    rw [top2Combine]
    by_cases h : z.2.2.2.isSome = true ∧ z.2.2.1.2.1 + 1 < (top2Wins z.1.1).length
    · rw [if_pos ((top2GoChain_eq_true z).2 h), if_pos h]
    · rw [if_neg (fun hcon => h ((top2GoChain_eq_true z).1 hcon)), if_neg h])

theorem polyFun_top2Finish {solve : RawWinSI → RawCoset} (hs : PolyFun solve) :
    PolyFun (top2Finish solve) := by
  have hacc : PolyFun (fun z : RawTop2Node × Top2State => z.2.2.2.2.getD (none : RawCoset)) :=
    (((polyFun_snd.comp polyFun_snd).comp polyFun_snd).comp polyFun_snd).pair
      (polyFun_const (none : RawCoset)) |>.comp polyFun_optionGetD
  exact ((((polyFun_fst.comp polyFun_snd).pair polyFun_id).comp
    (PolyFun.optionElim hacc (polyFun_fst.comp hs)))).of_eq (fun z => by
      cases hoz : z.1.2 <;> simp [top2Finish, hoz])

/-- The same for a solver that is only quasipolynomial, which is the case of Sec. 15. -/
theorem quasiPolyFun_top2Finish {solve : RawWinSI → RawCoset} (hs : QuasiPolyFun solve) :
    QuasiPolyFun (top2Finish solve) := by
  have hacc : PolyFun (fun z : RawTop2Node × Top2State => z.2.2.2.2.getD (none : RawCoset)) :=
    (((polyFun_snd.comp polyFun_snd).comp polyFun_snd).comp polyFun_snd).pair
      (polyFun_const (none : RawCoset)) |>.comp polyFun_optionGetD
  exact ((((polyFun_fst.comp polyFun_snd).pair polyFun_id).comp_quasi
    (QuasiPolyFun.optionElim hacc.quasiPolyFun (polyFun_fst.comp_quasi hs)))).of_eq
      (fun z => by cases hoz : z.1.2 <;> simp [top2Finish, hoz])

/-! ### The size bound

Everything the round stores is normalised — `Algo.topWinStart` tidies its generators,
`Algo.top2NormC` and `Algo.top2NormS` rewrite an answer in the normal form of
`Algo.rawRightTranslate` — so the state is bounded by `Algo.chainBound` of the domain.  What
does grow with the instance is the pair of strings of a window instance: it is the output of
a `RAM.PolyFun` applied to the top node together with an index below the number of top
tests, and that is what `Algo.top2Str` bounds. -/

/-- A natural is smaller than its successor's encoding. -/
theorem size_nat_le_self (k : ℕ) : Enc.size k ≤ k + 2 := by
  have h1 : Enc.size k = Nat.size k + 2 := Small.size_nat k
  have h2 : Nat.size k ≤ k := size_le_self k
  omega

/-- A four-component state costs at most eight times its components. -/
theorem size_top2State_le (s : Top2State) :
    Enc.size s ≤ 2 * Enc.size s.1 + 4 * Enc.size s.2.1 + 8 * Enc.size s.2.2.1
      + 8 * Enc.size s.2.2.2 := by
  have h1 : Enc.size s ≤ 2 * Enc.size s.1 + 2 * Enc.size s.2 := Combine.size_pair_le _ _
  have h2 : Enc.size s.2 ≤ 2 * Enc.size s.2.1 + 2 * Enc.size s.2.2 := Combine.size_pair_le _ _
  have h3 : Enc.size s.2.2 ≤ 2 * Enc.size s.2.2.1 + 2 * Enc.size s.2.2.2 :=
    Combine.size_pair_le _ _
  omega

theorem chainBound_ge (m : ℕ) : 16 * (m + 1) ≤ chainBound m := by
  have h : chainBound m = 16 * (gensBound m + m + 1) := rfl
  omega

/-- **A window instance of the round is small.**  `Algo.size_winSI_le` asks in addition that
the window is invariant under the generators, which the round does not check of its own
leaves. -/
theorem size_top2LeafWF_le {n m : ℕ} {W : RawWinSI} (hW : Top2LeafWF n W) (hm : n ≤ m)
    (hs : Enc.size W.2.2.2 ≤ m) : Enc.size W ≤ chainBound m := by
  have hwin : Enc.size W.1 ≤ strBound m :=
    size_natList_le (le_trans (length_le_of_nodup_lt hW.2.2.1 hW.2.2.2.1) hm)
      (fun a ha => lt_of_lt_of_le (hW.2.2.2.1 a ha) hm)
  have hgens : Enc.size W.2.1 ≤ gensBound m :=
    size_gens_le' (n := n) hm hW.2.2.2.2.1 hW.2.2.2.2.2.1
  have hrep : Enc.size W.2.2.1 ≤ strBound m :=
    size_perm_le' (n := n) hm hW.2.2.2.2.2.2
  have hp1 : Enc.size W ≤ 2 * Enc.size W.1 + 2 * Enc.size W.2 := Combine.size_pair_le _ _
  have hp2 : Enc.size W.2 ≤ 2 * Enc.size W.2.1 + 2 * Enc.size W.2.2 := Combine.size_pair_le _ _
  have hp3 : Enc.size W.2.2 ≤ 2 * Enc.size W.2.2.1 + 2 * Enc.size W.2.2.2 :=
    Combine.size_pair_le _ _
  have hSG := strBound_le_gensBound m
  have hb : chainBound m = 16 * (gensBound m + m + 1) := rfl
  omega

/-- The size the two strings of a window instance can reach, in terms of the size bound `D`
of the routine that computes them and the size bound `T` of the list of top tests. -/
def top2Str (D T : ℕ → ℕ) (m : ℕ) : ℕ := D (2 * m + 2 * (T m + 4)) + m

/-- **The size bound of the window round.** -/
def top2Bound (D T K : ℕ → ℕ) (m : ℕ) : ℕ :=
  16 * (chainBound (top2Str D T m) + T m + K m + 8)

theorem le_top2Str (D T : ℕ → ℕ) (m : ℕ) : m ≤ top2Str D T m := by
  rw [top2Str]; omega

theorem mono_top2Str {D T : ℕ → ℕ} (hD : ∀ a b, a ≤ b → D a ≤ D b)
    (hT : ∀ a b, a ≤ b → T a ≤ T b) : Monotone (top2Str D T) := by
  intro a b hab
  have h1 : 2 * a + 2 * (T a + 4) ≤ 2 * b + 2 * (T b + 4) := by
    have := hT a b hab; omega
  have h2 := hD _ _ h1
  rw [top2Str, top2Str]; omega

theorem mono_top2Bound {D T K : ℕ → ℕ} (hD : ∀ a b, a ≤ b → D a ≤ D b)
    (hT : ∀ a b, a ≤ b → T a ≤ T b) (hK : ∀ a b, a ≤ b → K a ≤ K b) :
    Monotone (top2Bound D T K) := by
  intro a b hab
  have h1 := mono_chainBound (mono_top2Str hD hT hab)
  have h2 := hT a b hab
  have h3 := hK a b hab
  rw [top2Bound, top2Bound]; omega

theorem polyBound_top2Bound {D T K : ℕ → ℕ} (hD : PolyBound D) (hT : PolyBound T)
    (hK : PolyBound K) : PolyBound (top2Bound D T K) := by
  have hE : PolyBound (fun m => 2 * m + 2 * (T m + 4)) :=
    ((polyBound_const 2).mul polyBound_id).add
      ((polyBound_const 2).mul (hT.add (polyBound_const 4)))
  have hS : PolyBound (top2Str D T) := (hD.comp hE).add polyBound_id
  exact (polyBound_const 16).mul
    ((((polyBound_chainBound.comp hS).add hT).add hK).add (polyBound_const 8))

/-- **The cost data of the window round (Cor. 12.0.6).**  The solver is charged for: it has
to be a `RAM.QuasiPolyFun` and to answer within the bound of the Chain Rule round, which is
exactly what `Algo.chainCost` guarantees of it. -/
def top2CostOf (n : ℕ) (solve : RawWinSI → RawCoset)
    (hsolve : QuasiPolyFun solve)
    (hsize : ∀ W, Top2LeafWF n W → Enc.size (solve W) ≤ chainBound (Enc.size W.2.2.2))
    (D T K : ℕ → ℕ)
    (hDb : PolyBound D) (hDm : ∀ a b : ℕ, a ≤ b → D a ≤ D b)
    (hD : ∀ z : RawTop1 × ℕ,
      Enc.size ((topWinSrc (top2Test z.1 z.2), topWinTgt (top2Test z.1 z.2)) : RawStr × RawStr)
        ≤ D (Enc.size z))
    (hTb : PolyBound T) (hTm : ∀ a b : ℕ, a ≤ b → T a ≤ T b)
    (hT : ∀ p : RawTop1, Enc.size (top2Tests p) ≤ T (Enc.size p))
    (hKb : PolyBound K) (hKm : ∀ a b : ℕ, a ≤ b → K a ≤ K b)
    (hK : ∀ p : RawTop1, Enc.size (top2Wins p) ≤ K (Enc.size p)) :
    Round.Cost (top2Round n solve) := by
  -- the domain fits inside the instance
  have hn_le : ∀ I : RawTop2Node, Top2WF n I → n ≤ Enc.size I.1 := by
    intro I hI
    have h1 : I.1.1.1.1.length ≤ Enc.size I.1.1.1.1 := length_le_size _
    have h2 : Enc.size I.1.1.1.1 ≤ Enc.size I.1.1.1 := size_fst_le' _
    have h3 : Enc.size I.1.1.1 ≤ Enc.size I.1.1 := size_fst_le' _
    have h4 : Enc.size I.1.1 ≤ Enc.size I.1 := size_fst_le' _
    rw [← hI.2.1]; omega
  have htests : ∀ p : RawTop1, (top2Tests p).length ≤ T (Enc.size p) := fun p =>
    le_trans (length_le_size _) (hT p)
  have hwins : ∀ p : RawTop1, (top2Wins p).length ≤ K (Enc.size p) := fun p =>
    le_trans (length_le_size _) (hK p)
  -- the two strings of the `t`-th test
  have hstr : ∀ (p : RawTop1) (t : ℕ), t < (top2Tests p).length →
      Enc.size ((topWinSrc (top2Test p t), topWinTgt (top2Test p t)) : RawStr × RawStr)
        ≤ top2Str D T (Enc.size p) := by
    intro p t ht
    have h1 : Enc.size ((p, t) : RawTop1 × ℕ) ≤ 2 * Enc.size p + 2 * Enc.size t :=
      Combine.size_pair_le _ _
    have h2 := size_nat_le_self t
    have h3 : t ≤ T (Enc.size p) := by have := htests p; omega
    have h5 : Enc.size ((p, t) : RawTop1 × ℕ)
        ≤ 2 * Enc.size p + 2 * (T (Enc.size p) + 4) := by omega
    have h6 : Enc.size ((topWinSrc (top2Test p t), topWinTgt (top2Test p t)) : RawStr × RawStr)
        ≤ D (Enc.size ((p, t) : RawTop1 × ℕ)) := hD (p, t)
    have h7 := hDm _ _ h5
    have h8 : top2Str D T (Enc.size p)
        = D (2 * Enc.size p + 2 * (T (Enc.size p) + 4)) + Enc.size p := rfl
    omega
  have hleaf : ∀ (p : RawTop1) (t i : ℕ) (c : RawGens × RawPerm), n ≤ Enc.size p →
      p.1.1.1.length = n → t < (top2Tests p).length →
      Enc.size (top2Leaf p t i c) ≤ chainBound (top2Str D T (Enc.size p)) := by
    intro p t i c hn hd ht
    exact size_top2LeafWF_le (top2LeafWF_leaf hd t i c) (le_trans hn (le_top2Str D T _))
      (hstr p t ht)
  have hsolveleaf : ∀ (p : RawTop1) (t i : ℕ) (c : RawGens × RawPerm), p.1.1.1.length = n →
      t < (top2Tests p).length →
      Enc.size (solve (top2Leaf p t i c)) ≤ chainBound (top2Str D T (Enc.size p)) := by
    intro p t i c hd ht
    exact le_trans (hsize _ (top2LeafWF_leaf hd t i c)) (mono_chainBound (hstr p t ht))
  refine
    { bound := top2Bound D T K
      polyBound_bound := polyBound_top2Bound hDb hTb hKb
      mono_bound := mono_top2Bound hDm hTm hKm
      widthBound := fun m => T m * K m
      quasiPolyBound_widthBound := (hTb.mul hKb).quasiPoly
      quasiPolyFun_child := polyFun_top2Child.quasiPolyFun
      quasiPolyFun_init := ?_
      quasiPolyFun_combine := polyFun_top2Combine.quasiPolyFun
      quasiPolyFun_finish := quasiPolyFun_top2Finish hsolve
      ground_le := fun I => size_fst_le' I
      size_le := ?_
      init_le := ?_
      combine_le := ?_
      finish_le := ?_
      bot_le := ?_
      width_le := ?_ }
  · show QuasiPolyFun (fun I : RawTop2Node =>
      ((0, 0, topWinStart (top2Test I.1 0), (some none : Top1State)) : Top2State))
    exact ((polyFun_const 0).pair ((polyFun_const 0).pair
      ((((polyFun_fst.pair (polyFun_const 0)).comp polyFun_top2Test).comp
        polyFun_topWinStart).pair
          (polyFun_const (some none : Top1State))))).quasiPolyFun
  · -- `size_le`
    intro I hI
    show Enc.size I ≤ top2Bound D T K (Enc.size I.1)
    have hm := hn_le I hI
    have hp : Enc.size I ≤ 2 * Enc.size I.1 + 2 * Enc.size I.2 := Combine.size_pair_le _ _
    have hcb := chainBound_ge (top2Str D T (Enc.size I.1))
    have hst := le_top2Str D T (Enc.size I.1)
    have hbd : top2Bound D T K (Enc.size I.1)
        = 16 * (chainBound (top2Str D T (Enc.size I.1)) + T (Enc.size I.1)
            + K (Enc.size I.1) + 8) := rfl
    rcases ho : I.2 with _ | W
    · have h2 : Enc.size I.2 = 2 := by rw [ho]; exact size_none
      omega
    · obtain ⟨t, i, c, ht, hWeq⟩ := hI.2.2 W ho
      have h1 : Enc.size I.2 = Enc.size W + 2 := by rw [ho]; exact size_some_eq _
      have h2 : Enc.size W ≤ chainBound (top2Str D T (Enc.size I.1)) := by
        rw [hWeq]; exact hleaf I.1 t i c hm hI.2.1 ht
      omega
  · -- `init_le`
    intro I hI
    show Enc.size ((0, 0, topWinStart (top2Test I.1 0), (some none : Top1State)) : Top2State)
      ≤ top2Bound D T K (Enc.size I.1)
    have hm := hn_le I hI
    have hcb := chainBound_ge (top2Str D T (Enc.size I.1))
    have hst := le_top2Str D T (Enc.size I.1)
    have hcbm : chainBound (Enc.size I.1) ≤ chainBound (top2Str D T (Enc.size I.1)) :=
      mono_chainBound hst
    have hbd : top2Bound D T K (Enc.size I.1)
        = 16 * (chainBound (top2Str D T (Enc.size I.1)) + T (Enc.size I.1)
            + K (Enc.size I.1) + 8) := rfl
    have h0 := size_nat_le_self 0
    have hsn : Enc.size (some none : Top1State) = Enc.size (none : RawCoset) + 2 :=
      size_some_eq _
    have hnn : Enc.size (none : RawCoset) = 2 := size_none
    have hstart : Enc.size (topWinStart (top2Test I.1 0)) ≤ chainBound (Enc.size I.1) :=
      size_topWinStart_le (by rw [top2Test_dom]; exact hI.2.1) hm
    have hs := size_top2State_le
      ((0, 0, topWinStart (top2Test I.1 0), (some none : Top1State)) : Top2State)
    dsimp only at hs
    omega
  · -- `combine_le`
    intro I j s a hI _ _
    show Enc.size (top2Combine (I, j, s, a)) ≤ top2Bound D T K (Enc.size I.1)
    have hm := hn_le I hI
    have hd : I.1.1.1.1.length = n := hI.2.1
    have hcb := chainBound_ge (top2Str D T (Enc.size I.1))
    have hst := le_top2Str D T (Enc.size I.1)
    have hcbm : chainBound (Enc.size I.1) ≤ chainBound (top2Str D T (Enc.size I.1)) :=
      mono_chainBound hst
    have hbd : top2Bound D T K (Enc.size I.1)
        = 16 * (chainBound (top2Str D T (Enc.size I.1)) + T (Enc.size I.1)
            + K (Enc.size I.1) + 8) := rfl
    have hT' := htests I.1
    have hK' := hwins I.1
    have hnormS := size_top2NormS_le hd hm s.2.2.2
    have hjoinS := size_top2NormS_le hd hm
      (top1Join (I.1.1.1.1, s.2.2.2,
        topLiftFinish (I.1.1.1.1, topLiftPrepare (top2Test I.1 s.1), a)))
    have hnormC := size_top2NormC_le hd hm a
    rw [top2Combine]
    dsimp only
    by_cases hg : a.isSome = true ∧ s.2.1 + 1 < (top2Wins I.1).length
    · rw [if_pos hg]
      have hs := size_top2State_le ((min s.1 (top2Tests I.1).length,
        min (s.2.1 + 1) (top2Wins I.1).length, top2NormC I.1.1.1.1 a,
        top2NormS I.1.1.1.1 s.2.2.2) : Top2State)
      dsimp only at hs
      have h1 := size_nat_le_self (min s.1 (top2Tests I.1).length)
      have h2 := size_nat_le_self (min (s.2.1 + 1) (top2Wins I.1).length)
      have h3 : min s.1 (top2Tests I.1).length ≤ (top2Tests I.1).length := Nat.min_le_right _ _
      have h4 : min (s.2.1 + 1) (top2Wins I.1).length ≤ (top2Wins I.1).length :=
        Nat.min_le_right _ _
      omega
    · rw [if_neg hg]
      have hs := size_top2State_le ((min (s.1 + 1) (top2Tests I.1).length, 0,
        topWinStart (top2Test I.1 (min (s.1 + 1) (top2Tests I.1).length)),
        top2NormS I.1.1.1.1 (top1Join (I.1.1.1.1, s.2.2.2,
          topLiftFinish (I.1.1.1.1, topLiftPrepare (top2Test I.1 s.1), a)))) : Top2State)
      dsimp only at hs
      have h1 := size_nat_le_self (min (s.1 + 1) (top2Tests I.1).length)
      have h3 : min (s.1 + 1) (top2Tests I.1).length ≤ (top2Tests I.1).length :=
        Nat.min_le_right _ _
      have h0 := size_nat_le_self 0
      have hstart : Enc.size (topWinStart
          (top2Test I.1 (min (s.1 + 1) (top2Tests I.1).length)))
            ≤ chainBound (Enc.size I.1) :=
        size_topWinStart_le (by rw [top2Test_dom]; exact hd) hm
      omega
  · -- `finish_le`
    intro I s hI hs
    have hgr : (top2Round n solve).ground I = Enc.size I.1 := rfl
    rw [hgr] at hs
    show Enc.size (top2Finish solve (I, s)) ≤ top2Bound D T K (Enc.size I.1)
    have hm := hn_le I hI
    have hcb := chainBound_ge (top2Str D T (Enc.size I.1))
    have hbd : top2Bound D T K (Enc.size I.1)
        = 16 * (chainBound (top2Str D T (Enc.size I.1)) + T (Enc.size I.1)
            + K (Enc.size I.1) + 8) := rfl
    rcases ho : I.2 with _ | W
    · have he : top2Finish solve (I, s) = s.2.2.2.getD none := by
        rw [top2Finish, ho]; rfl
      have h1 : ∀ o : Top1State, Enc.size (o.getD (none : RawCoset)) ≤ Enc.size o := by
        intro o
        cases o with
        | none => rw [Option.getD_none, size_none, size_none]
        | some c => rw [Option.getD_some, size_some_eq]; omega
      have h2 : Enc.size s.2.2.2 ≤ Enc.size s.2.2 := size_snd_le' _
      have h3 : Enc.size s.2.2 ≤ Enc.size s.2 := size_snd_le' _
      have h4 : Enc.size s.2 ≤ Enc.size s := size_snd_le' _
      have h5 := h1 s.2.2.2
      rw [he]
      omega
    · obtain ⟨t, i, c, ht, hWeq⟩ := hI.2.2 W ho
      have he : top2Finish solve (I, s) = solve W := by rw [top2Finish, ho]; rfl
      have h2 : Enc.size (solve W) ≤ chainBound (top2Str D T (Enc.size I.1)) := by
        rw [hWeq]; exact hsolveleaf I.1 t i c hI.2.1 ht
      rw [he]
      omega
  · -- `bot_le`
    intro m
    have hcb := chainBound_ge (top2Str D T m)
    have hbd : top2Bound D T K m
        = 16 * (chainBound (top2Str D T m) + T m + K m + 8) := rfl
    show Enc.size (none : RawCoset) ≤ top2Bound D T K m
    rw [size_none]
    omega
  · -- `width_le`
    intro I hI
    show I.2.elim ((top2Tests I.1).length * (top2Wins I.1).length) (fun _ => 0)
      ≤ T (Enc.size I.1) * K (Enc.size I.1)
    rcases ho : I.2 with _ | W
    · exact Nat.mul_le_mul (htests I.1) (hwins I.1)
    · exact Nat.zero_le _

/-- The size bound of the routine that computes the two strings of a window instance. -/
private theorem top2SB_str : ∃ S : ℕ → ℕ, PolyBound S ∧ (∀ a b : ℕ, a ≤ b → S a ≤ S b) ∧
    ∀ z : RawTop1 × ℕ,
      Enc.size ((topWinSrc (top2Test z.1 z.2), topWinTgt (top2Test z.1 z.2)) : RawStr × RawStr)
        ≤ S (Enc.size z) :=
  SizeBound.exists_polyBound
    (polyFun_top2Test.comp (polyFun_topWinSrc.pair polyFun_topWinTgt)).size

/-- The size bound of the routine that lists the top tests. -/
private theorem top2SB_tests : ∃ S : ℕ → ℕ, PolyBound S ∧ (∀ a b : ℕ, a ≤ b → S a ≤ S b) ∧
    ∀ p : RawTop1, Enc.size (top2Tests p) ≤ S (Enc.size p) :=
  SizeBound.exists_polyBound polyFun_top2Tests.size

/-- The size bound of the routine that lists the orbits of the kernel. -/
private theorem top2SB_wins : ∃ S : ℕ → ℕ, PolyBound S ∧ (∀ a b : ℕ, a ≤ b → S a ≤ S b) ∧
    ∀ p : RawTop1, Enc.size (top2Wins p) ≤ S (Enc.size p) :=
  SizeBound.exists_polyBound polyFun_top2Wins.size

/-- **Cor. 12.0.6: the window round is paid for.**  The bounds of the three routines that
read the instance are the ones `RAM.PolyFun` carries. -/
noncomputable def top2Cost (n : ℕ) (solve : RawWinSI → RawCoset)
    (hsolve : QuasiPolyFun solve)
    (hsize : ∀ W, Top2LeafWF n W → Enc.size (solve W) ≤ chainBound (Enc.size W.2.2.2)) :
    Round.Cost (top2Round n solve) :=
  top2CostOf n solve hsolve hsize
    top2SB_str.choose top2SB_tests.choose top2SB_wins.choose
    top2SB_str.choose_spec.1 top2SB_str.choose_spec.2.1 top2SB_str.choose_spec.2.2
    top2SB_tests.choose_spec.1 top2SB_tests.choose_spec.2.1 top2SB_tests.choose_spec.2.2
    top2SB_wins.choose_spec.1 top2SB_wins.choose_spec.2.1 top2SB_wins.choose_spec.2.2

end Cost

end Algo
