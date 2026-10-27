import Workspace.Algo.TopWindowRound

/-!
# Sec. 12, Proposition 12.0.5: the cost of the top round

`Workspace/Algo/TopRound.lean` (A12 session 2) builds `Algo.top1Round`, the round of
Prop. 12.0.5: the `|S| + 1` top tests, each turned into a full-window instance for the
kernel `N` by `Babai.Proposition_12_0_1_lifting`, their answers translated back by the
computed lift and joined by Eq. (62).  What it does not carry is the `Algo.Round.Cost`:
the four routines are `RAM.PolyFun`, but the size bounds — one polynomial bounding the
instance, the state and the answer in terms of the size of the top node — were left open.

This file supplies them.  Two observations do the work.

* A child of the top node is `Algo.topLiftChild (Algo.top1Request (p, j))` with
  `j < |top1Inputs p|`, which is recorded in `Algo.Top1WF`; it is therefore the value of a
  `RAM.PolyFun` at the top node paired with an index that is itself bounded by the size of
  the top node, so it is polynomially small (`Algo.top2Str`, reused from
  `Workspace/Algo/TopWindowRound.lean`).
* The state never grows.  `Algo.top1Combine` joins the accumulator with an answer that has
  been *right translated* first, and `Algo.rawRightTranslate` returns at most `n²`
  well-formed generators with a well-formed representative; `Algo.rawCosetJoin` with a
  second argument of that shape returns a coset of the same kind.  So the state is bounded
  by `Algo.chainBound` of the domain, whatever the answers of the children are.

## Main definitions

* `Algo.top1Bound` — the size bound;
* `Algo.top1Cost` — **the cost data of `Algo.top1Round`** (Prop. 12.0.5).

No axiom, no `sorry`.
-/

namespace Algo

open RAM RAM.Targets
open Equiv (Perm)

/-! ## Sizes that do not grow -/

/-- **A right translated answer is small**, whatever the answer was: `Algo.rawRightTranslate`
tidies the generators and normalises the representative. -/
theorem size_rawRightTranslate_le {n m : ℕ} {dom : List ℕ} (hd : dom.length = n) (hm : n ≤ m)
    (r : RawPerm) (c : RawCoset) :
    Enc.size (rawRightTranslate (dom, r, c)) ≤ chainBound m := by
  have h0 := chainBound_ge m
  rcases h : rawRightTranslate (dom, r, c) with _ | ⟨gs, ρ⟩
  · rw [size_none]; omega
  · obtain ⟨hw, hl, hr⟩ := rawRightTranslate_wf hd r c h
    exact size_coset_le' (n := n) hm hw hl hr

/-- The answer of a top test, translated back by the computed lift, is small. -/
theorem size_topLiftFinish_le {n m : ℕ} {dom : List ℕ} (hd : dom.length = n) (hm : n ≤ m)
    (prep : Option TopLiftPlan) (a : RawCoset) :
    Enc.size (topLiftFinish (dom, prep, a)) ≤ chainBound m := by
  have h0 := chainBound_ge m
  cases prep with
  | none => show Enc.size (none : RawCoset) ≤ _; rw [size_none]; omega
  | some q =>
      show Enc.size (rawRightTranslate (dom, q.1, a)) ≤ _
      exact size_rawRightTranslate_le hd hm q.1 a

/-- **The join with a small second argument is small**, whatever the first argument is.
`Algo.size_rawCosetJoin_le` bounds the join by a bound on *both* arguments; here the second
one is a coset, so the join is either that coset or a freshly shortened one. -/
theorem size_rawCosetJoin_some_le {n m : ℕ} {x : RawStr} (hx : x.length = n) (hm : n ≤ m)
    (c : RawCoset) (q : RawGens × RawPerm)
    (hq : Enc.size (some q : RawCoset) ≤ chainBound m) :
    Enc.size (rawCosetJoin (x, c, some q)) ≤ chainBound m := by
  match c, q with
  | none, q => exact hq
  | some (M, τ), (N, ρ) =>
      have hallwf : RawGens.WF n (normGens (x, M) ++ normGens (x, N)
          ++ [rawMul (rawInv (normPerm (x, τ)), normPerm (x, ρ))]) := by
        intro g hg
        rcases List.mem_append.1 hg with hg | hg
        · rcases List.mem_append.1 hg with hg | hg
          · exact wf_normGens hx M g hg
          · exact wf_normGens hx N g hg
        · rw [List.mem_singleton.1 hg]
          exact wf_rawMul (wf_rawInv (wf_normPerm hx τ)) (wf_normPerm hx ρ)
      exact size_coset_le' (n := n) hm (rawShorten_wf hx hallwf)
        (length_rawShorten_wf hx hallwf) (wf_normPerm hx τ)

/-- **The accumulator of Prop. 12.0.5 does not grow.**  Eq. (62) joins it with an answer
that `Algo.topLiftFinish` has already normalised. -/
theorem size_top1Join_le {n m : ℕ} {dom : List ℕ} (hd : dom.length = n) (hm : n ≤ m)
    (s : Top1State) {c : RawCoset} (hc : Enc.size c ≤ chainBound m) :
    Enc.size (top1Join (dom, s, c)) ≤ chainBound m + 2 := by
  have h0 := chainBound_ge m
  cases s with
  | none => show Enc.size (none : Top1State) ≤ _; rw [size_none]; omega
  | some s' =>
      cases c with
      | none => show Enc.size (none : Top1State) ≤ _; rw [size_none]; omega
      | some q =>
          show Enc.size (some (rawCosetJoin (dom, s', some q)) : Top1State) ≤ _
          rw [size_some_eq]
          have h1 := size_rawCosetJoin_some_le hd hm s' q hc
          omega

/-! ## The bound -/

/-- **The size bound of the top round** (Prop. 12.0.5).  `D` bounds the size of a computed
kernel child, `T` the size of the list of top tests, and `S` the size of the answer the
solver returns for a child. -/
def top1Bound (D T S : ℕ → ℕ) (m : ℕ) : ℕ :=
  16 * (chainBound (top2Str D T m) + S (top2Str D T m) + T m + 8)

theorem mono_top1Bound {D T S : ℕ → ℕ} (hD : ∀ a b : ℕ, a ≤ b → D a ≤ D b)
    (hT : ∀ a b : ℕ, a ≤ b → T a ≤ T b) (hS : ∀ a b : ℕ, a ≤ b → S a ≤ S b) :
    Monotone (top1Bound D T S) := by
  intro a b hab
  have h0 := mono_top2Str hD hT hab
  have h1 := mono_chainBound h0
  have h2 := hS _ _ h0
  have h3 := hT a b hab
  rw [top1Bound, top1Bound]; omega

theorem polyBound_top1Bound {D T S : ℕ → ℕ} (hD : PolyBound D) (hT : PolyBound T)
    (hS : PolyBound S) : PolyBound (top1Bound D T S) := by
  have hE : PolyBound (fun m => 2 * m + 2 * (T m + 4)) :=
    ((polyBound_const 2).mul polyBound_id).add
      ((polyBound_const 2).mul (hT.add (polyBound_const 4)))
  have hSt : PolyBound (top2Str D T) := (hD.comp hE).add polyBound_id
  exact (polyBound_const 16).mul
    ((((polyBound_chainBound.comp hSt).add (hS.comp hSt)).add hT).add (polyBound_const 8))

/-! ## The cost -/

/-- The quasipolynomial form of `Algo.polyFun_top1Finish`. -/
theorem quasiPolyFun_top1Finish {solve : RawSI → RawCoset} (hs : QuasiPolyFun solve) :
    QuasiPolyFun (top1Finish solve) := by
  have hd : PolyFun (fun p : RawTop1Node × Top1State => p.2.getD (none : RawCoset)) :=
    (polyFun_snd.pair (polyFun_const none)).comp polyFun_optionGetD
  exact ((((polyFun_fst.comp polyFun_snd).pair polyFun_id).comp_quasi
    (QuasiPolyFun.optionElim hd.quasiPolyFun (polyFun_fst.comp_quasi hs)))).of_eq
      (fun _ => rfl)

/-- **The cost data of the top round (Prop. 12.0.5)**, with the bounds of the two routines
that read the instance and of the solver supplied as data. -/
def top1CostOf (n : ℕ) (solve : RawSI → RawCoset) (hsolve : QuasiPolyFun solve)
    (D T S : ℕ → ℕ)
    (hDb : PolyBound D) (hDm : ∀ a b : ℕ, a ≤ b → D a ≤ D b)
    (hD : ∀ z : RawTop1 × ℕ, Enc.size (topLiftChild (top1Request z)) ≤ D (Enc.size z))
    (hTb : PolyBound T) (hTm : ∀ a b : ℕ, a ≤ b → T a ≤ T b)
    (hT : ∀ p : RawTop1, Enc.size (top1Inputs p) ≤ T (Enc.size p))
    (hSb : PolyBound S) (hSm : ∀ a b : ℕ, a ≤ b → S a ≤ S b)
    (hS : ∀ q : RawSI, Enc.size (solve q) ≤ S (Enc.size q)) :
    Round.Cost (top1Round n solve) := by
  have hn_le : ∀ I : RawTop1Node, Top1WF n I → n ≤ Enc.size I.1 := by
    intro I hI
    have h1 : I.1.1.1.1.length ≤ Enc.size I.1.1.1.1 := length_le_size _
    have h2 : Enc.size I.1.1.1.1 ≤ Enc.size I.1.1.1 := size_fst_le' _
    have h3 : Enc.size I.1.1.1 ≤ Enc.size I.1.1 := size_fst_le' _
    have h4 : Enc.size I.1.1 ≤ Enc.size I.1 := size_fst_le' _
    rw [← hI.1]; omega
  have htests : ∀ p : RawTop1, (top1Inputs p).length ≤ T (Enc.size p) := fun p =>
    le_trans (length_le_size _) (hT p)
  -- a computed child is small
  have hchild : ∀ (p : RawTop1) (j : ℕ), j < (top1Inputs p).length →
      Enc.size (topLiftChild (top1Request (p, j))) ≤ top2Str D T (Enc.size p) := by
    intro p j hj
    have h1 : Enc.size ((p, j) : RawTop1 × ℕ) ≤ 2 * Enc.size p + 2 * Enc.size j :=
      Combine.size_pair_le _ _
    have h2 := size_nat_le_self j
    have h3 : j ≤ T (Enc.size p) := by have := htests p; omega
    have h5 : Enc.size ((p, j) : RawTop1 × ℕ)
        ≤ 2 * Enc.size p + 2 * (T (Enc.size p) + 4) := by omega
    have h6 : Enc.size (topLiftChild (top1Request ((p, j) : RawTop1 × ℕ)))
        ≤ D (Enc.size ((p, j) : RawTop1 × ℕ)) := hD (p, j)
    have h7 := hDm _ _ h5
    have h8 : top2Str D T (Enc.size p)
        = D (2 * Enc.size p + 2 * (T (Enc.size p) + 4)) + Enc.size p := rfl
    omega
  refine
    { bound := top1Bound D T S
      polyBound_bound := polyBound_top1Bound hDb hTb hSb
      mono_bound := mono_top1Bound hDm hTm hSm
      widthBound := T
      quasiPolyBound_widthBound := hTb.quasiPoly
      quasiPolyFun_child := polyFun_top1Child.quasiPolyFun
      quasiPolyFun_init := (polyFun_const (some none : Top1State)).quasiPolyFun
      quasiPolyFun_combine := polyFun_top1Combine.quasiPolyFun
      quasiPolyFun_finish := quasiPolyFun_top1Finish hsolve
      ground_le := fun I => size_fst_le' I
      size_le := ?_
      init_le := ?_
      combine_le := ?_
      finish_le := ?_
      bot_le := ?_
      width_le := ?_ }
  · -- `size_le`
    intro I hI
    show Enc.size I ≤ top1Bound D T S (Enc.size I.1)
    have hm := hn_le I hI
    have hp : Enc.size I ≤ 2 * Enc.size I.1 + 2 * Enc.size I.2 := Combine.size_pair_le _ _
    have hcb := chainBound_ge (top2Str D T (Enc.size I.1))
    have hst := le_top2Str D T (Enc.size I.1)
    have hbd : top1Bound D T S (Enc.size I.1)
        = 16 * (chainBound (top2Str D T (Enc.size I.1)) + S (top2Str D T (Enc.size I.1))
            + T (Enc.size I.1) + 8) := rfl
    rcases ho : I.2 with _ | q
    · have h2 : Enc.size I.2 = 2 := by rw [ho]; exact size_none
      omega
    · obtain ⟨j, hj, hq⟩ := hI.2 q ho
      have h1 : Enc.size I.2 = Enc.size q + 2 := by rw [ho]; exact size_some_eq _
      have h2 : Enc.size q ≤ top2Str D T (Enc.size I.1) := by
        rw [hq]; exact hchild I.1 j hj
      omega
  · -- `init_le`
    intro I hI
    have hcb := chainBound_ge (top2Str D T (Enc.size I.1))
    have hbd : top1Bound D T S (Enc.size I.1)
        = 16 * (chainBound (top2Str D T (Enc.size I.1)) + S (top2Str D T (Enc.size I.1))
            + T (Enc.size I.1) + 8) := rfl
    show Enc.size (some none : Top1State) ≤ top1Bound D T S (Enc.size I.1)
    have h1 : Enc.size (some none : Top1State) = Enc.size (none : RawCoset) + 2 :=
      size_some_eq _
    have h2 : Enc.size (none : RawCoset) = 2 := size_none
    omega
  · -- `combine_le`
    intro I j s a hI _ _
    show Enc.size (top1Combine (I, j, s, a)) ≤ top1Bound D T S (Enc.size I.1)
    have hm := hn_le I hI
    have hcb := chainBound_ge (top2Str D T (Enc.size I.1))
    have hst := le_top2Str D T (Enc.size I.1)
    have hcbm : chainBound (Enc.size I.1) ≤ chainBound (top2Str D T (Enc.size I.1)) :=
      mono_chainBound hst
    have hbd : top1Bound D T S (Enc.size I.1)
        = 16 * (chainBound (top2Str D T (Enc.size I.1)) + S (top2Str D T (Enc.size I.1))
            + T (Enc.size I.1) + 8) := rfl
    have hfin := size_topLiftFinish_le hI.1 hm
      (topLiftPrepare (top1Request (I.1, j))) a
    have hjoin := size_top1Join_le hI.1 hm s hfin
    show Enc.size (top1Join (I.1.1.1.1, s,
      topLiftFinish (I.1.1.1.1, topLiftPrepare (top1Request (I.1, j)), a)))
        ≤ top1Bound D T S (Enc.size I.1)
    omega
  · -- `finish_le`
    intro I s hI hs
    have hgr : (top1Round n solve).ground I = Enc.size I.1 := rfl
    rw [hgr] at hs
    show Enc.size (top1Finish solve (I, s)) ≤ top1Bound D T S (Enc.size I.1)
    have hm := hn_le I hI
    have hcb := chainBound_ge (top2Str D T (Enc.size I.1))
    have hbd : top1Bound D T S (Enc.size I.1)
        = 16 * (chainBound (top2Str D T (Enc.size I.1)) + S (top2Str D T (Enc.size I.1))
            + T (Enc.size I.1) + 8) := rfl
    rcases ho : I.2 with _ | q
    · have he : top1Finish solve (I, s) = s.getD none := by rw [top1Finish, ho]; rfl
      have h1 : Enc.size (s.getD (none : RawCoset)) ≤ Enc.size s := by
        cases s with
        | none => rw [Option.getD_none, size_none, size_none]
        | some c => rw [Option.getD_some, size_some_eq]; omega
      rw [he]
      omega
    · obtain ⟨j, hj, hq⟩ := hI.2 q ho
      have he : top1Finish solve (I, s) = solve q := by rw [top1Finish, ho]; rfl
      have h1 : Enc.size (solve q) ≤ S (Enc.size q) := hS q
      have h2 : Enc.size q ≤ top2Str D T (Enc.size I.1) := by
        rw [hq]; exact hchild I.1 j hj
      have h3 := hSm _ _ h2
      rw [he]
      omega
  · -- `bot_le`
    intro m
    have hcb := chainBound_ge (top2Str D T m)
    have hbd : top1Bound D T S m
        = 16 * (chainBound (top2Str D T m) + S (top2Str D T m) + T m + 8) := rfl
    show Enc.size (none : RawCoset) ≤ top1Bound D T S m
    rw [size_none]
    omega
  · -- `width_le`
    intro I hI
    show I.2.elim (top1Inputs I.1).length (fun _ => 0) ≤ T (Enc.size I.1)
    rcases ho : I.2 with _ | q
    · exact htests I.1
    · exact Nat.zero_le _

/-- The size bound of the routine that computes a kernel child. -/
private theorem top1SB_child : ∃ S : ℕ → ℕ, PolyBound S ∧ (∀ a b : ℕ, a ≤ b → S a ≤ S b) ∧
    ∀ z : RawTop1 × ℕ, Enc.size (topLiftChild (top1Request z)) ≤ S (Enc.size z) :=
  SizeBound.exists_polyBound (polyFun_top1Request.comp polyFun_topLiftChild).size

/-- The size bound of the routine that lists the top tests. -/
private theorem top1SB_tests : ∃ S : ℕ → ℕ, PolyBound S ∧ (∀ a b : ℕ, a ≤ b → S a ≤ S b) ∧
    ∀ p : RawTop1, Enc.size (top1Inputs p) ≤ S (Enc.size p) :=
  SizeBound.exists_polyBound polyFun_top1Inputs.size

/-- **Prop. 12.0.5: the top round is paid for.**  The solver is charged for: it has to be a
`RAM.QuasiPolyFun` and to answer within a polynomial of the size of the instance it is
given. -/
noncomputable def top1Cost (n : ℕ) (solve : RawSI → RawCoset) (hsolve : QuasiPolyFun solve)
    (S : ℕ → ℕ) (hSb : PolyBound S) (hSm : ∀ a b : ℕ, a ≤ b → S a ≤ S b)
    (hS : ∀ q : RawSI, Enc.size (solve q) ≤ S (Enc.size q)) :
    Round.Cost (top1Round n solve) :=
  top1CostOf n solve hsolve top1SB_child.choose top1SB_tests.choose S
    top1SB_child.choose_spec.1 top1SB_child.choose_spec.2.1 top1SB_child.choose_spec.2.2
    top1SB_tests.choose_spec.1 top1SB_tests.choose_spec.2.1 top1SB_tests.choose_spec.2.2
    hSb hSm hS

end Algo
