/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: Theorem 13.1.3 on the RAM.
-/
import Workspace.Algo.LocalCertOracle
import Workspace.Algo.LocalCertStepWith

/-!
# Theorem 13.1.3 on the RAM

> **Theorem 13.1.3** (Local certificates). Let `T ⊆ Γ` where `|T| = t`. … By making `≤ t!n²`
> calls to String Isomorphism problems on domains of size `≤ n/t` and performing `t! poly(n)`
> computation we can decide whether `T` is full and (a) if `T` is full, find a certificate
> `K(T) ≤ Aut_G(x)` of fullness; (b) if `T` is not full, find a certificate `M(T) ≤ S(T)` of
> non-fullness.

The paper counts the calls to String Isomorphism apart from the rest of the computation.  The
statement here does the same.  The calls are answered by an arbitrary program `Q` (any
String Isomorphism routine), and `τ(W)` is the number of steps `Q` takes on the call `W`.
Procedure LocalCertificates is one program `F Q` that runs `Q` on each call.  Its running time
is at most

  `A · ∑_{W ∈ calls} τ(W)  +  t! · poly(input size)`,

with `A` an absolute constant: the calls cost what `Q` takes on them (the factor `A` is the
overhead of the machine's pairing routine around each call), and the rest is
`t! · poly(n)`.  The calls are those of `Algo.lcCallsQ`: at most `t!·n²` of them
(`Algo.length_lcCallsQ_le`), each on a window of at most `n/t` points
(`Algo.window_lcCallsQ_le`).  The answers of `Q` are only asked to be polynomially small in
the instance (the polynomial `S`); the procedure normalizes them.

## Main results

* `Algo.exists_chainProg`, `Algo.exists_recomputeProg` — one coset of line 04e, and
  Procedure Recompute `H(W)`, on the RAM;
* `Algo.theorem_13_1_3_ram` — **Theorem 13.1.3 on the RAM**.

No axiom, no `sorry`, no `native_decide`.
-/

namespace Algo

open RAM RAM.Targets
open Equiv (Perm)

variable {n : ℕ}

/-! ## Small facts -/

theorem size_nat_le_add_two (k : ℕ) : Enc.size k ≤ k + 2 := by
  have h1 : Enc.size k = Nat.size k + 2 := Small.size_nat k
  have h2 := size_le_self k
  omega

/-- The value of a fold is the finish of a state satisfying any invariant of the fold. -/
theorem Round.loopAux_inv {ι ω α : Type*} (R : Round ι ω α) (rec : ι → α) (I : ι)
    (P : ω → Prop)
    (hP : ∀ j s J, P s → R.child (I, j, s) = some J → P (R.combine (I, j, s, rec J))) :
    ∀ (w j : ℕ) (s : ω), P s → ∃ s', P s' ∧ R.loopAux rec w I j s = R.finish (I, s') := by
  intro w
  induction w with
  | zero => intro j s h; exact ⟨s, h, rfl⟩
  | succ w ih =>
    intro j s h
    cases hc : R.child (I, j, s) with
    | none => exact ⟨s, h, R.loopAux_succ_none hc⟩
    | some J =>
      rw [R.loopAux_succ_some hc]
      exact ih _ _ (hP j s J h hc)

/-! ## The routines of the Recompute round are machine routines -/

theorem polyFun_lcR0_width : PolyFun lcR0.width := by
  have hopt := PolyFun.optionElim
    (g := fun I : RawLCSI => (winOrbits (I.1.2.1, I.1.1)).length)
    (h := fun z : (RawTAct × ℕ) × RawLCSI => z.1.2)
    ((((polyFun_fst.comp polyFun_snd).comp polyFun_fst).pair
      (polyFun_fst.comp polyFun_fst)).comp polyFun_winOrbits |>.comp polyFun_length)
    (polyFun_fst.comp polyFun_snd)
  have hin : PolyFun (fun I : RawLCSI => ((I.2, I) : Option (RawTAct × ℕ) × RawLCSI)) :=
    polyFun_snd.pair polyFun_id
  exact (hin.comp hopt).of_eq (fun I => rfl)

theorem polyFun_lcR0_finish : PolyFun lcR0.finish := by
  have horbW : PolyFun (fun z : RawLCSI × RawCoset =>
      decide ((winOrbits (z.1.1.2.1, z.1.1.1)).length ≤ 1)) := by
    have h1 : PolyFun (fun z : RawLCSI × RawCoset => winOrbits (z.1.1.2.1, z.1.1.1)) :=
      (((((polyFun_fst.comp polyFun_fst).comp polyFun_snd).comp polyFun_fst).pair
        ((polyFun_fst.comp polyFun_fst).comp polyFun_fst))).comp polyFun_winOrbits
    exact ((h1.comp polyFun_length).pair (polyFun_const 1)).comp polyFun_le
  have hg : PolyFun (fun z : RawLCSI × RawCoset =>
      if (winOrbits (z.1.1.2.1, z.1.1.1)).length ≤ 1 then (none : RawCoset) else z.2) :=
    (PolyFun.ite horbW (polyFun_const none) polyFun_snd).of_eq (fun z => by
      by_cases h : (winOrbits (z.1.1.2.1, z.1.1.1)).length ≤ 1 <;> simp [h])
  have hopt := PolyFun.optionElim
    (g := fun z : RawLCSI × RawCoset =>
      if (winOrbits (z.1.1.2.1, z.1.1.1)).length ≤ 1 then (none : RawCoset) else z.2)
    (h := fun z : (RawTAct × ℕ) × (RawLCSI × RawCoset) => z.2.2)
    hg (polyFun_snd.comp polyFun_snd)
  have hin : PolyFun (fun p : RawLCSI × RawCoset =>
      ((p.1.2, p) : Option (RawTAct × ℕ) × (RawLCSI × RawCoset))) :=
    (polyFun_fst.comp polyFun_snd).pair polyFun_id
  exact (hin.comp hopt).of_eq (fun p => rfl)

/-! ## Sizes -/

section Sizes

variable {ansQ : RawWinSI → RawCoset}

/-- The ground size of a raw instance: the size of its pair of strings. -/
abbrev lcGround (I : RawLCSI) : ℕ := Enc.size I.1.2.2.2

theorem lcGround_le (I : RawLCSI) : lcGround I ≤ Enc.size I :=
  le_trans (size_snd_le' I.1.2.2)
    (le_trans (size_snd_le' I.1.2) (le_trans (size_snd_le' I.1) (size_fst_le' I)))

/-- The children of an instance have the same strings. -/
theorem lcGround_child {I J : RawLCSI} {j : ℕ} {s : RawCoset} (hc : lcChild (I, j, s) = some J) :
    lcGround J = lcGround I := by
  obtain ⟨o, ho⟩ : ∃ o, I.2 = o := ⟨_, rfl⟩
  cases o with
  | none =>
    obtain ⟨J', hw, rfl⟩ := lcChild_chain_eq_some (p := (I, j, s)) ho hc
    obtain ⟨g, τ, -, -, -, -, rfl⟩ := winChild_eq_some hw
    rfl
  | some q =>
    obtain ⟨td, idx⟩ := q
    obtain ⟨-, rfl⟩ := lcChild_desc_eq_some (p := (I, j, s)) ho hc
    rfl

/-- The width is a number no larger than the instance. -/
theorem size_lcR0_width_le (I : RawLCSI) : Enc.size (lcR0.width I) ≤ Enc.size I + 2 := by
  obtain ⟨o, ho⟩ : ∃ o, I.2 = o := ⟨_, rfl⟩
  cases o with
  | none =>
    have hw : lcR0.width I = (winOrbits (I.1.2.1, I.1.1)).length := by
      show I.2.elim _ _ = _; rw [ho]; rfl
    rw [hw]
    have h1 := length_winOrbits_le I.1.2.1 I.1.1
    have h2 : I.1.1.length ≤ Enc.size I :=
      le_trans (length_le_size _) (le_trans (size_fst_le' I.1) (size_fst_le' I))
    have h3 := size_nat_le_add_two (winOrbits (I.1.2.1, I.1.1)).length
    omega
  | some q =>
    have hw : lcR0.width I = q.2 := by show I.2.elim _ _ = _; rw [ho]; rfl
    rw [hw]
    have h1 : Enc.size q.2 ≤ Enc.size q := size_snd_le' q
    have h2 : Enc.size (some q) = Enc.size q + 2 := size_some_eq q
    have h3 : Enc.size I.2 ≤ Enc.size I := size_snd_le' I
    rw [ho] at h3
    omega

/-- The empty partial answer is small. -/
theorem size_lcInit_le {I : RawLCSI} (hI : LCWF n I) :
    Enc.size (lcInit I) ≤ lcBound (lcGround I) := by
  obtain ⟨o, ho⟩ : ∃ o, I.2 = o := ⟨_, rfl⟩
  have hcb := chainBound_le_lcBound (lcGround I)
  cases o with
  | none =>
    have h0 : lcInit I = some (I.1.2.1, I.1.2.2.1) := by rw [lcInit, ho]; rfl
    have h1 : Enc.size (some (I.1.2.1, I.1.2.2.1) : RawCoset)
        = Enc.size ((I.1.2.1, I.1.2.2.1) : RawGens × RawPerm) + 2 := size_some_eq _
    have h2 : Enc.size ((I.1.2.1, I.1.2.2.1) : RawGens × RawPerm)
        ≤ 2 * Enc.size I.1.2.1 + 2 * Enc.size I.1.2.2.1 := size_pair_le' _
    have h3 : Enc.size I.1.2.1 ≤ gensBound (lcGround I) := size_gens_le hI.1
    have h4 : Enc.size I.1.2.2.1 ≤ strBound (lcGround I) := size_rep_le hI.1
    have hSG := strBound_le_gensBound (lcGround I)
    have h5 : chainBound (lcGround I) = 16 * (gensBound (lcGround I) + lcGround I + 1) := rfl
    rw [h0]
    omega
  | some q =>
    have h0 : lcInit I = none := by rw [lcInit, ho]; rfl
    have h1 : Enc.size (none : RawCoset) = 2 := size_none
    have h2 := four_le_lcBound (lcGround I)
    rw [h0]
    omega

/-- A normalized answer is small. -/
theorem size_lcAnsN_le {W : RawWinSI} (hW : WinWF n W) :
    Enc.size (lcAnsN ansQ W) ≤ chainBound (Enc.size W.2.2.2) :=
  size_lcNormAns_le (le_trans (le_of_eq hW.1) (le_size_strings hW)) _

/-- **One coset of line 04e returns a small answer.** -/
theorem size_lcChainEval_le {I : RawLCSI} (hI : LCWF n I) (hq : I.2 = none) :
    Enc.size (lcChainEval ansQ I) ≤ lcBound (lcGround I) := by
  have hcb := chainBound_le_lcBound (lcGround I)
  unfold lcChainEval
  by_cases h1 : lcOrbCount I ≤ 1
  · rw [if_pos h1]
    exact le_trans (size_lcAnsN_le hI.1) hcb
  · rw [if_neg h1]
    obtain ⟨s', hs', he⟩ := lcR0.loopAux_inv (fun J => lcAnsN ansQ J.1) I
      (fun s => Enc.size s ≤ lcBound (lcGround I))
      (fun j s J _ hc => by
        show Enc.size (lcCombine (I, j, s, lcAnsN ansQ J.1)) ≤ _
        rw [lcCombine, hq]
        have hJ : LCWF n J := (lcRound n (fun _ => none)).child_wf I j s J hI hc
        have := size_lcAnsN_le (ansQ := ansQ) hJ.1
        have hg : Enc.size J.1.2.2.2 = lcGround I := lcGround_child hc
        rw [hg] at this
        exact le_trans this hcb)
      (lcR0.width I) 0 (lcR0.init I) (size_lcInit_le hI)
    rw [he]
    show Enc.size (lcFinish (fun _ => none) (I, s')) ≤ _
    have h1' : ¬ (winOrbits (I.1.2.1, I.1.1)).length ≤ 1 := h1
    simp only [lcFinish, hq, Option.elim]
    rw [if_neg h1']
    exact hs'

/-- **Procedure Recompute returns a small answer.** -/
theorem size_lcSolveQ_desc_le {I : RawLCSI} (hI : LCWF n I) {td : RawTAct} {idx : ℕ}
    (hs : I.2 = some (td, idx)) :
    Enc.size (lcSolveQ ansQ I) ≤ lcBound (lcGround I) := by
  have e1 : lcSolveQ ansQ I
      = lcR0.loopAux (lcChainEval ansQ) (lcR0.width I) I 0 (lcR0.init I) := by
    simp [lcSolveQ, hs]
  rw [e1]
  obtain ⟨s', hs', he⟩ := lcR0.loopAux_inv (lcChainEval ansQ) I
    (fun s => Enc.size s ≤ lcBound (lcGround I))
    (fun j s J hsb hc => by
      show Enc.size (lcCombine (I, j, s, lcChainEval ansQ J)) ≤ _
      rw [lcCombine, hs]
      have hJ : LCWF n J := (lcRound n (fun _ => none)).child_wf I j s J hI hc
      have hJb := size_lcChainEval_le (ansQ := ansQ) hJ (lcChild_desc_snd hs hc)
      rw [lcGround_child hc] at hJb
      exact size_rawCosetJoin_le (n := n) hI.1.1 (lc_le_ground hI)
        (chainBound_le_lcBound _) hsb hJb)
    (lcR0.width I) 0 (lcR0.init I) (size_lcInit_le hI)
  rw [he]
  show Enc.size (lcFinish (fun _ => none) (I, s')) ≤ _
  simp only [lcFinish, hs, Option.elim]
  exact hs'

end Sizes

/-! ## List arithmetic -/

theorem sum_map_le_of_le {α : Type*} (l : List α) (f g : α → ℕ) (a b : ℕ)
    (h : ∀ x ∈ l, f x ≤ a * g x + b) :
    (l.map f).sum ≤ a * (l.map g).sum + l.length * b := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have h1 := h x (List.mem_cons_self ..)
    have h2 := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    nlinarith

theorem sum_map_flatMap {α β : Type*} (l : List α) (f : α → List β) (τ : β → ℕ) :
    ((l.flatMap f).map τ).sum = (l.map (fun x => ((f x).map τ).sum)).sum := by
  induction l with
  | nil => simp
  | cons x l ih => simp [List.flatMap_cons, List.map_append, List.sum_append, ih]

theorem CleanComputeAt.wf' {α β : Type*} [Enc α] [Enc β] [Inhabited α] {K : ℕ} {P : Program}
    {f : α → β} {T : ℕ → ℕ} (h : CleanComputeAt K P f T) : Wf P :=
  (h.runsOn default).wf

theorem pw_eq (c d m : ℕ) : pw c d m = c * (m + 1) ^ d := rfl

/-! ## The oracle, normalized -/

/-- **One call, normalized.**  From any program `Q` answering an instance, a program that
returns the normalized answer, in ten times the steps of `Q` plus a polynomial in the size of
the instance; the polynomial depends on the bound `S` on the size of the answers of `Q`. -/
theorem exists_normProg (S : ℕ → ℕ) (hS : PolyBound S) :
    ∃ (N : Program → Program) (c d : ℕ), ∀ Q : Program, Wf Q → Wf (N Q) ∧
      ∀ (ansQ : RawWinSI → RawCoset) (W : RawWinSI) (τ : ℕ),
        RunsOn 16 Q W (ansQ W) τ → Enc.size (ansQ W) ≤ S (Enc.size W) →
        RunsOn 16 (N Q) W (lcAnsN ansQ W) (10 * τ + pw c d (Enc.size W)) := by
  have hx : PolyFun (fun W : RawWinSI => W.2.2.2.1) :=
    ((polyFun_snd.comp polyFun_snd).comp polyFun_snd).comp polyFun_fst
  obtain ⟨Px, c1, d1, hPx, -⟩ := polyFun_witness hx
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
    (hPn.runsOn ((W.2.2.2.1, ansQ W) : RawStr × RawCoset))
  refine r.mono ?_
  have hxW : Enc.size W.2.2.2.1 ≤ Enc.size W :=
    le_trans (size_fst_le' _) (le_trans (size_snd_le' _) (le_trans (size_snd_le' _)
      (size_snd_le' W)))
  have hp : Enc.size ((W.2.2.2.1, ansQ W) : RawStr × RawCoset)
      ≤ 2 * Enc.size W + 2 * S (Enc.size W) := by
    have := size_pair_le' ((W.2.2.2.1, ansQ W) : RawStr × RawCoset)
    simp only at this
    omega
  have e1 : c2 * (Enc.size ((W.2.2.2.1, ansQ W) : RawStr × RawCoset) + 1) ^ d2
      ≤ pw c2 d2 (2 * Enc.size W + 2 * S (Enc.size W)) := pw_mono c2 d2 hp
  have e2 := hcd (Enc.size W)
  rw [hGd] at e2
  have e3 : c1 * (Enc.size W + 1) ^ d1 = pw c1 d1 (Enc.size W) := rfl
  have e4 : c * (Enc.size W + 1) ^ d = pw c d (Enc.size W) := rfl
  simp only at e1
  omega

/-! ## One coset of line 04e on the RAM -/

/-- The width of a Chain Rule instance is at most its size. -/
theorem lcR0_width_chain_le {I : RawLCSI} (hq : I.2 = none) : lcR0.width I ≤ Enc.size I := by
  have hw : lcR0.width I = (winOrbits (I.1.2.1, I.1.1)).length := by
    show I.2.elim _ _ = _; rw [hq]; rfl
  rw [hw]
  exact le_trans (length_winOrbits_le _ _)
    (le_trans (length_le_size _) (le_trans (size_fst_le' I.1) (size_fst_le' I)))

theorem polyFun_lcTest : PolyFun (fun I : RawLCSI =>
    ((if lcOrbCount I ≤ 1 then some I.1 else none, I) : Option RawWinSI × RawLCSI)) := by
  have horb : PolyFun (fun I : RawLCSI => decide (lcOrbCount I ≤ 1)) := by
    have h1 : PolyFun (fun I : RawLCSI => winOrbits (I.1.2.1, I.1.1)) :=
      (((polyFun_fst.comp polyFun_snd).comp polyFun_fst).pair
        (polyFun_fst.comp polyFun_fst)).comp polyFun_winOrbits
    exact ((h1.comp polyFun_length).pair (polyFun_const 1)).comp polyFun_le
  have hs : PolyFun (fun I : RawLCSI =>
      if lcOrbCount I ≤ 1 then some I.1 else (none : Option RawWinSI)) :=
    (PolyFun.ite horb (polyFun_fst.comp polyFun_some) polyFun_none).of_eq (fun I => by
      by_cases h : lcOrbCount I ≤ 1 <;> simp [h])
  exact hs.pair polyFun_id

set_option maxHeartbeats 4000000 in
/-- **One coset of line 04e on the RAM.**  The Chain Rule over the orbits of `N` with each
orbit answered by `Q`: a thousand times the steps of `Q` on the calls, plus a polynomial in
the size of the instance. -/
theorem exists_chainProg (S : ℕ → ℕ) (hS : PolyBound S) :
    ∃ (CE : Program → Program) (c d : ℕ), ∀ Q : Program, Wf Q → Wf (CE Q) ∧
      ∀ (n : ℕ) (ansQ : RawWinSI → RawCoset) (τ : RawWinSI → ℕ) (I : RawLCSI),
        LCWF n I → I.2 = none →
        (∀ W, WinWF n W → RunsOn 16 Q W (ansQ W) (τ W) ∧ Enc.size (ansQ W) ≤ S (Enc.size W)) →
        RunsOn 16 (CE Q) I (lcChainEval ansQ I)
          (1000 * ((lcChainCalls ansQ I).map τ).sum + pw c d (Enc.size I)) := by
  obtain ⟨N, cN, dN, hN⟩ := exists_normProg S hS
  obtain ⟨F0, c0, d0, hF0⟩ := lcR0.exists_foldProg polyFun_lcChild polyFun_lcCombine
    polyFun_lcInit polyFun_lcR0_finish polyFun_lcR0_width
  obtain ⟨Pf, cf, df, hPf, -⟩ :=
    polyFun_witness (polyFun_fst : PolyFun (fun I : RawLCSI => I.1))
  obtain ⟨Pf2, cf2, df2, hPf2, -⟩ :=
    polyFun_witness (polyFun_fst : PolyFun (fun z : RawWinSI × RawLCSI => z.1))
  obtain ⟨Pt, ct, dt, hPt, hPt_s⟩ := polyFun_witness polyFun_lcTest
  obtain ⟨Bc, hBc⟩ : ∃ B : ℕ → ℕ, ∀ m, B m = 12 * m + 8 * lcBound m + 30 := ⟨_, fun _ => rfl⟩
  obtain ⟨K, hKd⟩ : ∃ K : ℕ → ℕ, ∀ m, K m = pw cf df (lcBound m) + pw cN dN (lcBound m) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨G, hGd⟩ : ∃ G : ℕ → ℕ, ∀ m, G m = 25 * pw ct dt m + 16 + 104 + 2
      + pw cf2 df2 (4 * m) + pw cN dN m + 100 * ((m + 2) * K m)
      + (m + 2) * pw c0 d0 (Bc m) := ⟨_, fun _ => rfl⟩
  have hG : PolyBound G := by
    have hB : PolyBound Bc := by
      rw [show Bc = fun m => 12 * m + 8 * lcBound m + 30 from funext hBc]
      exact (((polyBound_const 12).mul polyBound_id).add
        ((polyBound_const 8).mul polyBound_lcBound)).add (polyBound_const 30)
    have hK : PolyBound K := by
      rw [show K = fun m => pw cf df (lcBound m) + pw cN dN (lcBound m) from funext hKd]
      exact ((polyBound_pw cf df).comp polyBound_lcBound).add
        ((polyBound_pw cN dN).comp polyBound_lcBound)
    have ht := polyBound_pw ct dt
    rw [show G = fun m => 25 * pw ct dt m + 16 + 104 + 2
      + pw cf2 df2 (4 * m) + pw cN dN m + 100 * ((m + 2) * K m)
      + (m + 2) * pw c0 d0 (Bc m) from funext hGd]
    exact (((((((((polyBound_const 25).mul ht).add (polyBound_const 16)).add
      (polyBound_const 104)).add (polyBound_const 2)).add ((polyBound_pw cf2 df2).comp
        ((polyBound_const 4).mul polyBound_id))).add (polyBound_pw cN dN)).add
      ((polyBound_const 100).mul ((polyBound_id.add (polyBound_const 2)).mul hK))).add
      ((polyBound_id.add (polyBound_const 2)).mul ((polyBound_pw c0 d0).comp hB)))
  obtain ⟨c, d, hcd⟩ := hG
  let L : Program → Program := fun Q => RAM.seq Pf (N Q)
  refine ⟨fun Q => RAM.seq Pt (Lists.optElimProg 16 (F0 (L Q)) (RAM.seq Pf2 (N Q))), c, d,
    fun Q hQwf => ?_⟩
  have hNwf := (hN Q hQwf).1
  have hLwf : Wf (L Q) := wf_seq (CleanComputeAt.wf' hPf) hNwf
  obtain ⟨hFwf, hFrun⟩ := hF0 (L Q) hLwf
  have hFwf' : Wf (F0 (L Q)) := hFwf default
  have hSomeWf : Wf (RAM.seq Pf2 (N Q)) := wf_seq (CleanComputeAt.wf' hPf2) hNwf
  refine ⟨wf_seq (CleanComputeAt.wf' hPt) (Lists.wf_optElimProg (by omega) hFwf' hSomeWf), ?_⟩
  intro n ansQ τ I hI hq hQ
  set m := Enc.size I with hm
  have hGI := hcd m
  rw [hGd] at hGI
  have hBI := hBc m
  have hKI := hKd m
  have htest := hPt.runsOn I
  have htsz := hPt_s I
  have hgm : lcGround I ≤ m := lcGround_le I
  have hlb : lcBound (lcGround I) ≤ lcBound m := mono_lcBound hgm
  have hcb := chainBound_le_lcBound (lcGround I)
  have ept : ct * (m + 1) ^ dt = pw ct dt m := rfl
  have ept' : ct * (Enc.size I + 1) ^ dt = pw ct dt m := rfl
  have epc : c * (m + 1) ^ d = pw c d m := rfl
  have hI1 : Enc.size I.1 ≤ m := size_fst_le' I
  by_cases h1 : lcOrbCount I ≤ 1
  · -- the instance itself is the call
    have ht : ((if lcOrbCount I ≤ 1 then some I.1 else none, I) : Option RawWinSI × RawLCSI)
        = ((some I.1, I) : Option RawWinSI × RawLCSI) := by rw [if_pos h1]
    obtain ⟨hQrun, hQsz⟩ := hQ I.1 hI.1
    have r1 := (hPf2.runsOn ((I.1, I) : RawWinSI × RawLCSI)).seq
      ((hN Q hQwf).2 ansQ I.1 (τ I.1) hQrun hQsz)
    have r2 := RunsOn.optionElim_some (Pg := F0 (L Q)) (K := 16) (by omega) hFwf' r1
    rw [← ht] at r2
    have r3 := htest.seq r2
    have hval : lcChainEval ansQ I = lcAnsN ansQ I.1 := by rw [lcChainEval, if_pos h1]
    have hcalls : lcChainCalls ansQ I = [I.1] := by rw [lcChainCalls, if_pos h1]
    rw [hval, hcalls]
    refine r3.mono ?_
    have hs1 : Enc.size ((if lcOrbCount I ≤ 1 then some I.1 else none, I)
        : Option RawWinSI × RawLCSI) ≤ pw ct dt m := by rw [← ept]; exact htsz
    have hs2 : Enc.size ((I.1, I) : RawWinSI × RawLCSI) ≤ 4 * m := by
      have := size_pair_le' ((I.1, I) : RawWinSI × RawLCSI)
      simp only at this
      omega
    have e2 : cf2 * (Enc.size ((I.1, I) : RawWinSI × RawLCSI) + 1) ^ df2 ≤ pw cf2 df2 (4 * m) :=
      pw_mono cf2 df2 hs2
    have e3 : pw cN dN (Enc.size I.1) ≤ pw cN dN m := pw_mono cN dN hI1
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    have hK0 : 0 ≤ 100 * ((m + 2) * K m) := Nat.zero_le _
    omega
  · -- the Chain Rule over the orbits
    have ht : ((if lcOrbCount I ≤ 1 then some I.1 else none, I) : Option RawWinSI × RawLCSI)
        = ((none, I) : Option RawWinSI × RawLCSI) := by rw [if_neg h1]
    let ans : RawLCSI → RawCoset := fun J => lcAnsN ansQ J.1
    let τ' : RawLCSI → ℕ := fun J =>
      cf * (Enc.size J + 1) ^ df + (10 * τ J.1 + pw cN dN (Enc.size J.1))
    have hJsize : ∀ J ∈ lcR0.loopCalls ans (lcR0.width I) I 0 (lcR0.init I),
        LCWF n J ∧ Enc.size J ≤ lcBound m := by
      intro J hJ
      obtain ⟨j', s', hc⟩ := exists_child_of_mem_loopCalls hJ
      have hJwf : LCWF n J := (lcRound n (fun _ => none)).child_wf I j' s' J hI hc
      have h1 : Enc.size J ≤ lcBound (lcGround J) := size_lcSI_le hJwf
      rw [lcGround_child hc] at h1
      exact ⟨hJwf, le_trans h1 hlb⟩
    have hcallsF : ∀ J ∈ lcR0.loopCalls ans (lcR0.width I) I 0 (lcR0.init I),
        RunsOn 16 (L Q) J (ans J) (τ' J) ∧ Enc.size J ≤ Bc m ∧ Enc.size (ans J) ≤ Bc m := by
      intro J hJ
      obtain ⟨hJwf, hJs⟩ := hJsize J hJ
      obtain ⟨j', s', hc⟩ := exists_child_of_mem_loopCalls hJ
      obtain ⟨hQrun, hQsz⟩ := hQ J.1 hJwf.1
      refine ⟨(hPf.runsOn J).seq ((hN Q hQwf).2 ansQ J.1 (τ J.1) hQrun hQsz), by omega, ?_⟩
      have h1 : Enc.size (ans J) ≤ chainBound (lcGround J) := size_lcAnsN_le hJwf.1
      rw [lcGround_child hc] at h1
      omega
    have hstatesF : ∀ k ≤ lcR0.width I,
        Enc.size ((lcR0.foldStep ans)^[k] ((I, 0, lcR0.init I), false)) ≤ Bc m := by
      intro k _
      obtain ⟨j', s', b', he, hj', hs'⟩ := lcR0.foldStep_iterate_inv ans I
        (fun j s => j ≤ lcR0.width I ∧ Enc.size s ≤ lcBound (lcGround I))
        (fun j s J _ hc => ⟨lcR0.lt_width_of_child hc, by
          show Enc.size (lcCombine (I, j, s, ans J)) ≤ _
          rw [lcCombine, hq]
          have hJwf : LCWF n J := (lcRound n (fun _ => none)).child_wf I j s J hI hc
          have h1 : Enc.size (ans J) ≤ chainBound (lcGround J) := size_lcAnsN_le hJwf.1
          rw [lcGround_child hc] at h1
          exact le_trans h1 (chainBound_le_lcBound _)⟩)
        k 0 (lcR0.init I) false ⟨Nat.zero_le _, size_lcInit_le hI⟩
      rw [he]
      have h1 := Round.size_foldSt_le I j' s' b'
      have h2 : Enc.size j' ≤ Enc.size (lcR0.width I) := size_nat_le_of_le hj'
      have h3 := size_lcR0_width_le I
      omega
    have r := hFrun ans τ' I (Bc m) hcallsF hstatesF
    have r2 := RunsOn.optionElim_none (β := RawWinSI) (K := 16) (by omega) hSomeWf r
    rw [← ht] at r2
    have r3 := htest.seq r2
    have hval : lcChainEval ansQ I = lcR0.loopAux ans (lcR0.width I) I 0 (lcR0.init I) := by
      rw [lcChainEval, if_neg h1]
    rw [hval]
    refine r3.mono ?_
    set l := lcR0.loopCalls ans (lcR0.width I) I 0 (lcR0.init I) with hl
    have hsum := sum_map_le_of_le l τ' (fun J => τ J.1) 10 (K m) (fun J hJ => by
      obtain ⟨-, hJs⟩ := hJsize J hJ
      have e1 : cf * (Enc.size J + 1) ^ df ≤ pw cf df (lcBound m) := pw_mono cf df hJs
      have e2 : pw cN dN (Enc.size J.1) ≤ pw cN dN (lcBound m) :=
        pw_mono cN dN (le_trans (size_fst_le' J) hJs)
      show cf * (Enc.size J + 1) ^ df + (10 * τ J.1 + pw cN dN (Enc.size J.1))
        ≤ 10 * τ J.1 + K m
      omega)
    have hmap : (lcChainCalls ansQ I).map τ = l.map (fun J => τ J.1) := by
      rw [lcChainCalls, if_neg h1, List.map_map]; rfl
    rw [hmap]
    have hlen : l.length ≤ lcR0.width I := lcR0.length_loopCalls_le ans I _ 0 _
    have hw : lcR0.width I ≤ m := lcR0_width_chain_le hq
    have e1 : l.length * K m ≤ (m + 2) * K m := Nat.mul_le_mul_right _ (by omega)
    have e2 : (lcR0.width I + 2) * pw c0 d0 (Bc m) ≤ (m + 2) * pw c0 d0 (Bc m) :=
      Nat.mul_le_mul_right _ (by omega)
    have hs1 : Enc.size ((if lcOrbCount I ≤ 1 then some I.1 else none, I)
        : Option RawWinSI × RawLCSI) ≤ pw ct dt m := by rw [← ept]; exact htsz
    omega

/-! ## Procedure Recompute `H(W)` on the RAM -/

set_option maxHeartbeats 4000000 in
/-- **Procedure Recompute `H(W)` on the RAM** (lines 04a–04h).  The union over the `idx`
cosets of `N` (`idx = |H(W_old)^T| ≤ t!`), each coset answered by the Chain Rule with its
calls answered by `Q`: at most `10⁵` times the steps of `Q` on the calls, plus `idx + 2`
times a polynomial in the size of the instance. -/
theorem exists_recomputeProg (S : ℕ → ℕ) (hS : PolyBound S) :
    ∃ (RC : Program → Program) (c d : ℕ), ∀ Q : Program, Wf Q → Wf (RC Q) ∧
      ∀ (n : ℕ) (ansQ : RawWinSI → RawCoset) (τ : RawWinSI → ℕ) (I : RawLCSI)
        (td : RawTAct) (idx : ℕ), LCWF n I → I.2 = some (td, idx) →
        (∀ W, WinWF n W → RunsOn 16 Q W (ansQ W) (τ W) ∧ Enc.size (ansQ W) ≤ S (Enc.size W)) →
        RunsOn 16 (RC Q) I (lcSolveQ ansQ I)
          (100000 * ((lcDescCalls ansQ I).map τ).sum + (idx + 2) * pw c d (Enc.size I)) := by
  obtain ⟨CE, c1, d1, hCE⟩ := exists_chainProg S hS
  obtain ⟨F0, c0, d0, hF0⟩ := lcR0.exists_foldProg polyFun_lcChild polyFun_lcCombine
    polyFun_lcInit polyFun_lcR0_finish polyFun_lcR0_width
  obtain ⟨Bc, hBc⟩ : ∃ B : ℕ → ℕ, ∀ m, B m = 12 * m + 8 * lcBound m + 30 := ⟨_, fun _ => rfl⟩
  obtain ⟨G, hGd⟩ : ∃ G : ℕ → ℕ, ∀ m, G m = 100 * pw c1 d1 (lcBound m) + pw c0 d0 (Bc m) :=
    ⟨_, fun _ => rfl⟩
  have hG : PolyBound G := by
    have hB : PolyBound Bc := by
      rw [show Bc = fun m => 12 * m + 8 * lcBound m + 30 from funext hBc]
      exact (((polyBound_const 12).mul polyBound_id).add
        ((polyBound_const 8).mul polyBound_lcBound)).add (polyBound_const 30)
    rw [show G = fun m => 100 * pw c1 d1 (lcBound m) + pw c0 d0 (Bc m) from funext hGd]
    exact ((polyBound_const 100).mul ((polyBound_pw c1 d1).comp polyBound_lcBound)).add
      ((polyBound_pw c0 d0).comp hB)
  obtain ⟨c, d, hcd⟩ := hG
  refine ⟨fun Q => F0 (CE Q), c, d, fun Q hQwf => ?_⟩
  obtain ⟨hCEwf, hCErun⟩ := hCE Q hQwf
  obtain ⟨hFwf, hFrun⟩ := hF0 (CE Q) hCEwf
  refine ⟨hFwf default, ?_⟩
  intro n ansQ τ I td idx hI hs hQ
  have m_def : ∃ m, m = Enc.size I := ⟨_, rfl⟩
  obtain ⟨m, hm⟩ := m_def
  have hGI := hcd m
  rw [hGd] at hGI
  have hBI := hBc m
  have hgm : lcGround I ≤ m := hm ▸ lcGround_le I
  have hlb : lcBound (lcGround I) ≤ lcBound m := mono_lcBound hgm
  have epc : c * (m + 1) ^ d = pw c d m := rfl
  have e1 : lcSolveQ ansQ I
      = lcR0.loopAux (lcChainEval ansQ) (lcR0.width I) I 0 (lcR0.init I) := by
    simp [lcSolveQ, hs]
  rw [e1]
  let τ' : RawLCSI → ℕ := fun C =>
    1000 * ((lcChainCalls ansQ C).map τ).sum + pw c1 d1 (Enc.size C)
  have hJsize : ∀ C ∈ lcR0.loopCalls (lcChainEval ansQ) (lcR0.width I) I 0 (lcR0.init I),
      LCWF n C ∧ C.2 = none ∧ Enc.size C ≤ lcBound m ∧
        Enc.size (lcChainEval ansQ C) ≤ lcBound m := by
    intro C hC
    obtain ⟨j', s', hc⟩ := exists_child_of_mem_loopCalls hC
    have hCwf : LCWF n C := (lcRound n (fun _ => none)).child_wf I j' s' C hI hc
    have hCq : C.2 = none := lcChild_desc_snd hs hc
    have h1 : Enc.size C ≤ lcBound (lcGround C) := size_lcSI_le hCwf
    have h2 : Enc.size (lcChainEval ansQ C) ≤ lcBound (lcGround C) :=
      size_lcChainEval_le hCwf hCq
    rw [lcGround_child hc] at h1 h2
    exact ⟨hCwf, hCq, le_trans h1 hlb, le_trans h2 hlb⟩
  have hcallsF : ∀ C ∈ lcR0.loopCalls (lcChainEval ansQ) (lcR0.width I) I 0 (lcR0.init I),
      RunsOn 16 (CE Q) C (lcChainEval ansQ C) (τ' C) ∧ Enc.size C ≤ Bc m ∧
        Enc.size (lcChainEval ansQ C) ≤ Bc m := by
    intro C hC
    obtain ⟨hCwf, hCq, h1, h2⟩ := hJsize C hC
    exact ⟨hCErun n ansQ τ C hCwf hCq hQ, by omega, by omega⟩
  have hstatesF : ∀ k ≤ lcR0.width I,
      Enc.size ((lcR0.foldStep (lcChainEval ansQ))^[k] ((I, 0, lcR0.init I), false))
        ≤ Bc m := by
    intro k _
    obtain ⟨j', s', b', he, hj', hs'⟩ := lcR0.foldStep_iterate_inv (lcChainEval ansQ) I
      (fun j s => j ≤ lcR0.width I ∧ Enc.size s ≤ lcBound (lcGround I))
      (fun j s J hP hc => ⟨lcR0.lt_width_of_child hc, by
        show Enc.size (lcCombine (I, j, s, lcChainEval ansQ J)) ≤ _
        rw [lcCombine, hs]
        have hJ : LCWF n J := (lcRound n (fun _ => none)).child_wf I j s J hI hc
        have hJb := size_lcChainEval_le (ansQ := ansQ) hJ (lcChild_desc_snd hs hc)
        rw [lcGround_child hc] at hJb
        exact size_rawCosetJoin_le (n := n) hI.1.1 (lc_le_ground hI)
          (chainBound_le_lcBound _) hP.2 hJb⟩)
      k 0 (lcR0.init I) false ⟨Nat.zero_le _, size_lcInit_le hI⟩
    rw [he]
    have h1 := Round.size_foldSt_le I j' s' b'
    have h2 : Enc.size j' ≤ Enc.size (lcR0.width I) := size_nat_le_of_le hj'
    have h3 := size_lcR0_width_le I
    omega
  have r := hFrun (lcChainEval ansQ) τ' I (Bc m) hcallsF hstatesF
  refine r.mono ?_
  set l := lcR0.loopCalls (lcChainEval ansQ) (lcR0.width I) I 0 (lcR0.init I) with hl
  have hsum := sum_map_le_of_le l τ' (fun C => ((lcChainCalls ansQ C).map τ).sum) 1000
    (pw c1 d1 (lcBound m)) (fun C hC => by
      obtain ⟨-, -, h1, -⟩ := hJsize C hC
      have e1 : pw c1 d1 (Enc.size C) ≤ pw c1 d1 (lcBound m) := pw_mono c1 d1 h1
      show 1000 * ((lcChainCalls ansQ C).map τ).sum + pw c1 d1 (Enc.size C)
        ≤ 1000 * ((lcChainCalls ansQ C).map τ).sum + pw c1 d1 (lcBound m)
      omega)
  have hflat : ((lcDescCalls ansQ I).map τ).sum
      = (l.map (fun C => ((lcChainCalls ansQ C).map τ).sum)).sum :=
    sum_map_flatMap l (lcChainCalls ansQ) τ
  rw [hflat]
  have hw : lcR0.width I = idx := by
    show I.2.elim (winOrbits (I.1.2.1, I.1.1)).length (fun q => q.2) = _
    rw [hs]; rfl
  have hlen : l.length ≤ idx := hw ▸ lcR0.length_loopCalls_le _ I _ 0 _
  have e2 : l.length * pw c1 d1 (lcBound m) ≤ (idx + 2) * pw c1 d1 (lcBound m) :=
    Nat.mul_le_mul_right _ (by omega)
  have e3 : (idx + 2) * (100 * pw c1 d1 (lcBound m) + pw c0 d0 (Bc m))
      ≤ (idx + 2) * pw c d m := Nat.mul_le_mul_left _ (by omega)
  have e4 : (idx + 2) * (100 * pw c1 d1 (lcBound m) + pw c0 d0 (Bc m))
      = 100 * ((idx + 2) * pw c1 d1 (lcBound m)) + (idx + 2) * pw c0 d0 (Bc m) := by ring
  rw [hw, ← hm]
  omega

/-! ## Theorem 13.1.3 on the RAM -/

theorem sum_range_eq_list (N : ℕ) (g : ℕ → ℕ) :
    ∑ j ∈ Finset.range N, g j = ((List.range N).map g).sum := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, List.range_succ, List.map_append, List.sum_append]
    simp

theorem polyFun_lcCondInst : PolyFun (fun q : RawLCLoop =>
    ((if lcCond q then some (lcInst q) else none, q) : Option RawLCSI × RawLCLoop)) :=
  (PolyFun.ite polyFun_lcCond (polyFun_lcInst.comp polyFun_some) polyFun_none).pair polyFun_id

set_option maxHeartbeats 16000000 in
/-- **Theorem 13.1.3 on the RAM** (§13.1), the running time.  One program transformer `F`:
for every program `Q` that answers the well-formed String Isomorphism instances, `F Q` runs
Procedure LocalCertificates within

  `10⁷ · ∑_{W ∈ calls} τ(W) + t! · poly(size of the input)`

steps, where `τ(W)` is the number of steps of `Q` on the call `W` and the calls are
`Algo.lcCallsQ` (at most `t!·n²` of them, on windows of at most `n/t` points:
`Algo.length_lcCallsQ_le`, `Algo.window_lcCallsQ_le`).  The output is the output of
Procedure LocalCertificates with Procedure Recompute answered through `Q`; that it is the
paper's `(W(T), K(T), M(T))` is `Algo.theorem_13_1_3_ram_spec`.  The polynomial depends on
the polynomial `S` that bounds the size of the answers of `Q`, and on nothing else. -/
theorem theorem_13_1_3_ram (S : ℕ → ℕ) (hS : PolyBound S) :
    ∃ (F : Program → Program) (c d : ℕ), ∀ Q : Program, Wf Q → Wf (F Q) ∧
      ∀ {n m : ℕ} {G : Subgroup (Perm (Fin n))} {ϕ : G →* Perm (Fin m)} {xs : RawStr}
        {tdom : List ℕ} (hc : LCCtxWF n m xs tdom) {st0 : RawLCSt},
        StateFor hc (Babai.stages ϕ (decStrN n xs) (winSet m tdom) 0) st0 →
        ∀ (ansQ : RawWinSI → RawCoset) (τ : RawWinSI → ℕ),
        (∀ W, WinWF n W → RunsOn 16 Q W (ansQ W) (τ W) ∧ Enc.size (ansQ W) ≤ S (Enc.size W) ∧
          decCoset n (ansQ W) = (decWinSI n W).answer) →
        RunsOn 16 (F Q) ((xs, tdom), st0) (lcOut (lcSolveQ ansQ) ((xs, tdom), st0))
          (10 ^ 7 * ((lcCallsQ ansQ ((xs, tdom), st0)).map τ).sum
            + Nat.factorial tdom.length * pw c d (Enc.size (((xs, tdom), st0) : RawLCLoop))) := by
  obtain ⟨RC, cR, dR, hRC⟩ := exists_recomputeProg S hS
  obtain ⟨Pstart, c6, d6, hstart, -⟩ := polyFun_witness polyFun_lcCount
  obtain ⟨Pend, c7, d7, hend, -⟩ := polyFun_witness
    ((polyFun_snd : PolyFun (fun z : ℕ × RawLCLoop => z.2)).comp lcwPolyFun_out)
  obtain ⟨Pcond, cC, dC, hcond, hcond_s⟩ := polyFun_witness polyFun_lcCondInst
  obtain ⟨Pid, cI, dI, hid, -⟩ := polyFun_witness (polyFun_id : PolyFun (id : RawLCLoop → RawLCLoop))
  obtain ⟨Pf3, c3, d3, hf3, -⟩ :=
    polyFun_witness (polyFun_fst : PolyFun (fun z : RawLCSI × RawLCLoop => z.1))
  obtain ⟨Ps3, c4, d4, hs3, -⟩ :=
    polyFun_witness (polyFun_snd : PolyFun (fun z : RawLCSI × RawLCLoop => z.2))
  obtain ⟨Ppost, c5, d5, hpost, -⟩ := polyFun_witness lcwPolyFun_step
  obtain ⟨Ppred, cP, dP, hpred, -⟩ := polyFun_witness
    ((polyFun_fst.sub (polyFun_const 1)) : PolyFun (fun z : ℕ × RawLCLoop => z.1 - 1))
  obtain ⟨Psnd, cS, dS, hsnd, -⟩ :=
    polyFun_witness (polyFun_snd : PolyFun (fun z : ℕ × RawLCLoop => z.2))
  -- the size bounds, in the size `M` of the input
  obtain ⟨Zq, hZq⟩ : ∃ f : ℕ → ℕ, ∀ M, f M = 4 * M + 2 * lcStBound M := ⟨_, fun _ => rfl⟩
  obtain ⟨Zk, hZk⟩ : ∃ f : ℕ → ℕ, ∀ M, f M = M + 2 := ⟨_, fun _ => rfl⟩
  obtain ⟨Zp, hZp⟩ : ∃ f : ℕ → ℕ, ∀ M, f M = 2 * Zk M + 2 * Zq M := ⟨_, fun _ => rfl⟩
  obtain ⟨ZI, hZI⟩ : ∃ f : ℕ → ℕ, ∀ M, f M = lcBound (4 * M) := ⟨_, fun _ => rfl⟩
  obtain ⟨Ziq, hZiq⟩ : ∃ f : ℕ → ℕ, ∀ M, f M = 2 * ZI M + 2 * Zq M := ⟨_, fun _ => rfl⟩
  obtain ⟨Zc, hZc⟩ : ∃ f : ℕ → ℕ, ∀ M, f M = pw cC dC (Zq M) := ⟨_, fun _ => rfl⟩
  obtain ⟨PR, hPR⟩ : ∃ f : ℕ → ℕ, ∀ M, f M = pw cR dR (ZI M) := ⟨_, fun _ => rfl⟩
  obtain ⟨E1, hE1⟩ : ∃ f : ℕ → ℕ, ∀ M, f M = 25 * Zc M + 122 + 19 * Ziq M + 19 * ZI M
      + 19 * Zq M + 10 * pw c3 d3 (Ziq M) + 10 * pw c4 d4 (Ziq M) + 376 + pw c5 d5 (Ziq M)
      + pw cI dI (Zq M) := ⟨_, fun _ => rfl⟩
  obtain ⟨E2, hE2⟩ : ∃ f : ℕ → ℕ, ∀ M, f M = 19 * Zp M + 19 * Zk M + 19 * Zq M
      + 10 * pw cP dP (Zp M) + 10 * pw cS dS (Zp M) + 376 + 10 * E1 M := ⟨_, fun _ => rfl⟩
  obtain ⟨Gf, hGf⟩ : ∃ f : ℕ → ℕ, ∀ M, f M = M * (300 * PR M + E2 M + 2) + 1 + pw c6 d6 M
      + pw c7 d7 (Zp M) := ⟨_, fun _ => rfl⟩
  have hGfP : PolyBound Gf := by
    have pZq : PolyBound Zq := by
      rw [show Zq = _ from funext hZq]
      exact ((polyBound_const 4).mul polyBound_id).add
        ((polyBound_const 2).mul polyBound_lcStBound)
    have pZk : PolyBound Zk := by
      rw [show Zk = _ from funext hZk]; exact polyBound_id.add (polyBound_const 2)
    have pZp : PolyBound Zp := by
      rw [show Zp = _ from funext hZp]
      exact ((polyBound_const 2).mul pZk).add ((polyBound_const 2).mul pZq)
    have pZI : PolyBound ZI := by
      rw [show ZI = _ from funext hZI]
      exact polyBound_lcBound.comp ((polyBound_const 4).mul polyBound_id)
    have pZiq : PolyBound Ziq := by
      rw [show Ziq = _ from funext hZiq]
      exact ((polyBound_const 2).mul pZI).add ((polyBound_const 2).mul pZq)
    have pZc : PolyBound Zc := by
      rw [show Zc = _ from funext hZc]; exact (polyBound_pw cC dC).comp pZq
    have pPR : PolyBound PR := by
      rw [show PR = _ from funext hPR]; exact (polyBound_pw cR dR).comp pZI
    have pE1 : PolyBound E1 := by
      rw [show E1 = _ from funext hE1]
      exact (((((((((((polyBound_const 25).mul pZc).add (polyBound_const 122)).add
        ((polyBound_const 19).mul pZiq)).add ((polyBound_const 19).mul pZI)).add
        ((polyBound_const 19).mul pZq)).add ((polyBound_const 10).mul
          ((polyBound_pw c3 d3).comp pZiq))).add ((polyBound_const 10).mul
          ((polyBound_pw c4 d4).comp pZiq))).add (polyBound_const 376)).add
        ((polyBound_pw c5 d5).comp pZiq)).add ((polyBound_pw cI dI).comp pZq))
    have pE2 : PolyBound E2 := by
      rw [show E2 = _ from funext hE2]
      exact ((((((polyBound_const 19).mul pZp).add ((polyBound_const 19).mul pZk)).add
        ((polyBound_const 19).mul pZq)).add ((polyBound_const 10).mul
          ((polyBound_pw cP dP).comp pZp))).add ((polyBound_const 10).mul
          ((polyBound_pw cS dS).comp pZp))).add (polyBound_const 376) |>.add
        ((polyBound_const 10).mul pE1)
    rw [show Gf = _ from funext hGf]
    exact (((polyBound_id.mul ((((polyBound_const 300).mul pPR).add pE2).add
      (polyBound_const 2))).add (polyBound_const 1)).add (polyBound_pw c6 d6)).add
      ((polyBound_pw c7 d7).comp pZp)
  obtain ⟨c, d, hcd⟩ := hGfP
  -- the programs
  let SomeBr : Program → Program := fun Q =>
    RAM.seq (Pairing.pairProg 16 (RAM.seq Pf3 (RC Q)) Ps3) Ppost
  let Step : Program → Program := fun Q =>
    RAM.seq Pcond (Lists.optElimProg 16 Pid (SomeBr Q))
  let Body : Program → Program := fun Q => Pairing.pairProg 16 Ppred (RAM.seq Psnd (Step Q))
  refine ⟨fun Q => RAM.seq Pstart (RAM.seq (whileNz 18 (Body Q)) Pend), c, d, ?_⟩
  intro Q hQwf
  obtain ⟨hRCwf, hRCrun⟩ := hRC Q hQwf
  have hSomeWf : Wf (SomeBr Q) :=
    wf_seq (Pairing.wf_pairProg 16 (wf_seq (CleanComputeAt.wf' hf3) hRCwf)
      (CleanComputeAt.wf' hs3)) (CleanComputeAt.wf' hpost)
  have hStepWf : Wf (Step Q) :=
    wf_seq (CleanComputeAt.wf' hcond) (Lists.wf_optElimProg (by omega) (CleanComputeAt.wf' hid)
      hSomeWf)
  have hBodyWf : Wf (Body Q) :=
    Pairing.wf_pairProg 16 (CleanComputeAt.wf' hpred) (wf_seq (CleanComputeAt.wf' hsnd) hStepWf)
  refine ⟨wf_seq (CleanComputeAt.wf' hstart) (wf_seq (wf_whileNz hBodyWf)
    (CleanComputeAt.wf' hend)), ?_⟩
  intro n m G ϕ xs tdom hc st0 h0 ansQ τ hQ
  have hQ' : ∀ W, WinWF n W → RunsOn 16 Q W (ansQ W) (τ W) ∧
      Enc.size (ansQ W) ≤ S (Enc.size W) := fun W hW => ⟨(hQ W hW).1, (hQ W hW).2.1⟩
  have hQc : ∀ W, WinWF n W → decCoset n (ansQ W) = (decWinSI n W).answer :=
    fun W hW => (hQ W hW).2.2
  -- notation
  set p : RawLCLoop := ((xs, tdom), st0) with hp
  obtain ⟨M, hM⟩ : ∃ M, M = Enc.size p := ⟨_, rfl⟩
  set step := lcStep (lcSolveQ ansQ) with hstepdef
  set N := xs.length with hN
  set f := Nat.factorial tdom.length with hf
  have hf1 : 1 ≤ f := Nat.factorial_pos _
  have hNM : N ≤ M := by
    rw [hM]
    exact le_trans (lcDeg_le p) (size_fst_le' p)
  have hxsM : Enc.size xs ≤ M := by
    rw [hM]
    exact le_trans (size_fst_le' (xs, tdom)) (size_fst_le' p)
  have hZqM := hZq M
  have hZkM := hZk M
  have hZpM := hZp M
  have hZIM := hZI M
  have hZiqM := hZiq M
  have hZcM := hZc M
  have hPRM := hPR M
  have hE1M := hE1 M
  have hE2M := hE2 M
  -- the states of the loop are small
  have hqsize : ∀ j, Enc.size (step^[j] p) ≤ Zq M := by
    intro j
    have h1 := size_pair_le' (step^[j] p)
    have h2 : (step^[j] p).1 = p.1 := lcStep_iterate_fst (lcSolveQ ansQ) j p
    have h3 : Enc.size (step^[j] p).2 ≤ max (Enc.size p.2) (lcStBound (Enc.size p.1)) :=
      size_lcStep_iterate_le (lcSolveQ ansQ) j p
    have h4 : Enc.size p.1 ≤ M := hM ▸ size_fst_le' p
    have h5 : Enc.size p.2 ≤ M := hM ▸ size_snd_le' p
    have h6 : lcStBound (Enc.size p.1) ≤ lcStBound M := mono_lcStBound h4
    have h7 : max (Enc.size p.2) (lcStBound (Enc.size p.1)) ≤ M + lcStBound M :=
      max_le (by omega) (by omega)
    rw [h2] at h1
    omega
  have hksize : ∀ k ≤ N, Enc.size k ≤ Zk M := by
    intro k hk
    have := size_nat_le_add_two k
    omega
  -- one step of the while loop
  have hstep : ∀ j < N, RunsOn 16 (Step Q) (step^[j] p) (step^[j + 1] p)
      (10 ^ 6 * ((lcStepCalls ansQ (step^[j] p)).map τ).sum + 10 * ((f + 2) * PR M) + E1 M) := by
    intro j hj
    set q := step^[j] p with hq
    have hqeq : q = ((xs, tdom), q.2) := lcLoop_eq_pair (lcSolveQ ansQ) j st0
    have hqs : Enc.size q ≤ Zq M := hqsize j
    have hnext : step^[j + 1] p = step q := Function.iterate_succ_apply' step j p
    rw [hnext]
    have hcs : Enc.size ((if lcCond q then some (lcInst q) else none, q)
        : Option RawLCSI × RawLCLoop) ≤ Zc M := by
      have e1 := hcond_s q
      have e2 : cC * (Enc.size q + 1) ^ dC ≤ pw cC dC (Zq M) := pw_mono cC dC hqs
      simp only at e1
      omega
    have ect : cC * (Enc.size q + 1) ^ dC ≤ Zc M := by
      have e2 : cC * (Enc.size q + 1) ^ dC ≤ pw cC dC (Zq M) := pw_mono cC dC hqs
      omega
    by_cases hcnd : lcCond q = true
    · -- line 04 runs
      obtain ⟨-, hst⟩ := lcCond_iterate hQc h0 hcnd
      set I := lcInst q with hIdef
      have hcs' : Enc.size ((if lcCond q then some (lcInst q) else none, q)
          : Option RawLCSI × RawLCLoop) ≤ Zc M := hcs
      have hI : LCWF n I := by rw [hIdef, hqeq]; exact lcwf_lcInst hst
      have hs : I.2 = some ((tdom, q.2.2.2), lcIdx q) := by rw [hIdef, hqeq]; rfl
      obtain ⟨-, -, ⟨ψ, hψ⟩, -⟩ := hI.2 _ _ hs
      have hidx : lcIdx q ≤ f := lcWidth_le_factorial hI hs hψ
      have hrc := hRCrun n ansQ τ I _ _ hI hs hQ'
      have hgI : lcGround I ≤ 4 * M := by
        have e1 : lcGround I = Enc.size ((q.1.1, q.1.1) : RawStr × RawStr) := by rw [hIdef]; rfl
        have e2 := size_pair_le' ((q.1.1, q.1.1) : RawStr × RawStr)
        have e3 : q.1.1 = xs := by rw [hqeq]
        rw [e1]; rw [e3] at e2 ⊢; simp only at e2; omega
      have hIsz : Enc.size I ≤ ZI M := by
        have e1 : Enc.size I ≤ lcBound (lcGround I) := size_lcSI_le hI
        have e2 : lcBound (lcGround I) ≤ lcBound (4 * M) := mono_lcBound hgI
        omega
      have hasz : Enc.size (lcSolveQ ansQ I) ≤ ZI M := by
        have e1 := size_lcSolveQ_desc_le (ansQ := ansQ) hI hs
        have e2 : lcBound (lcGround I) ≤ lcBound (4 * M) := mono_lcBound hgI
        omega
      have r1 := (hf3.runsOn ((I, q) : RawLCSI × RawLCLoop)).seq hrc
      have r2 := RunsOn.pair (K := 16) (by omega) r1 (hs3.runsOn ((I, q) : RawLCSI × RawLCLoop))
      have r3 := r2.seq (hpost.runsOn ((lcSolveQ ansQ I, q) : RawCoset × RawLCLoop))
      have r4 := RunsOn.optionElim_some (Pg := Pid) (K := 16) (by omega) (CleanComputeAt.wf' hid) r3
      have ht : ((if lcCond q then some (lcInst q) else none, q) : Option RawLCSI × RawLCLoop)
          = ((some I, q) : Option RawLCSI × RawLCLoop) := by rw [if_pos hcnd]
      rw [← ht] at r4
      have r5 := (hcond.runsOn q).seq r4
      have hval : lcStepWith (lcSolveQ ansQ I) q = step q := (lcwStep_eq _ q).symm
      simp only at r5
      rw [hval] at r5
      refine r5.mono ?_
      have hcalls : lcStepCalls ansQ q = lcDescCalls ansQ I := by
        rw [lcStepCalls, if_pos hcnd]
      rw [hcalls]
      have hIq : Enc.size ((I, q) : RawLCSI × RawLCLoop) ≤ Ziq M := by
        have := size_pair_le' ((I, q) : RawLCSI × RawLCLoop); simp only at this; omega
      have haq : Enc.size ((lcSolveQ ansQ I, q) : RawCoset × RawLCLoop) ≤ Ziq M := by
        have := size_pair_le' ((lcSolveQ ansQ I, q) : RawCoset × RawLCLoop)
        simp only at this; omega
      have e3 : c3 * (Enc.size ((I, q) : RawLCSI × RawLCLoop) + 1) ^ d3 ≤ pw c3 d3 (Ziq M) :=
        pw_mono c3 d3 hIq
      have e4 : c4 * (Enc.size ((I, q) : RawLCSI × RawLCLoop) + 1) ^ d4 ≤ pw c4 d4 (Ziq M) :=
        pw_mono c4 d4 hIq
      have e5 : c5 * (Enc.size ((lcSolveQ ansQ I, q) : RawCoset × RawLCLoop) + 1) ^ d5
          ≤ pw c5 d5 (Ziq M) := pw_mono c5 d5 haq
      have e6 : pw cR dR (Enc.size I) ≤ PR M := by rw [hPRM]; exact pw_mono cR dR hIsz
      have e7 : (lcIdx q + 2) * pw cR dR (Enc.size I) ≤ (f + 2) * PR M :=
        Nat.mul_le_mul (by omega) e6
      have hqs' : Enc.size q ≤ Zq M := hqs
      have e8 : 0 ≤ pw cI dI (Zq M) := Nat.zero_le _
      omega
    · -- the loop has stopped: the step is the identity
      have hcf : lcCond q = false := by simpa using hcnd
      have hsq : step q = q := by
        show lcStep (lcSolveQ ansQ) q = q
        rw [lcStep, if_neg hcnd]
      have r4 := RunsOn.optionElim_none (β := RawLCSI) (K := 16) (by omega) hSomeWf (hid.runsOn q)
      have ht : ((if lcCond q then some (lcInst q) else none, q) : Option RawLCSI × RawLCLoop)
          = ((none, q) : Option RawLCSI × RawLCLoop) := by rw [if_neg hcnd]
      rw [← ht] at r4
      have r5 := (hcond.runsOn q).seq r4
      rw [hsq]
      refine r5.mono ?_
      have hcalls : lcStepCalls ansQ q = [] := by rw [lcStepCalls, if_neg hcnd]
      rw [hcalls]
      have e1 : cI * (Enc.size (id q) + 1) ^ dI ≤ pw cI dI (Zq M) := pw_mono cI dI hqs
      simp only [List.map_nil, List.sum_nil, id] at e1 ⊢
      omega
  -- one pass of the body
  have hbody : ∀ j < N, RunsOn 16 (Body Q) ((N - j, step^[j] p) : ℕ × RawLCLoop)
      ((N - (j + 1), step^[j + 1] p) : ℕ × RawLCLoop)
      (10 ^ 7 * ((lcStepCalls ansQ (step^[j] p)).map τ).sum + 100 * ((f + 2) * PR M)
        + E2 M) := by
    intro j hj
    have r1 := hpred.runsOn ((N - j, step^[j] p) : ℕ × RawLCLoop)
    have r2 := (hsnd.runsOn ((N - j, step^[j] p) : ℕ × RawLCLoop)).seq (hstep j hj)
    have r3 := RunsOn.pair (K := 16) (by omega) r1 r2
    have he : (((N - j, step^[j] p) : ℕ × RawLCLoop).1 - 1) = N - (j + 1) := by
      simp only; omega
    simp only at r3
    rw [show N - j - 1 = N - (j + 1) by omega] at r3
    refine r3.mono ?_
    have hp1 : Enc.size ((N - j, step^[j] p) : ℕ × RawLCLoop) ≤ Zp M := by
      have := size_pair_le' ((N - j, step^[j] p) : ℕ × RawLCLoop)
      have h1 := hksize (N - j) (by omega)
      have h2 := hqsize j
      simp only at this; omega
    have h3 := hksize (N - (j + 1)) (by omega)
    have h4 := hqsize (j + 1)
    have e1 : cP * (Enc.size ((N - j, step^[j] p) : ℕ × RawLCLoop) + 1) ^ dP ≤ pw cP dP (Zp M) :=
      pw_mono cP dP hp1
    have e2 : cS * (Enc.size ((N - j, step^[j] p) : ℕ × RawLCLoop) + 1) ^ dS ≤ pw cS dS (Zp M) :=
      pw_mono cS dS hp1
    omega
  -- the loop, the setup and the read-off
  have hloop := runsOn_iterate_sum (K := 16) (Q := Body Q) (step := step) hBodyWf N p _ hbody
  have hs1 : RunsOn 16 Pstart p ((N, p) : ℕ × RawLCLoop) (c6 * (Enc.size p + 1) ^ d6) :=
    hstart.runsOn p
  have hs3 := hend.runsOn ((0 : ℕ), step^[N] p)
  have hall := hs1.seq (hloop.seq hs3)
  have hout : lcOutOf (((0 : ℕ), step^[N] p) : ℕ × RawLCLoop).2 = lcOut (lcSolveQ ansQ) p := rfl
  simp only at hall
  rw [hout] at hall
  refine hall.mono ?_
  -- the arithmetic
  have hsum : ∑ j ∈ Finset.range N, (10 ^ 7 * ((lcStepCalls ansQ (step^[j] p)).map τ).sum
        + 100 * ((f + 2) * PR M) + E2 M + 2)
      = 10 ^ 7 * ((lcCallsQ ansQ p).map τ).sum + N * (100 * ((f + 2) * PR M) + E2 M + 2) := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, sum_range_eq_list]
    have hc : lcCallsQ ansQ p = (List.range N).flatMap (fun j => lcStepCalls ansQ (step^[j] p)) :=
      rfl
    rw [hc, sum_map_flatMap]
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul]
    ring
  rw [hsum]
  have hfinB : Enc.size (((0 : ℕ), step^[N] p) : ℕ × RawLCLoop) ≤ Zp M := by
    have := size_pair_le' (((0 : ℕ), step^[N] p) : ℕ × RawLCLoop)
    have h1 := hksize 0 (Nat.zero_le _)
    have h2 := hqsize N
    simp only at this; omega
  have e1 : c7 * (Enc.size (((0 : ℕ), step^[N] p) : ℕ × RawLCLoop) + 1) ^ d7
      ≤ pw c7 d7 (Zp M) := pw_mono c7 d7 hfinB
  have e2 : c6 * (M + 1) ^ d6 = pw c6 d6 M := rfl
  have e3 : N * (100 * ((f + 2) * PR M) + E2 M + 2)
      ≤ f * (M * (300 * PR M + E2 M + 2)) := by
    have k1 : 100 * ((f + 2) * PR M) ≤ f * (300 * PR M) := by nlinarith
    have k2 : E2 M + 2 ≤ f * (E2 M + 2) := by nlinarith
    calc N * (100 * ((f + 2) * PR M) + E2 M + 2)
        ≤ M * (f * (300 * PR M) + f * (E2 M + 2)) :=
          Nat.mul_le_mul hNM (by omega)
      _ = f * (M * (300 * PR M + E2 M + 2)) := by ring
  have e4 : 1 + pw c6 d6 M + pw c7 d7 (Zp M) ≤ f * (1 + pw c6 d6 M + pw c7 d7 (Zp M)) := by
    nlinarith
  have e5 : f * Gf M ≤ f * pw c d M := Nat.mul_le_mul_left _ (hcd M)
  have e6 : f * Gf M = f * (M * (300 * PR M + E2 M + 2))
      + f * (1 + pw c6 d6 M + pw c7 d7 (Zp M)) := by rw [hGf]; ring
  rw [← hM]
  omega

/-- **Theorem 13.1.3 on the RAM** (§13.1), what the program of `Algo.theorem_13_1_3_ram`
computes and which calls it makes.  With a program `Q` answering String Isomorphism on the
windows, the output of Procedure LocalCertificates is the paper's triple: the window `W(T)`,
whether `T` is full, `K(T)`, and `M(T)`.  The calls to `Q` number at most `t!·n²`, and each
is on a window `W` with `t·|W| ≤ n` (when `t ≥ 5`), which is the paper's count "at most
`t!·n²` instances of String Isomorphism on windows of size at most `n/t`". -/
theorem theorem_13_1_3_ram_spec {n m : ℕ} {G : Subgroup (Perm (Fin n))}
    {ϕ : G →* Perm (Fin m)} {xs : RawStr} {tdom : List ℕ} (hc : LCCtxWF n m xs tdom)
    {st0 : RawLCSt} (h0 : StateFor hc (Babai.stages ϕ (decStrN n xs) (winSet m tdom) 0) st0)
    (ansQ : RawWinSI → RawCoset)
    (hQ : ∀ W, WinWF n W → decCoset n (ansQ W) = (decWinSI n W).answer) :
    winSet n (lcOut (lcSolveQ ansQ) ((xs, tdom), st0)).1
        = Babai.windowOut ϕ (decStrN n xs) (winSet m tdom) ∧
      ((lcOut (lcSolveQ ansQ) ((xs, tdom), st0)).2.1 = true
        ↔ Babai.isFullOut ϕ (decStrN n xs) (winSet m tdom)) ∧
      decGroup n (lcOut (lcSolveQ ansQ) ((xs, tdom), st0)).2.2.1
        = Babai.certK ϕ (decStrN n xs) (winSet m tdom) ∧
      decGroup tdom.length (lcOut (lcSolveQ ansQ) ((xs, tdom), st0)).2.2.2
        = (Babai.certM ϕ (decStrN n xs) (winSet m tdom)).map
          ((tName m tdom hc.nodup hc.ltM).symm.permCongrHom :
            Perm ↥(winSet m tdom) ≃* Perm (Fin tdom.length)).toMonoidHom ∧
      (lcCallsQ ansQ ((xs, tdom), st0)).length ≤ Nat.factorial tdom.length * n ^ 2 ∧
      (5 ≤ tdom.length → ∀ W ∈ lcCallsQ ansQ ((xs, tdom), st0),
        WinWF n W ∧ tdom.length * W.1.length ≤ n) := by
  have hsolve : ∀ I, LCWF n I → decCoset n (lcSolveQ ansQ I) = (decLCSI n I).answer :=
    fun I hI => lcSolveQ_correct hQ hI
  exact ⟨winSet_lcOut hsolve h0, lcOut_isFull hsolve h0, decGroup_lcOut_certK hsolve h0,
    decGroup_lcOut_certM hsolve h0, length_lcCallsQ_le hQ h0,
    fun h5 => window_lcCallsQ_le hQ h0 h5⟩

end Algo
