/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: the loop of Procedure "Design Lemma" (§8.2, lines 02–03) on the RAM.
-/
import Workspace.Algo.DesignPoly
import Workspace.Algo.WLVertex
import Workspace.Algo.FunctorsGuarded
import Workspace.Algo.DesignCongr

/-!
# §8.2 Procedure "Design Lemma" — the loop of lines 02–03, and the whole procedure

```
01 apply k-WL to X
02 for ℓ = 0 to k − 1
03   for x⃗ ∈ Ω^⟨ℓ⟩
04–08  the test at x⃗
```

`Workspace/Algo/DesignRaw.lean` is the test of lines 03–08 at one string (`Algo.returnsB`) and
the inner loop of line 03 at one *fixed* length (`Algo.scanLen`).  This file is the outer loop
of line 02, with the length **in the input**, and then the composition with line 01.

## How the loop is run

`Algo.polyFun_scanLen` has `ℓ` as a parameter of the theorem because `Algo.polyFun_tuplesOf` is
stated per length.  To put `ℓ` in the input the loop is run the way `Workspace/Algo/WLGuarded.lean`
runs the table builder: one pass of `RAM.QuasiFun.iterateSetup` whose state carries the list of
the strings of the current length, and which extends that list by one letter per round
(`Algo.extendStep`, the very fold that builds the table of `k`-tuples).  Round `j` tests the
strings of length `j`, so `k = |ks|` rounds cover `ℓ = 0 … k − 1` — the paper's loop exactly.
The answer, once set, is never overwritten (`Algo.scanStep` keeps the `some`), so the string
returned has the **least** returning length, which is what `Babai.KAryPartStruct.procedure`
selects with `Nat.find`.

Reading the strings of length `ℓ` off line 01's table of `k`-tuples as prefixes was the other
candidate; it fails in the degenerate case `n = 0`, where there is no `k`-tuple but the empty
string is a string of length `0`, and it would make the routine's meaning depend on `k > 0`.
The loop above has no such case.

The guard is the one of `Workspace/Algo/WLGuarded.lean`: the routine is a `RAM.QuasiFun` only
when the arity is below `Algo.guardBound c₀ n`, because the state holds `n^ℓ` strings; outside
the guard it answers `none` (a `RAM.QuasiFun` is total).  This is the paper's `n^{O(k)}` with
`k = O(log n)`.

## Main definitions

* `Algo.scanStep`, `Algo.ansUpTo` — one round of line 02, and the answer after `j` rounds;
* `Algo.rawDesignScan` — lines 02–08 on a table, guarded;
* `Algo.designProcedure` — lines 01–08, the whole procedure from the domain.

## Main results

* `Algo.rawDesignScan_some`, `Algo.rawDesignScan_none_iff` — the answer is a returning string of
  the least returning length, and `none` exactly when no string of length `< k` returns;
* `Algo.rawDesignScan_length_eq_procedure` — its length is the length
  `Babai.KAryPartStruct.procedure` returns;
* `Algo.quasiFun_rawDesignScan`, `Algo.quasiFun_designProcedure` — both are `RAM.QuasiFun`s.

No axiom and no `sorry`.
-/

namespace Algo

open Babai RAM

/-! ## The state of the loop

The state is `((z, L), ans)`: the input of the test (`Algo.DIn`, whose string slot is
overwritten at each string by `Algo.withStr`), the list `L` of the strings of the current
length, and the answer found so far. -/

/-- The state of the loop of line 02. -/
abbrev SState : Type := (DIn × List (List ℕ)) × Option (List ℕ)

/-- Line 03 over an explicit list of strings: the first string of the list at which the test of
lines 04–08 fires. -/
def scanPick (w : DIn × List (List ℕ)) : Option (List ℕ) :=
  (w.2.filter fun t => returnsB (withStr (w.1, t))).head?

theorem scanLen_eq_scanPick (l : ℕ) (z : DIn) :
    scanLen l z = scanPick (z, tuplesOf z.1.2.1 l) := rfl

/-- One round of the loop of line 02: run line 03 over the strings of the current length unless
an answer was already found, and lengthen the strings by one letter. -/
def scanStep (s : SState) : SState :=
  ((s.1.1, extendStep (s.1.1.1.2.1, s.1.2)), s.2.elim (scanPick s.1) some)

/-- The answer after the rounds `ℓ = 0 … j − 1`: the first returning string of the least
returning length below `j`. -/
def ansUpTo (z : DIn) : ℕ → Option (List ℕ)
  | 0 => none
  | j + 1 => (ansUpTo z j).elim (scanLen j z) some

theorem scanStep_iterate (z : DIn) : ∀ j : ℕ,
    scanStep^[j] (((z, [[]]), none) : SState) = ((z, tuplesOf z.1.2.1 j), ansUpTo z j)
  | 0 => rfl
  | j + 1 => by
      rw [Function.iterate_succ_apply', scanStep_iterate z j]
      show ((z, extendStep (z.1.2.1, tuplesOf z.1.2.1 j)),
        (ansUpTo z j).elim (scanPick (z, tuplesOf z.1.2.1 j)) some) = _
      rw [← tuplesOf_succ]
      rfl

/-! ## What the loop computes -/

theorem ansUpTo_isSome {z : DIn} : ∀ {j : ℕ} {xs : List ℕ}, ansUpTo z j = some xs →
    ∃ l, l < j ∧ scanLen l z = some xs := by
  intro j
  induction j with
  | zero => intro xs h; exact absurd h (by simp [ansUpTo])
  | succ j ih =>
      intro xs h
      rw [ansUpTo] at h
      cases hj : ansUpTo z j with
      | none =>
          rw [hj] at h
          exact ⟨j, Nat.lt_succ_self j, h⟩
      | some xs' =>
          rw [hj] at h
          have hxs : xs' = xs := by simpa using h
          obtain ⟨l, hl, hsc⟩ := ih (hxs ▸ hj)
          exact ⟨l, Nat.lt_succ_of_lt hl, hsc⟩

theorem ansUpTo_eq_none_iff {z : DIn} : ∀ {j : ℕ},
    ansUpTo z j = none ↔ ∀ l < j, scanLen l z = none := by
  intro j
  induction j with
  | zero => exact ⟨fun _ l hl => absurd hl (Nat.not_lt_zero l), fun _ => rfl⟩
  | succ j ih =>
      rw [ansUpTo]
      cases hj : ansUpTo z j with
      | none =>
          simp only [Option.elim]
          constructor
          · intro h l hl
            rcases Nat.lt_succ_iff_lt_or_eq.1 hl with hlt | rfl
            · exact ih.1 hj l hlt
            · exact h
          · intro h; exact h j (Nat.lt_succ_self j)
      | some xs =>
          simp only [Option.elim]
          constructor
          · intro h; exact absurd h (by simp)
          · intro h
            obtain ⟨l, hl, hsc⟩ := ansUpTo_isSome hj
            rw [h l (Nat.lt_succ_of_lt hl)] at hsc
            exact absurd hsc (by simp)

/-- **The answer of the loop has the least returning length.** -/
theorem ansUpTo_eq_some {z : DIn} : ∀ {j : ℕ} {xs : List ℕ}, ansUpTo z j = some xs →
    ∃ l, l < j ∧ scanLen l z = some xs ∧ ∀ l' < l, scanLen l' z = none := by
  intro j
  induction j with
  | zero => intro xs h; exact absurd h (by simp [ansUpTo])
  | succ j ih =>
      intro xs h
      rw [ansUpTo] at h
      cases hj : ansUpTo z j with
      | none =>
          rw [hj] at h
          exact ⟨j, Nat.lt_succ_self j, h, fun l' hl' => ansUpTo_eq_none_iff.1 hj l' hl'⟩
      | some xs' =>
          rw [hj] at h
          have hxs : xs' = xs := by simpa using h
          obtain ⟨l, hl, hsc, hmin⟩ := ih (hxs ▸ hj)
          exact ⟨l, Nat.lt_succ_of_lt hl, hsc, hmin⟩

/-- Every string the loop can answer is one of the strings it enumerates. -/
theorem ansUpTo_mem {z : DIn} {j : ℕ} {xs : List ℕ} (h : ansUpTo z j = some xs) :
    ∃ l, l < j ∧ xs ∈ tuplesOf z.1.2.1 l := by
  obtain ⟨l, hl, hsc⟩ := ansUpTo_isSome h
  refine ⟨l, hl, ?_⟩
  have := List.mem_of_mem_head? hsc
  exact (List.mem_filter.1 this).1

/-! ## The guarded loop -/

/-- The number of rounds: the arity `k = |ks|`, so that the lengths `ℓ = 0 … k − 1` are
covered — unless the arity exceeds the guard, in which case the loop is not run. -/
def scanRounds (c₀ : ℕ) (z : DIn) : ℕ :=
  if z.1.1.1.length ≤ guardBound c₀ z.1.2.1.length then z.1.1.1.length else 0

/-- The set-up of the loop: the number of rounds, and the state holding the single string of
length `0` and no answer. -/
def scanSetUp (c₀ : ℕ) (z : DIn) : ℕ × SState := (scanRounds c₀ z, ((z, [[]]), none))

/-- **Lines 02–08 of Procedure "Design Lemma"** on the table produced by line 01: the first
string, of the least length `ℓ ≤ k − 1`, at which the test of lines 04–08 fires. -/
def rawDesignScan (c₀ : ℕ) (z : DIn) : Option (List ℕ) :=
  (scanStep^[(scanSetUp c₀ z).1] (scanSetUp c₀ z).2).2

theorem rawDesignScan_eq (c₀ : ℕ) (z : DIn) :
    rawDesignScan c₀ z = ansUpTo z (scanRounds c₀ z) := by
  rw [rawDesignScan, scanSetUp, scanStep_iterate]

theorem scanRounds_of_guard {c₀ : ℕ} {z : DIn}
    (hg : z.1.1.1.length ≤ guardBound c₀ z.1.2.1.length) : scanRounds c₀ z = z.1.1.1.length :=
  if_pos hg

/-! ## The specification -/

section Spec

variable {n k a b c₀ : ℕ} {ks x₀ : List ℕ} {p : RawWL}

/-- **Lines 02–08, the answer.**  The string the procedure returns is a string of distinct
vertices of some length `ℓ < k` at which the paper's test fires, and no string of any smaller
length does. -/
theorem rawDesignScan_some {α : ℝ} (h : RawWL.WF n k p) (hk : ks.length = k) (hb : 0 < b)
    (hab : α = (a : ℝ) / (b : ℝ)) (hg : ks.length ≤ guardBound c₀ p.1.length) {xs : List ℕ}
    (hs : rawDesignScan c₀ (((ks, x₀), p), (a, b)) = some xs) :
    ∃ l, ∃ hl : l < k, ∃ x : Str (Fin n) l, tupleOf x = xs ∧
      Babai.KAryPartStruct.Returns α (decWL n k p) hl.le x ∧
      ∀ (l' : ℕ) (_ : l' < l), ∀ y : Str (Fin n) l',
        ¬ Babai.KAryPartStruct.Returns α (decWL n k p) (by omega : l' ≤ k) y := by
  rw [rawDesignScan_eq, scanRounds_of_guard hg] at hs
  obtain ⟨l, hl, hsc, hmin⟩ := ansUpTo_eq_some hs
  rw [hk] at hl
  obtain ⟨x, hx, hret⟩ := scanLen_some (x₀ := x₀) h hk hl.le hb hab hsc
  refine ⟨l, hl, x, hx, hret, fun l' hl' y => ?_⟩
  exact (scanLen_none_iff (x₀ := x₀) h hk (by omega) hb hab).1 (hmin l' hl') y

/-- **Lines 02–08, exhaustiveness.**  The procedure returns nothing exactly when the paper's
test fires at no string of length `ℓ < k`. -/
theorem rawDesignScan_none_iff {α : ℝ} (h : RawWL.WF n k p) (hk : ks.length = k) (hb : 0 < b)
    (hab : α = (a : ℝ) / (b : ℝ)) (hg : ks.length ≤ guardBound c₀ p.1.length) :
    rawDesignScan c₀ (((ks, x₀), p), (a, b)) = none
      ↔ ∀ l, ¬ Babai.KAryPartStruct.ReturnsAt α (decWL n k p) l := by
  rw [rawDesignScan_eq, scanRounds_of_guard hg, ansUpTo_eq_none_iff, hk]
  constructor
  · rintro hall l ⟨hlk, x, hx⟩
    exact (scanLen_none_iff (x₀ := x₀) h hk hlk.le hb hab).1 (hall l hlk) x hx
  · intro hno l hl
    refine (scanLen_none_iff (x₀ := x₀) h hk hl.le hb hab).2 (fun x hx => ?_)
    exact hno l ⟨hl, x, hx⟩

/-- **The loop agrees with `Babai.KAryPartStruct.procedure` where it must.**  The mathematical
procedure chooses its string with `Exists.choose` and the paper prescribes no order on `Ω^⟨ℓ⟩`
(risk R-A9-1), so the two strings need not be the same; but the *length* is determined — it is
the least returning length — and it is the same. -/
theorem rawDesignScan_length_eq_procedure {α : ℝ} (h : RawWL.WF n k p) (hk : ks.length = k)
    (hb : 0 < b) (hab : α = (a : ℝ) / (b : ℝ)) (hg : ks.length ≤ guardBound c₀ p.1.length)
    {xs : List ℕ} (hs : rawDesignScan c₀ (((ks, x₀), p), (a, b)) = some xs) :
    ∃ q : Σ l : ℕ, Str (Fin n) l, (decWL n k p).procedure α = some q ∧ q.1 = xs.length := by
  classical
  obtain ⟨l, hl, x, hx, hret, hmin⟩ := rawDesignScan_some (x₀ := x₀) h hk hb hab hg hs
  have hex : ∃ l, Babai.KAryPartStruct.ReturnsAt α (decWL n k p) l := ⟨l, hl, x, hret⟩
  have hfind : Nat.find hex = l := by
    refine Nat.find_eq_iff hex |>.2 ⟨⟨hl, x, hret⟩, fun l' hl' hc => ?_⟩
    obtain ⟨hlk, y, hy⟩ := hc
    exact hmin l' hl' y hy
  refine ⟨⟨Nat.find hex, ((Nat.find_spec hex).choose_spec).choose⟩, ?_, ?_⟩
  · rw [Babai.KAryPartStruct.procedure, dif_pos hex]
  · show Nat.find hex = xs.length
    rw [hfind, ← hx]
    simp

/-- The procedure returns nothing exactly when `Babai.KAryPartStruct.procedure` does. -/
theorem rawDesignScan_none_iff_procedure {α : ℝ} (h : RawWL.WF n k p) (hk : ks.length = k)
    (hb : 0 < b) (hab : α = (a : ℝ) / (b : ℝ)) (hg : ks.length ≤ guardBound c₀ p.1.length) :
    rawDesignScan c₀ (((ks, x₀), p), (a, b)) = none ↔ (decWL n k p).procedure α = none := by
  classical
  rw [rawDesignScan_none_iff (x₀ := x₀) h hk hb hab hg, Babai.KAryPartStruct.procedure]
  constructor
  · intro hno
    rw [dif_neg (fun hc => (hno hc.choose) hc.choose_spec)]
  · intro hpr l hl
    by_cases hex : ∃ l, Babai.KAryPartStruct.ReturnsAt α (decWL n k p) l
    · rw [dif_pos hex] at hpr; exact absurd hpr (by simp)
    · exact hex ⟨l, hl⟩

end Spec

/-! ## The cost of the loop -/

theorem polyFun_scanPick : PolyFun scanPick := by
  have hq : PolyFun (fun s : (DIn × List (List ℕ)) × List ℕ =>
      returnsB (withStr (s.1.1, s.2))) :=
    (((polyFun_fst.comp polyFun_fst).pair polyFun_snd).comp polyFun_withStr).comp
      polyFun_returnsB
  exact ((polyFun_id.pair polyFun_snd).comp (PolyFun.filterParam hq)).comp polyFun_headOption

theorem polyFun_scanStep : PolyFun scanStep := by
  have hdom : PolyFun (fun s : SState => s.1.1.1.2.1) :=
    polyFun_fst.comp polyFun_fst |>.comp polyFun_fst |>.comp polyFun_snd |>.comp polyFun_fst
  have hext : PolyFun (fun s : SState => extendStep (s.1.1.1.2.1, s.1.2)) :=
    (hdom.pair (polyFun_fst.comp polyFun_snd)).comp polyFun_extendStep
  have hfst : PolyFun (fun s : SState => ((s.1.1, extendStep (s.1.1.1.2.1, s.1.2)) :
      DIn × List (List ℕ))) := (polyFun_fst.comp polyFun_fst).pair hext
  have hsnd : PolyFun (fun s : SState => s.2.elim (scanPick s.1) some) := by
    have h := PolyFun.optionElim (β := List ℕ) (σ := DIn × List (List ℕ))
      (g := scanPick) (h := fun q : List ℕ × (DIn × List (List ℕ)) => some q.1)
      polyFun_scanPick (polyFun_fst.comp polyFun_some)
    exact ((polyFun_snd.pair polyFun_fst).comp h).of_eq (fun s => rfl)
  exact hfst.pair hsnd

theorem polyFun_guardBoundDom (c₀ : ℕ) :
    PolyFun (fun z : DIn => guardBound c₀ z.1.2.1.length) := by
  have hn : PolyFun (fun z : DIn => Nat.log 2 z.1.2.1.length) :=
    ((polyFun_fst.comp polyFun_snd |>.comp polyFun_fst).comp polyFun_length).comp polyFun_log2
  exact polyFun_powConst (hn.add (polyFun_const 1)) c₀

theorem polyFun_scanRounds (c₀ : ℕ) : PolyFun (scanRounds c₀) := by
  have hk : PolyFun (fun z : DIn => z.1.1.1.length) :=
    (polyFun_fst.comp polyFun_fst |>.comp polyFun_fst).comp polyFun_length
  refine (PolyFun.ite (hk.le (polyFun_guardBoundDom c₀)) hk (polyFun_const 0)).of_eq
    (fun z => ?_)
  by_cases h : z.1.1.1.length ≤ guardBound c₀ z.1.2.1.length <;> simp [scanRounds, h]

theorem polyFun_scanSetUp (c₀ : ℕ) : PolyFun (scanSetUp c₀) :=
  ((polyFun_scanRounds c₀).pair ((polyFun_id.pair (polyFun_const [[]])).pair
    (polyFun_const none))).of_eq (fun z => rfl)

/-! ### The state of the loop is quasipolynomially large

The state holds the input, the `n^ℓ` strings of the current length and the answer.  Under the
guard `ℓ ≤ k ≤ (log₂ n + 1)^{c₀}`, this is the counting of `Algo.size_state_le`. -/

/-- The quasipolynomial bound on the size of every state the loop of line 02 passes through. -/
def scanSizeBound (c₀ N : ℕ) : ℕ :=
  4 * N + 4 * (1 + 2 ^ ((Nat.log 2 N + 2) ^ (c₀ + 1))
      * (2 * (1 + (Nat.log 2 N + 2) ^ c₀ * (2 * N + 1)) + 1))
    + 2 * ((1 + (Nat.log 2 N + 2) ^ c₀ * (2 * N + 1)) + 2)

theorem quasiPolyBound_scanSizeBound (c₀ : ℕ) : QuasiPolyBound (scanSizeBound c₀) := by
  have hT : PolyBound (fun n : ℕ => 1 + (Nat.log 2 n + 2) ^ c₀ * (2 * n + 1)) :=
    (polyBound_const 1).add ((polyBound_logPow c₀).mul
      (((polyBound_const 2).mul polyBound_id).add (polyBound_const 1)))
  have h4 : QuasiPolyBound (fun n : ℕ => 4 * n + 4 * (1 + 2 ^ ((Nat.log 2 n + 2) ^ (c₀ + 1))
      * (2 * (1 + (Nat.log 2 n + 2) ^ c₀ * (2 * n + 1)) + 1))) :=
    ((polyBound_const 4).mul polyBound_id).quasiPoly.add
      ((polyBound_const 4).quasiPoly.mul ((polyBound_const 1).quasiPoly.add
        ((quasiPolyBound_witness (c₀ + 1)).mul
          (((polyBound_const 2).mul hT).add (polyBound_const 1)).quasiPoly)))
  exact h4.add ((polyBound_const 2).quasiPoly.mul (hT.add (polyBound_const 2)).quasiPoly)

/-- The scan state is bounded by any ambient input-size bound. This also
covers the top domain in Section 15, whose arity is bounded using `|Ω|`. -/
theorem size_scanIterate_le (c₀ : ℕ) (z : DIn) (N j : ℕ)
    (hz : Enc.size z ≤ N) (hB : j ≤ (Nat.log 2 N + 1) ^ c₀) :
    Enc.size (scanStep^[j] (((z, [[]]), none) : SState)) ≤ scanSizeBound c₀ N := by
  classical
  set dom := z.1.2.1 with hdomdef
  set T := 1 + (Nat.log 2 N + 2) ^ c₀ * (2 * N + 1) with hT
  set R := 2 ^ ((Nat.log 2 N + 2) ^ (c₀ + 1)) with hR
  -- the vertex list is a part of the input
  have hdomN : Enc.size dom ≤ N := by
    exact ((size_fst_le' z.1.2).trans ((size_snd_le' z.1).trans (size_fst_le' z))).trans hz
  have hnN : dom.length ≤ N := le_trans (length_le_size dom) hdomN
  have hB2 : j ≤ (Nat.log 2 N + 2) ^ c₀ :=
    le_trans hB (Nat.pow_le_pow_left (by omega) c₀)
  rw [scanStep_iterate]
  change Enc.size (((z, tuplesOf dom j), ansUpTo z j) : SState) ≤ scanSizeBound c₀ N
  -- every string of the current length is short
  have hentm : ∀ m ≤ j, ∀ t ∈ tuplesOf dom m, Enc.size t ≤ T := by
    intro m hm t ht
    obtain ⟨hlen, hmem⟩ := (mem_tuplesOf dom m t).1 ht
    have h := size_list_le_of_entries t N
      (fun x hx => le_trans (size_mem_le (hmem x hx)) hdomN)
    rw [hlen] at h
    have h2 : m * (2 * N + 1) ≤ (Nat.log 2 N + 2) ^ c₀ * (2 * N + 1) :=
      Nat.mul_le_mul_right _ (le_trans hm hB2)
    omega
  have hent : ∀ t ∈ tuplesOf dom j, Enc.size t ≤ T := hentm j le_rfl
  have hcount : (tuplesOf dom j).length ≤ R := by
    rw [length_tuplesOf]
    exact pow_le_quasi hnN hB
  have hlist : Enc.size (tuplesOf dom j) ≤ 1 + R * (2 * T + 1) := by
    have h := size_list_le_of_entries (tuplesOf dom j) T hent
    have h2 : (tuplesOf dom j).length * (2 * T + 1) ≤ R * (2 * T + 1) :=
      Nat.mul_le_mul_right _ hcount
    omega
  -- the answer found so far is one of those strings
  have hans : Enc.size (ansUpTo z j) ≤ T + 2 := by
    cases hA : ansUpTo z j with
    | none => rw [size_none]; omega
    | some xs =>
        obtain ⟨l, hl, hmem⟩ := ansUpTo_mem hA
        have hle : Enc.size xs ≤ T := hentm l (le_of_lt hl) xs hmem
        rw [size_some_eq]
        omega
  have hpair1 : Enc.size ((z, tuplesOf dom j) : DIn × List (List ℕ))
      ≤ 2 * N + 2 * Enc.size (tuplesOf dom j) :=
    (size_pair_le' _).trans (Nat.add_le_add (Nat.mul_le_mul_left 2 hz) le_rfl)
  have hpair2 : Enc.size (((z, tuplesOf dom j), ansUpTo z j) : SState)
      ≤ 2 * Enc.size ((z, tuplesOf dom j) : DIn × List (List ℕ))
        + 2 * Enc.size (ansUpTo z j) := size_pair_le' _
  rw [scanSizeBound, ← hT, ← hR]
  omega

/-- **The state of the loop of line 02 stays quasipolynomially small.** -/
theorem size_scanState_le (c₀ : ℕ) (z : DIn) (j : ℕ) (hj : j ≤ (scanSetUp c₀ z).1) :
    Enc.size (scanStep^[j] (scanSetUp c₀ z).2) ≤ scanSizeBound c₀ (Enc.size z) := by
  apply size_scanIterate_le c₀ z (Enc.size z) j le_rfl
  have hn : z.1.2.1.length ≤ Enc.size z :=
    (length_le_size _).trans ((size_fst_le' z.1.2).trans
      ((size_snd_le' z.1).trans (size_fst_le' z)))
  by_cases hg : z.1.1.1.length ≤ guardBound c₀ z.1.2.1.length
  · have hj' : j ≤ z.1.1.1.length := by simpa [scanSetUp, scanRounds, hg] using hj
    exact (hj'.trans hg).trans (Nat.pow_le_pow_left
      (Nat.add_le_add_right (Nat.log_mono_right hn) 1) c₀)
  · have : j = 0 := by simpa [scanSetUp, scanRounds, hg] using hj
    subst j
    exact Nat.zero_le _

/-- **Lines 02–08 are a `RAM.QuasiFun`.**  With the arity in the input and guarded by
`k ≤ (log₂ n + 1)^{c₀}`, the loop over `ℓ = 0 … k − 1` of line 02 and the loop over the
strings of line 03 run in quasipolynomial time: the paper's `n^{O(k)}` for `k = O(log n)`. -/
theorem quasiFun_rawDesignScan (c₀ : ℕ) : QuasiFun (rawDesignScan c₀) := by
  have hstep : QuasiFun (fun x : ℕ × SState => (x.1 - 1, scanStep x.2)) :=
    ((polyFun_fst.sub (polyFun_const 1)).pair (polyFun_snd.comp polyFun_scanStep)).quasiFun
  refine (QuasiFun.iterateSetup (q := fun n => n) (p := scanSizeBound c₀)
    (polyFun_scanSetUp c₀).quasiFun hstep polyFun_snd.quasiFun ?_ polyBound_id.quasiPoly
    (size_scanState_le c₀) (quasiPolyBound_scanSizeBound c₀)).of_eq (fun z => rfl)
  intro z
  show (scanSetUp c₀ z).1 ≤ Enc.size z
  have hle : z.1.1.1.length ≤ Enc.size z :=
    le_trans (length_le_size _) (le_trans (size_fst_le' z.1.1)
      (le_trans (size_fst_le' z.1) (size_fst_le' z)))
  by_cases hg : z.1.1.1.length ≤ guardBound c₀ z.1.2.1.length
  · have : (scanSetUp c₀ z).1 = z.1.1.1.length := by rw [scanSetUp]; exact if_pos hg
    omega
  · have : (scanSetUp c₀ z).1 = 0 := by rw [scanSetUp]; exact if_neg hg
    omega

/-! ## Lines 01–08: the whole procedure

Line 01 is *"apply `k`-WL to `X`"* — the pipeline `F3 ∘ F2 ∘ F1` of §5.2 applied to the input
relational structure `X = (Ω, R)` (`Algo.guardedPipeline321`, `Workspace/Algo/FunctorsGuarded.lean`),
under the same guard on the arity as the scan.  The input of the whole procedure is therefore the
arity carrier, the vertex list, the relations, and the threshold. -/

/-- The input of the whole procedure: the `k`-ary structure `X = (Ω, R)` as `(ks, Ω)` together
with its relations, and the threshold `α = a / b`. -/
abbrev GIn : Type := PIn × (ℕ × ℕ)

/-- **Procedure "Design Lemma" (§8.2), lines 01–08.**  Apply `k`-ary WL refinement to the input
structure `X = (Ω, R)` — that is, the pipeline `F3 ∘ F2 ∘ F1` of §5.2 — then run the loops of
lines 02–03 with the tests of lines 04–08 on the refined table.  The answer is the string `x⃗` at
which lines 05 or 08 fire. -/
def designProcedure (c₀ : ℕ) (g : GIn) : Option (List ℕ) :=
  rawDesignScan c₀ (((g.1.1.1, []), guardedPipeline321 c₀ g.1), g.2)

/-- **The whole procedure is a `RAM.QuasiFun`.**  This is the running-time clause of
Thm. 8.1.2, *"in time `n^{O(k)}`"*, read with `k = O(log n)` in the input, on the unit-cost RAM
of `Workspace/Machine`. -/
theorem quasiFun_designProcedure (c₀ : ℕ) : QuasiFun (designProcedure c₀) := by
  have hin : QuasiFun (fun g : GIn =>
      (((g.1.1.1, ([] : List ℕ)), guardedPipeline321 c₀ g.1), g.2) : GIn → DIn) :=
    (((((polyFun_fst.comp polyFun_fst).comp polyFun_fst).pair
      (polyFun_const ([] : List ℕ))).quasiFun.pair
      (polyFun_fst.comp_quasiFun (quasiFun_guardedPipeline321 c₀))).pair polyFun_snd.quasiFun)
  exact (hin.comp (quasiFun_rawDesignScan c₀)).of_eq (fun g => rfl)

/-! ### What the whole procedure computes -/

theorem fst_guardedPipeline (c₀ : ℕ) (a : List ℕ × List ℕ) :
    (guardedPipeline c₀ a).1 = a.2 := by
  rw [guardedPipeline, fst_rawWLStable]
  by_cases hg : a.1.length ≤ guardBound c₀ a.2.length
  · rw [guardedTable_of_guard hg]; rfl
  · rw [guardedTable_of_not_guard hg]

section Whole

variable {n k a b c₀ : ℕ} {ks dom : List ℕ} {rels : RawRelStruct}

/-- Line 01 under the guard: the table the pipeline of §5.2 produces is well formed. -/
theorem wf_line01 (hnd : dom.Nodup) (hmem : ∀ c, c ∈ dom ↔ c < n) (hk : ks.length = k)
    (hg : ks.length ≤ guardBound c₀ dom.length) :
    RawWL.WF n k (guardedPipeline321 c₀ ((ks, dom), rels)) := by
  subst hk
  exact guardedPipeline321_wf (a := ((ks, dom), rels)) hnd hmem hg

/-- **Line 01 computes `F3 ∘ F2 ∘ F1` of the input structure.**  The table the procedure scans
has exactly the color classes of the `k`-ary coherent configuration of §5.2. -/
theorem classes_line01 (hnd : dom.Nodup) (hmem : ∀ c, c ∈ dom ↔ c < n) (hk : ks.length = k)
    (hg : ks.length ≤ guardBound c₀ dom.length) (x x' : Str (Fin n) k) :
    (decWL n k (guardedPipeline321 c₀ ((ks, dom), rels))).color x
        = (decWL n k (guardedPipeline321 c₀ ((ks, dom), rels))).color x'
      ↔ (decRel n k rels).F1.F2.F3.color x = (decRel n k rels).F1.F2.F3.color x' := by
  subst hk
  exact guardedPipeline321_spec (a := ((ks, dom), rels)) hnd hmem hg x x'

/-- **Procedure "Design Lemma", the answer.**  The string the procedure returns is a string of
distinct vertices of some length `ℓ ≤ k − 1` at which the test of lines 04–08 fires in the
`k`-ary coherent configuration `F3(F2(F1(X)))` produced by line 01 from the input structure
`X = (Ω, R)`, and no string of smaller length does. -/
theorem designProcedure_some {α : ℝ} (hnd : dom.Nodup) (hmem : ∀ c, c ∈ dom ↔ c < n)
    (hk : ks.length = k) (hb : 0 < b) (hab : α = (a : ℝ) / (b : ℝ))
    (hg : ks.length ≤ guardBound c₀ dom.length) {xs : List ℕ}
    (hs : designProcedure c₀ (((ks, dom), rels), (a, b)) = some xs) :
    ∃ l, ∃ hl : l < k, ∃ x : Str (Fin n) l, tupleOf x = xs ∧
      Babai.KAryPartStruct.Returns α (decRel n k rels).F1.F2.F3 hl.le x ∧
      ∀ (l' : ℕ) (_ : l' < l), ∀ y : Str (Fin n) l',
        ¬ Babai.KAryPartStruct.Returns α (decRel n k rels).F1.F2.F3
            (by omega : l' ≤ k) y := by
  have hwf : RawWL.WF n k (guardedPipeline321 c₀ ((ks, dom), rels)) :=
    wf_line01 (rels := rels) hnd hmem hk hg
  have hcl := classes_line01 (rels := rels) (c₀ := c₀) hnd hmem hk hg
  have hguard : ks.length
      ≤ guardBound c₀ (guardedPipeline321 c₀ ((ks, dom), rels)).1.length := by
    rw [fst_guardedPipeline321]; exact hg
  obtain ⟨l, hl, x, hx, hret, hmin⟩ :=
    rawDesignScan_some (x₀ := []) hwf hk hb hab hguard hs
  exact ⟨l, hl, x, hx, (returns_congr hcl hl.le x).1 hret,
    fun l' hl' y hc => hmin l' hl' y ((returns_congr hcl (by omega) y).2 hc)⟩

/-- **Procedure "Design Lemma", exhaustiveness.**  The procedure returns nothing exactly when
the test of lines 04–08 fires at no string of length `ℓ ≤ k − 1` of `F3(F2(F1(X)))`, that is
exactly when `Babai.KAryPartStruct.procedure` returns nothing on that structure. -/
theorem designProcedure_none_iff {α : ℝ} (hnd : dom.Nodup) (hmem : ∀ c, c ∈ dom ↔ c < n)
    (hk : ks.length = k) (hb : 0 < b) (hab : α = (a : ℝ) / (b : ℝ))
    (hg : ks.length ≤ guardBound c₀ dom.length) :
    designProcedure c₀ (((ks, dom), rels), (a, b)) = none
      ↔ ((decRel n k rels).F1.F2.F3).procedure α = none := by
  have hwf : RawWL.WF n k (guardedPipeline321 c₀ ((ks, dom), rels)) :=
    wf_line01 (rels := rels) hnd hmem hk hg
  have hcl := classes_line01 (rels := rels) (c₀ := c₀) hnd hmem hk hg
  have hguard : ks.length
      ≤ guardBound c₀ (guardedPipeline321 c₀ ((ks, dom), rels)).1.length := by
    rw [fst_guardedPipeline321]; exact hg
  rw [show designProcedure c₀ (((ks, dom), rels), (a, b))
      = rawDesignScan c₀ (((ks, []), guardedPipeline321 c₀ ((ks, dom), rels)), (a, b)) from rfl,
    rawDesignScan_none_iff_procedure (x₀ := []) hwf hk hb hab hguard]
  exact procedure_eq_none_congr hcl

end Whole

end Algo
