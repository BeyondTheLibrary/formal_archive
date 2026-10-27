/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Sections 9.4-9.8: Procedure Bipartite Split-or-Johnson as a recursion on the measure of
progress of Section 9.5.
-/
import Workspace.SplitOrJohnson.BipBlocks
import Workspace.SplitOrJohnson.Depth
import Workspace.SplitOrJohnson.Hint
import Workspace.SplitOrJohnson.KerPart
import Workspace.SplitOrJohnson.WLColor
import Mathlib.Combinatorics.Colex

/-!
# §9.4-§9.8  Procedure Bipartite Split-or-Johnson as a recursion

Version 2.5, lines 4101-4182 of `babai-gi-source/quasi25.txt`.

Theorem 9.2.2 is proved by a procedure that, in several of its steps, hands a smaller
instance back to Theorem 9.2.2 itself.  §9.5 is what makes this terminate.  This file is
the skeleton of that recursion in the wider category `Babai.BipBlockInputs` of
`Workspace/SplitOrJohnson/BipBlocks.lean`, in which a vertex of `V₂` is a block of points.

## The measure of progress

§9.5 says:

> *"Throughout the process, `n₁ = |V₁|` will not increase.  We say that a parameter `m` is
> significantly reduced if `m_new ≤ 0.9 m_old`.  We deem to have made major progress if any
> of the following occurs: goal (a) or (b) is achieved; `n₂` is significantly reduced; `X₂`
> moves from clique to UPCC while `n₂` does not increase."*

`Babai.measure_9_5` turns the three kinds of major progress into the single natural number

  `m(X) = 2 n₂ + (0 if `X` carries the hint, else 1)`,

where *carrying the hint* is `Babai.VColBipBlk.HasHint`: the coloring `h` of the pairs of
blocks is, on the blocks, the coloring of a homogeneous coherent configuration of rank
`≥ 3` — the structure that a previous turn found on `V₂` (§9.7, Cases 3a1, 3a2 and 3b).
An isomorphism preserves the measure (`Babai.measure_9_5_congr`), and the recursion lowers
it at every turn:

* *goal (a) or (b) is achieved*: the turn returns an outcome and makes no recursive call,
  so no drop is needed;
* *`n₂` is significantly reduced*: `10 n₂_new ≤ 9 n₂_old` forces `n₂_new < n₂_old`
  whenever `n₂_old ≥ 1`, so `2 n₂` drops by at least **two** and the bit can only cost
  back one;
* *`X₂` moves from clique to UPCC while `n₂` does not increase*: this is the one turn at
  which `n₂` may stay put; the object handed back carries the hint and the one the turn
  started from did not, so the bit drops from `1` to `0`.

See the entry on §9.7, Cases 3a1, 3a2 and 3b in the corrected paper.

## The cost

The multiplicative cost of the whole recursion is one quasipolynomial per turn
(`Babai.turnCost`; §9.7, Case 3a applies the Design Lemma at a multiplicative cost of
`n₂^{d₁}` with `d₁ ≤ (7/3) log₂ n₁`) raised to the number of turns, which is
`O(log n₂)` by §9.5 (`Babai.steps09`), times a constant that absorbs the two bounded steps
1 and 2.  The exponent is `2 (steps09 n₂) + 1 + (the hint bit)`: **two** turns per
significant reduction of `n₂`, because between two reductions the procedure may spend one
turn on the third kind of progress, and the odd summand pays for that turn.  `Babai.cost_9_4` is that cost, and `Babai.quasiPolyBound_costBound` says it is
quasipolynomial.

## Numbering map

| Paper | Lean |
|---|---|
| §9.5, the measure of progress | `Babai.measure_9_5` |
| §9.4, the cost of the recursion | `Babai.cost_9_4` |
| §9.4, step 1 (`n₁ ≤ C₀`) | `Babai.step_9_4_1` |
| §9.4, step 2 (`n₂ ≤ c log n₁`) | `Babai.step_9_4_2` |
| §9.4, step 3 (WL refinement) | `Babai.VColBipBlk.wlColor` (`Workspace/SplitOrJohnson/WLColor.lean`) |
| §9.4, step 4 (`all vertex-color classes small`) | `Babai.AllClassesSmall`, `Babai.step_9_4_4` |
| §9.4, step 5 (the dominant color class `W₁`) | `Babai.dominantClass` |
| §9.4, step 5 (`α ← α n₁ / \|W₁\|`) | `Babai.alphaNew`, `Babai.claim_9_4_step5_at` |
| §9.4, steps 5 and 7 (the induced substructure) | `Babai.VColBipBlk.restrictTo` |
| §9.4, step 5 (`X ← X[W₁ ∪ V₂]`) | `Babai.step5Obj` |
| §9.4, step 5 (the restricted instance is admissible) | `Babai.step5Obj_isThm922Input` |
| §9.4, steps 5-9 and the three cases §9.6-§9.8 | `Babai.steps_9_4_5_to_9` (`Workspace/SplitOrJohnson/Turn.lean`) |
| §9.4, steps 3-9 | `Babai.steps_9_4_3_to_9` (`Workspace/SplitOrJohnson/Turn.lean`) |
| §9.4, one turn of the procedure | `Babai.procedure_9_4_turn` (`Workspace/SplitOrJohnson/Turn.lean`) |
| Theorem 9.2.2 in the wider category | `Babai.theorem_9_2_2_blocks` (`Workspace/SplitOrJohnson/Turn.lean`) |
-/

namespace Babai

/-! ### The number of blocks and the first part -/

namespace VColBipBlk

variable {s t : Type} {κ : Type} [Zero κ]

/-- The blocks of an isomorphic copy are the images of the blocks. -/
theorem blocks_image_of_isIsoTo {X : VColBipBlk s κ} {Y : VColBipBlk t κ} {φ : s ≃ t}
    (h : X.IsIsoTo Y φ) : Y.blocks = (fun B => φ '' B) '' X.blocks := by
  ext B'
  constructor
  · intro hB'
    refine ⟨φ.symm '' B', ?_, ?_⟩
    · rw [← h.blocks (φ.symm '' B'), Equiv.image_symm_image]; exact hB'
    · show φ '' (φ.symm '' B') = B'
      rw [Equiv.image_symm_image]
  · rintro ⟨B, hB, rfl⟩
    exact (h.blocks B).2 hB

/-- `|V₂|`, the number of blocks, is an isomorphism invariant. -/
theorem numBlocks_eq_of_isIsoTo {X : VColBipBlk s κ} {Y : VColBipBlk t κ} {φ : s ≃ t}
    (h : X.IsIsoTo Y φ) : X.numBlocks = Y.numBlocks := by
  rw [numBlocks, numBlocks, blocks_image_of_isIsoTo h,
    Set.ncard_image_of_injective _ (Set.image_injective.2 φ.injective)]

/-- The first part of an isomorphic copy is the image of the first part. -/
theorem V₁_image_of_isIsoTo {X : VColBipBlk s κ} {Y : VColBipBlk t κ} {φ : s ≃ t}
    (h : X.IsIsoTo Y φ) : Y.V₁ = φ '' X.V₁ := by
  ext y
  simp only [V₁, Set.mem_setOf_eq, Set.mem_image]
  constructor
  · intro hy
    exact ⟨φ.symm y, by rw [← h.part₁ (φ.symm y), Equiv.apply_symm_apply]; exact hy,
      φ.apply_symm_apply y⟩
  · rintro ⟨x, hx, rfl⟩
    exact (h.part₁ x).2 hx

/-- `|V₁|` is an isomorphism invariant. -/
theorem V₁_ncard_eq_of_isIsoTo {X : VColBipBlk s κ} {Y : VColBipBlk t κ} {φ : s ≃ t}
    (h : X.IsIsoTo Y φ) : X.V₁.ncard = Y.V₁.ncard := by
  rw [V₁_image_of_isIsoTo h, Set.ncard_image_of_injective _ φ.injective]

/-- The blocks are pairwise disjoint and non-empty, so there are at most as many of them
as there are points. -/
theorem numBlocks_le_card [Fintype s] (X : VColBipBlk s κ) :
    X.numBlocks ≤ Fintype.card s := by
  classical
  rcases isEmpty_or_nonempty s with hs | hs
  · have hb : X.blocks = ∅ := by
      ext B
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hB
      obtain ⟨x, -⟩ := X.blocks_nonempty B hB
      exact hs.elim x
    simp [numBlocks, hb]
  · -- choose one point in each block
    set f : Set s → s := fun B => if h : B.Nonempty then h.some else Classical.arbitrary s
      with hf
    have hinj : Set.InjOn f X.blocks := by
      intro B hB B' hB' heq
      by_contra hne
      have h1 : B.Nonempty := X.blocks_nonempty B hB
      have h2 : B'.Nonempty := X.blocks_nonempty B' hB'
      rw [hf] at heq
      simp only [dif_pos h1, dif_pos h2] at heq
      have hx1 : h1.some ∈ B := h1.some_mem
      have hx2 : h2.some ∈ B' := h2.some_mem
      rw [← heq] at hx2
      exact (Set.disjoint_left.1 (X.blocks_disjoint B hB B' hB' hne)) hx1 hx2
    have hle : X.blocks.ncard ≤ (Set.univ : Set s).ncard :=
      Set.ncard_le_ncard_of_injOn f (fun _ _ => Set.mem_univ _) hinj Set.finite_univ
    rwa [Set.ncard_univ, Nat.card_eq_fintype_card] at hle

end VColBipBlk

/-! ### The measure of progress -/

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

/-- §9.5.  `n₂ = |V₂|` of an admissible input: the **number of blocks**. -/
noncomputable def BipBlockInputs.numBlocks (X : Pt (BipBlockInputs Ω)) : ℕ :=
  X.obj.1.1.numBlocks

/-- §9.4.  `n₁ = |V₁|` of an admissible input. -/
noncomputable def BipBlockInputs.n₁ (X : Pt (BipBlockInputs Ω)) : ℕ := X.obj.1.1.V₁.ncard

/-- An isomorphism of admissible inputs is an isomorphism of the underlying graphs. -/
theorem BipBlockInputs.isIsoTo_of_isoP {X Y : Pt (BipBlockInputs Ω)}
    {φ : ↥X.car ≃ ↥Y.car} (hφ : φ ∈ (BipBlockInputs Ω).IsoP X Y) :
    X.obj.1.1.IsIsoTo Y.obj.1.1 φ := hφ.2

theorem BipBlockInputs.numBlocks_congr {X Y : Pt (BipBlockInputs Ω)}
    (h : ((BipBlockInputs Ω).IsoP X Y).Nonempty) :
    BipBlockInputs.numBlocks X = BipBlockInputs.numBlocks Y := by
  obtain ⟨φ, hφ⟩ := h
  exact VColBipBlk.numBlocks_eq_of_isIsoTo (BipBlockInputs.isIsoTo_of_isoP hφ)

theorem BipBlockInputs.n₁_congr {X Y : Pt (BipBlockInputs Ω)}
    (h : ((BipBlockInputs Ω).IsoP X Y).Nonempty) :
    BipBlockInputs.n₁ X = BipBlockInputs.n₁ Y := by
  obtain ⟨φ, hφ⟩ := h
  exact VColBipBlk.V₁_ncard_eq_of_isIsoTo (BipBlockInputs.isIsoTo_of_isoP hφ)

theorem BipBlockInputs.numBlocks_le_ncard (X : Pt (BipBlockInputs Ω)) :
    BipBlockInputs.numBlocks X ≤ X.car.ncard := by
  letI : Fintype ↥X.car := Fintype.ofFinite _
  have h := X.obj.1.1.numBlocks_le_card
  rw [← Nat.card_eq_fintype_card] at h
  exact h

/-- §9.5.  **The measure of progress.**  The three kinds of major progress of §9.5 in one
natural number: `2 n₂ + 1`.  A significant reduction of `n₂` lowers it by at least two, and
the one turn at which `n₂` may stay put — *"`X₂` moves from clique to UPCC"*, §9.7
Case 3a2 — spends the remaining unit.  See the module docstring. -/
noncomputable def hintBit (X : Pt (BipBlockInputs Ω)) : ℕ := by
  classical
  letI : Fintype ↥X.car := Fintype.ofFinite _
  letI : DecidableEq ↥X.car := Classical.decEq _
  exact if X.obj.1.1.HasHint then 0 else 1

theorem hintBit_le_one (X : Pt (BipBlockInputs Ω)) : hintBit X ≤ 1 := by
  classical
  rw [hintBit]
  split <;> omega

/-- §9.5.  The hint bit is an isomorphism invariant (`Babai.VColBipBlk.hasHint_congr`). -/
theorem hintBit_congr {X Y : Pt (BipBlockInputs Ω)}
    (h : ((BipBlockInputs Ω).IsoP X Y).Nonempty) : hintBit X = hintBit Y := by
  classical
  letI : Fintype ↥X.car := Fintype.ofFinite _
  letI : DecidableEq ↥X.car := Classical.decEq _
  letI : Fintype ↥Y.car := Fintype.ofFinite _
  letI : DecidableEq ↥Y.car := Classical.decEq _
  obtain ⟨φ, hφ⟩ := h
  have hiso : X.obj.1.1.IsIsoTo Y.obj.1.1 φ := hφ.2
  have hXY : X.obj.1.1.HasHint ↔ Y.obj.1.1.HasHint :=
    ⟨VColBipBlk.hasHint_congr hiso, VColBipBlk.hasHint_congr (VColBipBlk.IsIsoTo.symm hiso)⟩
  rw [hintBit, hintBit]
  by_cases hX : X.obj.1.1.HasHint
  · rw [if_pos hX, if_pos (hXY.1 hX)]
  · rw [if_neg hX, if_neg (fun hc => hX (hXY.2 hc))]

noncomputable def measure_9_5 (X : Pt (BipBlockInputs Ω)) : ℕ :=
  2 * BipBlockInputs.numBlocks X + hintBit X

/-- §9.5.  The measure is an isomorphism invariant.  This is not automatic: a `Babai.Pt`
carries its underlying set, and two isomorphic objects live on different subsets of `Ω`. -/
theorem measure_9_5_congr {X Y : Pt (BipBlockInputs Ω)}
    (h : ((BipBlockInputs Ω).IsoP X Y).Nonempty) : measure_9_5 X = measure_9_5 Y := by
  rw [measure_9_5, measure_9_5, BipBlockInputs.numBlocks_congr h, hintBit_congr h]

theorem measure_9_5_lt (X : Pt (BipBlockInputs Ω)) :
    measure_9_5 X < 2 * Fintype.card Ω + 2 := by
  have h1 : BipBlockInputs.numBlocks X ≤ X.car.ncard := BipBlockInputs.numBlocks_le_ncard X
  have h2 : X.car.ncard ≤ Fintype.card Ω := by
    have := Set.ncard_le_ncard (Set.subset_univ X.car) Set.finite_univ
    rwa [Set.ncard_univ, Nat.card_eq_fintype_card] at this
  have h3 := hintBit_le_one X
  rw [measure_9_5]
  omega

/-! ### The cost of the recursion -/

/-- §9.4.  The constant factor of the cost: it absorbs steps 1 and 2 of Procedure
Bipartite Split-or-Johnson, whose multiplicative costs — `n₁^{(1-α)n₁} ≤ C₀^{C₀}` for step
1, and the individualization of the `n₂` vertices of `V₂` for step 2 — are bounded in terms
of the absolute constant `C₀` alone on the instances on which those steps fire.

The value of the constant is ours, not the paper's; it only has to be large enough for the
two cost bounds `Babai.pow_self_le_constFactor` and `Babai.pow_self_le_cost_of_log_le`,
which is what fixes it here. -/
def constFactor (C₀ : ℕ) : ℕ := 2 ^ (4 ^ ((C₀ + 2) ^ 2))

theorem one_le_constFactor (C₀ : ℕ) : 1 ≤ constFactor C₀ := Nat.one_le_two_pow

/-- `m ≤ 2^m`, in the form needed below. -/
private theorem self_le_two_pow (m : ℕ) : m ≤ 2 ^ m := (Nat.lt_two_pow_self).le

/-- §9.4, step 1.  The individualization of at most `C₀` vertices costs at most
`Babai.constFactor C₀`. -/
theorem pow_self_le_constFactor {m C₀ : ℕ} (h : m ≤ C₀) : m ^ m ≤ constFactor C₀ := by
  have h1 : m ^ m ≤ (2 ^ m) ^ m := Nat.pow_le_pow_left (self_le_two_pow m) m
  have h3 : m * m ≤ C₀ * C₀ := Nat.mul_le_mul h h
  have h4 : C₀ * C₀ ≤ 4 ^ ((C₀ + 2) ^ 2) := by
    have h5 : C₀ * C₀ ≤ (C₀ + 2) ^ 2 := by nlinarith
    have h6 : (C₀ + 2) ^ 2 ≤ 2 ^ ((C₀ + 2) ^ 2) := self_le_two_pow _
    have h7 : (2 : ℕ) ^ ((C₀ + 2) ^ 2) ≤ 4 ^ ((C₀ + 2) ^ 2) :=
      Nat.pow_le_pow_left (by norm_num) _
    omega
  calc m ^ m ≤ (2 ^ m) ^ m := h1
    _ = 2 ^ (m * m) := by rw [← pow_mul]
    _ ≤ 2 ^ (4 ^ ((C₀ + 2) ^ 2)) := Nat.pow_le_pow_right (by norm_num) (le_trans h3 h4)

/-- §9.5.  A significant reduction of a parameter is at most a halving, so the number of
significant reductions of `m` is at least `log₂ m`.  This is what makes the single turn
that step 2 of §9.4 spends pay for the individualization of the `n₂` vertices of `V₂`. -/
theorem log_le_steps09 (m : ℕ) : Nat.log 2 m ≤ steps09 m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    rw [steps09_succ]
    have hhalf : (k + 1) / 2 ≤ reduce09 (k + 1) := by
      refine Nat.le_div_iff_mul_le (by norm_num) |>.2 ?_
      have h1 : (k + 1) / 2 * 2 ≤ k + 1 := Nat.div_mul_le_self (k + 1) 2
      omega
    have hlog : Nat.log 2 (k + 1) ≤ Nat.log 2 ((k + 1) / 2) + 1 := by
      have := Nat.log_div_base 2 (k + 1)
      omega
    have hmono : Nat.log 2 ((k + 1) / 2) ≤ Nat.log 2 (reduce09 (k + 1)) :=
      Nat.log_mono_right hhalf
    have hih : Nat.log 2 (reduce09 (k + 1)) ≤ steps09 (reduce09 (k + 1)) :=
      ih _ (reduce09_lt (Nat.succ_pos k))
    omega

/-- §9.4, step 2.  The individualization of the `n₂` vertices of `V₂` costs at most `n₂^n₂`,
and on the instances of step 2 (`n₂ ≤ C₀ log₂ n₁`) this is below
`Babai.constFactor C₀` times the cost of one turn of the recursion.

Two cases.  If the number `steps09 m + 1` of turns that the recursion still has is at least
`C₀^2`, then those turns alone pay: `m^m ≤ 2^{m^2} ≤ 2^{C₀^2 (log₂ n)^2}`.  Otherwise
`log₂ m ≤ steps09 m < C₀^2`, so `m < 2^{C₀^2}` is bounded in terms of `C₀` alone, and the
constant factor pays. -/
theorem pow_self_le_cost_of_log_le {C₀ n n₁ m b : ℕ} (hn₁ : n₁ ≤ n)
    (hm : m ≤ C₀ * Nat.log 2 n₁) : m ^ m ≤ constFactor C₀ * costFun n m b := by
  set L := Nat.log 2 n with hL
  have hmL : m ≤ C₀ * L := le_trans hm (Nat.mul_le_mul_left _ (Nat.log_mono_right hn₁))
  have hmm : m ^ m ≤ 2 ^ (m * m) := by
    calc m ^ m ≤ (2 ^ m) ^ m := Nat.pow_le_pow_left (self_le_two_pow m) m
      _ = 2 ^ (m * m) := by rw [← pow_mul]
  rcases Nat.lt_or_ge (steps09 m + 1) (C₀ ^ 2) with hsmall | hbig
  · -- the constant factor pays
    rcases Nat.eq_zero_or_pos m with rfl | hmpos
    · have hpos : 0 < constFactor C₀ * costFun n 0 b :=
        Nat.mul_pos (one_le_constFactor C₀) (Nat.one_le_pow _ _ (one_le_turnCost n))
      simpa only [pow_zero] using hpos
    have hlogm : Nat.log 2 m < C₀ ^ 2 := by
      have := log_le_steps09 m
      omega
    have hmlt : m < 2 ^ (C₀ ^ 2) :=
      (Nat.log_lt_iff_lt_pow (by norm_num) (by omega)).1 hlogm
    have hmm2 : m * m ≤ 4 ^ ((C₀ + 2) ^ 2) := by
      calc m * m ≤ 2 ^ (C₀ ^ 2) * 2 ^ (C₀ ^ 2) := Nat.mul_le_mul (by omega) (by omega)
        _ = 4 ^ (C₀ ^ 2) := by
            rw [← pow_add, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
            ring_nf
        _ ≤ 4 ^ ((C₀ + 2) ^ 2) :=
            Nat.pow_le_pow_right (by norm_num) (Nat.pow_le_pow_left (by omega) 2)
    calc m ^ m ≤ 2 ^ (m * m) := hmm
      _ ≤ 2 ^ (4 ^ ((C₀ + 2) ^ 2)) := Nat.pow_le_pow_right (by norm_num) hmm2
      _ = constFactor C₀ := rfl
      _ ≤ constFactor C₀ * costFun n m b :=
          Nat.le_mul_of_pos_right _ (Nat.one_le_pow _ _ (one_le_turnCost n))
  · -- the remaining turns of the recursion pay
    have hcost : costFun n m b = 2 ^ (turnConst * (L + 2) ^ 2 * (2 * steps09 m + 1 + b)) := by
      rw [costFun, turnCost, ← pow_mul, hL]
    have hexp : m * m ≤ turnConst * (L + 2) ^ 2 * (2 * steps09 m + 1 + b) := by
      have hbase : m * m ≤ (L + 2) ^ 2 * (steps09 m + 1) := by
        calc m * m ≤ (C₀ * L) * (C₀ * L) := Nat.mul_le_mul hmL hmL
          _ = C₀ ^ 2 * L ^ 2 := by ring
          _ ≤ (steps09 m + 1) * (L + 2) ^ 2 :=
              Nat.mul_le_mul hbig (Nat.pow_le_pow_left (by omega) 2)
          _ = (L + 2) ^ 2 * (steps09 m + 1) := by ring
      have h2 : (L + 2) ^ 2 * (steps09 m + 1)
          ≤ turnConst * (L + 2) ^ 2 * (steps09 m + 1) :=
        Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_left _ (by norm_num [turnConst]))
      have h3 : turnConst * (L + 2) ^ 2 * (steps09 m + 1)
          ≤ turnConst * (L + 2) ^ 2 * (2 * steps09 m + 1 + b) :=
        Nat.mul_le_mul_left _ (by omega)
      omega
    calc m ^ m ≤ 2 ^ (m * m) := hmm
      _ ≤ 2 ^ (turnConst * (L + 2) ^ 2 * (2 * steps09 m + 1 + b)) :=
          Nat.pow_le_pow_right (by norm_num) hexp
      _ = costFun n m b := hcost.symm
      _ ≤ constFactor C₀ * costFun n m b :=
          Nat.le_mul_of_pos_left _ (one_le_constFactor C₀)

/-- §9.4, §9.5.  The multiplicative cost of the recursion of §9.4-§9.8 started at `X`: the
constant factor of steps 1 and 2, times one `Babai.turnCost` per turn, and there are at
most `2 (steps09 n₂) + 1 + (the hint bit)` turns (§9.5): two per significant reduction of
`n₂`, plus the last one. -/
noncomputable def cost_9_4 (C₀ : ℕ) (X : Pt (BipBlockInputs Ω)) : ℕ :=
  constFactor C₀ * costFun X.car.ncard (BipBlockInputs.numBlocks X) (hintBit X)

/-- The quasipolynomial that bounds `Babai.cost_9_4`. -/
def costBound_9_4 (C₀ : ℕ) (n : ℕ) : ℕ := constFactor C₀ * costBound n

theorem cost_9_4_le (C₀ : ℕ) (X : Pt (BipBlockInputs Ω)) :
    cost_9_4 C₀ X ≤ costBound_9_4 C₀ X.car.ncard :=
  Nat.mul_le_mul_left _
    (costFun_le_costBound (BipBlockInputs.numBlocks_le_ncard X) (hintBit_le_one X))

theorem quasiPolyBound_costBound_9_4 (C₀ : ℕ) : RAM.QuasiPolyBound (costBound_9_4 C₀) :=
  RAM.QuasiPolyBound.mul (RAM.PolyBound.quasiPoly ⟨constFactor C₀, 0, fun _ => by simp⟩)
    quasiPolyBound_costBound

/-! ### The subcategories of the steps of §9.4 -/

/-- §9.4, step 1.  *"If `n₁ ≤ C₀` for some absolute constant `C₀`"*. -/
noncomputable def IsSmallPart₁ (C₀ : ℕ) (X : Pt (BipBlockInputs Ω)) : Prop :=
  BipBlockInputs.n₁ X ≤ C₀

/-- §9.4, step 2.  *"If `n₂ ≤ c log n₁` for some specific constant `c > 0`"*.  The
constant is the same `C₀` as in step 1; taking one constant for both steps loses nothing,
since both statements only become weaker as the constant grows. -/
noncomputable def IsSmallPart₂ (C₀ : ℕ) (X : Pt (BipBlockInputs Ω)) : Prop :=
  BipBlockInputs.numBlocks X ≤ C₀ * Nat.log 2 (BipBlockInputs.n₁ X)

/-- The category of the inputs of measure exactly `N`: the objects on which one turn of
Procedure Bipartite Split-or-Johnson is run, given the recursion on the smaller ones. -/
noncomputable def BipBlockInputsAt (Ω : Type) [Fintype Ω] [DecidableEq Ω] (N : ℕ) :
    Cat.{0, 0} Ω :=
  (BipBlockInputs Ω).full fun s Y => measure_9_5 ⟨s, Y⟩ = N

/-- What Theorem 9.2.2 is asked to find, read on an input of the wider category. -/
def Good_9_2_2 (X : Pt (BipBlockInputs Ω)) (Z : Pt (SplitOutcomes Ω)) : Prop :=
  IsSplitOutcome (BipBlockInputs.alpha X) (BipBlockInputs.V₁ X) Z

/-! ### The steps of Procedure Bipartite Split-or-Johnson -/

/-! ### §9.4, step 1: individualizing `(1-α)n₁` vertices of `V₁`

*"If `n₁ ≤ C₀` for some absolute constant `C₀`, individualize `(1-α)n₁` vertices of `V₁`,
exit (objective (a) achieved)."*  (Version 2.5, lines 4118-4119.)

Individualizing a set of vertices of `V₁` is the choice of a numbering of `V₁` by
`0, …, n₁-1` (`Babai.IsPart₁Numbering`); the individualized vertices are the ones numbered
below a threshold `k`, and the returned colored partition of `V₁` has one block for each of
them and one block for all the others (`Babai.indivColor`).  With
`k = n₁ - ⌊α n₁⌋`, so that `n₁ - k = ⌊α n₁⌋ ≤ α n₁` vertices are left over, the blocks have
at most `α n₁` points each, which is objective (a). -/

section Step1

variable {s t : Set Ω}

/-- §9.4, step 1.  A numbering of the points of `V₁` by `0, …, n₁ - 1`.  Points outside
`V₁` get the number `0`, which no construction reads. -/
def IsPart₁Numbering (G : VColBipBlk ↥s ℕ) (σ : ↥s → ℕ) : Prop :=
  (∀ x, ¬ G.part₁ x → σ x = 0) ∧ Set.InjOn σ G.V₁ ∧ ∀ x ∈ G.V₁, σ x < G.V₁.ncard

/-- §9.4, step 1.  The coloring of the vertices after the individualization: a point of
`V₁` numbered below `k` gets its own color, and every other point gets the color `0`. -/
def indivColor (σ : ↥s → ℕ) (k : ℕ) (x : ↥s) : ℕ := if σ x < k then σ x + 1 else 0

/-- There is a numbering of `V₁`. -/
theorem exists_isPart₁Numbering (G : VColBipBlk ↥s ℕ) : ∃ σ, IsPart₁Numbering G σ := by
  classical
  letI : Fintype ↥G.V₁ := Fintype.ofFinite _
  have hcard : Fintype.card ↥G.V₁ = G.V₁.ncard := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
  set e := Fintype.equivFin ↥G.V₁ with he
  refine ⟨fun x => if h : x ∈ G.V₁ then ((e ⟨x, h⟩ : Fin _) : ℕ) else 0,
    fun x hx => dif_neg hx, ?_, ?_⟩
  · intro x hx y hy hxy
    simp only [dif_pos hx, dif_pos hy] at hxy
    exact congrArg Subtype.val (e.injective (Fin.ext hxy))
  · intro x hx
    simp only [dif_pos hx]
    rw [← hcard]
    exact (e ⟨x, hx⟩).2

/-- The numberings of `V₁` are finitely many: at most `n₁^{n₁}`, which is the
multiplicative cost of the individualization of step 1. -/
theorem card_isPart₁Numbering_le (G : VColBipBlk ↥s ℕ) :
    Nat.card {σ : ↥s → ℕ // IsPart₁Numbering G σ} ≤ G.V₁.ncard ^ G.V₁.ncard := by
  classical
  letI : Fintype ↥G.V₁ := Fintype.ofFinite _
  have hcard : Fintype.card ↥G.V₁ = G.V₁.ncard := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
  have hinj : Function.Injective
      (fun σ : {σ : ↥s → ℕ // IsPart₁Numbering G σ} =>
        (fun x : ↥G.V₁ => (⟨σ.1 x.1, σ.2.2.2 x.1 x.2⟩ : Fin G.V₁.ncard))) := by
    intro a b hab
    refine Subtype.ext (funext fun x => ?_)
    by_cases hx : x ∈ G.V₁
    · exact congrArg Fin.val (congrFun hab ⟨x, hx⟩)
    · rw [a.2.1 x hx, b.2.1 x hx]
  refine le_trans (Nat.card_le_card_of_injective _ hinj) ?_
  rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin, hcard]

instance instFiniteIsPart₁Numbering (G : VColBipBlk ↥s ℕ) :
    Finite {σ : ↥s → ℕ // IsPart₁Numbering G σ} := by
  classical
  letI : Fintype ↥G.V₁ := Fintype.ofFinite _
  refine Finite.of_injective
    (fun σ : {σ : ↥s → ℕ // IsPart₁Numbering G σ} =>
      (fun x : ↥G.V₁ => (⟨σ.1 x.1, σ.2.2.2 x.1 x.2⟩ : Fin G.V₁.ncard))) ?_
  intro a b hab
  refine Subtype.ext (funext fun x => ?_)
  by_cases hx : x ∈ G.V₁
  · exact congrArg Fin.val (congrFun hab ⟨x, hx⟩)
  · rw [a.2.1 x hx, b.2.1 x hx]

/-- §9.4, step 1.  Every block of the returned partition — a singleton for an
individualized point of `V₁`, and the set of the remaining points — has at most `b` points,
where `b = n₁ - k` is the number of points that were not individualized. -/
theorem indivColor_class_le (G : VColBipBlk ↥s ℕ) {σ : ↥s → ℕ}
    (hσ : IsPart₁Numbering G σ) {b : ℕ} (hb1 : 1 ≤ b) (hbn : b ≤ G.V₁.ncard)
    {x : ↥s} (hx : x ∈ G.V₁) :
    {y : ↥s | y ∈ G.V₁ ∧ indivColor σ (G.V₁.ncard - b) y
        = indivColor σ (G.V₁.ncard - b) x}.ncard ≤ b := by
  classical
  set n := G.V₁.ncard with hn
  set k := n - b with hk
  by_cases hxk : σ x < k
  · have hsub : {y : ↥s | y ∈ G.V₁ ∧ indivColor σ k y = indivColor σ k x} ⊆ {x} := by
      rintro y ⟨hy, hcol⟩
      rw [indivColor, indivColor, if_pos hxk] at hcol
      by_cases hyk : σ y < k
      · rw [if_pos hyk] at hcol
        exact hσ.2.1 hy hx (by omega)
      · rw [if_neg hyk] at hcol; omega
    calc {y : ↥s | y ∈ G.V₁ ∧ indivColor σ k y = indivColor σ k x}.ncard
        ≤ ({x} : Set ↥s).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
      _ = 1 := Set.ncard_singleton x
      _ ≤ b := hb1
  · have hmaps : ∀ y ∈ {y : ↥s | y ∈ G.V₁ ∧ indivColor σ k y = indivColor σ k x},
        σ y ∈ (↑(Finset.Ico k n) : Set ℕ) := by
      rintro y ⟨hy, hcol⟩
      rw [indivColor, indivColor, if_neg hxk] at hcol
      have hyk : ¬ σ y < k := by
        intro hc
        rw [if_pos hc] at hcol
        omega
      simp only [Finset.coe_Ico, Set.mem_Ico]
      exact ⟨by omega, hσ.2.2 y hy⟩
    have hinj : Set.InjOn σ
        {y : ↥s | y ∈ G.V₁ ∧ indivColor σ k y = indivColor σ k x} :=
      fun a ha c hc hac => hσ.2.1 ha.1 hc.1 hac
    calc {y : ↥s | y ∈ G.V₁ ∧ indivColor σ k y = indivColor σ k x}.ncard
        ≤ ((↑(Finset.Ico k n) : Set ℕ)).ncard :=
          Set.ncard_le_ncard_of_injOn σ hmaps hinj (Set.toFinite _)
      _ = b := by rw [Set.ncard_coe_finset, Nat.card_Ico]; omega

/-- §9.4, step 1.  The outcome: the colored partition of `V₁` into the individualized
singletons and the rest, for the threshold `k = n₁ - ⌊α n₁⌋`. -/
noncomputable def step1Outcome (α : ℝ) (G : VColBipBlk ↥s ℕ) (σ : ↥s → ℕ) :
    (Cat.sub (SplitOutcomes Ω)).Obj s :=
  kerOutcome G.V₁ (indivColor σ (G.V₁.ncard - ⌊α * (G.V₁.ncard : ℝ)⌋₊))

/-- §9.4, step 1.  *"Claim: objective (a) is achieved."*  The partition returned is a
colored `α`-partition of `V₁`: its blocks are the `n₁ - ⌊α n₁⌋` individualized singletons
(the points with `σ < n₁ - ⌊α n₁⌋`, i.e. `⌈(1-α) n₁⌉` of them, the paper's `(1-α)n₁`) and
the set of the `⌊α n₁⌋ ≤ α n₁` remaining points. -/
theorem step1Outcome_isAlphaPartition {α : ℝ} (hα : 2 / 3 ≤ α) (hα1 : α < 1)
    (G : VColBipBlk ↥s ℕ) (h2 : 2 ≤ G.V₁.ncard) {σ : ↥s → ℕ}
    (hσ : IsPart₁Numbering G σ) (iF : Fintype ↥(Subtype.val '' G.V₁)) :
    @ColoredPartition.IsAlphaPartition _ _
      (kerPartition G.V₁ (indivColor σ (G.V₁.ncard - ⌊α * (G.V₁.ncard : ℝ)⌋₊))) iF α := by
  set n := G.V₁.ncard with hn
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h2
  have hprod : (1 : ℝ) ≤ α * (n : ℝ) := by nlinarith
  have hb1 : 1 ≤ ⌊α * (n : ℝ)⌋₊ := Nat.le_floor (by exact_mod_cast hprod)
  have hble : ⌊α * (n : ℝ)⌋₊ ≤ n := by
    have hle : α * (n : ℝ) ≤ (n : ℝ) := by nlinarith
    calc ⌊α * (n : ℝ)⌋₊ ≤ ⌊(n : ℝ)⌋₊ := Nat.floor_le_floor hle
      _ = n := Nat.floor_natCast n
  have hfl : (⌊α * (n : ℝ)⌋₊ : ℝ) ≤ α * (n : ℝ) := Nat.floor_le (by nlinarith)
  exact kerPartition_isAlphaPartition G.V₁ _ iF
    (fun x hx => indivColor_class_le G hσ hb1 hble hx) hfl

/-- §6.  Condition (ii) of Definition 6.0.1 for the outcomes of step 1. -/
theorem step1Outcome_mem_subIso {α : ℝ} {G : VColBipBlk ↥s ℕ} {H : VColBipBlk ↥t ℕ}
    {φ : ↥s ≃ ↥t} (h : G.IsIsoTo H φ) (σ : ↥s → ℕ) :
    φ ∈ (Cat.sub (SplitOutcomes Ω)).Iso (step1Outcome α G σ)
      (step1Outcome α H (fun y => σ (φ.symm y))) := by
  have hncard : G.V₁.ncard = H.V₁.ncard := VColBipBlk.V₁_ncard_eq_of_isIsoTo h
  refine kerOutcome_mem_subIso φ (fun x => h.part₁ x) (fun x => ?_)
  show indivColor (fun y => σ (φ.symm y)) (H.V₁.ncard - ⌊α * (H.V₁.ncard : ℝ)⌋₊) (φ x)
    = indivColor σ (G.V₁.ncard - ⌊α * (G.V₁.ncard : ℝ)⌋₊) x
  rw [← hncard, indivColor, indivColor, Equiv.symm_apply_apply]

/-- A numbering of `V₁` is carried to a numbering of `V₁` by an isomorphism. -/
theorem isPart₁Numbering_map {G : VColBipBlk ↥s ℕ} {H : VColBipBlk ↥t ℕ} {φ : ↥s ≃ ↥t}
    (h : G.IsIsoTo H φ) {σ : ↥s → ℕ} (hσ : IsPart₁Numbering G σ) :
    IsPart₁Numbering H (fun y => σ (φ.symm y)) := by
  have hncard : G.V₁.ncard = H.V₁.ncard := VColBipBlk.V₁_ncard_eq_of_isIsoTo h
  have hmem : ∀ y : ↥t, φ.symm y ∈ G.V₁ ↔ y ∈ H.V₁ := by
    intro y
    show G.part₁ (φ.symm y) ↔ H.part₁ y
    rw [← h.part₁ (φ.symm y), Equiv.apply_symm_apply]
  refine ⟨fun y hy => hσ.1 _ (fun hc => hy ((hmem y).1 hc)), ?_, ?_⟩
  · intro y hy z hz hyz
    have := hσ.2.1 ((hmem y).2 hy) ((hmem z).2 hz) hyz
    exact φ.symm.injective this
  · intro y hy
    rw [← hncard]
    exact hσ.2.2 _ ((hmem y).2 hy)

end Step1

/-- §9.4, step 1.  *"If `n₁ ≤ C₀` for some absolute constant `C₀`, individualize
`(1-α)n₁` vertices of `V₁`, exit (objective (a) achieved)."*  (Version 2.5, lines
4118-4119.)

The multiplicative cost is the choice of the individualization, that is of a numbering of
`V₁`: at most `n₁^{n₁} ≤ C₀^{C₀}`, a constant, which is why `Babai.cost_9_4` carries
`Babai.constFactor` (`Babai.pow_self_le_constFactor`).  The colored partition returned has
one block for each of the `n₁ - ⌊α n₁⌋ = ⌈(1-α) n₁⌉` individualized points and one block for
the `⌊α n₁⌋ ≤ α n₁` points that were not individualized, so every block has at most
`α n₁` points: this is objective (a) (`Babai.step1Outcome_isAlphaPartition`).  The symmetry
defect hypothesis is not needed for this step. -/
theorem step_9_4_1 (C₀ N : ℕ) :
    FindsAtMultCost
      ((BipBlockInputsAt Ω N).full fun s Y => IsSmallPart₁ C₀ ⟨s, Y.1⟩)
      (SplitOutcomes Ω)
      (fun X => cost_9_4 C₀ ⟨X.car, X.obj.1.1⟩)
      (fun X Z => Good_9_2_2 ⟨X.car, X.obj.1.1⟩ Z) := by
  classical
  refine FindsAtMultCost.of_outcomes_sub
    (fun X => Set.range fun σ : {σ : ↥X.car → ℕ // IsPart₁Numbering X.obj.1.1.1.1 σ} =>
      step1Outcome X.obj.1.1.1.2 X.obj.1.1.1.1 σ.1)
    (fun X => ?_) (fun X => Set.finite_range _) (fun X => ?_)
    (fun {X Y f} hf Z hZ => ?_) (fun X Z hZ => ?_)
  · obtain ⟨σ, hσ⟩ := exists_isPart₁Numbering X.obj.1.1.1.1
    exact ⟨_, ⟨⟨σ, hσ⟩, rfl⟩⟩
  · -- at most `n₁^{n₁} ≤ C₀^{C₀}` outcomes, which the constant factor of the cost absorbs
    have hsmall : X.obj.1.1.1.1.V₁.ncard ≤ C₀ := X.obj.2
    have hrange : (Set.range fun σ : {σ : ↥X.car → ℕ // IsPart₁Numbering X.obj.1.1.1.1 σ} =>
        step1Outcome X.obj.1.1.1.2 X.obj.1.1.1.1 σ.1).ncard
        ≤ Nat.card {σ : ↥X.car → ℕ // IsPart₁Numbering X.obj.1.1.1.1 σ} := by
      rw [← Set.image_univ]
      have h1 := Set.ncard_image_le (s := (Set.univ :
          Set {σ : ↥X.car → ℕ // IsPart₁Numbering X.obj.1.1.1.1 σ}))
        (f := fun σ => step1Outcome X.obj.1.1.1.2 X.obj.1.1.1.1 σ.1) Set.finite_univ
      rwa [Set.ncard_univ] at h1
    refine le_trans hrange (le_trans (card_isPart₁Numbering_le _) ?_)
    refine le_trans (pow_self_le_constFactor hsmall) ?_
    exact Nat.le_mul_of_pos_right _ (Nat.one_le_pow _ _ (one_le_turnCost _))
  · obtain ⟨σ, rfl⟩ := hZ
    have hiso : X.obj.1.1.1.2 = Y.obj.1.1.1.2 ∧
        f ∈ (VColBlkGraphs Ω ℕ).Iso X.obj.1.1.1.1 Y.obj.1.1.1.1 := hf
    have hg : X.obj.1.1.1.1.IsIsoTo Y.obj.1.1.1.1 f := hiso.2
    refine ⟨step1Outcome Y.obj.1.1.1.2 Y.obj.1.1.1.1 (fun y => σ.1 (f.symm y)),
      ⟨⟨fun y => σ.1 (f.symm y), isPart₁Numbering_map hg σ.2⟩, rfl⟩, ?_⟩
    rw [← hiso.1]
    exact step1Outcome_mem_subIso hg σ.1
  · obtain ⟨σ, rfl⟩ := hZ
    obtain ⟨hα, hα1, hinput⟩ := X.obj.1.1.2
    exact ⟨rfl, step1Outcome_isAlphaPartition hα hα1 _ hinput.1 σ.2 _⟩

/-! ### §9.4, step 2: individualizing all vertices of `V₂`

*"If `n₂ ≤ c log n₁` for some specific constant `c > 0` then individualize all vertices of
`V₂`, apply naive vertex refinement, return colored partition of `V₁`, exit.  Claim.  This
is a colored `α`-partition.  Proof.  All vertices of the same color in `V₁` are twins."*
(Version 2.5, lines 4120-4125.)

Individualizing all vertices of `V₂` is the choice of a numbering of the blocks by
`0, …, n₂-1` (`Babai.IsBlockNumbering`).  Naive vertex refinement then gives each vertex of
`V₁` the color `Babai.blkColor`: its own vertex color together with the set of numbers of
the blocks it is joined to.  Two vertices of `V₁` with the same color have the same vertex
color and the same neighboring blocks, so they are twins
(`Babai.VColBipBlk.isTwin_iff`), which is the paper's Claim.  A color class is therefore a
set of twins, so it has at most `symmetricity₁ ≤ α n₁` points, and the partition into the
color classes is a colored `α`-partition. -/

section Step2

variable {s t : Set Ω}

/-- §9.4, step 2.  A numbering of the vertices of `V₂` — that is, of the blocks — by
`0, …, n₂ - 1`.  Subsets that are not blocks get the number `0`, which no construction
reads. -/
def IsBlockNumbering (G : VColBipBlk ↥s ℕ) (σ : Set ↥s → ℕ) : Prop :=
  (∀ B ∉ G.blocks, σ B = 0) ∧ Set.InjOn σ G.blocks ∧ ∀ B ∈ G.blocks, σ B < G.numBlocks

open scoped Classical in
/-- §9.4, step 2.  The color a vertex receives from naive vertex refinement once all
vertices of `V₂` have been individualized: its own vertex color `f`, paired with the set of
numbers of the blocks it is joined to, written in binary. -/
noncomputable def blkColor (G : VColBipBlk ↥s ℕ) (σ : Set ↥s → ℕ) (x : ↥s) : ℕ :=
  Nat.pair (G.f x)
    (∑ i ∈ (Finset.range G.numBlocks).filter
      (fun i => ∃ B ∈ G.blocks, σ B = i ∧ (x, B) ∈ G.E), 2 ^ i)

open scoped Classical in
/-- The number of a block is one of the numbers recorded by `Babai.blkColor` exactly when
the vertex is joined to that block. -/
theorem mem_blkColor_filter (G : VColBipBlk ↥s ℕ) {σ : Set ↥s → ℕ}
    (hσ : IsBlockNumbering G σ) (x : ↥s) {B : Set ↥s} (hB : B ∈ G.blocks) :
    σ B ∈ (Finset.range G.numBlocks).filter
        (fun i => ∃ B' ∈ G.blocks, σ B' = i ∧ (x, B') ∈ G.E) ↔ (x, B) ∈ G.E := by
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨-, B', hB', hσB', hE⟩
    rwa [hσ.2.1 hB' hB hσB'] at hE
  · intro hE
    exact ⟨hσ.2.2 B hB, B, hB, rfl, hE⟩

/-- §9.4, step 2.  *"Claim.  All vertices of the same color in `V₁` are twins."*  Two
vertices with the same `Babai.blkColor` have the same vertex color and the same set of
neighboring blocks, which by `Babai.VColBipBlk.isTwin_iff` is exactly twinness. -/
theorem blkColor_eq_imp (G : VColBipBlk ↥s ℕ) {σ : Set ↥s → ℕ}
    (hσ : IsBlockNumbering G σ) {x x' : ↥s} (h : blkColor G σ x = blkColor G σ x') :
    G.f x = G.f x' ∧ ∀ B ∈ G.blocks, ((x, B) ∈ G.E ↔ (x', B) ∈ G.E) := by
  classical
  rw [blkColor, blkColor] at h
  obtain ⟨hf, hcode⟩ := Nat.pair_eq_pair.1 h
  refine ⟨hf, fun B hB => ?_⟩
  have hfil := Finset.geomSum_injective (n := 2) (le_refl 2) hcode
  rw [← mem_blkColor_filter G hσ x hB, ← mem_blkColor_filter G hσ x' hB, hfil]

open scoped Classical in
/-- A set of twins inside `V₁` is no larger than the absolute symmetricity of `V₁`
(Def. 2.4.29). -/
theorem ncard_le_symmetricity₁ (G : VColBipBlk ↥s ℕ) [Fintype ↥s] [DecidableEq ↥s]
    {S : Set ↥s} (hS : ∀ x ∈ S, G.part₁ x) (hT : IsTwinSet G.Aut S) :
    S.ncard ≤ G.symmetricity₁ := by
  have hfin : S.ncard = S.toFinset.card := Set.ncard_eq_toFinset_card' S
  rw [hfin]
  refine Finset.le_sup (f := Finset.card) ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_toFinset]
  exact ⟨fun y hy => hS y hy, by rwa [Set.coe_toFinset]⟩

/-- Definition 2.4.29.  A symmetry defect of `V₁` of at least `1 - α` means that a set of
twins inside `V₁` has at most `α n₁` points. -/
theorem symmetricity₁_le_alpha (G : VColBipBlk ↥s ℕ) [Fintype ↥s] [DecidableEq ↥s]
    {α : ℝ} (hn : 0 < G.V₁.ncard) (h : 1 - α ≤ ((G.defect₁ : ℚ) : ℝ)) :
    (G.symmetricity₁ : ℝ) ≤ α * (G.V₁.ncard : ℝ) := by
  have hd : (G.defect₁ : ℚ) = 1 - (G.symmetricity₁ : ℚ) / (G.V₁.ncard : ℚ) := rfl
  rw [hd] at h
  push_cast at h
  have hnR : (0 : ℝ) < (G.V₁.ncard : ℝ) := by exact_mod_cast hn
  have hdiv : (G.symmetricity₁ : ℝ) / (G.V₁.ncard : ℝ) ≤ α := by linarith
  rw [div_le_iff₀ hnR] at hdiv
  linarith

/-- §9.4, step 2.  A color class of `Babai.blkColor` inside `V₁` is a set of twins, so it
has at most `symmetricity₁` points. -/
theorem blkColor_class_le (G : VColBipBlk ↥s ℕ) [Fintype ↥s] [DecidableEq ↥s]
    {σ : Set ↥s → ℕ} (hσ : IsBlockNumbering G σ) {x : ↥s} (hx : x ∈ G.V₁) :
    {y : ↥s | y ∈ G.V₁ ∧ blkColor G σ y = blkColor G σ x}.ncard ≤ G.symmetricity₁ := by
  refine ncard_le_symmetricity₁ G (fun y hy => hy.1) ?_
  intro a ha b hb hab
  exact (G.isTwin_iff ha.1 hb.1 hab).2 (blkColor_eq_imp G hσ (ha.2.trans hb.2.symm))

/-- There is a numbering of the blocks. -/
theorem exists_isBlockNumbering (G : VColBipBlk ↥s ℕ) [Finite ↥s] :
    ∃ σ, IsBlockNumbering G σ := by
  classical
  letI : Fintype ↥G.blocks := Fintype.ofFinite _
  have hcard : Fintype.card ↥G.blocks = G.numBlocks := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]; rfl
  set e := Fintype.equivFin ↥G.blocks with he
  refine ⟨fun B => if h : B ∈ G.blocks then ((e ⟨B, h⟩ : Fin _) : ℕ) else 0,
    fun B hB => dif_neg hB, ?_, ?_⟩
  · intro B hB B' hB' hBB'
    simp only [dif_pos hB, dif_pos hB'] at hBB'
    exact congrArg Subtype.val (e.injective (Fin.ext hBB'))
  · intro B hB
    simp only [dif_pos hB]
    rw [← hcard]
    exact (e ⟨B, hB⟩).2

instance instFiniteIsBlockNumbering (G : VColBipBlk ↥s ℕ) [Finite ↥s] :
    Finite {σ : Set ↥s → ℕ // IsBlockNumbering G σ} := by
  classical
  letI : Fintype ↥G.blocks := Fintype.ofFinite _
  refine Finite.of_injective
    (fun σ : {σ : Set ↥s → ℕ // IsBlockNumbering G σ} =>
      (fun B : ↥G.blocks => (⟨σ.1 B.1, σ.2.2.2 B.1 B.2⟩ : Fin G.numBlocks))) ?_
  intro a b hab
  refine Subtype.ext (funext fun B => ?_)
  by_cases hB : B ∈ G.blocks
  · exact congrArg Fin.val (congrFun hab ⟨B, hB⟩)
  · rw [a.2.1 B hB, b.2.1 B hB]

/-- The numberings of the blocks are at most `n₂^{n₂}` — the multiplicative cost of
*"individualize all vertices of `V₂`"*. -/
theorem card_isBlockNumbering_le (G : VColBipBlk ↥s ℕ) [Finite ↥s] :
    Nat.card {σ : Set ↥s → ℕ // IsBlockNumbering G σ} ≤ G.numBlocks ^ G.numBlocks := by
  classical
  letI : Fintype ↥G.blocks := Fintype.ofFinite _
  have hcard : Fintype.card ↥G.blocks = G.numBlocks := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]; rfl
  have hinj : Function.Injective
      (fun σ : {σ : Set ↥s → ℕ // IsBlockNumbering G σ} =>
        (fun B : ↥G.blocks => (⟨σ.1 B.1, σ.2.2.2 B.1 B.2⟩ : Fin G.numBlocks))) := by
    intro a b hab
    refine Subtype.ext (funext fun B => ?_)
    by_cases hB : B ∈ G.blocks
    · exact congrArg Fin.val (congrFun hab ⟨B, hB⟩)
    · rw [a.2.1 B hB, b.2.1 B hB]
  refine le_trans (Nat.card_le_card_of_injective _ hinj) ?_
  rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin, hcard]

/-- A numbering of the blocks is carried to a numbering of the blocks by an isomorphism. -/
theorem isBlockNumbering_map {G : VColBipBlk ↥s ℕ} {H : VColBipBlk ↥t ℕ} {φ : ↥s ≃ ↥t}
    (h : G.IsIsoTo H φ) {σ : Set ↥s → ℕ} (hσ : IsBlockNumbering G σ) :
    IsBlockNumbering H (fun C => σ (φ.symm '' C)) := by
  have hnb : G.numBlocks = H.numBlocks := VColBipBlk.numBlocks_eq_of_isIsoTo h
  have hmem : ∀ C : Set ↥t, φ.symm '' C ∈ G.blocks ↔ C ∈ H.blocks := by
    intro C
    rw [← h.blocks (φ.symm '' C), Equiv.image_symm_image]
  refine ⟨fun C hC => hσ.1 _ (fun hc => hC ((hmem C).1 hc)), ?_, ?_⟩
  · intro C hC C' hC' hCC'
    have heq := hσ.2.1 ((hmem C).2 hC) ((hmem C').2 hC') hCC'
    have := congrArg (fun A => φ '' A) heq
    simpa only [Equiv.image_symm_image] using this
  · intro C hC
    rw [← hnb]
    exact hσ.2.2 _ ((hmem C).2 hC)

open scoped Classical in
/-- §9.4, step 2.  The refinement color is canonical: an isomorphism carries the color of a
vertex to the color of its image, for the transported numbering of the blocks. -/
theorem blkColor_map {G : VColBipBlk ↥s ℕ} {H : VColBipBlk ↥t ℕ} {φ : ↥s ≃ ↥t}
    (h : G.IsIsoTo H φ) (σ : Set ↥s → ℕ) (x : ↥s) :
    blkColor H (fun C => σ (φ.symm '' C)) (φ x) = blkColor G σ x := by
  have hnb : G.numBlocks = H.numBlocks := VColBipBlk.numBlocks_eq_of_isIsoTo h
  rw [blkColor, blkColor, h.color₁, ← hnb]
  have hset : (Finset.range G.numBlocks).filter
        (fun i => ∃ B ∈ H.blocks, σ (φ.symm '' B) = i ∧ (φ x, B) ∈ H.E)
      = (Finset.range G.numBlocks).filter
        (fun i => ∃ B ∈ G.blocks, σ B = i ∧ (x, B) ∈ G.E) := by
    refine Finset.filter_congr fun i _ => ?_
    constructor
    · rintro ⟨C, hC, hσC, hE⟩
      refine ⟨φ.symm '' C, ?_, hσC, ?_⟩
      · rw [← h.blocks (φ.symm '' C), Equiv.image_symm_image]; exact hC
      · rw [← h.edges x (φ.symm '' C), Equiv.image_symm_image]; exact hE
    · rintro ⟨B, hB, hσB, hE⟩
      refine ⟨φ '' B, (h.blocks B).2 hB, ?_, (h.edges x B).2 hE⟩
      rwa [Equiv.symm_image_image]
  rw [hset]

/-- §9.4, step 2.  The outcome: the colored partition of `V₁` into the color classes of the
naive refinement. -/
noncomputable def step2Outcome (G : VColBipBlk ↥s ℕ) (σ : Set ↥s → ℕ) :
    (Cat.sub (SplitOutcomes Ω)).Obj s :=
  kerOutcome G.V₁ (blkColor G σ)

/-- §6.  Condition (ii) of Definition 6.0.1 for the outcomes of step 2. -/
theorem step2Outcome_mem_subIso {G : VColBipBlk ↥s ℕ} {H : VColBipBlk ↥t ℕ} {φ : ↥s ≃ ↥t}
    (h : G.IsIsoTo H φ) (σ : Set ↥s → ℕ) :
    φ ∈ (Cat.sub (SplitOutcomes Ω)).Iso (step2Outcome G σ)
      (step2Outcome H (fun C => σ (φ.symm '' C))) :=
  kerOutcome_mem_subIso φ (fun x => h.part₁ x) (fun x => blkColor_map h σ x)

end Step2

/-- §9.4, step 2.  *"If `n₂ ≤ c log n₁` for some specific constant `c > 0` then
individualize all vertices of `V₂`, apply naive vertex refinement, return colored partition
of `V₁`, exit.  Claim.  This is a colored `α`-partition.  Proof.  All vertices of the same
color in `V₁` are twins."*  (Version 2.5, lines 4120-4125.)

The Claim is `Babai.blkColor_eq_imp`: two vertices of `V₁` with the same refinement color
have the same vertex color and the same neighboring blocks, hence are twins
(`Babai.VColBipBlk.isTwin_iff`).  A color class is therefore a set of twins, so it has at
most `symmetricity₁ ≤ α n₁` points and the partition into the color classes is a colored
`α`-partition (`Babai.blkColor_class_le`, `Babai.symmetricity₁_le_alpha`).

The multiplicative cost is the choice of the individualization of `V₂`, that is of a
numbering of the `n₂` blocks: at most `n₂^{n₂}`, a little above the paper's `n₂!`.  On this
subcategory `n₂ ≤ C₀ log₂ n₁`, and `Babai.pow_self_le_cost_of_log_le` shows that
`n₂^{n₂} ≤ constFactor C₀ · costFun n n₂`, which is the cost charged here.  Note that
`(C₀ log₂ n₁)!` is *not* bounded by a constant, so the constant factor alone does not pay
for this step: the turns that the recursion still has do.  (The paper
adds that the method of §4.1.2 brings the cost down to `n₁^{O(1)}`; that refinement is not
needed for the bound proved here.) -/
theorem step_9_4_2 (C₀ N : ℕ) :
    FindsAtMultCost
      (((BipBlockInputsAt Ω N).full fun s Y => ¬ IsSmallPart₁ C₀ ⟨s, Y.1⟩).full
        fun s Y => IsSmallPart₂ C₀ ⟨s, Y.1.1⟩)
      (SplitOutcomes Ω)
      (fun X => cost_9_4 C₀ ⟨X.car, X.obj.1.1.1⟩)
      (fun X Z => Good_9_2_2 ⟨X.car, X.obj.1.1.1⟩ Z) := by
  classical
  refine FindsAtMultCost.of_outcomes_sub
    (fun X =>
      Set.range fun σ : {σ : Set ↥X.car → ℕ // IsBlockNumbering X.obj.1.1.1.1.1 σ} =>
        step2Outcome X.obj.1.1.1.1.1 σ.1)
    (fun X => ?_) (fun X => Set.finite_range _) (fun X => ?_)
    (fun {X Y f} hf Z hZ => ?_) (fun X Z hZ => ?_)
  · obtain ⟨σ, hσ⟩ := exists_isBlockNumbering X.obj.1.1.1.1.1
    exact ⟨_, ⟨⟨σ, hσ⟩, rfl⟩⟩
  · -- at most `n₂^{n₂}` outcomes, which is the cost of individualizing all of `V₂`
    have hsmall : X.obj.1.1.1.1.1.numBlocks
        ≤ C₀ * Nat.log 2 X.obj.1.1.1.1.1.V₁.ncard := X.obj.2
    have hn₁ : X.obj.1.1.1.1.1.V₁.ncard ≤ X.car.ncard := by
      have h := Set.ncard_le_ncard (Set.subset_univ X.obj.1.1.1.1.1.V₁) Set.finite_univ
      rwa [Set.ncard_univ, Nat.card_coe_set_eq] at h
    have hrange :
        (Set.range fun σ : {σ : Set ↥X.car → ℕ // IsBlockNumbering X.obj.1.1.1.1.1 σ} =>
          step2Outcome X.obj.1.1.1.1.1 σ.1).ncard
          ≤ Nat.card {σ : Set ↥X.car → ℕ // IsBlockNumbering X.obj.1.1.1.1.1 σ} := by
      rw [← Set.image_univ]
      have h1 := Set.ncard_image_le (s := (Set.univ :
          Set {σ : Set ↥X.car → ℕ // IsBlockNumbering X.obj.1.1.1.1.1 σ}))
        (f := fun σ => step2Outcome X.obj.1.1.1.1.1 σ.1) Set.finite_univ
      rwa [Set.ncard_univ] at h1
    exact le_trans hrange (le_trans (card_isBlockNumbering_le _)
      (pow_self_le_cost_of_log_le hn₁ hsmall))
  · obtain ⟨σ, rfl⟩ := hZ
    have hiso : X.obj.1.1.1.1.2 = Y.obj.1.1.1.1.2 ∧
        f ∈ (VColBlkGraphs Ω ℕ).Iso X.obj.1.1.1.1.1 Y.obj.1.1.1.1.1 := hf
    have hg : X.obj.1.1.1.1.1.IsIsoTo Y.obj.1.1.1.1.1 f := hiso.2
    exact ⟨step2Outcome Y.obj.1.1.1.1.1 (fun C => σ.1 (f.symm '' C)),
      ⟨⟨fun C => σ.1 (f.symm '' C), isBlockNumbering_map hg σ.2⟩, rfl⟩,
      step2Outcome_mem_subIso hg σ.1⟩
  · obtain ⟨σ, rfl⟩ := hZ
    obtain ⟨hα, hα1, h2, hlt, hdef⟩ := X.obj.1.1.1.2
    letI : Fintype ↥X.car := Fintype.ofFinite _
    letI : DecidableEq ↥X.car := Classical.decEq _
    have hn : 0 < X.obj.1.1.1.1.1.V₁.ncard := by omega
    refine ⟨rfl, kerPartition_isAlphaPartition _ _ _
      (fun x hx => blkColor_class_le X.obj.1.1.1.1.1 σ.2 hx) ?_⟩
    exact symmetricity₁_le_alpha X.obj.1.1.1.1.1 hn hdef

/-! ### §9.4, steps 3 and 4: WL refinement, and the branch on the vertex-color classes

*"3. Apply WL refinement to `X`. …  4. If all vertex-color classes in `V₁` have size
`≤ αn₁` then return the colored partition of `V₁`, exit (objective (a) achieved)
(: dominant vertex-color class has size `> αn₁` :)"*  (Version 2.5, lines 4126-4135.)

Step 3 is `Babai.VColBipBlk.wlColor` (`Workspace/SplitOrJohnson/WLColor.lean`): the
coherent configuration `X` of the paper, on the vertex set *"points of `V₁` plus blocks"*,
with its colors named by natural numbers canonically.  It adds no data to the input — the
coloring is a function of the object — so step 3 changes no category; what it contributes
is the vertex coloring `Babai.VColBipBlk.wlDiag` of step 4 and its canonicity.

Step 4 is a branch.  Its condition is `Babai.AllClassesSmall`, and in the positive branch
the outcome is the colored partition of `V₁` into the classes of `wlDiag`, which the
condition makes a colored `α`-partition. -/

/-- §9.4, step 4.  *"all vertex-color classes in `V₁` have size `≤ αn₁`"*, for the vertex
coloring of the coherent configuration produced by step 3. -/
noncomputable def AllClassesSmall (X : Pt (BipBlockInputs Ω)) : Prop :=
  ∀ x ∈ X.obj.1.1.V₁,
    (({y : ↥X.car | y ∈ X.obj.1.1.V₁ ∧
        VColBipBlk.wlDiag X.obj.1.1 y = VColBipBlk.wlDiag X.obj.1.1 x}.ncard : ℝ))
      ≤ BipBlockInputs.alpha X * (BipBlockInputs.n₁ X : ℝ)

/-- §9.4, step 4.  The class of the vertex color `k` inside `V₁`. -/
noncomputable def colorClass₁ (X : Pt (BipBlockInputs Ω)) (k : ℕ) : Set ↥X.car :=
  {y : ↥X.car | y ∈ X.obj.1.1.V₁ ∧ VColBipBlk.wlDiag X.obj.1.1 y = k}

/-- §9.4, steps 3 and 4.  An isomorphism carries the class of a vertex color onto the class
of the **same** vertex color: this is the canonicity of step 3
(`Babai.VColBipBlk.wlDiag_map`), and it is what makes every condition of steps 4 to 8 an
isomorphism invariant. -/
theorem colorClass₁_image {X Y : Pt (BipBlockInputs Ω)} {φ : ↥X.car ≃ ↥Y.car}
    (hφ : φ ∈ (BipBlockInputs Ω).IsoP X Y) (k : ℕ) :
    colorClass₁ Y k = φ '' colorClass₁ X k := by
  have hg : X.obj.1.1.IsIsoTo Y.obj.1.1 φ := hφ.2
  have hmem : ∀ x : ↥X.car, φ x ∈ Y.obj.1.1.V₁ ↔ x ∈ X.obj.1.1.V₁ := fun x => hg.part₁ x
  ext z'
  constructor
  · rintro ⟨hz1, hz2⟩
    refine ⟨φ.symm z', ⟨?_, ?_⟩, φ.apply_symm_apply z'⟩
    · rw [← hmem (φ.symm z'), Equiv.apply_symm_apply]; exact hz1
    · rw [← VColBipBlk.wlDiag_map hg, Equiv.apply_symm_apply]; exact hz2
  · rintro ⟨z, ⟨hz1, hz2⟩, rfl⟩
    exact ⟨(hmem z).2 hz1, (VColBipBlk.wlDiag_map hg z).trans hz2⟩

theorem colorClass₁_ncard_congr {X Y : Pt (BipBlockInputs Ω)}
    (h : ((BipBlockInputs Ω).IsoP X Y).Nonempty) (k : ℕ) :
    (colorClass₁ X k).ncard = (colorClass₁ Y k).ncard := by
  obtain ⟨φ, hφ⟩ := h
  rw [colorClass₁_image hφ k, Set.ncard_image_of_injective _ φ.injective]

theorem allClassesSmall_iff (X : Pt (BipBlockInputs Ω)) :
    AllClassesSmall X ↔ ∀ k : ℕ, ((colorClass₁ X k).ncard : ℝ)
      ≤ BipBlockInputs.alpha X * (BipBlockInputs.n₁ X : ℝ) := by
  constructor
  · intro h k
    rcases Set.eq_empty_or_nonempty (colorClass₁ X k) with he | ⟨x, hx⟩
    · rw [he]
      have hα : (0 : ℝ) ≤ BipBlockInputs.alpha X * (BipBlockInputs.n₁ X : ℝ) := by
        have h1 : (2 : ℝ) / 3 ≤ BipBlockInputs.alpha X := X.obj.2.1
        have h2 : (0 : ℝ) ≤ (BipBlockInputs.n₁ X : ℝ) := Nat.cast_nonneg _
        nlinarith
      simpa using hα
    · have hk : VColBipBlk.wlDiag X.obj.1.1 x = k := hx.2
      have := h x hx.1
      rwa [show {y : ↥X.car | y ∈ X.obj.1.1.V₁ ∧
        VColBipBlk.wlDiag X.obj.1.1 y = VColBipBlk.wlDiag X.obj.1.1 x}
          = colorClass₁ X k by rw [colorClass₁, hk]] at this
  · intro h x hx
    exact h (VColBipBlk.wlDiag X.obj.1.1 x)

/-- §9.4, step 4.  The branch condition is an isomorphism invariant, which is what
`Babai.FindsAtMultCost.cases` asks of it.  This is the canonicity of step 3
(`Babai.colorClass₁_image`) together with the invariance of `α` and of `n₁`. -/
theorem allClassesSmall_congr {X Y : Pt (BipBlockInputs Ω)}
    (h : ((BipBlockInputs Ω).IsoP X Y).Nonempty) (hX : AllClassesSmall X) :
    AllClassesSmall Y := by
  obtain ⟨φ, hφ⟩ := h
  have hα : BipBlockInputs.alpha X = BipBlockInputs.alpha Y := hφ.1
  have hn₁ : BipBlockInputs.n₁ X = BipBlockInputs.n₁ Y := BipBlockInputs.n₁_congr ⟨φ, hφ⟩
  refine (allClassesSmall_iff Y).2 fun k => ?_
  rw [← colorClass₁_ncard_congr ⟨φ, hφ⟩ k, ← hα, ← hn₁]
  exact (allClassesSmall_iff X).1 hX k

/-- §9.4, step 4.  *"If all vertex-color classes in `V₁` have size `≤ αn₁` then return the
colored partition of `V₁`, exit (objective (a) achieved)."*  (Version 2.5, lines
4132-4134.)

The partition returned is `Babai.kerPartition` for the vertex coloring
`Babai.VColBipBlk.wlDiag` of step 3, so its blocks are exactly the vertex-color classes; by
the branch condition each of them has at most `α n₁` points, so it is a colored
`α`-partition (Def. 7.1.1), which is objective (a).  There is one outcome, so the
multiplicative cost is `1`; the canonicity is the canonicity of step 3
(`Babai.VColBipBlk.wlDiag_map`). -/
theorem step_9_4_4 (C₀ N : ℕ) :
    FindsAtMultCost
      ((((BipBlockInputsAt Ω N).full fun s Y => ¬ IsSmallPart₁ C₀ ⟨s, Y.1⟩).full
        fun s Y => ¬ IsSmallPart₂ C₀ ⟨s, Y.1.1⟩).full
        fun s Y => AllClassesSmall ⟨s, Y.1.1.1⟩)
      (SplitOutcomes Ω)
      (fun X => cost_9_4 C₀ ⟨X.car, X.obj.1.1.1.1⟩)
      (fun X Z => Good_9_2_2 ⟨X.car, X.obj.1.1.1.1⟩ Z) := by
  classical
  refine FindsAtMultCost.of_outcomes_sub
    (fun X => {kerOutcome X.obj.1.1.1.1.1.1.V₁
      (VColBipBlk.wlDiag X.obj.1.1.1.1.1.1)})
    (fun X => Set.singleton_nonempty _) (fun X => Set.finite_singleton _) (fun X => ?_)
    (fun {X Y f} hf Z hZ => ?_) (fun X Z hZ => ?_)
  · rw [Set.ncard_singleton]
    exact Nat.mul_pos (one_le_constFactor C₀) (Nat.one_le_pow _ _ (one_le_turnCost _))
  · rw [Set.mem_singleton_iff] at hZ
    subst hZ
    have hiso : X.obj.1.1.1.1.1.2 = Y.obj.1.1.1.1.1.2 ∧
        f ∈ (VColBlkGraphs Ω ℕ).Iso X.obj.1.1.1.1.1.1 Y.obj.1.1.1.1.1.1 := hf
    have hg : X.obj.1.1.1.1.1.1.IsIsoTo Y.obj.1.1.1.1.1.1 f := hiso.2
    exact ⟨_, rfl, kerOutcome_mem_subIso f (fun x => hg.part₁ x)
      (fun x => VColBipBlk.wlDiag_map hg x)⟩
  · rw [Set.mem_singleton_iff] at hZ
    subst hZ
    obtain ⟨hα, hα1, hinput⟩ := X.obj.1.1.1.1.2
    have hsmall := X.obj.2
    refine ⟨rfl, ?_⟩
    set G := X.obj.1.1.1.1.1.1 with hG
    set a := X.obj.1.1.1.1.1.2 with ha
    have hapos : (0 : ℝ) ≤ a * (G.V₁.ncard : ℝ) := by
      have : (0 : ℝ) ≤ a := by linarith
      positivity
    refine kerPartition_isAlphaPartition G.V₁ _ _ (k := ⌊a * (G.V₁.ncard : ℝ)⌋₊)
      (fun x hx => ?_) (Nat.floor_le hapos)
    exact Nat.le_floor (hsmall x hx)

/-! ### §9.4, step 5: the dominant vertex-color class

*"5. Let `W₁ ⊆ V₁` be the dominant color class: `|W₁| > αn₁`."*  (Version 2.5, line 4136.)

The class exists because this is the negative branch of step 4, and it is *unique* because
`α ≥ 2/3 > 1/2`: two classes of more than half of `V₁` cannot be disjoint.  Uniqueness is
what makes *"the dominant color class"* a canonical construction, so `W₁` is built here and
the rest of step 5 — the restriction of the instance and the update `α ← α n₁ / |W₁|`,
whose arithmetic is `Babai.claim_9_4_step5_at` — is left to `Babai.steps_9_4_5_to_9`. -/

/-- §9.4, step 5.  The vertex colors whose class inside `V₁` has more than `α n₁`
points. -/
noncomputable def dominantColors (X : Pt (BipBlockInputs Ω)) : Set ℕ :=
  {k | BipBlockInputs.alpha X * (BipBlockInputs.n₁ X : ℝ) < ((colorClass₁ X k).ncard : ℝ)}

theorem alpha_mul_n₁_nonneg (X : Pt (BipBlockInputs Ω)) :
    (0 : ℝ) ≤ BipBlockInputs.alpha X * (BipBlockInputs.n₁ X : ℝ) := by
  have h1 : (2 : ℝ) / 3 ≤ BipBlockInputs.alpha X := X.obj.2.1
  have h2 : (0 : ℝ) ≤ (BipBlockInputs.n₁ X : ℝ) := Nat.cast_nonneg _
  nlinarith

/-- A dominant color is the color of a point of `V₁`: its class is non-empty. -/
theorem exists_mem_of_mem_dominantColors {X : Pt (BipBlockInputs Ω)} {k : ℕ}
    (hk : k ∈ dominantColors X) :
    ∃ y ∈ X.obj.1.1.V₁, VColBipBlk.wlDiag X.obj.1.1 y = k := by
  have hpos : (0 : ℝ) < ((colorClass₁ X k).ncard : ℝ) :=
    lt_of_le_of_lt (alpha_mul_n₁_nonneg X) hk
  have hne : (colorClass₁ X k).ncard ≠ 0 := by
    intro h0; rw [h0] at hpos; norm_num at hpos
  obtain ⟨y, hy⟩ := Set.nonempty_of_ncard_ne_zero hne
  exact ⟨y, hy.1, hy.2⟩

theorem dominantColors_bddAbove (X : Pt (BipBlockInputs Ω)) :
    BddAbove (dominantColors X) := by
  refine Set.Finite.bddAbove (Set.Finite.subset
    (Set.Finite.image (VColBipBlk.wlDiag X.obj.1.1) (Set.toFinite X.obj.1.1.V₁)) ?_)
  intro k hk
  obtain ⟨y, hy, hyk⟩ := exists_mem_of_mem_dominantColors hk
  exact ⟨y, hy, hyk⟩

/-- §9.4, step 5.  *"the dominant vertex-color class has size `> αn₁`"*: in the negative
branch of step 4 a dominant color exists. -/
theorem dominantColors_nonempty {X : Pt (BipBlockInputs Ω)} (h : ¬ AllClassesSmall X) :
    (dominantColors X).Nonempty := by
  rw [allClassesSmall_iff] at h
  push_neg at h
  obtain ⟨k, hk⟩ := h
  exact ⟨k, hk⟩

/-- §9.4, step 5.  **The dominant color is unique.**  Two classes of more than `α n₁`
points would be disjoint subsets of `V₁` of more than half of `V₁` each, since
`α ≥ 2/3`. -/
theorem dominantColors_subsingleton (X : Pt (BipBlockInputs Ω)) :
    (dominantColors X).Subsingleton := by
  intro k hk k' hk'
  by_contra hne
  have hdisj : Disjoint (colorClass₁ X k) (colorClass₁ X k') := by
    rw [Set.disjoint_left]
    rintro y ⟨-, hy⟩ ⟨-, hy'⟩
    exact hne (hy ▸ hy')
  have hsub : colorClass₁ X k ∪ colorClass₁ X k' ⊆ X.obj.1.1.V₁ := by
    rintro y (⟨hy, -⟩ | ⟨hy, -⟩) <;> exact hy
  have hunion : (colorClass₁ X k).ncard + (colorClass₁ X k').ncard
      = (colorClass₁ X k ∪ colorClass₁ X k').ncard :=
    (Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _)).symm
  have hle : (colorClass₁ X k ∪ colorClass₁ X k').ncard ≤ BipBlockInputs.n₁ X :=
    Set.ncard_le_ncard hsub (Set.toFinite _)
  have hleR : ((colorClass₁ X k).ncard : ℝ) + ((colorClass₁ X k').ncard : ℝ)
      ≤ (BipBlockInputs.n₁ X : ℝ) := by
    have : (colorClass₁ X k).ncard + (colorClass₁ X k').ncard ≤ BipBlockInputs.n₁ X := by
      omega
    exact_mod_cast this
  have hα : (2 : ℝ) / 3 ≤ BipBlockInputs.alpha X := X.obj.2.1
  have hn : (2 : ℝ) ≤ (BipBlockInputs.n₁ X : ℝ) := by
    have h2 : 2 ≤ X.obj.1.1.V₁.ncard := X.obj.2.2.2.1
    exact_mod_cast h2
  have hk1 : BipBlockInputs.alpha X * (BipBlockInputs.n₁ X : ℝ)
      < ((colorClass₁ X k).ncard : ℝ) := hk
  have hk2 : BipBlockInputs.alpha X * (BipBlockInputs.n₁ X : ℝ)
      < ((colorClass₁ X k').ncard : ℝ) := hk'
  have hprod : (2 : ℝ) / 3 * (BipBlockInputs.n₁ X : ℝ)
      ≤ BipBlockInputs.alpha X * (BipBlockInputs.n₁ X : ℝ) :=
    mul_le_mul_of_nonneg_right hα (by linarith)
  linarith

/-- §9.4, step 5.  *"the dominant color class"*: the unique vertex color whose class inside
`V₁` has more than `α n₁` points (`Babai.dominantColors_subsingleton`), written as the
supremum so that it is manifestly a function of the input alone. -/
noncomputable def dominantColor (X : Pt (BipBlockInputs Ω)) : ℕ := sSup (dominantColors X)

theorem dominantColor_mem {X : Pt (BipBlockInputs Ω)} (h : ¬ AllClassesSmall X) :
    dominantColor X ∈ dominantColors X :=
  Nat.sSup_mem (dominantColors_nonempty h) (dominantColors_bddAbove X)

/-- §9.4, step 5.  `W₁`, the dominant color class. -/
noncomputable def dominantClass (X : Pt (BipBlockInputs Ω)) : Set ↥X.car :=
  colorClass₁ X (dominantColor X)

theorem dominantClass_subset (X : Pt (BipBlockInputs Ω)) :
    dominantClass X ⊆ X.obj.1.1.V₁ := fun _ hy => hy.1

/-- §9.4, step 5.  *"`|W₁| > αn₁`"*. -/
theorem alpha_mul_n₁_lt_dominantClass {X : Pt (BipBlockInputs Ω)}
    (h : ¬ AllClassesSmall X) :
    BipBlockInputs.alpha X * (BipBlockInputs.n₁ X : ℝ) < ((dominantClass X).ncard : ℝ) :=
  dominantColor_mem h

theorem dominantColors_congr {X Y : Pt (BipBlockInputs Ω)}
    (h : ((BipBlockInputs Ω).IsoP X Y).Nonempty) : dominantColors X = dominantColors Y := by
  obtain ⟨φ, hφ⟩ := h
  have hα : BipBlockInputs.alpha X = BipBlockInputs.alpha Y := hφ.1
  have hn₁ : BipBlockInputs.n₁ X = BipBlockInputs.n₁ Y := BipBlockInputs.n₁_congr ⟨φ, hφ⟩
  ext k
  simp only [dominantColors, Set.mem_setOf_eq]
  rw [hα, hn₁, colorClass₁_ncard_congr ⟨φ, hφ⟩ k]

theorem dominantColor_congr {X Y : Pt (BipBlockInputs Ω)}
    (h : ((BipBlockInputs Ω).IsoP X Y).Nonempty) : dominantColor X = dominantColor Y := by
  rw [dominantColor, dominantColor, dominantColors_congr h]

/-- §9.4, step 5.  **`W₁` is canonical.**  A morphism of the inputs carries the dominant
color class onto the dominant color class, which is what makes the restriction of step 5 a
functor. -/
theorem dominantClass_image {X Y : Pt (BipBlockInputs Ω)} {φ : ↥X.car ≃ ↥Y.car}
    (hφ : φ ∈ (BipBlockInputs Ω).IsoP X Y) :
    dominantClass Y = φ '' dominantClass X := by
  rw [dominantClass, dominantClass, ← dominantColor_congr ⟨φ, hφ⟩,
    colorClass₁_image hφ (dominantColor X)]

/-! ### The induced subobject, for steps 5 and 7

Steps 5 and 7 both replace `X` by an induced substructure: step 5 by `X[W₁ ∪ V₂]` and
step 7 by `X[V₁ ∪ D_j]`.  In both the new point set is a subset `s'` of the old one, the
blocks that survive are those contained in `s'`, and the colorings and the edge relation
are inherited.  `Babai.VColBipBlk.restrictTo` is that construction. -/

namespace VColBipBlk

section Restrict

variable {Ω : Type} {κ : Type} [Zero κ] {s s' : Set Ω}

/-- The inclusion of a subset of the ambient set into a larger one, on the level of the
point types. -/
def incl (hs : s' ⊆ s) : ↥s' → ↥s := fun x => ⟨(x : Ω), hs x.2⟩

theorem incl_injective (hs : s' ⊆ s) : Function.Injective (incl hs) :=
  fun _ _ h => Subtype.ext (congrArg (fun z : ↥s => (z : Ω)) h)

theorem incl_image_injective (hs : s' ⊆ s) :
    Function.Injective (fun B : Set ↥s' => incl hs '' B) :=
  Set.image_injective.2 (incl_injective hs)

open scoped Classical in
/-- §9.4, steps 5 and 7.  **The induced subobject `X[s']`.**  The first part, the edges and
the two colorings are inherited along the inclusion, and a block of `X[s']` is a set of
points of `s'` whose image is a block of `X`; so the blocks of `X` that are not contained
in `s'` simply disappear.

The block coloring is renormalized (`g_off`) so that it is `0` off the new blocks; this is
the normalization that `Babai.VColBipBlk` demands, see the module docstring of
`Workspace/SplitOrJohnson/BipBlocks.lean`. -/
noncomputable def restrictTo (G : VColBipBlk ↥s κ) (hs : s' ⊆ s) : VColBipBlk ↥s' κ where
  part₁ x := G.part₁ (incl hs x)
  blocks := {B | incl hs '' B ∈ G.blocks}
  blocks_nonempty B hB := by
    obtain ⟨y, hy⟩ := G.blocks_nonempty _ hB
    obtain ⟨x, hx, -⟩ := hy
    exact ⟨x, hx⟩
  blocks_disjoint B hB B' hB' hne := by
    have hne' : incl hs '' B ≠ incl hs '' B' := fun h => hne (incl_image_injective hs h)
    have hd := G.blocks_disjoint _ hB _ hB' hne'
    rw [Set.disjoint_left] at hd ⊢
    intro x hxB hxB'
    exact hd (Set.mem_image_of_mem _ hxB) (Set.mem_image_of_mem _ hxB')
  blocks_off₁ B hB x hx :=
    G.blocks_off₁ _ hB (incl hs x) (Set.mem_image_of_mem _ hx)
  E := {p | (incl hs p.1, incl hs '' p.2) ∈ G.E}
  E_sub p hp := ⟨(G.E_sub _ hp).1, (G.E_sub _ hp).2⟩
  f x := G.f (incl hs x)
  g B := if incl hs '' B ∈ G.blocks then G.g (incl hs '' B) else 0
  g_off B hB := if_neg hB
  -- **The hint is kept.**  No renormalization is needed: a set of points of `s'` is a
  -- block of the restriction exactly when its image is a block of `G`, so `G.h_off`
  -- already gives the padding color `0` off the new blocks.
  h A B := G.h (incl hs '' A) (incl hs '' B)
  h_off A B hAB := G.h_off _ _ hAB

@[simp] theorem restrictTo_part₁ (G : VColBipBlk ↥s κ) (hs : s' ⊆ s) (x : ↥s') :
    (G.restrictTo hs).part₁ x ↔ G.part₁ (incl hs x) := Iff.rfl

@[simp] theorem restrictTo_blocks (G : VColBipBlk ↥s κ) (hs : s' ⊆ s) (B : Set ↥s') :
    B ∈ (G.restrictTo hs).blocks ↔ incl hs '' B ∈ G.blocks := Iff.rfl

@[simp] theorem restrictTo_E (G : VColBipBlk ↥s κ) (hs : s' ⊆ s) (x : ↥s') (B : Set ↥s') :
    (x, B) ∈ (G.restrictTo hs).E ↔ (incl hs x, incl hs '' B) ∈ G.E := Iff.rfl

@[simp] theorem restrictTo_f (G : VColBipBlk ↥s κ) (hs : s' ⊆ s) (x : ↥s') :
    (G.restrictTo hs).f x = G.f (incl hs x) := rfl

/-- §9.4, steps 5 and 7.  **The hint survives the restriction**: the hint of `X[s']` at a
pair of sets of points of `s'` is the hint of `X` at the pair of their images.  This is
what makes the third kind of major progress of §9.5 — *"`X₂` moves from clique to UPCC
while `n₂` does not increase"* — available to the next turn. -/
@[simp] theorem restrictTo_h (G : VColBipBlk ↥s κ) (hs : s' ⊆ s) (A B : Set ↥s') :
    (G.restrictTo hs).h A B = G.h (incl hs '' A) (incl hs '' B) := rfl

/-- The first part of the induced subobject is the part of the old first part that lies
in `s'`. -/
theorem restrictTo_V₁ (G : VColBipBlk ↥s κ) (hs : s' ⊆ s) :
    (G.restrictTo hs).V₁ = incl hs ⁻¹' G.V₁ := rfl

/-- **The blocks are kept**, provided every block of `X` lies inside `s'`: then the blocks
of `X[s']` are exactly the preimages of the blocks of `X`.  This is the situation of
step 5, where `s' = W₁ ∪ V₂` keeps all of `V₂`. -/
theorem restrictTo_blocks_image (G : VColBipBlk ↥s κ) (hs : s' ⊆ s)
    (hb : ∀ B ∈ G.blocks, ∀ x ∈ B, (x : Ω) ∈ s') :
    (fun B : Set ↥s' => incl hs '' B) '' (G.restrictTo hs).blocks = G.blocks := by
  ext B
  constructor
  · rintro ⟨B', hB', rfl⟩; exact hB'
  · intro hB
    have himg : incl hs '' (incl hs ⁻¹' B) = B :=
      le_antisymm (Set.image_preimage_subset _ _) (by
        rintro y hy
        exact ⟨⟨(y : Ω), hb B hB y hy⟩, hy, rfl⟩)
    exact ⟨incl hs ⁻¹' B, by rw [restrictTo_blocks, himg]; exact hB, himg⟩

/-- **`n₂` does not change** when every block lies inside `s'`. -/
theorem restrictTo_numBlocks (G : VColBipBlk ↥s κ) (hs : s' ⊆ s)
    (hb : ∀ B ∈ G.blocks, ∀ x ∈ B, (x : Ω) ∈ s') :
    (G.restrictTo hs).numBlocks = G.numBlocks := by
  rw [numBlocks, numBlocks, ← restrictTo_blocks_image G hs hb,
    Set.ncard_image_of_injective _ (incl_image_injective hs)]

/-- §9.4, step 5.  **Twins of the induced subobject are twins of `X`.**  Two points of the
new first part that have the same vertex color and the same neighboring blocks *in
`X[s']`* have the same vertex color and the same neighboring blocks *in `X`*, provided
every block of `X` lies inside `s'`.

This is what carries the symmetry defect hypothesis of Theorem 9.2.2 through step 5: a set
of twins of the restriction is a set of twins of `X`
(`Babai.VColBipBlk.isTwin_iff` in both directions), so it obeys the bound
`Babai.ncard_le_alphaNew_mul_dominantClass`. -/
theorem restrictTo_twin_imp (G : VColBipBlk ↥s κ) (hs : s' ⊆ s)
    (hb : ∀ B ∈ G.blocks, ∀ x ∈ B, (x : Ω) ∈ s') {x y : ↥s'}
    (hf : (G.restrictTo hs).f x = (G.restrictTo hs).f y)
    (hE : ∀ B ∈ (G.restrictTo hs).blocks,
      ((x, B) ∈ (G.restrictTo hs).E ↔ (y, B) ∈ (G.restrictTo hs).E)) :
    G.f (incl hs x) = G.f (incl hs y) ∧
      ∀ B ∈ G.blocks, ((incl hs x, B) ∈ G.E ↔ (incl hs y, B) ∈ G.E) := by
  refine ⟨hf, fun B hB => ?_⟩
  have hsub : B ⊆ incl hs '' (incl hs ⁻¹' B) := by
    rintro y' hy'
    exact ⟨⟨(y' : Ω), hb B hB y' hy'⟩, hy', rfl⟩
  have himg : incl hs '' (incl hs ⁻¹' B) = B :=
    le_antisymm (Set.image_preimage_subset _ _) hsub
  have hB' : incl hs ⁻¹' B ∈ (G.restrictTo hs).blocks := by
    rw [restrictTo_blocks, himg]; exact hB
  have h := hE _ hB'
  rw [restrictTo_E, restrictTo_E, himg] at h
  exact h

end Restrict

end VColBipBlk

/-! ### §9.4, step 5: the restriction to `W₁ ∪ V₂` and the new threshold

*"5. Let `W₁ ⊆ V₁` be the dominant color class: `|W₁| > αn₁`.  Update `α ← αn₁/|W₁|`,
`V₁ ← W₁` (this automatically updates `n₁`), `X ← X[W₁, V₂]` (induced subgraph),
`X ← X[W₁ ∪ V₂]`; this automatically updates `X₁`, `X₂`, `X₁₂`."*  (Version 2.5,
lines 4136-4139.)

The class `W₁` is `Babai.dominantClass`; it exists (`Babai.dominantColors_nonempty`), is
unique (`Babai.dominantColors_subsingleton`) and is canonical
(`Babai.dominantClass_image`).  What this block adds is the arithmetic of the update and
the **admissibility of the restricted instance**, which is the hypothesis that §9.6-§9.8
inherit from Theorem 9.2.2.

The one delicate point is the symmetry defect.  The restricted graph `X[W₁, V₂]` keeps the
second part and keeps the colors, so two points of `W₁` are twins in it exactly when they
are twins in `X` (`Babai.VColBipBlk.isTwin_iff`: being twins means having the same color
and the same set of neighboring blocks, and neither changes under the restriction).  A set
of twins of the restriction is therefore a set of twins of `X`, so it has at most
`symmetricity₁(X) ≤ α n₁` points, and `α n₁ = α_new |W₁|` is exactly the bound that
*"symmetry defect `≥ 1 - α_new` on `W₁`"* asks for.
`Babai.ncard_le_alphaNew_mul_dominantClass` is that bound, stated for an arbitrary set of
twins of `X` inside `V₁` so that it needs no restriction construction. -/

/-- §9.4, step 5.  *"Update `α ← α n₁ / |W₁|`"*: the threshold of the restricted
instance. -/
noncomputable def alphaNew (X : Pt (BipBlockInputs Ω)) : ℝ :=
  BipBlockInputs.alpha X * (BipBlockInputs.n₁ X : ℝ) / ((dominantClass X).ncard : ℝ)

/-- `W₁ ⊆ V₁`, so `|W₁| ≤ n₁`: *"`n₁` will not increase"* (§9.5). -/
theorem dominantClass_ncard_le (X : Pt (BipBlockInputs Ω)) :
    (dominantClass X).ncard ≤ BipBlockInputs.n₁ X :=
  Set.ncard_le_ncard (dominantClass_subset X) (Set.toFinite _)

/-- *"`|V₁| ≥ 2`"*, a hypothesis of Theorem 9.2.2. -/
theorem two_le_n₁ (X : Pt (BipBlockInputs Ω)) : 2 ≤ BipBlockInputs.n₁ X := X.obj.2.2.2.1

/-- §9.4, step 5.  The new first part has at least two points, so the restricted instance
satisfies *"`|V₁| ≥ 2`"*: `|W₁| > α n₁ ≥ (2/3)·2 > 1`. -/
theorem two_le_dominantClass_ncard {X : Pt (BipBlockInputs Ω)} (h : ¬ AllClassesSmall X) :
    2 ≤ (dominantClass X).ncard := by
  have hlt := alpha_mul_n₁_lt_dominantClass h
  have hα : (2 : ℝ) / 3 ≤ BipBlockInputs.alpha X := X.obj.2.1
  have hn : (2 : ℝ) ≤ (BipBlockInputs.n₁ X : ℝ) := by exact_mod_cast two_le_n₁ X
  have h1 : (1 : ℝ) < ((dominantClass X).ncard : ℝ) := by nlinarith
  have h2 : 1 < (dominantClass X).ncard := by exact_mod_cast h1
  omega

theorem dominantClass_ncard_pos {X : Pt (BipBlockInputs Ω)} (h : ¬ AllClassesSmall X) :
    (0 : ℝ) < ((dominantClass X).ncard : ℝ) := by
  have := two_le_dominantClass_ncard h
  have : (0 : ℕ) < (dominantClass X).ncard := by omega
  exact_mod_cast this

/-- §9.4, step 5.  **The bookkeeping of the update**: `α_new |W₁| = α n₁`.  This is what
carries a colored `α_new`-partition of `W₁` back to a colored `α`-partition of `V₁`, and
what makes a Johnson scheme on `≥ α_new |W₁|` points of `W₁` a Johnson scheme on
`≥ α n₁` points of `V₁`. -/
theorem alphaNew_mul_dominantClass {X : Pt (BipBlockInputs Ω)} (h : ¬ AllClassesSmall X) :
    alphaNew X * ((dominantClass X).ncard : ℝ)
      = BipBlockInputs.alpha X * (BipBlockInputs.n₁ X : ℝ) := by
  have hm : ((dominantClass X).ncard : ℝ) ≠ 0 := ne_of_gt (dominantClass_ncard_pos h)
  rw [alphaNew, div_mul_cancel₀ _ hm]

/-- §9.4, step 5.  The threshold does not decrease, because `|W₁| ≤ n₁`. -/
theorem alpha_le_alphaNew {X : Pt (BipBlockInputs Ω)} (h : ¬ AllClassesSmall X) :
    BipBlockInputs.alpha X ≤ alphaNew X := by
  have hm : (0 : ℝ) < ((dominantClass X).ncard : ℝ) := dominantClass_ncard_pos h
  have hle : ((dominantClass X).ncard : ℝ) ≤ (BipBlockInputs.n₁ X : ℝ) := by
    exact_mod_cast dominantClass_ncard_le X
  have hα : (0 : ℝ) ≤ BipBlockInputs.alpha X := by
    have : (2 : ℝ) / 3 ≤ BipBlockInputs.alpha X := X.obj.2.1
    linarith
  rw [alphaNew, le_div_iff₀ hm]
  nlinarith

/-- §9.4, step 5.  The new threshold is still below `1`, because `|W₁| > α n₁`. -/
theorem alphaNew_lt_one {X : Pt (BipBlockInputs Ω)} (h : ¬ AllClassesSmall X) :
    alphaNew X < 1 := by
  rw [alphaNew, div_lt_one (dominantClass_ncard_pos h)]
  exact alpha_mul_n₁_lt_dominantClass h

/-- §9.4, step 5.  **The arithmetic of the update `α ← α n₁ / |W₁|`, `V₁ ← W₁`.**  The
restricted instance again carries an admissible threshold — `2/3 ≤ α_new < 1`, the range
that `Babai.BipBlockInputs` asks for — its first part again has at least two points, and
the product `α n₁` that all the outcome statements are measured against is unchanged.

This is `Babai.claim_9_4_step5` (`Workspace/SplitOrJohnson/Procedure.lean`), which states
the same arithmetic for bare numbers, read at an object of the category. -/
theorem claim_9_4_step5_at {X : Pt (BipBlockInputs Ω)} (h : ¬ AllClassesSmall X) :
    2 / 3 ≤ alphaNew X ∧ alphaNew X < 1 ∧
      alphaNew X * ((dominantClass X).ncard : ℝ)
        = BipBlockInputs.alpha X * (BipBlockInputs.n₁ X : ℝ) ∧
      2 ≤ (dominantClass X).ncard :=
  ⟨le_trans X.obj.2.1 (alpha_le_alphaNew h), alphaNew_lt_one h,
    alphaNew_mul_dominantClass h, two_le_dominantClass_ncard h⟩

/-- §9.4, step 5.  **The symmetry defect of the restricted instance.**  *"the symmetry
defect of `X` on `V₁` is at least `1 - α`"* is inherited by `X[W₁ ∪ V₂]` with the new
threshold: a set of twins inside `V₁` has at most `α n₁ = α_new |W₁|` points.

Two points of `W₁` that are twins in the restriction `X[W₁, V₂]` are twins in `X` — being
twins means having the same vertex color and the same set of neighboring blocks
(`Babai.VColBipBlk.isTwin_iff`), and the restriction changes neither — so a set of twins
of the restriction inside `W₁` is a set of twins of `X` inside `V₁`, and this bound applies
to it.  Since `1 - α_new = 1 - (α_new |W₁|)/|W₁|`, the defect of `W₁` in the restriction is
at least `1 - α_new`, which is the hypothesis of Theorem 9.2.2 for the restricted
instance.

The hypothesis is the twin condition of `Babai.VColBipBlk.isTwin_iff` written out — same
vertex color, same set of neighboring blocks — rather than `Babai.IsTwinSet`, because that
is the form in which the restricted instance delivers it, and because it mentions no
decidability instance. -/
theorem ncard_le_alphaNew_mul_dominantClass {X : Pt (BipBlockInputs Ω)}
    (hd : ¬ AllClassesSmall X) {S : Set ↥X.car}
    (hS : ∀ x ∈ S, X.obj.1.1.part₁ x)
    (hT : ∀ x ∈ S, ∀ y ∈ S, X.obj.1.1.f x = X.obj.1.1.f y ∧
      ∀ B ∈ X.obj.1.1.blocks, ((x, B) ∈ X.obj.1.1.E ↔ (y, B) ∈ X.obj.1.1.E)) :
    (S.ncard : ℝ) ≤ alphaNew X * ((dominantClass X).ncard : ℝ) := by
  classical
  letI : Fintype ↥X.car := Fintype.ofFinite _
  letI : DecidableEq ↥X.car := Classical.decEq _
  obtain ⟨hα, hα1, h2, hlt, hdef⟩ := X.obj.2
  have hTS : IsTwinSet X.obj.1.1.Aut S := by
    intro x hx y hy hne
    exact (X.obj.1.1.isTwin_iff (hS x hx) (hS y hy) hne).2 (hT x hx y hy)
  have h1 : S.ncard ≤ X.obj.1.1.symmetricity₁ := ncard_le_symmetricity₁ _ hS hTS
  have hn : 0 < X.obj.1.1.V₁.ncard := by omega
  have h3 := symmetricity₁_le_alpha X.obj.1.1 hn hdef
  have h4 : (S.ncard : ℝ) ≤ (X.obj.1.1.symmetricity₁ : ℝ) := by exact_mod_cast h1
  rw [alphaNew_mul_dominantClass hd]
  exact h4.trans h3

/-! #### The restricted instance `X[W₁ ∪ V₂]` and its admissibility -/

/-- §9.4, step 5.  The new point set `W₁ ∪ V₂`: the dominant color class together with all
the points that lie in blocks. -/
noncomputable def step5Set (X : Pt (BipBlockInputs Ω)) : Set Ω :=
  Subtype.val '' (dominantClass X ∪ X.obj.1.1.support₂)

theorem step5Set_subset (X : Pt (BipBlockInputs Ω)) : step5Set X ⊆ X.car := by
  rintro z ⟨w, -, rfl⟩; exact w.2

/-- §9.4, step 5.  *"`X ← X[W₁, V₂]` (induced subgraph), `X ← X[W₁ ∪ V₂]`"*. -/
noncomputable def step5Obj (X : Pt (BipBlockInputs Ω)) : VColBipBlk ↥(step5Set X) ℕ :=
  X.obj.1.1.restrictTo (step5Set_subset X)

/-- Every block survives the restriction of step 5: `V₂` is kept whole. -/
theorem step5_blocks_subset (X : Pt (BipBlockInputs Ω)) :
    ∀ B ∈ X.obj.1.1.blocks, ∀ x ∈ B, (x : Ω) ∈ step5Set X :=
  fun B hB x hx => ⟨x, Or.inr ⟨B, hB, hx⟩, rfl⟩

/-- §9.4, step 5.  *"`V₁ ← W₁`"*: the first part of the restricted instance is exactly the
dominant color class.  A point of `W₁ ∪ V₂` that lies in the old first part cannot lie in a
block (`blocks_off₁`), so it lies in `W₁`. -/
theorem step5Obj_part₁_iff (X : Pt (BipBlockInputs Ω)) (x : ↥(step5Set X)) :
    (step5Obj X).part₁ x ↔ VColBipBlk.incl (step5Set_subset X) x ∈ dominantClass X := by
  constructor
  · intro hx
    obtain ⟨w, hw, hwx⟩ := x.2
    have hwu : w = VColBipBlk.incl (step5Set_subset X) x := Subtype.ext hwx
    subst hwu
    rcases hw with hw | ⟨B, hB, hmem⟩
    · exact hw
    · exact absurd hx (X.obj.1.1.blocks_off₁ B hB _ hmem)
  · intro hx; exact hx.1

theorem step5Obj_V₁_image (X : Pt (BipBlockInputs Ω)) :
    VColBipBlk.incl (step5Set_subset X) '' (step5Obj X).V₁ = dominantClass X := by
  ext u
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (step5Obj_part₁_iff X x).1 hx
  · intro hu
    refine ⟨⟨(u : Ω), ⟨u, Or.inl hu, rfl⟩⟩, ?_, rfl⟩
    exact (step5Obj_part₁_iff X _).2 hu

/-- §9.4, step 5.  `n₁` becomes `|W₁|`. -/
theorem step5Obj_V₁_ncard (X : Pt (BipBlockInputs Ω)) :
    (step5Obj X).V₁.ncard = (dominantClass X).ncard := by
  rw [← step5Obj_V₁_image X,
    Set.ncard_image_of_injective _ (VColBipBlk.incl_injective (step5Set_subset X))]

/-- §9.4, step 5.  `n₂` does not change. -/
theorem step5Obj_numBlocks (X : Pt (BipBlockInputs Ω)) :
    (step5Obj X).numBlocks = X.obj.1.1.numBlocks :=
  VColBipBlk.restrictTo_numBlocks _ _ (step5_blocks_subset X)

/-- §9.4, step 5.  **The restricted instance is an admissible input of Theorem 9.2.2 for
the new threshold.**  *"`|V₁| ≥ 2`"* because `|W₁| > α n₁ ≥ 4/3`; *"`|V₂| < α|V₁|`"*
because `n₂` does not change and `α_new |W₁| = α n₁`; and the symmetry defect of `W₁` is at
least `1 - α_new` because a set of twins of `X[W₁ ∪ V₂]` inside `W₁` is a set of twins of
`X` inside `V₁` (`Babai.VColBipBlk.restrictTo_twin_imp`), so it has at most
`α n₁ = α_new |W₁|` points (`Babai.ncard_le_alphaNew_mul_dominantClass`).

Together with `Babai.claim_9_4_step5_at` (`2/3 ≤ α_new < 1`) this is everything the steps 6-9
inherit from the hypotheses of Theorem 9.2.2. -/
theorem step5Obj_isThm922Input {X : Pt (BipBlockInputs Ω)} (h : ¬ AllClassesSmall X)
    [Fintype ↥(step5Set X)] [DecidableEq ↥(step5Set X)] :
    (step5Obj X).IsThm922Input (alphaNew X) := by
  classical
  have hWpos : (0 : ℝ) < ((dominantClass X).ncard : ℝ) := dominantClass_ncard_pos h
  -- a set of twins of the restriction inside `W₁` has at most `α_new |W₁|` points
  have hsym : ((step5Obj X).symmetricity₁ : ℝ)
      ≤ alphaNew X * ((dominantClass X).ncard : ℝ) := by
    obtain ⟨T, hT, hTeq⟩ := Finset.exists_mem_eq_sup
      (Finset.univ.filter fun T : Finset ↥(step5Set X) =>
        (∀ x ∈ T, (step5Obj X).part₁ x) ∧ IsTwinSet (step5Obj X).Aut (↑T : Set ↥(step5Set X)))
      ⟨∅, by simp [IsTwinSet]⟩ Finset.card
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hT
    obtain ⟨hTpart, hTtwin⟩ := hT
    set ι := VColBipBlk.incl (step5Set_subset X) with hι
    have hS : ∀ u ∈ ι '' (↑T : Set ↥(step5Set X)), X.obj.1.1.part₁ u := by
      rintro u ⟨x, hx, rfl⟩
      exact hTpart x (by simpa using hx)
    have hTw : ∀ u ∈ ι '' (↑T : Set ↥(step5Set X)),
        ∀ v ∈ ι '' (↑T : Set ↥(step5Set X)),
        X.obj.1.1.f u = X.obj.1.1.f v ∧
          ∀ B ∈ X.obj.1.1.blocks, ((u, B) ∈ X.obj.1.1.E ↔ (v, B) ∈ X.obj.1.1.E) := by
      rintro u ⟨x, hx, rfl⟩ v ⟨y, hy, rfl⟩
      rcases eq_or_ne x y with rfl | hne
      · exact ⟨rfl, fun _ _ => Iff.rfl⟩
      have htw := hTtwin x hx y hy hne
      have hiff := ((step5Obj X).isTwin_iff (hTpart x (by simpa using hx))
        (hTpart y (by simpa using hy)) hne).1 htw
      exact VColBipBlk.restrictTo_twin_imp _ _ (step5_blocks_subset X) hiff.1 hiff.2
    have hcard : (ι '' (↑T : Set ↥(step5Set X))).ncard = T.card := by
      rw [Set.ncard_image_of_injective _ (VColBipBlk.incl_injective (step5Set_subset X)),
        Set.ncard_coe_finset]
    have hbound := ncard_le_alphaNew_mul_dominantClass h hS hTw
    rw [hcard] at hbound
    have : (step5Obj X).symmetricity₁ = T.card := hTeq
    rw [this]
    exact hbound
  refine ⟨?_, ?_, ?_⟩
  · rw [step5Obj_V₁_ncard]; exact two_le_dominantClass_ncard h
  · rw [step5Obj_numBlocks, step5Obj_V₁_ncard, alphaNew_mul_dominantClass h]
    exact X.obj.2.2.2.2.1
  · have hV : ((step5Obj X).V₁.ncard : ℝ) = ((dominantClass X).ncard : ℝ) := by
      rw [step5Obj_V₁_ncard]
    have hdef : ((step5Obj X).defect₁ : ℝ)
        = 1 - ((step5Obj X).symmetricity₁ : ℝ) / ((step5Obj X).V₁.ncard : ℝ) := by
      have : ((step5Obj X).defect₁ : ℚ)
          = 1 - ((step5Obj X).symmetricity₁ : ℚ) / ((step5Obj X).V₁.ncard : ℚ) := rfl
      rw [this]; push_cast; ring
    rw [hdef, hV]
    have hdiv : ((step5Obj X).symmetricity₁ : ℝ) / ((dominantClass X).ncard : ℝ)
        ≤ alphaNew X := by
      rw [div_le_iff₀ hWpos]; exact hsym
    linarith

/-- §9.4, step 5.  The new threshold is an isomorphism invariant, which is what makes the
restriction of step 5 a functor. -/
theorem alphaNew_congr {X Y : Pt (BipBlockInputs Ω)}
    (h : ((BipBlockInputs Ω).IsoP X Y).Nonempty) : alphaNew X = alphaNew Y := by
  obtain ⟨φ, hφ⟩ := h
  have hα : BipBlockInputs.alpha X = BipBlockInputs.alpha Y := hφ.1
  have hn₁ : BipBlockInputs.n₁ X = BipBlockInputs.n₁ Y := BipBlockInputs.n₁_congr ⟨φ, hφ⟩
  have hW : (dominantClass Y).ncard = (dominantClass X).ncard := by
    rw [dominantClass_image hφ, Set.ncard_image_of_injective _ φ.injective]
  rw [alphaNew, alphaNew, hα, hn₁, hW]

end Babai
