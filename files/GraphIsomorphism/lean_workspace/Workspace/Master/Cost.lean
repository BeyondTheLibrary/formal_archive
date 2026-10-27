/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Sections 11.4 and 15: the cost of Procedure String-Isomorphism.
-/
import Workspace.Master.Correctness

/-!
# The cost of the Master Algorithm

Sec. 11.4 bounds the cost of Procedure String-Isomorphism by recurrences, one for the
Chain Rule, one for the window size `n` and one for the Johnson parameter `m`:

> (i) `T(x) ≤ max {∑_i T_trans(n_i) + p(x)}`, the maximum over all partitions of `⌊x⌋`
> (ii') `T_trans(x) ≤ 1.1 x T_Jh(x)`
> (v) `T_Jh(x,y) ≤ q₁(x) (T(4x/5) + T_Jh(x, 0.9y))`
> `T(x) ≤ 2x q(x) T(4x/5) < q(x)² T(4x/5)`  (66)
> which resolves to `T(x) = q(x)^{O(log x)}`  (67)

and the multiplicative cost `q(m)` of Sec. 14.2 enters through Eqs. (71)–(74).  The
real-valued resolutions of those recurrences are in `Workspace/Luks/Cost.lean`
(`Babai.cost_resolution`, `Babai.costJh_resolution`).

What is counted here is the number of String Isomorphism instances the recursion generates
— the number of nodes of the recursion tree (`Babai.countCalls`).  The bounding function is

> `T(I) = n² · B^{johnsonRank I}`,  `B = q + 1`,

with `q` the multiplicative cost of a round.  The two factors pay for the two kinds of
round:

* a **shrinking** round (recurrences (ii), (v)) drops `johnsonRank` by at least one, so each
  of its at most `q` instances costs a factor `B` less than `T(I)`, and `q + q·T(I)/B ≤
  T(I)`;
* a **Chain Rule** round (recurrence (i)) keeps `johnsonRank` but splits the window into
  parts `n₁, …, n_k` with `∑ n_i ≤ n` and `n_i < n`.  The factor `n²` is *superadditive*
  along such a split, `∑ n_i² ≤ (n-1)·∑ n_i ≤ n² - n`, and the `n` left over pays for the
  `k ≤ q` instances themselves.  This is the discrete form of the paper's step from (i) to
  (i'), which is also justified by superadditivity of `T`.

The main results are

* `Babai.MasterStep.count_le` — the recursion tree has at most `n² (q+1)^{johnsonRank I}`
  nodes;
* `Babai.MasterStep.johnsonRank_le_rankBound` (`Workspace/Master/Procedure.lean`) —
  `johnsonRank I = O(log² n)`, explicitly `≤ 14 (log₂ n + 1)²`;
* `Babai.Theorem_1_1_1_math_of_masterStep` — putting the two together: Procedure
  String-Isomorphism returns `Iso_G(x,y)` and generates at most `exp(O((log n)^c))`
  instances, with `c = c₁ + 2` where `q(n) ≤ exp((log n)^{c₁})` is the multiplicative cost
  of one round.

The *running time* — the cost in group operations, and the RAM model of `Workspace/Machine/`
is not covered; see the Sec. 15 entry of the corrected paper.
-/

universe u v w

namespace Babai

variable {Ω : Type u} {A : Type v} {ι : Type w}

/-! ### Two list estimates -/

/-- Termwise comparison of a sum against a multiple of another sum. -/
theorem sum_map_le_mul {α : Type*} (L : List α) (f g : α → ℕ) (c : ℕ)
    (h : ∀ a ∈ L, f a ≤ c * g a) : (L.map f).sum ≤ c * (L.map g).sum := by
  induction L with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons, Nat.mul_add]
    exact Nat.add_le_add (h a (List.mem_cons_self ..))
      (ih fun b hb => h b (List.mem_cons_of_mem _ hb))

/-- **Superadditivity of the square**, the discrete form of the paper's step from
recurrence (i) to (i'): if the parts of a split are all at most `k` then the sum of their
squares is at most `k` times the size of the split. -/
theorem sum_sq_le_mul {α : Type*} (L : List α) (g : α → ℕ) (k : ℕ)
    (h : ∀ a ∈ L, g a ≤ k) : (L.map (fun a => g a * g a)).sum ≤ k * (L.map g).sum :=
  sum_map_le_mul L _ g k fun a ha => Nat.mul_le_mul_right _ (h a ha)

namespace MasterStep

variable (M : MasterStep Ω A ι)

/-! ### The window never grows -/

/-- Every instance produced by a round has window size at most that of the instance the
round was applied to (both forms of `decreases` say so). -/
theorem win_call_le (i : ι) (hi : IsGroupInstance (M.inst i)) (J : SIInstance Ω A)
    (hJ : J ∈ (M.step i).calls) : M.win (M.lift i J) ≤ M.win i := by
  rcases M.decreases' i hi with hsh | ⟨-, hcalls, -⟩
  · exact win_le_of_makesProgress (hsh J hJ)
  · exact le_of_lt (hcalls (M.lift i J) (List.mem_map_of_mem hJ)).1

/-! ### The size of the recursion tree -/

/-- The bounding function of the recursion: `T(I) = n² B^{johnsonRank I}`. -/
noncomputable def costBound (B : ℕ) (i : ι) : ℕ :=
  M.win i ^ 2 * B ^ M.johnsonRank i

/-- **The one-round recurrence**: the number of instances a round produces, plus what each
of them costs, is at most what the instance costs.

*Proof.*  Two cases, the two forms of `Babai.MasterStep.decreases`.

*Shrinking round.*  If there are no calls there is nothing to prove.  Otherwise the window
is nonempty, so `johnsonRank I ≥ 3` (`Babai.MasterStep.three_le_johnsonRank`), and every
call `J` has `n_J ≤ n` and `johnsonRank J < johnsonRank I`, so
`T(J) ≤ n² B^{johnsonRank I - 1} =: c`.  There are at most `q = B - 1` calls, so the left
side is at most `q + q c`, and `c ≥ B² ≥ B > q` gives `q + q c ≤ c + q c = B c = T(I)`.

*Chain Rule round.*  Every call has `johnsonRank J ≤ johnsonRank I`, so
`∑ T(J) ≤ B^{johnsonRank I} ∑ n_J²`.  The windows are strictly smaller than `n = k + 1` and
add up to at most `n`, so `∑ n_J² ≤ k · n`.  There are at most `q < B ≤ B^{johnsonRank I}`
calls, and `B^{johnsonRank I} (n + k n) = B^{johnsonRank I} n² = T(I)`. -/
theorem round_recurrence (n₀ : ℕ) (hmono : Monotone M.roundCost) (i : ι)
    (hgrp : IsGroupInstance (M.inst i)) (hI : M.win i ≤ n₀) :
    ((M.step i).calls).length +
        (((M.step i).calls).map
          (fun J => M.costBound (M.roundCost n₀ + 1) (M.lift i J))).sum
      ≤ M.costBound (M.roundCost n₀ + 1) i := by
  set q := M.roundCost n₀ with hq
  set B := q + 1 with hB
  set L := (M.step i).calls with hL
  have hlen : L.length ≤ q := le_trans (M.calls_length_le i hgrp) (hmono hI)
  have hB1 : 1 ≤ B := by omega
  rcases M.decreases' i hgrp with hsh | ⟨hpos, hcalls, hsum⟩
  · -- shrinking round
    by_cases hnil : L = []
    · rw [hnil]; simp [costBound]
    · -- the window is nonempty, so the Johnson measure is at least `3`
      obtain ⟨J₀, hmem⟩ : ∃ J₀, J₀ ∈ L := by
        cases hcase : L with
        | nil => exact absurd hcase hnil
        | cons a t => exact ⟨a, hcase ▸ (List.mem_cons_self : a ∈ a :: t)⟩
      have hprog := hsh J₀ hmem
      have hn1 : 1 ≤ M.win i := by
        rcases hprog with ⟨h, -⟩ | ⟨-, h, -⟩
        · exact h
        · have := M.param_le i
          show 1 ≤ M.win i
          rw [win]
          omega
      have hjr3 : 3 ≤ M.johnsonRank i := M.three_le_johnsonRank i hn1
      set d := M.johnsonRank i with hd
      set c := M.win i ^ 2 * B ^ (d - 1) with hc
      -- every call costs at most `c`
      have hterm : ∀ J ∈ L, M.costBound B (M.lift i J) ≤ c := by
        intro J hJ
        have hp := hsh J hJ
        have h1 : M.win (M.lift i J) ≤ M.win i := win_le_of_makesProgress hp
        have h2 : M.johnsonRank (M.lift i J) ≤ d - 1 := by
          have := M.johnsonRank_lt i _ hp; omega
        exact Nat.mul_le_mul (Nat.pow_le_pow_left h1 2) (Nat.pow_le_pow_right hB1 h2)
      have hsumle : (L.map (fun J => M.costBound B (M.lift i J))).sum ≤ L.length * c := by
        have := List.sum_le_card_nsmul (L.map (fun J => M.costBound B (M.lift i J))) c
          (by intro v hv; obtain ⟨J, hJ, rfl⟩ := List.mem_map.1 hv; exact hterm J hJ)
        simpa [List.length_map, smul_eq_mul] using this
      -- `c` is at least `B`, because `n ≥ 1` and `d - 1 ≥ 2`
      have hcB : B ≤ c := by
        have h1 : (1:ℕ) ≤ M.win i ^ 2 := Nat.one_le_pow _ _ hn1
        have h2 : B ^ 1 ≤ B ^ (d - 1) := Nat.pow_le_pow_right hB1 (by omega)
        have : B ≤ B ^ (d - 1) := by simpa using h2
        calc B ≤ B ^ (d - 1) := this
          _ = 1 * B ^ (d - 1) := (one_mul _).symm
          _ ≤ M.win i ^ 2 * B ^ (d - 1) := Nat.mul_le_mul_right _ h1
      have hsplit : B ^ d = B * B ^ (d - 1) := by
        rw [← pow_succ']
        congr 1
        omega
      have hpow : M.costBound B i = q * c + c := by
        show M.win i ^ 2 * B ^ d = q * c + c
        rw [hsplit, hc, hB]
        ring
      have hmul : L.length * c ≤ q * c := Nat.mul_le_mul_right _ hlen
      have hlenc : L.length ≤ c := by omega
      have hsum2 : (L.map (fun J => M.costBound B (M.lift i J))).sum ≤ q * c :=
        le_trans hsumle hmul
      omega
  · -- Chain Rule round
    obtain ⟨k, hk⟩ : ∃ k, M.win i = k + 1 := ⟨M.win i - 1, by omega⟩
    set d := M.johnsonRank i with hd
    have hcalls' : ∀ J ∈ L, M.win (M.lift i J) < M.win i ∧
        M.param (M.lift i J) ≤ M.param i :=
      fun J hJ => hcalls (M.lift i J) (List.mem_map_of_mem hJ)
    -- every call costs at most `B^d` times the square of its window
    have hterm : ∀ J ∈ L, M.costBound B (M.lift i J)
        ≤ B ^ d * (M.win (M.lift i J) * M.win (M.lift i J)) := by
      intro J hJ
      obtain ⟨h1, h2⟩ := hcalls' J hJ
      have hjr : M.johnsonRank (M.lift i J) ≤ d := M.johnsonRank_le i _ (le_of_lt h1) h2
      calc M.costBound B (M.lift i J) = M.win (M.lift i J) ^ 2 * B ^ M.johnsonRank (M.lift i J) := rfl
        _ ≤ M.win (M.lift i J) ^ 2 * B ^ d :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hB1 hjr)
        _ = B ^ d * (M.win (M.lift i J) * M.win (M.lift i J)) := by ring
    have hsum1 : (L.map (fun J => M.costBound B (M.lift i J))).sum
        ≤ B ^ d * (L.map (fun J => M.win (M.lift i J) * M.win (M.lift i J))).sum :=
      sum_map_le_mul L _ _ _ hterm
    have hsq : (L.map (fun J => M.win (M.lift i J) * M.win (M.lift i J))).sum
        ≤ k * (L.map (fun J => M.win (M.lift i J))).sum :=
      sum_sq_le_mul L (fun J => M.win (M.lift i J)) k
        (fun J hJ => by
          have := (hcalls' J hJ).1
          show M.win (M.lift i J) ≤ k
          omega)
    have hsummap : (L.map (fun J => M.win (M.lift i J))).sum
        = ((L.map (M.lift i)).map M.win).sum := by
      rw [List.map_map]; rfl
    have hsq2 : (L.map (fun J => M.win (M.lift i J) * M.win (M.lift i J))).sum
        ≤ k * (k + 1) := by
      refine le_trans hsq (Nat.mul_le_mul_left _ ?_)
      rw [hsummap, ← hk]
      exact hsum
    -- the calls themselves are paid for by the leftover `n`
    have hcount : L.length ≤ B ^ d * (k + 1) := by
      have h1 : B ≤ B ^ d := by
        have : B ^ 1 ≤ B ^ d := Nat.pow_le_pow_right hB1 (by
          have := M.three_le_johnsonRank i hpos; omega)
        simpa using this
      have h2 : B ^ d ≤ B ^ d * (k + 1) := Nat.le_mul_of_pos_right _ (by omega)
      omega
    have htot : M.costBound B i = B ^ d * (k + 1) + B ^ d * (k * (k + 1)) := by
      rw [costBound, ← hd, hk]; ring
    have := Nat.mul_le_mul_left (B ^ d) hsq2
    omega

/-- **The recursion tree has at most `n² (q+1)^{johnsonRank I}` nodes**, where `q` bounds
the number of instances one round produces.  This is the discrete form of the resolution of
Eqs. (i)–(66). -/
theorem count_le (n₀ : ℕ) (hmono : Monotone M.roundCost) (f : ℕ) (i : ι)
    (hgrp : IsGroupInstance (M.inst i)) (hI : M.win i ≤ n₀) (hf : M.rank i < f) :
    M.count f i ≤ M.costBound (M.roundCost n₀ + 1) i :=
  countCalls_le M.step M.lift M.inst M.lift_inst
    (fun j => M.win j ≤ n₀ ∧ IsGroupInstance (M.inst j)) M.rank
    (M.costBound (M.roundCost n₀ + 1))
    (fun f' j hj hr => M.solve_eq_answer f' j hj.2 hr)
    (fun i' hi' => M.rank_lt i' hi'.2)
    (fun i' hi' J hJ => ⟨le_trans (M.win_call_le i' hi'.2 J hJ) hi'.1, by
      rw [M.lift_inst i' J hJ]; exact M.calls_isGroupInstance i' hi'.2 J hJ⟩)
    (fun i' hi' => M.round_recurrence n₀ hmono i' hi'.2 hi'.1) f i ⟨hI, hgrp⟩ hf

end MasterStep

/-! ### Theorem 1.1.1, the mathematical half -/

/-- **Theorem 1.1.1** (Sec. 1.1, proved by the Master Algorithm of Sec. 15), the
mathematical half:

> The String Isomorphism problem for a group `G ≤ S(Ω)`, `|Ω| = n`, can be solved in
> `exp(O((log n)^c))` time for some constant `c`.

Given one round of Procedure String-Isomorphism (`Babai.MasterStep`) whose multiplicative
cost `q(n)` is quasipolynomial, `q(n) ≤ exp((log n)^{c₁})`, the procedure

* returns `Iso_G(x,y)` (Sec. 15, the output line), and
* generates at most `exp(30 (log₂ n + 2)^{c₁ + 2})` String Isomorphism instances,

so the exponent is `c = c₁ + 2`: two extra powers of `log n` for the depth of the recursion,
exactly as in `T(x) = q(x)^{O(log x)}` (Eq. (67)) composed with the Johnson recursion of
item (v) of Sec. 11.4.

What is bounded is the number of instances, i.e. the number of nodes of the recursion tree,
not the number of group operations; see the Sec. 15 entry of the corrected paper.
**This is conditional on a `MasterStep`.** It is the recursion analysis of Sec. 15 given one
round with the properties listed in `MasterStep`. Theorem 1.1.1 at the mathematical level
follows only once `masterStep_of_procedure` builds such a round from the procedures of
Secs. 11–14 (not done yet). The name `Theorem_1_1_1_math` is kept free for that
unconditional statement.

The hypothesis is `q(n) ≤ 2^{(log₂ n + 2)^{c₁}}`, which is `RAM.QuasiPolyBound q` written
out.  An earlier form of this theorem wrote `log₂ n + 1` there.  That form is empty: at
`n = 1` its right side is `2^{1^{c₁}} = 2` for every `c₁`, while the cost of one round of
Sec. 15 is at least `8`, so no round of ours could satisfy it.  See the the corrected paper
entry on the round-cost hypothesis of Theorem 1.1.1. -/
theorem Theorem_1_1_1_math_of_masterStep (M : MasterStep Ω A ι) (hmono : Monotone M.roundCost)
    (c₁ : ℕ) (hq : ∀ n : ℕ, M.roundCost n ≤ 2 ^ ((Nat.log 2 n + 2) ^ c₁))
    (G : Subgroup (Equiv.Perm Ω)) (x y : Ω → A) :
    let I : SIInstance Ω A := ⟨(G : Set (Equiv.Perm Ω)), Set.univ, x, y⟩
    let i := M.top I
    let f := M.rank i + 1
    M.solve f i = strIso (G : Set (Equiv.Perm Ω)) x y ∧
      M.count f i ≤ 2 ^ (30 * (Nat.log 2 I.windowSize + 2) ^ (c₁ + 2)) := by
  intro I i f
  refine ⟨M.solve_eq_strIso G x y f (Nat.lt_succ_self _), ?_⟩
  have hwin : M.win i = I.windowSize := by rw [MasterStep.win, M.inst_top]
  set n := I.windowSize with hn
  set L := Nat.log 2 n + 2 with hLdef
  have hL1 : 1 ≤ L := by omega
  have hcount : M.count f i ≤ n ^ 2 * (M.roundCost n + 1) ^ M.johnsonRank i := by
    have := M.count_le n hmono f i (by rw [M.inst_top]; exact isGroupInstance_full G x y)
      (le_of_eq hwin) (Nat.lt_succ_self _)
    rwa [MasterStep.costBound, hwin] at this
  -- `q + 1 ≤ 2^{L^{c₁} + 1}`
  have hQ : M.roundCost n + 1 ≤ 2 ^ (L ^ c₁ + 1) := by
    have h := hq n
    have h2 : (2 : ℕ) ^ (L ^ c₁) + 1 ≤ 2 ^ (L ^ c₁ + 1) := by
      have h1 : 1 ≤ (2 : ℕ) ^ (L ^ c₁) := Nat.one_le_two_pow
      rw [pow_succ]
      omega
    rw [← hLdef] at h
    omega
  -- `johnsonRank ≤ 14 L²`
  have hrank : M.johnsonRank i ≤ 14 * L ^ 2 := by
    have h := M.johnsonRank_le_rankBound i
    rw [MasterStep.rankBound, hwin] at h
    refine le_trans h (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ?_ 2))
    omega
  -- `n² ≤ 2^{2L}`
  have hn2 : n ^ 2 ≤ 2 ^ (2 * L) := by
    have hlt : n < 2 ^ L :=
      lt_of_lt_of_le (Nat.lt_pow_succ_log_self (by norm_num) n)
        (Nat.pow_le_pow_right (by norm_num) (by omega))
    calc n ^ 2 ≤ (2 ^ L) ^ 2 := Nat.pow_le_pow_left (le_of_lt hlt) 2
      _ = 2 ^ (2 * L) := by rw [← pow_mul, mul_comm]
  calc M.count f i ≤ n ^ 2 * (M.roundCost n + 1) ^ M.johnsonRank i := hcount
    _ ≤ 2 ^ (2 * L) * (2 ^ (L ^ c₁ + 1)) ^ (14 * L ^ 2) := by
        exact Nat.mul_le_mul hn2 ((Nat.pow_le_pow_left hQ _).trans
          (Nat.pow_le_pow_right Nat.one_le_two_pow hrank))
    _ = 2 ^ (2 * L + (L ^ c₁ + 1) * (14 * L ^ 2)) := by rw [← pow_mul, ← pow_add]
    _ ≤ 2 ^ (30 * L ^ (c₁ + 2)) := by
        refine Nat.pow_le_pow_right (by norm_num) ?_
        have hle : L ^ 2 ≤ L ^ (c₁ + 2) := Nat.pow_le_pow_right hL1 (by omega)
        have hle1 : L ≤ L ^ 2 := by nlinarith
        have hexp : (L ^ c₁ + 1) * (14 * L ^ 2) = 14 * (L ^ c₁ * L ^ 2) + 14 * L ^ 2 := by
          ring
        rw [hexp, ← pow_add]
        omega

end Babai
