/-
An explicit running time for Theorem 1.1.1 (Babai, version 2.5), part 2: the refined node
count of the recursion tree (Eqs. (6) and (74), with the window factor kept apart).
Not part of the faithful formalization.
-/
import Workspace.Algo.MasterRecurrences

/-!
# The refined Eq. (74)

`Algo.Round.nodes_le_costBoundG` bounds the recursion tree by `n²·(q+1)^{johnsonRank}` with one
bound `q` on the calls of every node. At line 2 of the Master (`m ≤ ℓ = (log n)^3`) the calls
number up to `ℓ!·n`, which is `2^{Θ(log³ n · log log n)}`; with one bound for all nodes this
gives `2^{O(log^5 n · log log n)}`, so exponent 6 in the form `2^{C(log n+2)^c}`.

The paper's Eq. (6) (§1.1.3, `quasi25.txt` l. 1203) keeps the two costs apart:
`f(n) ≤ q₁(n)^{O(log² n)} (ℓ(n)!)^{O(log n)}`. The rounds with the large cost `ℓ!` shrink the
window by a constant factor, so there are `O(log n)` of them on every path. This file proves
that bound on the raw recursion tree:

* `Explicit.nodes_le_split`: if the *wide* nodes (a predicate `W`) have at most `Qw` calls,
  each shrinking the window to at most `4/5`, and every other node has at most `Qp` calls and
  the progress of `Algo.RoundProgress`, then
  `nodes ≤ win²·(2(Qw+1))^{windowRank win}·(Qp+1)^{johnsonRank}`;
* `Explicit.nodes_le_exp5`: with `Qw ≤ 2^{Aw (log₂ n+2)^4}` and `Qp ≤ 2^{Ap (log₂ n+2)^3}`,
  `nodes ≤ 2^{(4Aw + 14Ap + 24)(log₂ n+2)^5}`.

The call bounds are asked of the calls of the run at a good node (`R.roundCalls f I` with
`R.measure I < f + 1`; interface change R3: the width `R.width` is only fuel and may be far
larger), at the degree `n₀` of the root (the degree does not
grow along the tree, `Algo.Round.ground_mem_loopCalls`).
-/

universe u v

namespace Explicit

open Algo Babai RAM

variable {ι ω α : Type*} {Ω : Type u} {A : Type v}

namespace Round'

variable (R : Algo.Round ι ω α)

theorem length_loopCalls_le (rec : ι → α) :
    ∀ (w : ℕ) (I : ι) (j : ℕ) (s : ω), (R.loopCalls rec w I j s).length ≤ w := by
  intro w
  induction w with
  | zero => intro I j s; simp
  | succ w ih =>
    intro I j s
    rw [Algo.Round.loopCalls]
    cases R.child (I, j, s) with
    | none => simp
    | some J =>
      simp only [List.length_cons]
      have := ih I (j + 1) (R.combine (I, j, s, rec J))
      omega

end Round'

/-- The calls of a node are at most its width. -/
theorem length_roundCalls_le_width (R : Algo.Round ι ω α) (f : ℕ) (I : ι) :
    (R.roundCalls f I).length ≤ R.width I :=
  Round'.length_loopCalls_le R _ _ _ _ _

/-- The ground of every call is at most the ground of the node. -/
theorem ground_roundCalls_le (R : Algo.Round ι ω α) {f : ℕ} {I : ι} (hI : R.WF I) :
    ∀ J ∈ R.roundCalls f I, R.ground J ≤ R.ground I :=
  R.ground_mem_loopCalls _ hI _ _ _

section Split

variable (R : Algo.Round ι ω α) {Good : ι → Prop} {Ch : ι → ι → Prop}
    {decI : ι → SIInstance Ω A} {decA : ι → α → Set (Equiv.Perm Ω)}
    {ρ : ι → SIReduction Ω A (Set (Equiv.Perm Ω))} {win param : ι → ℕ} {q : ℕ → ℕ}

/-- **The refined count of the recursion tree** (Eq. (6) of §1.1.3 on the raw tree).

* `W`: the wide nodes. At a wide node every call of the run shrinks the window to at most
  `4/5` (`hW`), and the node has at most `Qw n₀` calls.
* At every other node there are at most `Qp n₀` calls, and the round makes the progress of
  `Algo.RoundProgress` (its `decreases` field; the call bound `q` of `hP` is not used).

The potential is `win²·(2(Qw n₀+1))^{windowRank win}·(Qp n₀+1)^{johnsonRankOf win param}`. -/
theorem nodes_le_split (himpl : ImplementsG R Good Ch decI decA ρ)
    (hρ : ∀ I : ι, Good I → R.WF I → (ρ I).run = (decI I).answer)
    (hP : RoundProgress R Good Ch decI ρ win param q)
    (W : ι → Prop) (Qw Qp : ℕ → ℕ) (n₀ : ℕ)
    (hW : ∀ I, Good I → R.WF I → W I → ∀ f, R.measure I < f + 1 →
      ∀ J ∈ R.roundCalls f I, 1 ≤ win I ∧ 5 * win J ≤ 4 * win I)
    (hwide : ∀ I, Good I → R.WF I → R.ground I ≤ n₀ → W I → ∀ f, R.measure I < f + 1 →
      (R.roundCalls f I).length ≤ Qw n₀)
    (hnarrow : ∀ I, Good I → R.WF I → R.ground I ≤ n₀ → ¬ W I → ∀ f, R.measure I < f + 1 →
      (R.roundCalls f I).length ≤ Qp n₀) :
    ∀ (f : ℕ) (I : ι), Good I → R.WF I → R.measure I < f → R.ground I ≤ n₀ →
      R.nodes f I ≤ win I ^ 2 * (2 * (Qw n₀ + 1)) ^ windowRank (win I) *
        (Qp n₀ + 1) ^ johnsonRankOf (win I) (param I) := by
  intro f
  induction f with
  | zero => intro I _ _ h; exact absurd h (Nat.not_lt_zero _)
  | succ f ih =>
    intro I hG hI hf hn
    rw [R.nodes_succ]
    set Bw := 2 * (Qw n₀ + 1) with hBw
    set Bp := Qp n₀ + 1 with hBp
    have hBw1 : 1 ≤ Bw := by omega
    have hBp1 : 1 ≤ Bp := by omega
    obtain ⟨hmap, hch⟩ := roundCalls_eqG R himpl hP.good_child hρ f I hG hI hf
    set L := R.roundCalls f I with hL
    have hgoodL : ∀ J ∈ L, Good J ∧ R.WF J ∧ R.measure J < f ∧ R.ground J ≤ n₀ := by
      intro J hJ
      obtain ⟨hw, hm⟩ := R.mem_roundCalls hI J hJ
      exact ⟨hP.good_child I J (hch J hJ), hw, by omega,
        (ground_roundCalls_le R hI J hJ).trans hn⟩
    have hpI := hP.param_le I hG hI
    set wr := windowRank (win I) with hwr
    set d := johnsonRankOf (win I) (param I) with hd
    by_cases hWI : W I
    · -- a wide round: every call shrinks the window
      have hlen : L.length ≤ Qw n₀ := hwide I hG hI hn hWI f hf
      by_cases hnil : L = []
      · rw [hnil]; simp
      obtain ⟨J₀, hmem⟩ : ∃ J₀, J₀ ∈ L := by
        cases hcase : L with
        | nil => exact absurd hcase hnil
        | cons a t => exact ⟨a, List.mem_cons_self⟩
      have hn1 : 1 ≤ win I := (hW I hG hI hWI f hf J₀ hmem).1
      have hwr1 : 1 ≤ wr := one_le_windowRank _ hn1
      set c := win I ^ 2 * Bw ^ (wr - 1) * Bp ^ d with hc
      have hc1 : 1 ≤ c := by
        have h1 : 1 ≤ win I ^ 2 := Nat.one_le_pow _ _ hn1
        have h2 : 1 ≤ Bw ^ (wr - 1) := Nat.one_le_pow _ _ hBw1
        have h3 : 1 ≤ Bp ^ d := Nat.one_le_pow _ _ hBp1
        calc 1 = 1 * 1 * 1 := by norm_num
          _ ≤ c := Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3
      have hterm : ∀ J ∈ L, R.nodes f J ≤ c := by
        intro J hJ
        obtain ⟨hGJ, hWJ, hmJ, hnJ⟩ := hgoodL J hJ
        obtain ⟨h1', h5⟩ := hW I hG hI hWI f hf J hJ
        have h1 : win J ≤ win I := by omega
        have hr : windowRank (win J) ≤ wr - 1 := by
          have := windowRank_lt (win I) (win J) h1' h5; omega
        have hj : johnsonRankOf (win J) (param J) ≤ d :=
          le_of_lt (johnsonRankOf_lt (hP.param_le J hGJ hWJ) (Or.inl ⟨h1', h5⟩))
        calc R.nodes f J ≤ win J ^ 2 * Bw ^ windowRank (win J) *
              Bp ^ johnsonRankOf (win J) (param J) := ih J hGJ hWJ hmJ hnJ
          _ ≤ c := Nat.mul_le_mul (Nat.mul_le_mul (Nat.pow_le_pow_left h1 2)
              (Nat.pow_le_pow_right hBw1 hr)) (Nat.pow_le_pow_right hBp1 hj)
      have hsumle : (L.map (R.nodes f)).sum ≤ L.length * c := by
        have := List.sum_le_card_nsmul (L.map (R.nodes f)) c
          (by intro v hv; obtain ⟨J, hJ, rfl⟩ := List.mem_map.1 hv; exact hterm J hJ)
        simpa [List.length_map, smul_eq_mul] using this
      have hsplit : Bw ^ wr = Bw * Bw ^ (wr - 1) := by
        rw [← pow_succ']; congr 1; omega
      have hpow : win I ^ 2 * Bw ^ wr * Bp ^ d = Bw * c := by
        rw [hsplit, hc]; ring
      have hmul : L.length * c ≤ Qw n₀ * c := Nat.mul_le_mul_right _ hlen
      have hq : Qw n₀ ≤ Qw n₀ * c := Nat.le_mul_of_pos_right _ (by omega)
      rw [hpow, hBw]
      nlinarith
    · have hlen : L.length ≤ Qp n₀ := hnarrow I hG hI hn hWI f hf
      rcases hP.decreases I hG hI with hsh | ⟨hpos, hcalls, hsum⟩
      · -- a shrinking round
        by_cases hnil : L = []
        · rw [hnil]; simp
        obtain ⟨J₀, hmem⟩ : ∃ J₀, J₀ ∈ L := by
          cases hcase : L with
          | nil => exact absurd hcase hnil
          | cons a t => exact ⟨a, List.mem_cons_self⟩
        have hn1 : 1 ≤ win I := by
          rcases hsh J₀ (hch J₀ hmem) with ⟨h, -⟩ | ⟨-, h, -⟩
          · exact h
          · omega
        have hjr3 : 3 ≤ d := three_le_johnsonRankOf _ hn1
        set c := win I ^ 2 * Bw ^ wr * Bp ^ (d - 1) with hc
        have hterm : ∀ J ∈ L, R.nodes f J ≤ c := by
          intro J hJ
          obtain ⟨hGJ, hWJ, hmJ, hnJ⟩ := hgoodL J hJ
          have hp := hsh J (hch J hJ)
          have h1 : win J ≤ win I := win_le_of_makesProgress hp
          have h2 : johnsonRankOf (win J) (param J) ≤ d - 1 := by
            have := johnsonRankOf_lt (hP.param_le J hGJ hWJ) hp; omega
          calc R.nodes f J ≤ win J ^ 2 * Bw ^ windowRank (win J) *
                Bp ^ johnsonRankOf (win J) (param J) := ih J hGJ hWJ hmJ hnJ
            _ ≤ c := Nat.mul_le_mul (Nat.mul_le_mul (Nat.pow_le_pow_left h1 2)
                (Nat.pow_le_pow_right hBw1 (windowRank_le _ _ h1)))
                (Nat.pow_le_pow_right hBp1 h2)
        have hsumle : (L.map (R.nodes f)).sum ≤ L.length * c := by
          have := List.sum_le_card_nsmul (L.map (R.nodes f)) c
            (by intro v hv; obtain ⟨J, hJ, rfl⟩ := List.mem_map.1 hv; exact hterm J hJ)
          simpa [List.length_map, smul_eq_mul] using this
        have hcB : Bp ≤ c := by
          have h1 : (1:ℕ) ≤ win I ^ 2 := Nat.one_le_pow _ _ hn1
          have h1' : (1:ℕ) ≤ Bw ^ wr := Nat.one_le_pow _ _ hBw1
          have h2 : Bp ^ 1 ≤ Bp ^ (d - 1) := Nat.pow_le_pow_right hBp1 (by omega)
          calc Bp ≤ Bp ^ (d - 1) := by simpa using h2
            _ = 1 * 1 * Bp ^ (d - 1) := by ring
            _ ≤ win I ^ 2 * Bw ^ wr * Bp ^ (d - 1) :=
                Nat.mul_le_mul_right _ (Nat.mul_le_mul h1 h1')
        have hsplit : Bp ^ d = Bp * Bp ^ (d - 1) := by
          rw [← pow_succ']; congr 1; omega
        have hpow : win I ^ 2 * Bw ^ wr * Bp ^ d = Qp n₀ * c + c := by
          rw [hsplit, hc, hBp]; ring
        have hmul : L.length * c ≤ Qp n₀ * c := Nat.mul_le_mul_right _ hlen
        rw [hpow]
        omega
      · -- a Chain Rule round
        obtain ⟨k, hk⟩ : ∃ k, win I = k + 1 := ⟨win I - 1, by omega⟩
        set M := Bw ^ wr * Bp ^ d with hM
        have hterm : ∀ J ∈ L, R.nodes f J ≤ M * (win J * win J) := by
          intro J hJ
          obtain ⟨hGJ, hWJ, hmJ, hnJ⟩ := hgoodL J hJ
          obtain ⟨h1, h2⟩ := hcalls J (hch J hJ)
          have hjr : johnsonRankOf (win J) (param J) ≤ d := johnsonRankOf_le (le_of_lt h1) h2
          calc R.nodes f J ≤ win J ^ 2 * Bw ^ windowRank (win J) *
                Bp ^ johnsonRankOf (win J) (param J) := ih J hGJ hWJ hmJ hnJ
            _ ≤ win J ^ 2 * Bw ^ wr * Bp ^ d := Nat.mul_le_mul (Nat.mul_le_mul_left _
                (Nat.pow_le_pow_right hBw1 (windowRank_le _ _ (le_of_lt h1))))
                (Nat.pow_le_pow_right hBp1 hjr)
            _ = M * (win J * win J) := by rw [hM]; ring
        have hsum1 : (L.map (R.nodes f)).sum ≤ M * (L.map (fun J => win J * win J)).sum :=
          sum_map_le_mul L _ _ _ hterm
        have hsq : (L.map (fun J => win J * win J)).sum ≤ k * (L.map win).sum :=
          sum_sq_le_mul L win k (fun J hJ => by have := (hcalls J (hch J hJ)).1; omega)
        have hwinsum : (L.map win).sum = ((ρ I).calls.map SIInstance.windowSize).sum := by
          rw [← hmap, List.map_map]
          congr 1
          refine List.map_congr_left fun J hJ => ?_
          exact hP.win_eq J (hgoodL J hJ).1
        have hsq2 : (L.map (fun J => win J * win J)).sum ≤ k * (k + 1) := by
          refine le_trans hsq (Nat.mul_le_mul_left _ ?_)
          rw [hwinsum, ← hk]
          exact hsum
        have hcount : L.length ≤ M * (k + 1) := by
          have h1 : Bp ≤ Bp ^ d := by
            have : Bp ^ 1 ≤ Bp ^ d := Nat.pow_le_pow_right hBp1 (by
              have := three_le_johnsonRankOf (param I) hpos; omega)
            simpa using this
          have h1' : 1 ≤ Bw ^ wr := Nat.one_le_pow _ _ hBw1
          have h3 : Bp ^ d ≤ M := by
            rw [hM]; exact Nat.le_mul_of_pos_left _ (by omega)
          have h2 : M ≤ M * (k + 1) := Nat.le_mul_of_pos_right _ (by omega)
          omega
        have htot : win I ^ 2 * Bw ^ wr * Bp ^ d = M * (k + 1) + M * (k * (k + 1)) := by
          rw [hk, hM]; ring
        have := Nat.mul_le_mul_left M hsq2
        rw [htot]
        omega

/-- **The refined Eq. (74), exponent 5.** With `Qw n₀ ≤ 2^{Aw (log₂ n₀+2)^4}` (the wide rounds
of line 2) and `Qp n₀ ≤ 2^{Ap (log₂ n₀+2)^3}` (every other round), the recursion tree below a
node of degree at most `n₀` has at most `2^{(4Aw + 14Ap + 24)(log₂ n₀+2)^5}` nodes. -/
theorem nodes_le_exp5 (himpl : ImplementsG R Good Ch decI decA ρ)
    (hρ : ∀ I : ι, Good I → R.WF I → (ρ I).run = (decI I).answer)
    (hP : RoundProgress R Good Ch decI ρ win param q)
    (W : ι → Prop) (Qw Qp : ℕ → ℕ) (n₀ Aw Ap : ℕ)
    (hW : ∀ I, Good I → R.WF I → W I → ∀ f, R.measure I < f + 1 →
      ∀ J ∈ R.roundCalls f I, 1 ≤ win I ∧ 5 * win J ≤ 4 * win I)
    (hwide : ∀ I, Good I → R.WF I → R.ground I ≤ n₀ → W I → ∀ f, R.measure I < f + 1 →
      (R.roundCalls f I).length ≤ Qw n₀)
    (hnarrow : ∀ I, Good I → R.WF I → R.ground I ≤ n₀ → ¬ W I → ∀ f, R.measure I < f + 1 →
      (R.roundCalls f I).length ≤ Qp n₀)
    (hQw : Qw n₀ ≤ 2 ^ (Aw * (Nat.log 2 n₀ + 2) ^ 4))
    (hQp : Qp n₀ ≤ 2 ^ (Ap * (Nat.log 2 n₀ + 2) ^ 3))
    (hwin : ∀ I, Good I → R.WF I → win I ≤ R.ground I)
    (f : ℕ) (I : ι) (hG : Good I) (hI : R.WF I) (hf : R.measure I < f)
    (hn : R.ground I ≤ n₀) :
    R.nodes f I ≤ 2 ^ ((4 * Aw + 14 * Ap + 24) * (Nat.log 2 n₀ + 2) ^ 5) := by
  have h := nodes_le_split R himpl hρ hP W Qw Qp n₀ hW hwide hnarrow f I hG hI hf hn
  set L := Nat.log 2 n₀ + 2 with hLdef
  have hL2 : 2 ≤ L := by omega
  have hwI : win I ≤ n₀ := (hwin I hG hI).trans hn
  have hlogw : Nat.log 2 (win I) + 2 ≤ L := by
    have := Nat.log_mono_right (b := 2) hwI; omega
  -- the three factors
  have hn2 : win I ^ 2 ≤ 2 ^ (2 * L) := by
    have hlt : win I < 2 ^ L :=
      lt_of_lt_of_le (Nat.lt_pow_succ_log_self (by norm_num) (win I))
        (Nat.pow_le_pow_right (by norm_num) (by omega))
    calc win I ^ 2 ≤ (2 ^ L) ^ 2 := Nat.pow_le_pow_left (le_of_lt hlt) 2
      _ = 2 ^ (2 * L) := by rw [← pow_mul, mul_comm]
  have hBw : 2 * (Qw n₀ + 1) ≤ 2 ^ (Aw * L ^ 4 + 2) := by
    have h1 : (1 : ℕ) ≤ 2 ^ (Aw * L ^ 4) := Nat.one_le_two_pow
    have : (2 : ℕ) ^ (Aw * L ^ 4 + 2) = 4 * 2 ^ (Aw * L ^ 4) := by rw [pow_add]; ring
    rw [this]; omega
  have hBp : Qp n₀ + 1 ≤ 2 ^ (Ap * L ^ 3 + 1) := by
    have h1 : (1 : ℕ) ≤ 2 ^ (Ap * L ^ 3) := Nat.one_le_two_pow
    have : (2 : ℕ) ^ (Ap * L ^ 3 + 1) = 2 * 2 ^ (Ap * L ^ 3) := by rw [pow_add]; ring
    rw [this]; omega
  have hwr : windowRank (win I) ≤ 4 * L := by
    have := windowRank_le_log (win I); omega
  have hjr : johnsonRankOf (win I) (param I) ≤ 14 * L ^ 2 := by
    have h1 := johnsonRankOf_le_rankBound (hP.param_le I hG hI)
    rw [MasterStep.rankBound] at h1
    refine le_trans h1 (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ?_ 2))
    omega
  have hA : (2 * (Qw n₀ + 1)) ^ windowRank (win I) ≤ 2 ^ ((Aw * L ^ 4 + 2) * (4 * L)) := by
    calc (2 * (Qw n₀ + 1)) ^ windowRank (win I)
        ≤ (2 ^ (Aw * L ^ 4 + 2)) ^ windowRank (win I) := Nat.pow_le_pow_left hBw _
      _ ≤ (2 ^ (Aw * L ^ 4 + 2)) ^ (4 * L) := Nat.pow_le_pow_right Nat.one_le_two_pow hwr
      _ = 2 ^ ((Aw * L ^ 4 + 2) * (4 * L)) := by rw [← pow_mul]
  have hB : (Qp n₀ + 1) ^ johnsonRankOf (win I) (param I) ≤ 2 ^ ((Ap * L ^ 3 + 1) * (14 * L ^ 2)) := by
    calc (Qp n₀ + 1) ^ johnsonRankOf (win I) (param I)
        ≤ (2 ^ (Ap * L ^ 3 + 1)) ^ johnsonRankOf (win I) (param I) := Nat.pow_le_pow_left hBp _
      _ ≤ (2 ^ (Ap * L ^ 3 + 1)) ^ (14 * L ^ 2) := Nat.pow_le_pow_right Nat.one_le_two_pow hjr
      _ = 2 ^ ((Ap * L ^ 3 + 1) * (14 * L ^ 2)) := by rw [← pow_mul]
  refine h.trans ?_
  calc win I ^ 2 * (2 * (Qw n₀ + 1)) ^ windowRank (win I) *
        (Qp n₀ + 1) ^ johnsonRankOf (win I) (param I)
      ≤ 2 ^ (2 * L) * 2 ^ ((Aw * L ^ 4 + 2) * (4 * L)) *
          2 ^ ((Ap * L ^ 3 + 1) * (14 * L ^ 2)) := Nat.mul_le_mul (Nat.mul_le_mul hn2 hA) hB
    _ = 2 ^ (2 * L + (Aw * L ^ 4 + 2) * (4 * L) + (Ap * L ^ 3 + 1) * (14 * L ^ 2)) := by
        rw [← pow_add, ← pow_add]
    _ ≤ 2 ^ ((4 * Aw + 14 * Ap + 24) * L ^ 5) := by
        refine Nat.pow_le_pow_right (by norm_num) ?_
        have h1 : L ≤ L ^ 5 := by
          calc L = L ^ 1 := (pow_one L).symm
            _ ≤ L ^ 5 := Nat.pow_le_pow_right (by omega) (by norm_num)
        have h2 : L ^ 2 ≤ L ^ 5 := Nat.pow_le_pow_right (by omega) (by norm_num)
        have e1 : (Aw * L ^ 4 + 2) * (4 * L) = 4 * Aw * L ^ 5 + 8 * L := by ring
        have e2 : (Ap * L ^ 3 + 1) * (14 * L ^ 2) = 14 * Ap * L ^ 5 + 14 * L ^ 2 := by ring
        have e3 : (4 * Aw + 14 * Ap + 24) * L ^ 5 =
            4 * Aw * L ^ 5 + 14 * Ap * L ^ 5 + 24 * L ^ 5 := by ring
        rw [e1, e2, e3]
        omega

end Split

end Explicit
