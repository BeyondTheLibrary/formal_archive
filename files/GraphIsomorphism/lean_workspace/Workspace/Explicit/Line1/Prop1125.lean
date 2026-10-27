/-
An explicit running time for Theorem 1.1.1 (Babai, version 2.5), tier 2: the line-1 threshold.
Not part of the faithful formalization.
-/
import Workspace.Algo.CameronDescent

/-!
# Proposition 11.2.5 without a threshold, and the Cameron recognition step at `m ≥ 25`

`Babai.Proposition_11_2_5` is stated with a leading `∃ n₀` (the paper's "assuming `n` is
greater than an absolute constant"), and its proof takes `n₀ = 0`. The machine's threshold
`Algo.camDescentThreshold` is the `Classical.choose` of that statement, so it has no known
value. Here the same proof, line for line, is stated for every `n`
(`Explicit.proposition_11_2_5_all`), and the index bound of the Cameron recognition step
(`Algo.camRecognize_index`) follows from it at every `m ≥ 25`, the threshold of the cited
Theorem 11.2.3 (`Explicit.camRecognize_indexX`).
-/

universe u

namespace Explicit

open Babai MulAction Equiv Equiv.Perm

/-- §11.2, **Proposition 11.2.5**, for every degree: the proof of `Babai.Proposition_11_2_5`
(which takes `n₀ = 0`), with the threshold dropped. -/
theorem proposition_11_2_5_all : ∀ (Ω : Type u) [Fintype Ω] (G : Subgroup (Equiv.Perm Ω))
    (s t k : ℕ), IsCameronGroup G s t k →
      (Fintype.card Ω : ℝ) ^ (1 + Real.logb 2 (Fintype.card Ω)) ≤ (Nat.card G : ℝ) →
      Real.logb 2 (Fintype.card Ω) ≤ (k : ℝ) ∧
        ((Nat.factorial s : ℕ) : ℝ) < (Fintype.card Ω : ℝ) := by
  intro Ω _ G s t k hC hGcard
  obtain ⟨hs1, ht1, hmax, hk2t, hn, -⟩ := id hC
  have hk5 : 5 ≤ k := le_trans (le_max_right (2 * t) 5) hmax
  have hks : k ^ s ≤ Fintype.card Ω := pow_le_card hC
  have hn5 : 5 ≤ Fintype.card Ω :=
    le_trans (le_trans (Nat.le_self_pow (by omega) 5) (Nat.pow_le_pow_left hk5 s)) hks
  -- the paper's `|G| ≤ (k!)^s s!`, and `(k!)^s < k^{ks} ≤ n^k`
  have hcardG := card_le_of_isCameronGroup hC
  have hfactk : (Nat.factorial k) ^ s ≤ Fintype.card Ω ^ k := by
    calc (Nat.factorial k) ^ s ≤ (k ^ k) ^ s := Nat.pow_le_pow_left (Nat.factorial_le_pow k) s
      _ = (k ^ s) ^ k := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
      _ ≤ Fintype.card Ω ^ k := Nat.pow_le_pow_left hks k
  -- real-valued notation
  set n : ℕ := Fintype.card Ω with hndef
  set L : ℝ := Real.logb 2 (n : ℝ) with hLdef
  have hnR1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast lt_of_lt_of_le (by norm_num) hn5
  have hnR0 : (0 : ℝ) < (n : ℝ) := lt_trans zero_lt_one hnR1
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hL2 : (2 : ℝ) ≤ L := by
    have h4 : Real.log 4 ≤ Real.log (n : ℝ) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast le_trans (by norm_num) hn5)
    have hlog4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]; push_cast; ring
    rw [hLdef, Real.logb, le_div_iff₀ hlog2pos]
    rw [hlog4] at h4
    linarith
  have hL0 : (0 : ℝ) < L := lt_of_lt_of_le (by norm_num) hL2
  have hL1 : (1 : ℝ) ≤ L := le_trans (by norm_num) hL2
  -- Proposition 11.2.4: `s ≤ log n / log 5 ≤ (log₂ n)/2`
  have hsL : (s : ℝ) ≤ L / 2 := by
    obtain ⟨-, hsk, hk5'⟩ := Proposition_11_2_4 hC
    have hlogn0 : (0 : ℝ) ≤ Real.log (n : ℝ) := Real.log_nonneg (le_of_lt hnR1)
    have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have hlog45 : 2 * Real.log 2 ≤ Real.log 5 := by
      rw [show (2 : ℝ) * Real.log 2 = Real.log 4 by
        rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]; push_cast; ring]
      exact Real.log_le_log (by norm_num) (by norm_num)
    calc (s : ℝ) ≤ Real.log (n : ℝ) / Real.log 5 := le_trans hsk hk5'
      _ ≤ Real.log (n : ℝ) / (2 * Real.log 2) := by
          apply div_le_div_of_nonneg_left hlogn0 (by positivity) hlog45
      _ = L / 2 := by rw [hLdef, Real.logb]; ring
  -- `s! ≤ s^s ≤ L^L`
  have hfacts : ((Nat.factorial s : ℕ) : ℝ) ≤ L ^ L := by
    have hsR1 : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs1
    have h1 : ((Nat.factorial s : ℕ) : ℝ) ≤ (s : ℝ) ^ ((s : ℕ) : ℝ) := by
      rw [Real.rpow_natCast]
      exact_mod_cast Nat.factorial_le_pow s
    have hsLe : (s : ℝ) ≤ L := le_trans hsL (by linarith)
    calc ((Nat.factorial s : ℕ) : ℝ) ≤ (s : ℝ) ^ ((s : ℕ) : ℝ) := h1
      _ ≤ L ^ ((s : ℕ) : ℝ) := Real.rpow_le_rpow (by linarith) hsLe (by positivity)
      _ ≤ L ^ L := Real.rpow_le_rpow_of_exponent_le hL1 hsLe
  -- `L^L = n^{log₂ L}`
  have hLL : L ^ L = (n : ℝ) ^ (Real.logb 2 L) := by
    rw [Real.rpow_def_of_pos hL0, Real.rpow_def_of_pos hnR0, Real.logb, hLdef, Real.logb]
    congr 1
    field_simp
  -- `log₂ L < 1 + L/2`
  have hlogbL : Real.logb 2 L < 1 + L / 2 := by
    have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have hlog2' : (2 : ℝ) / 3 < Real.log 2 := by
      have := Real.log_two_gt_d9
      linarith
    have hlogL : Real.log L ≤ L / 3 + (Real.log 3 - 1) := by
      have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < L / 3 by positivity)
      rw [Real.log_div (by positivity) (by norm_num)] at h
      linarith
    have hlog3 : Real.log 3 - 1 < Real.log 2 := by
      have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (3 : ℝ) / 2 by norm_num)
      rw [Real.log_div (by norm_num) (by norm_num)] at h
      linarith
    have hthird : L / 3 ≤ Real.log 2 / 2 * L := by
      have : (1 : ℝ) / 3 ≤ Real.log 2 / 2 := by linarith
      nlinarith
    have hkey : Real.log L < Real.log 2 + Real.log 2 / 2 * L := by linarith
    rw [Real.logb, div_lt_iff₀ hlog2]
    calc Real.log L < Real.log 2 + Real.log 2 / 2 * L := hkey
      _ = (1 + L / 2) * Real.log 2 := by ring
  -- the paper's chain `n^{1+log₂ n} ≤ |G| ≤ (k!)^s s! < n^k · n^{log₂ log₂ n}`
  have hchain : (n : ℝ) ^ (1 + L) ≤ (n : ℝ) ^ ((k : ℝ) + Real.logb 2 L) := by
    refine le_trans hGcard ?_
    have h1 : (Nat.card G : ℝ) ≤ ((Nat.factorial k : ℕ) : ℝ) ^ (s : ℕ) *
        ((Nat.factorial s : ℕ) : ℝ) := by
      exact_mod_cast hcardG
    have h2 : ((Nat.factorial k : ℕ) : ℝ) ^ (s : ℕ) ≤ (n : ℝ) ^ (k : ℕ) := by
      exact_mod_cast hfactk
    calc (Nat.card G : ℝ) ≤ ((Nat.factorial k : ℕ) : ℝ) ^ (s : ℕ) *
          ((Nat.factorial s : ℕ) : ℝ) := h1
      _ ≤ (n : ℝ) ^ (k : ℕ) * (L ^ L) := by
          refine mul_le_mul h2 hfacts (by positivity) (by positivity)
      _ = (n : ℝ) ^ ((k : ℕ) : ℝ) * (n : ℝ) ^ (Real.logb 2 L) := by
          rw [hLL, Real.rpow_natCast]
      _ = (n : ℝ) ^ ((k : ℝ) + Real.logb 2 L) := by rw [Real.rpow_add hnR0]
  have hexp : 1 + L ≤ (k : ℝ) + Real.logb 2 L :=
    (Real.rpow_le_rpow_left_iff hnR1).1 hchain
  -- hence `s < k`, and `s! < s^s < k^s ≤ n`
  have hsk : s < k := by
    have : (s : ℝ) < (k : ℝ) := by linarith
    exact_mod_cast this
  have hfactn : Nat.factorial s < n :=
    lt_of_le_of_lt (Nat.factorial_le_pow s)
      (lt_of_lt_of_le (Nat.pow_lt_pow_left hsk (by omega)) hks)
  refine ⟨?_, by exact_mod_cast hfactn⟩
  -- and finally `n^{1+log₂ n} ≤ |G| < n^{k+1}`, so `log₂ n ≤ k`
  have hle : Nat.card G ≤ n ^ (k + 1) := by
    calc Nat.card G ≤ (Nat.factorial k) ^ s * (Nat.factorial s) := hcardG
      _ ≤ n ^ k * n := Nat.mul_le_mul hfactk (le_of_lt hfactn)
      _ = n ^ (k + 1) := by ring
  have hchain2 : (n : ℝ) ^ (1 + L) ≤ (n : ℝ) ^ ((k : ℝ) + 1) := by
    refine le_trans hGcard ?_
    have : (Nat.card G : ℝ) ≤ (n : ℝ) ^ (k + 1 : ℕ) := by exact_mod_cast hle
    calc (Nat.card G : ℝ) ≤ (n : ℝ) ^ (k + 1 : ℕ) := this
      _ = (n : ℝ) ^ (((k : ℕ) + 1 : ℕ) : ℝ) := (Real.rpow_natCast _ _).symm
      _ = (n : ℝ) ^ ((k : ℝ) + 1) := by push_cast; ring_nf
  have := (Real.rpow_le_rpow_left_iff hnR1).1 hchain2
  linarith


end Explicit

namespace Explicit

open RAM RAM.Targets Algo

/-- `Algo.camRecognize_index` at every `n ≥ 25`: the recognizer's witness gives the index
and parameter bounds of Theorem 11.2.1 (the same proof, through
`Explicit.proposition_11_2_5_all`, without the threshold `Algo.camDescentThreshold`). -/
theorem camRecognize_indexX
    (cameron : RawGens × List ℕ → Option RawCameron)
    (hpoly : PolyFun cameron) (hspec : CameronSpec cameron)
    (n : ℕ) (gs : RawGens) (dom : List ℕ) (hd : dom.length = n)
    (hw : RawGens.WF n gs) (hn : 25 ≤ n)
    (hp : Babai.IsPrimitive (decGroup n gs))
    (hb : (n : ℝ) ^ (1 + Real.logb 2 n) ≤ Nat.card (decGroup n gs)) :
    ∃ (c : RawCameron) (h : c.WF n), cameron (gs, dom) = some c ∧
      (camNbar c h).relIndex (decGroup n gs) ≤ n ∧ Real.logb 2 n ≤ (c.k : ℝ) := by
  obtain ⟨c, h, heq, hR, hlo, hhi⟩ := hspec n gs dom hd hw hn hp hb
  have hC : Babai.IsCameronGroup (decGroup n gs) c.s c.t c.k :=
    ⟨h.s_pos, h.t_pos, h.k_max, h.k_gt, by simpa using h.card,
      hR, decCameron c h, hlo, hhi⟩
  have hh := proposition_11_2_5_all.{0} (Fin n) (decGroup n gs)
    c.s c.t c.k hC (by simpa using hb)
  have hlog : Real.logb 2 n ≤ (c.k : ℝ) := by simpa using hh.1
  have hsk : 2 * c.s ≤ c.k := by
    have hskR : (2 * c.s : ℝ) ≤ (c.k : ℝ) :=
      (Babai.two_mul_le_logb hC).trans hh.1
    exact_mod_cast hskR
  exact ⟨c, h, heq, camNbar_index_le h _ hlo hhi hsk, hlog⟩

end Explicit
