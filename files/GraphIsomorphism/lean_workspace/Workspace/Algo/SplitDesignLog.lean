import Workspace.Algo.SplitBipLink
import Workspace.SplitOrJohnson.BlockDesignSkel

/-! # Section 9.7: exact logarithmic tests

The branch and skeleton rank use the real logarithm in the paper. Integer
power comparisons implement both choices exactly. List lengths bound every
exponent, including on malformed inputs.
-/
namespace Algo
open Babai RAM

/-- The Case 3a inequality is an integer comparison. -/
theorem designSmallRank_iff {n d : ℕ} (hn : 0 < n) :
    2 ^ (3 * d) ≤ n ^ 7 ↔ (d : ℝ) ≤ 7 / 3 * Real.logb 2 (n : ℝ) := by
  have hp : (0 : ℝ) < n := by exact_mod_cast hn
  have hh := Real.logb_le_logb (b := 2) (x := (2 : ℝ) ^ (3 * d))
    (y := (n : ℝ) ^ 7) (by norm_num) (by positivity) (by positivity)
  rw [Real.logb_pow,Real.logb_pow] at hh
  norm_num only [Real.logb_self_eq_one,Nat.cast_mul,Nat.cast_ofNat,mul_one] at hh
  have hc : 2 ^ (3 * d) ≤ n ^ 7 ↔ (2 : ℝ) ^ (3 * d) ≤ (n : ℝ) ^ 7 := by
    exact_mod_cast Iff.rfl
  rw [hc,← hh]
  constructor <;> intro h <;> linarith

/-- The skeleton ceiling is characterized by the opposite integer comparison. -/
theorem designSkel_le_iff {n t : ℕ} (hn : 0 < n) :
    ⌈7 / 4 * Real.logb 2 (n : ℝ)⌉₊ ≤ t ↔ n ^ 7 ≤ 2 ^ (4 * t) := by
  have hp : (0 : ℝ) < n := by exact_mod_cast hn
  have hh := Real.logb_le_logb (b := 2) (x := (n : ℝ) ^ 7)
    (y := (2 : ℝ) ^ (4 * t)) (by norm_num) (by positivity) (by positivity)
  rw [Real.logb_pow,Real.logb_pow] at hh
  norm_num only [Real.logb_self_eq_one,Nat.cast_mul,Nat.cast_ofNat,mul_one] at hh
  have hc : n ^ 7 ≤ 2 ^ (4 * t) ↔ (n : ℝ) ^ 7 ≤ (2 : ℝ) ^ (4 * t) := by
    exact_mod_cast Iff.rfl
  rw [Nat.ceil_le,hc,← hh]
  constructor <;> intro h <;> linarith

/-- First-part and rank witnesses, with no unary loop controlled by a binary numeral. -/
def designSmallRank (z : List ℕ × List ℕ) : Bool :=
  decide (2 ^ (3 * z.2.length) ≤ z.1.length ^ 7)

theorem polyFun_designSmallRank : PolyFun designSmallRank := by
  have he : PolyFun (fun z : List ℕ × List ℕ => 3 * z.2.length) :=
    (polyFun_const 3).mul (polyFun_snd.comp polyFun_length)
  have hp : PolyFun (fun z : List ℕ × List ℕ => 2 ^ (3 * z.2.length)) :=
    (polyFun_const 2).pow he (q := fun n => 3*n)
      (fun z => Nat.mul_le_mul_left 3 ((length_le_size _).trans (size_snd_le' z)))
      ((polyBound_const 3).mul polyBound_id)
  have hn : PolyFun (fun z : List ℕ × List ℕ => z.1.length ^ 7) :=
    (polyFun_fst.comp polyFun_length).pow (polyFun_const 7)
    (q := fun _ => 7) (fun _ => le_rfl) (polyBound_const 7)
  exact hp.le hn

/-- The search bound exceeds the exact ceiling. -/
theorem designSkel_bound {n : ℕ} (hn : 0 < n) :
    ⌈7 / 4 * Real.logb 2 (n : ℝ)⌉₊ ≤ 7 * (n + 1) := by
  rw [Nat.ceil_le]
  have hlog := logb_two_lt_natLog_succ n
  have hnat : (Nat.log 2 n : ℝ) ≤ n := by exact_mod_cast Nat.log_le_self 2 n
  push_cast
  linarith

/-- Test a candidate skeleton rank, with a size-safe exponent on every input. -/
def designSkelPass (z : List ℕ × ℕ) : Bool :=
  decide (z.1.length ^ 7 ≤ 2 ^ (4 * min z.2 (7 * (z.1.length + 1))))

theorem polyFun_designSkelPass : PolyFun designSkelPass := by
  have hn : PolyFun (fun z : List ℕ × ℕ => z.1.length) := polyFun_fst.comp polyFun_length
  have hb := (polyFun_const 7).mul (hn.add (polyFun_const 1))
  have he := (polyFun_const 4).mul (polyFun_snd.min' hb)
  have hp : PolyFun (fun z : List ℕ × ℕ => 2 ^ (4 * min z.2 (7 * (z.1.length + 1)))) :=
    (polyFun_const 2).pow he (q := fun n => 28*(n+1)) (fun z => by
      have hm := min_le_right z.2 (7 * (z.1.length + 1))
      have hl := (length_le_size z.1).trans (size_fst_le' z)
      change 4 * min z.2 (7 * (z.1.length + 1)) ≤ 28 * (Enc.size z + 1)
      omega) ((polyBound_const 28).mul (polyBound_id.add (polyBound_const 1)))
  exact (hn.pow (polyFun_const 7) (q := fun _ => 7) (fun _ => le_rfl)
    (polyBound_const 7)).le hp

/-- Scan all bounded candidate ranks and return the least passing one. -/
def designSkelCandidates (l : List ℕ) : List ℕ :=
  (List.range (7 * (l.length + 1) + 1)).filter (fun t => designSkelPass (l,t))

def designSkel (l : List ℕ) : ℕ := upccCaseLeast (designSkelCandidates l)

theorem polyFun_designSkel : PolyFun designSkel := by
  have hr : PolyFun (fun l : List ℕ => List.range (7 * (l.length + 1) + 1)) :=
    ((((polyFun_const ((0,0) : ℕ × ℕ)).pair
      (((polyFun_const (List.replicate 7 (0 : ℕ))).pair
        ((polyFun_const 0).pair polyFun_id |>.comp polyFun_cons)).comp
          GIReduction.polyFun_product)).comp polyFun_cons).comp
        polyFun_rangeLength).of_eq (fun l => by
          change List.range (((List.replicate 7 (0 : ℕ)).product (0 :: l)).length + 1) = _
          simp [List.product]
          congr 1
          omega)
  exact ((polyFun_id.pair hr).comp (PolyFun.filterParam polyFun_designSkelPass)).comp
    upccCasePoly_least

/-- The scan computes the paper's real-logarithm ceiling exactly. -/
theorem designSkel_spec (l : List ℕ) (hn : 0 < l.length) :
    designSkel l = ⌈7 / 4 * Real.logb 2 (l.length : ℝ)⌉₊ := by
  let t := ⌈7 / 4 * Real.logb 2 (l.length : ℝ)⌉₊
  have ht : t ≤ 7 * (l.length + 1) := designSkel_bound hn
  have hm (j : ℕ) : j ∈ designSkelCandidates l ↔
      j ≤ 7 * (l.length + 1) ∧ t ≤ j := by
    simp only [designSkelCandidates,List.mem_filter,List.mem_range,designSkelPass,
      decide_eq_true_eq]
    constructor
    · rintro ⟨hj,hp⟩
      rw [min_eq_left (by omega)] at hp
      exact ⟨by omega,(designSkel_le_iff hn).2 hp⟩
    · rintro ⟨hj,hp⟩
      exact ⟨by omega,by rw [min_eq_left hj]; exact (designSkel_le_iff hn).1 hp⟩
  have htm : t ∈ designSkelCandidates l := (hm t).2 ⟨ht,le_rfl⟩
  have hne : designSkelCandidates l ≠ [] := by intro hh; simp [hh] at htm
  obtain ⟨hmem,hle⟩ := upccCaseLeast_spec (designSkelCandidates l) hne
  exact le_antisymm (hle t htm) ((hm _).1 hmem).2

end Algo
