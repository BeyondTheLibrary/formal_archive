import Workspace.Algo.TopMasterWindowRecognize

/-! # An integer order threshold for Reduce-to-Johnson

Sec. 11.3, step 5 tests `|Ḡ| < m^{1+log₂ m}` with the real logarithm. The machine tests
`|Ḡ| < m^{1+⌈log₂ m⌉}` instead (`Algo.masterSmallOrder`). The two tests agree when `m` is a
power of two (`Algo.masterOrderCap_eq_of_pow_two`). For other `m` no routine with a proved
time bound is known for the printed test: with `g = |Ḡ|` it asks for the sign of
`(log₂ m)² − log₂(g/m)`. That number is `0` exactly when `2^x = m` and `m^x = g/m` for the
irrational `x = log₂ m`; no known theorem excludes this (the open four exponentials conjecture
would), and no effective lower bound on its absolute value is known either. See the
the corrected paper "Sec. 11.3, step 5: the order threshold is rounded up".

What the rounding keeps:

* a group that fails the machine test has order at least the printed threshold
  (`Algo.masterSmallOrder_false`), so step 6 has the hypothesis of Theorem 11.2.3;
* a group that passes it has order below `m^{2+log₂ m}`, inside the line-1 cost bound
  (`Algo.masterSmallOrder_true`), so step 5 has the paper's multiplicative cost up to a
  factor `m`;
* both branches are branches of the Master's line 1 as the mathematical layer states it
  (`Babai.Line1Case`, which admits step 5 whenever `|Ḡ| ≤ line1Cost n`).
-/
namespace Algo
open RAM RAM.Targets Babai Equiv

def masterClog (m : ℕ) : ℕ := if m ≤ 1 then 0 else Nat.log 2 (m - 1) + 1

theorem masterClog_eq (m : ℕ) : masterClog m = Nat.clog 2 m := by
  unfold masterClog
  split_ifs with hm
  · exact (Nat.clog_of_right_le_one hm 2).symm
  · have hpow := Nat.pow_log_le_self 2 (by omega : m - 1 ≠ 0)
    have hlt := Nat.lt_pow_succ_log_self (by decide : 1 < 2) (m - 1)
    have hlow := (Nat.lt_clog_iff_pow_lt (by decide : 1 < 2)).mpr
      (hpow.trans_lt (by omega : m - 1 < m))
    have hupp := (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).mpr
      (show m ≤ 2 ^ (Nat.log 2 (m - 1) + 1) by omega)
    omega

theorem masterClog_le (m : ℕ) : masterClog m ≤ Nat.log 2 m + 1 := by
  unfold masterClog
  split_ifs with hm
  · omega
  · exact Nat.add_le_add_right (Nat.log_mono_right (Nat.sub_le _ _)) _

theorem polyFun_masterClog : PolyFun masterClog := by
  exact (PolyFun.ite (polyFun_id.le (polyFun_const 1)) (polyFun_const 0)
    (((polyFun_id.sub (polyFun_const 1)).comp polyFun_log2).add (polyFun_const 1))).of_eq
      (fun m => by simp only [masterClog, decide_eq_true_eq, id_eq])

def masterOrderCap (dom : List ℕ) : ℕ := dom.length ^ (1 + masterClog dom.length)

def masterSmallOrder (p : RawGens × List ℕ) : Bool := decide (rawOrder (p.2, p.1) < masterOrderCap p.2)

theorem polyFun_masterOrderCap : PolyFun masterOrderCap := by
  have he : PolyFun (fun dom : List ℕ => 1 + masterClog dom.length) :=
    (polyFun_const 1).add (polyFun_length.comp polyFun_masterClog)
  exact polyFun_length.pow he (q := fun s => s + 2) (fun dom => by
    have h := masterClog_le dom.length
    have hl := Nat.log_le_self 2 dom.length
    have hs := length_le_size dom
    change 1 + masterClog dom.length ≤ Enc.size dom + 2
    omega) (polyBound_id.add (polyBound_const 2))

theorem polyFun_masterSmallOrder : PolyFun masterSmallOrder :=
  ((((polyFun_swap.comp polyFun_rawOrder).add (polyFun_const 1)).le
    (polyFun_snd.comp polyFun_masterOrderCap))).of_eq
      (fun p => by simp only [masterSmallOrder, Nat.add_one_le_iff])

/-- The rounded threshold is at least the literal real threshold. -/
theorem masterOrderCap_lower {dom : List ℕ} (hm : 1 ≤ dom.length) :
    (dom.length : ℝ) ^ (1 + Real.logb 2 dom.length) ≤ (masterOrderCap dom : ℝ) := by
  have hlog : Real.logb 2 dom.length ≤ (masterClog dom.length : ℝ) := by
    rw [masterClog_eq, ← Real.natCeil_logb_natCast]
    exact Nat.le_ceil _
  have hbase : (1 : ℝ) ≤ dom.length := by exact_mod_cast hm
  have he := Real.rpow_le_rpow_of_exponent_le hbase (add_le_add_left hlog 1)
  calc
    _ ≤ (dom.length : ℝ) ^ (1 + (masterClog dom.length : ℝ)) := by simpa only [add_comm] using he
    _ = (masterOrderCap dom : ℝ) := by
      rw [masterOrderCap, Nat.cast_pow, ← Real.rpow_natCast]
      push_cast
      rfl

/-- For `m = 2^a` the rounded threshold is the printed threshold `m^{1+log₂ m}`. -/
theorem masterOrderCap_eq_of_pow_two {dom : List ℕ} {a : ℕ} (hm : dom.length = 2 ^ a) :
    (masterOrderCap dom : ℝ) = (dom.length : ℝ) ^ (1 + Real.logb 2 dom.length) := by
  have hc : masterClog dom.length = a := by
    rw [masterClog_eq, hm, Nat.clog_pow 2 a (by decide)]
  have hl : Real.logb 2 (dom.length : ℝ) = a := by
    rw [hm, Nat.cast_pow, Nat.cast_ofNat, Real.logb_pow, Real.logb_self_eq_one one_lt_two,
      mul_one]
  rw [masterOrderCap, hc, hl, Nat.cast_pow, ← Real.rpow_natCast]
  push_cast
  rfl

/-- The existing recurrence bound already pays for the conservative rounding. -/
theorem masterOrderCap_upper {dom : List ℕ} (hm : 1 ≤ dom.length) :
    masterOrderCap dom ≤ line1Cost dom.length := by
  exact Nat.pow_le_pow_right hm (by have h := masterClog_le dom.length; omega)

/-- A large raw branch has the precise lower bound needed by Cameron recognition. -/
theorem masterSmallOrder_false {m : ℕ} {p : RawGens × List ℕ}
    (hd : p.2.length = m) (hw : RawGens.WF m p.1) (hm : 1 ≤ m)
    (ht : masterSmallOrder p = false) :
    (m : ℝ) ^ (1 + Real.logb 2 m) ≤ Nat.card (decGroup m p.1) := by
  have hh : masterOrderCap p.2 ≤ rawOrder (p.2, p.1) := by simpa [masterSmallOrder] using ht
  have he := rawOrder_spec p.2 hd (p.1.map (decPerm m))
  rw [map_encPerm_decPerm hw] at he
  have hc := masterOrderCap_lower (dom := p.2) (hd.symm ▸ hm)
  rw [hd] at hc
  exact hc.trans (by exact_mod_cast hh.trans_eq he)

/-- The small branch has at most the existing line-1 multiplicative cost. -/
theorem masterSmallOrder_true {m : ℕ} {p : RawGens × List ℕ}
    (hd : p.2.length = m) (hw : RawGens.WF m p.1) (hm : 1 ≤ m)
    (ht : masterSmallOrder p = true) : Nat.card (decGroup m p.1) ≤ line1Cost m := by
  have hh : rawOrder (p.2, p.1) < masterOrderCap p.2 := by simpa [masterSmallOrder] using ht
  have he := rawOrder_spec p.2 hd (p.1.map (decPerm m))
  rw [map_encPerm_decPerm hw] at he
  change rawOrder (p.2, p.1) = Nat.card (decGroup m p.1) at he
  rw [← he]
  exact hh.le.trans (hd ▸ masterOrderCap_upper (dom := p.2) (hd.symm ▸ hm))
end Algo
