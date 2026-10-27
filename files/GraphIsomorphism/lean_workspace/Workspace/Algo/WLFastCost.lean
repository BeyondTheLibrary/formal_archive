/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

§5.4.2 (lines 3399–3400): the trivial bound `O(k²n^{2k+1})` for `k`-ary WL refinement,
proved on the RAM.
-/
import Workspace.Algo.WLFastMain
import Workspace.Algo.WLPoly

/-!
# §5.4.2: `k`-ary WL refinement in time `O(k²n^{2k+1})`

The paper (lines 3399–3400): *"The stable refinement (`k`-ary coherent configuration) can
trivially be computed in time `O(k²n^{2k+1})`."*

The program `Algo.WLFast.wlFastP` follows §5.4.1 round by round.  It keeps the colors in an
array indexed by the tuples (`O(1)` tuple addressing: the index of a tuple is its value in base
`n`), and in each round it

* writes, for every tuple `t` and vertex `y`, the record `(t, c(t[1 ↦ y]), …, c(t[k ↦ y]))`,
  `N n` records of `k + 1` numbers (`N = n^k`);
* radix sorts them, which sorts the `n` tuples of colors of each `t`;
* writes the string of each `t` (its color, then its sorted tuples);
* radix sorts the `N` strings of length `nk + 1` and gives each its dense rank, which is the new
  color (`Algo.WLFast.wlNewCol_eq_drank`).

A round costs `O(k n N) = O(k n^{k+1})`, and the program stops after the first round that
changes no color, at most `N + 1` rounds (`Algo.WLFast.exists_fix_le`), for a total of
`O(k n^{2k+1})`.  The table of neighbour indices built at the start costs `O(k² n^{k+2})`.
Both are `O(k² n^{2k+1})` for `k ≥ 1` (`Algo.WLFast.tWL_le`).

No axiom, no `sorry`.
-/

namespace Algo

namespace WLFast

/-- **The step count is `O(k² n N²)`** when `1 ≤ k`, `1 ≤ n ≤ N`. -/
theorem tWL_le {n k N : ℕ} (hk : 1 ≤ k) (hn : 1 ≤ n) (hnN : n ≤ N) :
    tWL n k N (2 * n + 2 + N * (2 * k + 4)) ≤ 3000 * (k ^ 2 * n * N ^ 2) := by
  have hN : 1 ≤ N := hn.trans hnN
  have hk2 : k ≤ k ^ 2 := Nat.le_self_pow (by norm_num) k
  have hN2 : N ≤ N ^ 2 := Nat.le_self_pow (by norm_num) N
  have hk1 : 1 ≤ k ^ 2 := Nat.one_le_pow _ _ hk
  have hN1 : 1 ≤ N ^ 2 := Nat.one_le_pow _ _ hN
  -- every monomial of the step count is at most `k² n N²`
  have m0 : 1 ≤ k ^ 2 * n * N ^ 2 :=
    Nat.one_le_iff_ne_zero.2 (by positivity : k ^ 2 * n * N ^ 2 ≠ 0)
  have m1 : k ≤ k ^ 2 * n * N ^ 2 := by
    calc k = k * 1 * 1 := by ring
      _ ≤ k ^ 2 * n * N ^ 2 := by gcongr
  have m2 : n ≤ k ^ 2 * n * N ^ 2 := by
    calc n = 1 * n * 1 := by ring
      _ ≤ k ^ 2 * n * N ^ 2 := by gcongr
  have m3 : N ≤ k ^ 2 * n * N ^ 2 := by
    calc N = 1 * 1 * N := by ring
      _ ≤ k ^ 2 * n * N ^ 2 := by gcongr
  have m4 : k * n ≤ k ^ 2 * n * N ^ 2 := by
    calc k * n = k * n * 1 := by ring
      _ ≤ k ^ 2 * n * N ^ 2 := by gcongr
  have m5 : k * N ≤ k ^ 2 * n * N ^ 2 := by
    calc k * N = k * 1 * N := by ring
      _ ≤ k ^ 2 * n * N ^ 2 := by gcongr
  have m6 : n * N ≤ k ^ 2 * n * N ^ 2 := by
    calc n * N = 1 * n * N := by ring
      _ ≤ k ^ 2 * n * N ^ 2 := by gcongr
  have m7 : k * n * N ≤ k ^ 2 * n * N ^ 2 := by gcongr
  have m8 : N ^ 2 ≤ k ^ 2 * n * N ^ 2 := by
    calc N ^ 2 = 1 * 1 * N ^ 2 := by ring
      _ ≤ k ^ 2 * n * N ^ 2 := by gcongr
  have m9 : k * N ^ 2 ≤ k ^ 2 * n * N ^ 2 := by
    calc k * N ^ 2 = k * 1 * N ^ 2 := by ring
      _ ≤ k ^ 2 * n * N ^ 2 := by gcongr
  have m10 : n * N ^ 2 ≤ k ^ 2 * n * N ^ 2 := by
    calc n * N ^ 2 = 1 * n * N ^ 2 := by ring
      _ ≤ k ^ 2 * n * N ^ 2 := by gcongr
  have m11 : k * n * N ^ 2 ≤ k ^ 2 * n * N ^ 2 := by gcongr
  have m12 : k ^ 2 * n * N ≤ k ^ 2 * n * N ^ 2 := by gcongr
  have m13 : k ^ 2 * n ^ 2 * N ≤ k ^ 2 * n * N ^ 2 := by
    calc k ^ 2 * n ^ 2 * N = k ^ 2 * n * (n * N) := by ring
      _ ≤ k ^ 2 * n * (N * N) := by gcongr
      _ = k ^ 2 * n * N ^ 2 := by ring
  have m14 : k ^ 2 * n ≤ k ^ 2 * n * N ^ 2 := by
    calc k ^ 2 * n = k ^ 2 * n * 1 := by ring
      _ ≤ k ^ 2 * n * N ^ 2 := by gcongr
  have m15 : k ^ 2 * N ≤ k ^ 2 * n * N ^ 2 := by
    calc k ^ 2 * N = k ^ 2 * 1 * N := by ring
      _ ≤ k ^ 2 * n * N ^ 2 := by gcongr
  have m16 : k ^ 2 ≤ k ^ 2 * n * N ^ 2 := by
    calc k ^ 2 = k ^ 2 * 1 * 1 := by ring
      _ ≤ k ^ 2 * n * N ^ 2 := by gcongr
  have hN0 : N ≠ 0 := by omega
  unfold tWL
  rw [if_neg hN0]
  simp only [tInner, tAlloc, tBuild, tRow, tYB, tIB, tHorn, tRound, tR1, tR1Row, tR2, tR4, tR4Row,
    tR4Y, tR5, tR6, tR7, tOut, tRadix, tCs, tRank]
  ring_nf
  ring_nf at *
  linarith

/-- With `n = 0` (and `k ≥ 1`) the table is empty and the program only copies the input. -/
theorem tWL_zero (k : ℕ) : tWL 0 k 0 (2 * 0 + 2 + 0 * (2 * k + 4)) = 221 := by
  simp [tWL]

end WLFast

open RAM in
/-- **§5.4.2 (lines 3399–3400), proved**: `k`-ary WL refinement runs on the RAM in
`O(k²n^{2k+1})` steps (`WLFast.wlFastP`). -/
theorem section_5_4_2_trivial : Section_5_4_2_trivial_statement := by
  refine ⟨WLFast.wlFastP, 3000, fun n k p hk hwf => ?_⟩
  obtain ⟨t, ht, hhalt, hout⟩ := (WLFast.runsTo_wlFastP hk hwf).spec _ rfl
  refine ⟨t, ht.trans ?_, hhalt, hout⟩
  have hN : p.2.length = n ^ k := length_table hwf
  have hkey : ∀ q ∈ p.2, q.1.length = k := fun q hq =>
    ((hwf.keyMem q.1).1 (List.mem_map_of_mem hq)).1
  have hL : (Enc.encode p).length = 2 * n + 2 + n ^ k * (2 * k + 4) := by
    rw [WLFast.length_encode_rawWL hkey, WLFast.length_dom hwf, hN]
  rw [hN, hL]
  rcases Nat.eq_zero_or_pos n with h0 | hn
  · subst h0
    rw [zero_pow (by omega), WLFast.tWL_zero]
    omega
  · have hnN : n ≤ n ^ k := Nat.le_self_pow (by omega) n
    have e : n ^ (2 * k + 1) = n * (n ^ k) ^ 2 := by ring
    have := WLFast.tWL_le hk hn hnN
    rw [e]
    calc WLFast.tWL n k (n ^ k) (2 * n + 2 + n ^ k * (2 * k + 4))
        ≤ 3000 * (k ^ 2 * n * (n ^ k) ^ 2) := this
      _ ≤ 3000 * (k ^ 2 * (n * (n ^ k) ^ 2) + 1) := by
        rw [show k ^ 2 * n * (n ^ k) ^ 2 = k ^ 2 * (n * (n ^ k) ^ 2) by ring]; omega

end Algo
