import Workspace.Machine.ListOps2

/-! # Summing an explicit list on the RAM

The sum can be numerically large. Its bit length is at most the sum of
the entry bit lengths, up to the framing already present in the encoding.
Thus the addition fold has a linear state-size bound.
-/

namespace RAM

theorem size_add_le_sizes (a b : ℕ) : Enc.size (a + b) ≤ Enc.size a + Enc.size b := by
  have ha : a < 2 ^ Nat.size a := Nat.size_le.mp le_rfl
  have hb : b < 2 ^ Nat.size b := Nat.size_le.mp le_rfl
  have ha1 : 1 ≤ 2 ^ Nat.size a := Nat.one_le_two_pow
  have hb1 : 1 ≤ 2 ^ Nat.size b := Nat.one_le_two_pow
  have hs : Nat.size (a + b) ≤ Nat.size a + Nat.size b + 1 := by
    apply Nat.size_le.mpr
    rw [pow_succ, pow_add]
    have h1 := Nat.mul_le_mul_left (2 ^ Nat.size a) hb1
    have h2 := Nat.mul_le_mul_right (2 ^ Nat.size b) ha1
    simp only [Nat.mul_one, Nat.one_mul] at h1 h2
    omega
  simp only [Small.size_nat]
  omega

theorem size_foldl_add_le : ∀ (l : List ℕ) (a : ℕ),
    Enc.size (l.foldl (· + ·) a) ≤ Enc.size a + Enc.size l := by
  intro l
  induction l with
  | nil => intro a; simp
  | cons b l ih =>
      intro a
      rw [List.foldl_cons]
      have h := ih (a + b)
      have hab := size_add_le_sizes a b
      have hl : Enc.size (b :: l) =
          Enc.size b + (Nat.size (Enc.encode b).length + 1) + Enc.size l - 1 := by
        rw [size_cons_eq, listSize_frame]
        rfl
      have hp := one_le_size l
      omega

theorem polyFun_foldlAdd : PolyFun (fun z : ℕ × List ℕ => z.2.foldl (· + ·) z.1) := by
  apply PolyFun.foldl polyFun_add (p := fun n => 2 * n)
    ((polyBound_const 2).mul polyBound_id)
  intro a l j
  have h := size_foldl_add_le (l.take j) a
  have ha : Enc.size a ≤ Enc.size (a, l) := size_fst_le' (a, l)
  have hl := (size_take_le j l).trans (size_snd_le' (a, l))
  dsimp only
  omega

theorem polyFun_listSum : PolyFun (fun l : List ℕ => l.sum) := by
  exact (((polyFun_const 0).pair polyFun_id).comp polyFun_foldlAdd).of_eq
    (fun l => by simp [List.sum_eq_foldl])

end RAM

#print axioms RAM.polyFun_listSum
