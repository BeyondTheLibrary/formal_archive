import Workspace.Algo.SplitUpcc
import Workspace.SplitOrJohnson.BipSplit
import Workspace.SplitOrJohnson.Procedure

/-!
# Section 9.4, step 5: the threshold and its size

The machine stores the threshold as two naturals. The mathematical
interface uses a real number. We do not reduce the fraction after an
update. Each update adds at most two vertex-count bit lengths, so a
linear number of updates still has polynomial size.
-/

namespace Algo
open Babai RAM

/-- Section 9.4: the real threshold represented by a raw pair. -/
noncomputable def sbipAlphaValue (p : ℕ × ℕ) : ℝ := (p.1 : ℝ) / p.2

/-- Section 9.4, step 5: `α ← α n₁ / |W₁|`, without cancelling factors. -/
def sbipAlphaUpdate (z : (ℕ × ℕ) × (ℕ × ℕ)) : ℕ × ℕ :=
  (z.1.1 * z.2.1, z.1.2 * z.2.2)

theorem sbipPoly_alphaUpdate : PolyFun sbipAlphaUpdate :=
  ((polyFun_fst.comp polyFun_fst).mul (polyFun_snd.comp polyFun_fst)).pair
    ((polyFun_fst.comp polyFun_snd).mul (polyFun_snd.comp polyFun_snd))

/-- Section 9.4, step 5: the pair represents the paper's real quotient.
This identity also holds on zero denominators under Lean's division convention. -/
theorem sbipAlphaUpdate_value (p : ℕ × ℕ) (n₁ w : ℕ) :
    sbipAlphaValue (sbipAlphaUpdate (p, (n₁, w))) =
      sbipAlphaValue p * n₁ / w := by
  simp only [sbipAlphaValue, sbipAlphaUpdate, Nat.cast_mul]
  ring

theorem sbipAlphaUpdate_den_pos {p : ℕ × ℕ} {n₁ w : ℕ}
    (hb : 0 < p.2) (hw : 0 < w) :
    0 < (sbipAlphaUpdate (p, (n₁, w))).2 := Nat.mul_pos hb hw

/-- Section 9.4, step 5: the raw update satisfies `claim_9_4_step5`. -/
theorem sbipAlphaUpdate_valid {p : ℕ × ℕ} {n₁ w : ℕ}
    (hα : 0 < sbipAlphaValue p) (hw : sbipAlphaValue p * n₁ < w) (hwn : w ≤ n₁) :
    sbipAlphaValue (sbipAlphaUpdate (p, (n₁, w))) < 1 ∧
      sbipAlphaValue (sbipAlphaUpdate (p, (n₁, w))) * w = sbipAlphaValue p * n₁ ∧
      sbipAlphaValue p ≤ sbipAlphaValue (sbipAlphaUpdate (p, (n₁, w))) := by
  rw [sbipAlphaUpdate_value]
  exact claim_9_4_step5 hα hw hwn

/-- Section 9.4, step 5: the raw arithmetic agrees with `Babai.alphaNew`.
The caller supplies the represented threshold and the computed class size. -/
theorem sbipAlphaUpdate_spec {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    (X : Pt (BipBlockInputs Ω)) (p : ℕ × ℕ) (n₁ w : ℕ)
    (hα : sbipAlphaValue p = BipBlockInputs.alpha X)
    (hn : n₁ = BipBlockInputs.n₁ X) (hw : w = (dominantClass X).ncard) :
    sbipAlphaValue (sbipAlphaUpdate (p, (n₁, w))) = alphaNew X := by
  rw [sbipAlphaUpdate_value, hα, hn, hw]
  rfl

/-- Section 9.4, step 5: one update adds at most `2 * n.size` bits.
Both sizes may be smaller than the original ambient size `n`. -/
theorem sbipAlphaUpdate_bits (p : ℕ × ℕ) {n₁ w n : ℕ} (hn : n₁ ≤ n) (hw : w ≤ n) :
    Nat.size (sbipAlphaUpdate (p, (n₁, w))).1 +
      Nat.size (sbipAlphaUpdate (p, (n₁, w))).2 ≤
        Nat.size p.1 + Nat.size p.2 + 2 * Nat.size n := by
  have h₁ := size_mul_le p.1 n₁
  have h₂ := size_mul_le p.2 w
  have h₃ := Nat.size_le_size hn
  have h₄ := Nat.size_le_size hw
  dsimp only [sbipAlphaUpdate]
  omega

/-- Section 9.5: the one-update bound iterates over varying part sizes.
This is a bound on a sequence, not a machine loop over a binary counter. -/
theorem sbipAlphaSequence_bits (p : ℕ → ℕ × ℕ) (counts : ℕ → ℕ × ℕ)
    (n t : ℕ) (hstep : ∀ i < t, p (i + 1) = sbipAlphaUpdate (p i, counts i))
    (hbound : ∀ i < t, (counts i).1 ≤ n ∧ (counts i).2 ≤ n) :
    Nat.size (p t).1 + Nat.size (p t).2 ≤
      Nat.size (p 0).1 + Nat.size (p 0).2 + t * (2 * Nat.size n) := by
  induction t with
  | zero => simp
  | succ t ih =>
      have hi := ih (fun i hi => hstep i (by omega))
        (fun i hi => hbound i (by omega))
      have hb := hbound t (by omega)
      have hu := sbipAlphaUpdate_bits (p t) hb.1 hb.2
      rw [← hstep t (by omega)] at hu
      calc
        Nat.size (p (t + 1)).1 + Nat.size (p (t + 1)).2 ≤
            Nat.size (p t).1 + Nat.size (p t).2 + 2 * Nat.size n := hu
        _ ≤ Nat.size (p 0).1 + Nat.size (p 0).2 +
            t * (2 * Nat.size n) + 2 * Nat.size n := Nat.add_le_add_right hi _
        _ = Nat.size (p 0).1 + Nat.size (p 0).2 +
            (t + 1) * (2 * Nat.size n) := by ring

/-- Section 9.5: at most `2n + 2` updates use only the initial bits plus
`(4n + 4) * n.size` bits. This closes the arithmetic part of risk R-A10-1. -/
theorem sbipAlphaSequence_depth_bits (p : ℕ → ℕ × ℕ) (counts : ℕ → ℕ × ℕ)
    (n t : ℕ) (hstep : ∀ i < t, p (i + 1) = sbipAlphaUpdate (p i, counts i))
    (hbound : ∀ i < t, (counts i).1 ≤ n ∧ (counts i).2 ≤ n) (ht : t ≤ 2 * n + 2) :
    Nat.size (p t).1 + Nat.size (p t).2 ≤
      Nat.size (p 0).1 + Nat.size (p 0).2 + (4 * n + 4) * Nat.size n := by
  calc
    _ ≤ Nat.size (p 0).1 + Nat.size (p 0).2 + t * (2 * Nat.size n) :=
      sbipAlphaSequence_bits p counts n t hstep hbound
    _ ≤ Nat.size (p 0).1 + Nat.size (p 0).2 + (2 * n + 2) * (2 * Nat.size n) :=
      Nat.add_le_add_left (Nat.mul_le_mul_right _ ht) _
    _ = _ := by ring

/-- Section 9.5: the stored pair, including RAM framing, has polynomial size. -/
theorem sbipAlphaSequence_size (p : ℕ → ℕ × ℕ) (counts : ℕ → ℕ × ℕ)
    (n t : ℕ) (hstep : ∀ i < t, p (i + 1) = sbipAlphaUpdate (p i, counts i))
    (hbound : ∀ i < t, (counts i).1 ≤ n ∧ (counts i).2 ≤ n) (ht : t ≤ 2 * n + 2) :
    Enc.size (p t) ≤ 2 * (Nat.size (p 0).1 + Nat.size (p 0).2) +
      8 * (n + 1) ^ 2 + 8 := by
  have hb := sbipAlphaSequence_depth_bits p counts n t hstep hbound ht
  have hs := Combine.size_pair_le (p t).1 (p t).2
  rw [Small.size_nat, Small.size_nat] at hs
  have hn : Nat.size n ≤ n := Nat.size_le.2 Nat.lt_two_pow_self
  have hm := Nat.mul_le_mul_left (4 * n + 4) hn
  nlinarith

end Algo
