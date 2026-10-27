/-
An explicit running time for Theorem 1.1.1 (Babai, version 2.5), tier 2: the step count of
the top loop as an explicit RAM routine. Not part of the faithful formalization.
-/
import Workspace.Machine.Small
import Workspace.Explicit.Interface

/-!
# The step count `countE K m = 3·2^{K (log₂ m + 2)^5} + 1` on the RAM, in explicit time

A scratch-register routine on the input register `1` (the packaging of
`RAM.Small.cleanCompute_unary`): the bit length (`RAM.Arith.sizeTo`), then `L = log₂ m + 2`,
then `L^5` and `K·L^5` by repeated addition, then `2^e` by `e` doublings, then `3·2^e + 1`.
Every loop costs four steps per round, so the time is linear in `L`, `K` and
`e = K L^5` (`Explicit.cleanCompute_countE`, time `Explicit.countTime K`).
-/

namespace Explicit

open RAM

/-! ## Two loops -/

/-- `R acc ← R acc + R c · R a`, by `R c` additions (register `9` holds `1`). -/
def repAdd (acc a c : ℕ) : Program := whileNz c (seq (addTo acc acc a) (subTo c c 9))

theorem runsTo_repAdd (acc a c : ℕ) (hac : acc ≠ a) (hcc : acc ≠ c) (hca : c ≠ a)
    (h9a : acc ≠ 9) (h9c : c ≠ 9) (m₀ : Mem) (h9 : m₀ 9 = 1) :
    RunsTo (repAdd acc a c) (fun m => m = m₀)
      (fun m' => m' acc = m₀ acc + m₀ c * m₀ a ∧ m' c = 0 ∧ Outside [acc, c] m₀ m')
      (m₀ c * (2 + 2) + 1) := by
  let inv : Mem → Prop := fun m => m 9 = 1 ∧ m a = m₀ a ∧ m c ≤ m₀ c ∧
    m acc + m c * m₀ a = m₀ acc + m₀ c * m₀ a ∧ Outside [acc, c] m₀ m
  have hbody : ∀ n : ℕ, RunsTo (seq (addTo acc acc a) (subTo c c 9))
      (fun m => inv m ∧ m c ≠ 0 ∧ m c = n) (fun m' => inv m' ∧ m' c < n) (1 + 1) := by
    intro n
    refine runsTo_of_pointwise (fun m₁ => ?_)
    refine RunsTo.seq (mid := fun m => m = m₁.update acc (m₁ acc + m₁ a) ∧
        (inv m₁ ∧ m₁ c ≠ 0 ∧ m₁ c = n))
      (runsTo_addTo acc acc a (fun m hm => ⟨by rw [hm.1], hm.2⟩)) ?_
    refine runsTo_subTo c c 9 (fun m hm => ?_)
    obtain ⟨hm, ⟨i9, ia, ile, ieq, iout⟩, hne, hn⟩ := hm
    subst hm
    have e9 : (m₁.update acc (m₁ acc + m₁ a)) 9 = 1 := by
      rw [Mem.update_of_ne _ _ (Ne.symm h9a)]; exact i9
    have ec : (m₁.update acc (m₁ acc + m₁ a)) c = m₁ c := Mem.update_of_ne _ _ (Ne.symm hcc)
    refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · rw [Mem.update_of_ne _ _ (Ne.symm h9c)]; exact e9
    · rw [Mem.update_of_ne _ _ (Ne.symm hca), Mem.update_of_ne _ _ (Ne.symm hac)]; exact ia
    · rw [Mem.update_self, ec, e9]; omega
    · rw [Mem.update_of_ne _ _ hcc, Mem.update_self, Mem.update_self, ec, e9, ia]
      obtain ⟨k, hk⟩ : ∃ k, m₁ c = k + 1 := ⟨m₁ c - 1, by omega⟩
      rw [hk] at ieq ⊢
      rw [Nat.add_sub_cancel, ← ieq, Nat.succ_mul]
      ring
    · exact (iout.upd (by simp) _).upd (by simp) _
    · rw [Mem.update_self, ec, e9]; omega
  refine ((runsTo_whileNz (μ := fun m => m c) (N := m₀ c) hbody ?_).strengthen ?_).weaken ?_
  · rintro m ⟨-, -, ile, -, -⟩
    exact ile
  · rintro m rfl
    exact ⟨h9, rfl, le_rfl, rfl, Outside.refl _ _⟩
  · rintro m' ⟨⟨-, -, -, ieq, iout⟩, hc⟩
    refine ⟨?_, hc, iout⟩
    rw [hc, zero_mul, add_zero] at ieq
    exact ieq

/-- `R r ← R r · 2^{R c}`, by `R c` doublings (register `9` holds `1`). -/
def dbl (r c : ℕ) : Program := whileNz c (seq (addTo r r r) (subTo c c 9))

theorem runsTo_dbl (r c : ℕ) (hrc : r ≠ c) (h9r : r ≠ 9) (h9c : c ≠ 9) (m₀ : Mem)
    (h9 : m₀ 9 = 1) :
    RunsTo (dbl r c) (fun m => m = m₀)
      (fun m' => m' r = m₀ r * 2 ^ (m₀ c) ∧ m' c = 0 ∧ Outside [r, c] m₀ m')
      (m₀ c * (2 + 2) + 1) := by
  let inv : Mem → Prop := fun m => m 9 = 1 ∧ m c ≤ m₀ c ∧
    m r = m₀ r * 2 ^ (m₀ c - m c) ∧ Outside [r, c] m₀ m
  have hbody : ∀ n : ℕ, RunsTo (seq (addTo r r r) (subTo c c 9))
      (fun m => inv m ∧ m c ≠ 0 ∧ m c = n) (fun m' => inv m' ∧ m' c < n) (1 + 1) := by
    intro n
    refine runsTo_of_pointwise (fun m₁ => ?_)
    refine RunsTo.seq (mid := fun m => m = m₁.update r (m₁ r + m₁ r) ∧
        (inv m₁ ∧ m₁ c ≠ 0 ∧ m₁ c = n))
      (runsTo_addTo r r r (fun m hm => ⟨by rw [hm.1], hm.2⟩)) ?_
    refine runsTo_subTo c c 9 (fun m hm => ?_)
    obtain ⟨hm, ⟨i9, ile, ieq, iout⟩, hne, hn⟩ := hm
    subst hm
    have e9 : (m₁.update r (m₁ r + m₁ r)) 9 = 1 := by
      rw [Mem.update_of_ne _ _ (Ne.symm h9r)]; exact i9
    have ec : (m₁.update r (m₁ r + m₁ r)) c = m₁ c := Mem.update_of_ne _ _ (Ne.symm hrc)
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · rw [Mem.update_of_ne _ _ (Ne.symm h9c)]; exact e9
    · rw [Mem.update_self, ec, e9]; omega
    · rw [Mem.update_of_ne _ _ hrc, Mem.update_self, Mem.update_self, ec, e9, ieq]
      have hsub : m₀ c - (m₁ c - 1) = (m₀ c - m₁ c) + 1 := by omega
      rw [hsub, pow_succ]
      ring
    · exact (iout.upd (by simp) _).upd (by simp) _
    · rw [Mem.update_self, ec, e9]; omega
  refine ((runsTo_whileNz (μ := fun m => m c) (N := m₀ c) hbody ?_).strengthen ?_).weaken ?_
  · rintro m ⟨-, ile, -, -⟩
    exact ile
  · rintro m rfl
    exact ⟨h9, le_rfl, by simp, Outside.refl _ _⟩
  · rintro m' ⟨⟨-, -, ieq, iout⟩, hc⟩
    refine ⟨?_, hc, iout⟩
    rw [ieq, hc, Nat.sub_zero]

theorem wf_repAdd (acc a c : ℕ) (hac : acc ≠ a) (hcc : acc ≠ c) (hca : c ≠ a)
    (h9a : acc ≠ 9) (h9c : c ≠ 9) : Wf (repAdd acc a c) :=
  (runsTo_repAdd acc a c hac hcc hca h9a h9c (fun _ => 1) rfl).wf

/-- `Explicit.runsTo_repAdd` as a stage of a longer routine. -/
theorem stage_repAdd (acc a c : ℕ) (hac : acc ≠ a) (hcc : acc ≠ c) (hca : c ≠ a)
    (h9a : acc ≠ 9) (h9c : c ≠ 9) {P Q : Mem → Prop} {T : ℕ}
    (h9 : ∀ m, P m → m 9 = 1) (hT : ∀ m, P m → m c * 4 + 1 ≤ T)
    (hQ : ∀ m₁ m', P m₁ → m' acc = m₁ acc + m₁ c * m₁ a → m' c = 0 →
      Outside [acc, c] m₁ m' → Q m') :
    RunsTo (repAdd acc a c) P Q T := by
  refine runsTo_of_pointwise (fun m₁ => ?_)
  by_cases hP : P m₁
  · exact (((runsTo_repAdd acc a c hac hcc hca h9a h9c m₁ (h9 m₁ hP)).strengthen
      (fun m hm => hm.1)).weaken (fun m' h => hQ m₁ m' hP h.1 h.2.1 h.2.2)).mono (hT m₁ hP)
  · exact runsTo_of_false (wf_repAdd acc a c hac hcc hca h9a h9c) (fun m hm => hP hm.2)

theorem wf_dbl (r c : ℕ) (hrc : r ≠ c) (h9r : r ≠ 9) (h9c : c ≠ 9) : Wf (dbl r c) :=
  (runsTo_dbl r c hrc h9r h9c (fun _ => 1) rfl).wf

/-- `Explicit.runsTo_dbl` as a stage of a longer routine. -/
theorem stage_dbl (r c : ℕ) (hrc : r ≠ c) (h9r : r ≠ 9) (h9c : c ≠ 9) {P Q : Mem → Prop}
    {T : ℕ} (h9 : ∀ m, P m → m 9 = 1) (hT : ∀ m, P m → m c * 4 + 1 ≤ T)
    (hQ : ∀ m₁ m', P m₁ → m' r = m₁ r * 2 ^ (m₁ c) → m' c = 0 → Outside [r, c] m₁ m' → Q m') :
    RunsTo (dbl r c) P Q T := by
  refine runsTo_of_pointwise (fun m₁ => ?_)
  by_cases hP : P m₁
  · exact (((runsTo_dbl r c hrc h9r h9c m₁ (h9 m₁ hP)).strengthen
      (fun m hm => hm.1)).weaken (fun m' h => hQ m₁ m' hP h.1 h.2.1 h.2.2)).mono (hT m₁ hP)
  · exact runsTo_of_false (wf_dbl r c hrc h9r h9c) (fun m hm => hP hm.2)

/-! ## The routine -/

/-- The core of the step-count routine: input in register `1`, answer in register `2`,
scratch `2, …, 9`. -/
def countCore (K : ℕ) : Program :=
  seq (Arith.sizeTo 3 1 4) <|
  seq (assign 9 1) <| seq (subTo 3 3 9) <| seq (assign 8 2) <| seq (addTo 3 3 8) <|
  seq (assign 4 0) <| seq (copyTo 5 3) <| seq (repAdd 4 3 5) <|
  seq (assign 6 0) <| seq (copyTo 5 3) <| seq (repAdd 6 4 5) <|
  seq (assign 4 0) <| seq (copyTo 5 3) <| seq (repAdd 4 6 5) <|
  seq (assign 6 0) <| seq (copyTo 5 3) <| seq (repAdd 6 4 5) <|
  seq (assign 4 0) <| seq (assign 5 K) <| seq (repAdd 4 6 5) <|
  seq (assign 2 1) <| seq (dbl 2 4) <|
  seq (copyTo 3 2) <| seq (addTo 2 2 3) <| seq (addTo 2 2 3) (addTo 2 2 9)

theorem Outside.scratch_trans {m₀ m₁ m' : Mem} {S : List ℕ}
    (h1 : Outside Small.scratch m₀ m₁) (h2 : Outside S m₁ m')
    (hS : ∀ z ∈ S, z ∈ Small.scratch) : Outside Small.scratch m₀ m' :=
  fun z hz => by rw [h2 z (fun h => hz (hS z h)), h1 z hz]

set_option maxHeartbeats 1000000 in
theorem runsTo_countCore (K : ℕ) (m₀ : Mem) :
    RunsTo (countCore K) (fun m => m = m₀)
      (fun m' => m' 2 = 3 * 2 ^ (K * (Nat.size (m₀ 1) - 1 + 2) ^ 5) + 1 ∧
        Outside Small.scratch m₀ m')
      (6 * Nat.size (m₀ 1) + 16 * (Nat.size (m₀ 1) - 1 + 2) + 4 * K +
        4 * (K * (Nat.size (m₀ 1) - 1 + 2) ^ 5) + 31) := by
  set s := Nat.size (m₀ 1) with hs
  set L := s - 1 + 2 with hL
  set e := K * (L * (L * (L * (L * L)))) with he
  have hE : K * L ^ 5 = e := by rw [he]; ring
  rw [hE]
  have sc : ∀ z ∈ ([4, 5] : List ℕ), z ∈ Small.scratch := by decide
  have sc6 : ∀ z ∈ ([6, 5] : List ℕ), z ∈ Small.scratch := by decide
  have sc2 : ∀ z ∈ ([2, 4] : List ℕ), z ∈ Small.scratch := by decide
  have m3 : (3 : ℕ) ∈ Small.scratch := by decide
  refine RunsTo.mono (T := (6 * s + 6) + (1 + (1 + (1 + (1 + (1 + (1 + ((L * 4 + 1) + (1 + (1 + ((L * 4 + 1) + (1 + (1 + ((L * 4 + 1) + (1 + (1 + ((L * 4 + 1) + (1 + (1 + ((K * 4 + 1) + (1 + ((e * 4 + 1) + (1 + (1 + (1 + 1)))))))))))))))))))))))))
    ?_ (by omega)
  -- the bit length
  refine RunsTo.seq (mid := fun m => m 3 = s ∧ Outside Small.scratch m₀ m) ?_ ?_
  · refine (Arith.runsTo_sizeTo 3 1 4 (by omega) (by omega) (by omega) m₀).weaken ?_
    rintro m' ⟨h3, hout⟩
    exact ⟨h3, hout.mono (by decide)⟩
  -- `L = log₂ m + 2`
  refine RunsTo.seq (mid := fun m => m 9 = 1 ∧ m 3 = s ∧ Outside Small.scratch m₀ m)
    (runsTo_assign 9 1 fun m hm => ⟨by simp [Mem.update], by simp [Mem.update, hm.1],
      hm.2.upd (by decide) _⟩) ?_
  refine RunsTo.seq (mid := fun m => m 9 = 1 ∧ m 3 = s - 1 ∧ Outside Small.scratch m₀ m)
    (runsTo_subTo 3 3 9 fun m hm => ⟨by simp [Mem.update, hm.1], by simp [Mem.update, hm.1, hm.2.1],
      hm.2.2.upd (by decide) _⟩) ?_
  refine RunsTo.seq (mid := fun m => m 9 = 1 ∧ m 3 = s - 1 ∧ m 8 = 2 ∧
      Outside Small.scratch m₀ m)
    (runsTo_assign 8 2 fun m hm => ⟨by simp [Mem.update, hm.1], by simp [Mem.update, hm.2.1],
      by simp [Mem.update], hm.2.2.upd (by decide) _⟩) ?_
  refine RunsTo.seq (mid := fun m => m 9 = 1 ∧ m 3 = L ∧ Outside Small.scratch m₀ m)
    (runsTo_addTo 3 3 8 fun m hm => ⟨by simp [Mem.update, hm.1],
      by simp [Mem.update, hm.2.1, hm.2.2.1, hL], hm.2.2.2.upd (by decide) _⟩) ?_
  -- `L^2`
  refine RunsTo.seq (mid := fun m => m 9 = 1 ∧ m 3 = L ∧ m 4 = 0 ∧ Outside Small.scratch m₀ m)
    (runsTo_assign 4 0 fun m hm => ⟨by simp [Mem.update, hm.1], by simp [Mem.update, hm.2.1],
      by simp [Mem.update], hm.2.2.upd (by decide) _⟩) ?_
  refine RunsTo.seq (mid := fun m => m 9 = 1 ∧ m 3 = L ∧ m 4 = 0 ∧ m 5 = L ∧
      Outside Small.scratch m₀ m)
    (runsTo_copyTo 5 3 fun m hm => ⟨by simp [Mem.update, hm.1], by simp [Mem.update, hm.2.1],
      by simp [Mem.update, hm.2.2.1], by simp [Mem.update, hm.2.1],
      hm.2.2.2.upd (by decide) _⟩) ?_
  refine RunsTo.seq (mid := fun m => m 9 = 1 ∧ m 3 = L ∧ m 4 = L * L ∧
      Outside Small.scratch m₀ m)
    (stage_repAdd 4 3 5 (by omega) (by omega) (by omega) (by omega) (by omega) (T := L * 4 + 1)
      (fun m hm => hm.1) (fun m hm => by rw [hm.2.2.2.1]) fun m₁ m' hP ha hc hout => ?hq1) ?_
  case hq1 =>
    obtain ⟨h9, h3, h4, h5, ho⟩ := hP
    refine ⟨by rw [hout 9 (by decide), h9], by rw [hout 3 (by decide), h3], ?_,
      Outside.scratch_trans ho hout sc⟩
    rw [ha, h4, h5, h3]; ring
  -- `L^3`
  refine RunsTo.seq (mid := fun m => m 9 = 1 ∧ m 3 = L ∧ m 4 = L * L ∧ m 6 = 0 ∧
      Outside Small.scratch m₀ m)
    (runsTo_assign 6 0 fun m hm => ⟨by simp [Mem.update, hm.1], by simp [Mem.update, hm.2.1],
      by simp [Mem.update, hm.2.2.1], by simp [Mem.update], hm.2.2.2.upd (by decide) _⟩) ?_
  refine RunsTo.seq (mid := fun m => m 9 = 1 ∧ m 3 = L ∧ m 4 = L * L ∧ m 6 = 0 ∧ m 5 = L ∧
      Outside Small.scratch m₀ m)
    (runsTo_copyTo 5 3 fun m hm => ⟨by simp [Mem.update, hm.1], by simp [Mem.update, hm.2.1],
      by simp [Mem.update, hm.2.2.1], by simp [Mem.update, hm.2.2.2.1],
      by simp [Mem.update, hm.2.1], hm.2.2.2.2.upd (by decide) _⟩) ?_
  refine RunsTo.seq (mid := fun m => m 9 = 1 ∧ m 3 = L ∧ m 6 = L * (L * L) ∧
      Outside Small.scratch m₀ m)
    (stage_repAdd 6 4 5 (by omega) (by omega) (by omega) (by omega) (by omega) (T := L * 4 + 1)
      (fun m hm => hm.1) (fun m hm => by rw [hm.2.2.2.2.1]) fun m₁ m' hP ha hc hout => ?hq2) ?_
  case hq2 =>
    obtain ⟨h9, h3, h4, h6, h5, ho⟩ := hP
    refine ⟨by rw [hout 9 (by decide), h9], by rw [hout 3 (by decide), h3], ?_,
      Outside.scratch_trans ho hout sc6⟩
    rw [ha, h6, h5, h4, zero_add]
  -- `L^4`
  refine RunsTo.seq (mid := fun m => m 9 = 1 ∧ m 3 = L ∧ m 6 = L * (L * L) ∧ m 4 = 0 ∧
      Outside Small.scratch m₀ m)
    (runsTo_assign 4 0 fun m hm => ⟨by simp [Mem.update, hm.1], by simp [Mem.update, hm.2.1],
      by simp [Mem.update, hm.2.2.1], by simp [Mem.update], hm.2.2.2.upd (by decide) _⟩) ?_
  refine RunsTo.seq (mid := fun m => m 9 = 1 ∧ m 3 = L ∧ m 6 = L * (L * L) ∧ m 4 = 0 ∧
      m 5 = L ∧ Outside Small.scratch m₀ m)
    (runsTo_copyTo 5 3 fun m hm => ⟨by simp [Mem.update, hm.1], by simp [Mem.update, hm.2.1],
      by simp [Mem.update, hm.2.2.1], by simp [Mem.update, hm.2.2.2.1],
      by simp [Mem.update, hm.2.1], hm.2.2.2.2.upd (by decide) _⟩) ?_
  refine RunsTo.seq (mid := fun m => m 9 = 1 ∧ m 3 = L ∧ m 4 = L * (L * (L * L)) ∧
      Outside Small.scratch m₀ m)
    (stage_repAdd 4 6 5 (by omega) (by omega) (by omega) (by omega) (by omega) (T := L * 4 + 1)
      (fun m hm => hm.1) (fun m hm => by rw [hm.2.2.2.2.1]) fun m₁ m' hP ha hc hout => ?hq3) ?_
  case hq3 =>
    obtain ⟨h9, h3, h6, h4, h5, ho⟩ := hP
    refine ⟨by rw [hout 9 (by decide), h9], by rw [hout 3 (by decide), h3], ?_,
      Outside.scratch_trans ho hout sc⟩
    rw [ha, h4, h5, h6]; ring
  -- `L^5`
  refine RunsTo.seq (mid := fun m => m 9 = 1 ∧ m 3 = L ∧ m 4 = L * (L * (L * L)) ∧ m 6 = 0 ∧
      Outside Small.scratch m₀ m)
    (runsTo_assign 6 0 fun m hm => ⟨by simp [Mem.update, hm.1], by simp [Mem.update, hm.2.1],
      by simp [Mem.update, hm.2.2.1], by simp [Mem.update], hm.2.2.2.upd (by decide) _⟩) ?_
  refine RunsTo.seq (mid := fun m => m 9 = 1 ∧ m 3 = L ∧ m 4 = L * (L * (L * L)) ∧ m 6 = 0 ∧
      m 5 = L ∧ Outside Small.scratch m₀ m)
    (runsTo_copyTo 5 3 fun m hm => ⟨by simp [Mem.update, hm.1], by simp [Mem.update, hm.2.1],
      by simp [Mem.update, hm.2.2.1], by simp [Mem.update, hm.2.2.2.1],
      by simp [Mem.update, hm.2.1], hm.2.2.2.2.upd (by decide) _⟩) ?_
  refine RunsTo.seq (mid := fun m => m 9 = 1 ∧ m 6 = L * (L * (L * (L * L))) ∧
      Outside Small.scratch m₀ m)
    (stage_repAdd 6 4 5 (by omega) (by omega) (by omega) (by omega) (by omega) (T := L * 4 + 1)
      (fun m hm => hm.1) (fun m hm => by rw [hm.2.2.2.2.1]) fun m₁ m' hP ha hc hout => ?hq4) ?_
  case hq4 =>
    obtain ⟨h9, h3, h4, h6, h5, ho⟩ := hP
    refine ⟨by rw [hout 9 (by decide), h9], ?_, Outside.scratch_trans ho hout sc6⟩
    rw [ha, h6, h5, h4, zero_add]
  -- `e = K L^5`
  refine RunsTo.seq (mid := fun m => m 9 = 1 ∧ m 6 = L * (L * (L * (L * L))) ∧ m 4 = 0 ∧
      Outside Small.scratch m₀ m)
    (runsTo_assign 4 0 fun m hm => ⟨by simp [Mem.update, hm.1], by simp [Mem.update, hm.2.1],
      by simp [Mem.update], hm.2.2.upd (by decide) _⟩) ?_
  refine RunsTo.seq (mid := fun m => m 9 = 1 ∧ m 6 = L * (L * (L * (L * L))) ∧ m 4 = 0 ∧
      m 5 = K ∧ Outside Small.scratch m₀ m)
    (runsTo_assign 5 K fun m hm => ⟨by simp [Mem.update, hm.1], by simp [Mem.update, hm.2.1],
      by simp [Mem.update, hm.2.2.1], by simp [Mem.update], hm.2.2.2.upd (by decide) _⟩) ?_
  refine RunsTo.seq (mid := fun m => m 9 = 1 ∧ m 4 = e ∧ Outside Small.scratch m₀ m)
    (stage_repAdd 4 6 5 (by omega) (by omega) (by omega) (by omega) (by omega) (T := K * 4 + 1)
      (fun m hm => hm.1) (fun m hm => by rw [hm.2.2.2.1]) fun m₁ m' hP ha hc hout => ?hq5) ?_
  case hq5 =>
    obtain ⟨h9, h6, h4, h5, ho⟩ := hP
    refine ⟨by rw [hout 9 (by decide), h9], ?_, Outside.scratch_trans ho hout sc⟩
    rw [ha, h4, h5, h6, he]; ring
  -- `2^e`
  refine RunsTo.seq (mid := fun m => m 9 = 1 ∧ m 4 = e ∧ m 2 = 1 ∧ Outside Small.scratch m₀ m)
    (runsTo_assign 2 1 fun m hm => ⟨by simp [Mem.update, hm.1], by simp [Mem.update, hm.2.1],
      by simp [Mem.update], hm.2.2.upd (by decide) _⟩) ?_
  refine RunsTo.seq (mid := fun m => m 9 = 1 ∧ m 2 = 2 ^ e ∧ Outside Small.scratch m₀ m)
    (stage_dbl 2 4 (by omega) (by omega) (by omega) (T := e * 4 + 1)
      (fun m hm => hm.1) (fun m hm => by rw [hm.2.1]) fun m₁ m' hP ha hc hout => ?hq6) ?_
  case hq6 =>
    obtain ⟨h9, h4, h2, ho⟩ := hP
    refine ⟨by rw [hout 9 (by decide), h9], ?_, Outside.scratch_trans ho hout sc2⟩
    rw [ha, h2, h4, one_mul]
  -- `3·2^e + 1`
  refine RunsTo.seq (mid := fun m => m 9 = 1 ∧ m 2 = 2 ^ e ∧ m 3 = 2 ^ e ∧
      Outside Small.scratch m₀ m)
    (runsTo_copyTo 3 2 fun m hm => ⟨by simp [Mem.update, hm.1], by simp [Mem.update, hm.2.1],
      by simp [Mem.update, hm.2.1], hm.2.2.upd (by decide) _⟩) ?_
  refine RunsTo.seq (mid := fun m => m 9 = 1 ∧ m 2 = 2 * 2 ^ e ∧ m 3 = 2 ^ e ∧
      Outside Small.scratch m₀ m)
    (runsTo_addTo 2 2 3 fun m hm => ⟨by simp [Mem.update, hm.1],
      by simp [Mem.update, hm.2.1, hm.2.2.1]; ring, by simp [Mem.update, hm.2.2.1],
      hm.2.2.2.upd (by decide) _⟩) ?_
  refine RunsTo.seq (mid := fun m => m 9 = 1 ∧ m 2 = 3 * 2 ^ e ∧
      Outside Small.scratch m₀ m)
    (runsTo_addTo 2 2 3 fun m hm => ⟨by simp [Mem.update, hm.1],
      by simp [Mem.update, hm.2.1, hm.2.2.1]; ring, hm.2.2.2.upd (by decide) _⟩) ?_
  exact runsTo_addTo 2 2 9 fun m hm => ⟨by simp [Mem.update, hm.1, hm.2.1],
    hm.2.2.upd (by decide) _⟩

/-! ## The packaged routine -/

/-- The step-count routine at the top-level convention. -/
def countProg (K : ℕ) : Program :=
  seq (countCore K) (seq (copyTo 1 2) (seq (assign 0 1) (Small.clearRegs Small.scratch)))

/-- The time constant of the step count at the workspace convention. -/
def countTime (K : ℕ) : ℕ := 80 * K + 634

theorem cleanCompute_countE (K : ℕ) :
    CleanCompute (countProg K) (countE K) (fun N => (8 * K + 63) * (N + 1) ^ 5) := by
  refine Small.cleanCompute_unary (f := countE K) (v := countE K)
    (T := fun a => 6 * Nat.size a + 16 * (Nat.size a - 1 + 2) + 4 * K +
      4 * (K * (Nat.size a - 1 + 2) ^ 5) + 31) (S := Small.scratch)
    (fun a => rfl) (fun m₀ => ?_) (fun i hi => hi) (fun a => ?_)
  · refine (runsTo_countCore K m₀).weaken ?_
    rintro m' ⟨h2, hout⟩
    refine ⟨?_, hout⟩
    rw [h2, countE, Small.log_two_eq_size_sub_one]
  · rw [Small.size_nat]
    dsimp only
    set s := Nat.size a
    set P := (s + 2 + 1) ^ 5 with hP
    have h1 : s + 2 + 1 ≤ P := by
      rw [hP]
      exact Nat.le_self_pow (by norm_num) _
    have h2 : (s - 1 + 2) ^ 5 ≤ P := Nat.pow_le_pow_left (by omega) 5
    have h3 : K * (s - 1 + 2) ^ 5 ≤ K * P := Nat.mul_le_mul_left K h2
    have h4 : K ≤ K * P := Nat.le_mul_of_pos_right K (by omega)
    have h5 : (8 * K + 63) * P = 8 * (K * P) + 63 * P := by ring
    omega

/-- **The step count at the workspace convention**, in time `(80K + 634)(N+1)^5`. -/
theorem cleanComputeAt_countE (K : ℕ) :
    CleanComputeAt 16 (relocAt 16 (countProg K)) (countE K)
      (fun N => countTime K * (N + 1) ^ 5) := by
  intro a
  refine (cleanComputeAt_of_cleanCompute (K := 16) (by norm_num) (cleanCompute_countE K) a).mono ?_
  dsimp only
  have h1 : 1 ≤ (Enc.size a + 1) ^ 5 := Nat.one_le_pow _ _ (by omega)
  have h5 : countTime K * (Enc.size a + 1) ^ 5 =
      10 * ((8 * K + 63) * (Enc.size a + 1) ^ 5) + 4 * (Enc.size a + 1) ^ 5 := by
    unfold countTime; ring
  omega

/-- The step count is short: `K (log₂ m + 2)^5 + 5` bits and brackets. -/
theorem size_countE_le (K a : ℕ) : Enc.size (countE K a) ≤ (K + 5) * (Enc.size a + 1) ^ 5 := by
  rw [Small.size_nat, Small.size_nat]
  set e := K * (Nat.log 2 a + 2) ^ 5
  have hlt : countE K a < 2 ^ (e + 3) := by
    have h4 : (2 : ℕ) ^ (e + 3) = 8 * 2 ^ e := by rw [pow_add]; ring
    have : 1 ≤ 2 ^ e := Nat.one_le_two_pow
    have hc : countE K a = 3 * 2 ^ e + 1 := rfl
    omega
  have hs : Nat.size (countE K a) ≤ e + 3 := Nat.size_le.2 hlt
  have hlog : Nat.log 2 a + 2 ≤ Nat.size a + 2 + 1 := by
    rw [Small.log_two_eq_size_sub_one]; omega
  have he : e ≤ K * (Nat.size a + 2 + 1) ^ 5 :=
    Nat.mul_le_mul_left K (Nat.pow_le_pow_left hlog 5)
  have h1 : 1 ≤ (Nat.size a + 2 + 1) ^ 5 := Nat.one_le_pow _ _ (by omega)
  have h5 : (K + 5) * (Nat.size a + 2 + 1) ^ 5 =
      K * (Nat.size a + 2 + 1) ^ 5 + 5 * (Nat.size a + 2 + 1) ^ 5 := by ring
  omega

end Explicit
