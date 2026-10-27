import Workspace.Machine.Layout

/-!
# The bridge down: from the workspace convention to the output convention

`Workspace/Machine/Reloc.lean` carries a routine of the top-level convention up to the workspace
convention `initMemAt K`.  This file builds the other direction, in the form the final theorem
needs: a program `down` that turns the memory `initMemAt 16 l` into a memory holding `l` in the
*output* convention of `Workspace/Machine/Encoding.lean`.

Going down is not symmetric to going up.  The block `[K, K + n]` has to be moved to `[0, n]`,
and a copy loop needs a few registers of its own, which the move then overwrites.  Those few
registers have to be saved somewhere above the data and read back at the end, and reading a
saved value back costs registers too: an indirect load needs a pointer register, and stepping
the pointer needs a register holding the step.  The trick that removes the second cost is to
park the saved values at the addresses `A, 2A, 4A, 8A, ...`: stepping the pointer is then
`add 0 0 0`, which needs no second register, so one single register does the whole read-back.
This is `parkStep` / `unparkStep` below.

## The program

* `downPark` computes `S = 24 + n` into register `0` and parks the contents of the registers
  `21, 20, 19, 18, 17, 16` at `S, 2S, 4S, 8S, 16S, 32S`.  All these addresses lie above
  `16 + n`, the top of the data, so nothing live is destroyed.
* `downSetup` puts `S` back into register `5` and sets the copy loop going: register `0` is the
  destination pointer (from `6`), register `1` the source pointer (from `22 = 16 + 6`),
  register `3` the constant `1`, register `4` the counter `n - 5`.
* `downLoop` copies `mem[a] := mem[16 + a]` for `a = 6, ..., n`, in increasing order, which is
  correct for the overlapping downward move.  It writes only at addresses `6` and above, so the
  registers `0, ..., 5` survive it.
* `downRead` puts `S` back into register `0` and reads the six parked values back into the
  registers `5, 4, 3, 2, 1, 0`, doubling the pointer between two reads.

`OutputAt` inspects only the registers `0, ..., n`, so the garbage left above them — the parked
values and the old copy of the block — is allowed.

## Main results

* `RAM.Bridge.runsTo_down`: the specification of `down`, for an arbitrary starting memory whose
  register `16` holds `n`;
* `RAM.Bridge.runsTo_down_outputAt`: its form at the workspace convention, `7 * n + 34` steps.
-/

namespace RAM

/-- Outside the input block the initial memory is zero. -/
theorem initMem_eq_zero_of_gt {l : List ℕ} {x : ℕ} (h : l.length < x) : initMem l x = 0 := by
  unfold initMem
  rw [if_neg (by omega)]
  exact List.getD_eq_default _ _ (by omega)

/-- Above the work registers, the workspace memory is the initial memory shifted down. -/
theorem initMemAt_of_ge {K : ℕ} (l : List ℕ) {a : ℕ} (h : K ≤ a) :
    initMemAt K l a = initMem l (a - K) := by
  simp only [initMemAt, if_neg (by omega : ¬ a < K)]

namespace Bridge

/-! ## Parking a register, and reading it back -/

/-- Store the contents of register `r` at the address held in register `0`, then double
register `0`.  Two steps, and no register besides `0` and `r` is touched. -/
def parkStep (r : ℕ) : Program := seq (storeTo 0 r) (addTo 0 0 0)

/-- `parkRun rs k` parks the registers `rs 0, ..., rs (k-1)` at the addresses
`A, 2A, 4A, ...`, where `A` is the value register `0` starts with. -/
def parkRun (rs : ℕ → ℕ) : ℕ → Program
  | 0 => []
  | k + 1 => seq (parkRun rs k) (parkStep (rs k))

/-- The state reached after `k` parking steps from a memory `M` whose register `0` holds `A`. -/
def ParkedAt (M : Mem) (A : ℕ) (rs : ℕ → ℕ) (k : ℕ) (m : Mem) : Prop :=
  m 0 = 2 ^ k * A ∧ (∀ j < k, m (2 ^ j * A) = M (rs j)) ∧
    (∀ z, z ≠ 0 → (∀ j < k, z ≠ 2 ^ j * A) → m z = M z)

theorem le_two_pow_mul (j A : ℕ) : A ≤ 2 ^ j * A :=
  Nat.le_mul_of_pos_left _ (Nat.two_pow_pos j)

theorem two_pow_mul_lt {j k : ℕ} (h : j < k) {A : ℕ} (hA : 0 < A) :
    2 ^ j * A < 2 ^ k * A := by
  have h2 : (2:ℕ) ^ j < 2 ^ k := Nat.pow_lt_pow_right (by norm_num) h
  exact Nat.mul_lt_mul_of_lt_of_le h2 (le_refl A) hA

/-- **One parking step.** -/
theorem runsTo_parkStep {M : Mem} {A : ℕ} {rs : ℕ → ℕ} {k : ℕ} (hA : 0 < A)
    (hr0 : 0 < rs k) (hrA : rs k < A) :
    RunsTo (parkStep (rs k)) (ParkedAt M A rs k) (ParkedAt M A rs (k + 1)) 2 := by
  have hge : ∀ j, A ≤ 2 ^ j * A := fun j => le_two_pow_mul j A
  have hpos : ∀ j, 0 < 2 ^ j * A := fun j => lt_of_lt_of_le hA (hge j)
  refine RunsTo.mono (T := 1 + 1) ?_ (le_refl _)
  refine runsTo_of_pointwise (fun m₁ => ?_)
  refine RunsTo.seq (mid := fun m => m = m₁.update (m₁ 0) (m₁ (rs k)) ∧ ParkedAt M A rs k m₁)
    (runsTo_storeTo 0 (rs k) (fun m hm => ⟨by rw [hm.1], hm.2⟩)) ?_
  refine runsTo_addTo 0 0 0 (fun m hm => ?_)
  obtain ⟨hme, hz0, hpk, hfr⟩ := hm
  subst hme
  have hval : m₁ (rs k) = M (rs k) :=
    hfr _ (by omega) (fun j _ => by have := hge j; omega)
  have hne0 : (0:ℕ) ≠ m₁ 0 := by rw [hz0]; have := hpos k; omega
  have h00 : (m₁.update (m₁ 0) (m₁ (rs k))) 0 = 2 ^ k * A := by
    rw [Mem.update_of_ne _ _ hne0, hz0]
  rw [h00]
  refine ⟨?_, ?_, ?_⟩
  · rw [Mem.update_self]; ring
  · intro j hj
    rcases Nat.lt_or_ge j k with h | h
    · have hlt : 2 ^ j * A < 2 ^ k * A := two_pow_mul_lt h hA
      rw [Mem.update_of_ne _ _ (by have := hpos j; omega),
        Mem.update_of_ne _ _ (by rw [hz0]; omega)]
      exact hpk j h
    · have hjk : j = k := by omega
      subst hjk
      rw [Mem.update_of_ne _ _ (by have := hpos j; omega), ← hz0, Mem.update_self, hval]
  · intro z hz0' hzj
    have h1 : z ≠ 2 ^ k * A := hzj k (by omega)
    rw [Mem.update_of_ne _ _ hz0', Mem.update_of_ne _ _ (by rw [hz0]; omega)]
    exact hfr z hz0' (fun j hj => hzj j (by omega))

theorem wf_parkRun (rs : ℕ → ℕ) (k : ℕ) : Wf (parkRun rs k) := by
  induction k with
  | zero => intro i hi; exact absurd hi (by simp [parkRun])
  | succ k ih =>
      exact wf_seq ih (wf_seq (Layout.wf_storeTo _ _) (Layout.wf_addTo _ _ _))

/-- **The parking phase.** -/
theorem runsTo_parkRun {M : Mem} {A : ℕ} {rs : ℕ → ℕ} (hA : 0 < A) :
    ∀ k, (∀ j < k, 0 < rs j ∧ rs j < A) →
      RunsTo (parkRun rs k) (ParkedAt M A rs 0) (ParkedAt M A rs k) (2 * k) := by
  intro k
  induction k with
  | zero => exact fun _ => runsTo_nil (fun _ hm => hm)
  | succ k ih =>
      intro h
      refine RunsTo.mono (T := 2 * k + 2) ?_ (by omega)
      exact (ih (fun j hj => h j (by omega))).seq
        (runsTo_parkStep hA (h k (by omega)).1 (h k (by omega)).2)

/-- Read the value at the address held in register `0` into register `x`, then double
register `0`. -/
def unparkStep (x : ℕ) : Program := seq (loadTo x 0) (addTo 0 0 0)

/-- `unparkRun rs k` reads the values at `A, 2A, ..., 2^(k-1) A` into the registers
`rs 0, ..., rs (k-1)`. -/
def unparkRun (rs : ℕ → ℕ) : ℕ → Program
  | 0 => []
  | k + 1 => seq (unparkRun rs k) (unparkStep (rs k))

/-- The state reached after `k` read-back steps from a memory `M` whose register `0` holds
`A`. -/
def UnparkedAt (M : Mem) (A : ℕ) (rs : ℕ → ℕ) (k : ℕ) (m : Mem) : Prop :=
  m 0 = 2 ^ k * A ∧ (∀ j < k, m (rs j) = M (2 ^ j * A)) ∧
    (∀ z, z ≠ 0 → (∀ j < k, z ≠ rs j) → m z = M z)

/-- **One read-back step.** -/
theorem runsTo_unparkStep {M : Mem} {A : ℕ} {rs : ℕ → ℕ} {k : ℕ} (hA : 0 < A)
    (hr : ∀ j ≤ k, 0 < rs j ∧ rs j < A) (hinj : ∀ j < k, rs j ≠ rs k) :
    RunsTo (unparkStep (rs k)) (UnparkedAt M A rs k) (UnparkedAt M A rs (k + 1)) 2 := by
  have hge : ∀ j, A ≤ 2 ^ j * A := fun j => le_two_pow_mul j A
  have hpos : ∀ j, 0 < 2 ^ j * A := fun j => lt_of_lt_of_le hA (hge j)
  refine RunsTo.mono (T := 1 + 1) ?_ (le_refl _)
  refine runsTo_of_pointwise (fun m₁ => ?_)
  refine RunsTo.seq
    (mid := fun m => m = m₁.update (rs k) (m₁ (m₁ 0)) ∧ UnparkedAt M A rs k m₁)
    (runsTo_loadTo (rs k) 0 (fun m hm => ⟨by rw [hm.1], hm.2⟩)) ?_
  refine runsTo_addTo 0 0 0 (fun m hm => ?_)
  obtain ⟨hme, hz0, hpk, hfr⟩ := hm
  subst hme
  have hval : m₁ (m₁ 0) = M (2 ^ k * A) := by
    rw [hz0]
    exact hfr _ (by have := hpos k; omega)
      (fun j hj => by have := hge k; have := (hr j (by omega)).2; omega)
  have h00 : (m₁.update (rs k) (m₁ (m₁ 0))) 0 = 2 ^ k * A := by
    rw [Mem.update_of_ne _ _ (by have := (hr k (le_refl k)).1; omega), hz0]
  rw [h00]
  refine ⟨?_, ?_, ?_⟩
  · rw [Mem.update_self]; ring
  · intro j hj
    rcases Nat.lt_or_ge j k with h | h
    · rw [Mem.update_of_ne _ _ (by have := (hr j (by omega)).1; omega),
        Mem.update_of_ne _ _ (hinj j h)]
      exact hpk j h
    · have hjk : j = k := by omega
      subst hjk
      rw [Mem.update_of_ne _ _ (by have := (hr j (le_refl j)).1; omega), Mem.update_self, hval]
  · intro z hz0' hzj
    rw [Mem.update_of_ne _ _ hz0', Mem.update_of_ne _ _ (hzj k (by omega))]
    exact hfr z hz0' (fun j hj => hzj j (by omega))

theorem wf_unparkRun (rs : ℕ → ℕ) (k : ℕ) : Wf (unparkRun rs k) := by
  induction k with
  | zero => intro i hi; exact absurd hi (by simp [unparkRun])
  | succ k ih =>
      exact wf_seq ih (wf_seq (Layout.wf_loadTo _ _) (Layout.wf_addTo _ _ _))

/-- **The read-back phase.** -/
theorem runsTo_unparkRun {M : Mem} {A : ℕ} {rs : ℕ → ℕ} (hA : 0 < A) :
    ∀ k, (∀ j < k, 0 < rs j ∧ rs j < A) → (∀ i j, i < j → j < k → rs i ≠ rs j) →
      RunsTo (unparkRun rs k) (UnparkedAt M A rs 0) (UnparkedAt M A rs k) (2 * k) := by
  intro k
  induction k with
  | zero => exact fun _ _ => runsTo_nil (fun _ hm => hm)
  | succ k ih =>
      intro h hinj
      refine RunsTo.mono (T := 2 * k + 2) ?_ (by omega)
      refine (ih (fun j hj => h j (by omega))
        (fun i j hij hjk => hinj i j hij (by omega))).seq ?_
      exact runsTo_unparkStep hA (fun j hj => h j (by omega))
        (fun j hj => hinj j k hj (by omega))

/-! ## The program `down` -/

/-- The registers parked by `downPark`: `21, 20, 19, 18, 17, 16`. -/
def downRegs (j : ℕ) : ℕ := 21 - j

/-- The registers filled by `downRead`: `5, 4, 3, 2, 1`. -/
def downBack (j : ℕ) : ℕ := 5 - j

/-- Compute `S = 24 + n` into register `0` and park the six registers `16, ..., 21`. -/
def downPark : Program :=
  seq (assign 0 24) (seq (addTo 0 0 16) (parkRun downRegs 6))

/-- Set up the copy loop: `S` in register `5`, the destination pointer in register `0`, the
source pointer in register `1`, the constant `1` in register `3`, the counter in register `4`. -/
def downSetup : Program :=
  seq (assign 5 24) (seq (addTo 5 5 16) (seq (assign 0 6) (seq (assign 1 22)
    (seq (assign 3 1) (seq (assign 4 5) (subTo 4 16 4))))))

/-- One entry of the downward move. -/
def downBody : Program :=
  seq (loadTo 2 1) (seq (storeTo 0 2) (seq (addTo 0 0 3) (seq (addTo 1 1 3) (subTo 4 4 3))))

/-- The downward move of the block `[22, 16 + n]` to `[6, n]`. -/
def downLoop : Program := whileNz 4 downBody

/-- Read the six parked values back into the registers `5, 4, 3, 2, 1, 0`. -/
def downRead : Program :=
  seq (copyTo 0 5) (seq (unparkRun downBack 5) (loadTo 0 0))

/-- **The bridge down.**  From `initMemAt 16 l` to a memory holding `l` in the output
convention. -/
def down : Program := seq downPark (seq downSetup (seq downLoop downRead))

/-! ## The specification -/

section

variable {M : Mem} {n : ℕ}

/-- The invariant of the downward move: `t` entries have been moved. -/
def DownInv (M : Mem) (n S : ℕ) (m : Mem) : Prop :=
  ∃ t, t ≤ n - 5 ∧ m 0 = 6 + t ∧ m 1 = 22 + t ∧ m 3 = 1 ∧ m 4 = (n - 5) - t ∧ m 5 = S ∧
    (∀ j < 6, m (2 ^ j * S) = M (downRegs j)) ∧
    (∀ i < t, m (6 + i) = M (22 + i)) ∧
    (∀ z, 6 + t ≤ z → (∀ j < 6, z ≠ 2 ^ j * S) → m z = M z)

theorem runsTo_downPark (hM16 : M 16 = n) :
    RunsTo downPark (fun m => m = M) (ParkedAt M (24 + n) downRegs 6) 14 := by
  have hA : 0 < 24 + n := by omega
  refine RunsTo.mono (T := 1 + (1 + 2 * 6)) ?_ (by norm_num)
  refine RunsTo.seq (mid := fun m => m = M.update 0 24)
    (runsTo_assign 0 24 (fun m hm => by rw [hm])) ?_
  refine RunsTo.seq (mid := ParkedAt M (24 + n) downRegs 0) ?_ ?_
  · refine runsTo_addTo 0 0 16 (fun m hm => ?_)
    subst hm
    have h16 : (M.update 0 24) 16 = n := by rw [Mem.update_of_ne _ _ (by omega), hM16]
    rw [Mem.update_self, h16]
    refine ⟨by rw [Mem.update_self]; ring, by intro j hj; omega, ?_⟩
    intro z hz _
    rw [Mem.update_of_ne _ _ hz, Mem.update_of_ne _ _ hz]
  · exact runsTo_parkRun hA 6
      (fun j hj => ⟨by simp only [downRegs]; omega, by simp only [downRegs]; omega⟩)

theorem runsTo_downSetup (hM16 : M 16 = n) :
    RunsTo downSetup (ParkedAt M (24 + n) downRegs 6) (DownInv M n (24 + n)) 7 := by
  have hge : ∀ j, 24 + n ≤ 2 ^ j * (24 + n) := fun j => le_two_pow_mul j (24 + n)
  refine ⟨wf_seq (Layout.wf_assign _ _) (wf_seq (Layout.wf_addTo _ _ _)
    (wf_seq (Layout.wf_assign _ _) (wf_seq (Layout.wf_assign _ _)
      (wf_seq (Layout.wf_assign _ _) (wf_seq (Layout.wf_assign _ _)
        (Layout.wf_subTo _ _ _)))))), ?_⟩
  intro m₀ hm₀
  obtain ⟨hz0, hpk, hfr⟩ := hm₀
  have h16 : m₀ 16 = M 16 := hfr 16 (by omega) (fun j _ => by have := hge j; omega)
  refine (?_ : RunsTo downSetup (fun m => m = m₀) (DownInv M n (24 + n)) 7).spec m₀ rfl
  refine RunsTo.mono (T := 1 + (1 + (1 + (1 + (1 + (1 + 1)))))) ?_ (by norm_num)
  refine RunsTo.seq (mid := fun m => m = m₀.update 5 24)
    (runsTo_assign 5 24 (fun m hm => by rw [hm])) ?_
  set u1 : Mem := m₀.update 5 24 with hu1
  have hu116 : u1 5 + u1 16 = 24 + n := by
    rw [hu1, Mem.update_self, Mem.update_of_ne _ _ (by omega), h16, hM16]
  refine RunsTo.seq (mid := fun m => m = u1.update 5 (24 + n))
    (runsTo_addTo 5 5 16 (fun m hm => by rw [hm, hu116])) ?_
  set u2 : Mem := u1.update 5 (24 + n) with hu2
  refine RunsTo.seq (mid := fun m => m = u2.update 0 6)
    (runsTo_assign 0 6 (fun m hm => by rw [hm])) ?_
  set u3 : Mem := u2.update 0 6 with hu3
  refine RunsTo.seq (mid := fun m => m = u3.update 1 22)
    (runsTo_assign 1 22 (fun m hm => by rw [hm])) ?_
  set u4 : Mem := u3.update 1 22 with hu4
  refine RunsTo.seq (mid := fun m => m = u4.update 3 1)
    (runsTo_assign 3 1 (fun m hm => by rw [hm])) ?_
  set u5 : Mem := u4.update 3 1 with hu5
  refine RunsTo.seq (mid := fun m => m = u5.update 4 5)
    (runsTo_assign 4 5 (fun m hm => by rw [hm])) ?_
  set u6 : Mem := u5.update 4 5 with hu6
  refine runsTo_subTo 4 16 4 (fun m hm => ?_)
  subst hm
  -- the frame of the whole block
  have hframe : ∀ z, z ≠ 0 → z ≠ 1 → z ≠ 3 → z ≠ 4 → z ≠ 5 → u6 z = m₀ z := by
    intro z h0 h1 h3 h4 h5
    simp only [hu6, hu5, hu4, hu3, hu2, hu1, Mem.update, if_neg h0, if_neg h1, if_neg h3,
      if_neg h4, if_neg h5]
  have h6_16 : u6 16 = n := by rw [hframe 16 (by omega) (by omega) (by omega) (by omega)
    (by omega), h16, hM16]
  have h6_4 : u6 4 = 5 := by rw [hu6, Mem.update_self]
  have h6_0 : u6 0 = 6 := by
    simp only [hu6, hu5, hu4, hu3, Mem.update, if_neg (by omega : (0:ℕ) ≠ 4),
      if_neg (by omega : (0:ℕ) ≠ 3), if_neg (by omega : (0:ℕ) ≠ 1)]
    simp
  have h6_1 : u6 1 = 22 := by
    simp only [hu6, hu5, hu4, Mem.update, if_neg (by omega : (1:ℕ) ≠ 4),
      if_neg (by omega : (1:ℕ) ≠ 3)]
    simp
  have h6_3 : u6 3 = 1 := by
    simp only [hu6, hu5, Mem.update, if_neg (by omega : (3:ℕ) ≠ 4)]
    simp
  have h6_5 : u6 5 = 24 + n := by
    simp only [hu6, hu5, hu4, hu3, hu2, Mem.update, if_neg (by omega : (5:ℕ) ≠ 4),
      if_neg (by omega : (5:ℕ) ≠ 3), if_neg (by omega : (5:ℕ) ≠ 1),
      if_neg (by omega : (5:ℕ) ≠ 0)]
    simp
  rw [h6_16, h6_4]
  refine ⟨0, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Mem.update_of_ne _ _ (by omega), h6_0]
  · rw [Mem.update_of_ne _ _ (by omega), h6_1]
  · rw [Mem.update_of_ne _ _ (by omega), h6_3]
  · rw [Mem.update_self]; omega
  · rw [Mem.update_of_ne _ _ (by omega), h6_5]
  · intro j hj
    have := hge j
    rw [Mem.update_of_ne _ _ (by omega),
      hframe _ (by omega) (by omega) (by omega) (by omega) (by omega)]
    exact hpk j hj
  · intro i hi; omega
  · intro z hz hzj
    rw [Mem.update_of_ne _ _ (by omega),
      hframe _ (by omega) (by omega) (by omega) (by omega) (by omega)]
    exact hfr z (by omega) hzj

theorem runsTo_downBody (hM16 : M 16 = n) (t' : ℕ) :
    RunsTo downBody (fun m => DownInv M n (24 + n) m ∧ m 4 = t' + 1)
      (fun m' => DownInv M n (24 + n) m' ∧ m' 4 = t') 5 := by
  have hge : ∀ j, 24 + n ≤ 2 ^ j * (24 + n) := fun j => le_two_pow_mul j (24 + n)
  refine ⟨wf_seq (Layout.wf_loadTo _ _) (wf_seq (Layout.wf_storeTo _ _)
    (wf_seq (Layout.wf_addTo _ _ _) (wf_seq (Layout.wf_addTo _ _ _)
      (Layout.wf_subTo _ _ _)))), ?_⟩
  intro m₁ hm₁
  obtain ⟨⟨t, htn, e0, e1, e3, e4, e5, epk, ewr, efr⟩, hc⟩ := hm₁
  have htlt : t < n - 5 := by omega
  have hsrc : m₁ (22 + t) = M (22 + t) :=
    efr _ (by omega) (fun j _ => by have := hge j; omega)
  refine (?_ : RunsTo downBody (fun m => m = m₁)
    (fun m' => DownInv M n (24 + n) m' ∧ m' 4 = t') 5).spec m₁ rfl
  refine RunsTo.mono (T := 1 + (1 + (1 + (1 + 1)))) ?_ (by norm_num)
  refine RunsTo.seq (mid := fun m => m = m₁.update 2 (M (22 + t)))
    (runsTo_loadTo 2 1 (fun m hm => by rw [hm, e1, hsrc])) ?_
  set v1 : Mem := m₁.update 2 (M (22 + t)) with hv1
  have hv1_0 : v1 0 = 6 + t := by rw [hv1, Mem.update_of_ne _ _ (by omega), e0]
  have hv1_2 : v1 2 = M (22 + t) := by rw [hv1, Mem.update_self]
  refine RunsTo.seq (mid := fun m => m = v1.update (6 + t) (M (22 + t)))
    (runsTo_storeTo 0 2 (fun m hm => by rw [hm, hv1_0, hv1_2])) ?_
  set v2 : Mem := v1.update (6 + t) (M (22 + t)) with hv2
  have hv2_0 : v2 0 = 6 + t := by rw [hv2, Mem.update_of_ne _ _ (by omega), hv1_0]
  have hv2_3 : v2 3 = 1 := by
    rw [hv2, Mem.update_of_ne _ _ (by omega), hv1, Mem.update_of_ne _ _ (by omega), e3]
  refine RunsTo.seq (mid := fun m => m = v2.update 0 (6 + t + 1))
    (runsTo_addTo 0 0 3 (fun m hm => by rw [hm, hv2_0, hv2_3])) ?_
  set v3 : Mem := v2.update 0 (6 + t + 1) with hv3
  have hv3_1 : v3 1 = 22 + t := by
    rw [hv3, Mem.update_of_ne _ _ (by omega), hv2, Mem.update_of_ne _ _ (by omega), hv1,
      Mem.update_of_ne _ _ (by omega), e1]
  have hv3_3 : v3 3 = 1 := by rw [hv3, Mem.update_of_ne _ _ (by omega), hv2_3]
  refine RunsTo.seq (mid := fun m => m = v3.update 1 (22 + t + 1))
    (runsTo_addTo 1 1 3 (fun m hm => by rw [hm, hv3_1, hv3_3])) ?_
  set v4 : Mem := v3.update 1 (22 + t + 1) with hv4
  have hv4_3 : v4 3 = 1 := by rw [hv4, Mem.update_of_ne _ _ (by omega), hv3_3]
  have hv4_4 : v4 4 = t' + 1 := by
    rw [hv4, Mem.update_of_ne _ _ (by omega), hv3, Mem.update_of_ne _ _ (by omega), hv2,
      Mem.update_of_ne _ _ (by omega), hv1, Mem.update_of_ne _ _ (by omega), hc]
  refine runsTo_subTo 4 4 3 (fun m hm => ?_)
  subst hm
  rw [hv4_3, hv4_4]
  -- the frame of the body
  have hframe : ∀ z, z ≠ 0 → z ≠ 1 → z ≠ 2 → z ≠ 4 → z ≠ 6 + t → v4.update 4 (t' + 1 - 1) z
      = m₁ z := by
    intro z h0 h1 h2 h4 h6
    simp only [hv4, hv3, hv2, hv1, Mem.update, if_neg h0, if_neg h1, if_neg h2, if_neg h4,
      if_neg h6]
  have hnew : (v4.update 4 (t' + 1 - 1)) (6 + t) = M (22 + t) := by
    rw [Mem.update_of_ne _ _ (by omega), hv4, Mem.update_of_ne _ _ (by omega), hv3,
      Mem.update_of_ne _ _ (by omega), hv2, Mem.update_self]
  refine ⟨⟨t + 1, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    by rw [Mem.update_self]; omega⟩
  · rw [Mem.update_of_ne _ _ (by omega), hv4, Mem.update_of_ne _ _ (by omega), hv3,
      Mem.update_self]
    omega
  · rw [Mem.update_of_ne _ _ (by omega), hv4, Mem.update_self]; omega
  · rw [Mem.update_of_ne _ _ (by omega), hv4_3]
  · rw [Mem.update_self]; omega
  · rw [hframe 5 (by omega) (by omega) (by omega) (by omega) (by omega), e5]
  · intro j hj
    have := hge j
    rw [hframe _ (by omega) (by omega) (by omega) (by omega) (by omega)]
    exact epk j hj
  · intro i hi
    rcases Nat.lt_or_ge i t with h | h
    · rw [hframe _ (by omega) (by omega) (by omega) (by omega) (by omega)]
      exact ewr i h
    · have : i = t := by omega
      subst this
      exact hnew
  · intro z hz hzj
    rw [hframe _ (by omega) (by omega) (by omega) (by omega) (by omega)]
    exact efr z (by omega) hzj

theorem runsTo_downLoop (hM16 : M 16 = n) :
    RunsTo downLoop (DownInv M n (24 + n))
      (fun m' => DownInv M n (24 + n) m' ∧ m' 4 = 0) (7 * n + 1) := by
  refine RunsTo.mono (T := n * (5 + 2) + 1) ?_ (by omega)
  refine runsTo_forLoop (fun k => runsTo_downBody hM16 k) ?_
  rintro m ⟨t, htn, e0, e1, e3, e4, e5, epk, ewr, efr⟩
  omega

end

/-! ## Putting `down` together -/

theorem wf_down : Wf down := by
  refine wf_seq (wf_seq (Layout.wf_assign _ _) (wf_seq (Layout.wf_addTo _ _ _)
    (wf_parkRun _ _))) (wf_seq ?_ (wf_seq (wf_whileNz ?_) ?_))
  · exact wf_seq (Layout.wf_assign _ _) (wf_seq (Layout.wf_addTo _ _ _)
      (wf_seq (Layout.wf_assign _ _) (wf_seq (Layout.wf_assign _ _)
        (wf_seq (Layout.wf_assign _ _) (wf_seq (Layout.wf_assign _ _)
          (Layout.wf_subTo _ _ _))))))
  · exact wf_seq (Layout.wf_loadTo _ _) (wf_seq (Layout.wf_storeTo _ _)
      (wf_seq (Layout.wf_addTo _ _ _) (wf_seq (Layout.wf_addTo _ _ _)
        (Layout.wf_subTo _ _ _))))
  · exact wf_seq (Layout.wf_copyTo _ _) (wf_seq (wf_unparkRun _ _) (Layout.wf_loadTo _ _))

/-- **The bridge down.**  Started in a memory `M` whose register `16` holds `n`, `down` halts
within `7 * n + 34` steps in a memory whose register `0` holds `n` and whose register `i`, for
`1 ≤ i ≤ n`, holds `M (16 + i)`.  Nothing is claimed about the registers above `n`: the output
convention of `Workspace/Machine/Encoding.lean` does not look at them. -/
theorem runsTo_down {M : Mem} {n : ℕ} (hM16 : M 16 = n) :
    RunsTo down (fun m => m = M)
      (fun m' => m' 0 = n ∧ ∀ i, 1 ≤ i → i ≤ n → m' i = M (16 + i)) (7 * n + 34) := by
  have hge : ∀ j, 24 + n ≤ 2 ^ j * (24 + n) := fun j => le_two_pow_mul j (24 + n)
  have hA : 0 < 24 + n := by omega
  refine RunsTo.mono (T := 14 + (7 + ((7 * n + 1) + 12))) ?_ (by omega)
  refine (runsTo_downPark hM16).seq ((runsTo_downSetup hM16).seq
    ((runsTo_downLoop hM16).seq ?_))
  -- the read-back phase
  refine ⟨wf_seq (Layout.wf_copyTo _ _) (wf_seq (wf_unparkRun _ _) (Layout.wf_loadTo _ _)), ?_⟩
  intro m₀ hm₀
  obtain ⟨⟨t, htn, e0, e1, e3, e4, e5, epk, ewr, efr⟩, hzero⟩ := hm₀
  have ht : t = n - 5 := by omega
  subst ht
  refine (?_ : RunsTo downRead (fun m => m = m₀)
    (fun m' => m' 0 = n ∧ ∀ i, 1 ≤ i → i ≤ n → m' i = M (16 + i)) (1 + (2 * 5 + 1))).spec m₀ rfl
  refine RunsTo.seq (mid := fun m => m = m₀.update 0 (24 + n))
    (runsTo_copyTo 0 5 (fun m hm => by rw [hm, e5])) ?_
  set w0 : Mem := m₀.update 0 (24 + n) with hw0
  have hw0_frame : ∀ z, z ≠ 0 → w0 z = m₀ z := fun z hz => by
    rw [hw0, Mem.update_of_ne _ _ hz]
  have hstart : UnparkedAt w0 (24 + n) downBack 0 w0 := by
    refine ⟨by rw [hw0, Mem.update_self]; ring, by intro j hj; omega, fun z _ _ => rfl⟩
  refine RunsTo.seq (mid := UnparkedAt w0 (24 + n) downBack 5) ?_ ?_
  · refine (runsTo_unparkRun (M := w0) hA 5
      (fun j hj => ⟨by simp only [downBack]; omega, by simp only [downBack]; omega⟩)
      ?_).strengthen (fun m hm => by rw [hm]; exact hstart)
    intro i j hij hj
    simp only [downBack]
    omega
  refine runsTo_loadTo 0 0 (fun m hm => ?_)
  obtain ⟨g0, gpk, gfr⟩ := hm
  have hres : m (m 0) = M 16 := by
    rw [g0]
    have h1 : w0 (2 ^ 5 * (24 + n)) = m₀ (2 ^ 5 * (24 + n)) :=
      hw0_frame _ (by have := hge 5; omega)
    have h2 : m (2 ^ 5 * (24 + n)) = w0 (2 ^ 5 * (24 + n)) := by
      refine gfr _ (by have := hge 5; omega) (fun j hj => ?_)
      simp only [downBack]
      have := hge 5
      omega
    rw [h2, h1]
    have := epk 5 (by omega)
    simpa [downRegs] using this
  rw [hres, hM16]
  refine ⟨by rw [Mem.update_self], ?_⟩
  intro i h1i hin
  rw [Mem.update_of_ne _ _ (by omega)]
  rcases Nat.lt_or_ge i 6 with hi6 | hi6
  · -- the entry comes from the parked values
    have hj : downBack (5 - i) = i := by simp only [downBack]; omega
    have := gpk (5 - i) (by omega)
    rw [hj] at this
    rw [this]
    have hmem : w0 (2 ^ (5 - i) * (24 + n)) = m₀ (2 ^ (5 - i) * (24 + n)) :=
      hw0_frame _ (by have := hge (5 - i); omega)
    rw [hmem]
    have := epk (5 - i) (by omega)
    rw [this]
    simp only [downRegs]
    congr 1
    omega
  · -- the entry comes from the copy loop
    have hz : m i = w0 i := by
      refine gfr i (by omega) (fun j hj => ?_)
      simp only [downBack]
      omega
    rw [hz, hw0_frame i (by omega)]
    have := ewr (i - 6) (by omega)
    rw [show 6 + (i - 6) = i by omega] at this
    rw [this]
    congr 1
    omega

/-- **The bridge down at the workspace convention.**  From exactly `initMemAt 16 l`, the
program `down` halts within `7 * l.length + 34` steps in a memory displaying `l` in the output
convention. -/
theorem runsTo_down_outputAt (l : List ℕ) :
    RunsTo down (fun m => m = initMemAt 16 l) (fun m' => OutputAt m' l)
      (7 * l.length + 34) := by
  have hM16 : initMemAt 16 l 16 = l.length := by
    have := initMemAt_add 16 l 0
    simpa [initMem] using this
  refine (runsTo_down hM16).weaken (fun m' hm' => ?_)
  obtain ⟨h0, h1⟩ := hm'
  refine ⟨h0, fun i hi => ?_⟩
  have := h1 (i + 1) (by omega) (by omega)
  rw [this, show (16:ℕ) + (i + 1) = 16 + (i + 1) from rfl, initMemAt_add]
  simp [initMem]

end Bridge
end RAM
