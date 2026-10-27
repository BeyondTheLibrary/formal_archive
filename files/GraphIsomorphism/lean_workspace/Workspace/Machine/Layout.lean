import Workspace.Machine.Arrays
import Workspace.Machine.Reloc

/-!
# The layout algebra of the workspace convention

Pairing, the conditional and bounded iteration are all assembled by the same kind of program: a
few blocks of data are stacked above the input, a relocated routine is called on the topmost
block, and the result is moved back down to the base.  Carrying such a program through the Hoare
rules of `Workspace/Machine/Block.lean` means describing the *whole* memory at every stage, since
the postcondition of a clean routine is an equation between memories.  This file gives the
normal form in which those descriptions stay readable, and the half-dozen stage rules that the
combinators of `Workspace/Machine/Pairing.lean` are built from.

## The normal form

Every memory occurring in such a program has the shape

`memAt K w L`: the work registers `0, ..., K - 1` hold `w`, and from register `K` on the memory
is the list `L` followed by zeros.

This is a normal form because every stage transforms it into another one of the same shape:

* `initMemAt K l = memAt K 0 (l.length :: l)` (`initMemAt_eq_memAt`), so the convention of
  `Workspace/Machine/Offset.lean` is a special case;
* a write in a work register changes `w`, a write at address `K + L.length` appends an entry to
  `L` (`memAt_update_top`), and trailing zeros may always be dropped (`memAt_append_zeros`);
* a relocated call whose base is the start of the topmost block replaces that block
  (`runsTo_callTop`);
* a block copy to the top appends a segment of `L` to `L` (`runsTo_pushBlock`).

The predicate `At K Q L` ("the memory is `memAt K w L` for some `w` satisfying `Q`") is what the
stage rules take and return; `Q` is the caller's description of the work registers, and each rule
is stated with the rule of consequence built in, so that the caller supplies the description it
wants to carry forward and discharges it from the frame information of the stage.

## The register discipline of this file

`K ≥ 16` work registers, used as follows.

| registers | use |
|---|---|
| `0` | base address of a call; source address of a block copy |
| `1`, `2` | scratch of the relocation; destination and count of a block copy |
| `3 .. 7` | the scratch block `s = 3` of `Workspace/Machine/Arrays.lean` |
| `8` | the **top pointer**: always `K + L.length` |
| `10` | scratch for the constant `1` |
| `9`, `11 .. K-1` | free for the caller (pointers and lengths of the blocks) |

## Main results

* `RAM.Layout.memAt`, `RAM.Layout.At`, and the normal-form lemmas;
* `RAM.Layout.runsTo_clearRange`: zero the work registers, `K` steps;
* `RAM.Layout.runsTo_pushVal`: append the contents of a register to the top, `3` steps;
* `RAM.Layout.runsTo_pushBlock`: append a segment of the memory to the top, `7c + 7` steps;
* `RAM.Layout.runsTo_callTop`: call a relocated clean routine on the topmost block, `10T + 8`
  steps;
* `RAM.Layout.runsTo_finish`: move the topmost block down to the base, erase everything above it
  and clear the work registers, producing exactly `initMemAt K l'`.
-/

namespace RAM
namespace Layout

/-! ## The normal form -/

/-- `memAt K w L`: the work registers `0, ..., K-1` hold `w`, and from register `K` on the memory
is the list `L` followed by zeros. -/
def memAt (K : ℕ) (w : Mem) (L : List ℕ) : Mem :=
  fun z => if z < K then w z else L.getD (z - K) 0

theorem memAt_of_lt {K : ℕ} (w : Mem) (L : List ℕ) {z : ℕ} (h : z < K) : memAt K w L z = w z := by
  simp [memAt, h]

@[simp] theorem memAt_add (K : ℕ) (w : Mem) (L : List ℕ) (i : ℕ) :
    memAt K w L (K + i) = L.getD i 0 := by
  simp only [memAt, if_neg (by omega : ¬ K + i < K)]
  congr 1
  omega

/-- The criterion for recognizing a memory as being in normal form: it suffices to check the
part from register `K` on. -/
theorem eq_memAt (K : ℕ) {m : Mem} {L : List ℕ} (h : ∀ i, m (K + i) = L.getD i 0) :
    m = memAt K m L := by
  funext z
  rcases Nat.lt_or_ge z K with hz | hz
  · rw [memAt_of_lt _ _ hz]
  · have hzK : z = K + (z - K) := by omega
    rw [hzK, h, memAt_add]

/-- The workspace convention is the normal form with zeroed work registers and the length
prefixed to the list. -/
theorem initMemAt_eq_memAt (K : ℕ) (l : List ℕ) :
    initMemAt K l = memAt K (fun _ => 0) (l.length :: l) := by
  refine (eq_initMemAt (fun z hz => by rw [memAt_of_lt _ _ hz]) (fun x => ?_)).symm
  rw [memAt_add]
  cases x with
  | zero => simp [initMem]
  | succ i => simp [initMem, List.getD]

/-- Trailing zeros of the list are invisible. -/
theorem memAt_append_zeros (K : ℕ) (w : Mem) (L : List ℕ) (j : ℕ) :
    memAt K w (L ++ List.replicate j 0) = memAt K w L := by
  funext z
  simp only [memAt]
  split
  · rfl
  · rcases Nat.lt_or_ge (z - K) L.length with h | h
    · rw [List.getD_append _ _ _ _ h]
    · rw [List.getD_append_right _ _ _ _ h, List.getD_eq_default _ _ h]
      rcases Nat.lt_or_ge (z - K - L.length) j with h' | h'
      · exact List.getD_replicate _ h'
      · exact List.getD_eq_default _ _ (by simpa using h')

/-- A write in a work register. -/
theorem memAt_update_of_lt {K : ℕ} (w : Mem) (L : List ℕ) {z : ℕ} (h : z < K) (v : ℕ) :
    (memAt K w L).update z v = memAt K (w.update z v) L := by
  funext y
  by_cases hy : y = z
  · subst hy
    rw [Mem.update_self, memAt_of_lt _ _ h, Mem.update_self]
  · rw [Mem.update_of_ne _ _ hy]
    simp only [memAt]
    split
    · rw [Mem.update_of_ne _ _ hy]
    · rfl

/-- A write just above the list appends an entry. -/
theorem memAt_update_top {K : ℕ} (w : Mem) (L : List ℕ) (v : ℕ) :
    (memAt K w L).update (K + L.length) v = memAt K w (L ++ [v]) := by
  funext y
  rcases Nat.lt_or_ge y K with hy | hy
  · rw [Mem.update_of_ne _ _ (by omega : y ≠ K + L.length), memAt_of_lt _ _ hy,
      memAt_of_lt _ _ hy]
  · obtain ⟨i, rfl⟩ : ∃ i, y = K + i := ⟨y - K, by omega⟩
    rcases Nat.lt_trichotomy i L.length with h | h | h
    · rw [Mem.update_of_ne _ _ (by omega : K + i ≠ K + L.length), memAt_add, memAt_add,
        List.getD_append _ _ _ _ h]
    · subst h
      rw [Mem.update_self, memAt_add, List.getD_append_right _ _ _ _ (le_refl _)]
      simp
    · rw [Mem.update_of_ne _ _ (by omega : K + i ≠ K + L.length), memAt_add, memAt_add,
        List.getD_eq_default _ _ (by omega),
        List.getD_eq_default _ _ (by simp; omega)]

/-! ## The state predicate

`At K Q L m` says that `m` is in normal form with list `L`, the work registers satisfying the
caller's description `Q`.  Every stage rule below is stated with the rule of consequence built
in: the caller supplies the description `Q'` it wants after the stage and proves it from the
frame information the stage provides. -/

/-- The memory is in normal form with list `L`, its work registers satisfying `Q`. -/
def At (K : ℕ) (Q : Mem → Prop) (L : List ℕ) : Mem → Prop :=
  fun m => ∃ w, Q w ∧ m = memAt K w L

theorem At.intro {K : ℕ} {Q : Mem → Prop} {L : List ℕ} {w : Mem} (hQ : Q w) :
    At K Q L (memAt K w L) := ⟨w, hQ, rfl⟩

/-- A specification from a state predicate is proved one work-register assignment at a time. -/
theorem runsTo_of_At {K : ℕ} {Q : Mem → Prop} {L : List ℕ} {P : Program} {post : Mem → Prop}
    {T : ℕ} (hw : Wf P)
    (h : ∀ w, Q w → RunsTo P (fun m => m = memAt K w L) post T) :
    RunsTo P (At K Q L) post T :=
  ⟨hw, fun m hm => by obtain ⟨w, hQ, rfl⟩ := hm; exact (h w hQ).spec _ rfl⟩

/-! ## Well-formedness of the straight-line primitives -/

theorem wf_single {i : Instr} (ht : i.target ≤ 1) (hne : i ≠ Instr.halt) : Wf [i] := by
  intro j hj
  simp only [List.mem_singleton] at hj
  subst hj
  exact ⟨by simpa using ht, hne⟩

theorem wf_assign (x c : ℕ) : Wf (assign x c) :=
  wf_single (by simp [Instr.target]) (by simp)

theorem wf_copyTo (x y : ℕ) : Wf (copyTo x y) :=
  wf_single (by simp [Instr.target]) (by simp)

theorem wf_addTo (x y z : ℕ) : Wf (addTo x y z) :=
  wf_single (by simp [Instr.target]) (by simp)

theorem wf_subTo (x y z : ℕ) : Wf (subTo x y z) :=
  wf_single (by simp [Instr.target]) (by simp)

theorem wf_loadTo (x y : ℕ) : Wf (loadTo x y) :=
  wf_single (by simp [Instr.target]) (by simp)

theorem wf_storeTo (x y : ℕ) : Wf (storeTo x y) :=
  wf_single (by simp [Instr.target]) (by simp)

/-! ## Clearing the work registers -/

/-- `clearRange j` sets registers `0, ..., j - 1` to zero, one instruction each. -/
def clearRange : ℕ → Program
  | 0 => []
  | j + 1 => seq (clearRange j) (assign j 0)

/-- The memory with the registers below `j` zeroed. -/
def zeroBelow (j : ℕ) (m : Mem) : Mem := fun z => if z < j then 0 else m z

theorem runsTo_clearRange (j : ℕ) (m₁ : Mem) :
    RunsTo (clearRange j) (fun m => m = m₁) (fun m' => m' = zeroBelow j m₁) j := by
  induction j with
  | zero =>
      refine runsTo_nil (fun m hm => ?_)
      rw [hm]; funext z; simp [zeroBelow]
  | succ j ih =>
      refine RunsTo.mono (T := j + 1) ?_ (le_refl _)
      refine RunsTo.seq (mid := fun m => m = zeroBelow j m₁) ih ?_
      refine runsTo_assign j 0 (fun m hm => ?_)
      rw [hm]
      funext z
      by_cases hz : z = j
      · subst hz; simp [Mem.update, zeroBelow]
      · rw [Mem.update_of_ne _ _ hz]
        simp only [zeroBelow]
        by_cases h : z < j <;> simp [h] <;> omega

/-- Clearing the work registers of a memory in normal form. -/
theorem zeroBelow_memAt (K : ℕ) (w : Mem) (L : List ℕ) :
    zeroBelow K (memAt K w L) = memAt K (fun _ => 0) L := by
  funext z
  simp only [zeroBelow, memAt]
  split <;> rfl

/-! ## Pushing a register onto the top of the workspace -/

/-- `pushVal r` appends the contents of register `r` to the list, advancing the top pointer
(register `8`).  Register `10` is used for the constant `1`. -/
def pushVal (r : ℕ) : Program := seq (assign 10 1) (seq (storeTo 8 r) (addTo 8 8 10))

/-- **Appending a register to the top of the workspace**, three steps. -/
theorem runsTo_pushVal {K r : ℕ} (hK : 16 ≤ K) (hr : r < K) (hr10 : r ≠ 10)
    {Q Q' : Mem → Prop} {L : List ℕ} {v : ℕ}
    (hQ : ∀ w, Q w → w 8 = K + L.length ∧ w r = v)
    (hQ' : ∀ w w', Q w → (∀ z, z ≠ 8 → z ≠ 10 → w' z = w z) → w' 8 = K + L.length + 1 →
      w' 10 = 1 → Q' w') :
    RunsTo (pushVal r) (At K Q L) (At K Q' (L ++ [v])) 3 := by
  refine runsTo_of_At (wf_seq (wf_assign _ _) (wf_seq (wf_storeTo _ _) (wf_addTo _ _ _)))
    (fun w hw => ?_)
  obtain ⟨h8, hrv⟩ := hQ w hw
  refine RunsTo.mono (T := 1 + (1 + 1)) ?_ (by norm_num)
  refine RunsTo.seq (mid := fun m => m = memAt K (w.update 10 1) L)
    (runsTo_assign 10 1 (fun m hm => by
      rw [hm, memAt_update_of_lt _ _ (by omega : (10:ℕ) < K)])) ?_
  set w₁ : Mem := w.update 10 1 with hw₁
  have h18 : w₁ 8 = K + L.length := by rw [hw₁, Mem.update_of_ne _ _ (by omega : (8:ℕ) ≠ 10), h8]
  have h1r : w₁ r = v := by rw [hw₁, Mem.update_of_ne _ _ hr10, hrv]
  have h110 : w₁ 10 = 1 := by rw [hw₁, Mem.update_self]
  refine RunsTo.seq (mid := fun m => m = memAt K w₁ (L ++ [v]))
    (runsTo_storeTo 8 r (fun m hm => ?_)) ?_
  · rw [hm, memAt_of_lt _ _ (by omega : (8:ℕ) < K), memAt_of_lt _ _ hr, h18, h1r,
      memAt_update_top]
  refine runsTo_addTo 8 8 10 (fun m hm => ?_)
  rw [hm, memAt_of_lt _ _ (by omega : (8:ℕ) < K), memAt_of_lt _ _ (by omega : (10:ℕ) < K),
    h18, h110, memAt_update_of_lt _ _ (by omega : (8:ℕ) < K)]
  refine ⟨_, hQ' w _ hw (fun z hz8 hz10 => ?_) ?_ ?_, rfl⟩
  · rw [Mem.update_of_ne _ _ hz8, hw₁, Mem.update_of_ne _ _ hz10]
  · rw [Mem.update_self]
  · rw [Mem.update_of_ne _ _ (by omega : (10:ℕ) ≠ 8), h110]


/-! ## One-instruction rules on the work registers -/

theorem runsTo_assignReg {K x c : ℕ} (hx : x < K) {Q Q' : Mem → Prop} {L : List ℕ}
    (hQ' : ∀ w, Q w → Q' (w.update x c)) :
    RunsTo (assign x c) (At K Q L) (At K Q' L) 1 :=
  runsTo_of_At (wf_assign _ _) (fun w hw => runsTo_assign x c (fun m hm => by
    rw [hm, memAt_update_of_lt _ _ hx]; exact ⟨_, hQ' w hw, rfl⟩))

theorem runsTo_copyReg {K x y : ℕ} (hx : x < K) (hy : y < K) {Q Q' : Mem → Prop} {L : List ℕ}
    (hQ' : ∀ w, Q w → Q' (w.update x (w y))) :
    RunsTo (copyTo x y) (At K Q L) (At K Q' L) 1 :=
  runsTo_of_At (wf_copyTo _ _) (fun w hw => runsTo_copyTo x y (fun m hm => by
    rw [hm, memAt_of_lt _ _ hy, memAt_update_of_lt _ _ hx]; exact ⟨_, hQ' w hw, rfl⟩))

theorem runsTo_addReg {K x y z : ℕ} (hx : x < K) (hy : y < K) (hz : z < K) {Q Q' : Mem → Prop}
    {L : List ℕ} (hQ' : ∀ w, Q w → Q' (w.update x (w y + w z))) :
    RunsTo (addTo x y z) (At K Q L) (At K Q' L) 1 :=
  runsTo_of_At (wf_addTo _ _ _) (fun w hw => runsTo_addTo x y z (fun m hm => by
    rw [hm, memAt_of_lt _ _ hy, memAt_of_lt _ _ hz, memAt_update_of_lt _ _ hx]
    exact ⟨_, hQ' w hw, rfl⟩))

theorem runsTo_subReg {K x y z : ℕ} (hx : x < K) (hy : y < K) (hz : z < K) {Q Q' : Mem → Prop}
    {L : List ℕ} (hQ' : ∀ w, Q w → Q' (w.update x (w y - w z))) :
    RunsTo (subTo x y z) (At K Q L) (At K Q' L) 1 :=
  runsTo_of_At (wf_subTo _ _ _) (fun w hw => runsTo_subTo x y z (fun m hm => by
    rw [hm, memAt_of_lt _ _ hy, memAt_of_lt _ _ hz, memAt_update_of_lt _ _ hx]
    exact ⟨_, hQ' w hw, rfl⟩))

/-- Reading an entry of the workspace through a pointer register. -/
theorem runsTo_loadReg {K x y i : ℕ} (hx : x < K) (hy : y < K) {Q Q' : Mem → Prop} {L : List ℕ}
    (hQ : ∀ w, Q w → w y = K + i)
    (hQ' : ∀ w, Q w → Q' (w.update x (L.getD i 0))) :
    RunsTo (loadTo x y) (At K Q L) (At K Q' L) 1 :=
  runsTo_of_At (wf_loadTo _ _) (fun w hw => runsTo_loadTo x y (fun m hm => by
    rw [hm, memAt_of_lt _ _ hy, hQ w hw, memAt_add, memAt_update_of_lt _ _ hx]
    exact ⟨_, hQ' w hw, rfl⟩))

/-! ## Copying a segment of the workspace to the top -/

/-- The entries of a segment of a list. -/
theorem getD_seg {L : List ℕ} {i c j : ℕ} (h : i + c ≤ L.length) (hj : j < c) :
    ((L.drop i).take c).getD j 0 = L.getD (i + j) 0 := by
  have hlen : ((L.drop i).take c).length = c := by
    simp only [List.length_take, List.length_drop]
    omega
  rw [List.getD_eq_getElem _ _ (by omega : j < ((L.drop i).take c).length),
    List.getD_eq_getElem _ _ (by omega : i + j < L.length)]
  simp

theorem length_seg {L : List ℕ} {i c : ℕ} (h : i + c ≤ L.length) :
    ((L.drop i).take c).length = c := by
  simp only [List.length_take, List.length_drop]
  omega

theorem wf_copyBlock : Wf (Arrays.copyBlock 0 1 2 3) :=
  (Arrays.runsTo_copyBlock 0 1 2 3 (by omega) (by omega) (by omega) (fun _ => 100)
    (by decide) (by decide) (Or.inl (le_refl _))).wf

theorem wf_fillZero : Wf (Arrays.fillZero 0 1 3) :=
  (Arrays.runsTo_fillZero 0 1 3 (by omega) (by omega) (fun _ => 100) (by decide)).wf

/-- `pushBlock` copies the `R 2` registers starting at `R 0` to the top of the workspace and
advances the top pointer. -/
def pushBlock : Program := seq (copyTo 1 8) (seq (Arrays.copyBlock 0 1 2 3) (addTo 8 8 2))

/-- **Appending a segment of the workspace to its top**, `7c + 7` steps. -/
theorem runsTo_pushBlock {K : ℕ} (hK : 16 ≤ K) {Q Q' : Mem → Prop} {L : List ℕ} {i c : ℕ}
    (hic : i + c ≤ L.length)
    (hQ : ∀ w, Q w → w 8 = K + L.length ∧ w 0 = K + i ∧ w 2 = c)
    (hQ' : ∀ w w', Q w → (∀ z, z < K → z ≠ 1 → z ≠ 8 → ¬ (3 ≤ z ∧ z ≤ 7) → w' z = w z) →
      w' 8 = K + L.length + c → Q' w') :
    RunsTo pushBlock (At K Q L) (At K Q' (L ++ (L.drop i).take c)) (7 * c + 7) := by
  refine runsTo_of_At (wf_seq (wf_copyTo _ _) (wf_seq wf_copyBlock (wf_addTo _ _ _)))
    (fun w hw => ?_)
  obtain ⟨h8, h0, h2⟩ := hQ w hw
  set B : List ℕ := (L.drop i).take c with hB
  have hBlen : B.length = c := length_seg hic
  set w₁ : Mem := w.update 1 (K + L.length) with hw₁
  set m₁ : Mem := memAt K w₁ L with hm₁
  have e0 : m₁ 0 = K + i := by
    rw [hm₁, memAt_of_lt _ _ (by omega : (0:ℕ) < K), hw₁, Mem.update_of_ne _ _ (by omega), h0]
  have e1 : m₁ 1 = K + L.length := by
    rw [hm₁, memAt_of_lt _ _ (by omega : (1:ℕ) < K), hw₁, Mem.update_self]
  have e2 : m₁ 2 = c := by
    rw [hm₁, memAt_of_lt _ _ (by omega : (2:ℕ) < K), hw₁, Mem.update_of_ne _ _ (by omega), h2]
  have e8 : m₁ 8 = K + L.length := by
    rw [hm₁, memAt_of_lt _ _ (by omega : (8:ℕ) < K), hw₁, Mem.update_of_ne _ _ (by omega), h8]
  refine RunsTo.mono (T := 1 + ((7 * m₁ 2 + 5) + 1)) ?_ (by rw [e2]; omega)
  refine RunsTo.seq (mid := fun m => m = m₁)
    (runsTo_copyTo 1 8 (fun m hm => by
      rw [hm, memAt_of_lt _ _ (by omega : (8:ℕ) < K), h8, hm₁, hw₁,
        memAt_update_of_lt _ _ (by omega : (1:ℕ) < K)])) ?_
  refine RunsTo.seq (mid := fun m => m = memAt K m (L ++ B) ∧ m 8 = K + L.length ∧ m 2 = c ∧
      (∀ z, z < K → z ≠ 1 → z ≠ 8 → ¬ (3 ≤ z ∧ z ≤ 7) → m z = w z)) ?_ ?_
  · refine (Arrays.runsTo_copyBlock 0 1 2 3 (by omega) (by omega) (by omega) m₁
      (by rw [e0]; omega) (by rw [e1]; omega)
      (Or.inr (by rw [e0, e1, e2]; omega))).weaken (fun m hm => ?_)
    obtain ⟨hcopy, hout⟩ := hm
    have hfix : ∀ z, ¬ (m₁ 1 ≤ z ∧ z < m₁ 1 + m₁ 2) → ¬ (3 ≤ z ∧ z ≤ 7) → m z = m₁ z := by
      intro z hz hz'
      refine hout z hz ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      omega
    have hhigh : ∀ x, m (K + x) = (L ++ B).getD x 0 := by
      intro x
      rcases Nat.lt_or_ge x L.length with hx | hx
      · rw [hfix _ (by rw [e1]; omega) (by omega), hm₁, memAt_add,
          List.getD_append _ _ _ _ hx]
      · rcases Nat.lt_or_ge x (L.length + c) with hx' | hx'
        · have : K + x = m₁ 1 + (x - L.length) := by rw [e1]; omega
          rw [this, hcopy _ (by rw [e2]; omega), e0, Nat.add_assoc, hm₁, memAt_add,
            List.getD_append_right _ _ _ _ hx, getD_seg hic (by omega)]
        · rw [hfix _ (by rw [e1, e2]; omega) (by omega), hm₁, memAt_add,
            List.getD_eq_default _ _ (by omega),
            List.getD_eq_default _ _ (by simp [hBlen]; omega)]
    refine ⟨eq_memAt K hhigh, ?_, ?_, ?_⟩
    · rw [hfix _ (by rw [e1]; omega) (by omega), e8]
    · rw [hfix _ (by rw [e1]; omega) (by omega), e2]
    · intro z hz hz1 hz8 hz37
      rw [hfix _ (by rw [e1]; omega) hz37, hm₁, memAt_of_lt _ _ hz, hw₁,
        Mem.update_of_ne _ _ hz1]
  · refine runsTo_of_pointwise (fun m => ?_)
    refine runsTo_addTo 8 8 2 (fun m' hm' => ?_)
    obtain ⟨rfl, hmem, hm8, hm2, hagree⟩ := hm'
    rw [hm8, hm2]
    refine ⟨m'.update 8 (K + L.length + c), hQ' w _ hw (fun z hz hz1 hz8 hz37 => ?_) ?_, ?_⟩
    · rw [Mem.update_of_ne _ _ hz8]
      exact hagree z hz hz1 hz8 hz37
    · rw [Mem.update_self]
    · conv_lhs => rw [hmem]
      rw [memAt_update_of_lt _ _ (by omega : (8:ℕ) < K)]

/-! ## Calling a relocated routine on the topmost block -/

/-- The top-level convention read as a list: register `x` of `initMem l` is entry `x` of
`l.length :: l`. -/
theorem initMem_getD (l : List ℕ) (x : ℕ) : initMem l x = (l.length :: l).getD x 0 := by
  cases x with
  | zero => simp [initMem]
  | succ i => simp [initMem, List.getD]

/-- `callTop P` calls the relocated routine `P` on the topmost block of the workspace, whose base
address is held in register `0`, and resets the top pointer to just above the block the routine
has left there. -/
def callTop (P : Program) : Program :=
  seq (Reloc.relocate 0 1 2 P)
    (seq (loadTo 8 0) (seq (addTo 8 8 0) (seq (assign 10 1) (addTo 8 8 10))))

/-- **Calling a clean routine on the topmost block.**  The block is replaced by the routine's
output block, everything below it — the caller's own data, of any length — is untouched, and the
cost is ten times the routine's own, plus four steps of pointer arithmetic. -/
theorem runsTo_callTop {K : ℕ} (hK : 16 ≤ K) {P : Program} {l l' : List ℕ} {T : ℕ}
    (h : RunsTo P (fun m => m = initMem l) (fun m' => m' = initMem l') T)
    {Q Q' : Mem → Prop} {L₀ : List ℕ}
    (hQ : ∀ w, Q w → w 0 = K + L₀.length)
    (hQ' : ∀ w w', Q w → (∀ z, z < K → z ≠ 1 → z ≠ 2 → z ≠ 8 → z ≠ 10 → w' z = w z) →
      w' 0 = K + L₀.length → w' 8 = K + L₀.length + l'.length + 1 → Q' w') :
    RunsTo (callTop P) (At K Q (L₀ ++ (l.length :: l)))
      (At K Q' (L₀ ++ (l'.length :: l'))) (10 * T + 4) := by
  refine runsTo_of_At (wf_seq (Reloc.wf_relocate h.wf) (wf_seq (wf_loadTo _ _)
    (wf_seq (wf_addTo _ _ _) (wf_seq (wf_assign _ _) (wf_addTo _ _ _))))) (fun w hw => ?_)
  have h0 := hQ w hw
  set d : ℕ := K + L₀.length with hd
  set Lf : List ℕ := L₀ ++ (l'.length :: l') with hLf
  set m₀ : Mem := memAt K w (L₀ ++ (l.length :: l)) with hm₀
  have hgetd : Lf.getD L₀.length 0 = l'.length := by
    rw [hLf, List.getD_append_right _ _ _ _ (le_refl _)]
    simp
  have hs : Reloc.Shifted d (initMem l) m₀ := by
    intro x
    rw [hd, Nat.add_assoc, hm₀, memAt_add, List.getD_append_right _ _ _ _ (by omega),
      initMem_getD]
    congr 1
    omega
  have hb : m₀ 0 = d := by rw [hm₀, memAt_of_lt _ _ (by omega : (0:ℕ) < K), h0]
  have hok : Reloc.Ok 0 1 2 d :=
    ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
  refine RunsTo.mono (T := 10 * T + (1 + (1 + (1 + 1)))) ?_ (by omega)
  refine RunsTo.seq
    (mid := At K (fun v => v 0 = d ∧ ∀ z, z < K → z ≠ 1 → z ≠ 2 → v z = w z) Lf) ?_ ?_
  · refine (RAM.runsTo_reloc h hok m₀ hs hb).weaken (fun m hm => ?_)
    obtain ⟨hsh, hlow⟩ := hm
    have hlow' : ∀ z, z < K → z ≠ 1 → z ≠ 2 → m z = w z := by
      intro z hz hz1 hz2
      rw [hlow z (by omega) hz1 hz2, hm₀, memAt_of_lt _ _ hz]
    have hhigh : ∀ x, m (K + x) = Lf.getD x 0 := by
      intro x
      rcases Nat.lt_or_ge x L₀.length with hx | hx
      · rw [hlow (K + x) (by omega) (by omega) (by omega), hm₀, memAt_add,
          List.getD_append _ _ _ _ hx, hLf, List.getD_append _ _ _ _ hx]
      · have : K + x = d + (x - L₀.length) := by omega
        rw [this, hsh, initMem_getD, hLf, List.getD_append_right _ _ _ _ hx]
    exact ⟨m, ⟨by rw [hlow' _ (by omega) (by omega) (by omega), h0], hlow'⟩, eq_memAt K hhigh⟩
  refine RunsTo.seq
    (mid := At K (fun v => v 0 = d ∧ v 8 = l'.length ∧
      ∀ z, z < K → z ≠ 1 → z ≠ 2 → z ≠ 8 → z ≠ 10 → v z = w z) Lf) ?_ ?_
  · refine runsTo_loadReg (i := L₀.length) (by omega) (by omega) (fun v hv => hv.1) ?_
    rintro v ⟨hv0, hva⟩
    refine ⟨by rw [Mem.update_of_ne _ _ (by omega : (0:ℕ) ≠ 8), hv0], ?_, ?_⟩
    · rw [Mem.update_self, hgetd]
    · intro z hz hz1 hz2 hz8 hz10
      rw [Mem.update_of_ne _ _ hz8]
      exact hva z hz hz1 hz2
  refine RunsTo.seq
    (mid := At K (fun v => v 0 = d ∧ v 8 = l'.length + d ∧
      ∀ z, z < K → z ≠ 1 → z ≠ 2 → z ≠ 8 → z ≠ 10 → v z = w z) Lf) ?_ ?_
  · refine runsTo_addReg (by omega) (by omega) (by omega) ?_
    rintro v ⟨hv0, hv8, hva⟩
    refine ⟨by rw [Mem.update_of_ne _ _ (by omega : (0:ℕ) ≠ 8), hv0], ?_, ?_⟩
    · rw [Mem.update_self, hv8, hv0]
    · intro z hz hz1 hz2 hz8 hz10
      rw [Mem.update_of_ne _ _ hz8]
      exact hva z hz hz1 hz2 hz8 hz10
  refine RunsTo.seq
    (mid := At K (fun v => v 0 = d ∧ v 8 = l'.length + d ∧ v 10 = 1 ∧
      ∀ z, z < K → z ≠ 1 → z ≠ 2 → z ≠ 8 → z ≠ 10 → v z = w z) Lf) ?_ ?_
  · refine runsTo_assignReg (by omega) ?_
    rintro v ⟨hv0, hv8, hva⟩
    refine ⟨by rw [Mem.update_of_ne _ _ (by omega : (0:ℕ) ≠ 10), hv0],
      by rw [Mem.update_of_ne _ _ (by omega : (8:ℕ) ≠ 10), hv8], by rw [Mem.update_self], ?_⟩
    intro z hz hz1 hz2 hz8 hz10
    rw [Mem.update_of_ne _ _ hz10]
    exact hva z hz hz1 hz2 hz8 hz10
  refine runsTo_addReg (by omega) (by omega) (by omega) ?_
  rintro v ⟨hv0, hv8, hv10, hva⟩
  refine hQ' w _ hw (fun z hz hz1 hz2 hz8 hz10 => ?_) ?_ ?_
  · rw [Mem.update_of_ne _ _ hz8]
    exact hva z hz hz1 hz2 hz8 hz10
  · rw [Mem.update_of_ne _ _ (by omega : (0:ℕ) ≠ 8), hv0]
  · rw [Mem.update_self, hv8, hv10, hd]
    omega

/-! ## The final move: the answer back to the base -/

theorem getD_drop (L : List ℕ) (k j : ℕ) : (L.drop k).getD j 0 = L.getD (k + j) 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop]

/-- `finish K` moves the topmost block down to the base of the workspace, erases everything
above it and clears the work registers.  Register `11` holds the base address of the block and
register `12` its length. -/
def finish (K : ℕ) : Program :=
  seq (copyTo 0 11) (seq (assign 1 K) (seq (copyTo 2 12) (seq (Arrays.copyBlock 0 1 2 3)
    (seq (assign 0 K) (seq (addTo 0 0 12) (seq (assign 2 K) (seq (subTo 1 11 2)
      (seq (Arrays.fillZero 0 1 3) (clearRange K)))))))))

/-- **The final move.**  From a workspace whose topmost block is `B`, `finish K` produces
exactly the memory `memAt K 0 B`; with `B = l.length :: l` this is `initMemAt K l`. -/
theorem runsTo_finish {K : ℕ} (hK : 16 ≤ K) {Q : Mem → Prop} {L₀ B : List ℕ}
    (hQ : ∀ w, Q w → w 11 = K + L₀.length ∧ w 12 = B.length) :
    RunsTo (finish K) (At K Q (L₀ ++ B)) (fun m' => m' = memAt K (fun _ => 0) B)
      (7 * B.length + 5 * L₀.length + K + 17) := by
  have hLmlen : (B ++ (L₀ ++ B).drop B.length).length = B.length + L₀.length := by
    simp only [List.length_append, List.length_drop]
    omega
  have hLmget : ∀ x, (B ++ (L₀ ++ B).drop B.length).getD x 0 =
      if x < B.length then B.getD x 0 else (L₀ ++ B).getD x 0 := by
    intro x
    by_cases hx : x < B.length
    · rw [if_pos hx]
      exact List.getD_append B ((L₀ ++ B).drop B.length) 0 x hx
    · rw [if_neg hx,
        List.getD_append_right B ((L₀ ++ B).drop B.length) 0 x (by omega), getD_drop]
      congr 1
      omega
  set M : ℕ := L₀.length with hM
  set c : ℕ := B.length with hc
  set Lm : List ℕ := B ++ (L₀ ++ B).drop c with hLm
  refine RunsTo.mono
    (T := 1 + (1 + (1 + ((7 * c + 5) + (1 + (1 + (1 + (1 + ((5 * M + 5) + K))))))))) ?_ (by omega)
  refine RunsTo.seq (mid := At K (fun v => v 0 = K + M ∧ v 11 = K + M ∧ v 12 = c) (L₀ ++ B))
    (runsTo_copyReg (by omega) (by omega) (fun v hv => ?_)) ?_
  · obtain ⟨h11, h12⟩ := hQ v hv
    exact ⟨by rw [Mem.update_self, h11],
      by rw [Mem.update_of_ne _ _ (by omega : (11:ℕ) ≠ 0), h11],
      by rw [Mem.update_of_ne _ _ (by omega : (12:ℕ) ≠ 0), h12]⟩
  refine RunsTo.seq
    (mid := At K (fun v => v 0 = K + M ∧ v 1 = K ∧ v 11 = K + M ∧ v 12 = c) (L₀ ++ B))
    (runsTo_assignReg (by omega) (fun v hv => ?_)) ?_
  · obtain ⟨h0, h11, h12⟩ := hv
    exact ⟨by rw [Mem.update_of_ne _ _ (by omega : (0:ℕ) ≠ 1), h0], by rw [Mem.update_self],
      by rw [Mem.update_of_ne _ _ (by omega : (11:ℕ) ≠ 1), h11],
      by rw [Mem.update_of_ne _ _ (by omega : (12:ℕ) ≠ 1), h12]⟩
  refine RunsTo.seq
    (mid := At K (fun v => v 0 = K + M ∧ v 1 = K ∧ v 2 = c ∧ v 11 = K + M ∧ v 12 = c) (L₀ ++ B))
    (runsTo_copyReg (by omega) (by omega) (fun v hv => ?_)) ?_
  · obtain ⟨h0, h1, h11, h12⟩ := hv
    exact ⟨by rw [Mem.update_of_ne _ _ (by omega : (0:ℕ) ≠ 2), h0],
      by rw [Mem.update_of_ne _ _ (by omega : (1:ℕ) ≠ 2), h1],
      by rw [Mem.update_self, h12], by rw [Mem.update_of_ne _ _ (by omega : (11:ℕ) ≠ 2), h11],
      by rw [Mem.update_of_ne _ _ (by omega : (12:ℕ) ≠ 2), h12]⟩
  refine runsTo_of_At (wf_seq wf_copyBlock (wf_seq (wf_assign _ _) (wf_seq (wf_addTo _ _ _)
    (wf_seq (wf_assign _ _) (wf_seq (wf_subTo _ _ _) (wf_seq wf_fillZero
      (runsTo_clearRange K (fun _ => 0)).wf)))))) (fun v hv => ?_)
  obtain ⟨hv0, hv1, hv2, hv11, hv12⟩ := hv
  set m₁ : Mem := memAt K v (L₀ ++ B) with hm₁
  have e0 : m₁ 0 = K + M := by rw [hm₁, memAt_of_lt _ _ (by omega : (0:ℕ) < K), hv0]
  have e1 : m₁ 1 = K := by rw [hm₁, memAt_of_lt _ _ (by omega : (1:ℕ) < K), hv1]
  have e2 : m₁ 2 = c := by rw [hm₁, memAt_of_lt _ _ (by omega : (2:ℕ) < K), hv2]
  refine RunsTo.seq (mid := At K (fun u => u 11 = K + M ∧ u 12 = c) Lm) ?_ ?_
  · refine RunsTo.mono (T := 7 * m₁ 2 + 5) ?_ (by rw [e2])
    refine (Arrays.runsTo_copyBlock 0 1 2 3 (by omega) (by omega) (by omega) m₁
      (show 3 + 5 ≤ m₁ 0 by rw [e0]; omega) (show 3 + 5 ≤ m₁ 1 by rw [e1]; omega)
      (Or.inl (show m₁ 1 ≤ m₁ 0 by rw [e0, e1]; omega))).weaken (fun m hm => ?_)
    obtain ⟨hcopy, hout⟩ := hm
    have hfix : ∀ z, ¬ (K ≤ z ∧ z < K + c) → ¬ (3 ≤ z ∧ z ≤ 7) → m z = m₁ z := by
      intro z hz hz'
      refine hout z (by rw [e1, e2]; exact hz) ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      omega
    have hhigh : ∀ x, m (K + x) = Lm.getD x 0 := by
      intro x
      rw [hLm, hLmget]
      by_cases hx : x < c
      · rw [if_pos hx]
        have hKx : K + x = m₁ 1 + x := by rw [e1]
        rw [hKx, hcopy _ (show x < m₁ 2 by rw [e2]; exact hx), e0, Nat.add_assoc, hm₁, memAt_add]
        rw [List.getD_append_right L₀ B 0 (M + x) (by omega)]
        congr 1
        omega
      · rw [if_neg hx, hfix _ (by omega) (by omega), hm₁, memAt_add]
    refine ⟨m, ⟨?_, ?_⟩, eq_memAt K hhigh⟩
    · rw [hfix _ (by omega) (by omega), hm₁, memAt_of_lt _ _ (by omega : (11:ℕ) < K), hv11]
    · rw [hfix _ (by omega) (by omega), hm₁, memAt_of_lt _ _ (by omega : (12:ℕ) < K), hv12]
  refine RunsTo.seq (mid := At K (fun u => u 0 = K ∧ u 11 = K + M ∧ u 12 = c) Lm)
    (runsTo_assignReg (by omega) (fun u hu => ?_)) ?_
  · exact ⟨by rw [Mem.update_self], by rw [Mem.update_of_ne _ _ (by omega : (11:ℕ) ≠ 0), hu.1],
      by rw [Mem.update_of_ne _ _ (by omega : (12:ℕ) ≠ 0), hu.2]⟩
  refine RunsTo.seq (mid := At K (fun u => u 0 = K + c ∧ u 11 = K + M ∧ u 12 = c) Lm)
    (runsTo_addReg (by omega) (by omega) (by omega) (fun u hu => ?_)) ?_
  · obtain ⟨h0, h11, h12⟩ := hu
    exact ⟨by rw [Mem.update_self, h0, h12],
      by rw [Mem.update_of_ne _ _ (by omega : (11:ℕ) ≠ 0), h11],
      by rw [Mem.update_of_ne _ _ (by omega : (12:ℕ) ≠ 0), h12]⟩
  refine RunsTo.seq (mid := At K (fun u => u 0 = K + c ∧ u 2 = K ∧ u 11 = K + M) Lm)
    (runsTo_assignReg (by omega) (fun u hu => ?_)) ?_
  · obtain ⟨h0, h11, h12⟩ := hu
    exact ⟨by rw [Mem.update_of_ne _ _ (by omega : (0:ℕ) ≠ 2), h0], by rw [Mem.update_self],
      by rw [Mem.update_of_ne _ _ (by omega : (11:ℕ) ≠ 2), h11]⟩
  refine RunsTo.seq (mid := At K (fun u => u 0 = K + c ∧ u 1 = M) Lm)
    (runsTo_subReg (by omega) (by omega) (by omega) (fun u hu => ?_)) ?_
  · obtain ⟨h0, h2, h11⟩ := hu
    refine ⟨by rw [Mem.update_of_ne _ _ (by omega : (0:ℕ) ≠ 1), h0], ?_⟩
    rw [Mem.update_self, h11, h2]
    omega
  refine RunsTo.seq (mid := At K (fun _ => True) B) ?_ ?_
  · refine runsTo_of_At wf_fillZero (fun u hu => ?_)
    obtain ⟨hu0, hu1⟩ := hu
    set m₂ : Mem := memAt K u Lm with hm₂
    have f0 : m₂ 0 = K + c := by rw [hm₂, memAt_of_lt _ _ (by omega : (0:ℕ) < K), hu0]
    have f1 : m₂ 1 = M := by rw [hm₂, memAt_of_lt _ _ (by omega : (1:ℕ) < K), hu1]
    refine RunsTo.mono (T := 5 * m₂ 1 + 5) ?_ (by rw [f1])
    refine (Arrays.runsTo_fillZero 0 1 3 (by omega) (by omega) m₂
      (show 3 + 4 ≤ m₂ 0 by rw [f0]; omega)).weaken (fun m hm => ?_)
    obtain ⟨hzero, hout⟩ := hm
    have hnotscratch : ∀ z, K ≤ z → z ∉ [3, 3 + 1, 3 + 2, 3 + 3] := by
      intro z hz
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      omega
    refine ⟨m, trivial, eq_memAt K (fun x => ?_)⟩
    by_cases hx : x < c
    · rw [hout _ (by rw [f0, f1]; omega) (hnotscratch _ (by omega)), hm₂, memAt_add, hLm,
        hLmget, if_pos hx]
    · rw [List.getD_eq_default _ _ (by omega)]
      by_cases hx' : x < c + M
      · exact hzero _ (by rw [f0]; omega) (by rw [f0, f1]; omega)
      · rw [hout _ (by rw [f0, f1]; omega) (hnotscratch _ (by omega)), hm₂, memAt_add,
          List.getD_eq_default _ _ (by rw [hLm, hLmlen]; omega)]
  refine runsTo_of_At (runsTo_clearRange K (fun _ => 0)).wf (fun u _ => ?_)
  exact (runsTo_clearRange K (memAt K u B)).weaken (fun m' hm' => by
    rw [hm', zeroBelow_memAt])

/-- Reading an entry of the workspace by its fixed index. -/
theorem runsTo_copyFromList {K x i : ℕ} (hx : x < K) {Q Q' : Mem → Prop} {L : List ℕ}
    (hQ' : ∀ w, Q w → Q' (w.update x (L.getD i 0))) :
    RunsTo (copyTo x (K + i)) (At K Q L) (At K Q' L) 1 :=
  runsTo_of_At (wf_copyTo _ _) (fun w hw => runsTo_copyTo x (K + i) (fun m hm => by
    rw [hm, memAt_add, memAt_update_of_lt _ _ hx]
    exact ⟨_, hQ' w hw, rfl⟩))

/-- The segment of `A ++ (B ++ C)` occupied by `B`. -/
theorem seg_middle (A B C : List ℕ) :
    (((A ++ (B ++ C)).drop A.length).take B.length) = B := by
  rw [List.drop_left, List.take_left]

/-- The segment of `A ++ C` occupied by `A`. -/
theorem seg_prefix (A C : List ℕ) : (((A ++ C).drop 0).take A.length) = A := by
  rw [List.drop_zero, List.take_left]

/-! ## Advancing the top pointer over a block of zeros

Appending zeros to the list does not change the memory (`memAt_append_zeros`), so the workspace
registers a callee expects below its input are produced by advancing the top pointer, with
nothing to write. -/

/-- `pushZeros j` appends `j` zero entries to the list, by advancing the top pointer. -/
def pushZeros (j : ℕ) : Program := seq (assign 10 j) (addTo 8 8 10)

theorem runsTo_pushZeros {K j : ℕ} (hK : 16 ≤ K) {Q Q' : Mem → Prop} {L : List ℕ}
    (hQ : ∀ w, Q w → w 8 = K + L.length)
    (hQ' : ∀ w w', Q w → (∀ z, z ≠ 8 → z ≠ 10 → w' z = w z) → w' 8 = K + L.length + j →
      Q' w') :
    RunsTo (pushZeros j) (At K Q L) (At K Q' (L ++ List.replicate j 0)) 2 := by
  refine runsTo_of_At (wf_seq (wf_assign _ _) (wf_addTo _ _ _)) (fun w hw => ?_)
  have h8 := hQ w hw
  refine RunsTo.mono (T := 1 + 1) ?_ (le_refl _)
  refine RunsTo.seq (mid := fun m => m = memAt K (w.update 10 j) L)
    (runsTo_assign 10 j (fun m hm => by
      rw [hm, memAt_update_of_lt _ _ (by omega : (10:ℕ) < K)])) ?_
  refine runsTo_addTo 8 8 10 (fun m hm => ?_)
  rw [hm, memAt_of_lt _ _ (by omega : (8:ℕ) < K), memAt_of_lt _ _ (by omega : (10:ℕ) < K),
    Mem.update_of_ne _ _ (by omega : (8:ℕ) ≠ 10), Mem.update_self, h8,
    memAt_update_of_lt _ _ (by omega : (8:ℕ) < K)]
  refine ⟨_, hQ' w _ hw (fun z hz8 hz10 => ?_) ?_, (memAt_append_zeros K _ L j).symm⟩
  · rw [Mem.update_of_ne _ _ hz8, Mem.update_of_ne _ _ hz10]
  · rw [Mem.update_self]

/-! ## Calling a routine of the workspace convention -/

/-- The call rule of `Workspace/Machine/Reloc.lean` for an arbitrary pair of memories: the proof
there is stated for the top-level convention, but uses nothing of it.  This is the form the
workspace convention needs. -/
theorem runsTo_reloc_mem {P : Program} {M M' : Mem} {T : ℕ}
    (h : RunsTo P (fun m => m = M) (fun m' => m' = M') T)
    {b u v d : ℕ} (hok : Reloc.Ok b u v d) (m₀ : Mem)
    (hs : Reloc.Shifted d M m₀) (hb : m₀ b = d) :
    RunsTo (Reloc.relocate b u v P) (fun m => m = m₀)
      (fun m' => Reloc.Shifted d M' m' ∧ Reloc.LowAgree d u v m₀ m') (10 * T) := by
  refine ⟨Reloc.wf_relocate h.wf, fun m hm => ?_⟩
  subst hm
  obtain ⟨k, hk, hhalt, hmem⟩ := h.spec M rfl
  obtain ⟨n, hn, m'', hrun, hs'', hlow⟩ := Reloc.run_reloc h.wf hok hs hb k
  refine ⟨n, le_trans hn (Nat.mul_le_mul_left 10 hk), ?_, ?_⟩
  · exact Reloc.halted_reloc h.wf hhalt (by rw [hrun])
  · rw [hrun]
    exact ⟨by rw [← hmem]; exact hs'', hlow⟩

/-- The workspace convention read as a list: `K` zeros, then the length, then the entries. -/
theorem initMemAt_getD (K : ℕ) (l : List ℕ) (x : ℕ) :
    initMemAt K l x = (List.replicate K 0 ++ (l.length :: l)).getD x 0 := by
  rcases Nat.lt_or_ge x K with hx | hx
  · rw [initMemAt_of_lt _ hx,
      List.getD_append (List.replicate K 0) _ 0 x (by simpa using hx),
      List.getD_replicate _ hx]
  · have hlen : (List.replicate K 0).length ≤ x := by simpa using hx
    rw [List.getD_append_right (List.replicate K 0) _ 0 x hlen]
    have : x = K + (x - K) := by omega
    rw [this, initMemAt_add, initMem_getD]
    simp

/-- `callTopAt K P` calls the relocated routine `P` of the *workspace* convention on the topmost
block of the workspace, whose base address is held in register `0`, and resets the top pointer.
Register `0` is left holding the base plus `K`. -/
def callTopAt (K : ℕ) (P : Program) : Program :=
  seq (Reloc.relocate 0 1 2 P) (seq (assign 10 K) (seq (addTo 0 0 10)
    (seq (loadTo 8 0) (seq (addTo 8 8 0) (seq (assign 10 1) (addTo 8 8 10))))))

/-- **Calling a clean routine of the workspace convention on the topmost block.** -/
theorem runsTo_callTopAt {K : ℕ} (hK : 16 ≤ K) {P : Program} {l l' : List ℕ} {T : ℕ}
    (h : RunsTo P (fun m => m = initMemAt K l) (fun m' => m' = initMemAt K l') T)
    {Q Q' : Mem → Prop} {L₀ : List ℕ}
    (hQ : ∀ w, Q w → w 0 = K + L₀.length)
    (hQ' : ∀ w w', Q w → (∀ z, z < K → z ≠ 0 → z ≠ 1 → z ≠ 2 → z ≠ 8 → z ≠ 10 → w' z = w z) →
      w' 0 = K + L₀.length + K → w' 8 = K + L₀.length + (K + (l'.length + 1)) → Q' w') :
    RunsTo (callTopAt K P) (At K Q (L₀ ++ (List.replicate K 0 ++ (l.length :: l))))
      (At K Q' (L₀ ++ (List.replicate K 0 ++ (l'.length :: l')))) (10 * T + 6) := by
  refine runsTo_of_At (wf_seq (Reloc.wf_relocate h.wf) (wf_seq (wf_assign _ _)
    (wf_seq (wf_addTo _ _ _) (wf_seq (wf_loadTo _ _) (wf_seq (wf_addTo _ _ _)
      (wf_seq (wf_assign _ _) (wf_addTo _ _ _))))))) (fun w hw => ?_)
  have h0 := hQ w hw
  set d : ℕ := K + L₀.length with hd
  set Lf : List ℕ := L₀ ++ (List.replicate K 0 ++ (l'.length :: l')) with hLf
  set m₀ : Mem := memAt K w (L₀ ++ (List.replicate K 0 ++ (l.length :: l))) with hm₀
  have hgetd : Lf.getD (L₀.length + K) 0 = l'.length := by
    rw [hLf, List.getD_append_right L₀ _ 0 _ (by omega)]
    have : L₀.length + K - L₀.length = (List.replicate K 0).length := by simp
    rw [this, List.getD_append_right (List.replicate K 0) _ 0 _ (le_refl _)]
    simp
  have hs : Reloc.Shifted d (initMemAt K l) m₀ := by
    intro x
    rw [hd, Nat.add_assoc, hm₀, memAt_add, List.getD_append_right L₀ _ 0 _ (by omega),
      initMemAt_getD]
    congr 1
    omega
  have hb : m₀ 0 = d := by rw [hm₀, memAt_of_lt _ _ (by omega : (0:ℕ) < K), h0]
  have hok : Reloc.Ok 0 1 2 d :=
    ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
  refine RunsTo.mono (T := 10 * T + (1 + (1 + (1 + (1 + (1 + 1)))))) ?_ (by omega)
  refine RunsTo.seq
    (mid := At K (fun v => v 0 = d ∧ ∀ z, z < K → z ≠ 1 → z ≠ 2 → v z = w z) Lf) ?_ ?_
  · refine (runsTo_reloc_mem h hok m₀ hs hb).weaken (fun m hm => ?_)
    obtain ⟨hsh, hlow⟩ := hm
    have hlow' : ∀ z, z < K → z ≠ 1 → z ≠ 2 → m z = w z := by
      intro z hz hz1 hz2
      rw [hlow z (by omega) hz1 hz2, hm₀, memAt_of_lt _ _ hz]
    have hhigh : ∀ x, m (K + x) = Lf.getD x 0 := by
      intro x
      rcases Nat.lt_or_ge x L₀.length with hx | hx
      · rw [hlow (K + x) (by omega) (by omega) (by omega), hm₀, memAt_add,
          List.getD_append _ _ _ _ hx, hLf, List.getD_append _ _ _ _ hx]
      · have hKx : K + x = d + (x - L₀.length) := by omega
        rw [hKx, hsh, initMemAt_getD, hLf, List.getD_append_right L₀ _ 0 _ hx]
    exact ⟨m, ⟨by rw [hlow' _ (by omega) (by omega) (by omega), h0], hlow'⟩, eq_memAt K hhigh⟩
  refine RunsTo.seq
    (mid := At K (fun v => v 0 = d ∧ v 10 = K ∧
      ∀ z, z < K → z ≠ 1 → z ≠ 2 → z ≠ 8 → z ≠ 10 → v z = w z) Lf)
    (runsTo_assignReg (by omega) (fun v hv => ?_)) ?_
  · refine ⟨by rw [Mem.update_of_ne _ _ (by omega : (0:ℕ) ≠ 10), hv.1], by rw [Mem.update_self],
      fun z hz hz1 hz2 hz8 hz10 => ?_⟩
    rw [Mem.update_of_ne _ _ hz10]
    exact hv.2 z hz hz1 hz2
  refine RunsTo.seq
    (mid := At K (fun v => v 0 = d + K ∧
      ∀ z, z < K → z ≠ 0 → z ≠ 1 → z ≠ 2 → z ≠ 8 → z ≠ 10 → v z = w z) Lf)
    (runsTo_addReg (by omega) (by omega) (by omega) (fun v hv => ?_)) ?_
  · obtain ⟨hv0, hv10, hva⟩ := hv
    refine ⟨by rw [Mem.update_self, hv0, hv10], fun z hz hz0 hz1 hz2 hz8 hz10 => ?_⟩
    rw [Mem.update_of_ne _ _ hz0]
    exact hva z hz hz1 hz2 hz8 hz10
  refine RunsTo.seq
    (mid := At K (fun v => v 0 = d + K ∧ v 8 = l'.length ∧
      ∀ z, z < K → z ≠ 0 → z ≠ 1 → z ≠ 2 → z ≠ 8 → z ≠ 10 → v z = w z) Lf)
    (runsTo_loadReg (i := L₀.length + K) (by omega) (by omega) (fun v hv => by
      rw [hv.1, hd]; omega) (fun v hv => ?_)) ?_
  · obtain ⟨hv0, hva⟩ := hv
    refine ⟨by rw [Mem.update_of_ne _ _ (by omega : (0:ℕ) ≠ 8), hv0],
      by rw [Mem.update_self, hgetd], fun z hz hz0 hz1 hz2 hz8 hz10 => ?_⟩
    rw [Mem.update_of_ne _ _ hz8]
    exact hva z hz hz0 hz1 hz2 hz8 hz10
  refine RunsTo.seq
    (mid := At K (fun v => v 0 = d + K ∧ v 8 = l'.length + (d + K) ∧
      ∀ z, z < K → z ≠ 0 → z ≠ 1 → z ≠ 2 → z ≠ 8 → z ≠ 10 → v z = w z) Lf)
    (runsTo_addReg (by omega) (by omega) (by omega) (fun v hv => ?_)) ?_
  · obtain ⟨hv0, hv8, hva⟩ := hv
    refine ⟨by rw [Mem.update_of_ne _ _ (by omega : (0:ℕ) ≠ 8), hv0],
      by rw [Mem.update_self, hv8, hv0], fun z hz hz0 hz1 hz2 hz8 hz10 => ?_⟩
    rw [Mem.update_of_ne _ _ hz8]
    exact hva z hz hz0 hz1 hz2 hz8 hz10
  refine RunsTo.seq
    (mid := At K (fun v => v 0 = d + K ∧ v 8 = l'.length + (d + K) ∧ v 10 = 1 ∧
      ∀ z, z < K → z ≠ 0 → z ≠ 1 → z ≠ 2 → z ≠ 8 → z ≠ 10 → v z = w z) Lf)
    (runsTo_assignReg (by omega) (fun v hv => ?_)) ?_
  · obtain ⟨hv0, hv8, hva⟩ := hv
    refine ⟨by rw [Mem.update_of_ne _ _ (by omega : (0:ℕ) ≠ 10), hv0],
      by rw [Mem.update_of_ne _ _ (by omega : (8:ℕ) ≠ 10), hv8], by rw [Mem.update_self],
      fun z hz hz0 hz1 hz2 hz8 hz10 => ?_⟩
    rw [Mem.update_of_ne _ _ hz10]
    exact hva z hz hz0 hz1 hz2 hz8 hz10
  refine runsTo_addReg (by omega) (by omega) (by omega) (fun v hv => ?_)
  obtain ⟨hv0, hv8, hv10, hva⟩ := hv
  refine hQ' w _ hw (fun z hz hz0 hz1 hz2 hz8 hz10 => ?_) ?_ ?_
  · rw [Mem.update_of_ne _ _ hz8]
    exact hva z hz hz0 hz1 hz2 hz8 hz10
  · rw [Mem.update_of_ne _ _ (by omega : (0:ℕ) ≠ 8), hv0, hd]
  · rw [Mem.update_self, hv8, hv10, hd]
    omega

/-- A segment of a list is unaffected by what is appended above it. -/
theorem seg_append (D R : List ℕ) (i c : ℕ) (h : i + c ≤ D.length) :
    (((D ++ R).drop i).take c) = (D.drop i).take c := by
  rw [List.drop_append_of_le_length (by omega), List.take_append_of_le_length (by simp; omega)]

end Layout
end RAM
