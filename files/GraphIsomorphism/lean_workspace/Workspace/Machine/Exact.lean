import Workspace.Machine.Layout

/-!
# Step-exact reasoning about RAM programs

The combinators of `Workspace/Machine/Closure.lean` and `PolyFun.lean` produce *polynomial*
bounds: every clean call rewrites its whole state, so a loop over a list of length `ℓ` costs
`ℓ` times the size of the state.  Linear (and other exact) running times need programs that
work in place, on arrays, and a way to count their steps.  This file adds the little that is
needed on top of the Hoare logic of `Workspace/Machine/Block.lean`.

* **Pointwise rules.**  Every specification below starts from one memory `M`
  (`fun m => m = M`), so that straight-line code is executed symbolically: each instruction
  replaces `M` by an explicit `Mem.update`.
* **The amortized loop rule** `RAM.Exact.runsTo_whileNz_amort`: a loop whose iterations have
  different costs.  The cost is paid out of a potential `Φ` of the memory: an iteration from `M`
  that runs `t` steps must leave a memory `M'` with `Φ M' + t + 2 ≤ Φ M`.  The whole loop then
  runs in `Φ M + 1` steps.
* **Blocks of memory.**  `RAM.Exact.Blk m p xs` says that the registers `p, p+1, …` hold the
  list `xs`; the lemmas read framed encodings (`frame`, `encList`) out of a block.
-/

namespace RAM

namespace Exact

/-! ## Pointwise rules for straight-line code -/

theorem seq_eq {P Q : Program} {M M' : Mem} {post : Mem → Prop} {T T' : ℕ}
    (hP : RunsTo P (fun m => m = M) (fun m => m = M') T)
    (hQ : RunsTo Q (fun m => m = M') post T') :
    RunsTo (seq P Q) (fun m => m = M) post (T + T') := hP.seq hQ

theorem assign_seq {x c : ℕ} {Q : Program} {M : Mem} {post : Mem → Prop} {T : ℕ}
    (h : RunsTo Q (fun m => m = M.update x c) post T) :
    RunsTo (seq (assign x c) Q) (fun m => m = M) post (1 + T) :=
  (runsTo_assign x c (fun m hm => by rw [hm])).seq h

theorem copy_seq {x y : ℕ} {Q : Program} {M : Mem} {post : Mem → Prop} {T : ℕ}
    (h : RunsTo Q (fun m => m = M.update x (M y)) post T) :
    RunsTo (seq (copyTo x y) Q) (fun m => m = M) post (1 + T) :=
  (runsTo_copyTo x y (fun m hm => by rw [hm])).seq h

theorem add_seq {x y z : ℕ} {Q : Program} {M : Mem} {post : Mem → Prop} {T : ℕ}
    (h : RunsTo Q (fun m => m = M.update x (M y + M z)) post T) :
    RunsTo (seq (addTo x y z) Q) (fun m => m = M) post (1 + T) :=
  (runsTo_addTo x y z (fun m hm => by rw [hm])).seq h

theorem sub_seq {x y z : ℕ} {Q : Program} {M : Mem} {post : Mem → Prop} {T : ℕ}
    (h : RunsTo Q (fun m => m = M.update x (M y - M z)) post T) :
    RunsTo (seq (subTo x y z) Q) (fun m => m = M) post (1 + T) :=
  (runsTo_subTo x y z (fun m hm => by rw [hm])).seq h

theorem load_seq {x y : ℕ} {Q : Program} {M : Mem} {post : Mem → Prop} {T : ℕ}
    (h : RunsTo Q (fun m => m = M.update x (M (M y))) post T) :
    RunsTo (seq (loadTo x y) Q) (fun m => m = M) post (1 + T) :=
  (runsTo_loadTo x y (fun m hm => by rw [hm])).seq h

theorem store_seq {x y : ℕ} {Q : Program} {M : Mem} {post : Mem → Prop} {T : ℕ}
    (h : RunsTo Q (fun m => m = M.update (M x) (M y)) post T) :
    RunsTo (seq (storeTo x y) Q) (fun m => m = M) post (1 + T) :=
  (runsTo_storeTo x y (fun m hm => by rw [hm])).seq h

theorem assign_last {x c : ℕ} {M : Mem} {post : Mem → Prop} (h : post (M.update x c)) :
    RunsTo (assign x c) (fun m => m = M) post 1 :=
  runsTo_assign x c (fun m hm => by rw [hm]; exact h)

theorem copy_last {x y : ℕ} {M : Mem} {post : Mem → Prop} (h : post (M.update x (M y))) :
    RunsTo (copyTo x y) (fun m => m = M) post 1 :=
  runsTo_copyTo x y (fun m hm => by rw [hm]; exact h)

theorem add_last {x y z : ℕ} {M : Mem} {post : Mem → Prop} (h : post (M.update x (M y + M z))) :
    RunsTo (addTo x y z) (fun m => m = M) post 1 :=
  runsTo_addTo x y z (fun m hm => by rw [hm]; exact h)

theorem sub_last {x y z : ℕ} {M : Mem} {post : Mem → Prop} (h : post (M.update x (M y - M z))) :
    RunsTo (subTo x y z) (fun m => m = M) post 1 :=
  runsTo_subTo x y z (fun m hm => by rw [hm]; exact h)

theorem load_last {x y : ℕ} {M : Mem} {post : Mem → Prop} (h : post (M.update x (M (M y)))) :
    RunsTo (loadTo x y) (fun m => m = M) post 1 :=
  runsTo_loadTo x y (fun m hm => by rw [hm]; exact h)

theorem store_last {x y : ℕ} {M : Mem} {post : Mem → Prop} (h : post (M.update (M x) (M y))) :
    RunsTo (storeTo x y) (fun m => m = M) post 1 :=
  runsTo_storeTo x y (fun m hm => by rw [hm]; exact h)

/-- A block with a general postcondition, followed by more code: the continuation is proved for
every memory the block may end in. -/
theorem block_seq {P Q : Program} {M : Mem} {mid post : Mem → Prop} {T T' : ℕ}
    (hP : RunsTo P (fun m => m = M) mid T)
    (hQ : ∀ M', mid M' → RunsTo Q (fun m => m = M') post T') :
    RunsTo (seq P Q) (fun m => m = M) post (T + T') := by
  obtain ⟨k, -, -, hmid⟩ := hP.spec M rfl
  exact hP.seq ⟨(hQ _ hmid).wf, fun m hm => (hQ m hm).spec m rfl⟩

/-- The conditional from one memory: only the branch that runs is paid for. -/
theorem ifz_ne {i : ℕ} {P Q : Program} {M : Mem} {post : Mem → Prop} {T : ℕ}
    (hi : M i ≠ 0) (hP : RunsTo P (fun m => m = M) post T) (hQ : Wf Q) :
    RunsTo (ifz i P Q) (fun m => m = M) post (T + 2) := by
  have := RunsTo.ifz (i := i) (pre := fun m => m = M) (T' := 0)
    (hP.strengthen (fun m hm => hm.1)) (runsTo_of_false hQ (fun m hm => by
      rw [hm.1] at hm; exact hi hm.2))
  simpa using this

theorem ifz_eq {i : ℕ} {P Q : Program} {M : Mem} {post : Mem → Prop} {T : ℕ}
    (hi : M i = 0) (hQ : RunsTo Q (fun m => m = M) post T) (hP : Wf P) :
    RunsTo (ifz i P Q) (fun m => m = M) post (T + 2) := by
  have := RunsTo.ifz (i := i) (pre := fun m => m = M) (T := 0)
    (runsTo_of_false hP (fun m hm => by rw [hm.1] at hm; exact hm.2 hi))
    (hQ.strengthen (fun m hm => hm.1))
  simpa [Nat.add_comm] using this

/-! ## The amortized loop rule -/

/-- **The amortized while rule.**  Each iteration, started in a memory `M` of the invariant with
register `i` nonzero, runs some `t` steps and ends in a memory `M'` of the invariant with
`Φ M' + t + 2 ≤ Φ M`.  Then the loop, started in `M`, runs within `Φ M + 1` steps. -/
theorem runsTo_whileNz_amort {i : ℕ} {P : Program} (hw : Wf P) (inv : Mem → Prop)
    (Φ : Mem → ℕ)
    (hP : ∀ M, inv M → M i ≠ 0 → ∃ t, RunsTo P (fun m => m = M)
      (fun m' => inv m' ∧ Φ m' + t + 2 ≤ Φ M) t) :
    ∀ M, inv M → RunsTo (whileNz i P) (fun m => m = M) (fun m' => inv m' ∧ m' i = 0)
      (Φ M + 1) := by
  intro M hM
  refine ⟨wf_whileNz hw, ?_⟩
  set W := whileNz i P with hW
  have hjz : ∀ m : Mem, W[(⟨0, m⟩ : Config).pc]? = some (Instr.jz i (P.length + 2)) :=
    fun _ => rfl
  have hjump : W[1 + P.length]? = some (Instr.jump 0) := by
    simp [hW, whileNz, Nat.add_comm]
  have hexit : ∀ m : Mem, m i = 0 → run W ⟨0, m⟩ 1 = ⟨P.length + 2, m⟩ := by
    intro m h0
    rw [run_succ, run_zero, step_of_get (hjz m) (by simp)]
    simp [exec, h0]
  have key : ∀ (N : ℕ) (m : Mem), inv m → Φ m ≤ N →
      ∃ k ≤ Φ m + 1, Halted W (run W ⟨0, m⟩ k) ∧
        (inv (run W ⟨0, m⟩ k).mem ∧ (run W ⟨0, m⟩ k).mem i = 0) := by
    intro N
    induction N with
    | zero =>
        intro m hm hΦ
        by_cases h0 : m i = 0
        · exact ⟨1, by omega, by rw [hexit m h0]; exact halted_of_pc_length (by simp [hW]),
            by rw [hexit m h0]; exact ⟨hm, h0⟩⟩
        · obtain ⟨t, ht⟩ := hP m hm h0
          obtain ⟨k, -, m', -, ⟨-, hle⟩, -⟩ := ht.halt_at rfl
          omega
    | succ N ih =>
        intro m hm hΦ
        by_cases h0 : m i = 0
        · exact ⟨1, by omega, by rw [hexit m h0]; exact halted_of_pc_length (by simp [hW]),
            by rw [hexit m h0]; exact ⟨hm, h0⟩⟩
        · obtain ⟨t, ht⟩ := hP m hm h0
          obtain ⟨k, hkT, m', hkrun, ⟨hinv', hle⟩, hkmin⟩ := ht.halt_at rfl
          obtain ⟨k', hk'T, hk'halt, hk'post⟩ := ih m' hinv' (by omega)
          have hstep : run W ⟨0, m⟩ 1 = ⟨1, m⟩ := by
            rw [run_succ, run_zero, step_of_get (hjz m) (by simp)]
            simp [exec, h0]
          have hbody : run W ⟨1, m⟩ k = ⟨1 + P.length, m'⟩ := by
            rw [run_block (A := [Instr.jz i (P.length + 2)]) (Q := P)
              (B := [Instr.jump 0]) (by simp [hW, whileNz]) (by simp) k hkmin, hkrun]
          have hback : run W ⟨1 + P.length, m'⟩ 1 = ⟨0, m'⟩ := by
            rw [run_succ, run_zero, step_of_get (by simpa using hjump) (by simp)]
            simp [exec]
          refine ⟨1 + k + 1 + k', by omega, ?_, ?_⟩ <;>
            rw [run_add, run_add, run_add, hstep, hbody, hback]
          · exact hk'halt
          · exact hk'post
  rintro m rfl
  exact key _ m hM le_rfl

/-! ## Blocks of memory -/

/-- The registers `p, p + 1, …, p + |xs| - 1` hold the list `xs`. -/
def Blk (m : Mem) (p : ℕ) (xs : List ℕ) : Prop := ∀ j (h : j < xs.length), m (p + j) = xs[j]

theorem Blk.append {m : Mem} {p : ℕ} {xs ys : List ℕ} :
    Blk m p (xs ++ ys) ↔ Blk m p xs ∧ Blk m (p + xs.length) ys := by
  constructor
  · intro h
    refine ⟨fun j hj => ?_, fun j hj => ?_⟩
    · rw [h j (by simp; omega), List.getElem_append_left hj]
    · rw [show p + xs.length + j = p + (xs.length + j) by omega, h _ (by simp; omega),
        List.getElem_append_right (by omega)]
      simp
  · rintro ⟨h1, h2⟩ j hj
    by_cases hj' : j < xs.length
    · rw [h1 j hj', List.getElem_append_left hj']
    · have := h2 (j - xs.length) (by simp at hj; omega)
      rw [show p + xs.length + (j - xs.length) = p + j by omega] at this
      rw [this, List.getElem_append_right (by omega)]

theorem Blk.cons {m : Mem} {p x : ℕ} {xs : List ℕ} :
    Blk m p (x :: xs) ↔ m p = x ∧ Blk m (p + 1) xs := by
  constructor
  · intro h
    refine ⟨by simpa using h 0 (by simp), fun j hj => ?_⟩
    rw [show p + 1 + j = p + (j + 1) by omega, h (j + 1) (by simp; omega)]
    simp
  · rintro ⟨h1, h2⟩ j hj
    rcases j with _ | j
    · simpa using h1
    · rw [show p + (j + 1) = p + 1 + j by omega, h2 j (by simp at hj; omega)]
      simp

theorem Blk.nil (m : Mem) (p : ℕ) : Blk m p [] := fun j hj => absurd hj (by simp)

/-- A framed list: its length, then its entries. -/
theorem Blk.frame_iff {m : Mem} {p : ℕ} {xs : List ℕ} :
    Blk m p (frame xs) ↔ m p = xs.length ∧ Blk m (p + 1) xs := Blk.cons

/-- A block is unchanged by writes outside it. -/
theorem Blk.update {m : Mem} {p : ℕ} {xs : List ℕ} (h : Blk m p xs) {a v : ℕ}
    (ha : a < p ∨ p + xs.length ≤ a) : Blk (m.update a v) p xs := by
  intro j hj
  rw [Mem.update_of_ne _ _ (by omega)]
  exact h j hj

theorem Blk.congr {m m' : Mem} {p : ℕ} {xs : List ℕ} (h : Blk m p xs)
    (he : ∀ z, p ≤ z → z < p + xs.length → m' z = m z) : Blk m' p xs := by
  intro j hj
  rw [he _ (by omega) (by omega)]
  exact h j hj

/-- The head of an encoded list, framed: `encList f (a :: l) = frame (f a) ++ encList f l`. -/
theorem Blk.encList_cons {α : Type*} {f : α → List ℕ} {m : Mem} {p : ℕ} {a : α} {l : List α} :
    Blk m p (encList f (a :: l)) ↔
      m p = (f a).length ∧ Blk m (p + 1) (f a) ∧ Blk m (p + 1 + (f a).length) (encList f l) := by
  rw [encList, Blk.append, Blk.frame_iff]
  simp [RAM.frame, Nat.add_assoc, Nat.add_comm 1, and_assoc]

/-- The encoding of a natural number is itself. -/
theorem Blk.encode_nat {m : Mem} {p x : ℕ} : Blk m p (Enc.encode x) ↔ m p = x := by
  change Blk m p [x] ↔ _
  rw [Blk.cons]; simp [Blk.nil]

/-- The encoding of a pair. -/
theorem Blk.encode_pair {α β : Type*} [Enc α] [Enc β] {m : Mem} {p : ℕ} {a : α} {b : β} :
    Blk m p (Enc.encode (a, b)) ↔
      m p = (Enc.encode a).length ∧ Blk m (p + 1) (Enc.encode a) ∧
        m (p + 1 + (Enc.encode a).length) = (Enc.encode b).length ∧
          Blk m (p + 1 + (Enc.encode a).length + 1) (Enc.encode b) := by
  change Blk m p (frame (Enc.encode a) ++ frame (Enc.encode b)) ↔ _
  rw [Blk.append, Blk.frame_iff, Blk.frame_iff]
  simp [RAM.frame, Nat.add_assoc, Nat.add_comm 1, and_assoc]

theorem encode_list_eq {α : Type*} [Enc α] (l : List α) :
    Enc.encode l = encList Enc.encode l := rfl

/-! ## Loops over framed lists

`encList f xs` stores the elements of `xs` one after the other, each preceded by its length.
`framesLoop rp re rc rt B` walks such a list: register `rp` points at the current element, `re`
at the end of the list, `rc` holds the distance to the end (the loop test) and `rt` is a
temporary.  The body `B` handles the element at `rp`; the loop then advances `rp` past it.
Register `1` must hold the constant `1`. -/

theorem encList_append {α : Type*} (f : α → List ℕ) (a b : List α) :
    encList f (a ++ b) = encList f a ++ encList f b := by
  induction a with
  | nil => rfl
  | cons x a ih => simp [encList, ih]

theorem encList_split {α : Type*} (f : α → List ℕ) (xs : List α) (j : ℕ) (hj : j < xs.length) :
    encList f xs = encList f (xs.take j) ++ (frame (f xs[j]) ++ encList f (xs.drop (j + 1))) := by
  have e : xs.take j ++ xs[j] :: xs.drop (j + 1) = xs := by
    rw [← List.drop_eq_getElem_cons hj, List.take_append_drop]
  calc encList f xs = encList f (xs.take j ++ xs[j] :: xs.drop (j + 1)) := by rw [e]
    _ = _ := by rw [encList_append]; rfl

theorem encList_take_succ {α : Type*} (f : α → List ℕ) (xs : List α) (j : ℕ)
    (hj : j < xs.length) :
    encList f (xs.take (j + 1)) = encList f (xs.take j) ++ frame (f xs[j]) := by
  rw [List.take_succ, List.getElem?_eq_getElem hj, Option.toList_some, encList_append]
  simp [encList]

/-- The element number `j` of a framed list, inside a block holding the list. -/
theorem Blk.encList_get {α : Type*} {f : α → List ℕ} {m : Mem} {p : ℕ} {xs : List α}
    (h : Blk m p (encList f xs)) (j : ℕ) (hj : j < xs.length) :
    Blk m (p + (encList f (xs.take j)).length) (frame (f xs[j])) := by
  rw [encList_split f xs j hj, Blk.append, Blk.append] at h
  exact h.2.1

theorem encList_take_lt {α : Type*} (f : α → List ℕ) (xs : List α) (j : ℕ) (hj : j < xs.length) :
    (encList f (xs.take j)).length + 1 + (f xs[j]).length ≤ (encList f xs).length := by
  rw [encList_split f xs j hj]
  simp [RAM.frame]; omega

theorem encList_take_le {α : Type*} (f : α → List ℕ) (xs : List α) (j : ℕ) :
    (encList f (xs.take j)).length ≤ (encList f xs).length := by
  conv_rhs => rw [← List.take_append_drop j xs]
  rw [encList_append]; simp

theorem encList_take_length {α : Type*} (f : α → List ℕ) (xs : List α) :
    encList f (xs.take xs.length) = encList f xs := by rw [List.take_length]

/-- The loop over a framed list. -/
def framesLoop (rp re rc rt : ℕ) (B : Program) : Program :=
  seq (subTo rc re rp) (whileNz rc (seq B (seq (loadTo rt rp) (seq (addTo rp rp rt)
    (seq (addTo rp rp 1) (subTo rc re rp))))))

/-- **The loop over a framed list.**  `I j` is the invariant after `j` elements.  The body,
started at element `j`, runs some `t` steps, keeps the pointers, the constant `1` and the list,
and pays for itself out of `c₀ + c₁ · |f xs[j]|` plus the decrease of an extra potential `Ψ`
(for work done on other data, as when two lists are walked side by side). -/
theorem runsTo_framesLoop {α : Type*} (f : α → List ℕ) (xs : List α) (p0 : ℕ)
    {rp re rc rt : ℕ}
    (hd : rp ≠ re ∧ rp ≠ rc ∧ rp ≠ rt ∧ rp ≠ 1 ∧ re ≠ rc ∧ re ≠ rt ∧ re ≠ 1 ∧ rc ≠ rt ∧
      rc ≠ 1 ∧ rt ≠ 1)
    (hlo : rp < p0 ∧ rc < p0 ∧ rt < p0)
    {B : Program} (hBw : Wf B) (I : ℕ → Mem → Prop) (Ψ : Mem → ℕ) (c0 c1 : ℕ)
    (hstab : ∀ j m v, I j m → I j (m.update rp v) ∧ I j (m.update rc v) ∧ I j (m.update rt v))
    (hΨ : ∀ m v, Ψ (m.update rp v) = Ψ m ∧ Ψ (m.update rc v) = Ψ m ∧ Ψ (m.update rt v) = Ψ m)
    (hB : ∀ j (hj : j < xs.length) (M : Mem), I j M →
      M rp = p0 + (encList f (xs.take j)).length → M re = p0 + (encList f xs).length →
      M 1 = 1 → Blk M p0 (encList f xs) →
      ∃ t, RunsTo B (fun m => m = M) (fun m' => I (j + 1) m' ∧ m' rp = M rp ∧ m' re = M re ∧
        m' 1 = 1 ∧ Blk m' p0 (encList f xs) ∧ Ψ m' + t ≤ Ψ M + c0 + c1 * (f xs[j]).length) t) :
    ∀ M, I 0 M → M rp = p0 → M re = p0 + (encList f xs).length → M 1 = 1 →
      Blk M p0 (encList f xs) →
      RunsTo (framesLoop rp re rc rt B) (fun m => m = M)
        (fun m' => I xs.length m' ∧ m' rp = M re ∧ m' re = M re ∧ m' 1 = 1 ∧
          Blk m' p0 (encList f xs))
        (Ψ M + (c0 + c1 + 8) * (encList f xs).length + 2) := by
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10⟩ := hd
  intro M hI0 hp he h1 hblk
  set E := encList f xs with hE
  let pos : ℕ → ℕ := fun j => p0 + (encList f (xs.take j)).length
  have hpos : ∀ j, pos j = p0 + (encList f (xs.take j)).length := fun _ => rfl
  set K := c0 + c1 + 8 with hK
  let inv : Mem → Prop := fun m => ∃ j ≤ xs.length, I j m ∧ m rp = pos j ∧
    m re = p0 + E.length ∧ m rc = p0 + E.length - pos j ∧ m 1 = 1 ∧ Blk m p0 E
  let Φ : Mem → ℕ := fun m => Ψ m + K * (m re - m rp)
  have hw : Wf (seq B (seq (loadTo rt rp) (seq (addTo rp rp rt) (seq (addTo rp rp 1)
      (subTo rc re rp))))) :=
    wf_seq hBw (wf_seq (Layout.wf_loadTo _ _) (wf_seq (Layout.wf_addTo _ _ _)
      (wf_seq (Layout.wf_addTo _ _ _) (Layout.wf_subTo _ _ _))))
  have hloop := runsTo_whileNz_amort (i := rc) hw inv Φ (by
    rintro M' ⟨j, hj, hI, hrp, hre, hrc, h1', hblk'⟩ hne
    have hjl : j < xs.length := by
      rcases Nat.lt_or_ge j xs.length with h | h
      · exact h
      · exfalso; apply hne
        have : j = xs.length := by omega
        subst this
        rw [hrc, hpos, encList_take_length, ← hE, Nat.sub_self]
    obtain ⟨t, ht⟩ := hB j hjl M' hI hrp hre h1' hblk'
    refine ⟨t + 4, block_seq (Q := seq (loadTo rt rp) (seq (addTo rp rp rt) (seq (addTo rp rp 1)
      (subTo rc re rp)))) (T' := 4) ht (fun M'' hM'' => ?_)⟩
    obtain ⟨hI', hrp', hre', h1'', hblk'', hΨ'⟩ := hM''
    have hfr := (hblk''.encList_get j hjl)
    rw [Blk.frame_iff] at hfr
    have hlen : M'' (pos j) = (f xs[j]).length := hfr.1
    have hlt := encList_take_lt f xs j hjl
    have hsucc := encList_take_succ f xs j hjl
    have hnewp : pos j + (f xs[j]).length + 1 = pos (j + 1) := by
      simp only [hpos, hsucc, List.length_append, RAM.frame, List.length_cons]; omega
    refine load_seq (add_seq (add_seq (sub_last ?_)))
    set m1 := M''.update rt (M'' (M'' rp)) with hm1
    set m2 := m1.update rp (m1 rp + m1 rt) with hm2
    set m3 := m2.update rp (m2 rp + m2 1) with hm3
    have e1rp : m1 rp = pos j := by rw [hm1, Mem.update_of_ne _ _ d3, hrp', hrp]
    have e1rt : m1 rt = (f xs[j]).length := by rw [hm1, Mem.update_self, hrp', hrp, hlen]
    have e2rp : m2 rp = pos j + (f xs[j]).length := by rw [hm2, Mem.update_self, e1rp, e1rt]
    have e21 : m2 1 = 1 := by
      rw [hm2, Mem.update_of_ne _ _ d4.symm, hm1, Mem.update_of_ne _ _ d10.symm, h1'']
    have e3rp : m3 rp = pos (j + 1) := by rw [hm3, Mem.update_self, e2rp, e21, hnewp]
    have e3re : m3 re = p0 + E.length := by
      rw [hm3, Mem.update_of_ne _ _ d1.symm, hm2, Mem.update_of_ne _ _ d1.symm, hm1,
        Mem.update_of_ne _ _ d6, hre', hre]
    have e31 : m3 1 = 1 := by rw [hm3, Mem.update_of_ne _ _ d4.symm, e21]
    have hΨ3 : Ψ m3 = Ψ M'' := by
      rw [hm3, (hΨ _ _).1, hm2, (hΨ _ _).1, hm1, (hΨ _ _).2.2]
    have hI3 : I (j + 1) m3 := by
      rw [hm3]; refine (hstab _ _ _ ?_).1
      rw [hm2]; refine (hstab _ _ _ ?_).1
      rw [hm1]; exact (hstab _ _ _ hI').2.2
    have hblk3 : Blk m3 p0 E := by
      rw [hm3]; refine Blk.update ?_ (Or.inl hlo.1)
      rw [hm2]; refine Blk.update ?_ (Or.inl hlo.1)
      rw [hm1]; exact Blk.update hblk'' (Or.inl hlo.2.2)
    have hposle : pos (j + 1) ≤ p0 + E.length := by
      rw [hpos, hE]; have := encList_take_le f xs (j + 1); omega
    refine ⟨⟨j + 1, hjl, (hstab _ _ _ hI3).2.1, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · rw [Mem.update_of_ne _ _ d2, e3rp]
    · rw [Mem.update_of_ne _ _ d5, e3re]
    · rw [Mem.update_self, e3re, e3rp]
    · rw [Mem.update_of_ne _ _ d9.symm, e31]
    · exact Blk.update hblk3 (Or.inl hlo.2.1)
    · show Ψ (m3.update rc (m3 re - m3 rp)) + K * ((m3.update rc (m3 re - m3 rp)) re -
          (m3.update rc (m3 re - m3 rp)) rp) + (t + 4) + 2 ≤ Ψ M' + K * (M' re - M' rp)
      rw [(hΨ _ _).2.1, hΨ3, Mem.update_of_ne _ _ d5, Mem.update_of_ne _ _ d2, e3re, e3rp, hre,
        hrp]
      have hsplit : p0 + E.length - pos j = (p0 + E.length - pos (j + 1)) +
          ((f xs[j]).length + 1) := by omega
      rw [hsplit, Nat.mul_add]
      have : c0 + c1 * (f xs[j]).length + 6 ≤ K * ((f xs[j]).length + 1) := by
        have h1 : c1 * (f xs[j]).length ≤ K * (f xs[j]).length :=
          Nat.mul_le_mul_right _ (by omega)
        rw [Nat.mul_add, Nat.mul_one]; omega
      omega)
  have hM1 : inv (M.update rc (M re - M rp)) := by
    refine ⟨0, Nat.zero_le _, (hstab _ _ _ hI0).2.1, ?_, ?_, ?_, ?_, Blk.update hblk (Or.inl hlo.2.1)⟩
    · rw [Mem.update_of_ne _ _ d2, hp, hpos]; simp [encList]
    · rw [Mem.update_of_ne _ _ d5, he]
    · rw [Mem.update_self, he, hp, hpos]; simp [encList]
    · rw [Mem.update_of_ne _ _ d9.symm, h1]
  refine (sub_seq (hloop _ hM1)).conseq (fun m hm => hm) ?_ ?_
  · rintro m' ⟨⟨j, hj, hI, hrp, hre, hrc, h1', hblk'⟩, hz⟩
    have hjl : j = xs.length := by
      by_contra hne
      have hlt := encList_take_lt f xs j (by omega)
      rw [hpos, hE] at hrc
      omega
    subst hjl
    refine ⟨hI, ?_, by rw [hre, he], h1', hblk'⟩
    rw [hrp, he, hpos, encList_take_length]
  · show 1 + (Ψ (M.update rc (M re - M rp)) + K * ((M.update rc (M re - M rp)) re -
      (M.update rc (M re - M rp)) rp) + 1) ≤ _
    rw [(hΨ _ _).2.1, Mem.update_of_ne _ _ d5, Mem.update_of_ne _ _ d2, he, hp,
      Nat.add_sub_cancel_left]
    omega

end Exact

end RAM
