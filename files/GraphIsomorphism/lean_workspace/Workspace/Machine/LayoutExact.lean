import Workspace.Machine.Layout

/-!
# Exact-state rules for the workspace normal form

`Workspace/Machine/Layout.lean` states its stage rules with a state predicate `At K Q L` and a
frame condition.  For straight-line code on the work registers it is shorter to track the
*exact* state: from the memory `memAt 16 w L` one instruction leads to `memAt 16 w' L'` with
`w'` an explicit update of `w`.  Such steps chain by `RAM.RunsTo.seq` with no intermediate
predicate to write, and the register values a later step needs are read off the composite
update by `simp [Mem.update]`.

The offset is fixed at `16` (the workspace convention of every routine of `Workspace/Algo`).

The one rule not in `Layout.lean` is the **store into the middle of the list**
(`RAM.LX.ex_store`): an indirect store to an address inside the list replaces one entry.  This
is what random-access arrays kept in the workspace need.
-/

namespace RAM
namespace LX

open Layout

/-- A write inside the list replaces one entry. -/
theorem memAt_update_mid (K : ℕ) (w : Mem) (L : List ℕ) {i : ℕ} (hi : i < L.length) (v : ℕ) :
    (memAt K w L).update (K + i) v = memAt K w (L.set i v) := by
  funext y
  rcases Nat.lt_or_ge y K with hy | hy
  · rw [Mem.update_of_ne _ _ (by omega : y ≠ K + i), memAt_of_lt _ _ hy, memAt_of_lt _ _ hy]
  · obtain ⟨j, rfl⟩ : ∃ j, y = K + j := ⟨y - K, by omega⟩
    rw [memAt_add]
    by_cases hj : j = i
    · subst hj
      rw [Mem.update_self, List.getD_eq_getElem _ _ (by simpa using hi)]
      simp
    · rw [Mem.update_of_ne _ _ (by omega : K + j ≠ K + i), memAt_add]
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm hj)]

/-- Sequencing of specifications, right associative like the programs `seq A (seq B C)`. -/
scoped infixr:60 " ⨾ " => RunsTo.seq

/-- The exact state. -/
abbrev St (w : Mem) (L : List ℕ) : Mem → Prop := fun m => m = memAt 16 w L

theorem ex_assign (x c : ℕ) {w : Mem} {L : List ℕ} (hx : x < 16 := by decide) :
    RunsTo (assign x c) (St w L) (St (w.update x c) L) 1 :=
  runsTo_assign x c (fun m hm => by rw [hm, memAt_update_of_lt _ _ hx])

theorem ex_copy (x y : ℕ) {w : Mem} {L : List ℕ} (hx : x < 16 := by decide)
    (hy : y < 16 := by decide) :
    RunsTo (copyTo x y) (St w L) (St (w.update x (w y)) L) 1 :=
  runsTo_copyTo x y (fun m hm => by rw [hm, memAt_of_lt _ _ hy, memAt_update_of_lt _ _ hx])

theorem ex_add (x y z : ℕ) {w : Mem} {L : List ℕ} (hx : x < 16 := by decide)
    (hy : y < 16 := by decide) (hz : z < 16 := by decide) :
    RunsTo (addTo x y z) (St w L) (St (w.update x (w y + w z)) L) 1 :=
  runsTo_addTo x y z (fun m hm => by
    rw [hm, memAt_of_lt _ _ hy, memAt_of_lt _ _ hz, memAt_update_of_lt _ _ hx])

theorem ex_sub (x y z : ℕ) {w : Mem} {L : List ℕ} (hx : x < 16 := by decide)
    (hy : y < 16 := by decide) (hz : z < 16 := by decide) :
    RunsTo (subTo x y z) (St w L) (St (w.update x (w y - w z)) L) 1 :=
  runsTo_subTo x y z (fun m hm => by
    rw [hm, memAt_of_lt _ _ hy, memAt_of_lt _ _ hz, memAt_update_of_lt _ _ hx])

/-- Reading the list through a pointer register. -/
theorem ex_load (x y : ℕ) {w : Mem} {L : List ℕ} {i : ℕ} (h : w y = 16 + i)
    (hx : x < 16 := by decide) (hy : y < 16 := by decide) :
    RunsTo (loadTo x y) (St w L) (St (w.update x (L.getD i 0)) L) 1 :=
  runsTo_loadTo x y (fun m hm => by
    rw [hm, memAt_of_lt _ _ hy, h, memAt_add, memAt_update_of_lt _ _ hx])

/-- Reading the list at a fixed index. -/
theorem ex_loadFix (x i : ℕ) {w : Mem} {L : List ℕ} (hx : x < 16 := by decide) :
    RunsTo (copyTo x (16 + i)) (St w L) (St (w.update x (L.getD i 0)) L) 1 :=
  runsTo_copyTo x (16 + i) (fun m hm => by rw [hm, memAt_add, memAt_update_of_lt _ _ hx])

/-- **Writing inside the list** through a pointer register. -/
theorem ex_store (x y : ℕ) {w : Mem} {L : List ℕ} {i : ℕ} (h : w x = 16 + i)
    (hi : i < L.length) (hx : x < 16 := by decide) (hy : y < 16 := by decide) :
    RunsTo (storeTo x y) (St w L) (St w (L.set i (w y))) 1 :=
  runsTo_storeTo x y (fun m hm => by
    rw [hm, memAt_of_lt _ _ hx, memAt_of_lt _ _ hy, h, memAt_update_mid _ _ _ hi])

/-- Appending a register to the list. -/
theorem ex_push (r : ℕ) {w : Mem} {L : List ℕ} (h8 : w 8 = 16 + L.length)
    (hr : r < 16 := by decide) (hr10 : r ≠ 10 := by decide) :
    RunsTo (pushVal r) (St w L)
      (St ((w.update 10 1).update 8 (16 + L.length + 1)) (L ++ [w r])) 3 := by
  refine RunsTo.mono (T := 1 + (1 + 1)) ?_ (by norm_num)
  refine RunsTo.seq (ex_assign 10 1) ?_
  refine RunsTo.seq (mid := St (w.update 10 1) (L ++ [w r]))
    (runsTo_storeTo 8 r (fun m hm => ?_)) ?_
  · rw [hm, memAt_of_lt _ _ (by omega : (8:ℕ) < 16), memAt_of_lt _ _ hr,
      Mem.update_of_ne _ _ (by omega : (8:ℕ) ≠ 10), Mem.update_of_ne _ _ hr10, h8,
      memAt_update_top]
  refine (ex_add 8 8 10).weaken (fun m hm => ?_)
  rw [hm]
  congr 2
  simp [Mem.update, h8]

/-- Advancing the top pointer (register `8`) by the contents of register `r`: the list grows by
zeros, which the memory does not see. -/
theorem ex_advance (r : ℕ) {w : Mem} {L : List ℕ} (hr : r < 16 := by decide) :
    RunsTo (addTo 8 8 r) (St w L)
      (St (w.update 8 (w 8 + w r)) (L ++ List.replicate (w r) 0)) 1 :=
  (ex_add 8 8 r (hz := hr)).weaken (fun m hm => by
    show m = _
    rw [hm, memAt_append_zeros])

/-- The conditional from an exact state, register nonzero. -/
theorem ex_ifz_ne {i : ℕ} {P Q : Program} {w : Mem} {L : List ℕ} {post : Mem → Prop} {T : ℕ}
    (hi : i < 16) (hw : w i ≠ 0) (hP : RunsTo P (St w L) post T) (hQ : Wf Q) :
    RunsTo (ifz i P Q) (St w L) post (T + 2) := by
  have h := RunsTo.ifz (i := i) (pre := St w L) (T' := 0)
    (hP.strengthen (fun m hm => hm.1))
    (runsTo_of_false hQ (fun m hm => by
      obtain ⟨hm1, hm2⟩ := hm
      rw [hm1, memAt_of_lt _ _ hi] at hm2
      exact hw hm2))
  simpa using h

/-- The conditional from an exact state, register zero. -/
theorem ex_ifz_eq {i : ℕ} {P Q : Program} {w : Mem} {L : List ℕ} {post : Mem → Prop} {T : ℕ}
    (hi : i < 16) (hw : w i = 0) (hQ : RunsTo Q (St w L) post T) (hP : Wf P) :
    RunsTo (ifz i P Q) (St w L) post (T + 2) := by
  have h := RunsTo.ifz (i := i) (pre := St w L) (T := 0)
    (runsTo_of_false hP (fun m hm => by
      obtain ⟨hm1, hm2⟩ := hm
      rw [hm1, memAt_of_lt _ _ hi] at hm2
      exact hm2 hw))
    (hQ.strengthen (fun m hm => hm.1))
  simpa using h

/-- A precondition with a witness is handled one witness at a time. -/
theorem runsTo_exists {ι : Type*} {P : Program} {pre : ι → Mem → Prop} {post : Mem → Prop}
    {T : ℕ} (hw : Wf P) (h : ∀ x, RunsTo P (pre x) post T) :
    RunsTo P (fun m => ∃ x, pre x m) post T :=
  ⟨hw, fun m hm => by obtain ⟨x, hx⟩ := hm; exact (h x).spec m hx⟩

/-- Entering an exact state from a state predicate. -/
theorem runsTo_of_St {P : Program} {pre : Mem → Prop} {post : Mem → Prop} {T : ℕ} (hw : Wf P)
    (h : ∀ w L, pre (memAt 16 w L) → RunsTo P (St w L) post T)
    (hpre : ∀ m, pre m → ∃ w L, m = memAt 16 w L) :
    RunsTo P pre post T :=
  ⟨hw, fun m hm => by
    obtain ⟨w, L, rfl⟩ := hpre m hm
    exact (h w L hm).spec _ rfl⟩

/-! ## The same rules with the values named

In a long chain the register values of the rules above nest: every later step re-reads earlier
updates.  The variants below take the values as arguments, with a hypothesis each, so the state
after a chain is a flat list of updates by named values. -/

theorem ex_copyV (x y : ℕ) {w : Mem} {L : List ℕ} {a : ℕ} (hy' : w y = a)
    (hx : x < 16 := by decide) (hy : y < 16 := by decide) :
    RunsTo (copyTo x y) (St w L) (St (w.update x a) L) 1 := by
  subst hy'; exact ex_copy x y hx hy

theorem ex_addV (x y z : ℕ) {w : Mem} {L : List ℕ} {a b : ℕ} (hy' : w y = a) (hz' : w z = b)
    (hx : x < 16 := by decide) (hy : y < 16 := by decide) (hz : z < 16 := by decide) :
    RunsTo (addTo x y z) (St w L) (St (w.update x (a + b)) L) 1 := by
  subst hy' hz'; exact ex_add x y z hx hy hz

theorem ex_subV (x y z : ℕ) {w : Mem} {L : List ℕ} {a b : ℕ} (hy' : w y = a) (hz' : w z = b)
    (hx : x < 16 := by decide) (hy : y < 16 := by decide) (hz : z < 16 := by decide) :
    RunsTo (subTo x y z) (St w L) (St (w.update x (a - b)) L) 1 := by
  subst hy' hz'; exact ex_sub x y z hx hy hz

theorem ex_loadV (x y : ℕ) {w : Mem} {L : List ℕ} {i v : ℕ} (h : w y = 16 + i)
    (hv : L.getD i 0 = v) (hx : x < 16 := by decide) (hy : y < 16 := by decide) :
    RunsTo (loadTo x y) (St w L) (St (w.update x v) L) 1 := by
  subst hv; exact ex_load x y h hx hy

theorem ex_loadFixV (x i : ℕ) {w : Mem} {L : List ℕ} {v : ℕ} (hv : L.getD i 0 = v)
    (hx : x < 16 := by decide) :
    RunsTo (copyTo x (16 + i)) (St w L) (St (w.update x v) L) 1 := by
  subst hv; exact ex_loadFix x i hx

theorem ex_storeV (x y : ℕ) {w : Mem} {L : List ℕ} {i v : ℕ} (h : w x = 16 + i)
    (hv : w y = v) (hi : i < L.length) (hx : x < 16 := by decide) (hy : y < 16 := by decide) :
    RunsTo (storeTo x y) (St w L) (St w (L.set i v)) 1 := by
  subst hv; exact ex_store x y h hi hx hy

theorem ex_pushV (r : ℕ) {w : Mem} {L : List ℕ} {v : ℕ} (hv : w r = v)
    (h8 : w 8 = 16 + L.length) (hr : r < 16 := by decide) (hr10 : r ≠ 10 := by decide) :
    RunsTo (pushVal r) (St w L)
      (St ((w.update 10 1).update 8 (16 + L.length + 1)) (L ++ [v])) 3 := by
  subst hv; exact ex_push r h8 hr hr10

theorem ex_advanceV (r : ℕ) {w : Mem} {L : List ℕ} {t j : ℕ} (h8 : w 8 = t) (hj : w r = j)
    (hr : r < 16 := by decide) :
    RunsTo (addTo 8 8 r) (St w L) (St (w.update 8 (t + j)) (L ++ List.replicate j 0)) 1 := by
  subst h8 hj; exact ex_advance r hr

/-- Restating the list of an exact state. -/
theorem St.congr {w : Mem} {L L' : List ℕ} (h : L = L') {m : Mem} (hm : St w L m) :
    St w L' m := by
  subst h; exact hm

theorem St.to {w : Mem} {L L' : List ℕ} {m : Mem} (hm : St w L m) (h : L = L') :
    m = memAt 16 w L' := by
  subst h; exact hm

/-- Copying a segment of the list to its top (`RAM.Layout.runsTo_pushBlock`) from an exact
state.  The copy loop uses registers `1, 3, ..., 7`, whose final contents are not named. -/
theorem ex_pushBlock {w : Mem} {L : List ℕ} {p c : ℕ} (h8 : w 8 = 16 + L.length)
    (h0 : w 0 = 16 + p) (h2 : w 2 = c) (hpc : p + c ≤ L.length) :
    RunsTo pushBlock (St w L)
      (fun m => ∃ w', m = memAt 16 w' (L ++ (L.drop p).take c) ∧
        (∀ z, z < 16 → z ≠ 1 → z ≠ 8 → ¬ (3 ≤ z ∧ z ≤ 7) → w' z = w z) ∧
        w' 8 = 16 + L.length + c) (7 * c + 7) := by
  refine (runsTo_pushBlock (K := 16) (Q := fun v => v = w) (Q' := fun v => ?_) (le_refl _) hpc
    (fun v hv => by subst hv; exact ⟨h8, h0, h2⟩) (fun v v' hv hfr h8' => ?_)).conseq
    (fun m hm => ⟨w, rfl, hm⟩) (fun m hm => ?_) (le_refl _)
  · exact (∀ z, z < 16 → z ≠ 1 → z ≠ 8 → ¬ (3 ≤ z ∧ z ≤ 7) → v z = w z) ∧
      v 8 = 16 + L.length + c
  · subst hv
    exact ⟨hfr, h8'⟩
  · obtain ⟨v, hv, rfl⟩ := hm
    exact ⟨v, rfl, hv⟩

theorem runsTo_of_exists_St' {P : Program} {pre : Mem → Prop} {post : Mem → Prop} {T : ℕ}
    (hw : Wf P) (h : ∀ m, pre m → ∃ w L, m = memAt 16 w L ∧ RunsTo P (St w L) post T) :
    RunsTo P pre post T :=
  ⟨hw, fun m hm => by
    obtain ⟨w, L, hm', hr⟩ := h m hm
    exact hr.spec m hm'⟩

/-- `RAM.LX.ex_pushBlock` followed by a continuation. -/
theorem ex_pushBlock_then {w : Mem} {L : List ℕ} {p c : ℕ} {Q : Program} {post : Mem → Prop}
    {T : ℕ} (h8 : w 8 = 16 + L.length) (h0 : w 0 = 16 + p) (h2 : w 2 = c)
    (hpc : p + c ≤ L.length) (hQw : Wf Q)
    (hQ : ∀ w' : Mem, (∀ z, z < 16 → z ≠ 1 → z ≠ 8 → ¬ (3 ≤ z ∧ z ≤ 7) → w' z = w z) →
      w' 8 = 16 + L.length + c → RunsTo Q (St w' (L ++ (L.drop p).take c)) post T) :
    RunsTo (seq pushBlock Q) (St w L) post (7 * c + 7 + T) :=
  (ex_pushBlock h8 h0 h2 hpc).seq (runsTo_of_exists_St' hQw (fun m hm => by
    obtain ⟨w', hm', hfr, h8'⟩ := hm
    exact ⟨w', _, hm', hQ w' hfr h8'⟩))

/-- Entering exact states from a state predicate that names them. -/
theorem runsTo_of_exists_St {P : Program} {pre : Mem → Prop} {post : Mem → Prop} {T : ℕ}
    (hw : Wf P) (h : ∀ m, pre m → ∃ w L, m = memAt 16 w L ∧ RunsTo P (St w L) post T) :
    RunsTo P pre post T :=
  ⟨hw, fun m hm => by
    obtain ⟨w, L, hm', hr⟩ := h m hm
    exact hr.spec m hm'⟩

/-- Register arithmetic on a composite of updates: `simp` evaluates the updates at numeral
registers, then `omega`. -/
syntax (name := rsimpStx) "rsimp" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| rsimp) =>
      `(tactic| ((try simp [Mem.update, -List.getD_eq_getElem?_getD]) <;> (try omega)))
  | `(tactic| rsimp [$ls,*]) =>
      `(tactic| ((try simp [Mem.update, -List.getD_eq_getElem?_getD, $ls,*]) <;> (try omega)))

end LX
end RAM
