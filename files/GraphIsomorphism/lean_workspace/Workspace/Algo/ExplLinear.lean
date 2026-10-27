import Workspace.Machine.Trie
import Workspace.Machine.BridgeUp
import Workspace.Algo.ExplicitStructures

/-!
# Prop. 2.3.6 in linear time on the RAM

Version 2.5, §2.3.1, Prop. 2.3.6: "Given two explicit relational structures `X = (Ω, R)` and
`X' = (Ω', R')` and a bijection `σ : Ω → Ω'`, one can decide in linear time whether
`σ ∈ Iso(X, X')`."  This file proves the statement `Algo.Proposition_2_3_6_linear_statement`:
one RAM program decides the test `rawExplIsoTest` within `C · (size + 1)` steps.

## The algorithm

The paper's proof sorts each relation of `X^σ` and of `X'` by radix sort and compares the
sorted lists.  A radix sort with one bucket per point of `Ω'` spends `Θ(n)` steps per pass on
the buckets alone, for every relation; with many small relations this is not linear (see
the corrected paper entry for Prop. 2.3.6).  We therefore use the other form of radix sort,
the *digital search tree* (trie), which is what a most-significant-digit-first radix sort builds:
the tuples of a relation are the root-to-node paths, one node per distinct prefix.  Nodes are
allocated one after the other in fresh (zero) memory, so neither allocation nor clearing costs
anything, and the time is proportional to the number of entries read.  For each pair
`(Rᵢ, Rᵢ')`:

1. the arities are compared;
2. the tuples of `Rᵢ'` (those that are tuples of `[0,n)^a`) are stored in a trie `A`, and each
   tuple `t` of `Rᵢ` is looked up in `A` as `t^σ`;
3. the tuples `t^σ` for `t ∈ Rᵢ` are stored in a trie `B`, and each tuple of `Rᵢ'` is looked
   up in `B`.

This decides `Rᵢ^σ = Rᵢ'` (both inclusions).  Finally the numbers of relations are compared.

## Registers

After the input is moved to a far base `F`, the registers below `64` are free.  Register `1`
holds `1`; `11` holds `2n`; `12` the address `SIG` of `σ(0)` (so `σ(x)` is at `SIG + 2x`);
`13` the node width `2n + 1`; `14` the allocation pointer; `15` the answer flag.  The loops use
`16, 17, 20, 38` (relations of `X`), `18, 19` (relations of `X'`), `27, 28, 29, 37` (tuples),
`30, 31, 32, 36` (entries of a tuple); `21` holds `2a` for the current arity `a`, `22`–`25` the
bounds of the two tuple lists, `26` the root of the current trie, `33` the result of the tuple
check, `34` the current trie node, `35` the current entry, `2`–`6` are temporaries.
-/

namespace Algo

namespace ExplLinear

open RAM RAM.Exact RAM.Trie

/-! ## The frame of every routine -/

/-- The invariant data of the whole run: the input block, the constants, and the fresh memory
above the allocation pointer.  `lo` is the first address above the input. -/
structure Base (F : ℕ) (inp : List ℕ) (n SIG lo : ℕ) (sig : List ℕ) (m : Mem) : Prop where
  one : m 1 = 1
  n2 : m 11 = n + n
  sigr : m 12 = SIG
  w : m 13 = width n
  blk : Blk m F inp
  sigv : ∀ x < n, m (SIG + x + x) = sig.getD x 0
  sigin : SIG + n + n ≤ lo
  hF : 64 ≤ F
  hSIG : 64 ≤ SIG
  hlo : F + inp.length ≤ lo
  alo : lo ≤ m 14
  fresh : ∀ z, m 14 ≤ z → m z = 0
  siglt : ∀ x < n, sig.getD x 0 < n

/-- `OutLo lo W M m`: below `lo`, `m` differs from `M` only at the registers `W`. -/
def OutLo (lo : ℕ) (W : List ℕ) (M m : Mem) : Prop := ∀ z, z < lo → z ∉ W → m z = M z

theorem OutLo.refl (lo : ℕ) (W : List ℕ) (M : Mem) : OutLo lo W M M := fun _ _ _ => rfl

theorem OutLo.trans {lo : ℕ} {W W' : List ℕ} {M m m' : Mem} (h : OutLo lo W M m)
    (h' : OutLo lo W' m m') (hW : ∀ z ∈ W', z ∈ W) : OutLo lo W M m' := by
  intro z hz hzW
  rw [h' z hz (fun h'' => hzW (hW z h'')), h z hz hzW]

theorem OutLo.of_outside {lo : ℕ} {W : List ℕ} {M m : Mem} (h : Outside W M m) :
    OutLo lo W M m := fun z _ hz => h z hz

theorem OutLo.mono {lo : ℕ} {W W' : List ℕ} {M m : Mem} (h : OutLo lo W M m)
    (hW : ∀ z ∈ W, z ∈ W') : OutLo lo W' M m :=
  fun z hz hzW => h z hz (fun h' => hzW (hW z h'))

theorem OutLo.upd {lo : ℕ} {W : List ℕ} {M m : Mem} (h : OutLo lo W M m) {a : ℕ}
    (ha : a ∈ W ∨ lo ≤ a) (v : ℕ) : OutLo lo W M (m.update a v) := by
  intro z hz hzW
  have hza : z ≠ a := by
    rintro rfl; rcases ha with ha | ha
    · exact hzW ha
    · omega
  rw [Mem.update_of_ne _ _ hza]
  exact h z hz hzW

/-- The frame data survive every change below `lo` outside the fixed registers, and every change
above that keeps the fresh region fresh. -/
theorem Base.of_outLo {F : ℕ} {inp : List ℕ} {n SIG lo : ℕ} {sig : List ℕ} {M m : Mem}
    (hB : Base F inp n SIG lo sig M) {W : List ℕ} (hout : OutLo lo W M m)
    (hW : ∀ z ∈ W, z < 64 ∧ z ≠ 1 ∧ z ≠ 11 ∧ z ≠ 12 ∧ z ≠ 13)
    (halo : lo ≤ m 14) (hfresh : ∀ z, m 14 ≤ z → m z = 0) : Base F inp n SIG lo sig m := by
  have key : ∀ z, z < lo → (64 ≤ z ∨ z = 1 ∨ z = 11 ∨ z = 12 ∨ z = 13) → m z = M z := by
    intro z hz hz'
    refine hout z hz (fun hzW => ?_)
    have := hW z hzW
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hB.sigin, hB.hF, hB.hSIG, hB.hlo, halo, hfresh, hB.siglt⟩
  · rw [key 1 (by have := hB.hF; have := hB.hlo; omega) (by omega), hB.one]
  · rw [key 11 (by have := hB.hF; have := hB.hlo; omega) (by omega), hB.n2]
  · rw [key 12 (by have := hB.hF; have := hB.hlo; omega) (by omega), hB.sigr]
  · rw [key 13 (by have := hB.hF; have := hB.hlo; omega) (by omega), hB.w]
  · refine Blk.congr hB.blk (fun z hz1 hz2 => key z (by have := hB.hlo; omega)
      (by have := hB.hF; omega))
  · intro x hx
    rw [key _ (by have := hB.sigin; omega) (by have := hB.hSIG; omega), hB.sigv x hx]

/-- A register write outside the fixed registers keeps the frame. -/
theorem Base.upd {F : ℕ} {inp : List ℕ} {n SIG lo : ℕ} {sig : List ℕ} {m : Mem}
    (hB : Base F inp n SIG lo sig m) {r : ℕ} (hr : r < 64) (h1 : r ≠ 1) (h11 : r ≠ 11)
    (h12 : r ≠ 12) (h13 : r ≠ 13) (h14 : r ≠ 14) (v : ℕ) :
    Base F inp n SIG lo sig (m.update r v) := by
  have hlo : 64 ≤ lo := by have := hB.hF; have := hB.hlo; omega
  refine hB.of_outLo (W := [r]) ((OutLo.refl lo [r] m).upd (Or.inl (by simp)) v)
    (by simp; omega) (by rw [Mem.update_of_ne _ _ (Ne.symm h14)]; exact hB.alo) ?_
  intro z hz
  rw [Mem.update_of_ne _ _ (Ne.symm h14)] at hz
  have : z ≠ r := by have := hB.alo; omega
  rw [Mem.update_of_ne _ _ this]; exact hB.fresh z hz

/-! ## Encodings read from memory -/

theorem length_encode_nat_list (t : List ℕ) : (Enc.encode t).length = 2 * t.length := by
  induction t with
  | nil => rfl
  | cons x t ih =>
    change (encList Enc.encode t).length = _ at ih
    show (RAM.frame [x] ++ encList Enc.encode t).length = 2 * (t.length + 1)
    rw [List.length_append, ih]; simp [RAM.frame]; ring

/-- The element number `j` of an encoded list of numbers: `[1, x₀, 1, x₁, …]`. -/
theorem Blk.nat_entry {m : Mem} {p : ℕ} {t : List ℕ} (h : Blk m p (encList Enc.encode t))
    (j : ℕ) (hj : j < t.length) :
    m (p + (encList Enc.encode (t.take j)).length + 1) = t[j] := by
  have := h.encList_get j hj
  rw [Blk.frame_iff, Blk.encode_nat] at this
  exact this.2

/-! ## Entry bodies

Each entry of a tuple is framed as `[1, x]`; the entry loop points register `30` at the frame. -/

/-- Read the current entry into register `35`. -/
def rdX : Program := seq (addTo 3 30 1) (loadTo 35 3)

theorem runsTo_rdX {M : Mem} {x : ℕ} (h1 : M 1 = 1) (h30 : 4 ≤ M 30)
    (hx : M (M 30 + 1) = x) :
    RunsTo rdX (fun m => m = M) (fun m => Outside [3, 35] M m ∧ m 35 = x) 2 := by
  refine add_seq (load_last ⟨((Outside.refl _ _).upd (by simp) _).upd (by simp) _, ?_⟩)
  simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, h1, hx]

/-- Map the current entry by `σ`: `x ↦ σ(x)`, read at `SIG + 2x`. -/
def mapX : Program := seq (addTo 3 12 35) (seq (addTo 3 3 35) (loadTo 35 3))

/-- Optionally map the entry. -/
def mapB (ms : Bool) : Program := if ms then mapX else []

/-- The image of a tuple: itself, or its image under `σ` (as a list of values). -/
def imgT (ms : Bool) (sig : List ℕ) (t : List ℕ) : List ℕ :=
  if ms then t.map (fun x => sig.getD x 0) else t

/-- The image of one entry. -/
def imgX (ms : Bool) (sig : List ℕ) (x : ℕ) : ℕ := if ms then sig.getD x 0 else x

theorem imgT_length (ms : Bool) (sig t : List ℕ) : (imgT ms sig t).length = t.length := by
  cases ms <;> simp [imgT]

theorem imgT_getElem (ms : Bool) (sig t : List ℕ) (j : ℕ) (hj : j < t.length) :
    (imgT ms sig t)[j]'(by rw [imgT_length]; exact hj) = imgX ms sig t[j] := by
  cases ms <;> simp [imgT, imgX]

theorem imgT_take_succ (ms : Bool) (sig t : List ℕ) (j : ℕ) (hj : j < t.length) :
    (imgT ms sig t).take (j + 1) = (imgT ms sig t).take j ++ [imgX ms sig t[j]] := by
  rw [List.take_add_one, List.getElem?_eq_getElem (by rw [imgT_length]; exact hj),
    imgT_getElem ms sig t j hj]
  rfl

theorem wf_mapB (ms : Bool) : Wf (mapB ms) := by
  cases ms
  · intro i hi; exact absurd hi (by simp [mapB])
  · exact wf_seq (Layout.wf_addTo _ _ _) (wf_seq (Layout.wf_addTo _ _ _) (Layout.wf_loadTo _ _))

/-- `mapB`: the entry in register `35` becomes its image, with register `3` a scratch. -/
theorem runsTo_mapB (ms : Bool) {M : Mem} {n : ℕ} {sig : List ℕ} (hS : 4 ≤ M 12)
    (hsig : ∀ x < n, M (M 12 + x + x) = sig.getD x 0) (hx : M 35 < n) :
    RunsTo (mapB ms) (fun m => m = M)
      (fun m => Outside [3, 35] M m ∧ m 35 = imgX ms sig (M 35)) 3 := by
  cases ms with
  | false =>
    exact (runsTo_nil (fun m hm => by subst hm; exact ⟨Outside.refl _ _, rfl⟩)).mono (by omega)
  | true =>
    refine add_seq (add_seq (load_last ⟨?_, ?_⟩))
    · exact ((((Outside.refl _ _).upd (by simp) _).upd (by simp) _).upd (by simp) _)
    · simp (disch := omega) only [Mem.update_self, Mem.update_of_ne]
      exact hsig _ hx

/-- A block survives writes to registers below it. -/
theorem Blk.outside {m m' : Mem} {p : ℕ} {xs : List ℕ} (h : Blk m p xs) {W : List ℕ}
    (ho : Outside W m m') (hW : ∀ z ∈ W, z < p) : Blk m' p xs :=
  Blk.congr h (fun z hz _ => ho z (fun hzW => by have := hW z hzW; omega))

theorem Outside.sub {W W' : List ℕ} {M m m' : Mem} (h : Outside W M m) (h' : Outside W' m m')
    (hW : ∀ z ∈ W', z ∈ W) : Outside W M m' :=
  (h.trans h').mono (fun z hz => by
    rcases List.mem_append.1 hz with hz | hz
    · exact hz
    · exact hW z hz)

theorem framesLoop_regs_entry : (30 : ℕ) ≠ 31 ∧ (30 : ℕ) ≠ 32 ∧ (30 : ℕ) ≠ 36 ∧ (30 : ℕ) ≠ 1 ∧
    (31 : ℕ) ≠ 32 ∧ (31 : ℕ) ≠ 36 ∧ (31 : ℕ) ≠ 1 ∧ (32 : ℕ) ≠ 36 ∧ (32 : ℕ) ≠ 1 ∧ (36 : ℕ) ≠ 1 := by
  decide

/-- Forget the exact memory, keep what is known about it. -/
theorem at_mem {P : Program} {post : Mem → Prop} {T : ℕ} {M : Mem} (Φ : Mem → Prop) (hM : Φ M)
    (h : ∀ M', Φ M' → RunsTo P (fun m => m = M') post T) : RunsTo P (fun m => m = M) post T :=
  h M hM

/-- `Outside W M m` for a chain of register updates `m` of a memory `M1` with
`Outside W₀ M M1`, `W₀ ⊆ W`. -/
syntax "outside_tac" term : tactic
macro_rules
  | `(tactic| outside_tac $h) => `(tactic|
      (intro z hz; simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz;
       simp (disch := omega) only [Mem.update_of_ne];
       all_goals first
       | exact ($h) z (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; omega)
       | rfl))

theorem all_take_succ {β : Type*} (t : List β) (j : ℕ) (hj : j < t.length) (P : β → Prop) :
    (∀ x ∈ t.take (j + 1), P x) ↔ (∀ x ∈ t.take j, P x) ∧ P t[j] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some, List.forall_mem_append,
    List.forall_mem_singleton]

/-! ## Checking one tuple -/

/-- A listed tuple is a tuple of `[0,n)^a`. -/
def Good (n a : ℕ) (t : List ℕ) : Prop := t.length = a ∧ ∀ x ∈ t, x < n

instance (n a : ℕ) (t : List ℕ) : Decidable (Good n a t) := by unfold Good; infer_instance

theorem good_iff_goodTuple (n a : ℕ) (t : List ℕ) : Good n a t ↔ goodTuple ((n, a), t) = true := by
  simp [Good, goodTuple, wftAllLt_eq_true_iff]

/-- The check of one entry: clear register `33` if the entry is not below `n`. -/
def goodB : Program :=
  seq rdX (seq (addTo 3 35 35) (seq (addTo 3 3 1) (seq (subTo 3 3 11) (ifz 3 (assign 33 0) []))))

theorem wf_nil : Wf ([] : Program) := fun i hi => absurd hi (by simp)

theorem wf_goodB : Wf goodB :=
  wf_seq (wf_seq (Layout.wf_addTo _ _ _) (Layout.wf_loadTo _ _)) (wf_seq (Layout.wf_addTo _ _ _)
    (wf_seq (Layout.wf_addTo _ _ _) (wf_seq (Layout.wf_subTo _ _ _)
      (wf_ifz (Layout.wf_assign _ _) wf_nil))))

theorem runsTo_goodB {M : Mem} {n x : ℕ} (h1 : M 1 = 1) (h30 : 4 ≤ M 30)
    (hx : M (M 30 + 1) = x) (h11 : M 11 = n + n) :
    RunsTo goodB (fun m => m = M)
      (fun m => Outside [3, 35, 33] M m ∧ m 33 = if x < n then M 33 else 0) 8 := by
  refine RunsTo.mono (T := 2 + (1 + (1 + (1 + (1 + 2))))) ?_ (by omega)
  refine block_seq (runsTo_rdX h1 h30 hx) (fun M1 hM1 => ?_)
  obtain ⟨ho, h35⟩ := hM1
  have e1 : M1 1 = 1 := by rw [ho 1 (by simp), h1]
  have e11 : M1 11 = n + n := by rw [ho 11 (by simp), h11]
  have e33 : M1 33 = M 33 := ho 33 (by simp)
  refine add_seq (add_seq (sub_seq ?_))
  refine at_mem (fun M' => Outside [3, 35, 33] M M' ∧ M' 33 = M 33 ∧ M' 3 = x + x + 1 - (n + n))
    ⟨by outside_tac ho, ?_, ?_⟩ (fun M' hM' => ?_)
  · simp (disch := omega) only [Mem.update_of_ne, e33]
  · simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, e1, e11, h35]
  obtain ⟨ho', e33', e3⟩ := hM'
  by_cases hxn : x < n
  · refine (ifz_eq (T := 0) (by rw [e3]; omega) (runsTo_nil (fun m hm => ?_))
      (Layout.wf_assign _ _)).mono (by omega)
    subst hm
    exact ⟨ho', by rw [if_pos hxn, e33']⟩
  · refine ifz_ne (by rw [e3]; omega) (assign_last ⟨?_, ?_⟩) wf_nil
    · exact ho'.upd (by simp) _
    · simp only [Mem.update_self, if_neg hxn]

/-- The check of a tuple at register `27`: register `33` becomes `1` exactly when the tuple is
a tuple of `[0,n)^a`, where register `21` holds `2a`. -/
def goodChk : Program :=
  seq (assign 33 1) (seq (loadTo 2 27) (seq (subTo 3 2 21) (seq (subTo 4 21 2) (seq (addTo 3 3 4)
    (ifz 3 (assign 33 0) (seq (addTo 30 27 1) (seq (addTo 31 30 2)
      (framesLoop 30 31 32 36 goodB))))))))

/-- The registers the tuple check writes. -/
notation "Wg" => [2, 3, 4, 30, 31, 32, 33, 35, 36]

theorem wf_framesLoop {rp re rc rt : ℕ} {B : Program} (hB : Wf B) :
    Wf (framesLoop rp re rc rt B) :=
  wf_seq (Layout.wf_subTo _ _ _) (wf_whileNz (wf_seq hB (wf_seq (Layout.wf_loadTo _ _)
    (wf_seq (Layout.wf_addTo _ _ _) (wf_seq (Layout.wf_addTo _ _ _) (Layout.wf_subTo _ _ _))))))

theorem runsTo_goodChk {M : Mem} {n a q : ℕ} {t : List ℕ} (h1 : M 1 = 1) (h11 : M 11 = n + n)
    (h27 : M 27 = q) (hq : 64 ≤ q) (h21 : M 21 = a + a)
    (hblk : Blk M q (RAM.frame (Enc.encode t))) :
    RunsTo goodChk (fun m => m = M)
      (fun m => Outside Wg M m ∧ m 33 = if Good n a t then 1 else 0) (32 * t.length + 12) := by
  rw [Blk.frame_iff, length_encode_nat_list] at hblk
  obtain ⟨hlen, hents⟩ := hblk
  change Blk M (q + 1) (encList Enc.encode t) at hents
  have hE : (encList Enc.encode t).length = 2 * t.length := length_encode_nat_list t
  refine RunsTo.mono (T := 1 + (1 + (1 + (1 + (1 + (32 * t.length + 7)))))) ?_ (by omega)
  refine assign_seq (load_seq (sub_seq (sub_seq (add_seq ?_))))
  refine at_mem (fun M' => Outside Wg M M' ∧ M' 33 = 1 ∧ M' 2 = 2 * t.length ∧
      M' 3 = (2 * t.length - (a + a)) + ((a + a) - 2 * t.length))
    ⟨by outside_tac (Outside.refl Wg M), ?_, ?_, ?_⟩ (fun M' hM' => ?_)
  · simp (disch := omega) only [Mem.update_self, Mem.update_of_ne]
  · simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, h27, hlen]
  · simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, h27, hlen, h21]
  obtain ⟨ho, e33, e2, e3⟩ := hM'
  have f1 : ∀ m, Outside Wg M m → m 1 = 1 := fun m h => by rw [h 1 (by simp), h1]
  have f11 : ∀ m, Outside Wg M m → m 11 = n + n :=
    fun m h => by rw [h 11 (by simp), h11]
  have f27 : ∀ m, Outside Wg M m → m 27 = q := fun m h => by rw [h 27 (by simp), h27]
  by_cases hl : t.length = a
  · -- the lengths agree: run the entry loop
    refine (ifz_eq (T := 1 + (1 + ((0 + (8 + 0 + 8) * (encList Enc.encode t).length + 2))))
      (by rw [e3]; omega) ?_ (Layout.wf_assign _ _)).mono (by rw [hE]; ring_nf; omega)
    refine add_seq (add_seq ?_)
    refine at_mem (fun M'' => Outside Wg M M'' ∧ M'' 33 = 1 ∧ M'' 30 = q + 1 ∧
        M'' 31 = q + 1 + (encList Enc.encode t).length)
      ⟨by outside_tac ho, ?_, ?_, ?_⟩ (fun M'' hM'' => ?_)
    · simp (disch := omega) only [Mem.update_of_ne, e33]
    · simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, f27 _ ho, f1 _ ho]
    · simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, f27 _ ho, f1 _ ho, e2, hE]
    obtain ⟨ho'', e33'', e30, e31⟩ := hM''
    let I : ℕ → Mem → Prop := fun j m =>
      Outside Wg M m ∧ m 33 = if (∀ x ∈ t.take j, x < n) then 1 else 0
    refine (runsTo_framesLoop Enc.encode t (q + 1) framesLoop_regs_entry
      ⟨by omega, by omega, by omega⟩ wf_goodB I (fun _ => 0) 8 0 ?_ ?_ ?_ M''
      ⟨ho'', by rw [e33'']; simp⟩ e30 e31 (f1 _ ho'')
      (Blk.outside hents ho'' (by intro z hz; simp at hz; omega))).weaken ?_
    · intro j m v h
      refine ⟨⟨h.1.upd (by simp) v, (Mem.update_of_ne _ _ (by decide)).trans h.2⟩,
        ⟨h.1.upd (by simp) v, (Mem.update_of_ne _ _ (by decide)).trans h.2⟩,
        ⟨h.1.upd (by simp) v, (Mem.update_of_ne _ _ (by decide)).trans h.2⟩⟩
    · intro m v; exact ⟨rfl, rfl, rfl⟩
    · intro j hj M3 hI h30 h31 h1' hblk
      refine ⟨8, (runsTo_goodB (x := t[j]) h1' (by omega) (by rw [h30]; exact Blk.nat_entry hblk j hj)
        (f11 _ hI.1)).weaken (fun m hm => ?_)⟩
      refine ⟨⟨Outside.sub hI.1 hm.1 (fun z hz => by simp at hz ⊢; omega), ?_⟩,
        hm.1 30 (by simp), hm.1 31 (by simp), by rw [hm.1 1 (by simp), h1'],
        Blk.outside hblk hm.1 (by intro z hz; simp at hz; omega), by simp⟩
      rw [hm.2, hI.2]
      by_cases hx : t[j] < n <;> by_cases hall : ∀ x ∈ t.take j, x < n <;>
        simp [hx, hall, all_take_succ t j hj (· < n)]
    · rintro m ⟨⟨hoI, h33⟩, -⟩
      refine ⟨hoI, ?_⟩
      rw [h33, List.take_length]
      simp [Good, hl]
  · -- the lengths differ: the tuple is not good
    refine (ifz_ne (by rw [e3]; omega) (assign_last ⟨ho.upd (by simp) _, ?_⟩)
      (wf_seq (Layout.wf_addTo _ _ _) (wf_seq (Layout.wf_addTo _ _ _)
        (wf_framesLoop wf_goodB)))).mono (by omega)
    rw [Mem.update_self, if_neg (fun h => hl h.1)]

/-! ## The environment of a trie operation -/

/-- What a trie operation reads besides the trie: the constants and `σ`, all below `root`. -/
structure Env (n SIG root : ℕ) (sig : List ℕ) (M : Mem) : Prop where
  one : M 1 = 1
  n2 : M 11 = n + n
  sigr : M 12 = SIG
  w : M 13 = width n
  hS : 64 ≤ SIG
  sigv : ∀ x < n, M (SIG + x + x) = sig.getD x 0
  sigin : SIG + n + n ≤ root
  siglt : ∀ x < n, sig.getD x 0 < n
  r26 : M 26 = root
  hroot : 64 ≤ root

theorem Env.of_outLo {n SIG root : ℕ} {sig : List ℕ} {M m : Mem} (h : Env n SIG root sig M)
    {W : List ℕ} (ho : OutLo root W M m)
    (hW : ∀ z ∈ W, z < 64 ∧ z ≠ 1 ∧ z ≠ 11 ∧ z ≠ 12 ∧ z ≠ 13 ∧ z ≠ 26) :
    Env n SIG root sig m := by
  have key : ∀ z, z < root → (64 ≤ z ∨ z = 1 ∨ z = 11 ∨ z = 12 ∨ z = 13 ∨ z = 26) →
      m z = M z := by
    intro z hz hz'
    refine ho z hz (fun hzW => ?_)
    have := hW z hzW
    omega
  have hr := h.hroot
  refine ⟨?_, ?_, ?_, ?_, h.hS, ?_, h.sigin, h.siglt, ?_, h.hroot⟩
  · rw [key 1 (by omega) (by omega), h.one]
  · rw [key 11 (by omega) (by omega), h.n2]
  · rw [key 12 (by omega) (by omega), h.sigr]
  · rw [key 13 (by omega) (by omega), h.w]
  · intro x hx
    rw [key _ (by have := h.sigin; omega) (by have := h.hS; omega), h.sigv x hx]
  · rw [key 26 (by omega) (by omega), h.r26]

theorem Env.of_outLo' {n SIG root : ℕ} {sig : List ℕ} {M m : Mem} (h : Env n SIG root sig M)
    {W : List ℕ} (ho : OutLo root W M m)
    (hW : ∀ z ∈ W, z < 64 ∧ z ≠ 1 ∧ z ≠ 11 ∧ z ≠ 12 ∧ z ≠ 13) (h26 : m 26 = root) :
    Env n SIG root sig m := by
  have key : ∀ z, z < root → (64 ≤ z ∨ z = 1 ∨ z = 11 ∨ z = 12 ∨ z = 13) →
      m z = M z := by
    intro z hz hz'
    refine ho z hz (fun hzW => ?_)
    have := hW z hzW
    omega
  have hr := h.hroot
  refine ⟨?_, ?_, ?_, ?_, h.hS, ?_, h.sigin, h.siglt, h26, h.hroot⟩
  · rw [key 1 (by omega) (by omega), h.one]
  · rw [key 11 (by omega) (by omega), h.n2]
  · rw [key 12 (by omega) (by omega), h.sigr]
  · rw [key 13 (by omega) (by omega), h.w]
  · intro x hx
    rw [key _ (by have := h.sigin; omega) (by have := h.hS; omega), h.sigv x hx]

theorem Env.of_outside {n SIG root : ℕ} {sig : List ℕ} {M m : Mem} (h : Env n SIG root sig M)
    {W : List ℕ} (ho : Outside W M m)
    (hW : ∀ z ∈ W, z < 64 ∧ z ≠ 1 ∧ z ≠ 11 ∧ z ≠ 12 ∧ z ≠ 13 ∧ z ≠ 26) :
    Env n SIG root sig m := h.of_outLo (OutLo.of_outside ho) hW

/-- The trie survives register writes (the registers lie below the root). -/
theorem Rep.outside {m m' : Mem} {n root : ℕ} {ps S : List (List ℕ)} (h : Rep m n root ps S)
    {W : List ℕ} (ho : Outside W m m') (hW : ∀ z ∈ W, z < root) : Rep m' n root ps S :=
  h.congr (fun z hz _ => ho z (fun hzW => by have := hW z hzW; omega))

theorem Rep.outLo {m m' : Mem} {n root : ℕ} {ps S : List (List ℕ)} (h : Rep m n root ps S)
    {W : List ℕ} (ho : OutLo root W m m') (hW : ∀ z ∈ W, z < root)
    (hhi : ∀ z, root ≤ z → z < next n root ps → m' z = m z) : Rep m' n root ps S :=
  h.congr hhi

theorem mapB_image {ms : Bool} {n : ℕ} {sig : List ℕ} (hlt : ∀ x < n, sig.getD x 0 < n) {x : ℕ}
    (hx : x < n) : imgX ms sig x < n := by
  cases ms
  · exact hx
  · exact hlt x hx

theorem imgT_lt {ms : Bool} {n : ℕ} {sig : List ℕ} (hlt : ∀ x < n, sig.getD x 0 < n)
    {t : List ℕ} (ht : ∀ x ∈ t, x < n) : ∀ y ∈ imgT ms sig t, y < n := by
  cases ms
  · exact ht
  · intro y hy
    simp only [imgT, if_true, List.mem_map] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact hlt x (ht x hx)

/-! ## Looking a tuple up in a trie -/

/-- One step of a lookup along the current entry (mapped if `ms`): register `34` follows the
child pointer, unless it is already `0`. -/
def qryB (ms : Bool) : Program :=
  seq rdX (seq (mapB ms) (ifz 34 (seq (addTo 3 34 1) (seq (addTo 3 3 35) (seq (addTo 3 3 35)
    (loadTo 34 3)))) []))

theorem wf_rdX : Wf rdX := wf_seq (Layout.wf_addTo _ _ _) (Layout.wf_loadTo _ _)

theorem wf_qryB (ms : Bool) : Wf (qryB ms) :=
  wf_seq wf_rdX (wf_seq (wf_mapB ms) (wf_ifz (wf_seq (Layout.wf_addTo _ _ _)
    (wf_seq (Layout.wf_addTo _ _ _) (wf_seq (Layout.wf_addTo _ _ _) (Layout.wf_loadTo _ _))))
    wf_nil))

/-- The registers a lookup writes (before the flag). -/
notation "Wq" => [2, 3, 4, 30, 31, 32, 34, 35, 36]

theorem runsTo_qryB (ms : Bool) {M M3 : Mem} {n SIG root : ℕ} {sig : List ℕ}
    {ps S : List (List ℕ)} (hE : Env n SIG root sig M3) (hR : Rep M n root ps S)
    (hout : Outside Wq M M3) {x : ℕ} (hx : x < n) (h30 : 4 ≤ M3 30)
    (hX : M3 (M3 30 + 1) = x) {p : List ℕ} (hp : ∀ y ∈ p, y < n)
    (h34 : M3 34 = walk M root p) :
    RunsTo (qryB ms) (fun m => m = M3)
      (fun m => Outside [3, 35, 34] M3 m ∧ m 34 = walk M root (p ++ [imgX ms sig x])) 11 := by
  refine RunsTo.mono (T := 2 + (3 + (4 + 2))) ?_ (by omega)
  refine block_seq (runsTo_rdX hE.one h30 hX) (fun M4 hM4 => ?_)
  obtain ⟨ho4, h35⟩ := hM4
  have hE4 : Env n SIG root sig M4 := hE.of_outside ho4 (by intro z hz; simp at hz; omega)
  refine block_seq (runsTo_mapB ms (n := n) (sig := sig) (by rw [hE4.sigr]; have := hE.hS; omega)
    (by rw [hE4.sigr]; exact hE4.sigv) (by rw [h35]; exact hx)) (fun M5 hM5 => ?_)
  obtain ⟨ho5, h35'⟩ := hM5
  rw [h35] at h35'
  have e34 : M5 34 = walk M root p := by
    rw [ho5 34 (by simp), ho4 34 (by simp), h34]
  have hwalk := walk_eq hR (by have := hE.hroot; omega) p hp
  have hX' : imgX ms sig x < n := mapB_image hE.siglt hx
  by_cases hnd : M5 34 = 0
  · refine (ifz_eq (T := 0) hnd (runsTo_nil (fun m hm => ?_)) (wf_seq (Layout.wf_addTo _ _ _)
      (wf_seq (Layout.wf_addTo _ _ _) (wf_seq (Layout.wf_addTo _ _ _)
        (Layout.wf_loadTo _ _))))).mono (by omega)
    subst hm
    refine ⟨Outside.sub (ho4.mono (by simp)) ho5 (by simp), ?_⟩
    rw [walk_append, ← e34, hnd, stepW, if_pos rfl]
  · refine ifz_ne hnd (add_seq (add_seq (add_seq (load_last ⟨?_, ?_⟩)))) wf_nil
    · have h45 : Outside [3, 35, 34] M3 M5 := Outside.sub (ho4.mono (by simp)) ho5 (by simp)
      outside_tac h45
    · rw [walk_append, ← e34, stepW, if_neg hnd]
      -- the node is a real node, at or above the root
      have hnode : root ≤ M5 34 := by
        rw [e34, hwalk]; split_ifs with h
        · unfold addr; omega
        · exact absurd (by rw [e34, hwalk, if_neg h]) hnd
      have e1 : M5 1 = 1 := by rw [ho5 1 (by simp), ho4 1 (by simp), hE.one]
      have hr := hE.hroot
      simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, e1, h35']
      have := ho5 (M5 34 + 1 + imgX ms sig x + imgX ms sig x)
        (by simp; have := hE.hroot; omega)
      rw [this, ho4 _ (by simp; have := hE.hroot; omega),
        hout _ (by simp; have := hE.hroot; omega)]

/-- The flag at the end of a successful walk is nonzero exactly for the stored strings. -/
theorem walk_flag {m : Mem} {n root : ℕ} {ps S : List (List ℕ)} (h : Rep m n root ps S)
    (hroot : 0 < root) (t : List ℕ) (ht : ∀ x ∈ t, x < n) (hw : walk m root t ≠ 0) :
    m (walk m root t) ≠ 0 ↔ t ∈ S := by
  have hwe := walk_eq h hroot t ht
  by_cases hmem : t ∈ ps
  · rw [hwe, if_pos hmem]
    have := h.flag (ps.idxOf t) (idxOf_lt hmem)
    rw [getElem_idxOf hmem] at this
    rw [this]
    by_cases hS : t ∈ S <;> simp [hS]
  · rw [hwe, if_neg hmem] at hw; exact absurd rfl hw

theorem walk_zero_not_mem {m : Mem} {n root : ℕ} {ps S : List (List ℕ)} (h : Rep m n root ps S)
    (hroot : 0 < root) (t : List ℕ) (ht : ∀ x ∈ t, x < n) (hw : walk m root t = 0) : t ∉ S := by
  intro hS
  have := (query_iff h hroot t ht).2 hS
  exact this.1 hw

/-- **A lookup.**  The tuple at register `27` (mapped by `σ` if `ms`) is looked up in the trie
at register `26`; the flag `15` is cleared if it is not stored. -/
def qryOp (ms : Bool) : Program :=
  seq (copyTo 34 26) (seq (addTo 30 27 1) (seq (loadTo 2 27) (seq (addTo 31 30 2)
    (seq (framesLoop 30 31 32 36 (qryB ms))
      (ifz 34 (seq (loadTo 4 34) (ifz 4 [] (assign 15 0))) (assign 15 0))))))

theorem wf_qryOp (ms : Bool) : Wf (qryOp ms) :=
  wf_seq (Layout.wf_copyTo _ _) (wf_seq (Layout.wf_addTo _ _ _) (wf_seq (Layout.wf_loadTo _ _)
    (wf_seq (Layout.wf_addTo _ _ _) (wf_seq (wf_framesLoop (wf_qryB ms))
      (wf_ifz (wf_seq (Layout.wf_loadTo _ _) (wf_ifz wf_nil (Layout.wf_assign _ _)))
        (Layout.wf_assign _ _))))))

theorem runsTo_qryOp (ms : Bool) {M : Mem} {n SIG root q : ℕ} {sig : List ℕ}
    {ps S : List (List ℕ)} {t : List ℕ} (hE : Env n SIG root sig M) (hR : Rep M n root ps S)
    (h27 : M 27 = q) (hq : 64 ≤ q) (hblk : Blk M q (RAM.frame (Enc.encode t)))
    (ht : ∀ x ∈ t, x < n) :
    RunsTo (qryOp ms) (fun m => m = M)
      (fun m => Outside (15 :: Wq) M m ∧ m 15 = if imgT ms sig t ∈ S then M 15 else 0)
      (38 * t.length + 12) := by
  rw [Blk.frame_iff, length_encode_nat_list] at hblk
  obtain ⟨hlen, hents⟩ := hblk
  change Blk M (q + 1) (encList Enc.encode t) at hents
  have hEl : (encList Enc.encode t).length = 2 * t.length := length_encode_nat_list t
  have hr := hE.hroot
  have hwq : ∀ z ∈ Wq, z < 64 ∧ z ≠ 1 ∧ z ≠ 11 ∧ z ≠ 12 ∧ z ≠ 13 ∧ z ≠ 26 := by
    intro z hz; simp at hz; omega
  set u := imgT ms sig t with hu
  have hul : ∀ y ∈ u, y < n := imgT_lt hE.siglt ht
  refine RunsTo.mono (T := 1 + (1 + (1 + (1 + ((0 + (11 + 0 + 8) *
    (encList Enc.encode t).length + 2) + 6))))) ?_ (by rw [hEl]; ring_nf; omega)
  refine copy_seq (add_seq (load_seq (add_seq ?_)))
  refine at_mem (fun M' => Outside Wq M M' ∧ M' 30 = q + 1 ∧
      M' 31 = q + 1 + (encList Enc.encode t).length ∧ M' 34 = root)
    ⟨by outside_tac (Outside.refl Wq M), ?_, ?_, ?_⟩ (fun M' hM' => ?_)
  · simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, h27, hE.one]
  · simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, h27, hE.one, hlen, hEl]
  · simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, hE.r26]
  obtain ⟨ho, e30, e31, e34⟩ := hM'
  let I : ℕ → Mem → Prop := fun j m => Outside Wq M m ∧ m 34 = walk M root (u.take j)
  refine block_seq (runsTo_framesLoop Enc.encode t (q + 1) framesLoop_regs_entry
      ⟨by omega, by omega, by omega⟩ (wf_qryB ms) I (fun _ => 0) 11 0 ?_ ?_ ?_ M'
      ⟨ho, by rw [e34]; simp [walk]⟩ e30 e31 (by rw [ho 1 (by simp), hE.one])
      (Blk.outside hents ho (by intro z hz; simp at hz; omega))) (fun M'' hM'' => ?_)
  · intro j m v h
    refine ⟨⟨h.1.upd (by simp) v, (Mem.update_of_ne _ _ (by decide)).trans h.2⟩,
      ⟨h.1.upd (by simp) v, (Mem.update_of_ne _ _ (by decide)).trans h.2⟩,
      ⟨h.1.upd (by simp) v, (Mem.update_of_ne _ _ (by decide)).trans h.2⟩⟩
  · intro m v; exact ⟨rfl, rfl, rfl⟩
  · intro j hj M3 hI h30 h31 h1' hblk'
    have hE3 := hE.of_outside hI.1 hwq
    refine ⟨11, (runsTo_qryB ms (x := t[j]) (p := u.take j) hE3 hR hI.1 (ht _ (List.getElem_mem _))
      (by omega) (by rw [h30]; exact Blk.nat_entry hblk' j hj)
      (fun y hy => hul y (List.mem_of_mem_take hy)) hI.2).weaken (fun m hm => ?_)⟩
    refine ⟨⟨Outside.sub hI.1 hm.1 (fun z hz => by simp at hz ⊢; omega), ?_⟩,
      hm.1 30 (by simp), hm.1 31 (by simp), by rw [hm.1 1 (by simp), h1'],
      Blk.outside hblk' hm.1 (by intro z hz; simp at hz; omega), by simp⟩
    rw [hm.2, hu, imgT_take_succ ms sig t j hj]
  obtain ⟨⟨ho'', e34''⟩, -, -, -, -⟩ := hM''
  rw [show t.length = u.length by rw [hu, imgT_length], List.take_length] at e34''
  by_cases hnd : M'' 34 = 0
  · refine (ifz_eq (T := 1) hnd (assign_last ⟨?_, ?_⟩) (wf_seq (Layout.wf_loadTo _ _)
      (wf_ifz wf_nil (Layout.wf_assign _ _)))).mono (by omega)
    · exact (ho''.mono (fun z hz => by simp at hz ⊢; omega)).upd (by simp) _
    · rw [Mem.update_self, if_neg (walk_zero_not_mem hR (by omega) u hul (by rw [← e34'', hnd]))]
  · have hflag := walk_flag hR (by omega) u hul (by rw [← e34'']; exact hnd)
    rw [← e34''] at hflag
    have hnode : root ≤ M'' 34 := by
      have := walk_eq hR (by omega) u hul
      rw [← e34''] at this
      rw [this]; split_ifs with h
      · unfold addr; omega
      · exact absurd (by rw [this, if_neg h]) hnd
    have e15 : M'' 15 = M 15 := ho'' 15 (by simp)
    have eM : M'' (M'' 34) = M (M'' 34) := by
      exact ho'' _ (by simp; omega)
    refine (ifz_ne (T := 1 + 3) hnd (load_seq ?_) (Layout.wf_assign _ _)).mono (by omega)
    have e4 : (M''.update 4 (M'' (M'' 34))) 4 = M (M'' 34) := by rw [Mem.update_self, eM]
    by_cases hf : M (M'' 34) = 0
    · refine ifz_eq (by rw [e4, hf]) (assign_last ⟨?_, ?_⟩) wf_nil
      · exact (((ho''.mono (fun z hz => by simp at hz ⊢; omega)).upd (by simp) _).upd
          (by simp) _)
      · rw [Mem.update_self, if_neg (fun h => hflag.2 h hf)]
    · refine (ifz_ne (by rw [e4]; exact hf) (runsTo_nil (fun m hm => ?_))
        (Layout.wf_assign _ _)).mono (by omega)
      subst hm
      refine ⟨((ho''.mono (fun z hz => by simp at hz ⊢; omega)).upd (by simp) _), ?_⟩
      rw [Mem.update_of_ne _ _ (by decide), e15, if_pos (hflag.1 hf)]

/-! ## Storing a tuple in a trie -/

/-- One step of an insertion along the current entry (mapped if `ms`): follow the child
pointer, allocating the child at the pointer `14` if it is missing. -/
def insB (ms : Bool) : Program :=
  seq rdX (seq (mapB ms) (seq (addTo 3 34 1) (seq (addTo 3 3 35) (seq (addTo 3 3 35)
    (seq (loadTo 4 3) (seq (ifz 4 [] (seq (storeTo 3 14) (addTo 14 14 13))) (loadTo 34 3)))))))

theorem wf_insB (ms : Bool) : Wf (insB ms) :=
  wf_seq wf_rdX (wf_seq (wf_mapB ms) (wf_seq (Layout.wf_addTo _ _ _) (wf_seq (Layout.wf_addTo _ _ _)
    (wf_seq (Layout.wf_addTo _ _ _) (wf_seq (Layout.wf_loadTo _ _) (wf_seq
      (wf_ifz wf_nil (wf_seq (Layout.wf_storeTo _ _) (Layout.wf_addTo _ _ _)))
      (Layout.wf_loadTo _ _)))))))

theorem next_append (n root : ℕ) (ps : List (List ℕ)) (q : List ℕ) :
    next n root (ps ++ [q]) = next n root ps + width n := by
  simp [next, addr, Nat.mul_add]; ring

theorem idxOf_append_new {ps : List (List ℕ)} {q : List ℕ} (h : q ∉ ps) :
    (ps ++ [q]).idxOf q = ps.length := by
  rw [List.idxOf_append_of_notMem h]; simp

theorem addr_lt_next {n root : ℕ} {ps : List (List ℕ)} {q : List ℕ} (h : q ∈ ps) (j : ℕ)
    (hj : j < width n) : addr n root (ps.idxOf q) + j < next n root ps := by
  have hi := idxOf_lt h
  unfold next addr
  have : width n * ps.idxOf q + width n ≤ width n * ps.length := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hi
  omega

theorem runsTo_insB (ms : Bool) {M3 : Mem} {n SIG root : ℕ} {sig : List ℕ}
    {ps S : List (List ℕ)} (hE : Env n SIG root sig M3) (hR : Rep M3 n root ps S)
    (h14 : M3 14 = next n root ps) (hfr : ∀ z, M3 14 ≤ z → M3 z = 0)
    {x : ℕ} (hx : x < n) (h30 : 4 ≤ M3 30) (hX : M3 (M3 30 + 1) = x) {p : List ℕ}
    (hp : p ∈ ps) (h34 : M3 34 = addr n root (ps.idxOf p)) :
    RunsTo (insB ms) (fun m => m = M3)
      (fun m => ∃ ps', Rep m n root ps' S ∧ m 14 = next n root ps' ∧
        (∀ z, m 14 ≤ z → m z = 0) ∧ OutLo root [3, 4, 14, 34, 35] M3 m ∧
        p ++ [imgX ms sig x] ∈ ps' ∧ m 34 = addr n root (ps'.idxOf (p ++ [imgX ms sig x])))
      14 := by
  have hr := hE.hroot
  refine RunsTo.mono (T := 2 + (3 + (1 + (1 + (1 + (1 + (4 + 1))))))) ?_ (by omega)
  refine block_seq (runsTo_rdX hE.one h30 hX) (fun M4 hM4 => ?_)
  obtain ⟨ho4, h35⟩ := hM4
  have hE4 : Env n SIG root sig M4 := hE.of_outside ho4 (by intro z hz; simp at hz; omega)
  refine block_seq (runsTo_mapB ms (n := n) (sig := sig) (by rw [hE4.sigr]; have := hE.hS; omega)
    (by rw [hE4.sigr]; exact hE4.sigv) (by rw [h35]; exact hx)) (fun M5 hM5 => ?_)
  obtain ⟨ho5, h35'⟩ := hM5
  rw [h35] at h35'
  set X := imgX ms sig x with hXdef
  have hXn : X < n := mapB_image hE.siglt hx
  have ho45 : Outside [3, 35] M3 M5 := Outside.sub ho4 ho5 (by simp)
  have e34 : M5 34 = addr n root (ps.idxOf p) := by rw [ho45 34 (by simp), h34]
  have e1 : M5 1 = 1 := by rw [ho45 1 (by simp), hE.one]
  set c := addr n root (ps.idxOf p) + 1 + X + X with hc
  have hc_lt : c < next n root ps := by
    have := addr_lt_next (n := n) (root := root) hp (1 + X + X) (child_lt_width hXn)
    rw [hc]; omega
  have hc_ge : root ≤ c := by rw [hc]; unfold addr; omega
  have hchild := hR.child (ps.idxOf p) (idxOf_lt hp) X hXn
  rw [getElem_idxOf hp] at hchild
  refine add_seq (add_seq (add_seq (load_seq ?_)))
  refine at_mem (fun M' => Outside [3, 4, 35] M3 M' ∧ M' 3 = c ∧
      M' 4 = (if p ++ [X] ∈ ps then addr n root (ps.idxOf (p ++ [X])) else 0))
    ⟨by outside_tac ho45, ?_, ?_⟩ (fun M' hM' => ?_)
  · simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, e34, e1, h35']
    exact hc.symm
  · simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, e34, e1, h35']
    rw [← hc, ho45 c (by simp; omega), hchild]
  obtain ⟨ho', e3, e4⟩ := hM'
  have hR' : Rep M' n root ps S := Rep.outside hR ho' (by intro z hz; simp at hz; omega)
  have e14 : M' 14 = next n root ps := by rw [ho' 14 (by simp), h14]
  have hfr' : ∀ z, M' 14 ≤ z → M' z = 0 := by
    intro z hz; rw [e14] at hz
    rw [ho' z (by simp; unfold next addr at hz; omega)]; exact hfr z (by rw [h14]; exact hz)
  have hOut : OutLo root [3, 4, 14, 34, 35] M3 M' :=
    OutLo.of_outside (ho'.mono (by simp))
  by_cases hmem : p ++ [X] ∈ ps
  · -- the child exists
    rw [if_pos hmem] at e4
    refine ((ifz_ne (T := 0) (post := fun m => m = M') (by rw [e4]; exact addr_pos (by omega))
      (runsTo_nil (fun m hm => hm)) (wf_seq (Layout.wf_storeTo _ _) (Layout.wf_addTo _ _ _))).seq
      (load_last (M := M') ?_)).mono (by omega)
    · refine ⟨ps, hR'.update_out (Or.inl (by omega)), ?_, ?_, hOut.upd (by simp) _, hmem, ?_⟩
      · rw [Mem.update_of_ne _ _ (by decide), e14]
      · intro z hz
        rw [Mem.update_of_ne _ _ (by decide)] at hz
        rw [Mem.update_of_ne _ _ (by rw [e14] at hz; unfold next addr at hz; omega)]
        exact hfr' z hz
      · rw [Mem.update_self, e3]
        have := hR'.child (ps.idxOf p) (idxOf_lt hp) X hXn
        rw [getElem_idxOf hp, if_pos hmem] at this
        exact this
  · -- the child is missing: allocate it at the pointer
    rw [if_neg hmem] at e4
    obtain ⟨hRn, hfrn⟩ := hR'.addChild (fun z hz => hfr' z (by rw [e14]; exact hz)) hp hXn hmem
    rw [← hc] at hRn hfrn
    set ps' := ps ++ [p ++ [X]] with hps'
    have hw := hE.of_outside ho' (by intro z hz; simp at hz; omega) |>.w
    refine (block_seq (ifz_eq (T := 2) e4 (store_seq (add_last (post := fun m => Rep m n root ps' S ∧
        m 14 = next n root ps' ∧ (∀ z, m 14 ≤ z → m z = 0) ∧
        OutLo root [3, 4, 14, 34, 35] M3 m ∧ m 3 = c ∧ m c = next n root ps) ?_)) wf_nil)
      (fun m hm => load_last (M := m) ?_)).mono (by omega)
    · rw [e3, e14]
      have hc14 : c ≠ 14 := by omega
      refine ⟨hRn.update_out (Or.inl (by omega)), ?_, ?_, ?_, ?_, ?_⟩
      · simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, hw, e14]
        rw [hps', next_append]
      · intro z hz
        simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, hw, e14] at hz
        rw [Mem.update_of_ne _ _ (by unfold next addr at hz; omega)]
        exact hfrn z (by rw [hps', next_append]; exact hz)
      · exact (hOut.upd (Or.inr hc_ge) _).upd (Or.inl (by simp)) _
      · rw [Mem.update_of_ne _ _ (by decide), Mem.update_of_ne _ _ (by omega), e3]
      · rw [Mem.update_of_ne _ _ hc14, Mem.update_self]
    · obtain ⟨hRm, e14m, hfrm, hOm, e3m, ecm⟩ := hm
      refine ⟨ps', hRm.update_out (Or.inl (by omega)), ?_, ?_, hOm.upd (by simp) _, by simp [hps'],
        ?_⟩
      · rw [Mem.update_of_ne _ _ (by decide), e14m]
      · intro z hz
        rw [Mem.update_of_ne _ _ (by decide)] at hz
        rw [Mem.update_of_ne _ _ (by rw [e14m] at hz; unfold next addr at hz; omega)]
        exact hfrm z hz
      · rw [Mem.update_self, e3m, ecm, hps', idxOf_append_new hmem]; rfl

/-- **An insertion.**  The tuple at register `27` (mapped by `σ` if `ms`) is stored in the
trie at register `26`. -/
def insOp (ms : Bool) : Program :=
  seq (copyTo 34 26) (seq (addTo 30 27 1) (seq (loadTo 2 27) (seq (addTo 31 30 2)
    (seq (framesLoop 30 31 32 36 (insB ms)) (storeTo 34 1)))))

theorem wf_insOp (ms : Bool) : Wf (insOp ms) :=
  wf_seq (Layout.wf_copyTo _ _) (wf_seq (Layout.wf_addTo _ _ _) (wf_seq (Layout.wf_loadTo _ _)
    (wf_seq (Layout.wf_addTo _ _ _) (wf_seq (wf_framesLoop (wf_insB ms))
      (Layout.wf_storeTo _ _)))))

/-- The registers an insertion writes. -/
notation "Wi" => [2, 3, 4, 14, 30, 31, 32, 34, 35, 36]

theorem runsTo_insOp (ms : Bool) {M : Mem} {n SIG root q : ℕ} {sig : List ℕ}
    {ps S : List (List ℕ)} {t : List ℕ} (hE : Env n SIG root sig M) (hR : Rep M n root ps S)
    (h14 : M 14 = next n root ps) (hfr : ∀ z, M 14 ≤ z → M z = 0)
    (h27 : M 27 = q) (hq : 64 ≤ q) (hblk : Blk M q (RAM.frame (Enc.encode t)))
    (hqr : q + 1 + 2 * t.length ≤ root) (ht : ∀ x ∈ t, x < n) :
    RunsTo (insOp ms) (fun m => m = M)
      (fun m => ∃ ps', Rep m n root ps' (imgT ms sig t :: S) ∧ m 14 = next n root ps' ∧
        (∀ z, m 14 ≤ z → m z = 0) ∧ OutLo root Wi M m)
      (44 * t.length + 7) := by
  rw [Blk.frame_iff, length_encode_nat_list] at hblk
  obtain ⟨hlen, hents⟩ := hblk
  change Blk M (q + 1) (encList Enc.encode t) at hents
  have hEl : (encList Enc.encode t).length = 2 * t.length := length_encode_nat_list t
  have hr := hE.hroot
  have hwi : ∀ z ∈ Wi, z < 64 ∧ z ≠ 1 ∧ z ≠ 11 ∧ z ≠ 12 ∧ z ≠ 13 ∧ z ≠ 26 := by
    intro z hz; simp at hz; omega
  set u := imgT ms sig t with hu
  refine RunsTo.mono (T := 1 + (1 + (1 + (1 + ((0 + (14 + 0 + 8) *
    (encList Enc.encode t).length + 2) + 1))))) ?_ (by rw [hEl]; ring_nf; omega)
  refine copy_seq (add_seq (load_seq (add_seq ?_)))
  refine at_mem (fun M' => Outside [2, 30, 31, 34] M M' ∧ M' 30 = q + 1 ∧
      M' 31 = q + 1 + (encList Enc.encode t).length ∧ M' 34 = root)
    ⟨by outside_tac (Outside.refl [2, 30, 31, 34] M), ?_, ?_, ?_⟩ (fun M' hM' => ?_)
  · simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, h27, hE.one]
  · simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, h27, hE.one, hlen, hEl]
  · simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, hE.r26]
  obtain ⟨ho, e30, e31, e34⟩ := hM'
  have hR0 : Rep M' n root ps S := Rep.outside hR ho (by intro z hz; simp at hz; omega)
  let I : ℕ → Mem → Prop := fun j m => ∃ ps', Rep m n root ps' S ∧ m 14 = next n root ps' ∧
    (∀ z, m 14 ≤ z → m z = 0) ∧ OutLo root Wi M m ∧ u.take j ∈ ps' ∧
    m 34 = addr n root (ps'.idxOf (u.take j))
  have hI0 : I 0 M' := by
    refine ⟨ps, hR0, by rw [ho 14 (by simp), h14], ?_, (OutLo.of_outside ho).mono (by simp), ?_, ?_⟩
    · intro z hz
      rw [ho 14 (by simp), h14] at hz
      rw [ho z (by simp; unfold next addr at hz; omega)]
      exact hfr z (by rw [h14]; exact hz)
    · simpa using hR.head.1
    · rw [e34]; simp [hR.head.2, addr]
  have hstab1 : ∀ j m v (r : ℕ), r ∈ Wi → r ≠ 14 → r ≠ 34 → I j m → I j (m.update r v) := by
    intro j m v r hr hr14 hr34 ⟨ps', hR', e14', hfr', hO', hmem', e34'⟩
    have hr64 : r < 64 := by simp at hr; omega
    refine ⟨ps', hR'.update_out (Or.inl (by omega)), ?_, ?_, hO'.upd (Or.inl hr) _, hmem', ?_⟩
    · rw [Mem.update_of_ne _ _ (Ne.symm hr14), e14']
    · intro z hz
      rw [Mem.update_of_ne _ _ (Ne.symm hr14)] at hz
      rw [Mem.update_of_ne _ _ (by rw [e14'] at hz; unfold next addr at hz; omega)]
      exact hfr' z hz
    · rw [Mem.update_of_ne _ _ (Ne.symm hr34), e34']
  refine block_seq (runsTo_framesLoop Enc.encode t (q + 1) framesLoop_regs_entry
      ⟨by omega, by omega, by omega⟩ (wf_insB ms) I (fun _ => 0) 14 0 ?_ ?_ ?_ M'
      hI0 e30 e31 (by rw [ho 1 (by simp), hE.one])
      (Blk.outside hents ho (by intro z hz; simp at hz; omega))) (fun M'' hM'' => ?_)
  · intro j m v h
    exact ⟨hstab1 j m v 30 (by simp) (by decide) (by decide) h,
      hstab1 j m v 32 (by simp) (by decide) (by decide) h,
      hstab1 j m v 36 (by simp) (by decide) (by decide) h⟩
  · intro m v; exact ⟨rfl, rfl, rfl⟩
  · intro j hj M3 hI h30 h31 h1' hblk'
    obtain ⟨ps', hR', e14', hfr', hO', hmem', e34'⟩ := hI
    have hE3 := hE.of_outLo (hO'.mono (fun z hz => hz)) hwi
    refine ⟨14, (runsTo_insB ms (x := t[j]) (p := u.take j) hE3 hR' e14' hfr'
      (ht _ (List.getElem_mem _)) (by omega) (by rw [h30]; exact Blk.nat_entry hblk' j hj)
      hmem' e34').weaken (fun m hm => ?_)⟩
    obtain ⟨ps'', hR'', e14'', hfr'', hO'', hmem'', e34''⟩ := hm
    have hO3 : OutLo root Wi M m := hO'.trans hO'' (fun z hz => by simp at hz ⊢; omega)
    have hlt : ∀ z < root, z ∉ [3, 4, 14, 34, 35] → m z = M3 z := hO''
    refine ⟨⟨ps'', hR'', e14'', hfr'', hO3, ?_, ?_⟩, hlt 30 (by omega) (by simp),
      hlt 31 (by omega) (by simp), by rw [hlt 1 (by omega) (by simp), h1'],
      Blk.congr hblk' (fun z hz1 hz2 => hlt z ?_ (by simp; omega)), by simp⟩
    · rw [hu, imgT_take_succ ms sig t j hj]; exact hmem''
    · rw [hu, imgT_take_succ ms sig t j hj]; exact e34''
    · rw [hEl] at hz2; omega
  obtain ⟨⟨ps', hR', e14', hfr', hO', hmem', e34'⟩, -, -, -, -⟩ := hM''
  rw [show t.length = u.length by rw [hu, imgT_length], List.take_length] at hmem' e34'
  have e1 : M'' 1 = 1 := by rw [hO' 1 (by omega) (by simp), hE.one]
  have haddr := addr_lt_next (n := n) (root := root) hmem' 0 (by unfold width; omega)
  have hge : root ≤ addr n root (ps'.idxOf u) := by unfold addr; omega
  rw [Nat.add_zero] at haddr
  refine store_last ⟨ps', ?_, ?_, ?_, ?_⟩
  · rw [e34', e1]; exact hR'.setFlag hmem'
  · rw [Mem.update_of_ne _ _ (by omega), e14']
  · intro z hz
    rw [Mem.update_of_ne _ _ (by omega)] at hz
    rw [Mem.update_of_ne _ _ (by rw [e34']; omega)]
    exact hfr' z hz
  · exact hO'.upd (Or.inr (by rw [e34']; exact hge)) _

/-! ## Loops over the tuples of a relation -/

theorem exists_take_succ {β : Type*} (t : List β) (j : ℕ) (hj : j < t.length) (P : β → Prop) :
    (∃ x ∈ t.take (j + 1), P x) ↔ (∃ x ∈ t.take j, P x) ∨ P t[j] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some]
  constructor
  · rintro ⟨x, hx, hP⟩
    rw [List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact Or.inl ⟨x, hx, hP⟩
    · exact Or.inr hP
  · rintro (⟨x, hx, hP⟩ | hP)
    · exact ⟨x, List.mem_append_left _ hx, hP⟩
    · exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), hP⟩

/-- One tuple: check it, and run `op` on it if it is a tuple of `[0,n)^a`. -/
def tupB (op : Program) : Program := seq goodChk (ifz 33 op [])

/-- All tuples of a list: register `27` walks the list, register `28` holds its end. -/
def tupLoop (op : Program) : Program := framesLoop 27 28 29 37 (tupB op)

theorem wf_goodChk : Wf goodChk :=
  wf_seq (Layout.wf_assign _ _) (wf_seq (Layout.wf_loadTo _ _) (wf_seq (Layout.wf_subTo _ _ _)
    (wf_seq (Layout.wf_subTo _ _ _) (wf_seq (Layout.wf_addTo _ _ _) (wf_ifz (Layout.wf_assign _ _)
      (wf_seq (Layout.wf_addTo _ _ _) (wf_seq (Layout.wf_addTo _ _ _)
        (wf_framesLoop wf_goodB))))))))

theorem wf_tupLoop {op : Program} (h : Wf op) : Wf (tupLoop op) :=
  wf_framesLoop (wf_seq wf_goodChk (wf_ifz h wf_nil))

theorem framesLoop_regs_tuple : (27 : ℕ) ≠ 28 ∧ (27 : ℕ) ≠ 29 ∧ (27 : ℕ) ≠ 37 ∧ (27 : ℕ) ≠ 1 ∧
    (28 : ℕ) ≠ 29 ∧ (28 : ℕ) ≠ 37 ∧ (28 : ℕ) ≠ 1 ∧ (29 : ℕ) ≠ 37 ∧ (29 : ℕ) ≠ 1 ∧ (37 : ℕ) ≠ 1 := by
  decide

/-- The registers a loop of insertions writes. -/
notation "Wti" => [2, 3, 4, 14, 27, 29, 30, 31, 32, 33, 34, 35, 36, 37]

/-- The registers a loop of lookups writes. -/
notation "Wtq" => [2, 3, 4, 15, 27, 29, 30, 31, 32, 33, 34, 35, 36, 37]

theorem length_frame_encode (t : List ℕ) : (Enc.encode t).length = 2 * t.length :=
  length_encode_nat_list t

/-- **Storing the tuples of a list** that are tuples of `[0,n)^a` (their images, if `ms`). -/
theorem runsTo_insLoop (ms : Bool) {M : Mem} {n SIG root p0 a : ℕ} {sig : List ℕ}
    {ps S : List (List ℕ)} {ts : List (List ℕ)} (hE : Env n SIG root sig M)
    (hR : Rep M n root ps S) (h14 : M 14 = next n root ps) (hfr : ∀ z, M 14 ≤ z → M z = 0)
    (h27 : M 27 = p0) (h28 : M 28 = p0 + (encList Enc.encode ts).length) (h21 : M 21 = a + a)
    (hp0 : 64 ≤ p0) (hblk : Blk M p0 (encList Enc.encode ts))
    (hend : p0 + (encList Enc.encode ts).length ≤ root) :
    RunsTo (tupLoop (insOp ms)) (fun m => m = M)
      (fun m => ∃ ps' S', Rep m n root ps' S' ∧
        (∀ s, s ∈ S' ↔ s ∈ S ∨ ∃ t ∈ ts, Good n a t ∧ imgT ms sig t = s) ∧
        m 14 = next n root ps' ∧ (∀ z, m 14 ≤ z → m z = 0) ∧ OutLo root Wti M m)
      (72 * (encList Enc.encode ts).length + 2) := by
  have hr := hE.hroot
  have hwti : ∀ z ∈ Wti, z < 64 ∧ z ≠ 1 ∧ z ≠ 11 ∧ z ≠ 12 ∧ z ≠ 13 ∧ z ≠ 26 := by
    intro z hz; simp at hz; omega
  let I : ℕ → Mem → Prop := fun j m => ∃ ps' S', Rep m n root ps' S' ∧
    (∀ s, s ∈ S' ↔ s ∈ S ∨ ∃ t ∈ ts.take j, Good n a t ∧ imgT ms sig t = s) ∧
    m 14 = next n root ps' ∧ (∀ z, m 14 ≤ z → m z = 0) ∧ OutLo root Wti M m
  have hstab1 : ∀ j m v (r : ℕ), r ∈ Wti → r ≠ 14 → I j m → I j (m.update r v) := by
    intro j m v r hr' hr14 ⟨ps', S', hR', hS', e14', hfr', hO'⟩
    have hr64 : r < 64 := by simp at hr'; omega
    refine ⟨ps', S', hR'.update_out (Or.inl (by omega)), hS', ?_, ?_, hO'.upd (Or.inl hr') _⟩
    · rw [Mem.update_of_ne _ _ (Ne.symm hr14), e14']
    · intro z hz
      rw [Mem.update_of_ne _ _ (Ne.symm hr14)] at hz
      rw [Mem.update_of_ne _ _ (by rw [e14'] at hz; unfold next addr at hz; omega)]
      exact hfr' z hz
  refine (runsTo_framesLoop Enc.encode ts p0 framesLoop_regs_tuple
      ⟨by omega, by omega, by omega⟩ (wf_seq wf_goodChk (wf_ifz (wf_insOp ms) wf_nil)) I
      (fun _ => 0) 26 38 ?_ ?_ ?_ M ⟨ps, S, hR, by simp, h14, hfr, OutLo.refl _ _ _⟩ h27 h28
      hE.one hblk).weaken ?_ |>.mono (by omega)
  · intro j m v h
    exact ⟨hstab1 j m v 27 (by simp) (by decide) h, hstab1 j m v 29 (by simp) (by decide) h,
      hstab1 j m v 37 (by simp) (by decide) h⟩
  · intro m v; exact ⟨rfl, rfl, rfl⟩
  · intro j hj M3 hI h27' h28' h1' hblk'
    obtain ⟨ps', S', hR', hS', e14', hfr', hO'⟩ := hI
    have hE3 := hE.of_outLo hO' hwti
    have htup := Blk.encList_get hblk' j hj
    have hlt := encList_take_lt Enc.encode ts j hj
    have hlen := length_frame_encode ts[j]
    have e21 : M3 21 = a + a := by rw [hO' 21 (by omega) (by simp), h21]
    have hqr : p0 + (encList Enc.encode (ts.take j)).length + 1 + 2 * ts[j].length ≤ root := by
      omega
    have hfin : ∀ m, OutLo root [2, 3, 4, 14, 30, 31, 32, 33, 34, 35, 36] M3 m →
        m 27 = M3 27 ∧ m 28 = M3 28 ∧ m 1 = 1 ∧ Blk m p0 (encList Enc.encode ts) ∧
        0 + ((32 * ts[j].length + 12) + ((44 * ts[j].length + 7) + 2)) ≤
          0 + 26 + 38 * (Enc.encode ts[j]).length := by
      intro m hm
      refine ⟨hm 27 (by omega) (by simp), hm 28 (by omega) (by simp),
        by rw [hm 1 (by omega) (by simp), h1'], Blk.congr hblk' (fun z hz1 hz2 => hm z (by omega)
          (by simp; omega)), by rw [hlen]; omega⟩
    refine ⟨(32 * ts[j].length + 12) + ((44 * ts[j].length + 7) + 2),
      block_seq (runsTo_goodChk (n := n) (a := a) hE3.one hE3.n2 h27' (by omega) e21 htup)
        (fun M4 hM4 => ?_)⟩
    obtain ⟨ho4, e33⟩ := hM4
    have hR4 : Rep M4 n root ps' S' := Rep.outside hR' ho4 (by intro z hz; simp at hz; omega)
    have e14 : M4 14 = next n root ps' := by rw [ho4 14 (by simp), e14']
    have hfr4 : ∀ z, M4 14 ≤ z → M4 z = 0 := by
      intro z hz; rw [e14] at hz
      rw [ho4 z (by simp; unfold next addr at hz; omega)]; exact hfr' z (by rw [e14']; exact hz)
    have hO4 : OutLo root Wti M M4 :=
      hO'.trans (OutLo.of_outside ho4) (fun z hz => by simp at hz ⊢; omega)
    have hE4 := hE3.of_outside ho4 (by intro z hz; simp at hz; omega)
    have e27 : M4 27 = p0 + (encList Enc.encode (ts.take j)).length := by
      rw [ho4 27 (by simp), h27']
    by_cases hg : Good n a ts[j]
    · rw [if_pos hg] at e33
      refine (ifz_ne (by rw [e33]; decide) (runsTo_insOp ms hE4 hR4 e14 hfr4 e27 (by omega)
        (Blk.outside htup ho4 (by intro z hz; simp at hz; omega)) hqr hg.2)
        wf_nil).weaken (fun m hm => ?_)
      obtain ⟨ps'', hR'', e14'', hfr'', hO''⟩ := hm
      have hO3 : OutLo root [2, 3, 4, 14, 30, 31, 32, 33, 34, 35, 36] M3 m :=
        ((OutLo.of_outside ho4).mono (fun z hz => by simp at hz ⊢; omega)).trans hO''
          (fun z hz => by simp at hz ⊢; omega)
      refine ⟨⟨ps'', imgT ms sig ts[j] :: S', hR'', fun s => ?_, e14'', hfr'',
        hO4.trans hO'' (fun z hz => by simp at hz ⊢; omega)⟩, hfin m hO3⟩
      rw [List.mem_cons, hS', exists_take_succ ts j hj]
      constructor
      · rintro (rfl | h | h)
        · exact Or.inr (Or.inr ⟨hg, rfl⟩)
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
      · rintro (h | h | ⟨-, rfl⟩)
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
        · exact Or.inl rfl
    · rw [if_neg hg] at e33
      refine (ifz_eq (T := 0) e33 (runsTo_nil (fun m hm => ?_)) (wf_insOp ms)).mono (by omega)
      subst hm
      refine ⟨⟨ps', S', hR4, fun s => ?_, e14, hfr4, hO4⟩,
        hfin _ ((OutLo.of_outside ho4).mono (fun z hz => by simp at hz ⊢; omega))⟩
      rw [hS', exists_take_succ ts j hj]
      constructor
      · rintro (h | h)
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
      · rintro (h | h | ⟨h, -⟩)
        · exact Or.inl h
        · exact Or.inr h
        · exact absurd h hg
  · rintro m ⟨⟨ps', S', hR', hS', e14', hfr', hO'⟩, -⟩
    refine ⟨ps', S', hR', fun s => ?_, e14', hfr', hO'⟩
    rw [hS', List.take_length]

/-- **Looking up the tuples of a list** that are tuples of `[0,n)^a` (their images, if
`ms`): the flag `15` survives exactly when all of them are stored. -/
theorem runsTo_qryLoop (ms : Bool) {M : Mem} {n SIG root p0 a : ℕ} {sig : List ℕ}
    {ps S : List (List ℕ)} {ts : List (List ℕ)} {b : Prop} [Decidable b]
    (hE : Env n SIG root sig M) (hR : Rep M n root ps S)
    (h27 : M 27 = p0) (h28 : M 28 = p0 + (encList Enc.encode ts).length) (h21 : M 21 = a + a)
    (hp0 : 64 ≤ p0) (hblk : Blk M p0 (encList Enc.encode ts))
    (hend : p0 + (encList Enc.encode ts).length ≤ root) (h15 : M 15 = if b then 1 else 0) :
    RunsTo (tupLoop (qryOp ms)) (fun m => m = M)
      (fun m => Outside Wtq M m ∧
        m 15 = if (b ∧ ∀ t ∈ ts, Good n a t → imgT ms sig t ∈ S) then 1 else 0)
      (72 * (encList Enc.encode ts).length + 2) := by
  have hr := hE.hroot
  have hwtq : ∀ z ∈ Wtq, z < 64 ∧ z ≠ 1 ∧ z ≠ 11 ∧ z ≠ 12 ∧ z ≠ 13 ∧ z ≠ 26 := by
    intro z hz; simp at hz; omega
  let I : ℕ → Mem → Prop := fun j m => Outside Wtq M m ∧
    m 15 = if (b ∧ ∀ t ∈ ts.take j, Good n a t → imgT ms sig t ∈ S) then 1 else 0
  refine (runsTo_framesLoop Enc.encode ts p0 framesLoop_regs_tuple
      ⟨by omega, by omega, by omega⟩ (wf_seq wf_goodChk (wf_ifz (wf_qryOp ms) wf_nil)) I
      (fun _ => 0) 26 38 ?_ ?_ ?_ M ⟨Outside.refl _ _, by rw [h15]; simp⟩ h27 h28
      hE.one hblk).weaken ?_ |>.mono (by omega)
  · intro j m v h
    exact ⟨⟨h.1.upd (by simp) v, (Mem.update_of_ne _ _ (by decide)).trans h.2⟩,
      ⟨h.1.upd (by simp) v, (Mem.update_of_ne _ _ (by decide)).trans h.2⟩,
      ⟨h.1.upd (by simp) v, (Mem.update_of_ne _ _ (by decide)).trans h.2⟩⟩
  · intro m v; exact ⟨rfl, rfl, rfl⟩
  · intro j hj M3 hI h27' h28' h1' hblk'
    obtain ⟨hO', e15'⟩ := hI
    have hE3 := hE.of_outside hO' hwtq
    have htup := Blk.encList_get hblk' j hj
    have hlt := encList_take_lt Enc.encode ts j hj
    have hlen := length_frame_encode ts[j]
    have e21 : M3 21 = a + a := by rw [hO' 21 (by simp), h21]
    have hfin : ∀ m, Outside [2, 3, 4, 15, 30, 31, 32, 33, 34, 35, 36] M3 m →
        Outside Wtq M m ∧ m 27 = M3 27 ∧ m 28 = M3 28 ∧ m 1 = 1 ∧
        Blk m p0 (encList Enc.encode ts) ∧
        0 + ((32 * ts[j].length + 12) + ((38 * ts[j].length + 12) + 2)) ≤
          0 + 26 + 38 * (Enc.encode ts[j]).length := by
      intro m hm
      refine ⟨Outside.sub hO' hm (fun z hz => by simp at hz ⊢; omega), hm 27 (by simp),
        hm 28 (by simp), by rw [hm 1 (by simp), h1'],
        Blk.outside hblk' hm (by intro z hz; simp at hz; omega), by rw [hlen]; omega⟩
    refine ⟨(32 * ts[j].length + 12) + ((38 * ts[j].length + 12) + 2),
      block_seq (runsTo_goodChk (n := n) (a := a) hE3.one hE3.n2 h27' (by omega) e21 htup)
        (fun M4 hM4 => ?_)⟩
    obtain ⟨ho4, e33⟩ := hM4
    have hR4 : Rep M4 n root ps S := Rep.outside hR (Outside.sub hO' ho4
      (fun z hz => by simp at hz ⊢; omega)) (by intro z hz; simp at hz; omega)
    have hE4 := hE3.of_outside ho4 (by intro z hz; simp at hz; omega)
    have e27 : M4 27 = p0 + (encList Enc.encode (ts.take j)).length := by
      rw [ho4 27 (by simp), h27']
    have e15 : M4 15 = M3 15 := ho4 15 (by simp)
    have key : (b ∧ ∀ t ∈ ts.take (j + 1), Good n a t → imgT ms sig t ∈ S) ↔
        ((b ∧ ∀ t ∈ ts.take j, Good n a t → imgT ms sig t ∈ S) ∧
          (Good n a ts[j] → imgT ms sig ts[j] ∈ S)) := by
      rw [all_take_succ ts j hj (fun t => Good n a t → imgT ms sig t ∈ S)]
      exact ⟨fun ⟨hb, h1, h2⟩ => ⟨⟨hb, h1⟩, h2⟩, fun ⟨⟨hb, h1⟩, h2⟩ => ⟨hb, h1, h2⟩⟩
    by_cases hg : Good n a ts[j]
    · rw [if_pos hg] at e33
      refine (ifz_ne (by rw [e33]; decide) (runsTo_qryOp ms hE4 hR4 e27 (by omega)
        (Blk.outside htup ho4 (by intro z hz; simp at hz; omega)) hg.2)
        wf_nil).weaken (fun m hm => ?_)
      obtain ⟨ho, e15m⟩ := hm
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hfin m (Outside.sub (ho4.mono (by simp)) ho
        (fun z hz => by simp at hz ⊢; omega))
      refine ⟨⟨h1, ?_⟩, h2, h3, h4, h5, h6⟩
      rw [e15m, e15, e15']
      simp only [key]
      by_cases hin : imgT ms sig ts[j] ∈ S <;>
        by_cases hall : b ∧ ∀ t ∈ ts.take j, Good n a t → imgT ms sig t ∈ S <;>
        simp [hin, hall, hg]
    · rw [if_neg hg] at e33
      refine (ifz_eq (T := 0) e33 (runsTo_nil (fun m hm => ?_)) (wf_qryOp ms)).mono (by omega)
      subst hm
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hfin _ (ho4.mono (by simp))
      refine ⟨⟨h1, ?_⟩, h2, h3, h4, h5, h6⟩
      rw [e15, e15']
      simp only [key]
      by_cases hall : b ∧ ∀ t ∈ ts.take j, Good n a t → imgT ms sig t ∈ S <;>
        simp [hall, hg]
  · rintro m ⟨⟨hO', e15'⟩, -⟩
    refine ⟨hO', ?_⟩
    rw [e15', List.take_length]

/-! ## One pair of relations -/

/-- The head of a pair: register `21` gets `2a`, the flag is cleared if the arities differ, and
registers `22`–`25` get the bounds of the two tuple lists.  The relation of `X` is at the
pointer `16`, that of `X'` at the pointer `18`; each is laid out as `[len, 1, a, |ts|, ts…]`. -/
def pairHead : Program :=
  seq (addTo 2 16 1) (seq (addTo 2 2 1) (seq (loadTo 3 2) (seq (addTo 21 3 3)
    (seq (addTo 2 18 1) (seq (addTo 2 2 1) (seq (loadTo 4 2) (seq (subTo 5 3 4)
    (seq (subTo 6 4 3) (seq (addTo 5 5 6) (seq (ifz 5 (assign 15 0) [])
    (seq (addTo 22 16 1) (seq (addTo 22 22 1) (seq (addTo 22 22 1) (seq (loadTo 2 22)
    (seq (addTo 22 22 1) (seq (addTo 23 22 2)
    (seq (addTo 24 18 1) (seq (addTo 24 24 1) (seq (addTo 24 24 1) (seq (loadTo 2 24)
    (seq (addTo 24 24 1) (addTo 25 24 2))))))))))))))))))))))

theorem wf_pairHead : Wf pairHead := by
  unfold pairHead
  repeat (first | apply wf_seq | apply wf_ifz | apply Layout.wf_addTo | apply Layout.wf_subTo |
    apply Layout.wf_loadTo | apply Layout.wf_assign | exact wf_nil)

theorem runsTo_pairHead {M : Mem} {P P' a a' l l' : ℕ} (h1 : M 1 = 1) (h16 : M 16 = P)
    (h18 : M 18 = P') (hP : 64 ≤ P) (hP' : 64 ≤ P') (ha : M (P + 2) = a) (ha' : M (P' + 2) = a')
    (hl : M (P + 3) = l) (hl' : M (P' + 3) = l') :
    RunsTo pairHead (fun m => m = M)
      (fun m => Outside [2, 3, 4, 5, 6, 15, 21, 22, 23, 24, 25] M m ∧ m 21 = a + a ∧
        m 22 = P + 4 ∧ m 23 = P + 4 + l ∧ m 24 = P' + 4 ∧ m 25 = P' + 4 + l' ∧
        m 15 = if a = a' then M 15 else 0) 25 := by
  refine RunsTo.mono (T := 1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (3 +
    (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + 1)))))))))))))))))))))) ?_
    (by omega)
  refine add_seq (add_seq (load_seq (add_seq (add_seq (add_seq (load_seq (sub_seq (sub_seq
    (add_seq ?_)))))))))
  refine at_mem (fun M' => Outside [2, 3, 4, 5, 6, 21] M M' ∧ M' 21 = a + a ∧
      M' 5 = (a - a') + (a' - a))
    ⟨by outside_tac (Outside.refl [2, 3, 4, 5, 6, 21] M), ?_, ?_⟩ (fun M' hM' => ?_)
  · simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, h1, h16, ha]
  · simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, h1, h16, h18, ha, ha']
  obtain ⟨ho, e21, e5⟩ := hM'
  have hmid : RunsTo (ifz 5 (assign 15 0) []) (fun m => m = M')
      (fun m => Outside [2, 3, 4, 5, 6, 15, 21] M m ∧ m 21 = a + a ∧
        m 15 = if a = a' then M 15 else 0) 3 := by
    by_cases haa : a = a'
    · refine (ifz_eq (by rw [e5]; omega) (runsTo_nil (fun m hm => ?_))
        (Layout.wf_assign _ _)).mono (by omega)
      subst hm
      exact ⟨ho.mono (by simp), e21, by rw [if_pos haa, ho 15 (by simp)]⟩
    · refine ifz_ne (by rw [e5]; omega) (assign_last ⟨(ho.mono (by simp)).upd (by simp) _,
        by rw [Mem.update_of_ne _ _ (by decide), e21], by rw [Mem.update_self, if_neg haa]⟩) wf_nil
  refine block_seq hmid (fun M'' hM'' => ?_)
  obtain ⟨ho'', e21'', e15''⟩ := hM''
  have f1 : M'' 1 = 1 := by rw [ho'' 1 (by simp), h1]
  have f16 : M'' 16 = P := by rw [ho'' 16 (by simp), h16]
  have f18 : M'' 18 = P' := by rw [ho'' 18 (by simp), h18]
  have fl : M'' (P + 3) = l := by rw [ho'' _ (by simp; omega), hl]
  have fl' : M'' (P' + 3) = l' := by rw [ho'' _ (by simp; omega), hl']
  refine add_seq (add_seq (add_seq (load_seq (add_seq (add_seq (add_seq (add_seq (add_seq
    (load_seq (add_seq (add_last ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)))))))))))
  · have := ho''.mono (S' := [2, 3, 4, 5, 6, 15, 21, 22, 23, 24, 25]) (by simp)
    outside_tac this
  all_goals simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, f1, f16, f18, fl,
    fl', e21'', e15'']
  all_goals omega

/-- A phase: a fresh trie at the pointer `14`; the tuples of the first list (registers
`rs1`, `re1`) are stored in it (mapped if `ms1`), and the tuples of the second list (registers
`rs2`, `re2`) are looked up (mapped if `ms2`). -/
def phase (ms1 ms2 : Bool) (rs1 re1 rs2 re2 : ℕ) : Program :=
  seq (copyTo 26 14) (seq (addTo 14 14 13) (seq (copyTo 27 rs1) (seq (copyTo 28 re1)
    (seq (tupLoop (insOp ms1)) (seq (copyTo 27 rs2) (seq (copyTo 28 re2)
      (tupLoop (qryOp ms2))))))))

theorem wf_phase (ms1 ms2 : Bool) (rs1 re1 rs2 re2 : ℕ) : Wf (phase ms1 ms2 rs1 re1 rs2 re2) :=
  wf_seq (Layout.wf_copyTo _ _) (wf_seq (Layout.wf_addTo _ _ _) (wf_seq (Layout.wf_copyTo _ _)
    (wf_seq (Layout.wf_copyTo _ _) (wf_seq (wf_tupLoop (wf_insOp ms1))
      (wf_seq (Layout.wf_copyTo _ _) (wf_seq (Layout.wf_copyTo _ _)
        (wf_tupLoop (wf_qryOp ms2))))))))

/-- The registers a phase writes. -/
notation "Wph" => [2, 3, 4, 14, 15, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37]

theorem next_single (n root : ℕ) : next n root [[]] = root + width n := by
  simp [next, addr]

theorem Base.env {F : ℕ} {inp : List ℕ} {n SIG lo : ℕ} {sig : List ℕ} {m : Mem}
    (hB : Base F inp n SIG lo sig m) {root : ℕ} (hroot : lo ≤ root) (h26 : m 26 = root) :
    Env n SIG root sig m :=
  ⟨hB.one, hB.n2, hB.sigr, hB.w, hB.hSIG, hB.sigv, by have := hB.sigin; omega, hB.siglt, h26,
    by have := hB.hF; have := hB.hlo; omega⟩

theorem runsTo_phase (ms1 ms2 : Bool) {rs1 re1 rs2 re2 : ℕ}
    (hrs : 22 ≤ rs1 ∧ rs1 ≤ 25 ∧ 22 ≤ re1 ∧ re1 ≤ 25 ∧ 22 ≤ rs2 ∧ rs2 ≤ 25 ∧ 22 ≤ re2 ∧
      re2 ≤ 25)
    {M : Mem} {F : ℕ} {inp : List ℕ} {n SIG lo a p1 p2 : ℕ} {sig : List ℕ}
    {ts1 ts2 : List (List ℕ)} {b : Prop} [Decidable b] (hB : Base F inp n SIG lo sig M)
    (h21 : M 21 = a + a)
    (h1s : M rs1 = p1) (h1e : M re1 = p1 + (encList Enc.encode ts1).length)
    (hb1 : Blk M p1 (encList Enc.encode ts1)) (hp1 : 64 ≤ p1)
    (he1 : p1 + (encList Enc.encode ts1).length ≤ lo)
    (h2s : M rs2 = p2) (h2e : M re2 = p2 + (encList Enc.encode ts2).length)
    (hb2 : Blk M p2 (encList Enc.encode ts2)) (hp2 : 64 ≤ p2)
    (he2 : p2 + (encList Enc.encode ts2).length ≤ lo) (h15 : M 15 = if b then 1 else 0) :
    RunsTo (phase ms1 ms2 rs1 re1 rs2 re2) (fun m => m = M)
      (fun m => Base F inp n SIG lo sig m ∧ OutLo lo Wph M m ∧
        m 15 = if (b ∧ ∀ t ∈ ts2, Good n a t →
          ∃ t1 ∈ ts1, Good n a t1 ∧ imgT ms1 sig t1 = imgT ms2 sig t) then 1 else 0)
      (72 * ((encList Enc.encode ts1).length + (encList Enc.encode ts2).length) + 10) := by
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8⟩ := hrs
  have hlo := hB.hlo
  have hF := hB.hF
  have hAL_lo : lo ≤ M 14 := hB.alo
  refine RunsTo.mono (T := 1 + (1 + (1 + (1 + ((72 * (encList Enc.encode ts1).length + 2) +
    (1 + (1 + (72 * (encList Enc.encode ts2).length + 2)))))))) ?_ (by omega)
  refine copy_seq (add_seq (copy_seq (copy_seq ?_)))
  refine at_mem (fun M' => Outside [14, 26, 27, 28] M M' ∧ M' 26 = M 14 ∧
      M' 14 = M 14 + width n ∧ M' 27 = p1 ∧ M' 28 = p1 + (encList Enc.encode ts1).length)
    ⟨by outside_tac (Outside.refl [14, 26, 27, 28] M), ?_, ?_, ?_, ?_⟩ (fun M' hM' => ?_)
  · simp (disch := omega) only [Mem.update_self, Mem.update_of_ne]
  · simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, hB.w]
  · simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, h1s]
  · simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, h1e]
  obtain ⟨ho, e26, e14, e27, e28⟩ := hM'
  have hBM' : Base F inp n SIG lo sig M' := by
    refine hB.of_outLo (OutLo.of_outside ho) (by intro z hz; simp at hz; omega)
      (by rw [e14]; omega) (fun z hz => ?_)
    rw [e14] at hz
    rw [ho z (by simp; omega)]; exact hB.fresh z (by omega)
  have hEnv := hBM'.env hAL_lo e26
  have hRep : Rep M' n (M 14) [[]] [] := rep_new (fun z hz => by
    rw [ho z (by simp; omega)]; exact hB.fresh z hz)
  have e21 : M' 21 = a + a := by rw [ho 21 (by simp), h21]
  have hb1' : Blk M' p1 (encList Enc.encode ts1) :=
    Blk.outside hb1 ho (by intro z hz; simp at hz; omega)
  refine block_seq (runsTo_insLoop ms1 hEnv hRep (by rw [e14, next_single])
    (fun z hz => hBM'.fresh z hz) e27 e28 e21 hp1 hb1' (by omega)) (fun M3 hM3 => ?_)
  obtain ⟨ps', S', hR3, hS3, e14', hfr3, hO3⟩ := hM3
  refine copy_seq (copy_seq ?_)
  have f : ∀ r, r < M 14 → r ∉ Wti → r ∉ [14, 26, 27, 28] → M3 r = M r := fun r h1 h2 h3 => by
    rw [hO3 r h1 h2, ho r h3]
  refine at_mem (fun M4 => OutLo (M 14) (Wti ++ [26, 28]) M M4 ∧ OutLo (M 14) (Wti ++ [28]) M' M4 ∧ M4 27 = p2 ∧
      M4 28 = p2 + (encList Enc.encode ts2).length ∧ Rep M4 n (M 14) ps' S' ∧ M4 14 = next n (M 14) ps' ∧
      (∀ z, M4 14 ≤ z → M4 z = 0) ∧ M4 26 = M 14 ∧ M4 21 = a + a ∧ M4 15 = M 15)
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ (fun M4 hM4 => ?_)
  · refine ((((OutLo.of_outside ho).mono (fun z hz => by simp at hz ⊢; omega)).trans hO3
      (fun z hz => by simp at hz ⊢; omega)).upd (Or.inl (by simp)) _).upd (Or.inl (by simp)) _
  · exact ((hO3.mono (fun z hz => by simp at hz ⊢; omega)).upd (Or.inl (by simp)) _).upd
      (Or.inl (by simp)) _
  · simp (disch := omega) only [Mem.update_self, Mem.update_of_ne]
    rw [f rs2 (by omega) (by simp; omega) (by simp; omega), h2s]
  · simp (disch := omega) only [Mem.update_self, Mem.update_of_ne]
    rw [f re2 (by omega) (by simp; omega) (by simp; omega), h2e]
  · exact (hR3.update_out (Or.inl (by omega))).update_out (Or.inl (by omega))
  · rw [Mem.update_of_ne _ _ (by decide), Mem.update_of_ne _ _ (by decide), e14']
  · intro z hz
    rw [Mem.update_of_ne _ _ (by decide), Mem.update_of_ne _ _ (by decide)] at hz
    have : M 14 ≤ M3 14 := by rw [e14']; unfold next addr; omega
    rw [Mem.update_of_ne _ _ (by omega), Mem.update_of_ne _ _ (by omega)]
    exact hfr3 z hz
  · rw [Mem.update_of_ne _ _ (by decide), Mem.update_of_ne _ _ (by decide),
      hO3 26 (by omega) (by simp), e26]
  · rw [Mem.update_of_ne _ _ (by decide), Mem.update_of_ne _ _ (by decide),
      hO3 21 (by omega) (by simp), e21]
  · rw [Mem.update_of_ne _ _ (by decide), Mem.update_of_ne _ _ (by decide),
      hO3 15 (by omega) (by simp), ho 15 (by simp)]
  obtain ⟨hO4, hO4', e27', e28', hR4, e14'', hfr4, e26', e21', e15'⟩ := hM4
  have hEnv4 : Env n SIG (M 14) sig M4 :=
    hEnv.of_outLo' hO4' (by intro z hz; simp at hz; omega) e26'
  have hb2' : Blk M4 p2 (encList Enc.encode ts2) :=
    Blk.congr hb2 (fun z hz1 hz2 => hO4 z (by omega) (by simp; omega))
  refine (runsTo_qryLoop ms2 (b := b) hEnv4 hR4 e27' e28' e21' hp2 hb2' (by omega)
    (by rw [e15', h15])).weaken (fun m hm => ?_)
  obtain ⟨hom, e15m⟩ := hm
  have hOm : OutLo lo Wph M m := by
    intro z hz hzW
    rw [hom z (fun h => hzW (by simp at h ⊢; omega)), hO4 z (by omega) (fun h => hzW (by
      simp at h ⊢; omega))]
  have e14m : m 14 = next n (M 14) ps' := by rw [hom 14 (by simp), e14'']
  have hge : M 14 ≤ m 14 := by rw [e14m]; unfold next addr; omega
  refine ⟨hB.of_outLo hOm (by intro z hz; simp at hz; omega) (by omega) (fun z hz => ?_), hOm, ?_⟩
  · rw [hom z (by simp; omega)]; exact hfr4 z (by rw [← hom 14 (by simp)]; exact hz)
  · rw [e15m]
    congr 1
    simp only [hS3, List.not_mem_nil, false_or]

/-- The layout of one relation `(a, ts)`, framed: `[len, 1, a, |ts|, ts…]`. -/
theorem elem_layout {M : Mem} {P a : ℕ} {ts : List (List ℕ)}
    (h : Blk M P (RAM.frame (Enc.encode (a, ts)))) :
    M (P + 2) = a ∧ M (P + 3) = (encList Enc.encode ts).length ∧
      Blk M (P + 4) (encList Enc.encode ts) ∧
      (Enc.encode (a, ts)).length = 3 + (encList Enc.encode ts).length := by
  rw [Blk.frame_iff, Blk.encode_pair] at h
  obtain ⟨-, -, ha, hl, hts⟩ := h
  have e1 : (Enc.encode a).length = 1 := rfl
  rw [e1] at hl hts
  rw [Blk.encode_nat] at ha
  refine ⟨ha, hl, hts, ?_⟩
  change (RAM.frame (Enc.encode a) ++ RAM.frame (Enc.encode ts)).length = _
  simp [RAM.frame, e1]
  have : (Enc.encode ts).length = (encList Enc.encode ts).length := rfl
  omega

/-- The test for one pair of relations: equal arities, and each listed tuple of `[0,n)^a` on
either side has its partner on the other side (`t ↦ t^σ` from `X` to `X'`). -/
def PairOK (sig : List ℕ) (n : ℕ) (e e' : ℕ × List (List ℕ)) : Prop :=
  e.1 = e'.1 ∧
    (∀ t ∈ e.2, Good n e.1 t → ∃ t1 ∈ e'.2, Good n e.1 t1 ∧ imgT false sig t1 = imgT true sig t) ∧
    (∀ t ∈ e'.2, Good n e.1 t → ∃ t1 ∈ e.2, Good n e.1 t1 ∧ imgT true sig t1 = imgT false sig t)

instance (sig : List ℕ) (n : ℕ) (e e' : ℕ × List (List ℕ)) : Decidable (PairOK sig n e e') := by
  unfold PairOK; infer_instance

/-- One pair: the head, the two phases, and the step of the pointer `18`. -/
def pairB : Program :=
  seq pairHead (seq (phase false true 24 25 22 23) (seq (phase true false 22 23 24 25)
    (seq (loadTo 2 18) (seq (addTo 18 18 2) (addTo 18 18 1)))))

theorem wf_pairB : Wf pairB :=
  wf_seq wf_pairHead (wf_seq (wf_phase _ _ _ _ _ _) (wf_seq (wf_phase _ _ _ _ _ _)
    (wf_seq (Layout.wf_loadTo _ _) (wf_seq (Layout.wf_addTo _ _ _) (Layout.wf_addTo _ _ _)))))

/-- The registers a pair writes. -/
notation "Wpr" => [2, 3, 4, 5, 6, 14, 15, 18, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32,
  33, 34, 35, 36, 37]

theorem runsTo_pairB {M : Mem} {F : ℕ} {inp : List ℕ} {n SIG lo P P' : ℕ} {sig : List ℕ}
    {e e' : ℕ × List (List ℕ)} {b : Prop} [Decidable b] (hB : Base F inp n SIG lo sig M)
    (h16 : M 16 = P) (h18 : M 18 = P') (hP : 64 ≤ P) (hP' : 64 ≤ P')
    (hb : Blk M P (RAM.frame (Enc.encode e))) (hb' : Blk M P' (RAM.frame (Enc.encode e')))
    (hin : P + 1 + (Enc.encode e).length ≤ lo) (hin' : P' + 1 + (Enc.encode e').length ≤ lo)
    (h15 : M 15 = if b then 1 else 0) :
    RunsTo pairB (fun m => m = M)
      (fun m => Base F inp n SIG lo sig m ∧ OutLo lo Wpr M m ∧
        m 18 = P' + 1 + (Enc.encode e').length ∧
        m 15 = if (b ∧ PairOK sig n e e') then 1 else 0)
      (144 * ((Enc.encode e).length + (Enc.encode e').length) + 48) := by
  obtain ⟨a, ts⟩ := e
  obtain ⟨a', ts'⟩ := e'
  obtain ⟨ha, hl, hts, hlen⟩ := elem_layout hb
  obtain ⟨ha', hl', hts', hlen'⟩ := elem_layout hb'
  have hlo : 64 ≤ lo := by have := hB.hF; have := hB.hlo; omega
  refine RunsTo.mono (T := 25 + ((72 * ((encList Enc.encode ts').length +
    (encList Enc.encode ts).length) + 10) + ((72 * ((encList Enc.encode ts).length +
    (encList Enc.encode ts').length) + 10) + (1 + (1 + 1))))) ?_ (by rw [hlen, hlen']; omega)
  refine block_seq (runsTo_pairHead hB.one h16 h18 hP hP' ha ha' hl hl') (fun M1 hM1 => ?_)
  obtain ⟨ho1, e21, e22, e23, e24, e25, e15⟩ := hM1
  have hB1 : Base F inp n SIG lo sig M1 := by
    refine hB.of_outLo (OutLo.of_outside ho1) (by intro z hz; simp at hz; omega)
      (by rw [ho1 14 (by simp)]; exact hB.alo) (fun z hz => ?_)
    rw [ho1 14 (by simp)] at hz
    rw [ho1 z (by simp; have := hB.alo; omega)]; exact hB.fresh z hz
  have hts1 : Blk M1 (P + 4) (encList Enc.encode ts) :=
    Blk.outside hts ho1 (by intro z hz; simp at hz; omega)
  have hts1' : Blk M1 (P' + 4) (encList Enc.encode ts') :=
    Blk.outside hts' ho1 (by intro z hz; simp at hz; omega)
  refine block_seq (runsTo_phase false true (by omega) (a := a) (b := b ∧ a = a') hB1 e21 e24 e25
    hts1' (by omega) (by omega) e22 e23 hts1 (by omega) (by omega)
    (by rw [e15, h15]; by_cases hb0 : b <;> by_cases haa : a = a' <;> simp [hb0, haa]))
    (fun M2 hM2 => ?_)
  obtain ⟨hB2, hO2, e15'⟩ := hM2
  have f : ∀ r, r < 64 → r ∉ Wph → M2 r = M1 r := fun r hr hW => hO2 r (by omega) hW
  have hts2 : Blk M2 (P + 4) (encList Enc.encode ts) :=
    Blk.congr hts1 (fun z hz1 hz2 => hO2 z (by omega) (by simp; omega))
  have hts2' : Blk M2 (P' + 4) (encList Enc.encode ts') :=
    Blk.congr hts1' (fun z hz1 hz2 => hO2 z (by omega) (by simp; omega))
  refine block_seq (runsTo_phase true false (by omega) (a := a) hB2
    (by rw [f 21 (by omega) (by simp), e21]) (by rw [f 22 (by omega) (by simp), e22])
    (by rw [f 23 (by omega) (by simp), e23]) hts2 (by omega) (by omega)
    (by rw [f 24 (by omega) (by simp), e24]) (by rw [f 25 (by omega) (by simp), e25]) hts2'
    (by omega) (by omega) e15') (fun M3 hM3 => ?_)
  obtain ⟨hB3, hO3, e15''⟩ := hM3
  have e18 : M3 18 = P' := by
    rw [hO3 18 (by omega) (by simp), f 18 (by omega) (by simp), ho1 18 (by simp), h18]
  have e1 : M3 1 = 1 := hB3.one
  have eP' : M3 P' = (Enc.encode (a', ts')).length := by
    rw [hO3 P' (by omega) (by simp; omega), hO2 P' (by omega) (by simp; omega),
      ho1 P' (by simp; omega)]
    exact (Blk.frame_iff.1 hb').1
  refine load_seq (add_seq (add_last ⟨?_, ?_, ?_, ?_⟩))
  · refine ((hB3.upd (by omega) (by decide) (by decide) (by decide) (by decide) (by decide)
      _).upd (by omega) (by decide) (by decide) (by decide) (by decide) (by decide) _).upd
      (by omega) (by decide) (by decide) (by decide) (by decide) (by decide) _
  · have hO : OutLo lo Wpr M M3 :=
      (((OutLo.of_outside ho1).mono (fun z hz => by simp at hz ⊢; omega)).trans hO2
        (fun z hz => by simp at hz ⊢; omega)).trans hO3 (fun z hz => by simp at hz ⊢; omega)
    exact ((hO.upd (Or.inl (by simp)) _).upd (Or.inl (by simp)) _).upd (Or.inl (by simp)) _
  · simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, e18, e1, eP']
    omega
  · simp (disch := omega) only [Mem.update_self, Mem.update_of_ne]
    rw [e15'']
    unfold PairOK
    simp only
    by_cases hb0 : b <;> by_cases haa : a = a' <;> simp [hb0, haa]

/-! ## The loop over the relations -/

/-- One relation of `X`: if `X'` still has a relation, test the pair; otherwise clear the
flag. -/
def relB : Program := seq (subTo 5 19 18) (ifz 5 pairB (assign 15 0))

/-- The loop over the relations of `X` (pointer `16`, end `17`); the pointer `18` walks the
relations of `X'` alongside (end `19`). -/
def relLoop : Program := framesLoop 16 17 20 38 relB

theorem wf_relLoop : Wf relLoop :=
  wf_framesLoop (wf_seq (Layout.wf_subTo _ _ _) (wf_ifz wf_pairB (Layout.wf_assign _ _)))

/-- The registers the loop over the relations writes. -/
notation "Wrl" => [2, 3, 4, 5, 6, 14, 15, 16, 18, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30,
  31, 32, 33, 34, 35, 36, 37, 38]

/-- The pairs tested so far: the first `j` relations of `X` all have partners in `X'`, and all
pass. -/
def PairsOK (sig : List ℕ) (n : ℕ) (R R' : RawExplRels) (j : ℕ) : Prop :=
  j ≤ R'.length ∧ ∀ i, i < j → ∀ (h1 : i < R.length) (h2 : i < R'.length),
    PairOK sig n R[i] R'[i]

instance (sig : List ℕ) (n : ℕ) (R R' : RawExplRels) (j : ℕ) :
    Decidable (PairsOK sig n R R' j) := by
  unfold PairsOK; infer_instance

theorem pairsOK_succ {sig : List ℕ} {n : ℕ} {R R' : RawExplRels} {j : ℕ} (hj : j < R.length)
    (hj' : j < R'.length) :
    PairsOK sig n R R' (j + 1) ↔ PairsOK sig n R R' j ∧ PairOK sig n R[j] R'[j] := by
  unfold PairsOK
  constructor
  · rintro ⟨-, h⟩
    exact ⟨⟨by omega, fun i hi h1 h2 => h i (by omega) h1 h2⟩, h j (by omega) hj hj'⟩
  · rintro ⟨⟨-, h⟩, hp⟩
    refine ⟨by omega, fun i hi h1 h2 => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · exact h i hi h1 h2
    · exact hp

theorem pairsOK_succ_of_le {sig : List ℕ} {n : ℕ} {R R' : RawExplRels} {j : ℕ}
    (hj' : R'.length ≤ j) : ¬ PairsOK sig n R R' (j + 1) := fun h => by
  have := h.1; omega

theorem runsTo_relLoop {M : Mem} {F : ℕ} {inp : List ℕ} {n SIG lo p0 p0' : ℕ} {sig : List ℕ}
    {R R' : RawExplRels} (hB : Base F inp n SIG lo sig M)
    (h16 : M 16 = p0) (h17 : M 17 = p0 + (encList Enc.encode R).length)
    (hb : Blk M p0 (encList Enc.encode R)) (hp0 : 64 ≤ p0)
    (hin : p0 + (encList Enc.encode R).length ≤ lo)
    (h18 : M 18 = p0') (h19 : M 19 = p0' + (encList Enc.encode R').length)
    (hb' : Blk M p0' (encList Enc.encode R')) (hp0' : 64 ≤ p0')
    (hin' : p0' + (encList Enc.encode R').length ≤ lo) (h15 : M 15 = 1) :
    RunsTo relLoop (fun m => m = M)
      (fun m => Base F inp n SIG lo sig m ∧ OutLo lo Wrl M m ∧
        m 18 = p0' + (encList Enc.encode (R'.take R.length)).length ∧ m 19 = M 19 ∧
        m 15 = if PairsOK sig n R R' R.length then 1 else 0)
      (144 * (encList Enc.encode R').length + 203 * (encList Enc.encode R).length + 2) := by
  have hlo : 64 ≤ lo := by have := hB.hF; have := hB.hlo; omega
  let I : ℕ → Mem → Prop := fun j m => Base F inp n SIG lo sig m ∧ OutLo lo Wrl M m ∧
    m 18 = p0' + (encList Enc.encode (R'.take j)).length ∧ m 19 = M 19 ∧ m 15 = (if PairsOK sig n R R' j then 1 else 0) ∧
    Blk m p0' (encList Enc.encode R')
  have hI0 : I 0 M := ⟨hB, OutLo.refl _ _ _, by rw [h18]; simp [encList], rfl,
    by rw [h15, if_pos ⟨Nat.zero_le _, fun i hi => absurd hi (by omega)⟩], hb'⟩
  have hstab1 : ∀ j m v (r : ℕ), r ∈ Wrl → r ≠ 14 → r ≠ 15 → r ≠ 18 → I j m →
      I j (m.update r v) := by
    intro j m v r hr hr14 hr15 hr18 ⟨hBm, hO, e18, e19, e15, hbm⟩
    have hr64 : r < 64 := by simp at hr; omega
    have hr19 : r ≠ 19 := by simp at hr; omega
    refine ⟨hBm.upd hr64 (by simp at hr; omega) (by simp at hr; omega) (by simp at hr; omega)
      (by simp at hr; omega) hr14 v, hO.upd (Or.inl hr) v, ?_, ?_, ?_, Blk.update hbm
      (Or.inl (by omega))⟩
    · rw [Mem.update_of_ne _ _ (Ne.symm hr18), e18]
    · rw [Mem.update_of_ne _ _ (Ne.symm hr19), e19]
    · rw [Mem.update_of_ne _ _ (Ne.symm hr15), e15]
  refine (runsTo_framesLoop Enc.encode R p0 (rp := 16) (re := 17) (rc := 20) (rt := 38)
      (by decide) ⟨by omega, by omega, by omega⟩
      (wf_seq (Layout.wf_subTo _ _ _) (wf_ifz wf_pairB (Layout.wf_assign _ _))) I
      (fun m => 144 * (m 19 - m 18)) 51 144 ?_ ?_ ?_ M hI0 h16 h17 hB.one hb).weaken ?_
      |>.mono ?_
  · intro j m v h
    exact ⟨hstab1 j m v 16 (by simp) (by decide) (by decide) (by decide) h,
      hstab1 j m v 20 (by simp) (by decide) (by decide) (by decide) h,
      hstab1 j m v 38 (by simp) (by decide) (by decide) (by decide) h⟩
  · intro m v
    refine ⟨?_, ?_, ?_⟩ <;> simp only [Mem.update_of_ne _ _ (by decide : (19:ℕ) ≠ 16),
      Mem.update_of_ne _ _ (by decide : (18:ℕ) ≠ 16), Mem.update_of_ne _ _ (by decide : (19:ℕ) ≠ 20),
      Mem.update_of_ne _ _ (by decide : (18:ℕ) ≠ 20), Mem.update_of_ne _ _ (by decide : (19:ℕ) ≠ 38),
      Mem.update_of_ne _ _ (by decide : (18:ℕ) ≠ 38)]
  · intro j hj M3 hI h16' h17' h1' hblk'
    obtain ⟨hB3, hO3, e18, e19, e15, hb3'⟩ := hI
    have hlt := encList_take_lt Enc.encode R j hj
    have hleE' := encList_take_le Enc.encode R' j
    have hB5 := hB3.upd (r := 5) (by omega) (by decide) (by decide) (by decide) (by decide)
      (by decide) (M3 19 - M3 18)
    have hO5 : OutLo lo Wrl M (M3.update 5 (M3 19 - M3 18)) := hO3.upd (Or.inl (by simp)) _
    by_cases hj' : j < R'.length
    · have hlt' := encList_take_lt Enc.encode R' j hj'
      have hsucc' := encList_take_succ Enc.encode R' j hj'
      refine ⟨1 + ((144 * ((Enc.encode R[j]).length + (Enc.encode R'[j]).length) + 48) + 2),
        sub_seq (ifz_ne (by rw [Mem.update_self, e19, e18, h19]; omega)
          (runsTo_pairB (b := PairsOK sig n R R' j) hB5
            (by rw [Mem.update_of_ne _ _ (by decide), h16'])
            (by rw [Mem.update_of_ne _ _ (by decide), e18]) (by omega) (by omega)
            (Blk.update (Blk.encList_get hblk' j hj) (Or.inl (by omega)))
            (Blk.update (Blk.encList_get hb3' j hj') (Or.inl (by omega)))
            (by omega) (by omega)
            (by rw [Mem.update_of_ne _ _ (by decide), e15]))
          (Layout.wf_assign _ _) |>.weaken (fun m hm => ?_))⟩
      obtain ⟨hBm, hOm, e18m, e15m⟩ := hm
      have f : ∀ r, r < 64 → r ∉ Wpr → r ≠ 5 → m r = M3 r := fun r hr hW h5 => by
        rw [hOm r (by omega) hW, Mem.update_of_ne _ _ h5]
      have e19m : m 19 = M3 19 := f 19 (by omega) (by simp) (by decide)
      refine ⟨⟨hBm, hO5.trans hOm (fun z hz => by simp at hz ⊢; omega), ?_, by rw [e19m, e19],
        ?_, Blk.congr hb3' (fun z hz1 hz2 => by
          rw [hOm z (by omega) (by simp; omega), Mem.update_of_ne _ _ (by omega)])⟩,
        f 16 (by omega) (by simp) (by decide), f 17 (by omega) (by simp) (by decide), hBm.one,
        Blk.congr hblk' (fun z hz1 hz2 => by
          rw [hOm z (by omega) (by simp; omega), Mem.update_of_ne _ _ (by omega)]), ?_⟩
      · rw [e18m, hsucc']; simp only [List.length_append, RAM.frame, List.length_cons]
        omega
      · rw [e15m]
        simp only [pairsOK_succ hj hj']
      · show 144 * (m 19 - m 18) + _ ≤ 144 * (M3 19 - M3 18) + 51 + 144 * _
        rw [e19m, e18m, e18, e19, h19]
        omega
    · have hR' : R'.take j = R' := List.take_of_length_le (by omega)
      have hR'' : R'.take (j + 1) = R' := List.take_of_length_le (by omega)
      have hz5 : (M3.update 5 (M3 19 - M3 18)) 5 = 0 := by
        rw [Mem.update_self, e19, e18, h19, hR']; omega
      refine ⟨1 + (1 + 2), sub_seq (ifz_eq hz5 (assign_last ⟨⟨hB5.upd (by omega) (by decide) (by decide) (by decide)
          (by decide) (by decide) _, hO5.upd (Or.inl (by simp)) _, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_,
          ?_, ?_⟩) wf_pairB)⟩
      · rw [Mem.update_of_ne _ _ (by decide), Mem.update_of_ne _ _ (by decide), e18, hR', hR'']
      · rw [Mem.update_of_ne _ _ (by decide), Mem.update_of_ne _ _ (by decide), e19]
      · rw [Mem.update_self, if_neg (pairsOK_succ_of_le (by omega))]
      · exact Blk.update (Blk.update hb3' (Or.inl (by omega))) (Or.inl (by omega))
      · rw [Mem.update_of_ne _ _ (by decide), Mem.update_of_ne _ _ (by decide)]
      · rw [Mem.update_of_ne _ _ (by decide), Mem.update_of_ne _ _ (by decide)]
      · rw [Mem.update_of_ne _ _ (by decide), Mem.update_of_ne _ _ (by decide), h1']
      · exact Blk.update (Blk.update hblk' (Or.inl (by omega))) (Or.inl (by omega))
      · simp only [Mem.update_of_ne _ _ (by decide : (19:ℕ) ≠ 15),
          Mem.update_of_ne _ _ (by decide : (18:ℕ) ≠ 15),
          Mem.update_of_ne _ _ (by decide : (19:ℕ) ≠ 5),
          Mem.update_of_ne _ _ (by decide : (18:ℕ) ≠ 5)]
        omega
  · rintro m ⟨⟨hBm, hO, e18, e19, e15, -⟩, -⟩
    exact ⟨hBm, hO, e18, e19, e15⟩
  · rw [h19, h18]; omega

/-! ## What the flag means -/

section Semantics

open Equiv (Perm)

theorem relDirOk_iff_good (l : RawPerm) (a : ℕ) (ts ts' : List (List ℕ)) :
    relDirOk ((l, a), (ts, ts')) = true ↔
      ∀ t ∈ ts, Good l.length a t → rawMapTuple (l, t) ∈ ts' := by
  simp only [relDirOk, wftAll_eq_true_iff, tupOk, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_true_eq]
  refine forall_congr' (fun t => forall_congr' (fun _ => ?_))
  rw [good_iff_goodTuple]
  cases goodTuple ((l.length, a), t) <;> simp

/-- The value of `σ` read the way the machine reads it. -/
theorem getD_encPerm {n : ℕ} (σ : Perm (Fin n)) {x : ℕ} (hx : x < n) :
    (encPerm n σ).getD x 0 = (σ ⟨x, hx⟩ : ℕ) := by
  rw [List.getD_eq_getElem _ _ (by simpa using hx)]; simp [encPerm]

theorem rawMapTuple_encPerm {n : ℕ} (σ : Perm (Fin n)) {t : List ℕ} (ht : ∀ x ∈ t, x < n) :
    rawMapTuple (encPerm n σ, t) = imgT true (encPerm n σ) t := by
  simp only [rawMapTuple, imgT, if_true]
  refine List.map_congr_left (fun x hx => ?_)
  rw [rawApply_encPerm n σ (ht x hx), getD_encPerm σ (ht x hx)]

theorem imgT_good {n a : ℕ} (σ : Perm (Fin n)) {t : List ℕ} (ht : Good n a t) :
    Good n a (imgT true (encPerm n σ) t) := by
  refine ⟨by rw [imgT_length]; exact ht.1, fun y hy => ?_⟩
  simp only [imgT, if_true, List.mem_map] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  rw [getD_encPerm σ (ht.2 x hx)]; exact Fin.isLt _

theorem imgT_inv {n : ℕ} (σ : Perm (Fin n)) {t : List ℕ} (ht : ∀ x ∈ t, x < n) :
    imgT true (encPerm n σ) (imgT true (encPerm n σ⁻¹) t) = t := by
  simp only [imgT, if_true, List.map_map]
  conv_rhs => rw [← List.map_id t]
  refine List.map_congr_left (fun x hx => ?_)
  simp only [Function.comp]
  rw [getD_encPerm σ⁻¹ (ht x hx), getD_encPerm σ (Fin.isLt _)]
  simp

theorem imgT_inv' {n : ℕ} (σ : Perm (Fin n)) {t : List ℕ} (ht : ∀ x ∈ t, x < n) :
    imgT true (encPerm n σ⁻¹) (imgT true (encPerm n σ) t) = t := by
  have := imgT_inv σ⁻¹ ht
  rwa [inv_inv] at this

/-- **The pair test is the paper's test.** -/
theorem pairOk_iff_pairOK {n : ℕ} (σ : Perm (Fin n)) (e e' : ℕ × List (List ℕ)) :
    pairOk ((encPerm n σ, rawInv (encPerm n σ)), (e, e')) = true ↔
      PairOK (encPerm n σ) n e e' := by
  obtain ⟨a, ts⟩ := e
  obtain ⟨a', ts'⟩ := e'
  simp only [pairOk, Bool.and_eq_true, decide_eq_true_eq, relDirOk_iff_good, rawInv_encPerm,
    length_encPerm, PairOK]
  rw [and_assoc]
  refine and_congr Iff.rfl (and_congr ?_ ?_)
  · refine forall_congr' (fun t => forall_congr' (fun _ => forall_congr' (fun hg => ?_)))
    rw [rawMapTuple_encPerm σ hg.2]
    constructor
    · intro h; exact ⟨_, h, imgT_good σ hg, by simp [imgT]⟩
    · rintro ⟨t1, h1, -, he⟩
      have : t1 = imgT true (encPerm n σ) t := by simpa [imgT] using he
      rw [← this]; exact h1
  · refine forall_congr' (fun t => forall_congr' (fun _ => forall_congr' (fun hg => ?_)))
    rw [rawMapTuple_encPerm σ⁻¹ hg.2]
    constructor
    · intro h
      exact ⟨_, h, imgT_good σ⁻¹ hg, by rw [imgT_inv σ hg.2]; simp [imgT]⟩
    · rintro ⟨t1, h1, hg1, he⟩
      have he' : imgT true (encPerm n σ) t1 = t := by simpa [imgT] using he
      rw [← he', imgT_inv' σ hg1.2]; exact h1

/-- **The flag is the test.** -/
theorem rawExplIsoTest_iff_pairsOK {n : ℕ} (σ : Perm (Fin n)) (R R' : RawExplRels) :
    rawExplIsoTest ((R, R'), encPerm n σ) = true ↔
      R.length = R'.length ∧ PairsOK (encPerm n σ) n R R' R.length := by
  simp only [rawExplIsoTest, Bool.and_eq_true, decide_eq_true_eq, wftAll_eq_true_iff]
  constructor
  · rintro ⟨hl, h⟩
    rw [forall_mem_zip_iff hl] at h
    exact ⟨hl, by omega, fun i hi h1 h2 => (pairOk_iff_pairOK σ _ _).1 (h i h1)⟩
  · rintro ⟨hl, -, h⟩
    refine ⟨hl, ?_⟩
    rw [forall_mem_zip_iff hl]
    intro i hi
    exact (pairOk_iff_pairOK σ _ _).2 (h i hi hi _)

end Semantics

/-! ## The whole program -/

/-- Reading the layout of the input: registers `16`–`19` get the bounds of the two lists of
relations, `11`–`13` the constants of `σ`, `14` the first free address, `15` the flag.  The
input sits at the base in register `1`. -/
def parse : Program :=
  seq (copyTo 10 1) (seq (assign 1 1) (seq (addTo 2 10 1) (seq (loadTo 3 2) (seq (addTo 2 2 1)
    (seq (loadTo 4 2) (seq (addTo 16 2 1) (seq (addTo 17 16 4) (seq (addTo 18 17 1)
    (seq (addTo 19 2 3) (seq (loadTo 11 19) (seq (addTo 12 19 1) (seq (addTo 12 12 1)
    (seq (addTo 13 11 1) (seq (loadTo 5 10) (seq (addTo 14 10 5) (seq (addTo 14 14 1)
    (seq (addTo 14 14 1) (assign 15 1))))))))))))))))))

/-- After the bridge `up`: copy the input from `16` to the far base `2L + 100`, parse it, run
the loop over the relations, compare the numbers of relations, and write the answer. -/
def mainRest : Program :=
  seq (assign 0 16) (seq (copyTo 1 16) (seq (addTo 1 1 1) (seq (assign 2 100) (seq (addTo 1 1 2)
    (seq (copyTo 2 16) (seq (assign 3 1) (seq (addTo 2 2 3) (seq (Arrays.copyBlock 0 1 2 3)
    (seq parse (seq relLoop (seq (subTo 5 19 18) (seq (ifz 5 (assign 15 0) [])
    (seq (assign 0 1) (copyTo 1 15))))))))))))))

/-- **The program of Prop. 2.3.6.** -/
def explIsoProg : Program := seq Bridge.up mainRest

/-- The layout of the input `(R, R')`, `σ` in a block. -/
theorem input_layout {M : Mem} {F : ℕ} {R R' : RawExplRels} {sl : List ℕ}
    (h : Blk M (F + 1) (Enc.encode ((R, R'), sl))) :
    let A := (Enc.encode (R, R')).length
    let B := (encList Enc.encode R).length
    M (F + 1) = A ∧ M (F + 1 + 1) = B ∧ Blk M (F + 1 + 1 + 1) (encList Enc.encode R) ∧
      M (F + 1 + 1 + A) = 2 * sl.length ∧
      Blk M (F + 1 + 1 + 1 + B + 1) (encList Enc.encode R') ∧
      Blk M (F + 1 + 1 + A + 1) (encList Enc.encode sl) ∧
      A = B + (encList Enc.encode R').length + 2 ∧
      (Enc.encode ((R, R'), sl)).length = A + 2 * sl.length + 2 := by
  intro A B
  rw [Blk.encode_pair] at h
  obtain ⟨hA, hRR, hs, hsl⟩ := h
  rw [Blk.encode_pair] at hRR
  obtain ⟨hB, hR, hB', hR'⟩ := hRR
  have e1 : (Enc.encode sl).length = 2 * sl.length := length_encode_nat_list sl
  have eA : A = B + (encList Enc.encode R').length + 2 := by
    show (RAM.frame (Enc.encode R) ++ RAM.frame (Enc.encode R')).length = _
    simp only [List.length_append, RAM.frame, List.length_cons]
    change (encList Enc.encode R).length + 1 + ((encList Enc.encode R').length + 1) = _
    omega
  refine ⟨hA, hB, hR, by rw [hs, e1], ?_, hsl, eA, ?_⟩
  · have : F + 1 + 1 + 1 + (Enc.encode R).length + 1 = F + 1 + 1 + 1 + B + 1 := rfl
    rw [← this]; exact hR'
  · show (RAM.frame (Enc.encode (R, R')) ++ RAM.frame (Enc.encode sl)).length = _
    simp only [List.length_append, RAM.frame, List.length_cons, e1]
    omega

theorem wf_parse : Wf parse := by
  unfold parse
  repeat (first | apply wf_seq | apply Layout.wf_addTo | apply Layout.wf_copyTo |
    apply Layout.wf_loadTo | apply Layout.wf_assign)

theorem runsTo_parse {M2 : Mem} {F L A B N : ℕ} (e21 : M2 1 = F) (hL : M2 F = L)
    (hA : M2 (F + 1) = A) (hB : M2 (F + 1 + 1) = B) (h2n : M2 (F + 1 + 1 + A) = N)
    (hF100 : 100 ≤ F) :
    RunsTo parse (fun m => m = M2) (fun M3 => Outside [1, 2, 3, 4, 5, 10, 11, 12, 13,
      14, 15, 16, 17, 18, 19] M2 M3 ∧ M3 1 = 1 ∧ M3 11 = N ∧
      M3 12 = F + 1 + 1 + A + 1 + 1 ∧ M3 13 = N + 1 ∧ M3 14 = F + L + 1 + 1 ∧
      M3 15 = 1 ∧ M3 16 = F + 1 + 1 + 1 ∧ M3 17 = F + 1 + 1 + 1 + B ∧
      M3 18 = F + 1 + 1 + 1 + B + 1 ∧ M3 19 = F + 1 + 1 + A) 19 := by
  refine RunsTo.mono (T := 1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1))))))))))))))))))) ?_ (by omega)
  refine copy_seq (assign_seq (add_seq (load_seq (add_seq (load_seq ?_)))))
  refine at_mem (fun M => Outside [1, 2, 3, 4, 10] M2 M ∧ M 1 = 1 ∧ M 10 = F ∧
      M 2 = F + 1 + 1 ∧ M 3 = A ∧ M 4 = B) ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ (fun M hM => ?_)
  · outside_tac (Outside.refl [1, 2, 3, 4, 10] M2)
  all_goals try (simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, e21, hL, hA, hB])
  obtain ⟨ho, f1, f10, f2, f3, f4⟩ := hM
  have g : M (F + 1 + 1 + A) = N := by rw [ho _ (by simp; omega), h2n]
  have gL : M F = L := by rw [ho _ (by simp; omega), hL]
  refine add_seq (add_seq (add_seq (add_seq (load_seq (add_seq (add_seq (add_seq ?_)))))))
  refine at_mem (fun M' => Outside [1, 2, 3, 4, 10, 11, 12, 13, 16, 17, 18, 19] M2 M' ∧
      M' 1 = 1 ∧ M' 10 = F ∧ M' 11 = N ∧ M' 12 = F + 1 + 1 + A + 1 + 1 ∧ M' 13 = N + 1 ∧
      M' 16 = F + 1 + 1 + 1 ∧ M' 17 = F + 1 + 1 + 1 + B ∧ M' 18 = F + 1 + 1 + 1 + B + 1 ∧
      M' 19 = F + 1 + 1 + A ∧ M' F = L)
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ (fun M' hM' => ?_)
  · have ho' := ho.mono (S' := [1, 2, 3, 4, 10, 11, 12, 13, 16, 17, 18, 19]) (by simp)
    outside_tac ho'
  all_goals try (simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, f1, f10, f2, f3,
    f4, g, gL])
  all_goals try omega
  obtain ⟨ho', g1, g10, g11, g12, g13, g16, g17, g18, g19, gF⟩ := hM'
  refine load_seq (add_seq (add_seq (add_seq (assign_last ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_⟩))))
  · have ho'' := ho'.mono (S' := [1, 2, 3, 4, 5, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19])
      (by simp)
    outside_tac ho''
  all_goals simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, g1, g10, g11, g12,
    g13, g16, g17, g18, g19, gF]
  all_goals omega

theorem runsTo_mainRest {n : ℕ} (R R' : RawExplRels) (σ : Equiv.Perm (Fin n)) :
    RunsTo mainRest (fun m => m = initMemAt 16 (Enc.encode ((R, R'), encPerm n σ)))
      (fun m => OutputAt m (Enc.encode (rawExplIsoTest ((R, R'), encPerm n σ))))
      (400 * (Enc.encode ((R, R'), encPerm n σ)).length + 100) := by
  have e16 : initMemAt 16 (Enc.encode ((R, R'), encPerm n σ)) 16 =
      (Enc.encode ((R, R'), encPerm n σ)).length := by
    rw [initMemAt_of_ge _ (le_refl _)]; simp [initMem]
  have eM0 : ∀ j (hj : j < (Enc.encode ((R, R'), encPerm n σ)).length + 1),
      initMemAt 16 (Enc.encode ((R, R'), encPerm n σ)) (16 + j) =
        ((Enc.encode ((R, R'), encPerm n σ)).length :: Enc.encode ((R, R'), encPerm n σ))[j]'(by
          simp only [List.length_cons]; omega) := by
    intro j hj
    rw [initMemAt_of_ge _ (by omega)]
    rcases j with _ | j
    · simp [initMem]
    · simp only [initMem, Nat.add_sub_cancel_left, Nat.add_one_ne_zero, if_false,
        Nat.add_sub_cancel, List.getElem_cons_succ]
      rw [List.getD_eq_getElem _ _ (by omega)]
  set l := Enc.encode ((R, R'), encPerm n σ) with hl
  set L := l.length with hLdef
  set sl := encPerm n σ with hsl
  set M0 := initMemAt 16 l with hM0
  have eM0z : ∀ z, 16 + L + 1 ≤ z → M0 z = 0 := by
    intro z hz
    rw [hM0, initMemAt_of_ge l (by omega)]
    simp only [initMem, if_neg (by omega : ¬ z - 16 = 0)]
    exact List.getD_eq_default _ _ (by omega)
  refine RunsTo.mono (T := 1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + ((7 * (L + 1) + 5) + (19 + ((144 * L + 203 * L + 2) + (1 + (3 + (1 + (1))))))))))))))) ?_ (by omega)
  refine assign_seq (copy_seq (add_seq (assign_seq (add_seq (copy_seq (assign_seq
    (add_seq ?_)))))))
  refine at_mem (fun M1 => M1 0 = 16 ∧ M1 1 = L + L + 100 ∧ M1 2 = L + 1 ∧
      ∀ z, 4 ≤ z → M1 z = M0 z) ⟨?_, ?_, ?_, ?_⟩ (fun M1 hM1 => ?_)
  · simp (disch := omega) only [Mem.update_self, Mem.update_of_ne]
  · simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, e16]
  · simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, e16]
  · intro z hz; simp (disch := omega) only [Mem.update_self, Mem.update_of_ne]
  obtain ⟨h0, h1, h2, h4⟩ := hM1
  set F := L + L + 100 with hF
  have hF100 : 100 ≤ F := by omega
  refine block_seq (T := 7 * (L + 1) + 5) ((Arrays.runsTo_copyBlock 0 1 2 3 (by omega) (by omega)
    (by omega) M1 (by rw [h0]; omega) (by rw [h1]; omega) (Or.inr (by rw [h0, h2, h1]; omega))).mono
    (by rw [h2])) (fun M2 hM2 => ?_)
  obtain ⟨hc1, hc2⟩ := hM2
  rw [h0, h1, h2] at hc1
  rw [h1, h2] at hc2
  have hblk2 : Blk M2 F (L :: l) := by
    intro j hj
    rw [hc1 j (by simpa using hj), h4 _ (by omega), eM0 j (by simpa using hj)]
  have hfr2 : ∀ z, F + L + 1 ≤ z → M2 z = 0 := by
    intro z hz
    rw [hc2 z (by omega) (by simp; omega), h4 z (by omega), eM0z z (by omega)]
  have e21 : M2 1 = F := by rw [hc2 1 (by omega) (by simp), h1]
  rw [Blk.cons] at hblk2
  obtain ⟨hL, hl2⟩ := hblk2
  obtain ⟨hA, hB, hR, h2n, hR', hsig, eA, eLen⟩ := input_layout (M := M2) (F := F) hl2
  set A := (Enc.encode (R, R')).length with hAdef
  set B := (encList Enc.encode R).length with hBdef
  have hsl_len : sl.length = n := length_encPerm n σ
  have hLA : L = A + 2 * sl.length + 2 := eLen
  set B' := (encList Enc.encode R').length with hB'def
  have hBL : B ≤ L := by omega
  have hB'L : B' ≤ L := by omega
  -- parse
  refine block_seq (runsTo_parse e21 hL hA hB h2n hF100) (fun M3 hM3 => ?_)
  obtain ⟨ho3, e1, e11, e12, e13, e14, e15, e16', e17, e18, e19⟩ := hM3
  have hBase : Base F (L :: l) n (F + 1 + 1 + A + 1 + 1) (F + L + 1 + 1) sl M3 := by
    refine ⟨e1, by rw [e11, hsl_len]; omega, e12, by rw [e13, hsl_len]; unfold width; omega,
      Blk.outside (Blk.cons.2 ⟨hL, hl2⟩) ho3 (by intro z hz; simp at hz; omega), ?_,
      by omega, by omega, by omega, by simp; omega, by rw [e14], ?_, ?_⟩
    · intro x hx
      have hx' : x < sl.length := by omega
      have h := Blk.nat_entry hsig x hx'
      have hlen : (encList Enc.encode (sl.take x)).length = 2 * x := by
        have := length_encode_nat_list (sl.take x)
        change (encList Enc.encode (sl.take x)).length = _ at this
        rw [this, List.length_take]; omega
      rw [hlen] at h
      rw [ho3 _ (by simp; omega), List.getD_eq_getElem _ _ hx']
      rw [← h]; congr 1; omega
    · intro z hz
      rw [e14] at hz
      rw [ho3 z (by simp; omega)]; exact hfr2 z (by omega)
    · intro x hx
      rw [hsl, getD_encPerm σ hx]; exact Fin.isLt _
  have hRb : Blk M3 (F + 1 + 1 + 1) (encList Enc.encode R) :=
    Blk.outside hR ho3 (by intro z hz; simp at hz; omega)
  have hR'b : Blk M3 (F + 1 + 1 + 1 + B + 1) (encList Enc.encode R') :=
    Blk.outside hR' ho3 (by intro z hz; simp at hz; omega)
  refine block_seq (T := 144 * L + 203 * L + 2) ((runsTo_relLoop hBase e16' e17 hRb (by omega)
    (by omega) e18 (by rw [e19]; omega) hR'b (by omega) (by omega) e15).mono (by
      have : 144 * B' ≤ 144 * L := Nat.mul_le_mul_left _ hB'L
      have : 203 * B ≤ 203 * L := Nat.mul_le_mul_left _ hBL
      omega)) (fun M4 hM4 => ?_)
  obtain ⟨-, -, f18, f19, f15⟩ := hM4
  have hiff := rawExplIsoTest_iff_pairsOK σ R R'
  rw [← hsl] at hiff
  refine sub_seq ?_
  have hout : ∀ (M5 : Mem) (b : Bool), M5 15 = (if b then 1 else 0) →
      RunsTo (seq (assign 0 1) (copyTo 1 15)) (fun m => m = M5)
        (fun m => OutputAt m (Enc.encode b)) 2 := by
    intro M5 b h15
    refine assign_seq (copy_last ⟨?_, fun i hi => ?_⟩)
    · rw [Mem.update_of_ne _ _ (by decide), Mem.update_self]; rfl
    · have hi0 : i = 0 := by simpa [Enc.encode] using hi
      subst hi0
      simp only [Mem.update_self, Mem.update_of_ne _ _ (by decide : (15:ℕ) ≠ 0), h15]
      cases b <;> rfl
  by_cases hle : R'.length ≤ R.length
  · have htake : R'.take R.length = R' := List.take_of_length_le hle
    rw [htake] at f18
    refine (block_seq (ifz_eq (T := 0) (by rw [Mem.update_self, f18, f19, e19]; omega)
      (runsTo_nil (post := fun m => m = _) (fun m hm => hm)) (Layout.wf_assign _ _))
      (fun M5 hM5 => hout M5 _ ?_)).mono (by omega)
    rw [hM5, Mem.update_of_ne _ _ (by decide), f15]
    by_cases hp : PairsOK sl n R R' R.length
    · have : rawExplIsoTest ((R, R'), sl) = true := hiff.2 ⟨by have := hp.1; omega, hp⟩
      rw [this, if_pos hp]; rfl
    · have : rawExplIsoTest ((R, R'), sl) = false := by
        cases h : rawExplIsoTest ((R, R'), sl)
        · rfl
        · exact absurd (hiff.1 h).2 hp
      rw [this, if_neg hp]; rfl
  · have hlt := encList_take_lt Enc.encode R' R.length (by omega)
    refine block_seq (ifz_ne (T := 1) (by rw [Mem.update_self, f18, f19, e19]; omega)
      (assign_last (post := fun m => m = _) rfl) wf_nil) (fun M5 hM5 => hout M5 _ ?_)
    rw [hM5, Mem.update_self]
    have : rawExplIsoTest ((R, R'), sl) = false := by
      cases h : rawExplIsoTest ((R, R'), sl)
      · rfl
      · exact absurd (hiff.1 h).1 (by omega)
    rw [this]; rfl

/-- **Prop. 2.3.6, the linear-time claim** (§2.3.1): one program decides `σ ∈ Iso(X, X')`
(the test `rawExplIsoTest`, see `rawExplIsoTest_spec`) within `500 · (size + 1)` steps on every
input. -/
theorem proposition_2_3_6_linear : Proposition_2_3_6_linear_statement := by
  refine ⟨explIsoProg, 500, fun n R R' σ => ?_⟩
  have h := (Bridge.runsTo_up (Enc.encode ((R, R'), encPerm n σ))).seq (runsTo_mainRest R R' σ)
  obtain ⟨k, hk, hhalt, hout⟩ := h.spec _ rfl
  refine ⟨k, ?_, hhalt, hout⟩
  have hsz := length_lt_listSize (Enc.encode ((R, R'), encPerm n σ))
  change _ < Enc.size ((R, R'), encPerm n σ) at hsz
  omega

end ExplLinear

end Algo
