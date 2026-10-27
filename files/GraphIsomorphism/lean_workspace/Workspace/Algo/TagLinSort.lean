/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 4.1.1: the running time of the tagged refinement process.  The sorting routine: the
ordered palette of a list of strings, and the rank of every string in it.
-/
import Workspace.Algo.TagLinBase

/-!
# Sorting strings on the RAM, step by step

§4.1.1 standardizes a coloring `c : V → C` by replacing each color by its rank in "the ordered
set `C`", and appends the ordered list of the colors to the tag.  Colors are strings, ordered
lexicographically.  This file gives a RAM routine `sortProg` that, for `n` strings stored in
memory, computes the sorted list of the distinct strings (as the list `Dl` of the indices of one
representative each) and the rank of every string in it, within
`O(Σ |string| + n²)` steps (`runsTo_sortProg`).

## The algorithm

Insertion sort with longest common prefixes.  The distinct strings found so far are kept in
increasing order `t₀ < t₁ < ⋯ < t_{d-1}`, together with `L_i = lcp(t_i, t_{i+1})`.  A new string
`s` is compared with `t₀, t₁, …` in turn, and `l = lcp(s, t_i)` is carried from one element to
the next: if `t_i < s` and `L_i < l` then `s < t_{i+1}` at once; if `L_i ≥ l` the comparison
with `t_{i+1}` resumes at letter `l` (`Algo.TagLin.scan_lt`, `Algo.TagLin.scan_ge`).  So `l`
never decreases, and the insertion of `s` costs `O(|s| + d)` steps, plus `O(d)` to shift the
arrays.

## Registers

Inputs: `20` the address `SA` of the array of string addresses, `21` the number `n` of
strings.  Register `1` holds `1`, register `14` the allocation pointer `A`.  The routine takes
the region `[A, A + 5n)`: the array `D` of representatives at `A` (register `22`), the array of
doubled `lcp`s at `A + n` (`25`), the representatives `rep` at `A + 2n` (`26`), the positions
`pos` at `A + 3n` (`27`), the ranks at `A + 4n` (`24`).  Register `23` holds `d = |D|`.  The
scan uses `28` (the string number `x`), `29` (a counter), `30`, `31` (address and doubled
length of `s`), `32` (`i`), `33` (`2l`), `34` (the previous `2l`), `35`, `36` (address and
doubled length of `t_i`), `37`, `38` (loop flags), `39` (the insertion position), `10`, `11`
(the two new `lcp`s), `12` (insert or duplicate), `13` (the representative of a duplicate),
and `2`–`9` as scratch.

No axiom, no `sorry`.
-/

namespace Algo

namespace TagLin

open RAM RAM.Exact

/-! ## The programs -/

/-- Register `37` becomes nonzero exactly when `l < |s|`, `l < |t|` and `s[l] = t[l]`
(everything doubled: `31`, `36` hold `2|s|`, `2|t|`, `33` holds `2l`). -/
def flagB : Program :=
  seq (subTo 2 31 33) (ifz 2
    (seq (subTo 4 36 33) (ifz 4
      (seq (addTo 5 30 33) (seq (addTo 5 5 1) (seq (addTo 5 5 1) (seq (loadTo 5 5)
        (seq (addTo 6 35 33) (seq (addTo 6 6 1) (seq (addTo 6 6 1) (seq (loadTo 6 6)
        (seq (subTo 7 5 6) (seq (subTo 8 6 5) (seq (addTo 7 7 8) (subTo 37 1 7))))))))))))
      (assign 37 0)))
    (assign 37 0))

/-- Extend the common prefix while the next letters agree. -/
def extLoop : Program := whileNz 37 (seq (addTo 33 33 1) (seq (addTo 33 33 1) flagB))

/-- Fetch `t_i`: its address into `35`, its doubled length into `36`. -/
def loadT : Program :=
  seq (addTo 2 22 32) (seq (loadTo 2 2) (seq (addTo 2 20 2) (seq (loadTo 35 2) (loadTo 36 35))))

/-- The comparison of `s` with `t_i` at the common prefix: register `9` becomes `0` (equal),
`1` (`s < t_i`) or `2` (`s > t_i`). -/
def cmpB : Program :=
  seq (subTo 2 31 33) (seq (subTo 4 36 33) (ifz 2
    (ifz 4
      (seq (addTo 5 30 33) (seq (addTo 5 5 1) (seq (addTo 5 5 1) (seq (loadTo 5 5)
        (seq (addTo 6 35 33) (seq (addTo 6 6 1) (seq (addTo 6 6 1) (seq (loadTo 6 6)
        (seq (subTo 7 6 5) (ifz 7 (assign 9 1) (assign 9 2)))))))))))
      (assign 9 2))
    (ifz 4 (assign 9 1) (assign 9 0))))

/-- `s = t_i`: remember the representative, stop. -/
def dupB : Program := seq (addTo 2 22 32) (seq (loadTo 13 2) (seq (assign 12 0) (assign 38 0)))

/-- `s < t_i`: insert at `i`. -/
def ltB : Program :=
  seq (copyTo 39 32) (seq (copyTo 10 34) (seq (copyTo 11 33) (seq (assign 12 1) (assign 38 0))))

/-- `s > t_i` and `i + 1 = d`: insert at the end. -/
def gtEndB : Program := seq (copyTo 39 23) (seq (copyTo 10 33) (seq (assign 12 1) (assign 38 0)))

/-- `s > t_i` and `i + 1 < d`: compare `L_i` with `l`. -/
def gtMidB : Program :=
  seq (addTo 5 25 32) (seq (loadTo 5 5) (seq (subTo 6 33 5) (ifz 6
    (seq (addTo 39 32 1) (seq (copyTo 10 33) (seq (copyTo 11 5) (seq (assign 12 1)
      (assign 38 0)))))
    (seq (copyTo 34 33) (addTo 32 32 1)))))

/-- `s > t_i`. -/
def gtB : Program := seq (addTo 2 32 1) (seq (subTo 4 23 2) (ifz 4 gtMidB gtEndB))

/-- The decision after the comparison. -/
def decideB : Program := seq cmpB (ifz 9 (seq (subTo 2 9 1) (ifz 2 gtB ltB)) dupB)

/-- One step of the scan: fetch `t_i`, extend the common prefix, decide. -/
def scanBody : Program := seq loadT (seq flagB (seq extLoop decideB))

/-- The scan along the sorted list. -/
def scanLoop : Program := whileNz 38 scanBody

/-- Start the scan at `i = 0`, `l = 0`. -/
def scanInit : Program := seq (assign 32 0) (seq (assign 33 0) (seq (assign 34 0) (assign 38 1)))

/-- Shift `D[p..d)` and the `lcp`s `[p..d)` up by one place (register `3` counts, `4` points). -/
def shiftLoop : Program :=
  whileNz 3 (seq (loadTo 6 4) (seq (addTo 7 4 1) (seq (storeTo 7 6) (seq (addTo 5 4 21)
    (seq (loadTo 6 5) (seq (addTo 7 5 1) (seq (storeTo 7 6) (seq (subTo 4 4 1)
      (subTo 3 3 1)))))))))

theorem shiftLoop_eq : shiftLoop = whileNz 3 (seq (loadTo 6 4) (seq (addTo 7 4 1)
    (seq (storeTo 7 6) (seq (addTo 5 4 21) (seq (loadTo 6 5) (seq (addTo 7 5 1)
    (seq (storeTo 7 6) (seq (subTo 4 4 1) (subTo 3 3 1))))))))) := rfl

/-- Insert string `x` at position `p`: shift, write `x` and the two new `lcp`s, `rep[x] = x`,
`d := d + 1`. -/
def insertB : Program :=
  seq (subTo 3 23 39) (seq (addTo 4 22 23) (seq (subTo 4 4 1) (seq shiftLoop
    (seq (addTo 2 22 39) (seq (storeTo 2 28)
    (seq (ifz 39 (seq (addTo 2 25 39) (seq (subTo 2 2 1) (storeTo 2 10))) [])
    (seq (subTo 3 23 39) (seq (ifz 3 (seq (addTo 2 25 39) (storeTo 2 11)) [])
    (seq (addTo 2 26 28) (seq (storeTo 2 28) (addTo 23 23 1)))))))))))

/-- Process string `x`. -/
def insertOne : Program :=
  seq (addTo 2 20 28) (seq (loadTo 30 2) (seq (loadTo 31 30)
    (seq (ifz 23 (seq scanInit scanLoop) (seq (assign 39 0) (assign 12 1)))
      (ifz 12 insertB (seq (addTo 2 26 28) (storeTo 2 13))))))

/-- All strings. -/
def vertexLoop : Program :=
  whileNz 29 (seq insertOne (seq (addTo 28 28 1) (subTo 29 29 1)))

/-- `pos[D[i]] = i`. -/
def posLoop : Program :=
  seq (assign 32 0) (seq (copyTo 29 23) (whileNz 29 (seq (addTo 2 22 32) (seq (loadTo 2 2)
    (seq (addTo 2 27 2) (seq (storeTo 2 32) (seq (addTo 32 32 1) (subTo 29 29 1))))))))

/-- `rank[x] = pos[rep[x]]`. -/
def rankLoop : Program :=
  seq (assign 28 0) (seq (copyTo 29 21) (whileNz 29 (seq (addTo 2 26 28) (seq (loadTo 2 2)
    (seq (addTo 2 27 2) (seq (loadTo 2 2) (seq (addTo 4 24 28) (seq (storeTo 4 2)
      (seq (addTo 28 28 1) (subTo 29 29 1))))))))))

/-- Allocate the five arrays. -/
def sortInit : Program :=
  seq (copyTo 22 14) (seq (addTo 25 22 21) (seq (addTo 26 25 21) (seq (addTo 27 26 21)
    (seq (addTo 24 27 21) (seq (addTo 14 24 21) (seq (assign 23 0) (seq (assign 28 0)
      (copyTo 29 21))))))))

/-- **The sorting routine.** -/
def sortProg : Program := seq sortInit (seq vertexLoop (seq posLoop rankLoop))

/-! ## The comparison flag -/

theorem wf_flagB : Wf flagB := by unfold flagB; wf_tac

theorem runsTo_flagB {M : Mem} (h1 : M 1 = 1) (h30 : 64 ≤ M 30) (h35 : 64 ≤ M 35) :
    RunsTo flagB (fun m => m = M)
      (fun m => Outside [2, 4, 5, 6, 7, 8, 37] M m ∧
        (m 37 ≠ 0 ↔ (M 33 < M 31 ∧ M 33 < M 36 ∧
          M (M 30 + M 33 + 1 + 1) = M (M 35 + M 33 + 1 + 1)))) 18 := by
  unfold flagB
  refine sub_seq' ?_
  by_cases hs : M 33 < M 31
  · have e2 : (M.update 2 (M 31 - M 33)) 2 ≠ 0 := by rw [Mem.update_self]; omega
    refine ifz_ne' (T := 15) e2 ?_ (Layout.wf_assign _ _)
    refine sub_seq' ?_
    by_cases ht : M 33 < M 36
    · have e4 : ((M.update 2 (M 31 - M 33)).update 4 ((M.update 2 (M 31 - M 33)) 36 -
          (M.update 2 (M 31 - M 33)) 33)) 4 ≠ 0 := by
        simp (disch := omega) only [Mem.update_self, Mem.update_of_ne]; omega
      refine ifz_ne' (T := 12) e4 ?_ (Layout.wf_assign _ _)
      rt
      refine ⟨by outside_tac (Outside.refl [2, 4, 5, 6, 7, 8, 37] M), ?_⟩
      simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, h1]
      omega
    · have e4 : ((M.update 2 (M 31 - M 33)).update 4 ((M.update 2 (M 31 - M 33)) 36 -
          (M.update 2 (M 31 - M 33)) 33)) 4 = 0 := by
        simp (disch := omega) only [Mem.update_self, Mem.update_of_ne]; omega
      refine ifz_eq' (T := 12) e4 ?_ (by wf_tac)
      rt
      refine ⟨by outside_tac (Outside.refl [2, 4, 5, 6, 7, 8, 37] M), ?_⟩
      simp (disch := omega) only [Mem.update_self, Mem.update_of_ne]
      omega
  · have e2 : (M.update 2 (M 31 - M 33)) 2 = 0 := by rw [Mem.update_self]; omega
    refine ifz_eq' (T := 15) e2 ?_ (by wf_tac)
    rt
    refine ⟨by outside_tac (Outside.refl [2, 4, 5, 6, 7, 8, 37] M), ?_⟩
    simp (disch := omega) only [Mem.update_self, Mem.update_of_ne]
    omega


/-! ## Extending the common prefix -/

/-- What the comparison loops read: the strings `s` (at `sp`) and `t` (at `tp`). -/
structure CmpCtx (sp tp : ℕ) (s t : List ℕ) (m : Mem) : Prop where
  one : m 1 = 1
  r30 : m 30 = sp
  r31 : m 31 = 2 * s.length
  r35 : m 35 = tp
  r36 : m 36 = 2 * t.length
  hsp : 64 ≤ sp
  htp : 64 ≤ tp
  ss : StrAt m sp s
  st : StrAt m tp t

theorem CmpCtx.of_outside {sp tp : ℕ} {s t : List ℕ} {M m : Mem} (h : CmpCtx sp tp s t M)
    {W : List ℕ} (ho : Outside W M m) (hW : ∀ z ∈ W, z < 64 ∧ z ≠ 1 ∧ z ≠ 30 ∧ z ≠ 31 ∧
      z ≠ 35 ∧ z ≠ 36) : CmpCtx sp tp s t m := by
  have key : ∀ z, (64 ≤ z ∨ z = 1 ∨ z = 30 ∨ z = 31 ∨ z = 35 ∨ z = 36) → m z = M z :=
    fun z hz => ho z (fun hzW => by have := hW z hzW; omega)
  refine ⟨?_, ?_, ?_, ?_, ?_, h.hsp, h.htp, ?_, ?_⟩
  · rw [key 1 (by omega), h.one]
  · rw [key 30 (by omega), h.r30]
  · rw [key 31 (by omega), h.r31]
  · rw [key 35 (by omega), h.r35]
  · rw [key 36 (by omega), h.r36]
  · exact h.ss.congr (fun z hz _ => key z (Or.inl (by have := h.hsp; omega)))
  · exact h.st.congr (fun z hz _ => key z (Or.inl (by have := h.htp; omega)))

/-- The flag of `flagB`, read semantically. -/
theorem flag_sem {sp tp : ℕ} {s t : List ℕ} {m : Mem} (h : CmpCtx sp tp s t m) {l : ℕ}
    (hl : m 33 = 2 * l) :
    (m 33 < m 31 ∧ m 33 < m 36 ∧ m (m 30 + m 33 + 1 + 1) = m (m 35 + m 33 + 1 + 1)) ↔
      ∃ (h1 : l < s.length) (h2 : l < t.length), s[l] = t[l] := by
  rw [hl, h.r31, h.r36, h.r30, h.r35]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨by omega, by omega, ?_⟩
    rw [← h.ss.letter (by omega), ← h.st.letter (by omega)]; exact h3
  · rintro ⟨h1, h2, h3⟩
    refine ⟨by omega, by omega, ?_⟩
    rw [h.ss.letter h1, h.st.letter h2]; exact h3

/-- The invariant of the extension loop. -/
def ExtInv (M1 : Mem) (s t : List ℕ) (m : Mem) : Prop :=
  Outside [2, 4, 5, 6, 7, 8, 33, 37] M1 m ∧ ∃ l, m 33 = 2 * l ∧ l ≤ s.length ∧
    l ≤ t.length ∧ (∀ j < l, s[j]? = t[j]?) ∧
    (m 37 ≠ 0 ↔ ∃ (h1 : l < s.length) (h2 : l < t.length), s[l] = t[l])

theorem wf_extBody : Wf (seq (addTo 33 33 1) (seq (addTo 33 33 1) flagB)) :=
  wf_seq (Layout.wf_addTo _ _ _) (wf_seq (Layout.wf_addTo _ _ _) wf_flagB)

theorem wf_extLoop : Wf extLoop := wf_whileNz wf_extBody

/-- **The extension loop**: it stops at the common prefix, paying `11` steps per letter. -/
theorem runsTo_extLoop {M1 : Mem} {sp tp : ℕ} {s t : List ℕ} (hC : CmpCtx sp tp s t M1) :
    ∀ M, ExtInv M1 s t M → ∃ T, RunsTo extLoop (fun m => m = M)
      (fun m' => ExtInv M1 s t m' ∧ m' 37 = 0 ∧
        11 * (2 * s.length - m' 33) + T ≤ 11 * (2 * s.length - M 33) + 1) T := by
  refine runsTo_whileNz_amortX wf_extBody (ExtInv M1 s t)
    (fun m => 11 * (2 * s.length - m 33)) ?_
  intro M ⟨ho, l, h33, hls, hlt, hag, hfl⟩ h37
  obtain ⟨h1, h2, h3⟩ := hfl.1 h37
  have hC' := hC.of_outside ho (by intro z hz; simp at hz; omega)
  refine ⟨20, ?_⟩
  refine add_seq' (add_seq' ?_)
  set M' := (M.update 33 (M 33 + M 1)).update 33
    ((M.update 33 (M 33 + M 1)) 33 + (M.update 33 (M 33 + M 1)) 1) with hM'
  have e33 : M' 33 = 2 * (l + 1) := by
    rw [hM']; simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, hC'.one, h33]; ring
  have ho' : Outside [2, 4, 5, 6, 7, 8, 33, 37] M1 M' := by
    rw [hM']; exact (ho.upd (by simp) _).upd (by simp) _
  have hC'' := hC.of_outside ho' (by intro z hz; simp at hz; omega)
  refine (runsTo_flagB hC''.one (by rw [hC''.r30]; exact hC.hsp)
    (by rw [hC''.r35]; exact hC.htp)).weaken (fun m hm => ?_)
  obtain ⟨hom, hfm⟩ := hm
  have ho'' : Outside [2, 4, 5, 6, 7, 8, 33, 37] M1 m :=
    Algo.ExplLinear.Outside.sub ho' hom (by intro z hz; simp at hz ⊢; omega)
  have e33m : m 33 = 2 * (l + 1) := by rw [hom 33 (by simp), e33]
  refine ⟨⟨ho'', l + 1, e33m, by omega, by omega, ?_, ?_⟩, ?_⟩
  · intro j hj
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
    · exact hag j hj
    · rw [List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2, h3]
  · rw [hfm, flag_sem hC'' e33]
  · show 11 * (2 * s.length - m 33) + 20 + 2 ≤ 11 * (2 * s.length - M 33)
    rw [e33m, h33]; omega


/-! ## The environment of the sort -/

/-- The data the sort reads and never writes: the constants, the array of string addresses,
and the strings, all below the region `[A, A + 5n)`. -/
structure SEnv (n SA A : ℕ) (str : ℕ → List ℕ) (m : Mem) : Prop where
  one : m 1 = 1
  r20 : m 20 = SA
  r21 : m 21 = n
  r22 : m 22 = A
  r25 : m 25 = A + n
  r26 : m 26 = A + n + n
  r27 : m 27 = A + n + n + n
  r24 : m 24 = A + n + n + n + n
  hSA : 64 ≤ SA
  hSAn : SA + n ≤ A
  sp64 : ∀ v < n, 64 ≤ m (SA + v)
  spA : ∀ v < n, m (SA + v) + 1 + 2 * (str v).length ≤ A
  strs : ∀ v < n, StrAt m (m (SA + v)) (str v)

theorem SEnv.of_keep {n SA A : ℕ} {str : ℕ → List ℕ} {M m : Mem} (h : SEnv n SA A str M)
    {W : List ℕ} {a b : ℕ} (hk : Keep W a b M m) (ha : A ≤ a)
    (hW : ∀ z ∈ W, z < 64 ∧ z ≠ 1 ∧ z ≠ 20 ∧ z ≠ 21 ∧ z ≠ 22 ∧ z ≠ 24 ∧ z ≠ 25 ∧ z ≠ 26 ∧
      z ≠ 27) : SEnv n SA A str m := by
  have key : ∀ z, z < A → (64 ≤ z ∨ z = 1 ∨ z = 20 ∨ z = 21 ∨ z = 22 ∨ z = 24 ∨ z = 25 ∨
      z = 26 ∨ z = 27) → m z = M z :=
    fun z hz hz' => hk z (fun hzW => by have := hW z hzW; omega) (Or.inl (by omega))
  have hA : 64 ≤ A := by have := h.hSA; have := h.hSAn; omega
  have eS : ∀ v < n, m (SA + v) = M (SA + v) := fun v hv =>
    key _ (by have := h.hSAn; omega) (Or.inl (by have := h.hSA; omega))
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, h.hSA, h.hSAn, ?_, ?_, ?_⟩
  · rw [key 1 (by omega) (by omega), h.one]
  · rw [key 20 (by omega) (by omega), h.r20]
  · rw [key 21 (by omega) (by omega), h.r21]
  · rw [key 22 (by omega) (by omega), h.r22]
  · rw [key 25 (by omega) (by omega), h.r25]
  · rw [key 26 (by omega) (by omega), h.r26]
  · rw [key 27 (by omega) (by omega), h.r27]
  · rw [key 24 (by omega) (by omega), h.r24]
  · intro v hv; rw [eS v hv]; exact h.sp64 v hv
  · intro v hv; rw [eS v hv]; exact h.spA v hv
  · intro v hv
    rw [eS v hv]
    exact (h.strs v hv).congr (fun z hz1 hz2 => key z (by have := h.spA v hv; omega)
      (Or.inl (by have := h.sp64 v hv; omega)))

/-- The string of the representative number `i`. -/
def tStr (str : ℕ → List ℕ) (Dl : List ℕ) (i : ℕ) : List ℕ := str (Dl.getD i 0)

/-- The sorted list of representatives and the `lcp`s of neighbours. -/
structure SortCtx (n SA A : ℕ) (str : ℕ → List ℕ) (Dl : List ℕ) (m : Mem) : Prop where
  env : SEnv n SA A str m
  r23 : m 23 = Dl.length
  blk : Blk m A Dl
  dlt : ∀ v ∈ Dl, v < n
  sorted : (Dl.map str).Pairwise (· < ·)
  lcps : ∀ i, i + 1 < Dl.length →
    m (A + n + i) = 2 * lcp (tStr str Dl i) (tStr str Dl (i + 1))

theorem SortCtx.of_outside {n SA A : ℕ} {str : ℕ → List ℕ} {Dl : List ℕ} {M m : Mem}
    (h : SortCtx n SA A str Dl M) {W : List ℕ} (ho : Outside W M m)
    (hW : ∀ z ∈ W, z < 64 ∧ z ≠ 1 ∧ z ≠ 20 ∧ z ≠ 21 ∧ z ≠ 22 ∧ z ≠ 23 ∧ z ≠ 24 ∧ z ≠ 25 ∧
      z ≠ 26 ∧ z ≠ 27) : SortCtx n SA A str Dl m := by
  have hA : 64 ≤ A := by have := h.env.hSA; have := h.env.hSAn; omega
  refine ⟨h.env.of_keep (a := A) (b := A) (Keep.of_outside ho) le_rfl
    (fun z hz => by have := hW z hz; omega), ?_, ?_, h.dlt, h.sorted, ?_⟩
  · rw [ho 23 (fun h' => by have := hW 23 h'; omega), h.r23]
  · exact Blk.congr h.blk (fun z hz _ => ho z (fun h' => by have := hW z h'; omega))
  · intro i hi
    rw [ho _ (fun h' => by have := hW _ h'; omega), h.lcps i hi]

theorem tStr_lt {str : ℕ → List ℕ} {Dl : List ℕ} (hs : (Dl.map str).Pairwise (· < ·))
    {i j : ℕ} (hij : i < j) (hj : j < Dl.length) : tStr str Dl i < tStr str Dl j := by
  have := List.pairwise_iff_getElem.1 hs i j (by simp; omega) (by simp; omega) hij
  rw [tStr, tStr, List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ hj]
  simpa using this

theorem SortCtx.getD {n SA A : ℕ} {str : ℕ → List ℕ} {Dl : List ℕ} {m : Mem}
    (h : SortCtx n SA A str Dl m) {i : ℕ} (hi : i < Dl.length) :
    m (A + i) = Dl.getD i 0 ∧ Dl.getD i 0 < n := by
  rw [List.getD_eq_getElem _ _ hi]
  exact ⟨h.blk i hi, h.dlt _ (List.getElem_mem hi)⟩

/-! ## The scan -/

/-- The scan is at position `i = m 32`, all earlier strings are below `s`, and `s` agrees with
`t_i` on the first `l` letters (`m 33 = 2l`). -/
def ScanPos (str : ℕ → List ℕ) (Dl : List ℕ) (s : List ℕ) (m : Mem) : Prop :=
  m 32 < Dl.length ∧ ∃ l, m 33 = 2 * l ∧ l ≤ s.length ∧ l ≤ (tStr str Dl (m 32)).length ∧
    (∀ j < l, s[j]? = (tStr str Dl (m 32))[j]?) ∧ (∀ i' < m 32, tStr str Dl i' < s) ∧
    (0 < m 32 → m 34 = 2 * lcp (tStr str Dl (m 32 - 1)) s)

/-- The outcome of the scan: a duplicate (register `12` is `0`, `13` its representative), or
the insertion position `p = m 39` with the two new `lcp`s in `10`, `11`. -/
def ScanRes (str : ℕ → List ℕ) (Dl : List ℕ) (s : List ℕ) (m : Mem) : Prop :=
  (m 12 = 0 ∧ ∃ i' < Dl.length, m 13 = Dl.getD i' 0 ∧ tStr str Dl i' = s) ∨
  (m 12 = 1 ∧ m 39 ≤ Dl.length ∧ (∀ i' < m 39, tStr str Dl i' < s) ∧
    (∀ i', m 39 ≤ i' → i' < Dl.length → s < tStr str Dl i') ∧
    (0 < m 39 → m 10 = 2 * lcp (tStr str Dl (m 39 - 1)) s) ∧
    (m 39 < Dl.length → m 11 = 2 * lcp s (tStr str Dl (m 39))))

/-- The registers the scan writes. -/
notation "Wsc" => [2, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 32, 33, 34, 35, 36, 37, 38, 39]

theorem wf_loadT : Wf loadT := by unfold loadT; wf_tac

theorem runsTo_loadT {n SA A : ℕ} {str : ℕ → List ℕ} {Dl : List ℕ} {M : Mem}
    (hS : SortCtx n SA A str Dl M) (hi : M 32 < Dl.length) :
    RunsTo loadT (fun m => m = M) (fun m => Outside [2, 35, 36] M m ∧
      m 35 = M (SA + Dl.getD (M 32) 0) ∧ m 36 = 2 * (tStr str Dl (M 32)).length) 5 := by
  obtain ⟨eD, hv⟩ := hS.getD hi
  have hA : 64 ≤ A := by have := hS.env.hSA; have := hS.env.hSAn; omega
  have h64 := hS.env.sp64 _ hv
  have hstr := hS.env.strs _ hv
  have hSA := hS.env.hSA
  unfold loadT
  rt
  refine ⟨by outside_tac (Outside.refl [2, 35, 36] M), ?_, ?_⟩
  · simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, hS.env.r22, hS.env.r20, eD]
  · simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, hS.env.r22, hS.env.r20, eD]
    rw [hstr.1]; rfl

/-- The code of the comparison at the common prefix. -/
def cmpCode (m : Mem) : ℕ :=
  if m 33 < m 31 then
    (if m 33 < m 36 then (if m (m 35 + m 33 + 1 + 1) - m (m 30 + m 33 + 1 + 1) = 0 then 2 else 1)
      else 2)
  else (if m 33 < m 36 then 1 else 0)

theorem wf_cmpB : Wf cmpB := by unfold cmpB; wf_tac

theorem runsTo_cmpB {M : Mem} (h1 : M 1 = 1) (h30 : 64 ≤ M 30) (h35 : 64 ≤ M 35) :
    RunsTo cmpB (fun m => m = M)
      (fun m => Outside [2, 4, 5, 6, 7, 9] M m ∧ m 9 = cmpCode M) 18 := by
  unfold cmpB
  refine sub_seq' (sub_seq' ?_)
  set M1 := (M.update 2 (M 31 - M 33)).update 4 ((M.update 2 (M 31 - M 33)) 36 -
    (M.update 2 (M 31 - M 33)) 33) with hM1
  have e2 : M1 2 = M 31 - M 33 := by rw [hM1]; simp (disch := omega) only [Mem.update_self,
    Mem.update_of_ne]
  have e4 : M1 4 = M 36 - M 33 := by rw [hM1]; simp (disch := omega) only [Mem.update_self,
    Mem.update_of_ne]
  have ho1 : Outside [2, 4, 5, 6, 7, 9] M M1 := by
    rw [hM1]; outside_tac (Outside.refl [2, 4, 5, 6, 7, 9] M)
  have f : ∀ z, 9 < z → M1 z = M z := fun z hz => ho1 z (by simp; omega)
  have f1 : M1 1 = M 1 := ho1 1 (by simp)
  by_cases hs : M 33 < M 31
  · refine ifz_ne' (T := 14) (by rw [e2]; omega) ?_ (by wf_tac)
    by_cases ht : M 33 < M 36
    · refine ifz_ne' (T := 12) (by rw [e4]; omega) ?_ (by wf_tac)
      refine add_seq' (add_seq' (add_seq' (load_seq' (add_seq' (add_seq' (add_seq'
        (load_seq' (sub_seq' ?_))))))))
      by_cases hc : M (M 35 + M 33 + 1 + 1) - M (M 30 + M 33 + 1 + 1) = 0
      · refine ifz_eq' (T := 1) ?_ (assign_last' ⟨?_, ?_⟩) (by wf_tac)
        · simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, f, f1, h1]; omega
        · outside_tac ho1
        · rw [Mem.update_self, cmpCode, if_pos hs, if_pos ht, if_pos hc]
      · refine ifz_ne' (T := 1) ?_ (assign_last' ⟨?_, ?_⟩) (by wf_tac)
        · simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, f, f1, h1]; omega
        · outside_tac ho1
        · rw [Mem.update_self, cmpCode, if_pos hs, if_pos ht, if_neg hc]
    · refine ifz_eq' (T := 12) (by rw [e4]; omega) (assign_last' ⟨ho1.upd (by simp) _, ?_⟩)
        (by wf_tac)
      rw [Mem.update_self, cmpCode, if_pos hs, if_neg ht]
  · refine ifz_eq' (T := 14) (by rw [e2]; omega) ?_ (by wf_tac)
    by_cases ht : M 33 < M 36
    · refine ifz_ne' (T := 12) (by rw [e4]; omega) (assign_last' ⟨ho1.upd (by simp) _, ?_⟩)
        (by wf_tac)
      rw [Mem.update_self, cmpCode, if_neg hs, if_pos ht]
    · refine ifz_eq' (T := 12) (by rw [e4]; omega) (assign_last' ⟨ho1.upd (by simp) _, ?_⟩)
        (by wf_tac)
      rw [Mem.update_self, cmpCode, if_neg hs, if_neg ht]

/-- The code of the comparison, read semantically, at the common prefix `l = lcp s t`. -/
theorem cmpCode_sem {sp tp : ℕ} {s t : List ℕ} {m : Mem} (h : CmpCtx sp tp s t m)
    (hl : m 33 = 2 * lcp s t) :
    (cmpCode m = 0 → s = t) ∧ (cmpCode m = 1 → s < t) ∧ (cmpCode m = 2 → t < s) := by
  have hls := lcp_le_left s t
  have hlt := lcp_le_right s t
  have hc : lcp t s = lcp s t := lcp_comm t s
  unfold cmpCode
  rw [hl, h.r31, h.r36, h.r30, h.r35]
  by_cases hs : lcp s t < s.length
  · by_cases ht : lcp s t < t.length
    · have hne := lcp_stop hs ht
      have ea := h.ss.letter hs
      have eb := h.st.letter ht
      rw [if_pos (by omega), if_pos (by omega), ea, eb]
      by_cases hc' : t[lcp s t] - s[lcp s t] = 0
      · rw [if_pos hc']
        refine ⟨by omega, by omega, fun _ => ?_⟩
        rw [lt_iff_lcp, hc]
        right; refine ⟨by omega, by omega, ?_⟩
        have := Nat.lt_of_le_of_ne (by omega) (Ne.symm hne)
        exact this
      · rw [if_neg hc']
        refine ⟨by omega, fun _ => ?_, by omega⟩
        rw [lt_iff_lcp]
        right; exact ⟨hs, ht, by omega⟩
    · rw [if_pos (by omega), if_neg (by omega)]
      refine ⟨by omega, by omega, fun _ => ?_⟩
      rw [lt_iff_lcp, hc]; left; exact ⟨by omega, hs⟩
  · rw [if_neg (by omega)]
    by_cases ht : lcp s t < t.length
    · rw [if_pos (by omega)]
      refine ⟨by omega, fun _ => ?_, by omega⟩
      rw [lt_iff_lcp]; left; exact ⟨by omega, ht⟩
    · rw [if_neg (by omega)]
      refine ⟨fun _ => ?_, by omega, by omega⟩
      rw [eq_iff_lcp]; omega


/-! ## The decision -/

theorem wf_decideB : Wf decideB := by
  unfold decideB cmpB gtB gtMidB gtEndB ltB dupB; wf_tac

/-- The registers the decision writes. -/
notation "Wdc" => [2, 4, 5, 6, 7, 9, 10, 11, 12, 13, 32, 34, 38, 39]

/-- **The decision.**  After the extension loop, `33` holds `2 lcp(s, t_i)`.  The decision
either ends the scan with its outcome, or moves to `i + 1` keeping `l`. -/
theorem runsTo_decideB {n SA A : ℕ} {str : ℕ → List ℕ} {Dl : List ℕ} {s : List ℕ} {sp tp : ℕ}
    {M : Mem} (hS : SortCtx n SA A str Dl M) (hC : CmpCtx sp tp s (tStr str Dl (M 32)) M)
    (hi : M 32 < Dl.length) (hl : M 33 = 2 * lcp s (tStr str Dl (M 32)))
    (hprev : ∀ i' < M 32, tStr str Dl i' < s)
    (h34 : 0 < M 32 → M 34 = 2 * lcp (tStr str Dl (M 32 - 1)) s) :
    RunsTo decideB (fun m => m = M) (fun m => Outside Wdc M m ∧
      ((m 38 = 0 ∧ m 32 = M 32 ∧ ScanRes str Dl s m) ∨
       (m 38 = M 38 ∧ m 32 = M 32 + 1 ∧ m 33 = M 33 ∧ ScanPos str Dl s m))) 40 := by
  set i := M 32 with hidef
  set T := tStr str Dl with hT
  have hcs := cmpCode_sem hC hl
  have hsort := hS.sorted
  have h1 := hC.one
  have hA : 64 ≤ A := by have := hS.env.hSA; have := hS.env.hSAn; omega
  have r22 := hS.env.r22
  have r23 := hS.r23
  have r25 := hS.env.r25
  unfold decideB
  refine block_seq (T' := 22) (runsTo_cmpB h1 (by rw [hC.r30]; exact hC.hsp) (by rw [hC.r35]; exact hC.htp))
    (fun M1 hM1 => ?_)
  obtain ⟨ho1, e9⟩ := hM1
  have f : ∀ z, z ∉ [2, 4, 5, 6, 7, 9] → M1 z = M z := ho1
  have g1 : M1 1 = 1 := by rw [f 1 (by simp), h1]
  have g22 : M1 22 = A := by rw [f 22 (by simp), r22]
  have g23 : M1 23 = Dl.length := by rw [f 23 (by simp), r23]
  have g25 : M1 25 = A + n := by rw [f 25 (by simp), r25]
  have g32 : M1 32 = i := f 32 (by simp)
  have g33 : M1 33 = M 33 := f 33 (by simp)
  have g34 : M1 34 = M 34 := f 34 (by simp)
  have g38 : M1 38 = M 38 := f 38 (by simp)
  have gD : M1 (A + i) = Dl.getD i 0 := by
    rw [f _ (by simp; omega)]; exact (hS.getD hi).1
  have gL : i + 1 < Dl.length → M1 (A + n + i) = 2 * lcp (T i) (T (i + 1)) := fun h => by
    rw [f _ (by simp; omega)]; exact hS.lcps i h
  have hlcp := lcp_comm s (T i)
  rcases Nat.lt_or_ge (cmpCode M) 1 with hc0 | hc
  · -- `s = t_i`
    have heq : s = T i := hcs.1 (by omega)
    refine (ifz_eq' (T := 4) (by rw [e9]; omega) ?_ (by wf_tac)).mono (by omega)
    unfold dupB
    rt
    refine ⟨by outside_tac ho1, Or.inl ⟨?_, ?_, Or.inl ⟨?_, i, hi, ?_, heq.symm⟩⟩⟩
    · simp (disch := omega) only [Mem.update_self]
    · simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, g32]
    · simp (disch := omega) only [Mem.update_self, Mem.update_of_ne]
    · simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, g22, g32, gD]
  -- the branch on `9 - 1`
  refine (ifz_ne' (T := 1 + 2 + 16) (by rw [e9]; omega) ?_ (by wf_tac)).mono (by omega)
  refine sub_seq' ?_
  refine Algo.ExplLinear.at_mem (fun M2 => Outside [2, 4, 5, 6, 7, 9] M M2 ∧ M2 2 = cmpCode M - 1 ∧
      ∀ z, z ≠ 2 → M2 z = M1 z) ⟨?_, ?_, ?_⟩ (fun M2 hM2 => ?_)
  · outside_tac ho1
  · simp (disch := omega) only [Mem.update_self, e9, g1]
  · intro z hz; simp (disch := omega) only [Mem.update_of_ne]
  obtain ⟨ho2, e2, f2⟩ := hM2
  have h1' : M2 1 = 1 := by rw [f2 1 (by omega), g1]
  have h22' : M2 22 = A := by rw [f2 22 (by omega), g22]
  have h23' : M2 23 = Dl.length := by rw [f2 23 (by omega), g23]
  have h25' : M2 25 = A + n := by rw [f2 25 (by omega), g25]
  have h32' : M2 32 = i := by rw [f2 32 (by omega), g32]
  have h33' : M2 33 = M 33 := by rw [f2 33 (by omega), g33]
  have h34' : M2 34 = M 34 := by rw [f2 34 (by omega), g34]
  have h38' : M2 38 = M 38 := by rw [f2 38 (by omega), g38]
  have hL' : i + 1 < Dl.length → M2 (A + n + i) = 2 * lcp (T i) (T (i + 1)) := fun h => by
    rw [f2 _ (by omega)]; exact gL h
  rcases Nat.lt_or_ge (cmpCode M) 2 with hc1 | hc2
  · -- `s < t_i`: insert at `i`
    have hlt : s < T i := hcs.2.1 (by omega)
    refine (ifz_eq' (T := 5) (by rw [e2]; omega) ?_ (by unfold gtB gtMidB gtEndB; wf_tac)).mono
      (by omega)
    unfold ltB
    rt
    refine ⟨by outside_tac ho2, Or.inl ⟨?_, ?_, Or.inr ⟨?_, ?_⟩⟩⟩
    · simp (disch := omega) only [Mem.update_self]
    · simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, h32']
    · simp (disch := omega) only [Mem.update_self, Mem.update_of_ne]
    simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, h32', h33', h34']
    refine ⟨le_of_lt hi, hprev, fun i' h1' h2' => ?_, fun h => h34 h, fun _ => ?_⟩
    · rcases Nat.lt_or_ge i i' with h | h
      · exact lt_trans hlt (tStr_lt hsort h h2')
      · have : i' = i := by omega
        rw [this]; exact hlt
    · rw [hl]
  -- `s > t_i`
  have hgt : T i < s := hcs.2.2 (by
    have : cmpCode M ≤ 2 := by unfold cmpCode; split_ifs <;> omega
    omega)
  have hgt' : ∀ i' < i + 1, T i' < s := fun i' hi' => by
    rcases Nat.lt_or_ge i' i with h | h
    · exact hprev i' h
    · have : i' = i := by omega
      rw [this]; exact hgt
  refine (ifz_ne' (T := 14) (by rw [e2]; omega) ?_ (by unfold ltB; wf_tac)).mono (by omega)
  unfold gtB
  refine add_seq' (sub_seq' ?_)
  refine Algo.ExplLinear.at_mem (fun M3 => Outside [2, 4, 5, 6, 7, 9] M M3 ∧ M3 4 = Dl.length - (i + 1) ∧
      ∀ z, z ≠ 2 → z ≠ 4 → M3 z = M2 z) ⟨?_, ?_, ?_⟩ (fun M3 hM3 => ?_)
  · outside_tac ho2
  · simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, h1', h32', h23']
  · intro z hz hz'; simp (disch := omega) only [Mem.update_of_ne]
  obtain ⟨ho3, e4, f3⟩ := hM3
  have k1 : M3 1 = 1 := by rw [f3 1 (by omega) (by omega), h1']
  have k23 : M3 23 = Dl.length := by rw [f3 23 (by omega) (by omega), h23']
  have k25 : M3 25 = A + n := by rw [f3 25 (by omega) (by omega), h25']
  have k32 : M3 32 = i := by rw [f3 32 (by omega) (by omega), h32']
  have k33 : M3 33 = M 33 := by rw [f3 33 (by omega) (by omega), h33']
  have k38 : M3 38 = M 38 := by rw [f3 38 (by omega) (by omega), h38']
  by_cases hend : i + 1 < Dl.length
  · refine (ifz_ne' (T := 10) (by rw [e4]; omega) ?_ (by unfold gtEndB; wf_tac)).mono (by omega)
    unfold gtMidB
    refine add_seq' (load_seq' (sub_seq' ?_))
    have eL : M3 (A + n + i) = 2 * lcp (T i) (T (i + 1)) := by
      rw [f3 _ (by omega) (by omega)]; exact hL' hend
    refine Algo.ExplLinear.at_mem (fun M4 => Outside [2, 4, 5, 6, 7, 9] M M4 ∧
        M4 5 = 2 * lcp (T i) (T (i + 1)) ∧ M4 6 = M 33 - 2 * lcp (T i) (T (i + 1)) ∧
        ∀ z, z ≠ 5 → z ≠ 6 → M4 z = M3 z) ⟨?_, ?_, ?_, ?_⟩ (fun M4 hM4 => ?_)
    · outside_tac ho3
    · simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, k25, k32, eL]
    · simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, k25, k32, k33, eL]
    · intro z hz hz'; simp (disch := omega) only [Mem.update_of_ne]
    obtain ⟨ho4, e5, e6, f4⟩ := hM4
    have q1 : M4 1 = 1 := by rw [f4 1 (by omega) (by omega), k1]
    have q32 : M4 32 = i := by rw [f4 32 (by omega) (by omega), k32]
    have q33 : M4 33 = M 33 := by rw [f4 33 (by omega) (by omega), k33]
    have q38 : M4 38 = M 38 := by rw [f4 38 (by omega) (by omega), k38]
    by_cases hLl : lcp (T i) (T (i + 1)) < lcp s (T i)
    · -- insert at `i + 1`
      obtain ⟨hlt', hlcp'⟩ := scan_lt (tStr_lt hsort (Nat.lt_succ_self i) hend) hLl
      refine (ifz_ne' (T := 5) (by rw [e6, hl]; omega) ?_ (by wf_tac)).mono (by omega)
      rt
      refine ⟨by outside_tac ho4, Or.inl ⟨?_, ?_, Or.inr ⟨?_, ?_⟩⟩⟩
      · simp (disch := omega) only [Mem.update_self]
      · simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, q32]
      · simp (disch := omega) only [Mem.update_self, Mem.update_of_ne]
      simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, q1, q32, q33, e5]
      refine ⟨by omega, hgt', fun i' h1' h2' => ?_, fun _ => ?_, fun _ => ?_⟩
      · rcases Nat.lt_or_ge (i + 1) i' with h | h
        · exact lt_trans hlt' (tStr_lt hsort h h2')
        · have : i' = i + 1 := by omega
          rw [this]; exact hlt'
      · rw [hl, Nat.add_sub_cancel, lcp_comm]
      · rw [hlcp']
    · -- move on to `i + 1`
      obtain ⟨hag, hlen⟩ := scan_ge (s := s) (t := T i) (t' := T (i + 1)) (by omega)
      refine (ifz_eq' (T := 5) (by rw [e6, hl]; omega) ?_ (by wf_tac)).mono (by omega)
      rt
      refine ⟨by outside_tac ho4, Or.inr ⟨?_, ?_, ?_, ?_⟩⟩
      · simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, q38]
      · simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, q1, q32]
      · simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, q33]
      · unfold ScanPos
        simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, q1, q32, q33]
        refine ⟨hend, lcp s (T i), hl, lcp_le_left _ _, hlen, hag, hgt', fun _ => ?_⟩
        rw [Nat.add_sub_cancel, hl, lcp_comm]
  · refine (ifz_eq' (T := 10) (by rw [e4]; omega) ?_ (by unfold gtMidB; wf_tac)).mono (by omega)
    unfold gtEndB
    rt
    refine ⟨by outside_tac ho3, Or.inl ⟨?_, ?_, Or.inr ⟨?_, ?_⟩⟩⟩
    · simp (disch := omega) only [Mem.update_self]
    · simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, k32]
    · simp (disch := omega) only [Mem.update_self, Mem.update_of_ne]
    simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, k23, k33]
    have hd : Dl.length = i + 1 := by omega
    refine ⟨le_rfl, fun i' hi' => hgt' i' (by omega), fun i' h1' h2' => by omega,
      fun _ => ?_, fun h => by omega⟩
    rw [hd, Nat.add_sub_cancel, hl, lcp_comm]


/-! ## The scan loop -/

/-- The invariant of the scan loop. -/
def ScanInv (M0 : Mem) (str : ℕ → List ℕ) (Dl : List ℕ) (s : List ℕ) (m : Mem) : Prop :=
  Outside Wsc M0 m ∧ m 38 ≤ 1 ∧ (m 38 ≠ 0 → ScanPos str Dl s m) ∧
    (m 38 = 0 → ScanRes str Dl s m)

/-- The potential of the scan loop. -/
def scanPot (Dl : List ℕ) (s : List ℕ) (m : Mem) : ℕ :=
  11 * (2 * s.length - m 33) + 70 * (Dl.length - m 32) + 70 * m 38

theorem wf_scanBody : Wf scanBody :=
  wf_seq wf_loadT (wf_seq wf_flagB (wf_seq wf_extLoop wf_decideB))

theorem wf_scanLoop : Wf scanLoop := wf_whileNz wf_scanBody

/-- **The scan loop**: it finds the place of `s` among the representatives. -/
theorem runsTo_scanLoop {n SA A : ℕ} {str : ℕ → List ℕ} {Dl : List ℕ} {s : List ℕ} {sp : ℕ}
    {M0 : Mem} (hS : SortCtx n SA A str Dl M0) (h30 : M0 30 = sp) (h31 : M0 31 = 2 * s.length)
    (hsp : 64 ≤ sp) (hspA : sp + 1 + 2 * s.length ≤ A) (hss : StrAt M0 sp s) :
    ∀ M, ScanInv M0 str Dl s M → ∃ t, RunsTo scanLoop (fun m => m = M)
      (fun m' => ScanInv M0 str Dl s m' ∧ m' 38 = 0 ∧
        scanPot Dl s m' + t ≤ scanPot Dl s M + 1) t := by
  have hA : 64 ≤ A := by have := hS.env.hSA; have := hS.env.hSAn; omega
  refine runsTo_whileNz_amortX wf_scanBody (ScanInv M0 str Dl s) (scanPot Dl s) ?_
  intro M ⟨ho, h38le, hpos, _⟩ h38
  obtain ⟨hi, l, h33, hls, hlt, hag, hprev, h34⟩ := hpos h38
  set i := M 32 with hidef
  set T := tStr str Dl with hT
  have hSM : SortCtx n SA A str Dl M := hS.of_outside ho (by intro z hz; simp at hz; omega)
  have hsM : StrAt M sp s := hss.congr (fun z hz1 hz2 => ho z (by simp; omega))
  have hvn := (hSM.getD hi).2
  have htp64 := hSM.env.sp64 _ hvn
  have htpA := hSM.env.spA _ hvn
  have htstr := hSM.env.strs _ hvn
  -- fetch `t_i`
  obtain ⟨M1, ⟨ho1, e35, e36⟩, hrun1⟩ := (runsTo_loadT hSM hi).exact
  have hC1 : CmpCtx sp (M (SA + Dl.getD i 0)) s (T i) M1 := by
    refine ⟨by rw [ho1 1 (by simp), hSM.env.one], by rw [ho1 30 (by simp), ho 30 (by simp), h30],
      by rw [ho1 31 (by simp), ho 31 (by simp), h31], e35, e36, hsp, htp64, ?_, ?_⟩
    · exact hsM.congr (fun z hz1 hz2 => ho1 z (by simp; omega))
    · exact htstr.congr (fun z hz1 hz2 => ho1 z (by simp; omega))
  have g32 : M1 32 = i := ho1 32 (by simp)
  have g33 : M1 33 = 2 * l := by rw [ho1 33 (by simp), h33]
  have g34 : M1 34 = M 34 := ho1 34 (by simp)
  have g38 : M1 38 = M 38 := ho1 38 (by simp)
  -- the first flag
  obtain ⟨M2, ⟨ho2, hfl2⟩, hrun2⟩ := (runsTo_flagB hC1.one (by rw [hC1.r30]; exact hsp)
    (by rw [hC1.r35]; exact htp64)).exact
  have hext2 : ExtInv M1 s (T i) M2 := by
    refine ⟨ho2.mono (by intro z hz; simp at hz ⊢; omega), l, by rw [ho2 33 (by simp), g33],
      hls, hlt, hag, ?_⟩
    rw [hfl2, flag_sem hC1 g33]
  -- the extension loop
  obtain ⟨te, hte⟩ := runsTo_extLoop hC1 M2 hext2
  obtain ⟨M3, ⟨⟨ho3, l', h33', hls', hlt', hag', hfl3⟩, h37, hpot3⟩, hrun3⟩ := hte.exact
  have hlcp : lcp s (T i) = l' := by
    refine lcp_eq_of hag' hls' hlt' ?_
    by_cases a1 : l' < s.length
    · by_cases a2 : l' < (T i).length
      · right; right
        refine ⟨a1, a2, fun heq => ?_⟩
        exact (hfl3.2 ⟨a1, a2, heq⟩) h37
      · right; left; omega
    · left; omega
  have ho13 : Outside Wsc M M3 := by
    have := ho1.trans ho3
    exact this.mono (by intro z hz; simp at hz ⊢; omega)
  have hM3 : Outside Wsc M0 M3 := Algo.ExplLinear.Outside.sub ho ho13 (by simp)
  have hSM3 : SortCtx n SA A str Dl M3 := hS.of_outside hM3 (by intro z hz; simp at hz; omega)
  have hC3 : CmpCtx sp (M (SA + Dl.getD i 0)) s (T i) M3 :=
    hC1.of_outside ho3 (by intro z hz; simp at hz; omega)
  have k32 : M3 32 = i := by
    rw [ho3 32 (by simp), g32]
  have k34 : M3 34 = M 34 := by rw [ho3 34 (by simp), g34]
  have k38 : M3 38 = M 38 := by rw [ho3 38 (by simp), g38]
  have k33 : M3 33 = 2 * lcp s (T i) := by rw [h33', hlcp]
  have hM2_33 : M2 33 = 2 * l := by rw [ho2 33 (by simp), g33]
  -- the decision
  obtain ⟨M4, ⟨ho4, hres⟩, hrun4⟩ := (runsTo_decideB hSM3 (by rw [k32]; exact hC3)
    (by rw [k32]; exact hi) (by rw [k32]; exact k33) (by rw [k32]; exact hprev)
    (by rw [k32, k34]; exact h34)).exact
  refine ⟨5 + (18 + (te + 40)), ?_⟩
  refine (RunsTo.seq hrun1 (RunsTo.seq hrun2 (RunsTo.seq hrun3 hrun4))).weaken ?_
  intro m hm
  rw [hm]
  have hM4 : Outside Wsc M0 M4 := Algo.ExplLinear.Outside.sub hM3 ho4 (by simp)
  have hl'le : l' ≤ s.length := hls'
  rcases hres with ⟨e38, e32, hr⟩ | ⟨e38, e32, e33, hp⟩
  · refine ⟨⟨hM4, by omega, fun h => absurd e38 h, fun _ => hr⟩, ?_⟩
    have e33 : M4 33 = M3 33 := ho4 33 (by simp)
    unfold scanPot
    rw [e38, e32, k32, e33, h33', h33]
    have : 11 * (2 * s.length - 2 * l') + te ≤ 11 * (2 * s.length - 2 * l) + 1 := by
      rw [← h33', ← hM2_33]; exact hpot3
    have hll : l ≤ l' := by
      have := le_lcp_of hag hls hlt; omega
    have : M 38 = 1 := by omega
    rw [this]
    have : 11 * (2 * s.length - 2 * l) = 11 * (2 * s.length - 2 * l') + 22 * (l' - l) := by
      omega
    omega
  · refine ⟨⟨hM4, by rw [e38, k38]; exact h38le, fun _ => hp, fun h => by
      rw [e38, k38] at h; exact absurd h h38⟩, ?_⟩
    unfold scanPot
    rw [e38, e32, k32, k38, e33, h33', h33]
    have : 11 * (2 * s.length - 2 * l') + te ≤ 11 * (2 * s.length - 2 * l) + 1 := by
      rw [← h33', ← hM2_33]; exact hpot3
    have hll : l ≤ l' := by
      have := le_lcp_of hag hls hlt; omega
    have : i + 1 < Dl.length := by have := hp.1; rw [e32, k32] at this; exact this
    have : 11 * (2 * s.length - 2 * l) = 11 * (2 * s.length - 2 * l') + 22 * (l' - l) := by
      omega
    omega


/-! ## The shift -/

/-- The memory after `k` rounds of the shift: the top `k` cells of `D[p..d]` and of the `lcp`
array moved up by one. -/
def shiftMem (M0 : Mem) (A n d k : ℕ) (z : ℕ) : ℕ :=
  if (A + d - k < z ∧ z ≤ A + d) ∨ (A + n + d - k < z ∧ z ≤ A + n + d) then M0 (z - 1) else M0 z

def shiftBody : Program :=
  seq (loadTo 6 4) (seq (addTo 7 4 1) (seq (storeTo 7 6) (seq (addTo 5 4 21)
    (seq (loadTo 6 5) (seq (addTo 7 5 1) (seq (storeTo 7 6) (seq (subTo 4 4 1)
      (subTo 3 3 1))))))))

theorem wf_shiftBody : Wf shiftBody := by unfold shiftBody; wf_tac

theorem wf_shiftLoop : Wf shiftLoop := wf_whileNz wf_shiftBody

/-- **The shift loop.**  Register `3` holds `c = d - p`, register `4` the address `A + d - 1`;
the loop moves `D[p..d)` and the `lcp`s `[p..d)` (at `A + n`) up by one place. -/
theorem runsTo_shiftLoop {M0 : Mem} {A n d p : ℕ} (h1 : M0 1 = 1) (h21 : M0 21 = n)
    (h3 : M0 3 = d - p) (h4 : M0 4 = A + d - 1) (hpd : p ≤ d) (hdn : d < n) (hA : 64 ≤ A) :
    RunsTo shiftLoop (fun m => m = M0)
      (fun m => (∀ z, z ∉ [3, 4, 5, 6, 7] → m z = shiftMem M0 A n d (d - p) z) ∧
        m 1 = 1 ∧ m 21 = n) (11 * (d - p) + 1) := by
  have key := runsTo_whileNz_amortX (i := 3) wf_shiftBody
    (fun m => ∃ k ≤ d - p, m 3 = d - p - k ∧ m 4 + k + 1 = A + d ∧ m 1 = 1 ∧ m 21 = n ∧
      ∀ z, z ∉ [3, 4, 5, 6, 7] → m z = shiftMem M0 A n d k z)
    (fun m => 11 * m 3) ?_ M0 ⟨0, by omega, by rw [h3]; omega, by rw [h4]; omega, h1, h21,
      fun z _ => by unfold shiftMem; rw [if_neg (by omega)]⟩
  · obtain ⟨t, ht⟩ := key
    obtain ⟨k0, hk0, hrun⟩ := ht.spec M0 rfl
    refine ⟨wf_shiftLoop, fun m hm => ?_⟩
    subst hm
    obtain ⟨⟨k, hk, e3, e4, e1, e21, hz⟩, h30, hpot⟩ := hrun.2
    refine ⟨k0, ?_, hrun.1, ?_, e1, e21⟩
    · simp only at hpot; rw [h3] at hpot; omega
    · have : k = d - p := by omega
      rw [← this]; exact hz
  intro M ⟨k, hk, e3, e4, e1, e21, hz⟩ h3ne
  have hkc : k < d - p := by omega
  have hM4 : M 4 = A + d - 1 - k := by omega
  -- the two cells read are still the original ones
  have r1 : M (A + d - 1 - k) = M0 (A + d - 1 - k) := by
    rw [hz _ (by simp; omega)]; unfold shiftMem; rw [if_neg (by omega)]
  have r2 : M (A + n + d - 1 - k) = M0 (A + n + d - 1 - k) := by
    rw [hz _ (by simp; omega)]; unfold shiftMem; rw [if_neg (by omega)]
  refine ⟨9, ?_⟩
  unfold shiftBody
  rt
  refine ⟨⟨k + 1, by omega, ?_, ?_, ?_, ?_, fun z hzW => ?_⟩, ?_⟩
  · simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, e1, e3]; omega
  · simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, e1, hM4]; omega
  · simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, e1, hM4]
  · simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, e1, e21, hM4]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hzW
    simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, e1, e21, hM4]
    have ha : A + d - 1 - k + 1 = A + d - k := by omega
    have hb : A + d - 1 - k + n + 1 = A + n + d - k := by omega
    have hc : A + d - 1 - k + n = A + n + d - 1 - k := by omega
    rw [ha, hb, hc, r2]
    by_cases hz1 : z = A + n + d - k
    · subst hz1
      rw [Mem.update_self]
      unfold shiftMem; rw [if_pos (by omega)]; congr 1; omega
    · by_cases hz2 : z = A + d - k
      · subst hz2
        simp (disch := omega) only [Mem.update_self, Mem.update_of_ne]
        rw [r1]
        unfold shiftMem; rw [if_pos (by omega)]; congr 1; omega
      · simp (disch := omega) only [Mem.update_of_ne]
        rw [hz z (by simp; omega)]
        unfold shiftMem
        by_cases hin : (A + d - k < z ∧ z ≤ A + d) ∨ (A + n + d - k < z ∧ z ≤ A + n + d)
        · rw [if_pos hin, if_pos (by omega)]
        · rw [if_neg hin, if_neg (by omega)]
  · show 11 * _ + 9 + 2 ≤ 11 * M 3
    simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, e1, e3]
    omega


/-! ## The insertion -/

/-- The memory after an insertion at `p`, outside the scratch registers. -/
def insMem (M : Mem) (A n d p x : ℕ) (z : ℕ) : ℕ :=
  if z = A + n + n + x then x
  else if z = A + n + p ∧ p < d then M 11
  else if z = A + n + p - 1 ∧ 0 < p then M 10
  else if z = A + p then x
  else shiftMem M A n d (d - p) z

theorem wf_insertB : Wf insertB := by
  unfold insertB; rw [shiftLoop_eq]; wf_tac

set_option maxHeartbeats 0 in
/-- **The insertion**, at the level of memory cells. -/
theorem runsTo_insertB {M : Mem} {A n d p x : ℕ} (h1 : M 1 = 1) (h21 : M 21 = n)
    (h22 : M 22 = A) (h23 : M 23 = d) (h25 : M 25 = A + n) (h26 : M 26 = A + n + n)
    (h28 : M 28 = x) (h39 : M 39 = p) (hpd : p ≤ d) (hdn : d < n) (hA : 64 ≤ A) :
    RunsTo insertB (fun m => m = M)
      (fun m => (∀ z, z ∉ [2, 3, 4, 5, 6, 7, 23] → m z = insMem M A n d p x z) ∧
        m 23 = d + 1) (11 * (d - p) + 20) := by
  unfold insertB
  refine RunsTo.mono (T := 1 + (1 + (1 + ((11 * (d - p) + 1) + (1 + (1 + (5 + (1 + (4 + (1 + (1 + (1)))))))))))) ?_ (by omega)
  refine sub_seq (add_seq (sub_seq ?_))
  set M1 := ((M.update 3 (M 23 - M 39)).update 4 ((M.update 3 (M 23 - M 39)) 22 +
    (M.update 3 (M 23 - M 39)) 23)).update 4 (((M.update 3 (M 23 - M 39)).update 4
    ((M.update 3 (M 23 - M 39)) 22 + (M.update 3 (M 23 - M 39)) 23)) 4 -
    ((M.update 3 (M 23 - M 39)).update 4 ((M.update 3 (M 23 - M 39)) 22 +
    (M.update 3 (M 23 - M 39)) 23)) 1) with hM1
  have f1 : ∀ z, z ≠ 3 → z ≠ 4 → M1 z = M z := by
    intro z h3 h4; rw [hM1]; simp (disch := omega) only [Mem.update_of_ne]
  have e3 : M1 3 = d - p := by
    rw [hM1]; simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, h23, h39]
  have e4 : M1 4 = A + d - 1 := by
    rw [hM1]; simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, h22, h23, h1]
  clear_value M1
  refine block_seq (runsTo_shiftLoop (by rw [f1 1 (by omega) (by omega), h1])
    (by rw [f1 21 (by omega) (by omega), h21]) e3 e4 hpd hdn hA) (fun M2 hM2 => ?_)
  obtain ⟨hz2, g1, g21⟩ := hM2
  have g : ∀ z, z ∉ [3, 4, 5, 6, 7] → M2 z = shiftMem M A n d (d - p) z := by
    intro z hz
    rw [hz2 z hz]
    unfold shiftMem
    have hz3 : z ≠ 3 := by intro h; simp [h] at hz
    have hz4 : z ≠ 4 := by intro h; simp [h] at hz
    split_ifs with hin
    · exact f1 _ (by omega) (by omega)
    · exact f1 _ hz3 hz4
  have g22 : M2 22 = A := by rw [g 22 (by simp)]; unfold shiftMem; rw [if_neg (by omega), h22]
  have g23 : M2 23 = d := by rw [g 23 (by simp)]; unfold shiftMem; rw [if_neg (by omega), h23]
  have g25 : M2 25 = A + n := by
    rw [g 25 (by simp)]; unfold shiftMem; rw [if_neg (by omega), h25]
  have g26 : M2 26 = A + n + n := by
    rw [g 26 (by simp)]; unfold shiftMem; rw [if_neg (by omega), h26]
  have g28 : M2 28 = x := by rw [g 28 (by simp)]; unfold shiftMem; rw [if_neg (by omega), h28]
  have g39 : M2 39 = p := by rw [g 39 (by simp)]; unfold shiftMem; rw [if_neg (by omega), h39]
  have g10 : M2 10 = M 10 := by rw [g 10 (by simp)]; unfold shiftMem; rw [if_neg (by omega)]
  have g11 : M2 11 = M 11 := by rw [g 11 (by simp)]; unfold shiftMem; rw [if_neg (by omega)]
  refine add_seq (store_seq ?_)
  set M3 := (M2.update 2 (M2 22 + M2 39)).update ((M2.update 2 (M2 22 + M2 39)) 2)
    ((M2.update 2 (M2 22 + M2 39)) 28) with hM3
  have k : ∀ z, z ≠ 2 → M3 z = if z = A + p then x else M2 z := by
    intro z hz
    rw [hM3]
    simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, g22, g39, g28]
    by_cases hzp : z = A + p
    · subst hzp; rw [Mem.update_self, if_pos rfl]
    · rw [Mem.update_of_ne _ _ hzp, Mem.update_of_ne _ _ hz, if_neg hzp]
  have k1 : M3 1 = 1 := by rw [k 1 (by omega), if_neg (by omega), g1]
  have k23 : M3 23 = d := by rw [k 23 (by omega), if_neg (by omega), g23]
  have k25 : M3 25 = A + n := by rw [k 25 (by omega), if_neg (by omega), g25]
  have k26 : M3 26 = A + n + n := by rw [k 26 (by omega), if_neg (by omega), g26]
  have k28 : M3 28 = x := by rw [k 28 (by omega), if_neg (by omega), g28]
  have k39 : M3 39 = p := by rw [k 39 (by omega), if_neg (by omega), g39]
  have k10 : M3 10 = M 10 := by rw [k 10 (by omega), if_neg (by omega), g10]
  have k11 : M3 11 = M 11 := by rw [k 11 (by omega), if_neg (by omega), g11]
  clear_value M3
  -- the left `lcp`
  refine block_seq (T := 5) (mid := fun M4 => (∀ z, z ≠ 2 → M4 z =
      if z = A + n + p - 1 ∧ 0 < p then M 10 else M3 z)) ?_ (fun M4 hM4 => ?_)
  · by_cases hp : p = 0
    · refine (ifz_eq' (T := 0) (by rw [k39]; exact hp) (nil_last' ?_) (by wf_tac)).mono
        (by omega)
      intro z _; rw [if_neg (by omega)]
    · refine ifz_ne' (T := 3) (by rw [k39]; exact hp) ?_ Algo.ExplLinear.wf_nil
      rt
      intro z hz
      simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, k25, k39, k1, k10]
      by_cases hzp : z = A + n + p - 1
      · subst hzp; rw [Mem.update_self, if_pos ⟨rfl, by omega⟩]
      · rw [Mem.update_of_ne _ _ hzp, if_neg (by omega)]
        simp (disch := omega) only [Mem.update_of_ne]
  have l1 : M4 1 = 1 := by rw [hM4 1 (by omega), if_neg (by omega), k1]
  have l23 : M4 23 = d := by rw [hM4 23 (by omega), if_neg (by omega), k23]
  have l25 : M4 25 = A + n := by rw [hM4 25 (by omega), if_neg (by omega), k25]
  have l26 : M4 26 = A + n + n := by rw [hM4 26 (by omega), if_neg (by omega), k26]
  have l28 : M4 28 = x := by rw [hM4 28 (by omega), if_neg (by omega), k28]
  have l39 : M4 39 = p := by rw [hM4 39 (by omega), if_neg (by omega), k39]
  have l11 : M4 11 = M 11 := by rw [hM4 11 (by omega), if_neg (by omega), k11]
  refine sub_seq ?_
  -- the right `lcp`
  refine block_seq (T := 4) (mid := fun M5 => (∀ z, z ≠ 2 → z ≠ 3 → M5 z =
      if z = A + n + p ∧ p < d then M 11 else M4 z)) ?_ (fun M5 hM5 => ?_)
  · by_cases hp : p < d
    · refine ifz_ne' (T := 2) (by simp (disch := omega) only [Mem.update_self, l23, l39]; omega)
        ?_ Algo.ExplLinear.wf_nil
      rt
      intro z hz hz'
      simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, l25, l39, l11]
      by_cases hzp : z = A + n + p
      · subst hzp; rw [Mem.update_self, if_pos ⟨rfl, hp⟩]
      · rw [Mem.update_of_ne _ _ hzp, if_neg (by omega)]
        simp (disch := omega) only [Mem.update_of_ne]
    · refine (ifz_eq' (T := 0) (by simp (disch := omega) only [Mem.update_self, l23, l39]; omega)
        (nil_last' ?_) (by wf_tac)).mono (by omega)
      intro z hz hz'; rw [if_neg (by omega)]; simp (disch := omega) only [Mem.update_of_ne]
  have n1 : M5 1 = 1 := by rw [hM5 1 (by omega) (by omega), if_neg (by omega), l1]
  have n23 : M5 23 = d := by rw [hM5 23 (by omega) (by omega), if_neg (by omega), l23]
  have n26 : M5 26 = A + n + n := by rw [hM5 26 (by omega) (by omega), if_neg (by omega), l26]
  have n28 : M5 28 = x := by rw [hM5 28 (by omega) (by omega), if_neg (by omega), l28]
  refine add_seq ?_
  refine Algo.ExplLinear.at_mem (fun M6 => M6 2 = A + n + n + x ∧ M6 28 = x ∧
      ∀ z, z ≠ 2 → M6 z = M5 z) ⟨?_, ?_, ?_⟩ (fun M6 hM6 => ?_)
  · rw [Mem.update_self, n26, n28]
  · rw [Mem.update_of_ne _ _ (by decide), n28]
  · intro z hz; rw [Mem.update_of_ne _ _ hz]
  obtain ⟨e2, e28, f6⟩ := hM6
  refine store_seq (add_last ?_)
  rw [e2, e28]
  have hA2 : 64 ≤ A + n + n + x := by omega
  have e23 : (M6.update (A + n + n + x) x) 23 = d := by
    rw [Mem.update_of_ne _ _ (by omega), f6 23 (by decide), n23]
  have e1 : (M6.update (A + n + n + x) x) 1 = 1 := by
    rw [Mem.update_of_ne _ _ (by omega), f6 1 (by decide), n1]
  rw [e23, e1]
  refine ⟨fun z hz => ?_, Mem.update_self _ _ _⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
  rw [Mem.update_of_ne _ _ hz.2.2.2.2.2.2]
  unfold insMem
  by_cases hzx : z = A + n + n + x
  · rw [hzx, Mem.update_self, if_pos rfl]
  · rw [Mem.update_of_ne _ _ hzx, if_neg hzx, f6 z hz.1, hM5 z hz.1 hz.2.1]
    by_cases hr : z = A + n + p ∧ p < d
    · rw [if_pos hr, if_pos hr]
    · rw [if_neg hr, if_neg hr, hM4 z hz.1]
      by_cases hl : z = A + n + p - 1 ∧ 0 < p
      · rw [if_pos hl, if_pos hl]
      · rw [if_neg hl, if_neg hl, k z hz.1]
        by_cases hp : z = A + p
        · rw [if_pos hp, if_pos hp]
        · rw [if_neg hp, if_neg hp, g z (by simp; omega)]


/-! ## The insertion, semantically -/

/-- The list after inserting `x` at `p`. -/
def insL (Dl : List ℕ) (p x : ℕ) : List ℕ := Dl.take p ++ x :: Dl.drop p

theorem length_insL {Dl : List ℕ} {p x : ℕ} (hp : p ≤ Dl.length) :
    (insL Dl p x).length = Dl.length + 1 := by
  simp [insL]; omega

theorem getD_insL {Dl : List ℕ} {p x : ℕ} (hp : p ≤ Dl.length) (j : ℕ) :
    (insL Dl p x).getD j 0 =
      if j < p then Dl.getD j 0 else if j = p then x else Dl.getD (j - 1) 0 := by
  unfold insL
  have htl : (Dl.take p).length = p := by simp; omega
  rw [List.getD_eq_getElem?_getD, List.getElem?_append, htl]
  by_cases h : j < p
  · rw [if_pos h, if_pos h, List.getElem?_take_of_lt h, ← List.getD_eq_getElem?_getD]
  · rw [if_neg h, if_neg h]
    by_cases h2 : j = p
    · subst h2; rw [if_pos rfl]; simp
    · rw [if_neg h2]
      obtain ⟨k, rfl⟩ : ∃ k, j = p + 1 + k := ⟨j - p - 1, by omega⟩
      rw [show p + 1 + k - p = k + 1 by omega, List.getElem?_cons_succ, List.getElem?_drop,
        ← List.getD_eq_getElem?_getD]
      congr 1; omega

theorem tStr_insL {str : ℕ → List ℕ} {Dl : List ℕ} {p x : ℕ} (hp : p ≤ Dl.length) (j : ℕ) :
    tStr str (insL Dl p x) j =
      if j < p then tStr str Dl j else if j = p then str x else tStr str Dl (j - 1) := by
  unfold tStr; rw [getD_insL hp]; split_ifs <;> rfl

/-- **The insertion keeps the sorted list and the `lcp`s.** -/
theorem sortCtx_insert {n SA A : ℕ} {str : ℕ → List ℕ} {Dl : List ℕ} {M m : Mem} {x : ℕ}
    (hS : SortCtx n SA A str Dl M) (hx : x < n)
    (hres : M 39 ≤ Dl.length ∧ (∀ i' < M 39, tStr str Dl i' < str x) ∧
      (∀ i', M 39 ≤ i' → i' < Dl.length → str x < tStr str Dl i') ∧
      (0 < M 39 → M 10 = 2 * lcp (tStr str Dl (M 39 - 1)) (str x)) ∧
      (M 39 < Dl.length → M 11 = 2 * lcp (str x) (tStr str Dl (M 39))))
    (hdn : Dl.length < n)
    (hm : ∀ z, z ∉ [2, 3, 4, 5, 6, 7, 23] → m z = insMem M A n Dl.length (M 39) x z)
    (h23 : m 23 = Dl.length + 1) :
    SortCtx n SA A str (insL Dl (M 39) x) m := by
  obtain ⟨hpd, hlt, hgt, ha, hb⟩ := hres
  set p := M 39 with hpdef
  set d := Dl.length with hddef
  have hA : 64 ≤ A := by have := hS.env.hSA; have := hS.env.hSAn; omega
  have hlen := length_insL (x := x) hpd
  have hT := tStr_insL (str := str) (x := x) hpd
  -- cells outside the region are untouched
  have hout : ∀ z, z ∉ [2, 3, 4, 5, 6, 7, 23] → (z < A ∨ A + n + n + n ≤ z) → m z = M z := by
    intro z hz hr
    rw [hm z hz]; unfold insMem shiftMem
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega)]
  refine ⟨hS.env.of_keep (W := [2, 3, 4, 5, 6, 7, 23]) (a := A) (b := A + n + n + n)
    (fun z hz hr => hout z hz hr) le_rfl (by intro z hz; simp at hz; omega), by rw [h23, hlen],
    ?_, ?_, ?_, ?_⟩
  · -- the array `D`
    intro j hj
    rw [hlen] at hj
    rw [hm _ (by simp; omega), ← List.getD_eq_getElem _ 0, getD_insL hpd]
    unfold insMem shiftMem
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    by_cases hjp : j = p
    · rw [if_pos (by omega), if_neg (by omega), if_pos hjp]
    · rw [if_neg (by omega)]
      by_cases hj' : j < p
      · rw [if_neg (by omega), if_pos hj', (hS.getD (by omega)).1]
      · rw [if_pos (by omega), if_neg hj', if_neg hjp, show A + j - 1 = A + (j - 1) by omega,
          (hS.getD (by omega)).1]
  · intro v hv
    simp only [insL, List.mem_append, List.mem_cons] at hv
    rcases hv with hv | rfl | hv
    · exact hS.dlt v (List.mem_of_mem_take hv)
    · exact hx
    · exact hS.dlt v (List.mem_of_mem_drop hv)
  · -- sorted
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    simp only [List.length_map, hlen] at hi hj
    have ei : (List.map str (insL Dl p x))[i]'(by simp [hlen]; omega) =
        tStr str (insL Dl p x) i := by
      simp only [List.getElem_map, tStr]; rw [List.getD_eq_getElem _ 0 (by omega)]
    have ej : (List.map str (insL Dl p x))[j]'(by simp [hlen]; omega) =
        tStr str (insL Dl p x) j := by
      simp only [List.getElem_map, tStr]; rw [List.getD_eq_getElem _ 0 (by omega)]
    rw [ei, ej, hT, hT]
    have hs := hS.sorted
    split_ifs with h1 h2 h3 h4 h5 h6 h7 h8
    all_goals first
      | exact tStr_lt hs (by omega) (by omega)
      | omega
      | exact hlt _ (by omega)
      | exact hgt _ (by omega) (by omega)
      | exact lt_trans (hlt _ (by omega)) (hgt _ (by omega) (by omega))
      | skip
  · -- the `lcp`s
    intro i hi
    rw [hlen] at hi
    rw [hm _ (by simp; omega), hT, hT]
    unfold insMem shiftMem
    rw [if_neg (by omega)]
    by_cases hr : A + n + i = A + n + p ∧ p < d
    · rw [if_pos hr, hb hr.2, if_neg (by omega), if_pos (by omega), if_neg (by omega),
        if_neg (by omega), show i + 1 - 1 = p by omega]
    · rw [if_neg hr]
      by_cases hl : A + n + i = A + n + p - 1 ∧ 0 < p
      · rw [if_pos hl, ha hl.2, if_pos (by omega), if_neg (by omega), if_pos (by omega)]
        have : i = p - 1 := by omega
        subst this; congr 2
      · rw [if_neg hl, if_neg (by omega)]
        by_cases hin : A + n + d - (d - p) < A + n + i ∧ A + n + i ≤ A + n + d
        · rw [if_pos (Or.inr hin), show A + n + i - 1 = A + n + (i - 1) by omega,
            hS.lcps (i - 1) (by omega), if_neg (by omega), if_neg (by omega),
            if_neg (by omega), if_neg (by omega)]
          congr 2 <;> congr 1 <;> omega
        · rw [if_neg (by omega), hS.lcps i (by omega), if_pos (by omega), if_pos (by omega)]

end TagLin

end Algo
