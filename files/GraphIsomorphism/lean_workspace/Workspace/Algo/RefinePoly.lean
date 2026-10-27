/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: naive vertex-refinement runs in polynomial time.
-/
import Workspace.Algo.RefineRaw
import Workspace.Machine.ListOps3
import Workspace.Machine.ListOps5

/-!
# §4.1.1 — the cost of naive refinement

§4.1.1 (lines 2851–2859): "The cost of round `j` is `O(m)` comparison of colors, where
`m = |E|` … The overall total cost is `O(nk + n²m)`", and with tags the growth of the color
names is avoided.  Row R1 of `Workspace/Algo/DESIGN.md`, item 1.2, asks for this as a statement
about the RAM of `Workspace/Machine/`: the routine of `Workspace/Algo/RefineRaw.lean` is a
`RAM.PolyFun`.

Two remarks on how the bound is proved.

* **The round count arrives as a list.**  `List.range n` for a machine natural `n` is not a
  `RAM.PolyFun`, so the `n²` rounds of the process are counted by the length of
  `Algo.sqFuel`, a list of that length built from the color list by a `map` and a `flatten`.
* **The accumulator bound is proved from an arbitrary start.**  `RAM.PolyFun.foldl` quantifies
  over every start state, so the bound may not use well-formedness of the input.  It does not
  have to: after one round the colors are ranks, hence naturals below the number of vertices,
  whatever the input was (`Algo.rawNewCol_lt`).  This is exactly the paper's point about tags —
  the names of the colors do not grow — and it is what makes the fold affordable.

## Main results

* `Algo.polyFun_lexLtB`, `Algo.polyFun_rankIn` — the comparison and the renaming;
* `Algo.polyFun_rawRefineStep` — one round;
* `Algo.polyFun_rawStableRefine` — the whole process.

No axiom and no `sorry`.
-/

namespace Algo

open RAM

/-! ## The lexicographic comparison -/

theorem polyFun_lexStep : PolyFun lexStep := by
  have hzero : PolyFun (fun s : ℕ × (ℕ × ℕ) => decide (s.1 = 0)) :=
    polyFun_fst.natEq (polyFun_const 0)
  have hlt1 : PolyFun (fun s : ℕ × (ℕ × ℕ) => decide (s.2.1 + 1 ≤ s.2.2)) :=
    ((polyFun_snd.comp polyFun_fst).add (polyFun_const 1)).le (polyFun_snd.comp polyFun_snd)
  have hlt2 : PolyFun (fun s : ℕ × (ℕ × ℕ) => decide (s.2.2 + 1 ≤ s.2.1)) :=
    ((polyFun_snd.comp polyFun_snd).add (polyFun_const 1)).le (polyFun_snd.comp polyFun_fst)
  have hinner : PolyFun (fun s : ℕ × (ℕ × ℕ) =>
      if s.2.1 < s.2.2 then 1 else if s.2.2 < s.2.1 then 2 else 0) := by
    refine (PolyFun.ite hlt1 (polyFun_const 1)
      (PolyFun.ite hlt2 (polyFun_const 2) (polyFun_const 0))).of_eq (fun s => ?_)
    by_cases h1 : s.2.1 < s.2.2
    · simp [h1, Nat.succ_le_iff]
    · by_cases h2 : s.2.2 < s.2.1 <;> simp [h1, h2, Nat.succ_le_iff]
  refine (PolyFun.ite hzero hinner polyFun_fst).of_eq (fun s => ?_)
  by_cases h : s.1 = 0 <;> simp [lexStep, h]

/-- The comparison fold stays in `{0, 1, 2}` unless it never moved. -/
theorem lexFold_small : ∀ (l : List (ℕ × ℕ)) (x : ℕ),
    List.foldl (fun y a => lexStep (y, a)) x l = x ∨
      List.foldl (fun y a => lexStep (y, a)) x l < 3 := by
  intro l
  induction l with
  | nil => intro x; exact Or.inl rfl
  | cons a t ih =>
      intro x
      rw [List.foldl_cons]
      by_cases hx : x = 0
      · subst hx
        have hval : lexStep (0, a) = (if a.1 < a.2 then 1 else if a.2 < a.1 then 2 else 0) :=
          rfl
        have hstep : lexStep (0, a) < 3 := by
          rw [hval]
          split
          · omega
          · split <;> omega
        rcases ih (lexStep (0, a)) with h | h
        · rw [h]; exact Or.inr hstep
        · exact Or.inr h
      · have hstep : lexStep (x, a) = x := by simp [lexStep, hx]
        rw [hstep]
        exact ih x

theorem size_lexFold_le (l : List (ℕ × ℕ)) (x : ℕ) :
    Enc.size (List.foldl (fun y a => lexStep (y, a)) x l) ≤ Enc.size x + 4 := by
  rcases lexFold_small l x with h | h
  · rw [h]; omega
  · have h1 : Enc.size (List.foldl (fun y a => lexStep (y, a)) x l)
        = Nat.size (List.foldl (fun y a => lexStep (y, a)) x l) + 2 := Small.size_nat _
    have h2 : Nat.size (List.foldl (fun y a => lexStep (y, a)) x l) ≤ 2 := by
      refine Nat.size_le.2 ?_
      have h4 : (2 : ℕ) ^ 2 = 4 := by norm_num
      omega
    have h3 := one_le_size x
    omega

theorem polyFun_lexCmp : PolyFun lexCmp := by
  have hacc : ∀ (x : ℕ) (r : List (ℕ × ℕ)) (j : ℕ),
      Enc.size (List.foldl (fun y a => lexStep (y, a)) x (r.take j))
        ≤ (fun m => m + 4) (Enc.size ((x, r) : ℕ × List (ℕ × ℕ))) := by
    intro x r j
    have h1 := size_lexFold_le (r.take j) x
    have h2 : Enc.size x ≤ Enc.size ((x, r) : ℕ × List (ℕ × ℕ)) := Combine.size_fst_le x r
    dsimp only
    omega
  have hfold := PolyFun.foldl polyFun_lexStep (p := fun m => m + 4)
    (polyBound_id.add (polyBound_const 4)) hacc
  have hin : PolyFun (fun p : List ℕ × List ℕ => ((0 : ℕ), p.1.zip p.2)) :=
    (polyFun_const 0).pair polyFun_zip
  exact (hin.comp hfold).of_eq (fun p => rfl)

theorem polyFun_lexLtB : PolyFun lexLtB :=
  (polyFun_lexCmp.natEq (polyFun_const 1)).of_eq (fun p => rfl)

/-! ## The renaming -/

theorem polyFun_rankIn : PolyFun rankIn := by
  have hq : PolyFun (fun z : List ℕ × List ℕ => lexLtB (z.2, z.1)) :=
    polyFun_swap.comp polyFun_lexLtB
  have hfil : PolyFun (fun p : List ℕ × List (List ℕ) =>
      p.2.filter (fun u => lexLtB (u, p.1))) := PolyFun.filterParam hq
  exact ((polyFun_swap.comp hfil).comp polyFun_length).of_eq (fun p => rfl)

/-! ## Counting neighbors by color -/

theorem polyFun_countAt : PolyFun countAt := by
  have hq : PolyFun (fun z : ℕ × ℕ => decide (z.2 = z.1)) :=
    (polyFun_snd.pair polyFun_fst).comp polyFun_natEq
  exact ((PolyFun.filterParam hq).comp polyFun_length).of_eq (fun p => rfl)

theorem polyFun_nbrCols : PolyFun (fun p : List ℕ × List ℕ => nbrCols p.1 p.2) := by
  have hf : PolyFun (fun z : List ℕ × ℕ => z.1.getD z.2 0) :=
    (polyFun_id.pair (polyFun_const 0)).comp polyFun_getD
  exact (PolyFun.mapParam hf).of_eq (fun p => rfl)

theorem polyFun_tallyCols : PolyFun (fun p : List ℕ × List ℕ => tallyCols p.1 p.2) := by
  have hf : PolyFun (fun z : List ℕ × ℕ => countAt (z.2, z.1)) :=
    polyFun_swap.comp polyFun_countAt
  have hin : PolyFun (fun p : List ℕ × List ℕ => (p.2, List.range p.1.length)) :=
    polyFun_snd.pair (polyFun_fst.comp polyFun_rangeLength)
  exact (hin.comp (PolyFun.mapParam hf)).of_eq (fun p => rfl)

theorem polyFun_outNbrs : PolyFun (fun p : List (List ℕ) × ℕ => outNbrs p.1 p.2) :=
  ((polyFun_id.pair (polyFun_const ([] : List ℕ))).comp polyFun_getD).of_eq (fun p => rfl)

theorem polyFun_inNbrs : PolyFun (fun p : List (List ℕ) × ℕ => inNbrs p.1 p.2) := by
  have hq : PolyFun (fun z : ℕ × (List ℕ × ℕ) => decide (z.1 ∈ z.2.1)) :=
    (polyFun_fst.pair (polyFun_snd.comp polyFun_fst)).comp polyFun_natListMem
  have hin : PolyFun (fun p : List (List ℕ) × ℕ => (p.2, p.1.zipIdx)) :=
    polyFun_snd.pair (polyFun_fst.comp polyFun_zipIdx)
  exact ((hin.comp (PolyFun.filterParam hq)).comp (PolyFun.map polyFun_snd)).of_eq
    (fun p => rfl)

/-! ## One round -/

theorem polyFun_tagAt : PolyFun (fun p : RawCD × ℕ => tagAt p.1 p.2) := by
  have hcol : PolyFun (fun p : RawCD × ℕ => p.1.1) := polyFun_fst.comp polyFun_fst
  have hadj : PolyFun (fun p : RawCD × ℕ => p.1.2) := polyFun_fst.comp polyFun_snd
  have hx : PolyFun (fun p : RawCD × ℕ => p.2) := polyFun_snd
  have hhead : PolyFun (fun p : RawCD × ℕ => p.1.1.getD p.2 0) :=
    ((hcol.pair hx).pair (polyFun_const 0)).comp polyFun_getD
  have hout : PolyFun (fun p : RawCD × ℕ =>
      tallyCols p.1.1 (nbrCols p.1.1 (outNbrs p.1.2 p.2))) :=
    hcol.pair ((hcol.pair ((hadj.pair hx).comp polyFun_outNbrs)).comp polyFun_nbrCols)
      |>.comp polyFun_tallyCols
  have hin : PolyFun (fun p : RawCD × ℕ =>
      tallyCols p.1.1 (nbrCols p.1.1 (inNbrs p.1.2 p.2))) :=
    hcol.pair ((hcol.pair ((hadj.pair hx).comp polyFun_inNbrs)).comp polyFun_nbrCols)
      |>.comp polyFun_tallyCols
  exact (hhead.pair ((hout.pair hin).comp polyFun_append)).comp polyFun_cons
    |>.of_eq (fun p => rfl)

theorem polyFun_rawTags : PolyFun rawTags := by
  have hin : PolyFun (fun X : RawCD => (X, List.range X.1.length)) :=
    polyFun_id.pair (polyFun_fst.comp polyFun_rangeLength)
  exact (hin.comp (PolyFun.mapParam polyFun_tagAt)).of_eq (fun X => rfl)

theorem polyFun_rawColorSet : PolyFun rawColorSet :=
  ((polyFun_nil.pair polyFun_rawTags).comp
    (polyFun_dedupG (α := List ℕ) polyFun_listNatEq)).of_eq (fun X => rfl)

theorem polyFun_rawNewCol : PolyFun rawNewCol := by
  have hin : PolyFun (fun X : RawCD => (rawColorSet X, rawTags X)) :=
    polyFun_rawColorSet.pair polyFun_rawTags
  exact (hin.comp (PolyFun.mapParam polyFun_rankIn)).of_eq (fun X => rfl)

/-- **One round of naive vertex-refinement runs in polynomial time.** -/
theorem polyFun_rawRefineStep : PolyFun rawRefineStep :=
  (polyFun_rawNewCol.pair polyFun_snd).of_eq (fun X => rfl)

/-! ## The process

The fold runs the round `n²` times.  `RAM.PolyFun.foldl` asks for a bound on the state from an
**arbitrary** start, which is available because one round makes the colors ranks. -/

theorem polyFun_sqFuel : PolyFun sqFuel := by
  have hf : PolyFun (fun z : List ℕ × ℕ => z.1) := polyFun_fst
  have hin : PolyFun (fun col : List ℕ => (col, col)) := polyFun_id.pair polyFun_id
  exact ((hin.comp (PolyFun.mapParam hf)).comp polyFun_flatten).of_eq (fun col => rfl)

theorem iterate_fst_length (X : RawCD) :
    ∀ j : ℕ, (rawRefineStep^[j] X).1.length = X.1.length
  | 0 => rfl
  | j + 1 => by
      rw [Function.iterate_succ_apply', rawRefineStep_fst_length, iterate_fst_length X j]

theorem iterate_fst_lt (X : RawCD) (j : ℕ) {a : ℕ}
    (h : a ∈ (rawRefineStep^[j + 1] X).1) : a < X.1.length := by
  rw [Function.iterate_succ_apply'] at h
  have := rawNewCol_lt (X := rawRefineStep^[j] X) h
  rw [iterate_fst_length X j] at this
  exact this

theorem size_iterate_le (X : RawCD) (N : ℕ) (hN : Enc.size X ≤ N) :
    ∀ j : ℕ, Enc.size (rawRefineStep^[j] X) ≤ N + (2 * (1 + N * (2 * N + 5)) + 2 * N) := by
  intro j
  have hlenN : X.1.length ≤ N := by
    have h1 : X.1.length ≤ Enc.size X.1 := length_le_size _
    have h2 : Enc.size X.1 ≤ Enc.size X := size_fst_le' X
    omega
  match j with
  | 0 => simpa using (by omega : Enc.size X ≤ N + (2 * (1 + N * (2 * N + 5)) + 2 * N))
  | j + 1 =>
      set Y := rawRefineStep^[j + 1] X with hY
      have hlen : Y.1.length = X.1.length := iterate_fst_length X (j + 1)
      have hentry : ∀ a ∈ Y.1, Enc.size a ≤ N + 2 := by
        intro a ha
        have h1 : a < X.1.length := iterate_fst_lt X j (h := ha)
        have h2 : Enc.size a = Nat.size a + 2 := Small.size_nat a
        have h3 : Nat.size a ≤ a := size_le_self a
        omega
      have hcol : Enc.size Y.1 ≤ 1 + N * (2 * (N + 2) + 1) := by
        have h := size_list_le_of_entries Y.1 (N + 2) hentry
        have h2 : Y.1.length * (2 * (N + 2) + 1) ≤ N * (2 * (N + 2) + 1) :=
          Nat.mul_le_mul_right _ (by omega)
        omega
      have hsnd : Y.2 = X.2 := snd_iterate X (j + 1)
      have hsnd2 : Enc.size Y.2 ≤ N := by
        rw [hsnd]
        have := size_snd_le' X
        omega
      have hpair : Enc.size Y ≤ 2 * Enc.size Y.1 + 2 * Enc.size Y.2 := size_pair_le' Y
      have harith : 1 + N * (2 * (N + 2) + 1) ≤ 1 + N * (2 * N + 5) := by
        have : N * (2 * (N + 2) + 1) ≤ N * (2 * N + 5) := Nat.mul_le_mul_left _ (by omega)
        omega
      omega

/-- **The stable refinement runs in polynomial time.**  Row R1 of
`Workspace/Algo/DESIGN.md`, item 1.2. -/
theorem polyFun_rawStableRefine : PolyFun rawStableRefine := by
  have hstep : PolyFun (fun q : RawCD × ℕ => rawRefineStep q.1) :=
    polyFun_fst.comp polyFun_rawRefineStep
  have hacc : ∀ (x : RawCD) (r : List ℕ) (j : ℕ),
      Enc.size (List.foldl (fun y a => (fun q : RawCD × ℕ => rawRefineStep q.1) (y, a))
          x (r.take j))
        ≤ (fun m => m + (2 * (1 + m * (2 * m + 5)) + 2 * m))
            (Enc.size ((x, r) : RawCD × List ℕ)) := by
    intro x r j
    have hx : Enc.size x ≤ Enc.size ((x, r) : RawCD × List ℕ) := Combine.size_fst_le x r
    have hfold : List.foldl (fun y a => (fun q : RawCD × ℕ => rawRefineStep q.1) (y, a))
        x (r.take j) = rawRefineStep^[(r.take j).length] x := foldl_const_eq_iterate_gen _ _
    rw [hfold]
    exact size_iterate_le x _ hx _
  have hfold := PolyFun.foldl hstep
    (p := fun m => m + (2 * (1 + m * (2 * m + 5)) + 2 * m))
    (polyBound_id.add (((polyBound_const 2).mul ((polyBound_const 1).add
      (polyBound_id.mul (((polyBound_const 2).mul polyBound_id).add
        (polyBound_const 5))))).add ((polyBound_const 2).mul polyBound_id)))
    hacc
  have hin : PolyFun (fun X : RawCD => (X, sqFuel X.1)) :=
    polyFun_id.pair (polyFun_fst.comp polyFun_sqFuel)
  exact (hin.comp hfold).of_eq (fun X => rfl)

end Algo
