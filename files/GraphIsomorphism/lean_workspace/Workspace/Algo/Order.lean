/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: the order of a permutation group given by generators.
-/
import Workspace.Algo.ChainBuildPoly
import Workspace.Machine.Mul

/-!
# The order of a permutation group

`Algo.card_eq_prod_row_card_buildTable` says that `|⟨gens⟩|` is the product, over the levels,
of the number of filled positions in the corresponding row of the table built by the closure
loop.  On raw data a row is stored as an association list whose keys are pairwise distinct
(the shape invariant `Algo.Shape`), so "the number of filled positions" is simply the length
of the stored row, and the order is the product of the row lengths.

This is the class-D row "the order `|G|`" of `Workspace/Algo/DESIGN.md`, item 2, which
Procedure Reduce-to-Johnson (lines 2 and 5 of §11.3) needs.

## Why the product is short

`Algo.rawOrder` multiplies at most `n` numbers, each at most `n`, so it is at most `n^n`: a
number with `O(n log n)` bits, which is polynomial in the input size but *not* polynomial as a
value.  The bound for `RAM.PolyFun.foldl` is therefore proved on `Nat.size` of the accumulator
and uses `RAM.size_mul_le` — this is the "big-number arithmetic" of risk R1 in
`Workspace/Algo/DESIGN.md`, and it is the reason the routine needs `RAM.polyFun_mul` rather
than repeated addition.

## Main definitions and results

* `Algo.rawOrder` — the routine;
* `Algo.rawOrder_spec` — it computes `Nat.card (Algo.genGroup gens)`;
* `Algo.polyFun_rawOrder` — it runs in polynomial time.

No axiom and no `sorry`.
-/

namespace Algo

open RAM RAM.Targets
open Equiv (Perm)

variable {n : ℕ}

/-! ## A row's length is the number of its filled positions -/

theorem lookup_ne_none_iff {α β : Type*} [BEq α] [LawfulBEq α] :
    ∀ (l : List (α × β)) (a : α), l.lookup a ≠ none ↔ a ∈ l.map Prod.fst := by
  intro l
  induction l with
  | nil => intro a; simp [List.lookup]
  | cons q t ih =>
      intro a
      obtain ⟨k, v⟩ := q
      by_cases hk : a = k
      · subst hk
        simp [List.lookup]
      · have hbeq : (a == k) = false := by simpa using hk
        rw [List.map_cons, List.mem_cons]
        simp only [List.lookup, hbeq, cond_false]
        rw [ih a]
        simp [hk]

/-- **The number of filled positions in a row is the length of the stored row.**  This uses
both halves of the shape invariant: the keys are pairwise distinct, so no position is counted
twice, and they are below `n`, so none of them falls outside `Finset.range n`. -/
theorem card_row_eq_length {M : MTable n} (h : Shape n M) (i : ℕ) :
    (row (tableOf M) i).card = (M.getD i ([] : MRow n)).length := by
  classical
  rcases getD_mem_or_nil M i with hmem | hnil
  · have hnd : ((M.getD i ([] : MRow n)).map Prod.fst).Nodup := h.nodup _ hmem
    have hkeys : ∀ q ∈ M.getD i ([] : MRow n), q.1 < n := h.keys _ hmem
    have hset : row (tableOf M) i = ((M.getD i ([] : MRow n)).map Prod.fst).toFinset := by
      ext j
      rw [mem_row, List.mem_toFinset]
      constructor
      · rintro ⟨-, hj⟩
        exact (lookup_ne_none_iff _ j).1 hj
      · intro hj
        obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hj
        exact ⟨hkeys q hq, (lookup_ne_none_iff _ q.1).2 (List.mem_map.2 ⟨q, hq, rfl⟩)⟩
    rw [hset, List.toFinset_card_of_nodup hnd, List.length_map]
  · have hnone : ∀ j : ℕ, tableOf M i j = none := by
      intro j
      rw [tableOf, hnil]
      rfl
    have hempty : row (tableOf M) i = ∅ := by
      ext j
      constructor
      · intro hj
        rw [mem_row] at hj
        exact absurd (hnone j) hj.2
      · intro hj
        exact absurd hj (by simp)
    rw [hempty, hnil, Finset.card_empty, List.length_nil]

/-! ## The product over the levels is the product of the row lengths -/

theorem prod_range_eq_list_prod {M : Type*} [CommMonoid M] (f : ℕ → M) : ∀ m : ℕ,
    ∏ i ∈ Finset.range m, f i = ((List.range m).map f).prod := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.prod_range_succ, ih, List.range_succ, List.map_append, List.prod_append]
      simp

theorem map_range_length_eq {α : Type*} (l : List (List α)) :
    (List.range l.length).map (fun i => (l.getD i []).length) = l.map List.length := by
  refine List.ext_getElem (by simp) ?_
  intro k h1 h2
  have hk : k < l.length := by simpa using h1
  rw [List.getElem_map, List.getElem_range, List.getElem_map, List.getD_eq_getElem _ _ hk]

/-- **The order as a product of row lengths**, on a stored table with the shape invariant. -/
theorem prod_row_card_eq_prod_lengths {M : MTable n} (h : Shape n M) (hlen : M.length = n) :
    ∏ i ∈ Finset.range n, (row (tableOf M) i).card = (M.map List.length).prod := by
  have hr : List.range n = List.range M.length := by rw [hlen]
  have hmap : ((List.range M.length).map (fun i => (row (tableOf M) i).card))
      = (List.range M.length).map (fun i => (M.getD i ([] : MRow n)).length) :=
    List.map_congr_left (fun i _ => card_row_eq_length h i)
  rw [prod_range_eq_list_prod, hr, hmap, map_range_length_eq]

theorem length_buildTable (n : ℕ) (gens : List (Perm (Fin n))) :
    (buildTable n gens).length = n :=
  length_buildRound_iterate _ _ _ (length_initTable n)

/-- **The order of `⟨gens⟩` is the product of the row lengths of the table built.** -/
theorem card_genGroup_eq_prod_lengths (n : ℕ) (gens : List (Perm (Fin n))) :
    Nat.card (genGroup gens) = ((buildTable n gens).map List.length).prod := by
  rw [card_eq_prod_row_card_buildTable n gens,
    prod_row_card_eq_prod_lengths (shape_buildTable n gens) (length_buildTable n gens)]

/-! ## The routine -/

/-- **The order of a permutation group given by generators.**  `dom` is a domain witness: any
list of length `n`. -/
def rawOrder (p : List ℕ × List RawPerm) : ℕ :=
  List.foldl (fun a row => a * row.length) 1 (rawBuildTable p)

theorem map_length_encMTable (n : ℕ) (M : MTable n) :
    (encMTable n M).map List.length = M.map List.length := by
  rw [encMTable, List.map_map]
  exact List.map_congr_left (fun row _ => List.length_map ..)

theorem foldl_mul_length_eq {α : Type*} (l : List (List α)) :
    List.foldl (fun a row => a * row.length) 1 l = (l.map List.length).prod := by
  rw [← List.foldl_map (f := List.length) (g := fun a m => a * m)]
  exact List.prod_eq_foldl.symm

/-- **The routine computes the order.** -/
theorem rawOrder_spec {n : ℕ} (dom : List ℕ) (hdom : dom.length = n)
    (gens : List (Perm (Fin n))) :
    rawOrder (dom, gens.map (encPerm n)) = Nat.card (genGroup gens) := by
  rw [rawOrder, rawBuildTable_spec dom hdom gens, foldl_mul_length_eq,
    map_length_encMTable, card_genGroup_eq_prod_lengths]

/-! ## The running time

The accumulator of the fold is a *number*, and after `k` rounds it is a product of `k` row
lengths, so as a value it is exponential in the input size.  Its `Nat.size` is not: each factor
contributes at most its own bit length, and `RAM.size_mul_le` adds those up. -/

theorem size_cons_ge {α : Type*} [Enc α] (a : α) (u : List α) :
    Enc.size a + Enc.size u ≤ Enc.size (a :: u) := by
  have h2 : Enc.size (a :: u) = listSize (frame (Enc.encode a)) + Enc.size u - 1 :=
    size_cons_eq a u
  have h3 : listSize (frame (Enc.encode a))
      = Enc.size a + (Nat.size (Enc.encode a).length + 1) := listSize_frame _
  have h4 := one_le_size u
  omega

theorem size_foldl_mul_length_le {α : Type*} [Enc α] : ∀ (l : List (List α)) (x : ℕ),
    Nat.size (List.foldl (fun a row => a * row.length) x l) ≤ Nat.size x + Enc.size l := by
  intro l
  induction l with
  | nil => intro x; rw [List.foldl_nil]; omega
  | cons a t ih =>
      intro x
      rw [List.foldl_cons]
      have h1 := ih (x * a.length)
      have h2 : Nat.size (x * a.length) ≤ Nat.size x + Nat.size a.length := size_mul_le _ _
      have h3 : Nat.size a.length ≤ a.length := size_le_self _
      have h4 : a.length ≤ Enc.size a := length_le_size a
      have h5 := size_cons_ge a t
      omega

theorem polyFun_rawOrder : PolyFun rawOrder := by
  have hstep : PolyFun (fun z : ℕ × RawRow => z.1 * z.2.length) :=
    (polyFun_fst.pair (polyFun_snd.comp polyFun_length)).comp polyFun_mul
  have hacc : ∀ (x : ℕ) (r : List RawRow) (j : ℕ),
      Enc.size (List.foldl (fun a row => a * row.length) x (r.take j))
        ≤ (fun m => 2 * m + 2) (Enc.size ((x, r) : ℕ × List RawRow)) := by
    intro x r j
    set N := Enc.size ((x, r) : ℕ × List RawRow) with hN
    set F := List.foldl (fun a row => a * row.length) x (r.take j) with hF
    have hx : Enc.size x ≤ N := Combine.size_fst_le x r
    have hr : Enc.size r ≤ N := Combine.size_snd_le x r
    have h1 : Nat.size F ≤ Nat.size x + Enc.size (r.take j) :=
      size_foldl_mul_length_le (r.take j) x
    have h2 : Enc.size (r.take j) ≤ Enc.size r := size_take_le j r
    have h3 : Enc.size x = Nat.size x + 2 := Small.size_nat x
    have h4 : Enc.size F = Nat.size F + 2 := Small.size_nat F
    show Enc.size F ≤ 2 * N + 2
    omega
  have hfold := PolyFun.foldl (f := fun z : ℕ × RawRow => z.1 * z.2.length) hstep
    (p := fun m => 2 * m + 2)
    (((polyBound_const 2).mul polyBound_id).add (polyBound_const 2)) hacc
  have hin : PolyFun (fun p : List ℕ × List RawPerm =>
      ((1, rawBuildTable p) : ℕ × List RawRow)) :=
    (polyFun_const 1).pair polyFun_rawBuildTable
  exact (hin.comp hfold).of_eq (fun _ => rfl)

end Algo
