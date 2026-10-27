import Workspace.Machine.ListOps2

/-!
# Flattening, and duplicate-free insertion

`Workspace/Machine/ListOps.lean` and `Workspace/Machine/ListOps2.lean` build the fold and the
traversals.  This file adds the two combinators that a *closure loop* needs, and nothing else.

* **Flattening.**  A round of a closure loop produces, for every point found so far, the list of
  its images under all the generators.  That is a list of lists, and it has to be made into a
  list again.  `RAM.polyFun_flatten` does it, and `RAM.PolyFun.flatMapParam` packages the usual
  combination "map with a parameter, then flatten".
* **Duplicate-free insertion.**  A round must add only the points that are new.  `RAM.dedupInto`
  folds a list into an accumulator, keeping an entry only when it is not there yet.

The only real work is, as always, the bound on the accumulator, because `RAM.PolyFun.foldl` will
not take a fold whose accumulator may grow.  For `RAM.dedupInto` the bound is not obvious: the
fold is run from an **arbitrary** start accumulator, so nothing may be assumed about it.  What
saves the bound is `RAM.dedupInto_struct`: whatever the start accumulator `x` is, the answer is
`e ++ x` for a list `e` that has no repetition and whose entries all come from the list being
folded in.  So `e` is no longer than that list, and the whole answer is quadratically bounded.

## Main results

* sizes: `RAM.length_flatten_le_size`, `RAM.size_flatten_le`;
* flattening: `RAM.polyFun_flatten`, `RAM.PolyFun.flatMapParam`;
* insertion: `RAM.dedupInto`, `RAM.mem_dedupInto`, `RAM.dedupInto_struct`,
  `RAM.polyFun_dedupInto`.
-/

namespace RAM

variable {α β γ : Type*}

/-! ## Sizes of a flattened list

Two facts.  The flattened list is no longer than the encoding of the list of lists, because each
of its entries occupies at least one register there; and each of its entries is no larger than
the whole list, by `RAM.size_mem_le` applied twice. -/

/-- The flattened list is no longer than the encoding of the list of lists. -/
theorem length_flatten_le_size [Enc α] : ∀ l : List (List α), l.flatten.length ≤ Enc.size l := by
  intro l
  induction l with
  | nil =>
      have h : Enc.size ([] : List (List α)) = 1 := size_nil
      simp only [List.flatten_nil, List.length_nil]
      omega
  | cons a t ih =>
      rw [List.flatten_cons, List.length_append]
      have h1 : a.length ≤ Enc.size a := length_le_size a
      have h2 : Enc.size (a :: t) = listSize (frame (Enc.encode a)) + Enc.size t - 1 :=
        size_cons_eq a t
      have h3 : listSize (frame (Enc.encode a))
          = Enc.size a + (Nat.size (Enc.encode a).length + 1) := listSize_frame _
      have h4 := one_le_size t
      omega

/-- The size of a flattened list, quadratically in the size of the list of lists. -/
theorem size_flatten_le [Enc α] (l : List (List α)) :
    Enc.size l.flatten ≤ 1 + Enc.size l * (2 * Enc.size l + 1) := by
  have hentry : ∀ a ∈ l.flatten, Enc.size a ≤ Enc.size l := by
    intro a ha
    rw [List.mem_flatten] at ha
    obtain ⟨u, hu, hau⟩ := ha
    exact le_trans (size_mem_le hau) (size_mem_le hu)
  have h := size_list_le_of_entries l.flatten (Enc.size l) hentry
  have h2 := length_flatten_le_size l
  have h3 : l.flatten.length * (2 * Enc.size l + 1) ≤ Enc.size l * (2 * Enc.size l + 1) :=
    Nat.mul_le_mul_right _ h2
  omega

/-! ## Flattening

`List.flatten` is the fold that appends every entry to the accumulator.  Both the closed form and
the bound are one line each, given the two size facts above. -/

/-- **The closed form** of the fold that appends. -/
theorem foldl_append_eq {α : Type*} : ∀ (l : List (List α)) (x : List α),
    List.foldl (fun y a => y ++ a) x l = x ++ l.flatten := by
  intro l
  induction l with
  | nil => intro x; simp
  | cons a t ih =>
      intro x
      rw [List.foldl_cons, ih, List.flatten_cons, List.append_assoc]

/-- **`List.flatten` is a `PolyFun`.** -/
theorem polyFun_flatten [Enc α] : PolyFun (fun l : List (List α) => l.flatten) := by
  have hacc : ∀ (x : List α) (r : List (List α)) (j : ℕ),
      Enc.size (List.foldl (fun y a => (fun p : List α × List α => p.1 ++ p.2) (y, a))
          x (r.take j))
        ≤ (fun m => m + (1 + m * (2 * m + 1)))
            (Enc.size ((x, r) : List α × List (List α))) := by
    intro x r j
    show Enc.size (List.foldl (fun y a => y ++ a) x (r.take j)) ≤ _
    rw [foldl_append_eq]
    set N := Enc.size ((x, r) : List α × List (List α)) with hN
    have hx : Enc.size x ≤ N := Combine.size_fst_le x r
    have hr : Enc.size r ≤ N := Combine.size_snd_le x r
    have hrt : Enc.size (r.take j) ≤ Enc.size r := size_take_le j r
    have happ := size_append_le x ((r.take j).flatten)
    have hf := size_flatten_le (r.take j)
    have hmono : Enc.size (r.take j) * (2 * Enc.size (r.take j) + 1) ≤ N * (2 * N + 1) :=
      Nat.mul_le_mul (by omega) (by omega)
    dsimp only
    omega
  have hfold := PolyFun.foldl (α := List α) (σ := List α) polyFun_append
    (p := fun m => m + (1 + m * (2 * m + 1)))
    (polyBound_id.add ((polyBound_const 1).add
      (polyBound_id.mul (((polyBound_const 2).mul polyBound_id).add (polyBound_const 1)))))
    hacc
  have hin : PolyFun (fun l : List (List α) => (([] : List α), l)) := polyFun_nil.pair polyFun_id
  refine (hin.comp hfold).of_eq (fun l => ?_)
  show List.foldl (fun y a => y ++ a) ([] : List α) l = l.flatten
  rw [foldl_append_eq, List.nil_append]

/-- **Map with a parameter, then flatten.**  This is `flatMap` with the first argument of the
function held fixed, written in the form the closure loops of `Workspace/Algo/` use. -/
theorem PolyFun.flatMapParam [Enc α] [Enc β] [Enc γ] {f : γ × α → List β} (hf : PolyFun f) :
    PolyFun (fun p : γ × List α => (p.2.map (fun a => f (p.1, a))).flatten) :=
  (PolyFun.mapParam hf).comp polyFun_flatten

/-! ## Duplicate-free insertion

One round keeps the accumulator when the entry is already there, and conses it on otherwise.  So
the answer is always of the form `e ++ x`, where `x` is the start accumulator and `e` collects
the entries that were new.  That is `RAM.dedupInto_struct`, and everything else follows from
it. -/

/-- One round: add the entry unless it is already there. -/
def insertNew (s : List ℕ × ℕ) : List ℕ := if s.2 ∈ s.1 then s.1 else s.2 :: s.1

/-- **Fold a list into an accumulator, keeping only the entries that are new.** -/
def dedupInto (p : List ℕ × List ℕ) : List ℕ :=
  List.foldl (fun y a => insertNew (y, a)) p.1 p.2

/-- **What is in the answer**: the accumulator and the list, and nothing else. -/
theorem mem_dedupInto : ∀ (l acc : List ℕ) (k : ℕ),
    k ∈ List.foldl (fun y a => insertNew (y, a)) acc l ↔ k ∈ acc ∨ k ∈ l := by
  intro l
  induction l with
  | nil => intro acc k; simp
  | cons a t ih =>
      intro acc k
      rw [List.foldl_cons]
      by_cases ha : a ∈ acc
      · have h : insertNew (acc, a) = acc := by simp [insertNew, ha]
        rw [h, ih acc k]
        constructor
        · rintro (h1 | h1)
          · exact Or.inl h1
          · exact Or.inr (List.mem_cons_of_mem a h1)
        · rintro (h1 | h1)
          · exact Or.inl h1
          · rcases List.mem_cons.1 h1 with rfl | h2
            · exact Or.inl ha
            · exact Or.inr h2
      · have h : insertNew (acc, a) = a :: acc := by simp [insertNew, ha]
        rw [h, ih (a :: acc) k]
        constructor
        · rintro (h1 | h1)
          · rcases List.mem_cons.1 h1 with rfl | h2
            · exact Or.inr (List.mem_cons_self ..)
            · exact Or.inl h2
          · exact Or.inr (List.mem_cons_of_mem a h1)
        · rintro (h1 | h1)
          · exact Or.inl (List.mem_cons_of_mem a h1)
          · rcases List.mem_cons.1 h1 with rfl | h2
            · exact Or.inl (List.mem_cons_self ..)
            · exact Or.inr h2

/-- **The shape of the answer.**  Whatever the start accumulator `x`, the fold returns `e ++ x`
with `e` free of repetitions, disjoint from `x`, and contained in the list folded in.  This is
what bounds the accumulator, and what a closure loop needs to count its points. -/
theorem dedupInto_struct : ∀ (l acc : List ℕ),
    ∃ e : List ℕ, List.foldl (fun y a => insertNew (y, a)) acc l = e ++ acc ∧ e.Nodup ∧
      (∀ k ∈ e, k ∉ acc) ∧ (∀ k ∈ e, k ∈ l) := by
  intro l
  induction l with
  | nil => intro acc; exact ⟨[], by simp, by simp, by simp, by simp⟩
  | cons a t ih =>
      intro acc
      rw [List.foldl_cons]
      by_cases ha : a ∈ acc
      · have h : insertNew (acc, a) = acc := by simp [insertNew, ha]
        rw [h]
        obtain ⟨e, he, hnd, hne, hmem⟩ := ih acc
        exact ⟨e, he, hnd, hne, fun k hk => List.mem_cons_of_mem a (hmem k hk)⟩
      · have h : insertNew (acc, a) = a :: acc := by simp [insertNew, ha]
        rw [h]
        obtain ⟨e, he, hnd, hne, hmem⟩ := ih (a :: acc)
        have hanotin : a ∉ e := fun hae => (hne a hae) (List.mem_cons_self ..)
        refine ⟨e ++ [a], ?_, ?_, ?_, ?_⟩
        · rw [he, List.append_assoc]; rfl
        · rw [List.nodup_append]
          refine ⟨hnd, by simp, ?_⟩
          intro b hb c hc
          rw [List.mem_singleton] at hc
          subst hc
          intro hbc
          exact hanotin (hbc ▸ hb)
        · intro k hk
          rcases List.mem_append.1 hk with hk1 | hk1
          · exact fun hkacc => (hne k hk1) (List.mem_cons_of_mem a hkacc)
          · rw [List.mem_singleton] at hk1; exact hk1 ▸ ha
        · intro k hk
          rcases List.mem_append.1 hk with hk1 | hk1
          · exact List.mem_cons_of_mem a (hmem k hk1)
          · rw [List.mem_singleton] at hk1; exact hk1 ▸ List.mem_cons_self ..

theorem polyFun_insertNew : PolyFun insertNew := by
  refine (PolyFun.ite ((polyFun_snd.pair polyFun_fst).comp polyFun_natListMem)
    polyFun_fst ((polyFun_snd.pair polyFun_fst).comp polyFun_cons)).of_eq (fun s => ?_)
  by_cases h : s.2 ∈ s.1 <;> simp [insertNew, h]

/-- **Duplicate-free insertion is a `PolyFun`.** -/
theorem polyFun_dedupInto : PolyFun dedupInto := by
  have hacc : ∀ (x : List ℕ) (r : List ℕ) (j : ℕ),
      Enc.size (List.foldl (fun y a => insertNew (y, a)) x (r.take j))
        ≤ (fun m => m + (1 + m * (2 * m + 1))) (Enc.size ((x, r) : List ℕ × List ℕ)) := by
    intro x r j
    obtain ⟨e, he, hnd, _, hmem⟩ := dedupInto_struct (r.take j) x
    rw [he]
    set N := Enc.size ((x, r) : List ℕ × List ℕ) with hN
    have hx : Enc.size x ≤ N := Combine.size_fst_le x r
    have hr : Enc.size r ≤ N := Combine.size_snd_le x r
    have hrt : Enc.size (r.take j) ≤ Enc.size r := size_take_le j r
    have hsub : e ⊆ r.take j := fun k hk => hmem k hk
    have hlen : e.length ≤ (r.take j).length :=
      List.Subperm.length_le (List.subperm_of_subset hnd hsub)
    have hlen2 : (r.take j).length ≤ N := by
      have h1 : (r.take j).length ≤ Enc.size (r.take j) := length_le_size _
      omega
    have hentry : ∀ k ∈ e, Enc.size k ≤ N := by
      intro k hk
      have h1 : Enc.size k ≤ Enc.size (r.take j) := size_mem_le (hmem k hk)
      omega
    have hsize := size_list_le_of_entries e N hentry
    have hmul : e.length * (2 * N + 1) ≤ N * (2 * N + 1) :=
      Nat.mul_le_mul_right _ (by omega)
    have happ := size_append_le e x
    dsimp only
    omega
  have hfold := PolyFun.foldl polyFun_insertNew
    (p := fun m => m + (1 + m * (2 * m + 1)))
    (polyBound_id.add ((polyBound_const 1).add
      (polyBound_id.mul (((polyBound_const 2).mul polyBound_id).add (polyBound_const 1)))))
    hacc
  exact hfold.of_eq (fun p => rfl)

end RAM
