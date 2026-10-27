/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Machine layer: duplicate-free insertion at an arbitrary entry type.
-/
import Workspace.Machine.ListOps3

/-!
# Duplicate-free insertion, for any entry type

`RAM.dedupInto` of `Workspace/Machine/ListOps3.lean` folds a list of **naturals** into an
accumulator, keeping only the entries that are new.  Naive refinement (§4.1.1 of the paper)
needs the same routine one type up: its entries are the *tags* of the vertices, which are
lists of naturals.

Nothing about the proof of `RAM.dedupInto` uses the entry type, so this file repeats it with
the type as a parameter.  The only extra hypothesis is a `RAM.PolyFun` test for equality of
two entries, which is exactly what `RAM.polyFun_listMem` asks for.

## Main definitions and results

* `RAM.insertNewG`, `RAM.dedupG` — the round and the fold;
* `RAM.mem_dedupG` — what is in the answer;
* `RAM.dedupG_struct` — the shape of the answer, which is what bounds the accumulator;
* `RAM.nodup_dedupG`, `RAM.length_dedupG_le` — the two facts a caller wants;
* `RAM.polyFun_dedupG` — the routine runs in polynomial time.

No axiom and no `sorry`.
-/

namespace RAM

variable {α : Type*}

/-- One round: add the entry unless it is already there. -/
def insertNewG [DecidableEq α] (s : List α × α) : List α :=
  if s.2 ∈ s.1 then s.1 else s.2 :: s.1

/-- **Fold a list into an accumulator, keeping only the entries that are new.** -/
def dedupG [DecidableEq α] (p : List α × List α) : List α :=
  List.foldl (fun y a => insertNewG (y, a)) p.1 p.2

/-- **What is in the answer**: the accumulator and the list, and nothing else. -/
theorem mem_dedupG [DecidableEq α] : ∀ (l acc : List α) (k : α),
    k ∈ List.foldl (fun y a => insertNewG (y, a)) acc l ↔ k ∈ acc ∨ k ∈ l := by
  intro l
  induction l with
  | nil => intro acc k; simp
  | cons a t ih =>
      intro acc k
      rw [List.foldl_cons]
      by_cases ha : a ∈ acc
      · have h : insertNewG (acc, a) = acc := by simp [insertNewG, ha]
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
      · have h : insertNewG (acc, a) = a :: acc := by simp [insertNewG, ha]
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

/-- **The shape of the answer.**  Whatever the start accumulator `acc` is, the fold returns
`e ++ acc` with `e` free of repetitions, disjoint from `acc`, and contained in the list folded
in.  This is what bounds the accumulator. -/
theorem dedupG_struct [DecidableEq α] : ∀ (l acc : List α),
    ∃ e : List α, List.foldl (fun y a => insertNewG (y, a)) acc l = e ++ acc ∧ e.Nodup ∧
      (∀ k ∈ e, k ∉ acc) ∧ (∀ k ∈ e, k ∈ l) := by
  intro l
  induction l with
  | nil => intro acc; exact ⟨[], by simp, by simp, by simp, by simp⟩
  | cons a t ih =>
      intro acc
      rw [List.foldl_cons]
      by_cases ha : a ∈ acc
      · have h : insertNewG (acc, a) = acc := by simp [insertNewG, ha]
        rw [h]
        obtain ⟨e, he, hnd, hne, hmem⟩ := ih acc
        exact ⟨e, he, hnd, hne, fun k hk => List.mem_cons_of_mem a (hmem k hk)⟩
      · have h : insertNewG (acc, a) = a :: acc := by simp [insertNewG, ha]
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

/-- **Membership in the deduplicated list**, from the empty accumulator. -/
theorem mem_dedupG_nil [DecidableEq α] (l : List α) (k : α) :
    k ∈ dedupG (([] : List α), l) ↔ k ∈ l := by
  rw [dedupG, mem_dedupG]
  simp

/-- **The deduplicated list has no repetition.** -/
theorem nodup_dedupG [DecidableEq α] (l : List α) : (dedupG (([] : List α), l)).Nodup := by
  obtain ⟨e, he, hnd, -, -⟩ := dedupG_struct l ([] : List α)
  rw [dedupG, he]
  simpa using hnd

/-- **The deduplicated list is no longer than the list.** -/
theorem length_dedupG_le [DecidableEq α] (l : List α) :
    (dedupG (([] : List α), l)).length ≤ l.length := by
  obtain ⟨e, he, hnd, -, hmem⟩ := dedupG_struct l ([] : List α)
  have hsub : e ⊆ l := fun k hk => hmem k hk
  have := List.Subperm.length_le (List.subperm_of_subset hnd hsub)
  rw [dedupG, he]
  simpa using this

theorem polyFun_insertNewG [Enc α] [DecidableEq α]
    (heq : PolyFun (fun q : α × α => decide (q.1 = q.2))) : PolyFun (insertNewG (α := α)) := by
  refine (PolyFun.ite ((polyFun_snd.pair polyFun_fst).comp (polyFun_listMem heq))
    polyFun_fst ((polyFun_snd.pair polyFun_fst).comp polyFun_cons)).of_eq (fun s => ?_)
  by_cases h : s.2 ∈ s.1 <;> simp [insertNewG, h]

/-- **Duplicate-free insertion is a `PolyFun`**, at any entry type with a `PolyFun` equality
test. -/
theorem polyFun_dedupG [Enc α] [DecidableEq α]
    (heq : PolyFun (fun q : α × α => decide (q.1 = q.2))) : PolyFun (dedupG (α := α)) := by
  have hacc : ∀ (x : List α) (r : List α) (j : ℕ),
      Enc.size (List.foldl (fun y a => insertNewG (y, a)) x (r.take j))
        ≤ (fun m => m + (1 + m * (2 * m + 1))) (Enc.size ((x, r) : List α × List α)) := by
    intro x r j
    obtain ⟨e, he, hnd, -, hmem⟩ := dedupG_struct (r.take j) x
    rw [he]
    set N := Enc.size ((x, r) : List α × List α) with hN
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
  have hfold := PolyFun.foldl (polyFun_insertNewG heq)
    (p := fun m => m + (1 + m * (2 * m + 1)))
    (polyBound_id.add ((polyBound_const 1).add
      (polyBound_id.mul (((polyBound_const 2).mul polyBound_id).add (polyBound_const 1)))))
    hacc
  exact hfold.of_eq (fun p => rfl)

end RAM
