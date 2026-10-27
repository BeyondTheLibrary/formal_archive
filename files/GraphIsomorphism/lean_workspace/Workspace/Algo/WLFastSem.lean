/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

§5.4.2: the trivial bound `O(k²n^{2k+1})` for `k`-ary WL refinement.  The mathematics behind
the fast program: tags as sorted lists, and early stopping.
-/
import Workspace.Algo.WLRaw
import Workspace.Algo.RefineRaw
import Workspace.Refinement.Iterate

/-!
# §5.4.2 — the tags of `k`-ary WL refinement as sorted lists

A round of `Algo.rawWLStep` gives the tuple `t` the tag `c(t) :: (count of v)_v`, the counts of
the tuples `v = (c(tʲ(y)))_j` of old colors, listed over all `v` that occur in lexicographic
order.  That list can be as long as `n^{k+1}`, so a fast program cannot write it.  It writes
instead the string

  `c(t) :: compl(v₁) ++ … ++ compl(v_n)`,

where `v₁ ≤ … ≤ v_n` are the `n` tuples `v` of `t` (one per vertex `y`), sorted, and
`compl(v)` replaces every color `c` by `N - c` (`N` the number of rows).  This file proves that
the strings are ordered like the tags (`Algo.WLFast.cmpRec_tag_iff`), so the new color, the rank
of the tag, is the rank of the string among the strings that occur
(`Algo.WLFast.wlNewCol_eq_denseRank`).

The second half is early stopping: once a round leaves the table unchanged, the process has
reached `rawWLStable`, and this happens within `N` rounds (`Algo.WLFast.rawWLStable_eq_of_fix`,
`Algo.WLFast.exists_fix_le`).

No axiom, no `sorry`.
-/

namespace Algo

namespace WLFast

open Babai

/-! ## Lexicographic order -/

/-- `cmpRec` is the lexicographic order on lists of the same length. -/
theorem cmpRec_eq_one_iff : ∀ {u v : List ℕ}, u.length = v.length → (cmpRec u v = 1 ↔ u < v)
  | [], [], _ => by simp
  | a :: u, b :: v, h => by
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      rw [cmpRec_cons, List.cons_lt_cons_iff, ← cmpRec_eq_one_iff h]
      rcases Nat.lt_trichotomy a b with hab | rfl | hab
      · simp [hab]
      · simp
      · have h1 : ¬ a < b := by omega
        have h2 : a ≠ b := by omega
        simp [h1, hab, h2]

/-! ## Count vectors and sorted lists

For a multiset over a finite ordered universe `U`, the list of counts over `U` (in increasing
order) and the sorted list of the elements carry the same information, and the lexicographic
orders are reversed: more copies of the smallest element where the counts differ is a larger
count vector, but a smaller sorted list. -/

section Counts

variable {α : Type*} [LinearOrder α]

/-- A sorted list whose entries are at least `u` starts with its copies of `u`. -/
theorem sorted_eq_replicate_append {u : α} :
    ∀ {l : List α}, l.Pairwise (· ≤ ·) → (∀ x ∈ l, u ≤ x) →
      l = List.replicate (l.count u) u ++ l.filter (fun x => x ≠ u)
  | [], _, _ => by simp
  | x :: l, hs, hu => by
      have hs' := List.pairwise_cons.1 hs
      have ih := sorted_eq_replicate_append hs'.2 (fun y hy => hu y (List.mem_cons_of_mem _ hy))
      by_cases hx : x = u
      · subst hx
        rw [List.count_cons_self, List.replicate_succ, List.filter_cons_of_neg (by simp),
          List.cons_append, ← ih]
      · have hlt : u < x := lt_of_le_of_ne (hu x List.mem_cons_self) (Ne.symm hx)
        have hc : l.count u = 0 := List.count_eq_zero.2 (fun hm =>
          absurd (hs'.1 u hm) (not_le.2 hlt))
        have hc' : (x :: l).count u = 0 := by
          rw [List.count_cons, hc]; simpa using hx
        rw [hc', List.filter_cons_of_pos (by simpa using hx)]
        simp only [List.replicate_zero, List.nil_append]
        rw [List.filter_eq_self.2 (fun y hy => ?_)]
        have := hs'.1 y hy
        simp only [ne_eq, decide_eq_true_eq]
        intro hyu; subst hyu; exact absurd this (not_le.2 hlt)

theorem lt_replicate_append_iff (a : ℕ) (u : α) (X Y : List α) :
    List.replicate a u ++ X < List.replicate a u ++ Y ↔ X < Y := by
  induction a with
  | zero => simp
  | succ a ih =>
    simp only [List.replicate_succ, List.cons_append]
    rw [List.cons_lt_cons_iff]; simp [ih]

/-- Fewer leading copies of the least letter `u` make a larger list. -/
theorem replicate_append_lt_of_lt {u x : α} {a b : ℕ} (hab : a < b) (hux : u < x)
    (X Y : List α) : List.replicate b u ++ Y < List.replicate a u ++ (x :: X) := by
  obtain ⟨d, rfl⟩ : ∃ d, b = a + 1 + d := ⟨b - a - 1, by omega⟩
  rw [List.replicate_add, List.replicate_add, List.append_assoc, List.append_assoc,
    lt_replicate_append_iff]
  simp only [List.replicate_one, List.cons_append]
  exact List.Lex.rel hux

/-- The part of a list above its least letter `u`. -/
private theorem split_facts {u : α} {U : List α} (hU : ∀ v ∈ U, u < v) {A : List α}
    (hsA : A.Pairwise (· ≤ ·)) (hA : ∀ x ∈ A, x ∈ u :: U) :
    ∃ A', A = List.replicate (A.count u) u ++ A' ∧ A'.Pairwise (· ≤ ·) ∧ (∀ x ∈ A', x ∈ U) ∧
      (∀ x ∈ A', u < x) ∧ U.map (fun v => A.count v) = U.map (fun v => A'.count v) := by
  have huA : ∀ x ∈ A, u ≤ x := fun x hx => by
    rcases List.mem_cons.1 (hA x hx) with rfl | h
    · exact le_rfl
    · exact le_of_lt (hU x h)
  refine ⟨A.filter (fun x => x ≠ u), sorted_eq_replicate_append hsA huA, hsA.filter _,
    fun x hx => ?_, fun x hx => ?_, List.map_congr_left (fun v hv => ?_)⟩
  · rw [List.mem_filter] at hx
    rcases List.mem_cons.1 (hA x hx.1) with rfl | h
    · simp at hx
    · exact h
  · rw [List.mem_filter] at hx
    exact lt_of_le_of_ne (huA x hx.1) (Ne.symm (by simpa using hx.2))
  · rw [List.count_filter (by simpa using (ne_of_gt (hU v hv)))]

/-- **Count vectors against sorted lists.** -/
theorem counts_lt_iff : ∀ (U : List α), U.Pairwise (· < ·) →
    ∀ (A B : List α), A.Pairwise (· ≤ ·) → B.Pairwise (· ≤ ·) → (∀ x ∈ A, x ∈ U) →
      (∀ x ∈ B, x ∈ U) → A.length = B.length →
      (U.map (fun u => A.count u) < U.map (fun u => B.count u) ↔ B < A)
  | [], _, A, B, _, _, hA, hB, _ => by
      have hA' : A = [] := List.eq_nil_iff_forall_not_mem.2 (fun x hx => by simpa using hA x hx)
      have hB' : B = [] := List.eq_nil_iff_forall_not_mem.2 (fun x hx => by simpa using hB x hx)
      subst hA' hB'; simp
  | u :: U, hU, A, B, hsA, hsB, hA, hB, hlen => by
      have hU' := List.pairwise_cons.1 hU
      obtain ⟨A', eA, hsA', hmA', hgA', hcA⟩ := split_facts hU'.1 hsA hA
      obtain ⟨B', eB, hsB', hmB', hgB', hcB⟩ := split_facts hU'.1 hsB hB
      have hBA : B < A ↔ List.replicate (B.count u) u ++ B' < List.replicate (A.count u) u ++ A' := by
        rw [← eA, ← eB]
      have lA : A.length = A.count u + A'.length := by
        conv_lhs => rw [eA]
        simp
      have lB : B.length = B.count u + B'.length := by
        conv_lhs => rw [eB]
        simp
      simp only [List.map_cons, List.cons_lt_cons_iff]
      rw [hcA, hcB, hBA]
      generalize A.count u = a at *
      generalize B.count u = b at *
      rcases Nat.lt_trichotomy a b with h | rfl | h
      · -- `A` has fewer copies of `u`: `B < A`
        simp only [h, true_or, true_iff]
        cases A' with
        | nil => simp at lA; omega
        | cons x A'' => exact replicate_append_lt_of_lt h (hgA' x List.mem_cons_self) _ _
      · rw [lt_replicate_append_iff]
        simp only [lt_self_iff_false, true_and, false_or]
        exact counts_lt_iff U hU'.2 A' B' hsA' hsB' hmA' hmB' (by omega)
      · -- `A` has more copies of `u`: `A < B`
        have hn1 : ¬ a < b := by omega
        have hn2 : a ≠ b := by omega
        simp only [hn1, hn2, false_or, false_and, false_iff, not_lt]
        cases B' with
        | nil => simp at lB; omega
        | cons x B'' => exact le_of_lt (replicate_append_lt_of_lt h (hgB' x List.mem_cons_self) _ _)

end Counts

/-! ## More on the lexicographic order -/

section Lex

variable {α : Type*} [LinearOrder α]

theorem cons_le_cons_iff' {a b : α} {u v : List α} :
    a :: u ≤ b :: v ↔ a < b ∨ (a = b ∧ u ≤ v) := by
  rw [le_iff_lt_or_eq, List.cons_lt_cons_iff, List.cons.injEq, le_iff_lt_or_eq]
  constructor
  · rintro ((h | ⟨rfl, h⟩) | ⟨rfl, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨rfl, Or.inl h⟩
    · exact Or.inr ⟨rfl, Or.inr rfl⟩
  · rintro (h | ⟨rfl, h | rfl⟩)
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr ⟨rfl, h⟩)
    · exact Or.inr ⟨rfl, rfl⟩

/-- A map that is strictly increasing on the letters that occur preserves the order. -/
theorem map_lt_map_iff_of_strictMono {β : Type*} [LinearOrder β] (S : Set α) (f : α → β)
    (hf : ∀ a ∈ S, ∀ b ∈ S, a < b → f a < f b) :
    ∀ (X Y : List α), (∀ a ∈ X, a ∈ S) → (∀ a ∈ Y, a ∈ S) → (X.map f < Y.map f ↔ X < Y)
  | [], [], _, _ => by simp
  | [], _ :: _, _, _ => by simp [List.nil_lt_cons]
  | _ :: _, [], _, _ => by simp
  | a :: X, b :: Y, hX, hY => by
      have ha := hX a List.mem_cons_self
      have hb := hY b List.mem_cons_self
      have ih := map_lt_map_iff_of_strictMono S f hf X Y (fun c hc => hX c (List.mem_cons_of_mem _ hc))
        (fun c hc => hY c (List.mem_cons_of_mem _ hc))
      simp only [List.map_cons, List.cons_lt_cons_iff, ih]
      rcases lt_trichotomy a b with h | rfl | h
      · simp [hf a ha b hb h, h]
      · simp
      · have h1 := hf b hb a ha h
        simp [not_lt.2 h1.le, ne_of_gt h1, not_lt.2 h.le, ne_of_gt h]

/-- A map that is strictly decreasing on the letters that occur reverses the order of lists of
the same length. -/
theorem map_lt_map_iff_of_strictAnti {β : Type*} [LinearOrder β] (S : Set α) (f : α → β)
    (hf : ∀ a ∈ S, ∀ b ∈ S, a < b → f b < f a) :
    ∀ (X Y : List α), X.length = Y.length → (∀ a ∈ X, a ∈ S) → (∀ a ∈ Y, a ∈ S) →
      (X.map f < Y.map f ↔ Y < X)
  | [], [], _, _, _ => by simp
  | a :: X, b :: Y, hl, hX, hY => by
      have ha := hX a List.mem_cons_self
      have hb := hY b List.mem_cons_self
      have ih := map_lt_map_iff_of_strictAnti S f hf X Y (by simpa using hl)
        (fun c hc => hX c (List.mem_cons_of_mem _ hc)) (fun c hc => hY c (List.mem_cons_of_mem _ hc))
      simp only [List.map_cons, List.cons_lt_cons_iff, ih]
      rcases lt_trichotomy a b with h | rfl | h
      · have h1 := hf a ha b hb h
        simp [not_lt.2 h1.le, ne_of_gt h1, not_lt.2 h.le, ne_of_gt h]
      · simp
      · simp [hf b hb a ha h, h]

theorem append_lt_append_iff_of_length {a b u v : List α} (h : a.length = b.length) :
    a ++ u < b ++ v ↔ a < b ∨ (a = b ∧ u < v) := by
  induction a generalizing b with
  | nil =>
      cases b with
      | nil => simp
      | cons _ _ => simp at h
  | cons x a ih =>
      cases b with
      | nil => simp at h
      | cons y b =>
          simp only [List.length_cons, Nat.add_right_cancel_iff] at h
          simp only [List.cons_append, List.cons_lt_cons_iff, ih h, List.cons.injEq]
          constructor
          · rintro (h1 | ⟨rfl, h1 | ⟨rfl, h2⟩⟩)
            · exact Or.inl (Or.inl h1)
            · exact Or.inl (Or.inr ⟨rfl, h1⟩)
            · exact Or.inr ⟨⟨rfl, rfl⟩, h2⟩
          · rintro ((h1 | ⟨rfl, h1⟩) | ⟨⟨rfl, rfl⟩, h2⟩)
            · exact Or.inl h1
            · exact Or.inr ⟨rfl, Or.inl h1⟩
            · exact Or.inr ⟨rfl, Or.inr ⟨rfl, h2⟩⟩

/-- Flattening lists of blocks of one length preserves the order. -/
theorem flatten_lt_flatten_iff {k : ℕ} :
    ∀ (X Y : List (List α)), X.length = Y.length → (∀ a ∈ X, a.length = k) →
      (∀ a ∈ Y, a.length = k) → (X.flatten < Y.flatten ↔ X < Y)
  | [], [], _, _, _ => by simp
  | a :: X, b :: Y, hl, hX, hY => by
      have ha := hX a List.mem_cons_self
      have hb := hY b List.mem_cons_self
      have ih := flatten_lt_flatten_iff X Y (by simpa using hl)
        (fun c hc => hX c (List.mem_cons_of_mem _ hc)) (fun c hc => hY c (List.mem_cons_of_mem _ hc))
      rw [List.flatten_cons, List.flatten_cons, append_lt_append_iff_of_length (ha.trans hb.symm),
        ih, List.cons_lt_cons_iff]

end Lex

/-! ## Dense ranks

The rank of `x` among the values of a list: the number of distinct values below `x`. -/

section Dense

variable {κ : Type*} [LinearOrder κ]

/-- The number of distinct values of `L` below `x`. -/
def drank (L : List κ) (x : κ) : ℕ := (L.toFinset.filter (· < x)).card

theorem toFinset_map' {ι β : Type*} [DecidableEq ι] [DecidableEq β] (f : ι → β) (l : List ι) :
    (l.map f).toFinset = l.toFinset.image f := by
  ext x; simp

theorem drank_congr_perm {L L' : List κ} (h : L.Perm L') (x : κ) : drank L x = drank L' x := by
  unfold drank; rw [List.toFinset_eq_of_perm _ _ h]

theorem card_image_congr' {ι β γ : Type*} [DecidableEq β] [DecidableEq γ]
    (S : Finset ι) (f : ι → β) (g : ι → γ) (h : ∀ x ∈ S, ∀ y ∈ S, f x = f y ↔ g x = g y) :
    (S.image f).card = (S.image g).card := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    have ih' := ih (fun x hx y hy => h x (Finset.mem_insert_of_mem hx) y
      (Finset.mem_insert_of_mem hy))
    rw [Finset.image_insert, Finset.image_insert]
    have hiff : f a ∈ S.image f ↔ g a ∈ S.image g := by
      simp only [Finset.mem_image]
      constructor
      · rintro ⟨y, hy, e⟩
        exact ⟨y, hy, ((h y (Finset.mem_insert_of_mem hy) a (Finset.mem_insert_self a S)).1 e)⟩
      · rintro ⟨y, hy, e⟩
        exact ⟨y, hy, ((h y (Finset.mem_insert_of_mem hy) a (Finset.mem_insert_self a S)).2 e)⟩
    by_cases hf : f a ∈ S.image f
    · rw [Finset.insert_eq_of_mem hf, Finset.insert_eq_of_mem (hiff.1 hf), ih']
    · rw [Finset.card_insert_of_notMem hf, Finset.card_insert_of_notMem (mt hiff.2 hf), ih']

/-- **Dense ranks only see the order.**  If two labellings of the rows `R` order the rows the
same way, the dense rank of a row is the same for both. -/
theorem drank_map_congr {ι κ' : Type*} [LinearOrder κ'] [DecidableEq ι] (R : List ι)
    (a : ι → κ) (b : ι → κ') (h : ∀ u ∈ R, ∀ v ∈ R, a u < a v ↔ b u < b v) {t : ι}
    (ht : t ∈ R) : drank (R.map a) (a t) = drank (R.map b) (b t) := by
  have heq : ∀ u ∈ R, ∀ v ∈ R, a u = a v ↔ b u = b v := fun u hu v hv => by
    constructor
    · intro e
      rcases lt_trichotomy (b u) (b v) with h1 | h1 | h1
      · exact absurd ((h u hu v hv).2 h1) (by rw [e]; exact lt_irrefl _)
      · exact h1
      · exact absurd ((h v hv u hu).2 h1) (by rw [e]; exact lt_irrefl _)
    · intro e
      rcases lt_trichotomy (a u) (a v) with h1 | h1 | h1
      · exact absurd ((h u hu v hv).1 h1) (by rw [e]; exact lt_irrefl _)
      · exact h1
      · exact absurd ((h v hv u hu).1 h1) (by rw [e]; exact lt_irrefl _)
  unfold drank
  rw [toFinset_map', toFinset_map', Finset.filter_image, Finset.filter_image]
  have hf : R.toFinset.filter (fun u => a u < a t) = R.toFinset.filter (fun u => b u < b t) := by
    ext u
    simp only [Finset.mem_filter, List.mem_toFinset]
    exact ⟨fun ⟨hu, h1⟩ => ⟨hu, (h u hu t ht).1 h1⟩, fun ⟨hu, h1⟩ => ⟨hu, (h u hu t ht).2 h1⟩⟩
  rw [hf]
  exact card_image_congr' _ _ _ (fun u hu v hv => heq u (List.mem_toFinset.1 (Finset.mem_filter.1 hu).1)
    v (List.mem_toFinset.1 (Finset.mem_filter.1 hv).1))

/-- The least value of a sorted list has rank `0`. -/
theorem drank_sorted_zero {L : List κ} (hL : L.Pairwise (· ≤ ·)) (h0 : 0 < L.length) :
    drank L L[0] = 0 := by
  unfold drank
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro v hv
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem (List.mem_toFinset.1 hv)
  rcases Nat.eq_zero_or_pos j with rfl | hjpos
  · exact lt_irrefl _
  · exact not_lt.2 (List.pairwise_iff_getElem.1 hL 0 j h0 hj hjpos)

/-- **The dense rank along a sorted list** grows by one exactly where the value changes. -/
theorem drank_sorted_succ {L : List κ} (hL : L.Pairwise (· ≤ ·)) {i : ℕ} (hi : i + 1 < L.length) :
    drank L L[i + 1] = drank L L[i] + if L[i + 1] = L[i] then 0 else 1 := by
  have hle : L[i] ≤ L[i + 1] := List.pairwise_iff_getElem.1 hL i (i + 1) (by omega) hi (by omega)
  split_ifs with he
  · rw [he]; rfl
  · have hlt : L[i] < L[i + 1] := lt_of_le_of_ne hle (Ne.symm he)
    unfold drank
    have hset : L.toFinset.filter (· < L[i + 1]) = insert L[i] (L.toFinset.filter (· < L[i])) := by
      ext v
      simp only [Finset.mem_filter, List.mem_toFinset, Finset.mem_insert]
      constructor
      · rintro ⟨hv, hvl⟩
        obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hv
        rcases Nat.lt_or_ge j (i + 1) with hji | hji
        · rcases Nat.lt_or_ge j i with hji' | hji'
          · have := List.pairwise_iff_getElem.1 hL j i hj (by omega) hji'
            rcases eq_or_lt_of_le this with e | e
            · exact Or.inl e
            · exact Or.inr ⟨hv, e⟩
          · obtain rfl : j = i := by omega
            exact Or.inl rfl
        · rcases Nat.eq_or_lt_of_le hji with e | e
          · subst e; exact absurd hvl (lt_irrefl _)
          · exact absurd (List.pairwise_iff_getElem.1 hL (i + 1) j hi hj e) (not_le.2 hvl)
      · rintro (e | ⟨hv, hvl⟩)
        · rw [e]; exact ⟨List.getElem_mem _, hlt⟩
        · exact ⟨hv, lt_trans hvl hlt⟩
    rw [hset, Finset.card_insert_of_notMem (by simp)]

end Dense

/-! ## Counting sort, as a function on lists

A stable counting sort by a key `< K` lists the entries with key `0`, then those with key `1`,
and so on, each group in its old order. -/

section CSort

/-- The stable counting sort of `xs` by `key`, keys below `K`. -/
def csortL (key : ℕ → ℕ) (K : ℕ) (xs : List ℕ) : List ℕ :=
  (List.range K).flatMap (fun c => xs.filter (fun x => key x = c))

theorem csortL_succ (key : ℕ → ℕ) (K : ℕ) (xs : List ℕ) :
    csortL key (K + 1) xs = csortL key K xs ++ xs.filter (fun x => key x = K) := by
  unfold csortL; rw [List.range_succ, List.flatMap_append]; simp

@[simp] theorem csortL_zero (key : ℕ → ℕ) (xs : List ℕ) : csortL key 0 xs = [] := rfl

theorem mem_csortL {key : ℕ → ℕ} {K : ℕ} {xs : List ℕ} {x : ℕ} :
    x ∈ csortL key K xs ↔ x ∈ xs ∧ key x < K := by
  unfold csortL
  simp only [List.mem_flatMap, List.mem_range, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨c, hc, hx, rfl⟩; exact ⟨hx, hc⟩
  · rintro ⟨hx, hc⟩; exact ⟨key x, hc, hx, rfl⟩

theorem count_csortL (key : ℕ → ℕ) (K : ℕ) (xs : List ℕ) (a : ℕ) :
    (csortL key K xs).count a = if key a < K then xs.count a else 0 := by
  induction K with
  | zero => simp
  | succ K ih =>
      have hf : (xs.filter (fun x => key x = K)).count a = if key a = K then xs.count a else 0 := by
        split_ifs with h3
        · exact List.count_filter (by simpa using h3)
        · exact List.count_eq_zero.2 (fun hm => h3 (by simpa using (List.mem_filter.1 hm).2))
      rw [csortL_succ, List.count_append, ih, hf]
      by_cases h1 : key a < K
      · have h2 : key a < K + 1 := by omega
        have h3 : ¬ key a = K := by omega
        simp [h1, h2, h3]
      · by_cases h3 : key a = K
        · simp [h3]
        · have h2 : ¬ key a < K + 1 := by omega
          simp [h1, h2, h3]

theorem csortL_perm {key : ℕ → ℕ} {K : ℕ} {xs : List ℕ} (h : ∀ x ∈ xs, key x < K) :
    (csortL key K xs).Perm xs := by
  rw [List.perm_iff_count]
  intro a
  rw [count_csortL]
  split_ifs with ha
  · rfl
  · exact (List.count_eq_zero.2 (fun hm => ha (h a hm))).symm

/-- **Stability.**  Sorting a list ordered by `R` by the key gives the order "key first, then
`R`". -/
theorem csortL_pairwise {key : ℕ → ℕ} {K : ℕ} {xs : List ℕ} {R : ℕ → ℕ → Prop}
    (h : xs.Pairwise R) :
    (csortL key K xs).Pairwise (fun a b => key a < key b ∨ (key a = key b ∧ R a b)) := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [csortL_succ, List.pairwise_append]
      refine ⟨ih, ?_, fun a ha b hb => ?_⟩
      · exact (h.filter _).imp_of_mem (fun {a b} ha hb hab => by
          simp only [List.mem_filter, decide_eq_true_eq] at ha hb
          exact Or.inr ⟨ha.2.trans hb.2.symm, hab⟩)
      · have h1 := (mem_csortL.1 ha).2
        simp only [List.mem_filter, decide_eq_true_eq] at hb
        exact Or.inl (by omega)

theorem length_csortL_succ (key : ℕ → ℕ) (K : ℕ) (xs : List ℕ) :
    (csortL key (K + 1) xs).length = (csortL key K xs).length +
      (xs.filter (fun x => key x = K)).length := by
  rw [csortL_succ, List.length_append]

end CSort

/-! ## Blocks of one length -/

theorem getElem_flatMap_range_of_length {β : Type*} {f : ℕ → List β} {n : ℕ}
    (hf : ∀ r, (f r).length = n) :
    ∀ (N r y : ℕ) (_hr : r < N) (hy : y < n) (h : r * n + y < ((List.range N).flatMap f).length),
      ((List.range N).flatMap f)[r * n + y] = (f r)[y]'(by rw [hf]; exact hy)
  | 0, r, y, hr, _, _ => absurd hr (Nat.not_lt_zero _)
  | N + 1, r, y, hr, hy, h => by
      have hlen : ∀ M, ((List.range M).flatMap f).length = M * n := by
        intro M
        induction M with
        | zero => simp
        | succ M ih =>
            rw [List.range_succ, List.flatMap_append, List.length_append, ih]
            simp [hf, Nat.succ_mul]
      simp only [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
        List.append_nil]
      rcases Nat.lt_or_ge r N with hrN | hrN
      · have hl : r * n + y < ((List.range N).flatMap f).length := by
          rw [hlen]; nlinarith
        rw [List.getElem_append_left hl]
        exact getElem_flatMap_range_of_length hf N r y hrN hy hl
      · obtain rfl : r = N := by omega
        have hl : ((List.range r).flatMap f).length ≤ r * n + y := by rw [hlen]; omega
        rw [List.getElem_append_right hl]
        congr 1
        rw [hlen]; omega

/-! ## Tuple indices

The program keeps the colors in an array indexed by the number whose base-`n` digits are the
tuple: `idxOf n t = Σ tᵢ n^{k-1-i}`, computed by Horner's rule. -/

section Idx

/-- The base-`n` number with digits `t`, by Horner's rule. -/
def idxOf (n : ℕ) (t : List ℕ) : ℕ := t.foldl (fun a d => a * n + d) 0

theorem foldl_idxOf (n : ℕ) : ∀ (t : List ℕ) (a : ℕ),
    t.foldl (fun a d => a * n + d) a = a * n ^ t.length + idxOf n t
  | [], a => by simp [idxOf]
  | d :: t, a => by
      simp only [List.foldl_cons, idxOf]
      rw [foldl_idxOf n t (a * n + d), foldl_idxOf n t (0 * n + d)]
      simp only [List.length_cons, pow_succ, zero_mul, zero_add]
      ring

theorem idxOf_cons (n d : ℕ) (t : List ℕ) : idxOf n (d :: t) = d * n ^ t.length + idxOf n t := by
  rw [idxOf, List.foldl_cons, foldl_idxOf]; simp

theorem idxOf_append_singleton (n : ℕ) (t : List ℕ) (d : ℕ) :
    idxOf n (t ++ [d]) = idxOf n t * n + d := by
  simp [idxOf, List.foldl_append]

theorem idxOf_lt {n : ℕ} : ∀ {t : List ℕ}, (∀ d ∈ t, d < n) → idxOf n t < n ^ t.length
  | [], _ => by simp [idxOf]
  | d :: t, h => by
      rw [idxOf_cons, List.length_cons, pow_succ]
      have h1 := idxOf_lt (fun c hc => h c (List.mem_cons_of_mem _ hc))
      have h2 := h d List.mem_cons_self
      have h3 : d * n ^ t.length + n ^ t.length ≤ n ^ t.length * n := by
        have : (d + 1) * n ^ t.length ≤ n * n ^ t.length := Nat.mul_le_mul_right _ h2
        nlinarith
      omega

theorem idxOf_inj {n : ℕ} : ∀ {t t' : List ℕ}, t.length = t'.length → (∀ d ∈ t, d < n) →
    (∀ d ∈ t', d < n) → idxOf n t = idxOf n t' → t = t'
  | [], [], _, _, _, _ => rfl
  | d :: t, d' :: t', hl, h, h', he => by
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
      have h1 := idxOf_lt (fun c hc => h c (List.mem_cons_of_mem _ hc))
      have h1' := idxOf_lt (fun c hc => h' c (List.mem_cons_of_mem _ hc))
      rw [idxOf_cons, idxOf_cons, ← hl] at he
      rw [← hl] at h1'
      have hpos : 0 < n ^ t.length := by
        rcases Nat.eq_zero_or_pos (n ^ t.length) with h0 | h0
        · omega
        · exact h0
      have hd : d = d' := by
        have e1 : (idxOf n t + n ^ t.length * d) / n ^ t.length = d := by
          rw [Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt h1, zero_add]
        have e2 : (idxOf n t' + n ^ t.length * d') / n ^ t.length = d' := by
          rw [Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt h1', zero_add]
        rw [← e1, ← e2]; congr 1; linarith
      subst hd
      rw [idxOf_inj hl (fun c hc => h c (List.mem_cons_of_mem _ hc))
        (fun c hc => h' c (List.mem_cons_of_mem _ hc)) (by omega)]

end Idx

/-! ## Reading the table -/

theorem lookup_of_mem_nodup : ∀ {tbl : List (List ℕ × ℕ)}, (tbl.map Prod.fst).Nodup →
    ∀ {q : List ℕ × ℕ}, q ∈ tbl → tbl.lookup q.1 = some q.2
  | [], _, _, hq => absurd hq (by simp)
  | r :: tbl, hn, q, hq => by
      simp only [List.map_cons, List.nodup_cons] at hn
      rcases List.mem_cons.1 hq with rfl | hq'
      · simp [List.lookup]
      · have hne : q.1 ≠ r.1 := fun e => hn.1 (e ▸ List.mem_map_of_mem hq')
        have hb : (q.1 == r.1) = false := beq_eq_false_iff_ne.2 hne
        simp only [List.lookup, hb]
        exact lookup_of_mem_nodup hn.2 hq'

theorem mem_of_lookup : ∀ {tbl : List (List ℕ × ℕ)} {t : List ℕ} {v : ℕ},
    tbl.lookup t = some v → (t, v) ∈ tbl
  | [], _, _, h => by simp [List.lookup] at h
  | r :: tbl, t, v, h => by
      by_cases e : t = r.1
      · subst e
        simp only [List.lookup, beq_self_eq_true, Option.some.injEq] at h
        subst h; exact List.mem_cons_self
      · have hb : (t == r.1) = false := beq_eq_false_iff_ne.2 e
        simp only [List.lookup, hb] at h
        exact List.mem_cons_of_mem _ (mem_of_lookup h)

/-- In a table with distinct keys, the color of a listed row is read back. -/
theorem tblGet_of_mem {n k : ℕ} {p : RawWL} (h : RawWL.WF n k p) {q : List ℕ × ℕ} (hq : q ∈ p.2) :
    tblGet (p.2, q.1) = q.2 := by
  rw [tblGet, lookup_of_mem_nodup h.keyNodup hq]; rfl

/-- Colors read off a nonempty table are below its number of rows. -/
theorem tblGet_lt {n k : ℕ} {p : RawWL} (h : RawWL.WF n k p) (hne : 0 < p.2.length) (t : List ℕ) :
    tblGet (p.2, t) < p.2.length := by
  unfold tblGet
  cases e : p.2.lookup t with
  | none => simpa using hne
  | some v => exact h.colLt _ (mem_of_lookup e)

/-! ## The string of a tuple -/

section Str

/-- The tuples of old colors around `t`, one per vertex. -/
def vecsOf (p : RawWL) (t : List ℕ) : List (List ℕ) := p.1.map (innerVec p.2 t)

/-- The same tuples, sorted. -/
def sortedVecs (p : RawWL) (t : List ℕ) : List (List ℕ) := (vecsOf p t).mergeSort (· ≤ ·)

/-- **The string of a tuple**: its old color, then the sorted tuples of old colors around it,
concatenated, each color `c` written as `N - c` (`N` the number of rows). -/
def strOf (p : RawWL) (t : List ℕ) : List ℕ :=
  tblGet (p.2, t) :: ((sortedVecs p t).flatten.map (fun c => p.2.length - c))

theorem sortedVecs_pairwise (p : RawWL) (t : List ℕ) : (sortedVecs p t).Pairwise (· ≤ ·) :=
  List.pairwise_mergeSort' (· ≤ ·) _

theorem sortedVecs_perm (p : RawWL) (t : List ℕ) : (sortedVecs p t).Perm (vecsOf p t) :=
  List.mergeSort_perm _ _

/-- A sorted list of the tuples of old colors is `sortedVecs`. -/
theorem eq_sortedVecs {p : RawWL} {t : List ℕ} {L : List (List ℕ)} (hs : L.Pairwise (· ≤ ·))
    (hp : L.Perm (vecsOf p t)) : L = sortedVecs p t :=
  List.Perm.eq_of_pairwise' hs (sortedVecs_pairwise p t) (hp.trans (sortedVecs_perm p t).symm)

@[simp] theorem length_sortedVecs (p : RawWL) (t : List ℕ) :
    (sortedVecs p t).length = p.1.length := by
  rw [(sortedVecs_perm p t).length_eq]; simp [vecsOf]

variable {n k : ℕ} {p : RawWL}

theorem mem_sortedVecs {q : List ℕ × ℕ} (hq : q ∈ p.2) {v : List ℕ} (hv : v ∈ sortedVecs p q.1) :
    v ∈ vecSet p := by
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 ((sortedVecs_perm p q.1).subset hv)
  exact innerVec_mem_vecSet hq hy

theorem entry_lt_of_mem_vecSet (h : RawWL.WF n k p) {v : List ℕ} (hv : v ∈ vecSet p) {c : ℕ}
    (hc : c ∈ v) : c < p.2.length := by
  obtain ⟨q, hq, y, -, rfl⟩ := exists_of_mem_allVecs (mem_vecSet.1 hv)
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
  rw [getElem_innerVec]
  exact tblGet_lt h (List.length_pos_of_mem hq) _

/-- The rank of a tuple of old colors among those that occur. -/
theorem rankIn_mono (h : RawWL.WF n k p) {u v : List ℕ} (hu : u ∈ vecSet p) (hv : v ∈ vecSet p)
    (huv : u < v) : rankIn (vecSet p, u) < rankIn (vecSet p, v) :=
  rankIn_lt_rankIn hu ((cmpRec_eq_one_iff ((length_of_mem_vecSet h hu).trans
    (length_of_mem_vecSet h hv).symm)).2 huv)

/-- The tail of the tag, as counts of ranks. -/
theorem wlCount_eq_count (t : List ℕ) (j : ℕ) :
    wlCount p t j = ((vecsOf p t).map (fun v => rankIn (vecSet p, v))).count j := by
  rw [wlCount, vecsOf, List.map_map, List.count_eq_countP, List.countP_map,
    List.countP_eq_length_filter]
  congr 1

/-- **The tags are ordered as the strings.** -/
theorem wlTagAt_lt_iff (h : RawWL.WF n k p) {q q' : List ℕ × ℕ} (hq : q ∈ p.2) (hq' : q' ∈ p.2) :
    wlTagAt p q.1 < wlTagAt p q'.1 ↔ strOf p q.1 < strOf p q'.1 := by
  set ρ : List ℕ → ℕ := fun v => rankIn (vecSet p, v) with hρ
  set m := (vecSet p).length with hm
  have hN : 0 < p.2.length := List.length_pos_of_mem hq
  -- the tails of the tags are count vectors of the ranks
  have htail : ∀ r ∈ p.2, (List.range m).map (wlCount p r.1) =
      (List.range m).map (fun j => ((sortedVecs p r.1).map ρ).count j) := fun r _ =>
    List.map_congr_left (fun j _ => by
      rw [wlCount_eq_count, ((sortedVecs_perm p r.1).map ρ).count_eq])
  have hsort : ∀ r ∈ p.2, ((sortedVecs p r.1).map ρ).Pairwise (· ≤ ·) := fun r hr => by
    rw [List.pairwise_map]
    refine (sortedVecs_pairwise p r.1).imp_of_mem (fun {u v} hu hv huv => ?_)
    rcases eq_or_lt_of_le huv with e | e
    · rw [e]
    · exact (rankIn_mono h (mem_sortedVecs hr hu) (mem_sortedVecs hr hv) e).le
  have hmemU : ∀ r ∈ p.2, ∀ x ∈ (sortedVecs p r.1).map ρ, x ∈ List.range m := fun r hr x hx => by
    obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hx
    exact List.mem_range.2 (rankIn_lt_length (mem_sortedVecs hr hv))
  have hcnt := counts_lt_iff (List.range m) List.pairwise_lt_range _ _ (hsort q hq) (hsort q' hq')
    (hmemU q hq) (hmemU q' hq') (by simp)
  have hmono := map_lt_map_iff_of_strictMono {v | v ∈ vecSet p} ρ
    (fun a ha b hb hab => rankIn_mono h ha hb hab) (sortedVecs p q'.1) (sortedVecs p q.1)
    (fun v hv => mem_sortedVecs hq' hv) (fun v hv => mem_sortedVecs hq hv)
  have hflat := flatten_lt_flatten_iff (k := k) (sortedVecs p q'.1) (sortedVecs p q.1) (by simp)
    (fun v hv => length_of_mem_vecSet h (mem_sortedVecs hq' hv))
    (fun v hv => length_of_mem_vecSet h (mem_sortedVecs hq hv))
  have hent : ∀ r ∈ p.2, ∀ c ∈ (sortedVecs p r.1).flatten, c ∈ {c | c < p.2.length} :=
    fun r hr c hc => by
      obtain ⟨v, hv, hcv⟩ := List.mem_flatten.1 hc
      exact entry_lt_of_mem_vecSet h (mem_sortedVecs hr hv) hcv
  have hlenf : ∀ r ∈ p.2, (sortedVecs p r.1).flatten.length = p.1.length * k := fun r hr => by
    rw [List.length_flatten, List.map_congr_left (g := fun _ => k)
      (fun v hv => length_of_mem_vecSet h (mem_sortedVecs hr hv))]
    simp
  have hanti := map_lt_map_iff_of_strictAnti {c | c < p.2.length} (fun c => p.2.length - c)
    (fun a ha b hb hab => by simp only [Set.mem_setOf_eq] at ha hb ⊢; omega)
    (sortedVecs p q.1).flatten (sortedVecs p q'.1).flatten
    ((hlenf q hq).trans (hlenf q' hq').symm) (hent q hq) (hent q' hq')
  rw [wlTagAt, wlTagAt, strOf, strOf, List.cons_lt_cons_iff, List.cons_lt_cons_iff, htail q hq,
    htail q' hq', hcnt, hmono, ← hflat, hanti]

/-- The new color of a tuple is the number of distinct tags below its tag. -/
theorem wlNewCol_eq_drank_tag (p : RawWL) (t : List ℕ) :
    wlNewCol p t = drank (p.2.map (fun r => wlTagAt p r.1)) (wlTagAt p t) := by
  have hlen : ∀ u ∈ wlTagSet p, u.length = (wlTagAt p t).length := fun u hu => by
    obtain ⟨r, -, rfl⟩ := List.mem_map.1 (mem_wlTagSet.1 hu)
    simp
  rw [wlNewCol, rankIn, drank]
  have hnd : ((wlTagSet p).filter (fun u => lexLtB (u, wlTagAt p t))).Nodup :=
    (RAM.nodup_dedupG _).filter _
  rw [← List.toFinset_card_of_nodup hnd, List.toFinset_filter]
  have hset : (wlTagSet p).toFinset = (p.2.map (fun r => wlTagAt p r.1)).toFinset := by
    ext u; simp only [List.mem_toFinset]; exact mem_wlTagSet
  rw [hset]
  congr 1
  ext u
  simp only [Finset.mem_filter, List.mem_toFinset]
  refine and_congr_right (fun hu => ?_)
  have hu' : u ∈ wlTagSet p := mem_wlTagSet.2 (by simpa [wlTags] using hu)
  rw [lexLtB_eq, decide_eq_true_eq, cmpRec_eq_one_iff (hlen u hu')]

/-- **The new color of a tuple is the dense rank of its string** among the strings of all
tuples. -/
theorem wlNewCol_eq_drank (h : RawWL.WF n k p) {q : List ℕ × ℕ} (hq : q ∈ p.2) :
    wlNewCol p q.1 = drank (p.2.map (fun r => strOf p r.1)) (strOf p q.1) := by
  classical
  rw [wlNewCol_eq_drank_tag p q.1]
  exact drank_map_congr p.2 (fun r => wlTagAt p r.1) (fun r => strOf p r.1)
    (fun u hu v hv => wlTagAt_lt_iff h hu hv) hq

end Str

/-! ## Early stopping -/

section Stop

variable {n k : ℕ}

theorem nodup_wlTagSet' (p : RawWL) : (wlTagSet p).Nodup := RAM.nodup_dedupG _

theorem exists_tupleOf_of_mem {p : RawWL} (h : RawWL.WF n k p) {q : List ℕ × ℕ} (hq : q ∈ p.2) :
    ∃ x : Str (Fin n) k, tupleOf x = q.1 := by
  obtain ⟨h1, h2⟩ := (h.keyMem q.1).1 (List.mem_map_of_mem hq)
  exact exists_tupleOf h1 h2

/-- The new colors are ordered as the tags. -/
theorem wlNewCol_lt_iff {p : RawWL} {q q' : List ℕ × ℕ} (hq : q ∈ p.2) (hq' : q' ∈ p.2) :
    wlNewCol p q.1 < wlNewCol p q'.1 ↔ wlTagAt p q.1 < wlTagAt p q'.1 := by
  have hlen : ∀ u v : List ℕ × ℕ, (wlTagAt p u.1).length = (wlTagAt p v.1).length :=
    fun u v => by simp
  constructor
  · intro hlt
    rcases lt_trichotomy (wlTagAt p q.1) (wlTagAt p q'.1) with e | e | e
    · exact e
    · rw [wlNewCol, wlNewCol, e] at hlt; exact absurd hlt (lt_irrefl _)
    · have := rankIn_lt_rankIn (wlTagAt_mem_wlTagSet hq') ((cmpRec_eq_one_iff (hlen q' q)).2 e)
      exact absurd hlt (not_lt.2 this.le)
  · intro e
    exact rankIn_lt_rankIn (wlTagAt_mem_wlTagSet hq) ((cmpRec_eq_one_iff (hlen q q')).2 e)

/-- **A round after which the partition does not change gives back its input.**  The colors
of `rawWLStep q'` are dense ranks; if the next round refines nothing, it only renames the
colors by their ranks, which are the colors themselves. -/
theorem rawWLStep_fix {q' : RawWL} (h : RawWL.WF n k q')
    (hker : ∀ x x' : Str (Fin n) k,
      (decWL n k (rawWLStep (rawWLStep q'))).color x = (decWL n k (rawWLStep (rawWLStep q'))).color x'
        ↔ (decWL n k (rawWLStep q')).color x = (decWL n k (rawWLStep q')).color x') :
    rawWLStep (rawWLStep q') = rawWLStep q' := by
  classical
  set q := rawWLStep q' with hqdef
  have hq : RawWL.WF n k q := rawWLStep_wf h
  -- on the rows of `q`, the tags of `q` are ordered as the colors of `q`
  have horder : ∀ u ∈ q.2, ∀ v ∈ q.2,
      wlTagAt q u.1 < wlTagAt q v.1 ↔ tblGet (q.2, u.1) < tblGet (q.2, v.1) := by
    intro u hu v hv
    rw [wlTagAt, wlTagAt, List.cons_lt_cons_iff]
    constructor
    · rintro (e | ⟨e, e'⟩)
      · exact e
      · exfalso
        obtain ⟨x, hx⟩ := exists_tupleOf_of_mem hq hu
        obtain ⟨x', hx'⟩ := exists_tupleOf_of_mem hq hv
        have h1 : (decWL n k q).color x = (decWL n k q).color x' := by
          rw [decWL_color, decWL_color, hx, hx']; exact e
        have h2 := (hker x x').2 h1
        rw [decWL_color, decWL_color, hx, hx', tblGet_rawWLStep hu, tblGet_rawWLStep hv,
          wlNewCol_eq_iff hu hv] at h2
        rw [wlTagAt, wlTagAt] at h2
        have h3 := congrArg List.tail h2
        simp only [List.tail_cons] at h3
        rw [h3] at e'
        exact lt_irrefl _ e'
    · intro e; exact Or.inl e
  have hmonoq' : ∀ u ∈ q'.2, ∀ v ∈ q'.2,
      wlTagAt q' u.1 < wlTagAt q' v.1 ↔ wlNewCol q' u.1 < wlNewCol q' v.1 :=
    fun u hu v hv => (wlNewCol_lt_iff hu hv).symm
  have hcols : q.2.map (fun r => tblGet (q.2, r.1)) = q'.2.map (fun s => wlNewCol q' s.1) := by
    have e : ∀ s ∈ q'.2, tblGet (q.2, s.1) = wlNewCol q' s.1 := fun s hs => tblGet_rawWLStep hs
    calc q.2.map (fun r => tblGet (q.2, r.1))
        = (q'.2.map (fun s => (s.1, wlNewCol q' s.1))).map (fun r => tblGet (q.2, r.1)) := rfl
      _ = q'.2.map (fun s => wlNewCol q' s.1) := by
          rw [List.map_map]; exact List.map_congr_left (fun s hs => e s hs)
  have key : ∀ s ∈ q'.2, wlNewCol q s.1 = wlNewCol q' s.1 := by
    intro s hs
    have hr : (s.1, wlNewCol q' s.1) ∈ q.2 := List.mem_map.2 ⟨s, hs, rfl⟩
    have e1 := wlNewCol_eq_drank_tag q (s.1, wlNewCol q' s.1).1
    simp only at e1
    rw [e1, drank_map_congr q.2 (fun r => wlTagAt q r.1) (fun r => tblGet (q.2, r.1))
      horder hr]
    simp only
    have e2 : tblGet (q.2, s.1) = wlNewCol q' s.1 := tblGet_rawWLStep hs
    rw [hcols, e2]
    conv_rhs => rw [wlNewCol_eq_drank_tag q' s.1]
    exact (drank_map_congr q'.2 (fun r => wlTagAt q' r.1) (fun r => wlNewCol q' r.1)
      hmonoq' hs).symm
  show (q.1, q.2.map (fun r => (r.1, wlNewCol q r.1))) = q
  have hmap : q.2.map (fun r => (r.1, wlNewCol q r.1)) = q.2 :=
    calc q.2.map (fun r => (r.1, wlNewCol q r.1))
        = (q'.2.map (fun s => (s.1, wlNewCol q' s.1))).map (fun r => (r.1, wlNewCol q r.1)) := rfl
      _ = q'.2.map (fun s => (s.1, wlNewCol q' s.1)) := by
          rw [List.map_map]; exact List.map_congr_left (fun s hs => Prod.ext rfl (key s hs))
      _ = q.2 := rfl
  rw [hmap]

/-- The rounds, as memories: `p_j = rawWLStep^[j] p`. -/
theorem kernel_mono {p : RawWL} (h : RawWL.WF n k p) (j : ℕ) :
    kernelSet (decWL n k (rawWLStep^[j + 1] p)).color ⊆ kernelSet (decWL n k (rawWLStep^[j] p)).color := by
  intro x hx
  rw [mem_kernelSet] at hx ⊢
  rw [rawWLIter_spec h] at hx ⊢
  exact KAryPartStruct.wlIter_refines_le _ (Nat.le_succ j) hx

theorem kernel_step {p : RawWL} (h : RawWL.WF n k p) (j : ℕ)
    (he : kernelSet (decWL n k (rawWLStep^[j + 1] p)).color = kernelSet (decWL n k (rawWLStep^[j] p)).color) :
    kernelSet (decWL n k (rawWLStep^[j + 2] p)).color = kernelSet (decWL n k (rawWLStep^[j + 1] p)).color := by
  ext x
  rw [mem_kernelSet, mem_kernelSet]
  have e2 : rawWLStep^[j + 2] p = rawWLStep (rawWLStep^[j + 1] p) := Function.iterate_succ_apply' _ _ _
  have e1 : rawWLStep^[j + 1] p = rawWLStep (rawWLStep^[j] p) := Function.iterate_succ_apply' _ _ _
  rw [e2, rawWLStep_spec (wf_rawWLIter h (j + 1)), e1, rawWLStep_spec (wf_rawWLIter h j)]
  refine KAryPartStruct.wlStep_congr (fun u v => ?_) x.1 x.2
  have := congrArg (fun S => (u, v) ∈ S) he
  simp only [mem_kernelSet, eq_iff_iff] at this
  rw [← e1]; exact this

/-- **Within `N` rounds a round gives back its input** (`N` the number of rows). -/
theorem exists_fix_le {p : RawWL} (h : RawWL.WF n k p) :
    ∃ J ≤ p.2.length, rawWLStep (rawWLStep^[J] p) = rawWLStep^[J] p := by
  rcases Nat.eq_zero_or_pos p.2.length with h0 | hpos
  · refine ⟨0, Nat.zero_le _, ?_⟩
    have : p.2 = [] := List.eq_nil_of_length_eq_zero h0
    simp only [Function.iterate_zero, id, rawWLStep, this, List.map_nil]
    exact Prod.ext rfl this.symm
  · refine ⟨p.2.length, le_refl _, ?_⟩
    have hcard : Fintype.card (Str (Fin n) k) = p.2.length := by
      rw [length_table h]; simp [Str]
    have hmono := kernel_mono h
    have hst := kernel_step h
    have hN := kernelSet_eq_of_card_sub_one_le (α := Str (Fin n) k)
      (fun j => (decWL n k (rawWLStep^[j] p)).color) hmono hst
      (m := p.2.length - 1) (by rw [hcard])
    have hN' := hst _ hN
    obtain ⟨M, hM⟩ : ∃ M, p.2.length = M + 1 := ⟨p.2.length - 1, by omega⟩
    rw [show p.2.length - 1 = M by omega] at hN hN'
    rw [hM]
    have e : rawWLStep^[M + 1] p = rawWLStep (rawWLStep^[M] p) := Function.iterate_succ_apply' _ _ _
    rw [e]
    refine rawWLStep_fix (wf_rawWLIter h M) (fun x x' => ?_)
    have := congrArg (fun S => (x, x') ∈ S) hN'
    simp only [mem_kernelSet, eq_iff_iff] at this
    rw [← e, ← Function.iterate_succ_apply' rawWLStep (M + 1)]
    exact this

/-- **Early stopping is correct**: a round that gives back its input, reached within the
fixed number of rounds, is the stable coloring. -/
theorem rawWLStable_eq_of_fix {p : RawWL} {J : ℕ} (hJ : rawWLStep (rawWLStep^[J] p) = rawWLStep^[J] p)
    (hle : J ≤ p.2.length * p.2.length) : rawWLStable p = rawWLStep^[J] p := by
  rw [rawWLStable_eq_iterate]
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
  rw [hd, Nat.add_comm, Function.iterate_add_apply]
  exact Function.iterate_fixed hJ d

end Stop

end WLFast

end Algo
