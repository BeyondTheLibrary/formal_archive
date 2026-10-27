/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 4.1.1: the running time of the tagged refinement process.  Pure lemmas on longest
common prefixes and the lexicographic order, used by the sorting routine of
`Workspace/Algo/TagLinSort.lean`.
-/
import Mathlib.Data.List.Lex
import Mathlib.Data.Finset.Sort

/-!
# Longest common prefixes and the lexicographic order

§4.1.1 orders the colors, which are strings, lexicographically (the palette `C` of a round is
"the ordered set" of the colors).  The sorting routine of `Workspace/Algo/TagLinSort.lean`
inserts the strings one by one into a sorted list and keeps, for two neighbours of the list,
the length of their longest common prefix (`lcp`).  With these lengths a new string is compared
with each element of the list at the cost of the letters it has not yet matched.  This file
proves the facts about `lcp` and the order `<` of `List ℕ` (Mathlib's lexicographic order) that
the routine relies on.  No axiom, no `sorry`.
-/

namespace Algo

namespace TagLin

/-- The length of the longest common prefix of two strings. -/
def lcp : List ℕ → List ℕ → ℕ
  | a :: s, b :: t => if a = b then lcp s t + 1 else 0
  | _, _ => 0

@[simp] theorem lcp_nil_left (t : List ℕ) : lcp [] t = 0 := by cases t <;> rfl

@[simp] theorem lcp_nil_right (s : List ℕ) : lcp s [] = 0 := by cases s <;> rfl

theorem lcp_cons (a b : ℕ) (s t : List ℕ) :
    lcp (a :: s) (b :: t) = if a = b then lcp s t + 1 else 0 := rfl

theorem lcp_comm : ∀ s t : List ℕ, lcp s t = lcp t s
  | [], t => by simp
  | a :: s, [] => by simp
  | a :: s, b :: t => by
    rw [lcp_cons, lcp_cons, lcp_comm s t]
    by_cases h : a = b
    · subst h; simp
    · rw [if_neg h, if_neg (Ne.symm h)]

theorem lcp_le_left : ∀ s t : List ℕ, lcp s t ≤ s.length
  | [], t => by simp
  | a :: s, [] => by simp
  | a :: s, b :: t => by
    rw [lcp_cons]; split
    · have := lcp_le_left s t; simp; omega
    · omega

theorem lcp_le_right (s t : List ℕ) : lcp s t ≤ t.length := by
  rw [lcp_comm]; exact lcp_le_left t s

/-- Below the common prefix length the two strings agree. -/
theorem getElem?_eq_of_lt_lcp : ∀ {s t : List ℕ} {j : ℕ}, j < lcp s t → s[j]? = t[j]?
  | [], t, j, h => by simp at h
  | a :: s, [], j, h => by simp at h
  | a :: s, b :: t, j, h => by
    rw [lcp_cons] at h
    split at h
    · rename_i hab
      subst hab
      cases j with
      | zero => rfl
      | succ j =>
        simp only [List.getElem?_cons_succ]
        exact getElem?_eq_of_lt_lcp (by omega)
    · omega

/-- At the common prefix length the two strings differ (when both go on). -/
theorem lcp_stop : ∀ {s t : List ℕ} (h1 : lcp s t < s.length) (h2 : lcp s t < t.length),
    s[lcp s t] ≠ t[lcp s t]
  | [], t, h1, _ => by simp at h1
  | a :: s, [], _, h2 => by simp at h2
  | a :: s, b :: t, h1, h2 => by
    by_cases hab : a = b
    · subst hab
      have e : lcp (a :: s) (a :: t) = lcp s t + 1 := by rw [lcp_cons, if_pos rfl]
      have h1' : lcp s t < s.length := by rw [e] at h1; simp at h1; omega
      have h2' : lcp s t < t.length := by rw [e] at h2; simp at h2; omega
      simp only [e, List.getElem_cons_succ]
      exact lcp_stop h1' h2'
    · have e : lcp (a :: s) (b :: t) = 0 := by rw [lcp_cons, if_neg hab]
      simp only [e, List.getElem_cons_zero]
      exact hab

/-- `lcp` is characterized by agreement below it and a stop at it. -/
theorem lcp_eq_of : ∀ {s t : List ℕ} {l : ℕ}, (∀ j < l, s[j]? = t[j]?) → l ≤ s.length →
    l ≤ t.length → (l = s.length ∨ l = t.length ∨
      ∃ (h1 : l < s.length) (h2 : l < t.length), s[l] ≠ t[l]) → lcp s t = l
  | [], t, l, _, hs, _, _ => by simp at hs; simp [hs]
  | a :: s, [], l, _, _, ht, _ => by simp at ht; simp [ht]
  | a :: s, b :: t, l, hagree, hs, ht, hstop => by
    cases l with
    | zero =>
      rw [lcp_cons]
      rcases hstop with h | h | ⟨_, _, h⟩
      · simp at h
      · simp at h
      · simp only [List.getElem_cons_zero] at h
        rw [if_neg h]
    | succ l =>
      have hab : a = b := by simpa using hagree 0 (by omega)
      subst hab
      rw [lcp_cons, if_pos rfl]
      congr 1
      refine lcp_eq_of (fun j hj => by simpa using hagree (j + 1) (by omega))
        (by simp at hs; omega) (by simp at ht; omega) ?_
      rcases hstop with h | h | ⟨h1, h2, h⟩
      · left; simp at h; omega
      · right; left; simp at h; omega
      · right; right
        exact ⟨by simp at h1; omega, by simp at h2; omega, by simpa using h⟩

/-- Agreement on a prefix of length `l` gives `l ≤ lcp`. -/
theorem le_lcp_of : ∀ {s t : List ℕ} {l : ℕ}, (∀ j < l, s[j]? = t[j]?) → l ≤ s.length →
    l ≤ t.length → l ≤ lcp s t
  | [], t, l, _, hs, _ => by simp at hs; omega
  | a :: s, [], l, _, _, ht => by simp at ht; omega
  | a :: s, b :: t, l, hagree, hs, ht => by
    cases l with
    | zero => omega
    | succ l =>
      have hab : a = b := by simpa using hagree 0 (by omega)
      subst hab
      rw [lcp_cons, if_pos rfl]
      have := le_lcp_of (s := s) (t := t) (l := l)
        (fun j hj => by simpa using hagree (j + 1) (by omega)) (by simp at hs; omega)
        (by simp at ht; omega)
      omega

/-- Equality through `lcp`. -/
theorem eq_iff_lcp : ∀ {s t : List ℕ}, s = t ↔ lcp s t = s.length ∧ lcp s t = t.length
  | [], [] => by simp
  | [], b :: t => by simp
  | a :: s, [] => by simp
  | a :: s, b :: t => by
    rw [lcp_cons]
    by_cases hab : a = b
    · subst hab
      rw [if_pos rfl, List.cons.injEq, eq_iff_lcp]
      simp
    · rw [if_neg hab]; simp [hab]

/-- The lexicographic order through `lcp`: `s < t` exactly when `s` stops at the common prefix
while `t` goes on, or both go on and the next letter of `s` is smaller. -/
theorem lt_iff_lcp : ∀ {s t : List ℕ}, s < t ↔
    (lcp s t = s.length ∧ lcp s t < t.length) ∨
      ∃ (h1 : lcp s t < s.length) (h2 : lcp s t < t.length), s[lcp s t] < t[lcp s t]
  | [], [] => by simp
  | [], b :: t => by simp [List.nil_lt_cons]
  | a :: s, [] => by
    simp only [lcp_nil_right, List.length_cons, List.length_nil]
    constructor
    · intro h; exact absurd h (List.not_lt_nil _)
    · rintro (⟨h, _⟩ | ⟨_, h, _⟩) <;> omega
  | a :: s, b :: t => by
    rw [List.cons_lt_cons_iff]
    by_cases hab : a = b
    · subst hab
      have e : lcp (a :: s) (a :: t) = lcp s t + 1 := by rw [lcp_cons, if_pos rfl]
      simp only [e, List.length_cons, List.getElem_cons_succ, lt_irrefl, false_or, true_and]
      rw [lt_iff_lcp]
      constructor
      · rintro (⟨h1, h2⟩ | ⟨h1, h2, h3⟩)
        · left; omega
        · right; exact ⟨by omega, by omega, h3⟩
      · rintro (⟨h1, h2⟩ | ⟨h1, h2, h3⟩)
        · left; omega
        · right; exact ⟨by omega, by omega, h3⟩
    · have e : lcp (a :: s) (b :: t) = 0 := by rw [lcp_cons, if_neg hab]
      simp only [e, List.length_cons, List.getElem_cons_zero, hab, false_and, or_false]
      constructor
      · intro h; right; exact ⟨by omega, by omega, h⟩
      · rintro (⟨h1, _⟩ | ⟨_, _, h⟩)
        · omega
        · exact h

/-- The three cases of the scan.  Let `t < t'` be neighbours of the sorted list with common
prefix length `L`, and let `t < s` with common prefix length `l` (of `s` and `t`).  If `L < l`
then `s < t'` with common prefix length `L`; otherwise `s` and `t'` agree on the first `l`
letters. -/
theorem scan_lt {s t t' : List ℕ} (htt : t < t') (hL : lcp t t' < lcp s t) :
    s < t' ∧ lcp s t' = lcp t t' := by
  set L := lcp t t' with hLdef
  set l := lcp s t with hldef
  have hLt : L < t.length := by have := lcp_le_right s t; omega
  have hagreeT : ∀ j < L, t[j]? = t'[j]? := fun j hj => getElem?_eq_of_lt_lcp hj
  have hagreeS : ∀ j < l, s[j]? = t[j]? := fun j hj => getElem?_eq_of_lt_lcp hj
  have hls : l ≤ s.length := lcp_le_left s t
  -- `t < t'` with `L < |t|`: both go on at `L` and `t[L] < t'[L]`
  rcases lt_iff_lcp.1 htt with ⟨h1, _⟩ | ⟨h1, h2, h3⟩
  · omega
  have hsL : L < s.length := by omega
  have hsT : s[L] = t[L] := by
    have := hagreeS L hL
    rw [List.getElem?_eq_getElem hsL, List.getElem?_eq_getElem hLt] at this
    exact Option.some.inj this
  have hagree : ∀ j < L, s[j]? = t'[j]? := fun j hj => by
    rw [hagreeS j (by omega), hagreeT j hj]
  have hlcp : lcp s t' = L := lcp_eq_of hagree (by omega) (by omega)
    (Or.inr (Or.inr ⟨hsL, h2, by rw [hsT]; exact ne_of_lt h3⟩))
  refine ⟨?_, hlcp⟩
  rw [lt_iff_lcp]
  right
  refine ⟨by rw [hlcp]; exact hsL, by rw [hlcp]; exact h2, ?_⟩
  simp only [hlcp]
  rw [hsT]; exact h3

theorem scan_ge {s t t' : List ℕ} (hL : lcp s t ≤ lcp t t') :
    (∀ j < lcp s t, s[j]? = t'[j]?) ∧ lcp s t ≤ t'.length := by
  refine ⟨fun j hj => ?_, le_trans hL (lcp_le_right t t')⟩
  rw [getElem?_eq_of_lt_lcp hj, getElem?_eq_of_lt_lcp (by omega : j < lcp t t')]

/-! ## Sorted lists -/

/-- A strictly increasing list with the same members as a finset is its sorted list. -/
theorem eq_sort_of {l : List (List ℕ)} (hl : l.Pairwise (· < ·)) (S : Finset (List ℕ))
    (hmem : ∀ a, a ∈ l ↔ a ∈ S) : l = S.sort (· ≤ ·) :=
  hl.eq_of_mem_iff (Finset.sortedLT_sort S).pairwise (fun a => by rw [hmem, Finset.mem_sort])

end TagLin

end Algo
