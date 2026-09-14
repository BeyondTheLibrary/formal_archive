import Mathlib
import Workspace.Types.Core
import Workspace.Types.Pseudowheels
import Workspace.Types.Classes
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PathAttach
import Workspace.ProofLemmas.PrismBasics
import Workspace.ProofLemmas.KiteTailBasics
import Workspace.Statements.S02.Thm_2_11
import Workspace.Statements.S18.Thm_18_3
import Workspace.Statements.S18.Thm_18_4

/-!
# 18.5 — the shared vocabulary of the printed proof

The printed proof of **18.5** (`paper/proofs/18_5.md`, published page 111) runs a long case
analysis whose steps all reduce to the same handful of moves.  Those moves are named once, here,
so that the three terminal claims (`Thm185Claim3`, `Thm185Claim4`, `Thm185Final`) can cite them
instead of re-deriving them.

* `subpath_window` — the single most reused step of the printed proof.  Each of *"(If this is
  impossible then the conclusion holds.)"*, *"for otherwise the conclusion holds"*, *"if
  `k ≤ h+1` then the conclusion holds"*, *"but then the claim holds"*, … is the same manoeuvre:
  exhibit indices `a ≤ b` such that every neighbour of `v` in `P` has index in `[a,b]` and no
  `p_t` with `a < t < b` is `Y`-complete, then take `P' = p_{a+1}-⋯-p_{b+1}` (0-indexed
  `P[a] … P[b]`).
* `exists_minmax_index` — *"Choose `h,k` with `1 ≤ h ≤ k ≤ n` such that `v` is adjacent to
  `p_h, p_k`, with `h` minimum and `k` maximum"* and *"Choose `i,j` with `2 ≤ i ≤ j ≤ n` such that
  `p_i, p_j` are `Y`-complete, with `i` minimum and `j` maximum"*: one generic
  `Finset.min'`/`Finset.max'` extraction serving both.
* `conclusion_of_no_neighbour` — the parenthetical *"(If this is impossible then the conclusion
  holds.)"* in its degenerate form: `v` has no neighbour in `P` at all.
* `infix_eq_slice` / `slice_infix` — the bridge between `<:+:` (the vocabulary in which the
  **statements** 18.3, 18.5 and 18.6 are frozen) and `PathBasics.*_slice` (the vocabulary
  everything is actually **proved** in).  Needed for 18.3's maximality side condition.
* `setup` — the standing data, read off the pseudowheel together with the proof's first two
  sentences: *"By 18.3 it follows that …"* (so `pathLength P` is even) and *"`j − i ≥ 3` by
  18.4"* (whose first consequence is `n ≥ 7`).
* `claim2_witness` / `claim2_of_neighbour` — the positive branch of printed claim `(2)`:
  *"there is a `Y`-complete vertex in `{p_{i+1}, …, p_{j-1}}`.  If `v` has a neighbour in
  this set then the claim holds"*.  `claim2_of_neighbour` takes just a neighbour index and a
  `Y`-complete index, both strictly between `i` and `j`, and returns the positive branch of
  printed claim `(2)` outright.  Both are proved.
* `claim1` — the printed claim `(1)`, *"if `v` is both adjacent to `p₁` and `X`-complete then
  the conclusion holds"*; cited by claim `(2)` and by claim `(3)`.

Index convention: the paper's `p_a` is `P[a-1]` (0-indexed).  In particular the paper's
`2 ≤ i ≤ j ≤ n` becomes `1 ≤ i ≤ j < P.length`, and the paper's set
`{p_{i+1}, …, p_{j-1}}` becomes `{P[t] | i < t < j}`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm185Helpers

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Pseudowheels Workspace.Types.Pseudowheels.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.ProofLemmas

variable {V : Type*}

theorem subpath_window (G : SimpleGraph V) (X Y : Set V) (P : List V)
    (hP : IsPathList G P) (p₁ pₙ : V)
    (hhead : P.head? = some p₁) (hlast : P.getLast? = some pₙ)
    (v : V) (a b : ℕ) (hab : a ≤ b) (hb : b < P.length)
    (hnbr : ∀ (t : ℕ) (ht : t < P.length), G.Adj v (P[t]'ht) → a ≤ t ∧ t ≤ b)
    (hYint : ∀ (t : ℕ) (ht : t < P.length), a < t → t < b →
      ¬ VertexComplete G (P[t]'ht) Y)
    (hXc : VertexComplete G v X → ((a = 0 ∧ b = 0) ∨ b = P.length - 1)) :
    ∃ q : List V, IsPathList G q ∧ q <:+: P ∧
      (∀ w ∈ P, G.Adj v w → w ∈ q) ∧
      (∀ w ∈ SPGT.interior q, ¬ VertexComplete G w Y) ∧
      (VertexComplete G v X → ({w : V | w ∈ q} = {p₁} ∨ pₙ ∈ q)) := by
  classical
  set q : List V := (P.drop a).take (b - a + 1) with hq
  have hlenq : q.length = b - a + 1 := PathBasics.length_slice P hab hb
  have hqmem : ∀ {x : V}, x ∈ q ↔ ∃ (k : ℕ) (hk : k < P.length), a ≤ k ∧ k ≤ b ∧ (P[k]'hk) = x :=
    fun {x} => PathBasics.mem_slice_iff P hab hb
  -- the slice is a path
  have hqpath : IsPathList G q := by
    rcases Nat.lt_or_ge a b with hlt | hge
    · exact PathBasics.isPathList_slice hP hlt hb
    · have hEq : a = b := le_antisymm hab hge
      have h1 : q.length = 1 := by omega
      obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp h1
      have : q = [x] := hx
      rw [this]
      exact PathBasics.isPathList_singleton G x
  -- the slice is an infix
  have hqinf : q <:+: P := by
    refine ⟨P.take a, (P.drop a).drop (b - a + 1), ?_⟩
    rw [hq, List.append_assoc, List.take_append_drop, List.take_append_drop]
  refine ⟨q, hqpath, hqinf, ?_, ?_, ?_⟩
  · -- all neighbours of `v` in `P` lie in `q`
    intro w hw hadj
    obtain ⟨t, ht, hEq⟩ := List.mem_iff_getElem.mp hw
    have hrange := hnbr t ht (by rw [hEq]; exact hadj)
    exact hqmem.mpr ⟨t, ht, hrange.1, hrange.2, hEq⟩
  · -- no `Y`-complete vertex in the interior
    intro w hw
    rcases Nat.lt_or_ge a b with hlt | hge
    · obtain ⟨k, hk, hak, hkb, hEq⟩ :=
        (PathBasics.mem_interior_slice_iff hP hlt hb).mp hw
      rw [← hEq]
      exact hYint k hk hak hkb
    · exfalso
      have h1 : q.length = 1 := by omega
      have : (SPGT.interior q).length = q.length - 2 := PathBasics.interior_length q
      rw [h1] at this
      have : SPGT.interior q = [] := List.eq_nil_of_length_eq_zero (by omega)
      rw [this] at hw
      simp at hw
  · -- the `X`-complete clause
    intro hvX
    rcases hXc hvX with ⟨ha0, hb0⟩ | hbn
    · left
      have hPpos : 0 < P.length := by omega
      have hp0 : (P[0]'hPpos) = p₁ := PathBasics.getElem_zero_of_head? hhead hPpos
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
      constructor
      · intro hx
        obtain ⟨k, hk, hak, hkb, hEq⟩ := hqmem.mp hx
        have : k = 0 := by omega
        subst this
        rw [← hEq, hp0]
      · intro hx
        subst hx
        exact hqmem.mpr ⟨0, hPpos, by omega, by omega, hp0⟩
    · right
      have hPpos : 0 < P.length := by omega
      have hpl : (P[P.length - 1]'(by omega)) = pₙ :=
        PathBasics.getElem_last_of_getLast? hlast hPpos
      refine hqmem.mpr ⟨P.length - 1, by omega, by omega, by omega, hpl⟩

theorem exists_minmax_index (n lo : ℕ) (Q : ℕ → Prop)
    (hex : ∃ t, t < n ∧ lo ≤ t ∧ Q t) :
    ∃ i j : ℕ, i < n ∧ j < n ∧ lo ≤ i ∧ i ≤ j ∧ Q i ∧ Q j ∧
      ∀ t, t < n → lo ≤ t → Q t → i ≤ t ∧ t ≤ j := by
  classical
  set S : Finset ℕ := (Finset.range n).filter (fun t => lo ≤ t ∧ Q t) with hS
  have hmem : ∀ t, t ∈ S ↔ (t < n ∧ lo ≤ t ∧ Q t) := by
    intro t
    simp only [hS, Finset.mem_filter, Finset.mem_range, and_assoc]
  obtain ⟨t₀, ht₀⟩ := hex
  have hne : S.Nonempty := ⟨t₀, (hmem t₀).mpr ht₀⟩
  refine ⟨S.min' hne, S.max' hne, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ((hmem _).mp (S.min'_mem hne)).1
  · exact ((hmem _).mp (S.max'_mem hne)).1
  · exact ((hmem _).mp (S.min'_mem hne)).2.1
  · exact S.min'_le _ (S.max'_mem hne)
  · exact ((hmem _).mp (S.min'_mem hne)).2.2
  · exact ((hmem _).mp (S.max'_mem hne)).2.2
  · intro t htn htlo hQ
    have ht : t ∈ S := (hmem t).mpr ⟨htn, htlo, hQ⟩
    exact ⟨S.min'_le _ ht, S.le_max' _ ht⟩

theorem conclusion_of_no_neighbour (G : SimpleGraph V) (X Y : Set V) (P : List V)
    (hP : IsPathList G P) (p₁ pₙ : V)
    (hhead : P.head? = some p₁) (hlast : P.getLast? = some pₙ)
    (v : V) (hno : ∀ w ∈ P, ¬ G.Adj v w) :
    ∃ q : List V, IsPathList G q ∧ q <:+: P ∧
      (∀ w ∈ P, G.Adj v w → w ∈ q) ∧
      (∀ w ∈ SPGT.interior q, ¬ VertexComplete G w Y) ∧
      (VertexComplete G v X → ({w : V | w ∈ q} = {p₁} ∨ pₙ ∈ q)) := by
  refine subpath_window G X Y P hP p₁ pₙ hhead hlast v 0 0 le_rfl
    (PathBasics.path_length_pos hP) ?_ (by omega) (fun _ => Or.inl ⟨rfl, rfl⟩)
  intro t ht hadj
  exact absurd hadj (hno _ (List.getElem_mem ht))

theorem infix_eq_slice (r P : List V) (h : r <:+: P) :
    ∃ a : ℕ, a + r.length ≤ P.length ∧ r = (P.drop a).take r.length := by
  obtain ⟨s, t, hst⟩ := h
  refine ⟨s.length, ?_, ?_⟩
  · have : P.length = s.length + r.length + t.length := by
      rw [← hst]; simp [List.length_append]; omega
    omega
  · rw [← hst, List.append_assoc, List.drop_left, List.take_left]

theorem slice_infix (P : List V) (a m : ℕ) : (P.drop a).take m <:+: P := by
  exact ⟨P.take a, (P.drop a).drop m, by
    rw [List.append_assoc, List.take_append_drop, List.take_append_drop]⟩

section Setup

variable [Fintype V] [DecidableEq V]

theorem setup (G : SimpleGraph V) (hG : InF7 G) (X Y : Set V) (P : List V) (p₁ pₙ : V)
    (hpw : IsPseudowheel G X Y P)
    (hhead : P.head? = some p₁) (hlast : P.getLast? = some pₙ) :
    IsPathList G P ∧ 7 ≤ P.length ∧ Even (pathLength P) ∧
      (∀ w ∈ P, w ∉ X ∪ Y) ∧
      (∀ w ∈ P, VertexComplete G w X ↔ (w = p₁ ∨ w = pₙ)) ∧
      VertexComplete G p₁ Y ∧ ¬ VertexComplete G pₙ Y ∧
      (∀ (h1 : 1 < P.length), ¬ VertexComplete G (P[1]'h1) Y) ∧
      (∃ t, ∃ (ht : t < P.length), 1 ≤ t ∧ VertexComplete G (P[t]'ht) Y) := by
  obtain ⟨hXY, ⟨q₁, q₂, qₙ, ⟨hpf, htl, hout, hn5⟩, hXuniq, hY1, hYother, hY2, hYn⟩⟩ := hpw
  have hq₁ : q₁ = p₁ := by
    have := hpf.2.1; rw [hhead] at this; exact (Option.some.inj this).symm
  have hqₙ : qₙ = pₙ := by
    have := hpf.2.2; rw [hlast] at this; exact (Option.some.inj this).symm
  rw [hq₁, hqₙ] at hpf hXuniq
  rw [hq₁] at hY1 hYother
  rw [hqₙ] at hYn
  have hP : IsPathList G P := hpf.1
  have hpos : 0 < P.length := PathBasics.path_length_pos hP
  have hp0 : (P[0]'hpos) = p₁ := PathBasics.getElem_zero_of_head? hhead hpos
  -- 18.4: `pathLength P ≥ 6`, so `n ≥ 7`
  have h184 := _root_.Workspace.Statements.S18.SPGT.thm_18_4 G hG X Y P
    ⟨hXY, ⟨p₁, q₂, pₙ, ⟨hpf, htl, hout, hn5⟩, hXuniq, hY1, hYother, hY2, hYn⟩⟩
  have hlen7 : 7 ≤ P.length := by
    have := h184.2
    rw [pathLength] at this
    omega
  -- 18.3: `pathLength P` is even
  have houtU : ∀ w ∈ P, w ∉ X ∪ Y := by
    intro w hw hmem
    rcases hmem with h | h
    · exact (hout w hw).1 h
    · exact (hout w hw).2 h
  have h183 := _root_.Workspace.Statements.S18.SPGT.thm_18_3 G hG X Y hXY.1 hXY.2.1 hXY.2.2.1
    hXY.2.2.2.1 hXY.2.2.2.2.1 hXY.2.2.2.2.2 P p₁ pₙ hP houtU (by omega) hhead hlast hXuniq
  refine ⟨hP, hlen7, h183.1, houtU, hXuniq, hY1, hYn, ?_, ?_⟩
  · intro h1
    have htail : (P.tail)[0]'(by simp; omega) = q₂ :=
      PathBasics.getElem_zero_of_head? htl (by simp; omega)
    have : (P[1]'h1) = q₂ := by rw [← htail]; simp
    rw [this]; exact hY2
  · obtain ⟨w, hw, hwne, hwY⟩ := hYother
    obtain ⟨t, ht, hEq⟩ := List.mem_iff_getElem.mp hw
    refine ⟨t, ht, ?_, by rw [hEq]; exact hwY⟩
    rcases Nat.eq_zero_or_pos t with rfl | h
    · exact absurd (by rw [← hEq, hp0]) hwne
    · exact h

end Setup

/-- The positive half of printed claim `(2)` of 18.5: *"If `v` has a neighbour in this set then
the claim holds"*.

Given an index window `[a,b]` of the path `P` whose two ends are, in one order or the other, a
neighbour `P[t]` of `v` and a `Y`-complete vertex `P[r]`, and inside which `P[t]` is the *only*
neighbour of `v` and `P[r]` the *only* `Y`-complete vertex, the path `Q = v-P[t]-⋯-P[r]` is
exactly the object claim `(2)` asks for.  Callers obtain such a window by taking `r` the nearest
`Y`-complete index to a neighbour of `v` and then `t` the nearest neighbour index to `r`, both
searches staying inside the printed range `{p_{i+1}, …, p_{j-1}}`. -/
theorem claim2_witness (G : SimpleGraph V) (Y : Set V) (P : List V) (hP : IsPathList G P)
    (v : V) (hvP : v ∉ P) (hvY : ¬ VertexComplete G v Y)
    (a b t r : ℕ) (hab : a ≤ b) (hb : b < P.length)
    (ht : t < P.length) (hr : r < P.length)
    (hor : (t = a ∧ r = b) ∨ (t = b ∧ r = a))
    (hadj : G.Adj v (P[t]'ht)) (hYr : VertexComplete G (P[r]'hr) Y)
    (hnb : ∀ (m : ℕ) (hm : m < P.length), a ≤ m → m ≤ b → G.Adj v (P[m]'hm) → m = t)
    (hyc : ∀ (m : ℕ) (hm : m < P.length), a ≤ m → m ≤ b →
      VertexComplete G (P[m]'hm) Y → m = r) :
    ∃ (Q : List V) (q : V), IsPathFrom G Q v q ∧
      (∀ w ∈ Q, VertexComplete G w Y ↔ w = q) ∧
      (∀ w ∈ Q, w ≠ v → ∃ (m : ℕ) (hm : m < P.length),
        a ≤ m ∧ m ≤ b ∧ (P[m]'hm) = w) := by
  classical
  have geq : ∀ (m m' : ℕ) (hm : m < P.length) (hm' : m' < P.length),
      m = m' → (P[m]'hm) = (P[m']'hm') := by
    intro m m' hm hm' h; subst h; rfl
  have key : ∀ L : List V, IsPathFrom G L (P[t]'ht) (P[r]'hr) →
      (∀ w, w ∈ L ↔ ∃ (m : ℕ) (hm : m < P.length), a ≤ m ∧ m ≤ b ∧ (P[m]'hm) = w) →
      ∃ (Q : List V) (q : V), IsPathFrom G Q v q ∧
        (∀ w ∈ Q, VertexComplete G w Y ↔ w = q) ∧
        (∀ w ∈ Q, w ≠ v → ∃ (m : ℕ) (hm : m < P.length),
          a ≤ m ∧ m ≤ b ∧ (P[m]'hm) = w) := by
    intro L hL hmem
    have hvL : v ∉ L := by
      intro hv
      obtain ⟨m, hm, -, -, hEq⟩ := (hmem v).mp hv
      exact hvP (by rw [← hEq]; exact List.getElem_mem hm)
    have hQ : IsPathFrom G (v :: L) v (P[r]'hr) := by
      refine PathAttach.isPathFrom_cons hL hadj hvL ?_
      intro x hx hxne hadjx
      obtain ⟨m, hm, ham, hmb, hEq⟩ := (hmem x).mp hx
      have hmt : m = t := hnb m hm ham hmb (by rw [hEq]; exact hadjx)
      exact hxne (by rw [← hEq]; exact geq m t hm ht hmt)
    refine ⟨v :: L, P[r]'hr, hQ, ?_, ?_⟩
    · intro w hw
      rcases List.mem_cons.mp hw with rfl | hwL
      · constructor
        · intro hc; exact absurd hc hvY
        · intro hc; exact absurd (by rw [hc]; exact List.getElem_mem hr) hvP
      · obtain ⟨m, hm, ham, hmb, hEq⟩ := (hmem w).mp hwL
        constructor
        · intro hc
          have hmr : m = r := hyc m hm ham hmb (by rw [hEq]; exact hc)
          rw [← hEq]; exact geq m r hm hr hmr
        · intro hc; rw [hc]; exact hYr
    · intro w hw hwv
      rcases List.mem_cons.mp hw with rfl | hwL
      · exact absurd rfl hwv
      · exact (hmem w).mp hwL
  rcases Nat.eq_or_lt_of_le hab with heq | hlt
  · -- degenerate window: `t = r = a = b`, and `Q` is the single edge `v-P[t]`
    have htr : t = r := by rcases hor with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
    refine key [P[t]'ht] ?_ ?_
    · refine ⟨PathBasics.isPathList_singleton G _, rfl, ?_⟩
      simp [geq t r ht hr htr]
    · intro w
      constructor
      · intro hw
        refine ⟨t, ht, ?_, ?_, ?_⟩
        · rcases hor with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
        · rcases hor with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
        · have hwt : w = P[t]'ht := by simpa using hw
          exact hwt.symm
      · rintro ⟨m, hm, ham, hmb, hEq⟩
        have : m = t := by rcases hor with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
        rw [← hEq, geq m t hm ht this]
        simp
  · have hsl : IsPathFrom G ((P.drop a).take (b - a + 1)) (P[a]'(by omega)) (P[b]'hb) :=
      PathBasics.isPathFrom_slice hP hlt hb
    have hmemsl : ∀ w, w ∈ (P.drop a).take (b - a + 1) ↔
        ∃ (m : ℕ) (hm : m < P.length), a ≤ m ∧ m ≤ b ∧ (P[m]'hm) = w :=
      fun w => PathBasics.mem_slice_iff P hab hb
    rcases hor with ⟨hta, hrb⟩ | ⟨htb, hra⟩
    · refine key ((P.drop a).take (b - a + 1)) ?_ hmemsl
      rw [geq t a ht (by omega) hta, geq r b hr hb hrb]
      exact hsl
    · refine key ((P.drop a).take (b - a + 1)).reverse ?_ ?_
      · rw [geq t b ht hb htb, geq r a hr (by omega) hra]
        exact PathBasics.isPathFrom_reverse hsl
      · intro w
        rw [List.mem_reverse]
        exact hmemsl w

/-- The *"for otherwise the conclusion holds"* exit used when every neighbour of `v` in `P` has
index `≥ c` and no `P[t]` with `t > c` is `Y`-complete: take `P' = p_{c+1}-⋯-p_n`.  In printed
claim `(2)` this is *"We may assume `v` has a neighbour in `{p_1, …, p_i}`, for otherwise the
conclusion holds"*, with `c = j`; the `X`-complete clause is free because `p_n ∈ V(P')`. -/
theorem window_after (G : SimpleGraph V) (X Y : Set V) (P : List V)
    (hP : IsPathList G P) (p₁ pₙ : V)
    (hhead : P.head? = some p₁) (hlast : P.getLast? = some pₙ)
    (v : V) (c : ℕ) (hc : c < P.length)
    (hnbr : ∀ (t : ℕ) (ht : t < P.length), G.Adj v (P[t]'ht) → c ≤ t)
    (hYabove : ∀ (t : ℕ) (ht : t < P.length), c < t → ¬ VertexComplete G (P[t]'ht) Y) :
    ∃ q : List V, IsPathList G q ∧ q <:+: P ∧
      (∀ w ∈ P, G.Adj v w → w ∈ q) ∧
      (∀ w ∈ SPGT.interior q, ¬ VertexComplete G w Y) ∧
      (VertexComplete G v X → ({w : V | w ∈ q} = {p₁} ∨ pₙ ∈ q)) :=
  subpath_window G X Y P hP p₁ pₙ hhead hlast v c (P.length - 1) (by omega) (by omega)
    (fun t ht hadjt => ⟨hnbr t ht hadjt, by omega⟩)
    (fun t ht h1 _ => hYabove t ht h1) (fun _ => Or.inr rfl)

/-- The *"then the conclusion holds"* exit used when `v` is **not** `X`-complete and every
neighbour of `v` in `P` has index `≤ c`, no `P[t]` with `1 ≤ t < c` being `Y`-complete: take
`P' = p_{a+1}-⋯-p_{c+1}` where `a` is the least neighbour index.  In printed claim `(2)` this is
*"So `v` has no neighbours in `{p_j, …, p_n}`, and hence `k ≤ i`.  We may therefore assume that
`v` is `X`-complete"*, with `c = i`.  The degenerate case *"(If this is impossible then the
conclusion holds.)"* — `v` has no neighbour in `P` at all — is folded in. -/
theorem window_le (G : SimpleGraph V) (X Y : Set V) (P : List V)
    (hP : IsPathList G P) (p₁ pₙ : V)
    (hhead : P.head? = some p₁) (hlast : P.getLast? = some pₙ)
    (v : V) (hvX : ¬ VertexComplete G v X) (c : ℕ) (hc : c < P.length)
    (hnbr : ∀ (t : ℕ) (ht : t < P.length), G.Adj v (P[t]'ht) → t ≤ c)
    (hYbelow : ∀ (t : ℕ) (ht : t < P.length), 1 ≤ t → t < c →
      ¬ VertexComplete G (P[t]'ht) Y) :
    ∃ q : List V, IsPathList G q ∧ q <:+: P ∧
      (∀ w ∈ P, G.Adj v w → w ∈ q) ∧
      (∀ w ∈ SPGT.interior q, ¬ VertexComplete G w Y) ∧
      (VertexComplete G v X → ({w : V | w ∈ q} = {p₁} ∨ pₙ ∈ q)) := by
  classical
  by_cases hex : ∃ (t : ℕ) (ht : t < P.length), G.Adj v (P[t]'ht)
  · obtain ⟨a, ha, hamin⟩ : ∃ a, (∃ ht : a < P.length, G.Adj v (P[a]'ht)) ∧
        ∀ m, (∃ hm : m < P.length, G.Adj v (P[m]'hm)) → a ≤ m := by
      have hne : ((Finset.range P.length).filter
          (fun m => ∃ hm : m < P.length, G.Adj v (P[m]'hm))).Nonempty := by
        obtain ⟨t, ht, hadjt⟩ := hex
        exact ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ht, ⟨ht, hadjt⟩⟩⟩
      obtain ⟨-, hadj⟩ := Finset.mem_filter.mp (Finset.min'_mem _ hne)
      refine ⟨_, hadj, ?_⟩
      intro m hm
      obtain ⟨hmlen, hmadj⟩ := hm
      exact Finset.min'_le _ m
        (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hmlen, ⟨hmlen, hmadj⟩⟩)
    obtain ⟨halen, hadja⟩ := ha
    exact subpath_window G X Y P hP p₁ pₙ hhead hlast v a c (hnbr a halen hadja) hc
      (fun t ht hadjt => ⟨hamin t ⟨ht, hadjt⟩, hnbr t ht hadjt⟩)
      (fun t ht h1 h2 => hYbelow t ht (by omega) h2) (fun h => absurd h hvX)
  · refine conclusion_of_no_neighbour G X Y P hP p₁ pₙ hhead hlast v ?_
    intro w hw hadjw
    obtain ⟨t, ht, hEq⟩ := List.mem_iff_getElem.mp hw
    exact hex ⟨t, ht, by rw [hEq]; exact hadjw⟩

/-- *"Then there is a hole `C` containing `v`, with `C \ v ⊆ P`"* (printed claim `(2)`).

`P[a]` and `P[b]` are neighbours of `v` with no neighbour of `v` strictly between them, so
`v-p_{a+1}-⋯-p_{b+1}-v` closes up.  Callers take `a` the **largest** neighbour index `≤ i` and
`b` the **smallest** neighbour index `≥ j`, which makes the hypothesis `hmid` exactly *"`v` has
no neighbour in `{p_{i+1}, …, p_{j-1}}`"* plus the two extremality choices; the resulting hole
contains `p_i-⋯-p_j`, as the printed proof needs. -/
theorem hole_from_two_neighbours (G : SimpleGraph V) (P : List V) (hP : IsPathList G P)
    (v : V) (hvP : v ∉ P) (a b : ℕ) (hab : a + 2 ≤ b) (hb : b < P.length)
    (hva : G.Adj v (P[a]'(by omega))) (hvb : G.Adj v (P[b]'hb))
    (hmid : ∀ (m : ℕ) (hm : m < P.length), a < m → m < b → ¬ G.Adj v (P[m]'hm)) :
    IsHoleList G (v :: (P.drop a).take (b - a + 1)) := by
  have hlt : a < b := by omega
  have hsl : IsPathFrom G ((P.drop a).take (b - a + 1)) (P[a]'(by omega)) (P[b]'hb) :=
    PathBasics.isPathFrom_slice hP hlt hb
  refine PrismBasics.isHoleList_of_path_add_vertex hsl ?_ hva hvb ?_ ?_
  · have hlen := PathBasics.length_slice P (le_of_lt hlt) hb
    rw [PathBasics.pathLength_eq]
    omega
  · intro hmem
    obtain ⟨m, hm, -, -, hEq⟩ := (PathBasics.mem_slice_iff P (le_of_lt hlt) hb).mp hmem
    exact hvP (by rw [← hEq]; exact List.getElem_mem hm)
  · intro x hx hadjx
    obtain ⟨m, hm, ham, hmb, hEq⟩ := (PathBasics.mem_interior_slice_iff hP hlt hb).mp hx
    exact hmid m hm ham hmb (by rw [hEq]; exact hadjx)

/-- Printed claim `(2)` of 18.5, positive branch: *"there is a `Y`-complete vertex in
`{p_{i+1}, …, p_{j-1}}`.  If `v` has a neighbour in this set then the claim holds"*.

`P[t]` is the neighbour of `v` and `P[s]` the `Y`-complete vertex, both with index strictly
between `i` and `j`; the conclusion is exactly the positive branch of printed claim `(2)`.  The `Q` produced
runs from `v` to the `Y`-complete vertex nearest to `P[t]` on the `P[s]` side, entered at the
neighbour of `v` nearest to that vertex — so `v` has exactly one neighbour on `Q \ v` and `Q`
carries exactly one `Y`-complete vertex, its far end. -/
theorem claim2_of_neighbour (G : SimpleGraph V) (Y : Set V) (P : List V) (hP : IsPathList G P)
    (v : V) (hvP : v ∉ P) (hvY : ¬ VertexComplete G v Y)
    (i j t s : ℕ) (ht : t < P.length) (hs : s < P.length)
    (hit : i < t) (htj : t < j) (his : i < s) (hsj : s < j)
    (hadj : G.Adj v (P[t]'ht)) (hsY : VertexComplete G (P[s]'hs) Y) :
    ∃ (Q : List V) (q : V), IsPathFrom G Q v q ∧
      (∀ w ∈ Q, VertexComplete G w Y ↔ w = q) ∧
      (∀ w ∈ Q, w ≠ v → ∃ (m : ℕ) (hm : m < P.length),
        i < m ∧ m < j ∧ (P[m]'hm) = w) := by
  classical
  have hYCs : ∃ hm : s < P.length, VertexComplete G (P[s]'hm) Y := ⟨hs, hsY⟩
  have hNBt : ∃ hm : t < P.length, G.Adj v (P[t]'hm) := ⟨ht, hadj⟩
  rcases le_total t s with hts | hst
  · obtain ⟨r, hrl, hrr, hrYC, hrmin⟩ :
        ∃ r, t ≤ r ∧ r ≤ s ∧ (∃ hm : r < P.length, VertexComplete G (P[r]'hm) Y) ∧
          ∀ m, t ≤ m → m ≤ s → (∃ hm : m < P.length, VertexComplete G (P[m]'hm) Y) → r ≤ m := by
      have hne : ((Finset.Icc t s).filter
          (fun m => ∃ hm : m < P.length, VertexComplete G (P[m]'hm) Y)).Nonempty :=
        ⟨s, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hts, le_rfl⟩, hYCs⟩⟩
      obtain ⟨hIcc, hYC⟩ := Finset.mem_filter.mp (Finset.min'_mem _ hne)
      obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hIcc
      exact ⟨_, h1, h2, hYC, fun m hm1 hm2 hm3 =>
        Finset.min'_le _ m (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hm1, hm2⟩, hm3⟩)⟩
    obtain ⟨u, hul, hur, huNB, humax⟩ :
        ∃ u, t ≤ u ∧ u ≤ r ∧ (∃ hm : u < P.length, G.Adj v (P[u]'hm)) ∧
          ∀ m, t ≤ m → m ≤ r → (∃ hm : m < P.length, G.Adj v (P[m]'hm)) → m ≤ u := by
      have hne : ((Finset.Icc t r).filter
          (fun m => ∃ hm : m < P.length, G.Adj v (P[m]'hm))).Nonempty :=
        ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨le_rfl, hrl⟩, hNBt⟩⟩
      obtain ⟨hIcc, hNB⟩ := Finset.mem_filter.mp (Finset.max'_mem _ hne)
      obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hIcc
      exact ⟨_, h1, h2, hNB, fun m hm1 hm2 hm3 =>
        Finset.le_max' _ m (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hm1, hm2⟩, hm3⟩)⟩
    obtain ⟨hulen, huadj⟩ := huNB
    obtain ⟨hrlen, hrY⟩ := hrYC
    obtain ⟨Q, q, h1, h2, h3⟩ := claim2_witness G Y P hP v hvP hvY u r u r
      hur hrlen hulen hrlen (Or.inl ⟨rfl, rfl⟩) huadj hrY
      (fun m hm ham hmb hadjm =>
        le_antisymm (humax m (le_trans hul ham) hmb ⟨hm, hadjm⟩) ham)
      (fun m hm ham hmb hYm =>
        le_antisymm hmb (hrmin m (le_trans hul ham) (le_trans hmb hrr) ⟨hm, hYm⟩))
    refine ⟨Q, q, h1, h2, ?_⟩
    intro w hw hwv
    obtain ⟨m, hm, ham, hmb, hEq⟩ := h3 w hw hwv
    exact ⟨m, hm, by omega, by omega, hEq⟩
  · obtain ⟨r, hrl, hrr, hrYC, hrmax⟩ :
        ∃ r, s ≤ r ∧ r ≤ t ∧ (∃ hm : r < P.length, VertexComplete G (P[r]'hm) Y) ∧
          ∀ m, s ≤ m → m ≤ t → (∃ hm : m < P.length, VertexComplete G (P[m]'hm) Y) → m ≤ r := by
      have hne : ((Finset.Icc s t).filter
          (fun m => ∃ hm : m < P.length, VertexComplete G (P[m]'hm) Y)).Nonempty :=
        ⟨s, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨le_rfl, hst⟩, hYCs⟩⟩
      obtain ⟨hIcc, hYC⟩ := Finset.mem_filter.mp (Finset.max'_mem _ hne)
      obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hIcc
      exact ⟨_, h1, h2, hYC, fun m hm1 hm2 hm3 =>
        Finset.le_max' _ m (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hm1, hm2⟩, hm3⟩)⟩
    obtain ⟨u, hul, hur, huNB, humin⟩ :
        ∃ u, r ≤ u ∧ u ≤ t ∧ (∃ hm : u < P.length, G.Adj v (P[u]'hm)) ∧
          ∀ m, r ≤ m → m ≤ t → (∃ hm : m < P.length, G.Adj v (P[m]'hm)) → u ≤ m := by
      have hne : ((Finset.Icc r t).filter
          (fun m => ∃ hm : m < P.length, G.Adj v (P[m]'hm))).Nonempty :=
        ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hrr, le_rfl⟩, hNBt⟩⟩
      obtain ⟨hIcc, hNB⟩ := Finset.mem_filter.mp (Finset.min'_mem _ hne)
      obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hIcc
      exact ⟨_, h1, h2, hNB, fun m hm1 hm2 hm3 =>
        Finset.min'_le _ m (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hm1, hm2⟩, hm3⟩)⟩
    obtain ⟨hulen, huadj⟩ := huNB
    obtain ⟨hrlen, hrY⟩ := hrYC
    obtain ⟨Q, q, h1, h2, h3⟩ := claim2_witness G Y P hP v hvP hvY r u u r
      hul hulen hulen hrlen (Or.inr ⟨rfl, rfl⟩) huadj hrY
      (fun m hm ham hmb hadjm =>
        le_antisymm hmb (humin m ham (le_trans hmb hur) ⟨hm, hadjm⟩))
      (fun m hm ham hmb hYm =>
        le_antisymm (hrmax m (le_trans hrl ham) (le_trans hmb hur) ⟨hm, hYm⟩) ham)
    refine ⟨Q, q, h1, h2, ?_⟩
    intro w hw hwv
    obtain ⟨m, hm, ham, hmb, hEq⟩ := h3 w hw hwv
    exact ⟨m, hm, by omega, by omega, hEq⟩

section Claim1

variable [Fintype V] [DecidableEq V]

/-- **Printed claim `(1)` of the proof of 18.5** (`paper/proofs/18_5.md`, published p. 111):

> *"(1) If `v` is both adjacent to `p₁` and `X`-complete then the conclusion holds.*
>
> *For from the optimality of `(X, Y, P)` it follows that `(X, Y ∪ {v}, P)` is not a
> pseudowheel, and so `p₁` is the only `Y ∪ {v}`-complete vertex in `P`.  By 2.11 (with
> `X, Y` replaced by `Y ∪ {v}, X`) we deduce that either there exists `y ∈ Y ∪ {v}`
> nonadjacent to all `p₂, …, p_n`, or there exist nonadjacent `y₁, y₂ ∈ Y ∪ {v}` such that
> `y₁-p₂-⋯-p_n-y₂` is a path.  But `p_i` is `Y`-complete and `3 ≤ i ≤ n − 1`, so the second
> statement does not hold; and the first holds only if `y = v`.  This proves (1)."*

*"the conclusion holds"* is the conclusion of 18.5 itself, i.e. exactly the conclusion of
`Thm185Claim3.claim3` / of the negative branch of printed claim `(2)` — so a caller in the `X`-complete
branch closes with `exact claim1 …` (or `exact Or.inl (claim1 …)` against the
disjunction of printed claim `(2)`).

The hypothesis prefix is the one shared by `Thm185Claim3.claim3`, `Thm185Claim4.claim4` and
`Thm185Final.finalCase`; the two extra hypotheses `hadj`, `hvX` are the printed
*"both adjacent to `p₁` and `X`-complete"*.  The indices `i, j` of the opening paragraph are
**not** parameters: the printed proof re-chooses them internally (*"but `p_i` is `Y`-complete
and `3 ≤ i ≤ n − 1`"*), and they are recoverable from `hopt` through `setup` and
`exists_minmax_index`. -/
theorem claim1 (G : SimpleGraph V) (hG : InF7 G) (X Y : Set V) (P : List V) (p₁ pₙ : V)
    (hopt : OptimalPseudowheel G X Y P)
    (hhead : P.head? = some p₁) (hlast : P.getLast? = some pₙ)
    (v : V) (hvXY : v ∉ X ∪ Y) (hvP : v ∉ P) (hvY : ¬ VertexComplete G v Y)
    (hadj : G.Adj v p₁) (hvX : VertexComplete G v X) :
    ∃ q : List V, IsPathList G q ∧ q <:+: P ∧
      (∀ w ∈ P, G.Adj v w → w ∈ q) ∧
      (∀ w ∈ SPGT.interior q, ¬ VertexComplete G w Y) ∧
      (VertexComplete G v X → ({w : V | w ∈ q} = {p₁} ∨ pₙ ∈ q)) := by
  classical
  have geq : ∀ (l : List V) (m m' : ℕ) (hm : m < l.length) (hm' : m' < l.length),
      m = m' → (l[m]'hm) = (l[m']'hm') := by
    intro l m m' hm hm' h; subst h; rfl
  obtain ⟨hP, hlen7, heven, houtU, hXuniq, hp₁Y, hpₙY, hP1Y, hYex⟩ :=
    setup G hG X Y P p₁ pₙ hopt.1 hhead hlast
  obtain ⟨⟨hXYd, hXne, hYne, hXa, hYa, hcompl⟩, q₁, q₂, qₙ,
    ⟨hpf, htl, hout, hn5⟩, -, -, -, hY2', -⟩ := hopt.1
  have hq₁ : q₁ = p₁ := by
    have h := hpf.2.1; rw [hhead] at h; exact (Option.some.inj h).symm
  have hqₙ : qₙ = pₙ := by
    have h := hpf.2.2; rw [hlast] at h; exact (Option.some.inj h).symm
  rw [hq₁, hqₙ] at hpf
  have hBerge : Berge G := hG.1.1.1.1
  have hvXm : v ∉ X := fun h => hvXY (Or.inl h)
  have hvYm : v ∉ Y := fun h => hvXY (Or.inr h)
  have hYvne : (Y ∪ ({v} : Set V)).Nonempty := ⟨v, Or.inr rfl⟩
  have hYva : AnticonnectedSet G (Y ∪ {v}) :=
    KiteTailBasics.anticonnectedSet_union_singleton hYa hvY
  have hsub : ∀ {w : V}, VertexComplete G w (Y ∪ {v}) → VertexComplete G w Y :=
    fun {w} h y hy => h y (Or.inl hy)
  have hvcp₁ : VertexComplete G p₁ (Y ∪ {v}) := by
    intro y hy
    rcases hy with hy | hy
    · exact hp₁Y y hy
    · rw [Set.mem_singleton_iff] at hy; rw [hy]; exact hadj.symm
  have hdisjXY : Disjoint X (Y ∪ {v}) := by
    rw [Set.disjoint_union_right]
    exact ⟨hXYd, Set.disjoint_singleton_right.mpr hvXm⟩
  have hcomplXY : Complete G X (Y ∪ {v}) := by
    intro x hx y hy
    rcases hy with hy | hy
    · exact hcompl x hx y hy
    · rw [Set.mem_singleton_iff] at hy; rw [hy]; exact (hvX x hx).symm
  have hout' : ∀ w ∈ P, w ∉ X ∧ w ∉ (Y ∪ ({v} : Set V)) := by
    intro w hw
    refine ⟨(hout w hw).1, ?_⟩
    rintro (h | h)
    · exact (hout w hw).2 h
    · rw [Set.mem_singleton_iff] at h; exact hvP (h ▸ hw)
  -- *"`p₁` is the only `Y ∪ {v}`-complete vertex in `P`"*
  have huniq : ∀ w ∈ P, (VertexComplete G w (Y ∪ {v}) ↔ w = p₁) := by
    intro w hw
    refine ⟨fun hwc => ?_, fun h => by rw [h]; exact hvcp₁⟩
    by_contra hne
    refine hopt.2.2 ⟨Y ∪ {v}, ⟨⟨hdisjXY, hXne, hYvne, hXa, hYva, hcomplXY⟩,
      p₁, q₂, pₙ, ⟨hpf, htl, hout', hn5⟩, hXuniq,
      ⟨hvcp₁, ⟨w, hw, hne, hwc⟩, fun hc => hY2' (hsub hc), fun hc => hpₙY (hsub hc)⟩⟩,
      Set.subset_union_left, fun hcon => hvYm (hcon (Or.inr rfl))⟩
  -- the `Y`-complete vertex `p_i` of the printed proof: `2 ≤ i ≤ n - 2` (0-indexed)
  obtain ⟨i, hi, h1i, hYi⟩ := hYex
  have hi2 : 2 ≤ i := by
    by_contra hcon
    have hi1 : i = 1 := by omega
    exact hP1Y (by omega) (by rw [← geq P i 1 hi (by omega) hi1]; exact hYi)
  have hilast : i ≤ P.length - 2 := by
    by_contra hcon
    have hieq : i = P.length - 1 := by omega
    refine hpₙY ?_
    have hpl := PathBasics.getElem_last_of_getLast? hlast (show 0 < P.length by omega)
    rw [← hpl, ← geq P i (P.length - 1) hi (by omega) hieq]
    exact hYi
  -- 2.11 with `X, Y` replaced by `Y ∪ {v}, X`
  have h211 := _root_.Workspace.Statements.S02.SPGT.thm_2_11 G hBerge (Y ∪ {v}) X
    (Disjoint.symm hdisjXY) hYvne hXne hYva hXa
    (fun y hy x hx => (hcomplXY x hx y hy).symm) P p₁ pₙ hP
    (fun w hw hcon => by
      rcases hcon with h | h
      · exact (hout' w hw).2 h
      · exact (hout' w hw).1 h)
    heven (by have := PathBasics.pathLength_eq P; omega) hhead hlast huniq hXuniq
  -- `P[i] ∈ P.tail`, the vertex the printed proof plays against both alternatives
  have htaili : (P.tail)[i - 1]'(by simp; omega) = (P[i]'hi) := by
    have h := List.getElem_tail (l := P) (i := i - 1) (h := by simp; omega)
    rw [h]
    exact geq P (i - 1 + 1) i (by omega) hi (by omega)
  have himem : (P[i]'hi) ∈ P.tail := by
    rw [← htaili]; exact List.getElem_mem _
  rcases h211 with ⟨y, hy, hno⟩ | ⟨x₁, hx₁, x₂, hx₂, hnadj, hpath⟩
  · -- *"the first holds only if `y = v`"*
    have hyv : y = v := by
      rcases hy with hy | hy
      · exact absurd ((hYi y hy).symm) (hno _ himem)
      · exact Set.mem_singleton_iff.mp hy
    rw [hyv] at hno
    -- so `v`'s only neighbour in `P` is `p₁`, and `P' = {p₁}` is the required subpath
    refine subpath_window G X Y P hP p₁ pₙ hhead hlast v 0 0 le_rfl
      (PathBasics.path_length_pos hP) ?_ (by omega) (fun _ => Or.inl ⟨rfl, rfl⟩)
    intro t ht hadjt
    refine ⟨Nat.zero_le _, ?_⟩
    by_contra hcon
    have ht1 : 1 ≤ t := by omega
    have htail : (P.tail)[t - 1]'(by simp; omega) = (P[t]'ht) := by
      have h := List.getElem_tail (l := P) (i := t - 1) (h := by simp; omega)
      rw [h]
      exact geq P (t - 1 + 1) t (by omega) ht (by omega)
    exact hno _ (by rw [← htail]; exact List.getElem_mem _) hadjt
  · -- *"`p_i` is `Y`-complete and `3 ≤ i ≤ n − 1`, so the second statement does not hold"*
    exfalso
    set L : List V := x₁ :: (P.tail ++ [x₂]) with hLdef
    have htl' : P.tail.length = P.length - 1 := by simp
    have hLlen : L.length = P.length + 1 := by
      simp [hLdef, htl']; omega
    have hL0 : (L[0]'(by omega)) = x₁ := rfl
    have hLmid : ∀ (m : ℕ) (hm : m < P.length), 1 ≤ m →
        (L[m]'(by omega)) = (P[m]'hm) := by
      intro m hm h1m
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      have h1 : (L[k + 1]'(by omega)) = ((P.tail ++ [x₂])[k]'(by simp [htl']; omega)) := by
        simp [hLdef]
      rw [h1, List.getElem_append_left (by omega)]
      have h := List.getElem_tail (l := P) (i := k) (h := by omega)
      rw [h]
    have hLend : (L[P.length]'(by omega)) = x₂ := by
      obtain ⟨k, hk⟩ : ∃ k, P.length = k + 1 := ⟨P.length - 1, by omega⟩
      rw [geq L P.length (k + 1) (by omega) (by omega) hk]
      have h1 : (L[k + 1]'(by omega)) = ((P.tail ++ [x₂])[k]'(by simp [htl']; omega)) := by
        simp [hLdef]
      rw [h1, List.getElem_append_right (by simp [htl']; omega)]
      simp [htl', hk]
    have hnotY : ∀ z : V, z ∈ (Y ∪ ({v} : Set V)) → z ∉ Y → z = v := by
      intro z hz hzY
      rcases hz with h | h
      · exact absurd h hzY
      · exact Set.mem_singleton_iff.mp h
    have hkey : ∀ (m : ℕ) (hm : m < L.length) (z : V), (L[m]'hm) = z → z ∈ Y →
        m = 0 ∨ m + 1 = L.length → False := by
      intro m hm z hEq hzY hend
      have hadjz : G.Adj (P[i]'hi) z := hYi z hzY
      have hLi : (L[i]'(by omega)) = (P[i]'hi) := hLmid i hi (by omega)
      have hadjL : G.Adj (L[i]'(by omega)) (L[m]'hm) := by
        rw [hLi, hEq]; exact hadjz
      have := (PathBasics.path_adj_iff hpath (by omega) hm).mp hadjL
      rcases hend with h | h <;> omega
    rcases Classical.em (x₁ ∈ Y) with h1 | h1
    · exact hkey 0 (by omega) x₁ hL0 h1 (Or.inl rfl)
    · rcases Classical.em (x₂ ∈ Y) with h2 | h2
      · exact hkey P.length (by omega) x₂ hLend h2 (Or.inr (by omega))
      · have e1 : x₁ = v := hnotY x₁ hx₁ h1
        have e2 : x₂ = v := hnotY x₂ hx₂ h2
        have hnd : L.Nodup := PathBasics.path_nodup hpath
        rw [hLdef] at hnd
        exact (List.nodup_cons.mp hnd).1 (by
          rw [e1]
          exact List.mem_append_right _ (by rw [← e2]; exact List.mem_singleton_self _))

end Claim1

end Workspace.ProofLemmas.Thm185Helpers
