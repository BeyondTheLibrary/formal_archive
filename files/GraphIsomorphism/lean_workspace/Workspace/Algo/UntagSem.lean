/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 4.1.1, line 2860: the cost `O(nk + n²m)` of the untagged naive refinement process.
The string process on a raw input, in terms of the ranks of the tagged process.
-/
import Workspace.Algo.TagLinSem
import Workspace.Refinement.NaiveStr

/-!
# The untagged string process on a raw input

A raw colored digraph `r` lists the colors (strings) of the vertices `0, …, n-1` and the
edges.  `Babai.ColoredDigraph.strIter` is the untagged process with colors written as strings
(`Refinement/NaiveStr.lean`).  When all input colors have the same length `k` (the paper: "each
color in `X` is described by a string of length `k`"):

* all colors of round `j` have the same length (`length_strIter`), and the lexicographic order
  of the colors of round `j` is the order of the colors `sX` of the tagged process
  (`strIter_le_iff`); so the position of a color in the palette is its rank `rX`
  (`idxOf_palette_strIter`), and the palette has `NX` colors;
* hence the color of round `j + 1` is `( c_j(x) , ⟨the counts of the tagged row⟩ )`
  (`strIter_succ_eq`), and after `K` rounds it is
  `(^K c₀(x) T₀(x) ⋯ T_{K-1}(x)` with `T_j(x)` read off the tagged row of round `j + 1`
  (`strIter_eq`);
* both processes stop at the same round (`strStop_eq`);
* the number of rounds is at most `2m` (`stopIdx_le_two_mul`): after round `1` the isolated
  vertices and the others have different colors, the classes of isolated vertices never split,
  and every later round that refines splits a class of the at most `2m` non-isolated vertices.

No axiom, no `sorry`.
-/

namespace Algo

open Babai Babai.ColoredDigraph

/-- A colored digraph as the RAM reads it: the list of vertex colors (vertex `i` has color
`r.1[i]`) and the list of edges. -/
abbrev RawColored := List (List ℕ) × List (ℕ × ℕ)

/-- Well-formed input: no repeated edge, no loop, and edge ends are vertices. -/
def RawColored.WF (r : RawColored) : Prop :=
  r.2.Nodup ∧ ∀ e ∈ r.2, e.1 < r.1.length ∧ e.2 < r.1.length ∧ e.1 ≠ e.2

/-- The colored digraph on `Fin n` that `r` describes. -/
def decColored (r : RawColored) : ColoredDigraph (Fin r.1.length) (List ℕ) :=
  ⟨{p | ((p.1 : ℕ), (p.2 : ℕ)) ∈ r.2}, fun i => r.1.get i⟩

/-- The same input with the empty tag. -/
def toTagged (r : RawColored) : RawTagged := (r.1, (r.2, []))

/-- The output `X* = (V, E, c*)` of the untagged process, colors as strings. -/
noncomputable def untagOut (r : RawColored) : RawColored :=
  (List.ofFn (decColored r).strStable, r.2)

theorem RawColored.WF.toTagged {r : RawColored} (h : r.WF) : (toTagged r).WF := h

/-! ## Order lemmas -/

theorem lcons_lt {x y : ℕ} {a b : List ℕ} : x :: a < y :: b ↔ x < y ∨ x = y ∧ a < b :=
  List.cons_lt_cons_iff

theorem lcons_le {x y : ℕ} {a b : List ℕ} : x :: a ≤ y :: b ↔ x < y ∨ x = y ∧ a ≤ b := by
  rw [le_iff_lt_or_eq, le_iff_lt_or_eq, lcons_lt, List.cons.injEq]
  constructor
  · rintro ((h | ⟨rfl, h⟩) | ⟨rfl, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨rfl, Or.inl h⟩
    · exact Or.inr ⟨rfl, Or.inr rfl⟩
  · rintro (h | ⟨rfl, h | rfl⟩)
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr ⟨rfl, h⟩)
    · exact Or.inr ⟨rfl, rfl⟩

theorem append_le_append_iff {a a' b b' : List ℕ} (h : a.length = a'.length) :
    a ++ b ≤ a' ++ b' ↔ a < a' ∨ (a = a' ∧ b ≤ b') := by
  induction a generalizing a' with
  | nil =>
    obtain rfl : a' = [] := List.eq_nil_of_length_eq_zero (by simpa using h.symm)
    simp
  | cons x as ih =>
    obtain ⟨y, as', rfl⟩ : ∃ y as', a' = y :: as' := by
      cases a' with
      | nil => simp at h
      | cons y as' => exact ⟨y, as', rfl⟩
    rw [List.cons_append, List.cons_append, lcons_le, lcons_lt, List.cons.injEq,
      ih (by simpa using h)]
    constructor
    · rintro (h1 | ⟨rfl, h2 | ⟨rfl, h3⟩⟩)
      · exact Or.inl (Or.inl h1)
      · exact Or.inl (Or.inr ⟨rfl, h2⟩)
      · exact Or.inr ⟨⟨rfl, rfl⟩, h3⟩
    · rintro ((h1 | ⟨rfl, h2⟩) | ⟨⟨rfl, rfl⟩, h3⟩)
      · exact Or.inl h1
      · exact Or.inr ⟨rfl, Or.inl h2⟩
      · exact Or.inr ⟨rfl, Or.inr ⟨rfl, h3⟩⟩

/-- A count list written with commas: `, d₁ , d₂ , … )`. -/
def encCnt (u : List ℕ) : List ℕ := u.flatMap (fun a => [lComma, lNum a]) ++ [lClose]

theorem length_flatMap_two (u : List ℕ) :
    (u.flatMap (fun a => [lComma, lNum a])).length = 2 * u.length := by
  induction u with
  | nil => simp
  | cons a u ih => simp [List.flatMap_cons, ih]; ring

theorem length_encCnt (u : List ℕ) : (encCnt u).length = 2 * u.length + 1 := by
  simp only [encCnt, List.length_append, length_flatMap_two, List.length_singleton]

theorem flatMap_two_le_iff {u v : List ℕ} (h : u.length = v.length) :
    u.flatMap (fun a => [lComma, lNum a]) ≤ v.flatMap (fun a => [lComma, lNum a]) ↔ u ≤ v := by
  induction u generalizing v with
  | nil =>
    obtain rfl : v = [] := List.eq_nil_of_length_eq_zero (by simpa using h.symm)
    simp
  | cons a u ih =>
    obtain ⟨b, v', rfl⟩ : ∃ b v', v = b :: v' := by
      cases v with
      | nil => simp at h
      | cons b v' => exact ⟨b, v', rfl⟩
    simp only [List.flatMap_cons, List.cons_append, List.nil_append]
    rw [lcons_le, lcons_le, lcons_le, ih (by simpa using h)]
    simp [lNum]

theorem encCnt_le_iff {u v : List ℕ} (h : u.length = v.length) :
    encCnt u ≤ encCnt v ↔ u ≤ v := by
  unfold encCnt
  rw [append_le_append_iff (by rw [length_flatMap_two, length_flatMap_two, h]),
    ← flatMap_two_le_iff h]
  simp only [le_refl, and_true]
  exact (le_iff_lt_or_eq).symm

theorem encCnt_inj {u v : List ℕ} (h : u.length = v.length) : encCnt u = encCnt v ↔ u = v := by
  constructor
  · intro e
    exact le_antisymm ((encCnt_le_iff h).1 e.le) ((encCnt_le_iff h.symm).1 e.ge)
  · rintro rfl; rfl

/-! ## Positions in a sorted image -/

theorem idxOf_eq_length_filter {β : Type*} [LinearOrder β] [BEq β] [LawfulBEq β] {L : List β} (hL : L.Pairwise (· < ·))
    {a : β}
    (ha : a ∈ L) : L.idxOf a = (L.filter (fun b => decide (b < a))).length := by
  induction L with
  | nil => simp at ha
  | cons b L ih =>
    rw [List.pairwise_cons] at hL
    by_cases hab : b = a
    · subst hab
      rw [List.idxOf_cons_self]
      simp only [List.filter_cons, lt_self_iff_false, decide_false, Bool.false_eq_true,
        ↓reduceIte]
      symm
      rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
      intro c hc
      simpa using (hL.1 c hc).le
    · have ha' : a ∈ L := by
        rcases List.mem_cons.1 ha with h | h
        · exact absurd h.symm hab
        · exact h
      rw [List.idxOf_cons_ne _ hab]
      have hb : b < a := hL.1 a ha'
      simp only [List.filter_cons, hb, decide_true, ↓reduceIte, List.length_cons]
      rw [ih hL.2 ha']

theorem card_image_congr {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (S : Finset α) (f : α → β) (g : α → γ) (h : ∀ x ∈ S, ∀ y ∈ S, f x = f y ↔ g x = g y) :
    (S.image f).card = (S.image g).card := by
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
        exact ⟨y, hy, (h y (Finset.mem_insert_of_mem hy) a (Finset.mem_insert_self _ _)).1 e⟩
      · rintro ⟨y, hy, e⟩
        exact ⟨y, hy, (h y (Finset.mem_insert_of_mem hy) a (Finset.mem_insert_self _ _)).2 e⟩
    by_cases hf : f a ∈ S.image f
    · rw [Finset.card_insert_of_mem hf, Finset.card_insert_of_mem (hiff.1 hf), ih']
    · rw [Finset.card_insert_of_notMem hf, Finset.card_insert_of_notMem (fun h' => hf (hiff.2 h')),
        ih']

theorem idxOf_sort_eq_card {β : Type*} [LinearOrder β] [BEq β] [LawfulBEq β] (s : Finset β) {a : β} (ha : a ∈ s) :
    (s.sort (· ≤ ·)).idxOf a = (s.filter (· < a)).card := by
  rw [idxOf_eq_length_filter (Finset.sortedLT_sort s).pairwise (by rwa [Finset.mem_sort])]
  rw [← List.toFinset_card_of_nodup ((Finset.sort_nodup _ _).filter _)]
  congr 1
  ext b
  simp

theorem idxOf_sort_lt_iff {β : Type*} [LinearOrder β] [BEq β] [LawfulBEq β] (s : Finset β) {a b : β} (ha : a ∈ s)
    (hb : b ∈ s) : (s.sort (· ≤ ·)).idxOf a < (s.sort (· ≤ ·)).idxOf b ↔ a < b := by
  rw [idxOf_sort_eq_card s ha, idxOf_sort_eq_card s hb]
  constructor
  · intro hc
    by_contra hn
    rw [not_lt] at hn
    have : s.filter (· < b) ⊆ s.filter (· < a) := fun c hc => by
      simp only [Finset.mem_filter] at hc ⊢; exact ⟨hc.1, lt_of_lt_of_le hc.2 hn⟩
    have := Finset.card_le_card this
    omega
  · intro hab
    apply Finset.card_lt_card
    refine ⟨fun c hc => ?_, fun hsub => ?_⟩
    · simp only [Finset.mem_filter] at hc ⊢; exact ⟨hc.1, hc.2.trans hab⟩
    · have := hsub (Finset.mem_filter.2 ⟨ha, hab⟩)
      simp at this

section Congr

variable {α β γ : Type*} [Fintype α] [DecidableEq α] [LinearOrder β] [LinearOrder γ]
  [BEq β] [LawfulBEq β] [BEq γ] [LawfulBEq γ] (f : α → β) (g : α → γ)

theorem idxOf_sort_image_congr (h : ∀ x y, f x ≤ f y ↔ g x ≤ g y) (x : α) :
    ((Finset.univ.image f).sort (· ≤ ·)).idxOf (f x) =
      ((Finset.univ.image g).sort (· ≤ ·)).idxOf (g x) := by
  rw [idxOf_sort_eq_card _ (Finset.mem_image_of_mem _ (Finset.mem_univ x)),
    idxOf_sort_eq_card _ (Finset.mem_image_of_mem _ (Finset.mem_univ x))]
  have e1 : (Finset.univ.image f).filter (· < f x) =
      (Finset.univ.filter (fun y => f y < f x)).image f := by
    ext b; simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨y, rfl⟩, hb⟩; exact ⟨y, hb, rfl⟩
    · rintro ⟨y, hy, rfl⟩; exact ⟨⟨y, rfl⟩, hy⟩
  have e2 : (Finset.univ.image g).filter (· < g x) =
      (Finset.univ.filter (fun y => f y < f x)).image g := by
    ext b; simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨y, rfl⟩, hb⟩
      refine ⟨y, ?_, rfl⟩
      rw [← not_le, h, not_le]; exact hb
    · rintro ⟨y, hy, rfl⟩
      refine ⟨⟨y, rfl⟩, ?_⟩
      rw [← not_le, ← h, not_le]; exact hy
  rw [e1, e2]
  exact card_image_congr _ _ _ (fun y _ z _ => by
    constructor
    · intro e; exact le_antisymm ((h y z).1 e.le) ((h z y).1 e.ge)
    · intro e; exact le_antisymm ((h y z).2 e.le) ((h z y).2 e.ge))

omit [BEq β] [LawfulBEq β] [BEq γ] [LawfulBEq γ] in
theorem length_sort_image_congr (h : ∀ x y, f x ≤ f y ↔ g x ≤ g y) :
    ((Finset.univ.image f).sort (· ≤ ·)).length = ((Finset.univ.image g).sort (· ≤ ·)).length := by
  rw [Finset.length_sort, Finset.length_sort]
  exact card_image_congr _ _ _ (fun y _ z _ => by
    constructor
    · intro e; exact le_antisymm ((h y z).1 e.le) ((h z y).1 e.ge)
    · intro e; exact le_antisymm ((h y z).2 e.le) ((h z y).2 e.ge))

end Congr

theorem palette_idxOf_lt_iff {Ω C : Type*} [Fintype Ω] [LinearOrder C] [BEq C] [LawfulBEq C]
    (X : ColoredDigraph Ω C) (x y : Ω) :
    X.palette.idxOf (X.c x) < X.palette.idxOf (X.c y) ↔ X.c x < X.c y := by
  unfold palette
  exact idxOf_sort_lt_iff _ (Finset.mem_image_of_mem _ (Finset.mem_univ x))
    (Finset.mem_image_of_mem _ (Finset.mem_univ y))

theorem palette_idxOf_eq_iff {Ω C : Type*} [Fintype Ω] [LinearOrder C] [BEq C] [LawfulBEq C]
    (X : ColoredDigraph Ω C) (x y : Ω) :
    X.palette.idxOf (X.c x) = X.palette.idxOf (X.c y) ↔ X.c x = X.c y :=
  List.idxOf_inj ((X.mem_palette _).2 ⟨x, rfl⟩)

namespace TagLin

open Babai.TaggedDigraph

/-! ## The string process and the tagged process -/

variable {r : RawColored}

theorem tag_c (r : RawColored) (j : ℕ) (x : Fin r.1.length) :
    (tagIter (decTagged (toTagged r)) j).c x = sX (toTagged r) j x := by
  simp [sX, x.isLt, toTagged]

theorem rX_eq_rank (r : RawColored) (j : ℕ) (x : Fin r.1.length) :
    rX (toTagged r) j x = (tagIter (decTagged (toTagged r)) j).rank x := by
  simp [rX, x.isLt, toTagged]

/-- The counts of the tagged row of round `j + 1`. -/
noncomputable def cnts (r : RawColored) (j x : ℕ) : List ℕ :=
  (List.range (NX (toTagged r) j)).flatMap (fun i =>
    [outC r.2 (rX (toTagged r) j) i x, inC r.2 (rX (toTagged r) j) i x])

theorem length_cnts (r : RawColored) (j x : ℕ) : (cnts r j x).length = 2 * NX (toTagged r) j :=
  length_flatMap_pair _ _ _

theorem sX_succ' (hr : r.WF) (j : ℕ) {x : ℕ} (hx : x < r.1.length) :
    sX (toTagged r) (j + 1) x = rX (toTagged r) j x :: cnts r j x := by
  rw [sX_succ hr.toTagged j hx]; rfl

/-- The length of a color of round `j`. -/
noncomputable def lenS (r : RawColored) (k : ℕ) : ℕ → ℕ
  | 0 => k
  | j + 1 => lenS r k j + 4 * NX (toTagged r) j + 2

/-- **The order of the string colors is the order of the tagged colors**, and all string colors of
a round have the same length. -/
theorem strIter_spec (hr : r.WF) {k : ℕ} (hk : ∀ s ∈ r.1, s.length = k) :
    ∀ j, (∀ x, ((decColored r).strIter j x).length = lenS r k j) ∧
      (∀ x y, (decColored r).strIter j x ≤ (decColored r).strIter j y ↔
        sX (toTagged r) j x ≤ sX (toTagged r) j y) ∧
      ∀ x, (decColored r).strIter (j + 1) x =
        lOpen :: ((decColored r).strIter j x ++ encCnt (cnts r j x)) := by
  classical
  set X := decColored r
  set t := toTagged r
  -- the step, from the order of round `j`
  have step : ∀ j, (∀ x y, X.strIter j x ≤ X.strIter j y ↔ sX t j x ≤ sX t j y) →
      ∀ x, X.strIter (j + 1) x = lOpen :: (X.strIter j x ++ encCnt (cnts r j x)) := by
    intro j hord x
    have hord' : ∀ x y, X.strIter j x ≤ X.strIter j y ↔
        (tagIter (decTagged t) j).c x ≤ (tagIter (decTagged t) j).c y := by
      intro x y; rw [tag_c, tag_c]; exact hord x y
    have hidx : ∀ y, (X.recolor (X.strIter j)).palette.idxOf (X.strIter j y) = rX t j y := by
      intro y
      rw [rX_eq_rank]
      unfold palette rank TaggedDigraph.oldColors TaggedDigraph.realizedColors
      exact idxOf_sort_image_congr _ _ hord' y
    have hlen : (X.recolor (X.strIter j)).palette.length = NX t j := by
      unfold palette NX numColors TaggedDigraph.oldColors TaggedDigraph.realizedColors
      exact length_sort_image_congr _ _ hord'
    have hnd : (X.recolor (X.strIter j)).palette.Nodup := Finset.sort_nodup _ _
    -- the palette as a list indexed by ranks
    have hmap : (X.recolor (X.strIter j)).palette = (List.range (NX t j)).map
        (fun i => (X.recolor (X.strIter j)).palette.getD i []) := by
      apply List.ext_getElem (by simp [hlen])
      intro i h1 h2
      simp only [List.getElem_map, List.getElem_range]
      rw [List.getD_eq_getElem _ _ h1]
    have hcnt : ∀ i < NX t j, ∀ y : Fin r.1.length,
        X.strIter j y = (X.recolor (X.strIter j)).palette.getD i [] ↔ rX t j y = i := by
      intro i hi y
      rw [← hidx y]
      have hi' : i < (X.recolor (X.strIter j)).palette.length := by rw [hlen]; exact hi
      rw [List.getD_eq_getElem _ _ hi']
      constructor
      · intro e; rw [e]; exact hnd.idxOf_getElem i hi'
      · intro e
        subst e
        exact (List.getElem_idxOf _).symm
    have hout : ∀ i < NX t j, (X.recolor (X.strIter j)).outDegCol
        ((X.recolor (X.strIter j)).palette.getD i []) x = outC r.2 (rX t j) i x := by
      intro i hi
      unfold outDegCol outC
      rw [← ncard_eq_countP r.2 hr.1 (edges_lt hr.toTagged) (fun y => rX t j y = i) x]
      congr 1
      ext y
      simp only [Set.mem_setOf_eq, recolor_E, recolor_c]
      rw [hcnt i hi y]; rfl
    have hin : ∀ i < NX t j, (X.recolor (X.strIter j)).inDegCol
        ((X.recolor (X.strIter j)).palette.getD i []) x = inC r.2 (rX t j) i x := by
      intro i hi
      unfold inDegCol inC
      rw [← ncard_eq_countP' r.2 hr.1 (edges_lt hr.toTagged) (fun y => rX t j y = i) x]
      congr 1
      ext y
      simp only [Set.mem_setOf_eq, recolor_E, recolor_c]
      rw [hcnt i hi y]; rfl
    rw [strIter_succ]
    unfold strStep
    rw [recolor_c]
    congr 2
    unfold encCnt cnts
    congr 1
    rw [hmap, List.flatMap_map]
    have : ∀ l : List ℕ, (∀ i ∈ l, i < NX t j) →
        l.flatMap (fun i => [lComma, lNum ((X.recolor (X.strIter j)).outDegCol
          ((X.recolor (X.strIter j)).palette.getD i []) x), lComma,
          lNum ((X.recolor (X.strIter j)).inDegCol ((X.recolor (X.strIter j)).palette.getD i []) x)]) =
        (l.flatMap (fun i => [outC r.2 (rX t j) i x, inC r.2 (rX t j) i x])).flatMap
          (fun a => [lComma, lNum a]) := by
      intro l hl
      induction l with
      | nil => simp
      | cons a l ih =>
        simp only [List.flatMap_cons, List.cons_append, List.nil_append]
        rw [hout a (hl a List.mem_cons_self), hin a (hl a List.mem_cons_self),
          ih (fun i hi => hl i (List.mem_cons_of_mem _ hi))]
    exact this _ (fun i hi => List.mem_range.1 hi)
  intro j
  induction j with
  | zero =>
    have h0 : ∀ x y, X.strIter 0 x ≤ X.strIter 0 y ↔ sX t 0 x ≤ sX t 0 y := by
      intro x y
      rw [sX_zero _ x.isLt, sX_zero _ y.isLt]; rfl
    refine ⟨fun x => hk _ (List.getElem_mem _), h0, step 0 h0⟩
  | succ j ih =>
    obtain ⟨hl, hord, hs⟩ := ih
    have hl' : ∀ x, (X.strIter (j + 1) x).length = lenS r k (j + 1) := by
      intro x
      rw [hs x]
      simp only [List.length_cons, List.length_append, length_encCnt, length_cnts, hl x, lenS]
      ring
    have hord' : ∀ x y, X.strIter (j + 1) x ≤ X.strIter (j + 1) y ↔
        sX t (j + 1) x ≤ sX t (j + 1) y := by
      intro x y
      rw [hs x, hs y, sX_succ' hr j x.isLt, sX_succ' hr j y.isLt, lcons_le, lcons_le]
      simp only [lt_self_iff_false, true_and, false_or]
      rw [append_le_append_iff (by rw [hl, hl]), encCnt_le_iff (by rw [length_cnts, length_cnts])]
      have hord'' : ∀ x y, X.strIter j x ≤ X.strIter j y ↔
          (tagIter (decTagged t) j).c x ≤ (tagIter (decTagged t) j).c y := by
        intro x y; rw [tag_c, tag_c]; exact hord x y
      have hidx : ∀ y : Fin r.1.length, rX t j y = (X.recolor (X.strIter j)).palette.idxOf (X.strIter j y) := by
        intro y
        rw [rX_eq_rank]
        unfold palette rank TaggedDigraph.oldColors TaggedDigraph.realizedColors
        exact (idxOf_sort_image_congr _ _ hord'' y).symm
      have hlt : X.strIter j x < X.strIter j y ↔ rX t j x < rX t j y := by
        rw [hidx, hidx]
        exact (palette_idxOf_lt_iff (X.recolor (X.strIter j)) x y).symm
      have heq : X.strIter j x = X.strIter j y ↔ rX t j x = rX t j y := by
        rw [hidx, hidx]
        exact (palette_idxOf_eq_iff (X.recolor (X.strIter j)) x y).symm
      rw [hlt, heq]
    exact ⟨hl', hord', step (j + 1) hord'⟩

theorem strIter_succ_eq (hr : r.WF) {k : ℕ} (hk : ∀ s ∈ r.1, s.length = k) (j : ℕ)
    (x : Fin r.1.length) :
    (decColored r).strIter (j + 1) x =
      lOpen :: ((decColored r).strIter j x ++ encCnt (cnts r j x)) :=
  (strIter_spec hr hk j).2.2 x

theorem strIter_eq_iff (hr : r.WF) {k : ℕ} (hk : ∀ s ∈ r.1, s.length = k) (j : ℕ)
    (x y : Fin r.1.length) :
    (decColored r).strIter j x = (decColored r).strIter j y ↔
      sX (toTagged r) j x = sX (toTagged r) j y := by
  have h := (strIter_spec hr hk j).2.1
  rw [le_antisymm_iff, le_antisymm_iff, h, h]

theorem strNum_eq (hr : r.WF) {k : ℕ} (hk : ∀ s ∈ r.1, s.length = k) (j : ℕ) :
    (decColored r).strNum j = NX (toTagged r) j := by
  have hker : kernelSet ((decColored r).strIter j) =
      kernelSet (tagIter (decTagged (toTagged r)) j).c := by
    ext ⟨x, y⟩
    change _ = _ ↔ (tagIter (decTagged (toTagged r)) j).c x = (tagIter (decTagged (toTagged r)) j).c y
    rw [tag_c, tag_c]
    exact strIter_eq_iff hr hk j x y
  unfold strNum NX
  rw [numColors_eq_card_range]
  exact le_antisymm (card_range_le_of_kernelSet_subset _ _ hker.symm.le)
    (card_range_le_of_kernelSet_subset _ _ hker.le)

/-- Both processes stop at the same round. -/
theorem strStop_eq (hr : r.WF) {k : ℕ} (hk : ∀ s ∈ r.1, s.length = k) :
    (decColored r).strStop = stopIdx (decTagged (toTagged r)) := by
  classical
  refine (decColored r).strStop_eq_of ?_ (fun i hi => ?_)
  · rw [strNum_eq hr hk, strNum_eq hr hk]; exact stopIdx_spec _
  · rw [strNum_eq hr hk, strNum_eq hr hk]
    exact Nat.find_min (exists_stop _) hi

/-- **The color of round `K`**: `K` opening parentheses, the input color, then the count strings
of the rounds `0, …, K-1`. -/
theorem strIter_eq (hr : r.WF) {k : ℕ} (hk : ∀ s ∈ r.1, s.length = k) (K : ℕ)
    (x : Fin r.1.length) :
    (decColored r).strIter K x = List.replicate K lOpen ++ (r.1[x] ++
      (List.range K).flatMap (fun j => encCnt (cnts r j x))) := by
  induction K with
  | zero => simp [decColored]
  | succ K ih =>
    rw [strIter_succ_eq hr hk, ih, List.range_succ, List.flatMap_append, List.replicate_succ]
    simp

/-! ## At most `2m` rounds -/

section Rounds

variable {r : RawTagged}

/-- Vertex `v` is isolated: no listed edge has `v` as an end. -/
def IsoV (r : RawTagged) (v : ℕ) : Prop := ∀ e ∈ r.2.1, e.1 ≠ v ∧ e.2 ≠ v

theorem rX_eq_iff (r : RawTagged) (j : ℕ) {v w : ℕ} (hv : v < r.1.length) (hw : w < r.1.length) :
    rX r j v = rX r j w ↔ sX r j v = sX r j w := by
  simp only [rX, sX, hv, hw, dif_pos]
  exact rank_eq_iff _ _ _

theorem outC_isoV {v : ℕ} (hv : IsoV r v) (rk : ℕ → ℕ) (i : ℕ) : outC r.2.1 rk i v = 0 := by
  unfold outC
  rw [List.countP_eq_zero]
  intro e he
  simp [(hv e he).1]

theorem inC_isoV {v : ℕ} (hv : IsoV r v) (rk : ℕ → ℕ) (i : ℕ) : inC r.2.1 rk i v = 0 := by
  unfold inC
  rw [List.countP_eq_zero]
  intro e he
  simp [(hv e he).2]

/-- Two isolated vertices get the same color in round `j + 1` exactly when they had the same
color in round `j`. -/
theorem sX_succ_isoV_iff (hr : r.WF) (j : ℕ) {v w : ℕ} (hvn : v < r.1.length)
    (hwn : w < r.1.length) (hv : IsoV r v) (hw : IsoV r w) :
    sX r (j + 1) v = sX r (j + 1) w ↔ sX r j v = sX r j w := by
  rw [sX_succ hr j hvn, sX_succ hr j hwn]
  unfold rowStr
  rw [List.cons.injEq, rX_eq_iff r j hvn hwn]
  have : (List.range (NX r j)).flatMap (fun i => [outC r.2.1 (rX r j) i v, inC r.2.1 (rX r j) i v]) =
      (List.range (NX r j)).flatMap (fun i => [outC r.2.1 (rX r j) i w, inC r.2.1 (rX r j) i w]) := by
    simp only [outC_isoV hv, inC_isoV hv, outC_isoV hw, inC_isoV hw]
  rw [this]
  simp

theorem sX_isoV_iff (hr : r.WF) (j : ℕ) {v w : ℕ} (hvn : v < r.1.length)
    (hwn : w < r.1.length) (hv : IsoV r v) (hw : IsoV r w) :
    sX r j v = sX r j w ↔ sX r 0 v = sX r 0 w := by
  induction j with
  | zero => rfl
  | succ j ih => rw [sX_succ_isoV_iff hr j hvn hwn hv hw, ih]

/-- After round `1`, an isolated vertex and a non-isolated one have different colors. -/
theorem sX_succ_ne (hr : r.WF) (j : ℕ) {v w : ℕ} (hvn : v < r.1.length)
    (hwn : w < r.1.length) (hv : IsoV r v) (hw : ¬ IsoV r w) :
    sX r (j + 1) v ≠ sX r (j + 1) w := by
  intro h
  rw [sX_succ hr j hvn, sX_succ hr j hwn] at h
  unfold rowStr at h
  rw [List.cons.injEq] at h
  have hc := (flatMap_pair_eq_iff _ _ _ _ _).1 h.2
  unfold IsoV at hw
  push Not at hw
  obtain ⟨e, he, hne⟩ := hw
  have hel := (hr.2 e he)
  by_cases h1 : e.1 = w
  · have hi := rX_lt r j hel.2.1
    have := (hc (rX r j e.2) hi).1
    rw [outC_isoV hv] at this
    have hpos : 0 < outC r.2.1 (rX r j) (rX r j e.2) w := by
      unfold outC
      rw [List.countP_pos_iff]
      exact ⟨e, he, by simp [h1]⟩
    omega
  · have h2 : e.2 = w := hne h1
    have hi := rX_lt r j hel.1
    have := (hc (rX r j e.1) hi).2
    rw [inC_isoV hv] at this
    have hpos : 0 < inC r.2.1 (rX r j) (rX r j e.1) w := by
      unfold inC
      rw [List.countP_pos_iff]
      exact ⟨e, he, by simp [h2]⟩
    omega

theorem NX_eq_card (r : RawTagged) (j : ℕ) :
    NX r j = ((Finset.range r.1.length).image (sX r j)).card := by
  unfold NX numColors oldColors realizedColors
  rw [Finset.length_sort]
  congr 1
  ext s
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_range]
  constructor
  · rintro ⟨v, rfl⟩; exact ⟨v, v.isLt, by simp [sX, v.isLt]⟩
  · rintro ⟨v, hv, rfl⟩; exact ⟨⟨v, hv⟩, by simp [sX, hv]⟩

/-- **At most `2m` rounds refine**: `k ≤ 2m` for the stopping round `k`. -/
theorem stopIdx_le_two_mul (hr : r.WF) : stopIdx (decTagged r) ≤ 2 * r.2.1.length := by
  classical
  set n := r.1.length
  set K := stopIdx (decTagged r)
  set I := (Finset.range n).filter (fun v => IsoV r v)
  set J := (Finset.range n).filter (fun v => ¬ IsoV r v)
  have hIJ : Finset.range n = I ∪ J := by
    ext v; simp only [Finset.mem_union, Finset.mem_filter, I, J]; tauto
  have hN : ∀ j, NX r j ≤ (I.image (sX r j)).card + (J.image (sX r j)).card := by
    intro j
    rw [NX_eq_card, hIJ, Finset.image_union]
    exact Finset.card_union_le _ _
  have hN1 : ∀ j, NX r (j + 1) = (I.image (sX r (j + 1))).card + (J.image (sX r (j + 1))).card := by
    intro j
    rw [NX_eq_card, hIJ, Finset.image_union]
    refine Finset.card_union_of_disjoint (Finset.disjoint_left.2 (fun s hs1 hs2 => ?_))
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hs1
    obtain ⟨w, hw, e⟩ := Finset.mem_image.1 hs2
    simp only [Finset.mem_filter, Finset.mem_range, I, J] at hv hw
    exact sX_succ_ne hr j hv.1 hw.1 hv.2 hw.2 e.symm
  have ha : ∀ j, (I.image (sX r j)).card = (I.image (sX r 0)).card := fun j =>
    card_image_congr _ _ _ (fun v hv w hw => by
      simp only [Finset.mem_filter, Finset.mem_range, I] at hv hw
      exact sX_isoV_iff hr j hv.1 hw.1 hv.2 hw.2)
  have hJ : J.card ≤ 2 * r.2.1.length := by
    have hsub : J ⊆ (r.2.1.map Prod.fst ++ r.2.1.map Prod.snd).toFinset := by
      intro v hv
      simp only [Finset.mem_filter, Finset.mem_range, J, IsoV] at hv
      push Not at hv
      obtain ⟨e, he, h⟩ := hv.2
      simp only [List.mem_toFinset, List.mem_append, List.mem_map]
      by_cases h1 : e.1 = v
      · exact Or.inl ⟨e, he, h1⟩
      · exact Or.inr ⟨e, he, h h1⟩
    have := (Finset.card_le_card hsub).trans (List.toFinset_card_le _)
    simp only [List.length_append, List.length_map] at this
    omega
  have hb : ∀ j, (J.image (sX r j)).card ≤ 2 * r.2.1.length := fun j =>
    Finset.card_image_le.trans hJ
  have hmin : ∀ i < K, NX r (i + 1) ≠ NX r i := fun i hi => Nat.find_min (exists_stop _) hi
  have hlt : ∀ i < K, NX r i < NX r (i + 1) := fun i hi =>
    lt_of_le_of_ne (NX_mono r i) (hmin i hi).symm
  rcases Nat.eq_zero_or_pos K with hK | hK
  · omega
  -- some vertex is not isolated
  have hJne : J.Nonempty := by
    by_contra hJe
    rw [Finset.not_nonempty_iff_eq_empty] at hJe
    have h0 : NX r 0 = (I.image (sX r 0)).card := by
      rw [NX_eq_card, hIJ, hJe, Finset.union_empty]
    have h1 : NX r (0 + 1) = (I.image (sX r (0 + 1))).card := by
      have := hN1 0
      rw [hJe, Finset.image_empty, Finset.card_empty] at this
      omega
    have h2 := hlt 0 hK
    have h3 : (I.image (sX r (0 + 1))).card = (I.image (sX r 0)).card := ha (0 + 1)
    have h4 : NX r (0 + 1) ≤ NX r 0 := by rw [h1, h3, h0]
    exact absurd h2 (not_lt.2 h4)
  have hb1 : 1 ≤ (J.image (sX r 1)).card :=
    Finset.card_pos.2 (hJne.image _)
  have key : ∀ i, 1 ≤ i → i ≤ K → i ≤ (J.image (sX r i)).card := by
    intro i
    induction i with
    | zero => intro h; omega
    | succ i ih =>
      intro h1 h2
      rcases Nat.eq_zero_or_pos i with rfl | hi
      · exact hb1
      · have := ih hi (by omega)
        have hl := hlt i (by omega)
        obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
        rw [hN1, hN1, ha, ha (i' + 1 + 1)] at hl
        omega
  have := key K hK le_rfl
  have := hb K
  omega

end Rounds

end TagLin

end Algo
