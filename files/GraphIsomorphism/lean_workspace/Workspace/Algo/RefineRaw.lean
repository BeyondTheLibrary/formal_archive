/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: naive vertex-refinement (§4.1, §4.1.1) on raw data.
-/
import Workspace.Algo.Encodings
import Workspace.Refinement.Naive
import Workspace.Machine.ListOps5

/-!
# §4.1, §4.1.1 — naive vertex-refinement as a routine

This is the raw half of the work package **A8** of `Workspace/Algo/DESIGN.md` (rows R1 and R2
of item 1.2).  `Workspace/Refinement/Naive.lean` has the mathematics: one round `c ↦ c'`, the
process `X_j`, the stable refinement `X*`, Observations 4.1.1 and 4.1.2.  All of it is
noncomputable — the colors after `j` rounds live in the type `naiveColorType C j`, which grows
with `j`, and the degrees are `Set.ncard`s.  This file builds the computable copy on encodings
and proves that it has the same color classes.

## The paper's point about tags

§4.1.1 (lines 2851–2870) says that running the process as written makes the *names* of the
colors grow: "the description of each color in `X_j` has length `k + O(jn)` and therefore in
`X*`, the length is `k + O(n²)`".  The repair is to rename the colors after each round: "reduce,
in each round, the set of colors to an initial segment of the integers (specifically to
`[N(c_j)]` in round j) and remember this substitution of colors" as a tag.

That is exactly what `Algo.rawRefineStep` does.  The tag of a vertex is the paper's string
`c'(x) = (c(x), d⁺ᵢ(x), d⁻ᵢ(x) | i ∈ C)`, laid out as a list of `1 + 2n` naturals, and the new
color of `x` is the **rank** of that string among the distinct strings occurring, in the
lexicographic order the paper puts on `C'`.  So the new colors are again naturals below `n`,
and they form an initial segment of the integers, as §4.1.1 asks.  The tag of §4.1.1 — the
record of the substitution — is not carried: `Algo.decCD` reads the colors of a raw digraph as
naturals, so the substitution is invertible from the data, and the tag's only mathematical role
(Eq. (25): reject an isomorphism when the tags differ) is played by the answer of the routine
itself.

## Main definitions

* `Algo.cmpRec`, `Algo.lexCmp`, `Algo.lexLtB` — the lexicographic order on equal-length strings,
  once as a recursion (for the proofs) and once as a fold (for the machine);
* `Algo.rankIn` — the rank of a string among the distinct strings of a list;
* `Algo.RawCD`, `Algo.RawCD.WF`, `Algo.decCD` — a raw colored digraph, its well-formedness and
  its decoding to `Babai.ColoredDigraph (Fin n) ℕ`;
* `Algo.tagAt`, `Algo.rawTags`, `Algo.rawNewCol`, `Algo.rawRefineStep` — one round;
* `Algo.rawStableRefine` — the process, run for `n²` rounds.

## Main results

* `Algo.rankIn_inj` — the renaming is injective, so a round loses no information;
* `Algo.tagAt_eq_iff` — two vertices get the same tag exactly when
  `Babai.ColoredDigraph.naiveStep` gives them the same color;
* `Algo.rawRefineStep_wf`, `Algo.rawNewCol_lt` — the colors stay naturals below `n`, which is
  the paper's point about tags;
* `Algo.rawStableRefine_spec` — the routine and `Babai.ColoredDigraph.stableRefine` have the
  same color classes.

The running time is `Workspace/Algo/RefinePoly.lean`.  No axiom and no `sorry`.
-/

namespace Algo

open Babai

/-! ## The lexicographic order on strings of naturals

§4.1 orders the new colors lexicographically: "We regard the set `C' = {c'(x) | x ∈ V}` of
strings as a new set of colors, ordered lexicographically."  All the strings compared here have
the same length, `1 + 2n`, so the comparison is: look for the first position where the two
strings differ.

`Algo.cmpRec` is that comparison as a recursion — `0` for "no difference found", `1` for "the
left one is smaller", `2` for "the right one is smaller".  A recursion on two lists is not a
machine routine, so `Algo.lexCmp` repeats it as a `List.foldl` over the zipped strings, and
`Algo.lexCmp_eq_cmpRec` says the two agree. -/

/-- Comparison of two strings of naturals: `0` if neither is lexicographically smaller (which
for equal lengths means they are equal), `1` if the left one is smaller, `2` if the right one
is. -/
def cmpRec : List ℕ → List ℕ → ℕ
  | [], _ => 0
  | _ :: _, [] => 0
  | a :: u, b :: v => if a < b then 1 else if b < a then 2 else cmpRec u v

@[simp] theorem cmpRec_nil (v : List ℕ) : cmpRec [] v = 0 := rfl

@[simp] theorem cmpRec_nil_right (a : ℕ) (u : List ℕ) : cmpRec (a :: u) [] = 0 := rfl

theorem cmpRec_cons (a b : ℕ) (u v : List ℕ) :
    cmpRec (a :: u) (b :: v) = if a < b then 1 else if b < a then 2 else cmpRec u v := rfl

/-- The comparison of a string with itself finds no difference. -/
@[simp] theorem cmpRec_self : ∀ u : List ℕ, cmpRec u u = 0
  | [] => rfl
  | a :: u => by rw [cmpRec_cons]; simp [cmpRec_self u]

/-- The comparison takes only the three values `0`, `1`, `2`. -/
theorem cmpRec_lt_three : ∀ u v : List ℕ, cmpRec u v < 3
  | [], _ => by simp
  | _ :: _, [] => by simp
  | a :: u, b :: v => by
      rw [cmpRec_cons]
      split
      · omega
      · split
        · omega
        · exact cmpRec_lt_three u v

/-- On strings of the same length, "no difference found" means "equal". -/
theorem eq_of_cmpRec_eq_zero : ∀ u v : List ℕ, u.length = v.length → cmpRec u v = 0 → u = v
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | a :: u, b :: v, hl, h => by
      rw [cmpRec_cons] at h
      have hab : a = b := by
        by_contra hne
        rcases Nat.lt_or_ge a b with h1 | h1
        · rw [if_pos h1] at h; omega
        · have h2 : b < a := by omega
          rw [if_neg (by omega), if_pos h2] at h; omega
      subst hab
      rw [if_neg (by omega), if_neg (by omega)] at h
      have hl' : u.length = v.length := by simpa using hl
      rw [eq_of_cmpRec_eq_zero u v hl' h]

/-- The comparison is antisymmetric: the left one is smaller exactly when, the other way round,
the right one is. -/
theorem cmpRec_eq_two_iff : ∀ u v : List ℕ, cmpRec u v = 2 ↔ cmpRec v u = 1
  | [], [] => by simp
  | [], _ :: _ => by simp [cmpRec]
  | _ :: _, [] => by simp [cmpRec]
  | a :: u, b :: v => by
      rw [cmpRec_cons, cmpRec_cons]
      rcases Nat.lt_trichotomy a b with h | h | h
      · rw [if_pos h, if_neg (by omega), if_pos h]
        simp
      · subst h
        rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
        exact cmpRec_eq_two_iff u v
      · rw [if_neg (by omega), if_pos h, if_pos h]
        simp

/-- The comparison is transitive. -/
theorem cmpRec_trans : ∀ u v w : List ℕ, cmpRec u v = 1 → cmpRec v w = 1 → cmpRec u w = 1
  | [], _, _, h, _ => by simp at h
  | _ :: _, [], _, h, _ => by simp at h
  | _ :: _, _ :: _, [], _, h => by simp at h
  | a :: u, b :: v, c :: w, h1, h2 => by
      rw [cmpRec_cons] at h1 h2 ⊢
      have hab : a < b ∨ (a = b ∧ cmpRec u v = 1) := by
        rcases Nat.lt_trichotomy a b with h | h | h
        · exact Or.inl h
        · subst h
          rw [if_neg (by omega), if_neg (by omega)] at h1
          exact Or.inr ⟨rfl, h1⟩
        · rw [if_neg (by omega), if_pos h] at h1; omega
      have hbc : b < c ∨ (b = c ∧ cmpRec v w = 1) := by
        rcases Nat.lt_trichotomy b c with h | h | h
        · exact Or.inl h
        · subst h
          rw [if_neg (by omega), if_neg (by omega)] at h2
          exact Or.inr ⟨rfl, h2⟩
        · rw [if_neg (by omega), if_pos h] at h2; omega
      rcases hab with hab | ⟨hab, hu⟩
      · rcases hbc with hbc | ⟨hbc, -⟩
        · rw [if_pos (by omega)]
        · rw [if_pos (by omega)]
      · rcases hbc with hbc | ⟨hbc, hv⟩
        · rw [if_pos (by omega)]
        · subst hab; subst hbc
          rw [if_neg (by omega), if_neg (by omega)]
          exact cmpRec_trans u v w hu hv

/-- On strings of the same length, one of the three cases occurs. -/
theorem cmpRec_total {u v : List ℕ} (hl : u.length = v.length) (hne : u ≠ v) :
    cmpRec u v = 1 ∨ cmpRec v u = 1 := by
  have h0 : cmpRec u v ≠ 0 := fun h => hne (eq_of_cmpRec_eq_zero u v hl h)
  have h3 : cmpRec u v < 3 := cmpRec_lt_three u v
  rcases Nat.lt_or_ge (cmpRec u v) 2 with h | h
  · exact Or.inl (by omega)
  · have : cmpRec u v = 2 := by omega
    exact Or.inr ((cmpRec_eq_two_iff u v).1 this)

/-! ### The same comparison as a fold

The state of the fold is the answer found so far; once it is nonzero it is kept.  This is the
shape `RAM.PolyFun.foldl` takes. -/

/-- One round of the comparison fold. -/
def lexStep (s : ℕ × (ℕ × ℕ)) : ℕ :=
  if s.1 = 0 then (if s.2.1 < s.2.2 then 1 else if s.2.2 < s.2.1 then 2 else 0) else s.1

/-- The comparison of two strings, as a fold over the zipped strings. -/
def lexCmp (p : List ℕ × List ℕ) : ℕ :=
  List.foldl (fun y a => lexStep (y, a)) 0 (p.1.zip p.2)

/-- **The closed form of the fold**, from an arbitrary start state. -/
theorem lexFold : ∀ (u v : List ℕ) (s : ℕ),
    List.foldl (fun y a => lexStep (y, a)) s (u.zip v) = if s = 0 then cmpRec u v else s
  | [], v, s => by cases v <;> simp [lexStep]
  | a :: u, [], s => by simp
  | a :: u, b :: v, s => by
      rw [List.zip_cons_cons, List.foldl_cons, lexFold u v]
      by_cases hs : s = 0
      · subst hs
        rw [cmpRec_cons]
        rcases Nat.lt_trichotomy a b with h | h | h
        · simp [lexStep, h, Nat.not_lt.2 (le_of_lt h)]
        · subst h; simp [lexStep]
        · have h1 : ¬ a < b := by omega
          simp [lexStep, h1, h]
      · simp [lexStep, hs]

/-- The fold and the recursion agree. -/
theorem lexCmp_eq_cmpRec (u v : List ℕ) : lexCmp (u, v) = cmpRec u v := by
  rw [lexCmp, lexFold]
  simp

/-- "Lexicographically smaller", as a decision the machine makes. -/
def lexLtB (p : List ℕ × List ℕ) : Bool := decide (lexCmp p = 1)

theorem lexLtB_eq (u v : List ℕ) : lexLtB (u, v) = decide (cmpRec u v = 1) := by
  rw [lexLtB, lexCmp_eq_cmpRec]

@[simp] theorem lexLtB_self (u : List ℕ) : lexLtB (u, u) = false := by
  rw [lexLtB_eq]; simp

/-! ## Ranking

§4.1.1: the new color of `x` is the position of its string in the ordered set `C'` of the
strings that occur.  Equivalently, it is the number of *distinct* strings that occur and are
lexicographically smaller.  That is `Algo.rankIn`, which takes the list of distinct strings as
its first argument. -/

/-- The rank of a string `t` in a list `D` of strings: the number of entries of `D` that are
lexicographically smaller than `t`. -/
def rankIn (p : List (List ℕ) × List ℕ) : ℕ := (p.1.filter (fun u => lexLtB (u, p.2))).length

theorem rankIn_eq_countP (D : List (List ℕ)) (t : List ℕ) :
    rankIn (D, t) = D.countP (fun u => lexLtB (u, t)) := by
  rw [rankIn, List.countP_eq_length_filter]

/-- **A strict count**: if every entry counted by `p` is counted by `q`, and some entry of the
list is counted by `q` but not by `p`, then `q` counts strictly more. -/
theorem countP_lt_countP {α : Type*} {p q : α → Bool} {a : α} : ∀ l : List α,
    (∀ b ∈ l, p b = true → q b = true) → a ∈ l → q a = true → p a = false →
    l.countP p < l.countP q := by
  intro l
  induction l with
  | nil => intro _ ha; exact absurd ha (by simp)
  | cons b t ih =>
      intro hmono ha hqa hpa
      have hmono' : ∀ c ∈ t, p c = true → q c = true :=
        fun c hc => hmono c (List.mem_cons_of_mem b hc)
      have hle : t.countP p ≤ t.countP q := List.countP_mono_left hmono'
      rw [List.countP_cons, List.countP_cons]
      rcases List.mem_cons.1 ha with rfl | ha'
      · rw [hpa, hqa]
        simp only [Bool.false_eq_true, if_false, if_true]
        omega
      · have hstep := ih hmono' ha' hqa hpa
        have hb : (if p b = true then 1 else 0) ≤ (if q b = true then 1 else 0) := by
          by_cases h : p b = true
          · rw [if_pos h, if_pos (hmono b (List.mem_cons_self ..) h)]
          · simp [h]
        omega

/-- **The rank is strictly monotone**: a lexicographically smaller string has a smaller rank,
provided it occurs in the list. -/
theorem rankIn_lt_rankIn {D : List (List ℕ)} {s t : List ℕ} (hs : s ∈ D)
    (hst : cmpRec s t = 1) : rankIn (D, s) < rankIn (D, t) := by
  rw [rankIn_eq_countP, rankIn_eq_countP]
  refine countP_lt_countP (a := s) D (fun u _ hu => ?_) hs ?_ ?_
  · rw [lexLtB_eq] at hu ⊢
    exact decide_eq_true (cmpRec_trans u s t (of_decide_eq_true hu) hst)
  · rw [lexLtB_eq]; exact decide_eq_true hst
  · simp

/-- **The renaming is injective.**  Two entries of a list of strings of one and the same length
that get the same rank are equal.  This is why one round of refinement loses no information. -/
theorem rankIn_inj {D : List (List ℕ)} {L : ℕ} (hlen : ∀ u ∈ D, u.length = L)
    {s t : List ℕ} (hs : s ∈ D) (ht : t ∈ D) (h : rankIn (D, s) = rankIn (D, t)) : s = t := by
  by_contra hne
  rcases cmpRec_total ((hlen s hs).trans (hlen t ht).symm) hne with h1 | h1
  · exact absurd h (Nat.ne_of_lt (rankIn_lt_rankIn hs h1))
  · exact absurd h.symm (Nat.ne_of_lt (rankIn_lt_rankIn ht h1))

/-- **The ranks are an initial segment**: a rank is below the number of distinct strings.  This
is §4.1.1's "reduce the set of colors to an initial segment of the integers". -/
theorem rankIn_lt_length {D : List (List ℕ)} {t : List ℕ} (ht : t ∈ D) :
    rankIn (D, t) < D.length := by
  rw [rankIn_eq_countP]
  have h : D.length = D.countP (fun _ => true) := by
    rw [List.countP_eq_length_filter]; simp
  rw [h]
  exact countP_lt_countP (a := t) D (fun _ _ _ => rfl) ht rfl (by simp)

/-- **The rank does not depend on the order of the list.**  Only the *set* of strings matters,
so the renaming of §4.1.1 is determined by the set `C'` of strings that occur, not by the order
in which the vertices happen to produce them.  This is the half of canonicity (§4, Eq. (22))
that concerns the naming. -/
theorem rankIn_congr_perm {D D' : List (List ℕ)} (h : D.Perm D') (t : List ℕ) :
    rankIn (D, t) = rankIn (D', t) := by
  rw [rankIn_eq_countP, rankIn_eq_countP, h.countP_eq]

/-- Two duplicate-free lists with the same entries are permutations of each other, so by
`Algo.rankIn_congr_perm` they give the same ranks. -/
theorem rankIn_congr_mem {D D' : List (List ℕ)} (hD : D.Nodup) (hD' : D'.Nodup)
    (hmem : ∀ u, u ∈ D ↔ u ∈ D') (t : List ℕ) : rankIn (D, t) = rankIn (D', t) :=
  rankIn_congr_perm (List.perm_of_nodup_nodup_toFinset_eq hD hD'
    (by ext u; simpa using hmem u)) t

/-! ## Raw colored digraphs

§4.1: "Let `X = (V, E, c)` be a vertex-colored digraph without loops".  On raw data the vertex
set is `[0, n)`, the coloring is the list of the colors of `0, 1, …, n-1`, and the edge set is
the list of the out-neighbor lists. -/

/-- A raw vertex-colored digraph: the list of vertex colors, and the list of out-neighbor
lists.  The domain size `n` is the length of either list. -/
abbrev RawCD := List ℕ × List (List ℕ)

/-- **Well-formedness of a raw colored digraph** for the domain size `n`: both lists have `n`
entries, every color is below `n`, every neighbor is a vertex, and no neighbor is listed
twice. -/
structure RawCD.WF (n : ℕ) (X : RawCD) : Prop where
  /-- The coloring lists one color per vertex. -/
  colLen : X.1.length = n
  /-- Colors are naturals below `n`; §4.1.1's standard form. -/
  colLt : ∀ a ∈ X.1, a < n
  /-- The adjacency lists one row per vertex. -/
  adjLen : X.2.length = n
  /-- Every listed neighbor is a vertex. -/
  adjLt : ∀ l ∈ X.2, ∀ a ∈ l, a < n
  /-- A row lists each neighbor once, so it is a set. -/
  adjNodup : ∀ l ∈ X.2, l.Nodup

/-- §4.1, "without loops, i.e. `E ⊆ (V × V) \ diag(V)`". -/
def RawCD.IsLoopless (X : RawCD) : Prop := ∀ x < X.2.length, x ∉ X.2.getD x []

/-- The edge set a raw adjacency describes. -/
def rawEdges (n : ℕ) (adj : List (List ℕ)) : Set (Fin n × Fin n) :=
  {p | (p.2 : ℕ) ∈ adj.getD (p.1 : ℕ) []}

/-- The coloring a raw color list describes. -/
def rawColFun (n : ℕ) (col : List ℕ) : Fin n → ℕ := fun x => col.getD (x : ℕ) 0

/-- **The decoding**: the vertex-colored digraph a raw colored digraph describes. -/
def decCD (n : ℕ) (X : RawCD) : ColoredDigraph (Fin n) ℕ :=
  ⟨rawEdges n X.2, rawColFun n X.1⟩

@[simp] theorem decCD_E (n : ℕ) (X : RawCD) : (decCD n X).E = rawEdges n X.2 := rfl

@[simp] theorem decCD_c (n : ℕ) (X : RawCD) : (decCD n X).c = rawColFun n X.1 := rfl

theorem decCD_recolor (n : ℕ) (X Y : RawCD) (h : Y.2 = X.2) :
    decCD n Y = (decCD n X).recolor (rawColFun n Y.1) := by
  rw [decCD, decCD, ColoredDigraph.recolor, h]

/-- The decoded digraph is loopless exactly when the raw one is. -/
theorem isLoopless_decCD {n : ℕ} {X : RawCD} (h : X.2.length = n) :
    (decCD n X).IsLoopless ↔ X.IsLoopless := by
  constructor
  · intro hL x hx hmem
    have hxn : x < n := h ▸ hx
    have : ((⟨x, hxn⟩ : Fin n), (⟨x, hxn⟩ : Fin n)) ∈ (decCD n X).E ∩ diag (Fin n) :=
      ⟨hmem, rfl⟩
    rw [hL] at this
    exact this
  · intro hL
    rw [ColoredDigraph.IsLoopless, Set.eq_empty_iff_forall_notMem]
    rintro ⟨x, y⟩ ⟨hE, hd⟩
    have hxy : x = y := hd
    subst hxy
    exact hL (x : ℕ) (by rw [h]; exact x.isLt) hE

/-! ## Neighbors -/

/-- The out-neighbors of `x`: the row `x` of the adjacency. -/
def outNbrs (adj : List (List ℕ)) (x : ℕ) : List ℕ := adj.getD x []

/-- The in-neighbors of `x`: the indices of the rows that list `x`. -/
def inNbrs (adj : List (List ℕ)) (x : ℕ) : List ℕ :=
  (adj.zipIdx.filter (fun q => decide (x ∈ q.1))).map Prod.snd

theorem mem_inNbrs {adj : List (List ℕ)} {x z : ℕ} :
    z ∈ inNbrs adj x ↔ z < adj.length ∧ x ∈ adj.getD z [] := by
  constructor
  · intro hz
    rw [inNbrs, List.mem_map] at hz
    obtain ⟨q, hq, rfl⟩ := hz
    rw [List.mem_filter] at hq
    obtain ⟨hmem, hx⟩ := hq
    have hget : adj[q.2]? = some q.1 := by
      rw [← List.mk_mem_zipIdx_iff_getElem?]
      simpa using hmem
    have hlt : q.2 < adj.length := by
      rcases Nat.lt_or_ge q.2 adj.length with h | h
      · exact h
      · rw [List.getElem?_eq_none h] at hget; exact absurd hget (by simp)
    refine ⟨hlt, ?_⟩
    have : adj.getD q.2 [] = q.1 := by
      rw [List.getD_eq_getElem _ _ hlt]
      have := List.getElem?_eq_getElem hlt
      rw [this] at hget
      exact (Option.some_inj.1 hget)
    rw [this]
    exact of_decide_eq_true hx
  · rintro ⟨hlt, hx⟩
    rw [inNbrs, List.mem_map]
    refine ⟨(adj.getD z [], z), ?_, rfl⟩
    rw [List.mem_filter]
    refine ⟨?_, decide_eq_true hx⟩
    rw [List.mk_mem_zipIdx_iff_getElem?, List.getD_eq_getElem _ _ hlt,
      List.getElem?_eq_getElem hlt]

theorem nodup_inNbrs (adj : List (List ℕ)) (x : ℕ) : (inNbrs adj x).Nodup := by
  have hsub : List.Sublist (inNbrs adj x) (adj.zipIdx.map Prod.snd) :=
    List.Sublist.map Prod.snd List.filter_sublist
  have hnd : (adj.zipIdx.map Prod.snd).Nodup := by
    rw [List.zipIdx_map_snd]
    exact List.nodup_range'
  exact List.Nodup.sublist hsub hnd

theorem inNbrs_lt {adj : List (List ℕ)} {x z : ℕ} (h : z ∈ inNbrs adj x) : z < adj.length :=
  (mem_inNbrs.1 h).1

/-! ## The tag of a vertex

§4.1: "Let `c'(x) = (c(x), d⁺ᵢ(x), d⁻ᵢ(x) | i ∈ C)`, where the terms in the string `c'(x)` are
arranged in the order defined by the ordering of `C`."  On raw data the colors are the naturals
`0, 1, …, n-1`, so the string is the color of `x` followed by the `n` out-degrees and then the
`n` in-degrees. -/

/-- The colors of a list of vertices. -/
def nbrCols (col : List ℕ) (l : List ℕ) : List ℕ := l.map (fun y => col.getD y 0)

/-- How often the color `i` occurs in a list of colors. -/
def countAt (p : ℕ × List ℕ) : ℕ := (p.2.filter (fun c => decide (c = p.1))).length

/-- The degree vector: how often each of the colors `0, 1, …, n-1` occurs. -/
def tallyCols (col : List ℕ) (cs : List ℕ) : List ℕ :=
  (List.range col.length).map (fun i => countAt (i, cs))

@[simp] theorem length_tallyCols (col cs : List ℕ) :
    (tallyCols col cs).length = col.length := by simp [tallyCols]

/-- §4.1, the string `c'(x)`. -/
def tagAt (X : RawCD) (x : ℕ) : List ℕ :=
  X.1.getD x 0 :: (tallyCols X.1 (nbrCols X.1 (outNbrs X.2 x)) ++
    tallyCols X.1 (nbrCols X.1 (inNbrs X.2 x)))

@[simp] theorem length_tagAt (X : RawCD) (x : ℕ) :
    (tagAt X x).length = 1 + 2 * X.1.length := by
  rw [tagAt, List.length_cons, List.length_append, length_tallyCols, length_tallyCols]
  omega

/-- §4.1, the set `C' = {c'(x) | x ∈ V}` of strings, listed in the order of the vertices. -/
def rawTags (X : RawCD) : List (List ℕ) := (List.range X.1.length).map (fun x => tagAt X x)

@[simp] theorem length_rawTags (X : RawCD) : (rawTags X).length = X.1.length := by
  simp [rawTags]

theorem getElem_rawTags {X : RawCD} {x : ℕ} (h : x < (rawTags X).length) :
    (rawTags X)[x] = tagAt X x := by
  simp only [rawTags, List.getElem_map, List.getElem_range]

theorem getD_rawTags {X : RawCD} {x : ℕ} (hx : x < X.1.length) :
    (rawTags X).getD x [] = tagAt X x := by
  have hlt : x < (rawTags X).length := by rw [length_rawTags]; exact hx
  rw [List.getD_eq_getElem _ _ hlt, getElem_rawTags]

theorem mem_rawTags {X : RawCD} {t : List ℕ} :
    t ∈ rawTags X ↔ ∃ x < X.1.length, tagAt X x = t := by
  rw [rawTags, List.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩; exact ⟨x, List.mem_range.1 hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩; exact ⟨x, List.mem_range.2 hx, rfl⟩

theorem length_of_mem_rawTags {X : RawCD} {t : List ℕ} (h : t ∈ rawTags X) :
    t.length = 1 + 2 * X.1.length := by
  obtain ⟨x, -, rfl⟩ := mem_rawTags.1 h
  exact length_tagAt X x

/-! ## One round

§4.1.1: rename the strings by their ranks, so that the new colors are again small naturals. -/

/-- The distinct strings that occur, in the order in which the vertices produce them. -/
def rawColorSet (X : RawCD) : List (List ℕ) :=
  RAM.dedupG (([] : List (List ℕ)), rawTags X)

theorem mem_rawColorSet {X : RawCD} {t : List ℕ} : t ∈ rawColorSet X ↔ t ∈ rawTags X :=
  RAM.mem_dedupG_nil _ _

theorem nodup_rawColorSet (X : RawCD) : (rawColorSet X).Nodup :=
  RAM.nodup_dedupG (rawTags X)

theorem length_rawColorSet_le (X : RawCD) : (rawColorSet X).length ≤ X.1.length := by
  have := RAM.length_dedupG_le (rawTags X)
  rw [length_rawTags] at this
  exact this

/-- §4.1 and §4.1.1: one round of naive vertex-refinement, with the colors renamed to their
ranks. -/
def rawNewCol (X : RawCD) : List ℕ :=
  (rawTags X).map (fun t => rankIn (rawColorSet X, t))

@[simp] theorem length_rawNewCol (X : RawCD) : (rawNewCol X).length = X.1.length := by
  simp [rawNewCol]

theorem getD_rawNewCol {X : RawCD} {x : ℕ} (hx : x < X.1.length) :
    (rawNewCol X).getD x 0 = rankIn (rawColorSet X, tagAt X x) := by
  have hlt : x < (rawNewCol X).length := by rw [length_rawNewCol]; exact hx
  rw [List.getD_eq_getElem _ _ hlt]
  simp only [rawNewCol, List.getElem_map]
  rw [getElem_rawTags]

/-- **The new colors are naturals below `n`.**  This is the paper's point in §4.1.1: renaming
by the rank keeps the names short, so the strings do not grow from round to round. -/
theorem rawNewCol_lt {X : RawCD} {a : ℕ} (h : a ∈ rawNewCol X) : a < X.1.length := by
  rw [rawNewCol, List.mem_map] at h
  obtain ⟨t, ht, rfl⟩ := h
  have h1 : rankIn (rawColorSet X, t) < (rawColorSet X).length :=
    rankIn_lt_length (mem_rawColorSet.2 ht)
  have h2 := length_rawColorSet_le X
  omega

/-- **The new name of a string depends only on the set of strings that occur.**  Two raw
colored digraphs producing the same set of strings give one and the same string the same new
color, whatever the vertex order.  Together with `Algo.tagAt_eq_iff` this is the naming half of
canonicity (§4, Eq. (22)): the names come from the set `C'`, which is an isomorphism
invariant. -/
theorem rankIn_rawColorSet_congr {X Y : RawCD} (h : ∀ t, t ∈ rawTags X ↔ t ∈ rawTags Y)
    (t : List ℕ) : rankIn (rawColorSet X, t) = rankIn (rawColorSet Y, t) :=
  rankIn_congr_mem (nodup_rawColorSet X) (nodup_rawColorSet Y)
    (fun u => mem_rawColorSet.trans ((h u).trans mem_rawColorSet.symm)) t

/-- §4.1: "Let `X' = (V, E, c')`."  One round of the process on raw data. -/
def rawRefineStep (X : RawCD) : RawCD := (rawNewCol X, X.2)

@[simp] theorem rawRefineStep_snd (X : RawCD) : (rawRefineStep X).2 = X.2 := rfl

@[simp] theorem rawRefineStep_fst_length (X : RawCD) :
    (rawRefineStep X).1.length = X.1.length := length_rawNewCol X

/-- **Well-formedness is preserved by a round.** -/
theorem rawRefineStep_wf {n : ℕ} {X : RawCD} (h : RawCD.WF n X) :
    RawCD.WF n (rawRefineStep X) where
  colLen := by rw [rawRefineStep_fst_length, h.colLen]
  colLt := by
    intro a ha
    have := rawNewCol_lt (X := X) ha
    rw [h.colLen] at this
    exact this
  adjLen := h.adjLen
  adjLt := h.adjLt
  adjNodup := h.adjNodup

/-- **Two vertices get the same new color exactly when they get the same string.**  The rank is
injective on the strings that occur. -/
theorem rawNewCol_eq_iff {X : RawCD} {x y : ℕ} (hx : x < X.1.length) (hy : y < X.1.length) :
    (rawNewCol X).getD x 0 = (rawNewCol X).getD y 0 ↔ tagAt X x = tagAt X y := by
  rw [getD_rawNewCol hx, getD_rawNewCol hy]
  constructor
  · intro h
    refine rankIn_inj (L := 1 + 2 * X.1.length) (fun u hu => ?_) ?_ ?_ h
    · exact length_of_mem_rawTags (mem_rawColorSet.1 hu)
    · exact mem_rawColorSet.2 (mem_rawTags.2 ⟨x, hx, rfl⟩)
    · exact mem_rawColorSet.2 (mem_rawTags.2 ⟨y, hy, rfl⟩)
  · intro h; rw [h]

/-! ## Counting neighbors by color

§4.1: "`d⁺ᵢ(x)` [is] the number of out-neighbors of `x` of color `i`".  On the mathematical side
that is a `Set.ncard`; on raw data it is how often `i` occurs in the list of the colors of the
row.  The two agree because a row lists each neighbor once and every neighbor is a vertex. -/

/-- A set of vertices cut out by a duplicate-free list and a test has as many elements as the
filtered list. -/
theorem ncard_eq_length_filter {n : ℕ} (l : List ℕ) (hnd : l.Nodup) (hlt : ∀ a ∈ l, a < n)
    (q : ℕ → Bool) :
    {z : Fin n | (z : ℕ) ∈ l ∧ q (z : ℕ) = true}.ncard = (l.filter q).length := by
  classical
  set S : Set (Fin n) := {z : Fin n | (z : ℕ) ∈ l ∧ q (z : ℕ) = true} with hS
  have himg : (Fin.val '' S) = {a : ℕ | a ∈ l.filter q} := by
    ext a
    constructor
    · rintro ⟨z, ⟨hz1, hz2⟩, rfl⟩
      exact List.mem_filter.2 ⟨hz1, hz2⟩
    · intro ha
      obtain ⟨ha1, ha2⟩ := List.mem_filter.1 ha
      exact ⟨⟨a, hlt a ha1⟩, ⟨ha1, ha2⟩, rfl⟩
  have h1 : S.ncard = (Fin.val '' S).ncard :=
    (Set.ncard_image_of_injective S Fin.val_injective).symm
  rw [h1, himg]
  have h2 : {a : ℕ | a ∈ l.filter q} = ↑(l.filter q).toFinset := by
    rw [List.coe_toFinset]
  rw [h2, Set.ncard_coe_finset, List.toFinset_card_of_nodup (hnd.filter q)]

theorem countAt_eq_countP (col : List ℕ) (l : List ℕ) (i : ℕ) :
    countAt (i, nbrCols col l) = (l.filter (fun a => decide (col.getD a 0 = i))).length := by
  rw [countAt, nbrCols, ← List.countP_eq_length_filter, ← List.countP_eq_length_filter,
    List.countP_map]
  rfl

/-- Every color of a well-formed raw colored digraph is below `n`. -/
theorem rawColFun_lt {n : ℕ} {X : RawCD} (h : RawCD.WF n X) (y : Fin n) :
    rawColFun n X.1 y < n := by
  have hy : (y : ℕ) < X.1.length := by rw [h.colLen]; exact y.isLt
  rw [rawColFun, List.getD_eq_getElem _ _ hy]
  exact h.colLt _ (List.getElem_mem hy)

theorem outNbrs_mem {n : ℕ} {X : RawCD} (h : RawCD.WF n X) (x : Fin n) :
    outNbrs X.2 (x : ℕ) ∈ X.2 := by
  have hx : (x : ℕ) < X.2.length := by rw [h.adjLen]; exact x.isLt
  rw [outNbrs, List.getD_eq_getElem _ _ hx]
  exact List.getElem_mem hx

/-- **The raw out-degree is the paper's `d⁺ᵢ(x)`.** -/
theorem outDegCol_eq_countAt {n : ℕ} {X : RawCD} (h : RawCD.WF n X) (x : Fin n) (i : ℕ) :
    (decCD n X).outDegCol i x = countAt (i, nbrCols X.1 (outNbrs X.2 (x : ℕ))) := by
  have hmem := outNbrs_mem h x
  have hnd : (outNbrs X.2 (x : ℕ)).Nodup := h.adjNodup _ hmem
  have hlt : ∀ a ∈ outNbrs X.2 (x : ℕ), a < n := h.adjLt _ hmem
  have hset : {y : Fin n | (x, y) ∈ (decCD n X).E ∧ (decCD n X).c y = i}
      = {z : Fin n | (z : ℕ) ∈ outNbrs X.2 (x : ℕ) ∧
          (fun a => decide (X.1.getD a 0 = i)) (z : ℕ) = true} := by
    ext z
    simp [decCD, rawEdges, rawColFun, outNbrs]
  rw [ColoredDigraph.outDegCol, hset,
    ncard_eq_length_filter (n := n) (outNbrs X.2 (x : ℕ)) hnd hlt
      (fun a => decide (X.1.getD a 0 = i)),
    countAt_eq_countP]

/-- **The raw in-degree is the paper's `d⁻ᵢ(x)`.** -/
theorem inDegCol_eq_countAt {n : ℕ} {X : RawCD} (h : RawCD.WF n X) (x : Fin n) (i : ℕ) :
    (decCD n X).inDegCol i x = countAt (i, nbrCols X.1 (inNbrs X.2 (x : ℕ))) := by
  have hnd : (inNbrs X.2 (x : ℕ)).Nodup := nodup_inNbrs _ _
  have hlt : ∀ a ∈ inNbrs X.2 (x : ℕ), a < n := by
    intro a ha
    have := inNbrs_lt ha
    rw [h.adjLen] at this
    exact this
  have hset : {y : Fin n | (y, x) ∈ (decCD n X).E ∧ (decCD n X).c y = i}
      = {z : Fin n | (z : ℕ) ∈ inNbrs X.2 (x : ℕ) ∧
          (fun a => decide (X.1.getD a 0 = i)) (z : ℕ) = true} := by
    ext z
    have hz : (z : ℕ) < X.2.length := by rw [h.adjLen]; exact z.isLt
    simp [decCD, rawEdges, rawColFun, mem_inNbrs, hz]
  rw [ColoredDigraph.inDegCol, hset,
    ncard_eq_length_filter (n := n) (inNbrs X.2 (x : ℕ)) hnd hlt
      (fun a => decide (X.1.getD a 0 = i)),
    countAt_eq_countP]

/-- A color that no vertex carries contributes nothing. -/
theorem outDegCol_eq_zero {n : ℕ} {X : RawCD} (h : RawCD.WF n X) (x : Fin n) {i : ℕ}
    (hi : n ≤ i) : (decCD n X).outDegCol i x = 0 := by
  have hempty : {y : Fin n | (x, y) ∈ (decCD n X).E ∧ (decCD n X).c y = i} = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro y ⟨-, hy⟩
    have := rawColFun_lt h y
    rw [show (decCD n X).c y = rawColFun n X.1 y from rfl] at hy
    omega
  rw [ColoredDigraph.outDegCol, hempty, Set.ncard_empty]

theorem inDegCol_eq_zero {n : ℕ} {X : RawCD} (h : RawCD.WF n X) (x : Fin n) {i : ℕ}
    (hi : n ≤ i) : (decCD n X).inDegCol i x = 0 := by
  have hempty : {y : Fin n | (y, x) ∈ (decCD n X).E ∧ (decCD n X).c y = i} = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro y ⟨-, hy⟩
    have := rawColFun_lt h y
    rw [show (decCD n X).c y = rawColFun n X.1 y from rfl] at hy
    omega
  rw [ColoredDigraph.inDegCol, hempty, Set.ncard_empty]

/-! ## One round agrees with `Babai.ColoredDigraph.naiveStep` -/

theorem tallyCols_eq_iff {n : ℕ} {X : RawCD} (h : RawCD.WF n X) (cx cy : List ℕ)
    (Fx Fy : ℕ → ℕ) (hlow : ∀ i < n, countAt (i, cx) = Fx i ∧ countAt (i, cy) = Fy i)
    (hhigh : ∀ i, n ≤ i → Fx i = 0 ∧ Fy i = 0) :
    (tallyCols X.1 cx = tallyCols X.1 cy) ↔ ∀ i : ℕ, Fx i = Fy i := by
  rw [tallyCols, tallyCols, List.map_inj_left]
  constructor
  · intro hh i
    rcases Nat.lt_or_ge i n with hi | hi
    · obtain ⟨h1, h2⟩ := hlow i hi
      rw [← h1, ← h2]
      exact hh i (List.mem_range.2 (by rw [h.colLen]; exact hi))
    · obtain ⟨h1, h2⟩ := hhigh i hi
      rw [h1, h2]
  · intro hh i hi
    have hin : i < n := by rw [← h.colLen]; exact List.mem_range.1 hi
    obtain ⟨h1, h2⟩ := hlow i hin
    rw [h1, h2]
    exact hh i

/-- **One round of the routine is one round of naive vertex-refinement.**  Two vertices get the
same string exactly when `Babai.ColoredDigraph.naiveStep` gives them the same color. -/
theorem tagAt_eq_iff {n : ℕ} {X : RawCD} (h : RawCD.WF n X) (x y : Fin n) :
    tagAt X (x : ℕ) = tagAt X (y : ℕ) ↔ (decCD n X).naiveStep x = (decCD n X).naiveStep y := by
  have hlen : ∀ a b : ℕ, (tallyCols X.1 (nbrCols X.1 (outNbrs X.2 a))).length
      = (tallyCols X.1 (nbrCols X.1 (outNbrs X.2 b))).length := by
    intro a b; rw [length_tallyCols, length_tallyCols]
  have hsplit : tagAt X (x : ℕ) = tagAt X (y : ℕ) ↔
      (X.1.getD (x : ℕ) 0 = X.1.getD (y : ℕ) 0
        ∧ tallyCols X.1 (nbrCols X.1 (outNbrs X.2 (x : ℕ)))
            = tallyCols X.1 (nbrCols X.1 (outNbrs X.2 (y : ℕ)))
        ∧ tallyCols X.1 (nbrCols X.1 (inNbrs X.2 (x : ℕ)))
            = tallyCols X.1 (nbrCols X.1 (inNbrs X.2 (y : ℕ)))) := by
    rw [tagAt, tagAt]
    constructor
    · intro hh
      have h1 := List.head_eq_of_cons_eq hh
      have h2 := List.tail_eq_of_cons_eq hh
      obtain ⟨h3, h4⟩ := List.append_inj h2 (hlen _ _)
      exact ⟨h1, h3, h4⟩
    · rintro ⟨h1, h2, h3⟩
      rw [h1, h2, h3]
  rw [hsplit, ColoredDigraph.naiveStep_eq_iff]
  have hout := tallyCols_eq_iff h (nbrCols X.1 (outNbrs X.2 (x : ℕ)))
    (nbrCols X.1 (outNbrs X.2 (y : ℕ)))
    (fun i => (decCD n X).outDegCol i x) (fun i => (decCD n X).outDegCol i y)
    (fun i _ => ⟨(outDegCol_eq_countAt h x i).symm, (outDegCol_eq_countAt h y i).symm⟩)
    (fun i hi => ⟨outDegCol_eq_zero h x hi, outDegCol_eq_zero h y hi⟩)
  have hin := tallyCols_eq_iff h (nbrCols X.1 (inNbrs X.2 (x : ℕ)))
    (nbrCols X.1 (inNbrs X.2 (y : ℕ)))
    (fun i => (decCD n X).inDegCol i x) (fun i => (decCD n X).inDegCol i y)
    (fun i _ => ⟨(inDegCol_eq_countAt h x i).symm, (inDegCol_eq_countAt h y i).symm⟩)
    (fun i hi => ⟨inDegCol_eq_zero h x hi, inDegCol_eq_zero h y hi⟩)
  rw [hout, hin]
  exact Iff.rfl

/-! ## The process

§4.1: "Let `X₀ = X` and `X_{j+1} = X'_j`. … We call the colored digraph `X* = X_k` the stable
refinement of `X`."  As in `Workspace/Refinement/Naive.lean` the process is run for a fixed
number of rounds, `n²`, which is at least the number any input on `n` vertices needs; this keeps
the procedure canonical and matches `Babai.ColoredDigraph.stableRefine`, whose round count is
`Fintype.card (Ω × Ω)`.

The round count has to reach the machine as the **length of a list**, because `List.range n` for
a machine natural `n` is not a `RAM.PolyFun`.  `Algo.sqFuel` is such a list. -/

theorem foldl_const_eq_iterate_gen {α β : Type*} {g : α → α} : ∀ (l : List β) (x : α),
    List.foldl (fun y _ => g y) x l = g^[l.length] x := by
  intro l
  induction l with
  | nil => intro x; rfl
  | cons a t ih =>
      intro x
      rw [List.foldl_cons, ih, List.length_cons, Function.iterate_succ_apply]

/-- A list of length `n²`, built from a list of length `n`: the fuel of the process. -/
def sqFuel (col : List ℕ) : List ℕ := (col.map (fun _ => col)).flatten

@[simp] theorem length_sqFuel (col : List ℕ) :
    (sqFuel col).length = col.length * col.length := by
  rw [sqFuel, List.length_flatten, List.map_map]
  have hc : (List.length ∘ fun _ : ℕ => col) = fun _ : ℕ => col.length := rfl
  rw [hc, List.map_const', List.sum_replicate, smul_eq_mul]

/-- §4.1, `X*`: the stable refinement, on raw data. -/
def rawStableRefine (X : RawCD) : RawCD :=
  List.foldl (fun Y _ => rawRefineStep Y) X (sqFuel X.1)

theorem rawStableRefine_eq_iterate (X : RawCD) :
    rawStableRefine X = rawRefineStep^[X.1.length * X.1.length] X := by
  rw [rawStableRefine, foldl_const_eq_iterate_gen, length_sqFuel]

theorem snd_iterate (X : RawCD) : ∀ j : ℕ, (rawRefineStep^[j] X).2 = X.2
  | 0 => rfl
  | j + 1 => by rw [Function.iterate_succ_apply', rawRefineStep_snd, snd_iterate X j]

theorem wf_iterate {n : ℕ} {X : RawCD} (h : RawCD.WF n X) :
    ∀ j : ℕ, RawCD.WF n (rawRefineStep^[j] X)
  | 0 => h
  | j + 1 => by
      rw [Function.iterate_succ_apply']
      exact rawRefineStep_wf (wf_iterate h j)

/-- **The routine and the process have the same color classes, round by round.** -/
theorem iterate_col_eq_iff {n : ℕ} {X : RawCD} (h : RawCD.WF n X) :
    ∀ (j : ℕ) (x y : Fin n),
      rawColFun n (rawRefineStep^[j] X).1 x = rawColFun n (rawRefineStep^[j] X).1 y
        ↔ (decCD n X).naiveIter j x = (decCD n X).naiveIter j y := by
  intro j
  induction j with
  | zero => intro x y; exact Iff.rfl
  | succ j ih =>
      intro x y
      have hZ : RawCD.WF n (rawRefineStep^[j] X) := wf_iterate h j
      have hZ2 : (rawRefineStep^[j] X).2 = X.2 := snd_iterate X j
      have hx : (x : ℕ) < (rawRefineStep^[j] X).1.length := by rw [hZ.colLen]; exact x.isLt
      have hy : (y : ℕ) < (rawRefineStep^[j] X).1.length := by rw [hZ.colLen]; exact y.isLt
      have hker : kernelSet (rawColFun n (rawRefineStep^[j] X).1)
          = kernelSet ((decCD n X).naiveIter j) := by
        ext p
        simp only [mem_kernelSet]
        exact ih p.1 p.2
      have hcong := ColoredDigraph.kernelSet_naiveStep_congr (decCD n X) hker
      have hdec : decCD n (rawRefineStep^[j] X)
          = (decCD n X).recolor (rawColFun n (rawRefineStep^[j] X).1) :=
        decCD_recolor n X _ hZ2
      have hstep : rawColFun n (rawRefineStep^[j + 1] X).1 x
            = rawColFun n (rawRefineStep^[j + 1] X).1 y
          ↔ (decCD n (rawRefineStep^[j] X)).naiveStep x
            = (decCD n (rawRefineStep^[j] X)).naiveStep y := by
        rw [Function.iterate_succ_apply']
        exact (rawNewCol_eq_iff hx hy).trans (tagAt_eq_iff hZ x y)
      rw [hstep, hdec]
      have h1 : ((x, y) : Fin n × Fin n)
          ∈ kernelSet ((decCD n X).recolor (rawColFun n (rawRefineStep^[j] X).1)).naiveStep
        ↔ ((x, y) : Fin n × Fin n)
          ∈ kernelSet ((decCD n X).recolor ((decCD n X).naiveIter j)).naiveStep := by
        rw [hcong]
      simpa only [mem_kernelSet, ColoredDigraph.naiveIter_succ] using h1

/-- **§4.1, `X*`: the routine and `Babai.ColoredDigraph.stableRefine` have the same color
classes.**  This is row R1 of `Workspace/Algo/DESIGN.md`, item 1.2. -/
theorem rawStableRefine_spec {n : ℕ} {X : RawCD} (h : RawCD.WF n X) (x y : Fin n) :
    rawColFun n (rawStableRefine X).1 x = rawColFun n (rawStableRefine X).1 y
      ↔ (decCD n X).stableRefine.c x = (decCD n X).stableRefine.c y := by
  have hcard : Fintype.card (Fin n × Fin n) = n * n := by simp
  rw [rawStableRefine_eq_iterate, h.colLen]
  show _ ↔ (decCD n X).naiveIter (Fintype.card (Fin n × Fin n)) x
    = (decCD n X).naiveIter (Fintype.card (Fin n × Fin n)) y
  rw [hcard]
  exact iterate_col_eq_iff h (n * n) x y

/-- The same statement as an equality of partitions. -/
theorem rawStableRefine_kernelSet {n : ℕ} {X : RawCD} (h : RawCD.WF n X) :
    kernelSet (rawColFun n (rawStableRefine X).1) = kernelSet (decCD n X).stableRefine.c := by
  ext p
  simp only [mem_kernelSet]
  exact rawStableRefine_spec h p.1 p.2

/-- The answer is again a well-formed raw colored digraph, with the same edges. -/
theorem rawStableRefine_wf {n : ℕ} {X : RawCD} (h : RawCD.WF n X) :
    RawCD.WF n (rawStableRefine X) := by
  rw [rawStableRefine_eq_iterate]
  exact wf_iterate h _

theorem rawStableRefine_snd (X : RawCD) : (rawStableRefine X).2 = X.2 := by
  rw [rawStableRefine_eq_iterate]
  exact snd_iterate X _

end Algo
