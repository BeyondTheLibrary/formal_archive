/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 4.1.1 (Complexity of naive refinement; tagged structures): the tagged refinement
process.
-/
import Workspace.Refinement.Naive
import Mathlib.Data.List.Lex

/-!
# §4.1.1 The tagged refinement process

§4.1.1 describes colors as *strings* over an alphabet `Σ ⊇ [n]` and measures the lengths of
these strings.  `Refinement/Naive.lean` keeps colors abstract, which is enough for the
mathematics of §4.1 but cannot say how long a color or a tag is.  This file follows the
paper's string model:

* a color is a string of naturals, `List ℕ`, ordered lexicographically;
* a tag is a string of palettes separated by the special symbol `*`; we keep it as the list of
  the palettes, `List (List (List ℕ))`, and count the separators in `tagLen`.

The objects are `TaggedDigraph Ω (List ℕ) (List (List ℕ))` (`StrTagged Ω`).

## The process (lines 2886–2899)

"Let `X = (V, E, c, t)` be a tagged digraph.  Let us define `X' = (V, E, d, u)` as follows:
let `st(X) = (V, E, st(c), u)` and let `X' = (V, E, (st(c))', u)` where the coloring `st(c)'`
is defined … by the application of one round of naive refinement to the untagged colored
digraph `(V, E, st(c))`." (`tagStep`)  "Now let `X₀ = X` and `X_{j+1} = X_j'`" (`tagIter`).
"We stop when `X_k` is stable, i.e., when `N(c_{k+1}) = N(c_k)`" (`stopIdx`).  "We write
`X* = st(X_k)` and call it the stable refinement of `X`.  We write `t*` for the final tag"
(`stableTagged`).

## What is proved

* One round preserves isomorphisms (`iso_tagStep`), hence so does every `X_j`
  (`iso_tagIter`), and every tag `t_j` is an isomorphism invariant (`tag_tagIter_eq_of_iso`):
  lines 2900–2904.
* The process stops within `n - 1` rounds (`stopIdx_le`), as for the untagged process.
* For the stable refinement, Eq. (24) holds when the two initial tags have the same length
  (`iso_stableTagged`), and fails without that hypothesis (`iso_stableTagged_counterexample`):
  see the corrected paper (§4.1.1: Eq. (24) for the tagged stable refinement).
* The lengths: "The length of tag `t₁` is the length `t₀` … plus the size of the list of
  initial colors" (`tagLen_tag_tagIter_one`); "For `j ≥ 1` the increment `|t_{j+1}| - |t_j|`
  is `O(n²)`" (`tagLen_tag_tagIter_succ_le`: at most `2n² + 2n + 1`); "so the length of the
  final tag is `|t*| = |t₁| + O(n³)`" (`tagLen_finalTag_le`).
* The bound `O(n³)` is attained: on the directed path with `n` vertices, `m = n - 1` and
  `|t₁| = 2` (`pathX_tagLen_tag_tagIter_one`), while `(n-1)³ ≤ 12 |t*|`
  (`pathX_tagLen_finalTag`).  Since `X*` contains `t*`, no algorithm can output `X*` in the
  printed time `O(nm) + |t₁|` (or `O(m log n)`): see the corrected paper,
  entry 131 (§4.1.1: running time of the tagged refinement).

No axiom, no `sorry`.
-/

namespace Babai

namespace TaggedDigraph

/-- §4.1.1: tagged colored digraphs whose colors are strings over `Σ ⊇ [n]` and whose tag is a
string of palettes. -/
abbrev StrTagged (Ω : Type*) := TaggedDigraph Ω (List ℕ) (List (List ℕ))

variable {Ω Ω' : Type*} [Fintype Ω] [Fintype Ω']

section Round

variable (X : StrTagged Ω)

/-- `N(c)`, the number of colors used by `c`: the length of the ordered palette. -/
def numColors : ℕ := X.oldColors.length

/-- `st(c)(x)`: "`st(c)(x) = i` if `c(x)` is the `i`-th element of the ordered set `C`"
(counting from `0`). -/
def rank (x : Ω) : ℕ := X.oldColors.idxOf (X.c x)

/-- `d⁺ᵢ(x)` for the standardized coloring: the number of out-neighbors of `x` of color `i`. -/
noncomputable def outCnt (i : ℕ) (x : Ω) : ℕ := {y | (x, y) ∈ X.E ∧ X.rank y = i}.ncard

/-- `d⁻ᵢ(x)` for the standardized coloring: the number of in-neighbors of `x` of color `i`. -/
noncomputable def inCnt (i : ℕ) (x : Ω) : ℕ := {y | (y, x) ∈ X.E ∧ X.rank y = i}.ncard

/-- §4.1 applied to `st(c)`: "`c'(x) = (c(x), d⁺ᵢ(x), d⁻ᵢ(x) | i ∈ C)`, where the terms in
the string `c'(x)` are arranged in the order defined by the ordering of `C`", with
`C = [N(c)]`. -/
noncomputable def tagColor (x : Ω) : List ℕ :=
  X.rank x :: (List.range X.numColors).flatMap (fun i => [X.outCnt i x, X.inCnt i x])

/-- §4.1.1: one round of the tagged process, `X ↦ X'`: standardize (appending the ordered list
of the old colors to the tag), then refine the standardized coloring, keeping the tag. -/
noncomputable def tagStep : StrTagged Ω :=
  ⟨⟨X.E, X.tagColor⟩, X.tag ++ [X.oldColors]⟩

/-- §4.1.1: `st(X) = (V, E, st(c), t * C)`, with the colors `i ∈ [N(c)]` written as one-letter
strings. -/
noncomputable def stStr : StrTagged Ω :=
  ⟨⟨X.E, fun x => [X.rank x]⟩, X.tag ++ [X.oldColors]⟩

theorem c_mem_oldColors (x : Ω) : X.c x ∈ X.oldColors := (X.mem_oldColors _).2 ⟨x, rfl⟩

theorem rank_lt (x : Ω) : X.rank x < X.numColors :=
  List.idxOf_lt_length_iff.2 (X.c_mem_oldColors x)

theorem rank_eq_iff (x y : Ω) : X.rank x = X.rank y ↔ X.c x = X.c y :=
  List.idxOf_inj (X.c_mem_oldColors x)

theorem exists_rank_eq {i : ℕ} (hi : i < X.numColors) : ∃ x, X.rank x = i := by
  have hmem : X.oldColors[i] ∈ X.oldColors := List.getElem_mem hi
  obtain ⟨x, hx⟩ := (X.mem_oldColors _).1 hmem
  refine ⟨x, ?_⟩
  rw [rank, hx]
  exact List.Nodup.idxOf_getElem X.oldColors_nodup i hi

theorem length_flatMap_pair (N : ℕ) (f g : ℕ → ℕ) :
    ((List.range N).flatMap (fun i => [f i, g i])).length = 2 * N := by
  induction N with
  | zero => simp
  | succ N ih => rw [List.range_succ, List.flatMap_append, List.length_append, ih]; simp; ring

theorem flatMap_pair_eq_iff (N : ℕ) (f g f' g' : ℕ → ℕ) :
    (List.range N).flatMap (fun i => [f i, g i]) = (List.range N).flatMap (fun i => [f' i, g' i])
      ↔ ∀ i < N, f i = f' i ∧ g i = g' i := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_append]
    constructor
    · intro h
      obtain ⟨h1, h2⟩ := List.append_inj' h (by simp)
      have h2' : f N = f' N ∧ g N = g' N := by simpa using h2
      intro i hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · exact (ih.1 h1) i hi
      · exact h2'
    · intro h
      rw [ih.2 (fun i hi => h i (Nat.lt_succ_of_lt hi))]
      obtain ⟨e1, e2⟩ := h N (Nat.lt_succ_self N)
      simp [e1, e2]

theorem length_tagColor (x : Ω) : (X.tagColor x).length = 2 * X.numColors + 1 := by
  rw [tagColor, List.length_cons, length_flatMap_pair]

theorem outCnt_rank (x z : Ω) :
    X.outCnt (X.rank z) x = {y | (x, y) ∈ X.E ∧ X.c y = X.c z}.ncard := by
  simp only [outCnt, rank_eq_iff]

theorem inCnt_rank (x z : Ω) :
    X.inCnt (X.rank z) x = {y | (y, x) ∈ X.E ∧ X.c y = X.c z}.ncard := by
  simp only [inCnt, rank_eq_iff]

/-- §4.1: two vertices get the same refined color exactly if they have the same color and, for
every color class, the same numbers of out- and in-neighbors in it. -/
theorem tagColor_eq_iff (x y : Ω) :
    X.tagColor x = X.tagColor y ↔ X.c x = X.c y ∧ ∀ z : Ω,
      {w | (x, w) ∈ X.E ∧ X.c w = X.c z}.ncard = {w | (y, w) ∈ X.E ∧ X.c w = X.c z}.ncard ∧
      {w | (w, x) ∈ X.E ∧ X.c w = X.c z}.ncard = {w | (w, y) ∈ X.E ∧ X.c w = X.c z}.ncard := by
  rw [tagColor, tagColor, List.cons.injEq, flatMap_pair_eq_iff, rank_eq_iff]
  refine and_congr Iff.rfl ⟨fun h z => ?_, fun h i hi => ?_⟩
  · rw [← outCnt_rank, ← outCnt_rank, ← inCnt_rank, ← inCnt_rank]
    exact h _ (X.rank_lt z)
  · obtain ⟨z, rfl⟩ := X.exists_rank_eq hi
    rw [outCnt_rank, outCnt_rank, inCnt_rank, inCnt_rank]
    exact h z

/-- §4.1: "Clearly, the coloring `c'` is a refinement of `c`." -/
theorem tagColor_isRefinement : IsRefinement X.tagColor X.c :=
  fun x y h => ((X.tagColor_eq_iff x y).1 h).1

end Round

/-! ### Isomorphisms are preserved (Eq. (24), lines 2900–2904) -/

section Iso

variable {X : StrTagged Ω} {Y : StrTagged Ω'}

theorem rank_map {f : Ω ≃ Ω'} (hc : ∀ v, Y.c (f v) = X.c v) (x : Ω) :
    Y.rank (f x) = X.rank x := by
  rw [rank, rank, hc, oldColors_eq_of_preserves f hc]

theorem numColors_map {f : Ω ≃ Ω'} (hc : ∀ v, Y.c (f v) = X.c v) :
    Y.numColors = X.numColors := by
  rw [numColors, numColors, oldColors_eq_of_preserves f hc]

theorem outCnt_map {f : Ω ≃ Ω'} (hE : ∀ x y, (x, y) ∈ X.E ↔ (f x, f y) ∈ Y.E)
    (hc : ∀ v, Y.c (f v) = X.c v) (i : ℕ) (x : Ω) : Y.outCnt i (f x) = X.outCnt i x := by
  have : {y | (f x, y) ∈ Y.E ∧ Y.rank y = i} = f '' {y | (x, y) ∈ X.E ∧ X.rank y = i} := by
    ext y
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨f.symm y, ⟨(hE _ _).2 (by simpa using h1), ?_⟩, by simp⟩
      rw [← rank_map hc]; simpa using h2
    · rintro ⟨z, ⟨h1, h2⟩, rfl⟩
      exact ⟨(hE _ _).1 h1, by rw [rank_map hc]; exact h2⟩
  rw [outCnt, outCnt, this, Set.ncard_image_of_injective _ f.injective]

theorem inCnt_map {f : Ω ≃ Ω'} (hE : ∀ x y, (x, y) ∈ X.E ↔ (f x, f y) ∈ Y.E)
    (hc : ∀ v, Y.c (f v) = X.c v) (i : ℕ) (x : Ω) : Y.inCnt i (f x) = X.inCnt i x := by
  have : {y | (y, f x) ∈ Y.E ∧ Y.rank y = i} = f '' {y | (y, x) ∈ X.E ∧ X.rank y = i} := by
    ext y
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨f.symm y, ⟨(hE _ _).2 (by simpa using h1), ?_⟩, by simp⟩
      rw [← rank_map hc]; simpa using h2
    · rintro ⟨z, ⟨h1, h2⟩, rfl⟩
      exact ⟨(hE _ _).1 h1, by rw [rank_map hc]; exact h2⟩
  rw [inCnt, inCnt, this, Set.ncard_image_of_injective _ f.injective]

theorem tag_append_eq_iff (s t : List (List (List ℕ))) (p q : List (List ℕ)) :
    t ++ [q] = s ++ [p] ↔ t = s ∧ q = p := by
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := List.append_inj' h rfl
    exact ⟨h1, by simpa using h2⟩
  · rintro ⟨rfl, rfl⟩; rfl

/-- The colors are determined by the ranks once the palettes agree. -/
theorem c_eq_of_rank_eq {f : Ω ≃ Ω'} (hp : Y.oldColors = X.oldColors) {x : Ω}
    (h : Y.rank (f x) = X.rank x) : Y.c (f x) = X.c x := by
  rw [rank, rank, hp] at h
  exact (List.idxOf_inj (hp ▸ Y.c_mem_oldColors (f x))).1 h

/-- **One round preserves isomorphisms**: `Iso(X', Y') = Iso(X, Y)` for tagged digraphs
(Eq. (24) with Eq. (25), lines 2900–2904). -/
theorem iso_tagStep (X : StrTagged Ω) (Y : StrTagged Ω') :
    Iso X.tagStep Y.tagStep = Iso X Y := by
  ext f
  rw [mem_iso_iff, mem_iso_iff]
  change (Y.tag ++ [Y.oldColors] = X.tag ++ [X.oldColors] ∧
      (∀ x y, (x, y) ∈ X.E ↔ (f x, f y) ∈ Y.E) ∧ ∀ x, Y.tagColor (f x) = X.tagColor x) ↔
    (Y.tag = X.tag ∧ (∀ x y, (x, y) ∈ X.E ↔ (f x, f y) ∈ Y.E) ∧ ∀ x, Y.c (f x) = X.c x)
  rw [tag_append_eq_iff]
  constructor
  · rintro ⟨⟨ht, hp⟩, hE, hc⟩
    refine ⟨ht, hE, fun x => c_eq_of_rank_eq hp ?_⟩
    have := hc x
    rw [tagColor, tagColor, List.cons.injEq] at this
    exact this.1
  · rintro ⟨ht, hE, hc⟩
    refine ⟨⟨ht, oldColors_eq_of_preserves f hc⟩, hE, fun x => ?_⟩
    rw [tagColor, tagColor, rank_map hc, numColors_map hc]
    congr 1
    refine List.flatMap_congr fun i _ => ?_
    rw [outCnt_map hE hc, inCnt_map hE hc]

/-- Standardizing preserves isomorphisms: `Iso(st(X), st(Y)) = Iso(X, Y)`. -/
theorem iso_stStr (X : StrTagged Ω) (Y : StrTagged Ω') :
    Iso X.stStr Y.stStr = Iso X Y := by
  ext f
  rw [mem_iso_iff, mem_iso_iff]
  change (Y.tag ++ [Y.oldColors] = X.tag ++ [X.oldColors] ∧
      (∀ x y, (x, y) ∈ X.E ↔ (f x, f y) ∈ Y.E) ∧ ∀ x, [Y.rank (f x)] = [X.rank x]) ↔
    (Y.tag = X.tag ∧ (∀ x y, (x, y) ∈ X.E ↔ (f x, f y) ∈ Y.E) ∧ ∀ x, Y.c (f x) = X.c x)
  rw [tag_append_eq_iff]
  constructor
  · rintro ⟨⟨ht, hp⟩, hE, hc⟩
    exact ⟨ht, hE, fun x => c_eq_of_rank_eq hp (List.singleton_inj.1 (hc x))⟩
  · rintro ⟨ht, hE, hc⟩
    exact ⟨⟨ht, oldColors_eq_of_preserves f hc⟩, hE, fun x => by rw [rank_map hc]⟩

end Iso

/-! ### The process -/

section Process

/-- §4.1.1: "Now let `X₀ = X` and `X_{j+1} = X_j'`." -/
noncomputable def tagIter (X : StrTagged Ω) : ℕ → StrTagged Ω
  | 0 => X
  | j + 1 => (tagIter X j).tagStep

@[simp] theorem tagIter_zero (X : StrTagged Ω) : tagIter X 0 = X := rfl

theorem tagIter_succ (X : StrTagged Ω) (j : ℕ) : tagIter X (j + 1) = (tagIter X j).tagStep := rfl

/-- §4.1.1, lines 2900–2904: "Eq. 24 continues to hold" for every round: `Iso(X_j, Y_j) =
Iso(X, Y)`. -/
theorem iso_tagIter (X : StrTagged Ω) (Y : StrTagged Ω') (j : ℕ) :
    Iso (tagIter X j) (tagIter Y j) = Iso X Y := by
  induction j with
  | zero => rfl
  | succ j ih => rw [tagIter_succ, tagIter_succ, iso_tagStep, ih]

/-- §4.1.1: "Each tag `t_j` is an isomorphism invariant." -/
theorem tag_tagIter_eq_of_iso {X : StrTagged Ω} {Y : StrTagged Ω'} {f : Ω ≃ Ω'}
    (hf : f ∈ Iso X Y) (j : ℕ) : (tagIter Y j).tag = (tagIter X j).tag := by
  rw [← iso_tagIter X Y j] at hf
  exact (mem_iso_iff.1 hf).1

theorem numColors_eq_of_iso {X : StrTagged Ω} {Y : StrTagged Ω'} {f : Ω ≃ Ω'}
    (hf : f ∈ Iso X Y) : Y.numColors = X.numColors :=
  numColors_map (mem_iso_iff.1 hf).2.2

/-- The number of colors is the number of values of the coloring. -/
theorem numColors_eq_card_range (X : StrTagged Ω) :
    X.numColors = Nat.card (Set.range X.c) := by
  have h : (X.realizedColors : Set (List ℕ)) = Set.range X.c := by
    ext a; simp [realizedColors]
  rw [numColors, oldColors, Finset.length_sort, ← h, Nat.card_coe_set_eq, Set.ncard_coe_finset]

theorem kernelSet_tagIter_succ_subset (X : StrTagged Ω) (j : ℕ) :
    kernelSet (tagIter X (j + 1)).c ⊆ kernelSet (tagIter X j).c :=
  fun p hp => (tagIter X j).tagColor_isRefinement p.1 p.2 hp

/-- Once a round leaves the partition unchanged, so does the next one: the refined color only
sees the partition. -/
theorem kernelSet_tagIter_step (X : StrTagged Ω) (j : ℕ)
    (h : kernelSet (tagIter X (j + 1)).c = kernelSet (tagIter X j).c) :
    kernelSet (tagIter X (j + 2)).c = kernelSet (tagIter X (j + 1)).c := by
  have hk : ∀ x y, (tagIter X (j + 1)).c x = (tagIter X (j + 1)).c y ↔
      (tagIter X j).c x = (tagIter X j).c y := fun x y => by
    have := congrArg (fun S => (x, y) ∈ S) h
    simpa using this
  ext ⟨x, y⟩
  change (tagIter X (j + 1)).tagColor x = (tagIter X (j + 1)).tagColor y ↔
    (tagIter X j).tagColor x = (tagIter X j).tagColor y
  rw [tagColor_eq_iff, tagColor_eq_iff]
  have hE : (tagIter X (j + 1)).E = (tagIter X j).E := rfl
  simp only [hk, hE]

/-- A coarser partition has at most as many classes. -/
theorem card_range_le_of_kernelSet_subset {α β γ : Type*} [Finite α] (f : α → β)
    (g : α → γ) (hsub : kernelSet g ⊆ kernelSet f) :
    Nat.card (Set.range f) ≤ Nat.card (Set.range g) := by
  classical
  haveI : Fintype α := Fintype.ofFinite α
  let φ : Set.range g → Set.range f := fun c => ⟨f c.2.choose, c.2.choose, rfl⟩
  have hsurj : Function.Surjective φ := by
    rintro ⟨_, a, rfl⟩
    refine ⟨⟨g a, a, rfl⟩, Subtype.ext ?_⟩
    have hc : g (Exists.choose (⟨a, rfl⟩ : ∃ y, g y = g a)) = g a :=
      Exists.choose_spec (⟨a, rfl⟩ : ∃ y, g y = g a)
    exact hsub (show (_, a) ∈ kernelSet g from hc)
  haveI : Finite (Set.range f) := (Set.finite_range f).to_subtype
  haveI : Finite (Set.range g) := (Set.finite_range g).to_subtype
  exact Nat.card_le_card_of_surjective φ hsurj

/-- `N(c_{j+1}) = N(c_j)` exactly when the round did not change the partition. -/
theorem numColors_succ_eq_iff (X : StrTagged Ω) (j : ℕ) :
    (tagIter X (j + 1)).numColors = (tagIter X j).numColors ↔
      kernelSet (tagIter X (j + 1)).c = kernelSet (tagIter X j).c := by
  rw [numColors_eq_card_range, numColors_eq_card_range]
  constructor
  · intro h
    by_contra hne
    have := card_range_lt_of_kernelSet_ssubset (tagIter X j).c (tagIter X (j + 1)).c
      (kernelSet_tagIter_succ_subset X j) hne
    omega
  · intro h
    exact le_antisymm (card_range_le_of_kernelSet_subset _ _ h.symm.le)
      (card_range_le_of_kernelSet_subset _ _ h.le)

theorem exists_stop (X : StrTagged Ω) :
    ∃ j, (tagIter X (j + 1)).numColors = (tagIter X j).numColors :=
  ⟨Fintype.card Ω - 1, (numColors_succ_eq_iff X _).2
    (kernelSet_eq_of_card_sub_one_le (fun j => (tagIter X j).c) (kernelSet_tagIter_succ_subset X)
      (kernelSet_tagIter_step X) le_rfl)⟩

open Classical in
/-- §4.1.1: "We stop when `X_k` is stable, i.e., when `N(c_{k+1}) = N(c_k)`": the first such
`k`. -/
noncomputable def stopIdx (X : StrTagged Ω) : ℕ := Nat.find (exists_stop X)

theorem stopIdx_spec (X : StrTagged Ω) :
    (tagIter X (stopIdx X + 1)).numColors = (tagIter X (stopIdx X)).numColors := by
  classical
  exact Nat.find_spec (exists_stop X)

/-- §4.1.1, line 2850: "The naive refinement process clearly terminates in `k ≤ n - 1`
rounds." -/
theorem stopIdx_le (X : StrTagged Ω) : stopIdx X ≤ Fintype.card Ω - 1 := by
  classical
  exact Nat.find_min' (exists_stop X) ((numColors_succ_eq_iff X _).2
    (kernelSet_eq_of_card_sub_one_le (fun j => (tagIter X j).c) (kernelSet_tagIter_succ_subset X)
      (kernelSet_tagIter_step X) le_rfl))

/-- §4.1.1: "We write `X* = st(X_k)` and call it the stable refinement of `X`." -/
noncomputable def stableTagged (X : StrTagged Ω) : StrTagged Ω := (tagIter X (stopIdx X)).stStr

/-- §4.1.1: "We write `t*` for the final tag." -/
noncomputable def finalTag (X : StrTagged Ω) : List (List (List ℕ)) := (stableTagged X).tag

theorem length_tag_tagIter (X : StrTagged Ω) (j : ℕ) :
    (tagIter X j).tag.length = X.tag.length + j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [tagIter_succ]
    change ((tagIter X j).tag ++ [(tagIter X j).oldColors]).length = _
    rw [List.length_append, ih]; simp; ring

/-- Isomorphic inputs stop at the same round. -/
theorem stopIdx_eq_of_iso {X : StrTagged Ω} {Y : StrTagged Ω'} {f : Ω ≃ Ω'}
    (hf : f ∈ Iso X Y) : stopIdx Y = stopIdx X := by
  classical
  have hN : ∀ j, (tagIter Y j).numColors = (tagIter X j).numColors := fun j =>
    numColors_eq_of_iso (f := f) (by rw [iso_tagIter]; exact hf)
  have hP : ∀ j, (tagIter Y (j + 1)).numColors = (tagIter Y j).numColors ↔
      (tagIter X (j + 1)).numColors = (tagIter X j).numColors := fun j => by rw [hN, hN]
  unfold stopIdx
  exact le_antisymm (Nat.find_min' _ ((hP _).2 (Nat.find_spec (exists_stop X))))
    (Nat.find_min' _ ((hP _).1 (Nat.find_spec (exists_stop Y))))

/-- **Eq. (24) for the tagged stable refinement** (lines 2900–2904: "from each `X_j` we can
reconstruct `X`, so Eq. 24 continues to hold"), when the two initial tags have the same
length.  Without that hypothesis it fails (`iso_stableTagged_counterexample`). -/
theorem iso_stableTagged (X : StrTagged Ω) (Y : StrTagged Ω')
    (h : X.tag.length = Y.tag.length) :
    Iso (stableTagged X) (stableTagged Y) = Iso X Y := by
  by_cases hk : stopIdx Y = stopIdx X
  · rw [stableTagged, stableTagged, hk, iso_stStr, iso_tagIter]
  · have h1 : Iso (stableTagged X) (stableTagged Y) = ∅ := by
      apply iso_of_tag_ne
      intro ht
      have := congrArg List.length ht
      simp only [stableTagged, stStr, List.length_append, length_tag_tagIter,
        List.length_singleton] at this
      omega
    have h2 : Iso X Y = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.2
      intro f hf
      exact hk (stopIdx_eq_of_iso hf)
    rw [h1, h2]

theorem tagIter_tagStep (X : StrTagged Ω) (j : ℕ) : tagIter X.tagStep j = tagIter X (j + 1) := by
  induction j with
  | zero => rfl
  | succ j ih => rw [tagIter_succ, ih]; rfl

/-- If the first round changes the partition, the stable refinement of `X'` is that of `X`. -/
theorem stableTagged_tagStep (X : StrTagged Ω)
    (h : (tagIter X 1).numColors ≠ (tagIter X 0).numColors) :
    stableTagged X.tagStep = stableTagged X := by
  classical
  have h2 : ∃ j, (tagIter X (j + 1 + 1)).numColors = (tagIter X (j + 1)).numColors := by
    obtain ⟨j, hj⟩ := exists_stop X
    rcases j with _ | j
    · exact absurd hj h
    · exact ⟨j, hj⟩
  have hX : stopIdx X = Nat.find h2 + 1 := Nat.find_comp_succ (exists_stop X) h2 h
  have hY : stopIdx X.tagStep = Nat.find h2 := by
    unfold stopIdx
    congr 1
    funext j
    rw [tagIter_tagStep, tagIter_tagStep]
  rw [stableTagged, stableTagged, hY, hX, tagIter_tagStep]

/-- **The counterexample**: Eq. (24), `Iso(X*, Y*) = Iso(X, Y)`, fails for the tagged stable
refinement when the initial tags have different lengths.  Take `X` = the digraph `0 → 1` with
both vertices colored by the empty string and the empty tag, and `Y = X'`.  The first round
splits the two vertices, so `X* = Y*`; but `Iso(X, Y) = ∅`, because the tags differ. -/
theorem iso_stableTagged_counterexample :
    ∃ X Y : StrTagged (Fin 2), Iso (stableTagged X) (stableTagged Y) ≠ Iso X Y := by
  classical
  let X : StrTagged (Fin 2) := ⟨⟨{(0, 1)}, fun _ => []⟩, []⟩
  have hsplit : (tagIter X 1).numColors ≠ (tagIter X 0).numColors := by
    rw [Ne, numColors_succ_eq_iff]
    intro hk
    have h01 : ((0 : Fin 2), (1 : Fin 2)) ∈ kernelSet (tagIter X 0).c := rfl
    rw [← hk] at h01
    change X.tagColor 0 = X.tagColor 1 at h01
    rw [tagColor_eq_iff] at h01
    have := (h01.2 0).1
    have e0 : {w : Fin 2 | ((0 : Fin 2), w) ∈ X.E ∧ X.c w = X.c 0} = {1} := by
      ext w; fin_cases w <;> simp [X]
    have e1 : {w : Fin 2 | ((1 : Fin 2), w) ∈ X.E ∧ X.c w = X.c 0} = ∅ := by
      ext w; fin_cases w <;> simp [X]
    rw [e0, e1] at this
    simp at this
  refine ⟨X, X.tagStep, ?_⟩
  rw [stableTagged_tagStep X hsplit]
  intro heq
  have hrefl : Equiv.refl (Fin 2) ∈ Iso (stableTagged X) (stableTagged X) := by
    rw [mem_iso_iff]; exact ⟨rfl, fun _ _ => Iff.rfl, fun _ => rfl⟩
  rw [heq, mem_iso_iff] at hrefl
  have := congrArg List.length hrefl.1
  simp [tagStep, X] at this

/-! ### The lengths of the tags (lines 2905–2909) -/

/-- The length of a palette written as a string: each color followed by a separator, and the
separator `*` after the palette. -/
def palLen (p : List (List ℕ)) : ℕ := (p.map (fun col => col.length + 1)).sum + 1

/-- The length of a tag written as a string. -/
def tagLen (t : List (List (List ℕ))) : ℕ := (t.map palLen).sum

theorem tagLen_append_singleton (t : List (List (List ℕ))) (p : List (List ℕ)) :
    tagLen (t ++ [p]) = tagLen t + palLen p := by
  simp [tagLen]

/-- §4.1.1: "The length of tag `t₁` is the length `t₀` (typically `0`) plus the size of the
list of initial colors." -/
theorem tagLen_tag_tagIter_one (X : StrTagged Ω) :
    tagLen (tagIter X 1).tag = tagLen X.tag + palLen X.oldColors :=
  tagLen_append_singleton _ _

theorem numColors_le_card (X : StrTagged Ω) : X.numColors ≤ Fintype.card Ω := by
  rw [numColors_eq_card_range, ← Nat.card_eq_fintype_card]
  exact Finite.card_range_le _

theorem palLen_le (p : List (List ℕ)) (L : ℕ) (h : ∀ col ∈ p, col.length ≤ L) :
    palLen p ≤ p.length * (L + 1) + 1 := by
  rw [palLen]
  have : (p.map (fun col => col.length + 1)).sum ≤ (p.map (fun _ => L + 1)).sum :=
    List.sum_le_sum (fun col hc => by simpa using h col hc)
  simp only [List.map_const', List.sum_replicate, smul_eq_mul] at this
  omega

/-- §4.1.1: "For `j ≥ 1` the increment `|t_{j+1}| - |t_j|` is `O(n²)`": at most
`2n² + 2n + 1`, since the palette of `c_j` has at most `n` colors, each of length
`2N(c_{j-1}) + 1 ≤ 2n + 1`. -/
theorem tagLen_tag_tagIter_succ_le (X : StrTagged Ω) (j : ℕ) :
    tagLen (tagIter X (j + 2)).tag ≤
      tagLen (tagIter X (j + 1)).tag + (2 * Fintype.card Ω ^ 2 + 2 * Fintype.card Ω + 1) := by
  set n := Fintype.card Ω
  rw [tagIter_succ X (j + 1)]
  change tagLen ((tagIter X (j + 1)).tag ++ [(tagIter X (j + 1)).oldColors]) ≤ _
  rw [tagLen_append_singleton]
  have hlen : ∀ col ∈ (tagIter X (j + 1)).oldColors, col.length ≤ 2 * n + 1 := by
    intro col hc
    obtain ⟨v, rfl⟩ := ((tagIter X (j + 1)).mem_oldColors col).1 hc
    change ((tagIter X j).tagColor v).length ≤ _
    rw [length_tagColor]
    have := numColors_le_card (tagIter X j)
    omega
  have hp := palLen_le _ _ hlen
  have hN : (tagIter X (j + 1)).oldColors.length ≤ n := numColors_le_card _
  have : (tagIter X (j + 1)).oldColors.length * (2 * n + 1 + 1) ≤ n * (2 * n + 2) :=
    Nat.mul_le_mul hN le_rfl
  nlinarith

/-- The final tag is the tag of `X_{k+1}`. -/
theorem finalTag_eq (X : StrTagged Ω) : finalTag X = (tagIter X (stopIdx X + 1)).tag := rfl

/-- §4.1.1: "so the length of the final tag is `|t*| = |t₁| + O(n³)`": at most
`|t₁| + (n - 1)(2n² + 2n + 1)`. -/
theorem tagLen_finalTag_le (X : StrTagged Ω) :
    tagLen (finalTag X) ≤ tagLen (tagIter X 1).tag +
      (Fintype.card Ω - 1) * (2 * Fintype.card Ω ^ 2 + 2 * Fintype.card Ω + 1) := by
  set B := 2 * Fintype.card Ω ^ 2 + 2 * Fintype.card Ω + 1
  have hj : ∀ j, tagLen (tagIter X (j + 1)).tag ≤ tagLen (tagIter X 1).tag + j * B := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have := tagLen_tag_tagIter_succ_le X j
      change _ ≤ _ + B at this
      rw [show j + 1 + 1 = j + 2 by ring]
      have hB : (j + 1) * B = j * B + B := by ring
      omega
  rw [finalTag_eq]
  exact (hj _).trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ (stopIdx_le X)) _)

end Process

/-! ### The directed path: the final tag has length `Θ(n³)`

The bound `|t*| = |t₁| + O(n³)` is attained.  On the directed path `0 → 1 → ⋯ → n-1` with
all vertices of the same color and the empty tag (so `m = n - 1` and `|t₁| = 2`), after `j`
rounds two vertices `a ≠ b` have the same color exactly when both lie at distance at least `j`
from both ends (`pathX_c_iff`).  So the process runs for at least `(n-1)/2` rounds
(`two_mul_stopIdx_pathX`), round `j` has at least `j + 1` colors of length `2j + 1`, and the
final tag has length at least `(n-1)³/12` (`pathX_tagLen_finalTag`).  This refutes the printed
cost `O(nm) + |t₁|` of §4.1.1 for the output `X*`, which contains `t*`: see the corrected paper,
entry 131 (§4.1.1: running time of the tagged refinement). -/

section Path

/-- The directed path `0 → 1 → ⋯ → n-1`, all vertices colored by the empty string, empty
tag. -/
def pathX (n : ℕ) : StrTagged (Fin n) := ⟨⟨{p | (p.2 : ℕ) = p.1 + 1}, fun _ => []⟩, []⟩

/-- A tagged digraph on `Fin n` whose digraph is the directed path `0 → 1 → ⋯ → n-1` and whose
coloring is constant (any tag). -/
structure IsPathLike {n : ℕ} (X : StrTagged (Fin n)) : Prop where
  E_eq : X.E = {p | (p.2 : ℕ) = p.1 + 1}
  c_eq : ∀ a b, X.c a = X.c b

theorem isPathLike_pathX (n : ℕ) : IsPathLike (pathX n) := ⟨rfl, fun _ _ => rfl⟩

theorem E_tagIter (X : StrTagged Ω) (j : ℕ) : (tagIter X j).E = X.E := by
  induction j with
  | zero => rfl
  | succ j ih => exact ih

/-- The partition of the path after `j` rounds: `a ~ b` iff `a = b` or both are at distance at
least `j` from both ends. -/
def PathEq (n j a b : ℕ) : Prop := a = b ∨ (j ≤ a ∧ j ≤ b ∧ a + j < n ∧ b + j < n)

theorem ncard_eq_ncard_iff {n : ℕ} (Q Q' R R' : Fin n → Prop)
    (hQ : ∀ w w', Q w → Q w' → w = w') (hQ' : ∀ w w', Q' w → Q' w' → w = w') :
    {w | Q w ∧ R w}.ncard = {w | Q' w ∧ R' w}.ncard ↔
      ((∃ w, Q w ∧ R w) ↔ ∃ w, Q' w ∧ R' w) := by
  classical
  have key : ∀ (Q R : Fin n → Prop), (∀ w w', Q w → Q w' → w = w') →
      {w | Q w ∧ R w}.ncard = if ∃ w, Q w ∧ R w then 1 else 0 := by
    intro Q R hQ
    split_ifs with h
    · obtain ⟨w, hw⟩ := h
      rw [Set.ncard_eq_one]
      exact ⟨w, Set.ext fun w' => ⟨fun h' => hQ _ _ h'.1 hw.1, fun h' => h' ▸ hw⟩⟩
    · rw [Set.ncard_eq_zero]
      exact Set.eq_empty_iff_forall_notMem.2 fun w hw => h ⟨w, hw⟩
  rw [key Q R hQ, key Q' R' hQ']
  split_ifs with h1 h2 h2
  · exact ⟨fun _ => iff_of_true h1 h2, fun _ => rfl⟩
  · exact ⟨fun h => absurd h (by decide), fun h => absurd (h.1 h1) h2⟩
  · exact ⟨fun h => absurd h (by decide), fun h => absurd (h.2 h2) h1⟩
  · exact ⟨fun _ => iff_of_false h1 h2, fun _ => rfl⟩

theorem pathEq_nbr_iff (n j : ℕ) (oa ob : Prop) (ta tb : ℕ) :
    (∀ z : Fin n, (∃ w : Fin n, (oa ∧ (w : ℕ) = ta) ∧ PathEq n j w z) ↔
        (∃ w : Fin n, (ob ∧ (w : ℕ) = tb) ∧ PathEq n j w z)) ↔
      ((oa ∧ ta < n) ↔ (ob ∧ tb < n)) ∧ (oa ∧ ta < n → PathEq n j ta tb) := by
  unfold PathEq
  constructor
  · intro h
    have ha : oa ∧ ta < n → (ob ∧ tb < n) ∧ PathEq n j ta tb := by
      rintro ⟨hoa, hta⟩
      obtain ⟨w, ⟨hob, hw⟩, hwz⟩ := (h ⟨ta, hta⟩).1 ⟨⟨ta, hta⟩, ⟨hoa, rfl⟩, Or.inl rfl⟩
      refine ⟨⟨hob, hw ▸ w.2⟩, ?_⟩
      unfold PathEq; simp only at hwz; omega
    have hb : ob ∧ tb < n → oa ∧ ta < n := by
      rintro ⟨hob, htb⟩
      obtain ⟨w, ⟨hoa, hw⟩, -⟩ := (h ⟨tb, htb⟩).2 ⟨⟨tb, htb⟩, ⟨hob, rfl⟩, Or.inl rfl⟩
      exact ⟨hoa, hw ▸ w.2⟩
    exact ⟨⟨fun h' => (ha h').1, hb⟩, fun h' => (ha h').2⟩
  · rintro ⟨h1, h2⟩ z
    constructor
    · rintro ⟨w, ⟨hoa, hw⟩, hwz⟩
      have hta : ta < n := hw ▸ w.2
      obtain ⟨hob, htb⟩ := h1.1 ⟨hoa, hta⟩
      have := h2 ⟨hoa, hta⟩
      exact ⟨⟨tb, htb⟩, ⟨hob, rfl⟩, by simp only; omega⟩
    · rintro ⟨w, ⟨hob, hw⟩, hwz⟩
      have htb : tb < n := hw ▸ w.2
      obtain ⟨hoa, hta⟩ := h1.2 ⟨hob, htb⟩
      have := h2 ⟨hoa, hta⟩
      exact ⟨⟨ta, hta⟩, ⟨hoa, rfl⟩, by simp only; omega⟩

theorem pathEq_succ_iff (n j a b : ℕ) (ha : a < n) (hb : b < n) :
    PathEq n (j + 1) a b ↔ PathEq n j a b ∧
      (((True ∧ a + 1 < n) ↔ (True ∧ b + 1 < n)) ∧
        (True ∧ a + 1 < n → PathEq n j (a + 1) (b + 1))) ∧
      (((1 ≤ a ∧ a - 1 < n) ↔ (1 ≤ b ∧ b - 1 < n)) ∧
        (1 ≤ a ∧ a - 1 < n → PathEq n j (a - 1) (b - 1))) := by
  simp only [true_and]
  unfold PathEq
  omega

/-- The colors of the path after `j` rounds. -/
theorem pathX_c_iff {n : ℕ} {X : StrTagged (Fin n)} (hX : IsPathLike X) (j : ℕ) (a b : Fin n) :
    (tagIter X j).c a = (tagIter X j).c b ↔ PathEq n j a b := by
  induction j generalizing a b with
  | zero =>
    exact ⟨fun _ => Or.inr ⟨Nat.zero_le _, Nat.zero_le _, by simp, by simp⟩,
      fun _ => hX.c_eq a b⟩
  | succ j ih =>
    set Y := tagIter X j
    change Y.tagColor a = Y.tagColor b ↔ _
    have hE : ∀ x y : Fin n, (x, y) ∈ Y.E ↔ (y : ℕ) = x + 1 := fun x y => by
      rw [E_tagIter, hX.E_eq]; exact Iff.rfl
    have hout : ∀ x z : Fin n, {w | (x, w) ∈ Y.E ∧ Y.c w = Y.c z} =
        {w : Fin n | (True ∧ (w : ℕ) = x + 1) ∧ PathEq n j w z} := fun x z => by
      ext w; simp only [Set.mem_setOf_eq, hE, ih, true_and]
    have hin : ∀ x z : Fin n, {w | (w, x) ∈ Y.E ∧ Y.c w = Y.c z} =
        {w : Fin n | (1 ≤ (x : ℕ) ∧ (w : ℕ) = x - 1) ∧ PathEq n j w z} := fun x z => by
      ext w; simp only [Set.mem_setOf_eq, hE, ih]
      constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by omega, h2⟩
    rw [tagColor_eq_iff, ih, pathEq_succ_iff n j a b a.2 b.2, ← pathEq_nbr_iff,
      ← pathEq_nbr_iff, ← forall_and]
    refine and_congr Iff.rfl (forall_congr' fun z => ?_)
    rw [hout, hout, hin, hin, ncard_eq_ncard_iff _ _ _ _
        (fun w w' h h' => Fin.ext (h.2.trans h'.2.symm))
        (fun w w' h h' => Fin.ext (h.2.trans h'.2.symm)),
      ncard_eq_ncard_iff _ _ _ _ (fun w w' h h' => Fin.ext (by omega))
        (fun w w' h h' => Fin.ext (by omega))]

/-- Two vertices near one end are separated. -/
theorem pathX_c_ne {n : ℕ} {X : StrTagged (Fin n)} (hX : IsPathLike X) (j : ℕ) (a b : Fin n) (hab : a ≠ b) (hj : (a : ℕ) < j) :
    (tagIter X j).c a ≠ (tagIter X j).c b := by
  rw [Ne, pathX_c_iff hX, PathEq, not_or]
  exact ⟨fun h => hab (Fin.ext h), by omega⟩

/-- After `j < n` rounds the path has at least `j + 1` colors. -/
theorem pathX_numColors_ge {n : ℕ} {X : StrTagged (Fin n)} (hX : IsPathLike X) (j : ℕ)
    (hj : j < n) : j + 1 ≤ (tagIter X j).numColors := by
  rw [numColors_eq_card_range]
  let f : Fin (j + 1) → Set.range (tagIter X j).c :=
    fun i => ⟨_, ⟨i.1, by omega⟩, rfl⟩
  have hf : Function.Injective f := by
    intro i i' h
    have h' : (tagIter X j).c ⟨i.1, by omega⟩ = (tagIter X j).c ⟨i'.1, by omega⟩ :=
      congrArg Subtype.val h
    rw [pathX_c_iff hX, PathEq] at h'
    exact Fin.ext (by simp only at h'; omega)
  haveI : Finite (Set.range (tagIter X j).c) := (Set.finite_range _).to_subtype
  simpa using Nat.card_le_card_of_injective f hf

/-- The process on the path runs for at least `(n - 1)/2` rounds: while `2j + 2 ≤ n`, the
vertices `j` and `j + 1` share a color after `j` rounds and are separated in round `j + 1`. -/
theorem two_mul_stopIdx_pathX {n : ℕ} {X : StrTagged (Fin n)} (hX : IsPathLike X) : n ≤ 2 * stopIdx X + 1 := by
  by_contra hlt
  push Not at hlt
  set s := stopIdx X
  have h := (numColors_succ_eq_iff X s).1 (stopIdx_spec X)
  have hmem : ((⟨s, by omega⟩ : Fin n), (⟨s + 1, by omega⟩ : Fin n)) ∈
      kernelSet (tagIter X s).c := by
    change (tagIter X s).c _ = (tagIter X s).c _
    rw [pathX_c_iff hX, PathEq]; simp only; omega
  rw [← h] at hmem
  change (tagIter X (s + 1)).c _ = (tagIter X (s + 1)).c _ at hmem
  rw [pathX_c_iff hX, PathEq] at hmem
  simp only at hmem
  omega

theorem tagLen_tag_tagIter_succ (X : StrTagged Ω) (j : ℕ) :
    tagLen (tagIter X (j + 1)).tag = tagLen (tagIter X j).tag + palLen (tagIter X j).oldColors :=
  tagLen_append_singleton _ _

theorem palLen_ge (p : List (List ℕ)) (L : ℕ) (h : ∀ col ∈ p, L ≤ col.length) :
    p.length * (L + 1) ≤ palLen p := by
  rw [palLen]
  have : (p.map (fun _ => L + 1)).sum ≤ (p.map (fun col => col.length + 1)).sum :=
    List.sum_le_sum (fun col hc => by simpa using h col hc)
  simp only [List.map_const', List.sum_replicate, smul_eq_mul] at this
  omega

/-- The number of letters of a tag: the total length of its colors (separators not counted). -/
def tagLetters (t : List (List (List ℕ))) : ℕ := (t.map (fun p => (p.map List.length).sum)).sum

theorem tagLetters_le_tagLen (t : List (List (List ℕ))) : tagLetters t ≤ tagLen t := by
  unfold tagLetters tagLen
  apply List.sum_le_sum
  intro p _
  rw [palLen]
  have : (p.map List.length).sum ≤ (p.map (fun col => col.length + 1)).sum :=
    List.sum_le_sum (fun col _ => Nat.le_succ _)
  omega

theorem tagLetters_tag_tagIter_succ (X : StrTagged Ω) (j : ℕ) :
    tagLetters (tagIter X (j + 1)).tag =
      tagLetters (tagIter X j).tag + ((tagIter X j).oldColors.map List.length).sum := by
  change tagLetters ((tagIter X j).tag ++ [(tagIter X j).oldColors]) = _
  simp [tagLetters]

/-- On the path, round `k + 1 < n` appends at least `k + 2` colors of length `2k + 3`. -/
theorem pathX_letters_ge {n : ℕ} {X : StrTagged (Fin n)} (hX : IsPathLike X) (k : ℕ)
    (hk : k + 1 < n) :
    2 * (k + 1) * (k + 2) ≤ ((tagIter X (k + 1)).oldColors.map List.length).sum := by
  have hlen : ∀ col ∈ (tagIter X (k + 1)).oldColors, 2 * (k + 1) + 1 ≤ col.length := by
    intro col hc
    obtain ⟨v, rfl⟩ := ((tagIter X (k + 1)).mem_oldColors col).1 hc
    change _ ≤ ((tagIter X k).tagColor v).length
    rw [length_tagColor]
    have := pathX_numColors_ge hX k (by omega)
    omega
  have h1 : ((tagIter X (k + 1)).oldColors.map (fun _ => 2 * (k + 1) + 1)).sum ≤
      ((tagIter X (k + 1)).oldColors.map List.length).sum :=
    List.sum_le_sum (fun col hc => hlen col hc)
  simp only [List.map_const', List.sum_replicate, smul_eq_mul] at h1
  have h2 : k + 2 ≤ (tagIter X (k + 1)).oldColors.length :=
    pathX_numColors_ge hX (k + 1) hk
  have h3 : (k + 2) * (2 * (k + 1) + 1) ≤
      (tagIter X (k + 1)).oldColors.length * (2 * (k + 1) + 1) :=
    Nat.mul_le_mul h2 le_rfl
  nlinarith

/-- **The final tag of the path has `Θ(n³)` letters**: `(n-1)³ ≤ 12 · #letters(t*)`. -/
theorem pathX_tagLetters_finalTag {n : ℕ} {X : StrTagged (Fin n)} (hX : IsPathLike X) :
    (n - 1) ^ 3 ≤ 12 * tagLetters (finalTag X) := by
  set s := stopIdx X
  have hs : s ≤ n - 1 := by simpa using stopIdx_le X
  have hk : ∀ k ≤ s, 2 * k ^ 3 ≤ 3 * tagLetters (tagIter X (k + 1)).tag := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have h1 := ih (by omega)
      have h2 := pathX_letters_ge hX k (by omega)
      rw [tagLetters_tag_tagIter_succ X (k + 1)]
      nlinarith
  have h := hk s le_rfl
  rw [← finalTag_eq] at h
  have h2 := two_mul_stopIdx_pathX hX
  have h3 : (n - 1) ^ 3 ≤ (2 * s) ^ 3 := Nat.pow_le_pow_left (by omega) 3
  nlinarith

/-- **The final tag of the path has length `Θ(n³)`**: `(n-1)³ ≤ 12 |t*|`, while `m = n - 1`
and `|t₁| = |t₀| + |c(0)| + 2` (`tagLen_tag_tagIter_one_pathLike`). -/
theorem pathX_tagLen_finalTag {n : ℕ} {X : StrTagged (Fin n)} (hX : IsPathLike X) :
    (n - 1) ^ 3 ≤ 12 * tagLen (finalTag X) :=
  (pathX_tagLetters_finalTag hX).trans (Nat.mul_le_mul_left _ (tagLetters_le_tagLen _))

/-- A uniformly colored input has a one-color palette. -/
theorem oldColors_pathLike {n : ℕ} {X : StrTagged (Fin n)} (hX : IsPathLike X) (hn : 0 < n) :
    X.oldColors = [X.c ⟨0, hn⟩] := by
  have hmem : ∀ col, col ∈ X.oldColors ↔ col = X.c ⟨0, hn⟩ := fun col => by
    rw [mem_oldColors]
    exact ⟨fun ⟨v, h⟩ => h.symm.trans (hX.c_eq v _), fun h => ⟨⟨0, hn⟩, h.symm⟩⟩
  have hnd := X.oldColors_nodup
  rcases hl : X.oldColors with _ | ⟨c, l⟩
  · have := (hmem _).2 rfl; rw [hl] at this; simp at this
  · have hc : c = X.c ⟨0, hn⟩ := (hmem c).1 (by simp [hl])
    rcases l with _ | ⟨d, l⟩
    · rw [hc]
    · have hd : d = X.c ⟨0, hn⟩ := (hmem d).1 (by simp [hl])
      rw [hl, hc, hd] at hnd; simp at hnd

theorem tagLen_tag_tagIter_one_pathLike {n : ℕ} {X : StrTagged (Fin n)} (hX : IsPathLike X)
    (hn : 0 < n) : tagLen (tagIter X 1).tag = tagLen X.tag + ((X.c ⟨0, hn⟩).length + 2) := by
  rw [tagLen_tag_tagIter_one, oldColors_pathLike hX hn]
  simp [palLen]

/-- For the path `pathX n`: `|t₁| = 2`. -/
theorem pathX_tagLen_tag_tagIter_one (n : ℕ) (hn : 0 < n) :
    tagLen (tagIter (pathX n) 1).tag = 2 := by
  rw [tagLen_tag_tagIter_one_pathLike (isPathLike_pathX n) hn]; rfl

end Path

end TaggedDigraph

end Babai
