/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 4.1.1 (Complexity of naive refinement): the untagged naive refinement process with its
colors written as strings over `Σ`.
-/
import Workspace.Refinement.TaggedProcess

/-!
# §4.1.1 The untagged process, colors as strings

Lines 2852–2860: *"Let `Σ` be a finite alphabet that includes `[n]` and the three separator
symbols: comma, opening and closing parentheses.  If each color in `X` is described by a
string of length `k` over `Σ` then colors in `X'` are described by strings of length
`k + O(n)`. … The overall total cost is `O(nk + n²m)`."*

`Refinement/Naive.lean` keeps the colors of the untagged process abstract
(`naiveStep x = (c x, i ↦ d⁺ᵢ(x), i ↦ d⁻ᵢ(x))`).  To speak of the length of a color, this file
writes the refined color as the paper's string

  `c'(x) = ( c(x) , d⁺_{i₁}(x) , d⁻_{i₁}(x) , … , d⁺_{i_N}(x) , d⁻_{i_N}(x) )`,

where `i₁ < ⋯ < i_N` are the colors that occur, in lexicographic order (`palette`).  Letters
are natural numbers: `(` is `0`, `,` is `1`, `)` is `2`, and the number `d` is the letter
`d + 3` (`lOpen`, `lComma`, `lClose`, `lNum`).  So `Σ = {0, …, n + 2}` for the refined colors;
the input colors may use any letters.

* `strStep`, `strIter`: one round and the process `X₀ = X`, `X_{j+1} = X_j'`.
* The strings describe the colors of `Naive.lean`: a string color and the abstract color of
  `naiveStep` define the same partition (`kernelSet_strStep`), in every round
  (`kernelSet_strIter`).
* `strStop`: "We stop when `X_k` is stable, i.e., when `N(c_{k+1}) = N(c_k)`"; `strStable` is
  `X* = X_k`, and it is stable (`strStable_isStable`).

No axiom, no `sorry`.
-/

namespace Babai

namespace ColoredDigraph

variable {Ω : Type*} [Fintype Ω]

/-- The letter `(`. -/
def lOpen : ℕ := 0
/-- The letter `,`. -/
def lComma : ℕ := 1
/-- The letter `)`. -/
def lClose : ℕ := 2
/-- The number `d ∈ [n]` as a letter. -/
def lNum (d : ℕ) : ℕ := d + 3

/-- The colors that occur, in increasing order (the ordered set `C` of §4.1); for string colors
the order is lexicographic. -/
noncomputable def palette {C : Type*} [LinearOrder C] (X : ColoredDigraph Ω C) : List C :=
  (Finset.univ.image X.c).sort (· ≤ ·)

theorem mem_palette {C : Type*} [LinearOrder C] (X : ColoredDigraph Ω C) (s : C) :
    s ∈ X.palette ↔ ∃ v, X.c v = s := by
  simp [palette]

section Step

variable (X : ColoredDigraph Ω (List ℕ))

/-- §4.1, written as a string (§4.1.1): "`c'(x) = (c(x), d⁺ᵢ(x), d⁻ᵢ(x) | i ∈ C)`, where the
terms in the string `c'(x)` are arranged in the order defined by the ordering of `C`." -/
noncomputable def strStep (x : Ω) : List ℕ :=
  lOpen :: (X.c x ++ (X.palette.flatMap (fun s =>
    [lComma, lNum (X.outDegCol s x), lComma, lNum (X.inDegCol s x)]) ++ [lClose]))

theorem length_flatMap_four (l : List (List ℕ)) (f : List ℕ → List ℕ)
    (hf : ∀ s, (f s).length = 4) : (l.flatMap f).length = 4 * l.length := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, ih, hf]; ring

theorem length_strStep (x : Ω) :
    (X.strStep x).length = (X.c x).length + 4 * X.palette.length + 2 := by
  simp only [strStep, List.length_cons, List.length_append]
  rw [length_flatMap_four _ _ (fun s => rfl)]
  simp; ring

theorem outDegCol_eq_zero {s : List ℕ} (hs : s ∉ X.palette) (x : Ω) : X.outDegCol s x = 0 := by
  unfold outDegCol
  have : {y : Ω | (x, y) ∈ X.E ∧ X.c y = s} = ∅ := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro _ h
    exact hs ((X.mem_palette s).2 ⟨y, h⟩)
  rw [this, Set.ncard_empty]

theorem inDegCol_eq_zero {s : List ℕ} (hs : s ∉ X.palette) (x : Ω) : X.inDegCol s x = 0 := by
  unfold inDegCol
  have : {y : Ω | (y, x) ∈ X.E ∧ X.c y = s} = ∅ := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro _ h
    exact hs ((X.mem_palette s).2 ⟨y, h⟩)
  rw [this, Set.ncard_empty]

theorem flatMap_four_eq_iff (l : List (List ℕ)) (f g : List ℕ → ℕ × ℕ) :
    l.flatMap (fun s => [lComma, lNum (f s).1, lComma, lNum (f s).2]) =
      l.flatMap (fun s => [lComma, lNum (g s).1, lComma, lNum (g s).2]) ↔ ∀ s ∈ l, f s = g s := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.flatMap_cons, List.mem_cons, forall_eq_or_imp]
    rw [← ih]
    constructor
    · intro h
      obtain ⟨h1, h2⟩ := List.append_inj h rfl
      simp only [lNum, List.cons.injEq, add_left_inj, and_true, true_and] at h1
      exact ⟨Prod.ext h1.1 h1.2, h2⟩
    · rintro ⟨h1, h2⟩
      rw [h1, h2]

/-- A string color and the abstract color of `naiveStep` agree on equality. -/
theorem strStep_eq_iff (x y : Ω) : X.strStep x = X.strStep y ↔ X.naiveStep x = X.naiveStep y := by
  rw [naiveStep_eq_iff]
  have hlen : (X.palette.flatMap (fun s =>
      [lComma, lNum (X.outDegCol s x), lComma, lNum (X.inDegCol s x)])).length =
      (X.palette.flatMap (fun s =>
        [lComma, lNum (X.outDegCol s y), lComma, lNum (X.inDegCol s y)])).length := by
    rw [length_flatMap_four _ _ (fun s => rfl), length_flatMap_four _ _ (fun s => rfl)]
  have key := flatMap_four_eq_iff X.palette (fun s => (X.outDegCol s x, X.inDegCol s x))
    (fun s => (X.outDegCol s y, X.inDegCol s y))
  simp only at key
  constructor
  · intro h
    simp only [strStep, List.cons.injEq, true_and] at h
    have hl : (X.c x).length = (X.c y).length := by
      have := congrArg List.length h
      simp only [List.length_append] at this
      omega
    obtain ⟨h1, h2⟩ := List.append_inj h hl
    obtain ⟨h3, -⟩ := List.append_inj h2 hlen
    have h4 := key.1 h3
    refine ⟨h1, fun s => ?_, fun s => ?_⟩
    · by_cases hs : s ∈ X.palette
      · exact congrArg Prod.fst (h4 s hs)
      · rw [X.outDegCol_eq_zero hs, X.outDegCol_eq_zero hs]
    · by_cases hs : s ∈ X.palette
      · exact congrArg Prod.snd (h4 s hs)
      · rw [X.inDegCol_eq_zero hs, X.inDegCol_eq_zero hs]
  · rintro ⟨h1, h2, h3⟩
    simp only [strStep, h1, h2, h3]

theorem kernelSet_strStep : kernelSet X.strStep = kernelSet X.naiveStep := by
  ext ⟨x, y⟩
  exact X.strStep_eq_iff x y

end Step

/-! ## The process -/

/-- §4.1: "Let `X₀ = X` and `X_{j+1} = X_j'`", with the colors written as strings. -/
noncomputable def strIter (X : ColoredDigraph Ω (List ℕ)) : ℕ → Ω → List ℕ
  | 0 => X.c
  | j + 1 => (X.recolor (X.strIter j)).strStep

@[simp] theorem strIter_zero (X : ColoredDigraph Ω (List ℕ)) : X.strIter 0 = X.c := rfl

theorem strIter_succ (X : ColoredDigraph Ω (List ℕ)) (j : ℕ) :
    X.strIter (j + 1) = (X.recolor (X.strIter j)).strStep := rfl

/-- The string process has the partitions of the naive process of `Naive.lean`. -/
theorem kernelSet_strIter (X : ColoredDigraph Ω (List ℕ)) :
    ∀ j, kernelSet (X.strIter j) = kernelSet (X.naiveIter j)
  | 0 => rfl
  | j + 1 => by
    rw [strIter_succ, kernelSet_strStep, naiveIter_succ]
    exact kernelSet_naiveStep_congr X (kernelSet_strIter X j)

/-- `N(c_j)`, the number of colors of round `j`. -/
noncomputable def strNum (X : ColoredDigraph Ω (List ℕ)) (j : ℕ) : ℕ :=
  Nat.card (Set.range (X.strIter j))

theorem kernelSet_strIter_succ_subset (X : ColoredDigraph Ω (List ℕ)) (j : ℕ) :
    kernelSet (X.strIter (j + 1)) ⊆ kernelSet (X.strIter j) := by
  rw [kernelSet_strIter, kernelSet_strIter]
  intro p hp
  exact X.naiveIter_isRefinement j p.1 p.2 hp

theorem kernelSet_strIter_step (X : ColoredDigraph Ω (List ℕ)) (j : ℕ)
    (h : kernelSet (X.strIter (j + 1)) = kernelSet (X.strIter j)) :
    kernelSet (X.strIter (j + 2)) = kernelSet (X.strIter (j + 1)) := by
  rw [strIter_succ X (j + 1), kernelSet_strStep, strIter_succ X j, kernelSet_strStep]
  exact kernelSet_naiveStep_congr X h

/-- `N(c_{j+1}) = N(c_j)` exactly when the round did not change the partition. -/
theorem strNum_succ_eq_iff (X : ColoredDigraph Ω (List ℕ)) (j : ℕ) :
    X.strNum (j + 1) = X.strNum j ↔ kernelSet (X.strIter (j + 1)) = kernelSet (X.strIter j) := by
  unfold strNum
  constructor
  · intro h
    by_contra hne
    have := card_range_lt_of_kernelSet_ssubset (X.strIter j) (X.strIter (j + 1))
      (X.kernelSet_strIter_succ_subset j) hne
    omega
  · intro h
    exact le_antisymm (TaggedDigraph.card_range_le_of_kernelSet_subset _ _ h.symm.le)
      (TaggedDigraph.card_range_le_of_kernelSet_subset _ _ h.le)

theorem exists_strStop (X : ColoredDigraph Ω (List ℕ)) : ∃ j, X.strNum (j + 1) = X.strNum j :=
  ⟨Fintype.card Ω - 1, (X.strNum_succ_eq_iff _).2
    (kernelSet_eq_of_card_sub_one_le (fun j => X.strIter j) X.kernelSet_strIter_succ_subset
      X.kernelSet_strIter_step le_rfl)⟩

open Classical in
/-- §4.1: "We stop when `X_k` is stable, i.e., when `N(c_{k+1}) = N(c_k)`": the first such
`k`. -/
noncomputable def strStop (X : ColoredDigraph Ω (List ℕ)) : ℕ := Nat.find X.exists_strStop

theorem strStop_spec (X : ColoredDigraph Ω (List ℕ)) :
    X.strNum (X.strStop + 1) = X.strNum X.strStop := by
  classical
  exact Nat.find_spec X.exists_strStop

theorem strStop_min (X : ColoredDigraph Ω (List ℕ)) {j : ℕ} (hj : j < X.strStop) :
    X.strNum (j + 1) ≠ X.strNum j := by
  classical
  exact Nat.find_min X.exists_strStop hj

/-- The first round that does not change the number of colors is `strStop`. -/
theorem strStop_eq_of (X : ColoredDigraph Ω (List ℕ)) {k : ℕ}
    (hk : X.strNum (k + 1) = X.strNum k) (hlt : ∀ i < k, X.strNum (i + 1) ≠ X.strNum i) :
    X.strStop = k := by
  classical
  unfold strStop
  rw [Nat.find_eq_iff]
  exact ⟨hk, fun i hi => hlt i hi⟩

/-- §4.1: "We call the colored digraph `X* = X_k` the stable refinement of `X`", with its
colors written as strings. -/
noncomputable def strStable (X : ColoredDigraph Ω (List ℕ)) : Ω → List ℕ :=
  X.strIter X.strStop

/-- `X*` is stable with respect to naive vertex-refinement. -/
theorem strStable_isStable (X : ColoredDigraph Ω (List ℕ)) :
    (X.recolor X.strStable).IsStable := by
  rw [isStable_iff_kernelSet, recolor_c, ← kernelSet_strStep]
  exact (X.strNum_succ_eq_iff _).1 X.strStop_spec

/-- The partition of `X*` is that of the naive process after `strStop` rounds. -/
theorem kernelSet_strStable (X : ColoredDigraph Ω (List ℕ)) :
    kernelSet X.strStable = kernelSet (X.naiveIter X.strStop) :=
  X.kernelSet_strIter _

end ColoredDigraph

end Babai
