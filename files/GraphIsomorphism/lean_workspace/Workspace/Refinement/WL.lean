/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Sections 4.2 and 4.3: Weisfeiler–Leman canonical refinement.
-/
import Workspace.Refinement.Naive
import Workspace.Coherent.Configurations

/-!
# §4.2–§4.3 Weisfeiler–Leman refinement

§4.3: *"The classical Weisfeiler–Leman (WL) refinement takes as input a binary
configuration and refines it to a coherent configuration (see Sec. 3.2.1) as follows.  The
process proceeds in rounds.  Let `X` be the input to a round of refinement.  For
`(x,y) ∈ Ω × Ω`, we encode in the new color `c'(x,y)` the following information: the old
color `c(x,y)`, and for all `j,k ≤ r`, the number
`|{z ∈ Ω | c(x,z) = j and c(z,y) = k}|`.  These data form a list, naturally ordered.  To
each list we assign a new color; these colors are sorted lexicographically.  This gives a
refined coloring that defines a new configuration `X'`.  We stop when we reach a stable
configuration (`X = X'`, i. e., no refinement occurs, i. e., no `Rᵢ` is split)."*

§4.2 carries the heading "Weisfeiler-Leman canonical refinement" and no text in version
2.5; the canonicity statement of the process is the displayed equation at the end of §4.3
(Eq. (26)), recorded here as `iso_stable`.  See the corrected paper, §4.2.

## How the process is recorded

As in §4.1 (`Workspace/Refinement/Naive.lean`), a round is a map on *colorings*
`c : Ω → Ω → C` into a larger color set; "assigning a new color to each list and sorting
them lexicographically" is the passage to the quotient by the kernel, which is irrelevant
for everything the paper proves about the process, and keeping the lists themselves makes
the process manifestly canonical.  Running the round `|(Ω × Ω) × (Ω × Ω)|` times gives a
number of rounds that depends only on `Ω`, hence a canonical output that is stable
(`stable_isStable`); this is the paper's `X*`.

## Numbering map

| Paper | Lean |
|---|---|
| §4.3, the axioms of Def. 3.1.2 as a property of a coloring | `Babai.WL.IsConfigColoring` |
| §4.3, axiom (iii) of Def. 3.1.11 for a coloring | `Babai.WL.IsCoherentColoring` |
| §4.3, `c'` | `Babai.WL.step` |
| §4.3, "`X'` is a configuration" | `Babai.WL.isConfigColoring_step` |
| §4.3, "we stop when we reach a stable configuration" | `Babai.WL.IsStable`, `.stable` |
| Observation 4.3.1 | `Babai.WL.isStable_iff_isCoherentColoring`, `Babai.PartitionStructure.isStable_color_iff_isCoherent` |
| §4.3, "refines it to a coherent configuration" | `Babai.WL.isCoherentColoring_stable` |
| §4.3, Eq. (26) | `Babai.WL.iso_stable` |
-/

namespace Babai

namespace WL

universe u

variable {Ω Ω' : Type*} {C C' D D' : Type*}

/-! ### Configurations and coherence as properties of a coloring -/

/-- Definition 3.1.2 read as a property of a coloring `c : Ω → Ω → C` by an arbitrary
color set: (i) `c(x,y) = c(z,z) ⟹ x = y`; (ii) `c(u,v) = c(x,y) ⟹ c(v,u) = c(y,x)`.

The rounds of WL refinement produce colorings by ever larger color sets, for which
Def. 3.1.1's requirement that every color be used is not maintained (colors that are not
used are dropped only at the end); this is the form of Def. 3.1.2 used throughout §4.3. -/
def IsConfigColoring (c : Ω → Ω → C) : Prop :=
  (∀ x y z : Ω, c x y = c z z → x = y) ∧
    (∀ u v x y : Ω, c u v = c x y → c v u = c y x)

/-- Definition 3.1.11, axiom (iii), read as a property of a coloring. -/
def IsCoherentColoring (c : Ω → Ω → C) : Prop :=
  IsConfigColoring c ∧ ∃ p : C → C → C → ℕ, ∀ (i j k : C) (x y : Ω), c x y = k →
    {z : Ω | c x z = i ∧ c z y = j}.ncard = p i j k

theorem _root_.Babai.PartitionStructure.isConfigColoring_color {Ω : Type*}
    (X : PartitionStructure Ω) : X.IsConfiguration ↔ IsConfigColoring X.color :=
  ⟨fun h => ⟨h.diag, h.converse⟩, fun h => ⟨h.1, h.2⟩⟩

/-! ### §4.3 The refinement round -/

/-- §4.3.  One round of WL refinement: *"we encode in the new color `c'(x,y)` … the old
color `c(x,y)`, and for all `j,k ≤ r`, the number `|{z ∈ Ω | c(x,z) = j and c(z,y) = k}|`."*
-/
noncomputable def step (c : Ω → Ω → C) : Ω → Ω → C × (C × C → ℕ) :=
  fun x y => (c x y, fun jk => {z : Ω | c x z = jk.1 ∧ c z y = jk.2}.ncard)

@[simp] theorem step_fst (c : Ω → Ω → C) (x y : Ω) : (step c x y).1 = c x y := rfl

theorem step_eq_iff (c : Ω → Ω → C) (x y x' y' : Ω) :
    step c x y = step c x' y' ↔ c x y = c x' y' ∧
      ∀ j k : C, {z : Ω | c x z = j ∧ c z y = k}.ncard
        = {z : Ω | c x' z = j ∧ c z y' = k}.ncard := by
  constructor
  · intro h
    refine ⟨congrArg Prod.fst h, fun j k => ?_⟩
    exact congrFun (congrArg (fun p => p.2) h) (j, k)
  · rintro ⟨h1, h2⟩
    refine Prod.ext h1 ?_
    funext jk
    exact h2 jk.1 jk.2

/-- §4.3.  The refined coloring refines the old one ("no `Rᵢ` is split" refers to the
partition of the previous round). -/
theorem step_isRefinement (c : Ω → Ω → C) : IsRefinement (fun p : Ω × Ω => step c p.1 p.2)
    (fun p : Ω × Ω => c p.1 p.2) := fun _ _ h => congrArg Prod.fst h

/-- §4.3.  The counting data of `(v,u)` is determined by that of `(u,v)`: in a
configuration the color of a pair determines the color of the reversed pair
(Def. 3.1.2(ii)), so `{z | c(v,z) = j and c(z,u) = k}` is the set counted by the datum of
`(u,v)` at the pair of reversed colors.  This is the step behind axiom (ii) for the
refined coloring. -/
theorem count_conv {c : Ω → Ω → C} (h : IsConfigColoring c) {u v x y : Ω}
    (h2 : ∀ j k : C, {z : Ω | c u z = j ∧ c z v = k}.ncard
      = {z : Ω | c x z = j ∧ c z y = k}.ncard)
    (j k : C) (w : Ω) (hw1 : c v w = j) (hw2 : c w u = k) :
    {z : Ω | c v z = j ∧ c z u = k}.ncard = {z : Ω | c y z = j ∧ c z x = k}.ncard := by
  obtain ⟨-, hconv⟩ := h
  subst hw1
  subst hw2
  have hS : {z : Ω | c v z = c v w ∧ c z u = c w u}
      = {z : Ω | c u z = c u w ∧ c z v = c w v} := by
    ext z
    exact ⟨fun hz => ⟨hconv z u w u hz.2, hconv v z v w hz.1⟩,
      fun hz => ⟨hconv z v w v hz.2, hconv u z u w hz.1⟩⟩
  have hS' : {z : Ω | c y z = c v w ∧ c z x = c w u}
      = {z : Ω | c x z = c u w ∧ c z y = c w v} := by
    ext z
    exact ⟨fun hz => ⟨hconv z x w u hz.2, hconv y z v w hz.1⟩,
      fun hz => ⟨hconv z y w v hz.2, hconv x z u w hz.1⟩⟩
  rw [hS, hS']
  exact h2 (c u w) (c w v)

/-- §4.3.  *"This gives a refined coloring that defines a new configuration `X'`."*  The
two axioms of Def. 3.1.2 are inherited by the refined coloring. -/
theorem isConfigColoring_step {c : Ω → Ω → C} (h : IsConfigColoring c) :
    IsConfigColoring (step c) := by
  classical
  refine ⟨fun x y z hxy => h.1 x y z (congrArg Prod.fst hxy), ?_⟩
  intro u v x y huv
  obtain ⟨h1, h2⟩ := (step_eq_iff c u v x y).1 huv
  refine (step_eq_iff c v u y x).2 ⟨h.2 u v x y h1, fun j k => ?_⟩
  by_cases hw : ∃ w : Ω, c v w = j ∧ c w u = k
  · obtain ⟨w, hw1, hw2⟩ := hw
    exact count_conv h h2 j k w hw1 hw2
  · by_cases hw' : ∃ w : Ω, c y w = j ∧ c w x = k
    · obtain ⟨w, hw1, hw2⟩ := hw'
      exact (count_conv (u := x) (v := y) (x := u) (y := v) h
        (fun j k => (h2 j k).symm) j k w hw1 hw2).symm
    · push_neg at hw hw'
      have e1 : {z : Ω | c v z = j ∧ c z u = k} = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        exact fun z hz => hw z hz.1 hz.2
      have e2 : {z : Ω | c y z = j ∧ c z x = k} = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        exact fun z hz => hw' z hz.1 hz.2
      rw [e1, e2]

/-! ### Observation 4.3.1 -/

/-- §4.3.  *"We stop when we reach a stable configuration (`X = X'`, i. e., no refinement
occurs, i. e., no `Rᵢ` is split)":* the refined coloring does not separate two pairs of the
same color. -/
def IsStable (c : Ω → Ω → C) : Prop :=
  ∀ x y x' y' : Ω, c x y = c x' y' → step c x y = step c x' y'

/-- Observation 4.3.1.  "The stable configurations under WL refinement are precisely the
coherent configurations." -/
theorem isStable_iff_isCoherentColoring {c : Ω → Ω → C} (h : IsConfigColoring c) :
    IsStable c ↔ IsCoherentColoring c := by
  classical
  constructor
  · intro hst
    refine ⟨h, ⟨fun i j k => ?_, ?_⟩⟩
    · -- the common value of the counts on the color class of `k`, or `0` if `k` is unused
      exact if hk : ∃ p : Ω × Ω, c p.1 p.2 = k then
        {z : Ω | c hk.choose.1 z = i ∧ c z hk.choose.2 = j}.ncard else 0
    · intro i j k x y hxy
      have hk : ∃ p : Ω × Ω, c p.1 p.2 = k := ⟨(x, y), hxy⟩
      have hkc : c hk.choose.1 hk.choose.2 = k := hk.choose_spec
      have := ((step_eq_iff c x y hk.choose.1 hk.choose.2).1
        (hst x y hk.choose.1 hk.choose.2 (hxy.trans hkc.symm))).2 i j
      rw [this]
      simp only [hk, dif_pos]
  · rintro ⟨-, p, hp⟩
    intro x y x' y' hxy
    refine (step_eq_iff c x y x' y').2 ⟨hxy, fun j k => ?_⟩
    rw [hp j k (c x y) x y rfl, hp j k (c x y) x' y' hxy.symm]

/-- Observation 4.3.1 for a partition structure: a configuration is stable under WL
refinement exactly if it is coherent. -/
theorem _root_.Babai.PartitionStructure.isStable_color_iff_isCoherent {Ω : Type*}
    (X : PartitionStructure Ω) (h : X.IsConfiguration) :
    IsStable X.color ↔ X.IsCoherent := by
  classical
  rw [isStable_iff_isCoherentColoring (X.isConfigColoring_color.1 h)]
  constructor
  · rintro ⟨-, p, hp⟩
    refine ⟨h, ⟨fun i j k => p i j k, fun i j k x y hxy => hp i j k x y hxy⟩⟩
  · rintro ⟨-, p, hp⟩
    exact ⟨X.isConfigColoring_color.1 h, ⟨fun i j k => p i j k, fun i j k x y hxy =>
      hp i j k x y hxy⟩⟩

/-! ### §4.3 The refinement process -/

/-- Kernel-only dependence of the counting data: if two colorings of `Ω × Ω` define the
same partition, the counting data of the round separates the same pairs.  (Compare
`Babai.ColoredDigraph.colorCount_congr` for the unary process of §4.1.) -/
theorem count_congr_mp {Ω : Type*} {D D' : Type*} {d : Ω → Ω → D} {e : Ω → Ω → D'}
    (hk : ∀ a b a' b' : Ω, d a b = d a' b' ↔ e a b = e a' b') {x y x' y' : Ω}
    (h : ∀ j k : D, {z : Ω | d x z = j ∧ d z y = k}.ncard
      = {z : Ω | d x' z = j ∧ d z y' = k}.ncard) (j k : D') :
    {z : Ω | e x z = j ∧ e z y = k}.ncard = {z : Ω | e x' z = j ∧ e z y' = k}.ncard := by
  classical
  by_cases h1 : ∃ z₀ : Ω, e x z₀ = j ∧ e z₀ y = k
  · obtain ⟨z₀, hz1, hz2⟩ := h1
    have hA : {z : Ω | e x z = j ∧ e z y = k} = {z : Ω | d x z = d x z₀ ∧ d z y = d z₀ y} := by
      ext z
      exact ⟨fun hz => ⟨(hk x z x z₀).2 (hz.1.trans hz1.symm),
          (hk z y z₀ y).2 (hz.2.trans hz2.symm)⟩,
        fun hz => ⟨((hk x z x z₀).1 hz.1).trans hz1, ((hk z y z₀ y).1 hz.2).trans hz2⟩⟩
    have hB : {z : Ω | e x' z = j ∧ e z y' = k}
        = {z : Ω | d x' z = d x z₀ ∧ d z y' = d z₀ y} := by
      ext z
      exact ⟨fun hz => ⟨(hk x' z x z₀).2 (hz.1.trans hz1.symm),
          (hk z y' z₀ y).2 (hz.2.trans hz2.symm)⟩,
        fun hz => ⟨((hk x' z x z₀).1 hz.1).trans hz1, ((hk z y' z₀ y).1 hz.2).trans hz2⟩⟩
    rw [hA, hB]
    exact h (d x z₀) (d z₀ y)
  · by_cases h2 : ∃ z₀ : Ω, e x' z₀ = j ∧ e z₀ y' = k
    · obtain ⟨z₀, hz1, hz2⟩ := h2
      have hA : {z : Ω | e x z = j ∧ e z y = k}
          = {z : Ω | d x z = d x' z₀ ∧ d z y = d z₀ y'} := by
        ext z
        exact ⟨fun hz => ⟨(hk x z x' z₀).2 (hz.1.trans hz1.symm),
            (hk z y z₀ y').2 (hz.2.trans hz2.symm)⟩,
          fun hz => ⟨((hk x z x' z₀).1 hz.1).trans hz1, ((hk z y z₀ y').1 hz.2).trans hz2⟩⟩
      have hB : {z : Ω | e x' z = j ∧ e z y' = k}
          = {z : Ω | d x' z = d x' z₀ ∧ d z y' = d z₀ y'} := by
        ext z
        exact ⟨fun hz => ⟨(hk x' z x' z₀).2 (hz.1.trans hz1.symm),
            (hk z y' z₀ y').2 (hz.2.trans hz2.symm)⟩,
          fun hz => ⟨((hk x' z x' z₀).1 hz.1).trans hz1, ((hk z y' z₀ y').1 hz.2).trans hz2⟩⟩
      rw [hA, hB]
      exact h (d x' z₀) (d z₀ y')
    · push_neg at h1 h2
      have e1 : {z : Ω | e x z = j ∧ e z y = k} = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        exact fun z hz => h1 z hz.1 hz.2
      have e2 : {z : Ω | e x' z = j ∧ e z y' = k} = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        exact fun z hz => h2 z hz.1 hz.2
      rw [e1, e2]

/-- A round of WL refinement depends on the input coloring only through its partition. -/
theorem step_congr {Ω : Type*} {D D' : Type*} {d : Ω → Ω → D} {e : Ω → Ω → D'}
    (hk : ∀ a b a' b' : Ω, d a b = d a' b' ↔ e a b = e a' b') (a b a' b' : Ω) :
    step d a b = step d a' b' ↔ step e a b = step e a' b' := by
  rw [step_eq_iff, step_eq_iff]
  exact and_congr (hk a b a' b')
    ⟨fun h => fun j k => count_congr_mp hk h j k,
      fun h => fun j k => count_congr_mp (fun p q p' q' => (hk p q p' q').symm) h j k⟩

/-- §4.3.  The color set after `n` rounds of WL refinement. -/
def colorType (C : Type u) : ℕ → Type u
  | 0 => C
  | n + 1 => colorType C n × (colorType C n × colorType C n → ℕ)

/-- §4.3.  The WL refinement process: `c₀ = c` and `c_{n+1} = c'_n`. -/
noncomputable def iter {C : Type u} (c : Ω → Ω → C) : ∀ n : ℕ, Ω → Ω → colorType C n
  | 0 => c
  | n + 1 => step (iter c n)

@[simp] theorem iter_zero {C : Type u} (c : Ω → Ω → C) : iter c 0 = c := rfl

@[simp] theorem iter_succ {C : Type u} (c : Ω → Ω → C) (n : ℕ) :
    iter c (n + 1) = step (iter c n) := rfl

theorem iter_isRefinement_le {C : Type u} (c : Ω → Ω → C) {m n : ℕ} (h : m ≤ n)
    (x y x' y' : Ω) (hxy : iter c n x y = iter c n x' y') :
    iter c m x y = iter c m x' y' := by
  induction n with
  | zero =>
    obtain rfl : m = 0 := Nat.le_zero.1 h
    exact hxy
  | succ p ih =>
    rcases Nat.lt_or_ge m (p + 1) with hlt | hge
    · exact ih (by omega) (congrArg Prod.fst hxy)
    · obtain rfl : m = p + 1 := le_antisymm h hge
      exact hxy

theorem isConfigColoring_iter {C : Type u} {c : Ω → Ω → C} (h : IsConfigColoring c) :
    ∀ n : ℕ, IsConfigColoring (iter c n)
  | 0 => h
  | n + 1 => isConfigColoring_step (isConfigColoring_iter h n)

/-- §4.3.  *"We stop when we reach a stable configuration"*: the paper's `X*`.  The number
of rounds is `|(Ω × Ω) × (Ω × Ω)|`, a bound valid for every input on the vertex set `Ω`
(the process can only refine, and a refinement that does not change the partition changes
nothing afterwards), so it does not depend on the input and the process stays canonical.
-/
noncomputable def stable {C : Type u} [Fintype Ω] (c : Ω → Ω → C) :
    Ω → Ω → colorType C (Fintype.card ((Ω × Ω) × (Ω × Ω))) :=
  iter c (Fintype.card ((Ω × Ω) × (Ω × Ω)))

/-- §4.3.  The output of the process is stable. -/
theorem stable_isStable {C : Type u} [Fintype Ω] (c : Ω → Ω → C) : IsStable (stable c) := by
  classical
  set S : ℕ → Set ((Ω × Ω) × (Ω × Ω)) :=
    fun n => kernelSet (fun p : Ω × Ω => iter c n p.1 p.2) with hS
  have hmono : ∀ n, S (n + 1) ⊆ S n := by
    intro n p hp
    exact iter_isRefinement_le c (Nat.le_succ n) _ _ _ _ hp
  have hstep : ∀ n, S (n + 1) = S n → S (n + 2) = S (n + 1) := by
    intro n hn
    have hk : ∀ a b a' b' : Ω, iter c n a b = iter c n a' b'
        ↔ iter c (n + 1) a b = iter c (n + 1) a' b' := by
      intro a b a' b'
      constructor
      · intro hab
        have : ((a, b), (a', b')) ∈ S (n + 1) := by rw [hn]; exact hab
        exact this
      · intro hab
        exact hmono n (show ((a, b), (a', b')) ∈ S (n + 1) from hab)
    ext p
    obtain ⟨⟨a, b⟩, ⟨a', b'⟩⟩ := p
    exact (step_congr hk a b a' b').symm
  have hfix := eq_of_antitone_sets S hmono hstep
  intro x y x' y' hxy
  have hmem : ((x, y), (x', y')) ∈ S (Fintype.card ((Ω × Ω) × (Ω × Ω)) + 1) := by
    rw [hfix]; exact hxy
  exact hmem

/-- §4.3.  *"The classical WL refinement takes as input a binary configuration and refines
it to a coherent configuration."*  Combining Observation 4.3.1 with `stable_isStable`. -/
theorem isCoherentColoring_stable {C : Type u} [Fintype Ω] {c : Ω → Ω → C}
    (h : IsConfigColoring c) : IsCoherentColoring (stable c) :=
  (isStable_iff_isCoherentColoring (isConfigColoring_iter h _)).1 (stable_isStable c)

/-- §4.3.  The process is stable after **any** number of rounds at least `|(Ω×Ω)×(Ω×Ω)|`,
not only after exactly that number.  Running a fixed, larger number of rounds changes
nothing and makes the color type of the result independent of the vertex set, which is what
§9.4 step 3 needs: there the vertex set varies with the input, while the categories of §9.6
to §9.8 need one color type (see `Babai.wlRounds`). -/
theorem isStable_iter_of_card_le {C : Type u} [Finite Ω] (c : Ω → Ω → C) {M : ℕ}
    (hM : Nat.card ((Ω × Ω) × (Ω × Ω)) ≤ M) : IsStable (iter c M) := by
  classical
  set S : ℕ → Set ((Ω × Ω) × (Ω × Ω)) :=
    fun n => kernelSet (fun p : Ω × Ω => iter c n p.1 p.2) with hS
  have hmono : ∀ n, S (n + 1) ⊆ S n := by
    intro n p hp
    exact iter_isRefinement_le c (Nat.le_succ n) _ _ _ _ hp
  have hstep : ∀ n, S (n + 1) = S n → S (n + 2) = S (n + 1) := by
    intro n hn
    have hk : ∀ a b a' b' : Ω, iter c n a b = iter c n a' b'
        ↔ iter c (n + 1) a b = iter c (n + 1) a' b' := by
      intro a b a' b'
      constructor
      · intro hab
        have : ((a, b), (a', b')) ∈ S (n + 1) := by rw [hn]; exact hab
        exact this
      · intro hab
        exact hmono n (show ((a, b), (a', b')) ∈ S (n + 1) from hab)
    ext p
    obtain ⟨⟨a, b⟩, ⟨a', b'⟩⟩ := p
    exact (step_congr hk a b a' b').symm
  have hfix := eq_of_antitone_sets_le S hmono hstep hM
  intro x y x' y' hxy
  have hmem : ((x, y), (x', y')) ∈ S (M + 1) := by rw [hfix]; exact hxy
  exact hmem

/-- §4.3.  The coloring after `M ≥ |(Ω×Ω)×(Ω×Ω)|` rounds is coherent. -/
theorem isCoherentColoring_iter_of_card_le {C : Type u} [Finite Ω] {c : Ω → Ω → C} {M : ℕ}
    (h : IsConfigColoring c) (hM : Nat.card ((Ω × Ω) × (Ω × Ω)) ≤ M) :
    IsCoherentColoring (iter c M) :=
  (isStable_iff_isCoherentColoring (isConfigColoring_iter h _)).1
    (isStable_iter_of_card_le c hM)

/-! ### §4.3, Eq. (26): canonicity -/

/-- §4.2, §4.3.  `Iso(X, Y)` for colorings of `Ω × Ω` and `Ω' × Ω'` by the same color
set. -/
def Iso {C : Type u} (c : Ω → Ω → C) (c' : Ω' → Ω' → C) : Set (Ω ≃ Ω') :=
  {f | ∀ x y, c' (f x) (f y) = c x y}

/-- §4.3.  One round of WL refinement is canonical: `Iso(X', Y') = Iso(X, Y)`. -/
theorem iso_step {C : Type u} (c : Ω → Ω → C) (c' : Ω' → Ω' → C) :
    Iso (step c) (step c') = Iso c c' := by
  classical
  ext f
  constructor
  · intro h x y
    exact congrArg Prod.fst (h x y)
  · intro h x y
    refine Prod.ext (h x y) ?_
    funext jk
    have himg : {z' : Ω' | c' (f x) z' = jk.1 ∧ c' z' (f y) = jk.2}
        = f '' {z : Ω | c x z = jk.1 ∧ c z y = jk.2} := by
      ext z'
      constructor
      · intro hz
        refine ⟨f.symm z', ⟨?_, ?_⟩, f.apply_symm_apply z'⟩
        · rw [← h x (f.symm z'), f.apply_symm_apply]; exact hz.1
        · rw [← h (f.symm z') y, f.apply_symm_apply]; exact hz.2
      · rintro ⟨z, ⟨hz1, hz2⟩, rfl⟩
        exact ⟨(h x z).trans hz1, (h z y).trans hz2⟩
    show {z' : Ω' | c' (f x) z' = jk.1 ∧ c' z' (f y) = jk.2}.ncard = _
    rw [himg, Set.ncard_image_of_injective _ f.injective]
    rfl

/-- §4.3.  Every round of the process is canonical: `Iso(Xₙ, Yₙ) = Iso(X, Y)`. -/
theorem iso_iter {C : Type u} (c : Ω → Ω → C) (c' : Ω' → Ω' → C) :
    ∀ n : ℕ, Iso (iter c n) (iter c' n) = Iso c c'
  | 0 => rfl
  | n + 1 => (iso_step (iter c n) (iter c' n)).trans (iso_iter c c' n)

/-- §4.3, Eq. (26).  "Let `X` and `Y` be configurations.  We simultaneously execute each
round of refinement (merging the lists of refined colors).  Let `X*` and `Y*` be the
coherent configurations obtained.  Then `Iso(X, Y) = Iso(X*, Y*)`."

"Simultaneously" is the hypothesis that the same number of rounds is run on both sides,
which here follows from `|Ω| = |Ω'|`; for `|Ω| ≠ |Ω'|` both sides are empty. -/
theorem iso_stable {C : Type u} [Fintype Ω] [Fintype Ω'] (c : Ω → Ω → C) (c' : Ω' → Ω' → C) :
    Iso (stable c) (iter c' (Fintype.card ((Ω × Ω) × (Ω × Ω)))) = Iso c c' :=
  iso_iter c c' _

end WL

end Babai
