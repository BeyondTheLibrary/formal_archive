/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 5.1.1: Notation: strings.  Also the two string operators that §5.1.4 and §5.2
add to this notation: padding (Def. 5.1.6, Def. 5.1.12) and substitution (Not. 5.2.1).
-/
import Workspace.Prelim.Structures
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Logic.Equiv.Embedding

/-!
# §5.1.1 Strings over `Ω`

The paper's `Ω^k` is `Fin k → Ω`.  Indices are `0`-based in Lean and `1`-based in the
paper; every translated formula below says which index convention it is written in.

## Composition of index transformations (Notation 5.1.5)

The paper writes domain transformations in the exponent and composes them left to right
(`x^{fg} = (x^f)^g`), but writes index transformations `τ ∈ 𝔐_k` on the left,
`τ(x) = x_{1^τ} … x_{k^τ}`.  It records the resulting "unfortunate side-effect"
`(τμ)(x) = μ(τ(x))`.  That identity forces the product `τμ` in `𝔐_k` to be *ordinary*
composition `τ ∘ μ`: indeed with `τ(x) = x ∘ τ` we get

  `(τ ∘ μ)(x) = x ∘ τ ∘ μ = μ(τ(x))`,

which is `Babai.Str.idx_comp` below.  So the paper's `𝔐_k` is the monoid
`(Fin k → Fin k, ∘)` and `τ ↦ (x ↦ τ(x))` is an *anti*-homomorphism into the monoid of
maps `Ω^k → Ω^k`.  The same convention governs Remark 5.1.9 (`Higher/Configurations.lean`).

## Degenerate cases

`pad` (Def. 5.1.6) copies the *last* letter of a string, so it needs a nonempty string;
the paper assumes `1 ≤ ℓ` throughout §5.1.4, and `Str.pad` carries the hypothesis
`0 < l`.  Nothing else in this file restricts `k`, `l` or `Ω`: for `k = 0` the only
string is `Λ`, and for `Ω = ∅` there are no strings of positive length.

## Numbering map

| Paper | Lean |
|---|---|
| §5.1.1 `Ω^k`, `x⃗ y⃗`, `Λ`, `ℓ(x⃗)`, `supp(x⃗)`, `Ω^{≤k}` | `Babai.Str`, `.concat`, `.empty`, the index `k`, `.supp`, `Babai.StrLE` |
| Notation 5.1.1 (Tree of strings) | `Babai.Str.parent` |
| Definition 5.1.2 (Prefix) | `Babai.Str.take`, `Babai.Str.IsPrefix`, `.isPrefix_iff_parent` |
| Notation 5.1.3 (Strings of distinct elements) | `Babai.Str.Distinct`, `.card_distinct` |
| Notation 5.1.4 (Induced maps) | `Babai.tupleMap` (Notation 2.3.2) |
| Notation 5.1.5 (Symmetric monoid) | `Babai.Mon`, `Babai.Str.idx`, `.idx_comp`, `.idx_tupleMap` |
| Eq. (28) | `Babai.Str.supp_idx_subset` |
| Definition 5.1.6 (Padding) | `Babai.Str.pad` |
| Definition 5.1.12 (Padding of a transformation) | `Babai.Str.padMap` |
| Remark 5.1.13 | `Babai.Str.padMap_comp`, `.padMap_injective`, `.padMap_one_ne_one` |
| Observation 5.1.14 | `Babai.Str.idx_padMap_pad` |
| Notation 5.2.1 (Substitution) | `Babai.Str.subst` |
| the relation `ρ(x⃗)` of §5.1.5 | `Babai.Str.Rho` |
-/

namespace Babai

variable {Ω Ω' : Type*} {k l m : ℕ}

/-- §5.1.1.  "We write `Ω^k` to denote the set of strings of length `k` over `Ω`; so
`|Ω^k| = n^k`.  We write strings as `x⃗ = x₁ … x_k ∈ Ω^k`." -/
abbrev Str (Ω : Type*) (k : ℕ) : Type _ := Fin k → Ω

/-- Notation 5.1.5.  "For a set `Δ`, we write `𝔐(Δ)` to denote the *symmetric monoid*
over `Δ`; so `𝔐(Δ)` consists of all `Δ → Δ` maps.  We denote the set `{1,…,k}` by `[k]`
and set `𝔐_k := 𝔐[k]`."

The monoid operation is ordinary composition; see the module docstring. -/
abbrev Mon (k : ℕ) : Type _ := Fin k → Fin k

namespace Str

/-! ### Concatenation, the empty string, length, support -/

/-- §5.1.1.  "For `x⃗ ∈ Ω^k` and `y⃗ ∈ Ω^ℓ` we write `x⃗ y⃗ ∈ Ω^{k+ℓ}` to denote the
concatenation of the strings `x⃗` and `y⃗`." -/
def concat (x : Str Ω k) (y : Str Ω l) : Str Ω (k + l) := Fin.append x y

@[simp] theorem concat_left (x : Str Ω k) (y : Str Ω l) (i : Fin k) :
    concat x y (Fin.castAdd l i) = x i := Fin.append_left x y i

@[simp] theorem concat_right (x : Str Ω k) (y : Str Ω l) (i : Fin l) :
    concat x y (Fin.natAdd k i) = y i := Fin.append_right x y i

theorem concat_tupleMap (f : Ω → Ω') (x : Str Ω k) (y : Str Ω l) :
    concat (tupleMap f x) (tupleMap f y) = tupleMap f (concat x y) := by
  funext q
  refine Fin.addCases (fun i => ?_) (fun j => ?_) q <;> simp [tupleMap]

/-- §5.1.1.  "We denote the empty string by `Λ`, so `Ω⁰ = {Λ}`." -/
def empty : Str Ω 0 := Fin.elim0

theorem empty_unique (x : Str Ω 0) : x = empty := by
  funext i; exact absurd i.2 (Nat.not_lt_zero _)

/-- §5.1.1.  "We denote the length of the string `x⃗` by `ℓ(x⃗)`, so if `x⃗ ∈ Ω^k` then
`ℓ(x⃗) = k`."  The length is the type index `k`; this is the formal record of it. -/
def length (_x : Str Ω k) : ℕ := k

/-- §5.1.1.  "The *support* of the string `x⃗ = x₁ … x_k ∈ Ω^k` is the set
`supp(x⃗) = {x₁,…,x_k} ⊆ Ω`." -/
def supp (x : Str Ω k) : Set Ω := Set.range x

/-- §5.1.1.  "so `|supp(x⃗)| ≤ ℓ(x⃗)`." -/
theorem ncard_supp_le (x : Str Ω k) : (supp x).ncard ≤ k := by
  classical
  have h : (supp x).ncard ≤ (Set.univ : Set (Fin k)).ncard := by
    rw [supp, ← Set.image_univ]
    exact Set.ncard_image_le (Set.toFinite _)
  simpa using h

/-! ### The tree of strings, prefixes -/

/-- Notation 5.1.1 (Tree of strings).  "For `k ≥ 1` and `x⃗ = x₁ … x_k ∈ Ω^k` let
`p(x⃗) = x₁ … x_{k-1} ∈ Ω^{k-1}` be the 'parent' of `x⃗`.  The parent links define a rooted
tree structure on `Ω^{≤k}`, rooted at `Λ`." -/
def parent (x : Str Ω (k + 1)) : Str Ω k := Fin.init x

@[simp] theorem parent_apply (x : Str Ω (k + 1)) (i : Fin k) :
    parent x i = x i.castSucc := rfl

/-- Definition 5.1.2 (Prefix).  "For `ℓ ≤ k`, the *prefix of length `ℓ`* of the string
`x₁ … x_k ∈ Ω^k` is the substring `x₁ … x_ℓ ∈ Ω^ℓ`." -/
def take (h : l ≤ k) (x : Str Ω k) : Str Ω l := fun i => x (Fin.castLE h i)

@[simp] theorem take_apply (h : l ≤ k) (x : Str Ω k) (i : Fin l) :
    take h x i = x (Fin.castLE h i) := rfl

@[simp] theorem take_self (x : Str Ω k) : take le_rfl x = x := rfl

theorem take_take (h : l ≤ m) (h' : m ≤ k) (x : Str Ω k) :
    take h (take h' x) = take (h.trans h') x := rfl

/-- Definition 5.1.2.  `y⃗` is a prefix of `x⃗`. -/
def IsPrefix (y : Str Ω l) (x : Str Ω k) : Prop := ∃ h : l ≤ k, take h x = y

theorem isPrefix_take (h : l ≤ k) (x : Str Ω k) : IsPrefix (take h x) x := ⟨h, rfl⟩

theorem isPrefix_parent (x : Str Ω (k + 1)) : IsPrefix (parent x) x :=
  ⟨Nat.le_succ k, rfl⟩

/-- Definition 5.1.2, the remark after it.  The printed sentence reads "`y⃗ ∈ Ω^ℓ` is a
prefix of `x⃗ ∈ Ω^k` if and only if `y⃗` is a prefix of `x⃗`", which is a tautology; what is
meant is the compatibility of Def. 5.1.2 with the tree of Notation 5.1.1, namely that the
prefixes of `x⃗` are `x⃗` itself together with the prefixes of its parent `p(x⃗)`.  That is
what we record. -/
theorem isPrefix_iff_parent (y : Str Ω l) (x : Str Ω (k + 1)) :
    IsPrefix y x ↔ (∃ h : l = k + 1, y = fun i => x (Fin.cast h i)) ∨ IsPrefix y (parent x) := by
  constructor
  · rintro ⟨h, rfl⟩
    rcases Nat.lt_or_ge l (k + 1) with hlt | hge
    · exact Or.inr ⟨Nat.lt_succ_iff.1 hlt, rfl⟩
    · have hl : l = k + 1 := le_antisymm h hge
      exact Or.inl ⟨hl, by subst hl; rfl⟩
  · rintro (⟨rfl, rfl⟩ | ⟨h, rfl⟩)
    · exact ⟨le_rfl, rfl⟩
    · exact ⟨h.trans (Nat.le_succ k), rfl⟩

/-! ### Strings of distinct elements -/

/-- Notation 5.1.3 (Strings of distinct elements).  "`Ω^{⟨k⟩} = {x₁ … x_k ∈ Ω^k | all the
`xᵢ` are distinct}`." -/
def Distinct (x : Str Ω k) : Prop := Function.Injective x

/-- Notation 5.1.3.  "…to denote the subset of `Ω^k` consisting of the
`n(n-1)…(n-k+1)` strings of length `k` of distinct elements of `Ω`." -/
theorem card_distinct [Fintype Ω] :
    Nat.card {x : Str Ω k // Distinct x} = (Fintype.card Ω).descFactorial k := by
  classical
  have h : Nat.card {x : Str Ω k // Distinct x} = Nat.card (Fin k ↪ Ω) :=
    Nat.card_congr (Equiv.subtypeInjectiveEquivEmbedding (Fin k) Ω)
  rw [h, Nat.card_eq_fintype_card, Fintype.card_embedding_eq, Fintype.card_fin]

/-- Notation 5.1.3.  The support of a string of distinct elements has full size. -/
theorem ncard_supp_of_distinct (x : Str Ω k) (h : Distinct x) : (supp x).ncard = k := by
  classical
  rw [supp, Set.ncard_range_of_injective h]
  simp

/-! ### Induced maps and index transformations -/

/-- Notation 5.1.4 (Induced maps).  "For a map `f : Ω → Ω'` and a string
`x⃗ = x₁ … x_k ∈ Ω^k` we write `x⃗^f = x₁^f … x_k^f`."  This is Notation 2.3.2,
`Babai.tupleMap`. -/
theorem tupleMap_eq_comp (f : Ω → Ω') (x : Str Ω k) : tupleMap f x = f ∘ x := rfl

/-- Notation 5.1.5.  "The symmetric monoid `𝔐_k` induces an action on `Ω^k` by acting on
the subscripts ('index transformation'): for a map `τ ∈ 𝔐_k` and a string
`x⃗ = x₁ … x_k ∈ Ω^k` we write `τ(x⃗) = x_{1^τ} … x_{k^τ}`." -/
def idx (τ : Mon k) (x : Str Ω k) : Str Ω k := x ∘ τ

@[simp] theorem idx_apply (τ : Mon k) (x : Str Ω k) (i : Fin k) : idx τ x i = x (τ i) := rfl

@[simp] theorem idx_id (x : Str Ω k) : idx id x = x := rfl

/-- Notation 5.1.5.  "This has the usual unfortunate side-effect: `(τμ)(x⃗) = μ(τ(x⃗))`."
With the product of `𝔐_k` being composition of maps (see the module docstring), this is
the statement below. -/
theorem idx_comp (τ μ : Mon k) (x : Str Ω k) : idx (τ ∘ μ) x = idx μ (idx τ x) := rfl

/-- Notation 5.1.5.  "the domain transformation and the index transformation operators
commute; this will now appear as an associativity rule: for `f : Ω → Ω'` and `τ ∈ 𝔐_k` we
have `τ(x⃗^f) = (τ(x⃗))^f`." -/
theorem idx_tupleMap (f : Ω → Ω') (τ : Mon k) (x : Str Ω k) :
    idx τ (tupleMap f x) = tupleMap f (idx τ x) := rfl

/-- Eq. (28).  "`supp(τ(x⃗)) ⊆ supp(x⃗)`." -/
theorem supp_idx_subset (τ : Mon k) (x : Str Ω k) : supp (idx τ x) ⊆ supp x :=
  Set.range_comp_subset_range τ x

/-! ### `Ω^{≤k}` -/

end Str

/-- §5.1.1.  "We denote the set of strings of length not greater than `k` by
`Ω^{≤k} = ⋃_{0 ≤ ℓ ≤ k} Ω^ℓ`." -/
def StrLE (Ω : Type*) (k : ℕ) : Type _ := Σ l : {l : ℕ // l ≤ k}, Str Ω l

namespace StrLE

/-- The length `ℓ(x⃗)` of an element of `Ω^{≤k}`. -/
def length (x : StrLE Ω k) : ℕ := x.1.1

/-- The inclusion `Ω^ℓ ⊆ Ω^{≤k}` for `ℓ ≤ k`. -/
def of (h : l ≤ k) (x : Str Ω l) : StrLE Ω k := ⟨⟨l, h⟩, x⟩

@[simp] theorem length_of (h : l ≤ k) (x : Str Ω l) : length (of h x) = l := rfl

/-- Notation 5.1.3.  "We let `Ω^{⟨≤k⟩} = ⋃_{ℓ ≤ k} Ω^{⟨ℓ⟩}`." -/
def Distinct (x : StrLE Ω k) : Prop := Str.Distinct x.2

end StrLE

namespace Str

/-! ### Padding (Definitions 5.1.6 and 5.1.12) -/

/-- The index used by `pad`: `min j (l-1)`, the paper's "`j` if `j ≤ ℓ`, and `ℓ` if
`j ≥ ℓ`" in `0`-based form. -/
def padIdx (l : ℕ) (hl : 0 < l) (j : ℕ) : Fin l := ⟨min j (l - 1), by omega⟩

/-- The last index `ℓ` of a nonempty string (`0`-based: `l - 1`). -/
def lastIdx (l : ℕ) (hl : 0 < l) : Fin l := ⟨l - 1, by omega⟩

@[simp] theorem padIdx_of_lt {l : ℕ} (hl : 0 < l) {j : ℕ} (h : j < l) :
    padIdx l hl j = ⟨j, h⟩ := Fin.ext (by simp [padIdx]; omega)

theorem padIdx_of_ge {l : ℕ} (hl : 0 < l) {j : ℕ} (h : l - 1 ≤ j) :
    padIdx l hl j = lastIdx l hl := Fin.ext (by simp [padIdx, lastIdx]; omega)

/-- Definition 5.1.6 (Padding).  "Fix a set `Ω` and an integer `k ≥ 1`.  For `1 ≤ ℓ ≤ k`
and `x⃗ = x₁ … x_ℓ ∈ Ω^ℓ` let `pad(x⃗) = x₁ … x_k ∈ Ω^k` where for `j > ℓ` we set
`x_j := x_ℓ`."

The paper uses `pad` only for `1 ≤ ℓ ≤ k`; the definition below makes sense for every
`k` (for `k < l` it is the prefix of length `k`), and needs only `0 < l`, which is the
paper's `ℓ ≥ 1`. -/
def pad (hl : 0 < l) (k : ℕ) (x : Str Ω l) : Str Ω k := fun j => x (padIdx l hl j)

theorem pad_eq (hl : 0 < l) (k : ℕ) (x : Str Ω l) (j : Fin k) :
    pad hl k x j = x (padIdx l hl j) := rfl

theorem pad_apply_of_lt (hl : 0 < l) (x : Str Ω l) {j : Fin k} (h : (j : ℕ) < l) :
    pad hl k x j = x ⟨j, h⟩ := by
  unfold pad padIdx
  congr 1
  exact Fin.ext (by simp; omega)

theorem pad_apply_of_ge (hl : 0 < l) (x : Str Ω l) {j : Fin k} (h : l ≤ (j : ℕ)) :
    pad hl k x j = x ⟨l - 1, by omega⟩ := by
  unfold pad padIdx
  congr 1
  exact Fin.ext (by simp; omega)

/-- Definition 5.1.6.  Padding to the same length changes nothing. -/
@[simp] theorem pad_self (hl : 0 < l) (x : Str Ω l) : pad hl l x = x := by
  funext j
  rw [pad_apply_of_lt hl x j.2]

/-- Definition 5.1.6.  Padding commutes with domain transformations. -/
theorem pad_tupleMap (hl : 0 < l) (f : Ω → Ω') (x : Str Ω l) :
    pad hl k (tupleMap f x) = tupleMap f (pad hl k x) := rfl

/-- Definition 5.1.6.  The support of a padded string is the support of the string
(`l ≤ k`); in general it is contained in it. -/
theorem supp_pad_subset (hl : 0 < l) (x : Str Ω l) : supp (pad hl k x) ⊆ supp x := by
  rintro _ ⟨j, rfl⟩
  exact ⟨_, rfl⟩

/-- Definition 5.1.12.  "Let `τ ∈ 𝔐_ℓ`.  Let `τ' = pad(τ) ∈ 𝔐_k` be defined by setting,
for `j ∈ [k]`, `j^{τ'} = j^τ` if `j ≤ ℓ` and `j^{τ'} = ℓ^τ` if `j ≥ ℓ`."

In `0`-based form: `pad(τ)(j) = τ(min(j, ℓ-1))`, the image being cast into `[k]`. -/
def padMap (hl : 0 < l) (hlk : l ≤ k) (τ : Mon l) : Mon k :=
  fun j => Fin.castLE hlk (τ (padIdx l hl j))

theorem padMap_apply_of_lt (hl : 0 < l) (hlk : l ≤ k) (τ : Mon l) {j : Fin k}
    (h : (j : ℕ) < l) : padMap hl hlk τ j = Fin.castLE hlk (τ ⟨j, h⟩) := by
  unfold padMap padIdx
  congr 2
  exact Fin.ext (by simp; omega)

theorem padMap_apply_of_ge (hl : 0 < l) (hlk : l ≤ k) (τ : Mon l) {j : Fin k}
    (h : l ≤ (j : ℕ)) : padMap hl hlk τ j = Fin.castLE hlk (τ ⟨l - 1, by omega⟩) := by
  unfold padMap padIdx
  congr 2
  exact Fin.ext (by simp; omega)

/-- `padMap` is `pad` applied to `τ` read as a string, composed with the inclusion
`[ℓ] ⊆ [k]`. -/
theorem padMap_eq (hl : 0 < l) (hlk : l ≤ k) (τ : Mon l) :
    padMap hl hlk τ = tupleMap (Fin.castLE hlk) (pad hl k τ) := rfl

/-- Remark 5.1.13.  "The mapping `τ ↦ pad(τ)` is a semigroup embedding (injective
semigroup homomorphism) `𝔐_ℓ → 𝔐[k]`."  Homomorphism part. -/
theorem padMap_comp (hl : 0 < l) (hlk : l ≤ k) (τ μ : Mon l) :
    padMap hl hlk (τ ∘ μ) = padMap hl hlk τ ∘ padMap hl hlk μ := by
  funext j
  have hμ : ((padMap hl hlk μ j : Fin k) : ℕ) < l := by
    simp only [padMap, Fin.val_castLE]
    exact (μ _).2
  rw [Function.comp_apply, padMap_apply_of_lt hl hlk τ hμ]
  unfold padMap
  congr 2

/-- Remark 5.1.13.  Injectivity. -/
theorem padMap_injective (hl : 0 < l) (hlk : l ≤ k) :
    Function.Injective (padMap hl hlk) := by
  intro τ μ h
  funext i
  have hi : ((Fin.castLE hlk i : Fin k) : ℕ) < l := by simp [i.2]
  have hfun := congrFun h (Fin.castLE hlk i)
  rw [padMap_apply_of_lt hl hlk τ hi, padMap_apply_of_lt hl hlk μ hi] at hfun
  have hval : (τ ⟨(Fin.castLE hlk i : Fin k), hi⟩ : Fin l) = μ ⟨(Fin.castLE hlk i : Fin k), hi⟩ :=
    Fin.castLE_injective hlk hfun
  have hidx : (⟨((Fin.castLE hlk i : Fin k) : ℕ), hi⟩ : Fin l) = i := Fin.ext (by simp)
  rwa [hidx] at hval

/-- Remark 5.1.13.  "(but not a monoid embedding: the identity does not map to the
identity)."  For `ℓ < k`, `pad(id_ℓ)` sends every `j ≥ ℓ` to `ℓ`. -/
theorem padMap_id_ne_id (hl : 0 < l) (hlk : l ≤ k) (h : l < k) :
    padMap hl hlk (id : Mon l) ≠ (id : Mon k) := by
  intro hcon
  have hj : (l : ℕ) ≤ ((⟨l, h⟩ : Fin k) : ℕ) := le_rfl
  have := congrFun hcon (⟨l, h⟩ : Fin k)
  rw [padMap_apply_of_ge hl hlk id hj] at this
  simp only [id_eq] at this
  have : (l - 1 : ℕ) = l := congrArg Fin.val this
  omega

/-- Observation 5.1.14.  "Let `x⃗ = x₁ … x_ℓ ∈ Ω^ℓ` and `τ ∈ 𝔐_ℓ`.  Then
`(pad(τ))(pad(x⃗)) = pad(τ(x⃗))`."  (Eq. (31).)

Paper's proof: "Let `j ∈ [k]`.  Let us compare the `j`-th letter of the strings on each
side.  First assume `j ≤ ℓ`.  Then on the right-hand side we have `x_{j^τ}`.  On the
left-hand side we have `x_{j^{pad(τ)}}`.  As `j^τ = j^{pad(τ)}`, we are done.  Assume now
`j ≥ ℓ`.  Then on the right-hand side we have `x_{ℓ^τ}`.  On the left-hand side we have
`x_{ℓ^{pad(τ)}}`.  We conclude as before." -/
theorem idx_padMap_pad (hl : 0 < l) (hlk : l ≤ k) (τ : Mon l) (x : Str Ω l) :
    idx (padMap hl hlk τ) (pad hl k x) = pad hl k (idx τ x) := by
  funext j
  rw [idx_apply]
  rcases Nat.lt_or_ge (j : ℕ) l with h | h
  · -- `j ≤ ℓ` in the paper's `1`-based indexing
    rw [padMap_apply_of_lt hl hlk τ h, pad_apply_of_lt hl x (by simp),
      pad_apply_of_lt hl (idx τ x) h]
    simp [idx]
  · -- `j ≥ ℓ`
    rw [padMap_apply_of_ge hl hlk τ h, pad_apply_of_lt hl x (by simp),
      pad_apply_of_ge hl (idx τ x) h]
    simp [idx]

/-! ### Substitution (Notation 5.2.1) and the relation `ρ(x⃗)` -/

/-- Notation 5.2.1 (Substitution).  "For `x⃗ ∈ Ω^k`, `z ∈ Ω`, and `j ∈ [k]` we write
`x⃗^j(z)` to denote the string `y⃗ = y₁ … y_k` where `y_i = z` if `i = j` and `y_i = x_i`
if `i ≠ j`."  (Eq. (32).) -/
def subst (x : Str Ω k) (j : Fin k) (z : Ω) : Str Ω k := Function.update x j z

@[simp] theorem subst_same (x : Str Ω k) (j : Fin k) (z : Ω) : subst x j z j = z :=
  Function.update_self ..

@[simp] theorem subst_of_ne (x : Str Ω k) {i j : Fin k} (h : i ≠ j) (z : Ω) :
    subst x j z i = x i := Function.update_of_ne h ..

theorem subst_eq_self (x : Str Ω k) (j : Fin k) : subst x j (x j) = x := by
  funext i
  rcases eq_or_ne i j with rfl | h
  · simp
  · simp [h]

/-- Substituting into a coordinate of the second factor of a concatenation. -/
theorem concat_subst (x : Str Ω k) (y : Str Ω l) (t : Fin l) (z : Ω) :
    concat x (subst y t z) = subst (concat x y) (Fin.natAdd k t) z := by
  funext q
  refine Fin.addCases (fun i => ?_) (fun j => ?_) q
  · have hne : (Fin.castAdd l i : Fin (k + l)) ≠ Fin.natAdd k t := by
      intro hc
      have hv := congrArg Fin.val hc
      simp at hv
      omega
    rw [concat_left, subst_of_ne _ hne, concat_left]
  · rcases eq_or_ne j t with rfl | hjt
    · rw [concat_right, subst_same, subst_same]
    · have hne : (Fin.natAdd k j : Fin (k + l)) ≠ Fin.natAdd k t := by
        intro hc
        exact hjt (Fin.ext (by have hv := congrArg Fin.val hc; simpa using hv))
      rw [concat_right, subst_of_ne _ hne, subst_of_ne _ hjt, concat_right]

theorem subst_tupleMap (f : Ω → Ω') (x : Str Ω k) (j : Fin k) (z : Ω) :
    tupleMap f (subst x j z) = subst (tupleMap f x) j (f z) := by
  funext i
  rcases eq_or_ne i j with rfl | h
  · simp [tupleMap]
  · simp [tupleMap, h]

/-- §5.1.5.  "A string `x⃗ = x₁ … x_k ∈ Ω^k` defines an equivalence relation `ρ(x⃗)` on
`[k]` as follows: `i ∼ j` if `xᵢ = xⱼ`." -/
def Rho (x : Str Ω k) (i j : Fin k) : Prop := x i = x j

theorem rho_equivalence (x : Str Ω k) : Equivalence (Rho x) where
  refl _ := rfl
  symm h := h.symm
  trans h h' := h.trans h'

end Str

end Babai
