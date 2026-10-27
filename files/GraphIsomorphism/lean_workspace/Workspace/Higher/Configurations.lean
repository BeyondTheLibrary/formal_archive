/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Sections 5.1.2–5.1.5: k-ary relational structures, k-ary partition structures,
skeleton and extended coloring, k-ary configurations.
-/
import Workspace.Higher.Strings

/-!
# §5.1.2–§5.1.5 `k`-ary structures, partition structures, configurations

## The set of colors

The paper fixes "a finite linearly ordered set `C`" of colors and indexes the relations of
a `k`-ary structure by `C`.  Here `C` is a type parameter.  The linear order is used by
the paper only to *name* the new colors produced by the functors `F1`, `F2`, `F3`
(lexicographic ordering of tuples of old colors); since a renaming of colors changes no
isomorphism and no axiom, the functors below produce colors in a structured type
(`Set C`, a pair, …) and no ordering is needed.  This is the same convention as in §3,
where `Babai.PartitionStructure.ofColoring` renumbers a coloring by `[r]`
(`Coherent/Configurations.lean`).

## Partition structures and the skeleton

Definition 5.1.3 asks that the `Rᵢ` partition `Ω^k` *and that none of them be empty*.  The
first half is automatic once the structure is presented by a coloring `c : Ω^k → C`, which
is what `Babai.KAryPartStruct` does; the second half is `Function.Surjective c`, recorded
as the predicate `IsFull`.  It is *not* part of `IsConfiguration`/`IsCoherent` because the
paper's own constructions do not preserve it on the nose: the `ℓ`-skeleton `X^{(ℓ)}` uses
the color set of `X`, of which in general only some colors occur on `Ω^ℓ`.  The paper's
"clearly, `X^{(ℓ)}` is an `ℓ`-ary partition structure" therefore means "after the empty
relations are dropped", exactly as in Example 3.1.7 of §3.  Dropping them is the
restriction of `C` to the range of the coloring, which changes nothing else; `IsFull` and
`isFull_skeleton_range` record this.

## Degenerate cases

Nothing here assumes `Ω` finite, `Ω` nonempty, or `k ≥ 1`.  For `k = 0` the only string is
`Λ` and every coloring is a configuration; for `Ω = ∅` and `k ≥ 1` there are no strings at
all.  The skeleton `X^{(ℓ)}` is formed only for `1 ≤ ℓ ≤ k`, the paper's range, because
`pad` copies the last letter of a nonempty string, and because for `ℓ > k` padding would
truncate and Prop. 5.1.11 would fail.

## Numbering map

| Paper | Lean |
|---|---|
| §5.1.2 `k`-ary relation, `k`-ary structure, `Iso`, `Aut` | `Babai.KAryRelStruct`, `.Iso`, `.Aut` |
| §5.1.3 `k`-ary partition structure | `Babai.KAryPartStruct`, `.IsFull`, `.toRelStruct` |
| §5.1.3 the functor `F1` | `Babai.KAryRelStruct.F1`, `.iso_F1` |
| §5.1.3 induced substructure `(Φ, c_Φ)` | `Babai.KAryPartStruct.induced` |
| §5.1.4 Definition 5.1.7 (Skeleton) | `Babai.KAryPartStruct.skeleton`, `.skeletonColor` |
| §5.1.4 `X^{(k)} = X`, forgetful functor | `.skeleton_self`, `.iso_subset_iso_skeleton` |
| §5.1.4 extended coloring on `Ω^{≤k}`, color of `Λ` | `.extColor` |
| Definition 5.1.8 (Configuration) | `Babai.KAryPartStruct.IsConfiguration` |
| Remark 5.1.9 | `.eta`, `.color_idx_eq_eta`, `.eta_comp` |
| Observation 5.1.10 (Vertex-color awareness) | `.vcolor`, `.vcolor_eq_of_color_eq` |
| §5.1.5 the functor `F2` | `.F2`, `.F2_isConfiguration`, `.F2_refines`, `.F2_coarsest`, `.iso_F2` |
| Proposition 5.1.11 (Skeleton 1) | `.skeleton_isConfiguration` |
| Proposition 5.1.15 (Induced subconfiguration) | `.induced_isConfiguration` |
-/

namespace Babai

variable {Ω Ω' C C' : Type*} {k l : ℕ}

/-! ### §5.1.2 `k`-ary relational structures -/

/-- §5.1.2.  "A `k`-ary relation on `Ω` is a subset `R ⊆ Ω^k`.  A *`k`-ary relational
structure* or *`k`-ary structure* over the index set `C` is a pair `X = (Ω, R)` where
`R = (Rᵢ : i ∈ C)` where each `Rᵢ` is a `k`-ary relation on `Ω`." -/
structure KAryRelStruct (Ω : Type*) (C : Type*) (k : ℕ) where
  /-- The relations `Rᵢ ⊆ Ω^k`, one for each color `i ∈ C`. -/
  rel : C → Set (Str Ω k)

namespace KAryRelStruct

/-- §5.1.2.  "An isomorphism between `X` and `X' = (Ω', R')` where `R' = (R'ᵢ : i ∈ C)` is
a bijection `f : Ω → Ω'` such that for all `i ∈ C` and all `x⃗ ∈ Ω^k` we have `x⃗ ∈ Rᵢ` if
and only if `x⃗^f ∈ R'ᵢ`.  (Isomorphism can occur only when the two structures are indexed
over the same set of colors.)  The set of `X → X'` isomorphisms is denoted
`Iso(X, X')`." -/
def Iso (X : KAryRelStruct Ω C k) (X' : KAryRelStruct Ω' C k) : Set (Ω ≃ Ω') :=
  {f | ∀ (i : C) (x : Str Ω k), x ∈ X.rel i ↔ tupleMap f x ∈ X'.rel i}

/-- §5.1.2.  "The automorphism group of `X` is `Aut(X) = Iso(X, X)`." -/
def Aut (X : KAryRelStruct Ω C k) : Subgroup (Equiv.Perm Ω) where
  carrier := {f | ∀ (i : C) (x : Str Ω k), x ∈ X.rel i ↔ tupleMap f x ∈ X.rel i}
  one_mem' := by intro i x; rfl
  mul_mem' := by
    intro a b ha hb i x
    rw [hb i x, ha i (tupleMap b x)]
    rfl
  inv_mem' := by
    intro a ha i x
    rw [ha i (tupleMap ((a⁻¹ : Equiv.Perm Ω) : Ω → Ω) x)]
    have hx : tupleMap ((a : Equiv.Perm Ω) : Ω → Ω)
        (tupleMap ((a⁻¹ : Equiv.Perm Ω) : Ω → Ω) x) = x := by
      funext j; simp [tupleMap]
    rw [hx]

@[simp] theorem mem_Aut {X : KAryRelStruct Ω C k} {f : Equiv.Perm Ω} :
    f ∈ X.Aut ↔ ∀ (i : C) (x : Str Ω k), x ∈ X.rel i ↔ tupleMap f x ∈ X.rel i := Iff.rfl

theorem aut_eq_iso (X : KAryRelStruct Ω C k) : (X.Aut : Set (Equiv.Perm Ω)) = Iso X X := rfl

end KAryRelStruct

/-! ### §5.1.3 `k`-ary partition structures -/

/-- §5.1.3.  "We say that `X` is a `k`-ary *partition structure* if the `Rᵢ` partition
`Ω^k` and none of the `Rᵢ` is empty. … For `x⃗ ∈ Ω^k` we write `c(x⃗) = i` if `x⃗ ∈ Rᵢ`; in
this case we refer to `i` as 'the color' of `x⃗`.  We shall alternatively denote
`X = (Ω, R)` by `X = (Ω, c)` since `R` can be uniquely reconstructed from `c`."

We take the coloring as the primitive datum, which builds in "the `Rᵢ` partition `Ω^k`";
the remaining requirement "none of the `Rᵢ` is empty" is `IsFull`. -/
structure KAryPartStruct (Ω : Type*) (C : Type*) (k : ℕ) where
  /-- The coloring `c : Ω^k → C`. -/
  color : Str Ω k → C

namespace KAryPartStruct

variable (X : KAryPartStruct Ω C k)

/-- §5.1.3.  "`Rᵢ = c⁻¹(i)`." -/
def rel (i : C) : Set (Str Ω k) := {x | X.color x = i}

@[simp] theorem mem_rel {i : C} {x : Str Ω k} : x ∈ X.rel i ↔ X.color x = i := Iff.rfl

/-- §5.1.3.  `X = (Ω, c)` read as the `k`-ary relational structure `(Ω, R)`. -/
def toRelStruct : KAryRelStruct Ω C k := ⟨X.rel⟩

/-- §5.1.3.  "none of the `Rᵢ` is empty": every color is realized. -/
def IsFull : Prop := Function.Surjective X.color

/-- §5.1.2 for partition structures: `f` is an isomorphism exactly if it preserves the
coloring. -/
def Iso (X : KAryPartStruct Ω C k) (X' : KAryPartStruct Ω' C k) : Set (Ω ≃ Ω') :=
  {f | ∀ x : Str Ω k, X'.color (tupleMap f x) = X.color x}

/-- §5.1.2 for partition structures: `Aut(X) = Iso(X, X)`. -/
def Aut : Subgroup (Equiv.Perm Ω) where
  carrier := {f | ∀ x : Str Ω k, X.color (tupleMap f x) = X.color x}
  one_mem' := by intro x; rfl
  mul_mem' := by
    intro a b ha hb x
    have : tupleMap ((a * b : Equiv.Perm Ω) : Ω → Ω) x = tupleMap a (tupleMap b x) := rfl
    rw [this, ha (tupleMap b x), hb x]
  inv_mem' := by
    intro a ha x
    have h := ha (tupleMap ((a⁻¹ : Equiv.Perm Ω) : Ω → Ω) x)
    have hx : tupleMap ((a : Equiv.Perm Ω) : Ω → Ω)
        (tupleMap ((a⁻¹ : Equiv.Perm Ω) : Ω → Ω) x) = x := by
      funext j; simp [tupleMap]
    rw [hx] at h
    exact h.symm

@[simp] theorem mem_aut {X : KAryPartStruct Ω C k} {f : Equiv.Perm Ω} :
    f ∈ X.Aut ↔ ∀ x : Str Ω k, X.color (tupleMap f x) = X.color x := Iff.rfl

theorem iso_eq_relStruct_iso (X : KAryPartStruct Ω C k) (X' : KAryPartStruct Ω' C k) :
    Iso X X' = KAryRelStruct.Iso X.toRelStruct X'.toRelStruct := by
  ext f
  constructor
  · intro h i x
    simp only [KAryRelStruct.Iso, toRelStruct, mem_rel, Set.mem_setOf_eq]
    rw [h x]
  · intro h x
    exact (h (X.color x) x).1 rfl

/-- §5.1.3.  "Let `Φ ⊆ Ω`.  The *induced substructure* `(Φ, c_Φ)` is defined by letting
`c_Φ` be the restriction of the coloring `c` to `Φ^k`." -/
def induced (Φ : Set Ω) : KAryPartStruct Φ C k :=
  ⟨fun y => X.color (tupleMap Subtype.val y)⟩

@[simp] theorem induced_color (Φ : Set Ω) (y : Str Φ k) :
    (X.induced Φ).color y = X.color (tupleMap Subtype.val y) := rfl

end KAryPartStruct

namespace KAryRelStruct

/-- §5.1.3, the functor `F1`.  "There is a functor `F1`, computable in time `|C| · n^{O(k)}`,
that converts `k`-ary structures into `k`-ary partition structures without changing their
underlying sets, such that `Iso(X, Y) = Iso(F1(X), F1(Y))` for all pairs `(X, Y)` of
`k`-ary relational structures.  We define `F1(X)` as follows.  Assign to each `x⃗ ∈ Ω^k`
the color `c(x⃗) = {i ∈ C | x⃗ ∈ Rᵢ}`.  Let the new set `C'` of colors be the range of the
function `c`, and define `F1(X) = (Ω, R')` … `R'_j = {x⃗ ∈ Ω^k | c(x⃗) = j}`."

The paper's `C'` is the range of `c`; we keep the ambient color type `Set C`, so that
`F1(X)` is full after `C'` is cut down to the range (`isFull_F1_range`). -/
def F1 (X : KAryRelStruct Ω C k) : KAryPartStruct Ω (Set C) k :=
  ⟨fun x => {i | x ∈ X.rel i}⟩

@[simp] theorem F1_color (X : KAryRelStruct Ω C k) (x : Str Ω k) :
    X.F1.color x = {i | x ∈ X.rel i} := rfl

/-- §5.1.3, the functor `F1`: "`Iso(X, Y) = Iso(F1(X), F1(Y))`." -/
theorem iso_F1 (X : KAryRelStruct Ω C k) (Y : KAryRelStruct Ω' C k) :
    KAryPartStruct.Iso X.F1 Y.F1 = Iso X Y := by
  ext f
  constructor
  · intro h i x
    have := congrArg (fun S => i ∈ S) (h x)
    simpa using this.symm
  · intro h x
    ext i
    simpa using (h i x).symm

/-- §5.1.3.  After cutting the color set down to the range of `c`, `F1(X)` is a partition
structure in the paper's sense (no empty relation). -/
theorem isFull_F1_range (X : KAryRelStruct Ω C k) :
    Function.Surjective (fun x => (⟨X.F1.color x, Set.mem_range_self x⟩ :
      Set.range X.F1.color)) := by
  rintro ⟨j, x, rfl⟩
  exact ⟨x, rfl⟩

end KAryRelStruct

namespace KAryPartStruct

variable (X : KAryPartStruct Ω C k)

/-! ### §5.1.4 Skeleton, extended coloring -/

/-- Definition 5.1.7 (Skeleton).  "Let `X = (Ω, c)` be a `k`-ary partition structure.  For
`1 ≤ ℓ ≤ k` we define the coloring `c^{(ℓ)} : Ω^ℓ → C` by setting, for `x⃗ ∈ Ω^ℓ`,
`c^{(ℓ)}(x⃗) := c(pad(x⃗))`."  (Eq. (29).) -/
def skeletonColor (hl : 0 < l) (_hlk : l ≤ k) (x : Str Ω l) : C :=
  X.color (Str.pad hl k x)

/-- Definition 5.1.7.  "We define the `ℓ`-skeleton of `X` as `X^{(ℓ)} = (Ω, c^{(ℓ)})`." -/
def skeleton (hl : 0 < l) (hlk : l ≤ k) : KAryPartStruct Ω C l :=
  ⟨X.skeletonColor hl hlk⟩

@[simp] theorem skeleton_color (hl : 0 < l) (hlk : l ≤ k) (x : Str Ω l) :
    (X.skeleton hl hlk).color x = X.color (Str.pad hl k x) := rfl

/-- Definition 5.1.7.  "Note that `X^{(k)} = X`." -/
@[simp] theorem skeleton_self (hk : 0 < k) : X.skeleton hk (le_refl k) = X := by
  cases X with
  | mk c =>
    simp only [skeleton, mk.injEq]
    funext x
    show c (Str.pad hk k x) = c x
    rw [Str.pad_self]

/-- Definition 5.1.7.  "the assignment `X ↦ X^{(ℓ)}` defines a (forgetful) functor;
`Iso(X^{(ℓ)}, Y^{(ℓ)}) ⊇ Iso(X, Y)`." -/
theorem iso_subset_iso_skeleton (X : KAryPartStruct Ω C k) (Y : KAryPartStruct Ω' C k)
    (hl : 0 < l) (hlk : l ≤ k) :
    Iso X Y ⊆ Iso (X.skeleton hl hlk) (Y.skeleton hl hlk) := by
  intro f hf x
  rw [skeleton_color, skeleton_color, Str.pad_tupleMap, hf]

/-- Definition 5.1.7, extended coloring.  "For the empty string `Λ` we reserve a special
color `c^{(0)}(Λ)` since the convention above does not assign `Λ` a color.  With some abuse
of notation, for `x⃗ ∈ Ω^{≤k}` we shall write `c(x⃗)` to denote `c^{(ℓ(x⃗))}(x⃗)` whenever this
does not lead to ambiguity.  This way we have extended the coloring `c` from `Ω^k` to
`Ω^{≤k}`."

The "special color" reserved for `Λ` is realized as `none` in `Option C`. -/
def extColor (x : StrLE Ω k) : Option C :=
  if h : 0 < x.1.1 then some (X.color (Str.pad h k x.2)) else none

@[simp] theorem extColor_empty (x : StrLE Ω k) (h : x.1.1 = 0) : X.extColor x = none := by
  simp [extColor, h]

@[simp] theorem extColor_of (hl : 0 < l) (hlk : l ≤ k) (x : Str Ω l) :
    X.extColor (StrLE.of hlk x) = some (X.skeletonColor hl hlk x) := by
  simp [extColor, StrLE.of, skeletonColor, hl]

/-- Definition 5.1.7, extended coloring: the color of `Λ` is different from the color of
every nonempty string. -/
theorem extColor_empty_ne (x : StrLE Ω k) (h : 0 < x.1.1) (y : StrLE Ω k) (hy : y.1.1 = 0) :
    X.extColor x ≠ X.extColor y := by
  simp [extColor, h, hy]

/-! ### §5.1.5 `k`-ary configurations -/

/-- Definition 5.1.8 (Configuration).  "We say that the `k`-ary partition structure
`X = (Ω, c)` is a *`k`-ary configuration* if the following two axioms hold.  For all
`x⃗, y⃗ ∈ Ω^k` and `τ ∈ 𝔐_k`, if `c(x⃗) = c(y⃗)` then (i) `ρ(x⃗) = ρ(y⃗)`;
(ii) `c(τ(x⃗)) = c(τ(y⃗))`."

Here `ρ(x⃗)` is the equivalence relation `i ∼ j ⟺ xᵢ = xⱼ` on `[k]` (§5.1.5), so
`ρ(x⃗) = ρ(y⃗)` is the displayed biconditional. -/
structure IsConfiguration (X : KAryPartStruct Ω C k) : Prop where
  /-- Axiom (i): "`ρ(x⃗) = ρ(y⃗)`". -/
  rho : ∀ x y : Str Ω k, X.color x = X.color y → ∀ i j : Fin k, (x i = x j ↔ y i = y j)
  /-- Axiom (ii): "`c(τ(x⃗)) = c(τ(y⃗))`". -/
  idx : ∀ (x y : Str Ω k) (τ : Mon k), X.color x = X.color y →
    X.color (Str.idx τ x) = X.color (Str.idx τ y)

/-- Remark 5.1.9.  "The latter means that there is a monoid homomorphism
`η : 𝔐_k → 𝔐(C)` such that for all `x⃗ ∈ Ω^k` and `τ ∈ 𝔐_k` we have
`c(τ(x⃗)) = η(τ)(c(x⃗))`."

On colors that are not realized by any string, `η(τ)` is the identity (any value would
do). -/
noncomputable def eta (X : KAryPartStruct Ω C k) (τ : Mon k) (i : C) : C := by
  classical
  exact if h : ∃ x : Str Ω k, X.color x = i then X.color (Str.idx τ h.choose) else i

/-- Remark 5.1.9.  "`c(τ(x⃗)) = η(τ)(c(x⃗))`." -/
theorem color_idx_eq_eta (h : X.IsConfiguration) (τ : Mon k) (x : Str Ω k) :
    X.color (Str.idx τ x) = X.eta τ (X.color x) := by
  classical
  have hex : ∃ y : Str Ω k, X.color y = X.color x := ⟨x, rfl⟩
  rw [eta, dif_pos hex]
  exact (h.idx _ _ τ hex.choose_spec).symm

/-- Remark 5.1.9, the homomorphism property.  With the composition conventions of
Notation 5.1.5 (see the module docstring of `Higher/Strings.lean`), `η` reverses
composition: `η(τ ∘ μ) = η(μ) ∘ η(τ)`.  This is the same "unfortunate side-effect" as
`Babai.Str.idx_comp`; the paper's word "homomorphism" refers to its own left-to-right
composition of operators.

Full partition structures only: on a color that no string realizes, `η` is unconstrained. -/
theorem eta_comp (h : X.IsConfiguration) (hfull : X.IsFull) (τ μ : Mon k) :
    X.eta (τ ∘ μ) = X.eta μ ∘ X.eta τ := by
  funext i
  obtain ⟨x, rfl⟩ := hfull i
  rw [← color_idx_eq_eta X h, Function.comp_apply, ← color_idx_eq_eta X h,
    ← color_idx_eq_eta X h, Str.idx_comp]

/-- Observation 5.1.10, in the form used below: the *vertex color* `c(v)` of `v ∈ Ω` is
`c^{(1)}(v)`, the color of the constant string `v … v`. -/
def vcolor (X : KAryPartStruct Ω C k) (v : Ω) : C := X.color (fun _ => v)

theorem vcolor_eq_skeletonColor (hk : 0 < k) (v : Ω) :
    X.vcolor v = X.skeletonColor Nat.one_pos hk (fun _ : Fin 1 => v) := rfl

/-- Observation 5.1.10 (Vertex-color awareness).  "Let `X = (Ω, c)` be a configuration.
Let `x⃗ = x₁ … x_k` and `y⃗ = y₁ … y_k` be strings in `Ω^k`.  If `c(x⃗) = c(y⃗)` then for each
`i ∈ [k]` we have `c(xᵢ) = c(yᵢ)`."

Paper's proof: "Let `τᵢ ∈ 𝔐_k` be defined as the constant map to `i`, i.e. `τᵢ(j) = i` for
all `j ∈ [k]`.  So, using Axiom (ii) from Def. 5.1.8 we obtain
`c(xᵢ) = c^{(1)}(xᵢ) = c(τᵢ(x⃗)) = c(τᵢ(y⃗)) = c^{(1)}(yᵢ) = c(yᵢ)`." -/
theorem vcolor_eq_of_color_eq (h : X.IsConfiguration) {x y : Str Ω k}
    (hxy : X.color x = X.color y) (i : Fin k) : X.vcolor (x i) = X.vcolor (y i) := by
  have hconst : ∀ z : Str Ω k, Str.idx (fun _ => i) z = fun _ => z i := fun _ => rfl
  have := h.idx x y (fun _ => i) hxy
  rw [hconst x, hconst y] at this
  exact this

/-! ### §5.1.5 the functor `F2` -/

section F2

/-- §5.1.5, the functor `F2` ("ADD DETAILS HERE", p. 47).  "There is a functor `F2`,
computable in time `n^{O(k)}`, that converts `k`-ary partition structures into `k`-ary
configurations without changing their underlying sets, such that
`Iso(X, Y) = Iso(F2(X), F2(Y))` for all pairs `X, Y` of `k`-ary partition structures.
`F2` assigns to each partition structure its unique coarsest refinement that is a
configuration (with an appropriate assignment of colors)."

The details are missing from version 2.5 and from the original arXiv version, so we supply
the construction, in the paper's style: give `x⃗` the color consisting of the relation
`ρ(x⃗)` together with the list of the old colors of all the strings `τ(x⃗)`, `τ ∈ 𝔐_k`.
This is a refinement of `c` (take `τ = id`), it satisfies both axioms of Def. 5.1.8 after
a *single* round (`F2_isConfiguration`), and it is coarser than every refinement of `c`
that is a configuration (`F2_coarsest`), so it is the coarsest one.  See the corrected paper,
"hole in 2.5", §5.1.5. -/
def F2 (X : KAryPartStruct Ω C k) :
    KAryPartStruct Ω ((Fin k → Fin k → Prop) × (Mon k → C)) k :=
  ⟨fun x => (fun i j => x i = x j, fun τ => X.color (Str.idx τ x))⟩

@[simp] theorem F2_color (x : Str Ω k) :
    X.F2.color x = (fun i j => x i = x j, fun τ => X.color (Str.idx τ x)) := rfl

theorem F2_color_eq_iff (x y : Str Ω k) :
    X.F2.color x = X.F2.color y ↔
      (∀ i j : Fin k, (x i = x j ↔ y i = y j)) ∧
        ∀ τ : Mon k, X.color (Str.idx τ x) = X.color (Str.idx τ y) := by
  constructor
  · intro h
    refine ⟨fun i j => ?_, fun τ => ?_⟩
    · have := congrFun (congrFun (congrArg Prod.fst h) i) j
      exact iff_of_eq this
    · exact congrFun (congrArg Prod.snd h) τ
  · rintro ⟨h1, h2⟩
    refine Prod.ext ?_ ?_
    · funext i j; exact propext (h1 i j)
    · funext τ; exact h2 τ

/-- §5.1.5, `F2`: the result is a configuration. -/
theorem F2_isConfiguration : X.F2.IsConfiguration where
  rho x y h := ((X.F2_color_eq_iff x y).1 h).1
  idx x y τ h := by
    obtain ⟨h1, h2⟩ := (X.F2_color_eq_iff x y).1 h
    refine (X.F2_color_eq_iff _ _).2 ⟨fun i j => ?_, fun μ => ?_⟩
    · simpa using h1 (τ i) (τ j)
    · rw [← Str.idx_comp, ← Str.idx_comp]
      exact h2 (τ ∘ μ)

/-- §5.1.5, `F2`: the new coloring refines the old one. -/
theorem F2_refines {x y : Str Ω k} (h : X.F2.color x = X.F2.color y) :
    X.color x = X.color y := by
  have := ((X.F2_color_eq_iff x y).1 h).2 id
  simpa using this

/-- §5.1.5, `F2`: "its unique coarsest refinement that is a configuration".  Every
refinement `d` of `c` that is a configuration refines `F2(X)`, i.e. `F2(X)` is coarser
than `d`; together with `F2_refines` and `F2_isConfiguration` this says that `F2(X)` is
the coarsest configuration refinement, and it is unique up to renaming of colors. -/
theorem F2_coarsest (Y : KAryPartStruct Ω C' k) (hY : Y.IsConfiguration)
    (href : ∀ x y : Str Ω k, Y.color x = Y.color y → X.color x = X.color y)
    {x y : Str Ω k} (h : Y.color x = Y.color y) : X.F2.color x = X.F2.color y :=
  (X.F2_color_eq_iff x y).2 ⟨hY.rho x y h, fun τ => href _ _ (hY.idx x y τ h)⟩

/-- §5.1.5, `F2`: "`Iso(X, Y) = Iso(F2(X), F2(Y))`." -/
theorem iso_F2 (X : KAryPartStruct Ω C k) (Y : KAryPartStruct Ω' C k) :
    Iso X.F2 Y.F2 = Iso X Y := by
  ext f
  constructor
  · intro h x
    have := congrFun (congrArg Prod.snd (h x)) id
    simpa [Str.idx] using this
  · intro h x
    refine Prod.ext ?_ ?_
    · funext i j
      show (f (x i) = f (x j)) = (x i = x j)
      exact propext ⟨fun hij => f.injective hij, fun hij => congrArg f hij⟩
    · funext τ
      show Y.color (Str.idx τ (tupleMap (f : Ω → Ω') x)) = X.color (Str.idx τ x)
      have hcomm : Str.idx τ (tupleMap (f : Ω → Ω') x)
          = tupleMap (f : Ω → Ω') (Str.idx τ x) := rfl
      rw [hcomm, h]

end F2

/-! ### Proposition 5.1.11 (Skeleton 1) -/

/-- Proposition 5.1.11 (Skeleton 1).  "For `1 ≤ ℓ ≤ k`, the `ℓ`-skeleton `X^{(ℓ)}` of a
`k`-ary configuration `X` is an `ℓ`-ary configuration."

Paper's proof: "Let `x⃗, y⃗ ∈ Ω^ℓ` and assume `c^{(ℓ)}(x⃗) = c^{(ℓ)}(y⃗)`.  In other words
this means `c(pad(x⃗)) = c(pad(y⃗))`.  Therefore `ρ(pad(x⃗)) = ρ(pad(y⃗))`.  Restricting these
equivalence relations to `[ℓ]` we obtain `ρ(x⃗) = ρ(y⃗)`, verifying (i) in Def. 5.1.8.  Let
now `τ ∈ 𝔐_ℓ`.  To verify item (ii) we need to show that `c^{(ℓ)}(τ(x⃗)) = c^{(ℓ)}(τ(y⃗))`.
We know that `c(pad(x⃗)) = c(pad(y⃗))`.  Therefore, applying item (ii) to `X` we obtain that
`c((pad(τ))(pad(x⃗))) = c((pad(τ))(pad(y⃗)))`.  By Obs. 5.1.14 we infer that
`c(pad(τ(x⃗))) = c(pad(τ(y⃗)))`.  According to Def. 5.1.7, the left-hand side is equal to
`c^{(ℓ)}(τ(x⃗)) while the right-hand side is equal to `c^{(ℓ)}(τ(y⃗))`, as desired."

(The printed proof cites "Def. 5.4.1" for the last step; Def. 5.4.1 belongs to the
subsection marked "OLD — REMOVE THIS SUBSECTION", and the definition meant is the revised
Def. 5.1.7.  See the corrected paper.) -/
theorem skeleton_isConfiguration (h : X.IsConfiguration) (hl : 0 < l) (hlk : l ≤ k) :
    (X.skeleton hl hlk).IsConfiguration where
  rho x y hxy i j := by
    -- `ρ(pad(x⃗)) = ρ(pad(y⃗))`, restricted to `[ℓ]`
    have hi : ((Fin.castLE hlk i : Fin k) : ℕ) < l := by simp [i.2]
    have hj : ((Fin.castLE hlk j : Fin k) : ℕ) < l := by simp [j.2]
    have hpad := h.rho _ _ hxy (Fin.castLE hlk i) (Fin.castLE hlk j)
    rw [Str.pad_apply_of_lt hl x hi, Str.pad_apply_of_lt hl x hj,
      Str.pad_apply_of_lt hl y hi, Str.pad_apply_of_lt hl y hj] at hpad
    have ei : (⟨((Fin.castLE hlk i : Fin k) : ℕ), hi⟩ : Fin l) = i := Fin.ext (by simp)
    have ej : (⟨((Fin.castLE hlk j : Fin k) : ℕ), hj⟩ : Fin l) = j := Fin.ext (by simp)
    rwa [ei, ej] at hpad
  idx x y τ hxy := by
    have hpad := h.idx _ _ (Str.padMap hl hlk τ) hxy
    rw [Str.idx_padMap_pad hl hlk τ x, Str.idx_padMap_pad hl hlk τ y] at hpad
    exact hpad

/-! ### Proposition 5.1.15 (Induced subconfiguration) -/

/-- Proposition 5.1.15 (Induced subconfiguration).  "For `Φ ⊆ Ω`, the induced substructure
`X[Φ]` of a `k`-ary configuration is a `k`-ary configuration."

Paper's proof: "We only need to observe that if `supp(x⃗) ⊆ Φ` then `supp(τ(x⃗)) ⊆ Φ` by
Eq. (28)."  (The printed text has `supp(x⃗) ⊆ Φ` on both sides; the point of the proof is
Eq. (28), `supp(τ(x⃗)) ⊆ supp(x⃗)`.)  In our encoding a string over `Φ` is literally a
string of elements of `Φ`, and `Str.supp_idx_subset` is Eq. (28). -/
theorem induced_isConfiguration (h : X.IsConfiguration) (Φ : Set Ω) :
    (X.induced Φ).IsConfiguration where
  rho x y hxy i j := by
    have := h.rho _ _ hxy i j
    simpa [tupleMap, Subtype.ext_iff] using this
  idx x y τ hxy := by
    have hcomm : ∀ z : Str Φ k,
        tupleMap (Subtype.val) (Str.idx τ z) = Str.idx τ (tupleMap (Subtype.val) z) := by
      intro z; exact (Str.idx_tupleMap Subtype.val τ z).symm
    simp only [induced_color, hcomm]
    exact h.idx _ _ τ hxy

/-! ### Axiom (ii) of Def. 5.1.8 across two lengths -/

/-- Axiom (ii) of Def. 5.1.8 for the extended coloring of §5.1.4 and an index map
`σ : [ℓ] → [ℓ']` between two lengths `1 ≤ ℓ, ℓ' ≤ k`: if two strings of length `ℓ'` have
the same color, so do their images under `σ`.

Proof: `pad_{ℓ→k}(y⃗ ∘ σ) = idx τ (pad_{ℓ'→k}(y⃗))` for the index map
`τ(j) = σ(padIdx ℓ j) ∈ [ℓ'] ⊆ [k]`, so the statement is axiom (ii) of Def. 5.1.8 for
`τ ∈ 𝔐_k`. -/
theorem skeletonColor_comp (X : KAryPartStruct Ω C k) (h : X.IsConfiguration)
    {l l' : ℕ} (hl : 0 < l) (hlk : l ≤ k) (hl' : 0 < l') (hl'k : l' ≤ k)
    (σ : Fin l → Fin l') {y y' : Str Ω l'}
    (hc : X.skeletonColor hl' hl'k y = X.skeletonColor hl' hl'k y') :
    X.skeletonColor hl hlk (fun i => y (σ i))
      = X.skeletonColor hl hlk (fun i => y' (σ i)) := by
  set τ : Mon k := fun j => ⟨(σ (Str.padIdx l hl j) : ℕ),
    lt_of_lt_of_le (σ (Str.padIdx l hl j)).2 hl'k⟩ with hτ
  have key : ∀ z : Str Ω l',
      Str.pad hl k (fun i => z (σ i)) = Str.idx τ (Str.pad hl' k z) := by
    intro z
    funext j
    rw [Str.pad_eq, Str.idx_apply, Str.pad_eq]
    congr 1
    refine Fin.ext ?_
    have hlt : ((σ (Str.padIdx l hl j) : Fin l') : ℕ) < l' := (σ (Str.padIdx l hl j)).2
    rw [hτ]
    simp only [Str.padIdx]
    omega
  have hidx := h.idx _ _ τ hc
  show X.color (Str.pad hl k (fun i => y (σ i)))
      = X.color (Str.pad hl k (fun i => y' (σ i)))
  rw [key y, key y']
  exact hidx

end KAryPartStruct

end Babai
