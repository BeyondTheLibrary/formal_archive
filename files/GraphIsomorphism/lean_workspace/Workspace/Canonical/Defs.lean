/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 14: the objects Procedure Align (Sec. 14.1) works with.
-/
import Workspace.TopAction.Align
import Workspace.ColoredPartitions.Tuples

/-!
# §14 The canonical structures embedded in `Γ`

Section 14 studies the effect of a canonical structure `X(z)` on `Γ`, attached to the
input string `z`, on the String Isomorphism problem for a transitive `G ≤ S(Ω)` with a
giant representation `ϕ : G → S(Γ)`.

> Both our group-theoretic partitioning algorithm (AggregateCertificates, Theorem 13.2.1)
> and our combinatorial partitioning algorithm (the Extended Design Lemma, Theorem 9.2.3)
> produce a canonical coloring of `Γ` with an additional canonical structure on some of
> the color classes.  The additional structure can be an equipartition or a Johnson
> scheme.

This file fixes the vocabulary.

* `Babai.ColStruct`: a structure on `Γ` of the kind Procedure Align aligns — a vertex
  coloring of `Γ` (line 4: *"Each of our structures has an underlying coloring — possibly
  trivial"*) together with a coloring of the ordered pairs, which is where the additional
  structure on a color class sits: an equipartition
  (`Babai.ColStruct.IsEquipartitionOn`) or a
  Johnson scheme (`Babai.ColStruct.IsJohnsonOn`, whose pair color is `|S ∖ T|`,
  Def. 3.2.13).
  `S(Γ)` acts on `ColStruct Γ κ` in the obvious way.
* `Babai.IsCanonicalStructure`: canonicity of `z ↦ X(z)` with respect to `ϕ`, for an
  arbitrary `S(Γ)`-set of structures.  It generalizes `Babai.IsCanonicalColoring`
  (`Babai.isCanonicalColoring_iff`).
* `Babai.structIso`, `Babai.structAut`: `Iso_K(X, Y)` and `Aut(X)` for structures.
* `Babai.preimageSubgroup`: `ϕ⁻¹(H) ≤ S(Ω)`, the group of line 2 (iv) and of line 9.
* `Babai.PhiOf`, `Babai.omegaOf`: the sets `Φ(A) = (A choose t)` and
  `Ω(A) = ⋃_{T ∈ Φ(A)} B_T` of line 4, described through the labels `T(u)` of
  Theorem 10.5.1 (e).
* `Babai.tColor`, `Babai.omegaColor`: the coloring of `Φ` induced by a coloring of `Γ`
  (Lemma 7.2.1: *"the color of `T ∈ (Γ choose t)` is the vector `(|T ∩ Δᵢ|)ᵢ`"*), lifted
  to `Ω` through the standard blocks.
-/

universe u v w

namespace Babai

open MulAction Equiv Equiv.Perm
open scoped Pointwise

/-! ### Structures on `Γ` and the action of `S(Γ)` -/

/-- §14.  A *structure on `Γ`* of the kind Procedure Align aligns: a vertex coloring of
`Γ` — the coloring `(Δ₁, …, Δ_k)` of line 4, *"Each of our structures has an underlying
coloring – possibly trivial"* — together with a coloring of the ordered pairs, which
carries the additional structure on a color class: an equipartition (the equivalence
relation of line 7 (A)) or a Johnson scheme (line 7 (B); by Def. 3.2.13 the color of the
pair `(S, T)` of `t*`-subsets is `|S ∖ T|`). -/
@[ext] structure ColStruct (Γ : Type u) (κ : Type v) where
  /-- The underlying coloring of `Γ`. -/
  vcol : Γ → κ
  /-- The additional structure, as a coloring of the ordered pairs. -/
  ecol : Γ → Γ → ℕ

namespace ColStruct

variable {Γ : Type u} {κ : Type v}

instance : MulAction (Equiv.Perm Γ) (ColStruct Γ κ) where
  smul α X := ⟨fun γ => X.vcol (α⁻¹ γ), fun γ δ => X.ecol (α⁻¹ γ) (α⁻¹ δ)⟩
  one_smul X := by ext γ δ <;> rfl
  mul_smul α β X := by
    ext γ δ
    · show X.vcol ((α * β)⁻¹ γ) = X.vcol (β⁻¹ (α⁻¹ γ))
      simp [mul_inv_rev]
    · show X.ecol ((α * β)⁻¹ γ) ((α * β)⁻¹ δ) = X.ecol (β⁻¹ (α⁻¹ γ)) (β⁻¹ (α⁻¹ δ))
      simp [mul_inv_rev]

@[simp] theorem smul_vcol (α : Equiv.Perm Γ) (X : ColStruct Γ κ) (γ : Γ) :
    (α • X).vcol γ = X.vcol (α⁻¹ γ) := rfl

@[simp] theorem smul_ecol (α : Equiv.Perm Γ) (X : ColStruct Γ κ) (γ δ : Γ) :
    (α • X).ecol γ δ = X.ecol (α⁻¹ γ) (α⁻¹ δ) := rfl

end ColStruct

/-! ### Isomorphisms and automorphisms of structures -/

variable {Γ : Type*} {𝒳 : Type*} [MulAction (Equiv.Perm Γ) 𝒳]

/-- `Iso_K(X, Y)`, the set of isomorphisms of the structures `X` and `Y` inside
`K ⊆ S(Γ)`.  Procedure Align, line 2 (i), asks for an element of `Iso_{G^ϕ}(X(x), X(y))`. -/
def structIso (K : Set (Equiv.Perm Γ)) (X Y : 𝒳) : Set (Equiv.Perm Γ) :=
  {α ∈ K | α • X = Y}

/-- `Aut(X) ≤ S(Γ)`, the automorphism group of the structure `X` (line 2 (iv): the group
`G₁ = ϕ⁻¹(Aut(X(x)))`). -/
def structAut (X : 𝒳) : Subgroup (Equiv.Perm Γ) := stabilizer (Equiv.Perm Γ) X

theorem mem_structAut {X : 𝒳} {α : Equiv.Perm Γ} : α ∈ structAut X ↔ α • X = X :=
  mem_stabilizer_iff

theorem mem_structIso {K : Set (Equiv.Perm Γ)} {X Y : 𝒳} {α : Equiv.Perm Γ} :
    α ∈ structIso K X Y ↔ α ∈ K ∧ α • X = Y := Iff.rfl

/-! ### Canonicity -/

variable {Ω : Type u} {A : Type v} {G : Subgroup (Equiv.Perm Ω)}

/-- §14.  The assignment `z ↦ X(z)` of a structure on `Γ` to a string on `Ω` is
*canonical* with respect to the representation `ϕ : G → S(Γ)` when a `G`-shift of the
string shifts the structure by the corresponding permutation of `Γ`:
`X(z^σ) = X(z)^{σ^ϕ}`.

This is the property Procedure Align uses, and it is `Babai.IsCanonicalColoring`
(`Workspace/TopAction/Align.lean`) written for an arbitrary `S(Γ)`-set of structures; see
`Babai.isCanonicalColoring_iff`. -/
def IsCanonicalStructure (ϕ : G →* Equiv.Perm Γ) (X : (Ω → A) → 𝒳) : Prop :=
  ∀ (z : Ω → A) (σ : G), X (strAct z (σ : Equiv.Perm Ω)) = ϕ σ • X z

/-- The coloring notion of `Workspace/TopAction/Align.lean` is the special case of
`Babai.IsCanonicalStructure` for a structure with trivial pair coloring. -/
theorem isCanonicalColoring_iff {κ : Type v} (ϕ : G →* Equiv.Perm Γ)
    (col : (Ω → A) → Γ → κ) :
    IsCanonicalColoring ϕ col ↔
      IsCanonicalStructure ϕ (fun z => (⟨col z, fun _ _ => 0⟩ : ColStruct Γ κ)) := by
  constructor
  · intro h z σ
    ext γ δ
    · show col (strAct z (σ : Equiv.Perm Ω)) γ = col z ((ϕ σ)⁻¹ γ)
      have := h z σ ((ϕ σ)⁻¹ γ)
      rwa [show (ϕ σ) ((ϕ σ)⁻¹ γ) = γ from by simp] at this
    · rfl
  · intro h z σ γ
    have := congrArg (fun Y : ColStruct Γ κ => Y.vcol (ϕ σ γ)) (h z σ)
    simpa using this

/-! ### `ϕ⁻¹(H)` -/

/-- `ϕ⁻¹(H)`, a subgroup of `S(Ω)`: the group `G₁ = ϕ⁻¹(Aut(X(x)))` of Procedure Align,
line 2 (iv), and the group `G* = ϕ⁻¹(H)` of line 9. -/
def preimageSubgroup (ϕ : G →* Equiv.Perm Γ) (H : Subgroup (Equiv.Perm Γ)) :
    Subgroup (Equiv.Perm Ω) :=
  (H.comap ϕ).map G.subtype

theorem mem_preimageSubgroup {ϕ : G →* Equiv.Perm Γ} {H : Subgroup (Equiv.Perm Γ)}
    {τ : Equiv.Perm Ω} :
    τ ∈ preimageSubgroup ϕ H ↔ ∃ h : τ ∈ G, ϕ ⟨τ, h⟩ ∈ H := by
  constructor
  · rintro ⟨⟨g, hg⟩, hmem, rfl⟩
    exact ⟨hg, hmem⟩
  · rintro ⟨h, hmem⟩
    exact ⟨⟨τ, h⟩, hmem, rfl⟩

theorem preimageSubgroup_le (ϕ : G →* Equiv.Perm Γ) (H : Subgroup (Equiv.Perm Γ)) :
    preimageSubgroup ϕ H ≤ G := Subgroup.map_subtype_le _

/-- `ϕ(ϕ⁻¹(H)) = H ∩ G^ϕ`: the image of the preimage is the intersection with the image.

This is the reason Eq. (70)'s second clause is stated here as `G₁^ϕ = Aut(X(x)) ∩ G^ϕ`
rather than in the printed form `G₁^ϕ = Aut(X(x))`; see `Workspace/Canonical/Align.lean`
and the corrected paper. -/
theorem homImage_preimageSubgroup (ϕ : G →* Equiv.Perm Γ) (H : Subgroup (Equiv.Perm Γ)) :
    homImage ϕ ((preimageSubgroup ϕ H : Subgroup (Equiv.Perm Ω)) : Set (Equiv.Perm Ω)) =
      (H : Set (Equiv.Perm Γ)) ∩ (ϕ.range : Set (Equiv.Perm Γ)) := by
  ext α
  constructor
  · rintro ⟨τ, hτ, hG, rfl⟩
    obtain ⟨hτG, hτH⟩ := mem_preimageSubgroup.1 hτ
    exact ⟨hτH, ⟨⟨τ, hG⟩, rfl⟩⟩
  · rintro ⟨hα, ⟨g, rfl⟩⟩
    refine ⟨(g : Equiv.Perm Ω), mem_preimageSubgroup.2 ⟨g.2, ?_⟩, g.2, rfl⟩
    exact hα

/-! ### The two kinds of additional structure -/

namespace ColStruct

variable {κ : Type v}

/-- Procedure Align, line 7 (A): the structure `X` gives a **nontrivial equipartition** of
the color class `Δ ⊆ Γ`.

The equivalence relation is `X.ecol γ δ = 0` (line 7 (A): *"let `Y` be this equivalence
relation on `Δ_j`"*); `Γ*` is its set of blocks.  *Nontrivial* means the blocks are
neither singletons nor all of `Δ`; *equipartition* means they all have the same size.  The
size is stated as `b`, so `|Γ*| · b = |Δ|`. -/
structure IsEquipartitionOn (X : ColStruct Γ κ) (Δ : Set Γ) (b : ℕ) : Prop where
  /-- The relation is reflexive on `Δ`. -/
  refl : ∀ γ ∈ Δ, X.ecol γ γ = 0
  /-- The relation is symmetric on `Δ`. -/
  symm : ∀ γ ∈ Δ, ∀ δ ∈ Δ, X.ecol γ δ = 0 → X.ecol δ γ = 0
  /-- The relation is transitive on `Δ`. -/
  trans : ∀ γ ∈ Δ, ∀ δ ∈ Δ, ∀ ε ∈ Δ, X.ecol γ δ = 0 → X.ecol δ ε = 0 → X.ecol γ ε = 0
  /-- The classes lie inside `Δ`. -/
  mem : ∀ γ ∈ Δ, ∀ δ, X.ecol γ δ = 0 → δ ∈ Δ
  /-- Every class has exactly `b` elements. -/
  card : ∀ γ ∈ Δ, {δ | X.ecol γ δ = 0}.ncard = b
  /-- Nontriviality: the classes are not singletons. -/
  nontrivial : 2 ≤ b
  /-- Nontriviality: there are at least two classes in `Δ`. -/
  two_blocks : ∃ γ ∈ Δ, ∃ δ ∈ Δ, X.ecol γ δ ≠ 0

/-- Align line 7 (A) rejects a single block, including the block on `Fin 2`. -/
theorem not_isEquipartitionOn_oneBlock :
    ¬ IsEquipartitionOn (⟨fun _ => (), fun _ _ => 0⟩ : ColStruct (Fin 2) Unit)
      Set.univ 2 := by
  rintro ⟨_, _, _, _, _, _, γ, _, δ, _, h⟩
  exact h rfl

/-- Align line 7 (A) rejects the empty color class at every block size. -/
theorem not_isEquipartitionOn_empty (X : ColStruct Γ κ) (b : ℕ) :
    ¬ IsEquipartitionOn X ∅ b := by
  intro h
  obtain ⟨γ, hγ, _⟩ := h.two_blocks
  exact hγ

/-- Procedure Align, line 7 (B): the color class `Δ ⊆ Γ` **is the vertex set of a Johnson
scheme** `J(m*, t*)` with `t* ≥ 2`.

*"identify `Δ_j` with `Δ_j = (Γ* choose t*)` where `|Γ*| = m*`"*: there is a bijection `e`
of `Δ` with the `t*`-subsets of `[m*]` under which the pair coloring of `X` is the Johnson
coloring `|S ∖ T|` of Def. 3.2.13.  The parameter constraints of Def. 3.2.9 are `t* ≥ 2`
and `m* ≥ 2t* + 1`. -/
structure IsJohnsonOn (X : ColStruct Γ κ) (Δ : Set Γ) (ms ts : ℕ) : Prop where
  /-- `t* ≥ 2` (Def. 3.2.9; the degenerate `t* = 1` is the clique configuration). -/
  two_le : 2 ≤ ts
  /-- `m* ≥ 2t* + 1` (Def. 3.2.9). -/
  params : 2 * ts + 1 ≤ ms
  /-- The identification of `Δ` with `(Γ* choose t*)` carrying the pair coloring of `X`
  to the Johnson coloring. -/
  iso : ∃ e : Δ ≃ binom (Fin ms) ts,
    ∀ S T : Δ, X.ecol (S : Γ) (T : Γ) =
      (((e S : binom (Fin ms) ts) : Finset (Fin ms)) \
        ((e T : binom (Fin ms) ts) : Finset (Fin ms))).card

end ColStruct

variable {κ : Type v}

/-! ### `Φ(A)`, `Ω(A)`, and the induced colorings

Procedure Align, line 4:

> This coloring induces a canonical coloring of `Φ = (Γ choose t)` as described in
> Lemma 7.2.1; let `Φ₁, …, Φ_s` be the color classes.  This coloring in turn lifts to a
> canonical coloring of `Ω` with corresponding color classes `Ω₁, …, Ω_s` where
> `Ω_i = ⋃_{T ∈ Φ_i} B_T`.  For `A ⊆ Γ` recall the notation `Φ(A) = (A choose t)` and
> `Ω(A) = ⋃_{T ∈ Φ(A)} B_T`.

The standard blocks `B_T` are labelled by their common value `T(u)` of the label map of
Theorem 10.5.1 (e) (`Babai.Tpoint`), so a block is labelled inside `A` exactly when
`T(u) ⊆ A` for its points `u`; that is the label-free description used here. -/

/-- §14.1, line 4.  `Φ(A) = (A choose t)`, the `t`-subsets of `A ⊆ Γ`. -/
def PhiOf (A : Set Γ) (t : ℕ) : Set (Set Γ) := {T | T ⊆ A ∧ T.ncard = t}

/-- §14.1, line 4.  `Ω(A) = ⋃_{T ∈ Φ(A)} B_T`, the union of the standard blocks whose
label is a subset of `A`.  (This is the definition already used in §12, in the proof of
Cor. 12.0.10.) -/
def omegaOf {Ω : Type u} [Fintype Ω] [DecidableEq Ω] {m : ℕ}
    {G : Subgroup (Equiv.Perm Ω)} (ϕ : G →* Equiv.Perm (Fin m)) (C : Set (Fin m)) : Set Ω :=
  {u : Ω | Tpoint ϕ u ⊆ C}

theorem mem_omegaOf {Ω : Type u} [Fintype Ω] [DecidableEq Ω] {m : ℕ}
    {G : Subgroup (Equiv.Perm Ω)} {ϕ : G →* Equiv.Perm (Fin m)} {C : Set (Fin m)} {u : Ω} :
    u ∈ omegaOf ϕ C ↔ Tpoint ϕ u ⊆ C := Iff.rfl

/-- `Ω(A)` in the form of line 4: the points whose label lies in `Φ(A)`. -/
theorem omegaOf_eq_phiOf {Ω : Type u} [Fintype Ω] [DecidableEq Ω] {m : ℕ}
    {G : Subgroup (Equiv.Perm Ω)} (ϕ : G →* Equiv.Perm (Fin m)) (C : Set (Fin m)) :
    omegaOf ϕ C = {u : Ω | Tpoint ϕ u ∈ PhiOf C (tPoint ϕ u)} := by
  ext u
  exact ⟨fun h => ⟨h, rfl⟩, fun h => h.1⟩

/-- Lemma 7.2.1.  *"The color of `T ∈ (Γ choose t)` is the vector `(|T ∩ Δᵢ|)ᵢ`."*  Stated
for a set `T` rather than a `Finset`, so that it applies directly to the labels
`Babai.Tpoint`. -/
noncomputable def tColor (c : Γ → κ) (T : Set Γ) : κ → ℕ :=
  fun i => (T ∩ {γ | c γ = i}).ncard

/-- §14.1, line 4.  The coloring of `Ω` that the coloring `c` of `Γ` induces: the color of
`u ∈ Ω` is the color of the label `T(u)` of the standard block containing `u`. -/
noncomputable def omegaColor {Ω : Type u} [Fintype Ω] [DecidableEq Ω] {m : ℕ}
    {G : Subgroup (Equiv.Perm Ω)} (ϕ : G →* Equiv.Perm (Fin m)) (c : Fin m → κ) (u : Ω) :
    κ → ℕ :=
  tColor c (Tpoint ϕ u)

end Babai
