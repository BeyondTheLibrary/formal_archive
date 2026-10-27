/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 11 (Algorithmic setup): all definitions.
-/
import Workspace.Luks.PrelimExtra
import Workspace.Prelim.Socle
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Section 11, definitions

## The translation between the paper and Lean

The paper acts on the **right**: `u^τ` is the image of the point `u` under `τ`, and the
product `στ` means "first `σ`, then `τ`".  Lean acts on the **left**.  Throughout the
formalization (see `Workspace/Prelim/PermGroups.lean`) the dictionary is

* the paper's `u^τ` is Lean's `τ u`;
* the paper's product `στ` is Lean's `τ * σ`;
* consequently the paper's **right** coset `Kσ = {κσ | κ ∈ K}` is Lean's **left**
  translate `σ • K = {σ * κ | κ ∈ K}` (`Babai.mem_perm_smul_set`).

The last point is used everywhere in Section 11 and is isolated in one lemma,
`Babai.mem_perm_smul_set`, below.
-/

namespace Babai

open MulAction Equiv Equiv.Perm
open scoped Pointwise

variable {Ω A : Type*}

/-! ### §11.1 The paper's right cosets -/

/-- The paper's right coset `Kσ = {κσ | κ ∈ K}` is, under the left/right translation
(`στ` in the paper is `τ * σ` in Lean), the left translate `σ • K` in Lean.  This one
lemma carries the whole convention. -/
theorem mem_perm_smul_set {σ τ : Equiv.Perm Ω} {K : Set (Equiv.Perm Ω)} :
    τ ∈ σ • K ↔ σ⁻¹ * τ ∈ K := by
  constructor
  · rintro ⟨κ, hκ, rfl⟩
    simpa using hκ
  · intro h
    exact ⟨σ⁻¹ * τ, h, by simp⟩

/-- The paper's right coset `Kσ`, spelled out. -/
theorem perm_smul_set_eq (σ : Equiv.Perm Ω) (K : Set (Equiv.Perm Ω)) :
    σ • K = {τ | ∃ κ ∈ K, τ = σ * κ} := by
  ext τ
  rw [mem_perm_smul_set]
  constructor
  · intro h; exact ⟨σ⁻¹ * τ, h, (mul_inv_cancel_left σ τ).symm⟩
  · rintro ⟨κ, hκ, rfl⟩; simpa using hκ

/-! ### §11.1 Strings -/

/-- §11.1, Eq. (55).

> For `τ ∈ S(Ω)` and `x : Ω → Σ` we define the string `x^τ` by setting
> `x^τ(u) = x(u^{τ⁻¹})` for all `u ∈ Ω`.  In other words, for all `u ∈ Ω` and
> `τ ∈ S(Ω)`, `x^τ(u^τ) = x(u)`.  (55)

Under the translation of the header, the paper's `x^τ` is `Babai.strAct x τ`, i.e.
`fun u => x (τ⁻¹ u)`. -/
def strAct (x : Ω → A) (τ : Equiv.Perm Ω) : Ω → A := fun u => x (τ⁻¹ u)

/-- §11.1, Eq. (55) in the form the paper displays it: `x^τ(u^τ) = x(u)`. -/
@[simp] theorem strAct_apply (x : Ω → A) (τ : Equiv.Perm Ω) (u : Ω) :
    strAct x τ (τ u) = x u := by
  simp [strAct]

@[simp] theorem strAct_apply' (x : Ω → A) (τ : Equiv.Perm Ω) (u : Ω) :
    strAct x τ u = x (τ⁻¹ u) := rfl

/-- §11.1, Eq. (56).

> For `K ⊆ S(Ω)` we say that `τ` is a `K`-isomorphism of strings `x` and `y` if `τ ∈ K`
> and `x^τ = y`.  Let `Iso_K(x,y)` denote the set of `K`-isomorphisms of `x` and `y`:
> `Iso_K(x,y) = {τ ∈ K | x^τ = y} = {τ ∈ K | (∀u ∈ Ω)(x(u) = y(u^τ))}`.

`K` is an arbitrary subset of `S(Ω)`, as Remark 11.1.1 asks. -/
def strIso (K : Set (Equiv.Perm Ω)) (x y : Ω → A) : Set (Equiv.Perm Ω) :=
  {τ ∈ K | strAct x τ = y}

/-- §11.1, Eq. (56).  "let `Aut_K(x) = Iso_K(x,x)` denote the set of
`K`-automorphisms of `x`." -/
def strAut (K : Set (Equiv.Perm Ω)) (x : Ω → A) : Set (Equiv.Perm Ω) := strIso K x x

/-- §11.1, Definition 11.1.3 (Window isomorphism), Eq. (58).

> Let `Δ ⊆ Ω` and `K ⊂ S(Ω)`.  Let
> `Iso^Δ_K(x,y) = {τ ∈ K | (∀u ∈ Δ)(x(u) = y(u^τ))}`.  (58)

`Δ` is the *window*.  As in Eq. (56), `K` and `Δ` are arbitrary subsets. -/
def wIso (Δ : Set Ω) (K : Set (Equiv.Perm Ω)) (x y : Ω → A) : Set (Equiv.Perm Ω) :=
  {τ ∈ K | ∀ u ∈ Δ, x u = y (τ u)}

/-- §11.1.  `Aut^Δ_K(x) = Iso^Δ_K(x,x)`, the window automorphisms (the paper uses the
notation `Aut^Δ_G(x)` in Remark 11.1.5 without redefining it). -/
def wAut (Δ : Set Ω) (K : Set (Equiv.Perm Ω)) (x : Ω → A) : Set (Equiv.Perm Ω) :=
  wIso Δ K x x

/-- §11.1, Remark 11.1.5 (i).  "`Aut^Δ_G(x)` is a subgroup of `G`", under the standing
assumption of Remark 11.1.5 that the window `Δ` is `G`-invariant. -/
def wAutSubgroup (G : Subgroup (Equiv.Perm Ω)) (Δ : Set Ω) (h : IsInvariant G Δ)
    (x : Ω → A) : Subgroup (Equiv.Perm Ω) where
  carrier := wAut Δ (G : Set (Equiv.Perm Ω)) x
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨mul_mem ha hb, fun u hu => ?_⟩
    have hbu : b u ∈ Δ := h.mem_of_mem hb hu
    calc x u = x (b u) := hb' u hu
      _ = x (a (b u)) := ha' _ hbu
      _ = x ((a * b) u) := rfl
  one_mem' := ⟨one_mem _, fun u _ => rfl⟩
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨inv_mem ha, fun u hu => ?_⟩
    have hau : a⁻¹ u ∈ Δ := h.mem_of_mem (inv_mem ha) hu
    have := ha' (a⁻¹ u) hau
    simpa using this.symm

@[simp] theorem coe_wAutSubgroup (G : Subgroup (Equiv.Perm Ω)) (Δ : Set Ω)
    (h : IsInvariant G Δ) (x : Ω → A) :
    (wAutSubgroup G Δ h x : Set (Equiv.Perm Ω)) = wAut Δ (G : Set (Equiv.Perm Ω)) x := rfl

/-! ### §11.1 Definition 11.1.2 (String Isomorphism Problem)

> **Definition 11.1.2** (String Isomorphism Problem).
> Input:  a set `Ω`, a finite alphabet `Σ`, two strings `x, y : Ω → Σ`, a permutation
>         group `G ≤ S(Ω)` (given by a list of generators)
> Output: the set `Iso_G(x,y)`.  If this set is nonempty, it is represented by a list of
>         generators of the group `Aut_G(x)` and a coset representative `σ ∈ Iso_G(x,y)`.

The input is a bundle of data; the output *specification* is the mathematical content,
namely that `Iso_G(x,y)` is either empty or the coset `Aut_G(x)σ` for any
`σ ∈ Iso_G(x,y)` (this is Remark 11.1.5 (ii) with `Δ = Ω`, proved as
`Babai.wIso_eq_smul_wAut`).  The representation by a list of generators and the cost are
not modelled; see the corrected paper. -/

/-- Definition 11.1.2 (String Isomorphism Problem): the input of the problem. -/
structure StringIsoInput (Ω A : Type*) where
  /-- The permutation group `G ≤ S(Ω)`. -/
  G : Subgroup (Equiv.Perm Ω)
  /-- The first string. -/
  x : Ω → A
  /-- The second string. -/
  y : Ω → A

/-- Definition 11.1.2 (String Isomorphism Problem): the output is the set
`Iso_G(x,y)`. -/
def StringIsoInput.output (I : StringIsoInput Ω A) : Set (Equiv.Perm Ω) :=
  strIso (I.G : Set (Equiv.Perm Ω)) I.x I.y

/-! ### §11.1 Definition 11.1.10 (Straight-line programs) -/

/-- Definition 11.1.10 (Straight-line program), §11.1.

> Given a group `G` by a list `S` of generators, a *straight-line program* of length `ℓ`
> in `G` is a sequence of length `ℓ` of elements of `G` such that each element in the
> sequence is either one of the generators or is a product of two elements earlier in the
> sequence or is the inverse of an element earlier in the sequence.

The length `ℓ` is `p.length`. -/
def IsStraightLineProgram {G : Type*} [Group G] (S : Set G) (p : List G) : Prop :=
  ∀ i : Fin p.length,
    p.get i ∈ S ∨
    (∃ j k : Fin p.length, (j : ℕ) < i ∧ (k : ℕ) < i ∧ p.get i = p.get j * p.get k) ∨
    (∃ j : Fin p.length, (j : ℕ) < i ∧ p.get i = (p.get j)⁻¹)

/-- Definition 11.1.10.  "We say that the straight-line program *computes* a set `T` of
elements if the elements of `T` appear in the sequence and are marked as belonging to
`T`."  (The marking carries no mathematical content beyond `T ⊆ {entries of p}`.) -/
def SLPComputes {G : Type*} [Group G] (p : List G) (T : Set G) : Prop :=
  T ⊆ {g | g ∈ p}

/-- Definition 11.1.10.  "A subgroup is computed if a set of generators of the subgroup
is computed." -/
def SLPComputesSubgroup {G : Type*} [Group G] (p : List G) (H : Subgroup G) : Prop :=
  ∃ T : Set G, SLPComputes p T ∧ Subgroup.closure T = H

/-- Definition 11.1.10.  "A coset is computed if the corresponding subgroup and a coset
representative are computed."  The coset is the paper's right coset `Hσ`, i.e. `σ • H`
in Lean (see `Babai.mem_perm_smul_set`). -/
def SLPComputesCoset {G : Type*} [Group G] (p : List G) (C : Set G) : Prop :=
  ∃ (H : Subgroup G) (σ : G), SLPComputesSubgroup p H ∧ SLPComputes p {σ} ∧
    C = σ • (H : Set G)

/-! ### §11.1 `G`-invariant partitions of a window -/

/-- Theorem 11.1.9: "let `{B₁,…,B_m}` be a `G`-invariant partition of `Δ`".

This is the `G`-invariant partition of §2.2.1 (`Babai.IsInvariantPartition`) with the
`G`-invariant subset `Δ` in place of `Ω`:

> A `G`-invariant partition of `Ω` is a partition `{B₁,…,B_m}` where the `Bᵢ` are
> nonempty, pairwise disjoint subsets of which the union is `Ω` such that `G` permutes
> these subsets. -/
structure IsInvariantPartitionOn {Ω : Type*} (G : Subgroup (Equiv.Perm Ω)) (Δ : Set Ω)
    (ℬ : Set (Set Ω)) : Prop where
  /-- "the `Bᵢ` are nonempty" -/
  nonempty : ∀ B ∈ ℬ, B.Nonempty
  /-- "pairwise disjoint subsets" -/
  pairwiseDisjoint : ∀ B ∈ ℬ, ∀ B' ∈ ℬ, B ≠ B' → Disjoint B B'
  /-- "of which the union is `Δ`" -/
  covers : ⋃₀ ℬ = Δ
  /-- "such that `G` permutes these subsets" -/
  permutes : ∀ σ ∈ G, ∀ B ∈ ℬ, (σ : Equiv.Perm Ω) '' B ∈ ℬ

/-- A system of imprimitivity on `Δ` is in particular a `G`-invariant partition of `Δ`
(it asks in addition that `G` be transitive on the blocks). -/
theorem IsSystemOfImprimitivity.isInvariantPartitionOn {Ω : Type*}
    {G : Subgroup (Equiv.Perm Ω)} {Δ : Set Ω} {ℬ : Set (Set Ω)}
    (h : IsSystemOfImprimitivity G Δ ℬ) : IsInvariantPartitionOn G Δ ℬ :=
  ⟨h.nonempty, h.pairwiseDisjoint, h.covers, h.permutes⟩

/-! ### §11.2 Minimal systems of imprimitivity

§11.2 (and §11.3, §1.2.1, §16.1) use *minimal* systems of imprimitivity, which version 2.5
defines only in passing, inside the sentence after the proof of Theorem 11.1.9:

> Luks applied this reduction with great effect to minimal systems of imprimitivity
> (systems with at least two blocks that cannot be made coarser, i. e., the blocks are
> maximal) so `Ḡ` is a primitive group.

This is *not* the "maximal system of imprimitivity" of §2.2.1
(`Babai.IsMaximalSystemOfImprimitivity`, blocks minimal), which version 2.5 never uses
again.

The notion itself is `Babai.IsMinimalSystemOfImprimitivity`, in
`Workspace/Prelim/PermGroups.lean` (Sec. 10 uses it too, in Theorem 10.5.1 (g)).

### §11.2 The socle

> The socle `Soc(G)` of the group `G` is defined as the product of its minimal normal
> subgroups.

This repeats Definition 10.2.1, so the notions are the shared `Babai.IsMinimalNormal` and
`Babai.socle` of `Workspace/Prelim/Socle.lean`. -/

/-! ### §11.2 The wreath product in its product action

Definition 11.2.2 uses `S_k^(t) ≀ S_s` in its **product action** on
`(Ω choose t)^s`.  We spell the action out: the pair `(h, π)` with `h : Fin s → S(Γ)` and
`π ∈ S(Fin s)` acts on `f : Fin s → Γ` by `(h,π)·f = fun i => h i (f (π⁻¹ i))`. -/

/-- The permutation of `Fin s → Γ` given by a tuple `h` of permutations of `Γ` and a
permutation `π` of the coordinates: the product action of the wreath product. -/
def wreathPerm {Γ : Type*} {s : ℕ} (h : Fin s → Equiv.Perm Γ) (π : Equiv.Perm (Fin s)) :
    Equiv.Perm (Fin s → Γ) where
  toFun f := fun i => h i (f (π⁻¹ i))
  invFun f := fun i => (h (π i))⁻¹ (f (π i))
  left_inv := by intro f; funext i; simp
  right_inv := by intro f; funext i; simp

@[simp] theorem wreathPerm_apply {Γ : Type*} {s : ℕ} (h : Fin s → Equiv.Perm Γ)
    (π : Equiv.Perm (Fin s)) (f : Fin s → Γ) (i : Fin s) :
    wreathPerm h π f i = h i (f (π⁻¹ i)) := rfl

/-- §11.2, Definition 11.2.2.  The wreath product `H ≀ S_s` in its **product action** on
`Fin s → Γ`, for `H ≤ S(Γ)`. -/
def wreathProduct {Γ : Type*} (H : Subgroup (Equiv.Perm Γ)) (s : ℕ) :
    Subgroup (Equiv.Perm (Fin s → Γ)) where
  carrier := {w | ∃ (h : Fin s → Equiv.Perm Γ) (π : Equiv.Perm (Fin s)),
    (∀ i, h i ∈ H) ∧ w = wreathPerm h π}
  mul_mem' := by
    rintro a b ⟨h, π, hh, rfl⟩ ⟨h', π', hh', rfl⟩
    refine ⟨fun i => h i * h' (π⁻¹ i), π * π', fun i => mul_mem (hh i) (hh' _), ?_⟩
    ext f i
    simp [Equiv.Perm.mul_apply]
  one_mem' := ⟨fun _ => 1, 1, fun _ => one_mem _, by ext f i; simp⟩
  inv_mem' := by
    rintro a ⟨h, π, hh, rfl⟩
    refine ⟨fun i => (h (π i))⁻¹, π⁻¹, fun i => inv_mem (hh _), ?_⟩
    ext f i
    simp [Equiv.Perm.inv_def, wreathPerm]

/-- §11.2, Definition 11.2.2.  The base group `H^s` of the wreath product in its product
action: the coordinatewise action, with the coordinates not permuted. -/
def basePower {Γ : Type*} (H : Subgroup (Equiv.Perm Γ)) (s : ℕ) :
    Subgroup (Equiv.Perm (Fin s → Γ)) where
  carrier := {w | ∃ h : Fin s → Equiv.Perm Γ, (∀ i, h i ∈ H) ∧ w = wreathPerm h 1}
  mul_mem' := by
    rintro a b ⟨h, hh, rfl⟩ ⟨h', hh', rfl⟩
    refine ⟨fun i => h i * h' i, fun i => mul_mem (hh i) (hh' i), ?_⟩
    ext f i
    simp [Equiv.Perm.mul_apply]
  one_mem' := ⟨fun _ => 1, fun _ => one_mem _, by ext f i; simp⟩
  inv_mem' := by
    rintro a ⟨h, hh, rfl⟩
    refine ⟨fun i => (h i)⁻¹, fun i => inv_mem (hh i), ?_⟩
    ext f i
    simp [Equiv.Perm.inv_def, wreathPerm]

theorem basePower_le_wreathProduct {Γ : Type*} (H : Subgroup (Equiv.Perm Γ)) (s : ℕ) :
    basePower H s ≤ wreathProduct H s := by
  rintro a ⟨h, hh, rfl⟩
  exact ⟨h, 1, hh, rfl⟩

/-! ### §11.2 Definition 11.2.2 (Cameron groups) -/

/-- §11.2, Definition 11.2.2.  The socle data of a Cameron group: "the socle of `G` is
isomorphic to `A_k^s`, … moreover the induced action `G → S_s` on the direct factors of
the socle is transitive."

We record the direct factors `R 0, …, R (s-1)` explicitly: they are independent, pairwise
commuting subgroups whose supremum is the socle (so the socle is their internal direct
product, hence isomorphic to `A_k^s` by `factor_iso`), and `G` permutes them by
conjugation, transitively. -/
structure IsSocleFactorization {s : ℕ} (G : Type*) [Group G] (R : Fin s → Subgroup G)
    (k : ℕ) : Prop where
  /-- The socle is the product of the `R i`. -/
  socle_eq : socle G = ⨆ i, R i
  /-- The product is direct. -/
  indep : iSupIndep R
  /-- The product is direct. -/
  commutes : ∀ i j, i ≠ j → ∀ a ∈ R i, ∀ b ∈ R j, Commute a b
  /-- "the socle of `G` is isomorphic to `A_k^s`": each direct factor is `A_k`. -/
  factor_iso : ∀ i, Nonempty (R i ≃* alternatingGroup (Fin k))
  /-- `G` acts on the set of direct factors by conjugation. -/
  conj_perm : ∀ g : G, ∀ i, ∃ j, (R i).map (MulAut.conj g).toMonoidHom = R j
  /-- "the induced action `G → S_s` on the direct factors of the socle is transitive". -/
  conj_transitive : ∀ i j, ∃ g : G, (R i).map (MulAut.conj g).toMonoidHom = R j

/-- §11.2, **Definition 11.2.2**.

> `G ≤ S_n` is a *Cameron group* with parameters `s, t ≥ 1` and `k ≥ max(2t, 5)` if for
> some `s, t ≥ 1` and `k > 2t` we have `n = (k choose t)^s`, the socle of `G` is
> isomorphic to `A_k^s`, and `(A_k^(t))^s ≤ G ≤ S_k^(t) ≀ S_s` (wreath product, product
> action), moreover the induced action `G → S_s` on the direct factors of the socle is
> transitive.

Transcribed literally, including the two overlapping conditions on `k`: the paper states
both `k ≥ max(2t,5)` and `k > 2t` (together they say `k ≥ 5` and `k > 2t`, so one of the
two halves of `k ≥ max(2t,5)` is redundant).  We keep both, as printed.

The containments `(A_k^(t))^s ≤ G ≤ S_k^(t) ≀ S_s` identify the domain `Ω` (of size
`n = (k choose t)^s`) with `(Fin k choose t)^s`; the identification is the bijection `e`. -/
def IsCameronGroup [Fintype Ω] (G : Subgroup (Equiv.Perm Ω)) (s t k : ℕ) : Prop :=
  1 ≤ s ∧ 1 ≤ t ∧ max (2 * t) 5 ≤ k ∧ 2 * t < k ∧
    Fintype.card Ω = (k.choose t) ^ s ∧
    (∃ R : Fin s → Subgroup G, IsSocleFactorization G R k) ∧
    (∃ e : Ω ≃ (Fin s → binom (Fin k) t),
      basePower (JohnsonA k t) s ≤ G.map (Equiv.permCongrHom e).toMonoidHom ∧
      G.map (Equiv.permCongrHom e).toMonoidHom ≤ wreathProduct (JohnsonS k t) s)

/-! ### §11.2, §11.4 Acting as a Johnson group on a system of blocks -/

/-- "`G` acts on `ℬ` as the Johnson group `A_k^(t)`": the image `G^ℬ` of the block action
is, after identifying `ℬ` with `Fin k choose t`, literally the Johnson group `A_k^(t)`. -/
def ActsAsJohnsonA {Ω : Type*} (G : Subgroup (Equiv.Perm Ω)) (ℬ : Set (Set Ω))
    (hperm : ∀ σ ∈ G, ∀ B ∈ ℬ, (σ : Equiv.Perm Ω) '' B ∈ ℬ) (k t : ℕ) : Prop :=
  ∃ e : ℬ ≃ binom (Fin k) t,
    (onBlocks G ℬ hperm).map (Equiv.permCongrHom e).toMonoidHom = JohnsonA k t

/-- "`G` acts on `ℬ` as the Johnson group `S_k^(t)`". -/
def ActsAsJohnsonS {Ω : Type*} (G : Subgroup (Equiv.Perm Ω)) (ℬ : Set (Set Ω))
    (hperm : ∀ σ ∈ G, ∀ B ∈ ℬ, (σ : Equiv.Perm Ω) '' B ∈ ℬ) (k t : ℕ) : Prop :=
  ∃ e : ℬ ≃ binom (Fin k) t,
    (onBlocks G ℬ hperm).map (Equiv.permCongrHom e).toMonoidHom = JohnsonS k t

/-- §11.4, **Definition 11.4.1**.

> We refer to `(G, ℬ)` as the *Johnson case* if `G` is a transitive group with a system
> `ℬ` of imprimitivity such that `G` acts on `ℬ` as a Johnson group `S_k^(t)` or
> `A_k^(t)`.  We refer to `k` as the *Johnson parameter*.

`k` is the Johnson parameter. -/
structure IsJohnsonCase {Ω : Type*} (G : Subgroup (Equiv.Perm Ω)) (ℬ : Set (Set Ω))
    (k t : ℕ) : Prop where
  /-- The Johnson group range of §2.2.1: `1 ≤ t`. -/
  t_pos : 1 ≤ t
  /-- The Johnson group range of §2.2.1: `t ≤ k/2`. -/
  two_mul_t_le : 2 * t ≤ k
  /-- "`G` is a transitive group" (the paper's transitivity: exactly one orbit). -/
  transitive : IsTransitive G
  /-- "with a system `ℬ` of imprimitivity". -/
  system : IsSystemOfImprimitivity G Set.univ ℬ
  /-- "such that `G` acts on `ℬ` as a Johnson group `S_k^(t)` or `A_k^(t)`". -/
  johnson : ActsAsJohnsonS G ℬ system.permutes k t ∨ ActsAsJohnsonA G ℬ system.permutes k t

/-- Definition 11.4.1 inherits the parameter range of Johnson groups from §2.2.1.
In particular, a Johnson case cannot have `k = t = 0`. -/
theorem IsJohnsonCase.parameter_bounds {Ω : Type*} {G : Subgroup (Equiv.Perm Ω)}
    {ℬ : Set (Set Ω)} {k t : ℕ} (h : IsJohnsonCase G ℬ k t) :
    1 ≤ t ∧ 2 * t ≤ k :=
  ⟨h.t_pos, h.two_mul_t_le⟩

end Babai
