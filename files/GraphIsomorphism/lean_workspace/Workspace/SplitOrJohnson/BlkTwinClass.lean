/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 9.7, Case 2: the twin equivalence classes of the neighborhood hypergraph, and the
canonical choice of the class `C`.
-/
import Workspace.SplitOrJohnson.BlockDesignCase

/-!
# §9.7, Case 2  The twin classes of `H`, and the class `C`

Version 2.5, lines 4252-4256.

> *"Case 2.  There is an `H`-twin equivalence class `C ⊆ V₂` of size `|C| ≥ n₂/2`."*

The branch condition is an existential, while everything Case 2 returns is built from `C`
and must therefore be carried by every morphism of the input category.  This file makes
`C` a function of the input, as far as that is possible.

* `Babai.BlkCaseObj.IsHTwin` (Def. 2.3.9 for `H`) is an **equivalence relation** on the
  blocks (`Babai.BlkCaseObj.isHTwin_refl`, `.isHTwin_symm`, `.isHTwin_trans`); the proof of
  transitivity is the conjugation identity `(A C) = (A B)(B C)(A B)` for transpositions.
* `Babai.BlkCaseObj.twinClass B` is the class of `B` and `Babai.BlkCaseObj.bigTwin` is the
  union of the classes of size `≥ n₂/2`.  Both are canonical
  (`Babai.BlkCaseObj.IsMorphOn.mem_bigTwin_iff`).
* Under Case 2 there is such a class.  Either it is **unique**, and then
  `Babai.BlkCaseObj.bigTwin` is it (`Babai.BlkCaseObj.bigTwin_spec`); or **two** classes of
  size exactly `n₂/2` exhaust `V₂`, and then `Babai.BlkCaseObj.bigTwin` is all of `V₂`
  (`Babai.BlkCaseObj.bigTwin_eq_blocks_iff`), the twin partition is an equipartition of
  `V₂` into classes of one common size `m = n₂/2` with `2 ≤ m < n₂`
  (`Babai.BlkCaseObj.tie_spec`), and Case 2 takes the equipartition exit instead of
  choosing a class.  See the entry on §9.7 Case 2 in the corrected paper.

The test that separates the two is `Babai.BlkCaseObj.bigTwin = blocks`, which is an
isomorphism invariant.
-/

namespace Babai

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

/-! ### Swapping two members of a family is the transposition -/

/-- `Babai.swapIn B B' S` is the image of `S` under the transposition of `B` and `B'`. -/
theorem swapIn_eq_swap_image {α : Type*} [DecidableEq α] (B B' : α) (S : Set α) :
    swapIn B B' S = (Equiv.swap B B') '' S := by
  ext A
  rw [mem_image_equiv (Equiv.swap B B') S A, Equiv.symm_swap]
  simp only [swapIn, Set.mem_setOf_eq, Equiv.swap_apply_def]
  by_cases hA : A = B
  · subst hA
    by_cases hAB : A = B'
    · subst hAB; simp
    · simp [hAB]
  · by_cases hA' : A = B'
    · subst hA'; simp [hA]
    · simp [hA, hA']

namespace BlkCaseObj

variable {s : Set Ω} {Case : (Set ↥s → Set ↥s → ℕ) → Set (Set ↥s) → Set (Set ↥s) → Prop}

/-! ### The twin relation of `H` is an equivalence relation -/

/-- Definition 2.3.9.  Every block is its own twin: the transposition of `B` with itself is
the identity. -/
theorem isHTwin_refl (X : BlkCaseObj s Case) (B : Set ↥s) : X.IsHTwin B B := by
  intro S hS
  have : swapIn B B S = S := by
    ext A
    simp only [swapIn, Set.mem_setOf_eq]
    constructor
    · rintro (⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨-, -, h⟩) <;> exact h
    · intro h
      by_cases hA : A = B
      · exact Or.inl ⟨hA, hA ▸ h⟩
      · exact Or.inr (Or.inr ⟨hA, hA, h⟩)
  rwa [this]

/-- Definition 2.3.9.  The twin relation is symmetric: the transposition of `B` and `B'` is
the transposition of `B'` and `B`. -/
theorem isHTwin_symm (X : BlkCaseObj s Case) {B B' : Set ↥s} (h : X.IsHTwin B B') :
    X.IsHTwin B' B := by
  intro S hS
  have : swapIn B' B S = swapIn B B' S := by
    ext A
    simp only [swapIn, Set.mem_setOf_eq]
    constructor
    · rintro (h1 | h1 | ⟨h1, h2, h3⟩)
      · exact Or.inr (Or.inl h1)
      · exact Or.inl h1
      · exact Or.inr (Or.inr ⟨h2, h1, h3⟩)
    · rintro (h1 | h1 | ⟨h1, h2, h3⟩)
      · exact Or.inr (Or.inl h1)
      · exact Or.inl h1
      · exact Or.inr (Or.inr ⟨h2, h1, h3⟩)
  rw [this]
  exact h S hS

open scoped Classical in
/-- Definition 2.3.9.  **The twin relation is transitive**, by the conjugation identity
`(A C) = (A B)(B C)(A B)` for transpositions: if the transpositions `(A B)` and `(B C)`
both carry hyperedges to hyperedges, so does their conjugate `(A C)`. -/
theorem isHTwin_trans (X : BlkCaseObj s Case) {A B C : Set ↥s} (hab : X.IsHTwin A B)
    (hbc : X.IsHTwin B C) : X.IsHTwin A C := by
  classical
  by_cases hAC : A = C
  · subst hAC; exact X.isHTwin_refl A
  by_cases hAB : A = B
  · subst hAB; exact hbc
  by_cases hBC : B = C
  · subst hBC; exact hab
  -- `A`, `B`, `C` are pairwise distinct
  intro S hS
  have hswap : Equiv.swap A C
      = (Equiv.swap A B) * (Equiv.swap B C) * (Equiv.swap A B)⁻¹ := by
    have h1 : (Equiv.swap A B) B = A := Equiv.swap_apply_right A B
    have h2 : (Equiv.swap A B) C = C :=
      Equiv.swap_apply_of_ne_of_ne (fun hc => hAC hc.symm) (fun hc => hBC hc.symm)
    have key := Equiv.swap_apply_apply (Equiv.swap A B) B C
    rw [h1, h2] at key
    exact key
  have hstep : swapIn A C S = swapIn A B (swapIn B C (swapIn A B S)) := by
    rw [swapIn_eq_swap_image, swapIn_eq_swap_image, swapIn_eq_swap_image,
      swapIn_eq_swap_image, hswap]
    rw [Equiv.swap_inv]
    ext y
    simp only [Set.mem_image, Equiv.Perm.mul_apply]
    constructor
    · rintro ⟨x, hx, rfl⟩; exact ⟨_, ⟨_, ⟨x, hx, rfl⟩, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨_, ⟨x, hx, rfl⟩, rfl⟩, rfl⟩; exact ⟨x, hx, rfl⟩
  rw [hstep]
  exact hab _ (hbc _ (hab _ hS))

/-! ### The twin classes -/

/-- §9.7, Case 2.  The `H`-twin equivalence class of a block. -/
def twinClass (X : BlkCaseObj s Case) (B : Set ↥s) : Set (Set ↥s) :=
  {B' | B' ∈ X.blocks ∧ X.IsHTwin B B'}

theorem twinClass_subset_blocks (X : BlkCaseObj s Case) (B : Set ↥s) :
    X.twinClass B ⊆ X.blocks := fun _ h => h.1

theorem mem_twinClass_self (X : BlkCaseObj s Case) {B : Set ↥s} (hB : B ∈ X.blocks) :
    B ∈ X.twinClass B := ⟨hB, X.isHTwin_refl B⟩

theorem twinClass_nonempty (X : BlkCaseObj s Case) {B : Set ↥s} (hB : B ∈ X.blocks) :
    (X.twinClass B).Nonempty := ⟨B, X.mem_twinClass_self hB⟩

theorem one_le_ncard_twinClass (X : BlkCaseObj s Case) {B : Set ↥s} (hB : B ∈ X.blocks) :
    1 ≤ (X.twinClass B).ncard :=
  (Set.ncard_pos (Set.toFinite _)).2 (X.twinClass_nonempty hB)

/-- The class of a twin of `B` is the class of `B`. -/
theorem twinClass_eq_of_isHTwin (X : BlkCaseObj s Case) {B B' : Set ↥s}
    (h : X.IsHTwin B B') : X.twinClass B' = X.twinClass B := by
  ext D
  exact ⟨fun hD => ⟨hD.1, X.isHTwin_trans h hD.2⟩,
    fun hD => ⟨hD.1, X.isHTwin_trans (X.isHTwin_symm h) hD.2⟩⟩

/-- Two blocks that are not twins have disjoint classes. -/
theorem twinClass_disjoint (X : BlkCaseObj s Case) {B B' : Set ↥s}
    (h : ¬ X.IsHTwin B B') : Disjoint (X.twinClass B) (X.twinClass B') := by
  rw [Set.disjoint_left]
  rintro D ⟨-, hD⟩ ⟨-, hD'⟩
  exact h (X.isHTwin_trans hD (X.isHTwin_symm hD'))

/-- §9.7, Case 2.  **The class `C`, as a function of the input**: the union of the
`H`-twin classes of size `≥ n₂/2`.  Under the branch condition of Case 2 there is such a
class; if it is unique this is it (`Babai.BlkCaseObj.bigTwin_spec`), and otherwise this is
all of `V₂` (`Babai.BlkCaseObj.bigTwin_eq_blocks_iff`). -/
def bigTwin (X : BlkCaseObj s Case) : Set (Set ↥s) :=
  {B | B ∈ X.blocks ∧ X.n₂ ≤ 2 * (X.twinClass B).ncard}

theorem bigTwin_subset_blocks (X : BlkCaseObj s Case) : X.bigTwin ⊆ X.blocks :=
  fun _ h => h.1

/-- The union of two disjoint sub-families of the blocks whose sizes add up to `n₂` is all
of `V₂`. -/
theorem eq_blocks_of_disjoint_of_ncard (X : BlkCaseObj s Case) {U V : Set (Set ↥s)}
    (hU : U ⊆ X.blocks) (hV : V ⊆ X.blocks) (hd : Disjoint U V)
    (hc : X.n₂ ≤ U.ncard + V.ncard) : U ∪ V = X.blocks := by
  have hfin : X.blocks.Finite := Set.toFinite _
  have hsub : U ∪ V ⊆ X.blocks := Set.union_subset hU hV
  have hun : (U ∪ V).ncard = U.ncard + V.ncard :=
    Set.ncard_union_eq hd (Set.toFinite _) (Set.toFinite _)
  refine (Set.eq_of_subset_of_ncard_le hsub ?_ hfin)
  rw [hun]; exact hc

/-- Two classes of size `≥ n₂/2` that are distinct exhaust `V₂`, and then every class has
size `≥ n₂/2`, so `Babai.BlkCaseObj.bigTwin` is all of `V₂`. -/
theorem bigTwin_eq_blocks_of_two (X : BlkCaseObj s Case) {B B' : Set ↥s}
    (hB : B ∈ X.blocks) (hB' : B' ∈ X.blocks) (hnt : ¬ X.IsHTwin B B')
    (hcB : X.n₂ ≤ 2 * (X.twinClass B).ncard)
    (hcB' : X.n₂ ≤ 2 * (X.twinClass B').ncard) :
    X.bigTwin = X.blocks := by
  have hd := X.twinClass_disjoint hnt
  have hsum : (X.twinClass B).ncard + (X.twinClass B').ncard ≤ X.n₂ := by
    have hun : ((X.twinClass B) ∪ (X.twinClass B')).ncard
        = (X.twinClass B).ncard + (X.twinClass B').ncard :=
      Set.ncard_union_eq hd (Set.toFinite _) (Set.toFinite _)
    rw [← hun]
    exact Set.ncard_le_ncard
      (Set.union_subset (X.twinClass_subset_blocks B) (X.twinClass_subset_blocks B'))
      (Set.toFinite _)
  have heq : (X.twinClass B).ncard + (X.twinClass B').ncard = X.n₂ := by omega
  have hcov : X.twinClass B ∪ X.twinClass B' = X.blocks :=
    X.eq_blocks_of_disjoint_of_ncard (X.twinClass_subset_blocks B)
      (X.twinClass_subset_blocks B') hd (by omega)
  refine Set.Subset.antisymm (X.bigTwin_subset_blocks) (fun D hD => ?_)
  refine ⟨hD, ?_⟩
  rcases (hcov ▸ hD : D ∈ X.twinClass B ∪ X.twinClass B') with h | h
  · rw [X.twinClass_eq_of_isHTwin h.2]; exact hcB
  · rw [X.twinClass_eq_of_isHTwin h.2]; exact hcB'

/-- §9.7, Case 2.  **`Babai.BlkCaseObj.bigTwin` is the class `C` when it is unique.**
Under the branch condition of Case 2, if `Babai.BlkCaseObj.bigTwin` is not all of `V₂` then
it is an `H`-twin equivalence class of size `≥ n₂/2`, that is, it satisfies word for word
the four clauses of `Babai.BlkCaseObj.IsCase2`. -/
theorem bigTwin_spec (X : BlkCaseObj s Case) (h2 : X.IsCase2)
    (hne : X.bigTwin ≠ X.blocks) :
    X.bigTwin ⊆ X.blocks ∧ X.n₂ ≤ 2 * X.bigTwin.ncard ∧
      (∀ B ∈ X.bigTwin, ∀ B' ∈ X.bigTwin, X.IsHTwin B B') ∧
      (∀ B ∈ X.bigTwin, ∀ B' ∈ X.blocks, X.IsHTwin B B' → B' ∈ X.bigTwin) := by
  obtain ⟨C, hCsub, hCcard, hCpair, hCmax⟩ := h2
  -- `C` is nonempty
  have hCne : C.Nonempty := by
    by_contra hcon
    rw [Set.not_nonempty_iff_eq_empty] at hcon
    rw [hcon, Set.ncard_empty] at hCcard
    have : X.blocks = ∅ := by
      have : X.blocks.ncard = 0 := by simpa [n₂] using hCcard
      exact (Set.ncard_eq_zero (Set.toFinite _)).1 this
    exact hne ((Set.eq_empty_of_subset_empty (this ▸ X.bigTwin_subset_blocks)).trans this.symm)
  obtain ⟨B₀, hB₀⟩ := hCne
  have hB₀b : B₀ ∈ X.blocks := hCsub hB₀
  -- `C` is the class of `B₀`
  have hCeq : X.twinClass B₀ = C := by
    refine Set.Subset.antisymm (fun D hD => hCmax B₀ hB₀ D hD.1 hD.2) (fun D hD => ?_)
    exact ⟨hCsub hD, hCpair B₀ hB₀ D hD⟩
  -- `C ⊆ bigTwin`
  have hCsubBig : C ⊆ X.bigTwin := by
    intro D hD
    refine ⟨hCsub hD, ?_⟩
    have : X.twinClass D = C := by
      rw [← hCeq]
      exact X.twinClass_eq_of_isHTwin (hCpair B₀ hB₀ D hD)
    rw [this]
    exact hCcard
  -- and there is nothing else, or `bigTwin` would be all of `V₂`
  have hBigsubC : X.bigTwin ⊆ C := by
    intro D hD
    by_contra hDC
    have hnt : ¬ X.IsHTwin B₀ D := fun hc => hDC (hCmax B₀ hB₀ D hD.1 hc)
    exact hne (X.bigTwin_eq_blocks_of_two hB₀b hD.1 hnt (by rw [hCeq]; exact hCcard) hD.2)
  have hBigC : X.bigTwin = C := Set.Subset.antisymm hBigsubC hCsubBig
  rw [hBigC]
  exact ⟨hCsub, hCcard, hCpair, hCmax⟩

/-- §9.7, Case 2, the tie.  If `Babai.BlkCaseObj.bigTwin` is all of `V₂` and `V₂` is not a
set of twins (Case 1 is excluded), then the `H`-twin classes are **two** classes of one
common size `m` with `2m = n₂`.  The equipartition of Cases 3a1 and 3b. -/
theorem tie_spec (X : BlkCaseObj s Case) (h1 : ¬ X.IsCase1)
    (heq : X.bigTwin = X.blocks) :
    ∃ m : ℕ, 1 ≤ m ∧ 2 * m = X.n₂ ∧ ∀ B ∈ X.blocks, (X.twinClass B).ncard = m := by
  -- Case 1 is excluded, so two blocks are not twins
  have hex : ∃ B ∈ X.blocks, ∃ B' ∈ X.blocks, ¬ X.IsHTwin B B' := by
    by_contra hcon
    push_neg at hcon
    exact h1 fun B hB B' hB' => hcon B hB B' hB'
  obtain ⟨B, hB, B', hB', hnt⟩ := hex
  have hcB : X.n₂ ≤ 2 * (X.twinClass B).ncard := (heq ▸ hB : B ∈ X.bigTwin).2
  have hcB' : X.n₂ ≤ 2 * (X.twinClass B').ncard := (heq ▸ hB' : B' ∈ X.bigTwin).2
  have hd := X.twinClass_disjoint hnt
  have hsum : (X.twinClass B).ncard + (X.twinClass B').ncard ≤ X.n₂ := by
    have hun : ((X.twinClass B) ∪ (X.twinClass B')).ncard
        = (X.twinClass B).ncard + (X.twinClass B').ncard :=
      Set.ncard_union_eq hd (Set.toFinite _) (Set.toFinite _)
    rw [← hun]
    exact Set.ncard_le_ncard
      (Set.union_subset (X.twinClass_subset_blocks B) (X.twinClass_subset_blocks B'))
      (Set.toFinite _)
  have hcov : X.twinClass B ∪ X.twinClass B' = X.blocks :=
    X.eq_blocks_of_disjoint_of_ncard (X.twinClass_subset_blocks B)
      (X.twinClass_subset_blocks B') hd (by omega)
  refine ⟨(X.twinClass B).ncard, X.one_le_ncard_twinClass hB, by omega, fun D hD => ?_⟩
  rcases (hcov ▸ hD : D ∈ X.twinClass B ∪ X.twinClass B') with h | h
  · rw [X.twinClass_eq_of_isHTwin h.2]
  · rw [X.twinClass_eq_of_isHTwin h.2]; omega

/-! ### The tie forces `n₂ ≥ 4`

The equipartition of `V₂` into the two twin classes is a hint only if its classes have at
least `2` blocks (`Babai.eqvConfig` has rank `3` only then).  Since the two classes have
`n₂/2` blocks each, what has to be excluded is `n₂ = 2`, and that follows from the standing
hypothesis `n₂ < n₁` of Theorem 9.2.2: the labels `X(v)` are distinct `d₁`-subsets of `V₂`
(`Babai.BlkCaseObj.label_injective`), so `n₁ ≤ C(n₂, d₁) ≤ 2` for `n₂ = 2`. -/

/-- §9.7, Case 2, the tie.  **The twin partition of `V₂` is an equipartition into classes
of one common size `m` with `2 ≤ m < n₂`** — the input of `Babai.eqvConfig`.  The bound
`2 ≤ m` uses `n₂ < n₁`, the standing hypothesis of Theorem 9.2.2. -/
theorem tie_spec' (X : BlkDesignObj s) (hlt : X.n₂ < X.n₁) (h1 : ¬ X.IsCase1)
    (heq : X.bigTwin = X.blocks) :
    ∃ m : ℕ, 2 ≤ m ∧ m < X.n₂ ∧ ∀ B ∈ X.blocks, (X.twinClass B).ncard = m := by
  obtain ⟨m, hm1, hm2, hmall⟩ := X.tie_spec h1 heq
  refine ⟨m, ?_, by omega, hmall⟩
  by_contra hcon
  have hm : m = 1 := by omega
  have hn₂ : X.n₂ = 2 := by omega
  have hch := X.n₁_le_choose
  rw [hn₂] at hch
  have hmid : Nat.choose 2 X.d₁ ≤ Nat.choose 2 (2 / 2) := Nat.choose_le_middle _ _
  norm_num at hmid
  omega

/-! ### Canonicity -/

end BlkCaseObj

namespace BlkCaseObj

variable {s t : Set Ω}
  {Cs : (Set ↥s → Set ↥s → ℕ) → Set (Set ↥s) → Set (Set ↥s) → Prop}
  {Ct : (Set ↥t → Set ↥t → ℕ) → Set (Set ↥t) → Set (Set ↥t) → Prop}
  {X : BlkCaseObj s Cs} {Y : BlkCaseObj t Ct} {φ : ↥s ≃ ↥t}

/-- The twin class of a block is carried to the twin class of its image. -/
theorem IsMorphOn.twinClass_eq (h : X.IsMorphOn Y φ) (B : Set ↥s) :
    Y.twinClass (φ '' B) = (fun A => φ '' A) '' X.twinClass B := by
  ext D
  constructor
  · rintro ⟨hDb, hDt⟩
    refine ⟨φ.symm '' D, ⟨?_, ?_⟩, Equiv.image_symm_image φ D⟩
    · have hb := h.blocks (φ.symm '' D); rw [Equiv.image_symm_image] at hb; exact hb.1 hDb
    · have := (h.isHTwin_iff B (φ.symm '' D)).1
        (by rwa [Equiv.image_symm_image])
      exact this
  · rintro ⟨A, ⟨hAb, hAt⟩, rfl⟩
    exact ⟨(h.blocks A).2 hAb, (h.isHTwin_iff B A).2 hAt⟩

theorem IsMorphOn.ncard_twinClass_eq (h : X.IsMorphOn Y φ) (B : Set ↥s) :
    (Y.twinClass (φ '' B)).ncard = (X.twinClass B).ncard := by
  rw [h.twinClass_eq B,
    Set.ncard_image_of_injective _ (Set.image_injective.2 φ.injective)]

/-- §9.7, Case 2.  **The class `C` is canonical**: a morphism carries
`Babai.BlkCaseObj.bigTwin` onto `Babai.BlkCaseObj.bigTwin`. -/
theorem IsMorphOn.mem_bigTwin_iff (h : X.IsMorphOn Y φ) (B : Set ↥s) :
    φ '' B ∈ Y.bigTwin ↔ B ∈ X.bigTwin := by
  show (φ '' B ∈ Y.blocks ∧ Y.n₂ ≤ 2 * (Y.twinClass (φ '' B)).ncard)
    ↔ (B ∈ X.blocks ∧ X.n₂ ≤ 2 * (X.twinClass B).ncard)
  rw [h.blocks B, h.ncard_twinClass_eq B, h.n₂_eq]

/-- §9.7, Case 2.  The class `C` is carried onto the class `C`, as a family of sets. -/
theorem IsMorphOn.bigTwin_image_eq (h : X.IsMorphOn Y φ) :
    Y.bigTwin = imgEquiv φ '' X.bigTwin := by
  ext D
  constructor
  · intro hD
    refine ⟨φ.symm '' D, ?_, Equiv.image_symm_image φ D⟩
    exact (h.mem_bigTwin_iff (φ.symm '' D)).1 (by rwa [Equiv.image_symm_image])
  · rintro ⟨A, hA, rfl⟩
    exact (h.mem_bigTwin_iff A).2 hA

/-- §9.7, Case 2.  *"for `v ∈ V₁` let `c'(v) = |X(v) ∩ C|`"*: the coloring of `V₁` by the
size of the hyperedge of `H'` at `v`. -/
noncomputable def localSize (X : BlkCaseObj s Cs) (x : ↥s) : ℕ := (X.nbhd x ∩ X.bigTwin).ncard

/-- §9.7, Case 2.  The coloring `c'` is canonical. -/
theorem IsMorphOn.localSize_eq (h : X.IsMorphOn Y φ) (x : ↥s) :
    Y.localSize (φ x) = X.localSize x := by
  have h1 : Y.nbhd (φ x) ∩ Y.bigTwin = imgEquiv φ '' (X.nbhd x ∩ X.bigTwin) := by
    rw [h.nbhd_eq x, h.bigTwin_image_eq, ← Set.image_inter (imgEquiv φ).injective]
  show (Y.nbhd (φ x) ∩ Y.bigTwin).ncard = _
  rw [h1, Set.ncard_image_of_injective _ (imgEquiv φ).injective]
  rfl

/-- §9.7, Case 2.  A `c'`-color class is carried onto a `c'`-color class. -/
theorem IsMorphOn.ncard_localSizeClass (h : X.IsMorphOn Y φ) (x : ↥s) :
    ({y | Y.part₁ y ∧ Y.localSize y = Y.localSize (φ x)}).ncard
      = ({y | X.part₁ y ∧ X.localSize y = X.localSize x}).ncard := by
  have himg : {y | Y.part₁ y ∧ Y.localSize y = Y.localSize (φ x)}
      = φ '' {y | X.part₁ y ∧ X.localSize y = X.localSize x} := by
    ext z
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨φ.symm z, ⟨?_, ?_⟩, by simp⟩
      · exact (h.part₁ (φ.symm z)).1 (by simpa using h1)
      · have hz := h.localSize_eq (φ.symm z)
        rw [Equiv.apply_symm_apply] at hz
        rw [← hz, h2, h.localSize_eq]
    · rintro ⟨y, ⟨h1, h2⟩, rfl⟩
      exact ⟨(h.part₁ y).2 h1, by rw [h.localSize_eq, h.localSize_eq, h2]⟩
  rw [himg, Set.ncard_image_of_injective _ φ.injective]

/-- §9.7, Case 2.  The tie test is an isomorphism invariant. -/
theorem IsMorphOn.bigTwin_eq_blocks_iff (h : X.IsMorphOn Y φ) :
    Y.bigTwin = Y.blocks ↔ X.bigTwin = X.blocks := by
  constructor
  · intro hY
    refine Set.Subset.antisymm X.bigTwin_subset_blocks (fun B hB => ?_)
    exact (h.mem_bigTwin_iff B).1 (hY ▸ (h.blocks B).2 hB)
  · intro hX
    refine Set.Subset.antisymm Y.bigTwin_subset_blocks (fun D hD => ?_)
    have hD' : φ.symm '' D ∈ X.blocks := by
      have hb := h.blocks (φ.symm '' D); rw [Equiv.image_symm_image] at hb; exact hb.1 hD
    have := (h.mem_bigTwin_iff (φ.symm '' D)).2 (hX ▸ hD')
    rwa [Equiv.image_symm_image] at this

end BlkCaseObj

end Babai
