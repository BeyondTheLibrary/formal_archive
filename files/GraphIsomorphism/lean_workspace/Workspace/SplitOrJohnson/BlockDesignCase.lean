/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 9.7: the block design case, assembled as a reduction in the sense of §6.
-/
import Workspace.SplitOrJohnson.BlkCases
import Workspace.SplitOrJohnson.BlkDictionary2
import Workspace.SplitOrJohnson.BlockDesign
import Workspace.DesignLemma.Reduction
import Workspace.Functors.Ambient
import Workspace.Functors.Fibers

/-!
# §9.7  The block design case, as a reduction

`Babai.case_9_7` (at the end of this file; its categories and outcome are in
`Workspace/SplitOrJohnson/BlkCases.lean`) states the block design case in
the form of §6, *"at a multiplicative cost of `s` we can find a canonical …"*.  This file
assembles it from the four branches of §9.7.

The branches of §9.7 are

| Paper | Lean |
|---|---|
| Case 1, *"`V₂` is a set of twins in `H`"* | `Babai.BlkCaseObj.IsCase1` |
| Case 2, *"there is an `H`-twin equivalence class `C ⊆ V₂` of size `|C| ≥ n₂/2`"* | `Babai.BlkCaseObj.IsCase2` |
| Case 3a, *"`d₁ ≤ (7/3) log₂ n₁`"* | `Babai.BlkCaseObj.IsCase3a` (on `d' = min(d₁, n₂ − d₁)`) |
| Case 3b, *"`d₁ > (7/3) log₂ n₁`"* | its negation |

and the case distinction is exhaustive by construction: Case 3 of the paper, *"the relative
symmetry defect of `H` is `≥ 1/2`"*, is the negation of Case 2 (Def. 2.4.29: the symmetry
defect of `H` is `1 − (largest twin class)/n₂`, so it is `≥ 1/2` exactly when no twin class
`C` has `2|C| ≥ n₂`), and Case 1 is the special case of Case 2 in which the twin class is
all of `V₂`.

## The cost

The exponent of `Babai.case_9_7` is `7 (⌊log₂ n₁⌋ + 1)/3 + 2` (in `ℕ`, so with integer
division).  The four branches cost

* Case 1: nothing, cost `1`;
* Case 2: one call of Procedure Reduce-Part2-by-Color, cost `n₂`;
* Case 3a: the Design Lemma on the `d'`-ary structure `H` (or its bipartite complement),
  cost `n₂^{d'}` with `d' = min(d₁, n₂ − d₁) ≤ d₁`, and then Reduce-Part2-by-Color and
  (Case 3a2) §9.8, cost `n₂` each: `n₂^{d' + 2}`;
* Case 3b: the Design Lemma on the `t`-skeleton `H^{(t)}` with `t = ⌈(7/4) log₂ n₁⌉`, and
  the same two extra factors: `n₂^{t + 2}`.

`Babai.case_9_7_exp_3a` and `Babai.case_9_7_exp_3b` are the two arithmetic facts that make
the single exponent of `Babai.case_9_7` dominate all four: `d' ≤ 7(⌊log₂ n₁⌋+1)/3` in
Case 3a, and `t ≤ 7(⌊log₂ n₁⌋+1)/3` in Case 3b.
-/

namespace Babai

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

/-! ### The exponent of the cost

Two integer inequalities.  They are what says that the single exponent
`7 (⌊log₂ n₁⌋ + 1)/3 + 2` of `Babai.case_9_7` is at least the exponent of each of the four
branches of §9.7. -/

/-- `log₂ n < ⌊log₂ n⌋ + 1`, the only property of `Nat.log` used below. -/
theorem logb_two_lt_natLog_succ (n : ℕ) :
    Real.logb 2 (n : ℝ) < (Nat.log 2 n : ℝ) + 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simpa using (by norm_num : (0:ℝ) < 1)
  · have hlt : (n : ℝ) < (2 : ℝ) ^ ((Nat.log 2 n : ℝ) + 1) := by
      have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) n
      have : ((n : ℝ)) < ((2 ^ (Nat.log 2 n + 1) : ℕ) : ℝ) := by exact_mod_cast h
      rwa [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast (2:ℝ) (Nat.log 2 n + 1),
        Nat.cast_add, Nat.cast_one] at this
    exact (Real.logb_lt_iff_lt_rpow (by norm_num) (by exact_mod_cast hn)).2 hlt

/-- Case 3a of §9.7.  The branch condition *"`d₁ ≤ (7/3) log₂ n₁`"* bounds `d₁` by
`7(⌊log₂ n₁⌋ + 1)/3`, the exponent of `Babai.case_9_7` minus the two extra factors `n₂`.

From `log₂ n₁ < ⌊log₂ n₁⌋ + 1` one gets `3 d₁ ≤ 7(⌊log₂ n₁⌋ + 1)` over the reals, and both
sides are integers. -/
theorem case_9_7_exp_3a {n₁ d₁ : ℕ} (h : (d₁ : ℝ) ≤ 7 / 3 * Real.logb 2 (n₁ : ℝ)) :
    d₁ ≤ 7 * (Nat.log 2 n₁ + 1) / 3 := by
  have hlt := logb_two_lt_natLog_succ n₁
  have h3 : (3 * d₁ : ℝ) ≤ 7 * ((Nat.log 2 n₁ : ℝ) + 1) := by nlinarith
  have h3' : 3 * d₁ ≤ 7 * (Nat.log 2 n₁ + 1) := by exact_mod_cast h3
  omega

/-- Case 3b of §9.7.  The `t` of Case 3b, `t = ⌈(7/4) log₂ n₁⌉`, is at most
`7(⌊log₂ n₁⌋ + 1)/3`, the exponent of `Babai.case_9_7` minus the two extra factors `n₂`.

From `log₂ n₁ < ⌊log₂ n₁⌋ + 1 =: M` one gets `t ≤ ⌈(7/4)M⌉ = (7M + 3)/4`, and
`(7M + 3)/4 ≤ 7M/3` for every `M ≥ 1`. -/
theorem case_9_7_exp_3b (n₁ : ℕ) :
    ⌈7 / 4 * Real.logb 2 (n₁ : ℝ)⌉₊ ≤ 7 * (Nat.log 2 n₁ + 1) / 3 := by
  set M : ℕ := Nat.log 2 n₁ + 1 with hM
  have hlt := logb_two_lt_natLog_succ n₁
  have hle : 7 / 4 * Real.logb 2 (n₁ : ℝ) ≤ ((7 * M + 3) / 4 : ℕ) := by
    have h1 : 7 / 4 * Real.logb 2 (n₁ : ℝ) ≤ 7 / 4 * (M : ℝ) := by
      have : Real.logb 2 (n₁ : ℝ) ≤ (M : ℝ) := by
        rw [hM]; push_cast; linarith
      linarith
    have h2 : (7 : ℝ) / 4 * (M : ℝ) ≤ ((7 * M + 3) / 4 : ℕ) := by
      have hdiv : 4 * ((7 * M + 3) / 4) ≥ 7 * M := by omega
      have : (4 : ℝ) * (((7 * M + 3) / 4 : ℕ) : ℝ) ≥ (7 * M : ℕ) := by exact_mod_cast hdiv
      push_cast at this ⊢
      linarith
    linarith
  have hceil : ⌈7 / 4 * Real.logb 2 (n₁ : ℝ)⌉₊ ≤ (7 * M + 3) / 4 := Nat.ceil_le.2 hle
  have hfin : (7 * M + 3) / 4 ≤ 7 * M / 3 := by
    have hM1 : 1 ≤ M := by omega
    omega
  omega

/-- `n ^ a ≤ n ^ b` for `1 ≤ a ≤ b`, with no positivity hypothesis on `n`: the case `n = 0`
is `0 ≤ 0`.  The four branch costs of §9.7 are powers of `n₂`. -/
theorem pow_le_pow_exp {n a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) : n ^ a ≤ n ^ b := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [Nat.zero_pow (by omega), Nat.zero_pow (by omega)]
  · exact Nat.pow_le_pow_right hn hab

/-! ### The labels of Case 1: `d₁`-subsets, and their complements

Case 1 of §9.7 labels `v ∈ V₁` by `X(v)`, a `d₁`-subset of `V₂`, and calls the resulting
scheme *"the Johnson scheme `J(n₂, d₁)`"*.  By Defs. 3.2.9/3.2.13 a Johnson scheme `J(k,t)`
exists only for `2 ≤ t` and `2t + 1 ≤ k`, and §9.7 checks neither (entry 41 of
the corrected paper).  Two facts are proved here.

* `Babai.two_le_and_add_two_le_of_lt_choose`: from `n₂ < n₁ = C(n₂, d₁)` — the standing
  hypothesis `n₂ < αn₁ < n₁` of Theorem 9.2.2, read through the bijection of Case 1 — one
  gets `2 ≤ d₁` **and** `d₁ + 2 ≤ n₂`.  The first is `Babai.case_9_7_1_two_le_d₁`; the
  second is new and is what the complement needs.
* `Babai.isJohnsonColoring_of_labels`: labelling by `d₁`-subsets of an `n₂`-set gives an
  object of `Babai.JohnsonSchemes` as soon as **either** `2d₁ + 1 ≤ n₂` **or**
  `2(n₂ - d₁) + 1 ≤ n₂`.  The second alternative is the case `d₁ > n₂/2`, which the paper's
  phrase *"the Johnson scheme `J(n₂,d₁)`"* does not cover: there the labels are replaced by
  their complements `V₂ ∖ X(v)`, which is canonical and changes no color, because
  `|Sᶜ ∖ Tᶜ| = |T ∖ S| = |S ∖ T|` for `|S| = |T|`.  Together with
  `Babai.johnson_alternative` the only case left open is `n₂ = 2d₁`, which entry 41 of
  the corrected paper by the primitivity of `X₁`. -/

/-- If a `k`-set has more than `k` subsets of size `t`, then `2 ≤ t ≤ k - 2`.

In Case 1 of §9.7 the bijection `v ↦ X(v)` gives `n₁ = C(n₂, d₁)`, and `n₂ < n₁`; so this
says `2 ≤ d₁` (`Babai.case_9_7_1_two_le_d₁`) and `d₁ + 2 ≤ n₂`.  The four excluded values
are `t = 0` and `t = k` (one subset), `t = 1` and `t = k - 1` (`k` subsets), and `t > k`
(none). -/
theorem two_le_and_add_two_le_of_lt_choose {k t : ℕ} (hk : 1 ≤ k) (h : k < k.choose t) :
    2 ≤ t ∧ t + 2 ≤ k := by
  have htk : t ≤ k := by
    by_contra hlt
    rw [Nat.choose_eq_zero_of_lt (by omega)] at h; omega
  have ht0 : t ≠ 0 := by rintro rfl; rw [Nat.choose_zero_right] at h; omega
  have ht1 : t ≠ 1 := by rintro rfl; rw [Nat.choose_one_right] at h; omega
  have htk' : t ≠ k := by rintro rfl; rw [Nat.choose_self] at h; omega
  have htk1 : t ≠ k - 1 := by
    intro hne
    have hsymm : k.choose (k - t) = k.choose t := Nat.choose_symm htk
    have : k - t = 1 := by omega
    rw [this, Nat.choose_one_right] at hsymm
    omega
  omega

/-- The alternative that Case 1 of §9.7 runs on: with `2 ≤ t ≤ k - 2`, either `J(k,t)` is a
Johnson scheme in the sense of Def. 3.2.9 (`2t + 1 ≤ k`), or its complement `J(k, k-t)` is
(`2(k-t) + 1 ≤ k`).  The excluded case is exactly `k = 2t`. -/
theorem johnson_alternative {k t : ℕ} (h2 : 2 ≤ t) (h2' : t + 2 ≤ k) (hne : k ≠ 2 * t) :
    (2 ≤ t ∧ 2 * t + 1 ≤ k) ∨ (2 ≤ k - t ∧ 2 * (k - t) + 1 ≤ k) := by omega

/-- Relabelling the `t`-subsets of a set along a bijection of the ambient sets. -/
def binomCongr {α β : Type*} (e : α ≃ β) (t : ℕ) : binom α t ≃ binom β t :=
  e.finsetCongr.subtypeEquiv fun S => by simp [Equiv.finsetCongr_apply]

@[simp] theorem binomCongr_coe {α β : Type*} (e : α ≃ β) (t : ℕ) (S : binom α t) :
    ((binomCongr e t S : binom β t) : Finset β) = (S : Finset α).map e.toEmbedding := rfl

/-- Relabelling does not change `|S \ T|`. -/
theorem binomCongr_card_sdiff {α β : Type*} [DecidableEq α] [DecidableEq β] (e : α ≃ β)
    (t : ℕ) (S T : binom α t) :
    (((binomCongr e t S : binom β t) : Finset β) \ ((binomCongr e t T : binom β t) : Finset β)).card
      = ((S : Finset α) \ (T : Finset α)).card := by
  rw [binomCongr_coe, binomCongr_coe, ← Finset.map_sdiff, Finset.card_map]

/-- *"`J(k,t) ≅ J(k,k-t)`"*: passing from a `t`-subset to its complement.  This is the
canonical relabelling that Case 1 of §9.7 needs when `d₁ > n₂/2`. -/
def binomCompl {α : Type*} [Fintype α] [DecidableEq α] {k t : ℕ} (hk : Fintype.card α = k)
    (ht : t ≤ k) : binom α t ≃ binom α (k - t) where
  toFun S := ⟨(S : Finset α)ᶜ, by rw [Finset.card_compl, hk, S.2]⟩
  invFun S := ⟨(S : Finset α)ᶜ, by rw [Finset.card_compl, hk, S.2]; omega⟩
  left_inv S := Subtype.ext (compl_compl _)
  right_inv S := Subtype.ext (compl_compl _)

/-- Complementation does not change the Johnson color: `|Sᶜ \ Tᶜ| = |T \ S| = |S \ T|`,
the last equality because `|S| = |T|`. -/
theorem binomCompl_card_sdiff {α : Type*} [Fintype α] [DecidableEq α] {k t : ℕ}
    (hk : Fintype.card α = k) (ht : t ≤ k) (S T : binom α t) :
    (((binomCompl hk ht S : binom α (k - t)) : Finset α)
        \ ((binomCompl hk ht T : binom α (k - t)) : Finset α)).card
      = ((S : Finset α) \ (T : Finset α)).card := by
  have hset : ((S : Finset α)ᶜ \ (T : Finset α)ᶜ) = (T : Finset α) \ (S : Finset α) := by
    ext a; simp only [Finset.mem_sdiff, Finset.mem_compl]; tauto
  have h1 := Finset.card_sdiff_add_card_inter (S : Finset α) (T : Finset α)
  have h2 := Finset.card_sdiff_add_card_inter (T : Finset α) (S : Finset α)
  rw [Finset.inter_comm] at h2
  have hS : (S : Finset α).card = t := S.2
  have hT : (T : Finset α).card = t := T.2
  show ((S : Finset α)ᶜ \ (T : Finset α)ᶜ).card = ((S : Finset α) \ (T : Finset α)).card
  rw [hset]
  omega

/-- Definitions 3.2.9/3.2.13 from a labelling by `t`-subsets.  If the points of `S` are
labelled bijectively by the `t`-subsets of a `k`-set `V` and the coloring is the Johnson
coloring `|S \ T|` of those labels, then the coloring is a Johnson coloring — provided the
labels, **or their complements**, satisfy the constraints `2 ≤ t` and `2t + 1 ≤ k` of
Def. 3.2.9.

This is Case 1 of §9.7, *"Let us label `v ∈ V₁` by the set `X(v)`"*, with the fill for
`d₁ > n₂/2` described above: there the labels used are the complements `V₂ ∖ X(v)`. -/
theorem isJohnsonColoring_of_labels {α : Type} {S : Set α} {V : Type} [Fintype V]
    [DecidableEq V] {k t : ℕ} (hk : Fintype.card V = k) (htk : t ≤ k)
    {c : ↥S → ↥S → ℕ} (φ : ↥S ≃ binom V t)
    (hc : ∀ x y, c x y = ((φ x : Finset V) \ (φ y : Finset V)).card)
    (h : (2 ≤ t ∧ 2 * t + 1 ≤ k) ∨ (2 ≤ k - t ∧ 2 * (k - t) + 1 ≤ k)) :
    IsJohnsonColoring c := by
  classical
  have ε : V ≃ Fin k := Fintype.equivFinOfCardEq hk
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine ⟨k, t, φ.trans (binomCongr ε t), h1, h2, fun x y => ?_⟩
    rw [hc x y]
    exact (binomCongr_card_sdiff ε t (φ x) (φ y)).symm
  · refine ⟨k, k - t, (φ.trans (binomCompl hk htk)).trans (binomCongr ε (k - t)), h1, h2,
      fun x y => ?_⟩
    have key : ∀ z : ↥S, (((φ.trans (binomCompl hk htk)).trans (binomCongr ε (k - t))) z)
        = binomCongr ε (k - t) (binomCompl hk htk (φ z)) := fun _ => rfl
    rw [hc x y, key x, key y, binomCongr_card_sdiff]
    exact (binomCompl_card_sdiff hk htk (φ x) (φ y)).symm

/-! ### Swapping two members of a family

Definition 2.3.9 (twins) for the neighborhood hypergraph `H` is stated through the
transposition of two vertices of `H`, i.e. of two blocks.  `Babai.swapIn` is the action of
that transposition on a hyperedge, written without a decidability instance so that it
transports along a bijection without any instance juggling. -/

/-- The image of the family `S` under the transposition of `B` and `B'`. -/
def swapIn {α : Type*} (B B' : α) (S : Set α) : Set α :=
  {A | (A = B ∧ B' ∈ S) ∨ (A = B' ∧ B ∈ S) ∨ (A ≠ B ∧ A ≠ B' ∧ A ∈ S)}

theorem mem_image_equiv {α β : Type*} (e : α ≃ β) (T : Set α) (y : β) :
    y ∈ e '' T ↔ e.symm y ∈ T := by
  constructor
  · rintro ⟨x, hx, rfl⟩; simpa using hx
  · intro h; exact ⟨e.symm y, h, by simp⟩

/-- Swapping commutes with a bijection of the ambient type. -/
theorem swapIn_image {α β : Type*} (e : α ≃ β) (B B' : α) (S : Set α) :
    swapIn (e B) (e B') (e '' S) = e '' swapIn B B' S := by
  ext y
  simp only [swapIn, Set.mem_setOf_eq, mem_image_equiv e]
  have h1 : y = e B ↔ e.symm y = B := by
    constructor
    · rintro rfl; simp
    · intro h; rw [← h]; simp
  have h2 : y = e B' ↔ e.symm y = B' := by
    constructor
    · rintro rfl; simp
    · intro h; rw [← h]; simp
  simp only [ne_eq, h1, h2, Equiv.symm_apply_apply]

/-! ### The neighborhood hypergraph, read off the object

§9.7 works with *"the hypergraph `H = (V₂, E)` of neighborhoods of vertices in `V₁`"*, the
neighborhoods being taken in the bipartite graph `X = (V₁, V₂; Rᵢ)` that step 8 of §9.4
picks out of the link.  The object of `Babai.BlkCases` carries only the coloring `c`, so
the constituent has to be picked from `c`; as in step 8 it is the **smallest color that
occurs on `V₁ × V₂`** (`Babai.BlkCaseObj.linkColor`), which is a canonical choice because a
morphism preserves the color labels.

Since `H` is simple (*"This hypergraph has no multiple edges because there are no twins in
`V₁`"*) its edge multiset is a **set** of subsets of `V₂`, and this is how it is recorded
here (`Babai.BlkCaseObj.edgeFam`); nothing below uses the indexing of the edges by the
points of `V₁`. -/

namespace BlkCaseObj

variable {s : Set Ω} {Case : (Set ↥s → Set ↥s → ℕ) → Set (Set ↥s) → Set (Set ↥s) → Prop}

/-- §9.7.  *"`J = {c(x,y) | x ∈ V₁, y ∈ V₂}`"*: the colors that occur on the link. -/
def HasLinkColor (X : BlkCaseObj s Case) (k : ℕ) : Prop :=
  ∃ x, X.part₁ x ∧ ∃ B ∈ X.blocks, X.c {x} B = k

open scoped Classical in
/-- §9.7.  The constituent of the link that §9.7 reads the neighborhoods in: step 8 of §9.4
picks a constituent `Rᵢ` of `X₁₂`, and the canonical choice is the **smallest color that
occurs on `V₁ × V₂`**. -/
noncomputable def linkColor (X : BlkCaseObj s Case) : ℕ :=
  if h : ∃ k, X.HasLinkColor k then Nat.find h else 0

/-- §9.7.  *"`X(v)`"*: the neighborhood of a point `v` of `V₁`, a set of blocks. -/
def nbhd (X : BlkCaseObj s Case) (x : ↥s) : Set (Set ↥s) :=
  {B | B ∈ X.blocks ∧ X.c {x} B = X.linkColor}

/-- §9.7.  *"the hypergraph `H = (V₂, E)` of neighborhoods of vertices in `V₁`"*, as the
**set** of its hyperedges; `H` has no multiple edges, so nothing is lost. -/
def edgeFam (X : BlkCaseObj s Case) : Set (Set (Set ↥s)) :=
  {S | ∃ x, X.part₁ x ∧ X.nbhd x = S}

/-- Definition 2.3.9 for `H`: two blocks are `H`-twins when their transposition is an
automorphism of `H`, i.e. carries hyperedges to hyperedges. -/
def IsHTwin (X : BlkCaseObj s Case) (B B' : Set ↥s) : Prop :=
  ∀ S ∈ X.edgeFam, swapIn B B' S ∈ X.edgeFam

/-- Case 1 of §9.7: *"`V₂` is a set of twins in `H`."* -/
def IsCase1 (X : BlkCaseObj s Case) : Prop :=
  ∀ B ∈ X.blocks, ∀ B' ∈ X.blocks, X.IsHTwin B B'

/-- Case 2 of §9.7: *"There is an `H`-twin equivalence class `C ⊆ V₂` of size
`|C| ≥ n₂/2`."*  A *twin equivalence class* is a set of pairwise twins closed under being a
twin of one of its members. -/
def IsCase2 (X : BlkCaseObj s Case) : Prop :=
  ∃ C : Set (Set ↥s), C ⊆ X.blocks ∧ X.blocks.ncard ≤ 2 * C.ncard ∧
    (∀ B ∈ C, ∀ B' ∈ C, X.IsHTwin B B') ∧
    (∀ B ∈ C, ∀ B' ∈ X.blocks, X.IsHTwin B B' → B' ∈ C)

/-- `n₁ = |V₁|`. -/
noncomputable def n₁ (X : BlkCaseObj s Case) : ℕ := {x | X.part₁ x}.ncard

open scoped Classical in
/-- `d₁`, the common size of the neighborhoods: *"`H` … is uniform of rank `d₁`"*.  `X` is
semiregular (step 8 of §9.4), so all neighborhoods have the same size; taking the supremum
is a way of reading that size off the object without choosing a point of `V₁`. -/
noncomputable def d₁ (X : BlkCaseObj s Case) : ℕ :=
  sSup {n | ∃ x, X.part₁ x ∧ (X.nbhd x).ncard = n}

/-- `n₂ = |V₂|`, the number of blocks, read on the object of §9.7. -/
noncomputable def n₂ (X : BlkCaseObj s Case) : ℕ := X.blocks.ncard

/-- §9.7, Case 3.  The arity at which the Design Lemma is applied to `H`:
`d' = min(d₁, n₂ − d₁)`.

§9.7 writes `d₁`, and applies the Design Lemma (Theorem 8.1.2) to *"`H`, viewed as a
`d₁`-ary relational structure"*, without checking Theorem 8.1.2's hypothesis
`d₁ ≤ n₂/2`, which need not hold.  The **bipartite complement** `H^c = {V₂ ∖ E | E ∈ 𝓔}`
is `(n₂ − d₁)`-uniform, simple, and has the same automorphism group, hence the same
twins and the same symmetry defect, as `H`; and a canonical object on `V₂` for `H^c` is
one for `H`.  So Case 3 may be run on whichever of `H`, `H^c` has the smaller rank, and
that rank is `d'`.  See the entry *"§9.7 Case 3: `d₁ ≤ n₂/2` is not checked"* in
the corrected paper.

Since `d' ≤ d₁`, the branch costs only drop. -/
noncomputable def d' (X : BlkCaseObj s Case) : ℕ := min X.d₁ (X.n₂ - X.d₁)

/-- Case 3a of §9.7: *"`d₁ ≤ (7/3) log₂ n₁`"*, with `d₁` replaced by the rank `d'` at
which the Design Lemma is actually applied (`Babai.BlkCaseObj.d'`).  The condition is
weaker than the paper's, so Case 3a covers more objects and Case 3b fewer; on the objects
that satisfy the paper's condition it is the paper's branch, because `d' ≤ d₁`. -/
def IsCase3a (X : BlkCaseObj s Case) : Prop :=
  (X.d' : ℝ) ≤ 7 / 3 * Real.logb 2 (X.n₁ : ℝ)

end BlkCaseObj

/-! ### The branch conditions are isomorphism invariants

Everything of §9.7 above is read off the coloring and the two parts, and a morphism of
`Babai.BlkCases` preserves both together with the color **labels**; so each of the three
branch conditions transports.  This is what `Babai.FindsAtMultCost.cases` asks for. -/

/-- The three clauses of a morphism of `Babai.BlkCases`, as a standalone hypothesis, so
that the transport lemmas apply at every level of the nested full subcategories of the case
distinction of §9.7. -/
structure BlkCaseObj.IsMorphOn {s t : Set Ω}
    {Cs : (Set ↥s → Set ↥s → ℕ) → Set (Set ↥s) → Set (Set ↥s) → Prop}
    {Ct : (Set ↥t → Set ↥t → ℕ) → Set (Set ↥t) → Set (Set ↥t) → Prop}
    (X : BlkCaseObj s Cs) (Y : BlkCaseObj t Ct) (φ : ↥s ≃ ↥t) : Prop where
  /-- The first part goes to the first part. -/
  part₁ : ∀ x, Y.part₁ (φ x) ↔ X.part₁ x
  /-- Blocks go to blocks. -/
  blocks : ∀ B, φ '' B ∈ Y.blocks ↔ B ∈ X.blocks
  /-- The coloring is preserved, color label by color label. -/
  col : ∀ A B, Y.c (φ '' A) (φ '' B) = X.c A B

namespace BlkCaseObj

variable {s t : Set Ω}
  {Cs : (Set ↥s → Set ↥s → ℕ) → Set (Set ↥s) → Set (Set ↥s) → Prop}
  {Ct : (Set ↥t → Set ↥t → ℕ) → Set (Set ↥t) → Set (Set ↥t) → Prop}
  {X : BlkCaseObj s Cs} {Y : BlkCaseObj t Ct} {φ : ↥s ≃ ↥t}

theorem IsMorphOn.c_singleton (h : X.IsMorphOn Y φ) (x : ↥s) (B : Set ↥s) :
    Y.c {φ x} (φ '' B) = X.c {x} B := by
  have := h.col {x} B
  rwa [Set.image_singleton] at this

/-- The colors of the link are the same color labels for the two objects. -/
theorem IsMorphOn.hasLinkColor_iff (h : X.IsMorphOn Y φ) (k : ℕ) :
    Y.HasLinkColor k ↔ X.HasLinkColor k := by
  constructor
  · rintro ⟨y, hy, B, hB, hcol⟩
    refine ⟨φ.symm y, (h.part₁ (φ.symm y)).1 (by simpa using hy), φ.symm '' B, ?_, ?_⟩
    · have hb := h.blocks (φ.symm '' B)
      rw [Equiv.image_symm_image] at hb
      exact hb.1 hB
    · have h3 := h.c_singleton (φ.symm y) (φ.symm '' B)
      rw [Equiv.apply_symm_apply, Equiv.image_symm_image] at h3
      rw [← h3]; exact hcol
  · rintro ⟨x, hx, B, hB, hcol⟩
    exact ⟨φ x, (h.part₁ x).2 hx, φ '' B, (h.blocks B).2 hB,
      by rw [h.c_singleton x B]; exact hcol⟩

/-- The constituent picked by §9.7 is an isomorphism invariant. -/
theorem IsMorphOn.linkColor_eq (h : X.IsMorphOn Y φ) : Y.linkColor = X.linkColor := by
  classical
  by_cases hex : ∃ k, X.HasLinkColor k
  · have hex' : ∃ k, Y.HasLinkColor k := by
      obtain ⟨k, hk⟩ := hex; exact ⟨k, (h.hasLinkColor_iff k).2 hk⟩
    rw [linkColor, linkColor, dif_pos hex, dif_pos hex']
    exact le_antisymm (Nat.find_le ((h.hasLinkColor_iff _).2 (Nat.find_spec hex)))
      (Nat.find_le ((h.hasLinkColor_iff _).1 (Nat.find_spec hex')))
  · have hex' : ¬ ∃ k, Y.HasLinkColor k := by
      rintro ⟨k, hk⟩; exact hex ⟨k, (h.hasLinkColor_iff k).1 hk⟩
    rw [linkColor, linkColor, dif_neg hex, dif_neg hex']

/-- Neighborhoods are carried to neighborhoods. -/
theorem IsMorphOn.nbhd_eq (h : X.IsMorphOn Y φ) (x : ↥s) :
    Y.nbhd (φ x) = imgEquiv φ '' X.nbhd x := by
  ext B'
  rw [mem_image_equiv (imgEquiv φ)]
  show (B' ∈ Y.blocks ∧ Y.c {φ x} B' = Y.linkColor)
    ↔ (φ.symm '' B' ∈ X.blocks ∧ X.c {x} (φ.symm '' B') = X.linkColor)
  have himg : φ '' (φ.symm '' B') = B' := Equiv.image_symm_image φ B'
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · have := h.blocks (φ.symm '' B'); rw [himg] at this; exact this.1 h1
    · have h3 := h.c_singleton x (φ.symm '' B')
      rw [himg] at h3; rw [← h3, h2, h.linkColor_eq]
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · have := h.blocks (φ.symm '' B'); rw [himg] at this; exact this.2 h1
    · have h3 := h.c_singleton x (φ.symm '' B')
      rw [himg] at h3; rw [h3, h2, h.linkColor_eq]

/-- The hypergraph `H` is carried to the hypergraph `H`. -/
theorem IsMorphOn.edgeFam_eq (h : X.IsMorphOn Y φ) :
    Y.edgeFam = (fun S => imgEquiv φ '' S) '' X.edgeFam := by
  ext S'
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨X.nbhd (φ.symm y), ⟨φ.symm y, (h.part₁ (φ.symm y)).1 (by simpa using hy), rfl⟩, ?_⟩
    show imgEquiv φ '' X.nbhd (φ.symm y) = Y.nbhd y
    rw [← h.nbhd_eq (φ.symm y), Equiv.apply_symm_apply]
  · rintro ⟨S, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨φ x, (h.part₁ x).2 hx, h.nbhd_eq x⟩

theorem image_imgEquiv_injective (φ : ↥s ≃ ↥t) :
    Function.Injective (fun S : Set (Set ↥s) => imgEquiv φ '' S) :=
  Set.image_injective.2 (imgEquiv φ).injective

/-- Twins of `H` are carried to twins of `H`. -/
theorem IsMorphOn.isHTwin_iff (h : X.IsMorphOn Y φ) (B B' : Set ↥s) :
    Y.IsHTwin (φ '' B) (φ '' B') ↔ X.IsHTwin B B' := by
  have hmem : ∀ T : Set (Set ↥s), imgEquiv φ '' T ∈ Y.edgeFam ↔ T ∈ X.edgeFam := by
    intro T
    rw [h.edgeFam_eq]
    exact (image_imgEquiv_injective φ).mem_set_image
  constructor
  · intro hY S hS
    have h1 : swapIn (imgEquiv φ B) (imgEquiv φ B') (imgEquiv φ '' S) ∈ Y.edgeFam :=
      hY _ ((hmem S).2 hS)
    rw [swapIn_image] at h1
    exact (hmem _).1 h1
  · intro hX S' hS'
    rw [h.edgeFam_eq] at hS'
    obtain ⟨S, hS, rfl⟩ := hS'
    have h1 : swapIn B B' S ∈ X.edgeFam := hX S hS
    show swapIn (imgEquiv φ B) (imgEquiv φ B') (imgEquiv φ '' S) ∈ Y.edgeFam
    rw [swapIn_image]
    exact (hmem _).2 h1

/-- Case 1 is an isomorphism invariant. -/
theorem IsMorphOn.isCase1_iff (h : X.IsMorphOn Y φ) : Y.IsCase1 ↔ X.IsCase1 := by
  constructor
  · intro hY B hB B' hB'
    exact (h.isHTwin_iff B B').1 (hY _ ((h.blocks B).2 hB) _ ((h.blocks B').2 hB'))
  · intro hX B' hB' C' hC'
    have hB : φ.symm '' B' ∈ X.blocks := by
      have hb := h.blocks (φ.symm '' B'); rw [Equiv.image_symm_image] at hb; exact hb.1 hB'
    have hC : φ.symm '' C' ∈ X.blocks := by
      have hb := h.blocks (φ.symm '' C'); rw [Equiv.image_symm_image] at hb; exact hb.1 hC'
    have := (h.isHTwin_iff (φ.symm '' B') (φ.symm '' C')).2 (hX _ hB _ hC)
    rwa [Equiv.image_symm_image, Equiv.image_symm_image] at this

/-- The blocks are carried to the blocks, as a set of sets. -/
theorem IsMorphOn.blocks_eq (h : X.IsMorphOn Y φ) :
    Y.blocks = (fun B => φ '' B) '' X.blocks := by
  ext B'
  constructor
  · intro hB'
    refine ⟨φ.symm '' B', ?_, Equiv.image_symm_image φ B'⟩
    have hb := h.blocks (φ.symm '' B'); rw [Equiv.image_symm_image] at hb; exact hb.1 hB'
  · rintro ⟨B, hB, rfl⟩; exact (h.blocks B).2 hB

/-- Case 2 is an isomorphism invariant. -/
theorem IsMorphOn.isCase2_iff (h : X.IsMorphOn Y φ) : Y.IsCase2 ↔ X.IsCase2 := by
  have hinj : Function.Injective (fun B : Set ↥s => φ '' B) :=
    Set.image_injective.2 φ.injective
  have hblk := h.blocks_eq
  constructor
  · rintro ⟨C', hsub, hcard, hpair, hmax⟩
    refine ⟨(fun B' => φ.symm '' B') '' C', ?_, ?_, ?_, ?_⟩
    · rintro _ ⟨B', hB', rfl⟩
      have := h.blocks (φ.symm '' B'); rw [Equiv.image_symm_image] at this
      exact this.1 (hsub hB')
    · have hb : Y.blocks.ncard = X.blocks.ncard := by
        rw [hblk, Set.ncard_image_of_injective _ hinj]
      rw [Set.ncard_image_of_injective _ (Set.image_injective.2 φ.symm.injective), ← hb]
      exact hcard
    · rintro _ ⟨B', hB', rfl⟩ _ ⟨C₀, hC₀, rfl⟩
      have := (h.isHTwin_iff (φ.symm '' B') (φ.symm '' C₀)).1
        (by rw [Equiv.image_symm_image, Equiv.image_symm_image]; exact hpair _ hB' _ hC₀)
      exact this
    · rintro _ ⟨B', hB', rfl⟩ D hD htw
      refine ⟨φ '' D, hmax _ hB' _ ((h.blocks D).2 hD) ?_, Equiv.symm_image_image φ D⟩
      have := (h.isHTwin_iff (φ.symm '' B') D).2 htw
      rwa [Equiv.image_symm_image] at this
  · rintro ⟨C, hsub, hcard, hpair, hmax⟩
    refine ⟨(fun B => φ '' B) '' C, ?_, ?_, ?_, ?_⟩
    · rintro _ ⟨B, hB, rfl⟩; exact (h.blocks B).2 (hsub hB)
    · rw [hblk, Set.ncard_image_of_injective _ hinj, Set.ncard_image_of_injective _ hinj]
      exact hcard
    · rintro _ ⟨B, hB, rfl⟩ _ ⟨C₀, hC₀, rfl⟩
      exact (h.isHTwin_iff B C₀).2 (hpair _ hB _ hC₀)
    · rintro _ ⟨B, hB, rfl⟩ D' hD' htw
      refine ⟨φ.symm '' D', hmax _ hB _ ?_ ?_, Equiv.image_symm_image φ D'⟩
      · have := h.blocks (φ.symm '' D'); rw [Equiv.image_symm_image] at this
        exact this.1 hD'
      · have := (h.isHTwin_iff B (φ.symm '' D')).1
          (by rwa [Equiv.image_symm_image])
        exact this

/-- `n₁` is an isomorphism invariant. -/
theorem IsMorphOn.n₁_eq (h : X.IsMorphOn Y φ) : Y.n₁ = X.n₁ := by
  have hset : {y : ↥t | Y.part₁ y} = φ '' {x : ↥s | X.part₁ x} := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_image]
    constructor
    · intro hy; exact ⟨φ.symm y, (h.part₁ (φ.symm y)).1 (by simpa using hy), by simp⟩
    · rintro ⟨x, hx, rfl⟩; exact (h.part₁ x).2 hx
  rw [n₁, n₁, hset, Set.ncard_image_of_injective _ φ.injective]

/-- `d₁` is an isomorphism invariant. -/
theorem IsMorphOn.d₁_eq (h : X.IsMorphOn Y φ) : Y.d₁ = X.d₁ := by
  classical
  have hcard : ∀ x : ↥s, (Y.nbhd (φ x)).ncard = (X.nbhd x).ncard := by
    intro x
    rw [h.nbhd_eq x, Set.ncard_image_of_injective _ (imgEquiv φ).injective]
  have hset : {n | ∃ y, Y.part₁ y ∧ (Y.nbhd y).ncard = n}
      = {n | ∃ x, X.part₁ x ∧ (X.nbhd x).ncard = n} := by
    ext n
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨φ.symm y, (h.part₁ (φ.symm y)).1 (by simpa using hy), ?_⟩
      have hc := hcard (φ.symm y)
      rw [Equiv.apply_symm_apply] at hc
      exact hc.symm
    · rintro ⟨x, hx, rfl⟩
      exact ⟨φ x, (h.part₁ x).2 hx, hcard x⟩
  rw [d₁, d₁, hset]

/-- `n₂` is an isomorphism invariant. -/
theorem IsMorphOn.n₂_eq (h : X.IsMorphOn Y φ) : Y.n₂ = X.n₂ := by
  rw [n₂, n₂, h.blocks_eq,
    Set.ncard_image_of_injective _ (Set.image_injective.2 φ.injective)]

/-- `d'` is an isomorphism invariant. -/
theorem IsMorphOn.d'_eq (h : X.IsMorphOn Y φ) : Y.d' = X.d' := by
  rw [d', d', h.d₁_eq, h.n₂_eq]

/-- Case 3a is an isomorphism invariant. -/
theorem IsMorphOn.isCase3a_iff (h : X.IsMorphOn Y φ) : Y.IsCase3a ↔ X.IsCase3a := by
  rw [IsCase3a, IsCase3a, h.d'_eq, h.n₁_eq]

end BlkCaseObj

/-! ### The branch conditions on the category of inputs of §9.7 -/

namespace BlkBlockDesignInputs

/-- The object of §9.7 underlying an admissible input of the block design case. -/
def obj₀ (X : Pt (BlkBlockDesignInputs Ω)) :
    BlkCaseObj X.car (fun c 𝒱₁ 𝒞 => IsBlockDesignCaseOn c 𝒱₁ 𝒞) := X.obj.1.1

/-- A morphism of `Babai.BlkBlockDesignInputs` is a morphism of the underlying objects. -/
theorem isMorphOn_of_iso {X Y : Pt (BlkBlockDesignInputs Ω)} {φ : ↥X.car ≃ ↥Y.car}
    (hφ : φ ∈ (BlkBlockDesignInputs Ω).IsoP X Y) : (obj₀ X).IsMorphOn (obj₀ Y) φ :=
  ⟨hφ.2.1, hφ.2.2.1, hφ.2.2.2⟩

/-- `|V₁|` read on the ambient type is `n₁` read inside the point set. -/
theorem v₁_ncard (X : Pt (BlkBlockDesignInputs Ω)) :
    (BlkBlockDesignInputs.V₁ X).ncard = (obj₀ X).n₁ :=
  Set.ncard_image_of_injective _ Subtype.val_injective

/-- §9.7.  There is at least one block: the link `X₁₂` is nontrivial, so it has an edge,
whose head is a vertex of `V₂`, that is a block. -/
theorem blocks_nonempty_of_case {s : Set Ω} {c : Set ↥s → Set ↥s → ℕ}
    {𝒱₁ 𝒞 : Set (Set ↥s)} (h : IsBlockDesignCaseOn c 𝒱₁ 𝒞) : 𝒞.Nonempty := by
  letI : DecidableEq ↥(𝒱₁ ∪ 𝒞) := Classical.decEq _
  unfold IsBlockDesignCaseOn at h
  obtain ⟨-, y₁, -, -, -⟩ := h.toIsBipartiteCase.link_nontrivial
  exact ⟨(y₁.1 : Set ↥s), y₁.2⟩


theorem one_le_numBlocks (X : Pt (BlkBlockDesignInputs Ω)) :
    1 ≤ BlkBlockDesignInputs.numBlocks X := by
  have hne : (obj₀ X).blocks.Nonempty := blocks_nonempty_of_case (obj₀ X).case
  have hfin : (obj₀ X).blocks.Finite := Set.toFinite _
  have := (Set.ncard_pos hfin).2 hne
  exact this

/-- Case 1 of §9.7 as a condition on an admissible input. -/
def Case1P : ∀ s : Set Ω, (BlkBlockDesignInputs Ω).Obj s → Prop := fun _ X => X.1.1.IsCase1

/-- Case 2 of §9.7 as a condition on an admissible input. -/
def Case2P : ∀ s : Set Ω, (BlkBlockDesignInputs Ω).Obj s → Prop := fun _ X => X.1.1.IsCase2

/-- Case 3a of §9.7 as a condition on an admissible input. -/
def Case3aP : ∀ s : Set Ω, (BlkBlockDesignInputs Ω).Obj s → Prop :=
  fun _ X => X.1.1.IsCase3a

theorem case1P_congr {X Y : Pt (BlkBlockDesignInputs Ω)}
    (h : ((BlkBlockDesignInputs Ω).IsoP X Y).Nonempty)
    (hX : Case1P X.car X.obj) : Case1P Y.car Y.obj := by
  obtain ⟨φ, hφ⟩ := h
  exact ((isMorphOn_of_iso hφ).isCase1_iff).2 hX

theorem case2P_congr {X Y : Pt (BlkBlockDesignInputs Ω)}
    (h : ((BlkBlockDesignInputs Ω).IsoP X Y).Nonempty)
    (hX : Case2P X.car X.obj) : Case2P Y.car Y.obj := by
  obtain ⟨φ, hφ⟩ := h
  exact ((isMorphOn_of_iso hφ).isCase2_iff).2 hX

theorem case3aP_congr {X Y : Pt (BlkBlockDesignInputs Ω)}
    (h : ((BlkBlockDesignInputs Ω).IsoP X Y).Nonempty)
    (hX : Case3aP X.car X.obj) : Case3aP Y.car Y.obj := by
  obtain ⟨φ, hφ⟩ := h
  exact ((isMorphOn_of_iso hφ).isCase3a_iff).2 hX

end BlkBlockDesignInputs

/-! ### The arithmetic of the outcomes of §9.7

The four branches of §9.7 reach `Babai.IsBlkDesignOutcome` through five numerical facts,
proved here once.  Each is an inequality between the numbers the paper prints for the
branch and the numbers the outcome asks for. -/

/-- The symmetry defect a returned graph must keep is `1 - α`, and `α ≥ 2/3`, so a defect
of `1/2` — what Cases 3a2 (through §9.8) and 3b (through §9.6) deliver — is enough. -/
theorem blkDesignOutcome_defect {α : ℝ} (hα : 2 / 3 ≤ α) : 1 - α ≤ 1 / 2 := by linarith

/-- *"`n₂` is reduced to `≤ 3n₂/4`"* (Cases 3a1, 3b) is the significant reduction of §9.5,
`10 n₂_new ≤ 9 n₂`. -/
theorem blkDesignOutcome_three_quarters {m n₂ : ℕ} (h : 4 * m ≤ 3 * n₂) :
    10 * m ≤ 9 * n₂ := by omega

/-- *"`n₂` is reduced to `≤ n₂/2`"* (Case 2, Case 3a2, §9.8) is the significant reduction
of §9.5. -/
theorem blkDesignOutcome_half {m n₂ : ℕ} (h : 2 * m ≤ n₂) : 10 * m ≤ 9 * n₂ := by omega

/-- A returned graph with at most `n₂` blocks still satisfies *"`|V₂| < α|V₁|`"* on the
same first part, because the input does. -/
theorem blkDesignOutcome_numBlocks_lt {m n₂ n₁ : ℕ} {α : ℝ} (h : m ≤ n₂)
    (hin : (n₂ : ℝ) < α * n₁) : (m : ℝ) < α * n₁ :=
  lt_of_le_of_lt (by exact_mod_cast h) hin

/-- Case 2 of §9.7, the fill of *"return this partition"*: a class of the returned
partition of `V₁` has at most `n₁/2` points, and `n₁/2 < αn₁` because `α ≥ 2/3` and
`n₁ ≥ 1`.  So the partition is a colored `α`-partition of `V₁`, goal (a). -/
theorem blkDesignOutcome_alphaClass {k n₁ : ℕ} {α : ℝ} (hα : 2 / 3 ≤ α) (hn₁ : 1 ≤ n₁)
    (h : 2 * k ≤ n₁) : (k : ℝ) < α * n₁ := by
  have hk : (2 : ℝ) * k ≤ n₁ := by exact_mod_cast h
  have hn : (1 : ℝ) ≤ n₁ := by exact_mod_cast hn₁
  nlinarith

/-! ### Case 1 of §9.7: `H` is the complete `d₁`-uniform hypergraph

*"Case 1.  `V₂` is a set of twins in `H`.  This means `Aut(H)` acts on `V₂` as `S(V₂)`.
Since `H` has no multiple edges and is uniform of rank `d₁`, it follows that `H` is the
complete `d₁`-uniform hypergraph.  Let us label `v ∈ V₁` by the set `X(v)`.  This
establishes a bijection between `V₁` and the set `(V₂ choose d₁)`.  Since isomorphisms
preserve the number of common neighbors, this correspondence gives a canonical embedding of
the Johnson scheme `J(n₂, d₁)` on `V₁`."*  (Version 2.5, lines 4238–4249.)

*"`Aut(H)` acts on `V₂` as `S(V₂)`"* is `Babai.BlkCaseObj.IsCase1` unwound: every
transposition of two blocks carries hyperedges to hyperedges, and the transpositions
generate `S(V₂)`.  The generation is not needed in this form: what the paper uses is only
that any `d₁`-subset of `V₂` can be reached from a hyperedge by a sequence of
transpositions, which is `Babai.isCase1_mem_edgeFam` below, proved by induction on
`|S ∖ T|`.

Three facts of the situation of §9.7 are **not** part of `Babai.BlkCaseObj.IsCase1` and are
isolated here as named lemmas:
`Babai.BlkCaseObj.nbhd_ncard_uniform` (*"`H` … is uniform of rank `d₁`"*),
`Babai.BlkCaseObj.nbhd_injective` (*"no multiple edges because there are no twins in
`V₁`"*) and `Babai.BlkCaseObj.numBlocks_ne_two_mul_d₁` (entry 41 of the corrected paper).
All three are proved, from the coherent configuration of step 3 of §9.4; Case 1 is
complete. -/

/-- §9.7.  An input of the block design case, as an object of `Babai.BlkCases`; this is the
type of `Babai.BlkBlockDesignInputs.obj₀`. -/
abbrev BlkDesignObj (s : Set Ω) : Type :=
  BlkCaseObj s (fun c 𝒱₁ 𝒞 => IsBlockDesignCaseOn c 𝒱₁ 𝒞)

namespace BlkCaseObj

variable {s : Set Ω} {Case : (Set ↥s → Set ↥s → ℕ) → Set (Set ↥s) → Set (Set ↥s) → Prop}

/-- A neighborhood consists of blocks: `X(v) ⊆ V₂`. -/
theorem nbhd_subset_blocks (X : BlkCaseObj s Case) (x : ↥s) : X.nbhd x ⊆ X.blocks :=
  fun _ hB => hB.1

/-- §9.7, Case 1.  The color of the Johnson scheme on `V₁` (Def. 3.2.13):
`c(v_S, v_T) = |S ∖ T|` for the labels `S = X(u)`, `T = X(v)`.  Since the labels all have
`d₁` elements this is `d₁` minus *"the number of common neighbors"*, which is the quantity
the paper says isomorphisms preserve. -/
noncomputable def johnsonColor (X : BlkCaseObj s Case) (x y : ↥s) : ℕ :=
  (X.nbhd x \ X.nbhd y).ncard

end BlkCaseObj

namespace BlkCaseObj

variable {s t : Set Ω}
  {Cs : (Set ↥s → Set ↥s → ℕ) → Set (Set ↥s) → Set (Set ↥s) → Prop}
  {Ct : (Set ↥t → Set ↥t → ℕ) → Set (Set ↥t) → Set (Set ↥t) → Prop}
  {X : BlkCaseObj s Cs} {Y : BlkCaseObj t Ct} {φ : ↥s ≃ ↥t}

/-- The Johnson coloring of Case 1 is an isomorphism invariant: a morphism carries `X(v)`
to `X(φ v)`, and `|S ∖ T|` is preserved by a bijection. -/
theorem IsMorphOn.johnsonColor_eq (h : X.IsMorphOn Y φ) (x y : ↥s) :
    Y.johnsonColor (φ x) (φ y) = X.johnsonColor x y := by
  rw [johnsonColor, johnsonColor, h.nbhd_eq x, h.nbhd_eq y,
    ← Set.image_diff (imgEquiv φ).injective,
    Set.ncard_image_of_injective _ (imgEquiv φ).injective]

end BlkCaseObj

/-- The swap of `B` and `B'` in a family that contains `B` but not `B'`: it removes `B` and
puts `B'` in its place. -/
theorem swapIn_eq_insert {α : Type*} {B B' : α} {S : Set α} (hB : B ∈ S) (hB' : B' ∉ S) :
    swapIn B B' S = insert B' (S \ {B}) := by
  ext A
  simp only [swapIn, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_diff,
    Set.mem_singleton_iff]
  constructor
  · rintro (⟨rfl, hc⟩ | ⟨rfl, -⟩ | ⟨h1, -, h3⟩)
    · exact absurd hc hB'
    · exact Or.inl rfl
    · exact Or.inr ⟨h3, h1⟩
  · rintro (rfl | ⟨h1, h2⟩)
    · exact Or.inr (Or.inl ⟨rfl, hB⟩)
    · exact Or.inr (Or.inr ⟨h2, fun hc => hB' (hc ▸ h1), h1⟩)

/-- §9.7, Case 1.  *"Since `H` has no multiple edges and is uniform of rank `d₁`, it follows
that `H` is the complete `d₁`-uniform hypergraph."*  In Case 1 every transposition of two
blocks carries hyperedges to hyperedges, so from one hyperedge `S` every family `T` of
blocks with `|T| = |S|` is reached: induction on `|S ∖ T|`, one transposition replacing a
member of `S ∖ T` by a member of `T ∖ S`. -/
theorem isCase1_mem_edgeFam {s : Set Ω}
    {Case : (Set ↥s → Set ↥s → ℕ) → Set (Set ↥s) → Set (Set ↥s) → Prop}
    {X : BlkCaseObj s Case} (h : X.IsCase1) (n : ℕ) :
    ∀ S T : Set (Set ↥s), S ∈ X.edgeFam → S ⊆ X.blocks → T ⊆ X.blocks →
      T.ncard = S.ncard → (S \ T).ncard = n → T ∈ X.edgeFam := by
  induction n with
  | zero =>
      intro S T hS hSb hTb hcard hn
      have hempty : S \ T = ∅ := by
        rwa [Set.ncard_eq_zero (Set.toFinite _)] at hn
      have hsub : S ⊆ T := Set.diff_eq_empty.1 hempty
      have : S = T := Set.eq_of_subset_of_ncard_le hsub (le_of_eq hcard) (Set.toFinite _)
      exact this ▸ hS
  | succ n ih =>
      intro S T hS hSb hTb hcard hn
      -- a member of `S ∖ T` and a member of `T ∖ S`
      have hne : (S \ T).Nonempty := Set.nonempty_of_ncard_ne_zero (by omega)
      obtain ⟨B, hBS, hBT⟩ := hne
      have hsym : (T \ S).ncard = (S \ T).ncard := by
        have h1 := Set.ncard_inter_add_ncard_diff_eq_ncard S T (Set.toFinite _)
        have h2 := Set.ncard_inter_add_ncard_diff_eq_ncard T S (Set.toFinite _)
        rw [Set.inter_comm] at h2
        omega
      have hne' : (T \ S).Nonempty := Set.nonempty_of_ncard_ne_zero (by omega)
      obtain ⟨B', hB'T, hB'S⟩ := hne'
      -- the swapped family
      have hswap : swapIn B B' S = insert B' (S \ {B}) := swapIn_eq_insert hBS hB'S
      have hS' : swapIn B B' S ∈ X.edgeFam := h B (hSb hBS) B' (hTb hB'T) S hS
      have hS'b : swapIn B B' S ⊆ X.blocks := by
        rw [hswap]
        exact Set.insert_subset (hTb hB'T) (fun A hA => hSb hA.1)
      have hcard' : (swapIn B B' S).ncard = S.ncard := by
        rw [hswap, Set.ncard_insert_of_notMem (fun hc => hB'S hc.1) (Set.toFinite _),
          Set.ncard_diff_singleton_of_mem hBS]
        have : 0 < S.ncard := (Set.ncard_pos (Set.toFinite _)).2 ⟨B, hBS⟩
        omega
      have hdiff : swapIn B B' S \ T = (S \ T) \ {B} := by
        rw [hswap]
        ext A
        simp only [Set.mem_diff, Set.mem_insert_iff, Set.mem_singleton_iff]
        constructor
        · rintro ⟨rfl | ⟨h1, h2⟩, h3⟩
          · exact absurd hB'T h3
          · exact ⟨⟨h1, h3⟩, h2⟩
        · rintro ⟨⟨h1, h2⟩, h3⟩
          exact ⟨Or.inr ⟨h1, h3⟩, h2⟩
      have hn' : (swapIn B B' S \ T).ncard = n := by
        rw [hdiff, Set.ncard_diff_singleton_of_mem (Set.mem_diff _ |>.2 ⟨hBS, hBT⟩), hn]
        omega
      exact ih (swapIn B B' S) T hS' hS'b hTb (by rw [hcard, hcard']) hn'

namespace BlkCaseObj

variable {s : Set Ω}
  {Case : (Set ↥s → Set ↥s → ℕ) → Set (Set ↥s) → Set (Set ↥s) → Prop}

/-- §9.7.  `V₁` is not empty: the link `X₁₂` is nontrivial, so it has an edge, whose tail
is a vertex of `V₁`, which is the singleton of a point of the first part. -/
theorem part₁_nonempty (X : BlkDesignObj s) : ∃ x, X.part₁ x := by
  letI : DecidableEq ↥({A : Set ↥s | ∃ x, X.part₁ x ∧ A = {x}} ∪ X.blocks) :=
    Classical.decEq _
  have hcase := X.case
  unfold IsBlockDesignCaseOn at hcase
  obtain ⟨x₁, -, -, -, -⟩ := hcase.toIsBipartiteCase.link_nontrivial
  obtain ⟨x, hx, -⟩ := x₁.2
  exact ⟨x, hx⟩

/-! #### The neighborhoods as constituent neighborhoods

The three facts of Case 1 that are not part of `Babai.BlkCaseObj.IsCase1` all read the
neighborhood `X(v)` as the neighborhood of the vertex `v` in **one constituent** of the
coherent configuration `X` of step 3 of §9.4.  That configuration is the field `coherent`
of `Babai.IsBipartiteCase`; `Babai.IsBipartiteCase.data` unpacks it, and
`Workspace/SplitOrJohnson/BlkDictionary.lean` and `…/BlkDictionary2.lean` hold the readings
of it that §9.4-§9.8 use.  This section is the remaining, §9.7-specific half of the
dictionary: which vertex of that configuration a point of `V₁` (resp. a block) is, and
which constituent `Babai.BlkCaseObj.linkColor` names. -/

/-- §9.7.  The `Case` of §9.7 read on the vertex set, forgetting all but the part of it
that is common to §9.4-§9.8. -/
theorem bipCase' (X : BlkDesignObj s) :
    IsBipartiteCase X.vc {u : ↥X.vtxSet | (u : Set ↥s) ∈ X.sglSet}
      {u : ↥X.vtxSet | (u : Set ↥s) ∈ X.blocks} := by
  letI : DecidableEq ↥({A : Set ↥s | ∃ x, X.part₁ x ∧ A = {x}} ∪ X.blocks) := Classical.decEq _
  have hcase := X.case
  unfold IsBlockDesignCaseOn at hcase
  exact hcase.toIsBipartiteCase

/-- §9.7.  The coherent configuration `X` of step 3 of §9.4, for an input of §9.7. -/
noncomputable def bipData (X : BlkDesignObj s) :
    BipCaseData X.vc {u : ↥X.vtxSet | (u : Set ↥s) ∈ X.sglSet}
      {u : ↥X.vtxSet | (u : Set ↥s) ∈ X.blocks} :=
  X.bipCase'.data

/-- The vertex of `V₁` at a point of the first part. -/
def vtxPt (X : BlkCaseObj s Case) {x : ↥s} (hx : X.part₁ x) : ↥X.vtxSet :=
  ⟨{x}, Or.inl ⟨x, hx, rfl⟩⟩

/-- The vertex of `V₂` at a block. -/
def vtxBlk (X : BlkCaseObj s Case) {B : Set ↥s} (hB : B ∈ X.blocks) : ↥X.vtxSet :=
  ⟨B, Or.inr hB⟩

theorem vtxPt_mem₁ (X : BlkCaseObj s Case) {x : ↥s} (hx : X.part₁ x) :
    X.vtxPt hx ∈ {u : ↥X.vtxSet | (u : Set ↥s) ∈ X.sglSet} := ⟨x, hx, rfl⟩

theorem vtxBlk_mem₂ (X : BlkCaseObj s Case) {B : Set ↥s} (hB : B ∈ X.blocks) :
    X.vtxBlk hB ∈ {u : ↥X.vtxSet | (u : Set ↥s) ∈ X.blocks} := hB

/-- §9.7.  `Babai.BlkCaseObj.nbhd` for an arbitrary vertex of the configuration; at the
vertex of a point `x` of `V₁` it is `X(x)` (`Babai.BlkCaseObj.nbhdV_vtxPt`). -/
def nbhdV (X : BlkCaseObj s Case) (u : ↥X.vtxSet) : Set (Set ↥s) :=
  {B | B ∈ X.blocks ∧ X.c (u : Set ↥s) B = X.linkColor}

theorem nbhdV_vtxPt (X : BlkCaseObj s Case) {x : ↥s} (hx : X.part₁ x) :
    X.nbhdV (X.vtxPt hx) = X.nbhd x := rfl

theorem nbhdV_subset_blocks (X : BlkCaseObj s Case) (u : ↥X.vtxSet) :
    X.nbhdV u ⊆ X.blocks := fun _ hB => hB.1

/-- §9.7.  The color `Babai.BlkCaseObj.linkColor` does occur on `V₁ × V₂`: there is at
least one point of `V₁` and at least one block, so at least one color occurs there, and
`Babai.BlkCaseObj.linkColor` is the least one. -/
theorem hasLinkColor_linkColor (X : BlkDesignObj s) : X.HasLinkColor X.linkColor := by
  classical
  obtain ⟨x, hx⟩ := X.part₁_nonempty
  obtain ⟨B, hB⟩ := BlkBlockDesignInputs.blocks_nonempty_of_case X.case
  have hex : ∃ k, X.HasLinkColor k := ⟨X.c {x} B, x, hx, B, hB, rfl⟩
  rw [linkColor, dif_pos hex]
  exact Nat.find_spec hex

/-- §9.7.  Observation 3.3.4: the head of an edge of the color
`Babai.BlkCaseObj.linkColor` is a vertex of `V₂`, that is, a block. -/
theorem val_image_setOf_vc_eq (X : BlkDesignObj s) (u : ↥X.vtxSet) :
    Subtype.val '' {v : ↥X.vtxSet | X.vc u v = X.linkColor} = X.nbhdV u := by
  obtain ⟨x₀, hx₀, B₀, hB₀, hcol₀⟩ := X.hasLinkColor_linkColor
  ext A
  constructor
  · rintro ⟨v, hv, rfl⟩
    have hv' : X.vc u v = X.linkColor := hv
    have heq : X.vc u v = X.vc (X.vtxPt hx₀) (X.vtxBlk hB₀) := by
      rw [hv']; exact hcol₀.symm
    exact ⟨(X.bipData.head_mem_part₂_iff heq).2 (X.vtxBlk_mem₂ hB₀), hv'⟩
  · rintro ⟨hAb, hAc⟩
    exact ⟨X.vtxBlk hAb, hAc, rfl⟩

open scoped Classical in
/-- §9.7.  *"`X₁` is a UPCC"* (the field `upcc₁` of `Babai.IsBipartiteCase`), read as the
uniprimitivity of the subconfiguration that the configuration of step 3 of §9.4 induces on
its first vertex class.  This is the only place in §9.7 that reads that field. -/
theorem induced_isUniprimitive₁ (X : BlkDesignObj s) [Fintype ↥X.vtxSet]
    [Fintype ↥(X.bipData.P.vertexClass X.bipData.i)] :
    (X.bipData.P.induced (X.bipData.P.vertexClass X.bipData.i)).IsUniprimitive := by
  obtain ⟨Q, -, hQ, hQnat⟩ := X.bipCase'.upcc₁
  exact X.bipData.induced_isUniprimitive₁ hQ hQnat

open scoped Classical in
/-- §9.7.  `Babai.BlkCaseObj.induced_isUniprimitive₁` at a color named as the tail color of
a constituent of the link rather than as `Babai.BipCaseData.i`. -/
theorem induced_isPrimitive₁_at (X : BlkDesignObj s) [Fintype ↥X.vtxSet]
    {i' : Fin X.bipData.P.rank} [Fintype ↥(X.bipData.P.vertexClass i')]
    (hi : i' = X.bipData.i) :
    (X.bipData.P.induced (X.bipData.P.vertexClass i')).IsPrimitive := by
  subst hi; exact X.induced_isUniprimitive₁.1

/-- §9.7.  *"`H` … is uniform of rank `d₁`"*: all the neighborhoods `X(v)`, `v ∈ V₁`, have
the same size.

This is the semiregularity of the constituent `Rᵢ` of the link that step 8 of §9.4 picks
out: `Rᵢ` is a constituent of the coherent configuration `X` of step 3 of §9.4 (the field
`coherent` of `Babai.IsBipartiteCase`), and by Obs. 3.3.5 (degree awareness,
`Babai.PartitionStructure.outDegC_eq_of_vcolor_eq`) the out-degree in a fixed color depends
only on the vertex color, which is the same for all the vertices of `V₁`.

(The statement is not vacuous in the degenerate cases: for `d₁ = 0` it says that all
neighborhoods are empty, and for `V₁` a single point it is trivial.) -/
theorem nbhd_ncard_uniform (X : BlkDesignObj s) {x y : ↥s} (hx : X.part₁ x)
    (hy : X.part₁ y) : (X.nbhd x).ncard = (X.nbhd y).ncard := by
  classical
  have hvc : X.bipData.P.vcolor (X.vtxPt hx) = X.bipData.P.vcolor (X.vtxPt hy) := by
    rw [(X.bipData.mem_part₁_iff _).1 (X.vtxPt_mem₁ hx),
      (X.bipData.mem_part₁_iff _).1 (X.vtxPt_mem₁ hy)]
  have h := X.bipData.ncard_nbhd_eq hvc X.linkColor
  rw [← X.nbhdV_vtxPt hx, ← X.nbhdV_vtxPt hy, ← X.val_image_setOf_vc_eq (X.vtxPt hx),
    ← X.val_image_setOf_vc_eq (X.vtxPt hy),
    Set.ncard_image_of_injective _ Subtype.val_injective,
    Set.ncard_image_of_injective _ Subtype.val_injective]
  exact h

/-- §9.7.  *"This hypergraph has no multiple edges because there are no twins in `V₁`."*
Two different points of `V₁` have different neighborhoods.

The reason is the Claim of step 8 of §9.4 (`Babai.claim_9_4_step8`), which is Theorem 3.4.11
(*"no twins in primitive color"*) applied to the constituent `Rᵢ` of the link: `X₁` is a
UPCC, hence primitive (the field `upcc₁` of `Babai.IsBipartiteCase`), and the constituent is
nontrivial — it is nonempty because `Babai.BlkCaseObj.linkColor` is a color that occurs on
`V₁ × V₂`, and it is not complete because the link is nontrivial (the field
`link_nontrivial`), i.e. a second color occurs there.  The form of Theorem 3.4.11 that is
used is `Babai.PartitionStructure.nbr_ne_of_primitive`, which is literally *"distinct
vertices of the tail class have distinct `R_k`-neighbourhoods"*.

Note that the field `noTwins₁` of `Babai.IsBlockDesignCase` is **not** enough: it says that
no two points of `V₁` are twins for the whole coloring `c`, while what is needed here is
that no two of them have the same neighborhood in the **single** constituent
`Babai.BlkCaseObj.linkColor`.

-/
theorem nbhd_injective (X : BlkDesignObj s) {x y : ↥s} (hx : X.part₁ x) (hy : X.part₁ y)
    (hxy : X.nbhd x = X.nbhd y) : x = y := by
  classical
  letI : Fintype ↥X.vtxSet := Fintype.ofFinite _
  letI : DecidableEq ↥X.vtxSet := Classical.decEq _
  obtain ⟨x₀, hx₀, B₀, hB₀, hcol₀⟩ := X.hasLinkColor_linkColor
  set D := X.bipData with hD
  set ux₀ : ↥X.vtxSet := X.vtxPt hx₀ with hux₀
  set vB₀ : ↥X.vtxSet := X.vtxBlk hB₀ with hvB₀
  set k : Fin D.P.rank := D.P.color ux₀ vB₀ with hk
  -- the constituent `Rᵢ` of the link, named by `Babai.BlkCaseObj.linkColor`
  have hkval : (k : ℕ) = X.linkColor := by rw [hk, ← D.color_val ux₀ vB₀]; exact hcol₀
  have hmemk : ∀ u v : ↥X.vtxSet, D.P.color u v = k ↔ X.vc u v = X.linkColor := by
    intro u v
    rw [D.color_val u v, ← hkval]
    exact ⟨fun hc => by rw [hc], fun hc => Fin.ext hc⟩
  have hnbr : ∀ u : ↥X.vtxSet, D.P.nbr k u = {v | X.vc u v = X.linkColor} := by
    intro u; ext v; rw [PartitionStructure.mem_nbr]; exact hmemk u v
  -- its tail class is `V₁`, its head class is `V₂`
  have htail : D.P.tailColor k = D.i :=
    (D.P.vcolor_fst_eq D.isCoherent hk.symm).symm.trans
      ((D.mem_part₁_iff ux₀).1 (X.vtxPt_mem₁ hx₀))
  have hhead : D.P.headColor k = D.j :=
    (D.P.vcolor_snd_eq D.isCoherent hk.symm).symm.trans
      ((D.mem_part₂_iff vB₀).1 (X.vtxBlk_mem₂ hB₀))
  have hmemtail : ∀ {z : ↥s} (hz : X.part₁ z),
      X.vtxPt hz ∈ D.P.vertexClass (D.P.tailColor k) := by
    intro z hz
    show D.P.vcolor (X.vtxPt hz) = D.P.tailColor k
    rw [htail]; exact (D.mem_part₁_iff _).1 (X.vtxPt_mem₁ hz)
  -- the constituent is nontrivial (Theorem 3.4.11's hypothesis)
  have hnt : ¬ (D.P.bipConstituent k).IsTrivial := by
    rintro (hempty | huniv)
    · have hmem : ((⟨ux₀, hmemtail hx₀⟩ :
          ↥(D.P.vertexClass (D.P.tailColor k))),
          (⟨vB₀, D.P.vcolor_snd_eq D.isCoherent hk.symm⟩ :
          ↥(D.P.vertexClass (D.P.headColor k)))) ∈ (D.P.bipConstituent k).E := hk.symm
      rw [hempty] at hmem
      exact hmem
    · obtain ⟨a₁, b₁, a₂, b₂, hne⟩ := X.bipCase'.link_nontrivial
      refine hne ?_
      have hcolor : ∀ (a : ↥{u : ↥X.vtxSet | (u : Set ↥s) ∈ X.sglSet})
          (b : ↥{u : ↥X.vtxSet | (u : Set ↥s) ∈ X.blocks}),
          X.vc (a : ↥X.vtxSet) (b : ↥X.vtxSet) = X.linkColor := by
        intro a b
        refine (hmemk (a : ↥X.vtxSet) (b : ↥X.vtxSet)).1 ?_
        have hamem : (a : ↥X.vtxSet) ∈ D.P.vertexClass (D.P.tailColor k) := by
          show D.P.vcolor (a : ↥X.vtxSet) = D.P.tailColor k
          rw [htail]; exact (D.mem_part₁_iff _).1 a.2
        have hbmem : (b : ↥X.vtxSet) ∈ D.P.vertexClass (D.P.headColor k) := by
          show D.P.vcolor (b : ↥X.vtxSet) = D.P.headColor k
          rw [hhead]; exact (D.mem_part₂_iff _).1 b.2
        have : ((⟨(a : ↥X.vtxSet), hamem⟩ : ↥(D.P.vertexClass (D.P.tailColor k))),
            (⟨(b : ↥X.vtxSet), hbmem⟩ : ↥(D.P.vertexClass (D.P.headColor k))))
            ∈ (D.P.bipConstituent k).E := by rw [huniv]; exact Set.mem_univ _
        exact this
      rw [hcolor a₁ b₁, hcolor a₂ b₂]
  -- `X₁` is primitive (Theorem 3.4.11's other hypothesis)
  have hprim : (D.P.induced (D.P.vertexClass (D.P.tailColor k))).IsPrimitive :=
    X.induced_isPrimitive₁_at htail
  -- Theorem 3.4.11 in the form `Babai.PartitionStructure.nbr_ne_of_primitive`
  have hnbeq : D.P.nbr k (X.vtxPt hx) = D.P.nbr k (X.vtxPt hy) := by
    rw [hnbr, hnbr]
    refine Set.image_injective.2 Subtype.val_injective ?_
    rw [X.val_image_setOf_vc_eq, X.val_image_setOf_vc_eq, X.nbhdV_vtxPt, X.nbhdV_vtxPt]
    exact hxy
  have hvtx : X.vtxPt hx = X.vtxPt hy := by
    by_contra hcon
    exact D.P.nbr_ne_of_primitive D.isCoherent k hnt hprim (hmemtail hx) (hmemtail hy)
      hcon hnbeq
  have : ({x} : Set ↥s) = {y} := congrArg Subtype.val hvtx
  exact Set.singleton_injective this

/-- Uniformity, read against the definition of `Babai.BlkCaseObj.d₁` as a supremum: every
neighborhood has exactly `d₁` blocks. -/
theorem nbhd_ncard_eq_d₁ (X : BlkDesignObj s) {x : ↥s} (hx : X.part₁ x) :
    (X.nbhd x).ncard = X.d₁ := by
  have hset : {n | ∃ y, X.part₁ y ∧ (X.nbhd y).ncard = n} = {(X.nbhd x).ncard} := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨y, hy, rfl⟩; exact X.nbhd_ncard_uniform hy hx
    · rintro rfl; exact ⟨x, hx, rfl⟩
  rw [d₁, hset, csSup_singleton]

/-- `d₁ ≤ n₂`: a neighborhood is a family of blocks. -/
theorem d₁_le_numBlocks (X : BlkDesignObj s) : X.d₁ ≤ X.blocks.ncard := by
  obtain ⟨x, hx⟩ := X.part₁_nonempty
  rw [← X.nbhd_ncard_eq_d₁ hx]
  exact Set.ncard_le_ncard (X.nbhd_subset_blocks x) (Set.toFinite _)

/-! #### The labelling of `V₁` by `d₁`-subsets of `V₂` -/

open scoped Classical in
/-- §9.7, Case 1.  *"Let us label `v ∈ V₁` by the set `X(v)`"*, the label being read as a
finite set of vertices of `V₂`. -/
noncomputable def label (X : BlkCaseObj s Case) (x : ↥s) : Finset ↥X.blocks :=
  (Set.toFinite {B : ↥X.blocks | (B : Set ↥s) ∈ X.nbhd x}).toFinset

/-- A family of blocks has as many members read inside `V₂` as read among the subsets of
the point set. -/
theorem ncard_coe_blocks (X : BlkCaseObj s Case) {T : Set (Set ↥s)} (hT : T ⊆ X.blocks) :
    {B : ↥X.blocks | (B : Set ↥s) ∈ T}.ncard = T.ncard := by
  have himg : Subtype.val '' {B : ↥X.blocks | (B : Set ↥s) ∈ T} = T := by
    ext A
    constructor
    · rintro ⟨B, hB, rfl⟩; exact hB
    · intro hA; exact ⟨⟨A, hT hA⟩, hA, rfl⟩
  have hc := Set.ncard_image_of_injective {B : ↥X.blocks | (B : Set ↥s) ∈ T}
    Subtype.val_injective
  rw [himg] at hc
  exact hc.symm

theorem card_label (X : BlkCaseObj s Case) (x : ↥s) :
    (X.label x).card = (X.nbhd x).ncard := by
  classical
  rw [label, ← Set.ncard_eq_toFinset_card _ (Set.toFinite _),
    X.ncard_coe_blocks (X.nbhd_subset_blocks x)]

theorem card_label_sdiff (X : BlkCaseObj s Case) (x y : ↥s) :
    ((X.label x) \ (X.label y)).card = X.johnsonColor x y := by
  classical
  have hset : ((X.label x) \ (X.label y))
      = (Set.toFinite {B : ↥X.blocks | (B : Set ↥s) ∈ X.nbhd x \ X.nbhd y}).toFinset := by
    ext B
    simp only [Finset.mem_sdiff, label, Set.Finite.mem_toFinset, Set.mem_setOf_eq,
      Set.mem_diff]
  rw [hset, ← Set.ncard_eq_toFinset_card _ (Set.toFinite _),
    X.ncard_coe_blocks (fun A hA => X.nbhd_subset_blocks x hA.1)]
  rfl

theorem label_injective (X : BlkDesignObj s) {x y : ↥s} (hx : X.part₁ x) (hy : X.part₁ y)
    (hxy : X.label x = X.label y) : x = y := by
  classical
  refine X.nbhd_injective hx hy ?_
  ext A
  by_cases hA : A ∈ X.blocks
  · have h1 : (⟨A, hA⟩ : ↥X.blocks) ∈ X.label x ↔ (⟨A, hA⟩ : ↥X.blocks) ∈ X.label y := by
      rw [hxy]
    simpa only [label, Set.Finite.mem_toFinset, Set.mem_setOf_eq] using h1
  · exact ⟨fun h' => absurd (X.nbhd_subset_blocks x h') hA,
      fun h' => absurd (X.nbhd_subset_blocks y h') hA⟩

/-- §9.7, Case 1.  *"`H` is the complete `d₁`-uniform hypergraph"*: every `d₁`-subset of
`V₂` is the label of a point of `V₁`. -/
theorem label_surjective (X : BlkDesignObj s) (h : X.IsCase1) (T : Finset ↥X.blocks)
    (hT : T.card = X.d₁) : ∃ x, X.part₁ x ∧ X.label x = T := by
  classical
  obtain ⟨x₀, hx₀⟩ := X.part₁_nonempty
  have hT₀b : (Subtype.val '' (T : Set ↥X.blocks)) ⊆ X.blocks := by
    rintro _ ⟨B, -, rfl⟩; exact B.2
  have hT₀card : (Subtype.val '' (T : Set ↥X.blocks)).ncard = (X.nbhd x₀).ncard := by
    rw [Set.ncard_image_of_injective _ Subtype.val_injective, X.nbhd_ncard_eq_d₁ hx₀,
      ← hT, Set.ncard_coe_finset]
  obtain ⟨x, hx, hnb⟩ :=
    isCase1_mem_edgeFam h _ (X.nbhd x₀) (Subtype.val '' (T : Set ↥X.blocks))
      ⟨x₀, hx₀, rfl⟩ (X.nbhd_subset_blocks x₀) hT₀b hT₀card rfl
  refine ⟨x, hx, ?_⟩
  ext B
  simp only [label, Set.Finite.mem_toFinset, Set.mem_setOf_eq, hnb]
  constructor
  · rintro ⟨B', hB'mem, hB'⟩
    have hBB : B' = B := Subtype.ext hB'
    exact Finset.mem_coe.1 (hBB ▸ hB'mem)
  · intro hB; exact ⟨B, Finset.mem_coe.2 hB, rfl⟩

open scoped Classical in
/-- §9.7, Case 1.  *"This establishes a bijection between `V₁` and the set
`(V₂ choose d₁)`."* -/
noncomputable def labelEquiv (X : BlkDesignObj s) (h : X.IsCase1) :
    ↥{x : ↥s | X.part₁ x} ≃ binom ↥X.blocks X.d₁ :=
  Equiv.ofBijective (fun x => ⟨X.label (x : ↥s), by
      rw [X.card_label, X.nbhd_ncard_eq_d₁ x.2]⟩)
    ⟨fun x y hxy => Subtype.ext (X.label_injective x.2 y.2 (congrArg Subtype.val hxy)),
     fun T => by
       obtain ⟨x, hx, hlab⟩ := X.label_surjective h (T : Finset ↥X.blocks) T.2
       exact ⟨⟨x, hx⟩, Subtype.ext hlab⟩⟩

@[simp] theorem labelEquiv_coe (X : BlkDesignObj s) (h : X.IsCase1)
    (x : ↥{x : ↥s | X.part₁ x}) :
    ((X.labelEquiv h x : binom ↥X.blocks X.d₁) : Finset ↥X.blocks) = X.label (x : ↥s) :=
  rfl

open scoped Classical in
/-- §9.7, Case 1, entry 41 of the corrected paper.  `n₂ ≠ 2d₁`.

The boundary `n₂ = 2d₁` is the one case in which neither the labels `X(v)` nor their
complements satisfy the constraint `2t + 1 ≤ k` of Def. 3.2.9, so that
`Babai.isJohnsonColoring_of_labels` does not apply.  It is excluded by the primitivity of
`X₁`: the scheme `J(2d₁, d₁)` is imprimitive, its constituent `|S ∖ T| = d₁` being the
perfect matching `S ↔ V₂ ∖ S`; that relation is *"`u` and `v` have no common neighbour"*, an
intersection number of the coherent configuration `X`, hence a union of constituents of
`X₁`, each of them a non-empty subgraph of a perfect matching — contradicting the
primitivity of `X₁`.

The proof runs the argument of entry 41 inside the coherent configuration `X` of step 3 of
§9.4, where *"the number of common neighbours"* is an intersection number
(`Babai.PartitionStructure.ncard_inter_nbr_eq_interNum`) and so depends on a pair of
vertices of `V₁` only through its color.  Write `L = X(x₀)` for the label of one point `x₀`
of `V₁`.  Case 1 makes `V₂ ∖ L`, which has `n₂ − d₁ = d₁` blocks, again a hyperedge, say
`X(y₀)`; and `x₀ ≠ y₀` because `L` is not empty.  Let `ℓ` be the color of `(x₀, y₀)` in
`X₁`.  Every `ℓ`-edge `(u,v)` then has `|X(u) ∩ X(v)| = |X(x₀) ∩ X(y₀)| = 0`, so
`X(u) = V₂ ∖ X(v)`, because both have `d₁ = n₂/2` blocks.  *"Same or complementary label"*
is an equivalence relation, so by the weak connectivity of the `ℓ`-constituent — `X₁` is a
UPCC, hence primitive, and `ℓ` is off-diagonal — every point of `V₁` has label `L` or
`V₂ ∖ L`.  The labels are distinct (`Babai.BlkCaseObj.nbhd_injective`), so `V₁` has at most
two points, while a UPCC has at least three vertices
(`Babai.BipCaseData.three_le_ncard_part₁`). -/
theorem numBlocks_ne_two_mul_d₁ (X : BlkDesignObj s) (h : X.IsCase1) :
    X.blocks.ncard ≠ 2 * X.d₁ := by
  classical
  letI : Fintype ↥X.vtxSet := Fintype.ofFinite _
  letI : DecidableEq ↥X.vtxSet := Classical.decEq _
  intro heq
  -- the constituent `Rᵢ` of the link, named by `Babai.BlkCaseObj.linkColor`
  obtain ⟨x₁, hx₁, B₁, hB₁, hcol₁⟩ := X.hasLinkColor_linkColor
  set k : Fin X.bipData.P.rank :=
    X.bipData.P.color (X.vtxPt hx₁) (X.vtxBlk hB₁) with hk
  have hkval : (k : ℕ) = X.linkColor := by
    rw [hk, ← X.bipData.color_val (X.vtxPt hx₁) (X.vtxBlk hB₁)]; exact hcol₁
  have hnbr : ∀ u : ↥X.vtxSet,
      X.bipData.P.nbr k u = {v | X.vc u v = X.linkColor} := by
    intro u; ext v
    show X.bipData.P.color u v = k ↔ X.vc u v = X.linkColor
    rw [X.bipData.color_val u v, ← hkval]
    exact ⟨fun hc => by rw [hc], fun hc => Fin.ext hc⟩
  have hnbrV : ∀ u : ↥X.vtxSet,
      Subtype.val '' (X.bipData.P.nbr k u) = X.nbhdV u := by
    intro u; rw [hnbr u]; exact X.val_image_setOf_vc_eq u
  -- `d₁ ≥ 1`
  have hn₂pos : 0 < X.blocks.ncard :=
    (Set.ncard_pos (Set.toFinite _)).2 (BlkBlockDesignInputs.blocks_nonempty_of_case X.case)
  have hd₁pos : 0 < X.d₁ := by omega
  -- the label `L = X(x₀)` and its complement, which Case 1 makes a hyperedge too
  obtain ⟨x₀, hx₀⟩ := X.part₁_nonempty
  have hLsub : X.nbhd x₀ ⊆ X.blocks := X.nbhd_subset_blocks x₀
  have hLcard : (X.nbhd x₀).ncard = X.d₁ := X.nbhd_ncard_eq_d₁ hx₀
  have hLccard : (X.blocks \ X.nbhd x₀).ncard = X.d₁ := by
    rw [Set.ncard_diff hLsub (Set.toFinite _), hLcard]; omega
  obtain ⟨y₀, hy₀, hnby₀⟩ : ∃ y, X.part₁ y ∧ X.nbhd y = X.blocks \ X.nbhd x₀ :=
    isCase1_mem_edgeFam h ((X.nbhd x₀ \ (X.blocks \ X.nbhd x₀)).ncard) (X.nbhd x₀)
      (X.blocks \ X.nbhd x₀) ⟨x₀, hx₀, rfl⟩ hLsub Set.diff_subset
      (by rw [hLcard, hLccard]) rfl
  have hLne : (X.nbhd x₀).Nonempty := (Set.ncard_pos (Set.toFinite _)).1 (by omega)
  have hx₀y₀ : x₀ ≠ y₀ := by
    intro hcon
    obtain ⟨B, hB⟩ := hLne
    have hBc : B ∈ X.blocks \ X.nbhd x₀ := by rw [← hnby₀, ← hcon]; exact hB
    exact hBc.2 hB
  -- the vertices of `V₁`, and the color `ℓ` of the pair `(x₀, y₀)` in `X₁`
  have hmemi : ∀ {z : ↥s} (hz : X.part₁ z),
      X.vtxPt hz ∈ X.bipData.P.vertexClass X.bipData.i :=
    fun hz => (X.bipData.mem_part₁_iff _).1 (X.vtxPt_mem₁ hz)
  set l : Fin (X.bipData.P.induced (X.bipData.P.vertexClass X.bipData.i)).rank :=
    (X.bipData.P.induced (X.bipData.P.vertexClass X.bipData.i)).color
      ⟨X.vtxPt hx₀, hmemi hx₀⟩ ⟨X.vtxPt hy₀, hmemi hy₀⟩ with hl
  have ha₀b₀ : (⟨X.vtxPt hx₀, hmemi hx₀⟩ :
      ↥(X.bipData.P.vertexClass X.bipData.i)) ≠ ⟨X.vtxPt hy₀, hmemi hy₀⟩ := by
    intro hcon
    exact hx₀y₀ (Set.singleton_injective
      (congrArg Subtype.val (congrArg Subtype.val hcon)))
  have hloff :
      (X.bipData.P.induced (X.bipData.P.vertexClass X.bipData.i)).IsOffDiagonalColor l := by
    rcases (X.bipData.P.induced (X.bipData.P.vertexClass X.bipData.i)).diagonal_or_offDiagonal
      (X.bipData.P.induced_isConfiguration _ X.bipData.isCoherent.toIsConfiguration) l
      with hd | ho
    · exact absurd (hd (show ((⟨X.vtxPt hx₀, hmemi hx₀⟩ :
        ↥(X.bipData.P.vertexClass X.bipData.i)), (⟨X.vtxPt hy₀, hmemi hy₀⟩ :
        ↥(X.bipData.P.vertexClass X.bipData.i))) ∈
        (X.bipData.P.induced (X.bipData.P.vertexClass X.bipData.i)).rel l from hl.symm))
        ha₀b₀
    · exact ho
  -- *"same or complementary label"* is an equivalence relation
  have hrefl : ∀ a : ↥(X.bipData.P.vertexClass X.bipData.i),
      X.nbhdV (a : ↥X.vtxSet) = X.nbhdV (a : ↥X.vtxSet) ∨
        X.nbhdV (a : ↥X.vtxSet) = X.blocks \ X.nbhdV (a : ↥X.vtxSet) := fun _ => Or.inl rfl
  have hsymm : ∀ {a b : ↥(X.bipData.P.vertexClass X.bipData.i)},
      (X.nbhdV (a : ↥X.vtxSet) = X.nbhdV (b : ↥X.vtxSet) ∨
        X.nbhdV (a : ↥X.vtxSet) = X.blocks \ X.nbhdV (b : ↥X.vtxSet)) →
      (X.nbhdV (b : ↥X.vtxSet) = X.nbhdV (a : ↥X.vtxSet) ∨
        X.nbhdV (b : ↥X.vtxSet) = X.blocks \ X.nbhdV (a : ↥X.vtxSet)) := by
    rintro a b (h1 | h1)
    · exact Or.inl h1.symm
    · exact Or.inr (by rw [h1, Set.diff_diff_cancel_left (X.nbhdV_subset_blocks _)])
  have htrans : ∀ {a b c : ↥(X.bipData.P.vertexClass X.bipData.i)},
      (X.nbhdV (a : ↥X.vtxSet) = X.nbhdV (b : ↥X.vtxSet) ∨
        X.nbhdV (a : ↥X.vtxSet) = X.blocks \ X.nbhdV (b : ↥X.vtxSet)) →
      (X.nbhdV (b : ↥X.vtxSet) = X.nbhdV (c : ↥X.vtxSet) ∨
        X.nbhdV (b : ↥X.vtxSet) = X.blocks \ X.nbhdV (c : ↥X.vtxSet)) →
      (X.nbhdV (a : ↥X.vtxSet) = X.nbhdV (c : ↥X.vtxSet) ∨
        X.nbhdV (a : ↥X.vtxSet) = X.blocks \ X.nbhdV (c : ↥X.vtxSet)) := by
    rintro a b c (h1 | h1) (h2 | h2)
    · exact Or.inl (h1.trans h2)
    · exact Or.inr (h1.trans h2)
    · exact Or.inr (by rw [h1, h2])
    · exact Or.inl (by rw [h1, h2, Set.diff_diff_cancel_left (X.nbhdV_subset_blocks _)])
  -- all labels have `d₁` blocks, and disjoint labels are complementary
  have hcardV : ∀ u : ↥X.vtxSet, u ∈ X.bipData.P.vertexClass X.bipData.i →
      (X.nbhdV u).ncard = X.d₁ := by
    intro u hu
    obtain ⟨z, hz, hzu⟩ := (X.bipData.mem_part₁_iff u).2 hu
    have hnb : X.nbhdV u = X.nbhd z := by
      show {B | B ∈ X.blocks ∧ X.c (u : Set ↥s) B = X.linkColor} = _
      rw [hzu]; rfl
    rw [hnb, X.nbhd_ncard_eq_d₁ hz]
  have hcompl : ∀ u v : ↥X.vtxSet, u ∈ X.bipData.P.vertexClass X.bipData.i →
      v ∈ X.bipData.P.vertexClass X.bipData.i →
      X.bipData.P.nbr k u ∩ X.bipData.P.nbr k v = ∅ →
      X.nbhdV u = X.blocks \ X.nbhdV v := by
    intro u v hu hv hzero
    have hdisj : X.nbhdV u ∩ X.nbhdV v = ∅ := by
      rw [← hnbrV u, ← hnbrV v, ← Set.image_inter Subtype.val_injective, hzero,
        Set.image_empty]
    refine Set.eq_of_subset_of_ncard_le (fun B hB => ⟨X.nbhdV_subset_blocks u hB, ?_⟩) ?_
      (Set.toFinite _)
    · intro hBv
      have : B ∈ X.nbhdV u ∩ X.nbhdV v := ⟨hB, hBv⟩
      rw [hdisj] at this
      exact this
    · rw [Set.ncard_diff (X.nbhdV_subset_blocks v) (Set.toFinite _), hcardV u hu,
        hcardV v hv]
      omega
  -- an `ℓ`-edge joins complementary labels
  have hstep : ∀ a b : ↥(X.bipData.P.vertexClass X.bipData.i),
      ((X.bipData.P.induced (X.bipData.P.vertexClass X.bipData.i)).extConstituent l).Adj a b →
      (X.nbhdV (a : ↥X.vtxSet) = X.nbhdV (b : ↥X.vtxSet) ∨
        X.nbhdV (a : ↥X.vtxSet) = X.blocks \ X.nbhdV (b : ↥X.vtxSet)) := by
    intro a b hab
    have hcl : (X.bipData.P.induced (X.bipData.P.vertexClass X.bipData.i)).color a b = l := hab
    have hcolP : X.bipData.P.color (a : ↥X.vtxSet) (b : ↥X.vtxSet)
        = X.bipData.P.color (X.vtxPt hx₀) (X.vtxPt hy₀) :=
      (X.bipData.P.induced_color_eq_iff _ a b ⟨X.vtxPt hx₀, hmemi hx₀⟩
        ⟨X.vtxPt hy₀, hmemi hy₀⟩).1 (hcl.trans hl)
    -- the two labels of `(x₀, y₀)` are disjoint
    have hzero₀ : X.bipData.P.nbr k (X.vtxPt hx₀) ∩ X.bipData.P.nbr k (X.vtxPt hy₀) = ∅ := by
      ext v
      simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
      intro h1 h2
      have e1 : (v : Set ↥s) ∈ X.nbhd x₀ := by
        rw [← X.nbhdV_vtxPt hx₀, ← hnbrV]; exact ⟨v, h1, rfl⟩
      have e2 : (v : Set ↥s) ∈ X.blocks \ X.nbhd x₀ := by
        rw [← hnby₀, ← X.nbhdV_vtxPt hy₀, ← hnbrV]; exact ⟨v, h2, rfl⟩
      exact e2.2 e1
    -- *"isomorphisms preserve the number of common neighbours"*
    have hzero : X.bipData.P.nbr k (a : ↥X.vtxSet) ∩ X.bipData.P.nbr k (b : ↥X.vtxSet) = ∅ := by
      have hn : (X.bipData.P.nbr k (a : ↥X.vtxSet) ∩ X.bipData.P.nbr k (b : ↥X.vtxSet)).ncard
          = 0 := by
        rw [X.bipData.P.ncard_inter_nbr_eq_interNum X.bipData.isCoherent k, hcolP,
          ← X.bipData.P.ncard_inter_nbr_eq_interNum X.bipData.isCoherent k, hzero₀,
          Set.ncard_empty]
      exact (Set.ncard_eq_zero (Set.toFinite _)).1 hn
    exact Or.inr (hcompl _ _ a.2 b.2 hzero)
  -- weak connectivity of the `ℓ`-constituent of `X₁`
  have key : ∀ z (hz : X.part₁ z),
      X.nbhd z = X.nbhd x₀ ∨ X.nbhd z = X.blocks \ X.nbhd x₀ := by
    intro z hz
    have hacc := X.induced_isPrimitive₁_at (i' := X.bipData.i) rfl |>.2 l hloff
      ⟨X.vtxPt hz, hmemi hz⟩ ⟨X.vtxPt hx₀, hmemi hx₀⟩
    exact ((X.bipData.P.induced (X.bipData.P.vertexClass X.bipData.i)).extConstituent
      l).weaklyAccessible_rel
      (r := fun a b => X.nbhdV (a : ↥X.vtxSet) = X.nbhdV (b : ↥X.vtxSet) ∨
        X.nbhdV (a : ↥X.vtxSet) = X.blocks \ X.nbhdV (b : ↥X.vtxSet))
      hrefl hsymm htrans hstep hacc
  -- so `V₁` has at most two vertices, while a UPCC has at least three
  have hthree : 3 ≤ ({u : ↥X.vtxSet | (u : Set ↥s) ∈ X.sglSet}).ncard :=
    X.bipData.three_le_ncard_part₁ X.induced_isUniprimitive₁
  have hsub : {u : ↥X.vtxSet | (u : Set ↥s) ∈ X.sglSet}
      ⊆ {X.vtxPt hx₀, X.vtxPt hy₀} := by
    intro u hu
    obtain ⟨z, hz, hzu⟩ := hu
    rw [Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases key z hz with hc | hc
    · refine Or.inl (Subtype.ext ?_)
      show (u : Set ↥s) = {x₀}
      rw [hzu, X.nbhd_injective hz hx₀ hc]
    · refine Or.inr (Subtype.ext ?_)
      show (u : Set ↥s) = {y₀}
      rw [hzu, X.nbhd_injective hz hy₀ (hc.trans hnby₀.symm)]
  have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
  have hpair : ({X.vtxPt hx₀, X.vtxPt hy₀} : Set ↥X.vtxSet).ncard ≤ 2 :=
    le_trans (Set.ncard_insert_le _ _) (by rw [Set.ncard_singleton])
  omega

/-! #### The two hypotheses of Theorem 8.1.2 that §9.7 skips

Case 3 applies the Design Lemma to `H`, and Theorem 8.1.2 asks for `2 ≤ k ≤ n/2`, here
`2 ≤ d₁` and `2d₁ ≤ n₂`.  §9.7 checks neither.  The first holds; the second does not in
general, and the rank at which the Design Lemma is run is `Babai.BlkCaseObj.d'`, for which
both hold.  See the entry *"§9.7 Case 3: the Design Lemma is applied at rank `d₁` without
checking `d₁ ≤ n₂/2`"* in the corrected paper. -/

/-- §9.7.  *"This hypergraph has no multiple edges … and is uniform of rank `d₁`"*: the
labels `X(v)` are `n₁` distinct `d₁`-subsets of `V₂`, so `n₁ ≤ C(n₂, d₁)`. -/
theorem n₁_le_choose (X : BlkDesignObj s) : X.n₁ ≤ X.n₂.choose X.d₁ := by
  classical
  letI : Fintype ↥X.blocks := Fintype.ofFinite _
  have hinj : Function.Injective
      (fun x : ↥{x : ↥s | X.part₁ x} => (⟨X.label (x : ↥s), by
        rw [X.card_label, X.nbhd_ncard_eq_d₁ x.2]⟩ : binom ↥X.blocks X.d₁)) :=
    fun x y hxy => Subtype.ext (X.label_injective x.2 y.2 (congrArg Subtype.val hxy))
  have hcard : Nat.card ↥{x : ↥s | X.part₁ x} ≤ Nat.card (binom ↥X.blocks X.d₁) :=
    Nat.card_le_card_of_injective _ hinj
  have hb : Fintype.card ↥X.blocks = X.n₂ := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]; rfl
  rw [n₁, ← Nat.card_coe_set_eq]
  refine hcard.trans (le_of_eq ?_)
  rw [Nat.card_eq_fintype_card, Fintype.card_finset_len, hb]

/-- §9.7, Case 3, the fill of the corrected paper.  From `n₂ < n₁` — the standing hypothesis
`n₂ < αn₁ < n₁` of Theorem 9.2.2 — and `n₁ ≤ C(n₂, d₁)` one gets `2 ≤ d₁` **and**
`d₁ + 2 ≤ n₂`.  The four excluded values of `d₁` are `0` and `n₂` (one edge) and `1` and
`n₂ − 1` (at most `n₂` edges). -/
theorem two_le_d₁_and_add_two_le (X : BlkDesignObj s) (hlt : X.n₂ < X.n₁) :
    2 ≤ X.d₁ ∧ X.d₁ + 2 ≤ X.n₂ := by
  refine two_le_and_add_two_le_of_lt_choose ?_ (lt_of_lt_of_le hlt X.n₁_le_choose)
  exact (Set.ncard_pos (Set.toFinite _)).2 (BlkBlockDesignInputs.blocks_nonempty_of_case X.case)

/-- §9.7, Case 3, the fill of the corrected paper: *"`2 ≤ k`"* of Theorem 8.1.2, at the rank
`d' = min(d₁, n₂ − d₁)` at which the Design Lemma is applied. -/
theorem two_le_d' (X : BlkDesignObj s) (hlt : X.n₂ < X.n₁) : 2 ≤ X.d' := by
  obtain ⟨h1, h2⟩ := X.two_le_d₁_and_add_two_le hlt
  rw [d']; omega

/-- §9.7, Case 3, the fill of the corrected paper: *"`k ≤ n/2`"* of Theorem 8.1.2, at the rank
`d' = min(d₁, n₂ − d₁)`.  This is the hypothesis §9.7 skips and which `d₁` itself need not
satisfy. -/
theorem two_mul_d'_le_n₂ (X : BlkDesignObj s) : 2 * X.d' ≤ X.n₂ := by
  have h : X.d₁ ≤ X.n₂ := X.d₁_le_numBlocks
  rw [d']; omega

/-- `d' ≤ d₁`: the cost of Case 3 at the rank `d'` is at most the cost the paper
prints. -/
theorem d'_le_d₁ (X : BlkCaseObj s Case) : X.d' ≤ X.d₁ := min_le_left _ _

end BlkCaseObj

/-! #### Case 1 as a reduction

The outcome of Case 1 is the Johnson scheme on `V₁` itself: `Babai.Out97` holds it in the
first summand (`Babai.SplitOutcomes`), second summand (`Babai.JohnsonSchemes`), on the
vertex set `V₁`, so that the outcome `Babai.IsBlkDesignOutcome` reads *"`□Z ⊆ V₁` and
`α|V₁| ≤ |□Z|`"*, goal (b) of Theorem 9.2.2.  No choice is made, so the tuple has one
member and the cost is `1`. -/

namespace BlkCaseObj

variable {s : Set Ω} {Case : (Set ↥s → Set ↥s → ℕ) → Set (Set ↥s) → Set (Set ↥s) → Prop}

/-- A point of `V₁` read in the ambient type, as a point of `□X`. -/
def v₁Pt (X : BlkCaseObj s Case) (u : ↥(Subtype.val '' {x : ↥s | X.part₁ x})) : ↥s :=
  ⟨(u : Ω), by obtain ⟨x, -, hx⟩ := u.2; exact hx ▸ x.2⟩

theorem v₁Pt_part₁ (X : BlkCaseObj s Case)
    (u : ↥(Subtype.val '' {x : ↥s | X.part₁ x})) : X.part₁ (X.v₁Pt u) := by
  obtain ⟨x, hx, hxu⟩ := u.2
  have hxe : x = X.v₁Pt u := Subtype.ext hxu
  exact hxe ▸ hx

/-- `V₁` read in the ambient type and `V₁` read inside `□X` are the same set. -/
def v₁Equiv (X : BlkCaseObj s Case) :
    ↥(Subtype.val '' {x : ↥s | X.part₁ x}) ≃ ↥{x : ↥s | X.part₁ x} where
  toFun u := ⟨X.v₁Pt u, X.v₁Pt_part₁ u⟩
  invFun x := ⟨((x : ↥s) : Ω), ⟨(x : ↥s), x.2, rfl⟩⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext (Subtype.ext rfl)

/-- §9.7, Case 1.  The Johnson coloring of `V₁`, read on `V₁` as a subset of the ambient
type: this is the edge coloring of the object that Case 1 returns. -/
noncomputable def johnsonOutcomeColor (X : BlkCaseObj s Case) :
    ↥(Subtype.val '' {x : ↥s | X.part₁ x}) → ↥(Subtype.val '' {x : ↥s | X.part₁ x}) → ℕ :=
  fun u v => X.johnsonColor (X.v₁Pt u) (X.v₁Pt v)

end BlkCaseObj

namespace BlkBlockDesignInputs

/-- `V₁ ⊆ □X`. -/
theorem v₁_subset (X : Pt (BlkBlockDesignInputs Ω)) : BlkBlockDesignInputs.V₁ X ⊆ X.car := by
  rintro _ ⟨x, -, rfl⟩; exact x.2

/-- *"`|V₂| < α|V₁|`"* with `α < 1` gives `n₂ < n₁`. -/
theorem numBlocks_lt_n₁ (X : Pt (BlkBlockDesignInputs Ω)) :
    (obj₀ X).blocks.ncard < (obj₀ X).n₁ := by
  obtain ⟨-, hα1, hlt⟩ := X.obj.2
  have hα1' : BlkBlockDesignInputs.alpha X < 1 := hα1
  have hlt' : (((obj₀ X).blocks.ncard : ℕ) : ℝ)
      < BlkBlockDesignInputs.alpha X * (((obj₀ X).n₁ : ℕ) : ℝ) := hlt
  have hn : (0 : ℝ) ≤ (((obj₀ X).n₁ : ℕ) : ℝ) := Nat.cast_nonneg _
  have hR : (((obj₀ X).blocks.ncard : ℕ) : ℝ) < (((obj₀ X).n₁ : ℕ) : ℝ) := by nlinarith
  exact_mod_cast hR

open scoped Classical in
/-- §9.7, Case 1.  *"Since isomorphisms preserve the number of common neighbors, this
correspondence gives a canonical embedding of the Johnson scheme `J(n₂, d₁)` on `V₁`."*
The coloring `|X(u) ∖ X(v)|` of `V₁` is a Johnson coloring in the sense of Def. 3.2.13.

The parameters are checked as in entries 41 and 82 of the corrected paper: the bijection of
`V₁` with the `d₁`-subsets of `V₂` gives `n₁ = C(n₂, d₁)`, the standing hypothesis
`n₂ < αn₁ < n₁` then gives `2 ≤ d₁` and `d₁ + 2 ≤ n₂`
(`Babai.two_le_and_add_two_le_of_lt_choose`), the boundary `n₂ = 2d₁` is excluded by
`Babai.BlkCaseObj.numBlocks_ne_two_mul_d₁`, and for `d₁ > n₂/2` the labels are replaced by
their complements (`Babai.isJohnsonColoring_of_labels`). -/
theorem case1_isJohnsonColoring (X : Pt (BlkBlockDesignInputs Ω))
    (h1 : (obj₀ X).IsCase1) : IsJohnsonColoring (obj₀ X).johnsonOutcomeColor := by
  classical
  letI : Fintype ↥(obj₀ X).blocks := Fintype.ofFinite _
  letI : Fintype ↥{x : ↥X.car | (obj₀ X).part₁ x} := Fintype.ofFinite _
  have hk : Fintype.card ↥(obj₀ X).blocks = (obj₀ X).blocks.ncard := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
  have hn₁ : Fintype.card ↥{x : ↥X.car | (obj₀ X).part₁ x} = (obj₀ X).n₁ := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]; rfl
  -- `n₁ = C(n₂, d₁)`
  have hchoose : (obj₀ X).n₁ = ((obj₀ X).blocks.ncard).choose (obj₀ X).d₁ := by
    rw [← hn₁, Fintype.card_congr ((obj₀ X).labelEquiv h1), Fintype.card_finset_len, hk]
  have hlt : (obj₀ X).blocks.ncard < ((obj₀ X).blocks.ncard).choose (obj₀ X).d₁ := by
    rw [← hchoose]; exact numBlocks_lt_n₁ X
  obtain ⟨hd2, hd2'⟩ := two_le_and_add_two_le_of_lt_choose (one_le_numBlocks X) hlt
  refine isJohnsonColoring_of_labels (V := ↥(obj₀ X).blocks) hk (obj₀ X).d₁_le_numBlocks
    (((obj₀ X).v₁Equiv).trans ((obj₀ X).labelEquiv h1)) (fun u v => ?_)
    (johnson_alternative hd2 hd2' ((obj₀ X).numBlocks_ne_two_mul_d₁ h1))
  exact ((obj₀ X).card_label_sdiff ((obj₀ X).v₁Pt u) ((obj₀ X).v₁Pt v)).symm

end BlkBlockDesignInputs

/-! ### The four branches of §9.7

The four branch statements below are the four cases of §9.7, each on the full subcategory
cut out by its branch condition, each with the single cost `n₂^{7(⌊log₂ n₁⌋+1)/3 + 2}` of
`Babai.case_9_7` and the single outcome `Babai.IsBlkDesignOutcome` of `Babai.case_9_7`.
Cases 3a and 3b are stated with their own exponents (`d₁ + 2` and `t + 2`) and raised to
the common exponent by `Babai.case_9_7_exp_3a` and `Babai.case_9_7_exp_3b`, which is where
the branch condition of Case 3 is used.

**All four cases are proved.** -/

/-- The outcome category of §9.7. -/
abbrev Out97 (Ω : Type) [Fintype Ω] [DecidableEq Ω] : Cat.{0, 0} Ω :=
  Cat.sum (SplitOutcomes Ω) (BipBlockInputs Ω)

/-- The outcome of §9.7 for an input, `Babai.IsBlkDesignOutcome` read at the input. -/
def Good97 (X : Pt (BlkBlockDesignInputs Ω)) (Z : Pt (Out97 Ω)) : Prop :=
  IsBlkDesignOutcome (BlkBlockDesignInputs.alpha X) (BlkBlockDesignInputs.V₁ X)
    (BlkBlockDesignInputs.numBlocks X) Z

/-- The multiplicative cost of §9.7, `n₂^{7(⌊log₂ n₁⌋+1)/3 + 2}`. -/
noncomputable def cost97 (X : Pt (BlkBlockDesignInputs Ω)) : ℕ :=
  BlkBlockDesignInputs.numBlocks X ^
    (7 * (Nat.log 2 (BlkBlockDesignInputs.V₁ X).ncard + 1) / 3 + 2)

open BlkBlockDesignInputs in
open scoped Classical in
/-- §9.7, Case 1.  The single outcome: the Johnson scheme `J(n₂, d₁)` on `V₁`, as an object
of `Babai.Out97` on the subset `V₁` of `□X`. -/
noncomputable def case1Outcome (X : Pt ((BlkBlockDesignInputs Ω).full Case1P)) :
    (Cat.sub (Out97 Ω)).Obj X.car :=
  ⟨⟨BlkBlockDesignInputs.V₁ ⟨X.car, X.obj.1⟩,
      BlkBlockDesignInputs.v₁_subset ⟨X.car, X.obj.1⟩⟩,
    Sum.inl (Sum.inr ⟨(BlkBlockDesignInputs.obj₀
        (⟨X.car, X.obj.1⟩ : Pt (BlkBlockDesignInputs Ω))).johnsonOutcomeColor,
      BlkBlockDesignInputs.case1_isJohnsonColoring ⟨X.car, X.obj.1⟩ X.obj.2⟩)⟩

open BlkBlockDesignInputs in
/-- Case 1 of §9.7.  *"`V₂` is a set of twins in `H`. … Let us label `v ∈ V₁` by the set
`X(v)`.  This establishes a bijection between `V₁` and the set `(V₂ choose d₁)`. … this
correspondence gives a canonical embedding of the Johnson scheme `J(n₂, d₁)` on `V₁`,
achieving goal (b) of Theorem 9.2.2.  With this we not only exit this routine but exit the
main algorithm."*  (Version 2.5, lines 4240–4251.)

No choice is made, so the cost is `1`; it is weakened to the common cost of
`Babai.case_9_7` here.

**Proved.**  The construction is `Babai.case1Outcome`: the single outcome is the Johnson
scheme on `V₁` itself, so the reduction is `Babai.FindsAtMultCost.of_outcomes_sub` with a
one-member tuple, and the cost `1` is below the common cost of `Babai.case_9_7` because
`n₂ ≥ 1`.  Its four ingredients are

* *"`H` is the complete `d₁`-uniform hypergraph"*: `Babai.isCase1_mem_edgeFam`, by
  induction on `|S ∖ T|` — one transposition of blocks replaces a member of `S ∖ T` by a
  member of `T ∖ S`, and `Babai.BlkCaseObj.IsCase1` says that every such transposition
  preserves `Babai.BlkCaseObj.edgeFam`.
* *"This establishes a bijection between `V₁` and `(V₂ choose d₁)`"*:
  `Babai.BlkCaseObj.labelEquiv`, whose injectivity is
  `Babai.BlkCaseObj.nbhd_injective` (*"no multiple edges because there are no twins in
  `V₁`"*) and whose well-definedness is `Babai.BlkCaseObj.nbhd_ncard_uniform`
  (*"uniform of rank `d₁`"*).
* The parameters.  `Babai.two_le_and_add_two_le_of_lt_choose`, applied to
  `n₁ = C(n₂, d₁)` and `n₂ < n₁`, gives `2 ≤ d₁` **and** `d₁ + 2 ≤ n₂` — the first is the
  paper's missing check (entry 41 of the corrected paper), the second is what the complementary
  labels need; the boundary `n₂ = 2d₁` is `Babai.BlkCaseObj.numBlocks_ne_two_mul_d₁`.
* The labels.  `Babai.isJohnsonColoring_of_labels` builds the object of
  `Babai.JohnsonSchemes` under either of the two alternatives of
  `Babai.johnson_alternative`: `2d₁ + 1 ≤ n₂`, which is the paper's `J(n₂, d₁)`, or
  `2(n₂ − d₁) + 1 ≤ n₂`, where the labels are replaced by their complements `V₂ ∖ X(v)`
  and the scheme is `J(n₂, n₂ − d₁)` (entry 82 of the corrected paper).

Three of these ingredients rest on the named lemmas
`Babai.BlkCaseObj.nbhd_ncard_uniform`, `Babai.BlkCaseObj.nbhd_injective` and
`Babai.BlkCaseObj.numBlocks_ne_two_mul_d₁`, which read the situation of §9.7 off the
coherent configuration of step 3 of §9.4. -/
theorem case_9_7_case1 :
    FindsAtMultCost ((BlkBlockDesignInputs Ω).full Case1P) (Out97 Ω)
      (fun X => cost97 ⟨X.car, X.obj.1⟩)
      (fun X Z => Good97 ⟨X.car, X.obj.1⟩ Z) := by
  classical
  refine FindsAtMultCost.of_outcomes_sub (fun X => {case1Outcome X})
    (fun X => ⟨_, rfl⟩) (fun X => Set.finite_singleton _) (fun X => ?_)
    (fun {X Y f} hf Z hZ => ?_) (fun X Z hZ => ?_)
  · -- one outcome, and the common cost of `Babai.case_9_7` is at least `1`
    rw [Set.ncard_singleton]
    exact Nat.one_le_pow _ _ (one_le_numBlocks ⟨X.car, X.obj.1⟩)
  · -- the Johnson scheme is canonical
    rw [Set.mem_singleton_iff] at hZ
    subst hZ
    have hm : (obj₀ (⟨X.car, X.obj.1⟩ : Pt (BlkBlockDesignInputs Ω))).IsMorphOn
        (obj₀ (⟨Y.car, Y.obj.1⟩ : Pt (BlkBlockDesignInputs Ω))) f :=
      isMorphOn_of_iso (X := ⟨X.car, X.obj.1⟩) (Y := ⟨Y.car, Y.obj.1⟩) hf
    refine ⟨case1Outcome Y, rfl, ?_⟩
    refine ⟨((obj₀ (⟨X.car, X.obj.1⟩ : Pt (BlkBlockDesignInputs Ω))).v₁Equiv).trans
      ((Equiv.subtypeEquiv f (fun x => (hm.part₁ x).symm)).trans
        ((obj₀ (⟨Y.car, Y.obj.1⟩ : Pt (BlkBlockDesignInputs Ω))).v₁Equiv).symm),
      fun u => rfl, fun u v => ?_⟩
    exact hm.johnsonColor_eq _ _
  · -- goal (b) of Theorem 9.2.2 on `V₁` itself
    rw [Set.mem_singleton_iff] at hZ
    subst hZ
    refine ⟨subset_rfl, ?_⟩
    obtain ⟨-, hα1, -⟩ := X.obj.1.2
    have hα1' : BlkBlockDesignInputs.alpha ⟨X.car, X.obj.1⟩ < 1 := hα1
    have hn : (0 : ℝ) ≤ ((BlkBlockDesignInputs.V₁ ⟨X.car, X.obj.1⟩).ncard : ℝ) :=
      Nat.cast_nonneg _
    show BlkBlockDesignInputs.alpha ⟨X.car, X.obj.1⟩ *
        ((BlkBlockDesignInputs.V₁ ⟨X.car, X.obj.1⟩).ncard : ℝ)
      ≤ ((BlkBlockDesignInputs.V₁ ⟨X.car, X.obj.1⟩).ncard : ℝ)
    nlinarith

end Babai
