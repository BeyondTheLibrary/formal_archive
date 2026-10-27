/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Sections 9.5 and 9.7: the hint that a turn of Procedure Bipartite Split-or-Johnson leaves
on the pairs of blocks, and the argument of Case 3a2 that turns it into progress.
-/
import Workspace.SplitOrJohnson.BipBlocks
import Workspace.Coherent.Constituents

/-!
# §9.5, §9.7: the hint on the pairs of blocks

Version 2.5, lines 4176-4181 (§9.5) and 4281-4294 (§9.7, Cases 3a1 and 3a2).

§9.5 counts three kinds of major progress:

> *"We deem to have made major progress if any of the following occurs: goal (a) or (b) is
> achieved; `n₂` is significantly reduced; `X₂` moves from clique to UPCC while `n₂` does
> not increase."*

The third one is the subject of this file.  An object of `Babai.VColBipBlk` carries a
coloring `h` of the ordered pairs of blocks (`Babai.VColBipBlk.h`).  The object **has the
hint** when that coloring is, on the blocks, the coloring of a *homogeneous coherent
configuration of rank at least 3* on the set of blocks — the UPCC `Y` of Case 3a2, or the
equipartition of Cases 3a1 and 3b.  This is `Babai.VColBipBlk.HasHint`.

## Why the hint is progress

Case 3a2 says:

> *"Let `U ⊆ V₂` be the part selected, and `(X₂)_new` the homogeneous coherent
> configuration obtained on `U`.  If `(X₂)_new` is a UPCC, exit, significant progress.  If
> `(X₂)_new` is not a UPCC, i.e., it has rank 2, then `U` was a clique in `Y` and therefore
> `|U| ≤ |W|/2 ≤ n₂/2` by Prop. 2.4.11."*

The argument is `Babai.PartitionStructure.two_mul_ncard_le_of_clique`: a set `D` of blocks
all of whose *ordered pairs of distinct members* carry one color of a homogeneous coherent
configuration `P` of rank `≥ 3` has `2|D| ≤ n₂`.  Indeed a homogeneous configuration has
exactly one diagonal color, so of the `≥ 3` colors at least two are off-diagonal; `D` uses
only one of them, so `D` is an independent set of the other, which is a non-empty biregular
digraph on all the blocks, and Prop. 2.4.11 (`Babai.Digraph.ncard_independent_le`) gives
`2|D| ≤ n₂`.

The same statement read on an object that has the hint is
`Babai.VColBipBlk.two_mul_ncard_le_of_hint`.  What the clique branch of step 9 has to
supply is that the blocks of `D` all get one value of `h`, which is what the stable
coloring of step 3 gives, since it refines the initial coloring and the initial coloring
records `h` (`Babai.VColBipBlk.h_eq_of_initColor_eq`).

## Numbering map

| Paper | Lean |
|---|---|
| §9.5, *"`X₂` moves from clique to UPCC"*: the structure left on `V₂` | `Babai.VColBipBlk.HasHint` |
| the hint is an isomorphism invariant | `Babai.VColBipBlk.hasHint_congr` |
| §9.7, Case 3a2, the last step (Prop. 2.4.11) | `Babai.PartitionStructure.two_mul_ncard_le_of_clique` |
| §9.7, Case 3a2, read on an object with the hint | `Babai.VColBipBlk.two_mul_ncard_le_of_hint` |
-/

namespace Babai

/-! ### Constituents of a homogeneous coherent configuration -/

namespace PartitionStructure

variable {β : Type} [Fintype β] [DecidableEq β] (P : PartitionStructure β)

/-- Corollary 3.3.7 for a **homogeneous** coherent configuration: every constituent is a
biregular digraph on the whole vertex set.  In a homogeneous configuration every vertex
has the tail color and the head color of every color, so the out-degree and the in-degree
of Notation 3.3.6 are attained everywhere. -/
theorem extConstituent_isBiregular_of_isHomogeneous (h : P.IsCoherent)
    (hhom : P.IsHomogeneous) (k : Fin P.rank) : (P.extConstituent k).IsBiregular :=
  ⟨⟨P.outDegOf k, fun u => P.outDegC_eq_outDegOf h k (hhom _ _)⟩,
    ⟨P.inDegOf k, fun u => P.inDegC_eq_inDegOf h k (hhom _ _)⟩⟩

/-- A constituent is never empty: every color occurs (Def. 3.1.1). -/
theorem extConstituent_not_isEmpty (k : Fin P.rank) : ¬ (P.extConstituent k).IsEmpty := by
  obtain ⟨p, hp⟩ := P.rel_nonempty k
  intro hE
  have : p ∈ (∅ : Set (β × β)) := by rw [← hE]; exact hp
  exact this

/-- A homogeneous configuration has **exactly one diagonal color**: the color of `(x, x)`
is the same for all `x`, and every other color is off-diagonal. -/
theorem isOffDiagonalColor_of_ne_vcolor' (h : P.IsConfiguration) (hhom : P.IsHomogeneous)
    {k : Fin P.rank} {x : β} (hk : k ≠ P.vcolor x) : P.IsOffDiagonalColor k := by
  rcases P.diagonal_or_offDiagonal h k with hd | ho
  · -- a diagonal color is the color of some `(y, y)`, which is `vcolor y = vcolor x`
    exfalso
    obtain ⟨u, v, huv⟩ := P.color_surjective k
    have hmem : (u, v) ∈ P.rel k := huv
    have : (u, v) ∈ diag β := hd hmem
    have huv' : u = v := this
    subst huv'
    exact hk (huv.symm.trans (hhom u x))
  · exact ho

/-- §9.7, Case 3a2, the step with mathematical content.  **A clique of blocks is at most
half of them.**  *"`U` was a clique in `Y` and therefore `|U| ≤ |W|/2 ≤ n₂/2` by
Prop. 2.4.11."*  (Version 2.5, lines 4285-4294.)

Let `P` be a homogeneous coherent configuration of rank at least `3` on the set of blocks,
and let `D` be a set of at least two blocks all of whose *ordered pairs of distinct
members* carry one and the same color of `P`.  Then `2|D| ≤ n₂`.

The proof is the paper's.  A homogeneous configuration has one diagonal color, so of its
`≥ 3` colors at least two are off-diagonal.  `D` uses only the one color `c₀` off the
diagonal, so no edge of any other off-diagonal color `c₁` has both ends in `D`, that is,
`D` is independent in the constituent `c₁`.  That constituent is a non-empty biregular
digraph on the whole set of blocks
(`Babai.PartitionStructure.extConstituent_isBiregular_of_isHomogeneous`), so Prop. 2.4.11
applies. -/
theorem two_mul_ncard_le_of_clique (h : P.IsCoherent) (hhom : P.IsHomogeneous)
    (hrank : 3 ≤ P.rank) {D : Set β} (hD : 2 ≤ D.ncard)
    (hclique : ∀ A ∈ D, ∀ B ∈ D, ∀ A' ∈ D, ∀ B' ∈ D, A ≠ B → A' ≠ B' →
      P.color A B = P.color A' B') :
    2 * D.ncard ≤ Fintype.card β := by
  classical
  -- two distinct blocks of `D`, and the common color `c₀` of the ordered pairs
  obtain ⟨A, hA, B, hB, hAB⟩ : ∃ A ∈ D, ∃ B ∈ D, A ≠ B := by
    have hnt : D.Nontrivial := by
      have : D.Finite := Set.toFinite _
      haveI : Finite ↥D := this
      exact Set.one_lt_ncard_iff_nontrivial.1 (by omega)
    obtain ⟨A, hA, B, hB, hAB⟩ := hnt
    exact ⟨A, hA, B, hB, hAB⟩
  set c₀ : Fin P.rank := P.color A B with hc₀
  set d₀ : Fin P.rank := P.vcolor A with hd₀
  -- `c₀` is off the diagonal, so it is not the diagonal color `d₀`
  have hc₀d₀ : c₀ ≠ d₀ := by
    intro hcd
    have hdiag : P.IsOffDiagonalColor c₀ := by
      rcases P.diagonal_or_offDiagonal h.toIsConfiguration c₀ with hdg | ho
      · exact absurd (hdg (show (A, B) ∈ P.rel c₀ from rfl) : (A, B) ∈ diag β) hAB
      · exact ho
    have hAA : (A, A) ∈ P.rel c₀ := by rw [hcd]; rfl
    have : (A, A) ∈ P.rel c₀ ∩ diag β := ⟨hAA, rfl⟩
    rw [hdiag] at this
    exact this
  -- rank at least `3`: a third color `c₁`
  obtain ⟨c₁, hc₁0, hc₁d⟩ : ∃ c₁ : Fin P.rank, c₁ ≠ c₀ ∧ c₁ ≠ d₀ := by
    by_contra hcon
    push_neg at hcon
    have hsub : (Set.univ : Set (Fin P.rank)) ⊆ {c₀, d₀} := by
      intro c _
      rcases eq_or_ne c c₀ with rfl | hne
      · exact Or.inl rfl
      · exact Or.inr (hcon c hne)
    have h1 : (Set.univ : Set (Fin P.rank)).ncard ≤ ({c₀, d₀} : Set (Fin P.rank)).ncard :=
      Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] at h1
    have h2 : ({c₀, d₀} : Set (Fin P.rank)).ncard ≤ 2 := by
      simpa using Set.ncard_insert_le c₀ {d₀}
    omega
  -- `D` is independent in the constituent `c₁`
  have hind : (P.extConstituent c₁).IsIndependent D := by
    rw [Digraph.IsIndependent, Set.eq_empty_iff_forall_notMem]
    rintro ⟨A', B'⟩ ⟨hcol, hA', hB'⟩
    have hcol' : P.color A' B' = c₁ := hcol
    rcases eq_or_ne A' B' with rfl | hne
    · -- the diagonal carries the color `d₀`
      exact hc₁d (hcol'.symm.trans (hhom A' A))
    · -- an ordered pair of distinct blocks of `D` carries the color `c₀`
      exact hc₁0 (hcol'.symm.trans (hclique A' hA' B' hB' A hA B hB hne hAB))
  exact Digraph.ncard_independent_le (P.extConstituent_not_isEmpty c₁)
    (P.extConstituent_isBiregular_of_isHomogeneous h hhom c₁) hind

end PartitionStructure

/-! ### The hint on an object of the wider category -/

namespace VColBipBlk

variable {s t : Type} [Fintype s] [DecidableEq s] [Fintype t] [DecidableEq t]

/-- §9.5, §9.7.  **The object carries the hint.**  The coloring `h` of the ordered pairs
of blocks is, on the blocks, the coloring of a homogeneous coherent configuration of rank
at least `3` on the set of blocks: the UPCC `Y` of Case 3a2, or the equipartition of
Cases 3a1 and 3b.

As after the repair of the `Case` structures (see the entry on the `Case` structures in
the corrected paper), the configuration is asked to have the *color classes* of `h`, not its
color labels: naming the colors of a part by an ambient coloring is not satisfiable.

Rank at least `3` is not vacuous: `Babai.PartitionStructure` asks every color to occur
(Def. 3.1.1), so a structure of rank `≥ 3` needs at least two blocks. -/
def HasHint (X : VColBipBlk s ℕ) : Prop :=
  ∃ P : PartitionStructure ↥X.blocks,
    P.IsCoherent ∧ P.IsHomogeneous ∧ 3 ≤ P.rank ∧
      ∀ A B A' B' : ↥X.blocks,
        (P.color A B = P.color A' B' ↔ X.h A B = X.h A' B')

/-- The hint forces at least two blocks, so it is not vacuous at the empty family: a
partition structure of rank `≥ 3` has at least two colors, and on a set with at most one
element every pair carries the same color. -/
theorem two_le_numBlocks_of_hasHint {X : VColBipBlk s ℕ} (hX : X.HasHint) :
    2 ≤ X.numBlocks := by
  classical
  obtain ⟨P, -, -, hrank, -⟩ := hX
  by_contra hcon
  push_neg at hcon
  have hsubs : Subsingleton ↥X.blocks := by
    refine (Set.subsingleton_coe X.blocks).2 ?_
    have hle : X.blocks.ncard ≤ 1 := by
      have : X.blocks.ncard < 2 := hcon
      omega
    exact Set.ncard_le_one_iff_subsingleton.1 hle
  -- the colors `0` and `1` both occur, and on a subsingleton every pair has one color
  obtain ⟨x, y, hxy⟩ := P.color_surjective (⟨0, by omega⟩ : Fin P.rank)
  obtain ⟨x', y', hxy'⟩ := P.color_surjective (⟨1, by omega⟩ : Fin P.rank)
  rw [Subsingleton.elim x x', Subsingleton.elim y y', hxy'] at hxy
  exact absurd (congrArg Fin.val hxy) (by simp)

/-- §9.7, Case 3a2, at an object that carries the hint.  **A set of blocks on which the
hint is constant off the diagonal is at most half of the blocks.**

This is `Babai.PartitionStructure.two_mul_ncard_le_of_clique` read through the hint: the
configuration of the hint has the color classes of `h`, so "all ordered pairs of distinct
blocks of `D` get one value of `h`" is "all of them get one color of the configuration".
In the clique branch of step 9 the stable coloring gives exactly that hypothesis, because
it refines the initial coloring of step 3, which records `h`
(`Babai.VColBipBlk.h_eq_of_initColor_eq`). -/
theorem two_mul_ncard_le_of_hint {X : VColBipBlk s ℕ} (hX : X.HasHint)
    {D : Set ↥X.blocks} (hD : 2 ≤ D.ncard)
    (hclique : ∀ A ∈ D, ∀ B ∈ D, ∀ A' ∈ D, ∀ B' ∈ D, A ≠ B → A' ≠ B' →
      X.h A B = X.h A' B') :
    2 * D.ncard ≤ X.numBlocks := by
  classical
  obtain ⟨P, hco, hhom, hrank, hker⟩ := hX
  have hcard : Fintype.card ↥X.blocks = X.numBlocks := by
    rw [numBlocks, ← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
  rw [← hcard]
  refine P.two_mul_ncard_le_of_clique hco hhom hrank hD ?_
  intro A hA B hB A' hA' B' hB' hne hne'
  exact (hker A B A' B').2 (hclique A hA B hB A' hA' B' hB' hne hne')

/-! ### The hint is an isomorphism invariant -/

/-- An isomorphism of objects induces a bijection of the two sets of blocks. -/
noncomputable def blkEquivOfIsIsoTo {X : VColBipBlk s ℕ} {Y : VColBipBlk t ℕ} {φ : s ≃ t}
    (hφ : X.IsIsoTo Y φ) : ↥X.blocks ≃ ↥Y.blocks where
  toFun B := ⟨φ '' (B : Set s), (hφ.blocks _).2 B.2⟩
  invFun C := ⟨φ.symm '' (C : Set t), by
    have h := (hφ.blocks (φ.symm '' (C : Set t)))
    rw [Equiv.image_symm_image] at h
    exact h.1 C.2⟩
  left_inv B := Subtype.ext (Equiv.symm_image_image _ _)
  right_inv C := Subtype.ext (Equiv.image_symm_image _ _)

@[simp] theorem blkEquivOfIsIsoTo_val {X : VColBipBlk s ℕ} {Y : VColBipBlk t ℕ} {φ : s ≃ t}
    (hφ : X.IsIsoTo Y φ) (B : ↥X.blocks) :
    ((blkEquivOfIsIsoTo hφ B : ↥Y.blocks) : Set t) = φ '' (B : Set s) := rfl

/-- A partition structure carried along a bijection of vertex sets.

`Babai.PartitionStructure.congrEquiv` (`Workspace/DesignLemma/Reduction.lean`) is the same
construction, but that module stands *above* §9.4-§9.8 in the import order, so it cannot be
used here; this is a local copy, kept private. -/
private def transportStructure {β γ : Type} (P : PartitionStructure β) (e : β ≃ γ) :
    PartitionStructure γ where
  rank := P.rank
  color x y := P.color (e.symm x) (e.symm y)
  color_surjective i := by
    obtain ⟨x, y, hxy⟩ := P.color_surjective i
    exact ⟨e x, e y, by simpa using hxy⟩

@[simp] private theorem transportStructure_color {β γ : Type} (P : PartitionStructure β)
    (e : β ≃ γ) (x y : γ) :
    (transportStructure P e).color x y = P.color (e.symm x) (e.symm y) := rfl

private theorem transportStructure_isCoherent {β γ : Type} [Fintype β] [Fintype γ]
    {P : PartitionStructure β} (e : β ≃ γ) (h : P.IsCoherent) :
    (transportStructure P e).IsCoherent := by
  classical
  refine ⟨⟨fun x y z hxyz => e.symm.injective (h.diag _ _ _ hxyz),
    fun u v x y huv => h.converse _ _ _ _ huv⟩, ?_⟩
  obtain ⟨p, hp⟩ := h.intersection
  refine ⟨p, fun i j k x y hxy => ?_⟩
  have hset : {z : γ | (transportStructure P e).color x z = i
        ∧ (transportStructure P e).color z y = j}
      = e '' {z : β | P.color (e.symm x) z = i ∧ P.color z (e.symm y) = j} := by
    ext z
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨e.symm z, ⟨h1, h2⟩, by simp⟩
    · rintro ⟨w, ⟨h1, h2⟩, rfl⟩
      exact ⟨by simpa using h1, by simpa using h2⟩
  rw [hset, Set.ncard_image_of_injective _ e.injective]
  exact hp i j k _ _ hxy

/-- §9.5.  **The hint is preserved by an isomorphism.**  A morphism of the category carries
the blocks onto the blocks and the coloring `h` onto the coloring `h`
(`Babai.VColBipBlk.IsIsoTo.hint`), so the configuration of the hint transports along the
bijection of the two sets of blocks. -/
theorem hasHint_congr {X : VColBipBlk s ℕ} {Y : VColBipBlk t ℕ} {φ : s ≃ t}
    (hφ : X.IsIsoTo Y φ) (hX : X.HasHint) : Y.HasHint := by
  classical
  obtain ⟨P, hco, hhom, hrank, hker⟩ := hX
  set e : ↥X.blocks ≃ ↥Y.blocks := blkEquivOfIsIsoTo hφ with he
  -- the coloring of `Y` at a pair of blocks is the coloring of `X` at the preimage pair
  have hYh : ∀ C D : ↥Y.blocks, Y.h (C : Set t) (D : Set t)
      = X.h ((e.symm C : ↥X.blocks) : Set s) ((e.symm D : ↥X.blocks) : Set s) := by
    intro C D
    have hC : φ '' ((e.symm C : ↥X.blocks) : Set s) = (C : Set t) :=
      congrArg Subtype.val (e.apply_symm_apply C)
    have hD : φ '' ((e.symm D : ↥X.blocks) : Set s) = (D : Set t) :=
      congrArg Subtype.val (e.apply_symm_apply D)
    rw [← hC, ← hD]
    exact hφ.hint _ _
  refine ⟨transportStructure P e, transportStructure_isCoherent e hco,
    fun C D => hhom _ _, hrank, fun C D C' D' => ?_⟩
  show P.color (e.symm C) (e.symm D) = P.color (e.symm C') (e.symm D') ↔ _
  rw [hYh C D, hYh C' D']
  exact hker _ _ _ _

end VColBipBlk

end Babai
