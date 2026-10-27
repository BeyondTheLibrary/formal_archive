/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 9.6: the block system of the imprimitive case, defined from the edge coloring
alone.
-/
import Workspace.SplitOrJohnson.NatColor
import Workspace.Coherent.Constituents

/-!
# §9.6  The blocks `B₁, …, B_m`, as a function of the coloring

The proof of Lemma 9.6.1 opens with

> *"Let `B₁, …, B_m` be the connected components of a disconnected non-diagonal color in
> `X₂`, say `R₂`."*

An object of the category `Babai.BlkImprimitiveCases` is an `ℕ`-valued edge coloring `c`
together with the *proposition* `Babai.IsImprimitiveCase c V₁ V₂`.  A
`Babai.PartitionStructure` taken out of that proposition by choice is not natural in the
object, so the blocks have to be defined from `c` alone, exactly as the construction of
Lemma 9.3.1 is (see `Workspace/SplitOrJohnson/UpccToBip.lean`).  This file does that:

* `Babai.colorDigraph c k` — the digraph of one color of `c`;
* `Babai.IsDisconnectedColor c k` — *"`k` is a disconnected non-diagonal color"*;
* `Babai.blockColor c` — *"say `R₂`"*: the **smallest** such color, which is canonical
  because a morphism of `Babai.BlkImprimitiveCases` preserves the color labels;
* `Babai.blockOf c y` — the block `Bᵢ` containing `y`.

The two things one then needs about this definition are proved here:

* it transports along an isomorphism of colorings (`Babai.blockColor_map`,
  `Babai.blockOf_map`) — condition (ii) of Definition 6.0.1;
* under the hypotheses of the `Case` of §9.6 the blocks are a genuine, nontrivial system of
  imprimitivity (`Babai.exists_isDisconnectedColor`, `Babai.blockOf_equipartition`,
  `Babai.blockOf_nontrivial`, `Babai.exists_blockOf_ne`), which is Prop. 3.4.4
  (`Babai.PartitionStructure.homogeneous_disconnected_weakComponents`) read through
  `natColor`.

## Numbering map

| Paper | Lean |
|---|---|
| *"a disconnected non-diagonal color in `X₂`"* | `Babai.IsDisconnectedColor` |
| *"say `R₂`"* (the canonical choice) | `Babai.blockColor` |
| *"the connected components `B₁, …, B_m`"* | `Babai.blockOf`, `Babai.blocks` |
| Prop. 3.4.4 for these blocks | `Babai.blockOf_equipartition`, `Babai.blockOf_nontrivial` |
-/

namespace Babai

/-! ### Transport of connectivity along an isomorphism of digraphs -/

namespace Digraph

variable {T T' : Type*}

theorem adj_symmetrization {X : Digraph T} {u v : T} :
    X.symmetrization.Adj u v ↔ X.Adj u v ∨ X.Adj v u := Iff.rfl

/-- Accessibility is carried by an isomorphism of digraphs. -/
theorem accessible_map_of_equiv {X : Digraph T} {Y : Digraph T'} (f : T ≃ T')
    (hf : ∀ u v, Y.Adj (f u) (f v) ↔ X.Adj u v) (u v : T) :
    Y.Accessible (f u) (f v) ↔ X.Accessible u v := by
  rw [accessible_iff_reflTransGen, accessible_iff_reflTransGen]
  constructor
  · intro h
    have hlift : ∀ a b : T', Y.Adj a b → X.Adj (f.symm a) (f.symm b) := by
      intro a b hab
      have h2 : Y.Adj (f (f.symm a)) (f (f.symm b)) := by simpa using hab
      exact (hf (f.symm a) (f.symm b)).1 h2
    have := h.lift f.symm hlift
    simpa using this
  · intro h
    exact h.lift f fun a b hab => (hf a b).2 hab

/-- Weak accessibility is carried by an isomorphism of digraphs. -/
theorem symmetrization_accessible_map {X : Digraph T} {Y : Digraph T'} (f : T ≃ T')
    (hf : ∀ u v, Y.Adj (f u) (f v) ↔ X.Adj u v) (u v : T) :
    Y.symmetrization.Accessible (f u) (f v) ↔ X.symmetrization.Accessible u v :=
  accessible_map_of_equiv f (fun a b => by
    rw [adj_symmetrization, adj_symmetrization, hf a b, hf b a]) u v

/-- The weak components are carried by an isomorphism of digraphs. -/
theorem weakComponent_map {X : Digraph T} {Y : Digraph T'} (f : T ≃ T')
    (hf : ∀ u v, Y.Adj (f u) (f v) ↔ X.Adj u v) (u : T) :
    Y.weakComponent (f u) = f '' X.weakComponent u := by
  ext w
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨f.symm w, ⟨?_, ?_⟩, by simp⟩
    · refine (symmetrization_accessible_map f hf u (f.symm w)).1 ?_
      simpa using h1
    · refine (symmetrization_accessible_map f hf (f.symm w) u).1 ?_
      simpa using h2
  · rintro ⟨z, ⟨h1, h2⟩, rfl⟩
    exact ⟨(symmetrization_accessible_map f hf u z).2 h1,
      (symmetrization_accessible_map f hf z u).2 h2⟩

/-- Weak connectivity is carried by an isomorphism of digraphs. -/
theorem isWeaklyConnected_map {X : Digraph T} {Y : Digraph T'} (f : T ≃ T')
    (hf : ∀ u v, Y.Adj (f u) (f v) ↔ X.Adj u v) :
    Y.IsWeaklyConnected ↔ X.IsWeaklyConnected := by
  constructor
  · intro h u v
    exact (symmetrization_accessible_map f hf u v).1 (h (f u) (f v))
  · intro h u v
    have := (symmetrization_accessible_map f hf (f.symm u) (f.symm v)).2
      (h (f.symm u) (f.symm v))
    simpa using this

end Digraph

/-! ### One color of an edge coloring, as a digraph -/

variable {T T' : Type*}

/-- The digraph `(T, R_k)` of the color `k` of the edge coloring `c`.  For `c` the
`ℕ`-valued coloring of a partition structure this is the extended constituent
`Babai.PartitionStructure.extConstituent` of that color (`Babai.colorDigraph_natColor`). -/
def colorDigraph (c : T → T → ℕ) (k : ℕ) : Digraph T := ⟨{p | c p.1 p.2 = k}⟩

@[simp] theorem colorDigraph_adj {c : T → T → ℕ} {k : ℕ} {u v : T} :
    (colorDigraph c k).Adj u v ↔ c u v = k := Iff.rfl

theorem colorDigraph_natColor {Ω : Type*} (P : PartitionStructure Ω) {k : ℕ}
    (hk : k < P.rank) : colorDigraph P.natColor k = P.extConstituent ⟨k, hk⟩ := by
  refine congrArg Digraph.mk (Set.ext fun p => ?_)
  exact P.natColor_eq_iff_color_eq hk p.1 p.2

/-- §9.6, *"a disconnected non-diagonal color"*: the color `k` occurs, is not the color of
any loop, and its digraph is not weakly connected.

*"Occurs"* is part of the notion of a color of a partition structure (the relations `Rᵢ`
of Def. 3.1.1 are non-empty); without it the empty color would be "disconnected" and its
components would be the singletons, which is not a system of imprimitivity. -/
def IsDisconnectedColor (c : T → T → ℕ) (k : ℕ) : Prop :=
  (∀ x : T, c x x ≠ k) ∧ (∃ u v : T, c u v = k) ∧ ¬ (colorDigraph c k).IsWeaklyConnected

/-- An isomorphism of colorings carries the disconnected non-diagonal colors to the same
color labels: a morphism of `Babai.BlkImprimitiveCases` preserves the labels. -/
theorem isDisconnectedColor_map {c : T → T → ℕ} {c' : T' → T' → ℕ} (f : T ≃ T')
    (hf : ∀ u v, c' (f u) (f v) = c u v) (k : ℕ) :
    IsDisconnectedColor c' k ↔ IsDisconnectedColor c k := by
  have hadj : ∀ u v, (colorDigraph c' k).Adj (f u) (f v) ↔ (colorDigraph c k).Adj u v := by
    intro u v
    show c' (f u) (f v) = k ↔ c u v = k
    rw [hf u v]
  have hf' : ∀ u v : T', c' u v = c (f.symm u) (f.symm v) := by
    intro u v; simpa using hf (f.symm u) (f.symm v)
  refine and_congr ?_ (and_congr ?_ (not_congr (Digraph.isWeaklyConnected_map f hadj)))
  · constructor
    · intro h x; rw [← hf x x]; exact h (f x)
    · intro h x; rw [hf' x x]; exact h (f.symm x)
  · constructor
    · rintro ⟨u, v, huv⟩
      exact ⟨f.symm u, f.symm v, by rwa [hf' u v] at huv⟩
    · rintro ⟨u, v, huv⟩
      exact ⟨f u, f v, by rw [hf u v]; exact huv⟩

/-! ### The canonical choice of the color, and the blocks -/

open scoped Classical in
/-- §9.6, *"say `R₂`"*: the **smallest** disconnected non-diagonal color of `c`, and `0` if
there is none.

Taking the smallest label is what makes the choice canonical: a morphism of
`Babai.BlkImprimitiveCases` is a bijection preserving the color *labels*
(`Babai.ColoredEdges`), so it preserves the set of disconnected non-diagonal colors
(`Babai.isDisconnectedColor_map`) and hence its least element. -/
noncomputable def blockColor (c : T → T → ℕ) : ℕ :=
  if h : ∃ k, IsDisconnectedColor c k then Nat.find h else 0

theorem blockColor_spec {c : T → T → ℕ} (h : ∃ k, IsDisconnectedColor c k) :
    IsDisconnectedColor c (blockColor c) := by
  classical
  rw [blockColor, dif_pos h]
  exact Nat.find_spec h

/-- The canonical color is an isomorphism invariant. -/
theorem blockColor_map {c : T → T → ℕ} {c' : T' → T' → ℕ} (f : T ≃ T')
    (hf : ∀ u v, c' (f u) (f v) = c u v) : blockColor c' = blockColor c := by
  classical
  by_cases h : ∃ k, IsDisconnectedColor c k
  · have h' : ∃ k, IsDisconnectedColor c' k := by
      obtain ⟨k, hk⟩ := h
      exact ⟨k, (isDisconnectedColor_map f hf k).2 hk⟩
    rw [blockColor, blockColor, dif_pos h, dif_pos h']
    refine le_antisymm (Nat.find_le ?_) (Nat.find_le ?_)
    · exact (isDisconnectedColor_map f hf _).2 (Nat.find_spec h)
    · exact (isDisconnectedColor_map f hf _).1 (Nat.find_spec h')
  · have h' : ¬ ∃ k, IsDisconnectedColor c' k := by
      rintro ⟨k, hk⟩
      exact h ⟨k, (isDisconnectedColor_map f hf k).1 hk⟩
    rw [blockColor, blockColor, dif_neg h, dif_neg h']

/-- §9.6.  The block `Bᵢ` containing `y`: the weak component of `y` in the digraph of the
canonical color. -/
def blockOf (c : T → T → ℕ) (y : T) : Set T :=
  (colorDigraph c (blockColor c)).weakComponent y

/-- §9.6.  The system of blocks `{B₁, …, B_m}`. -/
def blocks (c : T → T → ℕ) : Set (Set T) :=
  (colorDigraph c (blockColor c)).weakComponents

theorem mem_blockOf_self (c : T → T → ℕ) (y : T) : y ∈ blockOf c y :=
  Digraph.mem_weakComponent_self _ y

theorem blockOf_mem_blocks (c : T → T → ℕ) (y : T) : blockOf c y ∈ blocks c := ⟨y, rfl⟩

/-- The blocks are carried by an isomorphism of colorings: condition (ii) of
Definition 6.0.1 for this construction. -/
theorem blockOf_map {c : T → T → ℕ} {c' : T' → T' → ℕ} (f : T ≃ T')
    (hf : ∀ u v, c' (f u) (f v) = c u v) (y : T) :
    blockOf c' (f y) = f '' blockOf c y := by
  have hadj : ∀ u v, (colorDigraph c' (blockColor c)).Adj (f u) (f v)
      ↔ (colorDigraph c (blockColor c)).Adj u v := by
    intro u v
    show c' (f u) (f v) = blockColor c ↔ c u v = blockColor c
    rw [hf u v]
  rw [blockOf, blockOf, blockColor_map f hf]
  exact Digraph.weakComponent_map f hadj y

/-! ### The blocks of the `Case` of §9.6 -/

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

omit [Fintype Ω] [DecidableEq Ω] in
/-- §9.6.  *"Let `B₁, …, B_m` be the connected components of a disconnected non-diagonal
color in `X₂`"*: such a color exists, because `X₂` is homogeneous and **not primitive**
(Def. 3.2.1: primitive means homogeneous with all off-diagonal constituents connected). -/
theorem exists_isDisconnectedColor {P : PartitionStructure Ω}
    (hhom : P.IsHomogeneous) (hprim : ¬ P.IsPrimitive) :
    ∃ k, IsDisconnectedColor P.natColor k := by
  rw [PartitionStructure.IsPrimitive, not_and_or] at hprim
  rcases hprim with h | h
  · exact absurd hhom h
  · obtain ⟨i, hi⟩ : ∃ i : Fin P.rank,
        ¬ (P.IsOffDiagonalColor i → (P.extConstituent i).IsWeaklyConnected) := by
      by_contra hcon
      exact h fun i => not_not.1 (fun hni => hcon ⟨i, hni⟩)
    have hoff : P.IsOffDiagonalColor i := by
      by_contra hc
      exact hi fun hcc => absurd hcc hc
    have hdisc : ¬ (P.extConstituent i).IsWeaklyConnected := fun hc => hi fun _ => hc
    refine ⟨(i : ℕ), fun x hx => ?_, ?_, ?_⟩
    · -- an off-diagonal color has no loop
      have hcol : P.color x x = i := (P.natColor_eq_iff_color_eq i.isLt x x).1 hx
      have : ((x, x) : Ω × Ω) ∈ P.rel i ∩ diag Ω := ⟨hcol, rfl⟩
      rw [hoff] at this
      exact this
    · -- the color occurs
      obtain ⟨⟨u, v⟩, huv⟩ := P.rel_nonempty i
      exact ⟨u, v, congrArg Fin.val huv⟩
    · rw [colorDigraph_natColor P i.isLt]
      exact hdisc

omit [Fintype Ω] [DecidableEq Ω] in
/-- The canonical color of §9.6 is a color of `P`, i.e. below its rank. -/
theorem blockColor_lt_rank {P : PartitionStructure Ω} (h : ∃ k, IsDisconnectedColor P.natColor k) :
    blockColor P.natColor < P.rank := by
  obtain ⟨-, ⟨u, v, huv⟩, -⟩ := blockColor_spec h
  exact huv ▸ P.natColor_lt_rank u v

omit [Fintype Ω] [DecidableEq Ω] in
/-- The canonical color of §9.6 is off-diagonal (Def. 3.1.9). -/
theorem blockColor_isOffDiagonalColor {P : PartitionStructure Ω}
    (h : ∃ k, IsDisconnectedColor P.natColor k) :
    P.IsOffDiagonalColor ⟨blockColor P.natColor, blockColor_lt_rank h⟩ := by
  obtain ⟨hdiag, -, -⟩ := blockColor_spec h
  refine Set.eq_empty_iff_forall_notMem.2 ?_
  rintro ⟨u, v⟩ ⟨hcol, huv⟩
  obtain rfl : u = v := huv
  exact hdiag u (congrArg Fin.val hcol)

/-- Proposition 3.4.4 for the blocks of §9.6: they form an equipartition of `V₂`. -/
theorem blockOf_equipartition {P : PartitionStructure Ω} (hcoh : P.IsCoherent)
    (hhom : P.IsHomogeneous) (h : ∃ k, IsDisconnectedColor P.natColor k) :
    IsEquipartition (blocks P.natColor) := by
  have he := P.homogeneous_weakComponents_isEquipartition hcoh hhom
    ⟨blockColor P.natColor, blockColor_lt_rank h⟩
  rwa [blocks, colorDigraph_natColor P (blockColor_lt_rank h)]

/-- Proposition 3.4.4 for the blocks of §9.6: every block has at least two elements, so
`m ≤ n₂/2` as the paper's *"reducing `n₂` to `m ≤ n₂/2`"* asserts. -/
theorem blockOf_nontrivial {P : PartitionStructure Ω} (hcoh : P.IsCoherent)
    (hhom : P.IsHomogeneous) (h : ∃ k, IsDisconnectedColor P.natColor k) (y : Ω) :
    (blockOf P.natColor y).Nontrivial := by
  have hnt := P.homogeneous_weakComponents_nontrivial hcoh hhom
    ⟨blockColor P.natColor, blockColor_lt_rank h⟩ (blockColor_isOffDiagonalColor h)
    (A := (P.extConstituent ⟨blockColor P.natColor, blockColor_lt_rank h⟩).weakComponent y)
    ⟨y, rfl⟩
  rwa [blockOf, colorDigraph_natColor P (blockColor_lt_rank h)]

omit [Fintype Ω] [DecidableEq Ω] in
/-- There are at least two blocks, so `|Bᵢ| ≤ n₂/2` as the paper's *"reducing `n₂` to
`n₂/m ≤ n₂/2`"* asserts. -/
theorem exists_blockOf_ne {P : PartitionStructure Ω} (h : ∃ k, IsDisconnectedColor P.natColor k) :
    ∃ A ∈ blocks P.natColor, ∃ B ∈ blocks P.natColor, A ≠ B := by
  obtain ⟨-, -, hdisc⟩ := blockColor_spec h
  exact (colorDigraph P.natColor (blockColor P.natColor)).exists_ne_weakComponents hdisc

/-! ### The two size bounds that Prop. 3.4.4 gives for §9.6 -/

/-- §9.6, step 2(i).  Two different blocks of an equipartition are disjoint and have the
same size, so a block holds at most half of the points.  This is the paper's *"reducing
`n₂` to `n₂/m ≤ n₂/2`"*. -/
theorem two_mul_ncard_le_of_isEquipartition {T : Type*} [Finite T] {P : Set (Set T)}
    (hP : IsEquipartition P) {A : Set T} (hA : A ∈ P) {B : Set T} (hB : B ∈ P)
    (hAB : A ≠ B) : 2 * A.ncard ≤ Nat.card T := by
  have hdisj := hP.pairwiseDisjoint A hA B hB hAB
  have hsize := hP.equal_size A hA B hB
  have hunion : (A ∪ B).ncard = A.ncard + B.ncard :=
    Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _)
  have hle : (A ∪ B).ncard ≤ Nat.card T := by
    rw [← Set.ncard_univ]
    exact Set.ncard_le_ncard (Set.subset_univ _) (Set.toFinite _)
  omega

/-- §9.6, step 2(ii).  A family of pairwise disjoint sets, each with at least two points,
has at most half as many members as there are points: pick two points in each member.
This is the paper's *"contracting each block, `n₂ ← m ≤ n₂/2`"*. -/
theorem two_mul_ncard_parts_le {T : Type*} [Finite T] {P : Set (Set T)}
    (hdisj : ∀ A ∈ P, ∀ B ∈ P, A ≠ B → Disjoint A B)
    (hnt : ∀ A ∈ P, A.Nontrivial) : 2 * P.ncard ≤ Nat.card T := by
  classical
  have hchoice : ∀ A : ↥P, ∃ p : T × T, p.1 ∈ (A : Set T) ∧ p.2 ∈ (A : Set T) ∧ p.1 ≠ p.2 := by
    intro A
    obtain ⟨x, hx, y, hy, hxy⟩ := hnt (A : Set T) A.2
    exact ⟨(x, y), hx, hy, hxy⟩
  choose f hf1 hf2 hf3 using hchoice
  set g : ↥P × Bool → T := fun q => if q.2 then (f q.1).2 else (f q.1).1 with hg
  have hmem : ∀ q : ↥P × Bool, g q ∈ (q.1 : Set T) := by
    intro q
    by_cases h : q.2 <;> simp only [hg, h, if_true, if_false]
    · exact hf2 q.1
    · exact hf1 q.1
  have hginj : Function.Injective g := by
    rintro ⟨A, i⟩ ⟨B, j⟩ h
    have hAB : A = B := by
      by_contra hne
      have hd := hdisj (A : Set T) A.2 (B : Set T) B.2 (fun hc => hne (Subtype.ext hc))
      exact (Set.disjoint_left.1 hd) (hmem (A, i)) (h ▸ hmem (B, j))
    subst hAB
    have hij : i = j := by
      cases i <;> cases j
      · rfl
      · exact absurd (by simpa [hg] using h) (hf3 A)
      · exact absurd (by simpa [hg] using h.symm) (hf3 A)
      · rfl
    subst hij; rfl
  have hcard := Nat.card_le_card_of_injective g hginj
  rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool,
    Nat.card_coe_set_eq] at hcard
  omega

/-! ### §9.6: a color that lives inside one vertex class

The blocks of §9.6 are the components of a color of `X₂`, a color whose edges all have
both ends in `V₂`.  Such a color is a color of the coloring of the whole vertex set, and
its components inside `V₂` are the same sets whether they are computed inside `V₂` or in
the whole vertex set.  This is what lets §9.6 work with one coloring only, and is what the
`ℕ`-color form of Theorem 3.4.9 below needs.  -/

section Restriction

variable {T : Type*}

/-- The restriction of an edge coloring to a set of vertices. -/
def restrictColor (c : T → T → ℕ) (W : Set T) : ↥W → ↥W → ℕ := fun u v => c u v

/-- *"a color of `X₂`"*: every edge of the color `k` has both ends in `W`.  In a coherent
configuration this holds for every color as soon as it holds for one edge
(Obs. 3.3.4). -/
def EdgesInside (c : T → T → ℕ) (W : Set T) (k : ℕ) : Prop :=
  ∀ u v, c u v = k → u ∈ W ∧ v ∈ W

/-- A weak walk of a color that lives inside `W` and starts in `W` stays in `W`. -/
theorem mem_of_reflTransGen_of_edgesInside {c : T → T → ℕ} {W : Set T} {k : ℕ}
    (hE : EdgesInside c W k) {u : T} (hu : u ∈ W) {z : T}
    (hz : Relation.ReflTransGen (colorDigraph c k).symmetrization.Adj u z) : z ∈ W := by
  induction hz with
  | refl => exact hu
  | @tail b z _ hbz ih =>
    rcases (Digraph.adj_symmetrization (X := colorDigraph c k)).1 hbz with hb | hb
    · exact (hE b z hb).2
    · exact (hE z b hb).1

/-- A weak walk of a color that lives inside `W` and starts in `W` is a weak walk of the
restricted coloring. -/
theorem reflTransGen_restrictColor {c : T → T → ℕ} {W : Set T} {k : ℕ}
    (hE : EdgesInside c W k) (u : ↥W) {z : T}
    (hz : Relation.ReflTransGen (colorDigraph c k).symmetrization.Adj (u : T) z) :
    ∀ hzW : z ∈ W,
      Relation.ReflTransGen (colorDigraph (restrictColor c W) k).symmetrization.Adj u
        ⟨z, hzW⟩ := by
  induction hz with
  | refl =>
    intro hzW
    have h : (⟨(u : T), hzW⟩ : ↥W) = u := Subtype.ext rfl
    rw [h]
  | @tail b z hub hbz ih =>
    intro hzW
    have hbW : b ∈ W := mem_of_reflTransGen_of_edgesInside hE u.2 hub
    refine (ih hbW).tail ?_
    show (restrictColor c W ⟨b, hbW⟩ ⟨z, hzW⟩ = k) ∨ (restrictColor c W ⟨z, hzW⟩ ⟨b, hbW⟩ = k)
    exact (Digraph.adj_symmetrization (X := colorDigraph c k)).1 hbz

/-- A weak walk of the restricted coloring is a weak walk of the coloring. -/
theorem reflTransGen_of_restrictColor {c : T → T → ℕ} {W : Set T} {k : ℕ} {u v : ↥W}
    (h : Relation.ReflTransGen (colorDigraph (restrictColor c W) k).symmetrization.Adj u v) :
    Relation.ReflTransGen (colorDigraph c k).symmetrization.Adj (u : T) (v : T) := by
  refine h.lift (fun w : ↥W => (w : T)) ?_
  intro a b hab
  exact (Digraph.adj_symmetrization (X := colorDigraph c k)).2
    ((Digraph.adj_symmetrization (X := colorDigraph (restrictColor c W) k)).1 hab)

/-- **The blocks do not depend on where they are computed.**  For a color whose edges all
have both ends in `W`, the weak component of a point of `W` in the whole vertex set is the
image of its weak component inside `W`. -/
theorem mem_weakComponent_restrictColor_iff {c : T → T → ℕ} {W : Set T} {k : ℕ}
    (hE : EdgesInside c W k) (u v : ↥W) :
    (v : T) ∈ (colorDigraph c k).weakComponent (u : T) ↔
      v ∈ (colorDigraph (restrictColor c W) k).weakComponent u := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · exact ((colorDigraph (restrictColor c W) k).symmetrization.accessible_iff_reflTransGen
        u v).2 (reflTransGen_restrictColor hE u
          (((colorDigraph c k).symmetrization.accessible_iff_reflTransGen _ _).1 h1) v.2)
    · exact ((colorDigraph (restrictColor c W) k).symmetrization.accessible_iff_reflTransGen
        v u).2 (reflTransGen_restrictColor hE v
          (((colorDigraph c k).symmetrization.accessible_iff_reflTransGen _ _).1 h2) u.2)
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · exact ((colorDigraph c k).symmetrization.accessible_iff_reflTransGen _ _).2
        (reflTransGen_of_restrictColor
          (((colorDigraph (restrictColor c W) k).symmetrization.accessible_iff_reflTransGen
            u v).1 h1))
    · exact ((colorDigraph c k).symmetrization.accessible_iff_reflTransGen _ _).2
        (reflTransGen_of_restrictColor
          (((colorDigraph (restrictColor c W) k).symmetrization.accessible_iff_reflTransGen
            v u).1 h2))

/-- A block of a color that lives inside `W` is contained in `W`. -/
theorem weakComponent_subset_of_edgesInside {c : T → T → ℕ} {W : Set T} {k : ℕ}
    (hE : EdgesInside c W k) {u : T} (hu : u ∈ W) :
    (colorDigraph c k).weakComponent u ⊆ W := by
  rintro z ⟨h1, -⟩
  exact mem_of_reflTransGen_of_edgesInside hE hu
    (((colorDigraph c k).symmetrization.accessible_iff_reflTransGen u z).1 h1)

/-- The weak component in `W` is the weak component in the whole vertex set. -/
theorem image_weakComponent_restrictColor {c : T → T → ℕ} {W : Set T} {k : ℕ}
    (hE : EdgesInside c W k) (u : ↥W) :
    Subtype.val '' ((colorDigraph (restrictColor c W) k).weakComponent u)
      = (colorDigraph c k).weakComponent (u : T) := by
  ext z
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact (mem_weakComponent_restrictColor_iff hE u v).2 hv
  · intro hz
    have hzW : z ∈ W := weakComponent_subset_of_edgesInside hE u.2 hz
    exact ⟨⟨z, hzW⟩, (mem_weakComponent_restrictColor_iff hE u ⟨z, hzW⟩).1 hz, rfl⟩

end Restriction


/-! ### (N8)  Theorem 3.4.9 (Contraction) at the `ℕ`-color level

Lemma 9.6.2 needs the contracted bipartite graph `Y = (V₁, [m]; R_h)` of Procedure
ImprimitiveCase, step 2(ii) to be semiregular, and takes this from Cor. 3.4.9.  An object
of `Babai.BlkImprimitiveCases` carries an `ℕ`-valued coloring and the *proposition* that
some coherent configuration has these color classes, so what §9.6 can use is the statement
below, which mentions only the coloring.  It is Theorem 3.4.9 read through
`Babai.PartitionStructure.natColor`, in the two halves in which the paper proves it:

* the `[m]` side is Lemma 3.4.6 (`ncard_outNbhd_component_eq`);
* the `Ω₂` side is Lemma 3.4.8 (`ncard_components_meeting_eq`).

Here `d₁` and `d₂` are the two vertex colors, `k₃` is the color of `X₂` whose components
are the blocks, and `h` is the color of the link that step 2(ii) contracts.  The two
conclusions are exactly the two degrees of `Babai.contractedBip` being constant, which is
`Babai.BipGraph.IsSemiregular` for that graph. -/

section Contraction

variable {V : Type} [Fintype V] [DecidableEq V]

/-- (N8)  Theorem 3.4.9 (Contraction), for the `ℕ`-valued coloring.  See the section
docstring.  The hypotheses name one edge of the color `k₃` inside the class `d₂` and one
edge of the color `h` from the class `d₁` to the class `d₂`; by vertex-color awareness
(Obs. 3.3.4) one edge determines the classes of all edges of that color. -/
theorem natColor_contraction_degrees {cc : V → V → ℕ}
    (hcoh : ∃ P : PartitionStructure V, P.IsCoherent ∧ P.natColor = cc)
    {d₁ d₂ k₃ h : ℕ} (hd : d₁ ≠ d₂)
    {u₀ v₀ : V} (hu₀ : cc u₀ u₀ = d₂) (hv₀ : cc v₀ v₀ = d₂) (huv₀ : cc u₀ v₀ = k₃)
    {x₀ y₀ : V} (hx₀ : cc x₀ x₀ = d₁) (hy₀ : cc y₀ y₀ = d₂) (hxy₀ : cc x₀ y₀ = h) :
    (∀ x x' : V, cc x x = d₁ → cc x' x' = d₁ →
        {B ∈ (colorDigraph cc k₃).weakComponents | ∃ z ∈ B, cc x z = h}.ncard
          = {B ∈ (colorDigraph cc k₃).weakComponents | ∃ z ∈ B, cc x' z = h}.ncard)
      ∧ (∀ y y' : V, cc y y = d₂ → cc y' y' = d₂ →
        {x : V | ∃ z ∈ (colorDigraph cc k₃).weakComponent y, cc x z = h}.ncard
          = {x : V | ∃ z ∈ (colorDigraph cc k₃).weakComponent y', cc x z = h}.ncard) := by
  classical
  obtain ⟨P, hP, rfl⟩ := hcoh
  -- the two colors of the configuration
  have hk₃lt : k₃ < P.rank := huv₀ ▸ P.natColor_lt_rank u₀ v₀
  have hhlt : h < P.rank := hxy₀ ▸ P.natColor_lt_rank x₀ y₀
  set c₃ : Fin P.rank := ⟨k₃, hk₃lt⟩ with hc₃
  set c₄ : Fin P.rank := P.conv ⟨h, hhlt⟩ with hc₄
  -- the colors of the two vertex classes, as `Fin`
  have hval : ∀ (w : V) (d : ℕ), P.natColor w w = d → (P.vcolor w : ℕ) = d := fun w d hw => hw
  have hcol_uv : P.color u₀ v₀ = c₃ := (P.natColor_eq_iff_color_eq hk₃lt u₀ v₀).1 huv₀
  have htail₃ : P.tailColor c₃ = P.vcolor u₀ := (P.vcolor_fst_eq hP hcol_uv).symm
  have hhead₃ : P.headColor c₃ = P.vcolor v₀ := (P.vcolor_snd_eq hP hcol_uv).symm
  have h3 : P.tailColor c₃ = P.headColor c₃ := by
    rw [htail₃, hhead₃]
    exact Fin.ext ((hval u₀ d₂ hu₀).trans (hval v₀ d₂ hv₀).symm)
  -- the link color, read backwards
  have hconv : ∀ x z : V, P.color z x = c₄ ↔ P.natColor x z = h := by
    intro x z
    rw [P.natColor_eq_iff_color_eq hhlt x z, hc₄,
      P.color_conv_iff hP.toIsConfiguration ⟨h, hhlt⟩ x z]
  have hcol_yx : P.color y₀ x₀ = c₄ := (hconv x₀ y₀).2 hxy₀
  have htail₄ : P.tailColor c₄ = P.vcolor y₀ := (P.vcolor_fst_eq hP hcol_yx).symm
  have hhead₄ : P.headColor c₄ = P.vcolor x₀ := (P.vcolor_snd_eq hP hcol_yx).symm
  have h4 : P.tailColor c₄ = P.tailColor c₃ := by
    rw [htail₄, htail₃]
    exact Fin.ext ((hval y₀ d₂ hy₀).trans (hval u₀ d₂ hu₀).symm)
  have htail₃val : (P.tailColor c₃ : ℕ) = d₂ := by rw [htail₃]; exact hval u₀ d₂ hu₀
  have hhead₄val : (P.headColor c₄ : ℕ) = d₁ := by rw [hhead₄]; exact hval x₀ d₁ hx₀
  have h34 : P.headColor c₄ ≠ P.tailColor c₃ := by
    intro hcon
    exact hd (hhead₄val.symm.trans (congrArg Fin.val hcon |>.trans htail₃val))
  -- the digraph of the color `k₃` is the constituent `c₃`
  have hdig : colorDigraph P.natColor k₃ = P.extConstituent c₃ := colorDigraph_natColor P hk₃lt
  have hcomp : ∀ w : V, P.compOf c₃ w = (colorDigraph P.natColor k₃).weakComponent w := by
    intro w; rw [PartitionStructure.compOf, hdig]
  refine ⟨fun x x' hx hx' => ?_, fun y y' hy hy' => ?_⟩
  · -- the `V₁` side: Lemma 3.4.8
    have hset : ∀ w : V, P.natColor w w = d₁ →
        {B ∈ (colorDigraph P.natColor k₃).weakComponents | ∃ z ∈ B, P.natColor w z = h}
          = P.componentsMeeting c₃ c₄ w := by
      intro w _
      ext B
      constructor
      · rintro ⟨⟨a, rfl⟩, z, hz, hwz⟩
        have hzx : P.color z w = c₄ := (hconv w z).2 hwz
        have hzcl : P.vcolor z = P.tailColor c₃ := by
          rw [P.vcolor_fst_eq hP hzx, h4]
        refine ⟨⟨z, hzcl, ?_⟩, ⟨z, hz, hzx⟩⟩
        rw [hcomp]
        exact ((colorDigraph P.natColor k₃).weakComponent_eq_of_mem hz).symm
      · rintro ⟨⟨a, -, rfl⟩, z, hz, hzw⟩
        rw [hcomp] at hz ⊢
        exact ⟨⟨a, rfl⟩, z, hz, (hconv w z).1 hzw⟩
    rw [hset x hx, hset x' hx']
    refine P.ncard_components_meeting_eq c₃ c₄ hP h3 h4 h34 ?_ ?_ <;>
      exact Fin.ext (by
        first
          | exact (hx.trans hhead₄val.symm)
          | exact (hx'.trans hhead₄val.symm))
  · -- the `V₂` side: Lemma 3.4.6
    have hset : ∀ w : V,
        {x : V | ∃ z ∈ (colorDigraph P.natColor k₃).weakComponent w, P.natColor x z = h}
          = P.outNbhdComp c₃ c₄ w := by
      intro w
      ext x
      constructor
      · rintro ⟨z, hz, hxz⟩
        exact ⟨z, by rw [hcomp]; exact hz, (hconv x z).2 hxz⟩
      · rintro ⟨z, hz, hzx⟩
        rw [hcomp] at hz
        exact ⟨z, hz, (hconv x z).1 hzx⟩
    rw [hset y, hset y']
    exact P.ncard_outNbhd_component_eq c₃ c₄ hP h3 h4 h34
      (Fin.ext (hy.trans htail₃val.symm)) (Fin.ext (hy'.trans htail₃val.symm))

end Contraction


/-! ### Proposition 3.4.4 for a coloring that names the colors differently

The blocks of §9.6 (`Babai.blockOf`) are defined from an `ℕ`-valued coloring, and
Proposition 3.4.4 is available for them when the coloring **is** the `natColor` of a
coherent homogeneous configuration (`Babai.blockOf_equipartition`).  Step 6 needs the same
statements for the coloring of `X₁`, which is the coloring of `X[W₁ ∪ V₂]` *read on the
points of `W₁`*: its color labels are the labels of the whole configuration `X`, as the
paper's *"the first disconnected off-diagonal color"* asks (the colors are the
`R₁, …, R_r` of `X`), and not the labels a configuration on `W₁` alone would give.

The two namings have the same color classes, and that is all Proposition 3.4.4 sees: the
digraph of a color, and hence the system of components, only depends on the partition of
the pairs into color classes.  `Babai.SameKernel` is that relation, and the three lemmas
below are `Babai.blockOf_equipartition`, `Babai.blockOf_nontrivial` and
`Babai.exists_blockOf_ne` for a coloring that has the same kernel as a `natColor`. -/

section SameKernel

variable {T : Type*} [Finite T]

/-- Two colorings with the same color classes. -/
def SameKernel (c c' : T → T → ℕ) : Prop :=
  ∀ a b a' b' : T, c a b = c a' b' ↔ c' a b = c' a' b'

theorem SameKernel.symm {c c' : T → T → ℕ} (h : SameKernel c c') : SameKernel c' c :=
  fun a b a' b' => (h a b a' b').symm

/-- Colorings with the same kernel have the same color digraphs, up to the naming of the
color: the digraph of the color of the pair `(u,v)` is the same for both. -/
theorem colorDigraph_eq_of_sameKernel {c c' : T → T → ℕ} (h : SameKernel c c') (u v : T) :
    colorDigraph c (c u v) = colorDigraph c' (c' u v) := by
  refine congrArg Digraph.mk (Set.ext fun p => ?_)
  exact h p.1 p.2 u v

/-- The canonical color of §9.6 is realized by a pair: this is the shape in which
`Babai.blockColor_spec` is used below. -/
theorem exists_eq_blockColor {c : T → T → ℕ} (h : ∃ k, IsDisconnectedColor c k) :
    ∃ u v : T, c u v = blockColor c := (blockColor_spec h).2.1

/-- Proposition 3.4.4 for a coloring with the same color classes as the `natColor` of a
coherent homogeneous configuration: the components of the canonical color form an
equipartition. -/
theorem isEquipartition_blocks_of_sameKernel {V : Type*} [Finite V] {c : V → V → ℕ}
    {P : PartitionStructure V} (hcoh : P.IsCoherent) (hhom : P.IsHomogeneous)
    (hker : SameKernel c P.natColor) (h : ∃ k, IsDisconnectedColor c k) :
    IsEquipartition (blocks c) := by
  classical
  letI : Fintype V := Fintype.ofFinite _
  obtain ⟨u, v, huv⟩ := exists_eq_blockColor h
  have hk : P.natColor u v < P.rank := P.natColor_lt_rank u v
  have hdig : colorDigraph c (blockColor c) = P.extConstituent ⟨P.natColor u v, hk⟩ := by
    rw [← huv, colorDigraph_eq_of_sameKernel hker u v, colorDigraph_natColor P hk]
  have he := P.homogeneous_weakComponents_isEquipartition hcoh hhom ⟨P.natColor u v, hk⟩
  rwa [blocks, hdig]

/-- Proposition 3.4.4 for a coloring with the same color classes as the `natColor` of a
coherent homogeneous configuration: every component of the canonical color has at least
two points. -/
theorem blockOf_nontrivial_of_sameKernel {V : Type*} [Finite V] {c : V → V → ℕ}
    {P : PartitionStructure V} (hcoh : P.IsCoherent) (hhom : P.IsHomogeneous)
    (hker : SameKernel c P.natColor) (h : ∃ k, IsDisconnectedColor c k) (y : V) :
    (blockOf c y).Nontrivial := by
  classical
  letI : Fintype V := Fintype.ofFinite _
  obtain ⟨hdiag, ⟨u, v, huv⟩, -⟩ := blockColor_spec h
  have hk : P.natColor u v < P.rank := P.natColor_lt_rank u v
  have hdig : colorDigraph c (blockColor c) = P.extConstituent ⟨P.natColor u v, hk⟩ := by
    rw [← huv, colorDigraph_eq_of_sameKernel hker u v, colorDigraph_natColor P hk]
  -- the color is off-diagonal, because no loop carries it
  have hoff : P.IsOffDiagonalColor ⟨P.natColor u v, hk⟩ := by
    refine Set.eq_empty_iff_forall_notMem.2 ?_
    rintro ⟨a, b⟩ ⟨hcol, hab⟩
    obtain rfl : a = b := hab
    have : P.natColor a a = P.natColor u v := congrArg Fin.val hcol
    exact hdiag a (huv ▸ (hker a a u v).2 this)
  have hnt := P.homogeneous_weakComponents_nontrivial hcoh hhom ⟨P.natColor u v, hk⟩ hoff
    (A := (P.extConstituent ⟨P.natColor u v, hk⟩).weakComponent y) ⟨y, rfl⟩
  rwa [blockOf, hdig]

end SameKernel

/-- A disconnected off-diagonal color is carried between colorings with the same color
classes. -/
theorem exists_isDisconnectedColor_congr {T : Type*} [Finite T] {c c' : T → T → ℕ}
    (h : SameKernel c c') :
    (∃ k, IsDisconnectedColor c k) ↔ (∃ k, IsDisconnectedColor c' k) := by
  have key : ∀ (d d' : T → T → ℕ), SameKernel d d' →
      (∃ k, IsDisconnectedColor d k) → (∃ k, IsDisconnectedColor d' k) := by
    rintro d d' hker ⟨k, hdiag, ⟨u, v, huv⟩, hdisc⟩
    refine ⟨d' u v, fun x hx => ?_, ⟨u, v, rfl⟩, ?_⟩
    · exact hdiag x (((hker x x u v).2 hx).trans huv)
    · rw [← colorDigraph_eq_of_sameKernel hker u v, huv]
      exact hdisc
  exact ⟨key c c' h, key c' c h.symm⟩

end Babai
