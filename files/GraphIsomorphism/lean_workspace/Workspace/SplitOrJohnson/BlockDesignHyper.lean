/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 9.7, Case 3: the neighborhood hypergraph `H` on the blocks, as a relational
structure over the ambient type `Set Ω`.
-/
import Workspace.SplitOrJohnson.BlockDesignCase
import Workspace.Prelim.HypergraphCompl
import Workspace.Prelim.TwinBound

/-!
# §9.7, Case 3  The neighborhood hypergraph on the blocks

Case 3 of §9.7 applies the Design Lemma (Theorem 8.1.2) *"to `H`, viewed as a `d₁`-ary
relational structure"*.  `H` lives on `V₂`, whose points are the **blocks**, and a block is
a set of points of `□X`; so the ambient type of that application is `Set Ω`
(`Workspace/Functors/Ambient.lean`).  This file builds `H` there:

* `Babai.BlkCaseObj.blkAmb`, the blocks read as points of `Set Ω`;
* `Babai.BlkCaseObj.edgeFinsetFam`, the neighborhoods `X(v)` read as hyperedges on those
  points, complemented when `d₁ > n₂/2` (`Babai.Hypergraph.compl`, see the entry
  *"§9.7 Case 3: the Design Lemma is applied at rank `d₁` without checking `d₁ ≤ n₂/2`"*
  of the corrected paper);
* `Babai.BlkCaseObj.nbhdHg`, the hypergraph itself, which is simple and `d'`-uniform;
* `Babai.BlkCaseObj.twinOrEq_iff_isHTwin`, the identification of `Babai.BlkCaseObj.IsHTwin`
  (Def. 2.3.9 for `H`, as §9.7 states Cases 1 and 2) with the twin relation of `Aut(H)`;
* `Babai.BlkCaseObj.defect_nbhdHg_ge`, Case 3 itself: *"the relative symmetry defect of `H`
  is `≥ 1/2`"*, read off the negation of Case 2;
* `Babai.BlkCaseObj.designObj` and `Babai.designFunc`, `H` as an admissible input of
  Theorem 8.1.2 and as a functor of the input of §9.7 on the fiber `{d' = N}`.

## Numbering map

| Paper | Lean |
|---|---|
| `H = (V₂, E)` on the blocks | `Babai.BlkCaseObj.nbhdHg` |
| *"`H` … is uniform of rank `d₁`"* | `Babai.BlkCaseObj.nbhdHg_isUniform` |
| *"`H` has no multiple edges"* | `Babai.BlkCaseObj.nbhdHg_isSimple` |
| Case 3, *"the relative symmetry defect of `H` is `≥ 1/2`"* | `Babai.BlkCaseObj.defect_nbhdHg_ge` |
| Case 3a, *"Apply the Design lemma to `H`, viewed as a `d₁`-ary relational structure"* | `Babai.designFunc` |
-/

namespace Babai

/-! ### A simple hypergraph with a prescribed edge set -/

namespace Hypergraph

variable {V : Type*}

/-- The simple hypergraph whose hyperedges are the members of `E`, each once.  Only
`Babai.Hypergraph.edgeSet_ofFinsetSet` and `Babai.Hypergraph.ofFinsetSet_isSimple` are used
below, so the arbitrary enumeration of `E` is harmless: the relational structure
`Babai.Hypergraph.toRelStructureSimple` depends on the edge **set** alone. -/
noncomputable def ofFinsetSet (E : Finset (Finset V)) : Hypergraph V where
  numEdges := E.card
  edge i := ((E.equivFin.symm i : {A // A ∈ E}) : Finset V)

@[simp] theorem edgeSet_ofFinsetSet (E : Finset (Finset V)) :
    (ofFinsetSet E).edgeSet = (↑E : Set (Finset V)) := by
  ext A
  constructor
  · rintro ⟨i, rfl⟩; exact (E.equivFin.symm i).2
  · intro hA
    exact ⟨E.equivFin ⟨A, hA⟩, by simp [ofFinsetSet]⟩

theorem ofFinsetSet_isSimple (E : Finset (Finset V)) : (ofFinsetSet E).IsSimple := by
  intro i j hij
  exact E.equivFin.symm.injective (Subtype.ext hij)

theorem ofFinsetSet_isUniform {E : Finset (Finset V)} {d : ℕ}
    (h : ∀ A ∈ E, A.card = d) : (ofFinsetSet E).IsUniform d := by
  intro i
  exact h _ (E.equivFin.symm i).2

/-- The membership test of `Aut(H)` for a **simple** hypergraph: a permutation is an
automorphism exactly if it preserves the edge set. -/
theorem mem_aut_iff_edgeSet [DecidableEq V] [Fintype V] {H : Hypergraph V} (hs : H.IsSimple)
    (σ : Equiv.Perm V) :
    σ ∈ H.Aut ↔ ∀ A : Finset V, (A.image σ ∈ H.edgeSet ↔ A ∈ H.edgeSet) := by
  constructor
  · intro hσ A
    have h := hσ A
    constructor
    · intro hmem
      have h1 : H.mult (A.image σ) = 1 := (mult_eq_one_iff hs _).2 hmem
      exact (mult_eq_one_iff hs _).1 (by rw [← h, h1])
    · intro hmem
      have h1 : H.mult A = 1 := (mult_eq_one_iff hs _).2 hmem
      exact (mult_eq_one_iff hs _).1 (by rw [h, h1])
  · intro hσ A
    by_cases hA : A ∈ H.edgeSet
    · rw [(mult_eq_one_iff hs _).2 hA, (mult_eq_one_iff hs _).2 ((hσ A).2 hA)]
    · have h1 : H.mult A = 0 := by
        have := mult_le_one hs A
        rcases Nat.lt_or_ge (H.mult A) 1 with h | h
        · omega
        · exact absurd ((mult_eq_one_iff hs A).1 (by omega)) hA
      have h2 : H.mult (A.image σ) = 0 := by
        have := mult_le_one hs (A.image σ)
        rcases Nat.lt_or_ge (H.mult (A.image σ)) 1 with h | h
        · omega
        · exact absurd ((hσ A).1 ((mult_eq_one_iff hs _).1 (by omega))) hA
      rw [h1, h2]

/-- For a simple hypergraph, a permutation that maps hyperedges to hyperedges **and is an
involution** is an automorphism: the two directions of
`Babai.Hypergraph.mem_aut_iff_edgeSet` are the same statement applied to `σ` and to
`σ⁻¹ = σ`. -/
theorem mem_aut_of_involutive_image [DecidableEq V] [Fintype V] {H : Hypergraph V}
    (hs : H.IsSimple)
    {σ : Equiv.Perm V} (hinv : ∀ x, σ (σ x) = x)
    (h : ∀ A ∈ H.edgeSet, A.image σ ∈ H.edgeSet) : σ ∈ H.Aut := by
  refine (mem_aut_iff_edgeSet hs σ).2 fun A => ⟨fun hmem => ?_, fun hmem => h A hmem⟩
  have hcomp : ((σ : V → V) ∘ (σ : V → V)) = id := funext hinv
  have himg : (A.image σ).image σ = A := by
    rw [Finset.image_image, hcomp, Finset.image_id]
  have := h _ hmem
  rwa [himg] at this

/-- The edge set of the complement: complementing each hyperedge. -/
theorem edgeSet_compl [DecidableEq V] [Fintype V] (H : Hypergraph V) :
    (compl H).edgeSet = (fun A : Finset V => Finset.univ \ A) '' H.edgeSet := by
  ext A
  constructor
  · rintro ⟨i, rfl⟩; exact ⟨H.edge i, ⟨i, rfl⟩, rfl⟩
  · rintro ⟨B, ⟨i, rfl⟩, rfl⟩; exact ⟨i, rfl⟩

/-- Complementing a set of vertices commutes with a bijection of the vertex sets. -/
theorem image_sdiff_univ' {W : Type*} [DecidableEq V] [Fintype V] [DecidableEq W]
    [Fintype W] (e : V ≃ W) (A : Finset V) :
    (Finset.univ \ A).image e = Finset.univ \ A.image e := by
  ext x
  simp only [Finset.mem_image, Finset.mem_sdiff, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rintro ⟨z, hz, hzy⟩
    exact hy (by rwa [← e.injective hzy])
  · intro hx
    exact ⟨e.symm x, fun h => hx ⟨e.symm x, h, by simp⟩, by simp⟩

/-- §2.5.1.  Two simple uniform hypergraphs whose edge sets correspond under a bijection
`e` of the vertex sets have relational structures that correspond under `e`.  This is what
carries the Design Lemma's input along a morphism of §9.7. -/
theorem map_toRelStructureSimple {W : Type*} [DecidableEq V] [Fintype V] [DecidableEq W]
    [Fintype W] (H : Hypergraph V) (K : Hypergraph W) (d : ℕ) (e : V ≃ W)
    (h : ∀ F : Finset V, F.image e ∈ K.edgeSet ↔ F ∈ H.edgeSet) :
    (H.toRelStructureSimple d).map (e : V → W) = K.toRelStructureSimple d := by
  refine (RelStructure.map_eq_iff (H.toRelStructureSimple d) e
    (K.toRelStructureSimple d).rel).2 fun i x => ?_
  have himg : Finset.univ.image (tupleMap (e : V → W) x)
      = (Finset.univ.image x).image (e : V → W) := by
    rw [Finset.image_image]; rfl
  have hinj : Function.Injective (tupleMap (e : V → W) x) ↔ Function.Injective x :=
    ⟨fun hf a b hab => hf (by simp [tupleMap, hab]), fun hf a b hab => hf (e.injective hab)⟩
  show (Function.Injective (tupleMap (e : V → W) x) ∧
      Finset.univ.image (tupleMap (e : V → W) x) ∈ K.edgeSet) ↔
    (Function.Injective x ∧ Finset.univ.image x ∈ H.edgeSet)
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨hinj.1 h1, (h _).1 (himg ▸ h2)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨hinj.2 h1, himg ▸ (h _).2 h2⟩

end Hypergraph

/-! ### The blocks as points of the ambient type `Set Ω` -/

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

namespace BlkCaseObj

variable {s : Set Ω} {Case : (Set ↥s → Set ↥s → ℕ) → Set (Set ↥s) → Set (Set ↥s) → Prop}

/-- §9.7.  The blocks of an input, read as points of the ambient type `Set Ω`.  This is the
vertex set `V₂` of the hypergraph `H` that Case 3 hands to the Design Lemma. -/
def blkAmb (X : BlkCaseObj s Case) : Set (Set Ω) :=
  (fun B : Set ↥s => Subtype.val '' B) '' X.blocks

noncomputable instance instFintypeBlkAmb (X : BlkCaseObj s Case) : Fintype ↥X.blkAmb :=
  Fintype.ofFinite _

noncomputable instance instDecidableEqBlkAmb (X : BlkCaseObj s Case) :
    DecidableEq ↥X.blkAmb := Classical.decEq _

/-- The block at a point of `Babai.BlkCaseObj.blkAmb`. -/
def blkOf (X : BlkCaseObj s Case) (b : ↥X.blkAmb) : Set ↥s := Subtype.val ⁻¹' (b : Set Ω)

theorem blkOf_mem (X : BlkCaseObj s Case) (b : ↥X.blkAmb) : X.blkOf b ∈ X.blocks := by
  obtain ⟨B, hB, hBb⟩ := b.2
  have : X.blkOf b = B := by
    show Subtype.val ⁻¹' (b : Set Ω) = B
    rw [← hBb, Set.preimage_image_eq _ Subtype.val_injective]
  exact this ▸ hB

theorem val_image_blkOf (X : BlkCaseObj s Case) (b : ↥X.blkAmb) :
    Subtype.val '' (X.blkOf b) = (b : Set Ω) := by
  obtain ⟨B, hB, hBb⟩ := b.2
  have hb : X.blkOf b = B := by
    show Subtype.val ⁻¹' (b : Set Ω) = B
    rw [← hBb, Set.preimage_image_eq _ Subtype.val_injective]
  rw [hb]; exact hBb

/-- The point of `Babai.BlkCaseObj.blkAmb` at a block. -/
def blkPt (X : BlkCaseObj s Case) {B : Set ↥s} (hB : B ∈ X.blocks) : ↥X.blkAmb :=
  ⟨Subtype.val '' B, B, hB, rfl⟩

@[simp] theorem blkOf_blkPt (X : BlkCaseObj s Case) {B : Set ↥s} (hB : B ∈ X.blocks) :
    X.blkOf (X.blkPt hB) = B := Set.preimage_image_eq _ Subtype.val_injective

@[simp] theorem blkPt_blkOf (X : BlkCaseObj s Case) (b : ↥X.blkAmb) :
    X.blkPt (X.blkOf_mem b) = b := Subtype.ext (X.val_image_blkOf b)

theorem blkOf_injective (X : BlkCaseObj s Case) : Function.Injective X.blkOf := by
  intro a b hab
  rw [← X.blkPt_blkOf a, ← X.blkPt_blkOf b]
  simp only [blkPt, Subtype.mk.injEq]
  rw [hab]

/-- `|V₂|` counted on the ambient type is `n₂`. -/
theorem card_blkAmb (X : BlkCaseObj s Case) : Fintype.card ↥X.blkAmb = X.n₂ := by
  classical
  rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, n₂, blkAmb,
    Set.ncard_image_of_injective _ (Set.image_injective.2 Subtype.val_injective)]

/-! ### The hyperedges -/

open scoped Classical in
/-- A family of blocks, read as a set of points of `Babai.BlkCaseObj.blkAmb`. -/
noncomputable def toBlkFinset (X : BlkCaseObj s Case) (S : Set (Set ↥s)) :
    Finset ↥X.blkAmb :=
  Finset.univ.filter fun b => X.blkOf b ∈ S

theorem mem_toBlkFinset (X : BlkCaseObj s Case) (S : Set (Set ↥s)) (b : ↥X.blkAmb) :
    b ∈ X.toBlkFinset S ↔ X.blkOf b ∈ S := by
  classical
  simp [toBlkFinset]

/-- Reading a family of blocks on `Babai.BlkCaseObj.blkAmb` loses nothing. -/
theorem toBlkFinset_injOn (X : BlkCaseObj s Case) {S T : Set (Set ↥s)}
    (hS : S ⊆ X.blocks) (hT : T ⊆ X.blocks) (h : X.toBlkFinset S = X.toBlkFinset T) :
    S = T := by
  ext B
  constructor
  · intro hB
    have hb := (X.mem_toBlkFinset S (X.blkPt (hS hB))).2 (by rw [X.blkOf_blkPt]; exact hB)
    rw [h, X.mem_toBlkFinset, X.blkOf_blkPt] at hb
    exact hb
  · intro hB
    have hb := (X.mem_toBlkFinset T (X.blkPt (hT hB))).2 (by rw [X.blkOf_blkPt]; exact hB)
    rw [← h, X.mem_toBlkFinset, X.blkOf_blkPt] at hb
    exact hb

/-- The size of a family of blocks is its size read on `Babai.BlkCaseObj.blkAmb`. -/
theorem card_toBlkFinset (X : BlkCaseObj s Case) {S : Set (Set ↥s)} (hS : S ⊆ X.blocks) :
    (X.toBlkFinset S).card = S.ncard := by
  classical
  have himg : Subtype.val '' ((X.toBlkFinset S : Finset ↥X.blkAmb) : Set ↥X.blkAmb)
      = (fun B : Set ↥s => Subtype.val '' B) '' S := by
    ext a
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact ⟨X.blkOf b, (X.mem_toBlkFinset S b).1 hb, X.val_image_blkOf b⟩
    · rintro ⟨B, hB, rfl⟩
      exact ⟨X.blkPt (hS hB), (X.mem_toBlkFinset S _).2 (by rw [X.blkOf_blkPt]; exact hB),
        rfl⟩
  have h1 : ((X.toBlkFinset S : Finset ↥X.blkAmb) : Set ↥X.blkAmb).ncard
      = ((fun B : Set ↥s => Subtype.val '' B) '' S).ncard := by
    rw [← himg, Set.ncard_image_of_injective _ Subtype.val_injective]
  rw [Set.ncard_coe_finset] at h1
  rw [h1, Set.ncard_image_of_injective _ (Set.image_injective.2 Subtype.val_injective)]

open scoped Classical in
/-- §9.7.  The hyperedges of `H`: the neighborhoods `X(v)`, `v ∈ V₁`, read on
`Babai.BlkCaseObj.blkAmb`.  *"`H` has no multiple edges"*, so this is a set of hyperedges
and not a multiset. -/
noncomputable def edgeFinsetFam (X : BlkCaseObj s Case) : Finset (Finset ↥X.blkAmb) :=
  Finset.univ.filter fun F => ∃ S ∈ X.edgeFam, F = X.toBlkFinset S

theorem mem_edgeFinsetFam (X : BlkCaseObj s Case) (F : Finset ↥X.blkAmb) :
    F ∈ X.edgeFinsetFam ↔ ∃ S ∈ X.edgeFam, F = X.toBlkFinset S := by
  classical
  simp [edgeFinsetFam]

theorem edgeFam_subset_blocks (X : BlkCaseObj s Case) {S : Set (Set ↥s)}
    (hS : S ∈ X.edgeFam) : S ⊆ X.blocks := by
  obtain ⟨x, -, rfl⟩ := hS
  exact X.nbhd_subset_blocks x

/-- A family of blocks is a hyperedge of `H` exactly if it is one read on
`Babai.BlkCaseObj.blkAmb`. -/
theorem toBlkFinset_mem_edgeFinsetFam (X : BlkCaseObj s Case) {S : Set (Set ↥s)}
    (hS : S ⊆ X.blocks) : X.toBlkFinset S ∈ X.edgeFinsetFam ↔ S ∈ X.edgeFam := by
  rw [X.mem_edgeFinsetFam]
  constructor
  · rintro ⟨T, hT, hTS⟩
    have : T = S := X.toBlkFinset_injOn (X.edgeFam_subset_blocks hT) hS hTS.symm
    exact this ▸ hT
  · intro hS'; exact ⟨S, hS', rfl⟩

/-! ### Swapping two blocks

Definition 2.3.9 for `H` (`Babai.BlkCaseObj.IsHTwin`) is stated with `Babai.swapIn`, the
action of a transposition of two blocks on a family of blocks.  Read on
`Babai.BlkCaseObj.blkAmb` that action is the image under the transposition of the two
points. -/

theorem blkOf_eq_iff (X : BlkCaseObj s Case) {B : Set ↥s} (hB : B ∈ X.blocks)
    (b : ↥X.blkAmb) : X.blkOf b = B ↔ b = X.blkPt hB := by
  constructor
  · intro h; exact X.blkOf_injective (by rw [h, X.blkOf_blkPt])
  · rintro rfl; exact X.blkOf_blkPt hB

theorem blkOf_swap (X : BlkCaseObj s Case) {B B' : Set ↥s} (hB : B ∈ X.blocks)
    (hB' : B' ∈ X.blocks) (S : Set (Set ↥s)) (b : ↥X.blkAmb) :
    X.blkOf (Equiv.swap (X.blkPt hB) (X.blkPt hB') b) ∈ S ↔ X.blkOf b ∈ swapIn B B' S := by
  set p := X.blkPt hB with hp
  set p' := X.blkPt hB' with hp'
  by_cases h1 : b = p
  · subst h1
    rw [Equiv.swap_apply_left, X.blkOf_blkPt, X.blkOf_blkPt]
    simp only [swapIn, Set.mem_setOf_eq]
    constructor
    · intro h; exact Or.inl ⟨trivial, h⟩
    · rintro (⟨-, h⟩ | ⟨heq, h⟩ | ⟨hne, -, -⟩)
      · exact h
      · exact heq ▸ h
      · exact absurd rfl hne
  · by_cases h2 : b = p'
    · subst h2
      rw [Equiv.swap_apply_right, X.blkOf_blkPt, X.blkOf_blkPt]
      simp only [swapIn, Set.mem_setOf_eq]
      constructor
      · intro h
        by_cases heq : B' = B
        · exact Or.inl ⟨heq, heq ▸ h⟩
        · exact Or.inr (Or.inl ⟨trivial, h⟩)
      · rintro (⟨heq, h⟩ | ⟨-, h⟩ | ⟨-, hne, h⟩)
        · exact heq ▸ h
        · exact h
        · exact absurd rfl hne
    · rw [Equiv.swap_apply_of_ne_of_ne h1 h2]
      simp only [swapIn, Set.mem_setOf_eq]
      have hnB : X.blkOf b ≠ B := fun h => h1 ((X.blkOf_eq_iff hB b).1 h)
      have hnB' : X.blkOf b ≠ B' := fun h => h2 ((X.blkOf_eq_iff hB' b).1 h)
      constructor
      · intro h; exact Or.inr (Or.inr ⟨hnB, hnB', h⟩)
      · rintro (⟨h, -⟩ | ⟨h, -⟩ | ⟨-, -, h⟩)
        · exact absurd h hnB
        · exact absurd h hnB'
        · exact h

/-- The transposition of two blocks, read on `Babai.BlkCaseObj.blkAmb`. -/
theorem toBlkFinset_swapIn (X : BlkCaseObj s Case) {B B' : Set ↥s} (hB : B ∈ X.blocks)
    (hB' : B' ∈ X.blocks) (S : Set (Set ↥s)) :
    X.toBlkFinset (swapIn B B' S)
      = (X.toBlkFinset S).image (Equiv.swap (X.blkPt hB) (X.blkPt hB')) := by
  classical
  ext b
  rw [X.mem_toBlkFinset]
  constructor
  · intro h
    refine Finset.mem_image.2 ⟨Equiv.swap (X.blkPt hB) (X.blkPt hB') b, ?_, by simp⟩
    rw [X.mem_toBlkFinset]
    exact (X.blkOf_swap hB hB' S b).2 h
  · intro h
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 h
    rw [X.mem_toBlkFinset] at ha
    refine (X.blkOf_swap hB hB' S _).1 ?_
    rwa [Equiv.swap_apply_self]

theorem swapIn_subset_blocks (X : BlkCaseObj s Case) {B B' : Set ↥s} (hB : B ∈ X.blocks)
    (hB' : B' ∈ X.blocks) {S : Set (Set ↥s)} (hS : S ⊆ X.blocks) :
    swapIn B B' S ⊆ X.blocks := by
  rintro A (⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨-, -, hA⟩)
  · exact hB
  · exact hB'
  · exact hS hA

/-- Def. 2.3.9 for `H`, read on `Babai.BlkCaseObj.blkAmb`: two blocks are `H`-twins exactly
if their transposition maps hyperedges to hyperedges. -/
theorem isHTwin_iff_image (X : BlkCaseObj s Case) {B B' : Set ↥s} (hB : B ∈ X.blocks)
    (hB' : B' ∈ X.blocks) :
    X.IsHTwin B B' ↔ ∀ F ∈ X.edgeFinsetFam,
      F.image (Equiv.swap (X.blkPt hB) (X.blkPt hB')) ∈ X.edgeFinsetFam := by
  constructor
  · intro h F hF
    obtain ⟨S, hS, rfl⟩ := (X.mem_edgeFinsetFam F).1 hF
    rw [← X.toBlkFinset_swapIn hB hB' S]
    exact (X.mem_edgeFinsetFam _).2 ⟨swapIn B B' S, h S hS, rfl⟩
  · intro h S hS
    have h1 : X.toBlkFinset S ∈ X.edgeFinsetFam := (X.mem_edgeFinsetFam _).2 ⟨S, hS, rfl⟩
    have h2 := h _ h1
    rw [← X.toBlkFinset_swapIn hB hB' S] at h2
    exact (X.toBlkFinset_mem_edgeFinsetFam
      (X.swapIn_subset_blocks hB hB' (X.edgeFam_subset_blocks hS))).1 h2

/-- A block is its own `H`-twin: the transposition of a block with itself is the
identity. -/
theorem isHTwin_refl (X : BlkCaseObj s Case) (B : Set ↥s) : X.IsHTwin B B := by
  intro S hS
  have : swapIn B B S = S := by
    ext A
    simp only [swapIn, Set.mem_setOf_eq, ne_eq]
    constructor
    · rintro (⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨-, -, h⟩) <;> exact h
    · intro h
      by_cases hA : A = B
      · exact Or.inl ⟨hA, hA ▸ h⟩
      · exact Or.inr (Or.inr ⟨hA, hA, h⟩)
  rwa [this]

/-! ### The hypergraph `H`, and its complement when `d₁ > n₂/2` -/

theorem card_mem_edgeFinsetFam (X : BlkDesignObj s) {F : Finset ↥X.blkAmb}
    (hF : F ∈ X.edgeFinsetFam) : F.card = X.d₁ := by
  obtain ⟨S, ⟨x, hx, rfl⟩, rfl⟩ := (X.mem_edgeFinsetFam F).1 hF
  rw [X.card_toBlkFinset (X.nbhd_subset_blocks x), X.nbhd_ncard_eq_d₁ hx]

/-- §9.7.  *"Let `H = (V₂, E)` be the hypergraph of neighborhoods of vertices in `V₁`"*,
on the vertex set `Babai.BlkCaseObj.blkAmb`, **complemented when `d₁ > n₂/2`**.

Theorem 8.1.2 asks for an arity at most `n₂/2`, which §9.7 does not check; the bipartite
complement has the same automorphism group, hence the same twins and the same symmetry
defect, and its rank is `n₂ − d₁`.  So `H` is taken here at the rank
`d' = min(d₁, n₂ − d₁)` (`Babai.BlkCaseObj.d'`).  See the entry *"§9.7 Case 3: the Design
Lemma is applied at rank `d₁` without checking `d₁ ≤ n₂/2`"* of the corrected paper. -/
noncomputable def nbhdHg (X : BlkDesignObj s) : Hypergraph ↥X.blkAmb :=
  if 2 * X.d₁ ≤ X.n₂ then Hypergraph.ofFinsetSet X.edgeFinsetFam
  else (Hypergraph.ofFinsetSet X.edgeFinsetFam).compl

/-- §9.7.  *"This hypergraph has no multiple edges because there are no twins in `V₁`"*:
the hyperedges are recorded as a set, and the complement of a simple hypergraph is
simple. -/
theorem nbhdHg_isSimple (X : BlkDesignObj s) : X.nbhdHg.IsSimple := by
  rw [nbhdHg]
  split_ifs
  · exact Hypergraph.ofFinsetSet_isSimple _
  · exact Hypergraph.compl_isSimple (Hypergraph.ofFinsetSet_isSimple _)

/-- §9.7.  *"`H` … is uniform of rank `d₁`"*, at the rank `d'` at which the Design Lemma
is applied. -/
theorem nbhdHg_isUniform (X : BlkDesignObj s) : X.nbhdHg.IsUniform X.d' := by
  have hd₁ : X.d₁ ≤ X.n₂ := X.d₁_le_numBlocks
  have hbase : (Hypergraph.ofFinsetSet X.edgeFinsetFam).IsUniform X.d₁ :=
    Hypergraph.ofFinsetSet_isUniform fun A hA => X.card_mem_edgeFinsetFam hA
  rw [nbhdHg]
  split_ifs with h
  · have hd' : X.d' = X.d₁ := by rw [d']; omega
    rw [hd']; exact hbase
  · have hd' : X.d' = X.n₂ - X.d₁ := by rw [d']; omega
    have hc := Hypergraph.compl_isUniform hbase
    rw [X.card_blkAmb] at hc
    rw [hd']; exact hc

/-- Complementing changes no automorphism (`Babai.Hypergraph.aut_compl`), so the twins and
the symmetry defect of `H` may be read on the uncomplemented hypergraph. -/
theorem nbhdHg_aut (X : BlkDesignObj s) :
    X.nbhdHg.Aut = (Hypergraph.ofFinsetSet X.edgeFinsetFam).Aut := by
  rw [nbhdHg]
  split_ifs
  · rfl
  · exact Hypergraph.aut_compl _

/-! ### Def. 2.3.9 for `H`: `Babai.BlkCaseObj.IsHTwin` is the twin relation of `Aut(H)` -/

theorem mem_aut_swap_iff_isHTwin (X : BlkDesignObj s) {B B' : Set ↥s} (hB : B ∈ X.blocks)
    (hB' : B' ∈ X.blocks) :
    Equiv.swap (X.blkPt hB) (X.blkPt hB') ∈ X.nbhdHg.Aut ↔ X.IsHTwin B B' := by
  rw [X.nbhdHg_aut]
  constructor
  · intro h
    refine (X.isHTwin_iff_image hB hB').2 fun F hF => ?_
    have hiff := (Hypergraph.mem_aut_iff_edgeSet
      (Hypergraph.ofFinsetSet_isSimple X.edgeFinsetFam) _).1 h F
    rw [Hypergraph.edgeSet_ofFinsetSet] at hiff
    exact hiff.2 hF
  · intro h
    refine Hypergraph.mem_aut_of_involutive_image
      (Hypergraph.ofFinsetSet_isSimple X.edgeFinsetFam)
      (fun x => Equiv.swap_apply_self _ _ x) fun A hA => ?_
    rw [Hypergraph.edgeSet_ofFinsetSet] at hA ⊢
    exact (X.isHTwin_iff_image hB hB').1 h A hA

theorem mem_aut_swap_iff_isHTwin' (X : BlkDesignObj s) (b b' : ↥X.blkAmb) :
    Equiv.swap b b' ∈ X.nbhdHg.Aut ↔ X.IsHTwin (X.blkOf b) (X.blkOf b') := by
  have h := X.mem_aut_swap_iff_isHTwin (X.blkOf_mem b) (X.blkOf_mem b')
  rwa [X.blkPt_blkOf, X.blkPt_blkOf] at h

/-- Def. 2.3.9 and Obs. 2.3.10 for `H`: the *"twin or equal"* relation of `Aut(H)` on the
blocks is `Babai.BlkCaseObj.IsHTwin`, which is how §9.7 states Cases 1 and 2. -/
theorem twinOrEq_iff_isHTwin (X : BlkDesignObj s) (b b' : ↥X.blkAmb) :
    TwinOrEq X.nbhdHg.Aut b b' ↔ X.IsHTwin (X.blkOf b) (X.blkOf b') := by
  constructor
  · rintro (rfl | ⟨-, hmem⟩)
    · exact X.isHTwin_refl _
    · exact (X.mem_aut_swap_iff_isHTwin' b b').1 hmem
  · intro h
    by_cases hbb : b = b'
    · exact Or.inl hbb
    · exact Or.inr ⟨hbb, (X.mem_aut_swap_iff_isHTwin' b b').2 h⟩

/-! ### Case 3: *"the relative symmetry defect of `H` is `≥ 1/2`"* -/

/-- §9.7, Case 3.  The negation of Case 2, *"there is an `H`-twin equivalence class
`C ⊆ V₂` of size `|C| ≥ n₂/2`"*, applied to the twin equivalence class of a block: every
twin equivalence class of `Aut(H)` has fewer than `n₂/2` blocks. -/
theorem twinClass_ncard_lt (X : BlkDesignObj s) (h2 : ¬ X.IsCase2) (b : ↥X.blkAmb) :
    2 * (twinClass X.nbhdHg.Aut b).ncard < X.n₂ := by
  classical
  set G := X.nbhdHg.Aut with hG
  set C : Set (Set ↥s) := X.blkOf '' twinClass G b with hC
  have hCsub : C ⊆ X.blocks := by
    rintro _ ⟨c, -, rfl⟩; exact X.blkOf_mem c
  have hpair : ∀ B ∈ C, ∀ B' ∈ C, X.IsHTwin B B' := by
    rintro _ ⟨c, hc, rfl⟩ _ ⟨c', hc', rfl⟩
    refine (X.twinOrEq_iff_isHTwin c c').1 ?_
    exact (twinOrEq_equivalence G).trans ((twinOrEq_equivalence G).symm hc) hc'
  have hmax : ∀ B ∈ C, ∀ B' ∈ X.blocks, X.IsHTwin B B' → B' ∈ C := by
    rintro _ ⟨c, hc, rfl⟩ B' hB' htw
    have hc' : TwinOrEq G c (X.blkPt hB') := by
      refine (X.twinOrEq_iff_isHTwin c (X.blkPt hB')).2 ?_
      rwa [X.blkOf_blkPt]
    exact ⟨X.blkPt hB', (twinOrEq_equivalence G).trans hc hc', X.blkOf_blkPt hB'⟩
  have hncard : C.ncard = (twinClass G b).ncard :=
    Set.ncard_image_of_injective _ X.blkOf_injective
  by_contra hcon
  exact h2 ⟨C, hCsub, by rw [hncard]; exact Nat.le_of_not_lt hcon, hpair, hmax⟩

/-- §9.7, **Case 3**: *"The relative symmetry defect of `H` is `≥ 1/2`."*  This is the
negation of Case 2 read through Obs. 2.3.12 (`Babai.defect_ge_of_twinClass_ncard_le`): the
symmetricity of `Aut(H)` is the size of a largest twin equivalence class, and by
`Babai.BlkCaseObj.twinClass_ncard_lt` no class has `n₂/2` blocks.

For `n₂ = 0` Lean's `1 − 0/0 = 1`, so the bound holds there too. -/
theorem defect_nbhdHg_ge (X : BlkDesignObj s) (h2 : ¬ X.IsCase2) :
    (1 : ℚ) / 2 ≤ Babai.defect X.nbhdHg.Aut := by
  have hb : ∀ b : ↥X.blkAmb, (twinClass X.nbhdHg.Aut b).ncard ≤ X.n₂ / 2 := by
    intro b
    have := X.twinClass_ncard_lt h2 b
    omega
  have hmain := defect_ge_of_twinClass_ncard_le X.nbhdHg.Aut hb
  rw [X.card_blkAmb] at hmain
  refine le_trans ?_ hmain
  rcases Nat.eq_zero_or_pos X.n₂ with h0 | hpos
  · rw [h0]; norm_num
  · have hn : (0 : ℚ) < (X.n₂ : ℚ) := by exact_mod_cast hpos
    have hle : ((X.n₂ / 2 : ℕ) : ℚ) ≤ (X.n₂ : ℚ) / 2 := by
      have h2n : 2 * (X.n₂ / 2) ≤ X.n₂ := by omega
      have : (2 : ℚ) * ((X.n₂ / 2 : ℕ) : ℚ) ≤ (X.n₂ : ℚ) := by exact_mod_cast h2n
      linarith
    have hdiv : ((X.n₂ / 2 : ℕ) : ℚ) / (X.n₂ : ℚ) ≤ 1 / 2 := by
      rw [div_le_iff₀ hn]
      linarith
    linarith

/-! ### `H` as a `d'`-ary relational structure -/

/-- §9.7, Case 3.  *"`H`, viewed as a `d₁`-ary relational structure"* (§2.5.1,
`Babai.Hypergraph.toRelStructureSimple`), at the rank `N` — which
`Babai.BlkCaseObj.nbhdHg_isUniform` makes `d'`. -/
noncomputable def nbhdStruct (X : BlkDesignObj s) (N : ℕ) : RelStructure ↥X.blkAmb :=
  X.nbhdHg.toRelStructureSimple N

theorem nbhdStruct_isKAry (X : BlkDesignObj s) (N : ℕ) : (X.nbhdStruct N).IsKAry N :=
  fun _ => rfl

/-- §2.5.1: viewing `H` as a relational structure changes no automorphism. -/
theorem aut_nbhdStruct (X : BlkDesignObj s) {N : ℕ} (hN : X.d' = N) :
    (X.nbhdStruct N).Aut = X.nbhdHg.Aut := by
  subst hN
  exact Hypergraph.aut_toRelStructureSimple X.nbhdHg_isSimple X.nbhdHg_isUniform

/-- `n₂ ≤ |Ω|`: the blocks are non-empty and pairwise disjoint, so picking a point in each
is injective.  This is the bound that makes the fibers of `d'` finitely many
(`Babai.FindsAtMultCost.ofFibers`). -/
theorem n₂_le_card (X : BlkCaseObj s Case) : X.n₂ ≤ Fintype.card Ω := by
  classical
  have hpick : ∀ B : ↥X.blocks, ((X.blocks_nonempty B.1 B.2).choose : ↥s) ∈ (B : Set ↥s) :=
    fun B => (X.blocks_nonempty B.1 B.2).choose_spec
  have hinj : Function.Injective
      (fun B : ↥X.blocks => (((X.blocks_nonempty B.1 B.2).choose : ↥s) : Ω)) := by
    intro B B' hBB'
    by_contra hne
    have hne' : (B : Set ↥s) ≠ (B' : Set ↥s) := fun h => hne (Subtype.ext h)
    have hdisj := X.blocks_disjoint B.1 B.2 B'.1 B'.2 hne'
    have hx : ((X.blocks_nonempty B.1 B.2).choose : ↥s)
        = ((X.blocks_nonempty B'.1 B'.2).choose : ↥s) := Subtype.ext hBB'
    exact Set.disjoint_left.1 hdisj (hpick B) (hx ▸ hpick B')
  have h := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_coe_set_eq, Nat.card_eq_fintype_card] at h
  exact h

theorem ncard_blkAmb (X : BlkCaseObj s Case) : X.blkAmb.ncard = X.n₂ := by
  rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card, X.card_blkAmb]

/-- §9.7, Case 3.  The symmetry defect of `H` **as a relational structure**: §2.5.1 says
that viewing `H` as a `d'`-ary relational structure changes no automorphism, so this is
Case 3 itself, *"the relative symmetry defect of `H` is `≥ 1/2`"*. -/
theorem defect_nbhdStruct_ge (X : BlkDesignObj s) (h2 : ¬ X.IsCase2) {N : ℕ}
    (hN : X.d' = N) : (1 : ℚ) / 2 ≤ structDefect (X.nbhdStruct N) := by
  show (1 : ℚ) / 2 ≤ Babai.defect (X.nbhdStruct N).Aut
  rw [X.aut_nbhdStruct hN]
  exact X.defect_nbhdHg_ge h2

/-- §9.7, Case 3.  **`H` as an admissible input of Theorem 8.1.2** at the rank `N = d'` and
the threshold `3/4`.  The three hypotheses of Theorem 8.1.2 are `2 ≤ d'`
(`Babai.BlkCaseObj.two_le_d'`), `2d' ≤ n₂` (`Babai.BlkCaseObj.two_mul_d'_le_n₂` — the
hypothesis §9.7 skips) and the symmetry defect `≥ 1 − 3/4 = 1/4`, which Case 3 gives as
`≥ 1/2` (`Babai.BlkCaseObj.defect_nbhdStruct_ge`). -/
noncomputable def designObj (X : BlkDesignObj s) (hlt : X.n₂ < X.n₁) (h2 : ¬ X.IsCase2)
    {N : ℕ} (hN : X.d' = N) : (DesignInputs (Set Ω) N (3 / 4)).Obj X.blkAmb :=
  ⟨⟨X.nbhdStruct N, X.nbhdStruct_isKAry N⟩, by
    refine ⟨hN ▸ X.two_le_d' hlt, ?_, ?_⟩
    · rw [X.ncard_blkAmb, ← hN]; exact X.two_mul_d'_le_n₂
    · have hdef : (1 : ℚ) / 2 ≤ structDefect (X.nbhdStruct N) := X.defect_nbhdStruct_ge h2 hN
      have hdef' : ((1 : ℚ) / 2 : ℝ) ≤ ((structDefect (X.nbhdStruct N) : ℚ) : ℝ) := by
        exact_mod_cast hdef
      push_cast at hdef' ⊢
      linarith⟩

end BlkCaseObj

/-! ### The transport along a morphism of §9.7 -/

namespace BlkCaseObj

variable {s t : Set Ω}
  {Cs : (Set ↥s → Set ↥s → ℕ) → Set (Set ↥s) → Set (Set ↥s) → Prop}
  {Ct : (Set ↥t → Set ↥t → ℕ) → Set (Set ↥t) → Set (Set ↥t) → Prop}
  {X : BlkCaseObj s Cs} {Y : BlkCaseObj t Ct} {φ : ↥s ≃ ↥t}

/-- The inverse of a morphism of §9.7 is a morphism. -/
theorem IsMorphOn.symm (h : X.IsMorphOn Y φ) : Y.IsMorphOn X φ.symm where
  part₁ y := by
    have := h.part₁ (φ.symm y)
    rw [Equiv.apply_symm_apply] at this
    exact this.symm
  blocks B := by
    have := h.blocks (φ.symm '' B)
    rw [Equiv.image_symm_image] at this
    exact this.symm
  col A B := (h.col (φ.symm '' A) (φ.symm '' B)).symm ▸ by
    rw [Equiv.image_symm_image, Equiv.image_symm_image]

/-- The action of a morphism on the blocks, read on `Babai.BlkCaseObj.blkAmb`. -/
def blkMap (h : X.IsMorphOn Y φ) (b : ↥X.blkAmb) : ↥Y.blkAmb :=
  Y.blkPt ((h.blocks (X.blkOf b)).2 (X.blkOf_mem b))

@[simp] theorem val_blkMap (h : X.IsMorphOn Y φ) (b : ↥X.blkAmb) :
    ((blkMap h b : ↥Y.blkAmb) : Set Ω) = Subtype.val '' (φ '' (X.blkOf b)) := rfl

@[simp] theorem blkOf_blkMap (h : X.IsMorphOn Y φ) (b : ↥X.blkAmb) :
    Y.blkOf (blkMap h b) = φ '' (X.blkOf b) := Y.blkOf_blkPt _

/-- The bijection of the two vertex sets `V₂` that a morphism of §9.7 induces. -/
def blkAmbEquiv (h : X.IsMorphOn Y φ) : ↥X.blkAmb ≃ ↥Y.blkAmb where
  toFun := blkMap h
  invFun := blkMap h.symm
  left_inv b := by
    refine Subtype.ext ?_
    rw [val_blkMap, blkOf_blkMap, Equiv.symm_image_image, X.val_image_blkOf]
  right_inv c := by
    refine Subtype.ext ?_
    rw [val_blkMap, blkOf_blkMap, Equiv.image_symm_image, Y.val_image_blkOf]

@[simp] theorem blkAmbEquiv_apply (h : X.IsMorphOn Y φ) (b : ↥X.blkAmb) :
    blkAmbEquiv h b = blkMap h b := rfl

@[simp] theorem blkAmbEquiv_symm_apply (h : X.IsMorphOn Y φ) (c : ↥Y.blkAmb) :
    (blkAmbEquiv h).symm c = blkMap h.symm c := rfl

/-- A family of blocks read on `Babai.BlkCaseObj.blkAmb` is carried by the induced
bijection to the image family read there. -/
theorem toBlkFinset_image (h : X.IsMorphOn Y φ) (S : Set (Set ↥s)) :
    (X.toBlkFinset S).image (blkAmbEquiv h) = Y.toBlkFinset (imgEquiv φ '' S) := by
  classical
  ext c
  rw [Y.mem_toBlkFinset]
  constructor
  · intro hc
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hc
    rw [X.mem_toBlkFinset] at hb
    exact ⟨X.blkOf b, hb, by rw [blkAmbEquiv_apply, blkOf_blkMap]; rfl⟩
  · rintro ⟨B, hB, hBc⟩
    refine Finset.mem_image.2 ⟨(blkAmbEquiv h).symm c, ?_, (blkAmbEquiv h).apply_symm_apply c⟩
    rw [X.mem_toBlkFinset]
    have hc : Y.blkOf c = φ '' B := hBc.symm
    have h2 : X.blkOf ((blkAmbEquiv h).symm c) = B := by
      rw [blkAmbEquiv_symm_apply, blkOf_blkMap, hc, Equiv.symm_image_image]
    rw [h2]; exact hB

theorem edgeFinsetFam_image_mem (h : X.IsMorphOn Y φ) {F : Finset ↥X.blkAmb}
    (hF : F ∈ X.edgeFinsetFam) : F.image (blkAmbEquiv h) ∈ Y.edgeFinsetFam := by
  obtain ⟨S, hS, rfl⟩ := (X.mem_edgeFinsetFam F).1 hF
  rw [toBlkFinset_image]
  refine (Y.mem_edgeFinsetFam _).2 ⟨imgEquiv φ '' S, ?_, rfl⟩
  rw [h.edgeFam_eq]
  exact ⟨S, hS, rfl⟩

theorem edgeFinsetFam_image (h : X.IsMorphOn Y φ) (F : Finset ↥X.blkAmb) :
    F.image (blkAmbEquiv h) ∈ Y.edgeFinsetFam ↔ F ∈ X.edgeFinsetFam := by
  classical
  refine ⟨fun hF => ?_, fun hF => edgeFinsetFam_image_mem h hF⟩
  have h2 := edgeFinsetFam_image_mem h.symm hF
  rwa [Finset.image_image, show ((blkAmbEquiv h.symm : ↥Y.blkAmb → ↥X.blkAmb) ∘
    (blkAmbEquiv h : ↥X.blkAmb → ↥Y.blkAmb)) = id from
      funext fun b => (blkAmbEquiv h).left_inv b, Finset.image_id] at h2

/-- Complementing is an involution on the families of hyperedges. -/
theorem mem_compl_image_iff {V : Type*} [DecidableEq V] [Fintype V]
    (E : Set (Finset V)) (A : Finset V) :
    A ∈ (fun B : Finset V => Finset.univ \ B) '' E ↔ Finset.univ \ A ∈ E := by
  constructor
  · rintro ⟨B, hB, rfl⟩
    have : Finset.univ \ (Finset.univ \ B) = B := by ext x; simp
    rwa [this]
  · intro hA
    refine ⟨Finset.univ \ A, hA, ?_⟩
    ext x; simp

variable {X : BlkDesignObj s} {Y : BlkDesignObj t}

/-- The hyperedges of `H` correspond under the bijection of the vertex sets that a morphism
of §9.7 induces.  Both objects take the same branch of `Babai.BlkCaseObj.nbhdHg`, because
`d₁` and `n₂` are isomorphism invariants. -/
theorem nbhdHg_edgeSet_image (h : X.IsMorphOn Y φ) (F : Finset ↥X.blkAmb) :
    F.image (blkAmbEquiv h) ∈ Y.nbhdHg.edgeSet ↔ F ∈ X.nbhdHg.edgeSet := by
  classical
  rw [nbhdHg, nbhdHg, h.d₁_eq, h.n₂_eq]
  split_ifs with hc
  · rw [Hypergraph.edgeSet_ofFinsetSet, Hypergraph.edgeSet_ofFinsetSet]
    simpa only [Finset.mem_coe] using edgeFinsetFam_image h F
  · rw [Hypergraph.edgeSet_compl, Hypergraph.edgeSet_compl, mem_compl_image_iff,
      mem_compl_image_iff, Hypergraph.edgeSet_ofFinsetSet, Hypergraph.edgeSet_ofFinsetSet,
      ← Hypergraph.image_sdiff_univ' (blkAmbEquiv h) F]
    simpa only [Finset.mem_coe] using edgeFinsetFam_image h (Finset.univ \ F)

/-- §9.7, Case 3.  The relational structure of `H` is carried to the relational structure
of `H` by the bijection of the vertex sets that a morphism of §9.7 induces.  This is what
makes the assignment *"input ↦ `H`"* a functor. -/
theorem map_nbhdStruct (h : X.IsMorphOn Y φ) (N : ℕ) :
    (X.nbhdStruct N).map ((blkAmbEquiv h : ↥X.blkAmb ≃ ↥Y.blkAmb) : ↥X.blkAmb → ↥Y.blkAmb)
      = Y.nbhdStruct N :=
  Hypergraph.map_toRelStructureSimple X.nbhdHg Y.nbhdHg N (blkAmbEquiv h)
    (nbhdHg_edgeSet_image h)

end BlkCaseObj

/-! ### The assignment *"input ↦ `H`"* as a functor

Case 3a of §9.7 applies the Design Lemma to `H` at the rank `d'`, which is a number read
off the input.  The arity is a **parameter of the category** `Babai.DesignInputs`, so the
assignment is a functor on each fiber `{d' = N}` separately
(`Babai.FindsAtMultCost.ofFibers`). -/

open BlkBlockDesignInputs in
/-- §9.7, Case 3a.  The inputs of Case 3a with `d' = N`: the fiber of
`Babai.FindsAtMultCost.ofFibers` for the isomorphism invariant `d'`. -/
abbrev Case3aFiber (Ω : Type) [Fintype Ω] [DecidableEq Ω] (N : ℕ) : Cat.{0, 0} Ω :=
  ((((BlkBlockDesignInputs Ω).full (fun s X => ¬ Case1P s X)).full
    (fun s X => ¬ Case2P s X.1)).full (fun s X => Case3aP s X.1.1)).full
    (fun s X => (obj₀ ⟨s, X.1.1.1⟩).d' = N)

namespace Case3aFiber

variable {N : ℕ}

/-- The admissible input of §9.7 underlying an object of the fiber. -/
def bbd (Z : Pt (Case3aFiber Ω N)) : Pt (BlkBlockDesignInputs Ω) := ⟨Z.car, Z.obj.1.1.1.1⟩

/-- The object of §9.7 underlying an object of the fiber. -/
def obj (Z : Pt (Case3aFiber Ω N)) : BlkDesignObj Z.car :=
  BlkBlockDesignInputs.obj₀ (bbd Z)

theorem n₂_lt_n₁ (Z : Pt (Case3aFiber Ω N)) : (obj Z).n₂ < (obj Z).n₁ :=
  BlkBlockDesignInputs.numBlocks_lt_n₁ (bbd Z)

theorem not_isCase2 (Z : Pt (Case3aFiber Ω N)) : ¬ (obj Z).IsCase2 := Z.obj.1.1.2

theorem d'_eq (Z : Pt (Case3aFiber Ω N)) : (obj Z).d' = N := Z.obj.2

theorem isCase3a (Z : Pt (Case3aFiber Ω N)) : (obj Z).IsCase3a := Z.obj.1.2

/-- A morphism of the fiber is a morphism of the objects of §9.7. -/
theorem isMorphOn_of_hom {Z W : Pt (Case3aFiber Ω N)} (f : Hom (Case3aFiber Ω N) Z W) :
    (obj Z).IsMorphOn (obj W) f.1 :=
  BlkBlockDesignInputs.isMorphOn_of_iso (X := bbd Z) (Y := bbd W) f.2

end Case3aFiber

/-! ### The data that a Design Lemma call on the blocks needs

Cases 3a and 3b both apply the Design Lemma to a hypergraph on the blocks — `H` itself in
Case 3a, its `t`-skeleton in Case 3b — and then take the **same** exit.  The two calls
differ only in which relational structure is assigned to the input, so the whole of step 2
(`Workspace/SplitOrJohnson/Step97Design.lean`,
`Workspace/SplitOrJohnson/Step97Select.lean`) is written once, for an arbitrary
`Babai.BlkDesignSetup`. -/

/-- §9.7, Case 3.  **The data of a Design Lemma call on the blocks**: a category `C` of
inputs, each carrying an object of §9.7 (`obj`) whose morphisms are the morphisms of `C`
(`morph`), together with a `N`-ary relational structure on the blocks (`dobj`) that is an
admissible input of Theorem 8.1.2 and is carried along by the action on the blocks
(`map_dobj`).

Case 3a instantiates it with `H` itself at the rank `d'` (`Babai.case3aSetup`), Case 3b
with the `t`-skeleton of `H` at the rank `t` (`Babai.case3bSetup`). -/
structure BlkDesignSetup (Ω : Type) [Fintype Ω] [DecidableEq Ω] (N : ℕ) where
  /-- The category of inputs. -/
  C : Cat.{0, 0} Ω
  /-- The admissible input of §9.7 underlying an input. -/
  bbd : ∀ Y : Pt C, (BlkBlockDesignInputs Ω).Obj Y.car
  /-- A morphism of `C` is a morphism of the admissible inputs. -/
  hbbd : ∀ {Y Z : Pt C} {f : ↥Y.car ≃ ↥Z.car}, f ∈ C.IsoP Y Z →
    f ∈ (BlkBlockDesignInputs Ω).IsoP ⟨Y.car, bbd Y⟩ ⟨Z.car, bbd Z⟩
  /-- The relational structure on the blocks handed to the Design Lemma. -/
  dobj : ∀ Y : Pt C,
    (DesignInputs (Set Ω) N (3 / 4)).Obj
      (BlkBlockDesignInputs.obj₀ (⟨Y.car, bbd Y⟩ : Pt (BlkBlockDesignInputs Ω))).blkAmb
  /-- The structure is carried along by the action on the blocks. -/
  map_dobj : ∀ {Y Z : Pt C} (f : Hom C Y Z),
    BlkCaseObj.blkAmbEquiv (BlkBlockDesignInputs.isMorphOn_of_iso (hbbd f.2)) ∈
      (DesignInputs (Set Ω) N (3 / 4)).Iso (dobj Y) (dobj Z)
  /-- `n₂ < n₁`, which §9.7 has for every input. -/
  n₂_lt_n₁ : ∀ Y : Pt C,
    (BlkBlockDesignInputs.obj₀ (⟨Y.car, bbd Y⟩ : Pt (BlkBlockDesignInputs Ω))).n₂ <
      (BlkBlockDesignInputs.obj₀ (⟨Y.car, bbd Y⟩ : Pt (BlkBlockDesignInputs Ω))).n₁

variable {N : ℕ}

/-- The object of §9.7 underlying an input of a Design Lemma call on the blocks. -/
@[reducible] def BlkDesignSetup.obj (S : BlkDesignSetup Ω N) (Y : Pt S.C) :
    BlkDesignObj Y.car :=
  BlkBlockDesignInputs.obj₀ (⟨Y.car, S.bbd Y⟩ : Pt (BlkBlockDesignInputs Ω))

/-- A morphism of `C` is a morphism of the objects of §9.7. -/
theorem BlkDesignSetup.morph (S : BlkDesignSetup Ω N) {Y Z : Pt S.C} (f : Hom S.C Y Z) :
    (S.obj Y).IsMorphOn (S.obj Z) f.1 :=
  BlkBlockDesignInputs.isMorphOn_of_iso (S.hbbd f.2)

open BlkCaseObj in
/-- §9.7, Case 3.  **The Design Lemma's input, as a functor of the input of §9.7**:
*"Apply the Design lemma to `H`, viewed as a `d₁`-ary relational structure."*

The object is the hypergraph on the blocks read as an `N`-ary relational structure over the
ambient type `Set Ω`; a morphism acts on it by its action on the blocks
(`Babai.BlkCaseObj.blkAmbEquiv`). -/
noncomputable def BlkDesignSetup.func (S : BlkDesignSetup Ω N) :
    Func S.C (DesignInputs (Set Ω) N (3 / 4)) where
  obj Z := ⟨(S.obj Z).blkAmb, S.dobj Z⟩
  map {Z W} f := ⟨blkAmbEquiv (S.morph f), S.map_dobj f⟩
  map_id Z := Hom.ext fun b => by
    refine Subtype.ext ?_
    show Subtype.val '' ((Equiv.refl ↥Z.car) '' ((S.obj Z).blkOf b)) = (b : Set Ω)
    rw [Equiv.coe_refl, Set.image_id, (S.obj Z).val_image_blkOf]
  map_trans {Z W U} f g := Hom.ext fun b => by
    refine Subtype.ext ?_
    show Subtype.val '' ((f.1.trans g.1) '' ((S.obj Z).blkOf b))
      = Subtype.val '' (g.1 '' ((S.obj W).blkOf (blkMap (S.morph f) b)))
    rw [blkOf_blkMap, Equiv.coe_trans, Set.image_comp]

open BlkCaseObj in
/-- §9.7, Case 3a.  The Design Lemma call of Case 3a: `H` itself, at the rank `d' = N`
(`Babai.BlkCaseObj.designObj`), carried along by `Babai.BlkCaseObj.map_nbhdStruct`. -/
noncomputable def case3aSetup (Ω : Type) [Fintype Ω] [DecidableEq Ω] (N : ℕ) :
    BlkDesignSetup Ω N where
  C := Case3aFiber Ω N
  bbd Z := Z.obj.1.1.1.1
  hbbd hf := hf
  dobj Z := (Case3aFiber.obj Z).designObj (Case3aFiber.n₂_lt_n₁ Z)
    (Case3aFiber.not_isCase2 Z) (Case3aFiber.d'_eq Z)
  map_dobj f := map_nbhdStruct (Case3aFiber.isMorphOn_of_hom f) N
  n₂_lt_n₁ := Case3aFiber.n₂_lt_n₁

/-- §9.7, Case 3.  The objects that `Babai.BlkDesignSetup.func` assigns are **families of
blocks** in the sense of `Babai.Func.IsBlockFunc`: a morphism acts on a block `B` by
`B ↦ f(B)`.  This is what makes the way back of `Babai.FindsAtMultCost.of_comap`
available. -/
theorem BlkDesignSetup.func_isBlockFunc (S : BlkDesignSetup Ω N) :
    S.func.IsBlockFunc := fun _ _ => rfl

/-- The admissible input of §9.7 underlying an input of a Design Lemma call on the
blocks. -/
@[reducible] def BlkDesignSetup.bbdPt (S : BlkDesignSetup Ω N) (Y : Pt S.C) :
    Pt (BlkBlockDesignInputs Ω) := ⟨Y.car, S.bbd Y⟩

/-- The admissible input of §9.7 underlying a version of the Design Lemma's answer (an
object of the category of versions of `Babai.NormalRed.comap`). -/
@[reducible] def comapBBD {N : ℕ} {S : BlkDesignSetup Ω N}
    {N' : NormalRed (DesignInputs (Set Ω) N (3 / 4))}
    (Y : Pt (NormalRed.comap S.func N').D) : Pt (BlkBlockDesignInputs Ω) :=
  S.bbdPt ⟨Y.car, Y.obj.1⟩

end Babai
