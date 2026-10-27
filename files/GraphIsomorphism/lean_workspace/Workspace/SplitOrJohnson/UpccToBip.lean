/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 9.3: the construction inside the proof of Lemma 9.3.1 (UPCC-to-bipartite).
-/
import Workspace.SplitOrJohnson.Main
import Workspace.Functors.Equivariant
import Workspace.SplitOrJohnson.NatColor

/-!
# §9.3 The construction of Lemma 9.3.1

Proof of Lemma 9.3.1 (version 2.5, lines 4053–4072):

> *"Let `X = (V; R₁,…,R_r)` where `R₁ = diag(V)` is the diagonal.  Let `dᵢ` be the
> out-degree of the vertices in `Rᵢ`; so `d₁ = 1`.  Pick a vertex `x ∈ V`.  Let
> `Cᵢ = {y ∈ V | (x,y) ∈ Rᵢ}`; so `|Cᵢ| = dᵢ`.  Individualize `x`; this splits `V` into the
> (relative) canonical subsets `Cᵢ`.  If `dᵢ ≤ βn` for all `i`, we are done (objective (a)
> has been achieved).  Assume now that (say) `d₂ > βn` … Consider the bipartite graph
> `X̄ = (C₂, Cᵢ; E)` where `E = (C₂ × Cᵢ) ∩ R_j`."*

Everything here is built from the edge coloring `c` and the individualized vertex `x`
alone.  This is forced: an object of `Babai.UPCCs Ω` is a coloring plus the *proposition*
`Babai.IsUPCCColoring`, and a partition structure taken out of that proposition by choice
is not natural in the object (see the module docstring of
`Workspace/SplitOrJohnson/NatColor.lean`).  The facts about `c` that the proof uses are
(N1)–(N6) of that file.

| Paper | Lean |
|---|---|
| the cells `Cᵢ = Rᵢ(x)` | `Babai.cell` |
| *"this splits `V` into the canonical subsets `Cᵢ`"* | `Babai.cellPartition` |
| *"if `dᵢ ≤ βn` for all `i`, we are done"* | `Babai.cellPartition_isAlphaPartition` |
| the color `2` with `d₂ > βn` | `Babai.bigCell`, `Babai.bigCell_unique` |
-/

namespace Babai

variable {Ω : Type} [Fintype Ω] {s : Set Ω}

/-! ### The cells of the individualized vertex -/

/-- §9.3.  *"Let `Cᵢ = {y ∈ V | (x,y) ∈ Rᵢ}`."*  The color class of the color `k` at the
individualized vertex `x`. -/
def cell (c : ↥s → ↥s → ℕ) (x y : ↥s) : Set ↥s := {z | c x z = c x y}

/-- The cell named by a color label. -/
def cellOf (c : ↥s → ↥s → ℕ) (x : ↥s) (k : ℕ) : Set ↥s := {z | c x z = k}

@[simp] theorem mem_cellOf {c : ↥s → ↥s → ℕ} {x : ↥s} {k : ℕ} {z : ↥s} :
    z ∈ cellOf c x k ↔ c x z = k := Iff.rfl

theorem cell_eq_cellOf (c : ↥s → ↥s → ℕ) (x y : ↥s) : cell c x y = cellOf c x (c x y) := rfl

/-- The cells at `x` are pairwise disjoint. -/
theorem cellOf_disjoint {c : ↥s → ↥s → ℕ} {x : ↥s} {k l : ℕ} (h : k ≠ l) :
    Disjoint (cellOf c x k) (cellOf c x l) := by
  rw [Set.disjoint_left]
  intro z hz hz'
  exact h (hz ▸ hz')

/-- The diagonal cell is the single vertex `x` (axiom (i) of Def. 3.1.2). -/
theorem cellOf_diag {c : ↥s → ↥s → ℕ} (hc : IsUPCCColoring c) (x : ↥s) :
    cellOf c x (c x x) = {x} := by
  ext z
  constructor
  · intro hz
    exact (natColor_eq_diag_imp_eq hc hz).symm
  · intro hz
    simp only [Set.mem_singleton_iff] at hz
    rw [hz]
    rfl

/-! ### Objective (a): the partition of `V` into the cells -/

/-- §9.3.  *"Individualize `x`; this splits `V` into the (relative) canonical subsets
`Cᵢ`."*  The colored partition of `V` whose color classes — and whose blocks — are the
cells of `x`. -/
def cellPartition (c : ↥s → ↥s → ℕ) (x : ↥s) : ColoredPartition ↥s ℕ where
  color y := c x y
  part := ⟨fun y z => c x y = c x z, ⟨fun _ => rfl, fun h => h.symm, fun h h' => h.trans h'⟩⟩
  part_le_color h := h

theorem cellPartition_block (c : ↥s → ↥s → ℕ) (x y : ↥s) :
    (cellPartition c x).block y = cell c x y := rfl

theorem cellPartition_colorClass (c : ↥s → ↥s → ℕ) (x y : ↥s) :
    (cellPartition c x).colorClass ((cellPartition c x).color y) = cell c x y := rfl

/-- The partition into cells is admissible (Def. 7.1.1): each block **is** a color
class. -/
theorem cellPartition_isAdmissible (c : ↥s → ↥s → ℕ) (x : ↥s) :
    (cellPartition c x).IsAdmissible := fun _ h => h

/-- §9.3.  *"If `dᵢ ≤ βn` for all `i`, we are done (objective (a) has been achieved)."* -/
theorem cellPartition_isAlphaPartition [Fintype ↥s] {c : ↥s → ↥s → ℕ} {x : ↥s} {β : ℝ}
    (h : ∀ k : ℕ, ((cellOf c x k).ncard : ℝ) ≤ β * (Fintype.card ↥s : ℝ)) :
    (cellPartition c x).IsAlphaPartition β := by
  refine ⟨cellPartition_isAdmissible c x, ?_⟩
  rcases isEmpty_or_nonempty ↥s with hem | hne
  · have h0 : (cellPartition c x).rho = 0 := by
      rw [ColoredPartition.rho]
      simp [Finset.univ_eq_empty]
    have hcard : Fintype.card ↥s = 0 := Fintype.card_eq_zero
    rw [h0, hcard]
    norm_num
  · obtain ⟨y, -, hy⟩ :=
      Finset.exists_mem_eq_sup (Finset.univ : Finset ↥s) Finset.univ_nonempty
        (fun y => ((cellPartition c x).block y).ncard)
    have : (cellPartition c x).rho = (cell c x y).ncard := hy
    rw [this, cell_eq_cellOf]
    exact h _

/-! ### The bipartite graph `X̄ = (C₂, Cᵢ; E)`

The construction is parameterized by the three color labels `k` (the paper's `2`), `i` and
`j`.  The canonical choice of the labels is made further below; here they are arguments,
and the properties of `X̄` are proved from the properties of the labels that the proof of
Lemma 9.3.1 establishes. -/

/-- The vertex set of `X̄`: the union of the two cells, as a subset of the ambient type. -/
def bipCarrier (c : ↥s → ↥s → ℕ) (x : ↥s) (k i : ℕ) : Set Ω :=
  Subtype.val '' (cellOf c x k ∪ cellOf c x i)

theorem bipCarrier_subset (c : ↥s → ↥s → ℕ) (x : ↥s) (k i : ℕ) :
    bipCarrier c x k i ⊆ s := by
  rintro z ⟨w, -, rfl⟩
  exact w.2

/-- A vertex of `X̄`, read as a vertex of the ambient UPCC. -/
def bipIota {c : ↥s → ↥s → ℕ} {x : ↥s} {k i : ℕ} (w : ↥(bipCarrier c x k i)) : ↥s :=
  ⟨(w : Ω), bipCarrier_subset c x k i w.2⟩

theorem bipIota_injective {c : ↥s → ↥s → ℕ} {x : ↥s} {k i : ℕ} :
    Function.Injective (bipIota (c := c) (x := x) (k := k) (i := i)) :=
  by
  intro a b h
  have hval : ((bipIota a : ↥s) : Ω) = ((bipIota b : ↥s) : Ω) := congrArg Subtype.val h
  exact Subtype.ext hval

theorem bipIota_mem {c : ↥s → ↥s → ℕ} {x : ↥s} {k i : ℕ} (w : ↥(bipCarrier c x k i)) :
    bipIota w ∈ cellOf c x k ∪ cellOf c x i := by
  obtain ⟨v, hv, hv'⟩ := w.2
  have : bipIota w = v := Subtype.ext hv'.symm
  rw [this]
  exact hv

/-- The number of vertices of `X̄` lying in a given set of vertices of the UPCC, when that
set is contained in the union of the two cells. -/
theorem ncard_bipIota_preimage {c : ↥s → ↥s → ℕ} {x : ↥s} {k i : ℕ} {A : Set ↥s}
    (hA : A ⊆ cellOf c x k ∪ cellOf c x i) :
    {w : ↥(bipCarrier c x k i) | bipIota w ∈ A}.ncard = A.ncard := by
  have himg : (bipIota (c := c) (x := x) (k := k) (i := i)) ''
      {w : ↥(bipCarrier c x k i) | bipIota w ∈ A} = A := by
    ext v
    constructor
    · rintro ⟨w, hw, rfl⟩; exact hw
    · intro hv
      refine ⟨⟨(v : Ω), ⟨v, hA hv, rfl⟩⟩, ?_, rfl⟩
      show bipIota (⟨(v : Ω), ⟨v, hA hv, rfl⟩⟩ : ↥(bipCarrier c x k i)) ∈ A
      exact hv
  have hcard := Set.ncard_image_of_injective {w : ↥(bipCarrier c x k i) | bipIota w ∈ A}
    (bipIota_injective (c := c) (x := x) (k := k) (i := i))
  rw [himg] at hcard
  exact hcard.symm

/-- §9.3.  *"Consider the bipartite graph `X̄ = (C₂, Cᵢ; E)` where `E = (C₂ × Cᵢ) ∩ R_j`."*

The second part is written `{w | c x w ≠ k}` rather than `{w | c x w = i}`; on the vertex
set of `X̄` the two agree as soon as `i ≠ k`, and writing it this way makes the edges run
from the first part to the second by construction.  The vertex coloring `f` is the cell of
the vertex, which is what distinguishes the two parts (§9.4). -/
def bipGraph (c : ↥s → ↥s → ℕ) (x : ↥s) (k i j : ℕ) :
    VColBip ↥(bipCarrier c x k i) ℕ where
  part₁ w := c x (bipIota w) = k
  E := {p | c x (bipIota p.1) = k ∧ c x (bipIota p.2) ≠ k ∧
    c (bipIota p.1) (bipIota p.2) = j}
  f w := c x (bipIota w)
  E_sub _ hp := ⟨hp.1, hp.2.1⟩

theorem bipGraph_V₁ (c : ↥s → ↥s → ℕ) (x : ↥s) (k i j : ℕ) :
    (bipGraph c x k i j).V₁ = {w | bipIota w ∈ cellOf c x k} := rfl

theorem bipGraph_V₂ (c : ↥s → ↥s → ℕ) (x : ↥s) (k i j : ℕ) :
    (bipGraph c x k i j).V₂ = {w | bipIota w ∉ cellOf c x k} := rfl

/-- On the vertex set of `X̄` the second part is the cell `Cᵢ`. -/
theorem bipGraph_V₂_eq {c : ↥s → ↥s → ℕ} {x : ↥s} {k i j : ℕ} (hik : i ≠ k) :
    (bipGraph c x k i j).V₂ = {w | bipIota w ∈ cellOf c x i} := by
  ext w
  rcases bipIota_mem w with hw | hw
  · exact ⟨fun hcon => absurd hw hcon, fun hcon => absurd (hcon.symm.trans hw) hik⟩
  · exact ⟨fun _ => hw, fun _ hcon => hik (hw.symm.trans hcon)⟩

theorem ncard_bipGraph_V₁ (c : ↥s → ↥s → ℕ) (x : ↥s) (k i j : ℕ) :
    (bipGraph c x k i j).V₁.ncard = (cellOf c x k).ncard :=
  ncard_bipIota_preimage Set.subset_union_left

theorem ncard_bipGraph_V₂ {c : ↥s → ↥s → ℕ} {x : ↥s} {k i j : ℕ} (hik : i ≠ k) :
    (bipGraph c x k i j).V₂.ncard = (cellOf c x i).ncard := by
  rw [bipGraph_V₂_eq hik]
  exact ncard_bipIota_preimage Set.subset_union_right

/-- The degree of a vertex of the first part of `X̄`, as a count inside the UPCC:
the number of common out-neighbours of `x` in color `i` and of `w` in color `j`. -/
theorem degA_bipGraph {c : ↥s → ↥s → ℕ} {x : ↥s} {k i j : ℕ} (hik : i ≠ k)
    {w : ↥(bipCarrier c x k i)} (hw : c x (bipIota w) = k) :
    (bipGraph c x k i j).degA w
      = {v : ↥s | c x v = i ∧ c (bipIota w) v = j}.ncard := by
  have hset : {y : ↥(bipCarrier c x k i) | (w, y) ∈ (bipGraph c x k i j).E}
      = {y | bipIota y ∈ {v : ↥s | c x v = i ∧ c (bipIota w) v = j}} := by
    ext y
    constructor
    · rintro ⟨-, hy2, hy3⟩
      refine ⟨?_, hy3⟩
      rcases bipIota_mem y with hy | hy
      · exact absurd hy hy2
      · exact hy
    · rintro ⟨hy1, hy2⟩
      exact ⟨hw, fun hcon => hik (hy1.symm.trans hcon), hy2⟩
  rw [VColBip.degA, hset]
  exact ncard_bipIota_preimage fun v hv => Or.inr hv.1

/-- The degree of a vertex of the second part of `X̄`, as a count inside the UPCC:
the number of vertices of the cell `C_k` joined to it in color `j`. -/
theorem degB_bipGraph {c : ↥s → ↥s → ℕ} {x : ↥s} {k i j : ℕ} (hik : i ≠ k)
    {v : ↥(bipCarrier c x k i)} (hv : c x (bipIota v) = i) :
    (bipGraph c x k i j).degB v
      = {u : ↥s | c x u = k ∧ c u (bipIota v) = j}.ncard := by
  have hset : {u : ↥(bipCarrier c x k i) | (u, v) ∈ (bipGraph c x k i j).E}
      = {u | bipIota u ∈ {u : ↥s | c x u = k ∧ c u (bipIota v) = j}} := by
    ext u
    exact ⟨fun hu => ⟨hu.1, hu.2.2⟩,
      fun hu => ⟨hu.1, fun hcon => hik (hv.symm.trans hcon), hu.2⟩⟩
  rw [VColBip.degB, hset]
  exact ncard_bipIota_preimage fun u hu => Or.inl hu.1

/-- *"`X̄` is a semiregular (Prop. 3.4.5) bipartite graph"* (§9.3, line 4062): both degrees
are intersection numbers of the coherent configuration, by (N3) and (N3′). -/
theorem bipGraph_isSemiregular {c : ↥s → ↥s → ℕ} (hc : IsUPCCColoring c) {x : ↥s}
    {k i j : ℕ} (hik : i ≠ k) : (bipGraph c x k i j).IsSemiregular := by
  constructor
  · rcases Set.eq_empty_or_nonempty (bipGraph c x k i j).V₁ with hem | ⟨w₀, hw₀⟩
    · exact ⟨0, fun w hw => absurd hw (by rw [hem]; exact fun h => h)⟩
    · refine ⟨{v : ↥s | c x v = i ∧ c (bipIota w₀) v = j}.ncard, fun w hw => ?_⟩
      rw [degA_bipGraph hik (show c x (bipIota w) = k from hw)]
      exact natColor_interNum_out hc
        ((show c x (bipIota w) = k from hw).trans (show c x (bipIota w₀) = k from hw₀).symm)
        i j
  · rcases Set.eq_empty_or_nonempty (bipGraph c x k i j).V₂ with hem | ⟨v₀, hv₀⟩
    · exact ⟨0, fun v hv => absurd hv (by rw [hem]; exact fun h => h)⟩
    · have hv₀' : c x (bipIota v₀) = i := by
        rw [bipGraph_V₂_eq hik] at hv₀; exact hv₀
      refine ⟨{u : ↥s | c x u = k ∧ c u (bipIota v₀) = j}.ncard, fun v hv => ?_⟩
      have hv' : c x (bipIota v) = i := by
        rw [bipGraph_V₂_eq hik] at hv; exact hv
      rw [degB_bipGraph hik hv']
      exact natColor_interNum hc (hv'.trans hv₀'.symm) k j


/-! ### `X̄` is nontrivial -/

/-- The vertex of `X̄` given by a vertex of one of the two cells. -/
def bipPt {c : ↥s → ↥s → ℕ} {x : ↥s} {k i : ℕ} {v : ↥s}
    (hv : v ∈ cellOf c x k ∪ cellOf c x i) : ↥(bipCarrier c x k i) :=
  ⟨(v : Ω), ⟨v, hv, rfl⟩⟩

@[simp] theorem bipIota_bipPt {c : ↥s → ↥s → ℕ} {x : ↥s} {k i : ℕ} {v : ↥s}
    (hv : v ∈ cellOf c x k ∪ cellOf c x i) : bipIota (bipPt hv) = v := rfl

/-- §9.3.  *"We have `E ≠ ∅` since `(z,y) ∈ E`."* -/
theorem bipGraph_E_nonempty {c : ↥s → ↥s → ℕ} {x : ↥s} {k i j : ℕ} (hik : i ≠ k)
    {z y : ↥s} (hz : c x z = k) (hy : c x y = i) (hzy : c z y = j) :
    (bipGraph c x k i j).E ≠ ∅ := by
  intro hem
  have hmem : ((bipPt (Or.inl hz : z ∈ cellOf c x k ∪ cellOf c x i)),
      (bipPt (Or.inr hy : y ∈ cellOf c x k ∪ cellOf c x i))) ∈ (bipGraph c x k i j).E :=
    ⟨hz, fun hcon => hik (hy.symm.trans hcon), hzy⟩
  rw [hem] at hmem
  exact hmem

/-- §9.3.  *"The degree of `y ∈ Cᵢ` in `X̄` is `d_j < n/3 < 2n/3 ≤ d₂` and therefore `E` is
not complete."*  The hypothesis is that inequality: fewer vertices of `C_k` are joined to
`y` in color `j` than `C_k` has. -/
theorem bipGraph_not_complete {c : ↥s → ↥s → ℕ} {x : ↥s} {k i j : ℕ} (hik : i ≠ k)
    {y : ↥s} (hy : c x y = i)
    (hlt : {u : ↥s | c x u = k ∧ c u y = j}.ncard < (cellOf c x k).ncard) :
    (bipGraph c x k i j).E
      ≠ {p | (bipGraph c x k i j).part₁ p.1 ∧ ¬ (bipGraph c x k i j).part₁ p.2} := by
  intro hcompl
  -- some vertex of `C_k` is not joined to `y` in color `j`
  obtain ⟨u, hu, huy⟩ : ∃ u ∈ cellOf c x k, c u y ≠ j := by
    by_contra hcon
    push_neg at hcon
    have heq : {u : ↥s | c x u = k ∧ c u y = j} = cellOf c x k :=
      Set.Subset.antisymm (fun u hu => hu.1) (fun u hu => ⟨hu, hcon u hu⟩)
    rw [heq] at hlt
    exact lt_irrefl _ hlt
  have hmem : ((bipPt (Or.inl hu : u ∈ cellOf c x k ∪ cellOf c x i)),
      (bipPt (Or.inr hy : y ∈ cellOf c x k ∪ cellOf c x i)))
      ∈ {p : ↥(bipCarrier c x k i) × ↥(bipCarrier c x k i) |
          (bipGraph c x k i j).part₁ p.1 ∧ ¬ (bipGraph c x k i j).part₁ p.2} :=
    ⟨hu, fun hcon => hik (hy.symm.trans hcon)⟩
  rw [← hcompl] at hmem
  exact huy hmem.2.2

/-- §9.3.  *"`X̄` … is nontrivial"*: it is neither empty nor complete, which is what
Prop. 2.4.30 needs in order to give symmetry defect `≥ 1/2` in each part. -/
theorem bipGraph_not_isTrivial {c : ↥s → ↥s → ℕ} {x : ↥s} {k i j : ℕ} (hik : i ≠ k)
    {z y : ↥s} (hz : c x z = k) (hy : c x y = i) (hzy : c z y = j)
    (hlt : {u : ↥s | c x u = k ∧ c u y = j}.ncard < (cellOf c x k).ncard) :
    ¬ (bipGraph c x k i j).IsTrivial := by
  rintro (hem | hcompl)
  · exact bipGraph_E_nonempty hik hz hy hzy hem
  · exact bipGraph_not_complete hik hy hlt hcompl

/-! ### Counting the cells -/

/-- (N2) and (N4): the number of vertices joined to `y` in color `j` is the size of the
cell `C_j`, whichever `y` is. -/
theorem ncard_inNbr_eq_cell {c : ↥s → ↥s → ℕ} (hc : IsUPCCColoring c) (x y : ↥s) (j : ℕ) :
    {u : ↥s | c u y = j}.ncard = (cellOf c x j).ncard :=
  (natColor_inDeg_eq_outDeg hc y j).trans (natColor_outDeg_eq hc y x j)

/-- Three cells of distinct colors, one of them the diagonal cell `{x}`, fit inside the
vertex set. -/
theorem cell_add_cell_add_one_le {c : ↥s → ↥s → ℕ} (hc : IsUPCCColoring c) (x : ↥s)
    {k j : ℕ} (hjk : j ≠ k) (hjd : j ≠ c x x) (hkd : k ≠ c x x) :
    (cellOf c x j).ncard + (cellOf c x k).ncard + 1 ≤ s.ncard := by
  have hdisj : Disjoint (cellOf c x j ∪ cellOf c x k) (cellOf c x (c x x)) := by
    rw [Set.disjoint_union_left]
    exact ⟨cellOf_disjoint hjd, cellOf_disjoint hkd⟩
  have h1 : (cellOf c x j ∪ cellOf c x k).ncard
      = (cellOf c x j).ncard + (cellOf c x k).ncard :=
    Set.ncard_union_eq (cellOf_disjoint hjk) (Set.toFinite _) (Set.toFinite _)
  have h2 : ((cellOf c x j ∪ cellOf c x k) ∪ cellOf c x (c x x)).ncard
      = (cellOf c x j).ncard + (cellOf c x k).ncard + 1 := by
    rw [Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _), h1,
      cellOf_diag hc x, Set.ncard_singleton]
  rw [← h2]
  have hle := Set.ncard_le_ncard
    (Set.subset_univ ((cellOf c x j ∪ cellOf c x k) ∪ cellOf c x (c x x)))
    (Set.toFinite _)
  rwa [Set.ncard_univ, Nat.card_coe_set_eq] at hle

/-! ### The canonical choice of the three colors

The paper writes *"assume now that (say) `d₂ > βn`"* and *"let `(x,z) ∈ R₂` and let
`y ∈ V` be such that …"*.  The color `k` with `d_k > βn` is unique (`bigCell_unique`), so
naming it is canonical.  The vertices `z` and `y` are *not* canonical, but the
construction uses them only through the two colors `i = c(x,y)` and `j = c(z,y)`; so the
pair `(i,j)` is taken to be the least one (in the pairing order of `ℕ`) for which such
`z`, `y` exist.  Both choices are formulas in `c` and `x`, which is what canonicity
requires. -/

/-- §9.3.  *"Assume now that (say) `d₂ > βn`."*  At most one color has a cell of more than
`βn` vertices, because two such cells are disjoint and `2βn ≥ n`. -/
theorem bigCell_unique {c : ↥s → ↥s → ℕ} {x : ↥s} {β : ℝ} (hβ : 1 / 2 ≤ β) {k l : ℕ}
    (hk : β * (s.ncard : ℝ) < ((cellOf c x k).ncard : ℝ))
    (hl : β * (s.ncard : ℝ) < ((cellOf c x l).ncard : ℝ)) : k = l := by
  by_contra hkl
  have hsum : (cellOf c x k).ncard + (cellOf c x l).ncard ≤ s.ncard := by
    rw [← Set.ncard_union_eq (cellOf_disjoint hkl) (Set.toFinite _) (Set.toFinite _)]
    have hle := Set.ncard_le_ncard (Set.subset_univ (cellOf c x k ∪ cellOf c x l))
      (Set.toFinite _)
    rwa [Set.ncard_univ, Nat.card_coe_set_eq] at hle
  have hsum' : ((cellOf c x k).ncard : ℝ) + ((cellOf c x l).ncard : ℝ) ≤ (s.ncard : ℝ) := by
    exact_mod_cast hsum
  have h0 : (0 : ℝ) ≤ (s.ncard : ℝ) := by positivity
  nlinarith

open scoped Classical in
/-- The color `k` with `d_k > βn`, if there is one (`bigCell_unique`: there is at most
one).  The value `0` when there is none is never used. -/
noncomputable def bigCellIdx (β : ℝ) (c : ↥s → ↥s → ℕ) (x : ↥s) : ℕ :=
  if h : ∃ k : ℕ, β * (s.ncard : ℝ) < ((cellOf c x k).ncard : ℝ) then h.choose else 0

theorem bigCellIdx_spec {β : ℝ} {c : ↥s → ↥s → ℕ} {x : ↥s}
    (h : ∃ k : ℕ, β * (s.ncard : ℝ) < ((cellOf c x k).ncard : ℝ)) :
    β * (s.ncard : ℝ) < ((cellOf c x (bigCellIdx β c x)).ncard : ℝ) := by
  classical
  rw [bigCellIdx, dif_pos h]
  exact h.choose_spec

/-- The color with the big cell is the one named by `bigCellIdx`. -/
theorem bigCellIdx_eq {β : ℝ} (hβ : 1 / 2 ≤ β) {c : ↥s → ↥s → ℕ} {x : ↥s} {k : ℕ}
    (hk : β * (s.ncard : ℝ) < ((cellOf c x k).ncard : ℝ)) : bigCellIdx β c x = k :=
  bigCell_unique hβ (bigCellIdx_spec ⟨k, hk⟩) hk

/-- §9.3.  *"Let `(x,z) ∈ R₂` and let `y ∈ V` be such that `(x,y) ∈ Rᵢ` and `(z,y) ∈ R_j`
where `i, j ≥ 3`."*  The property of the pair `(i,j)`, encoded as one number by the
pairing function of `ℕ`. -/
def MidPair (c : ↥s → ↥s → ℕ) (x : ↥s) (k m : ℕ) : Prop :=
  ∃ z y : ↥s, c x z = k ∧ c x y = m.unpair.1 ∧ c z y = m.unpair.2 ∧
    m.unpair.1 ≠ c x x ∧ m.unpair.1 ≠ k ∧ m.unpair.2 ≠ c x x ∧ m.unpair.2 ≠ k

open scoped Classical in
/-- The least code of a pair `(i,j)` as in the diameter-2 step. -/
noncomputable def midIdx (c : ↥s → ↥s → ℕ) (x : ↥s) (k : ℕ) : ℕ :=
  if h : ∃ m, MidPair c x k m then Nat.find h else 0

/-- The color `i` of the second cell of `X̄`. -/
noncomputable def midI (c : ↥s → ↥s → ℕ) (x : ↥s) (k : ℕ) : ℕ := (midIdx c x k).unpair.1

/-- The color `j` of the edges of `X̄`. -/
noncomputable def midJ (c : ↥s → ↥s → ℕ) (x : ↥s) (k : ℕ) : ℕ := (midIdx c x k).unpair.2

theorem midIdx_spec {c : ↥s → ↥s → ℕ} {x : ↥s} {k : ℕ} (h : ∃ m, MidPair c x k m) :
    MidPair c x k (midIdx c x k) := by
  classical
  rw [midIdx, dif_pos h]
  exact Nat.find_spec h

/-- §9.3.  The diameter-2 step gives such a pair, once `d_k > βn`. -/
theorem exists_midPair {c : ↥s → ↥s → ℕ} (hc : IsUPCCColoring c) {x : ↥s} {β : ℝ}
    (hβ : 2 / 3 ≤ β) {k : ℕ}
    (hk : β * (s.ncard : ℝ) < ((cellOf c x k).ncard : ℝ)) : ∃ m, MidPair c x k m := by
  -- the vertex set has at least two elements
  obtain ⟨u₀, v₀, huv⟩ := natColor_nontrivial hc
  haveI : Nontrivial ↥s := ⟨u₀, v₀, huv⟩
  have hn2 : 2 ≤ s.ncard := by
    have h1 : 1 < Nat.card ↥s := Finite.one_lt_card
    rw [Nat.card_coe_set_eq] at h1
    omega
  have hn2' : (2 : ℝ) ≤ (s.ncard : ℝ) := by exact_mod_cast hn2
  have hbn : (4 : ℝ) / 3 ≤ β * (s.ncard : ℝ) := by nlinarith
  -- the big cell is not the diagonal cell
  have hkd : k ≠ c x x := by
    intro hcon
    rw [hcon, cellOf_diag hc x, Set.ncard_singleton] at hk
    norm_num at hk
    linarith
  -- the color `k` is symmetric, since its cell has more than half the vertices
  have hhalf : Nat.card ↥s < 2 * (cellOf c x k).ncard := by
    have : (s.ncard : ℝ) < 2 * ((cellOf c x k).ncard : ℝ) := by nlinarith
    rw [Nat.card_coe_set_eq]
    exact_mod_cast this
  have hsymm : ∀ u v : ↥s, c u v = k → c v u = k := fun u v h =>
    natColor_symm_of_large hc (x := x) hhalf h
  -- a vertex `z` of the big cell
  obtain ⟨z, hz⟩ : (cellOf c x k).Nonempty := by
    rw [← Set.ncard_pos (Set.toFinite _)]
    have : (0 : ℝ) < ((cellOf c x k).ncard : ℝ) := by linarith
    exact_mod_cast this
  obtain ⟨y, h1, h2, h3, h4⟩ := natColor_exists_mid hc hsymm (z := z) hz hkd
  refine ⟨Nat.pair (c x y) (c z y), z, y, hz, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    rw [Nat.unpair_pair]
  · exact h1
  · exact h2
  · exact h3
  · exact h4

/-! ### The estimates of the case `d₂ > βn` -/

/-- A UPCC has at least two vertices. -/
theorem upcc_two_le_ncard {c : ↥s → ↥s → ℕ} (hc : IsUPCCColoring c) : 2 ≤ s.ncard := by
  obtain ⟨u₀, v₀, huv⟩ := natColor_nontrivial hc
  haveI : Nontrivial ↥s := ⟨u₀, v₀, huv⟩
  have h1 : 1 < Nat.card ↥s := Finite.one_lt_card
  rw [Nat.card_coe_set_eq] at h1
  omega

/-- The color of the big cell is not the color of the vertices: the diagonal cell has one
element, while the big cell has more than `βn ≥ 4/3`. -/
theorem bigCell_ne_diag {c : ↥s → ↥s → ℕ} (hc : IsUPCCColoring c) {x : ↥s} {β : ℝ}
    (hβ : 2 / 3 ≤ β) {k : ℕ}
    (hk : β * (s.ncard : ℝ) < ((cellOf c x k).ncard : ℝ)) : k ≠ c x x := by
  have hn2 : (2 : ℝ) ≤ (s.ncard : ℝ) := by exact_mod_cast upcc_two_le_ncard hc
  intro hcon
  rw [hcon, cellOf_diag hc x, Set.ncard_singleton] at hk
  norm_num at hk
  nlinarith

/-- Every other cell, apart from the big one and the diagonal one, is small: it misses
the big cell and the vertex `x`. -/
theorem cell_ncard_lt_of_ne {c : ↥s → ↥s → ℕ} (hc : IsUPCCColoring c) {x : ↥s} {β : ℝ}
    (hβ : 2 / 3 ≤ β) {k l : ℕ}
    (hk : β * (s.ncard : ℝ) < ((cellOf c x k).ncard : ℝ)) (hlk : l ≠ k)
    (hld : l ≠ c x x) :
    ((cellOf c x l).ncard : ℝ) < (s.ncard : ℝ) - β * (s.ncard : ℝ) := by
  have hsum := cell_add_cell_add_one_le hc x hlk hld (bigCell_ne_diag hc hβ hk)
  have hsum' : ((cellOf c x l).ncard : ℝ) + ((cellOf c x k).ncard : ℝ) + 1
      ≤ (s.ncard : ℝ) := by exact_mod_cast hsum
  linarith

/-- The big cell has more than half the vertices, so every other cell is smaller than
it. -/
theorem cell_ncard_lt_bigCell {c : ↥s → ↥s → ℕ} (hc : IsUPCCColoring c) {x : ↥s} {β : ℝ}
    (hβ : 2 / 3 ≤ β) {k l : ℕ}
    (hk : β * (s.ncard : ℝ) < ((cellOf c x k).ncard : ℝ)) (hlk : l ≠ k)
    (hld : l ≠ c x x) : (cellOf c x l).ncard < (cellOf c x k).ncard := by
  have h1 := cell_ncard_lt_of_ne hc hβ hk hlk hld
  have hn2 : (2 : ℝ) ≤ (s.ncard : ℝ) := by exact_mod_cast upcc_two_le_ncard hc
  have : ((cellOf c x l).ncard : ℝ) < ((cellOf c x k).ncard : ℝ) := by nlinarith
  exact_mod_cast this

/-- The big cell has at least two vertices. -/
theorem two_le_bigCell {c : ↥s → ↥s → ℕ} (hc : IsUPCCColoring c) {x : ↥s} {β : ℝ}
    (hβ : 2 / 3 ≤ β) {k : ℕ}
    (hk : β * (s.ncard : ℝ) < ((cellOf c x k).ncard : ℝ)) :
    2 ≤ (cellOf c x k).ncard := by
  have hn2 : (2 : ℝ) ≤ (s.ncard : ℝ) := by exact_mod_cast upcc_two_le_ncard hc
  have : (1 : ℝ) < ((cellOf c x k).ncard : ℝ) := by nlinarith
  have : 1 < (cellOf c x k).ncard := by exact_mod_cast this
  omega

/-! ### The data of the case `d₂ > βn`, collected

`bipCase` bundles what the proof of Lemma 9.3.1 establishes about the three colors
`k = bigCellIdx`, `i = midI` and `j = midJ`: the hypotheses of `bipGraph_isSemiregular`,
of `bipGraph_not_isTrivial`, and the size estimates that make `X̄` an admissible input of
Theorem 9.2.2 for the threshold `α = βn/d_k`. -/

/-- The threshold parameter handed to Theorem 9.2.2: *"let now `α = βn/d₂`"*. -/
noncomputable def bipAlpha (β : ℝ) (c : ↥s → ↥s → ℕ) (x : ↥s) (k : ℕ) : ℝ :=
  β * (s.ncard : ℝ) / ((cellOf c x k).ncard : ℝ)

/-- The conclusions of the case `d₂ > βn` of the proof of Lemma 9.3.1, for the three
canonically chosen colors. -/
theorem bipCase {c : ↥s → ↥s → ℕ} (hc : IsUPCCColoring c) {x : ↥s} {β : ℝ}
    (hβ : 2 / 3 ≤ β) {k : ℕ}
    (hk : β * (s.ncard : ℝ) < ((cellOf c x k).ncard : ℝ)) :
    midI c x k ≠ k ∧
    (bipGraph c x k (midI c x k) (midJ c x k)).IsSemiregular ∧
    ¬ (bipGraph c x k (midI c x k) (midJ c x k)).IsTrivial ∧
    2 ≤ (bipGraph c x k (midI c x k) (midJ c x k)).V₁.ncard ∧
    (((bipGraph c x k (midI c x k) (midJ c x k)).V₂.ncard : ℝ)
      < bipAlpha β c x k * ((bipGraph c x k (midI c x k) (midJ c x k)).V₁.ncard : ℝ)) ∧
    β * (s.ncard : ℝ)
      ≤ ((bipGraph c x k (midI c x k) (midJ c x k)).V₁.ncard : ℝ) ∧
    β ≤ bipAlpha β c x k ∧ bipAlpha β c x k < 1 ∧
    bipAlpha β c x k * ((bipGraph c x k (midI c x k) (midJ c x k)).V₁.ncard : ℝ)
      = β * (s.ncard : ℝ) := by
  classical
  obtain ⟨z, y, hz, hy, hzy, hid, hik, hjd, hjk⟩ :=
    midIdx_spec (exists_midPair hc hβ hk)
  -- `hy`, `hzy` name the two colors
  have hyi : c x y = midI c x k := hy
  have hzyj : c z y = midJ c x k := hzy
  have hik' : midI c x k ≠ k := hik
  have hjk' : midJ c x k ≠ k := hjk
  have hid' : midI c x k ≠ c x x := hid
  have hjd' : midJ c x k ≠ c x x := hjd
  have hn2 : (2 : ℝ) ≤ (s.ncard : ℝ) := by exact_mod_cast upcc_two_le_ncard hc
  have hdpos : (0 : ℝ) < ((cellOf c x k).ncard : ℝ) := by nlinarith
  -- the count that makes `X̄` not complete
  have hlt : {u : ↥s | c x u = k ∧ c u y = midJ c x k}.ncard < (cellOf c x k).ncard := by
    have hsub : {u : ↥s | c x u = k ∧ c u y = midJ c x k} ⊆
        {u : ↥s | c u y = midJ c x k} := fun u hu => hu.2
    have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [ncard_inNbr_eq_cell hc x y (midJ c x k)] at h1
    exact lt_of_le_of_lt h1 (cell_ncard_lt_bigCell hc hβ hk hjk' hjd')
  have hV₁ : (bipGraph c x k (midI c x k) (midJ c x k)).V₁.ncard = (cellOf c x k).ncard :=
    ncard_bipGraph_V₁ c x k _ _
  have hV₂ : (bipGraph c x k (midI c x k) (midJ c x k)).V₂.ncard
      = (cellOf c x (midI c x k)).ncard := ncard_bipGraph_V₂ hik'
  have hα : bipAlpha β c x k * ((cellOf c x k).ncard : ℝ) = β * (s.ncard : ℝ) := by
    rw [bipAlpha, div_mul_cancel₀ _ (ne_of_gt hdpos)]
  refine ⟨hik', bipGraph_isSemiregular hc hik',
    bipGraph_not_isTrivial hik' hz hyi hzyj hlt, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hV₁]; exact two_le_bigCell hc hβ hk
  · rw [hV₂, hV₁, hα]
    have h1 := cell_ncard_lt_of_ne hc hβ hk hik' hid'
    nlinarith
  · rw [hV₁]; linarith
  · rw [bipAlpha, le_div_iff₀ hdpos]
    have hle : ((cellOf c x k).ncard : ℝ) ≤ (s.ncard : ℝ) := by
      have := Set.ncard_le_ncard (Set.subset_univ (cellOf c x k)) (Set.toFinite _)
      rw [Set.ncard_univ, Nat.card_coe_set_eq] at this
      exact_mod_cast this
    nlinarith
  · rw [bipAlpha, div_lt_one hdpos]; exact hk
  · rw [hV₁]; exact hα

/-! ### Transport along an isomorphism of colorings

Condition (ii) of Definition 6.0.1 for the family of outcomes: an isomorphism `f` of two
UPCC colorings carries the outcome attached to `x` to the outcome attached to `f x`.  Every
ingredient of the construction is a formula in the coloring and in `x`, so it is enough to
transport those formulas; this section does that, first for the color labels. -/

variable {t : Set Ω}

/-- An isomorphism carries the cells of `x` to the cells of `f x`. -/
theorem cellOf_map {c : ↥s → ↥s → ℕ} {d : ↥t → ↥t → ℕ} (f : ↥s ≃ ↥t)
    (hf : ∀ u v, d (f u) (f v) = c u v) (x : ↥s) (k : ℕ) :
    cellOf d (f x) k = f '' cellOf c x k := by
  ext y
  constructor
  · intro hy
    refine ⟨f.symm y, ?_, Equiv.apply_symm_apply f y⟩
    have := hf x (f.symm y)
    rw [Equiv.apply_symm_apply] at this
    rw [mem_cellOf, ← this]
    exact hy
  · rintro ⟨u, hu, rfl⟩
    rw [mem_cellOf, hf x u]
    exact hu

theorem ncard_cellOf_map {c : ↥s → ↥s → ℕ} {d : ↥t → ↥t → ℕ} (f : ↥s ≃ ↥t)
    (hf : ∀ u v, d (f u) (f v) = c u v) (x : ↥s) (k : ℕ) :
    (cellOf d (f x) k).ncard = (cellOf c x k).ncard := by
  rw [cellOf_map f hf x k, Set.ncard_image_of_injective _ f.injective]

theorem ncard_eq_of_equiv (f : ↥s ≃ ↥t) : s.ncard = t.ncard := by
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
  exact Nat.card_eq_of_bijective f f.bijective

/-- The color of the big cell is a label, so it is the same on both sides. -/
theorem bigCellIdx_map {c : ↥s → ↥s → ℕ} {d : ↥t → ↥t → ℕ} {β : ℝ} (hβ : 1 / 2 ≤ β)
    (f : ↥s ≃ ↥t) (hf : ∀ u v, d (f u) (f v) = c u v) (x : ↥s)
    (h : ∃ k : ℕ, β * (s.ncard : ℝ) < ((cellOf c x k).ncard : ℝ)) :
    bigCellIdx β d (f x) = bigCellIdx β c x := by
  obtain ⟨k, hk⟩ := h
  have hk' : β * (t.ncard : ℝ) < ((cellOf d (f x) k).ncard : ℝ) := by
    rw [ncard_cellOf_map f hf x k, ← ncard_eq_of_equiv f]
    exact hk
  rw [bigCellIdx_eq hβ hk', bigCellIdx_eq hβ hk]

/-- The existential that splits the two cases of the construction is invariant. -/
theorem bigCell_exists_map {c : ↥s → ↥s → ℕ} {d : ↥t → ↥t → ℕ} {β : ℝ} (f : ↥s ≃ ↥t)
    (hf : ∀ u v, d (f u) (f v) = c u v) (x : ↥s) :
    (∃ k : ℕ, β * (t.ncard : ℝ) < ((cellOf d (f x) k).ncard : ℝ))
      ↔ ∃ k : ℕ, β * (s.ncard : ℝ) < ((cellOf c x k).ncard : ℝ) := by
  constructor <;> rintro ⟨k, hk⟩ <;> refine ⟨k, ?_⟩
  · rw [ncard_cellOf_map f hf x k, ← ncard_eq_of_equiv f] at hk; exact hk
  · rw [ncard_cellOf_map f hf x k, ← ncard_eq_of_equiv f]; exact hk

theorem midPair_map {c : ↥s → ↥s → ℕ} {d : ↥t → ↥t → ℕ} (f : ↥s ≃ ↥t)
    (hf : ∀ u v, d (f u) (f v) = c u v) (x : ↥s) (k m : ℕ)
    (h : MidPair c x k m) : MidPair d (f x) k m := by
  obtain ⟨z, y, h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨f z, f y, by rw [hf]; exact h1, by rw [hf]; exact h2, by rw [hf]; exact h3,
    by rw [hf]; exact h4, h5, by rw [hf]; exact h6, h7⟩

/-- The two colors of the diameter-2 step are labels, so they are the same on both
sides. -/
theorem midIdx_map {c : ↥s → ↥s → ℕ} {d : ↥t → ↥t → ℕ} (f : ↥s ≃ ↥t)
    (hf : ∀ u v, d (f u) (f v) = c u v) (x : ↥s) (k : ℕ) :
    midIdx d (f x) k = midIdx c x k := by
  classical
  have hf' : ∀ u v, c (f.symm u) (f.symm v) = d u v := by
    intro u v
    have := hf (f.symm u) (f.symm v)
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at this
    exact this.symm
  have hiff : ∀ m, MidPair d (f x) k m ↔ MidPair c x k m := by
    intro m
    refine ⟨fun hm => ?_, midPair_map f hf x k m⟩
    have := midPair_map f.symm hf' (f x) k m hm
    rwa [Equiv.symm_apply_apply] at this
  by_cases h : ∃ m, MidPair c x k m
  · have h' : ∃ m, MidPair d (f x) k m := by
      obtain ⟨m, hm⟩ := h; exact ⟨m, (hiff m).2 hm⟩
    rw [midIdx, dif_pos h', midIdx, dif_pos h]
    refine le_antisymm (Nat.find_min' h' ((hiff _).2 (Nat.find_spec h)))
      (Nat.find_min' h ((hiff _).1 (Nat.find_spec h')))
  · have h' : ¬ ∃ m, MidPair d (f x) k m := by
      rintro ⟨m, hm⟩; exact h ⟨m, (hiff m).1 hm⟩
    rw [midIdx, dif_neg h', midIdx, dif_neg h]

theorem midI_map {c : ↥s → ↥s → ℕ} {d : ↥t → ↥t → ℕ} (f : ↥s ≃ ↥t)
    (hf : ∀ u v, d (f u) (f v) = c u v) (x : ↥s) (k : ℕ) :
    midI d (f x) k = midI c x k := by rw [midI, midI, midIdx_map f hf]

theorem midJ_map {c : ↥s → ↥s → ℕ} {d : ↥t → ↥t → ℕ} (f : ↥s ≃ ↥t)
    (hf : ∀ u v, d (f u) (f v) = c u v) (x : ↥s) (k : ℕ) :
    midJ d (f x) k = midJ c x k := by rw [midJ, midJ, midIdx_map f hf]

/-- The threshold parameter `α = βn/d₂` is the same on both sides. -/
theorem bipAlpha_map {c : ↥s → ↥s → ℕ} {d : ↥t → ↥t → ℕ} {β : ℝ} (f : ↥s ≃ ↥t)
    (hf : ∀ u v, d (f u) (f v) = c u v) (x : ↥s) (k : ℕ) :
    bipAlpha β d (f x) k = bipAlpha β c x k := by
  rw [bipAlpha, bipAlpha, ncard_cellOf_map f hf x k, ncard_eq_of_equiv f]

/-- The bijection of the vertex sets of the two copies of `X̄` induced by an isomorphism
of the two colorings. -/
def bipEquiv {c : ↥s → ↥s → ℕ} {d : ↥t → ↥t → ℕ} (f : ↥s ≃ ↥t)
    (hf : ∀ u v, d (f u) (f v) = c u v) (x : ↥s) (k i : ℕ) :
    ↥(bipCarrier c x k i) ≃ ↥(bipCarrier d (f x) k i) where
  toFun w := ⟨(f (bipIota w) : Ω), by
    refine ⟨f (bipIota w), ?_, rfl⟩
    rcases bipIota_mem w with hw | hw
    · exact Or.inl (by rw [cellOf_map f hf x k]; exact ⟨_, hw, rfl⟩)
    · exact Or.inr (by rw [cellOf_map f hf x i]; exact ⟨_, hw, rfl⟩)⟩
  invFun w := ⟨(f.symm (bipIota w) : Ω), by
    refine ⟨f.symm (bipIota w), ?_, rfl⟩
    rcases bipIota_mem w with hw | hw
    · rw [cellOf_map f hf x k] at hw
      obtain ⟨u, hu, hu'⟩ := hw
      exact Or.inl (by rw [← hu', Equiv.symm_apply_apply]; exact hu)
    · rw [cellOf_map f hf x i] at hw
      obtain ⟨u, hu, hu'⟩ := hw
      exact Or.inr (by rw [← hu', Equiv.symm_apply_apply]; exact hu)⟩
  left_inv w := by
    refine Subtype.ext ?_
    show ((f.symm (f (bipIota w)) : ↥s) : Ω) = ((w : Ω))
    rw [Equiv.symm_apply_apply]
    rfl
  right_inv w := by
    refine Subtype.ext ?_
    show ((f (f.symm (bipIota w)) : ↥t) : Ω) = ((w : Ω))
    rw [Equiv.apply_symm_apply]
    rfl

theorem bipIota_bipEquiv {c : ↥s → ↥s → ℕ} {d : ↥t → ↥t → ℕ} (f : ↥s ≃ ↥t)
    (hf : ∀ u v, d (f u) (f v) = c u v) (x : ↥s) (k i : ℕ)
    (w : ↥(bipCarrier c x k i)) : bipIota (bipEquiv f hf x k i w) = f (bipIota w) := rfl

/-- The induced bijection is an isomorphism of the two copies of `X̄` (Def. 2.3.4 for
vertex-colored bipartite graphs). -/
theorem bipEquiv_mem_iso {c : ↥s → ↥s → ℕ} {d : ↥t → ↥t → ℕ} (f : ↥s ≃ ↥t)
    (hf : ∀ u v, d (f u) (f v) = c u v) (x : ↥s) (k i j : ℕ) :
    bipEquiv f hf x k i ∈ (VColBipGraphs Ω ℕ).Iso (bipGraph c x k i j)
      (bipGraph d (f x) k i j) := by
  refine ⟨fun w => ?_, fun w y => ?_, fun w => ?_⟩
  · show d (f x) (f (bipIota w)) = k ↔ c x (bipIota w) = k
    rw [hf]
  · show (d (f x) (f (bipIota w)) = k ∧ d (f x) (f (bipIota y)) ≠ k ∧
      d (f (bipIota w)) (f (bipIota y)) = j) ↔ _
    rw [hf, hf, hf]
    exact Iff.rfl
  · show d (f x) (f (bipIota w)) = c x (bipIota w)
    rw [hf]

/-- The cells at `x` are the blocks of `cellPartition`, and an isomorphism carries the one
partition to the other. -/
theorem cellPartition_mem_iso {c : ↥s → ↥s → ℕ} {d : ↥t → ↥t → ℕ} (f : ↥s ≃ ↥t)
    (hf : ∀ u v, d (f u) (f v) = c u v) (x : ↥s) :
    f ∈ (ColoredPartitions Ω ℕ).Iso (cellPartition c x) (cellPartition d (f x)) := by
  refine ⟨fun y => ?_, fun y z => ?_⟩
  · show d (f x) (f y) = c x y
    rw [hf]
  · show c x y = c x z ↔ d (f x) (f y) = d (f x) (f z)
    rw [hf, hf]

end Babai
