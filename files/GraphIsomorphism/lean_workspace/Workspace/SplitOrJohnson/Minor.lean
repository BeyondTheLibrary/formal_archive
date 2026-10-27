/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 9.3: Minor subroutines (Lemma 9.3.1, Procedure Reduce-Part2-by-Color,
Lemma 9.3.2).
-/
import Workspace.SplitOrJohnson.Main
import Workspace.SplitOrJohnson.UpccToBip

/-!
# §9.3 Minor subroutines

Version 2.5, lines 4038–4090 of `babai-gi-source/quasi25.txt`.

| Paper | Lean |
|---|---|
| `X[V₁, C]` (Def. 2.4.25 for colored bipartite graphs) | `Babai.VColBip.restrict₂` |
| absolute symmetry defect of `V₁` (Def. 2.4.29) | `Babai.VColBip.symDefect₁` |
| Lemma 9.3.1 (UPCC-to-bipartite) | `Babai.lemma_9_3_1` |
| Lemma 9.3.1, transfer of the solutions | `Babai.lemma_9_3_1_transfer` |
| Procedure Reduce-Part2-by-Color | `Babai.reducePart2ByColor`, `.spec` |
| Lemma 9.3.2 | `Babai.lemma_9_3_2` |

## Modelling note on `X[V₁, C]`

The paper's `X_j = X[V₁, C_j]` deletes the vertices of `V₂ \ C_j`.  We keep the vertex set
and delete only the edges leaving `C_j`.  The two differ only by isolated vertices in the
second part, which changes neither the twins inside `V₁` nor the symmetry defect of `V₁`,
the only quantities the paper uses in §9.3.
-/

namespace Babai

/-! ### The induced colored bipartite subgraph on a subset of the second part -/

namespace VColBip

variable {s : Type} {κ : Type} (X : VColBip s κ)

/-- Definition 2.4.25 for colored bipartite graphs: the induced subgraph `X[V₁, C]`, whose
edges are the edges of `X` that end in `C`. -/
def restrict₂ (C : Set s) : VColBip s κ where
  part₁ := X.part₁
  E := {p | p ∈ X.E ∧ p.2 ∈ C}
  f := X.f
  E_sub p hp := X.E_sub p hp.1

@[simp] theorem restrict₂_part₁ (C : Set s) : (X.restrict₂ C).part₁ = X.part₁ := rfl

@[simp] theorem restrict₂_V₁ (C : Set s) : (X.restrict₂ C).V₁ = X.V₁ := rfl

/-- Definition 2.4.29.  *"`|Ωᵢ \ Tᵢ|` is the absolute symmetry defect of `Ωᵢ` in `X`."*
The case `i = 1`, as a rational number (`symmetricity₁ ≤ |V₁|`, so nothing is truncated). -/
noncomputable def symDefect₁ [Fintype s] [DecidableEq s] : ℚ := (X.V₁.ncard : ℚ) - (X.symmetricity₁ : ℚ)

variable {X}

open scoped Classical in
/-- A set of twins inside `V₁` is no larger than the symmetricity of `V₁`. -/
theorem card_le_symmetricity₁ [Fintype s] [DecidableEq s] {T : Finset s}
    (hT₁ : ∀ x ∈ T, X.part₁ x) (hT : IsTwinSet X.Aut (↑T : Set s)) :
    T.card ≤ X.symmetricity₁ := by
  refine Finset.le_sup (f := Finset.card) ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨hT₁, hT⟩

open scoped Classical in
/-- The symmetricity of `V₁` is attained by a set of twins inside `V₁`. -/
theorem exists_twinSet_card_eq_symmetricity₁ [Fintype s] [DecidableEq s] :
    ∃ T : Finset s, (∀ x ∈ T, X.part₁ x) ∧ IsTwinSet X.Aut (↑T : Set s) ∧
      T.card = X.symmetricity₁ := by
  have hne : (Finset.univ.filter fun T : Finset s =>
      (∀ x ∈ T, X.part₁ x) ∧ IsTwinSet X.Aut (↑T : Set s)).Nonempty := by
    refine ⟨∅, ?_⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨by simp, ?_⟩
    intro x hx
    simp at hx
  obtain ⟨T, hT, hsup⟩ := Finset.exists_mem_eq_sup _ hne Finset.card
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hT
  exact ⟨T, hT.1, hT.2, hsup.symm⟩

/-- An automorphism of both `X[V₁, C₁]` and `X[V₁, C₂]` is an automorphism of `X`, as soon
as `C₁ ∪ C₂` covers the second part.  (Every edge of `X` ends in `V₂`, hence is an edge of
one of the two induced subgraphs.)

This is the step *"all vertices in `D₁ ∩ D₂` are twins in `X`"* of the proof of
Lemma 9.3.2. -/
theorem aut_restrict₂_inf_le {C₁ C₂ : Set s} (hcov : X.V₂ ⊆ C₁ ∪ C₂) :
    (X.restrict₂ C₁).Aut ⊓ (X.restrict₂ C₂).Aut ≤ X.Aut := by
  have key : ∀ σ ∈ (X.restrict₂ C₁).Aut ⊓ (X.restrict₂ C₂).Aut, ∀ u v : s,
      (u, v) ∈ X.E → (σ u, σ v) ∈ X.E := by
    rintro σ ⟨⟨-, hE₁, -⟩, -, hE₂, -⟩ u v huv
    rcases hcov (X.E_sub _ huv).2 with hv | hv
    · exact ((hE₁ u v).2 ⟨huv, hv⟩).1
    · exact ((hE₂ u v).2 ⟨huv, hv⟩).1
  intro σ hσ
  obtain ⟨⟨hp, -, hf⟩, -⟩ := id hσ
  refine ⟨hp, fun x y => ⟨fun h => ?_, key σ hσ x y⟩, hf⟩
  have hinv := key σ⁻¹ (Subgroup.inv_mem _ hσ) (σ x) (σ y) h
  simpa using hinv

/-- Observation 2.4.28 for a vertex-colored bipartite graph: two vertices of the first part
with the same neighborhood and the same vertex color are twins.

Proof: the transposition `τ = (u,v)` preserves the two parts (`u`, `v` both lie in `V₁`),
fixes every vertex of the second part, and preserves the edges — an edge runs from the
first part to the second, so its head is fixed by `τ` and its tail is moved only between
`u` and `v`, which have equal neighborhoods.  The vertex colors are preserved because
`f(u) = f(v)`.

This is the step used in step 7 of Procedure Bipartite Split-or-Johnson (*"otherwise `V₁`
would be a twin equivalence class in `X₁₂`"*) and in §9.7 (*"This hypergraph has no multiple
edges because there are no twins in `V₁`"*). -/
theorem isTwinIn_of_nbhd_eq [DecidableEq s] {X : VColBip s κ} {u v : s}
    (hu : u ∈ X.V₁) (hv : v ∈ X.V₁) (huv : u ≠ v)
    (hnb : ∀ y : s, (u, y) ∈ X.E ↔ (v, y) ∈ X.E) (hf : X.f u = X.f v) :
    X.IsTwinIn u v := by
  have hswapV : ∀ x : s, X.part₁ (Equiv.swap u v x) ↔ X.part₁ x := by
    intro x
    rcases eq_or_ne x u with rfl | hxu
    · rw [Equiv.swap_apply_left]; exact ⟨fun _ => hu, fun _ => hv⟩
    · rcases eq_or_ne x v with rfl | hxv
      · rw [Equiv.swap_apply_right]; exact ⟨fun _ => hv, fun _ => hu⟩
      · rw [Equiv.swap_apply_of_ne_of_ne hxu hxv]
  have hfix : ∀ y : s, ¬ X.part₁ y → Equiv.swap u v y = y := fun y hy =>
    Equiv.swap_apply_of_ne_of_ne (fun h => hy (h ▸ hu)) (fun h => hy (h ▸ hv))
  have hE : ∀ x y : s, (Equiv.swap u v x, Equiv.swap u v y) ∈ X.E ↔ (x, y) ∈ X.E := by
    intro x y
    by_cases hy : X.part₁ y
    · constructor
      · intro h
        exact absurd ((hswapV y).2 hy) (X.E_sub _ h).2
      · intro h
        exact absurd hy (X.E_sub _ h).2
    · rw [hfix y hy]
      rcases eq_or_ne x u with rfl | hxu
      · rw [Equiv.swap_apply_left]; exact (hnb y).symm
      · rcases eq_or_ne x v with rfl | hxv
        · rw [Equiv.swap_apply_right]; exact hnb y
        · rw [Equiv.swap_apply_of_ne_of_ne hxu hxv]
  have hcol : ∀ x : s, X.f (Equiv.swap u v x) = X.f x := by
    intro x
    rcases eq_or_ne x u with rfl | hxu
    · rw [Equiv.swap_apply_left]; exact hf.symm
    · rcases eq_or_ne x v with rfl | hxv
      · rw [Equiv.swap_apply_right]; exact hf
      · rw [Equiv.swap_apply_of_ne_of_ne hxu hxv]
  exact ⟨huv, hswapV, hE, hcol⟩

/-! ### Proposition 2.4.30 for vertex-colored bipartite graphs

`Babai.BipGraph.defect_ge_half` proves Proposition 2.4.30 for a bipartite graph
`X = (A, B; E)` whose two parts are two *types*.  The bipartite graphs of §9 are
vertex-colored bipartite graphs on **one** vertex set (`Babai.VColBip`), because that is
the category in which Theorem 9.2.2 states its canonicity, and the symmetry defect that
Theorem 9.2.2 speaks about is `Babai.VColBip.defect₁`, taken with respect to
`Babai.VColBip.Aut`.  This section proves Proposition 2.4.30 in that form; it is what the
proof of Lemma 9.3.1 needs in order to hand `X̄` to Theorem 9.2.2.

The paper's proof is followed, with the passage to the bipartite complement inlined: a set
`T` of twins in `V₁` is contained in the neighborhood of any neighbour of one of its
points, and also in the non-neighborhood of any non-neighbour, so
`|T| ≤ min(d₂, |V₁| - d₂) ≤ |V₁|/2`. -/

/-- Twins in `V₁` have the same neighborhood: the transposition `(x,y)` fixes every vertex
of `V₂`, so it carries the edges at `x` to the edges at `y`.  (This is the direction of
Observation 2.4.28(b) that Proposition 2.4.30 uses; the converse is
`Babai.VColBip.isTwinIn_of_nbhd_eq` and needs the vertex colors to agree.) -/
theorem nbhd_eq_of_isTwin [DecidableEq s] {X : VColBip s κ} {x y : s}
    (hx : x ∈ X.V₁) (hy : y ∈ X.V₁) (h : IsTwin X.Aut x y) {z : s} (hz : z ∈ X.V₂) :
    ((x, z) ∈ X.E ↔ (y, z) ∈ X.E) := by
  obtain ⟨hne, hmem⟩ := h
  have hzx : z ≠ x := fun hzx => hz (hzx ▸ hx)
  have hzy : z ≠ y := fun hzy => hz (hzy ▸ hy)
  have hfz : Equiv.swap x y z = z := Equiv.swap_apply_of_ne_of_ne hzx hzy
  have hfx : Equiv.swap x y x = y := Equiv.swap_apply_left x y
  have := (hmem.2.1 x z)
  rw [hfx, hfz] at this
  exact this.symm

open scoped Classical in
/-- A set of twins in `V₁` lies inside the neighborhood of any neighbour of any of its
points, and inside the non-neighborhood of any non-neighbour. -/
theorem twinSet₁_subset [DecidableEq s] {X : VColBip s κ} {T : Finset s}
    (hT₁ : ∀ x ∈ T, X.part₁ x) (hT : IsTwinSet X.Aut (↑T : Set s)) {x : s} (hx : x ∈ T)
    {z : s} (hz : z ∈ X.V₂) :
    ((x, z) ∈ X.E → (↑T : Set s) ⊆ {w | (w, z) ∈ X.E}) ∧
      ((x, z) ∉ X.E → (↑T : Set s) ⊆ {w | w ∈ X.V₁ ∧ (w, z) ∉ X.E}) := by
  have key : ∀ w ∈ T, ((w, z) ∈ X.E ↔ (x, z) ∈ X.E) := by
    intro w hw
    rcases eq_or_ne w x with rfl | hne
    · exact Iff.rfl
    · exact nbhd_eq_of_isTwin (hT₁ w hw) (hT₁ x hx) (hT w (by simpa using hw) x
        (by simpa using hx) hne) hz
  refine ⟨fun hxz w hw => ?_, fun hxz w hw => ?_⟩
  · exact (key w (by simpa using hw)).2 hxz
  · exact ⟨hT₁ w (by simpa using hw), fun hc => hxz ((key w (by simpa using hw)).1 hc)⟩

open scoped Classical in
/-- Proposition 2.4.30 for a vertex-colored bipartite graph, in the integer form
`2 s₁ ≤ |V₁|`: *"The symmetry defect of each part of a nontrivial semiregular bipartite
graph is `≥ 1/2`."* -/
theorem two_mul_symmetricity₁_le [Fintype s] [DecidableEq s] {X : VColBip s κ}
    (hsr : X.IsSemiregular) (hnt : ¬ X.IsTrivial) :
    2 * X.symmetricity₁ ≤ X.V₁.ncard := by
  obtain ⟨⟨d₁, hd₁⟩, ⟨d₂, hd₂⟩⟩ := hsr
  rw [VColBip.IsTrivial, not_or] at hnt
  obtain ⟨hne, hncomp⟩ := hnt
  -- the out-neighborhood of a vertex of `V₁` lies in `V₂`
  have hnbhd_sub : ∀ w : s, {y | (w, y) ∈ X.E} ⊆ X.V₂ := fun w y hy => (X.E_sub _ hy).2
  -- the in-neighborhood of a vertex of `V₂` lies in `V₁`
  have hin_sub : ∀ z : s, {w | (w, z) ∈ X.E} ⊆ X.V₁ := fun z w hw => (X.E_sub _ hw).1
  -- `E ≠ ∅`: some vertex of `V₁` has a neighbour, so `d₁ > 0`
  have hdA : ∀ w ∈ X.V₁, ({y | (w, y) ∈ X.E}).ncard = d₁ := fun w hw => hd₁ w hw
  have hdB : ∀ z ∈ X.V₂, ({w | (w, z) ∈ X.E}).ncard = d₂ := fun z hz => hd₂ z hz
  have hd₁pos : 0 < d₁ := by
    obtain ⟨p, hp⟩ := Set.nonempty_iff_ne_empty.2 hne
    have hp₁ : p.1 ∈ X.V₁ := (X.E_sub _ hp).1
    have : 0 < ({y | (p.1, y) ∈ X.E}).ncard :=
      (Set.ncard_pos (Set.toFinite _)).2 ⟨p.2, hp⟩
    rwa [hdA p.1 hp₁] at this
  -- `E` is not complete: some vertex of `V₁` has a non-neighbour in `V₂`, so `d₁ < |V₂|`
  have hd₁lt : d₁ < X.V₂.ncard := by
    by_contra hcon
    push_neg at hcon
    refine hncomp (Set.Subset.antisymm (fun p hp => ⟨(X.E_sub _ hp).1, (X.E_sub _ hp).2⟩)
      fun p hp => ?_)
    have hp₁ : p.1 ∈ X.V₁ := hp.1
    have heq : {y | (p.1, y) ∈ X.E} = X.V₂ :=
      Set.eq_of_subset_of_ncard_le (hnbhd_sub p.1) (by rw [hdA p.1 hp₁]; exact hcon)
        (Set.toFinite _)
    have : p.2 ∈ {y | (p.1, y) ∈ X.E} := heq ▸ hp.2
    exact this
  -- every twin set inside `V₁` has at most `|V₁|/2` elements
  have hbound : ∀ T : Finset s, ((∀ x ∈ T, X.part₁ x) ∧ IsTwinSet X.Aut (↑T : Set s)) →
      2 * T.card ≤ X.V₁.ncard := by
    intro T hT
    obtain ⟨hT₁, hTt⟩ := hT
    rcases T.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
    · simp
    have hxV₁ : x ∈ X.V₁ := hT₁ x hx
    -- `|{w | (w,z) ∈ E}| = d₂` for every `z ∈ V₂`
    have hd₂card := hdB
    have hd₂le : d₂ ≤ X.V₁.ncard := by
      obtain ⟨z, hz⟩ : X.V₂.Nonempty := by
        rcases Set.eq_empty_or_nonempty X.V₂ with h0 | h; · rw [h0] at hd₁lt; simp at hd₁lt
        · exact h
      rw [← hd₂card z hz]
      exact Set.ncard_le_ncard (hin_sub z) (Set.toFinite _)
    by_cases hcase : 2 * d₂ ≤ X.V₁.ncard
    · -- use a neighbour of `x`
      obtain ⟨z, hz⟩ : ({y | (x, y) ∈ X.E}).Nonempty := by
        rw [← Set.ncard_pos (Set.toFinite _), hdA x hxV₁]; exact hd₁pos
      have hzV₂ : z ∈ X.V₂ := hnbhd_sub x hz
      have hsub := (twinSet₁_subset hT₁ hTt hx hzV₂).1 hz
      have : T.card ≤ d₂ := by
        rw [← hd₂card z hzV₂, ← Set.ncard_coe_finset]
        exact Set.ncard_le_ncard hsub (Set.toFinite _)
      omega
    · -- use a non-neighbour of `x`
      push_neg at hcase
      obtain ⟨z, hzV₂, hz⟩ : ∃ z ∈ X.V₂, (x, z) ∉ X.E := by
        by_contra hcon
        push_neg at hcon
        have : X.V₂ ⊆ {y | (x, y) ∈ X.E} := fun y hy => hcon y hy
        have hle := Set.ncard_le_ncard this (Set.toFinite _)
        rw [hdA x hxV₁] at hle
        omega
      have hsub := (twinSet₁_subset hT₁ hTt hx hzV₂).2 hz
      have hcompl : ({w | w ∈ X.V₁ ∧ (w, z) ∉ X.E}).ncard = X.V₁.ncard - d₂ := by
        have hd : {w | w ∈ X.V₁ ∧ (w, z) ∉ X.E} = X.V₁ \ {w | (w, z) ∈ X.E} := by
          ext w; exact Iff.rfl
        rw [hd, Set.ncard_diff (hin_sub z) (Set.toFinite _), hd₂card z hzV₂]
      have : T.card ≤ X.V₁.ncard - d₂ := by
        rw [← hcompl, ← Set.ncard_coe_finset]
        exact Set.ncard_le_ncard hsub (Set.toFinite _)
      omega
  have hs : X.symmetricity₁ ≤ X.V₁.ncard / 2 := by
    refine Finset.sup_le fun T hT => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hT
    have := hbound T hT
    omega
  omega

/-- Proposition 2.4.30 for a vertex-colored bipartite graph: *"The symmetry defect of each
part of a nontrivial semiregular bipartite graph is `≥ 1/2`."*  This is the form in which
the proof of Lemma 9.3.1 uses it (`X̄` is semiregular, non-empty and not complete, so its
relative symmetry defect on `C₂` is `≥ 1/2 ≥ 1 - α`). -/
theorem half_le_defect₁ [Fintype s] [DecidableEq s] {X : VColBip s κ}
    (hsr : X.IsSemiregular) (hnt : ¬ X.IsTrivial) : 1 / 2 ≤ X.defect₁ := by
  have h := two_mul_symmetricity₁_le hsr hnt
  rcases Nat.eq_zero_or_pos X.V₁.ncard with h0 | hpos
  · have hs : X.symmetricity₁ = 0 := by omega
    rw [VColBip.defect₁, hs, h0]
    norm_num
  · have hn : (0 : ℚ) < (X.V₁.ncard : ℚ) := by exact_mod_cast hpos
    have hle : (X.symmetricity₁ : ℚ) / (X.V₁.ncard : ℚ) ≤ 1 / 2 := by
      rw [div_le_iff₀ hn]
      have : (2 : ℚ) * (X.symmetricity₁ : ℚ) ≤ (X.V₁.ncard : ℚ) := by exact_mod_cast h
      linarith
    rw [VColBip.defect₁]
    linarith

end VColBip

/-! ### Proposition 2.4.30 for graphs whose second part is a family of blocks

Step 8 of §9.4 applies Proposition 2.4.30 to the graph `(V₁, V₂; R_i)`, whose second part
is the family of blocks that the recursion of §9.4-§9.8 carries
(`Workspace/SplitOrJohnson/BipBlocks.lean`).  Two points of `V₁` are twins of such a graph
exactly when they have the same color and the same set of neighboring blocks
(`Babai.VColBipBlk.isTwin_iff`), so the proof is the one above, with the vertices of `V₂`
replaced by the blocks. -/

namespace VColBipBlk

variable {s : Type} {κ : Type} [Zero κ]

/-- §2.4.2, for a graph whose second part is a family of blocks: *"We say that `X` is
semiregular if every vertex in `A` has the same degree and every vertex in `B` has the same
degree."*  The degree of a point of `V₁` is the number of blocks joined to it, the degree
of a block is the number of points of `V₁` joined to it. -/
def IsSemiregular (X : VColBipBlk s κ) : Prop :=
  (∃ d, ∀ x ∈ X.V₁, {B | (x, B) ∈ X.E}.ncard = d) ∧
    (∃ d, ∀ B ∈ X.blocks, {x | (x, B) ∈ X.E}.ncard = d)

/-- §2.4.2, for a graph whose second part is a family of blocks: *"The trivial bipartite
graphs are the empty (`E = ∅`) and complete (`E = A × B`) bipartite graphs."* -/
def IsTrivial (X : VColBipBlk s κ) : Prop :=
  X.E = ∅ ∨ X.E = {p | X.part₁ p.1 ∧ p.2 ∈ X.blocks}

/-- Twins in `V₁` are joined to the same blocks.  This is the direction of
Observation 2.4.28(b) that Proposition 2.4.30 uses; it is one half of
`Babai.VColBipBlk.isTwin_iff`. -/
theorem nbhd_eq_of_isTwin [DecidableEq s] {X : VColBipBlk s κ} {x y : s} (hx : X.part₁ x)
    (hy : X.part₁ y) (h : IsTwin X.Aut x y) {B : Set s} (hB : B ∈ X.blocks) :
    ((x, B) ∈ X.E ↔ (y, B) ∈ X.E) :=
  ((X.isTwin_iff hx hy h.1).1 h).2 B hB

open scoped Classical in
/-- A set of twins in `V₁` lies inside the set of points joined to any block joined to one
of its points, and inside the set of points not joined to any block not joined to it. -/
theorem twinSet₁_subset [DecidableEq s] {X : VColBipBlk s κ} {T : Finset s}
    (hT₁ : ∀ x ∈ T, X.part₁ x) (hT : IsTwinSet X.Aut (↑T : Set s)) {x : s} (hx : x ∈ T)
    {B : Set s} (hB : B ∈ X.blocks) :
    ((x, B) ∈ X.E → (↑T : Set s) ⊆ {w | (w, B) ∈ X.E}) ∧
      ((x, B) ∉ X.E → (↑T : Set s) ⊆ {w | X.part₁ w ∧ (w, B) ∉ X.E}) := by
  have key : ∀ w ∈ T, ((w, B) ∈ X.E ↔ (x, B) ∈ X.E) := by
    intro w hw
    rcases eq_or_ne w x with rfl | hne
    · exact Iff.rfl
    · exact nbhd_eq_of_isTwin (hT₁ w hw) (hT₁ x hx)
        (hT w (by simpa using hw) x (by simpa using hx) hne) hB
  refine ⟨fun hxB w hw => ?_, fun hxB w hw => ?_⟩
  · exact (key w (by simpa using hw)).2 hxB
  · exact ⟨hT₁ w (by simpa using hw), fun hc => hxB ((key w (by simpa using hw)).1 hc)⟩

open scoped Classical in
/-- Proposition 2.4.30 for a graph whose second part is a family of blocks, in the integer
form `2 s₁ ≤ |V₁|`: *"The symmetry defect of each part of a nontrivial semiregular
bipartite graph is `≥ 1/2`."*

The proof is the one of `Babai.VColBip.two_mul_symmetricity₁_le`: a set `T` of twins in
`V₁` is contained in the set of points joined to any block joined to one of its points, and
also in the set of points not joined to any block not joined to it, so
`|T| ≤ min(d₂, |V₁| - d₂) ≤ |V₁|/2`. -/
theorem two_mul_symmetricity₁_le [Fintype s] [DecidableEq s] {X : VColBipBlk s κ}
    (hsr : X.IsSemiregular) (hnt : ¬ X.IsTrivial) :
    2 * X.symmetricity₁ ≤ X.V₁.ncard := by
  obtain ⟨⟨d₁, hd₁⟩, ⟨d₂, hd₂⟩⟩ := hsr
  rw [VColBipBlk.IsTrivial, not_or] at hnt
  obtain ⟨hne, hncomp⟩ := hnt
  have hnbhd_sub : ∀ w : s, {B | (w, B) ∈ X.E} ⊆ X.blocks := fun w B hB => (X.E_sub _ hB).2
  have hin_sub : ∀ B : Set s, {w | (w, B) ∈ X.E} ⊆ X.V₁ := fun B w hw => (X.E_sub _ hw).1
  -- `E ≠ ∅`: some point of `V₁` is joined to a block, so `d₁ > 0`
  have hd₁pos : 0 < d₁ := by
    obtain ⟨p, hp⟩ := Set.nonempty_iff_ne_empty.2 hne
    have hp₁ : p.1 ∈ X.V₁ := (X.E_sub _ hp).1
    have : 0 < ({B | (p.1, B) ∈ X.E}).ncard := (Set.ncard_pos (Set.toFinite _)).2 ⟨p.2, hp⟩
    rwa [hd₁ p.1 hp₁] at this
  -- `E` is not complete: some point of `V₁` misses a block, so `d₁ < n₂`
  have hd₁lt : d₁ < X.blocks.ncard := by
    by_contra hcon
    push_neg at hcon
    refine hncomp (Set.Subset.antisymm (fun p hp => ⟨(X.E_sub _ hp).1, (X.E_sub _ hp).2⟩)
      fun p hp => ?_)
    have hp₁ : p.1 ∈ X.V₁ := hp.1
    have heq : {B | (p.1, B) ∈ X.E} = X.blocks :=
      Set.eq_of_subset_of_ncard_le (hnbhd_sub p.1) (by rw [hd₁ p.1 hp₁]; exact hcon)
        (Set.toFinite _)
    have : p.2 ∈ {B | (p.1, B) ∈ X.E} := heq ▸ hp.2
    exact this
  -- every twin set inside `V₁` has at most `|V₁|/2` elements
  have hbound : ∀ T : Finset s, ((∀ x ∈ T, X.part₁ x) ∧ IsTwinSet X.Aut (↑T : Set s)) →
      2 * T.card ≤ X.V₁.ncard := by
    intro T hT
    obtain ⟨hT₁, hTt⟩ := hT
    rcases T.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
    · simp
    have hxV₁ : x ∈ X.V₁ := hT₁ x hx
    have hd₂le : d₂ ≤ X.V₁.ncard := by
      obtain ⟨B, hB⟩ : X.blocks.Nonempty := by
        rcases Set.eq_empty_or_nonempty X.blocks with h0 | h
        · rw [h0] at hd₁lt; simp at hd₁lt
        · exact h
      rw [← hd₂ B hB]
      exact Set.ncard_le_ncard (hin_sub B) (Set.toFinite _)
    by_cases hcase : 2 * d₂ ≤ X.V₁.ncard
    · -- use a block joined to `x`
      obtain ⟨B, hB⟩ : ({B | (x, B) ∈ X.E}).Nonempty := by
        rw [← Set.ncard_pos (Set.toFinite _), hd₁ x hxV₁]; exact hd₁pos
      have hBblk : B ∈ X.blocks := hnbhd_sub x hB
      have hsub := (twinSet₁_subset hT₁ hTt hx hBblk).1 hB
      have : T.card ≤ d₂ := by
        rw [← hd₂ B hBblk, ← Set.ncard_coe_finset]
        exact Set.ncard_le_ncard hsub (Set.toFinite _)
      omega
    · -- use a block not joined to `x`
      push_neg at hcase
      obtain ⟨B, hBblk, hB⟩ : ∃ B ∈ X.blocks, (x, B) ∉ X.E := by
        by_contra hcon
        push_neg at hcon
        have hsub : X.blocks ⊆ {B | (x, B) ∈ X.E} := fun B hB => hcon B hB
        have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
        rw [hd₁ x hxV₁] at hle
        omega
      have hsub := (twinSet₁_subset hT₁ hTt hx hBblk).2 hB
      have hcompl : ({w | X.part₁ w ∧ (w, B) ∉ X.E}).ncard = X.V₁.ncard - d₂ := by
        have hd : {w | X.part₁ w ∧ (w, B) ∉ X.E} = X.V₁ \ {w | (w, B) ∈ X.E} := by
          ext w; exact Iff.rfl
        rw [hd, Set.ncard_diff (hin_sub B) (Set.toFinite _), hd₂ B hBblk]
      have : T.card ≤ X.V₁.ncard - d₂ := by
        rw [← hcompl, ← Set.ncard_coe_finset]
        exact Set.ncard_le_ncard hsub (Set.toFinite _)
      omega
  have hs : X.symmetricity₁ ≤ X.V₁.ncard / 2 := by
    refine Finset.sup_le fun T hT => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hT
    have := hbound T hT
    omega
  omega

/-- Proposition 2.4.30 for a graph whose second part is a family of blocks: *"The symmetry
defect of each part of a nontrivial semiregular bipartite graph is `≥ 1/2`."*  This is the
form step 8 of §9.4 uses: *"`X` is semiregular, nontrivial; therefore its symmetry defect
is `≥ 1/2` in each part by Prop. 2.4.30"*. -/
theorem half_le_defect₁ [Fintype s] [DecidableEq s] {X : VColBipBlk s κ}
    (hsr : X.IsSemiregular) (hnt : ¬ X.IsTrivial) : 1 / 2 ≤ X.defect₁ := by
  have h := two_mul_symmetricity₁_le hsr hnt
  rcases Nat.eq_zero_or_pos X.V₁.ncard with h0 | hpos
  · have hs : X.symmetricity₁ = 0 := by omega
    rw [VColBipBlk.defect₁, hs, h0]
    norm_num
  · have hn : (0 : ℚ) < (X.V₁.ncard : ℚ) := by exact_mod_cast hpos
    have hle : (X.symmetricity₁ : ℚ) / (X.V₁.ncard : ℚ) ≤ 1 / 2 := by
      rw [div_le_iff₀ hn]
      have : (2 : ℚ) * (X.symmetricity₁ : ℚ) ≤ (X.V₁.ncard : ℚ) := by exact_mod_cast h
      linarith
    rw [VColBipBlk.defect₁]
    linarith

end VColBipBlk

/-! ### Procedure Reduce-Part2-by-Color and Lemma 9.3.2 -/

variable {s : Type} [Fintype s] [DecidableEq s] {κ : Type}

/-- Lemma 9.3.2.  *"In at least one of `X₁` and `X₂`, the symmetry defect of `V₁` is at
least `(n₁ - 1)/2`."*  (Version 2.5, lines 4085–4090.)

Here `X_j = X[V₁, C_j]` for a partition `V₂ = C₁ ∪ C₂`, and `X` has no twins in `V₁`,
as in the input of Procedure Reduce-Part2-by-Color.

Paper's proof: *"Assume for a contradiction that for `j = 1, 2` there exists a twin
equivalence class `D_j ⊆ V₁` of size `|D_j| ≥ 1 + (n₁/2)` in `X_j`.  It follows that
`|D₁ ∩ D₂| ≥ 2`.  On the other hand, all vertices in `D_j` are twins with respect to
`C_j`; therefore all vertices in `D₁ ∩ D₂` are twins in `X`.  Since `X` has no twins, we
infer `|D₁ ∩ D₂| ≤ 1`, a contradiction."* -/
theorem lemma_9_3_2 (X : VColBip s κ)
    (hno : ∀ x ∈ X.V₁, ∀ y ∈ X.V₁, ¬ X.IsTwinIn x y)
    {C₁ C₂ : Set s} (hcov : X.V₂ ⊆ C₁ ∪ C₂) :
    ((X.V₁.ncard : ℚ) - 1) / 2 ≤ (X.restrict₂ C₁).symDefect₁ ∨
      ((X.V₁.ncard : ℚ) - 1) / 2 ≤ (X.restrict₂ C₂).symDefect₁ := by
  classical
  by_contra hcon
  push_neg at hcon
  obtain ⟨h₁, h₂⟩ := hcon
  set n₁ := X.V₁.ncard with hn₁
  -- the two symmetricities are large: `n₁ + 1 < 2 sⱼ`
  have hbig : ∀ C : Set s, (X.restrict₂ C).symDefect₁ < ((n₁ : ℚ) - 1) / 2 →
      (n₁ : ℚ) + 1 < 2 * ((X.restrict₂ C).symmetricity₁ : ℚ) := by
    intro C hC
    have : (X.restrict₂ C).V₁.ncard = n₁ := by rw [hn₁, VColBip.restrict₂_V₁]
    rw [VColBip.symDefect₁, this] at hC
    linarith
  have hb₁ := hbig C₁ h₁
  have hb₂ := hbig C₂ h₂
  -- realize the symmetricities by sets of twins
  obtain ⟨D₁, hD₁p, hD₁t, hD₁c⟩ :=
    VColBip.exists_twinSet_card_eq_symmetricity₁ (X := X.restrict₂ C₁)
  obtain ⟨D₂, hD₂p, hD₂t, hD₂c⟩ :=
    VColBip.exists_twinSet_card_eq_symmetricity₁ (X := X.restrict₂ C₂)
  -- both live inside `V₁`, whose size is `n₁`
  set V : Finset s := Finset.univ.filter fun x => X.part₁ x with hV
  have hVcard : V.card = n₁ := by
    rw [hn₁]
    have : X.V₁ = (↑V : Set s) := by
      ext x; simp [hV, VColBip.V₁]
    rw [this, Set.ncard_coe_finset]
  have hsub₁ : D₁ ⊆ V := by
    intro x hx
    simp only [hV, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hD₁p x hx
  have hsub₂ : D₂ ⊆ V := by
    intro x hx
    simp only [hV, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hD₂p x hx
  -- `|D₁ ∩ D₂| ≥ 2`
  have hcard : n₁ + 2 ≤ D₁.card + D₂.card := by
    have e₁ : (n₁ : ℚ) + 1 < 2 * (D₁.card : ℚ) := by rw [hD₁c]; exact hb₁
    have e₂ : (n₁ : ℚ) + 1 < 2 * (D₂.card : ℚ) := by rw [hD₂c]; exact hb₂
    have : (n₁ : ℚ) + 1 < (D₁.card : ℚ) + D₂.card := by linarith
    exact_mod_cast this
  have hunion : (D₁ ∪ D₂).card ≤ n₁ := by
    rw [← hVcard]
    exact Finset.card_le_card (Finset.union_subset hsub₁ hsub₂)
  have hinter : 2 ≤ (D₁ ∩ D₂).card := by
    have := Finset.card_union_add_card_inter D₁ D₂
    omega
  -- pick two distinct vertices in the intersection; they are twins in `X`
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.1 hinter
  have hxV₁ : x ∈ X.V₁ := hD₁p x (Finset.mem_inter.1 hx).1
  have hyV₁ : y ∈ X.V₁ := hD₁p y (Finset.mem_inter.1 hy).1
  have ht₁ := hD₁t x (Finset.mem_inter.1 hx).1 y (Finset.mem_inter.1 hy).1 hxy
  have ht₂ := hD₂t x (Finset.mem_inter.1 hx).2 y (Finset.mem_inter.1 hy).2 hxy
  refine hno x hxV₁ y hyV₁ ⟨hxy, ?_⟩
  exact VColBip.aut_restrict₂_inf_le hcov ⟨ht₁.2, ht₂.2⟩

/-- Procedure Reduce-Part2-by-Color.  (Version 2.5, lines 4076–4084.)

> *Input:*  A colored bipartite graph `X = (V₁, V₂; E, f)` where `|V₂| < α|V₁|` such that
> there are no twins in `V₁`; a partition `V₂ = C₁ ∪ C₂` where each `C_j` is a union of
> color classes.
> *Output:* `j ∈ {1,2}` such that in the induced colored bipartite subgraph
> `X_j = X[V₁, C_j]` the symmetry defect of `V₁` is `≥ (n₁ - 1)/2` where `n₁ = |V₁|`.
> *"The procedure computes the symmetry defect of `V₁` in each `X_j`."*

The procedure is a function: it returns the part `C_j` selected (this is how the callers in
§9.7 and §9.8 use it — "if `V₂ \ C` is selected …").  It is total: the two hypotheses of
the input specification enter only in `reducePart2ByColor_spec`, which is Lemma 9.3.2.
The condition "each `C_j` is a union of color classes" is not used by the output condition;
it is what makes the selected part canonical. -/
noncomputable def reducePart2ByColor (X : VColBip s κ) (C₁ C₂ : Set s) : Set s :=
  if ((X.V₁.ncard : ℚ) - 1) / 2 ≤ (X.restrict₂ C₁).symDefect₁ then C₁ else C₂

/-- Procedure Reduce-Part2-by-Color: the output condition, by Lemma 9.3.2. -/
theorem reducePart2ByColor_spec (X : VColBip s κ)
    (hno : ∀ x ∈ X.V₁, ∀ y ∈ X.V₁, ¬ X.IsTwinIn x y)
    {C₁ C₂ : Set s} (hcov : X.V₂ ⊆ C₁ ∪ C₂) :
    ((X.V₁.ncard : ℚ) - 1) / 2 ≤
      (X.restrict₂ (reducePart2ByColor X C₁ C₂)).symDefect₁ := by
  unfold reducePart2ByColor
  split_ifs with h
  · exact h
  · exact (lemma_9_3_2 X hno hcov).resolve_left h

/-- Procedure Reduce-Part2-by-Color returns one of the two parts. -/
theorem reducePart2ByColor_mem (X : VColBip s κ) (C₁ C₂ : Set s) :
    reducePart2ByColor X C₁ C₂ = C₁ ∨ reducePart2ByColor X C₁ C₂ = C₂ := by
  unfold reducePart2ByColor; split_ifs with h
  · exact Or.inl rfl
  · exact Or.inr rfl

/-! ### Lemma 9.3.1 (UPCC-to-bipartite) -/

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

/-- The outcome of Lemma 9.3.1 for the threshold parameter `β`: either objective (a) of
Theorem 9.2.1 (*"a canonical colored `β`-partition of `V`"*), or a *"(relative) canonically
embedded semiregular bipartite graph `X̄ = (V₁, V₂; E)` with `V₁ ∪ V₂ ⊆ V` and
`|V₁| ≥ βn`"* which is an admissible input of Theorem 9.2.2 for some threshold parameter
`α ≥ 2/3`, *"such that a solution to each part of Theorem 9.2.2 for `X̄` is also a solution
to the corresponding part of Theorem 9.2.1 for `X`"*.

The last clause is `α ≤ 1` together with `α|V₁| = βn`, which are exactly the hypotheses
under which `lemma_9_3_1_transfer` carries a solution over.  The paper's construction has
`α = βn/d₂` with `|V₁| = d₂`, i.e. `α|V₁| = βn` on the nose, and **equality is needed**:
outcome (b) for `X̄` gives a subset of size `≥ α|V₁|` and needs `α|V₁| ≥ βn`, while
outcome (a) for `X̄` gives blocks of size `≤ α|V₁|` and needs `α|V₁| ≤ βn`.

*"a threshold parameter `α ≥ 2/3`"* and *"an instance of Theorem 9.2.2"* are the defining
conditions of the category `BipInputs Ω` of §9.2, whose objects carry `α` as data — which
is what lets `FindsAtMultCost.comp` chain this lemma with Theorem 9.2.2, since the `α`
produced here depends on the input object. -/
def IsUPCCToBipOutcome (β : ℝ) (X : Pt (UPCCs Ω))
    (Z : Pt (Cat.sum (ColoredPartitions Ω ℕ) (BipInputs Ω))) : Prop :=
  match Z.obj with
  | Sum.inl P => Z.car = X.car ∧ letI : Fintype ↥Z.car := Fintype.ofFinite _;
      P.IsAlphaPartition β
  | Sum.inr Y => Z.car ⊆ X.car ∧ Y.1.1.IsSemiregular ∧
      β * (X.car.ncard : ℝ) ≤ (Y.1.1.V₁.ncard : ℝ) ∧ Y.1.2 ≤ 1 ∧
        Y.1.2 * (Y.1.1.V₁.ncard : ℝ) = β * (X.car.ncard : ℝ)

/-- The conditions that make `X̄ = (C_k, Cᵢ; R_j)` with the threshold `α = βn/d_k` an
admissible input of Theorem 9.2.2, i.e. an object of `BipInputs Ω`. -/
def upccBipCond (β : ℝ) {s : Set Ω} (c : ↥s → ↥s → ℕ) (x : ↥s) (k i j : ℕ) : Prop :=
  letI : Fintype ↥(bipCarrier c x k i) := Fintype.ofFinite _
  letI : DecidableEq ↥(bipCarrier c x k i) := Classical.decEq _
  2 / 3 ≤ bipAlpha β c x k ∧ bipAlpha β c x k < 1 ∧
    (bipGraph c x k i j).IsThm922Input (bipAlpha β c x k)

open scoped Classical in
/-- The second outcome of Lemma 9.3.1: the bipartite graph `X̄ = (C_k, Cᵢ; R_j)` with its
threshold parameter, as an object of `BipInputs Ω` on a subset of `V`.

The three colors are plain arguments, and the conditions are checked inside, so that this
is a function `ℕ → ℕ → ℕ → …` whose value type does not depend on them.  That is what lets
the transport lemma `upccOutcome_iso` rewrite the colors. -/
noncomputable def upccBipOutcome (β : ℝ) {s : Set Ω} (c : ↥s → ↥s → ℕ) (x : ↥s)
    (k i j : ℕ) : (Cat.sub (Cat.sum (ColoredPartitions Ω ℕ) (BipInputs Ω))).Obj s :=
  if h : upccBipCond β c x k i j then
    ⟨⟨bipCarrier c x k i, bipCarrier_subset _ _ _ _⟩,
      Sum.inr ⟨(bipGraph c x k i j, bipAlpha β c x k), h⟩⟩
  else ⟨⟨s, subset_rfl⟩, Sum.inl (cellPartition c x)⟩

/-- In the case `d_k > βn` of the proof of Lemma 9.3.1 the bipartite graph built from the
three canonically chosen colors is an admissible input of Theorem 9.2.2. -/
theorem upccBipCond_of {β : ℝ} (hβ : 2 / 3 ≤ β) {s : Set Ω} {c : ↥s → ↥s → ℕ}
    (hc : IsUPCCColoring c) {x : ↥s}
    (h : ∃ k : ℕ, β * (s.ncard : ℝ) < ((cellOf c x k).ncard : ℝ)) :
    upccBipCond β c x (bigCellIdx β c x) (midI c x (bigCellIdx β c x))
      (midJ c x (bigCellIdx β c x)) := by
  obtain ⟨hik, hsr, hnt, h2, hlt2, hge, hαβ, hα1, hαe⟩ :=
    bipCase hc hβ (bigCellIdx_spec h)
  refine ⟨by linarith, hα1, h2, hlt2, ?_⟩
  have key : ∀ (iF : Fintype ↥(bipCarrier c x (bigCellIdx β c x)
        (midI c x (bigCellIdx β c x))))
      (iD : DecidableEq ↥(bipCarrier c x (bigCellIdx β c x)
        (midI c x (bigCellIdx β c x)))),
      (1 : ℚ) / 2 ≤ @VColBip.defect₁ _ _ (bipGraph c x (bigCellIdx β c x)
          (midI c x (bigCellIdx β c x)) (midJ c x (bigCellIdx β c x))) iF iD :=
    fun iF iD => @VColBip.half_le_defect₁ _ _ iF iD _ hsr hnt
  have hle : (1 : ℝ) - bipAlpha β c x (bigCellIdx β c x) ≤ ((1 / 2 : ℚ) : ℝ) := by
    push_cast
    linarith
  exact hle.trans (Rat.cast_le.2 (key _ _))

open scoped Classical in
/-- The outcome of Lemma 9.3.1 attached to the individualized vertex `x`: the colored
`β`-partition of `V` into the cells of `x` if all cells are small, and the bipartite graph
`X̄ = (C₂, Cᵢ; R_j)` with its threshold parameter `α = βn/d₂` otherwise.

Everything is a formula in the coloring `c` and in `x`.  That is what makes the family of
outcomes equivariant (condition (ii) of Def. 6.0.1). -/
noncomputable def upccOutcome (β : ℝ) {s : Set Ω} (c : ↥s → ↥s → ℕ) (x : ↥s) :
    (Cat.sub (Cat.sum (ColoredPartitions Ω ℕ) (BipInputs Ω))).Obj s :=
  if _ : ∃ k : ℕ, β * (s.ncard : ℝ) < ((cellOf c x k).ncard : ℝ) then
    upccBipOutcome β c x (bigCellIdx β c x) (midI c x (bigCellIdx β c x))
      (midJ c x (bigCellIdx β c x))
  else ⟨⟨s, subset_rfl⟩, Sum.inl (cellPartition c x)⟩

/-- Every outcome of `upccOutcome` is a solution of Lemma 9.3.1: objective (a) of
Theorem 9.2.1 in the first case, and an admissible input of Theorem 9.2.2 with
`α·|V₁| = βn` in the second. -/
theorem upccOutcome_good (β : ℝ) (hβ : 2 / 3 ≤ β) (X : Pt (UPCCs Ω)) (x : ↥X.car) :
    IsUPCCToBipOutcome β X
      ⟨(upccOutcome β X.obj.1 x).1.1, (upccOutcome β X.obj.1 x).2⟩ := by
  classical
  unfold upccOutcome
  by_cases h : ∃ k : ℕ, β * (X.car.ncard : ℝ) < ((cellOf X.obj.1 x k).ncard : ℝ)
  · rw [dif_pos h]
    unfold upccBipOutcome
    rw [dif_pos (upccBipCond_of hβ X.obj.2 h)]
    obtain ⟨hik, hsr, hnt, h2, hlt2, hge, hαβ, hα1, hαe⟩ :=
      bipCase X.obj.2 hβ (bigCellIdx_spec h)
    exact ⟨bipCarrier_subset _ _ _ _, hsr, hge, le_of_lt hα1, hαe⟩
  · rw [dif_neg h]
    refine ⟨rfl, ?_⟩
    push_neg at h
    have key : ∀ iF : Fintype ↥X.car,
        @ColoredPartition.IsAlphaPartition _ _ (cellPartition X.obj.1 x) iF β := by
      intro iF
      refine cellPartition_isAlphaPartition (fun k => ?_)
      have hcard : (@Fintype.card ↥X.car iF : ℕ) = X.car.ncard := by
        rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
      rw [hcard]
      exact h k
    exact key _

/-- Condition (ii) of Definition 6.0.1 for the family of outcomes: an isomorphism of two
UPCC colorings carries the outcome attached to `x` to the outcome attached to `f x`. -/
theorem upccOutcome_iso (β : ℝ) (hβ : 2 / 3 ≤ β) {X Y : Pt (UPCCs Ω)}
    {f : ↥X.car ≃ ↥Y.car} (hf : f ∈ (UPCCs Ω).IsoP X Y) (x : ↥X.car) :
    f ∈ (Cat.sub (Cat.sum (ColoredPartitions Ω ℕ) (BipInputs Ω))).Iso
      (upccOutcome β X.obj.1 x) (upccOutcome β Y.obj.1 (f x)) := by
  classical
  have hf' : ∀ u v, Y.obj.1 (f u) (f v) = X.obj.1 u v := hf
  have hβ2 : (1 : ℝ) / 2 ≤ β := by linarith
  unfold upccOutcome
  by_cases h : ∃ k : ℕ, β * (X.car.ncard : ℝ) < ((cellOf X.obj.1 x k).ncard : ℝ)
  · have h' : ∃ k : ℕ, β * (Y.car.ncard : ℝ) < ((cellOf Y.obj.1 (f x) k).ncard : ℝ) :=
      (bigCell_exists_map f hf' x).2 h
    have hcondY := upccBipCond_of hβ Y.obj.2 h'
    have hcondX := upccBipCond_of hβ X.obj.2 h
    rw [midJ_map f hf' x _, midI_map f hf' x _, bigCellIdx_map hβ2 f hf' x h] at hcondY
    rw [dif_pos h, dif_pos h', bigCellIdx_map hβ2 f hf' x h, midI_map f hf' x _,
      midJ_map f hf' x _]
    unfold upccBipOutcome
    rw [dif_pos hcondX, dif_pos hcondY]
    exact ⟨bipEquiv f hf' x _ _, fun w => rfl,
      (bipAlpha_map f hf' x _).symm, bipEquiv_mem_iso f hf' x _ _ _⟩
  · have h' : ¬ ∃ k : ℕ, β * (Y.car.ncard : ℝ) < ((cellOf Y.obj.1 (f x) k).ncard : ℝ) :=
      fun hcon => h ((bigCell_exists_map f hf' x).1 hcon)
    rw [dif_neg h, dif_neg h']
    exact ⟨f, fun w => rfl, cellPartition_mem_iso f hf' x⟩

/-- Lemma 9.3.1 (UPCC-to-bipartite).  *"Let `X = (V; R)` be a UPCC with `n` vertices and
let `2/3 ≤ β ≤ 1` be a threshold parameter.  Then at a multiplicative cost of `≤ n` and
polynomial additive cost one can either (i) achieve objective (a) of Theorem 9.2.1, or
(ii) reduce the given instance of Theorem 9.2.1 to Theorem 9.2.2 by computing a threshold
parameter `α ≥ 2/3` and a (relative) canonically embedded semiregular bipartite graph
`X̄ = (V₁, V₂; E)` with `V₁ ∪ V₂ ⊆ V`, and `|V₁| ≥ βn` such that a solution to each part of
Theorem 9.2.2 for `X̄` is also a solution to the corresponding part of Theorem 9.2.1 for
`X`."*  (Version 2.5, lines 4044–4052.)

The multiplicative cost `≤ n` is the individualization of one vertex `x ∈ V` in the
paper's proof.  The last clause of (ii) — *"a solution … is also a solution …"* — is
`lemma_9_3_1_transfer`.  The additive polynomial cost is a running-time claim and is
pending. -/
theorem lemma_9_3_1 (β : ℝ) (hβ : 2 / 3 ≤ β) (hβ1 : β ≤ 1) :
    FindsAtMultCost (UPCCs Ω) (Cat.sum (ColoredPartitions Ω ℕ) (BipInputs Ω))
      (fun X => X.car.ncard) (fun X Z => IsUPCCToBipOutcome β X Z) := by
  -- The paper's proof: individualize one vertex `x ∈ V` (multiplicative cost `n`), which
  -- splits `V` into the relatively canonical subsets `Cᵢ = Rᵢ(x)`.  If `dᵢ ≤ βn` for all
  -- `i`, these are the blocks of a colored `β`-partition — objective (a).  Otherwise
  -- `d₂ > βn`, and `X̄ = (C₂, Cᵢ; (C₂ × Cᵢ) ∩ Rⱼ)` for the `i, j ≥ 3` of the diameter-2
  -- argument is semiregular, non-empty and not complete, so its relative symmetry defect
  -- is `≥ 1/2` in each part (Prop. 2.4.30), and `α = βn/d₂ ≥ β` makes it an input of
  -- Theorem 9.2.2 with `α·|C₂| = βn`.  All of this is `Babai.upccOutcome` and
  -- `Babai.upccOutcome_good`.
  --
  -- The family of outcomes is indexed by the individualized vertex, so it has at most `n`
  -- members, which is the multiplicative cost; its equivariance (condition (ii) of
  -- Def. 6.0.1) is `Babai.upccOutcome_iso`.
  classical
  refine FindsAtMultCost.of_outcomes_sub
    (fun X => Set.range fun x : ↥X.car => upccOutcome β X.obj.1 x) (fun X => ?_)
    (fun X => Set.finite_range _) (fun X => ?_) (fun {X Y f} hf Z hZ => ?_)
    (fun X Z hZ => ?_)
  · -- a UPCC has a vertex, so there is at least one outcome
    have h2 := upcc_two_le_ncard X.obj.2
    obtain ⟨x, hx⟩ : X.car.Nonempty := by
      rw [← Set.ncard_pos (Set.toFinite _)]; omega
    exact ⟨upccOutcome β X.obj.1 ⟨x, hx⟩, ⟨x, hx⟩, rfl⟩
  · -- at most `n` outcomes: one for each vertex
    show (Set.range fun x : ↥X.car => upccOutcome β X.obj.1 x).ncard ≤ X.car.ncard
    rw [← Set.image_univ]
    have h1 := Set.ncard_image_le (s := (Set.univ : Set ↥X.car))
      (f := fun x : ↥X.car => upccOutcome β X.obj.1 x) Set.finite_univ
    rwa [Set.ncard_univ, Nat.card_coe_set_eq] at h1
  · obtain ⟨x, rfl⟩ := hZ
    exact ⟨upccOutcome β Y.obj.1 (f x), ⟨f x, rfl⟩, upccOutcome_iso β hβ hf x⟩
  · obtain ⟨x, rfl⟩ := hZ
    exact upccOutcome_good β hβ X x

/-! ### Extending a colored partition of `W` to one of `V ⊇ W` -/

open scoped Classical in
/-- The colored partition of `V` obtained from a colored partition `Π` of a subset
`W ⊆ V` by adding `V \ W` as a single block of a new color.

This is the construction used in the proof of the transfer clause of Lemma 9.3.1: *"a
colored `α`-partition of `W` becomes a colored `β`-partition of `V`"*.  The colors of `W`
are shifted by one so that the new color `0` of `V \ W` is not a color of `W`; the blocks
inside `W` are the blocks of `Π`, and `V \ W` is one block. -/
noncomputable def extendPartition (V W : Set Ω) (P : ColoredPartition ↥W ℕ) :
    ColoredPartition ↥V ℕ where
  color x := if h : (x : Ω) ∈ W then P.color ⟨(x : Ω), h⟩ + 1 else 0
  part :=
    ⟨fun x y => ((x : Ω) ∈ W ↔ (y : Ω) ∈ W) ∧
        ∀ (hx : (x : Ω) ∈ W) (hy : (y : Ω) ∈ W), P.part ⟨(x : Ω), hx⟩ ⟨(y : Ω), hy⟩,
      ⟨fun x => ⟨Iff.rfl, fun hx _ => P.part.iseqv.refl ⟨(x : Ω), hx⟩⟩,
       fun {_ _} h => ⟨h.1.symm, fun hx hy => P.part.iseqv.symm (h.2 hy hx)⟩,
       fun {_ _ _} h₁ h₂ => ⟨h₁.1.trans h₂.1, fun hx hz =>
         P.part.iseqv.trans (h₁.2 hx (h₁.1.1 hx)) (h₂.2 (h₁.1.1 hx) hz)⟩⟩⟩
  part_le_color := by
    rintro x y ⟨hiff, hp⟩
    by_cases hx : (x : Ω) ∈ W
    · rw [dif_pos hx, dif_pos (hiff.1 hx)]
      exact congrArg (· + 1) (P.part_le_color (hp hx (hiff.1 hx)))
    · rw [dif_neg hx, dif_neg (fun h => hx (hiff.2 h))]

namespace extendPartition

variable {V W : Set Ω} (hW : W ⊆ V) (P : ColoredPartition ↥W ℕ)

theorem color_of_mem {x : ↥V} (hx : (x : Ω) ∈ W) :
    (extendPartition V W P).color x = P.color ⟨(x : Ω), hx⟩ + 1 := dif_pos hx

theorem color_of_notMem {x : ↥V} (hx : (x : Ω) ∉ W) :
    (extendPartition V W P).color x = 0 := dif_neg hx

/-- Inside `W` the blocks of the extension are the blocks of `Π`. -/
theorem block_of_mem {x : ↥V} (hx : (x : Ω) ∈ W) :
    (extendPartition V W P).block x = Set.inclusion hW '' P.block ⟨(x : Ω), hx⟩ := by
  ext y
  constructor
  · rintro ⟨hiff, hp⟩
    have hy : (y : Ω) ∈ W := hiff.2 hx
    exact ⟨⟨(y : Ω), hy⟩, hp hy hx, Subtype.ext rfl⟩
  · rintro ⟨w, hw, rfl⟩
    refine ⟨⟨fun _ => hx, fun _ => w.2⟩, fun hy hx' => ?_⟩
    have h2 : (⟨((Set.inclusion hW w : ↥V) : Ω), hy⟩ : ↥W) = w := Subtype.ext rfl
    rw [h2]
    exact hw

/-- Outside `W` the extension has the single block `V \ W`. -/
theorem block_of_notMem {x : ↥V} (hx : (x : Ω) ∉ W) :
    (extendPartition V W P).block x = {y : ↥V | (y : Ω) ∉ W} := by
  ext y
  constructor
  · rintro ⟨hiff, -⟩
    exact fun hy => hx (hiff.1 hy)
  · intro hy
    exact ⟨⟨fun h => absurd h hy, fun h => absurd h hx⟩, fun hy' => absurd hy' hy⟩

/-- Inside `W` the color classes of the extension are the color classes of `Π`. -/
theorem colorClass_of_mem {x : ↥V} (hx : (x : Ω) ∈ W) :
    (extendPartition V W P).colorClass ((extendPartition V W P).color x)
      = Set.inclusion hW '' P.colorClass (P.color ⟨(x : Ω), hx⟩) := by
  ext y
  simp only [ColoredPartition.colorClass, Set.mem_setOf_eq, Set.mem_image,
    color_of_mem P hx]
  constructor
  · intro hy
    by_cases hyW : (y : Ω) ∈ W
    · refine ⟨⟨(y : Ω), hyW⟩, ?_, Subtype.ext rfl⟩
      rw [color_of_mem P hyW] at hy
      show P.color ⟨(y : Ω), hyW⟩ = _
      omega
    · rw [color_of_notMem P hyW] at hy; omega
  · rintro ⟨w, hw, rfl⟩
    rw [color_of_mem (V := V) (x := Set.inclusion hW w) P w.2]
    have h2 : (⟨((Set.inclusion hW w : ↥V) : Ω), w.2⟩ : ↥W) = w := Subtype.ext rfl
    rw [h2]
    have hw' : P.color w = P.color ⟨(x : Ω), hx⟩ := hw
    rw [hw']

/-- Outside `W` the color class of the extension is `V \ W`, which is also the block. -/
theorem colorClass_of_notMem {x : ↥V} (hx : (x : Ω) ∉ W) :
    (extendPartition V W P).colorClass ((extendPartition V W P).color x)
      = {y : ↥V | (y : Ω) ∉ W} := by
  ext y
  simp only [ColoredPartition.colorClass, Set.mem_setOf_eq, color_of_notMem P hx]
  by_cases hy : (y : Ω) ∈ W
  · rw [color_of_mem P hy]
    exact ⟨fun h => by omega, fun h => absurd hy h⟩
  · rw [color_of_notMem P hy]
    exact ⟨fun _ => hy, fun _ => rfl⟩

/-- The extension is admissible if `Π` is. -/
theorem isAdmissible {V W : Set Ω} (hW : W ⊆ V) (P : ColoredPartition ↥W ℕ)
    (hP : P.IsAdmissible) : (extendPartition V W P).IsAdmissible := by
  intro x hx
  by_cases hxW : (x : Ω) ∈ W
  · rw [block_of_mem hW P hxW, Set.ncard_image_of_injective _ (Set.inclusion_injective hW)]
    refine hP ⟨(x : Ω), hxW⟩ ?_
    rw [colorClass_of_mem hW P hxW,
      Set.ncard_image_of_injective _ (Set.inclusion_injective hW)] at hx
    exact hx
  · rw [block_of_notMem P hxW]
    rwa [colorClass_of_notMem P hxW] at hx

/-- The block of the extension outside `W` has `|V| - |W|` elements. -/
theorem ncard_outside {V W : Set Ω} (hW : W ⊆ V) :
    ({y : ↥V | (y : Ω) ∉ W}).ncard = V.ncard - W.ncard := by
  have himg : (Subtype.val : ↥V → Ω) '' {y : ↥V | (y : Ω) ∉ W} = V \ W := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩; exact ⟨y.2, hy⟩
    · rintro ⟨hzV, hzW⟩; exact ⟨⟨z, hzV⟩, hzW, rfl⟩
  rw [← Set.ncard_image_of_injective _ Subtype.val_injective, himg,
    Set.ncard_diff hW (Set.toFinite _)]

/-- The extension of a colored `α`-partition of `W` is a colored `β`-partition of `V`, as
soon as `α ≤ 1`, `1/2 ≤ β` and `α|W| = β|V|`.

The blocks of the extension are the blocks of `Π`, of size `≤ ρ(Π) ≤ α|W| = β|V|`, and the
one new block `V \ W`, of size `|V| - |W| ≤ |V| - β|V| = (1-β)|V| ≤ β|V|` — the last step is
where `β ≥ 1/2` is used, and `|W| ≥ α|W| = β|V|` is where `α ≤ 1` is used. -/
theorem isAlphaPartition {V W : Set Ω} (hW : W ⊆ V) (iW : Fintype ↥W) (iV : Fintype ↥V)
    (P : ColoredPartition ↥W ℕ) {α β : ℝ} (hα1 : α ≤ 1) (hβ : 1 / 2 ≤ β)
    (hαβ : α * (W.ncard : ℝ) = β * (V.ncard : ℝ))
    (hP : @ColoredPartition.IsAlphaPartition ↥W ℕ P iW α) :
    @ColoredPartition.IsAlphaPartition ↥V ℕ (extendPartition V W P) iV β := by
  letI := iW
  letI := iV
  have hWV : W.ncard ≤ V.ncard := Set.ncard_le_ncard hW (Set.toFinite _)
  have hW0 : (0 : ℝ) ≤ (W.ncard : ℝ) := by positivity
  have hV0 : (0 : ℝ) ≤ (V.ncard : ℝ) := by positivity
  have hcW : (Fintype.card ↥W : ℕ) = W.ncard := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
  have hcV : (Fintype.card ↥V : ℕ) = V.ncard := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
  -- `β|V| = α|W| ≤ |W|`, because `α ≤ 1`
  have hβW : β * (V.ncard : ℝ) ≤ (W.ncard : ℝ) := by
    have h := mul_le_mul_of_nonneg_right hα1 hW0
    rw [one_mul] at h
    linarith [hαβ]
  refine ⟨isAdmissible hW P hP.1, ?_⟩
  -- every block of the extension has at most `max ρ(Π) (|V| - |W|)` elements
  set M : ℕ := max P.rho (V.ncard - W.ncard) with hM
  have hblocks : ∀ x : ↥V, ((extendPartition V W P).block x).ncard ≤ M := by
    intro x
    by_cases hx : (x : Ω) ∈ W
    · rw [block_of_mem hW P hx,
        Set.ncard_image_of_injective _ (Set.inclusion_injective hW)]
      exact le_trans (P.ncard_block_le_rho _) (le_max_left _ _)
    · rw [block_of_notMem P hx, ncard_outside hW]
      exact le_max_right _ _
  have hrho : (extendPartition V W P).rho ≤ M := ColoredPartition.rho_le _ hblocks
  have hMle : (M : ℝ) ≤ β * (V.ncard : ℝ) := by
    rw [hM, Nat.cast_max]
    refine max_le ?_ ?_
    · have h1 : (P.rho : ℝ) ≤ α * (Fintype.card ↥W : ℝ) := hP.2
      rw [hcW, hαβ] at h1
      exact h1
    · rw [Nat.cast_sub hWV]
      have hhalf := mul_le_mul_of_nonneg_right hβ hV0
      linarith
  have hfin : ((extendPartition V W P).rho : ℝ) ≤ (M : ℝ) := by exact_mod_cast hrho
  rw [hcV]
  linarith

/-- The extension of a colored partition by the block `V \ W` is canonical: if `f : V ≃ V'`
restricts to an isomorphism `g : Π → Π'` of the colored partitions of `W` and `W'`, then
`f` is an isomorphism of the two extensions.

The colors match because the extension gives the color `P.color + 1` inside `W` and the
color `0` outside, and `f` maps `W` onto `W'`; the blocks match because inside `W` they are
the blocks of `Π` and outside `W` there is the single block `V \ W`. -/
theorem mem_iso {V W V' W' : Set Ω} (hW : W ⊆ V) (hW' : W' ⊆ V')
    {P : ColoredPartition ↥W ℕ} {P' : ColoredPartition ↥W' ℕ}
    (f : ↥V ≃ ↥V') (g : ↥W ≃ ↥W')
    (hg : ∀ x : ↥W, ((g x : Ω)) = ((f ⟨(x : Ω), hW x.2⟩ : Ω)))
    (hgiso : g ∈ (ColoredPartitions Ω ℕ).Iso P P') :
    f ∈ (ColoredPartitions Ω ℕ).Iso (extendPartition V W P)
      (extendPartition V' W' P') := by
  obtain ⟨hcol, hpart⟩ := hgiso
  -- `f` carries `W` onto `W'`.
  have hgval : ∀ (x : ↥V) (hx : (x : Ω) ∈ W),
      (g ⟨(x : Ω), hx⟩ : ↥W') = ⟨(f x : Ω), by
        have h := (g ⟨(x : Ω), hx⟩).2
        have he : ((g ⟨(x : Ω), hx⟩ : ↥W') : Ω) = (f x : Ω) := by
          have := hg ⟨(x : Ω), hx⟩
          simpa using this
        rwa [he] at h⟩ := by
    intro x hx
    refine Subtype.ext ?_
    have := hg ⟨(x : Ω), hx⟩
    simpa using this
  have hmem : ∀ x : ↥V, ((f x : Ω) ∈ W' ↔ (x : Ω) ∈ W) := by
    intro x
    refine ⟨fun h => ?_, fun h => ?_⟩
    · set y : ↥W := g.symm ⟨(f x : Ω), h⟩ with hy
      have h1 : ((g y : ↥W') : Ω) = ((f ⟨(y : Ω), hW y.2⟩ : ↥V') : Ω) := hg y
      have h2 : ((g y : ↥W') : Ω) = (f x : Ω) := by
        rw [hy, Equiv.apply_symm_apply]
      have h4 : (⟨(y : Ω), hW y.2⟩ : ↥V) = x :=
        f.injective (Subtype.ext (h1.symm.trans h2))
      have h5 : (x : Ω) = (y : Ω) := (congrArg Subtype.val h4).symm
      rw [h5]
      exact y.2
    · have := hgval x h
      have h2 := (g ⟨(x : Ω), h⟩).2
      rw [this] at h2
      exact h2
  refine ⟨fun x => ?_, fun x y => ?_⟩
  · by_cases hx : (x : Ω) ∈ W
    · have hfx : ((f x : ↥V') : Ω) ∈ W' := (hmem x).2 hx
      rw [color_of_mem _ hfx, color_of_mem _ hx]
      have := hcol ⟨(x : Ω), hx⟩
      rw [hgval x hx] at this
      rw [this]
    · have hfx : ((f x : ↥V') : Ω) ∉ W' := fun h => hx ((hmem x).1 h)
      rw [color_of_notMem _ hfx, color_of_notMem _ hx]
  · constructor
    · rintro ⟨hiff, hp⟩
      refine ⟨?_, fun hfx hfy => ?_⟩
      · rw [hmem x, hmem y]; exact hiff
      · have hx : (x : Ω) ∈ W := (hmem x).1 hfx
        have hy : (y : Ω) ∈ W := (hmem y).1 hfy
        have := (hpart ⟨(x : Ω), hx⟩ ⟨(y : Ω), hy⟩).1 (hp hx hy)
        rwa [hgval x hx, hgval y hy] at this
    · rintro ⟨hiff, hp⟩
      refine ⟨?_, fun hx hy => ?_⟩
      · rw [← hmem x, ← hmem y]; exact hiff
      · have hfx : ((f x : ↥V') : Ω) ∈ W' := (hmem x).2 hx
        have hfy : ((f y : ↥V') : Ω) ∈ W' := (hmem y).2 hy
        refine (hpart ⟨(x : Ω), hx⟩ ⟨(y : Ω), hy⟩).2 ?_
        rw [hgval x hx, hgval y hy]
        exact hp hfx hfy

end extendPartition

/-- Lemma 9.3.1(ii), the transfer clause: *"a solution to each part of Theorem 9.2.2 for
`X̄` is also a solution to the corresponding part of Theorem 9.2.1 for `X`"*.

In the paper's proof, `W = C₂` is the first part of `X̄`, `V` is the vertex set of the
UPCC, and `α = βn/d₂`, so that `α|W| = βn = β|V|`; a colored `α`-partition of `W` becomes
a colored `β`-partition of `V` by adding `V \ W` as one block of a new color (of size
`|V| - |W| ≤ (1-β)|V| ≤ β|V|`, which is where `β ≥ 1/2` is used), and an embedded Johnson
scheme on a subset of `W` of relative size `≥ α` has absolute size `≥ α|W| = β|V|` already.

The hypothesis is the paper's equality `α|W| = β|V|`, not an inequality: the two branches
need it in opposite directions (see the note on `IsUPCCToBipOutcome`). -/
theorem lemma_9_3_1_transfer {α β : ℝ} {V W : Set Ω} (hW : W ⊆ V)
    (hα1 : α ≤ 1) (hβ : 1 / 2 ≤ β) (hαβ : α * (W.ncard : ℝ) = β * (V.ncard : ℝ))
    {Z : Pt (SplitOutcomes Ω)} (hZ : IsSplitOutcome α W Z) :
    ∃ Z' : Pt (SplitOutcomes Ω), IsSplitOutcome β V Z' := by
  classical
  obtain ⟨c, o⟩ := Z
  cases o with
  | inr J =>
    -- objective (b): the same Johnson scheme works, since `α|W| = β|V|`
    obtain ⟨hsub, hle⟩ := hZ
    exact ⟨⟨c, Sum.inr J⟩, hsub.trans hW, by rw [← hαβ]; exact hle⟩
  | inl P =>
    -- objective (a): add `V \ W` as one block of a new color
    obtain ⟨hcW, hP⟩ := hZ
    have hcW' : c = W := hcW
    subst hcW'
    exact ⟨⟨V, Sum.inl (extendPartition V c P)⟩, rfl,
      extendPartition.isAlphaPartition hW (Fintype.ofFinite _) (Fintype.ofFinite _) P
        hα1 hβ hαβ hP⟩

end Babai
