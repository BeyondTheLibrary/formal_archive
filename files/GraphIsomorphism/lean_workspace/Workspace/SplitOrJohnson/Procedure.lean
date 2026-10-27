/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Sections 9.4 and 9.5: Procedure Bipartite Split-or-Johnson and its three claims;
measures of progress.
-/
import Workspace.SplitOrJohnson.Imprimitive
import Workspace.Coherent.LargeClique
import Workspace.Coherent.TwinAwareness

/-!
# §9.4 Procedure Bipartite Split-or-Johnson, §9.5 Measures of progress

Version 2.5, lines 4092–4182 of `babai-gi-source/quasi25.txt`.

| Paper | Lean |
|---|---|
| Claim of step 2 ("This is a colored `α`-partition") | `Babai.claim_9_4_step2` |
| step 5 (the dominant vertex-color class, the update of `α`) | `Babai.claim_9_4_step5` |
| step 7 ("otherwise `V₁` would be a twin equivalence class") | `Babai.claim_9_4_step7` |
| Claim of step 6 ("`X₁` is uniprimitive") | `Babai.claim_9_4_step6` |
| Claim of step 8 ("There are no `X`-twins in `V₁`") | `Babai.claim_9_4_step8` |
| §9.5, "significantly reduced" | `Babai.IsSignificantlyReduced` |
| §9.5, "major progress" | `Babai.MajorProgress` |

## The procedure

Procedure Bipartite Split-or-Johnson (lines 4118–4180) is the proof of Theorem 9.2.2: a
loop whose steps either exit with objective (a) or (b), or transform the instance
(`X ← X[W₁, V₂]`, `X ← X[V₁ ∪ D_j]`, `X ← (V₁, V₂; Rᵢ)`, …) and continue.  Its steps are
therefore not a single canonical construction; what is formalized here are the three
Claims made inside the procedure, which are the mathematical content of its steps 2, 6
and 8, and the measures of progress of §9.5 that the case analysis of step 9 uses.  The
overall statement of the procedure is Theorem 9.2.2 itself (`Babai.theorem_9_2_2`).
-/

namespace Babai

/-! ### Step 2 -/

/-- Claim of step 2 of Procedure Bipartite Split-or-Johnson.  *"If `n₂ ≤ c log n₁` … then
individualize all vertices of `V₂`, apply naive vertex refinement, return colored partition
of `V₁`, exit.  Claim.  This is a colored `α`-partition.  Proof.  All vertices of the same
color in `V₁` are twins."*  (Version 2.5, lines 4115–4118.)

The content of the claim is that a block consisting of twins has size `≤ αn₁`: this is what
makes the returned colored partition a colored `α`-partition (Def. 7.1.1), and it uses the
standing hypothesis of Theorem 9.2.2 that the symmetry defect of `X` on `V₁` is at least
`1 - α`. -/
theorem claim_9_4_step2 {s : Type} [Fintype s] [DecidableEq s] {κ : Type}
    (X : VColBip s κ) {α : ℝ} (hdef : 1 - α ≤ (X.defect₁ : ℝ))
    {T : Finset s} (hT₁ : ∀ x ∈ T, X.part₁ x) (hT : IsTwinSet X.Aut (↑T : Set s)) :
    (T.card : ℝ) ≤ α * (X.V₁.ncard : ℝ) := by
  have hcard : (T.card : ℝ) ≤ (X.symmetricity₁ : ℝ) := by
    exact_mod_cast VColBip.card_le_symmetricity₁ hT₁ hT
  rcases Nat.eq_zero_or_pos X.V₁.ncard with h0 | hpos
  · -- `V₁` is empty, so there are no twins inside it either
    have hV : X.V₁ = ∅ := (Set.ncard_eq_zero (Set.toFinite X.V₁)).1 h0
    have hT0 : T = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro x hx
      have hxV : x ∈ X.V₁ := hT₁ x hx
      rw [hV] at hxV
      exact hxV
    simp [hT0, h0]
  · -- `s₁ = (1 - defect₁) n₁ ≤ α n₁`
    have hn : (0 : ℝ) < (X.V₁.ncard : ℝ) := by exact_mod_cast hpos
    have hdef' : 1 - α ≤ 1 - (X.symmetricity₁ : ℝ) / (X.V₁.ncard : ℝ) := by
      have : ((X.defect₁ : ℚ) : ℝ)
          = 1 - (X.symmetricity₁ : ℝ) / (X.V₁.ncard : ℝ) := by
        rw [VColBip.defect₁]; push_cast; ring
      rwa [this] at hdef
    have : (X.symmetricity₁ : ℝ) / (X.V₁.ncard : ℝ) ≤ α := by linarith
    calc (T.card : ℝ) ≤ (X.symmetricity₁ : ℝ) := hcard
      _ = ((X.symmetricity₁ : ℝ) / (X.V₁.ncard : ℝ)) * (X.V₁.ncard : ℝ) := by
          field_simp
      _ ≤ α * (X.V₁.ncard : ℝ) := by nlinarith

/-! ### Step 5 -/

/-- Step 5 of Procedure Bipartite Split-or-Johnson.  *"Let `W₁ ⊆ V₁` be the dominant color
class: `|W₁| > αn₁`.  Update `α ← αn₁/|W₁|`, `V₁ ← W₁` (this automatically updates `n₁`),
`X ← X[W₁, V₂]` (induced subgraph), `X ← X[W₁ ∪ V₂]`."*  (Version 2.5, lines 4136–4139.)

The step is legitimate only if the new instance is again an admissible input of
Theorem 9.2.2, i.e. if the new threshold parameter `α_new = αn₁/|W₁|` is again `< 1` and if
the hypothesis `|V₂| < α n₁` of the old instance becomes `|V₂| < α_new |W₁|` for the new
one.  Both are recorded here, and the second holds with equality of the two bounds:
`α_new |W₁| = α n₁`.  (That `α_new ≥ α`, so that the symmetry-defect hypothesis
`1 - α_new ≤ 1 - α` is not tightened, is the third clause.) -/
theorem claim_9_4_step5 {α : ℝ} {n₁ w : ℕ} (hα : 0 < α) (hw : α * (n₁ : ℝ) < w)
    (hwn : w ≤ n₁) : α * (n₁ : ℝ) / w < 1 ∧ α * (n₁ : ℝ) / w * w = α * n₁ ∧
      α ≤ α * (n₁ : ℝ) / w := by
  have hwpos : (0 : ℝ) < w := lt_of_le_of_lt (by positivity) hw
  refine ⟨(div_lt_one hwpos).2 hw, div_mul_cancel₀ _ (ne_of_gt hwpos), ?_⟩
  have hwn' : (w : ℝ) ≤ n₁ := by exact_mod_cast hwn
  rw [le_div_iff₀ hwpos]
  nlinarith

/-! ### Step 6 -/

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- Claim of step 6 of Procedure Bipartite Split-or-Johnson.  *"Claim.  `X₁` is
uniprimitive.  Proof.  Given that `X₁` is primitive, we only need to rule out that `X₁` is
the clique configuration.  `V₁` is larger than any other color-class in `X`.  Therefore, if
`X₁` were the clique configuration, it would follow by the Large clique lemma
(Lemma 3.4.25) that `V₁` is a twin equivalence class in `X`, a contradiction with the
positive symmetry defect assumption."*  (Version 2.5, lines 4142–4146.)

"`X₁` is the clique configuration" is `rank (X[V₁]) = 2`, so the claim is that the rank of
`X[V₁]` is not `2`; together with the primitivity of `X₁` this is uniprimitivity
(Def. 3.2.1).  The "positive symmetry defect assumption" says that `V₁` is not a single
twin equivalence class of `X`. -/
theorem claim_9_4_step6 (X : PartitionStructure Ω) (h : X.IsCoherent) (i₀ : Fin X.rank)
    (hmax : ∀ i : Fin X.rank, i ≠ i₀ →
      (X.vertexClass i).ncard < (X.vertexClass i₀).ncard)
    {x : Ω} (hx : x ∈ X.vertexClass i₀) (hdef : twinClass X.Aut x ≠ X.vertexClass i₀) :
    (X.induced (X.vertexClass i₀)).rank ≠ 2 := fun hclique =>
  hdef (X.large_clique_twinClass h i₀ hmax hclique hx)

/-! ### Step 7 -/

/-- Step 7 of Procedure Bipartite Split-or-Johnson.  *"If `X₂` is not homogeneous, let
`(D₁,…,D_k)` be the partition of `V₂` into vertex-color classes.  Pick the smallest `j` such
that the induced bipartite substructure `X[V₁, D_j]` is nontrivial.  (Such a `j` exists
because otherwise `V₁` would be a twin equivalence class in `X₁₂`.)"*
(Version 2.5, lines 4152–4155.)

The content is the parenthesis, stated contrapositively: if *every* `X[V₁, D_j]` is trivial
— for each `j` either no vertex of `V₁` has a neighbor in `D_j`, or every vertex of `V₁` is
joined to every vertex of `D_j` — then all the vertices of `V₁` have the same neighborhood
(the union of the `D_j` of the second kind), hence, `V₁` being a single vertex-color class,
they are pairwise twins, so `V₁` is a twin equivalence class.  That contradicts the standing
assumption that the symmetry defect of `X` on `V₁` is positive.

`D` is the set of vertex-color classes of `V₂`; `hcov` says that they cover `V₂`. -/
theorem claim_9_4_step7 {s : Type} [Fintype s] [DecidableEq s] {κ : Type} (X : VColBip s κ)
    (D : Set (Set s)) (hcov : ∀ y ∈ X.V₂, ∃ Dj ∈ D, y ∈ Dj)
    (htriv : ∀ Dj ∈ D, (∀ x ∈ X.V₁, ∀ y ∈ Dj, (x, y) ∉ X.E) ∨
      (∀ x ∈ X.V₁, ∀ y ∈ Dj, y ∈ X.V₂ → (x, y) ∈ X.E))
    (hcolor : ∀ x ∈ X.V₁, ∀ y ∈ X.V₁, X.f x = X.f y)
    {u v : s} (hu : u ∈ X.V₁) (hv : v ∈ X.V₁) (huv : u ≠ v) :
    X.IsTwinIn u v := by
  refine VColBip.isTwinIn_of_nbhd_eq hu hv huv ?_ (hcolor u hu v hv)
  intro y
  by_cases hy : y ∈ X.V₂
  · obtain ⟨Dj, hDj, hyD⟩ := hcov y hy
    rcases htriv Dj hDj with hemp | hfull
    · exact ⟨fun h => absurd h (hemp u hu y hyD), fun h => absurd h (hemp v hv y hyD)⟩
    · exact ⟨fun _ => hfull v hv y hyD hy, fun _ => hfull u hu y hyD hy⟩
  · -- a vertex outside `V₂` is the head of no edge
    constructor
    · intro h; exact absurd (X.E_sub _ h).2 (by simpa [VColBip.V₂] using hy)
    · intro h; exact absurd (X.E_sub _ h).2 (by simpa [VColBip.V₂] using hy)

/-! ### Step 8 -/

/-- Claim of step 8 of Procedure Bipartite Split-or-Johnson.  *"Claim.  There are no
`X`-twins in `V₁`.  Proof.  This follows from the 'no twins in primitive color' theorem
(Theorem 3.4.11), given that `X₁` is primitive."*  (Version 2.5, lines 4161–4163.)

At this point of the procedure `X` has been replaced by the single constituent
`(V₁, V₂; Rᵢ)` of the link, which is nontrivial and semiregular; `V₁` is the tail class of
the color `i`. -/
theorem claim_9_4_step8 (X : PartitionStructure Ω) (h : X.IsCoherent) (k : Fin X.rank)
    (hij : X.tailColor k ≠ X.headColor k)
    (hnt : ¬ (X.bipConstituent k).IsTrivial)
    (hprim : (X.induced (X.vertexClass (X.tailColor k))).IsPrimitive)
    {x y : Ω} (hx : x ∈ X.vertexClass (X.tailColor k))
    (hy : y ∈ X.vertexClass (X.tailColor k)) (hxy : x ≠ y) :
    ¬ IsTwin (X.bipConstituent k).Aut (Sum.inl ⟨x, hx⟩) (Sum.inl ⟨y, hy⟩) :=
  X.no_twins_in_primitive_color h k hij hnt hprim hx hy hxy

/-! ### §9.5 Measures of progress -/

/-- §9.5.  *"We say that a parameter `m` is significantly reduced if
`m_new ≤ 0.9 m_old`."*  (Version 2.5, lines 4174–4176.) -/
def IsSignificantlyReduced (mNew mOld : ℕ) : Prop := 10 * mNew ≤ 9 * mOld

/-- §9.5.  *"We deem to have made major progress if any of the following occurs: goal (a)
or (b) is achieved; `n₂` is significantly reduced; `X₂` moves from clique to UPCC while
`n₂` does not increase."*  (Version 2.5, lines 4176–4181.)

The three disjuncts are parameters of the definition: `goal` records whether goal (a) or
(b) has been achieved, `n₂old`, `n₂new` are the sizes of the second part before and after,
and `cliqueToUPCC` records the third alternative. -/
def MajorProgress (goal : Prop) (n₂old n₂new : ℕ) (cliqueToUPCC : Prop) : Prop :=
  goal ∨ IsSignificantlyReduced n₂new n₂old ∨ (cliqueToUPCC ∧ n₂new ≤ n₂old)

end Babai
