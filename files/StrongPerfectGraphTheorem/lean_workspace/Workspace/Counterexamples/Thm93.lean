import Workspace.Types.Knots
import Workspace.Types.Overshadowed
import Workspace.ProofLemmas.Thm93Infrastructure
import Workspace.ProofLemmas.PathGlue
import Workspace.ProofLemmas.BergeTwoRegularCriterion
import Workspace.ProofLemmas.K4AppearanceEightVertices
import Workspace.ProofLemmas.K4AppearanceDegreeCriterion
import Workspace.ProofLemmas.K4TrackLengthDegeneracy
import Workspace.ProofLemmas.LK33Regular
import Workspace.ProofLemmas.NoK4EnlargementAppearance

/-!
# Statement 9.3, as printed, is false

This module is a countermodel, not a step of the proof.  It lives in `Workspace/Counterexamples`
and nothing in the development imports it: the main theorem does not depend on a single line
below.  Its job is to justify one repair the repository makes to the paper, by exhibiting a
graph that satisfies every hypothesis of `Workspace.Statements.S09.SPGT.thm_9_3` and refutes the
conclusion **as printed**.  That is the content of the single theorem `printed_nine_three_false`.

The graph has eleven vertices.  On `{0,…,9}` it is the complement of the line graph of the
bipartite subdivision of `K₄` with square `0-1-2-3-0` and diagonal branches `0-4-5-6-2` and
`1-7-3`, whose ten edges are labelled `a₁,b₁,a₂,b₂,x₁,z₁,z₂,y₁,x₂,y₂` in that order; those ten
vertices carry the knot `([0,1], [2,3], [4,5,6,7], [8,9])` and are its `K`.  Vertex `10` is a
*twin of `x₁` in `Ḡ`* — its `Ḡ`-neighbourhood inside `K` is `{b₁, b₂, z₁} = {1,3,5}`, exactly
that of `x₁` — and it lies **outside** `K`, which is what makes `F = {10} ⊆ Kᶜ` hold.

Eleven vertices is forced, not chosen: a knot needs `|K| ≥ 8`; the antipath `Q₁` must be long
for outcome 9.3.4 to bite; 9.1 makes its track length even, so `|V(Q₁)| ≥ 4` and `|K| ≥ 10`;
and `F` needs one more.

**This does not contradict the repository's `thm_9_3`.**  That theorem carries the approved
repair of outcome 9.3.4 — `∃ w, (w ∈ Q₁ ∨ w ∈ Q₂) ∧ w ∉ Q' ∧ w ≠ x ∧ ¬ G.Adj f w` in place of
the printed `¬ G.Adj f y` — and this configuration *satisfies* the repaired conclusion, with
witness `w = 5` (`repaired_conclusion11`).  The two results together pin the repair exactly:
the printed clause genuinely fails here, the weakened clause genuinely holds.
-/

set_option autoImplicit false

namespace Workspace.Counterexamples.Thm93

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Knots Workspace.Types.Knots.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Overshadowed.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.ProofLemmas.Thm93Infrastructure
open Workspace.ProofLemmas.K4TrackLengthDegeneracy
open Workspace.ProofLemmas.K4AppearanceDegreeCriterion
open Workspace.ProofLemmas

variable {V : Type*}

/-- **The conclusion of 9.3 as printed.**

This is `Thm93Infrastructure.Conclusion` with the printed form of outcome 9.3.4, namely
`¬ G.Adj f y`, in place of the repaired clause
`∃ w, (w ∈ Q₁ ∨ w ∈ Q₂) ∧ w ∉ Q' ∧ w ≠ x ∧ ¬ G.Adj f w`.  It is what the graph of this module
refutes; the repaired conclusion does hold for that graph, with the witness `w = 5`. -/
abbrev PrintedConclusion (G : SimpleGraph V)
    (P₁ P₂ Q₁ Q₂ : List V) (a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂ : V) (K F : Set V) : Prop :=
    (∃ f ∈ F, ResolvesKnot G P₁ P₂ Q₁ Q₂ (G.neighborSet f ∩ K)) ∨
    (∃ (a : V) (P P' : List V),
      ((a, P, P') = (a₁, P₁, P₂) ∨ (a, P, P') = (b₁, P₁, P₂) ∨
        (a, P, P') = (a₂, P₂, P₁) ∨ (a, P, P') = (b₂, P₂, P₁)) ∧
      ∃ (R : List V) (r₁ r₂ : V),
        IsPathFrom G R r₁ r₂ ∧ (∀ v ∈ R, v ∈ F) ∧
        (∀ w ∈ ({v : V | v ∈ P'} ∪ {v : V | v ∈ Q₁} ∪ {v : V | v ∈ Q₂} : Set V),
          (G.Adj r₁ w ↔ G.Adj a w)) ∧
        Anticomplete G ({v : V | v ∈ R} \ {r₁})
          ({v : V | v ∈ P'} ∪ {v : V | v ∈ Q₁} ∪ {v : V | v ∈ Q₂}) ∧
        (∃ w ∈ ({v : V | v ∈ P} \ {a} : Set V), G.Adj r₂ w) ∧
        Anticomplete G ({v : V | v ∈ R} \ {r₂}) ({v : V | v ∈ P} \ {a})) ∨
    (∃ (a b : V) (P P' : List V),
      ((a, b, P, P') = (a₁, b₁, P₁, P₂) ∨ (a, b, P, P') = (b₁, a₁, P₁, P₂) ∨
        (a, b, P, P') = (a₂, b₂, P₂, P₁) ∨ (a, b, P, P') = (b₂, a₂, P₂, P₁)) ∧
      ∃ (R : List V) (r₁ r₂ : V),
        IsPathFrom G R r₁ r₂ ∧ (∀ v ∈ R, v ∈ F) ∧ Odd (pathLength R) ∧
        (∀ w ∈ ({v : V | v ∈ P'} ∪ {v : V | v ∈ Q₁} ∪ {v : V | v ∈ Q₂} : Set V),
          (G.Adj r₁ w ↔ G.Adj a w)) ∧
        (∀ w ∈ ({v : V | v ∈ P'} ∪ {v : V | v ∈ Q₁} ∪ {v : V | v ∈ Q₂} : Set V),
          (G.Adj r₂ w ↔ G.Adj b w)) ∧
        Anticomplete G {v : V | v ∈ SPGT.interior R}
          ({v : V | v ∈ P'} ∪ {v : V | v ∈ Q₁} ∪ {v : V | v ∈ Q₂}) ∧
        (∀ u ∈ R, ∀ w ∈ P, G.Adj u w → ((u = r₁ ∧ w = a) ∨ (u = r₂ ∧ w = b)))) ∨
    (∃ (x y : V) (Q' : List V),
      ((x, y, Q') = (x₁, y₁, Q₂) ∨ (x, y, Q') = (y₁, x₁, Q₂) ∨
        (x, y, Q') = (x₂, y₂, Q₁) ∨ (x, y, Q') = (y₂, x₂, Q₁)) ∧
      ∃ f ∈ F,
        (∀ w ∈ ({v : V | v ∈ P₁} ∪ {v : V | v ∈ P₂} ∪ {v : V | v ∈ Q'} : Set V),
          (G.Adj f w ↔ G.Adj x w)) ∧
        ¬ G.Adj f y)

/-! ## An adjusted counterexample: `F` genuinely outside the knot

The graph above puts `F` **inside** `K`, so it refutes the frozen gap lemma rather than 9.3
itself.  Adjusting it removes that defect.  Keep the same knot on `{0,…,9}`, and add one new
vertex `10` which is a *twin of* `x₁ = 4` in `Ḡ`: its `Ḡ`-neighbourhood inside `K` is
`{b₁, b₂, z₁} = {1, 3, 5}`, exactly that of `x₁`.  Now

* `K = {0,…,9}` and `F = {10}`, so `F ⊆ Kᶜ` **holds** (`F_subset_compl11`);
* the printed conclusion of 9.3 still fails (`not_conclusion11`);
* the **repaired** conclusion holds, with witness `w = 5` (`repaired_conclusion11`), which is
  the precise sense in which the approved repair of 9.3.4 is not too weak.

Eleven vertices is forced: a knot needs `|K| ≥ 8`, the antipath `Q₁` must be long for 9.3.4 to
bite, and 9.1 makes its track length even, so `|V(Q₁)| ≥ 4` and `|K| ≥ 10`; one more vertex is
needed for `F`. -/

/-- The thirty-six edges: the twenty-nine above, plus `10` joined to `K \ {b₁, b₂, z₁}`. -/
def edges11 : Finset (Sym2 (Fin 11)) :=
  {s(0,1), s(0,4), s(0,8), s(0,5), s(0,6),
   s(2,3), s(2,4), s(2,9), s(2,5), s(2,6),
   s(1,7), s(1,9), s(1,5), s(1,6),
   s(3,8), s(3,7), s(3,5), s(3,6),
   s(4,8), s(4,7), s(4,9), s(4,6),
   s(8,7), s(8,5), s(8,6),
   s(7,9), s(7,5), s(9,5), s(9,6),
   s(10,0), s(10,2), s(10,4), s(10,6), s(10,7), s(10,8), s(10,9)}

/-- The eleven-vertex graph: the knot of `graph`, plus a `Ḡ`-twin of `x₁` outside it. -/
def graph11 : SimpleGraph (Fin 11) := SimpleGraph.fromEdgeSet (↑edges11)

instance : DecidableRel graph11.Adj := by
  unfold graph11
  infer_instance

instance : DecidableRel graph11ᶜ.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

/-- The knot's vertex set: everything except the new vertex `10`. -/
def K11 : Set (Fin 11) := {0, 1, 2, 3, 4, 5, 6, 7, 8, 9}

/-! ### `hknot`, `hP₁ hP₂`, `hQ₁ hQ₂`, `hK` -/

theorem short_paths11 :
    IsPathFrom graph11 [0,1] 0 1 ∧ IsPathFrom graph11 [2,3] 2 3 :=
  ⟨⟨PathBasics.isPathList_pair (by decide), rfl, rfl⟩,
    ⟨PathBasics.isPathList_pair (by decide), rfl, rfl⟩⟩

theorem antipaths11 :
    IsAntipathFrom graph11 [4,5,6,7] 4 7 ∧ IsAntipathFrom graph11 [8,9] 8 9 := by
  refine ⟨⟨?_, rfl, rfl⟩, ⟨PathBasics.isPathList_pair (by decide), rfl, rfl⟩⟩
  exact PathGlue.isPathList_four (G := graph11ᶜ) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

theorem isKnot11 : IsKnot graph11 [0,1] [2,3] [4,5,6,7] [8,9] := by
  refine ⟨0,1,2,3,4,7,8,9, short_paths11.1, short_paths11.2,
    antipaths11.1, antipaths11.2, ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, pathLength,
    List.length_cons, List.length_nil, Set.mem_insert_iff, Set.mem_singleton_iff,
    Anticomplete, Complete, VertexAnticomplete, VertexComplete, Set.mem_setOf_eq,
    forall_eq_or_imp, forall_eq]
  repeat' apply And.intro
  all_goals first | decide | change s(_, _) ∈ edges11; decide

theorem induces11 : KnotInduces [0,1] [2,3] [4,5,6,7] [8,9] K11 := by
  ext v
  fin_cases v <;> simp [K11]

/-! ### `hG : Berge G` -/

set_option maxRecDepth 80000 in
/-- The eleven-vertex graph is Berge, by the same `2`-regular criterion. -/
theorem berge11 : Berge graph11 := by
  constructor
  · exact BergeTwoRegularCriterion.even_of_no_odd_two_regular graph11 (by decide)
  · exact BergeTwoRegularCriterion.even_of_no_odd_two_regular graph11ᶜ (by decide)

/-! ### `hFsub : F ⊆ Kᶜ` — now **true** -/

/-- `hFsub` **holds** here: the new vertex `10` lies outside the knot. -/
theorem F_subset_compl11 : ({10} : Set (Fin 11)) ⊆ K11ᶜ := by
  intro v hv
  have hv10 : v = 10 := hv
  subst hv10
  simp [K11]

/-! ### `hFconn : ConnectedSet G F` -/

theorem F_connected11 : ConnectedSet graph11 ({10} : Set (Fin 11)) := by
  intro u v
  have huv : u = v :=
    Subtype.ext ((u.2 : (u : Fin 11) = 10).trans (v.2 : (v : Fin 11) = 10).symm)
  exact huv ▸ SimpleGraph.Reachable.refl u

/-! ### `hFattach` -/

private theorem mem_attachments11 {v : Fin 11} (hv : v ∈ K11) (h : graph11.Adj v 10) :
    v ∈ attachments graph11 ({10} : Set (Fin 11)) K11 :=
  ⟨hv, 10, rfl, h⟩

theorem attachments_not_local11 :
    ¬ LocalForKnot graph11 [0,1] [2,3] [4,5,6,7] [8,9]
        (attachments graph11 ({10} : Set (Fin 11)) K11) := by
  rintro ⟨hdisj, -, -, -⟩
  have h0 := mem_attachments11 (v := 0) (by simp [K11]) (by decide)
  have h2 := mem_attachments11 (v := 2) (by simp [K11]) (by decide)
  rcases hdisj with h | h
  · exact Set.disjoint_left.mp h h0 (by simp)
  · exact Set.disjoint_left.mp h h2 (by simp)

/-! ### The conclusion still fails, and the repaired one holds -/

/-- The attachment set of `F` does not resolve the knot: the edge `b₁z₁ = (1,5)` has neither
end in it. -/
theorem not_resolves11 :
    ¬ ResolvesKnot graph11 [0,1] [2,3] [4,5,6,7] [8,9]
        (graph11.neighborSet 10 ∩ K11) := by
  intro h
  have he := h.2.2.2 1 (by simp) 5 (by simp) (by decide)
  rcases he with h | h
  · exact (show ¬ graph11.Adj 10 1 by decide) h.1
  · exact (show ¬ graph11.Adj 10 5 by decide) h.1

/-- **All four alternatives of 9.3 as printed fail**, now with `F` genuinely outside `K`. -/
theorem not_conclusion11 :
    ¬ PrintedConclusion graph11 [0,1] [2,3] [4,5,6,7] [8,9]
        0 1 2 3 4 7 8 9 K11 ({10} : Set (Fin 11)) := by
  rintro (⟨f, hf, hres⟩ | h | h | h)
  · have he : f = 10 := hf
    subst f
    exact not_resolves11 hres
  · obtain ⟨a, P, P', hchoice, R, r₁, r₂, hR, hRF, hsame, _⟩ := h
    have hr : r₁ = 10 := hRF r₁ (PathBasics.isPathFrom_ends_mem hR).1
    subst r₁
    rcases hchoice with h | h | h | h <;> cases h <;>
      have hh := (hsame 5 (by simp)).mpr (by decide) <;>
      exact (show ¬ graph11.Adj 10 5 by decide) hh
  · obtain ⟨a, b, P, P', hchoice, R, r₁, r₂, hR, hRF, _, hsame, _⟩ := h
    have hr : r₁ = 10 := hRF r₁ (PathBasics.isPathFrom_ends_mem hR).1
    subst r₁
    rcases hchoice with h | h | h | h <;> cases h <;>
      have hh := (hsame 5 (by simp)).mpr (by decide) <;>
      exact (show ¬ graph11.Adj 10 5 by decide) hh
  · obtain ⟨x, y, Q', hchoice, f, hf, hsame, hnon⟩ := h
    have he : f = 10 := hf
    subst f
    rcases hchoice with h | h | h | h <;> cases h
    · exact hnon (by decide)
    · exact (show ¬ graph11.Adj 7 0 by decide) ((hsame 0 (by simp)).mp (by decide))
    · exact (show ¬ graph11.Adj 10 3 by decide) ((hsame 3 (by simp)).mpr (by decide))
    · exact (show ¬ graph11.Adj 10 1 by decide) ((hsame 1 (by simp)).mpr (by decide))

/-- **The repaired conclusion does hold** for this graph, with witness `w = 5`.

Together with `not_conclusion11` this pins the repair exactly: the printed 9.3.4 fails here
while the weakened clause succeeds, so the change is neither vacuous nor too generous. -/
theorem repaired_conclusion11 :
    Conclusion graph11 [0,1] [2,3] [4,5,6,7] [8,9]
      0 1 2 3 4 7 8 9 K11 ({10} : Set (Fin 11)) := by
  refine Or.inr (Or.inr (Or.inr ⟨4, 7, [8,9], Or.inl rfl, 10, rfl, ?_, 5, ?_, ?_, ?_, ?_⟩))
  · intro w hw
    simp only [Set.mem_union, Set.mem_setOf_eq, List.mem_cons, List.not_mem_nil,
      or_false] at hw
    rcases hw with ((rfl | rfl) | (rfl | rfl)) | (rfl | rfl) <;> decide
  · exact Or.inl (by simp)
  · simp
  · decide
  · decide

/-! ### `hnoover` and half of `hnoenl`: `graph11` has no `K₄`-appearance at all

Every vertex of `L(H)`, for `H` a subdivision of `K₄`, has degree between `2` and `4` (it is an
edge `uv` of `H`, of degree `deg u + deg v - 2`, and `H` has degrees `2` and `3` only).  For
`graph11` no vertex subset of size `≥ 8` has all its internal degrees in that range, so no
appearance exists — and `8` is the lower bound of `K4AppearanceEightVertices`. -/

set_option maxRecDepth 100000 in
private theorem deg_crit11 :
    ∀ S : Finset (Fin 11), 8 ≤ S.card →
      ∃ v ∈ S, (S.filter (fun w => graph11.Adj v w)).card < 2 ∨
               4 < (S.filter (fun w => graph11.Adj v w)).card := by decide

/-- `graph11` has no appearance of `K₄` whatsoever. -/
theorem no_appearance11 : ¬ Appears graph11 (⊤ : SimpleGraph (Fin 4)) := by
  refine Workspace.ProofLemmas.K4AppearanceDegreeCriterion.no_appearance_of_degree_criterion
    graph11 ?_
  intro K hK
  classical
  have hcard : K.ncard = K.toFinset.card := Set.ncard_eq_toFinset_card' K
  obtain ⟨v, hvS, hv⟩ := deg_crit11 K.toFinset (by omega)
  refine ⟨v, Set.mem_toFinset.mp hvS, ?_⟩
  have hconv : (graph11.neighborSet v ∩ K).ncard
      = (K.toFinset.filter (fun w => graph11.Adj v w)).card := by
    rw [Set.ncard_eq_toFinset_card']
    congr 1
    ext w
    simp [SimpleGraph.mem_neighborSet, and_comm]
  rwa [hconv]

/-- `hnoover`: with no appearance at all, none can be overshadowed. -/
theorem no_overshadowed11 :
    ¬ ∃ (n : ℕ) (H : SimpleGraph (Fin n)) (K' : Set (Fin 11))
      (φ : H.lineGraph ≃g graph11.induce K'),
      IsAppearance graph11 (⊤ : SimpleGraph (Fin 4)) H K' ∧
        IsOvershadowedAppearance graph11 H K' φ := by
  rintro ⟨n, H, K', φ, happ, -⟩
  exact no_appearance11 ⟨n, H, K', happ⟩

/-! ### No induced `L(K₃,₃)`, in `graph11` and in its complement

`L(K₃,₃)` is `4`-regular on nine vertices (`LK33Regular`), so an induced copy would be a
nine-element vertex set every one of whose members has exactly four neighbours inside it.
Neither graph has such a set. -/

set_option maxRecDepth 100000 in
private theorem deg9_crit11 :
    ∀ S : Finset (Fin 11), S.card = 9 →
      ∃ v ∈ S, (S.filter (fun w => graph11.Adj v w)).card ≠ 4 := by decide

set_option maxRecDepth 100000 in
private theorem deg9_crit11c :
    ∀ S : Finset (Fin 11), S.card = 9 →
      ∃ v ∈ S, (S.filter (fun w => (graph11ᶜ).Adj v w)).card ≠ 4 := by decide

/-- Shared bridge: a `Finset`-level degree fact transfers to the `Set`-level form that
`LK33Regular.no_induced_L33_of_degree_criterion` wants. -/
private theorem nine_criterion_of_finset (Gx : SimpleGraph (Fin 11)) [DecidableRel Gx.Adj]
    (h : ∀ S : Finset (Fin 11), S.card = 9 →
      ∃ v ∈ S, (S.filter (fun w => Gx.Adj v w)).card ≠ 4) :
    ∀ K : Set (Fin 11), K.ncard = 9 → ∃ v ∈ K, (Gx.neighborSet v ∩ K).ncard ≠ 4 := by
  intro K hK
  classical
  have hcard : K.ncard = K.toFinset.card := Set.ncard_eq_toFinset_card' K
  obtain ⟨v, hvS, hv⟩ := h K.toFinset (by omega)
  refine ⟨v, Set.mem_toFinset.mp hvS, ?_⟩
  have hconv : (Gx.neighborSet v ∩ K).ncard
      = (K.toFinset.filter (fun w => Gx.Adj v w)).card := by
    rw [Set.ncard_eq_toFinset_card']
    congr 1
    ext w
    simp [SimpleGraph.mem_neighborSet, and_comm]
  rwa [hconv]

theorem no_L33_11 :
    ¬ ∃ K : Set (Fin 11),
      Nonempty ((completeBipartiteGraph (Fin 3) (Fin 3)).lineGraph ≃g graph11.induce K) :=
  Workspace.ProofLemmas.LK33Regular.no_induced_L33_of_degree_criterion graph11
    (nine_criterion_of_finset graph11 deg9_crit11)

theorem no_L33_11c :
    ¬ ∃ K : Set (Fin 11),
      Nonempty ((completeBipartiteGraph (Fin 3) (Fin 3)).lineGraph ≃g (graph11ᶜ).induce K) :=
  Workspace.ProofLemmas.LK33Regular.no_induced_L33_of_degree_criterion graph11ᶜ
    (nine_criterion_of_finset graph11ᶜ deg9_crit11c)

/-- `hnoenl`, the `graph11` half: no `K₄`-enlargement appears in `graph11`.

`NoK4EnlargementAppearance.no_k4_enlargement_appears` needs "every `K₄`-appearance is
degenerate" and "no induced `L(K₃,₃)`".  Here the first is vacuous, since there is no
appearance at all. -/
theorem no_enlargement11 :
    ¬ ∃ (m : ℕ) (J' : SimpleGraph (Fin m)),
      IsJEnlargement (⊤ : SimpleGraph (Fin 4)) J' ∧ Appears graph11 J' :=
  Workspace.ProofLemmas.NoK4EnlargementAppearance.no_k4_enlargement_appears graph11
    (fun n H K happ => absurd ⟨n, H, K, happ⟩ no_appearance11) no_L33_11

/-! ### The complement side: every `K₄`-appearance in `graph11ᶜ` is degenerate

Appearances *do* exist here — by 9.2 the knot itself is one — so they cannot be excluded by a
degree count.  Instead: in `L(H)` a vertex has degree `4` exactly when its edge joins two
branch-vertices (a track of length `1`), and degree `3` exactly when one end is a branch-vertex,
which happens twice per track of length `≥ 2`.  With six tracks this gives
`2·#deg₄ + #deg₃ = 12`.  For `graph11ᶜ` that identity forces `#deg₄ ≥ 4`, i.e. four tracks of
length `1`; bipartite parity then makes those four a `4`-cycle through all four branch-vertices,
so the appearance is degenerate and no branch has odd length `≥ 3`. -/

set_option maxRecDepth 200000 in
private theorem track_count_crit11c :
    ∀ S : Finset (Fin 11), 8 ≤ S.card →
      2 * (S.filter (fun v => (S.filter (fun w => (graph11ᶜ).Adj v w)).card = 4)).card
        + (S.filter (fun v => (S.filter (fun w => (graph11ᶜ).Adj v w)).card = 3)).card ≠ 12
      ∨ 4 ≤ (S.filter (fun v => (S.filter (fun w => (graph11ᶜ).Adj v w)).card = 4)).card := by
  decide

private theorem count_conv (K : Set (Fin 11)) [Fintype ↥K] (k : ℕ) :
    {v ∈ K | ((graph11ᶜ).neighborSet v ∩ K).ncard = k}.ncard
      = (K.toFinset.filter (fun v =>
          (K.toFinset.filter (fun w => (graph11ᶜ).Adj v w)).card = k)).card := by
  classical
  have inner : ∀ v : Fin 11,
      ((graph11ᶜ).neighborSet v ∩ K).ncard
        = (K.toFinset.filter (fun w => (graph11ᶜ).Adj v w)).card := by
    intro v
    rw [Set.ncard_eq_toFinset_card']
    congr 1
    ext w
    simp [SimpleGraph.mem_neighborSet, and_comm]
  have hset : {v ∈ K | ((graph11ᶜ).neighborSet v ∩ K).ncard = k}
      = ↑(K.toFinset.filter (fun v =>
          (K.toFinset.filter (fun w => (graph11ᶜ).Adj v w)).card = k)) := by
    ext v
    simp only [Set.mem_setOf_eq, Finset.coe_filter, Set.mem_toFinset, inner v]
  rw [hset, Set.ncard_coe_finset]

/-- Every `K₄`-appearance in `graph11ᶜ` has at least four branch-to-branch edges. -/
theorem four_le_bedges11c {n : ℕ} {H : SimpleGraph (Fin n)} {K : Set (Fin 11)}
    (hH : IsBipartiteSubdivision (⊤ : SimpleGraph (Fin 4)) H)
    (φ : H.lineGraph ≃g (graph11ᶜ).induce K) :
    4 ≤ (bedges H).ncard := by
  classical
  have h8 : 8 ≤ K.ncard :=
    Workspace.ProofLemmas.K4AppearanceEightVertices.eight_le_ncard_of_isAppearance
      graph11ᶜ ⟨hH, ⟨φ⟩⟩
  have h12 := two_mul_deg_four_add_deg_three graph11ᶜ hH φ
  have h4 := deg_four_eq_branch_edges graph11ᶜ hH φ
  rw [count_conv K 4] at h12 h4
  rw [count_conv K 3] at h12
  have hcard : K.ncard = K.toFinset.card := Set.ncard_eq_toFinset_card' K
  rcases track_count_crit11c K.toFinset (by omega) with hbad | hgood
  · exact absurd h12 hbad
  · omega

/-- Every `K₄`-appearance in `graph11ᶜ` is degenerate — the `hdeg` input of
`NoK4EnlargementAppearance.no_k4_enlargement_appears`. -/
theorem degenerate11c : ∀ (n : ℕ) (H : SimpleGraph (Fin n)) (K : Set (Fin 11)),
    IsAppearance (graph11ᶜ) (⊤ : SimpleGraph (Fin 4)) H K →
      DegenerateAppearance (⊤ : SimpleGraph (Fin 4)) H := by
  rintro n H K ⟨hsub, ⟨φ⟩⟩
  exact Or.inl ⟨⟨SimpleGraph.Iso.refl⟩,
    degenerate_of_four_branch_edges hsub (four_le_bedges11c hsub φ)⟩

/-- `hnoovercompl`: no overshadowed appearance of `K₄` in `graph11ᶜ`. -/
theorem no_overshadowed11c :
    ¬ ∃ (n : ℕ) (H : SimpleGraph (Fin n)) (K' : Set (Fin 11))
      (φ : H.lineGraph ≃g (graph11ᶜ).induce K'),
      IsAppearance (graph11ᶜ) (⊤ : SimpleGraph (Fin 4)) H K' ∧
        IsOvershadowedAppearance (graph11ᶜ) H K' φ := by
  rintro ⟨n, H, K', φ, ⟨hsub, -⟩, B, b₁, b₂, hbranch, -, hodd, hge3, -⟩
  exact no_long_odd_branch_of_four_branch_edges hsub (four_le_bedges11c hsub φ) B hbranch
    ⟨hodd, hge3⟩

/-- No `K₄`-enlargement appears in `graph11ᶜ`. -/
theorem no_enlargement11c :
    ¬ ∃ (m : ℕ) (J' : SimpleGraph (Fin m)),
      IsJEnlargement (⊤ : SimpleGraph (Fin 4)) J' ∧ Appears (graph11ᶜ) J' :=
  Workspace.ProofLemmas.NoK4EnlargementAppearance.no_k4_enlargement_appears graph11ᶜ
    degenerate11c no_L33_11c

/-- `hnoenl`, in the exact shape `thm_9_3` asks for. -/
theorem no_enlargement11_both :
    ¬ ∃ (m : ℕ) (J' : SimpleGraph (Fin m)),
      IsJEnlargement (⊤ : SimpleGraph (Fin 4)) J' ∧
        (Appears graph11 J' ∨ Appears (graph11ᶜ) J') := by
  rintro ⟨m, J', hJ', hApp | hApp⟩
  · exact no_enlargement11 ⟨m, J', hJ', hApp⟩
  · exact no_enlargement11c ⟨m, J', hJ', hApp⟩

/-! ## Capstone: the printed 9.3 is false -/

/-- **Statement 9.3 as printed is false.**

Every hypothesis of `Workspace.Statements.S09.SPGT.thm_9_3` holds of the configuration
`G = graph11`, `(P₁,P₂,Q₁,Q₂) = ([0,1],[2,3],[4,5,6,7],[8,9])`, `K = K11`, `F = {10}` — listed
below in the order of that theorem's binders — and yet the printed conclusion fails.

The repository's `thm_9_3` is *not* contradicted: it carries the approved repair of outcome
9.3.4, which this configuration does satisfy (`repaired_conclusion11`, witness `w = 5`). -/
theorem printed_nine_three_false :
    -- hG
    Berge graph11 ∧
    -- hknot
    IsKnot graph11 [0,1] [2,3] [4,5,6,7] [8,9] ∧
    -- hP₁, hP₂
    IsPathFrom graph11 [0,1] 0 1 ∧ IsPathFrom graph11 [2,3] 2 3 ∧
    -- hQ₁, hQ₂
    IsAntipathFrom graph11 [4,5,6,7] 4 7 ∧ IsAntipathFrom graph11 [8,9] 8 9 ∧
    -- hK
    KnotInduces [0,1] [2,3] [4,5,6,7] [8,9] K11 ∧
    -- hnoenl
    (¬ ∃ (m : ℕ) (J' : SimpleGraph (Fin m)),
      IsJEnlargement (⊤ : SimpleGraph (Fin 4)) J' ∧
        (Appears graph11 J' ∨ Appears (graph11ᶜ) J')) ∧
    -- hnoover
    (¬ ∃ (n : ℕ) (H : SimpleGraph (Fin n)) (K' : Set (Fin 11))
      (φ : H.lineGraph ≃g graph11.induce K'),
      IsAppearance graph11 (⊤ : SimpleGraph (Fin 4)) H K' ∧
        IsOvershadowedAppearance graph11 H K' φ) ∧
    -- hnoovercompl
    (¬ ∃ (n : ℕ) (H : SimpleGraph (Fin n)) (K' : Set (Fin 11))
      (φ : H.lineGraph ≃g (graph11ᶜ).induce K'),
      IsAppearance (graph11ᶜ) (⊤ : SimpleGraph (Fin 4)) H K' ∧
        IsOvershadowedAppearance (graph11ᶜ) H K' φ) ∧
    -- hFsub, hFconn, hFattach
    (({10} : Set (Fin 11)) ⊆ K11ᶜ) ∧
    ConnectedSet graph11 ({10} : Set (Fin 11)) ∧
    (¬ LocalForKnot graph11 [0,1] [2,3] [4,5,6,7] [8,9]
        (attachments graph11 ({10} : Set (Fin 11)) K11)) ∧
    -- and yet the printed conclusion fails
    (¬ PrintedConclusion graph11 [0,1] [2,3] [4,5,6,7] [8,9]
        0 1 2 3 4 7 8 9 K11 ({10} : Set (Fin 11))) :=
  ⟨berge11, isKnot11, short_paths11.1, short_paths11.2, antipaths11.1, antipaths11.2,
    induces11, no_enlargement11_both, no_overshadowed11, no_overshadowed11c,
    F_subset_compl11, F_connected11, attachments_not_local11, not_conclusion11⟩


end Workspace.Counterexamples.Thm93
