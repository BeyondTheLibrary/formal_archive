/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 9.2: Split-or-Johnson, the Extended Design Lemma.  The three main theorems.
-/
import Workspace.SplitOrJohnson.BipSplit

/-!
# §9.2 Split-or-Johnson: the Extended Design Lemma

Version 2.5, lines 4002–4040 of `babai-gi-source/quasi25.txt`.

| Paper | Lean |
|---|---|
| Theorem 9.2.1 (UPCC Split-or-Johnson) | `Babai.theorem_9_2_1` (`Workspace/SplitOrJohnson/Sec92.lean`) |
| Theorem 9.2.2 (Bipartite Split-or-Johnson) | `Babai.theorem_9_2_2` (`Workspace/SplitOrJohnson/Turn.lean`) |
| Theorem 9.2.3 (Extended Design Lemma) | `Babai.theorem_9_2_3` (`Workspace/SplitOrJohnson/Sec92.lean`) |
| the admissible inputs of Thm. 9.2.1 | `Babai.UPCCInputs` |
| the admissible inputs of Thm. 9.2.2 | `Babai.BipInputs` |
| Theorem 9.2.2 in the wider category of §9.4-§9.8 | `Babai.theorem_9_2_2_blocks` (`Workspace/SplitOrJohnson/Turn.lean`) |
| points as singleton blocks | `Babai.bipToBlk` |
| the admissible inputs of Thm. 9.2.3 | `Babai.KAryInputs` |

## How the statements are worded

Each theorem says: *"at (quasipolynomial) multiplicative cost we can find either (a) … or
(b) …"*.  This is `Babai.FindsAtMultCost` (Defs. 6.0.3, 6.0.5, 6.0.7 of §6) applied to the
category of admissible inputs and to the category `SplitOutcomes` of the two possible
outputs, with the property `IsSplitOutcome` of the output.

The parenthetical *"(The time bounds do not depend on `α`.)"* is rendered by putting the
quantifier over the cost function `q` **outside** the quantifier over the threshold
parameter: one quasipolynomial `q` works for all admissible `α`.

The running-time clauses ("in time …", "polynomial additive cost") are **pending**; they
will be stated in the RAM model of `Workspace/Machine/` (Decision 2 of `PLAN.md`).  See
the entry of kind "pending" in the corrected paper.
-/

namespace Babai

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

/-! ### The inputs of Theorem 9.2.1 -/

/-- §9.2.  The category of edge-colored binary structures that carry a **threshold
parameter** `β` as part of the object; a morphism keeps the parameter.

This is to Theorem 9.2.1 what `Babai.VColBipThr` is to Theorem 9.2.2, and it is there for
the same reason: the `β` that the proof of Theorem 9.2.3 hands to Theorem 9.2.1 is
`β = αn/|C|`, a function of the input object (see `Babai.designBeta` and the entry for
Theorem 9.2.3 in the corrected paper), and `Babai.FindsAtMultCost.comp_dep` can only chain
reductions whose parameters are object data. -/
def ColoredEdgesThr (Ω : Type) : Cat.{0, 0} Ω where
  Obj s := (↥s → ↥s → ℕ) × ℝ
  Iso X Y := {g | X.2 = Y.2 ∧ g ∈ (ColoredEdges Ω ℕ).Iso X.1 Y.1}
  refl_mem X := ⟨rfl, (ColoredEdges Ω ℕ).refl_mem X.1⟩
  symm_mem hf := ⟨hf.1.symm, (ColoredEdges Ω ℕ).symm_mem hf.2⟩
  trans_mem hf hg := ⟨hf.1.trans hg.1, (ColoredEdges Ω ℕ).trans_mem hf.2 hg.2⟩
  faithful hid := Prod.ext ((ColoredEdges Ω ℕ).faithful hid.2) hid.1

/-- The admissible inputs of Theorem 9.2.1: a UPCC **together with its threshold
parameter `β`**, subject to *"`2/3 ≤ β < 1`"*.

The morphisms are exactly the isomorphisms of UPCCs that keep `β`, so for a fixed `β` this
is the category `Babai.UPCCs` of the printed statement; `Babai.upccAttachBeta` is that
identification, and `Babai.theorem_9_2_1_at` is the printed statement. -/
def UPCCInputs (Ω : Type) : Cat.{0, 0} Ω :=
  (ColoredEdgesThr Ω).full fun _ X => 2 / 3 ≤ X.2 ∧ X.2 < 1 ∧ IsUPCCColoring X.1

/-- The threshold parameter `β` of an admissible input of Theorem 9.2.1. -/
def UPCCInputs.beta (X : Pt (UPCCInputs Ω)) : ℝ := X.obj.1.2

/-- The UPCC of an admissible input of Theorem 9.2.1: the input with its threshold
parameter forgotten.  It is a canonical embedding onto the same vertex set. -/
def upccThrForget : Func (UPCCInputs Ω) (UPCCs Ω) where
  obj X := ⟨X.car, ⟨X.obj.1.1, X.obj.2.2.2⟩⟩
  map f := ⟨f.1, f.2.2⟩
  map_id _ := rfl
  map_trans _ _ := rfl

omit [Fintype Ω] [DecidableEq Ω] in
@[simp] theorem upccThrForget_car (X : Pt (UPCCInputs Ω)) :
    (upccThrForget.obj X).car = X.car := rfl

omit [Fintype Ω] [DecidableEq Ω] in
/-- §6.  Forgetting the threshold parameter is a canonical embedding: it does not move the
underlying set, and a morphism is sent to itself. -/
theorem upccThrForget_isCanonicalEmbedding :
    (upccThrForget (Ω := Ω)).IsCanonicalEmbedding where
  car_subset _ := subset_rfl
  map_restrict _ _ := rfl

/-- A UPCC with a **fixed** threshold parameter `β`, as an admissible input of
Theorem 9.2.1.  This is the functor that turns the printed statement of Theorem 9.2.1 into
the statement on the category `Babai.UPCCInputs`: it does not move the underlying set, and
a morphism of UPCCs is a morphism of the pairs because both carry the same `β`. -/
def upccAttachBeta (β : ℝ) (hβ : 2 / 3 ≤ β) (hβ1 : β < 1) :
    Func (UPCCs Ω) (UPCCInputs Ω) where
  obj X := ⟨X.car, ⟨(X.obj.1, β), ⟨hβ, hβ1, X.obj.2⟩⟩⟩
  map f := ⟨f.1, ⟨rfl, f.2⟩⟩
  map_id _ := rfl
  map_trans _ _ := rfl

omit [Fintype Ω] [DecidableEq Ω] in
@[simp] theorem upccAttachBeta_beta (β : ℝ) (hβ : 2 / 3 ≤ β) (hβ1 : β < 1)
    (X : Pt (UPCCs Ω)) :
    UPCCInputs.beta ((upccAttachBeta β hβ hβ1).obj X) = β := rfl

omit [Fintype Ω] [DecidableEq Ω] in
@[simp] theorem upccAttachBeta_car (β : ℝ) (hβ : 2 / 3 ≤ β) (hβ1 : β < 1)
    (X : Pt (UPCCs Ω)) : ((upccAttachBeta β hβ hβ1).obj X).car = X.car := rfl

omit [Fintype Ω] [DecidableEq Ω] in
/-- §6.  Attaching a fixed threshold parameter is a canonical embedding. -/
theorem upccAttachBeta_isCanonicalEmbedding (β : ℝ) (hβ : 2 / 3 ≤ β) (hβ1 : β < 1) :
    (upccAttachBeta (Ω := Ω) β hβ hβ1).IsCanonicalEmbedding where
  car_subset _ := subset_rfl
  map_restrict _ _ := rfl

/-! ### Theorem 9.2.2 -/

/-- The vertex set `V₁` of a vertex-colored bipartite graph, as a subset of the ambient
type. -/
def bipV₁ {κ : Type} (X : Pt (VColBipGraphs Ω κ)) : Set Ω := Subtype.val '' X.obj.V₁

/-- The admissible inputs of Theorem 9.2.2: a vertex-colored bipartite graph
`X = (V₁, V₂; E, f)` **together with its threshold parameter `α`** (see `VColBipThr`),
subject to *"`2/3 ≤ α < 1`"*, *"`|V₁| ≥ 2`"*, *"`|V₂| < α|V₁|`"* and *"the symmetry defect
of `X` on `V₁` is at least `1 - α`"*.

The threshold is data of the object rather than a parameter of the category because the
`α` that Lemma 9.3.1 hands to Theorem 9.2.2 depends on the object; see the docstring of
`Babai.VColBipThr` and `Babai.theorem_9_2_2_at`. -/
def BipInputs (Ω : Type) [Fintype Ω] [DecidableEq Ω] : Cat.{0, 0} Ω :=
  (VColBipThr Ω).full fun s X =>
    letI : Fintype ↥s := Fintype.ofFinite _
    letI : DecidableEq ↥s := Classical.decEq _
    2 / 3 ≤ X.2 ∧ X.2 < 1 ∧ X.1.IsThm922Input X.2

/-- The threshold parameter `α` of an admissible input of Theorem 9.2.2. -/
def BipInputs.alpha (X : Pt (BipInputs Ω)) : ℝ := X.obj.1.2

/-- The vertex set `V₁` of an admissible input of Theorem 9.2.2. -/
def BipInputs.V₁ (X : Pt (BipInputs Ω)) : Set Ω := Subtype.val '' X.obj.1.1.V₁

/-! #### Points as singleton blocks

The recursion of §9.4-§9.8 runs in the wider category `Babai.BipBlockInputs`, in which a
vertex of `V₂` is a block of points; see the module docstring of
`Workspace/SplitOrJohnson/BipBlocks.lean`.  The paper's inputs are the case of singleton
blocks, and the functor below is that case, as a canonical embedding. -/

/-- "Points as singleton blocks" on an admissible input of Theorem 9.2.2: the underlying
set, the threshold `α`, the first part `V₁`, the number of vertices of `V₂` and the
symmetry defect of `V₁` are all unchanged (`Babai.VColBip.toBlk_isThm922Input`), so the
image is an admissible input of Theorem 9.2.2 in the wider category. -/
noncomputable def bipToBlkObj (X : Pt (BipInputs Ω)) : Pt (BipBlockInputs Ω) :=
  ⟨X.car, ⟨(X.obj.1.1.toBlk, X.obj.1.2), by
    obtain ⟨h1, h2, h3⟩ := X.obj.2
    exact ⟨h1, h2, (@VColBip.toBlk_isThm922Input ↥X.car X.obj.1.1 (Fintype.ofFinite _)
      (Classical.decEq _) X.obj.1.2).2 h3⟩⟩⟩

/-- "Points as singleton blocks" as a functor `BipInputs Ω → BipBlockInputs Ω`: an
isomorphism of vertex-colored bipartite graphs is an isomorphism of the graphs with
singleton blocks (`Babai.VColBip.toBlk_isIsoTo`), and it is the *same* bijection of the
underlying set. -/
noncomputable def bipToBlk : Func (BipInputs Ω) (BipBlockInputs Ω) where
  obj := bipToBlkObj
  map {_ _} f := ⟨f.1, ⟨f.2.1, VColBip.toBlk_isIsoTo f.2.2.1 f.2.2.2.1 f.2.2.2.2⟩⟩
  map_id _ := rfl
  map_trans _ _ := rfl

/-- §6.  "Points as singleton blocks" is a canonical embedding: it does not move the
underlying set, and a morphism is sent to itself. -/
theorem bipToBlk_isCanonicalEmbedding :
    (bipToBlk (Ω := Ω)).IsCanonicalEmbedding where
  car_subset _ := subset_rfl
  map_restrict _ _ := rfl

@[simp] theorem bipToBlk_car (X : Pt (BipInputs Ω)) :
    (bipToBlk.obj X).car = X.car := rfl

@[simp] theorem bipToBlk_alpha (X : Pt (BipInputs Ω)) :
    BipBlockInputs.alpha (bipToBlk.obj X) = BipInputs.alpha X := rfl

@[simp] theorem bipToBlk_V₁ (X : Pt (BipInputs Ω)) :
    BipBlockInputs.V₁ (bipToBlk.obj X) = BipInputs.V₁ X := rfl

/-- The inputs of Theorem 9.2.2 whose threshold parameter is a **fixed** `α`: a full
subcategory of `BipInputs Ω`, with exactly the morphisms of the printed statement (an
isomorphism of the two vertex-colored bipartite graphs, the equality of the two copies of
`α` being vacuous). -/
def BipInputsAt (Ω : Type) [Fintype Ω] [DecidableEq Ω] (α : ℝ) : Cat.{0, 0} Ω :=
  (BipInputs Ω).full fun _ X => X.1.2 = α

/-! ### Theorem 9.2.3 -/

/-- The admissible inputs of Theorem 9.2.3 for the arity `k` and the threshold parameter
`α`: a `k`-ary relational structure with `n` vertices, *"`2 ≤ k ≤ n/4`"* and *"relative
strong symmetry defect `> 1 - α`"*.

(Version 2.5 still writes "strong symmetry defect" here; version 2.5 removed the weak twin
relation, so this is the symmetry defect of Def. 2.3.13/2.3.16.) -/
def KAryInputs (Ω : Type) [Fintype Ω] [DecidableEq Ω] (k : ℕ) (α : ℝ) : Cat.{0, 0} Ω :=
  (KAryStructures Ω k).full fun s X =>
    letI : Fintype ↥s := Fintype.ofFinite _
    letI : DecidableEq ↥s := Classical.decEq _
    2 ≤ k ∧ 4 * k ≤ s.ncard ∧ 1 - α < (structDefect X.1 : ℝ)

/-! Theorem 9.2.1 and Theorem 9.2.3 are stated in `Workspace/SplitOrJohnson/Sec92.lean`
(`Babai.theorem_9_2_1`, `Babai.theorem_9_2_1_at`, `Babai.theorem_9_2_3`).  They are proved
from Lemma 9.3.1 (§9.3) and from Theorem 9.2.2, and §9.3 is built on top of this file, so
they cannot live here. -/

end Babai
