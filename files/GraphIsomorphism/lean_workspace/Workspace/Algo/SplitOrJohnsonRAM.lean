/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: the running-time claims of §9 as statements about the RAM.
-/
import Workspace.Algo.SplitSolverCanonical
import Workspace.Algo.SplitUpccRunTransport
import Workspace.Algo.SplitUpccTransport
import Workspace.Algo.SplitImprimitiveCase

/-!
# Section 9 on the RAM: Theorems 9.2.1–9.2.3, Lemmas 9.3.1 and 9.6.1

The routines of §9 are implemented on the RAM elsewhere (`Workspace/Algo/Split*.lean`).  This
file states the results of §9.2, §9.3 and §9.6 in the paper's form, one theorem per numbered
item, by assembling what those files prove.

**How the paper's cost words are read.**  *"At multiplicative cost `s` we can find …"*
(Def. 6.0.3) is a family of at most `s` candidate outcomes, one for each choice; on the RAM the
routine returns the whole family as a list, so the multiplicative cost is the length of that
list, and the time is the time of the routine that computes it.  *"Quasipolynomial
multiplicative cost"* is a `RAM.QuasiFun` routine: its time is quasipolynomial, and so is the
length of the list it returns (`Algo.length_le_of_quasiFun`).  *"Polynomial additive cost"* is a
`RAM.PolyFun` routine for each member of the family.

**"The time bounds do not depend on `β`."**  The threshold is part of the input, as a pair of
naturals `(a, b)` with `β = a/b`.  Each routine below has one time bound, a function of the size
of the input, valid for every threshold.  The size of the input counts the bits of `a` and `b`;
so the bound depends on `β` only through the length of its encoding.  (the corrected paper
entry on the running-time claims of §9.)

## Main results

* `Algo.theorem_9_2_1_ram` — UPCC Split-or-Johnson;
* `Algo.theorem_9_2_2_ram` — Bipartite Split-or-Johnson;
* `Algo.theorem_9_2_3_ram` — the Extended Design Lemma, for arities `k ≤ (log₂ n + 1)^a`
  (every arity: `Algo.theorem_9_2_3_ram_all` in `Workspace/Algo/ExtendedDesignAllRAM.lean`);
* `Algo.lemma_9_3_1_ram` — UPCC-to-bipartite: `n` versions, each polynomial;
* `Algo.lemma_9_6_1_ram` — ImprimitiveCase: at most `n₂` versions, the whole family polynomial.

No axiom and no `sorry`.
-/

namespace Algo

open Babai RAM
open scoped Classical

/-- The multiplicative cost of a `RAM.QuasiFun` family is quasipolynomial: the family is no
longer than its encoding. -/
theorem length_le_of_quasiFun {α β : Type} [Enc α] [Enc β] {f : α → List β} (h : QuasiFun f) :
    ∃ q : ℕ → ℕ, QuasiPolyBound q ∧ ∀ a, (f a).length ≤ q (Enc.size a) := by
  obtain ⟨S, hS, -, hSb⟩ := h.size.exists_quasiPolyBound
  exact ⟨S, hS, fun a => (length_le_size _).trans (hSb a)⟩

theorem length_getD_le_size {β : Type} [Enc β] (o : Option (List β)) :
    (o.getD []).length ≤ Enc.size o := by
  cases o with
  | none => simp
  | some l =>
      rw [Option.getD_some, size_some_eq]
      have := length_le_size l
      omega

/-- The same for a family returned as an optional list. -/
theorem length_getD_le_of_quasiFun {α β : Type} [Enc α] [Enc β] {f : α → Option (List β)}
    (h : QuasiFun f) :
    ∃ q : ℕ → ℕ, QuasiPolyBound q ∧ ∀ a, ((f a).getD []).length ≤ q (Enc.size a) := by
  obtain ⟨S, hS, -, hSb⟩ := h.size.exists_quasiPolyBound
  exact ⟨S, hS, fun a => (length_getD_le_size _).trans (hSb a)⟩

/-- **Theorem 9.2.1 (UPCC Split-or-Johnson), §9.2, on the RAM.**  *"Let `X = (V; R₁, …, R_r)`
be a UPCC with `n` vertices and let `2/3 ≤ β < 1` be a threshold parameter.  Then at
quasipolynomial multiplicative cost we can find either (a) a canonical colored `β`-partition of
`V`, or (b) a canonically embedded nontrivial Johnson scheme on a subset of `V` of size `≥ βn`.
(The time bounds do not depend on `β`.)"*

For every value of the internal constant `c`, there are bounds `t`, `d` such that the routine
`Algo.upccSplitFamily c t d` is a `RAM.QuasiFun` (one bound for every threshold); its family is
quasipolynomially long; on every represented UPCC it is nonempty and each member is an outcome
(a) or (b) (`Babai.IsSplitOutcome`); and it is canonical: an isomorphism of two represented UPCCs
with the same threshold carries every member to a member. -/
theorem theorem_9_2_1_ram (c : ℕ) :
    ∃ t d, QuasiFun (upccSplitFamily c t d) ∧
      (∃ q : ℕ → ℕ, QuasiPolyBound q ∧
        ∀ r, (upccSplitFamily c t d r).length ≤ q (Enc.size r)) ∧
      (∀ m r (C : (UPCCs (Fin m)).Obj Set.univ), UpccInputRep m r C →
        (∃ o, o ∈ upccSplitFamily c t d r) ∧
        ∀ o ∈ upccSplitFamily c t d r, ∃ O, decAlignOutcome m o = some O ∧
          IsSplitOutcome (sbipAlphaValue r.2) Set.univ O) ∧
      (∀ m (r r' : RawUpcc) (C C' : (UPCCs (Fin m)).Obj Set.univ),
        UpccInputRep m r C → UpccInputRep m r' C' → sbipAlphaValue r.2 = sbipAlphaValue r'.2 →
        ∀ φ : ↥(Set.univ : Set (Fin m)) ≃ ↥(Set.univ : Set (Fin m)),
          φ ∈ (UPCCs (Fin m)).Iso C C' →
        ∀ π : Equiv.Perm (Fin m), (∀ x, (φ x).val = π x.val) →
        ∀ o ∈ upccSplitFamily c t d r, ∃ o' ∈ upccSplitFamily c t d r',
          RawSplitOutcomeIso m π o o') := by
  obtain ⟨t, d, -, hgood, hcan⟩ := exists_bipInputRun_valid_canonical c
  have hq := quasiFun_upccSplitFamily c t d
  refine ⟨t, d, hq, length_le_of_quasiFun hq, upccSplitFamilyGood_of_bip hgood, ?_⟩
  intro m r r' C C' h h' ha φ hφ π hπ o ho
  exact upccSplitFamily_transport hcan h h' ha φ hφ π hπ ho

/-- **Theorem 9.2.2 (Bipartite Split-or-Johnson), §9.2, on the RAM.**  *"Let
`X = (V₁, V₂; E, f)` be a vertex-colored bipartite graph with `|V₁| ≥ 2` and let
`2/3 ≤ α < 1` be a threshold parameter.  Assume `|V₂| < α|V₁|`.  Assume moreover that the
symmetry defect of `X` on `V₁` is at least `1 − α`.  Then at quasipolynomial multiplicative
cost we can find either (a) a canonical colored `α`-partition of `V₁`, or (b) a canonically
embedded nontrivial Johnson scheme on a subset of `V₁` of size `≥ α|V₁|`.  (The time bounds do
not depend on `α`.)"*

The routine `Algo.bipInputRun c t d` is a `RAM.QuasiFun`; its family is quasipolynomially
long; on every represented input (`Algo.BipInputRep`, which carries the hypotheses of the
theorem through `Babai.BipInputs`) it is nonempty with every member an outcome (a) or (b); and
it is canonical (`Algo.BipInputRunCanonical`). -/
theorem theorem_9_2_2_ram (c : ℕ) :
    ∃ t d, QuasiFun (bipInputRun c t d) ∧
      (∃ q : ℕ → ℕ, QuasiPolyBound q ∧
        ∀ r, ((bipInputRun c t d r).getD []).length ≤ q (Enc.size r)) ∧
      BipInputRunGood c t d ∧ BipInputRunCanonical c t d := by
  obtain ⟨t, d, hq, hgood, hcan⟩ := exists_bipInputRun_valid_canonical c
  exact ⟨t, d, hq, length_getD_le_of_quasiFun hq, hgood, hcan⟩

/-- **Theorem 9.2.3 (Extended Design Lemma), §9.2, on the RAM, for `k ≤ (log₂ n + 1)^a`.**
*"Let `3/4 ≤ α < 1` be a threshold parameter.  Let `X = (Ω, R)` be a `k`-ary relational
structure with `n` vertices, `2 ≤ k ≤ n/4`, and relative strong symmetry defect `> 1 − α`.
Then at a multiplicative cost of `q(n) n^{O(k)}`, where `q(n)` is a quasipolynomial function, we
can find either (a) a canonical colored `α`-partition of the vertex set, or (b) a canonically
embedded nontrivial Johnson scheme on a subset `W ⊆ Ω` of size `|W| ≥ αn`.  (The time bounds do
not depend on `α`.)"*

For every exponent `a` of the arity guard `k ≤ (log₂ n + 1)^a` (`Algo.ExtendedInputRep`), the
routine is a `RAM.QuasiFun` and its family is quasipolynomially long — in this range of `k`,
`q(n) n^{O(k)}` is a quasipolynomial; every member is an outcome (a) or (b); and the family is
canonical.  For every arity, with the time bound `poly(size) · q(n) · n^{O(k)}` and at most
`q(n) (n + 1)^k` members, see `Algo.theorem_9_2_3_ram_all`
(`Workspace/Algo/ExtendedDesignAllRAM.lean`). -/
theorem theorem_9_2_3_ram (c : ℕ) :
    ∃ t d, BipInputRunCanonical c t d ∧ ∀ a, QuasiFun (extendedSplitFamily a c t d) ∧
      (∃ q : ℕ → ℕ, QuasiPolyBound q ∧
        ∀ g, (extendedSplitFamily a c t d g).length ≤ q (Enc.size g)) ∧
      (∀ n g, ExtendedInputRep a n g →
        (∃ p, p ∈ extendedSplitFamily a c t d g) ∧
        ∀ p ∈ extendedSplitFamily a c t d g, ∃ Z, decAlignOutcome n p = some Z ∧
          IsSplitOutcome (sbipAlphaValue g.2) Set.univ Z) ∧
      (∀ n (g g' : AmbientGIn), ExtendedInputRep a n g → ExtendedInputRep a n g' →
        g.1.1 = g'.1.1 → g.2 = g'.2 → ∀ f : Equiv.Perm (Fin n),
        f ∈ KAryRelStruct.Iso (decRel n g.1.1.1.length g.1.2)
          (decRel n g.1.1.1.length g'.1.2) →
        ∀ p ∈ extendedSplitFamily a c t d g, ∃ p' ∈ extendedSplitFamily a c t d g',
          RawSplitOutcomeIso n f p p') := by
  obtain ⟨t, d, hcan, h⟩ := exists_extendedSplitFamily_valid_canonical c
  refine ⟨t, d, hcan, fun a => ?_⟩
  obtain ⟨hq, hv, hc⟩ := h a
  exact ⟨hq, length_le_of_quasiFun hq, hv, hc⟩

/-- **Lemma 9.3.1 (UPCC-to-bipartite), §9.3, on the RAM.**  *"Let `X = (V; R)` be a UPCC with
`n` vertices and let `2/3 ≤ β ≤ 1` be a threshold parameter.  Then at a multiplicative cost of
`≤ n` and polynomial additive cost one can either (i) achieve objective (a) of Theorem 9.2.1, or
(ii) reduce the given instance of Theorem 9.2.1 to Theorem 9.2.2 …"*

The versions are indexed by the individualized vertex: there are `Algo.Upcc.widthF r = n` of
them (the multiplicative cost `n`), each computed by the `RAM.PolyFun` `Algo.Upcc.versionF`
(the polynomial additive cost), and each is an outcome (i) or (ii)
(`Babai.IsUPCCToBipOutcome`).  The canonicity relative to the individualized vertex is
`Algo.Upcc.versionF_relabel`. -/
theorem lemma_9_3_1_ram :
    PolyFun Upcc.widthF ∧ PolyFun Upcc.versionF ∧
      ∀ {Ω : Type} [Fintype Ω] [DecidableEq Ω] (X : Pt (UPCCs Ω)) {n a b : ℕ}
        {p : RawConfig}, RawWL.WF n 2 p → ∀ (e : ↥X.car ≃ Fin n), UpccNames e p X.obj.1 →
        0 < b → (2 : ℝ) / 3 ≤ (a : ℝ) / b →
        Upcc.widthF (p, (a, b)) = n ∧
        ∀ i < Upcc.widthF (p, (a, b)),
          ∃ Z : Pt (Cat.sum (ColoredPartitions Ω ℕ) (BipInputs Ω)),
            UpccOutcomeRep e (Upcc.versionF ((p, (a, b)), i)) Z ∧
              IsUPCCToBipOutcome ((a : ℝ) / b) X Z := by
  refine ⟨Upcc.polyFun_widthF, Upcc.polyFun_versionF, ?_⟩
  intro Ω _ _ X n a b p h e he hb hβ
  exact ⟨Upcc.widthF_spec (r := (p, (a, b))) h,
    fun i hi => Upcc.versionF_spec_index X h e he hb hβ hi⟩

/-- **Lemma 9.6.1, §9.6, on the RAM.**  *"Under the assumptions stated in "Case" above, we can
either return a canonical colored `1/2`-partition of `V₁` at a multiplicative cost of `< n₂`,
or return, at only additive polynomial cost (no multiplicative cost) a canonical bipartite graph
`Y = (V₁, W₂; F)` such that `|W₂| ≤ |V₂|/2` such that the symmetry defect of `V₁` in `Y` is
`≥ 1/2`."*

Procedure ImprimitiveCase is the `RAM.PolyFun` `Algo.impCase`, whose family has at most `n₂`
members, and every member represents an outcome of the lemma
(`Babai.IsBlkImprimitiveOutcome`).  The multiplicative cost is `≤ n₂`, not `< n₂` in the first
branch and `1` in the second: the corrected paper, "Lemma 9.6.1: the stated costs contradict
Procedure ImprimitiveCase". -/
theorem lemma_9_6_1_ram :
    PolyFun impCase ∧
      (∀ r : RawUpccCase, 0 < r.2.2.length → (impCase r).length ≤ r.2.2.length) ∧
      ∀ {Ω : Type} [Fintype Ω] [DecidableEq Ω] {s : Set Ω}
        {X : BlkImprimitiveObj s} {name₁ : ↥X.Pt₁ → ℕ} {name₂ : ↥X.blocks → ℕ}
        {r : RawUpccCase}, ImpNames X name₁ name₂ r → r.2.1.Nodup → r.2.2.Nodup →
        ∀ (e₁ : ↥X.Pt₁ ≃ Fin r.2.1.length), (∀ x, r.2.1[(e₁ x).val] = name₁ x) →
        ∀ (e₂ : ↥X.blocks ≃ Fin r.2.2.length), (∀ B, r.2.2[(e₂ B).val] = name₂ B) →
        (∃ q, q ∈ impCase r) ∧
        ∀ q ∈ impCase r, ∃ Z : Pt (Cat.sum (ColoredPartitions Ω ℕ) (VColBlkGraphs Ω ℕ)),
          ImpOutcomeRep X name₁ name₂ r e₁ q Z ∧
            IsBlkImprimitiveOutcome (Subtype.val '' X.Pt₁) X.blocks.ncard Z := by
  refine ⟨polyFun_impCase, impCase_length, ?_⟩
  intro Ω _ _ s X name₁ name₂ r h hleft hright e₁ he₁ e₂ he₂
  exact ⟨impCase_nonempty h, fun q hq => impCase_spec h hleft hright e₁ he₁ e₂ he₂ q hq⟩

end Algo
