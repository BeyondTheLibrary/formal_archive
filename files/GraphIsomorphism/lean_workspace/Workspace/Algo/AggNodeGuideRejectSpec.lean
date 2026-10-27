/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: the rejection exit of the local guide in case (3) of Theorem 13.2.1,
stated with the classes of the original's Local guide proposition.
-/
import Workspace.Algo.AggNodeContinuation

/-! # Tag `6`: a class of `y` meets no tuple of `x`

Case (3) of Theorem 13.2.1 builds the structures `𝔷_i = (D_i; Q_i | Q ∈ Ξ)` of the Local guide
proposition (filled in from the original). Here `Ξ` is the set of
`∼`-classes of ordered `t`-tuples over both inputs. Version 2.5 runs CompareLocalCertificates
only on pairs whose first entry is a test set of `x`, so it decides `∼` on the classes that
meet `x`. The computed structures use one tuple of `x` per class as the relation label.

This file proves what the coverage test of the constructor means in those terms: it holds
exactly when every tuple of `D(y)` is `∼` to some tuple of `D(x)`
(`aggnGuideCovered_iff_tuples`). So tag `6` of `aggnContinuation` is taken exactly at
outcome (3) of `x`, with `|D(x)| = |D(y)|`, when some class meets `y` and not `x`
(`aggnContinuation_six_classes`). A class with `Q_1 = ∅ ≠ Q_2` is an invariant that differs
for the two inputs, and the original's proof of the proposition says: "If we find any invariant
that differs for X1 and X2, exit with rejection." Version 2.5 has no exit here, and its data do
not determine `𝔷_2` in this case. the corrected paper (Theorem 13.2.1 (3))
records this fill.
-/
set_option synthInstance.maxSize 2048
set_option quotPrecheck false
namespace Algo
open RAM RAM.Targets Babai Equiv

section
variable {c n m : ℕ} {C : AggnPhaseCtx} {s : AggnAggregateState} {tbl : RawAggCompareTable}
    {ϕ : decGroup n C.1.1.2 →* Perm (Fin m)}
    (hC : AggnPhaseCtxWF c n m C ϕ) (hs : AggnStoresComplete c ϕ s.1.2.1)
    (htbl : AggnCompareTableFor c ϕ tbl)
    (hset : LocalCertSetting (decGroup n C.1.1.2) ϕ)
    (ht : LargeK C.2.2.2.length (Nat.card (Fin n))) (htm : 10*C.2.2.2.length ≤ m)
    [Nonempty (Fin n)]
local notation "X" => (fun b : Bool => cond b (decStrN n C.2.2.1) (decStrN n C.2.1))
local notation "D" => localGuideData ϕ C.2.2.2.length X hset ht ((Nat.card_fin m).symm ▸ htm)
local notation "name" => (fun b : Bool => (Subtype.val : ↥(fixedGamma ϕ (X b) C.2.2.2.length) → Fin m))
include hC hs htbl

/-- §13.2, case (3): **the coverage test is the class condition.** The test at `y` holds
exactly when every ordered `t`-tuple of `D(y)` is `∼` to some ordered `t`-tuple of `D(x)`. -/
theorem aggnGuideCovered_iff_tuples :
    aggnGuideCovered (aggnGuideAt (aggnGuidePrepare c ((C,s),tbl),true)) = true ↔
      ∀ v : Fin C.2.2.2.length ↪ ↥(fixedGamma ϕ (X true) C.2.2.2.length),
        ∃ u : Fin C.2.2.2.length ↪ ↥(fixedGamma ϕ (X false) C.2.2.2.length),
          (D).mkClass ⟨false,u⟩ = (D).mkClass ⟨true,v⟩ := by
  rw [aggnGuideCovered_classes hC hs htbl hset ht htm true]
  constructor
  · intro h v
    obtain ⟨row,_,hrow⟩ := h v
    have hmem : (D).mkClass ⟨true,v⟩ ∈ aggnGuideClassKey D name false row := by
      rw [hrow]; exact Set.mem_singleton _
    obtain ⟨u,_,hu⟩ := hmem
    exact ⟨u,hu⟩
  · intro h v
    obtain ⟨u,hu⟩ := h v
    obtain ⟨row,hr,hrow⟩ := aggnGuideReps_tuple_complete hC hs htbl hset ht htm u
    exact ⟨row,hr,by rw [hrow,hu]⟩

end

section Six
variable {c n m : ℕ} {C : AggnPhaseCtx} {s : AggnAggregateState}
    {ϕ : decGroup n C.1.1.2 →* Perm (Fin m)}
    (hC : AggnPhaseCtxWF c n m C ϕ) (hs : AggnStoresComplete c ϕ s.1.2.1)
    (htbl : AggnCompareTableFor c ϕ (aggnCompareTable c (C,s.2.2.2.1)))
    (hset : LocalCertSetting (decGroup n C.1.1.2) ϕ)
    (ht : LargeK C.2.2.2.length (Nat.card (Fin n))) (htm : 10*C.2.2.2.length ≤ m)
    [Nonempty (Fin n)]
local notation "X" => (fun b : Bool => cond b (decStrN n C.2.2.1) (decStrN n C.2.1))
local notation "D" => localGuideData ϕ C.2.2.2.length X hset ht ((Nat.card_fin m).symm ▸ htm)
local notation "ts" => C.2.2.2.length
include hC hs htbl

/-- §13.2, case (3), with the Local guide proposition of the original: **tag `6` in the
paper's terms.** It is taken exactly at outcome (3) of `x`, with `|D(x)| = |D(y)|`, when some
ordered `t`-tuple of `D(y)` is `∼` to no ordered `t`-tuple of `D(x)`, that is, when some
class `Q ∈ Ξ` has `Q_1 = ∅` and `Q_2 ≠ ∅`. -/
theorem aggnContinuation_six_classes (b t d : ℕ) :
    (aggnContinuation c b t d (C,s)).1 = 6 ↔
      ((¬ Case1 (bigFGamma ϕ (X false) ts) ∧ ¬ Case2 (bigFGamma ϕ (X false) ts)) ∧
        (fixedGamma ϕ (X true) ts).ncard = (fixedGamma ϕ (X false) ts).ncard) ∧
        ∃ v : Fin ts ↪ ↥(fixedGamma ϕ (X true) ts),
          ∀ u : Fin ts ↪ ↥(fixedGamma ϕ (X false) ts),
            (D).mkClass ⟨false,u⟩ ≠ (D).mkClass ⟨true,v⟩ := by
  rw [(aggnContinuation_six_spec hC hs b t d htbl hset ht htm).1]
  have hlen (hn : (fixedGamma ϕ (X true) ts).ncard = (fixedGamma ϕ (X false) ts).ncard) :
      (aggnAggregateData ((C,s),false)).2.2.length = (aggnAggregateData ((C,s),true)).2.2.length := by
    rw [aggnAggregateFixed_length hC hs false,aggnAggregateFixed_length hC hs true]
    exact hn.symm
  have hcov := aggnGuideCovered_iff_tuples hC hs htbl hset ht htm (tbl := aggnCompareTable c (C,s.2.2.2.1))
  constructor
  · rintro ⟨hc,hno⟩
    refine ⟨hc,?_⟩
    by_contra hall
    push_neg at hall
    have hsome : aggnAggregateGuide c (C,s) ≠ none := by
      unfold aggnAggregateGuide aggnGuideBuild
      rw [if_pos]
      · simp
      simp only [Bool.and_eq_true,decide_eq_true_eq]
      exact ⟨hlen hc.2,hcov.mpr hall⟩
    exact hsome hno
  · rintro ⟨hc,v,hv⟩
    refine ⟨hc,?_⟩
    unfold aggnAggregateGuide aggnGuideBuild
    rw [if_neg]
    simp only [Bool.and_eq_true,decide_eq_true_eq,not_and]
    intro _ h
    obtain ⟨u,hu⟩ := hcov.mp h v
    exact hv u hu

end Six

end Algo
