import Workspace.Algo.FunctorsGuarded
import Workspace.Algo.AggregateTable

/-! # Section 5.2 with the arity bounded by the original instance size

Section 15, line 4c applies the relational functors on the top domain `Γ`.
The arity is bounded by `log₂ |Ω|`, since `Ω` is identified with the
`t`-subsets of `Γ`. The tuple table and transformation monoid must therefore
use the original domain as their size witness. Both tables are built by
the existing bounded tuple iteration. Their entries, and the subsequent
`F1`, `F2`, `F3` computations, are exactly those of Section 5.2.
-/

namespace Algo
open Babai RAM RAM.Targets

/-- Arity, original domain, top domain, and relations. -/
abbrev AmbientPIn := RawAggTestInput × RawRelStruct

/-- The transformation monoid on the arity positions. -/
def ambientMon (c : ℕ) (a : AmbientPIn) : List (List ℕ) :=
  (aggTable c (a.1.1, a.1.2.1, List.range a.1.1.length)).2.map Prod.fst

def ambientIdx (c : ℕ) (a : AmbientPIn) : IdxP :=
  (pairIdxOf ((a.1.1, a.1.2.2), a.2), ambientMon c a)

/-- Section 5.2 on the top domain, with the original domain supplying the guard. -/
def ambientPipeline321 (c : ℕ) (a : AmbientPIn) : RawWL :=
  rawPipelineI (ambientIdx c a) (aggTable c a.1, a.2)

theorem quasiFun_ambientMon (c : ℕ) : QuasiFun (ambientMon c) := by
  have hk : PolyFun (fun a : AmbientPIn => a.1.1) := polyFun_fst.comp polyFun_fst
  have hn : PolyFun (fun a : AmbientPIn => a.1.2.1) :=
    (polyFun_fst.comp polyFun_snd).comp polyFun_fst
  exact ((hk.pair (hn.pair (hk.comp polyFun_rangeLength))).comp_quasiFun
    (aggQuasiFun_table c)).comp_poly (polyFun_snd.comp (PolyFun.map polyFun_fst))

theorem quasiFun_ambientIdx (c : ℕ) : QuasiFun (ambientIdx c) := by
  have hp : PolyFun (fun a : AmbientPIn => ((a.1.1, a.1.2.2), a.2)) :=
    ((polyFun_fst.comp polyFun_fst).pair
      ((polyFun_fst.comp polyFun_snd).comp polyFun_snd)).pair polyFun_snd
  exact (hp.comp polyFun_pairIdxOf).quasiFun.pair (quasiFun_ambientMon c)

/-- An unconditional RAM bound, including inputs that fail the arity guard. -/
theorem quasiFun_ambientPipeline321 (c : ℕ) : QuasiFun (ambientPipeline321 c) :=
  ((quasiFun_ambientIdx c).pair
    ((polyFun_fst.comp_quasiFun (aggQuasiFun_table c)).pair
      polyFun_snd.quasiFun)).comp_poly polyFun_rawPipelineI

theorem ambientMon_of_guard {c : ℕ} {a : AmbientPIn}
    (hg : a.1.1.length ≤ guardBound c a.1.2.1.length) :
    ambientMon c a = monIdx a.1.1.length := by
  rw [ambientMon,
    aggTable_of_guard (a := (a.1.1, a.1.2.1, List.range a.1.1.length)) hg,
    keys_tupleTable]
  rfl

theorem ambientIdx_of_guard {c : ℕ} {a : AmbientPIn}
    (hg : a.1.1.length ≤ guardBound c a.1.2.1.length) :
    ambientIdx c a = idxOf a.1.1.length := by
  rw [ambientIdx, ambientMon_of_guard hg, pairIdxOf_eq]
  rfl

theorem ambientPipeline321_of_guard {c : ℕ} {a : AmbientPIn}
    (hg : a.1.1.length ≤ guardBound c a.1.2.1.length) :
    ambientPipeline321 c a =
      rawPipeline a.1.1.length (tupleTable a.1.2.2 a.1.1.length, a.2) := by
  rw [ambientPipeline321, ambientIdx_of_guard hg, aggTable_of_guard hg]
  rfl

theorem ambientPipeline321_spec {n c : ℕ} {a : AmbientPIn}
    (hnd : a.1.2.2.Nodup) (hmem : ∀ b, b ∈ a.1.2.2 ↔ b < n)
    (hg : a.1.1.length ≤ guardBound c a.1.2.1.length)
    (x x' : Str (Fin n) a.1.1.length) :
    (decWL n a.1.1.length (ambientPipeline321 c a)).color x =
        (decWL n a.1.1.length (ambientPipeline321 c a)).color x' ↔
      (decRel n a.1.1.length a.2).F1.F2.F3.color x =
        (decRel n a.1.1.length a.2).F1.F2.F3.color x' := by
  rw [ambientPipeline321_of_guard hg]
  exact rawPipeline_spec (a := (tupleTable a.1.2.2 a.1.1.length, a.2))
    (wf_tupleTable hnd hmem) x x'

theorem ambientPipeline321_wf {n c : ℕ} {a : AmbientPIn}
    (hnd : a.1.2.2.Nodup) (hmem : ∀ b, b ∈ a.1.2.2 ↔ b < n)
    (hg : a.1.1.length ≤ guardBound c a.1.2.1.length) :
    RawWL.WF n a.1.1.length (ambientPipeline321 c a) := by
  rw [ambientPipeline321_of_guard hg]
  exact rawPipeline_wf (a := (tupleTable a.1.2.2 a.1.1.length, a.2))
    (wf_tupleTable hnd hmem)

@[simp] theorem fst_aggTable (c : ℕ) (a : RawAggTestInput) :
    (aggTable c a).1 = a.2.2 := by
  by_cases hg : a.1.length ≤ guardBound c a.2.1.length
  · rw [aggTable_of_guard hg]; rfl
  · simp [aggTable, aggTabSetUp, hg, tabRead]

@[simp] theorem fst_ambientPipeline321 (c : ℕ) (a : AmbientPIn) :
    (ambientPipeline321 c a).1 = a.1.2.2 := by
  rw [ambientPipeline321, rawPipelineI, fst_rawWLStable, rawF2I_fst, rawF1_fst,
    fst_aggTable]

end Algo

#print axioms Algo.quasiFun_ambientPipeline321
#print axioms Algo.ambientPipeline321_spec
#print axioms Algo.ambientPipeline321_wf
