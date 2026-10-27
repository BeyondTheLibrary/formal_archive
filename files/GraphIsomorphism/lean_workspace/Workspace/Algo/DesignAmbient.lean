import Workspace.Algo.DesignOut
import Workspace.Algo.FunctorsAmbient

/-! # Section 8.2 on a top domain

The original string domain supplies the arity bound in Section 15, line 4c.
The scan still tests lengths `0, ..., k - 1` and keeps the first returning
tuple at the least returning length. Only the guard uses the original size.
-/

namespace Algo
open Babai RAM RAM.Targets

abbrev AmbientDIn := List ℕ × DIn

def ambientScanRounds (c : ℕ) (a : AmbientDIn) : ℕ :=
  if a.2.1.1.1.length ≤ guardBound c a.1.length then a.2.1.1.1.length else 0

def ambientScanSetUp (c : ℕ) (a : AmbientDIn) : ℕ × SState :=
  (ambientScanRounds c a, ((a.2, [[]]), none))

/-- Section 8.2, lines 02–08, with a separate original-domain size witness. -/
def ambientDesignScan (c : ℕ) (a : AmbientDIn) : Option (List ℕ) :=
  (scanStep^[(ambientScanSetUp c a).1] (ambientScanSetUp c a).2).2

theorem ambientDesignScan_of_guard {c : ℕ} {a : AmbientDIn}
    (hg : a.2.1.1.1.length ≤ guardBound c a.1.length) :
    ambientDesignScan c a = ansUpTo a.2 a.2.1.1.1.length := by
  rw [ambientDesignScan, ambientScanSetUp, scanStep_iterate]
  simp only [ambientScanRounds, if_pos hg]

theorem polyFun_ambientScanRounds (c : ℕ) : PolyFun (ambientScanRounds c) := by
  have hk : PolyFun (fun a : AmbientDIn => a.2.1.1.1.length) :=
    (((polyFun_snd.comp polyFun_fst).comp polyFun_fst).comp polyFun_fst).comp polyFun_length
  have hb : PolyFun (fun a : AmbientDIn => guardBound c a.1.length) :=
    (polyFun_fst.pair polyFun_fst).comp (polyFun_guardBound c)
  exact (PolyFun.ite (hk.le hb) hk (polyFun_const 0)).of_eq (fun a => by
    by_cases hg : a.2.1.1.1.length ≤ guardBound c a.1.length <;>
      simp [ambientScanRounds, hg])

theorem polyFun_ambientScanSetUp (c : ℕ) : PolyFun (ambientScanSetUp c) :=
  (polyFun_ambientScanRounds c).pair
    ((polyFun_snd.pair (polyFun_const [[]])).pair (polyFun_const none))

theorem size_ambientScanState_le (c : ℕ) (a : AmbientDIn) (j : ℕ)
    (hj : j ≤ (ambientScanSetUp c a).1) :
    Enc.size (scanStep^[j] (ambientScanSetUp c a).2) ≤ scanSizeBound c (Enc.size a) := by
  apply size_scanIterate_le c a.2 (Enc.size a) j (size_snd_le' a)
  by_cases hg : a.2.1.1.1.length ≤ guardBound c a.1.length
  · have hj' : j ≤ a.2.1.1.1.length := by
      simpa [ambientScanSetUp, ambientScanRounds, hg] using hj
    have hn : a.1.length ≤ Enc.size a := (length_le_size _).trans (size_fst_le' a)
    exact (hj'.trans hg).trans (Nat.pow_le_pow_left
      (Nat.add_le_add_right (Nat.log_mono_right hn) 1) c)
  · have hj' : j = 0 := by simpa [ambientScanSetUp, ambientScanRounds, hg] using hj
    subst j
    exact Nat.zero_le _

theorem quasiFun_ambientDesignScan (c : ℕ) : QuasiFun (ambientDesignScan c) := by
  have hstep : QuasiFun (fun x : ℕ × SState => (x.1 - 1, scanStep x.2)) :=
    ((polyFun_fst.sub (polyFun_const 1)).pair (polyFun_snd.comp polyFun_scanStep)).quasiFun
  refine (QuasiFun.iterateSetup (q := fun n => n) (p := scanSizeBound c)
    (polyFun_ambientScanSetUp c).quasiFun hstep polyFun_snd.quasiFun ?_
    polyBound_id.quasiPoly (size_ambientScanState_le c)
    (quasiPolyBound_scanSizeBound c)).of_eq (fun _ => rfl)
  intro a
  have hk : a.2.1.1.1.length ≤ Enc.size a :=
    (length_le_size _).trans ((size_fst_le' a.2.1.1).trans
      ((size_fst_le' a.2.1).trans ((size_fst_le' a.2).trans (size_snd_le' a))))
  by_cases hg : a.2.1.1.1.length ≤ guardBound c a.1.length <;>
    simp only [ambientScanSetUp, ambientScanRounds, hg, if_true, if_false]
  · exact hk
  · exact Nat.zero_le _

section ScanSpec

variable {n k a b c : ℕ} {ks x₀ base : List ℕ} {p : RawWL}

theorem ambientDesignScan_some {α : ℝ} (h : RawWL.WF n k p)
    (hk : ks.length = k) (hb : 0 < b) (hab : α = (a : ℝ) / (b : ℝ))
    (hg : ks.length ≤ guardBound c base.length) {xs : List ℕ}
    (hs : ambientDesignScan c (base, (((ks, x₀), p), (a, b))) = some xs) :
    ∃ l, ∃ hl : l < k, ∃ x : Str (Fin n) l, tupleOf x = xs ∧
      KAryPartStruct.Returns α (decWL n k p) hl.le x ∧
      ∀ (l' : ℕ) (_ : l' < l), ∀ y : Str (Fin n) l',
        ¬ KAryPartStruct.Returns α (decWL n k p) (by omega : l' ≤ k) y := by
  rw [ambientDesignScan_of_guard hg] at hs
  obtain ⟨l, hl, hsc, hmin⟩ := ansUpTo_eq_some hs
  rw [hk] at hl
  obtain ⟨x, hx, hret⟩ := scanLen_some (x₀ := x₀) h hk hl.le hb hab hsc
  exact ⟨l, hl, x, hx, hret, fun l' hl' y =>
    (scanLen_none_iff (x₀ := x₀) h hk (by omega) hb hab).1 (hmin l' hl') y⟩

theorem ambientDesignScan_none_iff {α : ℝ} (h : RawWL.WF n k p)
    (hk : ks.length = k) (hb : 0 < b) (hab : α = (a : ℝ) / (b : ℝ))
    (hg : ks.length ≤ guardBound c base.length) :
    ambientDesignScan c (base, (((ks, x₀), p), (a, b))) = none ↔
      ∀ l, ¬ KAryPartStruct.ReturnsAt α (decWL n k p) l := by
  rw [ambientDesignScan_of_guard hg, ansUpTo_eq_none_iff, hk]
  constructor
  · rintro hall l ⟨hl, x, hx⟩
    exact (scanLen_none_iff (x₀ := x₀) h hk hl.le hb hab).1 (hall l hl) x hx
  · intro hno l hl
    exact (scanLen_none_iff (x₀ := x₀) h hk hl.le hb hab).2
      (fun x hx => hno l ⟨hl, x, hx⟩)

end ScanSpec

abbrev AmbientGIn := AmbientPIn × (ℕ × ℕ)

/-- Refine once, then supply the table to the scan and its result reader. -/
def ambientDesignAt (c : ℕ) (g : AmbientGIn) (xs : List ℕ) : DIn :=
  (((g.1.1.1, xs), ambientPipeline321 c g.1), g.2)

def ambientDesignProcedure (c : ℕ) (g : AmbientGIn) : Option (List ℕ) :=
  ambientDesignScan c (g.1.1.2.1, ambientDesignAt c g [])

def ambientDesignOutcome (c : ℕ) (g : AmbientGIn) : Option (List ℕ × (List ℕ × ℕ)) :=
  (ambientDesignProcedure c g).elim none
    (fun xs => some (designOutRaw (ambientDesignAt c g xs)))

theorem ambientDesignOutcome_of_some {c : ℕ} {g : AmbientGIn} {xs : List ℕ}
    (hs : ambientDesignProcedure c g = some xs) :
    ambientDesignOutcome c g = some (designOutRaw (ambientDesignAt c g xs)) := by
  rw [ambientDesignOutcome, hs]; rfl

theorem ambientDesignOutcome_of_none {c : ℕ} {g : AmbientGIn}
    (hs : ambientDesignProcedure c g = none) : ambientDesignOutcome c g = none := by
  rw [ambientDesignOutcome, hs]; rfl

theorem quasiFun_ambientDesignAt (c : ℕ) :
    QuasiFun (fun g : AmbientGIn => ambientDesignAt c g []) :=
  (((((polyFun_fst.comp polyFun_fst).comp polyFun_fst).pair
    (polyFun_const ([] : List ℕ))).quasiFun.pair
      (polyFun_fst.comp_quasiFun (quasiFun_ambientPipeline321 c))).pair polyFun_snd.quasiFun)

theorem quasiFun_ambientDesignProcedure (c : ℕ) : QuasiFun (ambientDesignProcedure c) :=
  (((((polyFun_fst.comp polyFun_fst).comp polyFun_snd).comp polyFun_fst).quasiFun.pair
    (quasiFun_ambientDesignAt c)).comp (quasiFun_ambientDesignScan c))

theorem quasiFun_ambientDesignOutcome (c : ℕ) : QuasiFun (ambientDesignOutcome c) := by
  have hpair := (quasiFun_ambientDesignProcedure c).pair (quasiFun_ambientDesignAt c)
  have hh : QuasiFun (fun q : List ℕ × DIn =>
      some (designOutRaw (withStr (q.2, q.1)))) :=
    (((polyFun_snd.pair polyFun_fst).comp polyFun_withStr).comp polyFun_designOutRaw
      |>.comp polyFun_some).quasiFun
  exact (hpair.comp (QuasiFun.optionElim (quasiFun_const none) hh)).of_eq (fun g => by
    unfold ambientDesignOutcome
    cases ambientDesignProcedure c g <;> rfl)

section Whole

variable {n k a b c : ℕ} {ks base dom : List ℕ} {rels : RawRelStruct}

theorem ambientDesignProcedure_some {α : ℝ}
    (hnd : dom.Nodup) (hmem : ∀ u, u ∈ dom ↔ u < n) (hk : ks.length = k)
    (hb : 0 < b) (hab : α = (a : ℝ) / (b : ℝ))
    (hg : ks.length ≤ guardBound c base.length) {xs : List ℕ}
    (hs : ambientDesignProcedure c (((ks, base, dom), rels), (a, b)) = some xs) :
    ∃ l, ∃ hl : l < k, ∃ x : Str (Fin n) l, tupleOf x = xs ∧
      KAryPartStruct.Returns α (decRel n k rels).F1.F2.F3 hl.le x ∧
      ∀ (l' : ℕ) (_ : l' < l), ∀ y : Str (Fin n) l',
        ¬ KAryPartStruct.Returns α (decRel n k rels).F1.F2.F3 (by omega : l' ≤ k) y := by
  subst k
  have hwf := ambientPipeline321_wf (a := ((ks, base, dom), rels)) hnd hmem hg
  have hcl := ambientPipeline321_spec (a := ((ks, base, dom), rels)) hnd hmem hg
  obtain ⟨l, hl, x, hx, hret, hmin⟩ :=
    ambientDesignScan_some (x₀ := []) hwf rfl hb hab hg hs
  exact ⟨l, hl, x, hx, (returns_congr hcl hl.le x).1 hret,
    fun l' hl' y hc => hmin l' hl' y ((returns_congr hcl (by omega) y).2 hc)⟩

theorem ambientDesignProcedure_none_iff {α : ℝ}
    (hnd : dom.Nodup) (hmem : ∀ u, u ∈ dom ↔ u < n) (hk : ks.length = k)
    (hb : 0 < b) (hab : α = (a : ℝ) / (b : ℝ))
    (hg : ks.length ≤ guardBound c base.length) :
    ambientDesignProcedure c (((ks, base, dom), rels), (a, b)) = none ↔
      ∀ l, ¬ KAryPartStruct.ReturnsAt α (decRel n k rels).F1.F2.F3 l := by
  subst k
  have hwf := ambientPipeline321_wf (a := ((ks, base, dom), rels)) hnd hmem hg
  have hcl := ambientPipeline321_spec (a := ((ks, base, dom), rels)) hnd hmem hg
  rw [ambientDesignProcedure, ambientDesignAt,
    ambientDesignScan_none_iff hwf rfl hb hab hg]
  apply forall_congr'
  intro l
  apply not_congr
  change (∃ hl : l < ks.length, ∃ x, KAryPartStruct.Returns α _ hl.le x) ↔
    ∃ hl : l < ks.length, ∃ x, KAryPartStruct.Returns α _ hl.le x
  exact exists_congr (fun hl => exists_congr (fun x => returns_congr hcl hl.le x))

open scoped Classical in
/-- **Lines 05 and 08.**  The procedure returns the objects of Theorem 8.1.5 at a string `x⃗` of
distinct vertices of least returning length `ℓ ≤ k − 1`: the vertex coloring of `X_x⃗` over the
vertex list, the dominant class `C(x⃗)`, and the rank of the `2`-skeleton `(X_x⃗)^{(2)}` induced
on `C(x⃗)` (the number line 07 compares with `2`). -/
theorem ambientDesignOutcome_spec {α : ℝ} {rels : RawRelStruct} (hnd : dom.Nodup)
    (hmem : ∀ c, c ∈ dom ↔ c < n) (hk : ks.length = k) (hb : 0 < b)
    (hab : α = (a : ℝ) / (b : ℝ)) (hg : ks.length ≤ guardBound c base.length)
    {w : List ℕ × (List ℕ × ℕ)}
    (hs : ambientDesignOutcome c (((ks, base, dom), rels), (a, b)) = some w) :
    ∃ (xs : List ℕ) (l : ℕ) (hl : l < k) (x : Str (Fin n) l),
      tupleOf x = xs ∧ w = designOutRaw (ambientDesignAt c (((ks, base, dom), rels), (a, b)) xs) ∧
      Babai.KAryPartStruct.Returns α (decRel n k rels).F1.F2.F3 hl.le x ∧
      (∀ (l' : ℕ) (_ : l' < l), ∀ y : Str (Fin n) l',
        ¬ Babai.KAryPartStruct.Returns α (decRel n k rels).F1.F2.F3
            (by omega : l' ≤ k) y) ∧
      (∀ u : Fin n, restrVColorAt (ambientDesignAt c (((ks, base, dom), rels), (a, b)) xs, (u : ℕ))
        = ((decWL n k (ambientPipeline321 c ((ks, base, dom), rels))).restrTo hl.le x).vcolor u) ∧
      (∀ u : Fin n, (u : ℕ) ∈ w.2.1 ↔ u ∈ Babai.KAryPartStruct.dominantClass α
        ((decWL n k (ambientPipeline321 c ((ks, base, dom), rels))).restrTo hl.le x)) ∧
      (∀ _ : l + 2 ≤ k, w.2.2 =
        ((((decWL n k (ambientPipeline321 c ((ks, base, dom), rels))).restrTo hl.le x).skel2
            (by omega)).induced
          (Babai.KAryPartStruct.dominantClass α
            ((decWL n k (ambientPipeline321 c ((ks, base, dom), rels))).restrTo hl.le x))).rank) := by
  classical
  have hwf : RawWL.WF n k (ambientPipeline321 c ((ks, base, dom), rels)) :=
    by subst k; exact ambientPipeline321_wf (a := ((ks, base, dom), rels)) hnd hmem hg
  cases hp : ambientDesignProcedure c (((ks, base, dom), rels), (a, b)) with
  | none => rw [ambientDesignOutcome_of_none hp] at hs; exact absurd hs (by simp)
  | some xs =>
      obtain ⟨l, hl, x, hx, hret, hmin⟩ :=
        ambientDesignProcedure_some (n := n) (rels := rels) hnd hmem hk hb hab hg hp
      have hw : w = designOutRaw (ambientDesignAt c (((ks, base, dom), rels), (a, b)) xs) := by
        rw [ambientDesignOutcome_of_some hp] at hs
        exact (Option.some.inj hs).symm
      have hz : ambientDesignAt c (((ks, base, dom), rels), (a, b)) xs
          = (((ks, tupleOf x), ambientPipeline321 c ((ks, base, dom), rels)), (a, b)) := by
        rw [ambientDesignAt, hx]
      refine ⟨xs, l, hl, x, hx, hw, hret, hmin, ?_, ?_, ?_⟩
      · intro u
        rw [hz]
        exact restrVColorAt_spec hk hl.le x u
      · intro u
        rw [hw]
        show (u : ℕ) ∈ dominantList (ambientDesignAt c (((ks, base, dom), rels), (a, b)) xs) ↔ _
        rw [hz]
        exact mem_dominantList hwf hk hl.le x hb hab u
      · intro h2
        rw [hw]
        show cliqueRank (ambientDesignAt c (((ks, base, dom), rels), (a, b)) xs) = _
        rw [hz]
        exact cliqueRank_spec hwf hk hl.le h2 x hb hab

end Whole
end Algo

#print axioms Algo.quasiFun_ambientDesignOutcome
#print axioms Algo.ambientDesignProcedure_some
#print axioms Algo.ambientDesignProcedure_none_iff

#print axioms Algo.ambientDesignOutcome_spec
