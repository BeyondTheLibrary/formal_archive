/-
An explicit running time for Theorem 1.1.1 (Babai, version 2.5): line 4c of the Master
(Sec. 15), bounded at an external degree. Not part of the faithful formalization.
-/
import Workspace.Explicit.S9Family
import Workspace.Algo.PrimitiveLine4cSpec
import Workspace.Algo.PrimitiveLine4cRoute
import Workspace.Algo.PrimitiveLine4d
import Workspace.Algo.TopMasterRecursionCameron

/-!
# Line 4c, bounded at the degree

`Explicit.TN.line4cVersions`: line 4c of the Master (the Extended Design Lemma, Theorem 9.2.3,
on the relational structures of `H(x)` and `H(y)`), and the header of line 4d built on it
(`Explicit.TN.line4dHdr`), at a node of route 4 whose window has at most `n` points.

The relational structures list the injective tuples of arity `t ≤ log₂ n` of an `m`-set, so
they may be quasipolynomially large; Theorem 9.2.3 needs only the number of points `m ≤ n`
and the threshold `3/4` to be small (`Explicit.ExtPre`). Both structures satisfy the input
facts of Theorem 9.2.3 without the defect hypothesis (`Explicit.extRepW_line4c`); the machine
builds the versions of both, whatever the defect of `H(y)`.
-/

namespace Explicit

open RAM Algo Babai Equiv

/-! ## The input facts of Theorem 9.2.3 at line 4c -/

/-- **Line 4c: the structure is an input of the machine of Theorem 9.2.3**, as
`Algo.extendedInputRep_line4c` without the defect hypothesis. -/
theorem extRepW_line4c {n m t : ℕ} {p : RawAction} {ϕ : decGroup n p.1.2 →* Perm (Fin m)}
    (hp : RawAction.WF n m p ϕ) (id : PrimitiveCaseId ϕ t) (x y z : RawStr) :
    TN.ExtRepW 1 m (line4cAmbient (((p, x, y), t), z)) := by
  have hlen := line4cArity_length hp id x y
  have h4 := id.four_t
  rw [Fintype.card_fin] at h4
  refine ⟨List.nodup_range, fun i => ?_, ?_, by change 0 < 4; norm_num, ?_⟩
  · change i ∈ List.range p.2.1.length ↔ i < m
    rw [List.mem_range, hp.2.1]
  · change (line4cArity ((p, x, y), t)).length ≤ guardBound 1 (List.range p.1.1.length).length
    rw [hlen, List.length_range, hp.1]
    exact primitiveCase_arity_guard id
  · change (3 : ℝ) / 4 ≤ ((3 : ℕ) : ℝ) / ((4 : ℕ) : ℝ)
    norm_num

theorem size_three_four : Enc.size ((3, 4) : ℕ × ℕ) ≤ 64 := by
  have h := Combine.size_pair_le (3 : ℕ) (4 : ℕ)
  rw [Small.size_nat, Small.size_nat] at h
  have h3 : Nat.size 3 ≤ 3 := size_le_self 3
  have h4 : Nat.size 4 ≤ 4 := size_le_self 4
  change Enc.size ((3, 4) : ℕ × ℕ) ≤ _ at h
  omega

namespace TN

/-! ## The relational structures -/

/-- The tuple table of the relations of line 4c, on the Ω-list and the `m` points. -/
theorem primitiveRelations (c : ℕ) :
    TN (Algo.primitiveRelations c)
      (fun n p => AggTablePre c n (p.1.2, p.1.1.1.1.1, List.range p.1.1.1.2.1.length)) (c + 1) := by
  have hp : PolyFun (fun p : RawPrimitiveRelIn => p.1.1) :=
    polyFun_fst.comp polyFun_fst
  have ha := hp.comp polyFun_fst
  have hd := (ha.comp polyFun_fst).comp polyFun_fst
  have ht := ((ha.comp polyFun_snd).comp polyFun_fst).comp polyFun_rangeLength
  have htab : TN (fun p : RawPrimitiveRelIn => (Algo.aggTable c (p.1.2, p.1.1.1.1.1,
      List.range p.1.1.1.2.1.length)).2.map Prod.fst)
      (fun n p => AggTablePre c n (p.1.2, p.1.1.1.1.1, List.range p.1.1.1.2.1.length))
      (c + 1) :=
    (poly_comp ((polyFun_fst.comp polyFun_snd).pair (hd.pair ht)) (aggTable c)).comp_poly
      (polyFun_snd.comp (PolyFun.map polyFun_fst))
  exact (((ofPoly hp _ _).pair htab).pair (ofPoly polyFun_snd _ _)).comp_poly
    (PolyFun.mapParam polyFun_primitiveRelRows) |>.of_eq
      (fun p => by unfold Algo.primitiveRelations; rfl)

/-- The precondition of the table of line 4c at degree `n`. -/
def L4cTabPre (n : ℕ) (z : RawLine4cIn) : Prop :=
  AggTablePre 1 n (line4cArity z, z.1.1.1.1, List.range z.1.1.2.1.length)

theorem line4cAmbient :
    TN Algo.line4cAmbient (fun n z => L4cTabPre n z.1) 2 := by
  have hact : PolyFun (fun z : RawLine4cIn × RawStr => z.1.1.1) :=
    (polyFun_fst.comp polyFun_fst).comp polyFun_fst
  have hks : PolyFun (fun z : RawLine4cIn × RawStr => line4cArity z.1) :=
    polyFun_fst.comp polyFun_line4cArity
  have hbase : PolyFun (fun z : RawLine4cIn × RawStr => List.range z.1.1.1.1.1.length) :=
    ((hact.comp polyFun_fst).comp polyFun_fst).comp polyFun_rangeLength
  have hdom : PolyFun (fun z : RawLine4cIn × RawStr => List.range z.1.1.1.2.1.length) :=
    ((hact.comp polyFun_snd).comp polyFun_fst).comp polyFun_rangeLength
  have hpal : PolyFun (fun z : RawLine4cIn × RawStr => line4cPalette z.1.1) :=
    (polyFun_fst.comp polyFun_fst).comp polyFun_line4cPalette
  have hrel : TN (fun z : RawLine4cIn × RawStr => Algo.primitiveRelations 1
      (((z.1.1.1, z.2), line4cArity z.1), line4cPalette z.1.1)) (fun n z => L4cTabPre n z.1) 2 :=
    poly_comp (((hact.pair polyFun_snd).pair hks).pair hpal) (primitiveRelations 1)
  exact (((ofPoly (hks.pair (hbase.pair hdom)) _ _).pair hrel).pair
    (ofPoly (polyFun_const ((3, 4) : ℕ × ℕ)) _ _)).of_eq
    (fun z => by unfold Algo.line4cAmbient; rfl)

/-- The precondition of line 4c at degree `n`: the table meets its precondition, and both
structures are inputs of Theorem 9.2.3 at degree `n`. -/
def L4cPre (n : ℕ) (z : RawLine4cIn) : Prop :=
  L4cTabPre n z ∧ ExtPre 1 n (Algo.line4cAmbient (z, z.1.2.1)) ∧
    ExtPre 1 n (Algo.line4cAmbient (z, z.1.2.2))

/-- **Line 4c** (`Algo.line4cVersions`), bounded at the degree. -/
theorem line4cVersions (c tt dd k : ℕ) (h2 : 2 ≤ k) (hk : max (c + 2) 4 ≤ k)
    (ht : tt + 2 ≤ k) :
    TN (Algo.line4cVersions c tt dd) L4cPre k := by
  have hamb := line4cAmbient.mono_k h2
  have hx : TN (fun z : RawLine4cIn => Algo.extendedSplitFamily 1 c tt dd
      (Algo.line4cAmbient (z, z.1.2.1))) L4cPre k :=
    ((poly_comp (polyFun_id.pair ((polyFun_fst.comp polyFun_snd).comp polyFun_fst)) hamb).restrict
      (Pre' := L4cPre) (fun n z h => h.1)).comp (extendedSplitFamily 1 c tt dd k (by omega) hk ht)
      (fun n z h => h.2.1)
  have hy : TN (fun z : RawLine4cIn => Algo.extendedSplitFamily 1 c tt dd
      (Algo.line4cAmbient (z, z.1.2.2))) L4cPre k :=
    ((poly_comp (polyFun_id.pair ((polyFun_fst.comp polyFun_snd).comp polyFun_snd)) hamb).restrict
      (Pre' := L4cPre) (fun n z h => h.1)).comp (extendedSplitFamily 1 c tt dd k (by omega) hk ht)
      (fun n z h => h.2.2)
  exact (hx.pair hy).of_eq (fun z => by unfold Algo.line4cVersions; rfl)

/-! ## Route 4 of the Master -/

/-- A node of route 4 at degree `n`: a good hint, route 4, and a window of at most `n` points. -/
def R4Good (n : ℕ) (q : MasterHintInput) : Prop :=
  MasterHintGood q ∧ masterHintRoute q = 4 ∧ (masterHintTop q).1.1.1.length ≤ n

theorem R4Good.l4cPre {n : ℕ} {q : MasterHintInput} (h : R4Good n q) :
    L4cPre n (masterLine4cInput q) := by
  obtain ⟨hg, hr, hΩ⟩ := h
  obtain ⟨m, ϕ, B, hB, hp, hG, hϕ, -, -, -, -, -, hn⟩ := hg
  obtain ⟨-, id, -, -, hmn, -⟩ := masterLine4c_facts q hp hG hϕ hn hr
  have hΩ' : (masterHintTop q).1.1.1.length = (masterHintTop q).1.1.1.length := rfl
  have hm : (masterHintTop q).1.2.1.length = m := hp.2.1
  have hs := size_three_four
  have hext : ∀ z, ExtPre 1 n (Algo.line4cAmbient (masterLine4cInput q, z)) := by
    intro z
    refine ⟨⟨m, by omega, extRepW_line4c hp id _ _ z⟩, by
      change Enc.size ((3, 4) : ℕ × ℕ) ≤ n; omega, ?_⟩
    change (List.range (masterHintTop q).1.1.1.length).length ≤ n
    rw [List.length_range]; exact hΩ
  refine ⟨⟨hΩ, fun _ => ?_⟩, hext _, hext _⟩
  change (List.range (masterHintTop q).1.2.1.length).length ≤ n
  rw [List.length_range]; omega

variable (c tt dd k : ℕ) (h2 : 2 ≤ k) (hk : max (c + 2) 4 ≤ k) (ht : tt + 2 ≤ k)
include h2 hk ht

theorem masterLine4cVersions :
    TN (fun q => Algo.line4cVersions c tt dd (masterLine4cInput q)) R4Good k :=
  (poly_comp polyFun_masterLine4cInput (line4cVersions c tt dd k h2 hk ht)).restrict
    (fun n q h => h.l4cPre)

theorem line4dFixed : TN (Algo.line4dFixed c tt dd) R4Good k := by
  have hg : PolyFun (fun p : MasterHintInput => (masterHintTop p).1.2.1) :=
    polyFun_masterHintTop.comp ((polyFun_fst.comp polyFun_snd).comp polyFun_fst)
  have hin : TN (fun p : MasterHintInput => ((masterHintTop p).1.2.1,
      (Algo.line4cVersions c tt dd (masterLine4cInput p)).1)) R4Good k :=
    (ofPoly hg _ _).pair ((masterLine4cVersions c tt dd k h2 hk ht).comp_poly polyFun_fst)
  exact ((hin.comp_poly (polyFun_rawVersDedup.comp polyFun_headOption)).pair
    (ofPoly (polyFun_const ((none, none) : RawAlignOutcome)) _ _)).comp_poly
      polyFun_optionGetD |>.of_eq (fun _ => by
        rw [Algo.line4dFixed, List.headD_eq_head?_getD])

theorem line4dYs : TN (Algo.line4dYs c tt dd) R4Good k := by
  have hT := polyFun_masterHintTop
  have hd : PolyFun (fun p : MasterHintInput =>
      primitiveSmallDefect ((masterHintTop p).1, (masterHintTop p).2.2)) :=
    (hT.comp (polyFun_fst.pair (polyFun_snd.comp polyFun_snd))).comp
      polyFun_primitiveSmallDefect
  have hg : PolyFun (fun p : MasterHintInput => (masterHintTop p).1.2.1) :=
    hT.comp ((polyFun_fst.comp polyFun_snd).comp polyFun_fst)
  have hin : TN (fun p : MasterHintInput => ((masterHintTop p).1.2.1,
      (Algo.line4cVersions c tt dd (masterLine4cInput p)).2)) R4Good k :=
    (ofPoly hg _ _).pair ((masterLine4cVersions c tt dd k h2 hk ht).comp_poly polyFun_snd)
  exact (ite hd (ofPoly (polyFun_const []) (fun _ _ => True) k)
    (hin.comp_poly polyFun_rawVersDedup) (fun _ _ _ _ => trivial) (fun _ _ h _ => h)).of_eq
    (fun _ => rfl)

theorem line4dLab : TN (Algo.line4dLab c tt dd) R4Good k := by
  have hg : PolyFun (fun p : MasterHintInput => (masterHintTop p).1.2.1) :=
    polyFun_masterHintTop.comp ((polyFun_fst.comp polyFun_snd).comp polyFun_fst)
  exact (((ofPoly hg _ _).pair (line4dFixed c tt dd k h2 hk ht)).comp_poly
    polyFun_alignOutcomeLab).of_eq (fun _ => rfl)

theorem line4dHasDom : TN (Algo.line4dHasDom c tt dd) R4Good k := by
  have hP : PolyFun (fun q : RawAction × RawAlignOutcome =>
      alignRHasDom (alignRColorOf q) && decide (2 ≤ alignRMs q)) :=
    polyFun_and (polyFun_alignRColorOf.comp polyFun_alignRHasDom)
      ((polyFun_const 2).le polyFun_alignRMs)
  exact (((ofPoly (polyFun_masterHintTop.comp polyFun_fst) _ _).pair
    (line4dFixed c tt dd k h2 hk ht)).comp_poly hP).of_eq (fun _ => rfl)

/-- **The header of line 4d** (Eq. (71)), bounded at the degree at a node of route 4. -/
theorem line4dHdr : TN (Algo.line4dHdr c tt dd) R4Good k := by
  have hT := polyFun_masterHintTop
  have hA : PolyFun (fun p : MasterHintInput => (masterHintTop p).1) := hT.comp polyFun_fst
  have hW : TN (fun p : MasterHintInput =>
      alignRWindows ((masterHintTop p).1, Algo.line4dLab c tt dd p)) R4Good k :=
    ((ofPoly hA _ _).pair (line4dLab c tt dd k h2 hk ht)).comp_poly polyFun_alignRWindows
  exact ((ofPoly hA _ _).pair ((line4dFixed c tt dd k h2 hk ht).pair
    ((line4dYs c tt dd k h2 hk ht).pair (hW.pair
      ((ofPoly (hT.comp (polyFun_snd.comp polyFun_fst)) _ _).pair
        (ofPoly (hT.comp (polyFun_snd.comp polyFun_snd)) _ _)))))).of_eq (fun _ => rfl)

end TN

end Explicit
