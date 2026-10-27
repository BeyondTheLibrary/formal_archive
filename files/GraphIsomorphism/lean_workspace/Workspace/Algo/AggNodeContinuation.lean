import Workspace.Algo.AggNodeSideTests
import Workspace.Algo.AggNodeGuideReject

/-! # What the outcome of Theorem 13.2.1 leads to, on the RAM

After the two phases of Procedure AggregateCertificates (Sec. 13.2) the round of Sec. 15,
lines 5–7, reads the outcome off the completed stores and continues:

* outcome (1): the colored `4/5`-partition, the orbit partition of `F(z)^Γ`, for both
  strings (line 7);
* outcome (2a): Cor. 12.0.10, which is the separate continuation `top4AggregateEnter`;
* outcome (2b): the reject exit when the case test fails at `y`, and otherwise the versions
  of the binary structures `X_i` of both strings (lines 6, 6a);
* outcome (3): the reject exit when `|D(y)| ≠ |D(x)|`, the rejection of the local-guide
  constructor, and otherwise the versions of the `t`-ary structures of both strings.

`aggnContinuation` computes this dispatch as one quasipolynomial RAM routine. Its tag says
which exit was taken:

| tag | exit |
|---|---|
| 0 | reject, outcome (2b) (`Babai.Line57Data.rejectCase`) |
| 1 | outcome (1), versions `[P(x)]` and `[P(y)]` |
| 2 | outcome (2a), handed to `top4AggregateEnter` |
| 3 | outcome (2b), versions of both strings |
| 4 | outcome (3), versions of both strings |
| 5 | reject, outcome (3) (`Babai.Line57Data.rejectDefect`) |
| 6 | reject, outcome (3): a class of `∼` meets `y` and not `x` (the Local guide proposition's exit; `aggnContinuation_six_classes`) |

Each tag is proved to be taken exactly under the paper's condition, each reject is sound,
and each list of versions is nonempty and consists of Align-admissible outcomes on all of
`Γ` (for the versions of Theorem 9.2.3 this uses the hypothesis `AggnRestoredEntryGood`,
which `exists_aggnSplitFamilies` discharges for the fixed evaluators).
-/
set_option synthInstance.maxSize 2048
set_option quotPrecheck false
namespace Algo
open RAM RAM.Targets Babai Equiv MulAction

/-- The tag of the exit and the versions of `x` and of `y`. -/
abbrev AggnContOut := ℕ × (List RawAlignOutcome × List RawAlignOutcome)

/-- Outcome (1): the orbit partition of `F(z)^Γ` of each string. -/
def aggnContCaseOne (z : AggnPhaseCtx × AggnAggregateState) : AggnContOut :=
  (1,[aggnCaseOneOutcome (z,false)],[aggnCaseOneOutcome (z,true)])

/-- Outcome (2b): the versions of every member of the family of each string. -/
def aggnContCase2b (c b t d : ℕ) (z : AggnPhaseCtx × AggnAggregateState) : AggnContOut :=
  (3,aggnCase2bSplitFamily c b t d (z,false),aggnCase2bSplitFamily c b t d (z,true))

/-- Outcome (3): the versions of the two local-guide structures, or the guide rejection. -/
def aggnContCase3 (c b t d : ℕ) (z : AggnPhaseCtx × AggnAggregateState) : AggnContOut :=
  match aggnGuideSplitFamilies c b t d z with
  | none => (6,[],[])
  | some A => (4,A)

/-- §13.2 and §15, lines 5–7: **the continuation after AggregateCertificates**. The order of
the tests is the paper's: case (1), then case (2) with its sub-case (2a), then case (3). -/
def aggnContinuation (c b t d : ℕ) (z : AggnPhaseCtx × AggnAggregateState) : AggnContOut :=
  if decide (aggnAggregateDispatch z = 1) then aggnContCaseOne z
  else if decide (aggnAggregateDispatch z = 2) then
    if aggnAggregateGiantBranch z then (2,[],[])
    else if aggnRejectCase z then (0,[],[])
    else aggnContCase2b c b t d z
  else if aggnRejectDefect z then (5,[],[])
  else aggnContCase3 c b t d z

theorem aggnPolyFun_contCaseOne : PolyFun aggnContCaseOne := by
  have hx := (polyFun_id.pair (polyFun_const false)).comp aggnPolyFun_caseOneOutcome
  have hy := (polyFun_id.pair (polyFun_const true)).comp aggnPolyFun_caseOneOutcome
  have hl (f : AggnPhaseCtx × AggnAggregateState → RawAlignOutcome) (hf : PolyFun f) :
      PolyFun (fun z => [f z]) :=
    (hf.pair (polyFun_const [])).comp polyFun_cons
  exact (polyFun_const 1).pair ((hl _ hx).pair (hl _ hy))

theorem aggnQuasiFun_contCase2b (c b t d : ℕ) : QuasiFun (aggnContCase2b c b t d) :=
  (polyFun_const 3).quasiFun.pair
    (((polyFun_id.pair (polyFun_const false)).comp_quasiFun
      (aggnQuasiFun_case2bSplitFamily c b t d)).pair
    ((polyFun_id.pair (polyFun_const true)).comp_quasiFun
      (aggnQuasiFun_case2bSplitFamily c b t d)))

theorem aggnQuasiFun_contCase3 (c b t d : ℕ) : QuasiFun (aggnContCase3 c b t d) := by
  have hs : QuasiFun (fun p : (List RawAlignOutcome × List RawAlignOutcome) ×
      (AggnPhaseCtx × AggnAggregateState) => ((4 : ℕ),p.1)) :=
    ((polyFun_const 4).pair polyFun_fst).quasiFun
  exact (((aggnQuasiFun_guideSplitFamilies c b t d).pair polyFun_id.quasiFun).comp
    (QuasiFun.optionElim (quasiFun_const (6,[],[])) hs)).of_eq (fun z => by
      unfold aggnContCase3
      cases aggnGuideSplitFamilies c b t d z <;> rfl)

private theorem aggnPolyFun_dispatchIs (k : ℕ) :
    PolyFun (fun z : AggnPhaseCtx × AggnAggregateState => decide (aggnAggregateDispatch z = k)) :=
  (aggnPolyFun_aggregateDispatch.pair (polyFun_const k)).comp polyFun_natEq

/-- The whole continuation runs in quasipolynomial time on the RAM, with the evaluators of
Theorem 9.2.3 fixed once. -/
theorem aggnQuasiFun_continuation (c b t d : ℕ) : QuasiFun (aggnContinuation c b t d) :=
  QuasiFun.ite (aggnPolyFun_dispatchIs 1) aggnPolyFun_contCaseOne.quasiFun
    (QuasiFun.ite (aggnPolyFun_dispatchIs 2)
      (QuasiFun.ite aggnPolyFun_aggregateGiantBranch (quasiFun_const _)
        (QuasiFun.ite aggnPolyFun_rejectCase (quasiFun_const _) (aggnQuasiFun_contCase2b c b t d)))
      (QuasiFun.ite aggnPolyFun_rejectDefect (quasiFun_const _) (aggnQuasiFun_contCase3 c b t d)))

/-! ### Which exit is taken -/

theorem aggnContinuation_of_one {c b t d : ℕ} {z : AggnPhaseCtx × AggnAggregateState}
    (h : aggnAggregateDispatch z = 1) : aggnContinuation c b t d z = aggnContCaseOne z := by
  simp [aggnContinuation,h]

theorem aggnContinuation_of_giant {c b t d : ℕ} {z : AggnPhaseCtx × AggnAggregateState}
    (h : aggnAggregateDispatch z = 2) (hg : aggnAggregateGiantBranch z = true) :
    aggnContinuation c b t d z = (2,[],[]) := by
  simp [aggnContinuation,h,hg]

theorem aggnContinuation_of_rejectCase {c b t d : ℕ} {z : AggnPhaseCtx × AggnAggregateState}
    (h : aggnAggregateDispatch z = 2) (hg : aggnAggregateGiantBranch z = false)
    (hr : aggnRejectCase z = true) : aggnContinuation c b t d z = (0,[],[]) := by
  simp [aggnContinuation,h,hg,hr]

theorem aggnContinuation_of_case2b {c b t d : ℕ} {z : AggnPhaseCtx × AggnAggregateState}
    (h : aggnAggregateDispatch z = 2) (hg : aggnAggregateGiantBranch z = false)
    (hr : aggnRejectCase z = false) : aggnContinuation c b t d z = aggnContCase2b c b t d z := by
  simp [aggnContinuation,h,hg,hr]

theorem aggnContinuation_of_rejectDefect {c b t d : ℕ} {z : AggnPhaseCtx × AggnAggregateState}
    (h : aggnAggregateDispatch z = 3) (hr : aggnRejectDefect z = true) :
    aggnContinuation c b t d z = (5,[],[]) := by
  simp [aggnContinuation,h,hr]

theorem aggnContinuation_of_case3 {c b t d : ℕ} {z : AggnPhaseCtx × AggnAggregateState}
    (h : aggnAggregateDispatch z = 3) (hr : aggnRejectDefect z = false) :
    aggnContinuation c b t d z = aggnContCase3 c b t d z := by
  simp [aggnContinuation,h,hr]

theorem aggnAggregateCase_eq_two {p : List ℕ × RawGens} (h : aggnCase2 p = true) :
    aggnAggregateCase p = 2 := by
  have h1 : aggnCase1 p = false := by
    unfold aggnCase2 at h
    unfold aggnCase1
    cases hl : (aggnLargeOrbitPoints p).isEmpty
    · simp
    · rw [hl] at h; cases h
  simp [aggnAggregateCase,h1,h]

theorem aggnAggregateDispatch_cases (z : AggnPhaseCtx × AggnAggregateState) :
    aggnAggregateDispatch z = 1 ∨ aggnAggregateDispatch z = 2 ∨ aggnAggregateDispatch z = 3 := by
  unfold aggnAggregateDispatch aggnAggregateCase
  split
  · exact Or.inl rfl
  · split
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)

/-- The tag is one of the seven exits, and the tag alone determines which exit was taken. -/
theorem aggnContinuation_tag (c b t d : ℕ) (z : AggnPhaseCtx × AggnAggregateState) :
    ((aggnContinuation c b t d z).1 = 1 ↔ aggnAggregateDispatch z = 1) ∧
    ((aggnContinuation c b t d z).1 = 2 ↔
      aggnAggregateDispatch z = 2 ∧ aggnAggregateGiantBranch z = true) ∧
    ((aggnContinuation c b t d z).1 = 0 ↔
      aggnAggregateDispatch z = 2 ∧ aggnAggregateGiantBranch z = false ∧ aggnRejectCase z = true) ∧
    ((aggnContinuation c b t d z).1 = 3 ↔
      aggnAggregateDispatch z = 2 ∧ aggnAggregateGiantBranch z = false ∧ aggnRejectCase z = false) ∧
    ((aggnContinuation c b t d z).1 = 5 ↔
      aggnAggregateDispatch z = 3 ∧ aggnRejectDefect z = true) ∧
    ((aggnContinuation c b t d z).1 = 4 ↔ aggnAggregateDispatch z = 3 ∧
      aggnRejectDefect z = false ∧ (aggnGuideSplitFamilies c b t d z).isSome = true) ∧
    ((aggnContinuation c b t d z).1 = 6 ↔ aggnAggregateDispatch z = 3 ∧
      aggnRejectDefect z = false ∧ aggnGuideSplitFamilies c b t d z = none) := by
  rcases aggnAggregateDispatch_cases z with h | h | h
  · rw [aggnContinuation_of_one h]; simp [aggnContCaseOne,h]
  · cases hg : aggnAggregateGiantBranch z
    · cases hr : aggnRejectCase z
      · rw [aggnContinuation_of_case2b h hg hr]; simp [aggnContCase2b,h]
      · rw [aggnContinuation_of_rejectCase h hg hr]; simp [h]
    · rw [aggnContinuation_of_giant h hg]; simp [h]
  · cases hr : aggnRejectDefect z
    · rw [aggnContinuation_of_case3 h hr]
      unfold aggnContCase3
      cases aggnGuideSplitFamilies c b t d z <;> simp [h]
    · rw [aggnContinuation_of_rejectDefect h hr]; simp [h]

/-! ### The exits against the paper's conditions -/

section Spec
variable {c n m : ℕ} {C : AggnPhaseCtx} {s : AggnAggregateState}
    {ϕ : decGroup n C.1.1.2 →* Perm (Fin m)}
    (hC : AggnPhaseCtxWF c n m C ϕ) (hs : AggnStoresComplete c ϕ s.1.2.1)
include hC hs

local notation "X" => decStrN n C.2.1
local notation "Y" => decStrN n C.2.2.1
local notation "ts" => C.2.2.2.length

/-- Tag `1` is taken exactly at outcome (1) of `x`, and the versions are the orbit
partitions of `F(x)^Γ` and `F(y)^Γ`. -/
theorem aggnContinuation_one_spec (b t d : ℕ) :
    ((aggnContinuation c b t d (C,s)).1 = 1 ↔ Case1 (bigFGamma ϕ X ts)) ∧
    (Case1 (bigFGamma ϕ X ts) →
      (aggnContinuation c b t d (C,s)).2.1.map (decAlignOutcome m) =
          [some (orbitSplitOutcome (bigFGamma ϕ X ts))] ∧
        (aggnContinuation c b t d (C,s)).2.2.map (decAlignOutcome m) =
          [some (orbitSplitOutcome (bigFGamma ϕ Y ts))]) := by
  have hd := (aggnAggregateDispatch_spec hC hs).1
  refine ⟨(aggnContinuation_tag c b t d (C,s)).1.trans hd,fun h1 => ?_⟩
  rw [aggnContinuation_of_one (hd.mpr h1)]
  simp only [aggnContCaseOne,List.map_cons,List.map_nil,aggnCaseOneOutcome_decode hC hs,
    cond_false,cond_true,and_self]

/-- Tag `2` is taken exactly at outcome (2a) of `x`. -/
theorem aggnContinuation_two_spec (b t d : ℕ) :
    (aggnContinuation c b t d (C,s)).1 = 2 ↔ AggregateCase2a ϕ X ts := by
  rw [(aggnContinuation_tag c b t d (C,s)).2.1,← aggnAggregateGiantBranch_spec hC hs]
  refine ⟨fun h => h.2,fun hg => ⟨?_,hg⟩⟩
  have h2 : aggnCase2 (C.1.2.1,(aggnAggregateData ((C,s),false)).2.1) = true := by
    change (aggnCase2 _ && aggnCase2a _) = true at hg
    simp only [Bool.and_eq_true] at hg
    exact hg.1
  exact aggnAggregateCase_eq_two h2

/-- Tag `0` is taken exactly under the two hypotheses of `Babai.Line57Data.rejectCase`,
and then `Iso_G(x,y) = ∅`. -/
theorem aggnContinuation_zero_spec (b t d : ℕ) :
    ((aggnContinuation c b t d (C,s)).1 = 0 ↔
      (Case2 (bigFGamma ϕ X ts) ∧ ¬ AggregateCase2a ϕ X ts) ∧
        ¬ (Case2 (bigFGamma ϕ Y ts) ∧ ¬ AggregateCase2a ϕ Y ts)) ∧
    ((aggnContinuation c b t d (C,s)).1 = 0 →
      strIso (decGroup n C.1.1.2 : Set (Perm (Fin n))) X Y = ∅) := by
  have key : (aggnContinuation c b t d (C,s)).1 = 0 ↔ aggnRejectCase (C,s) = true := by
    rw [(aggnContinuation_tag c b t d (C,s)).2.2.1]
    constructor
    · exact fun h => h.2.2
    · intro hr
      have hx : aggnSideCase2b ((C,s),false) = true := by
        simp only [aggnRejectCase,Bool.and_eq_true] at hr; exact hr.1
      exact ⟨((aggnSideCase2b_false_iff C s).mp hx).1,((aggnSideCase2b_false_iff C s).mp hx).2,hr⟩
  exact ⟨key.trans (aggnRejectCase_spec hC hs),fun h => aggnRejectCase_iso hC hs (key.mp h)⟩

/-- Tag `3` is taken exactly when the case test of outcome (2b) holds at both strings. -/
theorem aggnContinuation_three_iff (b t d : ℕ) :
    (aggnContinuation c b t d (C,s)).1 = 3 ↔
      (Case2 (bigFGamma ϕ X ts) ∧ ¬ AggregateCase2a ϕ X ts) ∧
        (Case2 (bigFGamma ϕ Y ts) ∧ ¬ AggregateCase2a ϕ Y ts) := by
  have hx := aggnSideCase2b_spec hC hs false
  have hy := aggnSideCase2b_spec hC hs true
  simp only [cond_false,cond_true] at hx hy
  rw [(aggnContinuation_tag c b t d (C,s)).2.2.2.1,← hx,← hy,aggnSideCase2b_false_iff]
  simp only [aggnRejectCase,Bool.and_eq_false_iff,Bool.not_eq_false']
  constructor
  · rintro ⟨h2,hg,hr⟩
    have hx' : aggnSideCase2b ((C,s),false) = true := (aggnSideCase2b_false_iff C s).mpr ⟨h2,hg⟩
    rcases hr with hr | hr
    · rw [hx'] at hr; cases hr
    · exact ⟨⟨h2,hg⟩,hr⟩
  · rintro ⟨⟨h2,hg⟩,hy'⟩
    exact ⟨h2,hg,Or.inr hy'⟩

omit hs in
/-- At tag `3` both lists of versions are nonempty and consist of Align-admissible outcomes
on all of `Γ`. -/
theorem aggnContinuation_three_valid {b t d : ℕ} (hsolver : AggnRestoredEntryGood c b t d)
    (hm : 217 ≤ m) (h3 : (aggnContinuation c b t d (C,s)).1 = 3) :
    AggnSplitFamilyGood m (aggnContinuation c b t d (C,s)).2.1 ∧
      AggnSplitFamilyGood m (aggnContinuation c b t d (C,s)).2.2 := by
  obtain ⟨h2,hg,hr⟩ := (aggnContinuation_tag c b t d (C,s)).2.2.2.1.mp h3
  have hx : aggnSideCase2b ((C,s),false) = true := (aggnSideCase2b_false_iff C s).mpr ⟨h2,hg⟩
  have hy : aggnSideCase2b ((C,s),true) = true := by
    simp only [aggnRejectCase,hx,Bool.true_and,Bool.not_eq_false'] at hr
    exact hr
  rw [aggnContinuation_of_case2b h2 hg hr]
  exact ⟨aggnCase2bSplitFamily_side_valid hsolver hC hm hx,
    aggnCase2bSplitFamily_side_valid hsolver hC hm hy⟩

/-- Tag `5` is taken exactly at outcome (3) of `x` under the hypothesis of
`Babai.Line57Data.rejectDefect`, and then `Iso_G(x,y) = ∅`. -/
theorem aggnContinuation_five_spec (b t d : ℕ) :
    ((aggnContinuation c b t d (C,s)).1 = 5 ↔
      (¬ Case1 (bigFGamma ϕ X ts) ∧ ¬ Case2 (bigFGamma ϕ X ts)) ∧
        (fixedGamma ϕ Y ts).ncard ≠ (fixedGamma ϕ X ts).ncard) ∧
    ((aggnContinuation c b t d (C,s)).1 = 5 →
      strIso (decGroup n C.1.1.2 : Set (Perm (Fin n))) X Y = ∅) := by
  rw [(aggnContinuation_tag c b t d (C,s)).2.2.2.2.1,(aggnAggregateDispatch_spec hC hs).2.2,
    aggnRejectDefect_spec hC hs]
  exact ⟨Iff.rfl,fun h => strIso_eq_empty_of_ncard_fixedGamma_ne ϕ _ _ _ h.2⟩

/-- Tag `6`: at outcome (3) of `x`, with `|D(x)| = |D(y)|`, the local-guide constructor
finds no morphism of the guide category, and then `Iso_G(x,y) = ∅`
(`aggnAggregateGuide_reject`). -/
theorem aggnContinuation_six_spec (b t d : ℕ)
    (htbl : AggnCompareTableFor c ϕ (aggnCompareTable c (C,s.2.2.2.1)))
    (hset : LocalCertSetting (decGroup n C.1.1.2) ϕ)
    (ht : LargeK C.2.2.2.length (Nat.card (Fin n))) (htm : 10*C.2.2.2.length ≤ m)
    [Nonempty (Fin n)] :
    ((aggnContinuation c b t d (C,s)).1 = 6 ↔
      ((¬ Case1 (bigFGamma ϕ X ts) ∧ ¬ Case2 (bigFGamma ϕ X ts)) ∧
        (fixedGamma ϕ Y ts).ncard = (fixedGamma ϕ X ts).ncard) ∧
        aggnAggregateGuide c (C,s) = none) ∧
    ((aggnContinuation c b t d (C,s)).1 = 6 →
      strIso (decGroup n C.1.1.2 : Set (Perm (Fin n))) X Y = ∅) := by
  have hnone : aggnGuideSplitFamilies c b t d (C,s) = none ↔ aggnAggregateGuide c (C,s) = none := by
    unfold aggnGuideSplitFamilies aggnGuideEntries
    cases aggnAggregateGuide c (C,s) <;> simp
  have key := (aggnContinuation_tag c b t d (C,s)).2.2.2.2.2.2
  rw [(aggnAggregateDispatch_spec hC hs).2.2,hnone] at key
  have hrd : aggnRejectDefect (C,s) = false ↔
      (fixedGamma ϕ Y ts).ncard = (fixedGamma ϕ X ts).ncard := by
    rw [← Bool.not_eq_true,aggnRejectDefect_spec hC hs,not_not]
  rw [hrd] at key
  refine ⟨key.trans ⟨fun h => ⟨⟨h.1,h.2.1⟩,h.2.2⟩,fun h => ⟨h.1.1,h.1.2,h.2⟩⟩,fun h => ?_⟩
  exact aggnAggregateGuide_reject hC hs htbl hset ht htm (key.mp h).2.2

/-- Tag `4`: at outcome (3) of `x`, with `|D(x)| = |D(y)|` and a successful local-guide
constructor, the two lists are exactly the restored versions of the two computed
structures, and both are nonempty lists of Align-admissible outcomes on all of `Γ`. -/
theorem aggnContinuation_four_spec {b t d : ℕ} (hsolver : AggnRestoredEntryGood c b t d)
    (htbl : AggnCompareTableFor c ϕ (aggnCompareTable c (C,s.2.2.2.1)))
    (hset : LocalCertSetting (decGroup n C.1.1.2) ϕ)
    (ht : LargeK C.2.2.2.length (Nat.card (Fin n))) (htm : 10*C.2.2.2.length ≤ m)
    [Nonempty (Fin n)] (h4 : (aggnContinuation c b t d (C,s)).1 = 4) :
    (¬ Case1 (bigFGamma ϕ X ts) ∧ ¬ Case2 (bigFGamma ϕ X ts)) ∧
      (fixedGamma ϕ Y ts).ncard = (fixedGamma ϕ X ts).ncard ∧
      ∃ out,aggnAggregateGuide c (C,s) = some out ∧
        (aggnContinuation c b t d (C,s)).2 =
          aggnGuideSplitPair c b t d ((C,s),aggnGuideEntryPair ((C,s),out)) ∧
        AggnSplitFamilyGood m (aggnContinuation c b t d (C,s)).2.1 ∧
        AggnSplitFamilyGood m (aggnContinuation c b t d (C,s)).2.2 := by
  obtain ⟨h3,hr,hsome⟩ := (aggnContinuation_tag c b t d (C,s)).2.2.2.2.2.1.mp h4
  have hrd : (fixedGamma ϕ Y ts).ncard = (fixedGamma ϕ X ts).ncard := by
    by_contra hne
    rw [(aggnRejectDefect_spec hC hs).mpr hne] at hr
    cases hr
  obtain ⟨out,hout⟩ : ∃ out,aggnAggregateGuide c (C,s) = some out := by
    unfold aggnGuideSplitFamilies aggnGuideEntries at hsome
    cases h : aggnAggregateGuide c (C,s)
    · rw [h] at hsome; simp at hsome
    · exact ⟨_,rfl⟩
  have heq : (aggnContinuation c b t d (C,s)).2 =
      aggnGuideSplitPair c b t d ((C,s),aggnGuideEntryPair ((C,s),out)) := by
    rw [aggnContinuation_of_case3 h3 hr]
    unfold aggnContCase3
    rw [aggnGuideSplitFamilies_some hout]
  refine ⟨(aggnAggregateDispatch_spec hC hs).2.2.mp h3,hrd,out,hout,heq,?_,?_⟩
  · rw [heq]
    exact aggnGuideSplitPair_valid hsolver hC hs htbl hset ht htm hout h3 false
  · rw [heq]
    exact aggnGuideSplitPair_valid hsolver hC hs htbl hset ht htm hout h3 true

end Spec

end Algo
