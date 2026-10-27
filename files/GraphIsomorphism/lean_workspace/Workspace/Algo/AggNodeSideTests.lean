import Workspace.Algo.AggNodeSplitFamilies
import Workspace.Master.Line56a7a

/-! # The Section 13.2 tests at either string, and the two reject exits

Theorem 13.2.1 (v2.5, Sec. 13.2, pp. 92–94) reads its case distinction off `F(x)^Γ` and
ignores `y` ("Below we ignore `y` and focus on `x`"). The branch of Sec. 15, lines 5–7,
still has to decide what to do when `y` does not follow `x`, and the mathematical side has
two exits for that (`Babai.Line57Data.rejectCase`, `Babai.Line57Data.rejectDefect`):

* outcome (2b): the case test "case (2) and not case (2a)" holds at `x` and fails at `y`;
* outcome (3): `|D(y)| ≠ |D(x)|`.

This file computes the case (2b) test at either string, both reject tests, and proves that
each is exactly the condition the mathematical exit carries, and that each rejection is
sound (`Iso_G(x,y) = ∅`). It also restates the Case 2b facts, entries and split families of
`AggNodeCase2bFacts`, `AggNodeRecursiveEntries` and `AggNodeSplitFamilies` for either
string, because Procedure Align needs the versions of `y` as well as those of `x`.
-/
set_option synthInstance.maxSize 2048
namespace Algo
open RAM RAM.Targets Babai Equiv MulAction

/-- §13.2, **the test of outcome (2b) at the string selected by the bit**: case (2) holds
("`F^Γ` has an orbit of length `> 4m/5`") and case (2a) fails. -/
def aggnSideCase2b (z : (AggnPhaseCtx × AggnAggregateState) × Bool) : Bool :=
  aggnCase2 (aggnAggregateImage z) && !aggnCase2a (aggnAggregateImage z)

private theorem aggnPolyFun_bnot {γ : Type*} [Enc γ] {f : γ → Bool} (hf : PolyFun f) :
    PolyFun (fun z => !f z) :=
  (PolyFun.ite hf (polyFun_const false) (polyFun_const true)).of_eq (fun z => by
    cases f z <;> rfl)

theorem aggnPolyFun_sideCase2b : PolyFun aggnSideCase2b :=
  wftPolyFun_and (aggnPolyFun_aggregateImage.comp aggnPolyFun_case2)
    (aggnPolyFun_bnot (aggnPolyFun_aggregateImage.comp aggnPolyFun_case2a))

theorem aggnSideCase2b_iff (z : (AggnPhaseCtx × AggnAggregateState) × Bool) :
    aggnSideCase2b z = true ↔
      aggnCase2 (aggnAggregateImage z) = true ∧ aggnCase2a (aggnAggregateImage z) = false := by
  simp only [aggnSideCase2b, Bool.and_eq_true, Bool.not_eq_true']

/-- On the first string the side test is the conjunction the existing Case 2b lemmas take:
the dispatch is `2` and the giant branch is not taken. -/
theorem aggnSideCase2b_false_iff (C : AggnPhaseCtx) (s : AggnAggregateState) :
    aggnSideCase2b ((C,s),false) = true ↔
      aggnAggregateDispatch (C,s) = 2 ∧ aggnAggregateGiantBranch (C,s) = false := by
  rw [aggnSideCase2b_iff]
  change aggnCase2 (C.1.2.1,(aggnAggregateData ((C,s),false)).2.1) = true ∧
      aggnCase2a (C.1.2.1,(aggnAggregateData ((C,s),false)).2.1) = false ↔
    aggnAggregateCase (C.1.2.1,(aggnAggregateData ((C,s),false)).2.1) = 2 ∧
      (aggnCase2 (C.1.2.1,(aggnAggregateData ((C,s),false)).2.1) &&
        aggnCase2a (C.1.2.1,(aggnAggregateData ((C,s),false)).2.1)) = false
  generalize (C.1.2.1,(aggnAggregateData ((C,s),false)).2.1) = p
  unfold aggnAggregateCase aggnCase1
  cases h2 : aggnCase2 p <;> cases h2a : aggnCase2a p <;>
    simp_all [aggnCase2] <;> split <;> simp

section Spec
variable {c n m : ℕ} {C : AggnPhaseCtx} {s : AggnAggregateState}
    {ϕ : decGroup n C.1.1.2 →* Perm (Fin m)}

/-- The side test is the paper's case test of outcome (2b) at `x` (bit `false`) or `y`
(bit `true`). -/
theorem aggnSideCase2b_spec (hC : AggnPhaseCtxWF c n m C ϕ)
    (hs : AggnStoresComplete c ϕ s.1.2.1) (b : Bool) :
    aggnSideCase2b ((C,s),b) = true ↔
      Case2 (bigFGamma ϕ (cond b (decStrN n C.2.2.1) (decStrN n C.2.1)) C.2.2.2.length) ∧
        ¬ AggregateCase2a ϕ (cond b (decStrN n C.2.2.1) (decStrN n C.2.1)) C.2.2.2.length := by
  have hw : RawGens.WF m (aggnAggregateData ((C,s),b)).2.1 := wf_tidyGens hC.action.2.1 _
  have hd := (aggnAggregateData_spec hC hs b).2.1
  have h2 := aggnCase2_spec hC.action.2.1 hw
  have h2a := aggnCase2a_orbit_spec hC.action.2.1 hw
  rw [hd] at h2 h2a
  have h2a' : (aggnCase2 (aggnAggregateImage ((C,s),b)) = true ∧
      aggnCase2a (aggnAggregateImage ((C,s),b)) = true) ↔
      AggregateCase2a ϕ (cond b (decStrN n C.2.2.1) (decStrN n C.2.1)) C.2.2.2.length := by
    change (aggnCase2 (C.1.2.1,_) = true ∧ aggnCase2a (C.1.2.1,_) = true) ↔ _
    rw [h2a]
    simp only [AggregateCase2a, Fintype.card_fin]
  rw [aggnSideCase2b_iff]
  change aggnCase2 (C.1.2.1,_) = true ∧ _ ↔ _
  rw [h2]
  constructor
  · rintro ⟨hc, hg⟩
    refine ⟨hc, fun ha => ?_⟩
    have := (h2a'.mpr ha).2
    rw [this] at hg
    cases hg
  · rintro ⟨hc, hna⟩
    refine ⟨hc, ?_⟩
    cases hg : aggnCase2a (aggnAggregateImage ((C,s),b))
    · rfl
    · exact absurd (h2a'.mp ⟨(h2.mpr hc), hg⟩) hna

/-- The Case 2b facts of `AggNodeCase2bFacts` at the string the side test accepts. -/
theorem aggnAggregateCase2b_side_facts (hC : AggnPhaseCtxWF c n m C ϕ) (hm : 217 ≤ m)
    {b : Bool} (hb : aggnSideCase2b ((C,s),b) = true) :
    (∃ r,r ∈ aggnAggregateCase2b ((C,s),b)) ∧
      (∀ r ∈ aggnAggregateCase2b ((C,s),b),Case2bOk (3/4 : ℝ) (aggnDecodeConstituent m r) ∧
        11*m ≤ 15*(winSet m r.1).ncard) ∧
      (aggnAggregateCase2b ((C,s),b)).length ≤ m^5 := by
  obtain ⟨h2,hg⟩ := (aggnSideCase2b_iff _).mp hb
  exact aggnCase2bFamily_facts hC.action.2.1 (wf_tidyGens hC.action.2.1 _) hm h2 hg

/-- A computed member of either string's Case 2b family supplies its own size, defect and
numbering proofs (`aggnAggregateConstituent_admissible` for either string). -/
theorem aggnAggregateConstituent_side_admissible (hC : AggnPhaseCtxWF c n m C ϕ)
    (hm : 217 ≤ m) {b : Bool} (hb : aggnSideCase2b ((C,s),b) = true)
    {q : AggnRawConstituent} (hq : q ∈ aggnAggregateCase2b ((C,s),b)) :
    q.1.Nodup ∧ (∀ a ∈ q.1,a < m) ∧ 11*m ≤ 15*q.1.length ∧
      2 ≤ 2 ∧ 4*2 ≤ q.1.length ∧
      (1/4 : ℝ) < (defect (decRel q.1.length 2 (aggnConstituentEnter (C.2.1,q)).2).Aut : ℝ) := by
  obtain ⟨hnd,hlt⟩ := aggnCase2bFamily_names hC.action.2.1 hq
  obtain ⟨hok,hlarge⟩ := (aggnAggregateCase2b_side_facts hC hm hb).2.1 q hq
  have hc := ncard_winSet q.1 hnd hlt
  change 2 ≤ 2 ∧ 4*2 ≤ (winSet m q.1).ncard ∧ _ at hok
  rw [hc] at hok hlarge
  refine ⟨hnd,hlt,hlarge,hok.1,hok.2.1,?_⟩
  rw [aggnConstituentEnter_defect C.2.1 q hnd hlt]
  linarith [hok.2.2]

/-- `aggnCase2bEntries_admissible` for either string. -/
theorem aggnCase2bEntries_side_admissible (hC : AggnPhaseCtxWF c n m C ϕ)
    (hm : 217 ≤ m) {b : Bool} (hb : aggnSideCase2b ((C,s),b) = true)
    {a : AggnDesignEntry} (ha : a ∈ aggnCase2bEntries ((C,s),b)) :
    a.1.Nodup ∧ (∀ u ∈ a.1,u < m) ∧ 11*m ≤ 15*a.1.length ∧
      a.2.1 = ([0,1],C.2.1,List.range a.1.length) ∧
      4*2 ≤ a.1.length ∧ (1/4 : ℝ) < (defect (decRel a.1.length 2 a.2.2).Aut : ℝ) := by
  obtain ⟨q,hq,rfl⟩ := aggnCase2bEntries_mem.mp ha
  obtain ⟨hnd,hlt,hlarge,_,hsize,hdef⟩ := aggnAggregateConstituent_side_admissible hC hm hb hq
  exact ⟨hnd,hlt,hlarge,rfl,hsize,hdef⟩

/-- `aggnCase2bEntries_nonempty` for either string. -/
theorem aggnCase2bEntries_side_nonempty (hC : AggnPhaseCtxWF c n m C ϕ)
    (hm : 217 ≤ m) {b : Bool} (hb : aggnSideCase2b ((C,s),b) = true) :
    (∃ a,a ∈ aggnCase2bEntries ((C,s),b)) ∧ (aggnCase2bEntries ((C,s),b)).length ≤ m^5 := by
  obtain ⟨⟨q,hq⟩,_,hlen⟩ := aggnAggregateCase2b_side_facts hC hm hb
  exact ⟨⟨_,aggnCase2bEntries_mem.mpr ⟨q,hq,rfl⟩⟩,by simpa [aggnCase2bEntries] using hlen⟩

/-- `aggnCase2bEntries_split_input` for either string. -/
theorem aggnCase2bEntries_side_split_input (hC : AggnPhaseCtxWF c n m C ϕ)
    (hm : 217 ≤ m) {b : Bool} (hb : aggnSideCase2b ((C,s),b) = true)
    {a : AggnDesignEntry} (ha : a ∈ aggnCase2bEntries ((C,s),b)) :
    ExtendedInputRep (c+1) a.1.length (a.2,(3,4)) := by
  obtain ⟨_,_,_,hdata,hsize,hdef⟩ := aggnCase2bEntries_side_admissible hC hm hb ha
  have hk : a.2.1.1 = [0,1] := congrArg Prod.fst hdata
  refine ⟨?_,?_,?_,by norm_num,by norm_num [sbipAlphaValue],by norm_num [sbipAlphaValue],?_,?_,?_⟩
  · rw [hdata]; exact List.nodup_range
  · intro i; rw [hdata]; exact List.mem_range
  · rw [hdata]
    apply aggnGuard_two
    rw [hC.source]
    have hh := hC.degree
    omega
  · simpa only [hk,List.length_cons,List.length_nil] using (le_refl 2)
  · simpa only [hk,List.length_cons,List.length_nil] using hsize
  · change 1-sbipAlphaValue (3,4) < (defect (decRel a.1.length a.2.1.1.length a.2.2).Aut : ℝ)
    rw [hk]
    norm_num only [List.length_cons,List.length_nil,sbipAlphaValue,Nat.cast_ofNat]
    exact hdef

/-- `aggnCase2bSplitFamily_valid` for either string: every restored version of the string
the side test accepts is an Align-admissible outcome on all of `Γ`, and there is one. -/
theorem aggnCase2bSplitFamily_side_valid {b' t d : ℕ} (hsolver : AggnRestoredEntryGood c b' t d)
    (hC : AggnPhaseCtxWF c n m C ϕ) (hm : 217 ≤ m) {b : Bool}
    (hb : aggnSideCase2b ((C,s),b) = true) :
    AggnSplitFamilyGood m (aggnCase2bSplitFamily c b' t d ((C,s),b)) := by
  have hg (a : AggnDesignEntry) (ha : a ∈ aggnCase2bEntries ((C,s),b)) :
      AggnSplitFamilyGood m (aggnRestoredEntryFamily c b' t d (C.1.2.1,a)) := by
    obtain ⟨hnd,hlt,hlarge,_⟩ := aggnCase2bEntries_side_admissible hC hm hb ha
    exact hsolver m C.1.2.1 a hC.action.2.1 hnd hlt hlarge
      (aggnCase2bEntries_side_split_input hC hm hb ha)
  constructor
  · obtain ⟨a,ha⟩ := (aggnCase2bEntries_side_nonempty hC hm hb).1
    obtain ⟨o,ho⟩ := (hg a ha).1
    exact ⟨o,List.mem_flatMap.2 ⟨a,ha,ho⟩⟩
  · intro o ho
    obtain ⟨a,ha,ho⟩ := List.mem_flatMap.1 ho
    exact (hg a ha).2 o ho

end Spec

/-! ### The two reject tests -/

/-- §15, lines 5–7, **the reject test of outcome (2b)**: the case test of outcome (2b)
holds at `x` and fails at `y`. -/
def aggnRejectCase (z : AggnPhaseCtx × AggnAggregateState) : Bool :=
  aggnSideCase2b (z,false) && !aggnSideCase2b (z,true)

/-- §15, lines 5–7, **the reject test of outcome (3)**: the fixed sets `D(x)` and `D(y)`
of `F(x)^Γ` and `F(y)^Γ` have different sizes. -/
def aggnRejectDefect (z : AggnPhaseCtx × AggnAggregateState) : Bool :=
  !decide ((aggnAggregateData (z,false)).2.2.length = (aggnAggregateData (z,true)).2.2.length)

theorem aggnPolyFun_rejectCase : PolyFun aggnRejectCase := by
  have hx := (polyFun_id.pair (polyFun_const false)).comp aggnPolyFun_sideCase2b
  have hy := (polyFun_id.pair (polyFun_const true)).comp aggnPolyFun_sideCase2b
  have hny := aggnPolyFun_bnot hy
  exact wftPolyFun_and hx hny

theorem aggnPolyFun_rejectDefect : PolyFun aggnRejectDefect := by
  have hx := (((polyFun_id.pair (polyFun_const false)).comp aggnPolyFun_aggregateData).comp
    polyFun_snd).comp polyFun_snd |>.comp polyFun_length
  have hy := (((polyFun_id.pair (polyFun_const true)).comp aggnPolyFun_aggregateData).comp
    polyFun_snd).comp polyFun_snd |>.comp polyFun_length
  have he := (hx.pair hy).comp polyFun_natEq
  exact aggnPolyFun_bnot he

section Reject
variable {c n m : ℕ} {C : AggnPhaseCtx} {s : AggnAggregateState}
    {ϕ : decGroup n C.1.1.2 →* Perm (Fin m)}
    (hC : AggnPhaseCtxWF c n m C ϕ) (hs : AggnStoresComplete c ϕ s.1.2.1)
include hC hs

/-- The computed test is exactly the pair of hypotheses of `Babai.Line57Data.rejectCase`. -/
theorem aggnRejectCase_spec :
    aggnRejectCase (C,s) = true ↔
      (Case2 (bigFGamma ϕ (decStrN n C.2.1) C.2.2.2.length) ∧
          ¬ AggregateCase2a ϕ (decStrN n C.2.1) C.2.2.2.length) ∧
        ¬ (Case2 (bigFGamma ϕ (decStrN n C.2.2.1) C.2.2.2.length) ∧
          ¬ AggregateCase2a ϕ (decStrN n C.2.2.1) C.2.2.2.length) := by
  have hx := aggnSideCase2b_spec hC hs false
  have hy := aggnSideCase2b_spec hC hs true
  simp only [cond_false, cond_true] at hx hy
  rw [aggnRejectCase, Bool.and_eq_true, Bool.not_eq_true', hx, ← hy]
  simp

/-- The fixed-set list has the size of the paper's `D`. -/
theorem aggnAggregateFixed_length (b : Bool) :
    (aggnAggregateData ((C,s),b)).2.2.length =
      (fixedGamma ϕ (cond b (decStrN n C.2.2.1) (decStrN n C.2.1)) C.2.2.2.length).ncard := by
  obtain ⟨hnd,hlt⟩ := aggnAggregateGuide_names (s := s) hC b
  rw [← (aggnAggregateData_spec hC hs b).2.2, ncard_winSet _ hnd hlt]

/-- The computed test is exactly the hypothesis of `Babai.Line57Data.rejectDefect`. -/
theorem aggnRejectDefect_spec :
    aggnRejectDefect (C,s) = true ↔
      (fixedGamma ϕ (decStrN n C.2.2.1) C.2.2.2.length).ncard ≠
        (fixedGamma ϕ (decStrN n C.2.1) C.2.2.2.length).ncard := by
  have hx := aggnAggregateFixed_length hC hs false
  have hy := aggnAggregateFixed_length hC hs true
  simp only [cond_false, cond_true] at hx hy
  rw [aggnRejectDefect, Bool.not_eq_true', decide_eq_false_iff_not, hx, hy]
  exact ⟨fun h e => h e.symm, fun h e => h e.symm⟩

/-- Rejection at outcome (2b) is sound: the test is canonical (`Babai.case2b_test_strAct`). -/
theorem aggnRejectCase_iso (h : aggnRejectCase (C,s) = true) :
    strIso (decGroup n C.1.1.2 : Set (Perm (Fin n))) (decStrN n C.2.1) (decStrN n C.2.2.1) = ∅ := by
  obtain ⟨hx,hy⟩ := (aggnRejectCase_spec hC hs).mp h
  apply Set.eq_empty_iff_forall_notMem.2
  rintro σ ⟨hσ,hxy⟩
  exact hy (hxy ▸ (case2b_test_strAct ϕ (decStrN n C.2.1) C.2.2.2.length ⟨σ,hσ⟩).2 hx)

/-- Rejection at outcome (3) is sound: `|D|` is a canonical invariant
(`Babai.strIso_eq_empty_of_ncard_fixedGamma_ne`). -/
theorem aggnRejectDefect_iso (h : aggnRejectDefect (C,s) = true) :
    strIso (decGroup n C.1.1.2 : Set (Perm (Fin n))) (decStrN n C.2.1) (decStrN n C.2.2.1) = ∅ :=
  strIso_eq_empty_of_ncard_fixedGamma_ne ϕ _ _ _ ((aggnRejectDefect_spec hC hs).mp h)

end Reject

/-- The size check of the Case 3 constructor is the reject test of outcome (3): when the
test fires, the constructor returns no structure. -/
theorem aggnAggregateGuide_of_rejectDefect {c : ℕ} {C : AggnPhaseCtx} {s : AggnAggregateState}
    (h : aggnRejectDefect (C,s) = true) : aggnAggregateGuide c (C,s) = none := by
  rw [aggnRejectDefect, Bool.not_eq_true', decide_eq_false_iff_not] at h
  unfold aggnAggregateGuide aggnGuideBuild
  rw [if_neg]
  simp only [aggnGuidePrepare, aggnGuideSideRows, Bool.and_eq_true, decide_eq_true_eq, not_and]
  exact fun e => absurd e h

end Algo
