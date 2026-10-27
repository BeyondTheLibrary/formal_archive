import Workspace.Algo.AggNodeContinuationTransport

/-! # The Case 2b versions move with the input isomorphisms

Theorem 13.2.1 (v2.5, Sec. 13.2), case (2b), individualizes a set `S` and one orbital
`X_i` of `F^C_{(S)}`, with the Warning that the numbering of the orbitals is not canonical.
The family of all these choices is canonical: `Babai.case2bFamily_canonical` says that
`σ ∈ G` carries the family of `x` onto the family of `x^σ` along `ϕ(σ)`, member by member.

On the RAM the family is a list (`aggnAggregateCase2b`) whose decoded members are exactly
`Babai.case2bFamily` (`aggnAggregateCase2b_spec`). This file shows that a member of the
family of `x` and the matching member of the family of `y` give numbered binary inputs of
Theorem 9.2.3 that are isomorphic along the bijection `ϕ(σ)` induces, and then, with the
canonicity of Theorem 9.2.3 on the RAM (`AggnEntryFamilyCanonical`), that every computed
version of `x` goes along `ϕ(σ)` to a computed version of `y`.
-/
set_option synthInstance.maxSize 2048
namespace Algo
open RAM RAM.Targets Babai Equiv

theorem aggnTupleOf_two {n : ℕ} (x : Fin 2 → Fin n) : tupleOf x = [(x 0).val,(x 1).val] := by
  simp [tupleOf,List.ofFn_succ]

/-- Two raw constituents whose decoded sets and relations correspond along `π` give
numbered one-relation structures that are isomorphic along the bijection `π` induces on the
two name lists. -/
theorem aggnConstituentEntry_iso {m : ℕ} (q q' : AggnRawConstituent)
    (hn : q.1.Nodup) (hb : ∀ u ∈ q.1,u < m) (hn' : q'.1.Nodup) (hb' : ∀ u ∈ q'.1,u < m)
    (π : Perm (Fin m)) (hset : winSet m q'.1 = π '' winSet m q.1)
    (hrel : aggnDecodePairRel m q'.2 = Prod.map π π '' aggnDecodePairRel m q.2) :
    ∃ f : Fin q.1.length ≃ Fin q'.1.length,
      f ∈ KAryRelStruct.Iso (decRel q.1.length 2 [aggnConstituentRel q])
        (decRel q'.1.length 2 [aggnConstituentRel q']) ∧
      ∀ i : Fin q.1.length, q'.1[(f i).val] = (π ⟨q.1[i.val], hb _ (List.getElem_mem _)⟩).val := by
  let e1 := winEquiv m q.1 hn hb
  let e3 := winEquiv m q'.1 hn' hb'
  let e2 : ↥(winSet m q.1) ≃ ↥(winSet m q'.1) :=
    (Equiv.Set.image π (winSet m q.1) π.injective).trans (Equiv.setCongr hset.symm)
  let f := e1.trans (e2.trans e3.symm)
  have hval (i : Fin q.1.length) : (e3 (f i) : Fin m) = π ⟨q.1[i.val], hb _ (List.getElem_mem _)⟩ := by
    simp only [f,e2,Equiv.trans_apply,Equiv.apply_symm_apply]
    change π (e1 i : Fin m) = _
    rw [winEquiv_coe q.1 hn hb i.isLt]
  have hname (i : Fin q.1.length) :
      q'.1[(f i).val] = (π ⟨q.1[i.val], hb _ (List.getElem_mem _)⟩).val := by
    have h := congrArg Fin.val (hval i)
    rw [winEquiv_coe q'.1 hn' hb' (f i).isLt] at h
    exact h
  refine ⟨f,?_,hname⟩
  intro r x
  change tupleOf x ∈ [aggnConstituentRel q].getD r [] ↔
    tupleOf (tupleMap f x) ∈ [aggnConstituentRel q'].getD r []
  rcases r with _ | r
  · simp only [List.getD_cons_zero]
    rw [aggnTupleOf_two,aggnTupleOf_two,aggnConstituentRel_pair,aggnConstituentRel_pair]
    simp only [tupleMap]
    rw [hname,hname]
    have hmem (R : RawRel) (a b : Fin m) : [a.val,b.val] ∈ R ↔ (a,b) ∈ aggnDecodePairRel m R :=
      Iff.rfl
    rw [hmem,hrel]
    constructor
    · intro h
      exact ⟨(⟨q.1[(x 0).val], hb _ (List.getElem_mem _)⟩,⟨q.1[(x 1).val], hb _ (List.getElem_mem _)⟩),h,rfl⟩
    · rintro ⟨⟨a,b⟩,hab,he⟩
      simp only [Prod.map,Prod.mk.injEq] at he
      have ha := π.injective he.1
      have hb2 := π.injective he.2
      subst ha hb2
      exact hab
  · simp

section Case2b
variable {c n m : ℕ} {C : AggnPhaseCtx} {s : AggnAggregateState}
    {ϕ : decGroup n C.1.1.2 →* Perm (Fin m)}
    (hC : AggnPhaseCtxWF c n m C ϕ) (hs : AggnStoresComplete c ϕ s.1.2.1)
include hC hs

/-- §13.2, outcome (2b): **every member of the family of `x` has a member of the family of
`y` that it is carried to by `ϕ(σ)`**, for every `σ ∈ Iso_G(x,y)` (`case2bFamily_canonical`
read through the exact raw family). -/
theorem aggnAggregateCase2b_transport (hm : 217 ≤ m)
    (hx : aggnSideCase2b ((C,s),false) = true) (hy : aggnSideCase2b ((C,s),true) = true)
    (σ : decGroup n C.1.1.2) (hσ : strAct (decStrN n C.2.1) σ.val = decStrN n C.2.2.1)
    {q : AggnRawConstituent} (hq : q ∈ aggnAggregateCase2b ((C,s),false)) :
    ∃ q' ∈ aggnAggregateCase2b ((C,s),true),
      winSet m q'.1 = ϕ σ '' winSet m q.1 ∧
      aggnDecodePairRel m q'.2 = Prod.map (ϕ σ) (ϕ σ) '' aggnDecodePairRel m q.2 := by
  obtain ⟨h2x,hgx⟩ := (aggnSideCase2b_iff _).mp hx
  obtain ⟨h2y,hgy⟩ := (aggnSideCase2b_iff _).mp hy
  have hsx := aggnAggregateCase2b_spec hC hs false hm h2x hgx
  have hsy := aggnAggregateCase2b_spec hC hs true hm h2y hgy
  simp only [cond_false,cond_true] at hsx hsy
  have hQ : aggnDecodeConstituent m q ∈
      case2bFamily (bigFGamma ϕ (decStrN n C.2.1) C.2.2.2.length) := by
    rw [← hsx]; exact ⟨q,hq,rfl⟩
  have hQ' : moveCase2b (ϕ σ) (aggnDecodeConstituent m q) ∈
      case2bFamily (bigFGamma ϕ (decStrN n C.2.2.1) C.2.2.2.length) := by
    rw [← hσ,case2bFamily_canonical ϕ (decStrN n C.2.1) C.2.2.2.length σ]
    exact ⟨_,hQ,rfl⟩
  rw [← hsy] at hQ'
  obtain ⟨q',hq',he⟩ := hQ'
  refine ⟨q',hq',?_,?_⟩
  · exact congrArg Prod.fst he
  · exact congrArg Prod.snd he

/-- §13.2, outcome (2b), and §15, line 6a: **every version of `x` goes to a version of `y`
along `ϕ(σ)`**, for every `σ ∈ Iso_G(x,y)`. -/
theorem aggnCase2bSplitFamily_transport {b t d : ℕ} (hcan : AggnEntryFamilyCanonical c b t d)
    (hm : 217 ≤ m)
    (hx : aggnSideCase2b ((C,s),false) = true) (hy : aggnSideCase2b ((C,s),true) = true)
    (σ : decGroup n C.1.1.2) (hσ : strAct (decStrN n C.2.1) σ.val = decStrN n C.2.2.1)
    {o : RawAlignOutcome} (ho : o ∈ aggnCase2bSplitFamily c b t d ((C,s),false)) :
    ∃ o' ∈ aggnCase2bSplitFamily c b t d ((C,s),true), RawSplitOutcomeIso m (ϕ σ) o o' := by
  obtain ⟨a,ha,ho⟩ := List.mem_flatMap.1 ho
  have ha0 := ha
  obtain ⟨q,hq,rfl⟩ := aggnCase2bEntries_mem.mp ha
  obtain ⟨q',hq',hset,hrel⟩ := aggnAggregateCase2b_transport hC hs hm hx hy σ hσ hq
  have ha' : (q'.1,aggnConstituentEnter (C.2.1,q')) ∈ aggnCase2bEntries ((C,s),true) :=
    aggnCase2bEntries_mem.mpr ⟨q',hq',rfl⟩
  obtain ⟨hn,hb⟩ := aggnCase2bFamily_names hC.action.2.1 hq
  obtain ⟨hn',hb'⟩ := aggnCase2bFamily_names hC.action.2.1 hq'
  obtain ⟨f,hf,hπ⟩ := aggnConstituentEntry_iso q q' hn hb hn' hb' (ϕ σ) hset hrel
  have hlen : q'.1.length = q.1.length := by simpa using (Fintype.card_congr f).symm
  obtain ⟨o',ho',hi⟩ := aggnRestoredEntryFamily_transport hcan hC.action.2.1 hC.action.2.1
    (a := (q.1,aggnConstituentEnter (C.2.1,q))) (a' := (q'.1,aggnConstituentEnter (C.2.1,q')))
    hn hb hn' hb' (aggnCase2bEntries_side_split_input hC hm hx ha0)
    (aggnCase2bEntries_side_split_input hC hm hy ha')
    (by change ([0,1],C.2.1,List.range q.1.length) = ([0,1],C.2.1,List.range q'.1.length)
        rw [hlen])
    (ϕ σ) f hf hπ ho
  exact ⟨o',List.mem_flatMap.2 ⟨_,ha',ho'⟩,hi⟩

/-- At tag `3` of the continuation, every listed version of `x` goes along `ϕ(σ)` to a
listed version of `y`. -/
theorem aggnContinuation_three_transport {b t d : ℕ}
    (hcan : AggnEntryFamilyCanonical c b t d) (hm : 217 ≤ m)
    (h3 : (aggnContinuation c b t d (C,s)).1 = 3)
    (σ : decGroup n C.1.1.2) (hσ : strAct (decStrN n C.2.1) σ.val = decStrN n C.2.2.1)
    {o : RawAlignOutcome} (ho : o ∈ (aggnContinuation c b t d (C,s)).2.1) :
    ∃ o' ∈ (aggnContinuation c b t d (C,s)).2.2, RawSplitOutcomeIso m (ϕ σ) o o' := by
  obtain ⟨h2,hg,hr⟩ := (aggnContinuation_tag c b t d (C,s)).2.2.2.1.mp h3
  have hx : aggnSideCase2b ((C,s),false) = true := (aggnSideCase2b_false_iff C s).mpr ⟨h2,hg⟩
  have hy : aggnSideCase2b ((C,s),true) = true := by
    simp only [aggnRejectCase,hx,Bool.true_and,Bool.not_eq_false'] at hr
    exact hr
  rw [aggnContinuation_of_case2b h2 hg hr] at ho ⊢
  exact aggnCase2bSplitFamily_transport hC hs hcan hm hx hy σ hσ ho

end Case2b

end Algo
