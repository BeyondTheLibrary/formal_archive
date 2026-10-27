import Workspace.Algo.AggNodeContinuation
import Workspace.Algo.SplitRestoreTransport

/-! # The versions of the aggregate continuations move with the input isomorphisms

Theorem 13.2.1 (v2.5, Sec. 13.2) returns *canonical* objects, and line 6a of Sec. 15 applies
the Extended Design Lemma (Theorem 9.2.3), whose outputs are canonical too. Procedure Align
(Sec. 14.1) needs exactly this: an isomorphism `σ ∈ Iso_G(x,y)` carries every version of `x`
to a version of `y` along `ϕ(σ)`.

This file proves it for the versions the RAM computes at outcome (3), from two facts:

* the local-guide structures of `x` and `y` are isomorphic along the bijection of `D(x)` onto
  `D(y)` that `ϕ(σ)` induces (`aggnAggregateGuide_canonical`);
* the computed family of Theorem 9.2.3 is canonical on numbered inputs
  (`AggnEntryFamilyCanonical`, the RAM form of "canonical" in Theorem 9.2.3; it is a
  hypothesis here because the Section 9 track has not yet finished its proof for
  `extendedSplitFamily`);

and the restoration of old names commutes with the isomorphism
(`splitRestoreOutcome_iso`).
-/
set_option synthInstance.maxSize 2048
namespace Algo
open RAM RAM.Targets Babai Equiv

/-- **Canonicity of Theorem 9.2.3 on the RAM**, for the inputs of the aggregate
continuations (arity list, original string and numbered domain in `a.1`, relations in `a.2`,
threshold `3/4`): an isomorphism of two admitted numbered inputs with the same first
component carries every computed version of the first to a computed version of the second. -/
def AggnEntryFamilyCanonical (c b t d : ℕ) : Prop :=
  ∀ k (a a' : AmbientPIn), ExtendedInputRep (c+1) k (a,(3,4)) →
    ExtendedInputRep (c+1) k (a',(3,4)) → a.1 = a'.1 →
    ∀ f : Perm (Fin k),
      f ∈ KAryRelStruct.Iso (decRel k a.1.1.length a.2) (decRel k a.1.1.length a'.2) →
    ∀ o ∈ extendedSplitFamily (c+1) b t d (a,(3,4)),
      ∃ o' ∈ extendedSplitFamily (c+1) b t d (a',(3,4)), RawSplitOutcomeIso k f o o'

theorem aggnDecRel_iso_finCongr {n n' k : ℕ} (h : n' = n) (rels rels' : RawRelStruct)
    (f : Fin n ≃ Fin n') (hf : f ∈ KAryRelStruct.Iso (decRel n k rels) (decRel n' k rels')) :
    f.trans (finCongr h) ∈ KAryRelStruct.Iso (decRel n k rels) (decRel n k rels') := by
  subst h
  simpa using hf

/-- **Restoration is natural.** Two admitted entries whose numbered structures are isomorphic
along `f`, where `f` follows `π` through the two name lists, have restored families that
correspond member by member along `π`. -/
theorem aggnRestoredEntryFamily_transport {c b t d m : ℕ} (hcan : AggnEntryFamilyCanonical c b t d)
    {dom dom' : List ℕ} (hm : dom.length = m) (hm' : dom'.length = m)
    {a a' : AggnDesignEntry}
    (hn : a.1.Nodup) (hb : ∀ u ∈ a.1, u < m) (hn' : a'.1.Nodup) (hb' : ∀ u ∈ a'.1, u < m)
    (hI : ExtendedInputRep (c+1) a.1.length (a.2,(3,4)))
    (hI' : ExtendedInputRep (c+1) a'.1.length (a'.2,(3,4)))
    (h1 : a.2.1 = a'.2.1) (π : Perm (Fin m))
    (f : Fin a.1.length ≃ Fin a'.1.length)
    (hf : f ∈ KAryRelStruct.Iso (decRel a.1.length a.2.1.1.length a.2.2)
      (decRel a'.1.length a.2.1.1.length a'.2.2))
    (hπ : ∀ i : Fin a.1.length,
      a'.1[(f i).val] = (π ⟨a.1[i.val], hb _ (List.getElem_mem _)⟩).val)
    {o : RawAlignOutcome} (ho : o ∈ aggnRestoredEntryFamily c b t d (dom,a)) :
    ∃ o' ∈ aggnRestoredEntryFamily c b t d (dom',a'), RawSplitOutcomeIso m π o o' := by
  obtain ⟨D,A⟩ := a
  obtain ⟨E,A'⟩ := a'
  dsimp only at hn hb hn' hb' hI hI' h1 f hf hπ ⊢
  have hkk : E.length = D.length := by simpa using (Fintype.card_congr f).symm
  let f' : Perm (Fin D.length) := f.trans (finCongr hkk)
  have hf' : f' ∈ KAryRelStruct.Iso (decRel D.length A.1.1.length A.2)
      (decRel D.length A.1.1.length A'.2) :=
    aggnDecRel_iso_finCongr hkk A.2 A'.2 f hf
  have hI'' : ExtendedInputRep (c+1) D.length (A',(3,4)) := hkk ▸ hI'
  obtain ⟨p,hp,rfl⟩ := List.mem_map.1 ho
  obtain ⟨p',hp',hiso⟩ := hcan D.length A A' hI hI'' h1 f' hf' p hp
  refine ⟨aggnRestoreOutcome ((dom',E),p'),List.mem_map.2 ⟨p',hp',rfl⟩,?_⟩
  refine splitRestoreOutcome_iso D E hn hb rfl hn' hb' hkk π f' ?_ dom dom' hm hm' hiso
  intro i
  apply Fin.ext
  have hD : (splitNameEquiv D hn hb rfl i).val = ⟨D[i.val], hb _ (List.getElem_mem _)⟩ :=
    Fin.ext (by rw [splitNameEquiv_val,rawGet,List.getD_eq_getElem _ _ i.isLt])
  rw [hD,← hπ i,splitNameEquiv_val,rawGet]
  simp only [f',Equiv.trans_apply,finCongr_apply,Fin.val_cast]
  exact List.getD_eq_getElem _ _ _

/-! ### Outcome (3) -/

section Case3
variable {c n m : ℕ} {C : AggnPhaseCtx} {s : AggnAggregateState}
    {ϕ : decGroup n C.1.1.2 →* Perm (Fin m)}
    (hC : AggnPhaseCtxWF c n m C ϕ) (hs : AggnStoresComplete c ϕ s.1.2.1)
    (htbl : AggnCompareTableFor c ϕ (aggnCompareTable c (C,s.2.2.2.1)))
    (hset : LocalCertSetting (decGroup n C.1.1.2) ϕ)
    (ht : LargeK C.2.2.2.length (Nat.card (Fin n))) (htm : 10*C.2.2.2.length ≤ m)
    [Nonempty (Fin n)]
include hC hs htbl hset ht htm

/-- §13.2, outcome (3), and §15, line 6a: **every version of `x` goes to a version of `y`
along `ϕ(σ)`**, for every `σ ∈ Iso_G(x,y)`. -/
theorem aggnGuideSplitPair_transport {b t d : ℕ} (hcan : AggnEntryFamilyCanonical c b t d)
    {out : AmbientPIn × AmbientPIn}
    (hout : aggnAggregateGuide c (C,s) = some out) (hcase : aggnAggregateDispatch (C,s) = 3)
    (σ : decGroup n C.1.1.2) (hσ : strAct (decStrN n C.2.1) σ.val = decStrN n C.2.2.1)
    {o : RawAlignOutcome}
    (ho : o ∈ (aggnGuideSplitPair c b t d ((C,s),aggnGuideEntryPair ((C,s),out))).1) :
    ∃ o' ∈ (aggnGuideSplitPair c b t d ((C,s),aggnGuideEntryPair ((C,s),out))).2,
      RawSplitOutcomeIso m (ϕ σ) o o' := by
  obtain ⟨f,hfv,hf⟩ := aggnAggregateGuide_canonical hC hs htbl hset ht htm hout σ hσ
  obtain ⟨hnx,hbx,_,hdx,_⟩ := aggnGuideEntries_admissible hC hs htbl hset ht htm hout hcase false
  obtain ⟨hny,hby,_,hdy,_⟩ := aggnGuideEntries_admissible hC hs htbl hset ht htm hout hcase true
  have hIx := aggnGuideEntries_split_input hC hs htbl hset ht htm hout hcase false
  have hIy := aggnGuideEntries_split_input hC hs htbl hset ht htm hout hcase true
  simp only [cond_false,cond_true] at hnx hbx hdx hny hby hdy hIx hIy
  have hlen : (aggnAggregateData ((C,s),true)).2.2.length =
      (aggnAggregateData ((C,s),false)).2.2.length := by
    simpa using (Fintype.card_congr f).symm
  refine aggnRestoredEntryFamily_transport hcan hC.action.2.1 hC.action.2.1 hnx hbx hny hby
    hIx hIy ?_ (ϕ σ) f ?_ ?_ ho
  · change (aggnGuideEntryPair ((C,s),out)).1.2.1 = (aggnGuideEntryPair ((C,s),out)).2.2.1
    rw [hdx,hdy]
    change (C.2.2.2,C.2.1,List.range (aggnAggregateData ((C,s),false)).2.2.length) =
      (C.2.2.2,C.2.1,List.range (aggnAggregateData ((C,s),true)).2.2.length)
    rw [hlen]
  · have hk : (aggnGuideEntryPair ((C,s),out)).1.2.1.1 = C.2.2.2 := congrArg Prod.fst hdx
    change f ∈ KAryRelStruct.Iso
      (decRel (aggnAggregateData ((C,s),false)).2.2.length
        (aggnGuideEntryPair ((C,s),out)).1.2.1.1.length out.1.2)
      (decRel (aggnAggregateData ((C,s),true)).2.2.length
        (aggnGuideEntryPair ((C,s),out)).1.2.1.1.length out.2.2)
    rw [hk]
    exact hf
  · intro i
    have h := congrArg Fin.val (hfv i)
    rw [aggnAggregateGuideEquiv_name] at h
    change (aggnAggregateData ((C,s),true)).2.2[(f i).val] = _
    rw [h]
    congr 2

/-- The same at the level of the whole continuation: at tag `4`, every listed version of `x`
goes along `ϕ(σ)` to a listed version of `y`. -/
theorem aggnContinuation_four_transport {b t d : ℕ} (hcan : AggnEntryFamilyCanonical c b t d)
    (h4 : (aggnContinuation c b t d (C,s)).1 = 4)
    (σ : decGroup n C.1.1.2) (hσ : strAct (decStrN n C.2.1) σ.val = decStrN n C.2.2.1)
    {o : RawAlignOutcome} (ho : o ∈ (aggnContinuation c b t d (C,s)).2.1) :
    ∃ o' ∈ (aggnContinuation c b t d (C,s)).2.2, RawSplitOutcomeIso m (ϕ σ) o o' := by
  obtain ⟨h3,hr,hsome⟩ := (aggnContinuation_tag c b t d (C,s)).2.2.2.2.2.1.mp h4
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
  rw [heq] at ho ⊢
  exact aggnGuideSplitPair_transport hC hs htbl hset ht htm hcan hout h3 σ hσ ho

end Case3

end Algo
