import Workspace.Algo.DesignReadFamilyIso
import Workspace.Algo.SplitExtendedRunSpec
import Workspace.Algo.SplitUpccRunTransport
import Workspace.Algo.SplitRestoreTransport
import Workspace.Algo.TestSetNaming

/-! # Theorem 9.2.3 on the RAM is canonical

Theorem 9.2.3 (v2.5, Sec. 9.2) applies the Design Lemma to a `k`-ary relational structure and
then either returns the partition it finds or runs Theorem 9.2.1 on the dominant UPCC it finds.
Its outputs are canonical. On the RAM:

* the read family of the Design Lemma moves along any isomorphism `f`
  (`ambientDesignReadFamily_iso`);
* a partition output is an answer, related by `f`;
* a UPCC output is renamed to `0, …, |L| − 1`, solved, and the answers are restored to their
  old names; the renaming turns `f` into a permutation `ψ` of the local names, the UPCC run
  moves along `ψ` (`upccSplitFamily_transport`) and restoration turns `ψ` back into `f`
  (`splitRestoreOutcome_iso`).
-/
namespace Algo
open Babai RAM Equiv
open scoped Classical

theorem rawLetterIndex_getD {L : List ℕ} (hn : L.Nodup) {i : ℕ} (hi : i < L.length) :
    rawLetterIndex (L,L.getD i 0) = i := by
  have hm : L.getD i 0 ∈ L := by rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi
  obtain ⟨hlt,hget⟩ := rawLetterIndex_spec hm
  rw [List.getD_eq_getElem _ _ hlt] at hget
  have h2 : L[rawLetterIndex (L,L.getD i 0)] = L[i] := by
    rw [hget,List.getD_eq_getElem _ _ hi]
  exact (hn.getElem_inj_iff).1 h2

/-- The local renaming of a UPCC output of the Design Lemma, and its transport along `f`. -/
theorem extendedUpcc_transport {c t d n m : ℕ} (hsolver : BipInputRunCanonical c t d)
    (f : Perm (Fin n)) {L L' : List ℕ} {q q' : RawConfig} {r r' : RawUpcc}
    (hn : L.Nodup) (hb : ∀ a ∈ L,a < n) (hn' : L'.Nodup) (hb' : ∀ a ∈ L',a < n)
    (hm : L.length = m) (hm' : L'.length = m)
    (hr : r.1 = q) (hr' : r'.1 = q')
    {C C' : (UPCCs (Fin m)).Obj Set.univ} (hC : UpccInputRep m r C) (hC' : UpccInputRep m r' C')
    (ha : sbipAlphaValue r.2 = sbipAlphaValue r'.2)
    (hw : f '' winSet n L = winSet n L')
    (hq : ∀ u v : Fin n,u.val ∈ L → v.val ∈ L →
      binColor (q',(rawLetterIndex (L',(f u).val),rawLetterIndex (L',(f v).val))) =
      binColor (q,(rawLetterIndex (L,u.val),rawLetterIndex (L,v.val))))
    (dom dom' : List ℕ) (hd : dom.length = n) (hd' : dom'.length = n)
    {p : RawAlignOutcome} (hp : p ∈ upccSplitFamily c t d r) :
    ∃ p' ∈ upccSplitFamily c t d r',
      RawSplitOutcomeIso n f (aggnRestoreOutcome ((dom,L),p)) (aggnRestoreOutcome ((dom',L'),p')) := by
  let e := splitNameEquiv L hn hb hm
  let e' := splitNameEquiv L' hn' hb' hm'
  let fW : ↥(winSet n L) ≃ ↥(winSet n L') := (f.image (winSet n L)).trans (Equiv.setCongr hw)
  let ψ : Perm (Fin m) := e.trans (fW.trans e'.symm)
  have hψ : ∀ i,(e' (ψ i)).val = f (e i).val := by
    intro i
    simp only [ψ,Equiv.trans_apply,Equiv.apply_symm_apply]
    rfl
  -- the local index of a named point
  have hidx : ∀ i : Fin m,rawLetterIndex (L,((e i).val : ℕ)) = i.val := by
    intro i
    rw [splitNameEquiv_val,rawGet]
    exact rawLetterIndex_getD hn (by rw [hm]; exact i.isLt)
  have hidx' : ∀ i : Fin m,rawLetterIndex (L',((e' i).val : ℕ)) = i.val := by
    intro i
    rw [splitNameEquiv_val,rawGet]
    exact rawLetterIndex_getD hn' (by rw [hm']; exact i.isLt)
  let φ : ↥(Set.univ : Set (Fin m)) ≃ ↥(Set.univ : Set (Fin m)) :=
    (Equiv.Set.univ (Fin m)).trans (ψ.trans (Equiv.Set.univ (Fin m)).symm)
  have hφ : φ ∈ (UPCCs (Fin m)).Iso C C' := by
    intro x y
    have h1 := hC.names x y
    have h2 := hC'.names (φ x) (φ y)
    change binColor (r.1,(x.val.val,y.val.val)) = C.1 x y at h1
    change binColor (r'.1,((ψ x.val).val,(ψ y.val).val)) = C'.1 (φ x) (φ y) at h2
    rw [← h1,← h2,hr,hr']
    have := hq (e x.val).val (e y.val).val (e x.val).2 (e y.val).2
    rw [← hψ,← hψ,hidx',hidx',hidx,hidx] at this
    exact this
  obtain ⟨p',hp',hi⟩ := upccSplitFamily_transport hsolver hC hC' ha φ hφ ψ (fun _ => rfl) hp
  exact ⟨p',hp',splitRestoreOutcome_iso L L' hn hb hm hn' hb' hm' f ψ hψ dom dom' hd hd' hi⟩

/-- **Theorem 9.2.3, one branch.** Two read outputs related by `f` give computed answers
related by `f`. -/
theorem extendedSplitBranch_transport {a c t d n : ℕ} (hsolver : BipInputRunCanonical c t d)
    {g g' : AmbientGIn} (h : ExtendedInputRep a n g) (h' : ExtendedInputRep a n g')
    (hα : g.2 = g'.2) {xs xs' : List ℕ} {o o' : RawDesignReadOut}
    (ho : (xs,o) ∈ ambientDesignReadFamily a g) (ho' : (xs',o') ∈ ambientDesignReadFamily a g')
    {f : Perm (Fin n)} (hi : DesignReadOutIso n f o o')
    {p : RawAlignOutcome} (hp : p ∈ extendedSplitBranch c t d (g,o)) :
    ∃ p' ∈ extendedSplitBranch c t d (g',o'),RawSplitOutcomeIso n f p p' := by
  rcases hi with ⟨P,P',rfl,rfl,hc⟩ | ⟨L,L',q,q',rfl,rfl,hw,hq⟩
  · have he : p = rawAlignPartition P := by simpa [extendedSplitBranch] using hp
    subst he
    exact ⟨rawAlignPartition P',by simp [extendedSplitBranch],
      _,_,rfl,rfl,(splitOutcomeIso_partition_iff f P P').2 hc⟩
  · obtain ⟨hn,hb,-⟩ := h.upcc_storage ho rfl
    obtain ⟨hn',hb',-⟩ := h'.upcc_storage ho' rfl
    obtain ⟨C,hC,-,-⟩ := h.upcc_admissible ho rfl
    obtain ⟨C',hC',-,-⟩ := h'.upcc_admissible ho' rfl
    have hlen : L'.length = L.length := by
      rw [← ncard_winSet L' hn' hb',← hw,Set.ncard_image_of_injective _ f.injective,
        ncard_winSet L hn hb]
    have hp2 : p ∈ (upccSplitFamily c t d (extendedUpccInput ((g,(none,L,some q)),q))).map
        (fun p => aggnRestoreOutcome ((g.1.1.2.2,L),p)) := by
      simpa [extendedSplitBranch,extendedUpccAnswers] using hp
    obtain ⟨p₀,hp₀,rfl⟩ := List.mem_map.1 hp2
    have ha : sbipAlphaValue (extendedUpccInput ((g,(none,L,some q)),q)).2 =
        sbipAlphaValue (extendedUpccInput ((g',(none,L',some q')),q')).2 := by
      simp only [extendedUpccInput,h.domain_length,h'.domain_length,hlen,hα]
    change UpccInputRep L'.length _ C' at hC'
    revert C'
    rw [hlen]
    intro C' hC'
    obtain ⟨p',hp',hiso⟩ := extendedUpcc_transport hsolver f hn hb hn' hb' rfl hlen rfl rfl
      hC hC' ha hw hq g.1.1.2.2 g'.1.1.2.2 h.domain_length h'.domain_length hp₀
    refine ⟨_,?_,hiso⟩
    simp only [extendedSplitBranch,Option.elim_none,Option.elim_some,extendedUpccAnswers]
    exact List.mem_map_of_mem hp'

end Algo

namespace Algo
open Babai RAM Equiv
open scoped Classical

/-- **Theorem 9.2.3 on the RAM is canonical** (Sec. 9.2): an isomorphism `f` of two admitted
inputs with the same arity list, guard string and domain list carries every computed answer
of the first to a computed answer of the second, along `f`. The relations may be listed in any
order. -/
theorem extendedSplitFamily_transport {a c t d n : ℕ} (hsolver : BipInputRunCanonical c t d)
    {g g' : AmbientGIn} (h : ExtendedInputRep a n g) (h' : ExtendedInputRep a n g')
    (h1 : g.1.1 = g'.1.1) (hα : g.2 = g'.2) (f : Perm (Fin n))
    (hf : f ∈ KAryRelStruct.Iso (decRel n g.1.1.1.length g.1.2) (decRel n g.1.1.1.length g'.1.2))
    {p : RawAlignOutcome} (hp : p ∈ extendedSplitFamily a c t d g) :
    ∃ p' ∈ extendedSplitFamily a c t d g',RawSplitOutcomeIso n f p p' := by
  obtain ⟨u,hu,hpu⟩ := List.mem_flatMap.1 hp
  obtain ⟨⟨⟨ks,base,dom⟩,rels⟩,⟨α,β⟩⟩ := g
  obtain ⟨⟨⟨ks',base',dom'⟩,rels'⟩,⟨α',β'⟩⟩ := g'
  simp only [Prod.mk.injEq] at h1 hα
  obtain ⟨rfl,rfl,rfl⟩ := h1
  obtain ⟨rfl,rfl⟩ := hα
  obtain ⟨v,hv,hiso⟩ := ambientDesignReadFamily_iso h.nodup h.domain h'.nodup h'.domain
    h.guard h.denominator hf hu
  obtain ⟨p',hp',hi⟩ := extendedSplitBranch_transport hsolver h h' rfl hu hv hiso hpu
  exact ⟨p',List.mem_flatMap.2 ⟨v,hv,hp'⟩,hi⟩

end Algo
