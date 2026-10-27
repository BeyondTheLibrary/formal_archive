import Workspace.Algo.SplitDesignDomNames
import Workspace.Algo.SplitDesignDomMath

/-! # Section 9.7: well-formedness of the dominant Johnson output

The failed twin test makes the rows distinct. The trace bijection supplies
the exact binomial count, including when all labels are complemented.
-/
namespace Algo
open Babai RAM

theorem designDomLabel_sorted (z : RawDesignLocal) (i : ℕ) :
    (designDomLabel (z,i)).SortedLT := by
  unfold designDomLabel
  split <;> exact (List.pairwise_lt_range.filter _).sortedLT

theorem designDomLabel_lt (z : RawDesignLocal) (i a : ℕ)
    (ha : a ∈ designDomLabel (z,i)) : a < (designBigPositions z.1).length := by
  unfold designDomLabel at ha
  split at ha
  · exact List.mem_range.1 (List.mem_of_mem_filter ha)
  · exact (designComplementRow_mem _ _ _).1 ha |>.1

section
variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {s : Set Ω}
    {X : BlkDesignObj s} {name₁ : ↥X.Pt₁ → ℕ} {name₂ : ↥X.blocks → ℕ}
    {r : RawUpccCase} (h : DesignNames X name₁ name₂ r)
    (e₁ : ↥X.Pt₁ ≃ Fin r.2.1.length) (he₁ : ∀ x, r.2.1[(e₁ x).val] = name₁ x)
    (e₂ : ↥X.blocks ≃ Fin r.2.2.length) (he₂ : ∀ B, r.2.2[(e₂ B).val] = name₂ B)
    (p : ℕ × ℕ) (hb : 0 < p.2) (hd : X.DomHyp (sbipAlphaValue p))
include h he₁ he₂ hb hd

theorem designDomLabel_length (x : ↥(X.domClass (sbipAlphaValue p))) :
    (designDomLabel ((r,p),e₁ ⟨x.val,x.property.1⟩)).length = designDomRank (r,p) := by
  classical
  obtain ⟨eC,heC⟩ := designBigEquiv_exists h e₁ he₁ e₂ he₂
  rw [← card_rawJSet (designDomLabel_sorted _ _).nodup (designDomLabel_lt _ _),
    designDomLabel_set h e₁ he₁ e₂ he₂ p hb eC heC hd x,
    designDomRank_spec h e₁ he₁ e₂ he₂ p hb hd x]
  have hsize := hd.localSize_lt x.property
  split
  next hdir =>
    rw [Finset.card_image_of_injective _ eC.injective,X.card_traceFinset,min_eq_left (by omega)]
  next hdir =>
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),Finset.card_univ,Fintype.card_fin,
      Finset.card_image_of_injective _ eC.injective,X.card_traceFinset,
      designBigPositions_size h e₁ he₁ e₂ he₂,min_eq_right (by omega)]

theorem designDomLabel_injective (ht : designHasDomTwins (r,p) ≠ true) :
    Function.Injective (fun x : ↥(X.domClass (sbipAlphaValue p)) =>
      designDomLabel ((r,p),e₁ ⟨x.val,x.property.1⟩)) := by
  classical
  obtain ⟨eC,heC⟩ := designBigEquiv_exists h e₁ he₁ e₂ he₂
  intro x y hxy
  have hset := congrArg (rawJSet (designBigPositions r).length) hxy
  rw [designDomLabel_set h e₁ he₁ e₂ he₂ p hb eC heC hd x,
    designDomLabel_set h e₁ he₁ e₂ he₂ p hb eC heC hd y,
    designDom_localSize hd x y] at hset
  have hfin : X.traceFinset x.val = X.traceFinset y.val := by
    apply Finset.image_injective eC.injective
    split at hset
    · exact hset
    · ext B
      have hh := Finset.ext_iff.1 hset B
      simp only [Finset.mem_sdiff,Finset.mem_univ,true_and] at hh
      exact not_iff_not.mp hh
  by_contra hne
  exact ht ((designHasDomTwins_spec h e₁ he₁ e₂ he₂ p hb).2
    ⟨x.val,x.property,y.val,y.property,fun hh => hne (Subtype.ext hh),
      (X.traceFinset_eq_iff _ _).1 hfin⟩)

theorem designDomLabels_nodup (ht : designHasDomTwins (r,p) ≠ true) :
    (designDomLabels (r,p)).Nodup := by
  apply List.Nodup.map_on ?_ (List.nodup_range.filter _)
  intro i hi j hj hij
  have hil := List.mem_range.1 (List.mem_of_mem_filter hi)
  have hjl := List.mem_range.1 (List.mem_of_mem_filter hj)
  let u := e₁.symm ⟨i,hil⟩
  let v := e₁.symm ⟨j,hjl⟩
  have hu : u.val ∈ X.domClass (sbipAlphaValue p) :=
    (designDomPositions_spec h e₁ he₁ e₂ he₂ p hb u).1 (by
      simpa only [u,Equiv.apply_symm_apply] using hi)
  have hv : v.val ∈ X.domClass (sbipAlphaValue p) :=
    (designDomPositions_spec h e₁ he₁ e₂ he₂ p hb v).1 (by
      simpa only [v,Equiv.apply_symm_apply] using hj)
  have hh : (⟨u.val,hu⟩ : ↥(X.domClass (sbipAlphaValue p))) = ⟨v.val,hv⟩ :=
    designDomLabel_injective h e₁ he₁ e₂ he₂ p hb hd ht (by
      change designDomLabel ((r,p),e₁ u) = designDomLabel ((r,p),e₁ v)
      simpa only [u,v,Equiv.apply_symm_apply] using hij)
  have huv : u = v := Subtype.ext (congrArg (fun z : ↥(X.domClass (sbipAlphaValue p)) => z.val) hh)
  simpa only [u,v,Equiv.apply_symm_apply] using congrArg (fun x => (e₁ x).val) huv

theorem designDomJohnson_wf (hw : r.WF) (ht : designHasDomTwins (r,p) ≠ true)
    (hbound : designDomBoundary (r,p) ≠ true) :
    RawJohnson.WF r.1.1.length (designBigPositions r).length (designDomRank (r,p))
      (designDomJohnson (r,p)) := by
  classical
  obtain ⟨x₀,hx₀⟩ := hd.dom
  let x : ↥(X.domClass (sbipAlphaValue p)) := ⟨x₀,hx₀⟩
  have hinj : ∀ u ∈ X.domClass (sbipAlphaValue p),
      ∀ v ∈ X.domClass (sbipAlphaValue p),
      X.nbhd u ∩ X.bigTwin = X.nbhd v ∩ X.bigTwin → u = v := by
    intro u hu v hv htr
    by_contra huv
    exact ht ((designHasDomTwins_spec h e₁ he₁ e₂ he₂ p hb).2 ⟨u,hu,v,hv,huv,htr⟩)
  have hbnd : X.bigTwin.ncard ≠ 2 * X.localSize x.val := by
    intro hh
    exact hbound ((designDomBoundary_spec h e₁ he₁ e₂ he₂ p hb).2 ⟨x.val,x.property,hh⟩)
  have hparams := designDom_parameters hd hinj x hbnd
  have hrank := designDomRank_spec h e₁ he₁ e₂ he₂ p hb hd x
  have hbig := designBigPositions_size h e₁ he₁ e₂ he₂
  refine ⟨by rw [hrank]; exact hparams.1,by rw [hrank,hbig]; exact hparams.2,rfl,
    ?_,designDomPoints_nodup p hw.left_nodup,by simp [designDomJohnson,designDomLabels,designDomPoints],
    ?_,?_,?_,designDomLabels_nodup h e₁ he₁ e₂ he₂ p hb hd ht,?_⟩
  · intro w hw'
    obtain ⟨i,hi,rfl⟩ := List.mem_map.1 hw'
    have hil := List.mem_range.1 (List.mem_of_mem_filter hi)
    have hm : labAt r.2.1 i ∈ r.2.1 := by
      rw [labAt,List.getD_eq_getElem _ _ hil]
      exact List.getElem_mem _
    exact (hw.table.domMem _).1 ((hw.cover _).1 (List.mem_append_left _ hm))
  · intro row hr
    obtain ⟨i,_,rfl⟩ := List.mem_map.1 hr
    exact designDomLabel_sorted _ _
  · intro row hr
    obtain ⟨i,hi,rfl⟩ := List.mem_map.1 hr
    have hil := List.mem_range.1 (List.mem_of_mem_filter hi)
    let u := e₁.symm ⟨i,hil⟩
    have hu : u.val ∈ X.domClass (sbipAlphaValue p) :=
      (designDomPositions_spec h e₁ he₁ e₂ he₂ p hb u).1 (by
        simpa only [u,Equiv.apply_symm_apply] using hi)
    have hh := designDomLabel_length h e₁ he₁ e₂ he₂ p hb hd ⟨u.val,hu⟩
    change (designDomLabel ((r,p),e₁ u)).length = _ at hh
    simpa only [u,Equiv.apply_symm_apply] using hh
  · intro row hr a ha
    obtain ⟨i,_,rfl⟩ := List.mem_map.1 hr
    exact designDomLabel_lt _ _ _ ha
  · change (designDomLabels (r,p)).length = _
    rw [designDomLabels,List.length_map,designDomPositions_size h e₁ he₁ e₂ he₂ p hb,
      hbig,hrank,designDom_choose hd hinj x]
    have hle := (hd.localSize_lt x.property).le
    by_cases hmin : X.localSize x.val ≤ X.bigTwin.ncard - X.localSize x.val
    · rw [min_eq_left hmin]
    · rw [min_eq_right (by omega),Nat.choose_symm hle]

end
end Algo
