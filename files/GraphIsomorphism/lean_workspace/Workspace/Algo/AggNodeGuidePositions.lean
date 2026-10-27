import Workspace.Algo.AggNodeGuideClassKey

/-! # Compact vertices name the actual fixed set

Each returned guide structure uses consecutive local labels. This explicit
bijection identifies those labels with the fixed set computed from the
completed certificate store, and pulls every local tuple back to old names.
-/
namespace Algo
open RAM RAM.Targets Babai Equiv

/-- The computed list, including its actual order, gives the subset bijection. -/
noncomputable def aggnAggregateGuideEquiv {c n m : ℕ} {C : AggnPhaseCtx} {s : AggnAggregateState}
    {ϕ : decGroup n C.1.1.2 →* Perm (Fin m)}
    (hC : AggnPhaseCtxWF c n m C ϕ) (hs : AggnStoresComplete c ϕ s.1.2.1) (b : Bool) :
    Fin (aggnAggregateData ((C,s),b)).2.2.length ≃ ↥(fixedGamma ϕ
      (cond b (decStrN n C.2.2.1) (decStrN n C.2.1)) C.2.2.2.length) :=
  (winEquiv m _ (aggnAggregateGuide_names hC b).1 (aggnAggregateGuide_names hC b).2).trans
    (Equiv.setCongr (aggnAggregateData_spec hC hs b).2.2)

theorem aggnAggregateGuideEquiv_name {c n m : ℕ} {C : AggnPhaseCtx} {s : AggnAggregateState}
    {ϕ : decGroup n C.1.1.2 →* Perm (Fin m)}
    (hC : AggnPhaseCtxWF c n m C ϕ) (hs : AggnStoresComplete c ϕ s.1.2.1) (b : Bool)
    (i : Fin (aggnAggregateData ((C,s),b)).2.2.length) :
    ((aggnAggregateGuideEquiv hC hs b i).val).val = (aggnAggregateData ((C,s),b)).2.2[i.val] :=
  congrArg Fin.val (winEquiv_coe _ (aggnAggregateGuide_names hC b).1 (aggnAggregateGuide_names hC b).2 i.isLt)

/-- Pullback through the stored names is the exact mathematical tuple map. -/
theorem aggnAggregateGuide_tuple_pullback {c n m k : ℕ} {C : AggnPhaseCtx} {s : AggnAggregateState}
    {ϕ : decGroup n C.1.1.2 →* Perm (Fin m)}
    (hC : AggnPhaseCtxWF c n m C ϕ) (hs : AggnStoresComplete c ϕ s.1.2.1) (b : Bool)
    (v : Fin k → Fin (aggnAggregateData ((C,s),b)).2.2.length) :
    rawRestrictStr ((aggnAggregateData ((C,s),b)).2.2,aggnTupleName v) =
      aggnTupleName (fun i => (aggnAggregateGuideEquiv hC hs b (v i)).val) := by
  simp only [rawRestrictStr,aggnTupleName,List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  rw [aggnAggregateGuideEquiv_name]
  exact List.getD_eq_getElem _ _ (v i).isLt

/-- Every compact row has an injective interpretation on the numbered vertices. -/
theorem aggnGuideSideRows_complete {c : ℕ} {ks dom D row : List ℕ}
    (hg : ks.length ≤ guardBound c dom.length)
    (hr : row ∈ (aggnGuideSideRows c ((ks,dom),D)).2) :
    ∃ u : Fin ks.length ↪ Fin D.length,aggnTupleName u = row := by
  obtain ⟨u,hu⟩ := aggnGuideRows_complete (m := D.length) hg
    (fun _ h => List.mem_range.mp h) hr
  exact ⟨u.trans ⟨Subtype.val,Subtype.val_injective⟩,hu⟩

/-- Every injective numbered tuple occurs in the compact enumeration. -/
theorem aggnGuideSideRows_name {c : ℕ} {ks dom D : List ℕ}
    (hg : ks.length ≤ guardBound c dom.length) (u : Fin ks.length ↪ Fin D.length) :
    aggnTupleName u ∈ (aggnGuideSideRows c ((ks,dom),D)).2 := by
  apply (aggnGuideRows_mem hg).mpr
  refine ⟨aggnTupleName_length _,?_,aggnTupleName_nodup u.injective⟩
  intro a ha
  exact List.mem_range.mpr (aggnTupleName_lt u a ha)

end Algo
