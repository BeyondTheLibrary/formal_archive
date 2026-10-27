import Workspace.Algo.AggNodeGuideBuildRows

/-! # Reading the paper's guide class from a raw tuple

A set of classes gives a total specification even when no injective tuple
exists. For every legitimate tuple this set is a singleton. Thus the raw
class test can be used without choosing a default class on malformed rows.
-/
namespace Algo
open RAM RAM.Targets Babai Equiv

/-- Coordinate lists identify the underlying tuple uniquely. -/
theorem aggnTupleName_injective {m t : ℕ} :
    Function.Injective (aggnTupleName (m := m) (t := t)) := by
  intro u v h
  have h' : (fun i => (u i).val) = (fun i => (v i).val) := List.ofFn_inj.mp h
  exact funext fun i => Fin.ext (congrFun h' i)

section Keys
variable {I : Type*} {Ω : I → Type*} {k m : ℕ}
    (D : LocalGuideData I Ω k) (name : ∀ i, Ω i → Fin m)

/-- All classes represented by the named row. A valid row represents one class. -/
def aggnGuideClassKey (b : I) (row : List ℕ) : Set D.Class :=
  {Q | ∃ u : Fin k ↪ Ω b,
    aggnTupleName (fun i => name b (u i)) = row ∧ D.mkClass ⟨b,u⟩ = Q}

theorem aggnGuideClassKey_name {b : I} (hi : Function.Injective (name b))
    (u : Fin k ↪ Ω b) :
    aggnGuideClassKey D name b (aggnTupleName (fun i => name b (u i))) =
      {D.mkClass ⟨b,u⟩} := by
  ext Q
  constructor
  · rintro ⟨v,hv,hQ⟩
    have hvu : v = u := Function.Embedding.ext fun i =>
      hi (congrFun (aggnTupleName_injective hv) i)
    exact (hvu ▸ hQ).symm
  · intro hQ
    exact ⟨u,rfl,hQ.symm⟩

end Keys

/-- A computed fixed-set list has distinct, in-range names. -/
theorem aggnAggregateGuide_names {c n m : ℕ} {C : AggnPhaseCtx} {s : AggnAggregateState}
    {ϕ : decGroup n C.1.1.2 →* Perm (Fin m)}
    (hC : AggnPhaseCtxWF c n m C ϕ) (b : Bool) :
    (aggnAggregateData ((C,s),b)).2.2.Nodup ∧
      ∀ a ∈ (aggnAggregateData ((C,s),b)).2.2,a < m := by
  refine ⟨List.nodup_range.filter _,?_⟩
  intro a ha
  have hh := List.mem_range.mp (List.mem_of_mem_filter ha)
  exact hh.trans_le hC.action.2.1.le

/-- Every actual old-name row has a unique typed interpretation on the paper's fixed set. -/
theorem aggnAggregateGuideRows_complete {c n m : ℕ} {C : AggnPhaseCtx} {s : AggnAggregateState}
    {ϕ : decGroup n C.1.1.2 →* Perm (Fin m)}
    (hC : AggnPhaseCtxWF c n m C ϕ) (hs : AggnStoresComplete c ϕ s.1.2.1)
    (b : Bool) {row : List ℕ}
    (hr : row ∈ aggnGuideRows c (C.2.2.2,C.2.1,(aggnAggregateData ((C,s),b)).2.2)) :
    ∃ u : Fin C.2.2.2.length ↪ ↥(fixedGamma ϕ
      (cond b (decStrN n C.2.2.1) (decStrN n C.2.1)) C.2.2.2.length),
      aggnTupleName (fun i => (u i).val) = row := by
  obtain ⟨u,hu⟩ := aggnGuideRows_complete hC.guard (aggnAggregateGuide_names hC b).2 hr
  let e := Equiv.setCongr (aggnAggregateData_spec hC hs b).2.2
  exact ⟨u.trans e.toEmbedding,hu⟩

/-- Every paper tuple occurs in the computed old-name enumeration. -/
theorem aggnAggregateGuideRows_name {c n m : ℕ} {C : AggnPhaseCtx} {s : AggnAggregateState}
    {ϕ : decGroup n C.1.1.2 →* Perm (Fin m)}
    (hC : AggnPhaseCtxWF c n m C ϕ) (hs : AggnStoresComplete c ϕ s.1.2.1)
    (b : Bool) (u : Fin C.2.2.2.length ↪ ↥(fixedGamma ϕ
      (cond b (decStrN n C.2.2.1) (decStrN n C.2.1)) C.2.2.2.length)) :
    aggnTupleName (fun i => (u i).val) ∈
      aggnGuideRows c (C.2.2.2,C.2.1,(aggnAggregateData ((C,s),b)).2.2) := by
  let e := Equiv.setCongr (aggnAggregateData_spec hC hs b).2.2.symm
  exact aggnGuideRows_name hC.guard (u.trans e.toEmbedding)

end Algo
