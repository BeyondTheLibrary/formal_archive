import Workspace.Algo.SplitBipTurnChildTransport
import Workspace.Algo.SplitBipTurnFamily
import Workspace.Algo.SplitBipRunCanonical
import Workspace.Algo.SplitBipRunExact

/-! The recursive family of Split-or-Johnson (Sec. 9.4 with Secs. 9.6–9.8)
is canonical on the RAM: every answer at a represented node has a matching
answer at any isomorphic represented node, by the input map. The proof is
induction on the fuel. Immediate returns match by `init_transport`; a
child answer matches through the child transport and the lift. The only
premise is the Case 3 child correspondence `SbipDesign3ChildCovariant`.
-/
namespace Algo
open Babai RAM
open scoped Classical

private theorem sbipNodeAdmit_measure {I : RawSbipNode} {g : RawSbipStored}
    (h : sbipNodeAdmit (I,g) = some (sbipNodeMakeChild (I,g))) :
    sbipNodeMeasure (sbipNodeMakeChild (I,g)) < sbipNodeMeasure I := by
  unfold sbipNodeAdmit at h
  split at h
  next hh => exact hh
  next => cases h

/-- Sec. 9.4: the answers of the recursive family transport along an input
isomorphism, for any fuels above the two raw measures. -/
theorem sbipValue_transport (hC3 : SbipDesign3ChildCovariant) (c : ℕ) :
    ∀ f {m : ℕ} (I J : RawSbipNode) (X Y : Pt (BipBlockInputs (Fin m))),
      SbipNodeRep m I X → SbipNodeRep m J Y →
      ∀ φ : ↥X.car ≃ ↥Y.car,φ ∈ (BipBlockInputs (Fin m)).IsoP X Y →
      sbipNodeMeasure I < f → ∀ g,sbipNodeMeasure J < g →
      ∀ o ∈ (sbipRound c).value f I,∃ o' ∈ (sbipRound c).value g J,
        SbipNamedOutcomeIso I J X Y φ o o' := by
  intro f
  induction f with
  | zero => intro m I J X Y _ _ φ _ hf; omega
  | succ f ih =>
    intro m I J X Y h h' φ hφ hf g hg o ho
    obtain ⟨g,rfl⟩ : ∃ g0,g = g0+1 := ⟨g-1,by omega⟩
    rcases (h.value_mem_iff c f o).1 ho with hinit | ⟨gr,hgr,p,hp,rfl⟩
    · obtain ⟨o',ho',hiso⟩ := h.init_transport h' φ hφ c o hinit
      exact ⟨o',(h'.value_mem_iff c g o').2 (Or.inl ho'),hiso⟩
    · obtain ⟨gr',hgr',Z,Z',hZ,hZ',hS,hT,ψ,hψ,hval⟩ :=
        h.node_child_transport h' φ hφ hC3 c gr hgr
      have hlt := sbipNodeAdmit_measure (h.nodeGraph_admitted c gr hgr)
      have hlt' := sbipNodeAdmit_measure (h'.nodeGraph_admitted c gr' hgr')
      obtain ⟨p',hp',hiso⟩ := ih _ _ Z Z' hZ hZ' ψ hψ (by omega) g (by omega) p hp
      obtain ⟨Y0,hy0,hV0,_⟩ := h.nodeGraph_good c gr hgr
      obtain ⟨Y1,hy1,hV1,_⟩ := h'.nodeGraph_good c gr' hgr'
      have hV : BipBlockInputs.V₁ Z = step8V₁ X := by
        rw [← hZ.point_set,hy0.point_set,hV0]
      have hV' : BipBlockInputs.V₁ Z' = step8V₁ Y := by
        rw [← hZ'.point_set,hy1.point_set,hV1]
      exact ⟨_,(h'.value_mem_iff c g _).2 (Or.inr ⟨gr',hgr',p',hp',rfl⟩),
        h.lift_transport h' hZ hZ' φ hφ hV hV' hS hT ψ hval p p' hiso⟩

/-- Sec. 9.4 on the RAM: with the time and storage limits of
`exists_sbipRun_exact`, the executed family is canonical (`SbipRunCanonical`),
given the Case 3 child correspondence. -/
theorem exists_sbipRun_canonical_of_design3 (hC3 : SbipDesign3ChildCovariant) (c : ℕ) :
    ∃ t d,QuasiFun (sbipRun c t d) ∧ SbipRunCanonical c t d := by
  obtain ⟨t,d,hq,he⟩ := exists_sbipRun_exact c
  refine ⟨t,d,hq,?_⟩
  intro m I J X Y h h' φ hφ o ho
  rw [he m I ⟨X,h⟩ (sbipNodeMeasure I + 1) (by omega)] at ho
  rw [he m J ⟨Y,h'⟩ (sbipNodeMeasure J + 1) (by omega)]
  exact sbipValue_transport hC3 c _ I J X Y h h' φ hφ (by omega) _ (by omega) o ho

end Algo
