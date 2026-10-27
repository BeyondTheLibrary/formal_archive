import Workspace.Algo.SplitBipTurnDesignChildRep
import Workspace.Algo.SplitBipTurnInitTransport
import Workspace.Algo.SplitBipTurnUpccTransport
import Workspace.Algo.SplitBipTurnLiftTransport

/-! Every graph kept by the actual turn has a corresponding kept graph at an
isomorphic represented node, and the two next inputs are isomorphic by the
restriction of the input map. The Case 3 graphs of Sec. 9.7 come from the
Design Lemma family; their correspondence is the named statement
`SbipDesign3ChildCovariant` below, proved separately.
-/
namespace Algo
open Babai RAM
open scoped Classical
set_option maxHeartbeats 1000000

/-- The conclusion shared by all child transports: two next inputs, both
represented, and an isomorphism between them that restricts `φ`. -/
def SbipChildIso {m : ℕ} (K K' : RawSbipNode) (X Y : Pt (BipBlockInputs (Fin m)))
    (φ : ↥X.car ≃ ↥Y.car) : Prop :=
  ∃ Z Z' : Pt (BipBlockInputs (Fin m)),
    SbipNodeRep m K Z ∧ SbipNodeRep m K' Z' ∧
    ∃ (hS : Z.car ⊆ X.car) (_hT : Z'.car ⊆ Y.car) (ψ : ↥Z.car ≃ ↥Z'.car),
      ψ ∈ (BipBlockInputs (Fin m)).IsoP Z Z' ∧
      ∀ x,(ψ x).val = (φ ⟨x.val,hS x.property⟩).val

/-- Sec. 9.7, Case 3: every graph that the actual Design Lemma family
passes to Reduce-Part2-by-Color has a corresponding graph at an isomorphic
parent, with isomorphic next inputs. -/
def SbipDesign3ChildCovariant : Prop :=
  ∀ (m : ℕ) (I J : RawSbipNode) (X Y : Pt (BipBlockInputs (Fin m))),
    SbipNodeRep m I X → SbipNodeRep m J Y →
    ∀ φ : ↥X.car ≃ ↥Y.car,φ ∈ (BipBlockInputs (Fin m)).IsoP X Y →
    ¬ AllClassesSmall X → ¬ Step6Imprimitive X → Step9Clique X →
    designCase12 (sbipTurnCase I.1).2 = none →
    ∀ q ∈ designCase3Graphs (sbipTurnCase I.1).2.1,
      ∃ q' ∈ designCase3Graphs (sbipTurnCase J.1).2.1,
        SbipChildIso (sbipNodeMakeChild (I,designStored ((I.1.1,sbipGraphStep9Dictionary I.1.2),q.2)))
          (sbipNodeMakeChild (J,designStored ((J.1.1,sbipGraphStep9Dictionary J.1.2),q'.2))) X Y φ

namespace SbipNodeRep
variable {m : ℕ} {I J : RawSbipNode} {X Y : Pt (BipBlockInputs (Fin m))}
    (h : SbipNodeRep m I X) (h' : SbipNodeRep m J Y)
    (φ : ↥X.car ≃ ↥Y.car) (hφ : φ ∈ (BipBlockInputs (Fin m)).IsoP X Y)
include h h' hφ

/-- Sec. 9.7: every graph kept by the DesignCase branch has its match. -/
theorem design_child_transport (hC3 : SbipDesign3ChildCovariant)
    (hd : ¬ AllClassesSmall X) (h6 : ¬ Step6Imprimitive X) (hcl : Step9Clique X)
    (o : RawAlignOutcome) (g : RawSbipStored)
    (hout : (o,some g) ∈ sbipTurnDesign (sbipTurnCase I.1)) :
    ∃ g',sbipTurnRecur g' ∈ sbipTurnDesign (sbipTurnCase J.1) ∧
      SbipChildIso (sbipNodeMakeChild (I,g)) (sbipNodeMakeChild (J,g')) X Y φ := by
  obtain ⟨h1e,h2e,_⟩ := h.design_tests_transport h' φ hφ hd h6 hcl
  unfold sbipTurnDesign at hout
  cases hcase : designCase12 (sbipTurnCase I.1).2 with
  | none =>
    simp only [hcase,Option.elim_none] at hout
    obtain ⟨q,hq,ho⟩ := List.mem_map.1 hout
    have hg := congrArg Prod.snd ho
    change some (designStored ((I.1.1,sbipGraphStep9Dictionary I.1.2),q.2)) = some g at hg
    rw [← Option.some.inj hg]
    obtain ⟨q',hq',hiso⟩ := hC3 m I J X Y h h' φ hφ hd h6 hcl hcase q hq
    refine ⟨_,?_,hiso⟩
    obtain ⟨h1,h2⟩ := (designCase12_none _).1 hcase
    have hcase' : designCase12 (sbipTurnCase J.1).2 = none :=
      (designCase12_none _).2 ⟨h1e ▸ h1,h2e ▸ h2⟩
    unfold sbipTurnDesign
    simp only [hcase',Option.elim_none]
    exact List.mem_map.2 ⟨q',hq',rfl⟩
  | some q =>
    simp only [hcase,Option.elim_some,List.mem_singleton] at hout
    rcases q with ⟨⟨L,ro⟩,q⟩
    cases q with
    | none =>
      have hh := congrArg Prod.snd hout
      cases hh
    | some q =>
      have hg := congrArg Prod.snd hout
      change some g = some (designStored ((I.1.1,sbipGraphStep9Dictionary I.1.2),q)) at hg
      rw [Option.some.inj hg]
      obtain ⟨L',o',q',hcase',hiso⟩ := h.design12_child_transport h' hd φ hφ h6 hcl L ro q hcase
      refine ⟨_,?_,hiso⟩
      unfold sbipTurnDesign
      simp only [hcase',Option.elim_some,List.mem_singleton]
      rfl

/-- Sec. 9.4, step 9: every graph kept by the Step 9 dispatch has its match. -/
theorem cases_child_transport (hC3 : SbipDesign3ChildCovariant)
    (hd : ¬ AllClassesSmall X) (h6 : ¬ Step6Imprimitive X)
    (o : RawAlignOutcome) (g : RawSbipStored)
    (hout : (o,some g) ∈ sbipTurnCases (sbipTurnCase I.1)) :
    ∃ g',sbipTurnRecur g' ∈ sbipTurnCases (sbipTurnCase J.1) ∧
      SbipChildIso (sbipNodeMakeChild (I,g)) (sbipNodeMakeChild (J,g')) X Y φ := by
  have hs := h.case_spec hd
  have ht := h.case_tag_transport h' φ hφ hd
  unfold sbipTurnCases at hout ⊢
  rw [← ht]
  split at hout
  next hi =>
    rw [if_pos hi]
    exact h.imp_child_transport h' φ hφ hd h6 (hs.1.1 hi) o g hout
  next hi =>
    rw [if_neg hi]
    split at hout
    next hcl =>
      rw [if_pos hcl]
      exact h.design_child_transport h' φ hφ hC3 hd h6 (hs.2.1.1 hcl).2 o g hout
    next hcl =>
      rw [if_neg hcl]
      have hi' : ¬ Step9Imprimitive X := fun hh => hi (hs.1.2 hh)
      have hcl' : ¬ Step9Clique X := fun hh => hcl (hs.2.1.2 ⟨hi',hh⟩)
      exact h.upcc_child_transport h' φ hφ hd h6 hi' hcl' o g hout

/-- Sec. 9.4: every graph that the actual turn keeps for a recursive call
has a matching kept graph at an isomorphic node, with isomorphic next inputs. -/
theorem node_child_transport (hC3 : SbipDesign3ChildCovariant) (c : ℕ)
    (g : RawSbipStored) (hg : g ∈ sbipNodeGraphs c I) :
    ∃ g' ∈ sbipNodeGraphs c J,
      SbipChildIso (sbipNodeMakeChild (I,g)) (sbipNodeMakeChild (J,g')) X Y φ := by
  have hearly : ¬ SbipTurnEarly c I := fun hh => by
    rw [sbipNodeGraphs_eq_nil_of_early c I hh] at hg
    cases hg
  have hearly' : ¬ SbipTurnEarly c J := fun hh => hearly
    (h'.early_of_iso h φ.symm ((BipBlockInputs (Fin m)).symm_mem hφ) c hh)
  obtain ⟨hd,h6⟩ := h.not_step6_of_not_early c hearly
  obtain ⟨o,ho⟩ := (sbipTurnChildren_mem _ g).1 hg
  rw [sbipTurn_eq_cases c I hearly] at ho
  obtain ⟨g',hg',hiso⟩ := h.cases_child_transport h' φ hφ hC3 hd h6 o g ho
  refine ⟨g',(sbipTurnChildren_mem _ g').2 ⟨(none,none),?_⟩,hiso⟩
  rw [sbipTurn_eq_cases c J hearly']
  exact hg'

end SbipNodeRep
end Algo
