import Workspace.Algo.SplitBipInputRun
import Workspace.Algo.SplitOutcomeTransport

/-! Contracts for composing the actual recursive family with the outer
reductions. The core contract retains the input carrier map. Passing to
singleton blocks changes neither this map nor the decoded answers. -/
namespace Algo
open Babai RAM
open scoped Classical

def SbipRunCanonical (c t d : ℕ) : Prop :=
  ∀ m I J (X Y : Pt (BipBlockInputs (Fin m))),
    SbipNodeRep m I X → SbipNodeRep m J Y →
    ∀ φ : ↥X.car ≃ ↥Y.car,φ ∈ (BipBlockInputs (Fin m)).IsoP X Y →
      ∀ o ∈ (sbipRun c t d I).getD [],∃ o' ∈ (sbipRun c t d J).getD [],
        SbipNamedOutcomeIso I J X Y φ o o'

def BipInputRunCanonical (c t d : ℕ) : Prop :=
  ∀ m r r' (X Y : Pt (BipInputs (Fin m))),
    BipInputRep m r X → BipInputRep m r' Y →
    ∀ (φ : ↥X.car ≃ ↥Y.car) (π : Equiv.Perm (Fin m)),
      φ ∈ (BipInputs (Fin m)).IsoP X Y → (∀ x,(φ x).val = π x.val) →
      ∀ o ∈ (bipInputRun c t d r).getD [],
        ∃ o' ∈ (bipInputRun c t d r').getD [],∃ Z Z',
          sbipDecodeNamed m r.1.2.2.1 o = some Z ∧
          sbipDecodeNamed m r'.1.2.2.1 o' = some Z' ∧ SplitOutcomeIso π Z Z'

theorem bipInputRun_canonical_of_sbip {c t d : ℕ} (h : SbipRunCanonical c t d) :
    BipInputRunCanonical c t d := by
  intro m r r' X Y hX hY φ π hφ hπ o ho
  have hi : φ ∈ (BipBlockInputs (Fin m)).IsoP (bipToBlkObj X) (bipToBlkObj Y) :=
    ⟨hφ.1,VColBip.toBlk_isIsoTo hφ.2.1 hφ.2.2.1 hφ.2.2.2⟩
  obtain ⟨o',ho',hiso⟩ := h m (bipInputNode r) (bipInputNode r') (bipToBlkObj X)
    (bipToBlkObj Y) hX.node hY.node φ hi o ho
  exact ⟨o',ho',hiso.along hπ⟩

end Algo
