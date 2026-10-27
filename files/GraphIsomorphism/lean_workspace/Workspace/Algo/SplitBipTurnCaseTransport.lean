import Workspace.Algo.SplitBipTurnEarlyFamily
import Workspace.Algo.SplitImprimitiveStoredTransport

/-! The three Step 9 dispatch tags agree after the actual preparations
of isomorphic stored inputs. No agreement of raw compact list orders is
required: both tables are read through the canonical Step 8 coloring.
-/
namespace Algo
open Babai RAM
open scoped Classical
namespace SbipNodeRep
variable {m : ℕ} {I J : RawSbipNode} {X Y : Pt (BipBlockInputs (Fin m))}
    (h : SbipNodeRep m I X) (h' : SbipNodeRep m J Y)
    (φ : ↥X.car ≃ ↥Y.car) (hφ : φ ∈ (BipBlockInputs (Fin m)).IsoP X Y)
include h

theorem case_spec (hd : ¬ AllClassesSmall X) :
    (sbipStep9Case (sbipTurnCase I.1).2.1 = 0 ↔ Step9Imprimitive X) ∧
    (sbipStep9Case (sbipTurnCase I.1).2.1 = 1 ↔ ¬ Step9Imprimitive X ∧ Step9Clique X) ∧
    (sbipStep9Case (sbipTurnCase I.1).2.1 = 2 ↔ ¬ Step9Imprimitive X ∧ ¬ Step9Clique X) := by
  obtain ⟨name,e,hc,hs,hf,hnd,he,hp,hr⟩ := h.names
  obtain ⟨e9,he9⟩ := sbipGraphStep9_equiv_exists X name (sbipTurnGraphInput I.1) hc hnd e he hp hr
    h.alpha h.denominator h.left_nodup hd
  exact sbipGraphStep9Input_case X name (sbipTurnGraphInput I.1) hc hnd e he hp hr
    h.alpha h.denominator h.left_nodup hd e9 he9

include h' hφ

theorem case_tag_transport (hd : ¬ AllClassesSmall X) :
    sbipStep9Case (sbipTurnCase I.1).2.1 = sbipStep9Case (sbipTurnCase J.1).2.1 := by
  have hd' : ¬ AllClassesSmall Y := fun hh => hd
    (allClassesSmall_congr ⟨φ.symm,(BipBlockInputs (Fin m)).symm_mem hφ⟩ hh)
  have hi : Step9Imprimitive X ↔ Step9Imprimitive Y :=
    ⟨step9Imprimitive_congr ⟨φ,hφ⟩,
      step9Imprimitive_congr ⟨φ.symm,(BipBlockInputs (Fin m)).symm_mem hφ⟩⟩
  have hc : Step9Clique X ↔ Step9Clique Y :=
    ⟨step9Clique_congr ⟨φ,hφ⟩,
      step9Clique_congr ⟨φ.symm,(BipBlockInputs (Fin m)).symm_mem hφ⟩⟩
  have hs := h.case_spec hd
  have hs' := h'.case_spec hd'
  by_cases himp : Step9Imprimitive X
  · exact (hs.1.2 himp).trans (hs'.1.2 (hi.1 himp)).symm
  by_cases hcl : Step9Clique X
  · exact (hs.2.1.2 ⟨himp,hcl⟩).trans (hs'.2.1.2 ⟨fun hh => himp (hi.2 hh),hc.1 hcl⟩).symm
  · exact (hs.2.2.2 ⟨himp,hcl⟩).trans
      (hs'.2.2.2 ⟨fun hh => himp (hi.2 hh),fun hh => hcl (hc.2 hh)⟩).symm

end SbipNodeRep
end Algo
