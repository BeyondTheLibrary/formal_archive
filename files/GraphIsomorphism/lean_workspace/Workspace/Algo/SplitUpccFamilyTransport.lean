import Workspace.Algo.SplitUpccCaseOutcome

/-! Each block choice in the UPCC family has the same branch decision
after an input isomorphism, even when the compact orders are independent.
-/
namespace Algo
open Babai RAM
open scoped Classical

section
variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {s t : Set Ω}
    {X : UPCCObj s} {Y : UPCCObj t} {φ : ↥s ≃ ↥t}
    (hφ : φ ∈ (BlkUPCCCases Ω).Iso X Y)
    {n n' : ℕ} (e : ↥X.vtxSet ≃ Fin n) (e' : ↥Y.vtxSet ≃ Fin n')
    {r r' : RawUpccCase} (hw : r.WF) (hw' : r'.WF)
    (hn : UpccCaseNames X e r) (hn' : UpccCaseNames Y e' r')
include hφ hw hw' hn hn'

theorem upccCaseSplits_transport (B : ↥X.blocks) :
    upccCaseSplits (r,upccCaseName₂ X e B) =
      upccCaseSplits (r',upccCaseName₂ Y e' ⟨φ '' B.val,(hφ.2.1 B.val).2 B.property⟩) := by
  apply Bool.eq_iff_iff.mpr
  rw [upccCaseSplits_spec X e hw hn,upccCaseSplits_spec Y e' hw' hn']
  apply forall_congr'
  intro k
  simpa only [BlkCaseObj.IsBigColor₂,not_lt] using
    (not_congr (upcc_isBigColor₂_map hφ B.val k)).symm

end
end Algo
