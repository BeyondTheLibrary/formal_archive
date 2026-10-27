import Workspace.Algo.AggNodeCheckedMatch
import Workspace.Algo.AggNodeCheckedPhaseRAM

/-! # Audit of the checked certificate boundary

The child normalizer and bounds use only the standard Lean axioms. The final
certificate-store theorem inherits the cited group theory of Theorem 13.1.3.
The scan and local updates are bounded on every raw input. A full `CostQ`
state-closure proof is still a separate obligation.
-/
#print axioms Algo.aggnCheckedWindow_wf
#print axioms Algo.aggnCheckedWindow_decode
#print axioms Algo.aggnCheckedWindow_size
#print axioms Algo.aggnPolyFun_checkedWindow
#print axioms Algo.aggnCheckedRound
#print axioms Algo.aggnCheckedWF_of_context
#print axioms Algo.aggnCheckedChild_size
#print axioms Algo.aggnCalls_certPhase_strings
#print axioms Algo.aggnCheckedPhaseMatch
#print axioms Algo.aggnChecked_certificates
#print axioms Algo.aggnQuasiFun_checkedChild

#print axioms Algo.aggnPolyFun_recomputeStep
#print axioms Algo.aggnQuasiFun_certOpen
#print axioms Algo.aggnQuasiFun_certCombine
#print axioms Algo.aggnQuasiFun_map
#print axioms Algo.aggnReadyPotential_step
#print axioms Algo.aggnReadySize_iterate
#print axioms Algo.aggnPolyFun_readyScan
#print axioms Algo.aggnReadyJob_scan
#print axioms Algo.aggnQuasiFun_phaseScan
#print axioms Algo.aggnQuasiFun_phaseInit
#print axioms Algo.aggnCheckedInit_size_bound
#print axioms Algo.aggnQuasiFun_checkedCombine
#print axioms Algo.aggnPolyFun_checkedFinish
