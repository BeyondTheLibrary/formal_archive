import Workspace.Algo.AggNodeUniformMatch

/-! # Audit of the complete certificate-phase machine bounds

The size invariant, cap, and all `CostQ`/`RunCostQ` fields use only standard
Lean axioms. The final phase theorem inherits the same four cited group
theory results as the original certificate theorem.
-/
#print axioms Algo.aggnPolyFun_stateSize
#print axioms Algo.aggnNormAnswer_decode
#print axioms Algo.AggnCertBound.combine
#print axioms Algo.AggnPhaseBound.combine_norm
#print axioms Algo.AggnPhaseBound.size
#print axioms Algo.aggnEnvelope_exists
#print axioms Algo.aggnBoundedCostQ
#print axioms Algo.aggnBoundedWfCheck_spec
#print axioms Algo.aggnBoundedRunCostQ
#print axioms Algo.aggnBoundedLoopMatch
#print axioms Algo.aggnBounded_certificates

#print axioms Algo.aggnPolyFun_uniformWfCheck
#print axioms Algo.aggnUniformWfCheck_spec
#print axioms Algo.aggnUniformRunCostQ
#print axioms Algo.aggnUniformLoopMatch
#print axioms Algo.aggnUniformWF_of_context
#print axioms Algo.aggnUniform_certificates
