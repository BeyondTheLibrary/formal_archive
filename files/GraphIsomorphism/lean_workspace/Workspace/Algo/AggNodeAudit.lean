import Workspace.Algo.AggNodeCalls

/-! Kernel dependency checks for the A13 session 6 call boundary. -/

#print axioms Algo.aggnLoopMatchK_first
#print axioms Algo.aggnLength_recompute
#print axioms Algo.aggnCalls_loop
#print axioms Algo.aggnCalls_certRun
#print axioms Algo.aggnCall_kernelCoset
#print axioms Algo.aggnCoset_ne_group
#print axioms Algo.aggnKer_ne_of_loop
#print axioms Algo.aggnCall_ne_recomputeInput
#print axioms Algo.aggnRecompute_calls_ne_nil
#print axioms Algo.aggnCertRun_first
#print axioms Algo.aggnDec_lcInst
#print axioms Algo.aggnAnswer_recompute
#print axioms Algo.aggnLcInst_not_mem_calls
#print axioms Algo.aggnNo_loopMatchK_certRun
#print axioms Algo.aggnNo_phaseMatch_certRun

-- These existing facts mark the read-off boundary. They are not used by
-- the obstruction above. The fullness theorem has four cited dependencies.
#print axioms Babai.run_certRun
#print axioms Babai.theorem_13_1_3
