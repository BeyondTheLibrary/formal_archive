import Workspace.Algo.AggNodeLine57Match
import Workspace.Algo.AggNodeLine57RAM
import Workspace.Algo.AlignDomLargeMatch
import Workspace.Algo.AggNodeLine57GiantMatch
import Workspace.Algo.AggNodeLine57GiantRAM
import Workspace.Algo.AlignDescentFacts

/-! Axiom audit of the round of Sec. 15, lines 5–7, and of the loop of Procedure Align over
the versions. -/

#print axioms Algo.phaseMatch_alignVersions
#print axioms Algo.phaseMatch_alignShape_value
#print axioms Algo.alignOutcomeLab_eq_iff
#print axioms Algo.polyFun_alignOutcomeLab
#print axioms Algo.polyFun_avCombine
#print axioms Algo.polyFun_avChild
#print axioms Algo.aggnL57Calls_bdd
#print axioms Algo.aggnL57_align_match
#print axioms Algo.aggnL57_nil_match
#print axioms Algo.aggnL57_rejectCase_match
#print axioms Algo.aggnL57_rejectDefect_match
#print axioms Algo.aggnL57_hasRunCostQ
#print axioms Algo.aggnL57_align_match_small
#print axioms Algo.phaseMatch_adShape
#print axioms Algo.phaseMatch_adVersions
#print axioms Algo.quasiFun_adCombine
#print axioms Algo.quasiFun_adChild
#print axioms Algo.adRem_combine
#print axioms Algo.adStep_size_bdd
#print axioms Algo.l57Small_iff
#print axioms Algo.ADDescribes.mk'
#print axioms Algo.allCalls_top4AggregateTree
#print axioms Algo.aggnL57G_giant_match
#print axioms Algo.aggnL57G_align_match
#print axioms Algo.aggnL57G_align_match_small
#print axioms Algo.aggnL57G_nil_match
#print axioms Algo.aggnL57G_rejectCase_match
#print axioms Algo.aggnL57G_rejectDefect_match
#print axioms Algo.exists_l57GWFOK
#print axioms Algo.aggnL57G_hasRunCostQ
