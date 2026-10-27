import Workspace.Algo.AggNodeContinuationCanonical
import Workspace.Algo.AggNodeRejectMatch
import Workspace.Algo.AggNodeGuideRejectSpec

/-! Axiom audit of the Section 13.2 continuation dispatch, its exact tests and its
canonicity. -/

#print axioms Algo.aggnSideCase2b_spec
#print axioms Algo.aggnRejectCase_spec
#print axioms Algo.aggnRejectCase_iso
#print axioms Algo.aggnRejectDefect_spec
#print axioms Algo.aggnRejectDefect_iso
#print axioms Algo.aggnAggregateGuide_of_rejectDefect
#print axioms Algo.aggnCase2bSplitFamily_side_valid
#print axioms Algo.aggnQuasiFun_continuation
#print axioms Algo.aggnContinuation_tag
#print axioms Algo.aggnContinuation_one_spec
#print axioms Algo.aggnContinuation_two_spec
#print axioms Algo.aggnContinuation_zero_spec
#print axioms Algo.aggnContinuation_three_iff
#print axioms Algo.aggnContinuation_three_valid
#print axioms Algo.aggnContinuation_five_spec
#print axioms Algo.aggnContinuation_six_spec
#print axioms Algo.aggnContinuation_four_spec
#print axioms Algo.aggnRestoredEntryFamily_transport
#print axioms Algo.aggnGuideSplitPair_transport
#print axioms Algo.aggnConstituentEntry_iso
#print axioms Algo.aggnAggregateCase2b_transport
#print axioms Algo.aggnCase2bSplitFamily_transport
#print axioms Algo.aggnContinuation_transport
#print axioms Algo.aggnCase2bSplitFamily_length_le
#print axioms Algo.aggnAggregate_reject
#print axioms Algo.aggnGuideCovered_iff_tuples
#print axioms Algo.aggnContinuation_six_classes
