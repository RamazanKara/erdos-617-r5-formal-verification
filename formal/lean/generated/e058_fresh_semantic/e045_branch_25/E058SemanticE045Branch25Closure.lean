import Erdos617.Sat.R5CoreSemantics
import E058KernelE045Branch25Stage000

set_option maxHeartbeats 0 in
lrat_reify_stored E058SemanticE045Branch25Reified 3920
  E058KernelE045Branch25KernelProof.ctx
  E058KernelE045Branch25KernelProof

set_option maxHeartbeats 0 in
r5_specialize_reified E058SemanticE045Branch25GraphFormula
  zero_anchor E058SemanticE045Branch25Reified

set_option maxHeartbeats 0 in
r5_map_reified_core E058SemanticE045Branch25NamedCore
  zero_anchor E058SemanticE045Branch25GraphFormula
  ".e058-audit/cores/e045_branch_25.cnf"

set_option maxHeartbeats 0 in
r5_close_reified_core_with_units
  E058SemanticE045Branch25Contradiction
  zero_anchor E058SemanticE045Branch25NamedCore
  ".e058-audit/cores/e045_branch_25.cnf"
  ".e058-audit/units/e045_branch_25.cnf"

#print axioms E058SemanticE045Branch25Contradiction
#check E058SemanticE045Branch25Contradiction
