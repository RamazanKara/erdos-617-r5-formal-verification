import Erdos617.Sat.R5CoreSemantics
import E058KernelE045Branch20Stage003

set_option maxHeartbeats 0 in
lrat_reify_stored E058SemanticE045Branch20Reified 3920
  E058KernelE045Branch20Stage000.ctx
  E058KernelE045Branch20KernelProof

set_option maxHeartbeats 0 in
r5_specialize_reified E058SemanticE045Branch20GraphFormula
  zero_anchor E058SemanticE045Branch20Reified

set_option maxHeartbeats 0 in
r5_map_reified_core E058SemanticE045Branch20NamedCore
  zero_anchor E058SemanticE045Branch20GraphFormula
  ".e058-audit/cores/e045_branch_20.cnf"

set_option maxHeartbeats 0 in
r5_close_reified_core_with_units
  E058SemanticE045Branch20Contradiction
  zero_anchor E058SemanticE045Branch20NamedCore
  ".e058-audit/cores/e045_branch_20.cnf"
  ".e058-audit/units/e045_branch_20.cnf"

#print axioms E058SemanticE045Branch20Contradiction
#check E058SemanticE045Branch20Contradiction
