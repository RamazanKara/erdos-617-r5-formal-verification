import Erdos617.Sat.R5CoreSemantics
import E058KernelE045Branch21Stage001

set_option maxHeartbeats 0 in
lrat_reify_stored E058SemanticE045Branch21Reified 3920
  E058KernelE045Branch21Stage000.ctx
  E058KernelE045Branch21KernelProof

set_option maxHeartbeats 0 in
r5_specialize_reified E058SemanticE045Branch21GraphFormula
  zero_anchor E058SemanticE045Branch21Reified

set_option maxHeartbeats 0 in
r5_map_reified_core E058SemanticE045Branch21NamedCore
  zero_anchor E058SemanticE045Branch21GraphFormula
  ".e058-audit/cores/e045_branch_21.cnf"

set_option maxHeartbeats 0 in
r5_close_reified_core_with_units
  E058SemanticE045Branch21Contradiction
  zero_anchor E058SemanticE045Branch21NamedCore
  ".e058-audit/cores/e045_branch_21.cnf"
  ".e058-audit/units/e045_branch_21.cnf"

#print axioms E058SemanticE045Branch21Contradiction
#check E058SemanticE045Branch21Contradiction
