import Erdos617.Sat.R5CoreSemantics
import E058KernelE045Branch22Stage000

set_option maxHeartbeats 0 in
lrat_reify_stored E058SemanticE045Branch22Reified 3920
  E058KernelE045Branch22KernelProof.ctx
  E058KernelE045Branch22KernelProof

set_option maxHeartbeats 0 in
r5_specialize_reified E058SemanticE045Branch22GraphFormula
  zero_anchor E058SemanticE045Branch22Reified

set_option maxHeartbeats 0 in
r5_map_reified_core E058SemanticE045Branch22NamedCore
  zero_anchor E058SemanticE045Branch22GraphFormula
  ".e058-audit/cores/e045_branch_22.cnf"

set_option maxHeartbeats 0 in
r5_close_reified_core_with_units
  E058SemanticE045Branch22Contradiction
  zero_anchor E058SemanticE045Branch22NamedCore
  ".e058-audit/cores/e045_branch_22.cnf"
  ".e058-audit/units/e045_branch_22.cnf"

#print axioms E058SemanticE045Branch22Contradiction
#check E058SemanticE045Branch22Contradiction
