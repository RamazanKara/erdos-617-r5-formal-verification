import Erdos617.Sat.R5CoreSemantics
import E058KernelE045Branch24Stage000

set_option maxHeartbeats 0 in
lrat_reify_stored E058SemanticE045Branch24Reified 3920
  E058KernelE045Branch24KernelProof.ctx
  E058KernelE045Branch24KernelProof

set_option maxHeartbeats 0 in
r5_specialize_reified E058SemanticE045Branch24GraphFormula
  zero_anchor E058SemanticE045Branch24Reified

set_option maxHeartbeats 0 in
r5_map_reified_core E058SemanticE045Branch24NamedCore
  zero_anchor E058SemanticE045Branch24GraphFormula
  ".e058-audit/cores/e045_branch_24.cnf"

set_option maxHeartbeats 0 in
r5_close_reified_core_with_units
  E058SemanticE045Branch24Contradiction
  zero_anchor E058SemanticE045Branch24NamedCore
  ".e058-audit/cores/e045_branch_24.cnf"
  ".e058-audit/units/e045_branch_24.cnf"

#print axioms E058SemanticE045Branch24Contradiction
#check E058SemanticE045Branch24Contradiction
