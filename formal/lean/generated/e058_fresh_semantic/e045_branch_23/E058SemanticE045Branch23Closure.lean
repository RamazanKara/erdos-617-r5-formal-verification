import Erdos617.Sat.R5CoreSemantics
import E058KernelE045Branch23Stage008

set_option maxHeartbeats 0 in
lrat_reify_stored E058SemanticE045Branch23Reified 3920
  E058KernelE045Branch23Stage000.ctx
  E058KernelE045Branch23KernelProof

set_option maxHeartbeats 0 in
r5_specialize_reified E058SemanticE045Branch23GraphFormula
  zero_anchor E058SemanticE045Branch23Reified

set_option maxHeartbeats 0 in
r5_map_reified_core E058SemanticE045Branch23NamedCore
  zero_anchor E058SemanticE045Branch23GraphFormula
  ".e058-audit/cores/e045_branch_23.cnf"

set_option maxHeartbeats 0 in
r5_close_reified_core_with_units
  E058SemanticE045Branch23Contradiction
  zero_anchor E058SemanticE045Branch23NamedCore
  ".e058-audit/cores/e045_branch_23.cnf"
  ".e058-audit/units/e045_branch_23.cnf"

#print axioms E058SemanticE045Branch23Contradiction
#check E058SemanticE045Branch23Contradiction
