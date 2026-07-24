import Erdos617.Sat.R5CoreSemantics
import E058KernelE038Branch18Stage000

set_option maxHeartbeats 0 in
lrat_reify_stored E058SemanticE038Branch18Reified 3930
  E058KernelE038Branch18KernelProof.ctx
  E058KernelE038Branch18KernelProof

set_option maxHeartbeats 0 in
r5_specialize_reified E058SemanticE038Branch18GraphFormula
  full_exterior E058SemanticE038Branch18Reified

set_option maxHeartbeats 0 in
r5_map_reified_core E058SemanticE038Branch18NamedCore
  full_exterior E058SemanticE038Branch18GraphFormula
  ".e058-audit/cores/e038_branch_18.cnf"

set_option maxHeartbeats 0 in
r5_close_reified_core_with_units
  E058SemanticE038Branch18Contradiction
  full_exterior E058SemanticE038Branch18NamedCore
  ".e058-audit/cores/e038_branch_18.cnf"
  ".e058-audit/units/e038_branch_18.cnf"

#print axioms E058SemanticE038Branch18Contradiction
#check E058SemanticE038Branch18Contradiction
