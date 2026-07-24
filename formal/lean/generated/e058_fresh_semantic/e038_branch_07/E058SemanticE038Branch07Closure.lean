import Erdos617.Sat.R5CoreSemantics
import E058KernelE038Branch07Stage002

set_option maxHeartbeats 0 in
lrat_reify_stored E058SemanticE038Branch07Reified 3930
  E058KernelE038Branch07Stage000.ctx
  E058KernelE038Branch07KernelProof

set_option maxHeartbeats 0 in
r5_specialize_reified E058SemanticE038Branch07GraphFormula
  full_exterior E058SemanticE038Branch07Reified

set_option maxHeartbeats 0 in
r5_map_reified_core E058SemanticE038Branch07NamedCore
  full_exterior E058SemanticE038Branch07GraphFormula
  ".e058-audit/cores/e038_branch_07.cnf"

set_option maxHeartbeats 0 in
r5_close_reified_core_with_units
  E058SemanticE038Branch07Contradiction
  full_exterior E058SemanticE038Branch07NamedCore
  ".e058-audit/cores/e038_branch_07.cnf"
  ".e058-audit/units/e038_branch_07.cnf"

#print axioms E058SemanticE038Branch07Contradiction
#check E058SemanticE038Branch07Contradiction
