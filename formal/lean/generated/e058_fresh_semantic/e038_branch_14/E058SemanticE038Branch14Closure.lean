import Erdos617.Sat.R5CoreSemantics
import E058KernelE038Branch14Stage001

set_option maxHeartbeats 0 in
lrat_reify_stored E058SemanticE038Branch14Reified 3930
  E058KernelE038Branch14Stage000.ctx
  E058KernelE038Branch14KernelProof

set_option maxHeartbeats 0 in
r5_specialize_reified E058SemanticE038Branch14GraphFormula
  full_exterior E058SemanticE038Branch14Reified

set_option maxHeartbeats 0 in
r5_map_reified_core E058SemanticE038Branch14NamedCore
  full_exterior E058SemanticE038Branch14GraphFormula
  ".e058-audit/cores/e038_branch_14.cnf"

set_option maxHeartbeats 0 in
r5_close_reified_core_with_units
  E058SemanticE038Branch14Contradiction
  full_exterior E058SemanticE038Branch14NamedCore
  ".e058-audit/cores/e038_branch_14.cnf"
  ".e058-audit/units/e038_branch_14.cnf"

#print axioms E058SemanticE038Branch14Contradiction
#check E058SemanticE038Branch14Contradiction
