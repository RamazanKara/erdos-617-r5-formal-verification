import Erdos617.Sat.R5CoreSemantics
import E058KernelE038Branch15Stage000

set_option maxHeartbeats 0 in
lrat_reify_stored E058SemanticE038Branch15Reified 3930
  E058KernelE038Branch15KernelProof.ctx
  E058KernelE038Branch15KernelProof

set_option maxHeartbeats 0 in
r5_specialize_reified E058SemanticE038Branch15GraphFormula
  full_exterior E058SemanticE038Branch15Reified

set_option maxHeartbeats 0 in
r5_map_reified_core E058SemanticE038Branch15NamedCore
  full_exterior E058SemanticE038Branch15GraphFormula
  ".e058-audit/cores/e038_branch_15.cnf"

set_option maxHeartbeats 0 in
r5_close_reified_core_with_units
  E058SemanticE038Branch15Contradiction
  full_exterior E058SemanticE038Branch15NamedCore
  ".e058-audit/cores/e038_branch_15.cnf"
  ".e058-audit/units/e038_branch_15.cnf"

#print axioms E058SemanticE038Branch15Contradiction
#check E058SemanticE038Branch15Contradiction
