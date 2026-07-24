import Erdos617.Sat.R5CoreSemantics
import E058KernelE038Branch04Stage000

set_option maxHeartbeats 0 in
lrat_reify_stored E058SemanticE038Branch04Reified 3930
  E058KernelE038Branch04KernelProof.ctx
  E058KernelE038Branch04KernelProof

set_option maxHeartbeats 0 in
r5_specialize_reified E058SemanticE038Branch04GraphFormula
  full_exterior E058SemanticE038Branch04Reified

set_option maxHeartbeats 0 in
r5_map_reified_core E058SemanticE038Branch04NamedCore
  full_exterior E058SemanticE038Branch04GraphFormula
  ".e058-audit/cores/e038_branch_04.cnf"

set_option maxHeartbeats 0 in
r5_close_reified_core_with_units
  E058SemanticE038Branch04Contradiction
  full_exterior E058SemanticE038Branch04NamedCore
  ".e058-audit/cores/e038_branch_04.cnf"
  ".e058-audit/units/e038_branch_04.cnf"

#print axioms E058SemanticE038Branch04Contradiction
#check E058SemanticE038Branch04Contradiction
