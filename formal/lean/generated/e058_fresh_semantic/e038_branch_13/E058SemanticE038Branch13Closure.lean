import Erdos617.Sat.R5CoreSemantics
import E058KernelE038Branch13Stage000

set_option maxHeartbeats 0 in
lrat_reify_stored E058SemanticE038Branch13Reified 3930
  E058KernelE038Branch13KernelProof.ctx
  E058KernelE038Branch13KernelProof

set_option maxHeartbeats 0 in
r5_specialize_reified E058SemanticE038Branch13GraphFormula
  full_exterior E058SemanticE038Branch13Reified

set_option maxHeartbeats 0 in
r5_map_reified_core E058SemanticE038Branch13NamedCore
  full_exterior E058SemanticE038Branch13GraphFormula
  ".e058-audit/cores/e038_branch_13.cnf"

set_option maxHeartbeats 0 in
r5_close_reified_core_with_units
  E058SemanticE038Branch13Contradiction
  full_exterior E058SemanticE038Branch13NamedCore
  ".e058-audit/cores/e038_branch_13.cnf"
  ".e058-audit/units/e038_branch_13.cnf"

#print axioms E058SemanticE038Branch13Contradiction
#check E058SemanticE038Branch13Contradiction
