import Erdos617.Sat.R5CoreSemantics
import E058KernelE038Branch03Stage000

set_option maxHeartbeats 0 in
lrat_reify_stored E058SemanticE038Branch03Reified 3930
  E058KernelE038Branch03KernelProof.ctx
  E058KernelE038Branch03KernelProof

set_option maxHeartbeats 0 in
r5_specialize_reified E058SemanticE038Branch03GraphFormula
  full_exterior E058SemanticE038Branch03Reified

set_option maxHeartbeats 0 in
r5_map_reified_core E058SemanticE038Branch03NamedCore
  full_exterior E058SemanticE038Branch03GraphFormula
  ".e058-audit/cores/e038_branch_03.cnf"

set_option maxHeartbeats 0 in
r5_close_reified_core_with_units
  E058SemanticE038Branch03Contradiction
  full_exterior E058SemanticE038Branch03NamedCore
  ".e058-audit/cores/e038_branch_03.cnf"
  ".e058-audit/units/e038_branch_03.cnf"

#print axioms E058SemanticE038Branch03Contradiction
#check E058SemanticE038Branch03Contradiction
