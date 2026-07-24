import Erdos617.Sat.R5CoreSemantics
import E058KernelE038Branch02Stage000

set_option maxHeartbeats 0 in
lrat_reify_stored E058SemanticE038Branch02Reified 3930
  E058KernelE038Branch02KernelProof.ctx
  E058KernelE038Branch02KernelProof

set_option maxHeartbeats 0 in
r5_specialize_reified E058SemanticE038Branch02GraphFormula
  full_exterior E058SemanticE038Branch02Reified

set_option maxHeartbeats 0 in
r5_map_reified_core E058SemanticE038Branch02NamedCore
  full_exterior E058SemanticE038Branch02GraphFormula
  ".e058-audit/cores/e038_branch_02.cnf"

set_option maxHeartbeats 0 in
r5_close_reified_core_with_units
  E058SemanticE038Branch02Contradiction
  full_exterior E058SemanticE038Branch02NamedCore
  ".e058-audit/cores/e038_branch_02.cnf"
  ".e058-audit/units/e038_branch_02.cnf"

#print axioms E058SemanticE038Branch02Contradiction
#check E058SemanticE038Branch02Contradiction
