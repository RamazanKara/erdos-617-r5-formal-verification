import Erdos617.Sat.R5CoreSemantics
import E058KernelE038Branch17Stage000

set_option maxHeartbeats 0 in
lrat_reify_stored E058SemanticE038Branch17Reified 3930
  E058KernelE038Branch17KernelProof.ctx
  E058KernelE038Branch17KernelProof

set_option maxHeartbeats 0 in
r5_specialize_reified E058SemanticE038Branch17GraphFormula
  full_exterior E058SemanticE038Branch17Reified

set_option maxHeartbeats 0 in
r5_map_reified_core E058SemanticE038Branch17NamedCore
  full_exterior E058SemanticE038Branch17GraphFormula
  ".e058-audit/cores/e038_branch_17.cnf"

set_option maxHeartbeats 0 in
r5_close_reified_core_with_units
  E058SemanticE038Branch17Contradiction
  full_exterior E058SemanticE038Branch17NamedCore
  ".e058-audit/cores/e038_branch_17.cnf"
  ".e058-audit/units/e038_branch_17.cnf"

#print axioms E058SemanticE038Branch17Contradiction
#check E058SemanticE038Branch17Contradiction
