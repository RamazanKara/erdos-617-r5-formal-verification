import Erdos617.Sat.R5CoreSemantics
import E058KernelE038Branch11Stage000

set_option maxHeartbeats 0 in
lrat_reify_stored E058SemanticE038Branch11Reified 3930
  E058KernelE038Branch11KernelProof.ctx
  E058KernelE038Branch11KernelProof

set_option maxHeartbeats 0 in
r5_specialize_reified E058SemanticE038Branch11GraphFormula
  full_exterior E058SemanticE038Branch11Reified

set_option maxHeartbeats 0 in
r5_map_reified_core E058SemanticE038Branch11NamedCore
  full_exterior E058SemanticE038Branch11GraphFormula
  ".e058-audit/cores/e038_branch_11.cnf"

set_option maxHeartbeats 0 in
r5_close_reified_core_with_units
  E058SemanticE038Branch11Contradiction
  full_exterior E058SemanticE038Branch11NamedCore
  ".e058-audit/cores/e038_branch_11.cnf"
  ".e058-audit/units/e038_branch_11.cnf"

#print axioms E058SemanticE038Branch11Contradiction
#check E058SemanticE038Branch11Contradiction
