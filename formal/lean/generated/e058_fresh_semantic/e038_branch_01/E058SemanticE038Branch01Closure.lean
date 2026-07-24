import Erdos617.Sat.R5CoreSemantics
import E058KernelE038Branch01Stage000

set_option maxHeartbeats 0 in
lrat_reify_stored E058SemanticE038Branch01Reified 3930
  E058KernelE038Branch01KernelProof.ctx
  E058KernelE038Branch01KernelProof

set_option maxHeartbeats 0 in
r5_specialize_reified E058SemanticE038Branch01GraphFormula
  full_exterior E058SemanticE038Branch01Reified

set_option maxHeartbeats 0 in
r5_map_reified_core E058SemanticE038Branch01NamedCore
  full_exterior E058SemanticE038Branch01GraphFormula
  ".e058-audit/cores/e038_branch_01.cnf"

set_option maxHeartbeats 0 in
r5_close_reified_core_with_units
  E058SemanticE038Branch01Contradiction
  full_exterior E058SemanticE038Branch01NamedCore
  ".e058-audit/cores/e038_branch_01.cnf"
  ".e058-audit/units/e038_branch_01.cnf"

#print axioms E058SemanticE038Branch01Contradiction
#check E058SemanticE038Branch01Contradiction
