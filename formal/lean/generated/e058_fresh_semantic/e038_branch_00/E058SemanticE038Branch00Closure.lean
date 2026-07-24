import Erdos617.Sat.R5CoreSemantics
import E058KernelE038Branch00Stage000

set_option maxHeartbeats 0 in
lrat_reify_stored E058SemanticE038Branch00Reified 3930
  E058KernelE038Branch00KernelProof.ctx
  E058KernelE038Branch00KernelProof

set_option maxHeartbeats 0 in
r5_specialize_reified E058SemanticE038Branch00GraphFormula
  full_exterior E058SemanticE038Branch00Reified

set_option maxHeartbeats 0 in
r5_map_reified_core E058SemanticE038Branch00NamedCore
  full_exterior E058SemanticE038Branch00GraphFormula
  ".e058-audit/cores/e038_branch_00.cnf"

set_option maxHeartbeats 0 in
r5_close_reified_core_with_units
  E058SemanticE038Branch00Contradiction
  full_exterior E058SemanticE038Branch00NamedCore
  ".e058-audit/cores/e038_branch_00.cnf"
  ".e058-audit/units/e038_branch_00.cnf"

#print axioms E058SemanticE038Branch00Contradiction
#check E058SemanticE038Branch00Contradiction
