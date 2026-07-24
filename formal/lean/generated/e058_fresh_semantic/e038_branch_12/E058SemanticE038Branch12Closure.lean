import Erdos617.Sat.R5CoreSemantics
import E058KernelE038Branch12Stage000

set_option maxHeartbeats 0 in
lrat_reify_stored E058SemanticE038Branch12Reified 3930
  E058KernelE038Branch12KernelProof.ctx
  E058KernelE038Branch12KernelProof

set_option maxHeartbeats 0 in
r5_specialize_reified E058SemanticE038Branch12GraphFormula
  full_exterior E058SemanticE038Branch12Reified

set_option maxHeartbeats 0 in
r5_map_reified_core E058SemanticE038Branch12NamedCore
  full_exterior E058SemanticE038Branch12GraphFormula
  ".e058-audit/cores/e038_branch_12.cnf"

set_option maxHeartbeats 0 in
r5_close_reified_core_with_units
  E058SemanticE038Branch12Contradiction
  full_exterior E058SemanticE038Branch12NamedCore
  ".e058-audit/cores/e038_branch_12.cnf"
  ".e058-audit/units/e038_branch_12.cnf"

#print axioms E058SemanticE038Branch12Contradiction
#check E058SemanticE038Branch12Contradiction
