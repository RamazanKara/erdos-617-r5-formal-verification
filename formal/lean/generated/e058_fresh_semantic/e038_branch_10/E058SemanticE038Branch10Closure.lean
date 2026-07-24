import Erdos617.Sat.R5CoreSemantics
import E058KernelE038Branch10Stage000

set_option maxHeartbeats 0 in
lrat_reify_stored E058SemanticE038Branch10Reified 3930
  E058KernelE038Branch10KernelProof.ctx
  E058KernelE038Branch10KernelProof

set_option maxHeartbeats 0 in
r5_specialize_reified E058SemanticE038Branch10GraphFormula
  full_exterior E058SemanticE038Branch10Reified

set_option maxHeartbeats 0 in
r5_map_reified_core E058SemanticE038Branch10NamedCore
  full_exterior E058SemanticE038Branch10GraphFormula
  ".e058-audit/cores/e038_branch_10.cnf"

set_option maxHeartbeats 0 in
r5_close_reified_core_with_units
  E058SemanticE038Branch10Contradiction
  full_exterior E058SemanticE038Branch10NamedCore
  ".e058-audit/cores/e038_branch_10.cnf"
  ".e058-audit/units/e038_branch_10.cnf"

#print axioms E058SemanticE038Branch10Contradiction
#check E058SemanticE038Branch10Contradiction
