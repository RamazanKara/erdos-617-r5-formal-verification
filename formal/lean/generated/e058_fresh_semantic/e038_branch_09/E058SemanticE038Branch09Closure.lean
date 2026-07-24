import Erdos617.Sat.R5CoreSemantics
import E058KernelE038Branch09Stage002

set_option maxHeartbeats 0 in
lrat_reify_stored E058SemanticE038Branch09Reified 3930
  E058KernelE038Branch09Stage000.ctx
  E058KernelE038Branch09KernelProof

set_option maxHeartbeats 0 in
r5_specialize_reified E058SemanticE038Branch09GraphFormula
  full_exterior E058SemanticE038Branch09Reified

set_option maxHeartbeats 0 in
r5_map_reified_core E058SemanticE038Branch09NamedCore
  full_exterior E058SemanticE038Branch09GraphFormula
  ".e058-audit/cores/e038_branch_09.cnf"

set_option maxHeartbeats 0 in
r5_close_reified_core_with_units
  E058SemanticE038Branch09Contradiction
  full_exterior E058SemanticE038Branch09NamedCore
  ".e058-audit/cores/e038_branch_09.cnf"
  ".e058-audit/units/e038_branch_09.cnf"

#print axioms E058SemanticE038Branch09Contradiction
#check E058SemanticE038Branch09Contradiction
