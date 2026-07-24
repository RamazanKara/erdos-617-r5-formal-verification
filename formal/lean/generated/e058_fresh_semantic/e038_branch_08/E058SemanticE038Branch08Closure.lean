import Erdos617.Sat.R5CoreSemantics
import E058KernelE038Branch08Stage001

set_option maxHeartbeats 0 in
lrat_reify_stored E058SemanticE038Branch08Reified 3930
  E058KernelE038Branch08Stage000.ctx
  E058KernelE038Branch08KernelProof

set_option maxHeartbeats 0 in
r5_specialize_reified E058SemanticE038Branch08GraphFormula
  full_exterior E058SemanticE038Branch08Reified

set_option maxHeartbeats 0 in
r5_map_reified_core E058SemanticE038Branch08NamedCore
  full_exterior E058SemanticE038Branch08GraphFormula
  ".e058-audit/cores/e038_branch_08.cnf"

set_option maxHeartbeats 0 in
r5_close_reified_core_with_units
  E058SemanticE038Branch08Contradiction
  full_exterior E058SemanticE038Branch08NamedCore
  ".e058-audit/cores/e038_branch_08.cnf"
  ".e058-audit/units/e038_branch_08.cnf"

#print axioms E058SemanticE038Branch08Contradiction
#check E058SemanticE038Branch08Contradiction
