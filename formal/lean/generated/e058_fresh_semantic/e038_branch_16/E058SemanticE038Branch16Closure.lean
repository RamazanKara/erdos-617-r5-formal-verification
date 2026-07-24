import Erdos617.Sat.R5CoreSemantics
import E058KernelE038Branch16Stage000

set_option maxHeartbeats 0 in
lrat_reify_stored E058SemanticE038Branch16Reified 3930
  E058KernelE038Branch16KernelProof.ctx
  E058KernelE038Branch16KernelProof

set_option maxHeartbeats 0 in
r5_specialize_reified E058SemanticE038Branch16GraphFormula
  full_exterior E058SemanticE038Branch16Reified

set_option maxHeartbeats 0 in
r5_map_reified_core E058SemanticE038Branch16NamedCore
  full_exterior E058SemanticE038Branch16GraphFormula
  ".e058-audit/cores/e038_branch_16.cnf"

set_option maxHeartbeats 0 in
r5_close_reified_core_with_units
  E058SemanticE038Branch16Contradiction
  full_exterior E058SemanticE038Branch16NamedCore
  ".e058-audit/cores/e038_branch_16.cnf"
  ".e058-audit/units/e038_branch_16.cnf"

#print axioms E058SemanticE038Branch16Contradiction
#check E058SemanticE038Branch16Contradiction
