import Erdos617.Sat.R5CoreSemantics
import E058KernelE042Child14Stage000

set_option maxHeartbeats 0 in
lrat_reify_stored E058SemanticE042Child14Reified 3930
  E058KernelE042Child14KernelProof.ctx
  E058KernelE042Child14KernelProof

set_option maxHeartbeats 0 in
r5_specialize_reified E058SemanticE042Child14GraphFormula
  full_exterior E058SemanticE042Child14Reified

set_option maxHeartbeats 0 in
r5_map_reified_core E058SemanticE042Child14NamedCore
  full_exterior E058SemanticE042Child14GraphFormula
  ".e058-audit/cores/e042_child_14.cnf"

set_option maxHeartbeats 0 in
r5_close_reified_core_with_units
  E058SemanticE042Child14Contradiction
  full_exterior E058SemanticE042Child14NamedCore
  ".e058-audit/cores/e042_child_14.cnf"
  ".e058-audit/units/e042_child_14.cnf"

#print axioms E058SemanticE042Child14Contradiction
#check E058SemanticE042Child14Contradiction
