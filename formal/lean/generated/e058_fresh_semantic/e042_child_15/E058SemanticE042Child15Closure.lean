import Erdos617.Sat.R5CoreSemantics
import E058KernelE042Child15Stage000

set_option maxHeartbeats 0 in
lrat_reify_stored E058SemanticE042Child15Reified 3930
  E058KernelE042Child15KernelProof.ctx
  E058KernelE042Child15KernelProof

set_option maxHeartbeats 0 in
r5_specialize_reified E058SemanticE042Child15GraphFormula
  full_exterior E058SemanticE042Child15Reified

set_option maxHeartbeats 0 in
r5_map_reified_core E058SemanticE042Child15NamedCore
  full_exterior E058SemanticE042Child15GraphFormula
  ".e058-audit/cores/e042_child_15.cnf"

set_option maxHeartbeats 0 in
r5_close_reified_core_with_units
  E058SemanticE042Child15Contradiction
  full_exterior E058SemanticE042Child15NamedCore
  ".e058-audit/cores/e042_child_15.cnf"
  ".e058-audit/units/e042_child_15.cnf"

#print axioms E058SemanticE042Child15Contradiction
#check E058SemanticE042Child15Contradiction
