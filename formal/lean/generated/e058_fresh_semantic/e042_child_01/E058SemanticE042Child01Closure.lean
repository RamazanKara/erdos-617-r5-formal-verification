import Erdos617.Sat.R5CoreSemantics
import E058KernelE042Child01Stage052

set_option maxHeartbeats 0 in
lrat_reify_stored E058SemanticE042Child01Reified 3930
  E058KernelE042Child01Stage000.ctx
  E058KernelE042Child01KernelProof

set_option maxHeartbeats 0 in
r5_specialize_reified E058SemanticE042Child01GraphFormula
  full_exterior E058SemanticE042Child01Reified

set_option maxHeartbeats 0 in
r5_map_reified_core E058SemanticE042Child01NamedCore
  full_exterior E058SemanticE042Child01GraphFormula
  ".e058-audit/cores/e042_child_01.cnf"

set_option maxHeartbeats 0 in
r5_close_reified_core_with_units
  E058SemanticE042Child01Contradiction
  full_exterior E058SemanticE042Child01NamedCore
  ".e058-audit/cores/e042_child_01.cnf"
  ".e058-audit/units/e042_child_01.cnf"

#print axioms E058SemanticE042Child01Contradiction
#check E058SemanticE042Child01Contradiction
