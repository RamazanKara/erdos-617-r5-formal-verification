import Erdos617.Sat.R5CoreSemantics
import E058KernelE042Child12Stage000

set_option maxHeartbeats 0 in
lrat_reify_stored E058SemanticE042Child12Reified 3930
  E058KernelE042Child12KernelProof.ctx
  E058KernelE042Child12KernelProof

set_option maxHeartbeats 0 in
r5_specialize_reified E058SemanticE042Child12GraphFormula
  full_exterior E058SemanticE042Child12Reified

set_option maxHeartbeats 0 in
r5_map_reified_core E058SemanticE042Child12NamedCore
  full_exterior E058SemanticE042Child12GraphFormula
  ".e058-audit/cores/e042_child_12.cnf"

set_option maxHeartbeats 0 in
r5_close_reified_core_with_units
  E058SemanticE042Child12Contradiction
  full_exterior E058SemanticE042Child12NamedCore
  ".e058-audit/cores/e042_child_12.cnf"
  ".e058-audit/units/e042_child_12.cnf"

#print axioms E058SemanticE042Child12Contradiction
#check E058SemanticE042Child12Contradiction
