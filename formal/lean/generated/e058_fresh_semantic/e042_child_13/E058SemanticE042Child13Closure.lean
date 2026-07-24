import Erdos617.Sat.R5CoreSemantics
import E058KernelE042Child13Stage000

set_option maxHeartbeats 0 in
lrat_reify_stored E058SemanticE042Child13Reified 3930
  E058KernelE042Child13KernelProof.ctx
  E058KernelE042Child13KernelProof

set_option maxHeartbeats 0 in
r5_specialize_reified E058SemanticE042Child13GraphFormula
  full_exterior E058SemanticE042Child13Reified

set_option maxHeartbeats 0 in
r5_map_reified_core E058SemanticE042Child13NamedCore
  full_exterior E058SemanticE042Child13GraphFormula
  ".e058-audit/cores/e042_child_13.cnf"

set_option maxHeartbeats 0 in
r5_close_reified_core_with_units
  E058SemanticE042Child13Contradiction
  full_exterior E058SemanticE042Child13NamedCore
  ".e058-audit/cores/e042_child_13.cnf"
  ".e058-audit/units/e042_child_13.cnf"

#print axioms E058SemanticE042Child13Contradiction
#check E058SemanticE042Child13Contradiction
