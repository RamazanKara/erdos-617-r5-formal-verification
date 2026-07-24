import Erdos617.Sat.R5CoreSemantics
import E058KernelE042Child10Stage000

set_option maxHeartbeats 0 in
lrat_reify_stored E058SemanticE042Child10Reified 3930
  E058KernelE042Child10KernelProof.ctx
  E058KernelE042Child10KernelProof

set_option maxHeartbeats 0 in
r5_specialize_reified E058SemanticE042Child10GraphFormula
  full_exterior E058SemanticE042Child10Reified

set_option maxHeartbeats 0 in
r5_map_reified_core E058SemanticE042Child10NamedCore
  full_exterior E058SemanticE042Child10GraphFormula
  ".e058-audit/cores/e042_child_10.cnf"

set_option maxHeartbeats 0 in
r5_close_reified_core_with_units
  E058SemanticE042Child10Contradiction
  full_exterior E058SemanticE042Child10NamedCore
  ".e058-audit/cores/e042_child_10.cnf"
  ".e058-audit/units/e042_child_10.cnf"

#print axioms E058SemanticE042Child10Contradiction
#check E058SemanticE042Child10Contradiction
