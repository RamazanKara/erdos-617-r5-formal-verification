import Erdos617.Sat.R5CoreSemantics
import E058KernelE042Child03Stage000

set_option maxHeartbeats 0 in
lrat_reify_stored E058SemanticE042Child03Reified 3930
  E058KernelE042Child03KernelProof.ctx
  E058KernelE042Child03KernelProof

set_option maxHeartbeats 0 in
r5_specialize_reified E058SemanticE042Child03GraphFormula
  full_exterior E058SemanticE042Child03Reified

set_option maxHeartbeats 0 in
r5_map_reified_core E058SemanticE042Child03NamedCore
  full_exterior E058SemanticE042Child03GraphFormula
  ".e058-audit/cores/e042_child_03.cnf"

set_option maxHeartbeats 0 in
r5_close_reified_core_with_units
  E058SemanticE042Child03Contradiction
  full_exterior E058SemanticE042Child03NamedCore
  ".e058-audit/cores/e042_child_03.cnf"
  ".e058-audit/units/e042_child_03.cnf"

#print axioms E058SemanticE042Child03Contradiction
#check E058SemanticE042Child03Contradiction
