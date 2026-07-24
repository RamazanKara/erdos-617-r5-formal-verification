import Erdos617.Sat.R5CoreSemantics
import E058KernelE042Child06Stage000

set_option maxHeartbeats 0 in
lrat_reify_stored E058SemanticE042Child06Reified 3930
  E058KernelE042Child06KernelProof.ctx
  E058KernelE042Child06KernelProof

set_option maxHeartbeats 0 in
r5_specialize_reified E058SemanticE042Child06GraphFormula
  full_exterior E058SemanticE042Child06Reified

set_option maxHeartbeats 0 in
r5_map_reified_core E058SemanticE042Child06NamedCore
  full_exterior E058SemanticE042Child06GraphFormula
  ".e058-audit/cores/e042_child_06.cnf"

set_option maxHeartbeats 0 in
r5_close_reified_core_with_units
  E058SemanticE042Child06Contradiction
  full_exterior E058SemanticE042Child06NamedCore
  ".e058-audit/cores/e042_child_06.cnf"
  ".e058-audit/units/e042_child_06.cnf"

#print axioms E058SemanticE042Child06Contradiction
#check E058SemanticE042Child06Contradiction
