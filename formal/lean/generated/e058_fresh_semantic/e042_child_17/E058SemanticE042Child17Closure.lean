import Erdos617.Sat.R5CoreSemantics
import E058KernelE042Child17Stage000

set_option maxHeartbeats 0 in
lrat_reify_stored E058SemanticE042Child17Reified 3930
  E058KernelE042Child17KernelProof.ctx
  E058KernelE042Child17KernelProof

set_option maxHeartbeats 0 in
r5_specialize_reified E058SemanticE042Child17GraphFormula
  full_exterior E058SemanticE042Child17Reified

set_option maxHeartbeats 0 in
r5_map_reified_core E058SemanticE042Child17NamedCore
  full_exterior E058SemanticE042Child17GraphFormula
  ".e058-audit/cores/e042_child_17.cnf"

set_option maxHeartbeats 0 in
r5_close_reified_core_with_units
  E058SemanticE042Child17Contradiction
  full_exterior E058SemanticE042Child17NamedCore
  ".e058-audit/cores/e042_child_17.cnf"
  ".e058-audit/units/e042_child_17.cnf"

#print axioms E058SemanticE042Child17Contradiction
#check E058SemanticE042Child17Contradiction
