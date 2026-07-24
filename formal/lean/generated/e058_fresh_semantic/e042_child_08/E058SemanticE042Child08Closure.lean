import Erdos617.Sat.R5CoreSemantics
import E058KernelE042Child08Stage000

set_option maxHeartbeats 0 in
lrat_reify_stored E058SemanticE042Child08Reified 3930
  E058KernelE042Child08KernelProof.ctx
  E058KernelE042Child08KernelProof

set_option maxHeartbeats 0 in
r5_specialize_reified E058SemanticE042Child08GraphFormula
  full_exterior E058SemanticE042Child08Reified

set_option maxHeartbeats 0 in
r5_map_reified_core E058SemanticE042Child08NamedCore
  full_exterior E058SemanticE042Child08GraphFormula
  ".e058-audit/cores/e042_child_08.cnf"

set_option maxHeartbeats 0 in
r5_close_reified_core_with_units
  E058SemanticE042Child08Contradiction
  full_exterior E058SemanticE042Child08NamedCore
  ".e058-audit/cores/e042_child_08.cnf"
  ".e058-audit/units/e042_child_08.cnf"

#print axioms E058SemanticE042Child08Contradiction
#check E058SemanticE042Child08Contradiction
