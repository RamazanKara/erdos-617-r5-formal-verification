import Erdos617.Sat.R5CoreSemantics
import E058KernelE042Child00Stage022

set_option maxHeartbeats 0 in
lrat_reify_stored E058SemanticE042Child00Reified 3930
  E058KernelE042Child00Stage000.ctx
  E058KernelE042Child00KernelProof

set_option maxHeartbeats 0 in
r5_specialize_reified E058SemanticE042Child00GraphFormula
  full_exterior E058SemanticE042Child00Reified

set_option maxHeartbeats 0 in
r5_map_reified_core E058SemanticE042Child00NamedCore
  full_exterior E058SemanticE042Child00GraphFormula
  ".e058-audit/cores/e042_child_00.cnf"

set_option maxHeartbeats 0 in
r5_close_reified_core_with_units
  E058SemanticE042Child00Contradiction
  full_exterior E058SemanticE042Child00NamedCore
  ".e058-audit/cores/e042_child_00.cnf"
  ".e058-audit/units/e042_child_00.cnf"

#print axioms E058SemanticE042Child00Contradiction
#check E058SemanticE042Child00Contradiction
