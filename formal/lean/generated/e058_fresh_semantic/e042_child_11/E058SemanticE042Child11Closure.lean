import Erdos617.Sat.R5CoreSemantics
import E058KernelE042Child11Stage000

set_option maxHeartbeats 0 in
lrat_reify_stored E058SemanticE042Child11Reified 3930
  E058KernelE042Child11KernelProof.ctx
  E058KernelE042Child11KernelProof

set_option maxHeartbeats 0 in
r5_specialize_reified E058SemanticE042Child11GraphFormula
  full_exterior E058SemanticE042Child11Reified

set_option maxHeartbeats 0 in
r5_map_reified_core E058SemanticE042Child11NamedCore
  full_exterior E058SemanticE042Child11GraphFormula
  ".e058-audit/cores/e042_child_11.cnf"

set_option maxHeartbeats 0 in
r5_close_reified_core_with_units
  E058SemanticE042Child11Contradiction
  full_exterior E058SemanticE042Child11NamedCore
  ".e058-audit/cores/e042_child_11.cnf"
  ".e058-audit/units/e042_child_11.cnf"

#print axioms E058SemanticE042Child11Contradiction
#check E058SemanticE042Child11Contradiction
