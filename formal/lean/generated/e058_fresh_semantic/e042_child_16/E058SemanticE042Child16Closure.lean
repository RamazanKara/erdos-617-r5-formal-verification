import Erdos617.Sat.R5CoreSemantics
import E058KernelE042Child16Stage000

set_option maxHeartbeats 0 in
lrat_reify_stored E058SemanticE042Child16Reified 3930
  E058KernelE042Child16KernelProof.ctx
  E058KernelE042Child16KernelProof

set_option maxHeartbeats 0 in
r5_specialize_reified E058SemanticE042Child16GraphFormula
  full_exterior E058SemanticE042Child16Reified

set_option maxHeartbeats 0 in
r5_map_reified_core E058SemanticE042Child16NamedCore
  full_exterior E058SemanticE042Child16GraphFormula
  ".e058-audit/cores/e042_child_16.cnf"

set_option maxHeartbeats 0 in
r5_close_reified_core_with_units
  E058SemanticE042Child16Contradiction
  full_exterior E058SemanticE042Child16NamedCore
  ".e058-audit/cores/e042_child_16.cnf"
  ".e058-audit/units/e042_child_16.cnf"

#print axioms E058SemanticE042Child16Contradiction
#check E058SemanticE042Child16Contradiction
