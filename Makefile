PYTHON ?= python3
CC ?= cc
CFLAGS ?= -std=c11 -O2 -Wall -Wextra -Werror -pedantic
FAST_TMP ?= /tmp

BUILD_DIR := build
C_CHECKER := $(BUILD_DIR)/check_coloring_c
LRAT_CHECKER := $(BUILD_DIR)/lrat-check-upstream
DRAT_TRIM := $(BUILD_DIR)/drat-trim-upstream
AFFINE := artifacts/affine25.col
LOCAL_EQUALITY_CNF := artifacts/local_equality.cnf
LOCAL_EQUALITY_LRAT := certificates/local_equality.lrat
LOCAL_205_NEAR_CNF := artifacts/local_205_near.cnf
LOCAL_205_NEAR_CORE := artifacts/local_205_near_core.cnf
LOCAL_205_NEAR_LRAT := certificates/local_205_near.lrat.xz
LOCAL_209_CLASSIFIED_PARTIAL := \
	balanced_double45_44__variable45__b4555_small_a1 \
	balanced_double45_44__variable45__b4555_small_a2 \
	balanced_double45_44__variable45__b4555_large_a1 \
	unbalanced_double49_40__l205_5555_a1__variable40 \
	unbalanced_double49_40__l205_5555_a2__variable40 \
	unbalanced_double49_44__l205_5555_a1__b4555_small_a1 \
	unbalanced_double49_44__l205_5555_a1__b4555_small_a2 \
	unbalanced_double49_44__l205_5555_a1__b4555_large_a1 \
	unbalanced_double49_44__l205_5555_a1__b4555_large_a2 \
	unbalanced_double49_44__l205_5555_a2__b4555_small_a1 \
	unbalanced_double49_44__l205_5555_a2__b4555_small_a2 \
	unbalanced_double49_44__l205_5555_a2__b4555_large_a1 \
	unbalanced_double49_44__l205_5555_a2__b4555_large_a2

.PHONY: all verify test verify-r5-special-brooks verify-e058-unit verify-r5-kp-large reproduce-certificate reproduce-local-204 reproduce-local-205 reproduce-local-206 reproduce-local-207 reproduce-local-205-near reproduce-local-206-near reproduce-local-207-near reproduce-local-208 reproduce-local-208-classified clean

all: $(C_CHECKER) $(LRAT_CHECKER) $(AFFINE)

$(BUILD_DIR):
	mkdir -p $(BUILD_DIR)

$(C_CHECKER): src/check_coloring.c | $(BUILD_DIR)
	$(CC) $(CFLAGS) $< -o $@

# The pinned upstream checker intentionally ignores one diagnostic-only fgets
# result. Suppressing that single warning leaves its binary unchanged.
$(LRAT_CHECKER): third_party/drat-trim/lrat-check.c | $(BUILD_DIR)
	$(CC) -std=c99 -O2 -DLONGTYPE -Wno-unused-result $< -o $@

$(DRAT_TRIM): third_party/drat-trim/drat-trim.c | $(BUILD_DIR)
	$(CC) -std=c99 -O2 $< -o $@

$(AFFINE): src/generate_affine25.py
	$(PYTHON) $< $@

test: $(C_CHECKER) $(LRAT_CHECKER) $(AFFINE)
	$(PYTHON) tests/test_pipeline.py --python-checker src/check_coloring.py --c-checker $(C_CHECKER) --generator src/generate_affine25.py --artifact $(AFFINE)
	$(PYTHON) tests/test_lrat.py --cnf $(LOCAL_EQUALITY_CNF) --proof $(LOCAL_EQUALITY_LRAT) --c-checker $(LRAT_CHECKER) --python-checker src/check_lrat.py
	$(PYTHON) tests/test_local_204_generator.py
	$(PYTHON) tests/test_local_205_near_generator.py
	$(PYTHON) tests/test_local_206_reduction.py
	$(PYTHON) tests/test_local_206_near_generator.py
	$(PYTHON) tests/test_local_207_reduction.py
	$(PYTHON) tests/test_local_207_near_generator.py
	$(PYTHON) tests/test_local_208_reduction.py
	$(PYTHON) tests/test_local_208_near_generator.py
	$(PYTHON) tests/test_local_208_double_generator.py
	$(PYTHON) tests/test_local_208_double_classified_generator.py
	$(PYTHON) tests/test_local_208_double_classified_hard_generator.py
	$(PYTHON) tests/test_local_209_reduction.py
	$(PYTHON) tests/test_local_209_deletion_bridges.py
	$(PYTHON) tests/test_local_209_near_generator.py
	$(PYTHON) tests/test_local_209_double_generator.py
	$(PYTHON) tests/test_local_209_mixed_double_generator.py
	$(PYTHON) tests/test_local_209_double_classified_generator.py
	$(PYTHON) tests/test_local_209_double_classified_hard_generator.py
	$(PYTHON) tests/test_local_209_double_classified_u50_canonical_generator.py
	$(PYTHON) tests/test_local_209_double_classified_u50_full_canonical_generator.py
	$(PYTHON) tests/test_local_209_double_classified_mixed_canonical_generator.py
	$(PYTHON) tests/test_local_209_balanced_counter_split_generator.py
	$(PYTHON) tests/test_local_209_balanced_counter_refinement_generator.py
	$(PYTHON) tests/test_local_209_u50_a1_counter_refinement_generator.py
	$(PYTHON) tests/test_local_209_u50_counter_cascade_generator.py
	$(PYTHON) tests/test_local_209_u50_counter_cascade2_generator.py
	$(PYTHON) tests/test_local_209_u50_counter_cascade3_generator.py
	$(PYTHON) tests/test_local_209_u50_exact27_secondary_generator.py
	$(PYTHON) tests/test_local_209_u50_exact27_secondary_low_generator.py
	$(PYTHON) tests/test_local_209_u50_exact24_tertiary_generator.py
	$(PYTHON) tests/test_local_209_u50_tertiary_positive_refinement_generator.py
	$(PYTHON) tests/test_local_209_u50_refine5294_negative_refinement_generator.py
	$(PYTHON) tests/test_local_209_u50_refine5704_positive_refinement_generator.py
	$(PYTHON) tests/test_local_209_u50_refine5242_positive_refinement_generator.py
	$(PYTHON) tests/test_local_209_unbalanced_refine7279_positive_refinement_generator.py
	$(PYTHON) tests/test_local_209_hard_refine6080_negative_refinement_generator.py
	$(PYTHON) tests/test_local_209_hard_availability_generator.py
	$(PYTHON) tests/test_local_209_remaining_availability_generator.py
	$(PYTHON) tests/test_local_209_split_composer_inputs.py
	$(PYTHON) tests/test_dimacs_model_checker.py
	$(PYTHON) tests/test_lrat_split_lifter.py
	$(PYTHON) tests/test_lrat_full.py
	$(PYTHON) tests/test_full_k26_cnf.py --generator src/generate_full_k26_cnf.py
	$(PYTHON) tests/test_local_210_reduction.py
	$(PYTHON) tests/test_local_210_exact_generator.py
	$(PYTHON) tests/test_local_210_coloring_generator.py
	$(PYTHON) tests/test_full_k26_minority_cnf.py
	$(PYTHON) tests/test_full_k26_min_degree_branch_cnf.py
	$(PYTHON) tests/test_full_k26_minority59_cnf.py
	$(PYTHON) tests/test_full_k26_minority59_certificates.py
	$(PYTHON) tests/test_full_k26_minority60_cnf.py
	$(PYTHON) tests/test_full_k26_minority60_critical_cnf.py
	$(PYTHON) tests/test_full_k26_minority60_fixed_witness_cnf.py
	$(PYTHON) tests/test_full_k26_minority60_canonical_witness_cnf.py
	$(PYTHON) tests/test_minority60_critical_graph_cnf.py
	$(PYTHON) tests/test_minority60_degree4_structure_cnf.py
	$(PYTHON) tests/test_minority60_spoke_critical_cnf.py
	$(PYTHON) tests/test_full_k26_fixed_minority_graph_cnf.py
	$(PYTHON) tests/test_minority60_recursive_reduction.py
	$(PYTHON) tests/test_residual11_classification_cnf.py
	$(PYTHON) tests/test_minority60_recursive_certificates.py
	$(PYTHON) tests/test_minority61_recursive_reduction.py
	$(PYTHON) tests/test_minority61_triangle_residual_cnf.py
	$(PYTHON) tests/test_minority61_candidate_extension_cnf.py
	$(PYTHON) tests/test_minority61_certificates.py
	$(PYTHON) tests/test_minority62_reduction.py
	$(PYTHON) tests/test_minority62_triangle_residual_cnf.py
	$(PYTHON) tests/test_minority62_candidate_extension_cnf.py
	$(PYTHON) tests/test_minority62_certificates.py
	$(PYTHON) tests/test_minority63_reduction.py
	$(PYTHON) tests/test_minority63_component_family_cnf.py
	$(PYTHON) tests/test_minority63_critical_component_family_cnf.py
	$(PYTHON) tests/test_minority63_refined_family_cnf.py
	$(PYTHON) tests/test_minority63_min_degree_family_cnf.py
	$(PYTHON) tests/test_minority63_k4_k5_k5_family_cnf.py
	$(PYTHON) tests/test_minority63_all_color_lower_cnf.py
	$(PYTHON) tests/test_minority63_residual12_cnf.py
	$(PYTHON) tests/test_minority63_residual11_cnf.py
	$(PYTHON) tests/test_minority63_candidate_extension_cnf.py
	$(PYTHON) tests/test_minority63_q16_critical_family_cnf.py
	$(PYTHON) tests/test_minority63_q16_graph_cnf.py
	$(PYTHON) tests/test_minority63_q16_ore_extension_cnf.py
	$(PYTHON) tests/test_minority63_certificates.py
	$(PYTHON) tests/test_external_r5_proof_audit.py
	$(PYTHON) tests/test_r5_five_regular_brooks_cnf.py
	$(PYTHON) tests/test_r5_brooks_neighborhood_branch_cnf.py
	$(PYTHON) tests/test_r5_brooks_exterior_sorted_cnf.py
	$(PYTHON) tests/test_r5_brooks_first_pattern_cnf.py
	$(PYTHON) tests/test_r5_brooks_k4_local_cnf.py
	$(PYTHON) tests/test_r5_brooks_branch19_cross_pattern_cnf.py
	$(PYTHON) tests/test_r5_brooks_zero_pattern_neighborhood_cnf.py
	$(PYTHON) tests/test_r5_brooks_closed_neighborhood_admissibility_cnf.py
	$(PYTHON) tests/test_r5_brooks_zero_anchor_quotient_cnf.py
	$(PYTHON) tests/test_r5_kp_large_specialization_cnf.py
	$(PYTHON) tests/test_r5_kp_average_degree_anchor_cnf.py

verify: $(C_CHECKER) $(LRAT_CHECKER) $(AFFINE)
	$(PYTHON) src/check_coloring.py $(AFFINE) --expect-n 25 --expect-r 5 --expect-k 6
	$(C_CHECKER) $(AFFINE) 25 5 6
	$(PYTHON) src/verify_affine_nonextension.py $(AFFINE) > $(BUILD_DIR)/affine_nonextension.json
	cmp $(BUILD_DIR)/affine_nonextension.json artifacts/affine_nonextension.json
	$(PYTHON) src/verify_triangle_bound.py > $(BUILD_DIR)/triangle_bound.json
	cmp $(BUILD_DIR)/triangle_bound.json artifacts/triangle_bound.json
	$(PYTHON) src/generate_local_equality_cnf.py $(BUILD_DIR)/local_equality.cnf
	cmp $(BUILD_DIR)/local_equality.cnf $(LOCAL_EQUALITY_CNF)
	$(LRAT_CHECKER) $(LOCAL_EQUALITY_CNF) $(LOCAL_EQUALITY_LRAT)
	$(PYTHON) src/check_lrat.py $(LOCAL_EQUALITY_CNF) $(LOCAL_EQUALITY_LRAT)
	$(PYTHON) tests/test_pipeline.py --python-checker src/check_coloring.py --c-checker $(C_CHECKER) --generator src/generate_affine25.py --artifact $(AFFINE)
	$(PYTHON) tests/test_lrat.py --cnf $(LOCAL_EQUALITY_CNF) --proof $(LOCAL_EQUALITY_LRAT) --c-checker $(LRAT_CHECKER) --python-checker src/check_lrat.py
	$(PYTHON) tests/test_local_204_generator.py
	$(PYTHON) tests/verify_local_204_certificates.py --cnf-directory artifacts/local_204 --proof-directory certificates/local_204 --c-checker $(LRAT_CHECKER) --python-checker src/check_lrat.py
	$(PYTHON) tests/verify_local_204_certificates.py --family 205 --cnf-directory artifacts/local_205 --proof-directory certificates/local_205 --c-checker $(LRAT_CHECKER) --python-checker src/check_lrat.py
	$(PYTHON) tests/test_local_205_near_generator.py
	TMPDIR=$(FAST_TMP) $(PYTHON) tests/verify_local_205_near_certificate.py --cnf $(LOCAL_205_NEAR_CNF) --core $(LOCAL_205_NEAR_CORE) --proof $(LOCAL_205_NEAR_LRAT) --subset-checker src/check_cnf_subset.py --c-checker $(LRAT_CHECKER) --python-checker src/check_lrat.py
	$(PYTHON) tests/test_local_206_reduction.py
	$(PYTHON) tests/test_local_206_near_generator.py
	$(PYTHON) tests/verify_local_204_certificates.py --family 206 --cnf-directory artifacts/local_206 --proof-directory certificates/local_206 --c-checker $(LRAT_CHECKER) --python-checker src/check_lrat.py
	TMPDIR=$(FAST_TMP) $(PYTHON) tests/verify_local_206_near_certificates.py --cnf-directory artifacts/local_206_near --proof-directory certificates/local_206_near --c-checker $(LRAT_CHECKER) --python-checker src/check_lrat.py
	$(PYTHON) tests/test_local_207_reduction.py
	$(PYTHON) tests/test_local_207_near_generator.py
	$(PYTHON) tests/verify_local_204_certificates.py --family 207 --cnf-directory artifacts/local_207 --proof-directory certificates/local_207 --c-checker $(LRAT_CHECKER) --python-checker src/check_lrat.py
	TMPDIR=$(FAST_TMP) $(PYTHON) tests/verify_local_207_near_certificates.py --cnf-directory artifacts/local_207_near --proof-directory certificates/local_207_near --c-checker $(LRAT_CHECKER) --python-checker src/check_lrat.py
	$(PYTHON) tests/test_local_208_reduction.py
	$(PYTHON) tests/test_local_208_near_generator.py
	$(PYTHON) tests/test_local_208_double_generator.py
	$(PYTHON) tests/test_local_208_double_classified_generator.py
	$(PYTHON) tests/test_local_208_double_classified_hard_generator.py
	TMPDIR=$(FAST_TMP) $(PYTHON) tests/verify_local_208_certificates.py --near-cnf-directory artifacts/local_208_near --proof-directory certificates/local_208 --c-checker $(LRAT_CHECKER) --python-checker src/check_lrat.py
	TMPDIR=$(FAST_TMP) $(PYTHON) tests/verify_local_208_classified_certificates.py --classified-cnf-directory artifacts/local_208_double_classified --hard-cnf-directory artifacts/local_208_double_classified_hard --proof-directory certificates/local_208_classified --c-checker $(LRAT_CHECKER) --python-checker src/check_lrat.py
	$(PYTHON) tests/test_local_209_reduction.py
	$(PYTHON) tests/test_local_209_deletion_bridges.py
	$(PYTHON) tests/test_local_209_near_generator.py
	$(PYTHON) tests/test_local_209_double_generator.py
	$(PYTHON) tests/test_local_209_mixed_double_generator.py
	$(PYTHON) tests/test_local_209_double_classified_generator.py
	$(PYTHON) tests/test_local_209_double_classified_hard_generator.py
	$(PYTHON) tests/test_local_209_double_classified_u50_canonical_generator.py
	$(PYTHON) tests/test_local_209_double_classified_u50_full_canonical_generator.py
	$(PYTHON) tests/test_local_209_double_classified_mixed_canonical_generator.py
	$(PYTHON) tests/test_local_209_balanced_counter_split_generator.py
	$(PYTHON) tests/test_local_209_balanced_counter_refinement_generator.py
	$(PYTHON) tests/test_local_209_u50_a1_counter_refinement_generator.py
	$(PYTHON) tests/test_local_209_u50_counter_cascade_generator.py
	$(PYTHON) tests/test_local_209_u50_counter_cascade2_generator.py
	$(PYTHON) tests/test_local_209_u50_counter_cascade3_generator.py
	$(PYTHON) tests/test_local_209_u50_exact27_secondary_generator.py
	$(PYTHON) tests/test_local_209_u50_exact27_secondary_low_generator.py
	$(PYTHON) tests/test_local_209_u50_exact24_tertiary_generator.py
	$(PYTHON) tests/test_local_209_u50_tertiary_positive_refinement_generator.py
	$(PYTHON) tests/test_local_209_u50_refine5294_negative_refinement_generator.py
	$(PYTHON) tests/test_local_209_u50_refine5704_positive_refinement_generator.py
	$(PYTHON) tests/test_local_209_u50_refine5242_positive_refinement_generator.py
	$(PYTHON) tests/test_local_209_unbalanced_refine7279_positive_refinement_generator.py
	$(PYTHON) tests/test_local_209_hard_refine6080_negative_refinement_generator.py
	$(PYTHON) tests/test_local_209_hard_availability_generator.py
	$(PYTHON) tests/test_local_209_remaining_availability_generator.py
	$(PYTHON) tests/test_local_209_split_composer_inputs.py
	$(PYTHON) tests/test_dimacs_model_checker.py
	$(PYTHON) tests/test_lrat_split_lifter.py
	$(PYTHON) tests/test_lrat_full.py
	TMPDIR=$(FAST_TMP) $(PYTHON) tests/verify_local_209_hard_availability_certificate.py --c-checker $(LRAT_CHECKER) --python-checker src/check_lrat.py
	TMPDIR=$(FAST_TMP) $(PYTHON) tests/verify_local_209_remaining_availability_certificates.py --c-checker $(LRAT_CHECKER) --python-checker src/check_lrat.py
	TMPDIR=$(FAST_TMP) $(PYTHON) tests/verify_local_209_certificates.py --near-cnf-directory artifacts/local_209_near --proof-directory certificates/local_209 --c-checker $(LRAT_CHECKER) --python-checker src/check_lrat.py --only balanced49_minimal_canonical
	TMPDIR=$(FAST_TMP) $(PYTHON) tests/verify_local_209_classified_certificates.py --classified-cnf-directory artifacts/local_209_double_classified --hard-cnf-directory artifacts/local_209_double_classified_hard --mixed-cnf-directory artifacts/local_209_double_classified_mixed_canonical --u50-cnf-directory artifacts/local_209_double_classified_u50_full_canonical --proof-directory certificates/local_209_classified --c-checker $(LRAT_CHECKER) --python-checker src/check_lrat.py $(foreach id,$(LOCAL_209_CLASSIFIED_PARTIAL),--only $(id))
	$(PYTHON) tests/test_full_k26_cnf.py --generator src/generate_full_k26_cnf.py
	$(PYTHON) tests/test_local_210_reduction.py
	$(PYTHON) tests/test_local_210_exact_generator.py
	$(PYTHON) tests/test_local_210_coloring_generator.py
	$(PYTHON) tests/test_full_k26_minority_cnf.py
	$(PYTHON) tests/test_full_k26_min_degree_branch_cnf.py
	$(PYTHON) tests/test_full_k26_minority59_cnf.py
	$(PYTHON) tests/test_full_k26_minority59_certificates.py
	$(PYTHON) tests/test_full_k26_minority60_cnf.py
	$(PYTHON) tests/test_full_k26_minority60_critical_cnf.py
	$(PYTHON) tests/test_full_k26_minority60_fixed_witness_cnf.py
	$(PYTHON) tests/test_full_k26_minority60_canonical_witness_cnf.py
	$(PYTHON) tests/test_minority60_critical_graph_cnf.py
	$(PYTHON) tests/test_minority60_degree4_structure_cnf.py
	$(PYTHON) tests/test_minority60_spoke_critical_cnf.py
	$(PYTHON) tests/test_full_k26_fixed_minority_graph_cnf.py
	$(PYTHON) tests/test_minority60_recursive_reduction.py
	$(PYTHON) tests/test_residual11_classification_cnf.py
	$(PYTHON) tests/test_minority60_recursive_certificates.py
	$(PYTHON) tests/test_minority61_recursive_reduction.py
	$(PYTHON) tests/test_minority61_triangle_residual_cnf.py
	$(PYTHON) tests/test_minority61_candidate_extension_cnf.py
	$(PYTHON) tests/test_minority61_certificates.py
	$(PYTHON) tests/test_minority62_reduction.py
	$(PYTHON) tests/test_minority62_triangle_residual_cnf.py
	$(PYTHON) tests/test_minority62_candidate_extension_cnf.py
	$(PYTHON) tests/test_minority62_certificates.py
	$(PYTHON) tests/test_minority63_reduction.py
	$(PYTHON) tests/test_minority63_component_family_cnf.py
	$(PYTHON) tests/test_minority63_critical_component_family_cnf.py
	$(PYTHON) tests/test_minority63_refined_family_cnf.py
	$(PYTHON) tests/test_minority63_min_degree_family_cnf.py
	$(PYTHON) tests/test_minority63_k4_k5_k5_family_cnf.py
	$(PYTHON) tests/test_minority63_all_color_lower_cnf.py
	$(PYTHON) tests/test_minority63_residual12_cnf.py
	$(PYTHON) tests/test_minority63_residual11_cnf.py
	$(PYTHON) tests/test_minority63_candidate_extension_cnf.py
	$(PYTHON) tests/test_minority63_q16_critical_family_cnf.py
	$(PYTHON) tests/test_minority63_q16_graph_cnf.py
	$(PYTHON) tests/test_minority63_q16_ore_extension_cnf.py
	$(PYTHON) tests/test_minority63_certificates.py
	$(PYTHON) tests/test_external_r5_proof_audit.py
	$(PYTHON) tests/test_r5_five_regular_brooks_cnf.py
	$(PYTHON) tests/test_r5_brooks_neighborhood_branch_cnf.py
	$(PYTHON) tests/test_r5_brooks_exterior_sorted_cnf.py
	$(PYTHON) tests/test_r5_brooks_first_pattern_cnf.py
	$(PYTHON) tests/test_r5_brooks_k4_local_cnf.py
	$(PYTHON) tests/test_r5_brooks_branch19_cross_pattern_cnf.py
	$(PYTHON) tests/test_r5_brooks_zero_pattern_neighborhood_cnf.py
	$(PYTHON) tests/test_r5_brooks_closed_neighborhood_admissibility_cnf.py
	$(PYTHON) tests/test_r5_brooks_zero_anchor_quotient_cnf.py
	$(PYTHON) tests/test_r5_brooks_exterior_sorted_certificates.py
	$(PYTHON) tests/test_r5_brooks_residual_certificates.py
	$(PYTHON) tests/test_r5_kp_large_specialization_cnf.py
	$(PYTHON) tests/test_r5_kp_average_degree_anchor_cnf.py
	$(PYTHON) tests/verify_r5_kp_average_degree_anchor_certificates.py
	sha256sum --check artifacts/SHA256SUMS

verify-r5-special-brooks: $(LRAT_CHECKER)
	$(PYTHON) tests/test_r5_five_regular_brooks_cnf.py
	$(PYTHON) tests/test_r5_brooks_neighborhood_branch_cnf.py
	$(PYTHON) tests/test_r5_brooks_exterior_sorted_cnf.py
	$(PYTHON) tests/test_r5_brooks_k4_local_cnf.py
	$(PYTHON) tests/test_r5_brooks_branch19_cross_pattern_cnf.py
	$(PYTHON) tests/test_r5_brooks_zero_pattern_neighborhood_cnf.py
	$(PYTHON) tests/test_r5_brooks_closed_neighborhood_admissibility_cnf.py
	$(PYTHON) tests/test_r5_brooks_zero_anchor_quotient_cnf.py
	$(PYTHON) tests/test_r5_brooks_exterior_sorted_certificates.py
	$(PYTHON) tests/test_r5_brooks_residual_certificates.py

verify-e058-unit: $(LRAT_CHECKER)
	$(PYTHON) -m unittest \
		tests.test_minimize_rup_lrat \
		tests.test_rup_lrat_stages \
		tests.test_e058_audit_runner \
		tests.test_e058_lean_semantic_closures \
		tests.test_e058_neighborhood_orbit_certificate

verify-r5-kp-large: $(LRAT_CHECKER)
	$(PYTHON) tests/test_r5_kp_large_specialization_cnf.py
	$(PYTHON) tests/test_r5_kp_average_degree_anchor_cnf.py
	$(PYTHON) tests/verify_r5_kp_average_degree_anchor_certificates.py

# Optional full certificate reproduction. Requires python-sat==1.9.dev7 in the
# selected Python environment; verification itself does not trust or require it.
reproduce-certificate: $(DRAT_TRIM)
	$(PYTHON) repro/generate_local_equality_drup.py $(BUILD_DIR)/local_equality.drup
	$(DRAT_TRIM) $(LOCAL_EQUALITY_CNF) $(BUILD_DIR)/local_equality.drup -U -L $(BUILD_DIR)/local_equality.lrat
	cmp $(BUILD_DIR)/local_equality.lrat $(LOCAL_EQUALITY_LRAT)
	sha256sum $(BUILD_DIR)/local_equality.drup $(BUILD_DIR)/local_equality.lrat

# Optional E006 reproduction. CADICAL must name an official CaDiCaL 1.9.5
# binary; the script refuses every other reported version.
CADICAL ?= cadical
reproduce-local-204: $(DRAT_TRIM)
	$(PYTHON) repro/generate_local_204_certificates.py --cadical $(CADICAL) --drat-trim $(DRAT_TRIM)

reproduce-local-205: $(DRAT_TRIM)
	$(PYTHON) repro/generate_local_204_certificates.py --family 205 --cadical $(CADICAL) --drat-trim $(DRAT_TRIM)

reproduce-local-206: $(DRAT_TRIM)
	$(PYTHON) repro/generate_local_204_certificates.py --family 206 --cadical $(CADICAL) --drat-trim $(DRAT_TRIM)

reproduce-local-207: $(DRAT_TRIM)
	$(PYTHON) repro/generate_local_204_certificates.py --family 207 --cadical $(CADICAL) --drat-trim $(DRAT_TRIM)

# Optional E009 reproduction. KISSAT must name the pinned official 4.0.4
# binary. The deterministic search takes about nine minutes on the recorded
# machine; normal verification does not run or trust Kissat.
KISSAT ?= kissat
reproduce-local-205-near: $(DRAT_TRIM)
	$(PYTHON) repro/generate_local_205_near_certificate.py --kissat $(KISSAT) --drat-trim $(DRAT_TRIM)

reproduce-local-206-near: $(DRAT_TRIM)
	$(PYTHON) repro/generate_local_206_near_certificates.py --kissat $(KISSAT) --drat-trim $(DRAT_TRIM)

reproduce-local-207-near: $(DRAT_TRIM)
	$(PYTHON) repro/generate_local_207_near_certificates.py --kissat $(KISSAT) --drat-trim $(DRAT_TRIM)

reproduce-local-208: $(DRAT_TRIM)
	$(PYTHON) repro/generate_local_208_certificates.py --kissat $(KISSAT) --drat-trim $(DRAT_TRIM)

reproduce-local-208-classified: $(DRAT_TRIM) $(LRAT_CHECKER)
	$(PYTHON) repro/generate_local_208_classified_certificates.py --kissat $(KISSAT) --drat-trim $(DRAT_TRIM) --c-checker $(LRAT_CHECKER) --python-checker src/check_lrat.py

clean:
	rm -f $(C_CHECKER) $(LRAT_CHECKER) $(DRAT_TRIM) $(BUILD_DIR)/affine_nonextension.json $(BUILD_DIR)/triangle_bound.json $(BUILD_DIR)/local_equality.cnf $(BUILD_DIR)/local_equality.drup $(BUILD_DIR)/local_equality.lrat
