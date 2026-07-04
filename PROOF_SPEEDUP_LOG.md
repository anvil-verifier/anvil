# Proof speedup log

Ledger for the `speed-up-proofs` workflow. One row per attempted target. Compare
by `rlimit` (deterministic); isolated smt time is noted for reference.

| target | technique | rlimit before → after | result |
|--|--|--|--|
| rabbitmq_controller::proof::liveness::resource_match::lemma_inductive_current_state_matches_preserves_from_s_to_s_prime | 1 (split by step: extract `_during_api_server_step`) | 48,059,413 → 25,277,994 (parent 4,035,733 + api_server 21,242,261) | **-47.4%**, verifies 0 errors |
| rabbitmq_controller::proof::liveness::resource_match::lemma_inductive_current_state_matches_preserves_from_s_to_s_prime_during_controller_step | 1 (split by branch: extract `_this_cr`) | 69,088,379 → 28,879,529 (parent 5,985,553 + this_cr 22,893,976) | **-58.2%**, verifies 0 errors |
| rabbitmq_controller::proof::liveness::resource_match::lemma_from_after_update_resource_step_to_after_get_next_resource_step | 0 (extract `(s,s_prime)` `_inductive_step` subproof) | 37,023,054 → 28,496,191 (parent 4,191,931 + inductive_step 24,304,260) | **-23.0%**, verifies 0 errors |
| vdeployment_controller::proof::liveness::resource_match::lemma_from_receive_ok_resp_after_scale_new_vrs_to_after_ensure_new_vrs | 2 (`hide`), then 0 (`(s,s_prime)` extraction) | 31,409,826 (isolated) — both reverted | **no win**: `hide` broke the inductive goal; extraction regressed to 39.86M (+27%) |
| vstatefulset_controller::proof::helper_invariants::lemma_eventually_always_all_pod_requests_from_vsts_controller_carry_only_vsts_owner_ref | 0 (extract `_inductive_step`) | 173,996,780 → 25,927,930 (parent 85,665 + inductive_step 25,842,265) | **-85.1%**, verifies 0 errors |
