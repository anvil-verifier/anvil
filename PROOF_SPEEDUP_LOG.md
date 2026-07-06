# Proof speedup log

Ledger for the `speed-up-proofs` workflow. One row per attempted target. Times
are isolated single-function SMT run time (`total smt-run`, one thread — no
parallel contention), which is the real verification wall-cost. rlimit noted in
parentheses as the deterministic cross-check.

| target | technique | SMT before → after | Δ |
|--|--|--|--|
| rabbitmq_controller::…::resource_match::lemma_inductive_current_state_matches_preserves_from_s_to_s_prime | 1 (extract `_during_api_server_step`) | 66.06s → 20.32s (parent 2.40 + api_server 17.92) | **−69%** (rlimit 48.06M→25.28M) |
| rabbitmq_controller::…::resource_match::lemma_inductive_current_state_matches_preserves_from_s_to_s_prime_during_controller_step | 1 (extract `_this_cr`) | 71.72s → 19.04s (parent 3.01 + this_cr 16.03) | **−73%** (rlimit 69.09M→28.88M) |
| rabbitmq_controller::…::resource_match::lemma_from_after_update_resource_step_to_after_get_next_resource_step | 0 (extract `_inductive_step`) | 52.61s → 35.34s (parent 2.08 + inductive 33.27) | **−33%** (rlimit 37.02M→28.50M) |
| vdeployment_controller::…::resource_match::lemma_from_receive_ok_resp_after_scale_new_vrs_to_after_ensure_new_vrs | 2 (`hide`), then 0 (extraction) | 28.25s baseline — both reverted | **no win**: `hide` broke the inductive goal; extraction regressed to 33.08s |
| vstatefulset_controller::…::helper_invariants::lemma_eventually_always_all_pod_requests_from_vsts_controller_carry_only_vsts_owner_ref | 0 (extract `_inductive_step`) | 103.76s → 28.98s (parent 0.02 + inductive 28.96) | **−72%** (rlimit 174.0M→25.9M) |
| vstatefulset_controller::…::internal_rely_guarantee::lemma_local_pods_and_pvcs_are_bound_to_vsts_with_key_preserves_from_s_to_s_prime | 1 (extract `_during_controller_step`) | 111.93s → 28.62s (parent 1.01 + during_controller_step 27.61) | **−74%** (rlimit 146.5M→98.06M) |

| rabbitmq_controller::…::helper_invariants::proof::lemma_always_there_is_no_request_msg_to_external_from_controller | 0 (extract `_inductive_step`) | 66.36s → 13.66s (parent 0.01 + inductive 13.65) | **−79%** (rlimit 97.94M→18.79M) |
| vstatefulset_controller::…::liveness::proof::spec_entails_pending_request_invariants_part2 | 1 (split `_done` / `_error`) | 186.49s → 40.94s (wrapper 0.02 + done 11.55 + error 29.37) | **−88%** (rlimit 465.69M→57.43M) |
| vstatefulset_controller::…::liveness::resource_match::lemma_spec_entails_get_pvc_leads_to_skip_or_create_pvc | 1 (split leads_to chain into 3 stage sub-lemmas) | rlimit 169.98M → 71.15M (wrapper 0.06M + req 10.97M + resp 7.12M + skip/create 53.00M) | **−58%** rlimit |
| vstatefulset_controller::…::liveness::proof::spec_entails_pending_request_invariants_part3 | 1 (split GetPVC / CreatePVC / SkipPVC) | rlimit 55.31M → 29.22M sum; **wall-clock ~55-100s → ~14.5s critical path** (3 parallel spinoff queries: get 14.46s + create 5.32s + skip 9.79s) | **−47%** rlimit, ~−85% wall |
| vstatefulset_controller::…::liveness::proof::spec_entails_pending_request_invariants_part4 | 1 (split CreateNeeded / UpdateNeeded) | rlimit 46.03M → 26.76M sum; wall-clock critical path ~17.2s (create 17.19s + update 12.00s parallel) | **−42%** rlimit |

Note: `cargo clean -p` does NOT bust the verus SMT cache; `touch` busts only the Rust compile cache. Reliable per-function numbers come from a full-module `--output-json` run (function-breakdown gives deterministic rlimit).
| vdeployment_controller::…::liveness::resource_match::lemma_from_after_scale_down_old_vrs_with_old_vrs_of_n_to_pending_scale_down_req_in_flight | 0 (extract `_inductive_step`) | rlimit 96.07M → 42.01M (parent 1.41M + inductive 40.60M) | **−56%** rlimit |
| vstatefulset_controller::…::liveness::resource_match::lemma_spec_entails_deleted_condemned_of_i_leads_to_delete_condemned_of_i_plus_one_or_delete_outdated | 1 (split leads_to stages: request / response) | rlimit 68.10M → 42.15M (parent 0.08M + stage1 27.55M + stage2 14.52M) | **−38%** rlimit |
