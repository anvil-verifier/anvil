# Proof speedup log

Ledger for the `speed-up-proofs` workflow. One row per attempted target. Compare
by `rlimit` (deterministic); isolated smt time is noted for reference.

| target | technique | rlimit before → after | result |
|--|--|--|--|
| rabbitmq_controller::proof::liveness::resource_match::lemma_inductive_current_state_matches_preserves_from_s_to_s_prime | 1 (split by step: extract `_during_api_server_step`) | 48,059,413 → 25,277,994 (parent 4,035,733 + api_server 21,242,261) | **-47.4%**, verifies 0 errors |
| rabbitmq_controller::proof::liveness::resource_match::lemma_inductive_current_state_matches_preserves_from_s_to_s_prime_during_controller_step | 1 (split by branch: extract `_this_cr`) | 69,088,379 → 28,879,529 (parent 5,985,553 + this_cr 22,893,976) | **-58.2%**, verifies 0 errors |
