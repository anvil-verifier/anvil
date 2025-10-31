/home/ndate/Research/verus/source/target-verus/release/verus \
    -L dependency=src/deps_hack/target/debug/deps \
    --extern=deps_hack="src/deps_hack/target/debug/libdeps_hack.rlib" \
    src/vstatefulset_controller.rs \
    -Z macro-backtrace \
    --trace \
    --multiple-errors 100 \
    --verify-only-module vstatefulset_controller::trusted::reconciler \
    --verify-function get_ordinal