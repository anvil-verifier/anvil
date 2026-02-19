/home/ndate/Research/verus/source/target-verus/release/verus \
    -L dependency=src/deps_hack/target/debug/deps \
    --extern=deps_hack="src/deps_hack/target/debug/libdeps_hack.rlib" \
    --compile \
    src/esr_composition.rs \
    -Z macro-backtrace \
    --rlimit 50 \
    --time \
    --verify-module composition