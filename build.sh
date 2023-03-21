rv=$VERUS_DIR/source/tools/rust-verify.sh
cd src/deps_hack; bash build.sh
cd ..
k8s_openapi_rlib=$(find deps_hack/target/debug/deps/ -name 'libk8s_openapi-*.rlib')
$rv -L dependency=deps_hack/target/debug/deps --extern=k8s_openapi=$k8s_openapi_rlib --cfg erasure_macro_todo --erasure macro --compile main.rs
