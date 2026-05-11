// Verification entry point for the Anvil framework library.
// Building / verifying this binary pulls in the entire `verifiable_controllers`
// crate; verify with:
//     cargo verus verify anvil -- --rlimit 50 --time

use verifiable_controllers as _;

fn main() {}
