#![allow(unused_imports)]
#![allow(unused_variables)]
pub mod common;
pub mod rabbitmq_e2e;
pub mod zookeeper_e2e;
use common::Error;
use rabbitmq_e2e::rabbitmq_e2e_test;
use std::str::FromStr;
use std::{env, sync::Arc};
use zookeeper_e2e::zookeeper_e2e_test;

#[tokio::main]
async fn main() -> Result<(), Error> {
    let args: Vec<String> = env::args().collect();
    let cmd = args[1].clone();
    match cmd.as_str() {
        "zookeeper" => {
            println!("Running zookeeper end to end test!\n");
            return zookeeper_e2e_test().await;
        }
        "rabbitmq" => {
            println!("Running rabbitmq end to end test!\n");
            return rabbitmq_e2e_test().await;
        }
        _ => {
            println!("Please specify one controller!\n");
            Ok(())
        }
    }
}
