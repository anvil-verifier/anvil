mod handlers;
mod validator;

use warp::Filter;

#[tokio::main]
async fn main() {
    tracing_subscriber::fmt::init();

    let routes = warp::path("validate")
        .and(warp::body::json())
        .and_then(handlers::validate_handler)
        .with(warp::trace::request());

    warp::serve(warp::post().and(routes))
        .tls()
        .cert_path("/certs/tls.crt")
        .key_path("/certs/tls.key")
        .run(([0, 0, 0, 0], 8443))
        .await;
}
