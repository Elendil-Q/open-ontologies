//! Shared helper for tests that need a fixture the repository does not carry.
//!
//! Several tests used to `return` when their fixture was missing, three of them
//! without printing anything. A test that returns early reports `ok`, so in CI,
//! where neither `data/crosswalks.parquet` nor the embedding model exists, they
//! counted towards a green run while executing nothing. Reporting success for
//! work that did not happen is the one failure this project is built to catch,
//! and it was in its own suite.
//!
//! `skip_unless` makes the skip loud and, when `OO_REQUIRE_FIXTURES=1` is set,
//! fatal. Set that variable in any job that is supposed to provide fixtures and
//! the suite can no longer quietly shrink.

/// Returns true when the caller should skip. Panics instead if the environment
/// says fixtures are mandatory.
#[allow(dead_code)]
pub fn skip_unless(available: bool, what: &str, how_to_get_it: &str) -> bool {
    if available {
        return false;
    }
    let msg = format!("missing fixture: {what}. {how_to_get_it}");
    if std::env::var("OO_REQUIRE_FIXTURES").as_deref() == Ok("1") {
        panic!("{msg} (OO_REQUIRE_FIXTURES=1, so this is a failure, not a skip)");
    }
    // Distinctive marker so a CI step can count skips rather than let them
    // hide inside a green run.
    eprintln!("SKIPPED_FIXTURE: {msg}");
    true
}
