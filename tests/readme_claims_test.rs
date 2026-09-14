//! The README's tool count must be the tool count, in every place it is stated.
//!
//! It drifted. The file said 110 while the server exposed 111, and it said it in four
//! separate places, which is exactly why nobody noticed: a number repeated by hand has
//! four chances to go stale and no mechanism to notice that it has.
//!
//! The house rule is that a figure next to the thing it measures must be DERIVED, never
//! typed. A README cannot compute, so the next best thing is a test that refuses to let
//! the two disagree. This is that test.
//!
//! It deliberately checks each stated claim BY ITS SURROUNDING PHRASE rather than
//! scanning for every "N tools" in the file, because the README also contains subgroup
//! counts that are correctly smaller than the total. A test that flagged those would be
//! noise, and a noisy gate gets disabled.

use std::path::PathBuf;

fn repo() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}

/// The measurement. One `#[tool(name = ...)]` attribute per exposed MCP tool.
fn exposed_tool_count() -> usize {
    let server = std::fs::read_to_string(repo().join("src").join("server.rs"))
        .expect("src/server.rs must be readable");
    server.matches("#[tool(name = ").count()
}

/// Every place the README states the TOTAL, with the phrase that identifies it as a
/// total rather than a subgroup. Add a row here when a new one is written, and the
/// test will hold it to the same number as the rest.
fn total_claims(n: usize) -> Vec<(&'static str, String)> {
    vec![
        ("the lead paragraph", format!("**{n} tools**")),
        ("the default-build sentence", format!("A default build advertises all {n} tools.")),
        ("the tool-reference heading", format!("{n} tools organized by function")),
        ("the architecture diagram", format!("ToolGroups[\"{n} Tools\"]")),
    ]
}

#[test]
fn the_readme_states_the_tool_count_it_actually_exposes() {
    let n = exposed_tool_count();
    assert!(n > 0, "no #[tool(name = ...)] attributes found; the measurement itself is broken");

    let readme = std::fs::read_to_string(repo().join("README.md")).expect("README.md must exist");

    let mut wrong = Vec::new();
    for (where_, claim) in total_claims(n) {
        if !readme.contains(&claim) {
            wrong.push(format!("{where_}: expected to find {claim:?}"));
        }
    }

    assert!(
        wrong.is_empty(),
        "src/server.rs exposes {n} tools and the README does not say so everywhere it \
         claims a total.\n{}\n\nFix the README rather than this test: the server is the \
         measurement and the prose is the claim. If a claim was deliberately removed or \
         reworded, update `total_claims` in this file and say why in the commit.",
        wrong.join("\n")
    );
}

/// The other half, and the one that catches a HALF-DONE correction: if someone updates
/// three of the four places, a stale number is still in the file and the test above
/// would pass on the three it found. This fails on the leftover.
#[test]
fn no_stale_tool_count_survives_anywhere() {
    let n = exposed_tool_count();
    let readme = std::fs::read_to_string(repo().join("README.md")).expect("README.md must exist");

    // The shapes a total is written in here. Any number in one of them that is not the
    // measured count is a leftover from a partial edit.
    let shapes: [(&str, &str); 4] =
        [("**", " tools**"), ("advertises all ", " tools."), ("", " tools organized by function"), ("ToolGroups[\"", " Tools\"]")];

    let mut stale = Vec::new();
    for (prefix, suffix) in shapes {
        let mut rest = readme.as_str();
        while let Some(i) = rest.find(suffix) {
            let head = &rest[..i];
            let digits: String =
                head.chars().rev().take_while(|c| c.is_ascii_digit()).collect::<Vec<_>>().into_iter().rev().collect();
            if !digits.is_empty() && (prefix.is_empty() || head.ends_with(&format!("{prefix}{digits}"))) {
                if let Ok(found) = digits.parse::<usize>() {
                    if found != n {
                        stale.push(format!("{prefix}{found}{suffix} (server exposes {n})"));
                    }
                }
            }
            rest = &rest[i + suffix.len()..];
        }
    }

    assert!(
        stale.is_empty(),
        "a tool-count claim in the README disagrees with src/server.rs:\n  {}\n\nThis is what \
         a half-finished correction looks like: some copies updated, one left behind.",
        stale.join("\n  ")
    );
}
