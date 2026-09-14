//! A node-level constraint must reach `skipped_constraints` whatever target form
//! selected the shape.
//!
//! The node-shape complement builds its set of known shapes from the
//! `sh:targetClass` discovery query alone. A shape whose only target is
//! `sh:targetNode`, `sh:targetSubjectsOf` or `sh:targetObjectsOf` was therefore
//! filtered out of that check, so an unimplemented constraint asserted directly
//! on it was dropped with no record and the verdict came back `true`. Reporting
//! success for a rule that was never run is the one failure mode this validator
//! is built not to have, so it gets a test that fails before the fix.

use open_ontologies::graph::GraphStore;
use open_ontologies::shacl::ShaclValidator;
use std::sync::Arc;

const DATA: &str = r#"
    @prefix owl: <http://www.w3.org/2002/07/owl#> .
    @prefix ex:  <http://example.org/> .

    ex:Person a owl:Class .
    ex:Address a owl:Class .

    ex:alice a ex:Person ; ex:addr ex:notAnAddress .
    ex:notAnAddress a ex:Person .
"#;

/// `sh:class` directly on the node shape is not evaluated by this validator, so
/// it must be recorded. The only target here is `sh:targetNode`.
const TARGET_NODE_SHAPES: &str = r#"
    @prefix sh: <http://www.w3.org/ns/shacl#> .
    @prefix ex: <http://example.org/> .
    ex:AliceShape a sh:NodeShape ;
        sh:targetNode ex:alice ;
        sh:class ex:Address .
"#;

const TARGET_SUBJECTS_OF_SHAPES: &str = r#"
    @prefix sh: <http://www.w3.org/ns/shacl#> .
    @prefix ex: <http://example.org/> .
    ex:AddrSubjectShape a sh:NodeShape ;
        sh:targetSubjectsOf ex:addr ;
        sh:class ex:Address .
"#;

const TARGET_OBJECTS_OF_SHAPES: &str = r#"
    @prefix sh: <http://www.w3.org/ns/shacl#> .
    @prefix ex: <http://example.org/> .
    ex:AddrObjectShape a sh:NodeShape ;
        sh:targetObjectsOf ex:addr ;
        sh:class ex:Address .
"#;

fn report(shapes: &str) -> serde_json::Value {
    let graph = Arc::new(GraphStore::new());
    graph.load_turtle(DATA, None).expect("load");
    let json = ShaclValidator::validate(&graph, shapes).expect("validate");
    serde_json::from_str(&json).expect("parse")
}

fn assert_recorded_and_suppressed(shapes: &str, label: &str) {
    let r = report(shapes);

    let skipped = r["skipped_constraints"]
        .as_array()
        .cloned()
        .unwrap_or_default();
    assert!(
        skipped
            .iter()
            .any(|s| s["constraint"].as_str().unwrap_or_default().ends_with("#class")),
        "{label}: node-level sh:class was dropped with no skipped_constraints entry: {r}"
    );

    assert!(
        r["conforms"].is_null(),
        "{label}: an unevaluated constraint must suppress the verdict, got {}: {r}",
        r["conforms"]
    );
}

#[test]
fn a_target_node_shape_records_its_unevaluated_node_constraint() {
    assert_recorded_and_suppressed(TARGET_NODE_SHAPES, "sh:targetNode");
}

#[test]
fn a_target_subjects_of_shape_records_its_unevaluated_node_constraint() {
    assert_recorded_and_suppressed(TARGET_SUBJECTS_OF_SHAPES, "sh:targetSubjectsOf");
}

#[test]
fn a_target_objects_of_shape_records_its_unevaluated_node_constraint() {
    assert_recorded_and_suppressed(TARGET_OBJECTS_OF_SHAPES, "sh:targetObjectsOf");
}

/// The control. A `sh:targetClass` shape already reached the complement before
/// the fix, so this passes either way and catches a fix that works by
/// disabling the check rather than widening it.
#[test]
fn a_target_class_shape_still_records_its_unevaluated_node_constraint() {
    const SHAPES: &str = r#"
        @prefix sh: <http://www.w3.org/ns/shacl#> .
        @prefix ex: <http://example.org/> .
        ex:PersonShape a sh:NodeShape ;
            sh:targetClass ex:Person ;
            sh:class ex:Address .
    "#;
    assert_recorded_and_suppressed(SHAPES, "sh:targetClass");
}
