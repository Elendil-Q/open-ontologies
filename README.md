<!-- mcp-name: io.github.fabio-rovai/open-ontologies -->

<p align="center">
  <img src="docs/assets/logo.png" alt="Open Ontologies" width="300">
</p>

<h1 align="center">Open Ontologies</h1>

<p align="center">
  <strong>An ontology engine whose answers carry their evidence</strong><br>
  Reason, validate and align over RDF and OWL, then have a small verified checker in Lean 4
  confirm the result. Written in Rust. Ships as a single binary.
</p>

<p align="center">
  <a href="https://tesseractsemantics.com"><strong>tesseractsemantics.com</strong></a>
</p>

<p align="center">
  <a href="https://tesseractsemantics.com"><img src="https://img.shields.io/badge/Tesseract%20Semantics-tesseractsemantics.com-111827?style=for-the-badge" alt="Tesseract Semantics"></a>
  <a href="https://github.com/fabio-rovai/open-ontologies/stargazers"><img src="https://img.shields.io/github/stars/fabio-rovai/open-ontologies?style=for-the-badge&logo=github" alt="Stars"></a>
  <a href="https://github.com/fabio-rovai/open-ontologies/actions/workflows/ci.yml"><img src="https://img.shields.io/github/actions/workflow/status/fabio-rovai/open-ontologies/ci.yml?branch=main&style=for-the-badge" alt="CI"></a>
  <a href="LICENSE"><img src="https://img.shields.io/badge/License-MIT-blue.svg?style=for-the-badge" alt="MIT"></a>
  <a href="https://github.com/fabio-rovai/open-ontologies/pkgs/container/open-ontologies"><img src="https://img.shields.io/badge/GHCR-pull%20the%20image-2496ED?style=for-the-badge&logo=docker&logoColor=white" alt="Container image on GHCR"></a>
  <a href="https://github.com/sponsors/fabio-rovai"><img src="https://img.shields.io/github/sponsors/fabio-rovai?style=for-the-badge&label=Sponsor&logo=GitHub%20Sponsors&logoColor=EA4AAA&color=EA4AAA" alt="Sponsor"></a>
</p>

<p align="center">
  <strong>English</strong> · <a href="README.zh-CN.md">简体中文</a>
</p>

---

Ask a reasoner why it reached a conclusion and it will usually tell you to trust it.

This one hands you the working. An inference comes back with a derivation certificate. A
satisfiable ontology comes back with a model. An inconsistent one comes back with a refutation.
Each is replayed by a small checker written in Lean 4, in core Lean with no Mathlib, whose
theorems say the conclusion holds in **every** model of what you asserted.

You do not have to trust this engine. You can check what it did.

```bash
open-ontologies reason --profile owl-rl --certificate ./cert
cd lean && lake exe oo-cert ../cert/asserted.tsv ../cert/derivations.tsv
# {"ok":true,"verdict":"entailed","theorem":"OOCert.certificate_sound"}
```

## What is actually proved

| You ask | You get back | Checked against |
| --- | --- | --- |
| Reason over OWL | A derivation certificate | `OOCert.certificate_sound` |
| Reason with rules you wrote | A certificate, and a different verdict word | `OOCert.horn_certificate_sound` |
| Is this satisfiable | A finite model | `Dl.satisfiable_of_checkModel` |
| Is a solver's model real | The model, replayed | `Fol.satisfiable_of_check` |
| Is this inconsistent | A refutation | `OOCert.refutation_sound` |
| Does this data fit the shapes | A validation report | `Shacl.validate_spec` |
| Does a retrieval slice still support the answer | Per-claim preservation | `OOCert.certificate_sound` |

That last row is the one to read twice. A retrieval slice at 99% coverage can have dropped the
one triple an answer depends on, and one at 60% can preserve every claim that matters. Coverage
is a proxy that rises as the slice grows, so a retriever tuned on it learns to fetch more rather
than the right thing. Entailment preservation is the property, it is decidable here, and it
carries a certificate per claim. See [decision 0007](docs/decisions/0007-a-slice-preserves-a-conclusion-or-it-does-not.md).

The discipline matters more than the machinery, and it runs through all of it.

A rule **you** supplied is an assumption the certificate carries, never a fact it establishes, so
it earns `entailed_under_supplied_rules` and never `entailed`. A model a solver hands back can be
checked and becomes a certificate; a refutation cannot be replayed in core Lean and stays an
oracle opinion. The two never share a word. Where something is measured rather than proved, the
documentation says measured, and [what the proofs assume about the Rust](docs/trusted-computing-base.md)
is written down rather than left implied.

The reasoning behind each of those rules is in [docs/decisions/](docs/decisions/), one file per
rule, each naming the failure it exists to prevent.

## Install

```bash
# macOS (Apple Silicon)
curl -LO https://github.com/fabio-rovai/open-ontologies/releases/latest/download/open-ontologies-aarch64-apple-darwin
chmod +x open-ontologies-aarch64-apple-darwin && mv open-ontologies-aarch64-apple-darwin /usr/local/bin/open-ontologies

# Linux (x86_64)
curl -LO https://github.com/fabio-rovai/open-ontologies/releases/latest/download/open-ontologies-x86_64-unknown-linux-gnu
chmod +x open-ontologies-x86_64-unknown-linux-gnu && mv open-ontologies-x86_64-unknown-linux-gnu /usr/local/bin/open-ontologies

# Docker
docker pull ghcr.io/fabio-rovai/open-ontologies:latest

# From source (Rust 1.85+)
cargo build --release --features embeddings,plugins,sql
```

Intel macOS, native Windows and the rest: [docs/quickstart.md](docs/quickstart.md) and
[docs/windows.md](docs/windows.md).

`serve` starts an MCP server speaking JSON-RPC over stdin and stdout, so on launch it appears to
hang while it waits for a client. That is expected. From a terminal, use the CLI subcommands
instead, such as `open-ontologies validate <file.ttl>`.

## Connect it to Claude

Add to `~/.claude/settings.json` for Claude Code, or to
`~/Library/Application Support/Claude/claude_desktop_config.json` for Claude Desktop:

```json
{
  "mcpServers": {
    "open-ontologies": {
      "command": "/path/to/open-ontologies",
      "args": ["serve"]
    }
  }
}
```

Restart, and the `onto_*` tools are available. Cursor, Windsurf, Zed and VS Code are in
[docs/quickstart.md](docs/quickstart.md).

## What is in the box

**114 tools** to build, validate, query, diff, lint, version, reason over, align, plan, certify
and govern RDF and OWL, over an in-memory Oxigraph store. A default build advertises all 114 tools.
Eight need an optional Cargo feature and return an error without it: four need `embeddings`, two
need `plugins`, two need `postgres` or `duckdb`. The published binaries and the GHCR image are
built with the default feature set, so they do not carry those eight.

The Python package `open-ontologies-lite` now reasons as well, in pure Python with no Rust
toolchain, and its certificates are checked by the same Lean binaries. It is a second engine, and
being untrusted costs nothing: the warrant was never in the engine.

Alongside them, a marketplace of 33 standard ontologies, clinical crosswalks, semantic embeddings,
a lineage audit trail, and a desktop Studio with a virtualized ontology tree, an AI chat panel and
a Protégé-style inspector. No JVM. No Protégé.

## Documentation

| Topic | Link |
| --- | --- |
| Quickstart | [docs/quickstart.md](docs/quickstart.md) |
| Architecture | [docs/architecture.md](docs/architecture.md) |
| Derivation certificates and the Lean checkers | [docs/lean-certificates.md](docs/lean-certificates.md) |
| What the Lean proofs assume about the Rust | [docs/trusted-computing-base.md](docs/trusted-computing-base.md) |
| First-order export, TPTP and Common Logic | [docs/first-order-export.md](docs/first-order-export.md) |
| Every reasoning system, and why each was used or refused | [docs/reasoning-systems-inventory.md](docs/reasoning-systems-inventory.md) |
| Design decisions, one rule per file | [docs/decisions/](docs/decisions/) |
| SHIQ reasoning | [docs/reasoning.md](docs/reasoning.md) |
| Schema alignment | [docs/alignment.md](docs/alignment.md) |
| Data pipeline | [docs/data-pipeline.md](docs/data-pipeline.md) |
| Ontology lifecycle | [docs/lifecycle.md](docs/lifecycle.md) |
| Semantic embeddings | [docs/embeddings.md](docs/embeddings.md) |
| Clinical crosswalks | [docs/clinical.md](docs/clinical.md) |
| IES support | [ecosystem](docs/ies-ecosystem.md) · [alignment](docs/ies-alignment.md) · [SPARQL examples](docs/ies-examples.md) |
| Benchmarks | [docs/benchmarks.md](docs/benchmarks.md) |
| Determinism and corrected results | [docs/determinism.md](docs/determinism.md) |
| Windows | [docs/windows.md](docs/windows.md) |
| Contributing | [CONTRIBUTING.md](CONTRIBUTING.md) |

## Stack

Rust edition 2024, single binary, no JVM. Oxigraph 0.5 for RDF and SPARQL 1.1. `rmcp` for MCP over
streamable HTTP. SQLite for state, lineage and feedback. Lean 4 v4.33.1 for the checkers, core Lean
only, no Mathlib. Tauri 2, React 19 and Tailwind 4 for the Studio. Full table in
[docs/architecture.md](docs/architecture.md).

## Citation

- **Open Ontologies: Tool-Augmented Ontology Engineering with Stable Matching Alignment.** Fabio
  Rovai, 2026. [arXiv:2605.09184](https://arxiv.org/abs/2605.09184)
- **CIVeX: Causal Intervention Verification for Language Agents.** Fabio Rovai, 2026.
  [arXiv:2605.09168](https://arxiv.org/abs/2605.09168)

[`CITATION.cff`](CITATION.cff) carries machine-readable metadata and powers GitHub's "Cite this
repository" button.

## License

MIT. Maintained by [Fabio Rovai](https://github.com/fabio-rovai) at
[Tesseract Semantics](https://tesseractsemantics.com). If this is useful to you, you can support it
through [GitHub Sponsors](https://github.com/sponsors/fabio-rovai).
