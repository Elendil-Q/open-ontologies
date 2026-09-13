# The W3C SHACL test suite, vendored

This directory is a verbatim copy of `data-shapes-test-suite/tests/` from the
W3C Data Shapes Working Group repository. Two files are added by this project
and are not upstream: this `README.md` and `LICENSE.md` (a copy of the
repository-root licence, reproduced here so the terms travel with the data).

Nothing under `core/` or `sparql/` has been edited. Do not edit it: a test
suite you have patched measures your patch.

## Provenance

| | |
|---|---|
| Upstream | <https://github.com/w3c/data-shapes> |
| Path | `data-shapes-test-suite/tests/` |
| Commit | `94d8bc2bd4fc4fdc6f2964d1ec4a892329e05f06` |
| Commit date | 2026-09-12 |
| Commit subject | `#1226: Added test case and changed contract for rules with same order (#1244)` |
| Published report | <https://w3c.github.io/data-shapes/data-shapes-test-suite/> |
| Vendored on | 2026-09-13 |
| SHA-256 of the `.ttl` tree | `2ca9709d35a7e85d3dde6a1e4311a391728f1cf4b2ade47c0ce434652886fd40` |

The tree digest is reproducible with:

```sh
cd tests/w3c-shacl && find . -type f -name '*.ttl' | sort | xargs shasum -a 256 | shasum -a 256
```

## Licence

W3C Software and Document License, the terms the whole `w3c/data-shapes`
repository carries (`LICENSE.md` at its root, reproduced here). It permits
copying and redistribution, with or without modification, for any purpose,
provided the copyright notice, the licence link and a statement of changes
travel with the copy. This file is that statement of changes: there are none
to the test data.

## Why vendored rather than fetched at test time

The reasons are given in order of weight.

1. **A conformance number that depends on a network fetch is not a
   measurement.** The suite is a moving target: the Working Group approves and
   edits tests. If CI fetched it, the ratchet in
   `tests/w3c_shacl_conformance_test.rs` would compare today's engine against
   an unpinned oracle, and a red build could mean "someone in the WG merged a
   test" rather than "we regressed". Pinning the suite to a commit makes the
   baseline mean one thing.
2. **CI must run offline and deterministically.** Every other gate in this
   repository does. The `lean` job builds a checker from vendored sources; the
   `shacl-differential` job runs against a corpus that is in the tree. A
   network dependency in the test path is a flake generator, and this
   repository has already lost a six hour CI run to an apt mirror going dark
   (see the comment on the `features` job in `.github/workflows/ci.yml`).
3. **It is 632 KB.** The cost of carrying it is nil against the cost of not
   having it.

## Refreshing

```sh
git clone --depth 1 https://github.com/w3c/data-shapes /tmp/data-shapes
rm -rf tests/w3c-shacl/core tests/w3c-shacl/sparql tests/w3c-shacl/manifest.ttl
cp -R /tmp/data-shapes/data-shapes-test-suite/tests/. tests/w3c-shacl/
cp /tmp/data-shapes/LICENSE.md tests/w3c-shacl/LICENSE.md
# then update the table above and re-cut the baseline:
OO_W3C_SHACL_UPDATE_BASELINE=1 cargo test --test w3c_shacl_conformance_test -- --nocapture
```

A refresh that moves the totals is a deliberate act and shows up as a diff in
`tests/w3c_shacl_baseline.json`. A refresh that silently lowers the pass count
is caught by the ratchet before the baseline is re-cut.
