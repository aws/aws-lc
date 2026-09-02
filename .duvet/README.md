# Duvet — requirement-to-code coverage for aws-lc

[Duvet](https://github.com/awslabs/duvet) traces normative requirements from a
specification to the source that implements and tests them. Each requirement is
cited in-tree with a `//=` annotation, and Duvet reports which requirements are
covered, tested, or missing.

This directory is a scoped demonstration: it wires **RFC 8032 (EdDSA)** to the
Ed25519 / Ed25519ph surface in `crypto/fipsmodule/curve25519/`.

## Links

- Duvet project: https://github.com/awslabs/duvet
- Config schema (v0.4.0): https://awslabs.github.io/duvet/config/v0.4.0.json
- RFC 8032 (EdDSA): https://www.rfc-editor.org/rfc/rfc8032

## Layout

| Path | Purpose |
|------|---------|
| `config.toml` | Source patterns, specifications, requirement patterns, report config |
| `specifications/` | Cached copy of the spec text Duvet extracts from |
| `requirements/` | Requirements extracted from the RFC prose (`duvet extract`) |
| `rfc8032-requirements/` | Hand-authored requirements for descriptive (non-RFC-2119) prose |
| `scripts/check_annotations.py` | Annotation-regression guard (see below) |
| `annotations.baseline` | Committed snapshot of source-code annotations |
| `reports/` | Generated reports — gitignored, never committed |

## Generate reports locally

Install Duvet (Rust toolchain required):

```sh
cargo install duvet --locked
```

Generate the HTML + JSON coverage reports (run from the repo root):

```sh
duvet report
open .duvet/reports/report.html
```

Output paths and formats come from the `[report.*]` blocks in `config.toml`.
`reports/` is gitignored — this PR does not publish the report anywhere.

## Annotation-regression check

`scripts/check_annotations.py` snapshots every source-code `//=` citation Duvet
finds and fails if any snapshotted annotation is later removed or broken. The
`Duvet Annotation Coverage` GitHub Actions workflow runs it on every PR that
touches `.duvet/` or the annotated source, so a dropped citation fails CI.

```sh
# Verify no baselined annotation went missing (what CI runs):
python3 .duvet/scripts/check_annotations.py

# After intentionally adding/removing annotations, refresh the baseline:
python3 .duvet/scripts/check_annotations.py --update
```

Adding annotations never fails the check — it just reminds you to refresh the
baseline. Only removals are treated as regressions.

## TODOs

- Expand annotation coverage of the extracted RFC 8032 requirements (many
  `MUST`/`SHOULD` statements are currently uncited — see the HTML report).
- Add a matching `type=test` annotation for the `section-8.7` implementation
  citation (currently implementation-only).
- Decide whether to publish the HTML report (e.g. GitHub Pages) once coverage
  is meaningful; kept local-only for this PR.
- Extend the pattern to additional FIPS-relevant specs beyond EdDSA.
