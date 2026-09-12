# Verification Report

## Result

The core NC-C lower and upper complexity results, including their matching
regime, are formally verified. The endpoint
`NCC.MainResults.source_matching_oracle_complexity` compares both bounds
on `NCC.Complexity.PositiveDimension.minimaxOracleComplexity`.

This quantity uses positive primal and dual dimensions, known feasible
domains, causal deterministic algorithms, and the actual first-order
oracle. The lower bound has the required algorithm/instance quantifier
order; the upper algorithm is independent of the unknown objective and
uses its oracle replies.

## Mathematical correspondence

The development includes:

- The exact scalar functions and hard-instance objective, together with
  represented derivatives, smoothness and terminal certificates.
- Closed convex feasible domains and derivatives within those domains,
  without imposing an ambient differentiability assumption on the
  general source class.
- Euclidean norm conventions, actual dual maxima, proximal minimizers,
  and derivatives of the actual Moreau envelope.
- The full finite-horizon resisting construction, including feasibility,
  transcript correspondence, rotations, and dimension accounting.
- Executable reply-driven oracle programs with checked stopping,
  initialization, transitions, output selection, and query counts.
  Query indices and total oracle calls are related explicitly.
- The NC-C game-stationarity extension, with a genuine queried
  stationarity witness and its stated accuracy-dependent cost bound.

Additional extension theorems are checked under the assumptions and cost
formulas written in their respective modules.

## Kernel and build audit

The 2026-09-12 snapshot passed the strict build and transitive axiom audit:

| Check | Recorded result |
| --- | --- |
| Build jobs | 8,891 |
| Audited NCC theorem declarations | 2,192 |
| Audited NCC definitions | 519 |
| NCC source modules | 102, all reachable from `NCC.lean` |
| Nonstandard axioms or `sorryAx` | None in audited dependencies |

The permitted axioms are `propext`, `Classical.choice`, and
`Quot.sound`. The declaration counts describe the Lean development,
not the number of independent mathematical statements in the source.

The environment is pinned to Lean 4.32.0 and mathlib commit
`11d11a11a667a8fa8ea19d9456fe059f683e308f`.
See [README.md](README.md) for `build.ps1` and standard Lake commands.

## Source identification and scope

The source baseline is `main.tex`, SHA-256:

`5E18D87B1636334EB8497027F97BD7FDF74CB985D005D95F6DB4280D25281872`.

The checksum and audit metadata are recorded in
[paper-manifest.json](paper-manifest.json). The baseline identifies the
source used for correspondence checks; subsequent changes require a new
review.

Lean checks the precise formal statements and all their hypotheses.
Compilation alone does not establish equivalence with an informal
statement. The core results include explicit source-model bridges;
prose, numerical illustrations, historical comparisons, and external
literature are outside the kernel audit.
