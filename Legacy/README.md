# Vendored proof dependencies

The `Legacy` directory contains three supporting source namespaces:

- `NCPLVerification`: analytic, linear-algebra, and oracle-construction lemmas.
- `NCCLowerBoundVerification`: generic NC-C analysis, solver, and oracle infrastructure.
- `NCCLowerBound`: a simplified lower-bound construction and supporting identities.

They retain their namespaces to preserve import dependencies and are ordinary
`lean_lib` targets with `srcDir = "Legacy"`. They are built against the
toolchain and mathlib revision pinned by this repository. No external local
project directory is required.

## Reuse and coverage

A vendored theorem contributes to the main results only after its definitions
and hypotheses are connected to the corresponding `NCC` construction or
algorithm. For example, the generic fixed-cutoff upper schedule differs from
the first-success client and least-index minimum-Q selector implemented here.
See [upper correspondence](../docs/UPPER_CORRESPONDENCE.md) and the
[coverage ledger](../docs/COVERAGE.md).

Only the transitive imports of the exported development are included in
its verification scope. Unimported vendored sources are available for reuse
but are not counted as coverage of the main results.

## Toolchain compatibility

The vendored libraries retain their implicit-variable and synthesis settings.
Their library configuration disables cosmetic warnings for unused variables,
unused simplifier arguments, unused section variables, and unnecessary
sequence focus. The `NCC` library keeps explicit-variable settings.

Compatibility edits include renamed library lemmas, redundant tactic cleanup,
and a scoped definition-style linter exception. They do not add mathematical
hypotheses. The resisting-oracle cleanup preserves theorem statements and
dimension-capacity assumptions.

Strict builds reject proof holes. The transitive
[axiom audit](../Audit/Axioms.lean) checks imported dependencies of exported
`NCC` declarations and permits only `propext`, `Classical.choice`, and
`Quot.sound`. See [STATUS.md](../STATUS.md) for the audited revision.
