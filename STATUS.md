# Formalization Status

The core NC-C complexity results are verified for the positive-dimensional
source class and its causal first-order oracle model.

## Verified core

- Exact scalar functions and inner/outer hard-instance construction,
  including derivative bounds, strong concavity, smoothness, zero-chain
  support, phase estimates, and the initial value gap.
- The closed convex feasible-domain class, with prescribed derivatives
  within the domain and Euclidean smoothness. Dual attainment and actual
  value-function properties are derived from the class assumptions.
- Proximal existence and uniqueness, actual Moreau differentiability,
  the `2*ell` gradient Lipschitz bound, stationarity equivalence, and the
  initial squared-gradient bound `8*ell*Delta/3`.
- Scaling and parameter selection for the hard instance, terminal
  nonstationarity, and the zero-respecting lower bound.
- Rotation closure and Moreau covariance under within-domain derivatives,
  together with the finite-horizon resisting-oracle construction and the
  lower bound for arbitrary deterministic algorithms.
- A genuine reply-driven upper algorithm, including initialization,
  first-success local stopping, state transitions, minimum-residual
  selection, feasible queries, and the counted stationarity guarantee.
- Matching upper and lower bounds for one positive-dimensional minimax
  quantity in `NCC.MainResults.source_matching_oracle_complexity`.

Standalone estimates include the non-strict dual-boundary value/gradient
identity, the sharp coefficient-5 startup bound using the actual initial
gap, and residual bounds stated with the actual envelope infimum.

The NC-C game-stationarity extension proves an actual queried-output
guarantee with accuracy dependence `O(epsilon^(-5/2))` for fixed positive
class parameters. Other extension modules remain available under their
individual theorem assumptions.

## Checked snapshot

| Item | Result |
| --- | --- |
| Audit date | 2026-09-12 |
| Build jobs | 8,891 |
| NCC theorem declarations | 2,192 |
| NCC definitions | 519 |
| NCC source modules | 102 |
| Root coverage | Every NCC module reachable from `NCC.lean` |
| Allowed axioms | `propext`, `Classical.choice`, `Quot.sound` |
| Lean | 4.32.0 |
| mathlib commit | `11d11a11a667a8fa8ea19d9456fe059f683e308f` |

The snapshot passed the strict build and transitive axiom audit. Counts
refer to this checked revision and must be refreshed after mathematical
changes. They count Lean declarations, not independent paper statements.

## Source baseline

Source identifier: `main.tex`.

SHA-256:
`5E18D87B1636334EB8497027F97BD7FDF74CB985D005D95F6DB4280D25281872`.

This checksum identifies the source used for the correspondence checks.
It does not automatically certify later source revisions.

## Reproducibility and scope

[README.md](README.md) gives the build commands. Dependencies are pinned,
and reused proof sources are vendored under `Legacy/`. The recorded build
used matching dependency caches; it is not a claim that a fresh,
uncached installation has already been tested.

The audit checks the formal declarations and their transitive dependencies.
Mathematical correspondence is documented separately in the project
notes. No blanket verification of all surrounding prose or external
literature is asserted.
