# NC-C Lean Formalization

A Lean 4 formalization of deterministic first-order oracle complexity for
smooth nonconvex-concave (NC-C) minimax optimization.

The verified core includes the zero-respecting lower bound, the general
deterministic lower bound, the constructive upper bound, and their matching
complexity regime. The final result is
`NCC.MainResults.source_matching_oracle_complexity` in
[NCC/MainResults.lean](NCC/MainResults.lean). It proves matching bounds for
the same positive-dimensional function class and causal oracle model:

```text
Theta(ell^2 * D * Delta / epsilon^3)
```

The theorem states the positive-parameter assumptions, numerical constants,
and admissible accuracy range explicitly.

## Build

The project pins Lean **4.32.0** and mathlib commit
`11d11a11a667a8fa8ea19d9456fe059f683e308f`.
Install elan and Git, then run these commands from the repository root:

```text
lake exe cache get
lake --wfail build
lake env lean Audit/Axioms.lean
```

The wrapper requires PowerShell 7 (`pwsh`), not Windows PowerShell 5.1.
It additionally checks that every module under `NCC/` is reachable from
the root import:

```powershell
pwsh -File ./build.ps1
```

Keep `lean-toolchain`, `lakefile.toml`, and `lake-manifest.json` unchanged
to reproduce the pinned environment. Public dependencies are downloaded by
Lake; reused proof sources are included in `Legacy/`.

## Verification snapshot

The checked snapshot of 2026-09-12 completed **8,891 build jobs** and
audited **2,192 NCC theorem declarations**, **519 definitions**, and
**102 NCC source modules**. All mathematical modules were reachable from
`NCC.lean`.

The transitive axiom audit permits only `propext`, `Classical.choice`,
and `Quot.sound`. It rejects `sorryAx` and nonstandard axioms. These are
counts of Lean declarations, not counts of independent paper theorems.

## Project map

| Entry | Purpose |
| --- | --- |
| [NCC.lean](NCC.lean) | Root import for the mathematical development |
| [NCC/MainResults.lean](NCC/MainResults.lean) | Matching NC-C oracle complexity |
| [NCC/Oracle/PositiveDimension.lean](NCC/Oracle/PositiveDimension.lean) | Positive-dimensional minimax complexity |
| `NCC/Model/`, `NCC/Moreau/` | Feasible-domain derivatives, value functions, and actual Moreau envelopes |
| `NCC/Construction/` | Exact hard-instance formulas and analytic estimates |
| `NCC/Lower/` | Zero-chain, rotation, resisting-oracle, and deterministic lower bounds |
| `NCC/Upper/` | Reply-driven algorithms, stationarity, and query counts |
| `NCC/Extensions/` | Additional theorem modules with their declared assumptions |
| [Audit/Axioms.lean](Audit/Axioms.lean) | Transitive axiom audit |
| [STATUS.md](STATUS.md) | Coverage summary |
| [VERIFICATION_REPORT.md](VERIFICATION_REPORT.md) | Audit scope and mathematical correspondence |
| [paper-manifest.json](paper-manifest.json) | Source identifier, checksum, and pinned audit metadata |

## Scope

The core proofs connect the explicit construction, represented derivatives,
closed convex feasible sets, actual oracle replies, and counted algorithm
executions. The NC-C game-stationarity (GS) extension is also included.

This is a mathematical formalization, not a floating-point solver package.
The oracle model uses exact real arithmetic and known-domain projections;
oracle-call bounds do not measure arithmetic runtime.

Lean verifies each formal statement under its written assumptions.
Additional extension modules should be read with their exact hypotheses
and cost statements. The audit is not a blanket validation of prose,
figures, literature comparisons, or claims outside the formal declarations.
