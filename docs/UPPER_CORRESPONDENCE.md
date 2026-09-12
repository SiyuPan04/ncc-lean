# Upper algorithm correspondence

Source baseline: `main.tex`, SHA-256
`5E18D87B1636334EB8497027F97BD7FDF74CB985D005D95F6DB4280D25281872`.
The baseline identifier is recorded in [paper-manifest.json](../paper-manifest.json).
This document describes the correspondence for Theorem 3.3
(`thm:upper`), the tracked outer algorithm, and its feasible FOAM implementation.
Coverage is limited to the imported declarations described in [COVERAGE.md](COVERAGE.md).

## Analytic objects

Generic analytic components are vendored under
`Legacy/NCCLowerBoundVerification/Upper/`. The `NCC/Upper` modules instantiate
their hypotheses for the feasible-domain class and implement the specified algorithm.

| Object | Definitions and correspondence |
| --- | --- |
| Regularized saddle | `PointwiseConjugate.smoothedSaddle` is `f(x,y)+ell*||x-z||²-r*||y||²/2`. Removing the explicit quadratics gives `decurved`, independent of `r`. |
| Conjugate objective | `Gamma` takes the supremum over the actual primal set. `Pzr` adds `||q||²/(2ell)+r*||y||²/2`, with feasible dual argument encoded by a subtype. |
| State | `RelativeFOAM.State` stores `q,y,qFast,yFast`. `ValidState` requires only `yFast ∈ Y`; the slow dual coordinate can be infeasible. |
| Energy | The slow-coordinate coefficients are `2alpha/ell` and `2r`; the fast contribution is twice the actual conjugate gap. |
| Macro step | `alpha=sqrt(8r/ell)`, `etaQ=ell/2`, `etaY=4/(alpha*ell)`, and `theta=8/ell`. The interpolation, residual certificate, and slow updates are explicit. |
| Block length | `blockIterations` is the natural ceiling of `(2/alpha)*log(1/rho)` in the positive parameter range. |
| Primal readout | `projectX(-qFast/ell)`; its squared distance to the actual proximal point is at most `energy/ell`. |
| Center translation | Both conjugate coordinates shift by `-2ell*d`. The energy majorant is `2energy+24ell*||d||²`. |
| Curvature transfer | The state is retained when curvature changes from `r` to `r/4`; the transfer coefficient is `27/4`. |
| Outer potential | The actual proximal/readout trajectory satisfies the coupled descent estimate for `W=p+2B`. |

The real-valued helper `PzrTotal` is zero outside `Y`. It is used only with
feasible fast pairs in these energy theorems; it is not an extended-real
indicator objective at infeasible points.

## Algorithm-specific choices

The assembled algorithm differs from the generic fixed-cutoff schedule in five
explicit ways. These choices have separate definitions and correspondence proofs:

1. `WithinFirstStop.firstStopIndex` is the first successful residual test
   with index at least one. Its universal upper bound follows from the
   projected micro certificate.
2. The retained homotopy state receives the exact budget reset
   `B0=15*(Delta+r*D²)`.
3. The outer horizon is `ceil(4000*(ell*Delta/eps²+1))`.
4. Selection minimizes `Q=ell*||d||²+B`, rather than the generic
   square-root certificate.
5. Ties are resolved by the smallest numerical index.

The generic fixed-cutoff client and its square-root-score selector remain
separately defined. They are not identified with this execution.

## From class hypotheses to execution

`WithinSystem` derives projections, finite conjugate sections, saddle
stationarity, proximal existence, and local solver certificates directly from
`Model.WithinClass`. `WithinFirstStop` supplies the first-success solver and
its genuine normal-cone relations. `WithinRun` instantiates startup,
divide-by-four warm stages, the reset budget, the outer horizon, and the
least-index selection.

`AdaptiveMicroProgram` uses only local replies and known geometry.
`AdaptiveFOAMProgram` composes its macro calls, and `CurrentProgram.program`
composes startup, homotopy, translated outer calls, and selection.
`WithinProgram.feasible_program_correct` identifies the actual program
output and proves feasibility, Moreau OS, and its query bound without an
ambient-extension premise.

`Theorem.domainAlgorithm` receives numerical parameters and a known domain
label, not the objective or a class-membership proof. Its wrapper adds the
origin query and a query at the returned point. The resulting uniform
queried-iterate theorem is `Theorem.exists_domain_algorithm_uniform`.
`MainResults.source_matching_oracle_complexity` uses the same positive-dimensional
minimax quantity for both bounds.

For the sharp standalone estimates, see [EXACT_STARTUP.md](EXACT_STARTUP.md)
and `Upper.ExactResidual.residual_comparison`. For executable counts and
model conventions, see [CURRENT_COST.md](CURRENT_COST.md) and
[WITHIN_UPPER.md](WITHIN_UPPER.md).
