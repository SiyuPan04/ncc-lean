# Upper bound under feasible-domain differentiation

`NCC.Upper.WithinProgram.feasible_program_correct` applies to
`Model.WithinClass ell D Delta P` and every positive accuracy `eps`.
The actual reply-driven program returns a feasible point whose Moreau-envelope
gradient has squared Euclidean norm at most `eps²`. Its query-trace length
is at most

`CurrentCost.traceRateConstant * (ell*Delta/eps²+1) * max(1,ell*D/eps)`.

The derivative convention is `RepresentsJointGradientWithin` on `X × Y`.
No ambient or neighborhood extension is required.

## Analytic construction

`WithinFirstStop` derives the first positive successful residual index
and its universal bound from the feasible-domain micro certificate.
Projection normals and class-derived support inequalities construct the
first-stop `OuterSystem`. The adaptive micro program has the corresponding
output and exact count `firstStopIndex+1`.

`WithinRun` establishes initial-gap, proximal-displacement, startup,
homotopy, and reset-budget bounds for the actual retained states. It uses
the specified target curvature, horizon, and least-index minimizer of the
squared observable. `WithinRegularization` transfers stationarity to the
original value using only feasible maxima and actual Moreau derivatives.

## Causal implementation

`WithinProgram` reuses `CurrentProgram.program`. Its inputs are numerical
data, known projections, and a feasible initial point. The objective and its
class proof are inputs to correctness theorems, not to the program constructor.

Correspondence proofs identify startup, warm, and outer states and the final
selection. The count follows from compositional depth bounds, the geometric
warm-stage sum, and the outer-horizon estimate. Feasibility holds after every
counterfactual reply history.

## Domainwise queried-iterate theorem

`Theorem.domainAlgorithm` uses only numerical parameters and a known closed
convex domain pair. Projection uniqueness connects its geometric projections
to those used by the analytic proof.

The wrapper prepends the origin query and appends a query at the projected
output. On genuine class replies, this is the returned feasible anchor.
For client trace length `n`, the final query has index `n+1`, and the
total count is exactly `n+2`. Thus the total bound is

`(CurrentCost.traceRateConstant+2) * (ell*Delta/eps²+1) * max(1,ell*D/eps)`.

`Theorem.exists_domain_algorithm_uniform` chooses one algorithm before
every matching instance. `Complexity.PositiveDimension.oracleComplexity_upper`
packages its rate for the positive-dimensional minimax quantity.

The query model requires causal reply-history maps and a full-origin start.
It is an exact-real first-order oracle model: arithmetic and known projections
are not assigned additional runtime costs. See
[MODEL_SEMANTICS_AUDIT.md](MODEL_SEMANTICS_AUDIT.md) and
[CURRENT_COST.md](CURRENT_COST.md).
