# First-success oracle execution and query counts

The cost analysis connects concrete projected iterates, reply-driven programs,
and the final deterministic query sequence. Its main modules are
`CurrentCost`, `AdaptiveMicroProgram`, `AdaptiveFOAMProgram`,
`CurrentProgram`, `WithinProgram`, and `Upper.Theorem`.

## Micro execution

Let `s=firstStopIndex` and
`N=ProjectedMicro.feasibleMicroIterations`. The semantic micro trace lists
the feasible saddle-oracle queries corresponding to `u^0,...,u^s`.
The initial point is queried once, the first update is mandatory, and each
successive reply is reused in the next update. The terminal reply also
provides the data used to decode the returned tuple.

`microTrace_length` proves the exact count `s+1`;
`firstStopIndex_le_universal` gives `s<=N`.
The trace is not padded to the universal bound.

`AdaptiveMicroProgram.program` receives only projections, numerical
parameters, the center, and the state. Gradient data in its updates, test,
and output come exclusively from query replies. `program_correct` identifies
the returned tuple with the analytic first-stop oracle and gives the exact
executed count `firstStopIndex+1`.

The program is capped at `N` on arbitrary reply branches. Genuine class
replies pass the residual test by this cap. Other branches still return a
feasible tuple; a residual certificate is not asserted for arbitrary replies.

`DepthAtMost` permits unequal early-return depths. `program_depth` bounds
every branch by `N+1`, and `program_all_histories_feasible` proves feasibility
after every reply history.

## FOAM blocks and semantic traces

`macroTrace` concatenates micro traces at actual FOAM states.
`warmStageTrace` starts from the retained homotopy state, and
`outerStageTrace` starts from the co-translated outer state at its new center.
`runTrace` combines startup, warm stages, and all outer transitions.

`AdaptiveFOAMProgram.eval_callProgram_eq_family` identifies the reply-driven
block with the first-stop analytic system.
`blockProgram_trace_length_eq_macroTrace` proves equality of executed and
semantic counts. A literal equality of the trace lists is not needed.

For `K=blockIterations(alpha(ell,r),rho)`, all branches use at most
`K*(N+1)` queries. With `0<r<=ell/8` and `0<rho<1`, a conservative block
majorant is

`C(rho)*sqrt(ell/r)`, where
`C(rho)=(2*log(1/rho)+1)*(N+1)`.

The separate ceiling estimate in
`BlockCostConcrete.feasibleBlockCost_lt_alpha` retains the sharper
additive-one behavior when `rho` approaches one.

## Full program

`CurrentProgram.program` composes the first-success startup, divide-by-four
warm calls, exact reset `15*(Delta+r*D²)`, translated `rho=1/400` calls,
and least-index minimum-Q selection. It performs exactly

`T=ceil(4000*(ell*Delta/eps²+1))`

outer transitions and stores snapshots through time `T`.
Its constructor has no objective or gradient argument.

`eval_program` identifies the output with `CurrentRun.output`.
`program_trace_length` proves equality of its actual count with
`CurrentCost.runTrace.length`. All-history feasibility and a finite
all-branch depth bound are separate theorems.

`WithinProgram` gives the corresponding execution and direct count bound
under `Model.WithinClass`, using the same program constructor. It does not
require transport through an ambient differentiable extension.

## Uniform count and queried output

The geometric warm-stage sum avoids an additional factor equal to the
number of curvature levels. Using `T<=4001*(ell*Delta/eps²+1)`, the
uniform client bound is

`traceRateConstant * (ell*Delta/eps²+1) * max(1,ell*D/eps)`,

with numerical constant

`traceRateConstant=N+1+12*C(1/8)+24006*C(1/400)`.

This bounds an actual executed `List.length`. It is independent of the
objective, dimensions, and problem parameters.

The deterministic wrapper adds an origin query and a query at the returned
feasible anchor. If the client uses `n` queries, the final anchor is queried
at zero-based index `n+1`, and the wrapper uses exactly `n+2` calls.
The uniform total bound replaces `traceRateConstant` by
`traceRateConstant+2`. Query counts and first hitting indices are therefore
related by proved offsets, not identified definitionally.

See [WITHIN_UPPER.md](WITHIN_UPPER.md) for the class-to-algorithm endpoint
and [MODEL_SEMANTICS_AUDIT.md](MODEL_SEMANTICS_AUDIT.md) for oracle conventions.
