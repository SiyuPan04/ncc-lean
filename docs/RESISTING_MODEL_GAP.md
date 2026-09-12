# Deterministic resisting oracles

The development contains two complementary reductions: a uniform simulator
for arbitrary local oracles, and a tagged hard-family reduction for the
quantitative lower bound.

## Uniform simulator

`Lower.UniformResisting.finite_horizon_resisting_oracle` has quantifier order

`forall horizon, forall deterministic A, exists one zero-respecting Z, forall base oracles`.

The same domainwise simulator works before the base objective and positive
dual-ball diameter are supplied. Its ambient dimensions are exactly
`m+T0,n+T0`, and one final pair of orthonormal frames realizes every actual
query with index `t<T0`.

Positive base dual dimension ensures uniqueness of the positive diameter
encoded by the known ball domain. The theorem also permits primal dimension
zero; the final main minimax quantity uses positive dimensions for both sets.

| Module | Role |
| --- | --- |
| `UniformResisting.Frames` | Support-set revelation and completion under the non-strict capacity bound `base dimension + query count <= ambient dimension`. |
| `UniformResisting.Simulator` | Objective-independent replay, feasible base queries, origin initialization, zero-respecting behavior, and prefix consistency. |
| `UniformResisting.Realization` | Exact value and both-gradient transcript correspondence for one completed frame pair. |
| `UniformResisting.BallLabel` | Canonical known-domain labels and diameter uniqueness. |
| `UniformResisting.RawMaps` | All-history feasibility repair preserving every feasible actual run. |

Replay decisions use known dimensions, partial frames, previous virtual
queries, and received gradient coordinates. The realization theorem does
not assume a zero-chain or hard-family obstruction of the base oracle.

## Quantitative hard-family reduction

`Lower.Deterministic` takes a genuine hard instance, its tagged derivative
zero-chain, class certificate, and terminal nonstationarity theorem.
For every causal deterministic component, it constructs a rotated instance
whose first `K` queried primal points fail OS. The original algorithm need
not be zero-respecting.

The tagged construction uses the sufficient capacities

```text
base primal dimension + (K+1) < ambient primal dimension
base dual dimension   + (K+1) < ambient dual dimension.
```

These bounds suffice for a dimension-free lower theorem. The sharper
`base+T0` uniform-simulator statement is proved by the separate modules above.

`DeterministicLower.exists_current_hard_instance` discharges the class,
chain, scaling, and terminal premises for the concrete construction.
Its hypotheses contain numerical parameters, the accuracy regime, and
the arbitrary causal component—not a correctness certificate for the result.

The tagged primal layout `(a,b,s)` differs from the construction's
`(s,a,b)` layout. `Construction.ZeroChain.toPrimal` and
`Lower.TaggedSource` supply a genuine orthogonal block permutation,
derivative pullback, value covariance, and terminal obstruction.

The chosen horizon is `L-1`; exact floor arithmetic gives

`c1*ell²*D*Delta/eps³+1 <= L-1`.

`Complexity.PositiveDimension.oracleComplexity_lower` packages the bound
for the positive-dimensional infimum/supremum of actual OS hitting indices.

## Rotation and outputs

`Lower.WithinRotation.class_rotate` proves class closure on a full primal
space and a dual ball using only feasible-domain derivatives.
Its covariance theorems identify the actual proximal point, envelope
derivative, squared gradient norm, and OS predicate.
The global-derivative route in `Lower.Rotation` is a separate result that
also applies to the smooth hard construction.

For a positive horizon, `Deterministic.appendOutput` appends a feasible
deterministic primal output, paired with the dual origin, as query `K`.
The preceding transcript is unchanged. `arbitrary_output_failure` transfers
failure through `K+1` queries to this output.

`DeterministicLower.exists_current_hard_output` uses horizon `L-2`.
`outputHorizon_lower` provides enough arithmetic slack for the same cubic
lower rate while charging the extra query. The condition `0<K` preserves
the mandatory origin query at index zero.

## Raw causal maps

A `RawComponent` requires causality and the origin start.
Its `originRepair` keeps feasible proposals and replaces others by the origin.
`originRepair_queriedAt_eq` and `originRepair_queriedTranscript_eq`
preserve every feasible actual run, including function values and both
gradients. The domainwise repair is chosen independently of the objective,
so all-history feasibility does not exclude algorithms whose actual
trajectories satisfy the query model.
