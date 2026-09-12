# Model semantics

This document specifies the dimensions, differential convention, quantitative
norms, constrained values, and oracle quantifiers used by the main endpoints.
The associated source baseline is identified in
[paper-manifest.json](../paper-manifest.json).

## Positive dimensions

The final minimax quantity is
`Complexity.PositiveDimension.minimaxOracleComplexity`.
Its `Domain` type restricts both dimensions to positive integers, and its
algorithm type supplies components only for those domain labels.

The coordinate backend and the helper `Complexity.minimaxOracleComplexity`
also permit zero dimensions. `extendAlgorithm_component` and
`restrict_extend` relate their algorithm types using origin-only components
on excluded dimensions. The upper bound transfers in the required inequality
direction; equality of the enlarged and positive-dimensional quantities is
not needed. The hard instances have positive dimensions.

`minimaxOracleComplexity_eq` exposes the positive-dimensional infimum over
algorithms and supremum over domain-labelled class members.
`oracleComplexity_bounds` and
`MainResults.source_matching_oracle_complexity` use that single quantity.

## Euclidean quantitative norms

`EVec d` is a finite coordinate-function type. Its default topological norm
is the coordinate supremum norm, but quantitative estimates use `vecSq`
and `jointSq`: Euclidean sums of squares.

The smoothness, diameter, proximal quadratic, energy, and stationarity
bounds use those Euclidean quantities. `jointGradientCLM_apply` is the
coordinate dot product, and `hasFDerivAt_envelope` proves that the stated
residual vector represents the actual envelope derivative.
`GameStationarity.IsGS` takes distances in `EuclideanSpace`.
Topological norm comparisons used for compactness do not introduce a
dimension factor into these quantitative estimates.

## Feasible values and constrained infima

`ValueOn` is a real supremum. Under `WithinClass`, every feasible primal
point has an actual dual maximizer, so every feasible value used by the
endpoints is an attained finite value.

The indicator convention is encoded by minimizing explicitly over `X`.
`IsProxPoint` includes membership and minimality over feasible points;
`envelope_eq_inf` identifies the envelope with that constrained infimum.
Off-domain values of the total function do not participate.

The pointwise initial-gap field yields `value_bddBelow` and `initial_gap`.
The converse implication for a genuine finite infimum is
`Model.pointwise_gap_of_inf_gap`. The origin makes the relevant sets
nonempty. `ExactStartup` and `ExactResidual` additionally expose
greatest-lower-bound certificates for their standalone estimates.

## Boundary derivatives

The oracle supplies a linear functional satisfying `HasFDerivWithinAt`
on the closed feasible product. Normal components remain part of the
prescribed gradient even where the differential is nonunique.
The within derivative is tied to the actual objective, and joint smoothness
constrains the supplied gradients.

No ambient extension is required by the direct upper or rotation results.
The hard construction additionally has an actual ambient derivative.
The neighborhood-C1 convention maps into this model through
`ConventionBridge.InClass.toWithin`; no equivalence with every possible
boundary-derivative convention is asserted.

## Causality, feasibility, and hitting indices

`DeterministicFOComponent.nextQuery` receives a finite history of the
actual function value and both gradients. Components are indexed by known
domains, not objectives, and begin at the full origin.
Known projections and exact-real arithmetic are part of the model, not
separately charged computational primitives.

`queriedHittingTime` is the least successful zero-based query index, with
infinity when no query succeeds. `queriedHittingTime_lt_iff_actualOS`
identifies finite thresholds with the genuine feasible Moreau OS test.
Conversion to extended nonnegative reals preserves the required infima and
suprema.

The upper wrapper's final query has index `clientLength+1`; its count is
`clientLength+2`. These offsets are proved explicitly.
Typed components require feasibility for all reply histories.
`UniformResisting.RawMaps` repairs infeasible proposals to the known origin
and proves that one repaired algorithm preserves every feasible actual run.

For the deterministic lower bound, the algorithm is chosen before the hard
instance. A single instance works simultaneously for all zero-respecting
methods only in the separately stated zero-respecting theorem.
The uniform resisting theorem instead chooses one simulator before all base
objectives. See [RESISTING_MODEL_GAP.md](RESISTING_MODEL_GAP.md).
