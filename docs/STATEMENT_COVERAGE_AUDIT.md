# Active-statement coverage audit

Statement correspondence, 2026-09-12. Source: `main.tex`, SHA-256
`5E18D87B1636334EB8497027F97BD7FDF74CB985D005D95F6DB4280D25281872`.
The whole-project build and axiom audit are recorded in `../STATUS.md`.

## Scope and counting rule

Every active theorem/proposition/lemma label has a row in
`COVERAGE.md`, with concrete proof endpoints or explicitly connected generic
analytic theorems. Coverage is not inferred merely from the final complexity
theorem.

The named-statement inventory is:

| Kind | Count |
| --- | ---: |
| Theorem | 3 |
| Proposition | 6 |
| Lemma | 16 |
| Certificate condition | 1 |
| Definition | 7 |
| Corollary, assumption, claim, fact, observation, example, question | 0 |

Thus there are **25 active theorem/proposition/lemma statements**, alongside
the certificate condition and definitions. Percent-commented lines were
excluded before enumerating
the environments. No active `comment`, `restatable`, or `iffalse` block was
found. Commented-out drafts are not included as additional active statements.
Other verified conclusions are listed separately below.

## Complete theorem/proposition/lemma inventory

Names beginning with `Construction`, `Lower`, `Upper`, `Complexity`, or
`MainResults` below are under `NCC`. Generic dependencies named explicitly
are in the vendored `NCCLowerBoundVerification.Upper` or
`NCCLowerBoundVerification` namespaces. “Covered” means the displayed
standalone conclusion is represented, not just its later use.

| Source line | Active label and kind | Proof correspondence and verdict |
| ---: | --- | --- |
| 642 | `lem:rotation-covariance` — lemma | Covered by `Lower.WithinRotation.class_rotate`, `gradient_norm_covariance`, and `isOS_covariance`. Includes arbitrary source-class members with within-domain derivatives, not only the hard instance. |
| 656 | `lem:resisting-oracle` — lemma | Covered by `Lower.UniformResisting.finite_horizon_resisting_oracle`: one domain-wise zero-respecting simulator precedes all objectives and positive diameters; exact added dimensions are `m+T0,n+T0`. |
| 683 | `thm:zr-lower` — theorem | Covered by `Lower.ZeroRespecting.current_zeroRespecting_lower`: one current instance precedes every zero-respecting deterministic method, with actual query support, terminal obstruction, and the cubic horizon. |
| 694 | `thm:deterministic` — theorem | Covered by `Lower.DeterministicLower` and `Complexity.PositiveDimension.oracleComplexity_lower`; the source positive-dimensional minimax quantifiers are retained. |
| 723 | `thm:upper` — theorem | Covered by `Upper.Theorem.exists_domain_algorithm_uniform` and `Complexity.PositiveDimension.oracleComplexity_upper`, including every positive accuracy and counted origin/output queries. |
| 1320 | `lem:smoothing` — lemma | Covered directly by `Upper.WithinRegularization.gradient_bias`, for every ambient anchor and every nonnegative regularization, hence the printed positive case. |
| 1471 | `prop:foam-interface` — **lemma** | Covered by the actual first-stop system from `Upper.WithinFirstStop`, `OuterTrajectoryConcrete.readout_error_le_energy`, generic `RelativeFOAMContraction.block_energy_contraction`, and the executed block/call correspondence in `Upper.WithinProgram`. Actual finite query counts and feasible residual tests are implemented; contraction is not assumed. |
| 1537 | `prop:anchor-shift` — proposition | Covered by `TrackingConcrete.Pzr_anchor_energy_bound`, instantiated using class-derived stationary/subgradient witnesses. The coefficient becomes exactly `24*ell`; generic block contraction gives the printed arbitrary-`rho` consequence. The current `1/400` trajectory instance is separately packaged in `OuterTrajectoryConcrete`. |
| 1665 | `prop:warm-start` — proposition | Covered by `Upper.WithinRun.initialized_homotopy_snapshot`, `initializedSnapshot_energy`, and `finalCurvature_interval`, with the executed warm-program correspondence and geometric cost analysis. Both sides of the strict/non-strict curvature interval are present. |
| 1770 | `prop:function-class` — proposition | Covered by `Construction.Regularity.gradients_jointlySmooth`, `objective_dual_strongly_concave`, `Composite.value_differentiable`, and `BoundaryInactivity.restricted_value_and_gradient_identity`. The final identity uses the literal non-strict maximizer-feasibility condition, including its boundary. |
| 1835 | `prop:saddle-zero-chain` — proposition | Covered by `Construction.ZeroChain` and `Lower.Serialization.coordinateGradient_zeroChain` / `field_zeroChain`. The actual current coordinate ordering, not an unproved legacy identification, is used. |
| 1919 | `lem:phase-margins` — lemma | Covered by all three `Construction.Composite.phase_*` and `phase_*_fderiv` statements for the actual constrained value and current regularizer. |
| 2009 | `lem:bounded-connector` — lemma | Covered by `Construction.Frontier.small_unique_frontier`, `connector_norm_lt_twenty`, and `bounded_connector`. Includes uniqueness and the complete connector-vector bound, without assuming inactive constraints. |
| 2092 | `prop:terminal-gradient` — proposition | Covered by `Construction.Terminal.terminal_gradient_lower`; feasibility/inactivity follows from the actual connector/maximizer bounds. Numerical constants are independent of construction dimensions and diameter. |
| 2185 | `prop:initial-gap` — proposition | Covered by `Construction.Composite.value_origin`, `value_bddBelow`, and `initial_gap`, with the actual constrained value and dimension-linear constant. |
| 2252 | `lem:scaling` — lemma | Covered by generic positive-scale results in `ScaledObjective` (`scaledObjective_jointly_smooth`, `scaledValue_eq`, and the scalar/gradient scaling results), current `Lower.Serialization` support transport, and the current-instance assembly in `Lower.ScaledMembership` / `MoreauObstruction`. Generic scaling is not restricted to the accuracy-selected scale used in the final lower bound. |
| 2624 | `lem:startup-state` — lemma | Covered directly by `Upper.ExactStartup.startup_state_construction`: actual evaluated startup, coefficient **5**, genuine unregularized initial gap, and a universal true-query cap. The weaker budget 8 used later is not substituted for this statement. |
| 2654 | `lem:curvature-transfer` — lemma | Covered by `HomotopyConcrete.concrete_curvature_transfer` on the genuine constrained conjugate, with class-derived minimizers and the exact `27/4` coefficient. |
| 3198 | `lem:coupled-descent` — lemma | Covered by `OuterTrajectoryConcrete.one_step_outer_descent`, `one_step_potential_descent`, and their actual initialized trajectory realization in `Upper.WithinRun`. Both displayed descent inequalities are represented. |
| 3458 | `lem:observable-residual` — lemma | Covered directly by `Upper.ExactResidual.residual_comparison`, including both pointwise residual inequalities and the least-index output bound with the genuine envelope infimum. `evaluated_program_gradient_bound` connects it to execution. |
| 3871 | `lem:inner-interface` — lemma | Covered by `Construction.Inner`: ratio bounds, exact maximum/effective link, maximizer growth, strong concavity, Hessian bound, ordered zero-chain, both signs, and differentiability/radial bound for the true constrained multi-block maximum. All four clauses are present. |
| 4042 | `lem:gate-transformations` — lemma | Covered by `Construction.Scalar.p_contDiff`, `deriv_p_mem`, and `Scalar.Quantitative.p_second_derivative_mem`, for the literal integral-defined ramp. |
| 4252 | `lem:outer-gate` — lemma | Covered by `Construction.Scalar.q_contDiff`, plateau and range theorems, and `Scalar.Quantitative.q_derivative_mem` / `q_second_derivative_abs_le`, including `5/2` and `75/2`. |
| 4435 | `lem:identity-extensions` — lemma | Covered by the literal identity extensions in `Construction.Scalar` and their quantitative bounds. Includes both identity intervals, constant tails, value bounds, first-derivative interval, and second-derivative bound. |
| 4961 | `lem:app-feasible-rprox` — lemma | Covered by `Upper.WithinFirstStop.firstStopIndex_spec`, `firstStopIndex_le_universal`, `firstStopOracle_certificate`, and `program_correct`, together with the feasible projected program. The returned normal/residual certificate and actual terminating oracle count are proved. |

Two generality checks were made explicitly because the final main theorem
alone would not settle them. First, `ValidState Y` constrains only `yFast` to
lie in `Y`; the slow dual variable is unrestricted, exactly as stated at
source lines 1424–1426. Second, the arbitrary-state tracking and curvature
theorems use genuine conjugate minimizer/subgradient data supplied by the
current class-derived system; these are not unproved main-claim premises.

## Other verified conclusions

| Source lines | Label / identity | Verdict |
| --- | --- | --- |
| 708–715 | `rem:arbitrary-output` | Covered by `Deterministic.appendOutput` prefix preservation and `Lower.DeterministicLower.exists_current_hard_output` / `outputHorizon_lower`. It is not justified merely by ignoring the extra query. |
| 740–746 | Unlabelled matching-rate remark | Covered by `MainResults.source_matching_oracle_complexity`, using the same positive-dimensional minimax functional for both sides and the stated lower-bound regime. |
| 748–755 | NC-C gradient-stationarity extension | Covered by `Extensions.GSRate.nc_c_gs_complexity`: an actual queried distance-to-normal-cone stationarity witness and the stated accuracy-dependent query bound. |

## Definitions and certificate condition

Definitions specify the interpretation of the results; they are not seven
extra existential or analytic theorems. Their mathematical prerequisites
are handled by the class, Moreau, and oracle-model development.

| Source line | Label | Representation |
| ---: | --- | --- |
| 453 | `def:function-class` | `Model.Within` / `WithinConvexity`, and the positive-dimensional domain-labelled source class. |
| 481 | `def:stationary` | Actual constrained Moreau OS in `Moreau.Within`, with proximal/envelope existence and derivative theorems. |
| 529 | `def:first-order-oracle` | `Oracle.OracleReply` and `firstOrderOracle`, containing the actual value and both prescribed gradients. |
| 551 | `def:zero-respecting` | Actual-query support in `Oracle.Model`, transported by `Lower.Serialization`. |
| 571 | `def:deterministic-algorithm` | Domain-wise causal reply-history components, origin initialization, and the `UniformResisting.RawMaps` actual-run-preserving feasibility repair. |
| 591 | `def:complexity-algorithm-class` | `Oracle.PositiveDimension` and `Complexity.PositiveDimension`: source infimum/supremum ordering, zero-based actual OS hitting index, and infinity for non-hitting. |
| 609 | `def:saddle-zero-chain` | The generic support implication and current ordered field in `Construction.ZeroChain` / `Lower.Serialization`. |
| 838 | `cond:unscaled` — condition, not definition | All four asserted numerical certificates are discharged by the construction and assembled in `Lower.Membership`, `Certificates`, and `ScaledMembership`; they are not left as assumed hypotheses at the closed lower-bound endpoints. |

## Scope boundaries of this inventory

The unnumbered construction assertion at lines 1117–1119 concerning compactly
supported first derivatives is already explicitly recorded in the ledger
and proved in `Construction.Scalar.Support`. The conclusion's statement that
the hard instance is `C∞` is represented by
`Construction.Regularity.objective_contDiff`. Thus these two conspicuous
mathematical prose assertions do not hide extra missing standalone results.

The abstract, introduction, and conclusion restate the main complexity
claims and discuss their motivation; they do not add a fourth main theorem.
Algorithm boxes and equations define the routines, schedules, and quantities
used by the inventoried statements. Their implementation correspondences and
counts are already covered by the upper-analysis ledger. Source proof-internal
calculation steps were not reclassified as separate theorem statements.

Literature comparisons and proposed future randomized or higher-order
lower bounds are outside the formal theorem inventory. The correspondence
table concerns the statements and hypotheses explicitly identified above.
