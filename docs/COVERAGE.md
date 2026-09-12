# Current-paper verification ledger

Source: main.tex, SHA256
5E18D87B1636334EB8497027F97BD7FDF74CB985D005D95F6DB4280D25281872.

This ledger distinguishes a complete actual proof from a theorem
conditional on an assumed certificate. “Checked”
means that the current definitions and hypotheses are connected to a strict
Lean proof, not merely that a similarly named legacy theorem exists.
The latest whole-project audit is recorded in STATUS.md. New modules are
first checked individually and then included in that audit via NCC.lean.

## Main conclusions

| Source claim | Current status / endpoint |
| --- | --- |
| thm:zr-lower | Checked: Lower.ZeroRespecting.current_zeroRespecting_lower. Literal current objective, class, scaling, floors, actual query support and Moreau obstruction. |
| thm:deterministic | Checked: Lower.DeterministicLower and Complexity.PositiveDimension.oracleComplexity_lower. Exact current construction is permuted and rotated; no class, terminal or chain certificate is assumed. The final source minimax excludes zero dimensions. |
| thm:upper | Checked: Upper.Theorem.exists_domain_algorithm_uniform. The same objective-independent causal algorithm handles every known-domain class member. Adaptive queries, mandatory origin and output query are counted. Complexity.PositiveDimension.oracleComplexity_upper packages the exact source minimax rate. |
| Matching-rate remark | Checked: MainResults.source_matching_oracle_complexity. Both bounds use PositiveDimension.minimaxOracleComplexity, the exact positive-dimensional source infimum/supremum, and the actual source parameter regime. The older matching_oracle_complexity is retained for the enlarged zero-inclusive helper class. |
| rem:arbitrary-output | Checked: Deterministic.appendOutput proves prefix preservation; DeterministicLower.exists_current_hard_output and outputHorizon_lower give the current-parameter output lower bound. |
| Full lem:resisting-oracle | Checked: Lower.UniformResisting.finite_horizon_resisting_oracle. One domain-wise Z precedes all objectives and positive diameters; exact ambient dimensions m+T0,n+T0, positive base dual dimension as in the paper. |
| NC-C GS remark | Checked: Extensions.GSRate.nc_c_gs_complexity. Actual queried distance-to-normal-cone GS pair and a dimension/objective/accuracy-independent constant C(ell,D,Delta) giving C/(eps²sqrt eps) calls for 0<eps<=1. See docs/GS_UPPER.md. |

## Preliminaries and the oracle model

| Source definition / claim | Checked realization |
| --- | --- |
| def:function-class | Model.Within and WithinConvexity: prescribed derivatives within X×Y, arbitrary closed convex feasible sets, origin, diameter, weak convexity, attained dual maximum and finite initial gap. No ambient extension premise. |
| def:stationary / Moreau facts | Moreau.Within: actual proximal existence/uniqueness, envelope Frechet derivative, 2*ell gradient Lipschitz constant, exact feasible OS equivalence and initial 8*ell*Delta/3 squared-gradient bound. |
| def:first-order-oracle | Actual value/gradX/gradY replies at feasible queries. Model.Within supplies the derivative interpretation. |
| def:deterministic-algorithm | Domain-wise causal components depend only on known geometry/parameters and preceding replies; all-history feasibility and origin are enforced. The current source does not require measurability. |
| def:zero-respecting | Lower.Serialization and ZeroRespecting transport actual primal/dual gradient support through the explicit current permutation. |
| def:saddle-zero-chain | The one-step support implication for the actual ordered saddle field is represented in Construction.ZeroChain and Lower.Serialization; it is distinct from the algorithm's zero-respecting restriction. |
| def:complexity-algorithm-class | Oracle.PositiveDimension: the source's positive-dimensional domain union, infimum over source algorithms, supremum over domain-labelled instances, and extended-natural/real first hitting index. Exact actual-Moreau OS correspondence is proved. The older Oracle.Minimax permits zero dimensions and is only an enlarged helper. |
| lem:rotation-covariance | Lower.WithinRotation.class_rotate and gradient_covariance: actual class closure and Moreau-gradient/OS covariance for every source member on a full primal space and a dual ball, using only within-domain derivatives. No ambient derivative premise is added. |

## Exact construction and its four certificates

| TeX label | Checked realization |
| --- | --- |
| lem:inner-interface | Construction.Inner: exact matrix and H; all four clauses, including true constrained radial derivative, maximum Q, maximizer and growth, Hessian bound 6, strong concavity, zero-chain and signs. |
| lem:gate-transformations | Construction.Scalar and Scalar.Quantitative: literal integral p, C∞ and quantitative derivative bounds. |
| lem:outer-gate | Literal q=p'((5t-1)/4), plateaus and derivative bounds. |
| lem:identity-extensions | Literal e_s and e_nu, identity intervals, bounded values and derivatives. Scalar.Support additionally proves compact support and boundedness of all positive derivatives of q/e_s/e_nu. |
| eq:hard-instance | Construction.Outer and Composite: current C_en,C_ex,C_st,R, supremum-defined c_R and actual full stage sum. |
| prop:function-class | Construction.Regularity: actual joint derivative, dimension-independent smoothness and exact 1/N² dual strong concavity. Composite supplies constrained differentiability. BoundaryInactivity.restricted_value_and_gradient_identity proves value and gradient equality under the exact non-strict actual-maximizer norm condition, including the boundary. |
| prop:saddle-zero-chain | Construction.ZeroChain plus Lower.Serialization: actual signed gradient and exact (a,y...,b,s) order. |
| lem:phase-margins | Composite: actual current R and all three state-derivative cases. No old regularizer is substituted. |
| lem:bounded-connector | Frontier: actual gradient, unique high-to-low frontier, single outer active stage and dimension-free bound on the complete connector vector. |
| prop:terminal-gradient | Terminal: genuine constrained value, local inactivity proved from the connector bound, actual derivatives and contradiction. |
| prop:initial-gap | Composite: actual origin value zero and exact c_Delta*M bound. |
| cond:unscaled | All four concrete certificates discharged, assembled in Lower.Membership, Certificates and ScaledMembership. |
| lem:scaling | ScaledMembership and MoreauObstruction: actual scaled domains, class, gradients and terminal-zero non-OS. |
| Deterministic permutation | TaggedSource uses a genuine orthogonal block permutation from current (s,a,b) to legacy framework (a,b,s). The old tagged framework's index layout is not identified by casts alone. |

## Upper analysis and actual implementation

| TeX label / algorithm feature | Checked realization |
| --- | --- |
| lem:smoothing | WithinRegularization: feasible maxima, value bias, weak convexity, genuine prox and Moreau-gradient bias. |
| prop:foam-interface | WithinSystem, WithinFirstStop, AdaptiveMicroProgram and AdaptiveFOAMProgram: actual normal relations, real conjugate/state, first successful feasible residual test, contraction and actual query count. |
| prop:anchor-shift | Actual conjugate translation, optimizer movement and weighted energy bound via the checked analytic system. |
| lem:curvature-transfer | Actual regularized conjugate and minimizers, including the 27/4 energy-transfer coefficient. |
| lem:startup-state | ExactStartup.startup_state_construction: actual evaluated feasible startup, the source's sharp coefficient-5 bound using Phi(0)-inf_X Phi, and a universal true-query cap. The weaker coefficient-8 budget used in the upper run follows separately. |
| prop:warm-start | Actual geometric levels, retained states, 1/8 contractions, energy budgets and geometric total count. |
| lem:coupled-descent | WithinRun connects the genuine selected prox and actual state updates to the checked descent inequality. |
| lem:observable-residual | ExactResidual.residual_comparison: all three source inequalities on the actual initialized trajectory, including the selected-gradient bound with the genuine envelope infimum. evaluated_program_gradient_bound gives the same bound for the executed client. |
| Current horizon and reset | Exactly ceil(4000*(ell*Delta/eps²+1)) and reset 15*(Delta+r*D²). |
| Current output | Least-index minimizer of the current Q, not a different legacy observable. |
| lem:app-feasible-rprox | First positive successful test, universal finite cap, exact firstStopIndex+1 query count, and feasibility under every possible history. |
| Full oracle algorithm | Upper.Theorem constructs a geometry/parameter-only program, actual final query at N+1 and exact N+2 total calls including origin/output overhead. |
| Class generality | WithinSupport/Operator/System/Run/Program do not require a neighborhood C¹ representative or global gradient outside the feasible set. |

## Interpretation

Legacy sources are pinned, vendored dependencies. Compatibility-only changes
are documented in Legacy/README.md.
Reusing a theorem is accompanied by current-definition correspondence.

The main deterministic lower bound uses a checked fixed-instance
reduction. The uniform resisting lemma is independently
proved as well. RawMaps additionally proves that an objective-independent
origin repair preserves every feasible actual run of unrestricted causal
maps, so all-history feasibility is not an extra substantive restriction.

GS means the two normal-cone residuals, as in the cited smoothing paper.
A noncomputable exact saddle witness is not counted as a feasible oracle
algorithm. The GS rate is connected to an actual reply-driven program,
normal-residual output conversion and counted implementation.

Additional extension modules define a separate unbounded-dual class.
`Extensions.NCSCDomain.domainAlgorithm_queried_OS` and
`Extensions.NCSCGSUniform.algorithm_queried_isGS` prove objective-independent
algorithm guarantees with observed-gradient initialization and explicit
query counts. Their full hypotheses and initialization/refinement costs
are stated in the formal theorems.
