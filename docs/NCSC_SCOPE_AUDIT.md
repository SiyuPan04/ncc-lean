# NC-SC initialization and query-obstruction theorems

The NC-SC class permits an unbounded dual domain and controls primal
initial gap rather than initial dual distance. This document distinguishes
three proved quantities: initial tracking energy, completion count of a
configured program, and earliest successful GS query.

For class definitions and the algorithm's explicit rate, see
[NCSC_EXTENSION.md](NCSC_EXTENSION.md). For stationarity predicates, see
[EXTENSION_REFERENCE_AUDIT.md](EXTENSION_REFERENCE_AUDIT.md).

## Finite observed initialization

With `L=8*(ell+mu)`, the observed origin budget is

`Bobs=6*(||gradX f(0,0)||²/(2*(L-ell))+||gradY f(0,0)||²/(2mu))`.

`NCSCInitialBudget.initial_energy_bound` bounds the actual conjugate
energy of the coincident zero state. A feasible origin query obtains the
data. The startup factor is

`beta=min(1/2,Delta/(2*max(1,Bobs)))`.

The normalization block is part of the program.
Its resulting energy is at most `Delta`, its visible budget is exactly
`Delta`, and its outer potential gap is at most `3Delta`.

For fixed numerical micro cutoff `N`, define

`C(rho)=(2*log(1/rho)+1)*(N+1)`.

The startup count is bounded by
`1+C(beta)*sqrt(L/mu)`. It is finite for every class member and independent
of target accuracy, but depends on the observed initial gradients.

## Translated quadratics and completion counts

`NCSCQuadraticClass.class_mem` places

`f(x,y)=-(y-c)²/2`

in `NCSCClass 1 1 1` on full spaces. Its primal value is constant and
its primal gap is zero. `observed_budget` gives exactly `3c²`.

`NCSCStartupLower.adapted_initProgram_exact_count` proves the actual
initializer completion count

`1+blockIterations(alpha(L,r),factor(Delta,Bobs))*(N+1)`.

`NCSCQuadraticStartup.quadratic_initializer_exact_count` specializes it to

`1+blockIterations(alpha(16,1),factor(1,3c²))*(N+1)`.

`no_uniform_run_completion_bound` proves that the same configured program,
with fixed accuracy and refinement factor, has no uniform completion cap
over this family. The initializer is an actual prefix of the full run.

This is a statement about that program's completion, not the first stationary
query and not all algorithms. Every primal point of this example is already
OS. The simpler `NCSCInitialization` lemmas separately describe its
unbounded dual distance and initial residual at fixed curvature.

## Zero-respecting queried-GS obstruction

`NCSCZeroChainObstruction` uses the full-space family

```text
f(x,y)=c*y[0]-(1/2)*yᵀ*(I+pathLaplacian)*y,
c=(5^(n+1)+1)*eps.
```

The quadratic matrix has uniform bounds between `I` and `5I`.
`fixed_conditioned_GS_obstruction` proves `NCSCClass 5 1 1` membership,
zero actual primal gap, and failure of normal-cone GS at every query
`t<n+1` of every zero-respecting deterministic component.

The proof derives terminal-coordinate support from actual oracle histories.
A weighted gradient identity shows that terminal-zero points have dual
gradient norm greater than `eps`.

## Arbitrary deterministic queried-GS obstruction

A rectangular dual projection alone need not preserve strong concavity.
`NCSCRotation` instead defines

`f_UV(x,y)=auxiliary(f,mu)(Uᵀx,Vᵀy)-mu*||y||²/2`.

This equals the projected objective with a quadratic penalty on the
orthogonal complement of the embedded dual subspace.
`class_rotate` proves class membership; `isGS_projects` shows that a
GS pair of the lift projects to a GS pair of the base problem.

`NCSCResisting` transforms replies by the known quadratic and proves
exact function-value and both-gradient correspondence for one fixed pair
of frames. It imposes no zero-respecting restriction on the original method.

`NCSCDeterministicObstruction.fixed_conditioned_arbitrary_deterministic`
states: for every positive `eps`, finite horizon `K`, and causal component
on dimensions `(K+3,2K+3)`, there exists a full-space instance in
`NCSCClass 98 1 1` with zero actual primal gap for which every query
`t<K` fails GS.

The method is chosen before the instance.
`positive_domainwise_no_finite_GS_cap` allows one method to be chosen on
all positive dimensions before `K`. Therefore no dimension-free finite
queried-GS cap depending only on `ell,mu,Delta,eps` is uniform over this
class. Dimensions and forcing increase with the selected horizon.

This theorem concerns deterministic queries. It is not a fixed-dimension,
randomized-method, unqueried-output, or OS obstruction. It does not identify
an optimal logarithmic dependence on initial distance.

## Rate parameters

The constructive bound in [NCSC_EXTENSION.md](NCSC_EXTENSION.md) retains
its observed startup term and final refinement term. For GS, the refinement
factor `mu/(1000000L)` contributes through `C(rho)`.
The leading accuracy-dependent term is proportional to
`ell*Delta*sqrt(ell/mu)/eps²`.

The explicit comparison with `sqrt(ell/mu)` assumes `mu<=ell`.
`NCSCConditioning` derives this on nonsingleton dual sets and isolates
the singleton exception. The analytic correctness predicates do not add
that conditioning assumption.
