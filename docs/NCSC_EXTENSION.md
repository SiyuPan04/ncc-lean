# NC-SC model, algorithms, and counted rates

The NC-SC modules implement fixed-curvature tracking on closed convex domains
with a possibly unbounded dual set. They provide actual Moreau OS and
normal-cone GS outputs, feasible reply-driven execution, and explicit
initialization and refinement costs.

## Function class

`NCC.Extensions.NCSC.NCSCClass ell mu Delta P` requires:

- positive `ell`, `mu`, and `Delta`;
- closed convex primal and dual sets containing the origin, with origin initialization;
- prescribed joint derivatives within the feasible product;
- joint Euclidean `ell`-smoothness;
- concavity of `f(x,y)+mu*||y||²/2` in the feasible dual variable;
- pointwise initial primal value gap at most `Delta`.

No dual diameter, compactness, attained maximum, global extension, or
solver-correctness certificate is a class field.
`NCSCConditioning.strongConcavity_le_smoothness` derives `mu<=ell` when
the dual set has two distinct points. `ell<mu` forces the dual set to be
the singleton origin.

## Analytic system

`NCSC.maximum_attained` derives dual attainment from strong-concavity
coercivity on the closed dual set. `NCSCMoreau` proves lower semicontinuity
and weak convexity of the actual maximum, constrained proximal existence
and uniqueness, and the full derivative of its Moreau envelope.
`NCSC.gradient_le_internal_residual` controls the
squared envelope gradient by four times the internal proximal residual.

The solver uses

`auxiliary.f(x,y)=f(x,y)+mu*||y||²/2`,
`L=8*(ell+mu)`, and `r=mu`.

Subtracting the intrinsic regularizer recovers the original objective and
its actual maximized value exactly. `NCSCAuxiliary` proves the derivative,
smoothness, and pointwise-conjugate finiteness properties without a
dual-diameter bound. `NCSCGeometry`, `NCSCOperator`, and `NCSCSystem`
derive the local variational inequality, stationary witnesses, conjugate
subgradients, and finite projected micro certificate.

## Reply-driven implementation

`NCSCProgram.adaptReply_true`, `eval_adaptProgram`, and
`queryTrace_adaptProgram` prove that adding the known quadratic to each
original-oracle reply simulates the auxiliary oracle exactly.
This arithmetic does not require extra oracle queries.

The intrinsic configuration uses the universal fixed micro cutoff.
It composes macro blocks, the tracked history, minimum-Q selection,
and a final refinement. This is a separately configured client from the
NC-C adaptive first-success implementation.

The program constructors use numerical data, known domain projections,
and oracle replies. Exact saddle witnesses occur only in proofs.

## Observed initialization

Let `gx=gradX f(0,0)` and `gy=gradY f(0,0)`.
`NCSCInitialBudget` proves the observable seed bound

`Bobs=6*(||gx||²/(2*(L-ell))+||gy||²/(2mu))`.

One origin query supplies this data.
`NCSCStartupProgram` chooses

`rho0=min(1/2,Delta/(2*max(1,Bobs)))`

and executes a contracting FOAM block.
`NCSCTheorem.initializer_energy`, `initializer_B`, `initializer_z`,
and `initializer_gap` prove true energy at most `Delta`, visible budget
exactly `Delta`, anchor zero, and outer potential gap at most `3Delta`.
Initialization is an executed, counted prefix.

## Correctness and total count

`NCSCTheorem.run_isOS` gives a feasible Moreau-OS anchor for every class
member and positive accuracy. Its theorem does not assume an initial energy
bound or a whole-run solver certificate.

Let `N` be the fixed numerical micro cutoff and

`C(rho)=(2*log(1/rho)+1)*(N+1)`.

For `0<mu<=ell` and `0<rho<1`, `NCSCTheorem.run_count` bounds the
actual original-oracle trace by

```text
1 + [C(rho0)+4001*C(1/400)+C(rho)]*sqrt(L/mu)
  + 256064*C(1/400)*ell*(3Delta)/eps²*sqrt(ell/mu).
```

For OS, `rho` can be fixed at `1/2`.
The final domainwise endpoint
`NCSCDomain.domainAlgorithm_queried_OS` charges two additional queries
for its origin/output wrapper.

`NCSCGSTheorem.run_hasGSWitness` and `run_isGS` use
`rho=mu/(1000000L)` and one projected readout query to obtain actual
normal-cone GS for the original objective.
`NCSCGSUniform.algorithm_queried_isGS` supplies the domain-only algorithm
and includes three extra calls: the readout and two wrapper queries.

Thus the accuracy-dependent term is a numerical multiple of
`ell*Delta*sqrt(ell/mu)/eps²`. The displayed total count also includes
the finite observed initialization and refinement terms. For fixed
instance and parameters these additive terms are independent of accuracy.

`NCSCUniform.run_same_domains` and `NCSCDomain.domainRun_matches`
prove the objective-independent program correspondence.
Algorithm uniformity does not make `Bobs` uniformly bounded over all
class members. See [NCSC_SCOPE_AUDIT.md](NCSC_SCOPE_AUDIT.md) for the
formal initialization examples and queried-GS obstruction.
