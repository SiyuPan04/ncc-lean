# NC-C game stationarity

The endpoint is `NCC.Extensions.GSRate.nc_c_gs_complexity`.
For fixed positive `ell`, `D`, and `Delta`, it gives a positive constant
`C`, independent of accuracy, dimension, domains and objective, such that
for every `0 < eps ≤ 1` one domain-wise deterministic first-order
algorithm reaches an actual queried pair satisfying `IsGS`, after at
most `C / (eps² * sqrt eps)` oracle calls.

`IsGS` is the actual distance-to-shifted-normal-cone criterion in
Euclidean space. The proof first constructs explicit normal witnesses,
then applies `HasGSWitness.isGS`. It does not replace game stationarity
by a projected-gradient mapping or by envelope stationarity alone.

## Actual algorithm

`GSProgram.fullProgram` receives only positive numerical parameters,
known domain projections, and the feasible initial point. It never
receives an objective, its class-membership proof, or a saddle witness.
Its gradient-dependent decisions and updates use local oracle replies.

1. Use the same startup and divide-by-four warm trajectory, stopping at
   the first curvature level reaching `min(ell/8, eps/(64D))`.
2. Reset the actual retained state budget to `15*(Delta+rD²)` and use
   the same translated tracked outer calls. The horizon is
   `ceil(4000*(ell*(Delta+rD²)/(eps/2)²+1))`.
3. Retain the complete least-index minimum-Q snapshot, not just its
   anchor. Its actual energy is bounded by its computable budget, and
   the budget is less than `eps²/(128ell)`.
4. Perform a genuine finite first-stop FOAM refinement at that anchor,
   with contraction factor `rho=r/(1000000ell)`.
5. Query the feasible fast pair once, then take one projected step for
   the regularized saddle operator. This yields the normal witnesses
   for the unregularized problem.

`GSTheorem` prepends the required origin query and appends a query at
the projected returned pair. On the actual class instance the returned
pair is already feasible, so the last query is exactly that GS pair.
It occurs at index `N+1`, where `N` is the actual adaptive full-client
trace length; the wrapper uses exactly `N+2` calls. Every hypothetical
reply history also produces feasible queries. Projection uniqueness
connects analytic projections to the domain-only algorithm constructor.

## Analytic and counted correspondence

`GSRun` proves the retained observable, budget and genuine envelope
gradient estimates for the arbitrary geometric level and mass-aware
horizon. Its final energy estimate concerns the actual FOAM iterate.
The feasible raw pair is within squared distance `2E/r` of the actual
regularized saddle pair; that saddle is used only inside the proof.

`ProjectedReadout` converts this proximity, the anchor displacement,
and the dual regularization bias into explicit original normal-cone
residuals. `GSProgram` proves evaluation correspondence for the entire
reply-driven client and this one-query readout.

The compositional count before the final readout is bounded by

`N_micro+1 + (2*C(1/8) + T*C(1/400) + C(rho))*sqrt(ell/r)`,

where `C(rho)=(2*log(1/rho)+1)*(N_micro+1)`. The readout and wrapper add
three calls. These are bounds on actual program trace lengths, not a
synthetic cost variable defined to equal the target rate.

For `eps≤1`, `GSRate` proves

`r ≥ min(ell/32,1/(256D))*eps`,

`T ≤ 4001*(4ell*(Delta+(ell/8)*D²)+1)/eps²`,

and `C(rho) ≤ 3*(N_micro+1)/rho`. Together with `GSCost`, these give
the explicit accuracy-independent constant and the
`eps^(-5/2)` bound, without a multiplying logarithm. This deliberately
loose bound displays only the accuracy dependence; it is not a claim
of optimal dependence on the other fixed class parameters.

The independently configured NC-SC algorithms are documented in
[NCSC_EXTENSION.md](NCSC_EXTENSION.md).
