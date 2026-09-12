# Stationarity conventions and primary references

This note identifies stationarity criteria used by the formalization and
related primary references. The external papers are reference material,
not Lean-verified dependencies.

## Normal-cone game stationarity

`GameStationarity.IsGS` requires a feasible pair satisfying

```text
dist(0, gradX f(x,y) + N_X(x)) <= eps
dist(0, -gradY f(x,y) + N_Y(y)) <= eps.
```

Distances are computed in Euclidean space. For closed convex sets, the
normal cone is the subdifferential of the indicator function.
`HasGSWitness.isGS` converts explicit feasible normal witnesses to this
distance criterion.

This is Definition 2.1(ii) in Li, Nagarajan, Pan, and Zhang,
*Smoothing Meets Perturbation: Unified and Tight Analysis for
Nonconvex-Concave Minimax Optimization*. Their Assumption 2.2 uses a
bounded convex dual set. [ArXiv v2, p.5](https://arxiv.org/pdf/2602.14185v2#page=5).

## Moreau optimization stationarity

For `Phi(x)=max_y f(x,y)`, the constrained proximal point minimizes
`Phi(u)+ell*||u-x||²` over `u ∈ X`.
The formal OS predicates require feasibility, positive accuracy, and

`||2ell*(x-prox(x))|| <= eps`.

`Moreau.Within.hasFDerivAt_envelope` and its NC-SC counterpart prove that
this vector represents the actual Moreau-envelope derivative.
The parameter-comparison theorem `NCSC.gradient_le_internal_residual`
compares proximal residuals at different coefficients; it is not a
raw-primal-gradient identity.

## Version-specific projected and primal criteria

Lin, Jin, and Jordan's COLT proceedings Definition 5 evaluates both
projected-gradient mappings at the same pair. ArXiv v6 Definition 3.5
instead uses a projected dual step before evaluating the primal mapping.
The formula as well as the numbering is version-specific.
[Proceedings, p.5](https://proceedings.mlr.press/v125/lin20a/lin20a.pdf#page=5);
[arXiv v6, p.7](https://arxiv.org/pdf/2002.02417v6#page=7).

ArXiv Definition A.1 measures the raw smooth primal gradient
`||grad Phi||`; Definition A.5 measures the Moreau-envelope gradient.
The proceedings counterparts are Definitions 14 and 18.
[ArXiv v6, pp.20–21](https://arxiv.org/pdf/2002.02417v6#page=20).

Zhang, Yang, Guzman, Kiyavash, and He also use raw-primal-gradient
stationarity in Definition 2.5 of *The Complexity of
Nonconvex-Strongly-Concave Minimax Optimization*.
[UAI proceedings, p.485](https://proceedings.mlr.press/v161/zhang21c/zhang21c.pdf#page=4).

These criteria are kept distinct in theorem statements. A quantitative
conversion must specify its output point, assumptions, tolerance change,
and any associated oracle calls.

## Formal endpoints

- `Extensions.GSRate.nc_c_gs_complexity`: queried normal-cone GS for the
  bounded-dual NC-C class.
- `Extensions.NCSCDomain.domainAlgorithm_queried_OS`: queried Moreau OS
  for the NC-SC class.
- `Extensions.NCSCGSUniform.algorithm_queried_isGS`: queried normal-cone
  GS for the NC-SC class.

The precise classes and counts are documented in [GS_UPPER.md](GS_UPPER.md)
and [NCSC_EXTENSION.md](NCSC_EXTENSION.md).
