# Standalone analytic correspondence

This document records standalone conclusions that are useful independently
of the final complexity bounds. Their source baseline is `main.tex`,
SHA-256
`5E18D87B1636334EB8497027F97BD7FDF74CB985D005D95F6DB4280D25281872`.
See [COVERAGE.md](COVERAGE.md) for the complete endpoint ledger and
[STATUS.md](../STATUS.md) for verification scope.
Endpoint names below are in the `NCC` namespace.

## Rotation under within-domain derivatives

For the rotation lemma at `main.tex:642–654`,
`Lower.WithinRotation.class_rotate` applies to class members on the full
primal space and a dual ball, using only the prescribed within derivative.
It preserves the class parameters.
`gradient_covariance`, `gradient_norm_covariance`, and `isOS_covariance`
identify the actual Moreau derivative and stationarity under the embeddings.

The stronger global-derivative route in `Lower.Rotation` is a separate
theorem and is sufficient for the ambient-smooth hard construction.

## Dual maximizers on the boundary

`Construction.BoundaryInactivity.restricted_value_and_gradient_identity`
matches `main.tex:1776–1782` using the actual unconstrained maximizer
condition `||y*||<=D/2`,
including equality. It identifies the constrained and unconstrained values
and their derivatives by differentiable touching.

The terminal argument also uses the sufficient open condition
`8000*N²*||pulse||²<(D/2)²`. That condition is not substituted for the
boundary-inclusive standalone theorem.

## Exact initial and residual bounds

`Upper.ExactStartup.startup_state_construction` proves the bound in
`lem:startup-state` at `main.tex:2624`:

`energy<=5*(Phi(0)-inf_X Phi+3*r0*D²/2)`

for the actual evaluated adaptive startup state, together with a numerical
micro-query cap. The actual gap is nonnegative and the feasible value
infimum has a greatest-lower-bound certificate.

`Upper.ExactResidual.residual_comparison` supplies the pointwise residual
comparisons and selected-gradient estimate using the actual regularized
envelope infimum. `evaluated_program_gradient_bound` transfers that estimate
to the reply-driven client. Its `envelope_infimum` theorem certifies the
greatest lower bound of the nonempty, bounded-below envelope range.

## Quantitative details

- Scalar definitions use the integral smooth step and the specified
  identity extensions. Plateau endpoints and derivative bounds are explicit;
  an upper derivative bound is not automatically an attained maximum.
- The inner interface uses the literal quadratic chain, actual constrained
  finite-ball maximum, radial derivative, and Euclidean Hessian bound.
  The admissibility condition `N>=10` is stated explicitly.
- The uniform resisting simulator precedes all base objectives and has
  exact dimensions `m+K,n+K`.
- The upper client has first-success micro stopping, the complete
  slow/fast state, geometric warm levels, `1/400` tracked blocks,
  reset `15*(Delta+rD²)`, the specified outer ceiling, and least-index
  minimum-Q selection.
- The general block ceiling estimate retains the additive-one dependence
  near `rho=1`.
- Center translation, curvature transfer, coupled descent, and residual
  bounds use the actual conjugate system with coefficients
  `24`, `27/4`, `3/4`, `3`, `8`, and `32`.
- Hitting indices are zero based. The upper wrapper counts origin and output
  queries separately, and the arbitrary-output lower theorem reserves its
  additional query in the horizon arithmetic.

These are correspondences of explicitly stated, imported Lean results.
Numerical figure samples and external literature are not kernel-verified
artifacts; see [FIGURE_FORMULA_AUDIT.md](FIGURE_FORMULA_AUDIT.md) and
[EXTENSION_REFERENCE_AUDIT.md](EXTENSION_REFERENCE_AUDIT.md).
