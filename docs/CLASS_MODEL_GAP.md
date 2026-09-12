# Differentiation on closed feasible domains

The main class uses prescribed derivatives within the feasible product.
This permits closed convex sets with empty ambient interior and avoids
an assumption that the objective has a smooth extension to a neighborhood.

## Prescribed within derivative

`NCC.Model.RepresentsJointGradientWithin` requires

```lean
∀ x ∈ P.X, ∀ y ∈ P.Y,
  HasFDerivWithinAt (Function.uncurry P.f)
    (jointGradientCLM (P.gradX x y) (P.gradY x y))
    (P.X ×ˢ P.Y) (x, y)
```

Here `jointGradientCLM gx gy` acts by the Euclidean coordinate dot products.
The total function `P.f` is a representation convenience; the predicate
constrains only feasible approaches and does not impose off-domain behavior.

`WithinClass` adds positive parameters, origin initialization, closed convex
domains, bounded dual diameter, dual concavity, the pointwise primal gap,
and joint Euclidean smoothness:

`jointSq(gradX(q)-gradX(q'))(gradY(q)-gradY(q')) <= ell²*jointSq(q-q')`.

On a lower-dimensional domain, the ambient linear functional representing a
within derivative need not be unique. The supplied gradient remains part of
the oracle instance; it is not replaced by `fderivWithin`.
No `UniqueDiffOn` or nonempty ambient interior is assumed.

## Class-to-envelope results

| Module | Principal results |
| --- | --- |
| `Model.Within` | Joint feasible-domain continuity; compact-dual maximum attainment; continuity of the maximized value on the primal domain; proximal existence. |
| `Model.WithinConvexity` | Section derivatives, weak convexity with modulus `ell`, weak convexity of the actual maximum, and uniqueness of proximal minimizers. |
| `Model.FeasibleClass` | Derives compactness, attained maxima, finite lower bound, the infimum-form initial gap, and proximal existence from the class fields. |
| `Moreau.Within` | Actual proximal point and envelope; infimum identity; full envelope derivative; Euclidean gradient Lipschitz constant `2ell`; feasible OS equivalence; initial squared-gradient bound `8ell*Delta/3`. |

The convexity proofs restrict differentiation to feasible line segments.
The envelope has a full ambient derivative even though its defining objective
is differentiated only within the feasible set.

## Executable upper bound and rotation

`WithinSupport`, `WithinOperator`, `WithinSystem`, `WithinFirstStop`,
`WithinRun`, and `WithinProgram` use this class directly. Their analytic
hypotheses follow from feasible support inequalities and projection normals.
`Lower.WithinRotation` likewise proves class closure and Moreau covariance
using the within-domain chain rule.

The stronger neighborhood-C1 class is retained as a separate model.
`ConventionBridge.InClass.toWithin` maps it to `WithinClass`, preserving
the proximal point, envelope, gradient, and OS predicate. No converse
Whitney-extension theorem is assumed. The direct results above do not need one.

See [MODEL_SEMANTICS_AUDIT.md](MODEL_SEMANTICS_AUDIT.md) for norms, constrained
infima, and query conventions, and [WITHIN_UPPER.md](WITHIN_UPPER.md) for the
actual algorithm endpoint.
