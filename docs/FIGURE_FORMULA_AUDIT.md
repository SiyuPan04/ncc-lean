# Figures and displayed formulas

This document describes the four active figures in `main.tex` and their
relationship to the mathematical definitions. Source SHA-256:
`5E18D87B1636334EB8497027F97BD7FDF74CB985D005D95F6DB4280D25281872`.
The active source contains no table/tabular environments or external TeX
inputs containing additional tables. Figure and line references identify
the manuscript assets, which are separate from this Lean source repository.

The schematic is assessed as a visual illustration. The six scalar curves
are polylines specified by TikZ coordinate arrays; their numerical checks
are distinct from the formal proofs of the underlying analytic functions.

## Construction schematic

`main.tex:948-954` includes `ncc_chain_schematic.pdf`. The rendered left
panel has the actual stage order
`s_(i-1) -> a_i -> y_1^(i) -> ... -> y_N^(i) -> b_i -> s_i`,
with `s_0=1`, the stage ellipsis, and a final `s_M`. The color legend marks
both connector/state nodes as primal and inner-chain nodes as dual. This
matches the order at lines 937-946 and the caption at lines 951-952.

The right panel, reached by an arrow labelled `max_y`, suppresses the
inner coordinates and retains `a_i -> b_i -> s_i`. It is a **schematic
discovery-order illustration**, not a weighted dependency graph or a
claim that the constrained maximum globally equals the unconstrained
additive quadratic link. In particular, it does not depict the global
dual-ball coupling or state the feasibility condition needed for the
unconstrained value identity. No incorrect formula or coordinate label
was found in the graphic.

## Scalar curves: exact annotations and approximate drawings

All six scalar graphs use `plot coordinates`, so their rendered curves
are polylines through rounded numerical samples, not exact analytic
graphs. The checks used the actual source formulas at lines 1088-1109:

`p(t)=integral_0^t theta(v) dv` on `(0,1)`, with the two printed tails;
`theta(t)=exp(-1/t)/(exp(-1/t)+exp(-1/(1-t)))` on `(0,1)`;
`q(t)=theta((5t-1)/4)`; and
`e_s(t)=p(t+3)-p(t-2)-5/2`.

| Figure and source locations | Exact labels/annotations checked | Drawing status |
| --- | --- | --- |
| `p,p'`: 4049-4210; sample arrays 4064-4118 and 4142-4196 | `p(0)=0`, `p(1)=1/2`; the annotation `p(t)=t-1/2` for `t>=1`; `p'(0)=0`, `p'(1)=1`, and both tails. | 106 samples per curve. The non-affine segments are approximations; affine/constant tails and labelled endpoints are exact. |
| `q,q'`: 4264-4385; arrays 4271-4314 and 4328-4371 | The thresholds `1/5` and `1`; values 0 and 1; derivative zero at both thresholds; midpoint `3/5` and peak `q'(3/5)=5/2`. | 166 samples per curve. Exact tail levels and marked points; approximate transition polylines. |
| `e_s,e_s'`: 4451-4540; arrays 4463-4486 and 4504-4527 | Identity on `[-2,2]`; constant tails beginning at `-3,3`; levels `-5/2,5/2`; derivative 1 on `[-2,2]`, 0 on the outer tails, and the four marked derivative endpoints. | 87 samples per curve. Exact central/tail line segments and labelled endpoints; approximate transition polylines. |

The derivative peak annotation in the `q'` figure is stronger than merely
an upper bound, but is correct: `theta(1/2)=1/2` and
`theta'(1/2)=2`, so `q'(3/5)=(5/4)*2=5/2`. The global bound in the lemma
then confirms it is a maximum. None of the figures labels `75/2` as an
attained maximum of `|q''|`.

There is no separate `e_nu` graph. The text says explicitly that `e_s` is
the example (line 4449). Its thresholds `2,3` must not be read as the
`e_nu` thresholds `21,22`; the definitions and lemma give the latter
correctly, with tail magnitude `43/2`.

## Numerical sample check

All 718 stored points were evaluated independently using the exponential
formula and adaptive Simpson integration for `p`. These are numerical
checks, not interval-certified or Lean proofs of the sample tables.

| Curve | Maximum observed absolute sample error |
| --- | ---: |
| `p` | `9.81e-14` |
| `p'` | `5.00e-15` |
| `q` | `4.99e-11` |
| `q'` | `4.96e-11` |
| `e_s` | `4.99e-11` |
| `e_s'` | `4.99e-11` |

The ten-decimal `q` and extension arrays agree at ordinary rounding
precision. The `p` array prints fourteen decimals but contains a slightly
larger quadrature discrepancy than nearest rounding of its last decimal.
For example, line 4073 stores `p(0.14)=0.00003880323955`; an independent
45-digit decimal quadrature gives
`0.000038803239451925734963...`, a difference about `9.81e-14`.
The same check gives `p(0.5)=0.06888747413446359674487...`, versus the
stored `0.06888747413445`. This is negligible for the figure, but the
printed sample coordinates should not be characterized as exact values
or certified correctly rounded fourteen-decimal values.

Rounded samples may reach a tail level slightly before the true analytic
threshold (for example, `q` rounds to 1 before `t=1`). The axes and marked
thresholds correctly state the analytic plateau locations; the samples
are not evidence of an earlier exact plateau.

## Displayed algorithm notation

The active algorithms are located at lines 1712-1750, 4889-4906, and
4934-4959. The main algorithm returns the least-index minimum-Q
anchor, not the subsequent projected readout. Its `1/400` update, `24`
coefficient, and full state translation match the surrounding definitions.
The FOAM parameters `eta_omega=ell/2`, `eta_y=4/(alpha*ell)`, and
`alpha=sqrt(8r_y/ell)` match the displayed slow/fast recursion.

The projected micro loop is a repeat-until loop: the first update is
mandatory, which avoids requiring an undefined `b^0`. Its final gradient
reply, normal-vector scaling, and signs agree with the printed relative
proximal conditions. The formal algorithm correspondence is described in
[FINAL_FIDELITY_AUDIT.md](FINAL_FIDELITY_AUDIT.md). The diagrams and numerical
sample arrays themselves are not kernel-verified artifacts.
