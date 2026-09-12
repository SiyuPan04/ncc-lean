# Sharp initial-state bound

`NCC.Upper.ExactStartup.startup_state_construction` gives the standalone
initial-state estimate

`energy <= 5*(Phi(0)-inf_X Phi+(3/2)*(ell/8)*D²)`.

It corresponds to `lem:startup-state` in the source baseline identified by
[paper-manifest.json](../paper-manifest.json).

The state is the evaluated `CurrentProgram.startupProgram` at the origin:
a first-success relative-prox micro call followed by a coincident slow/fast
reset. Its genuine first-order trace contains at most
`ProjectedMicro.feasibleMicroIterations+1` queries.
`startup_all_histories_feasible` proves feasibility after every reply history.

The estimate uses the actual gap, not a replacement by the class budget
`Delta`. The module establishes a greatest lower bound for the nonempty,
bounded-below feasible value range, nonnegativity of the actual gap, and the
exact-gap proximal-displacement estimate. It then instantiates the sharp
conclusion of `StartupConcrete.startup_pzr_computable_majorant`.

The coarser `WithinRun.startup_snapshot_energy` estimate is a separate
majorant used by the outer algorithm. Both estimates apply to the actual
constructed state; they serve different quantitative purposes.
