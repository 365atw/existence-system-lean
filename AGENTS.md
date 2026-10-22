# Project agent memory

This file is the project's committed home for project-intrinsic agent knowledge: build, test, release, architecture, and sharp-edge notes that should travel with the code.

- Build with `lake build`. Audit axioms with `lake env lean checks/PrintAxioms.lean`. The bar is only `propext`, `Classical.choice`, and `Quot.sound`. Output is in `logs/lake-build.log` and `logs/print-axioms.log`.
- What each statement encodes, and what is left as prose, is in `README.md` and the module headers under `ExistenceSystem/`. `KL13.residual` is the coil sequence for KL13 and KL14; `KL18.residual` stays the merged copy (see the KL13 header).
- Layer-0 shared modules are `Quadratic`, `Lucas`, `Icosahedral`, `IcosahedralRep`, `Landau`, and `EulerLagrange`. KL18 imports Lucas; KL27 imports Quadratic. Do not give the coil faces a second home inside ℚ(√5).

## Maintaining this file

Keep this file for knowledge useful to almost every future agent session in this project.
Do not repeat what the codebase already shows; point to the authoritative file or command instead.
Prefer rewriting or pruning existing entries over appending new ones.
When updating this file, preserve this bar for all agents and keep entries concise.
