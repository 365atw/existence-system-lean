# Project agent memory

This file is the project's committed home for project-intrinsic agent knowledge: build, test, release, architecture, and sharp-edge notes that should travel with the code.

- Build with `lake build`. Audit axioms with `checks/item-logs.sh` (one item argument records only that item). It runs `lake env lean checks/PrintAxioms.lean` and writes `logs/<Item>-build.log` and `logs/<Item>-print-axioms.log`. The bar is only `propext`, `Classical.choice`, and `Quot.sound`. See `logs/README`.
- What each statement encodes, and what is left as prose, is in `README.md` and the module headers under `ExistenceSystem/`. `KL13.residual` is the coil sequence for KL13 and KL14; `KL18.residual` stays the merged copy (see the KL13 header). `ExistenceSystem/KL10.lean` is Lemma 4 (Note L104 / L909); the statement is the one the Note marks known (A14/A18), and the header records the reading choice. `ExistenceSystem/TheThing.lean` is `K = ℚ(√−5)`; `ζ_K(s) = ζ(s)·L(s, χ_{−20})` is the named gap `dedekindZeta_factorization_gap`, not a theorem (it stays the `∀ s` proposition, the wrong quantifier). The summit chain is `ExistenceSystem/Summit.lean`, `SummitHalfPlane.lean` (proves `halfPlane`), and `SummitStrip.lean`: the top result `rh_one_piece_strip` is conditional only on `stripZeroFree` (equivalent to RH ∧ `dirichletZeroLine`).
- Layer-0 shared modules are `Quadratic`, `Lucas`, `Icosahedral`, `IcosahedralRep`, `Landau`, and `EulerLagrange`. KL18 imports Lucas; KL27 imports Quadratic. Do not give the coil faces a second home inside ℚ(√5).

## Maintaining this file

Keep this file for knowledge useful to almost every future agent session in this project.
Do not repeat what the codebase already shows; point to the authoritative file or command instead.
Prefer rewriting or pruning existing entries over appending new ones.
When updating this file, preserve this bar for all agents and keep entries concise.
