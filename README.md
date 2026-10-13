# existence-system-lean

Lean 4 + Mathlib formalisation of results from THE EXACT AND FREE SYSTEM — AN EXISTENCE SYNTHESIS.

All mathematics: Kari A Light.

## KL3 — the indifference theorem (`ExistenceSystem/KL3.lean`)

For `V(x) = -(r/2)x² + ¼x⁴` with `r > 0`, proved with no `sorry`, `admit`, or new axioms:

- `V_branches`: `V(√r) = V(-√r) = -r²/4`
- `critical_set`, `critical_set_ncard`: `V′` vanishes at exactly `0`, `√r`, `-√r`
- `minimizers_eq`, `minimizers_nontrivial`, `minimizers_ncard`: the minimizers of `V` over `ℝ` are exactly `√r` and `-√r`

Her words are quoted beside each statement with line numbers from the Note.

Build: `lake exe cache get && lake build` (Lean `v4.35.0-rc4`, Mathlib `v4.35.0-rc4`).
Axiom check: `lake env lean checks/PrintAxioms.lean`. Logs in `logs/`.
