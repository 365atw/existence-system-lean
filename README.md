# existence-system-lean

Lean 4 + Mathlib formalisation of results from THE EXACT AND FREE SYSTEM — AN EXISTENCE SYNTHESIS.

All mathematics: Kari A Light.

## KL3 — the indifference theorem (`ExistenceSystem/KL3.lean`)

For `V(x) = -(r/2)x² + ¼x⁴` with `r > 0`, proved with no `sorry`, `admit`, or new axioms:

- `V_branches`: `V(√r) = V(-√r) = -r²/4`
- `critical_set`, `critical_set_ncard`: `V′` vanishes at exactly `0`, `√r`, `-√r`
- `minimizers_eq`, `minimizers_nontrivial`, `minimizers_ncard`: the minimizers of `V` over `ℝ` are exactly `√r` and `-√r`
- Supporting lemmas: `V_even` (`V(-x) = V(x)`), `hasDerivAt_V` / `deriv_V` (`V′(x) = -r x + x³`), `flow_eq_neg_deriv` (`r x - x³ = -V′(x)`)

Her words are quoted beside each statement with line numbers from the Note.
Only the mathematics of the potential is formalised; the prose concepts ("least-action drive", "provably indifferent", "exogenous", the cusp step of §3.3) are not encoded.

Build: `lake exe cache get && lake build` (Lean `v4.35.0-rc4`, Mathlib `v4.35.0-rc4`).
Axiom check: `lake env lean checks/PrintAxioms.lean` (standalone script, not part of the build target); every audited theorem depends only on `propext`, `Classical.choice`, `Quot.sound`. Logs in `logs/`.
