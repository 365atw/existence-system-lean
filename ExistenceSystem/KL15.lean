module

/-
KL15 — the identity case, from THE EXACT AND FREE SYSTEM — AN EXISTENCE SYNTHESIS.
All mathematics: Kari A Light.

Source: `THE-NOTE-EDITED.md` (194,868 bytes, 1,539 lines). Line numbers below refer to that file.
Her words are quoted exactly beside each statement. Nothing of hers is graded here.

Formalised here is only the trace identity `π_swap(m·φ) = m`. §7.3 supplies the reading: the pair is
`A = mφ`, `B = m·σ(φ) = m(1-φ)`, the fired pair is `(A-δ, B+δ)`, and the determinate reading is
the trace `A'+B'` (Note L1040). The identity does not depend on `δ`, so it holds at every coil.

Not encoded, by the map `data/lean-scope-b/G6.md` (KL15 point 5) and the captain's wording hold:
the claim that the trace is the *only* determinate reading past the four candidates of the §7.3
table; the units criterion ("mass-dimensioned"); the word *total* (ledger 2026-08-18 — nothing is
built on it); and `E = mc²` at the fixed point `r = 0`, which the Note joins at a definition
(§7.2) rather than as a theorem.
-/
public import Mathlib

@[expose] public section

open Real
open scoped goldenRatio

namespace ExistenceSystem.KL15

/-- The trace reading of `π_swap(m·φ)` supplied by §7.3 (Note L1040): `A' + B'`, with
`A = mφ`, `B = m(1-φ)`, `A' = A - δ`, `B' = B + δ`. -/
noncomputable def piSwapTrace (m δ : ℝ) : ℝ := (m * φ - δ) + (m * (1 - φ) + δ)

/-- Note line 114: "pi_swap(m . phi) = m as an algebraic identity at every coil (trace-only determinacy of section 7.3)." -/
theorem piSwap_eq_m (m δ : ℝ) : piSwapTrace m δ = m := by
  unfold piSwapTrace
  ring

end ExistenceSystem.KL15

end
