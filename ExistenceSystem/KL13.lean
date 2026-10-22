module

/-
KL13 — Positivity of the residual at every finite coil, from THE EXACT AND FREE SYSTEM —
AN EXISTENCE SYNTHESIS.
All mathematics: Kari A Light.

Source: `THE-NOTE-EDITED.md` (194,868 bytes, 1,539 lines). Line numbers below refer to that file.
Her words are quoted exactly beside each statement. Nothing of hers is graded here.

The coil law `r_{k+1} = φ^{-3} * r_k` is taken as given (captain's ruling; KL12 / §7.0).
The sequence below is that law. It is the same recursion `ExistenceSystem.KL18.residual` already
carries for the conjugate landing; it is defined here so this lemma does not depend on KL18,
which cites KL13.

The trailing clause of her list-form statement names KL12's *configuration*. That type is not
given in the Note (map `data/lean-scope-b/G6.md`, KL12 point 5 and KL13 point 5) and is not
encoded. The lemma formalised here is the positivity.
-/
public import Mathlib

@[expose] public section

open Real
open scoped goldenRatio

namespace ExistenceSystem.KL13

/-- The near-touch residual of the coil law, taken as given: `r_0` given and
`r_{k+1} = φ^{-3} * r_k`. -/
noncomputable def residual (r₀ : ℝ) : ℕ → ℝ
  | 0 => r₀
  | (k + 1) => (φ ^ 3)⁻¹ * residual r₀ k

/-- Note line 110: "r_0 > 0 and phi^{-3} > 0 give r_k > 0 for every finite k; no configuration is bound at any finite coil."

The positivity is the statement proved. "no configuration is bound at any finite coil" is her
clause for KL12's *configuration*, whose type the Note does not give; that type is not encoded. -/
theorem residual_pos (r₀ : ℝ) (hr : 0 < r₀) (hφ : 0 < (φ ^ 3)⁻¹) (k : ℕ) :
    0 < residual r₀ k := by
  induction k with
  | zero => simpa [residual] using hr
  | succ k ih => simpa [residual] using mul_pos hφ ih

end ExistenceSystem.KL13

end
