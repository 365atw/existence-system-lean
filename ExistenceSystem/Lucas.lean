module

/-
Lucas numbers, shared by the Layer-0 modules and by KL18 / KL27.

Note L1061: "The fold of the two conjugate faces is an exact whole number,
φⁿ + σ(φ)ⁿ = Lₙ, the Lucas numbers [Lucas 1878]."
Reference [68] (L1407): "The identity φⁿ + σ(φ)ⁿ = Lₙ".

The map (G6, "B-LF") records that Mathlib has no Lucas numbers. This module is that
definition, `L₀ = 2`, `L₁ = 1`, `Lₙ₊₂ = Lₙ₊₁ + Lₙ`, and the identity over ℝ.
The coil reading `n = 3k` stays in KL18; it is not rebuilt here.
-/
public import Mathlib

@[expose] public section

open Real
open scoped goldenRatio

namespace ExistenceSystem.Lucas

/-- The Lucas numbers. Note L1061 / L1261. `L₀ = 2`, `L₁ = 1`, `Lₙ₊₂ = Lₙ₊₁ + Lₙ`. -/
def lucas : ℕ → ℤ
  | 0 => 2
  | 1 => 1
  | (n + 2) => lucas (n + 1) + lucas n

@[simp] theorem lucas_zero : lucas 0 = 2 := rfl
@[simp] theorem lucas_one : lucas 1 = 1 := rfl
theorem lucas_add_two (n : ℕ) : lucas (n + 2) = lucas (n + 1) + lucas n := rfl

/-- Note L1061 / B.5 L1261: `φⁿ + σ(φ)ⁿ = Lₙ` for every `n`.
Here `σ(φ) = ψ = Real.goldenConj`. -/
theorem goldenRatio_pow_add_goldenConj_pow (n : ℕ) :
    φ ^ n + ψ ^ n = (lucas n : ℝ) := by
  induction n using Nat.twoStepInduction with
  | zero => norm_num
  | one => norm_num
  | more n ih1 ih2 =>
    have eφ : φ ^ (n + 2) = φ ^ (n + 1) + φ ^ n := by
      have h : φ ^ (n + 2) = φ ^ n * φ ^ 2 := by ring
      rw [h, goldenRatio_sq]; ring
    have eψ : ψ ^ (n + 2) = ψ ^ (n + 1) + ψ ^ n := by
      have h : ψ ^ (n + 2) = ψ ^ n * ψ ^ 2 := by ring
      rw [h, goldenConj_sq]; ring
    have hl : (lucas (n + 2) : ℝ) = (lucas (n + 1) : ℝ) + (lucas n : ℝ) := by
      rw [lucas_add_two]; push_cast; ring
    rw [eφ, eψ, hl, ← ih1, ← ih2]; ring

end ExistenceSystem.Lucas

end
