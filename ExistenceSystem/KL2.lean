module

/-
KL2 — the obstruction, from THE EXACT AND FREE SYSTEM — AN EXISTENCE SYNTHESIS (§2.1).
All mathematics: Kari A Light.

Source: `THE-NOTE-EDITED.md` (194,868 bytes, 1,539 lines). Line numbers below refer to that file.
Her words are quoted exactly beside each statement. Nothing of hers is graded here.

§2.1: "an exact algebraic characterisation of phi = a construction in which phi is an exact root".
Such a construction carries the minimal polynomial `x² − x − 1`.

Note l.360: "any two exact algebraic characterisations of phi agree at phi by necessity -- a theorem about Q(sqrt5), not a coincidence."

Her field `ℚ(√5)` is `ExistenceSystem.Quadratic.K` (`QuadraticAlgebra ℚ 1 1`), the carrier KL27
uses. φ is its generator `ω` (`ω² = 1 + ω`); `Quadratic.embedPhi` sends `ω` to Mathlib's
`Real.goldenRatio`.

Reading (Note l.358): "`φ` has minimal polynomial `x² − x − 1` over `ℚ` (irreducible by Selmer's
irreducibility theorem (A3), or by inspection at `n = 2`)". The inspection route is the one
formalised here: degree 2, no rational root, reusing `Quadratic.no_rational_root`.

This file closes the two-exact-functionals question only. Free selection is not encoded.
-/

public import ExistenceSystem.Quadratic

@[expose] public section

noncomputable section

open Polynomial
open Real
open QuadraticAlgebra
open scoped QuadraticAlgebra goldenRatio

namespace ExistenceSystem.KL2

/-- Her field `ℚ(√5)`, the carrier `QuadraticAlgebra ℚ 1 1` from `ExistenceSystem.Quadratic`. -/
abbrev K := Quadratic.K

/-- The polynomial `X² - X - 1`. -/
private def chi : ℚ[X] := X ^ 2 - X - C 1

private lemma chi_eq : chi = X ^ 2 - X - 1 := by
  rw [chi, C_1]

private lemma chi_eq_sub : chi = X ^ 2 - (X + C 1) := by
  rw [chi]
  ring

private lemma natDegree_chi : chi.natDegree = 2 := by
  have hlt : natDegree (X + C (1 : ℚ)) < natDegree ((X : ℚ[X]) ^ 2) := by
    rw [natDegree_X_pow, natDegree_X_add_C]
    decide
  rw [chi_eq_sub, natDegree_sub_eq_left_of_natDegree_lt hlt, natDegree_X_pow]

private lemma monic_chi : chi.Monic := by
  rw [chi_eq_sub]
  refine monic_X_pow_sub ?_
  rw [degree_X_add_C]
  exact WithBot.coe_lt_coe.mpr (by decide : (1 : ℕ) < 2)

/-- `ω² = 1 + ω` in `ℚ(√5)`. -/
private lemma omega_sq : (ω : K) ^ 2 = 1 + ω := by
  simpa using (omega_pow_two_eq_add : (ω : K) ^ 2 = (1 : ℚ) • (1 : K) + (1 : ℚ) • ω)

/-- `ω` is an exact root of `x² − x − 1`. -/
private lemma aeval_chi_omega : aeval (ω : K) chi = 0 := by
  rw [chi, map_sub, map_sub, aeval_X_pow, aeval_X, aeval_C, omega_sq, map_one]
  ring

/-- By inspection at `n = 2` (Note l.358): `X² - X - 1` is irreducible over `ℚ`, because a
quadratic with no rational root is irreducible. There is no rational root, by
`Quadratic.no_rational_root`, the same fact that makes `ℚ(√5)` a field. -/
private lemma chi_irreducible : Irreducible chi := by
  refine irreducible_of_degree_le_three_of_not_isRoot ?_ ?_
  · rw [natDegree_chi]
    decide
  · intro r hr
    have hr0 : r ^ 2 - r - 1 = 0 := by
      simpa [IsRoot, chi, eval_sub, eval_pow, eval_X, eval_C] using hr
    exact Quadratic.no_rational_root r (by linarith)

/-- Note l.358: "`φ` has minimal polynomial `x² − x − 1` over `ℚ`". Stated in her field
`ℚ(√5)`, where φ is the generator `ω`. -/
theorem minpoly_omega : minpoly ℚ (ω : K) = X ^ 2 - X - 1 := by
  rw [← chi_eq]
  exact (minpoly.eq_of_irreducible_of_monic (x := (ω : K)) chi_irreducible aeval_chi_omega
    monic_chi).symm

/-- Note l.358, for Mathlib's golden ratio: `minpoly ℚ φ = X² - X - 1`. -/
theorem minpoly_phi : minpoly ℚ φ = X ^ 2 - X - 1 := by
  have hroot : aeval φ chi = 0 := by
    rw [chi, map_sub, map_sub, aeval_X_pow, aeval_X, aeval_C, goldenRatio_sq, map_one]
    ring
  rw [← chi_eq]
  exact (minpoly.eq_of_irreducible_of_monic (x := φ) chi_irreducible hroot monic_chi).symm

/-- §2.1: "an exact algebraic characterisation of phi = a construction in which phi is an exact root".

A polynomial over `ℚ` for which φ, carried as `ω` in `ℚ(√5)`, is an exact root. -/
def IsExactAlgebraicCharacterisation (p : ℚ[X]) : Prop :=
  aeval (ω : K) p = 0

/-- Note l.358: "Any construction in which `φ` is an exact root carries that factor." -/
theorem carries_minpoly (p : ℚ[X]) (hp : IsExactAlgebraicCharacterisation p) :
    X ^ 2 - X - 1 ∣ p := by
  rw [← minpoly_omega]
  exact minpoly.dvd ℚ (ω : K) hp

/-- A polynomial divisible by `x² − x − 1` vanishes at `ω`, because `ω` is a root of that factor. -/
private theorem aeval_omega_eq_zero_of_dvd (p : ℚ[X]) (hp : X ^ 2 - X - 1 ∣ p) :
    aeval (ω : K) p = 0 := by
  rw [← chi_eq] at hp
  obtain ⟨q, rfl⟩ := hp
  rw [map_mul, aeval_chi_omega, zero_mul]

/-- Note l.360: "any two exact algebraic characterisations of phi agree at phi by necessity -- a theorem about Q(sqrt5), not a coincidence."

Both carry `x² − x − 1`, and that polynomial vanishes at φ in `ℚ(√5)`, so the two constructions
take the same value there. -/
theorem agree (p q : ℚ[X]) (hp : IsExactAlgebraicCharacterisation p)
    (hq : IsExactAlgebraicCharacterisation q) : aeval (ω : K) p = aeval (ω : K) q :=
  (aeval_omega_eq_zero_of_dvd p (carries_minpoly p hp)).trans
    (aeval_omega_eq_zero_of_dvd q (carries_minpoly q hq)).symm

end ExistenceSystem.KL2

end
