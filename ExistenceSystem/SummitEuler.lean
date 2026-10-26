module

/-
SUMMIT EULER — the Euler product is what `ζ_K` has and the Epstein twin lacks (checked on coefficients).

All mathematics: Kari A Light. Grades nothing; claims no RH; proves no RH.

`SummitEpstein` shows that the principal-class Epstein zeta `Z₁` of `x² + 5y²` has exactly `ζ_K`'s
completed functional equation, so (given the cited Davenport–Heilbronn theorem) the functional
equation alone cannot force the zero line. Whatever does force it must use the Euler product. This
module machine-checks that discriminator at the level of Dirichlet coefficients.

* `coeffK = 1 ⍟ χ_{−20}`, `coeffK n = ∑_{d ∣ n} χ_{−20}(d)` (the ideal counts of `ℤ[√−5]`).
* `coeffGenus = χ_{−4} ⍟ χ₅`, `coeffGenus n = ∑_{ab = n} χ_{−4}(a) χ₅(b)`.
* `coeffEpstein n = (coeffK n + coeffGenus n) / 2`.

PROVED, gap-free (Mathlib's `LSeries_convolution'`, `LFunction_eq_LSeries`, `LSeries_one_eq_riemannZeta`,
`ArithmeticFunction.IsMultiplicative.mul`):

* on `1 < Re s`: `zetaProduct s = LSeries coeffK s`, `L(χ_{−4}) L(χ₅) = LSeries coeffGenus s`, and so
  `epsteinPrincipal s = LSeries coeffEpstein s`;
* `coeffK` and `coeffGenus` are multiplicative (convolutions of multiplicative functions);
* `coeffEpstein` is NOT multiplicative: `coeffEpstein 2 = 0`, `coeffEpstein 3 = 0`,
  `coeffEpstein 6 = 2`, and `0 · 0 ≠ 2` with `gcd(2,3) = 1`.

The packaging theorem `euler_product_discriminates` conjoins: `ζ_K`'s coefficients are
multiplicative, the Epstein twin's are not, and both have the same completed functional equation
(`epstein_same_functionalEquation_as_K`). This pins the ONLY structural difference that the
functional-equation no-go leaves available to a forcing argument. It does not prove RH, and it does
not show that multiplicativity suffices for the zero line.
-/

public import ExistenceSystem.SummitEpstein
public import Mathlib

@[expose] public section

noncomputable section

open Complex DirichletCharacter ZMod

open scoped Real LSeries.notation

open scoped Classical

namespace ExistenceSystem.Summit

open ExistenceSystem.TheThing

/-! ## The coefficients -/

/-- Dirichlet coefficients of `ζ_K = ζ · L(χ_{−20})`: `(1 ⍟ χ_{−20})(n) = ∑_{d ∣ n} χ_{−20}(d)`,
the ideal counts of `ℤ[√−5]`. -/
def coeffK : ℕ → ℂ := (1 : ℕ → ℂ) ⍟ (fun n : ℕ => χ_neg20ℂ (n : ZMod (Nat.lcm 4 5)))

/-- Dirichlet coefficients of `L(χ_{−4}) L(χ₅)`: `∑_{ab = n} χ_{−4}(a) χ₅(b)`. -/
def coeffGenus : ℕ → ℂ :=
  (fun n : ℕ => χ_neg4ℂ (n : ZMod 4)) ⍟ (fun n : ℕ => χ₅ℂ (n : ZMod 5))

/-- Dirichlet coefficients of the Epstein zeta of `x² + 5y²`: half the sum. -/
def coeffEpstein (n : ℕ) : ℂ := (coeffK n + coeffGenus n) / 2

lemma coeffK_apply (n : ℕ) :
    coeffK n = ∑ p ∈ n.divisorsAntidiagonal, (1 : ℂ) * χ_neg20ℂ (p.2 : ZMod (Nat.lcm 4 5)) := by
  simp [coeffK, LSeries.convolution_def]

lemma coeffGenus_apply (n : ℕ) :
    coeffGenus n = ∑ p ∈ n.divisorsAntidiagonal,
      χ_neg4ℂ (p.1 : ZMod 4) * χ₅ℂ (p.2 : ZMod 5) := by
  simp [coeffGenus, LSeries.convolution_def]

/-! ## Dirichlet-series identities on `1 < Re s` -/

lemma lseries_zetaProduct {s : ℂ} (hs : 1 < s.re) : zetaProduct s = LSeries coeffK s := by
  unfold zetaProduct coeffK
  rw [LSeries_convolution' (LSeriesSummable_one_iff.mpr hs)
    (DirichletCharacter.LSeriesSummable_of_one_lt_re _ hs),
    LSeries_one_eq_riemannZeta hs, DirichletCharacter.LFunction_eq_LSeries _ hs]

lemma lseries_genus {s : ℂ} (hs : 1 < s.re) :
    DirichletCharacter.LFunction χ_neg4ℂ s * DirichletCharacter.LFunction χ₅ℂ s =
      LSeries coeffGenus s := by
  unfold coeffGenus
  rw [LSeries_convolution' (DirichletCharacter.LSeriesSummable_of_one_lt_re _ hs)
    (DirichletCharacter.LSeriesSummable_of_one_lt_re _ hs),
    DirichletCharacter.LFunction_eq_LSeries _ hs, DirichletCharacter.LFunction_eq_LSeries _ hs]

lemma lseriesSummable_coeffK {s : ℂ} (hs : 1 < s.re) : LSeriesSummable coeffK s :=
  (LSeriesSummable_one_iff.mpr hs).convolution (DirichletCharacter.LSeriesSummable_of_one_lt_re _ hs)

lemma lseriesSummable_coeffGenus {s : ℂ} (hs : 1 < s.re) : LSeriesSummable coeffGenus s :=
  (DirichletCharacter.LSeriesSummable_of_one_lt_re _ hs).convolution
    (DirichletCharacter.LSeriesSummable_of_one_lt_re _ hs)

/-- `Z₁ = LSeries coeffEpstein` on `1 < Re s`. -/
theorem epsteinPrincipal_eq_lseries {s : ℂ} (hs : 1 < s.re) :
    epsteinPrincipal s = LSeries coeffEpstein s := by
  have hE : coeffEpstein = (2 : ℂ)⁻¹ • (coeffK + coeffGenus) := by
    funext n; simp [coeffEpstein, div_eq_inv_mul]
  rw [epsteinPrincipal, lseries_zetaProduct hs, lseries_genus hs, hE, LSeries_smul,
    LSeries_add (lseriesSummable_coeffK hs) (lseriesSummable_coeffGenus hs)]
  ring

/-! ## Multiplicativity -/

/-- The sequence `n ↦ 1` as an arithmetic function (zero at `0`). -/
def oneAF : ArithmeticFunction ℂ := toArithmeticFunction (1 : ℕ → ℂ)

/-- A Dirichlet character as an arithmetic function. -/
def charAF {N : ℕ} (χ : DirichletCharacter ℂ N) : ArithmeticFunction ℂ :=
  toArithmeticFunction (fun n : ℕ => χ (n : ZMod N))

lemma oneAF_isMultiplicative : oneAF.IsMultiplicative := by
  refine ArithmeticFunction.IsMultiplicative.iff_ne_zero.mpr ⟨?_, fun {m} {n} hm hn _ => ?_⟩
  · simp [oneAF, toArithmeticFunction]
  · simp [oneAF, toArithmeticFunction, hm, hn]

lemma charAF_isMultiplicative {N : ℕ} (χ : DirichletCharacter ℂ N) :
    (charAF χ).IsMultiplicative :=
  DirichletCharacter.isMultiplicative_toArithmeticFunction χ

/-- `coeffK` as an arithmetic function: `1 * χ_{−20}`. -/
def coeffKAF : ArithmeticFunction ℂ := oneAF * charAF χ_neg20ℂ

/-- `coeffGenus` as an arithmetic function: `χ_{−4} * χ₅`. -/
def coeffGenusAF : ArithmeticFunction ℂ := charAF χ_neg4ℂ * charAF χ₅ℂ

lemma coeffKAF_apply (n : ℕ) : coeffKAF n = coeffK n := by rfl

lemma coeffGenusAF_apply (n : ℕ) : coeffGenusAF n = coeffGenus n := by rfl

/-- `ζ_K`'s Dirichlet coefficients are multiplicative (the Euler product, at the level of
coefficients). -/
theorem coeffK_isMultiplicative : coeffKAF.IsMultiplicative :=
  oneAF_isMultiplicative.mul (charAF_isMultiplicative _)

/-- The genus `L`-function's coefficients are multiplicative. -/
theorem coeffGenus_isMultiplicative : coeffGenusAF.IsMultiplicative :=
  (charAF_isMultiplicative _).mul (charAF_isMultiplicative _)

/-- `coeffEpstein` as an arithmetic function (zero at `0`, as `coeffEpstein 0 = 0`). -/
def coeffEpsteinAF : ArithmeticFunction ℂ := toArithmeticFunction coeffEpstein

lemma coeffEpsteinAF_apply (n : ℕ) : coeffEpsteinAF n = coeffEpstein n := by
  by_cases hn : n = 0
  · subst hn; simp [coeffEpsteinAF, toArithmeticFunction, coeffEpstein, coeffK, coeffGenus]
  · simp [coeffEpsteinAF, toArithmeticFunction, hn]

/-! ## The values `coeffEpstein 2, 3, 6` -/

lemma neg4_1 : χ_neg4ℂ (1 : ZMod 4) = 1 := by
  rw [χ_neg4ℂ_apply]; have : ZMod.χ₄ (1 : ZMod 4) = 1 := by decide
  rw [this]; simp
lemma neg4_2 : χ_neg4ℂ (2 : ZMod 4) = 0 := by
  rw [χ_neg4ℂ_apply]; have : ZMod.χ₄ (2 : ZMod 4) = 0 := by decide
  rw [this]; simp
lemma neg4_3 : χ_neg4ℂ (3 : ZMod 4) = -1 := by
  rw [χ_neg4ℂ_apply]; have : ZMod.χ₄ (3 : ZMod 4) = -1 := by decide
  rw [this]; simp
lemma neg4_6 : χ_neg4ℂ (6 : ZMod 4) = 0 := by
  rw [χ_neg4ℂ_apply]; have : ZMod.χ₄ (6 : ZMod 4) = 0 := by decide
  rw [this]; simp

lemma five_1 : χ₅ℂ (1 : ZMod 5) = 1 := by
  rw [χ₅ℂ_apply]; have : χ₅ (1 : ZMod 5) = 1 := by decide
  rw [this]; simp
lemma five_2 : χ₅ℂ (2 : ZMod 5) = -1 := by
  rw [χ₅ℂ_apply]; have : χ₅ (2 : ZMod 5) = -1 := by decide
  rw [this]; simp
lemma five_3 : χ₅ℂ (3 : ZMod 5) = -1 := by
  rw [χ₅ℂ_apply]; have : χ₅ (3 : ZMod 5) = -1 := by decide
  rw [this]; simp
lemma five_6 : χ₅ℂ (6 : ZMod 5) = 1 := by
  rw [χ₅ℂ_apply]; have : χ₅ (6 : ZMod 5) = 1 := by decide
  rw [this]; simp

lemma neg20_1 : χ_neg20ℂ (1 : ZMod (Nat.lcm 4 5)) = 1 := by simp
lemma neg20_2 : χ_neg20ℂ (2 : ZMod (Nat.lcm 4 5)) = 0 := by
  have h := χ_neg20ℂ_eq_val 2
  rw [χ_neg20Val_2] at h
  simpa using h
lemma neg20_3 : χ_neg20ℂ (3 : ZMod (Nat.lcm 4 5)) = 1 := by
  have h := χ_neg20ℂ_eq_val 3
  rw [χ_neg20Val_3] at h
  simpa using h
lemma neg20_6 : χ_neg20ℂ (6 : ZMod (Nat.lcm 4 5)) = 0 := by
  have h := χ_neg20ℂ_eq_val 6
  rw [χ_neg20Val_6] at h
  simpa using h

lemma antidiag_2 : Nat.divisorsAntidiagonal 2 = {(1, 2), (2, 1)} := by decide
lemma antidiag_3 : Nat.divisorsAntidiagonal 3 = {(1, 3), (3, 1)} := by decide
lemma antidiag_6 : Nat.divisorsAntidiagonal 6 = {(1, 6), (2, 3), (3, 2), (6, 1)} := by decide

lemma coeffK_2 : coeffK 2 = 1 := by
  rw [coeffK_apply, antidiag_2]; simp [neg20_1, neg20_2]
lemma coeffK_3 : coeffK 3 = 2 := by
  rw [coeffK_apply, antidiag_3]; simp [neg20_1, neg20_3]; norm_num
lemma coeffK_6 : coeffK 6 = 2 := by
  rw [coeffK_apply, antidiag_6]; simp [neg20_1, neg20_2, neg20_3, neg20_6]; norm_num

lemma coeffGenus_2 : coeffGenus 2 = -1 := by
  rw [coeffGenus_apply, antidiag_2]; simp [neg4_1, neg4_2, five_1, five_2]
lemma coeffGenus_3 : coeffGenus 3 = -2 := by
  rw [coeffGenus_apply, antidiag_3]; simp [neg4_1, neg4_3, five_1, five_3]; norm_num
lemma coeffGenus_6 : coeffGenus 6 = 2 := by
  rw [coeffGenus_apply, antidiag_6]
  simp [neg4_1, neg4_2, neg4_3, neg4_6, five_1, five_2, five_3, five_6]; norm_num

lemma coeffEpstein_2 : coeffEpstein 2 = 0 := by
  simp [coeffEpstein, coeffK_2, coeffGenus_2]
lemma coeffEpstein_3 : coeffEpstein 3 = 0 := by
  simp [coeffEpstein, coeffK_3, coeffGenus_3]
lemma coeffEpstein_6 : coeffEpstein 6 = 2 := by
  simp [coeffEpstein, coeffK_6, coeffGenus_6]

/-- **The Epstein twin's coefficients are not multiplicative**: `gcd(2,3) = 1`, but
`coeffEpstein 6 = 2 ≠ 0 = coeffEpstein 2 · coeffEpstein 3`. So `Z₁` has no Euler product. -/
theorem coeffEpstein_not_isMultiplicative : ¬ coeffEpsteinAF.IsMultiplicative := by
  intro h
  have h6 := h.map_mul_of_coprime (show Nat.Coprime 2 3 by decide)
  rw [show (2 * 3 : ℕ) = 6 from rfl, coeffEpsteinAF_apply, coeffEpsteinAF_apply,
    coeffEpsteinAF_apply, coeffEpstein_6, coeffEpstein_2, coeffEpstein_3] at h6
  norm_num at h6

/-! ## The discriminator -/

/-- **The Euler product discriminates.** `ζ_K`'s Dirichlet coefficients are multiplicative; the
Epstein twin's are not; yet the two completed products satisfy the SAME functional equation
`Λ(1 − s) = 20^(s − 1/2) Λ(s)`. So the Euler product (multiplicativity of the coefficients) is the
one structural difference the functional-equation no-go leaves available to a forcing argument.
This does not prove RH and does not show that multiplicativity suffices for the zero line. -/
theorem euler_product_discriminates :
    coeffKAF.IsMultiplicative ∧ ¬ coeffEpsteinAF.IsMultiplicative ∧
      (∀ s : ℂ, completedProductK (1 - s) = (20 : ℂ) ^ (s - 1 / 2) * completedProductK s) ∧
      (∀ s : ℂ, completedEpstein (1 - s) = (20 : ℂ) ^ (s - 1 / 2) * completedEpstein s) ∧
      (∀ s : ℂ, 1 < s.re → zetaProduct s = LSeries coeffK s ∧
        epsteinPrincipal s = LSeries coeffEpstein s) :=
  ⟨coeffK_isMultiplicative, coeffEpstein_not_isMultiplicative, completedProductK_one_sub,
    completedEpstein_one_sub, fun _ hs => ⟨lseries_zetaProduct hs, epsteinPrincipal_eq_lseries hs⟩⟩

end ExistenceSystem.Summit

end

end
