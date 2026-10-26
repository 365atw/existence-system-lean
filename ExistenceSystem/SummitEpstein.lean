module

/-
SUMMIT EPSTEIN — a function with exactly `ζ_K`'s completed functional equation that is NOT on the line.

All mathematics: Kari A Light. Grades nothing; claims no RH; proves no RH.

For `K = ℚ(√−5)` (class number 2) the Dedekind zeta factors `ζ_K = ζ · L(χ_{−20})` (`Summit`). The
principal-class partial zeta — the Epstein zeta of `x² + 5y²`, the norm form of `ℤ[√−5]` — is

    Z₁(s) = ½ [ ζ(s) L(s, χ_{−20}) + L(s, χ_{−4}) L(s, χ₅) ]

(`ζ_K` is the sum of the two class partial zetas, and their difference is the genus-character
`L`-function `L(χ_{−4}) L(χ₅)`; this decomposition is classical and recorded here in prose — the
module *defines* `epsteinPrincipal` by the displayed formula). `Z₁` has no Euler product and, by
Davenport–Heilbronn (1936), infinitely many zeros with `Re s > 1`. So a function with *exactly*
`ζ_K`'s completed functional equation can fail the zero line: the functional equation alone does not
force the zeros onto `Re = 1/2`. That is the no-go recorded here.

What is PROVED (all of it, gap-free, from Mathlib's functional equation for primitive Dirichlet
`L`-functions, `DirichletCharacter.IsPrimitive.completedLFunction_one_sub`):

* The characters `χ_{−4}`, `χ₅` over `ℂ` (`χ_neg4ℂ`, `χ₅ℂ`), their primitivity and parity.
* The three explicit Gauss sums over `ZMod 4`, `ZMod 5`, `ZMod (lcm 4 5) = ZMod 20` with Mathlib's
  `stdAddChar`: `g(χ_{−4}) = 2i`, `g(χ₅) = √5`, `g(χ_{−20}) = 2i√5`, hence all three root numbers are
  `1` (`rootNumber_χ_neg4ℂ`, `rootNumber_χ₅ℂ`, `rootNumber_χ_neg20ℂ`). The `√5` is
  `2cos(2π/5) − 2cos(4π/5)` with `cos(2π/5) = (√5 − 1)/4`; this is the carrier fact
  `2cos(2π/5) = 1/φ` of KL4 (`KL4.two_cos_eq_inv_goldenRatio`), re-derived here from
  `Real.cos_pi_div_five` so this module does not import KL4.
* The two completed products `completedProductK = Λ(ζ)·Λ(χ_{−20})` and
  `completedProductGenus = Λ(χ_{−4})·Λ(χ₅)` satisfy the SAME functional equation
  `Λ(1 − s) = 20^(s − 1/2) · Λ(s)` (conductors `1·20 = 4·5`, matching gamma factors, root numbers `1`),
  hence so does `completedEpstein = ½(Λ_K + Λ_genus)`.
* `completedEpstein s = Γℝ(s) Γℝ(s+1) · epsteinPrincipal s` for `0 < Re s`: `Z₁` really is the
  function whose completed form that is.

What is CARRIED (named, never proved, never an axiom, never a `sorry`): Davenport–Heilbronn's
theorem that `Z₁` has a zero with `Re s > 1` (`DavenportHeilbronnEpstein`). From it the adapter
`funEq_not_force_zeroLine` is proved: the same completed functional equation
as `ζ_K`, and a zero off `Re = 1/2`.

The summit chain and `stripZeroFree` are untouched; this is added alongside. The point of the no-go
is only that any proof of the zero line for `ζ_K` must use more than its functional equation — the
Euler product (equivalently, `ζ_K = ζ · L` as a product of two Euler products) is what `Z₁` lacks.
-/

public import ExistenceSystem.SummitStrip
public import Mathlib

@[expose] public section

noncomputable section

open Complex DirichletCharacter ZMod

open scoped Real

open scoped Classical

namespace ExistenceSystem.Summit

open ExistenceSystem.TheThing

/-! ## The characters `χ_{−4}` and `χ₅` over `ℂ` -/

/-- The odd character modulo `4`, over `ℂ`: Mathlib's `ZMod.χ₄` pushed along `ℤ → ℂ`. -/
def χ_neg4ℂ : DirichletCharacter ℂ 4 := ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)

/-- The even (Legendre) character modulo `5`, over `ℂ`. -/
def χ₅ℂ : DirichletCharacter ℂ 5 := χ₅.ringHomComp (Int.castRingHom ℂ)

lemma χ_neg4ℂ_apply (a : ZMod 4) : χ_neg4ℂ a = (ZMod.χ₄ a : ℂ) := by
  simp [χ_neg4ℂ, MulChar.ringHomComp_apply]

lemma χ₅ℂ_apply (a : ZMod 5) : χ₅ℂ a = (χ₅ a : ℂ) := by
  simp [χ₅ℂ, MulChar.ringHomComp_apply]

lemma χ_neg4ℂ_odd : χ_neg4ℂ.Odd := by
  rw [DirichletCharacter.Odd, χ_neg4ℂ_apply]
  have : ZMod.χ₄ (-1 : ZMod 4) = -1 := by decide
  rw [this]; norm_num

lemma χ₅ℂ_even : χ₅ℂ.Even := by
  rw [DirichletCharacter.Even, χ₅ℂ_apply]
  have : χ₅ (-1 : ZMod 5) = 1 := by decide
  rw [this]; norm_num

/-- A character that factors through level `d` agrees on integers (coprime to the modulus) that are
congruent mod `d`. -/
lemma eq_of_factorsThrough_cong {n d : ℕ} {χ : DirichletCharacter ℂ n} (h : χ.FactorsThrough d)
    {a b : ℤ} (ha : IsCoprime a (n : ℤ)) (hb : IsCoprime b (n : ℤ))
    (hab : (a : ZMod d) = (b : ZMod d)) : χ a = χ b := by
  obtain ⟨hd, χ₀, hχ⟩ := h
  rw [hχ, DirichletCharacter.changeLevel_eq_cast_of_dvd' χ₀ hd ha,
    DirichletCharacter.changeLevel_eq_cast_of_dvd' χ₀ hd hb, hab]

/-- `χ_{−4}` has conductor `4`. -/
theorem χ_neg4ℂ_isPrimitive : χ_neg4ℂ.IsPrimitive := by
  rw [DirichletCharacter.isPrimitive_def]
  have hdvd := χ_neg4ℂ.conductor_dvd_level
  have hft := χ_neg4ℂ.factorsThrough_conductor
  generalize χ_neg4ℂ.conductor = c at hdvd hft ⊢
  have hmem : c ∈ Nat.divisors 4 := Nat.mem_divisors.2 ⟨hdvd, by norm_num⟩
  have hd : Nat.divisors 4 = {1, 2, 4} := by decide
  rw [hd] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  have h3 : ZMod.χ₄ (((3:ℤ)) : ZMod 4) = -1 := by decide
  have h1 : ZMod.χ₄ (((1:ℤ)) : ZMod 4) = 1 := by decide
  rcases hmem with rfl | rfl | rfl
  · exfalso
    have := eq_of_factorsThrough_cong hft (a := 3) (b := 1)
      (by rw [Int.isCoprime_iff_gcd_eq_one]; decide) (by rw [Int.isCoprime_iff_gcd_eq_one]; decide)
      (Subsingleton.elim _ _)
    rw [χ_neg4ℂ_apply, χ_neg4ℂ_apply, h3, h1] at this
    norm_num at this
  · exfalso
    have := eq_of_factorsThrough_cong hft (a := 3) (b := 1)
      (by rw [Int.isCoprime_iff_gcd_eq_one]; decide) (by rw [Int.isCoprime_iff_gcd_eq_one]; decide)
      (by decide)
    rw [χ_neg4ℂ_apply, χ_neg4ℂ_apply, h3, h1] at this
    norm_num at this
  · rfl

/-- `χ₅` has conductor `5`. -/
theorem χ₅ℂ_isPrimitive : χ₅ℂ.IsPrimitive := by
  rw [DirichletCharacter.isPrimitive_def]
  have hdvd := χ₅ℂ.conductor_dvd_level
  have hft := χ₅ℂ.factorsThrough_conductor
  generalize χ₅ℂ.conductor = c at hdvd hft ⊢
  have hmem : c ∈ Nat.divisors 5 := Nat.mem_divisors.2 ⟨hdvd, by norm_num⟩
  have hd : Nat.divisors 5 = {1, 5} := by decide
  rw [hd] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with rfl | rfl
  · exfalso
    have := eq_of_factorsThrough_cong hft (a := 2) (b := 1)
      (by rw [Int.isCoprime_iff_gcd_eq_one]; decide) (by rw [Int.isCoprime_iff_gcd_eq_one]; decide)
      (Subsingleton.elim _ _)
    have h2 : χ₅ (((2:ℤ)) : ZMod 5) = -1 := by decide
    have h1 : χ₅ (((1:ℤ)) : ZMod 5) = 1 := by decide
    rw [χ₅ℂ_apply, χ₅ℂ_apply, h2, h1] at this
    norm_num at this
  · rfl

lemma χ_neg4ℂ_inv : χ_neg4ℂ⁻¹ = χ_neg4ℂ :=
  (ZMod.isQuadratic_χ₄.comp (Int.castRingHom ℂ)).inv

lemma χ₅ℂ_inv : χ₅ℂ⁻¹ = χ₅ℂ :=
  ((quadraticChar_isQuadratic (ZMod 5)).comp (Int.castRingHom ℂ)).inv

/-! ## The Gauss sums -/

/-- `g(χ_{−4}) = e(1/4) − e(3/4) = 2i`. -/
lemma gauss_χ_neg4ℂ : gaussSum χ_neg4ℂ stdAddChar = 2 * I := by
  unfold gaussSum
  change ∑ a : Fin 4, _ = _
  rw [Fin.sum_univ_four]
  have h0 : ((0 : Fin 4) : ZMod 4) = ((0:ℤ) : ZMod 4) := by decide
  have h1 : ((1 : Fin 4) : ZMod 4) = ((1:ℤ) : ZMod 4) := by decide
  have h2 : ((2 : Fin 4) : ZMod 4) = ((2:ℤ) : ZMod 4) := by decide
  have h3 : ((3 : Fin 4) : ZMod 4) = ((3:ℤ) : ZMod 4) := by decide
  rw [h0, h1, h2, h3]
  have c0 : ZMod.χ₄ ((0:ℤ) : ZMod 4) = 0 := by decide
  have c1 : ZMod.χ₄ ((1:ℤ) : ZMod 4) = 1 := by decide
  have c2 : ZMod.χ₄ ((2:ℤ) : ZMod 4) = 0 := by decide
  have c3 : ZMod.χ₄ ((3:ℤ) : ZMod 4) = -1 := by decide
  simp only [χ_neg4ℂ_apply, ZMod.stdAddChar_coe (N := 4), c0, c1, c2, c3]
  have e1 : Complex.exp (2 * π * I * ((1:ℤ):ℂ) / ((4:ℕ):ℂ)) = I := by
    rw [show (2 * π * I * ((1:ℤ):ℂ) / ((4:ℕ):ℂ) : ℂ) = (π / 2 : ℝ) * I by push_cast; ring,
      Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]; simp
  have e3 : Complex.exp (2 * π * I * ((3:ℤ):ℂ) / ((4:ℕ):ℂ)) = -I := by
    rw [show (2 * π * I * ((3:ℤ):ℂ) / ((4:ℕ):ℂ) : ℂ) = (3 * π / 2 : ℝ) * I by push_cast; ring,
      Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    have hc : Real.cos (3 * π / 2) = 0 := by
      rw [show 3 * π / 2 = π / 2 + π by ring, Real.cos_add_pi]; simp
    have hs : Real.sin (3 * π / 2) = -1 := by
      rw [show 3 * π / 2 = π / 2 + π by ring, Real.sin_add_pi]; simp
    rw [hc, hs]; simp
  rw [e1, e3]; simp; ring

/-- `cos(2π/5) = (√5 − 1)/4`; the carrier fact `2cos(2π/5) = 1/φ` of KL4, via `cos(π/5)`. -/
lemma cos_two_pi_div_five : Real.cos (2 * π / 5) = (Real.sqrt 5 - 1) / 4 := by
  rw [show (2 * π / 5 : ℝ) = 2 * (π / 5) by ring, Real.cos_two_mul, Real.cos_pi_div_five]
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  linear_combination (1 / 8 : ℝ) * h5

lemma cos_four_pi_div_five : Real.cos (4 * π / 5) = -((1 + Real.sqrt 5) / 4) := by
  rw [show (4 * π / 5 : ℝ) = π - π / 5 by ring, Real.cos_pi_sub, Real.cos_pi_div_five]

lemma stdAddChar_coe_cos_sin (N : ℕ) [NeZero N] (k : ℤ) : (stdAddChar (k : ZMod N) : ℂ) =
    ((Real.cos (2 * π * k / N) : ℝ) : ℂ) + ((Real.sin (2 * π * k / N) : ℝ) : ℂ) * I := by
  rw [ZMod.stdAddChar_coe, show (2 * π * I * k / N : ℂ) = ((2 * π * k / N : ℝ) : ℂ) * I by
    push_cast; ring, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

/-- `g(χ₅) = 2cos(2π/5) − 2cos(4π/5) = √5`. -/
lemma gauss_χ₅ℂ : gaussSum χ₅ℂ stdAddChar = (Real.sqrt 5 : ℝ) := by
  unfold gaussSum
  change ∑ a : Fin 5, _ = _
  rw [Fin.sum_univ_five]
  have h0 : ((0 : Fin 5) : ZMod 5) = ((0:ℤ) : ZMod 5) := by decide
  have h1 : ((1 : Fin 5) : ZMod 5) = ((1:ℤ) : ZMod 5) := by decide
  have h2 : ((2 : Fin 5) : ZMod 5) = ((2:ℤ) : ZMod 5) := by decide
  have h3 : ((3 : Fin 5) : ZMod 5) = ((3:ℤ) : ZMod 5) := by decide
  have h4 : ((4 : Fin 5) : ZMod 5) = ((4:ℤ) : ZMod 5) := by decide
  rw [h0, h1, h2, h3, h4]
  have c0 : χ₅ ((0:ℤ) : ZMod 5) = 0 := by decide
  have c1 : χ₅ ((1:ℤ) : ZMod 5) = 1 := by decide
  have c2 : χ₅ ((2:ℤ) : ZMod 5) = -1 := by decide
  have c3 : χ₅ ((3:ℤ) : ZMod 5) = -1 := by decide
  have c4 : χ₅ ((4:ℤ) : ZMod 5) = 1 := by decide
  simp only [χ₅ℂ_apply, stdAddChar_coe_cos_sin 5, c0, c1, c2, c3, c4]
  have a3 : Real.cos (2 * π * ((3:ℤ):ℝ) / ((5:ℕ):ℝ)) =
      Real.cos (2 * π * ((2:ℤ):ℝ) / ((5:ℕ):ℝ)) := by
    rw [← Real.cos_two_pi_sub]; congr 1; push_cast; ring
  have s3 : Real.sin (2 * π * ((3:ℤ):ℝ) / ((5:ℕ):ℝ)) =
      -Real.sin (2 * π * ((2:ℤ):ℝ) / ((5:ℕ):ℝ)) := by
    rw [← Real.sin_two_pi_sub]; congr 1; push_cast; ring
  have a4 : Real.cos (2 * π * ((4:ℤ):ℝ) / ((5:ℕ):ℝ)) =
      Real.cos (2 * π * ((1:ℤ):ℝ) / ((5:ℕ):ℝ)) := by
    rw [← Real.cos_two_pi_sub]; congr 1; push_cast; ring
  have s4 : Real.sin (2 * π * ((4:ℤ):ℝ) / ((5:ℕ):ℝ)) =
      -Real.sin (2 * π * ((1:ℤ):ℝ) / ((5:ℕ):ℝ)) := by
    rw [← Real.sin_two_pi_sub]; congr 1; push_cast; ring
  have k1 : Real.cos (2 * π * ((1:ℤ):ℝ) / ((5:ℕ):ℝ)) = (Real.sqrt 5 - 1) / 4 := by
    rw [← cos_two_pi_div_five]; congr 1; push_cast; ring
  have k2 : Real.cos (2 * π * ((2:ℤ):ℝ) / ((5:ℕ):ℝ)) = -((1 + Real.sqrt 5) / 4) := by
    rw [← cos_four_pi_div_five]; congr 1; push_cast; ring
  rw [a3, s3, a4, s4, k1, k2]
  push_cast
  ring

/-! ### `g(χ_{−20}) = 2i√5` over `ZMod (lcm 4 5) = ZMod 20` -/

lemma lcm_four_five_eq : Nat.lcm 4 5 = 20 := by decide

lemma sum_zmod_lcm (f : ZMod (Nat.lcm 4 5) → ℂ) :
    ∑ a : ZMod (Nat.lcm 4 5), f a =
      ∑ k ∈ Finset.range 20, f ((k : ℕ) : ZMod (Nat.lcm 4 5)) := by
  rw [← Fin.sum_univ_eq_sum_range (fun k => f ((k:ℕ) : ZMod (Nat.lcm 4 5))) 20]
  refine Fintype.sum_equiv (Equiv.refl _) _ _ (fun a => ?_)
  exact congrArg f (ZMod.natCast_zmod_val a).symm

lemma χ_neg20ℂ_intCast (k : ℤ) : χ_neg20ℂ (k : ZMod (Nat.lcm 4 5)) =
    ((ZMod.χ₄ (k : ZMod 4) * χ₅ (k : ZMod 5) : ℤ) : ℂ) := by
  rw [χ_neg20_int, χ_neg20_eq_mul]

/-- The value of `χ_{−20} = χ_{−4} χ₅` at a natural number, as an integer. -/
def χ_neg20Val (k : ℕ) : ℤ := ZMod.χ₄ (k : ZMod 4) * χ₅ (k : ZMod 5)

lemma χ_neg20ℂ_eq_val (k : ℕ) : χ_neg20ℂ (k : ZMod (Nat.lcm 4 5)) = (χ_neg20Val k : ℂ) := by
  have := χ_neg20ℂ_intCast (k : ℤ)
  simpa [χ_neg20Val] using this

lemma stdAddChar_lcm_natCast (k : ℕ) : (stdAddChar (k : ZMod (Nat.lcm 4 5)) : ℂ) =
    ((Real.cos (k * (π / 10)) : ℝ) : ℂ) + ((Real.sin (k * (π / 10)) : ℝ) : ℂ) * I := by
  have := ZMod.stdAddChar_coe (N := Nat.lcm 4 5) (k : ℤ)
  simp only [Int.cast_natCast] at this
  have h20 : ((Nat.lcm 4 5 : ℕ) : ℂ) = 20 := by rw [lcm_four_five_eq]; norm_num
  rw [this, h20, show (2 * π * I * k / 20 : ℂ) = ((k * (π / 10) : ℝ) : ℂ) * I by
    push_cast; ring, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

lemma χ_neg20Val_0 : χ_neg20Val 0 = 0 := by decide
lemma χ_neg20Val_1 : χ_neg20Val 1 = 1 := by decide
lemma χ_neg20Val_2 : χ_neg20Val 2 = 0 := by decide
lemma χ_neg20Val_3 : χ_neg20Val 3 = 1 := by decide
lemma χ_neg20Val_4 : χ_neg20Val 4 = 0 := by decide
lemma χ_neg20Val_5 : χ_neg20Val 5 = 0 := by decide
lemma χ_neg20Val_6 : χ_neg20Val 6 = 0 := by decide
lemma χ_neg20Val_7 : χ_neg20Val 7 = 1 := by decide
lemma χ_neg20Val_8 : χ_neg20Val 8 = 0 := by decide
lemma χ_neg20Val_9 : χ_neg20Val 9 = 1 := by decide
lemma χ_neg20Val_10 : χ_neg20Val 10 = 0 := by decide
lemma χ_neg20Val_11 : χ_neg20Val 11 = -1 := by decide
lemma χ_neg20Val_12 : χ_neg20Val 12 = 0 := by decide
lemma χ_neg20Val_13 : χ_neg20Val 13 = -1 := by decide
lemma χ_neg20Val_14 : χ_neg20Val 14 = 0 := by decide
lemma χ_neg20Val_15 : χ_neg20Val 15 = 0 := by decide
lemma χ_neg20Val_16 : χ_neg20Val 16 = 0 := by decide
lemma χ_neg20Val_17 : χ_neg20Val 17 = -1 := by decide
lemma χ_neg20Val_18 : χ_neg20Val 18 = 0 := by decide
lemma χ_neg20Val_19 : χ_neg20Val 19 = -1 := by decide

lemma sin_pi_div_ten : Real.sin (π / 10) = (Real.sqrt 5 - 1) / 4 := by
  rw [← Real.cos_pi_div_two_sub, show π / 2 - π / 10 = 2 * π / 5 by ring]
  exact cos_two_pi_div_five

lemma sin_three_pi_div_ten : Real.sin (3 * (π / 10)) = (1 + Real.sqrt 5) / 4 := by
  rw [← Real.cos_pi_div_two_sub, show π / 2 - 3 * (π / 10) = π / 5 by ring, Real.cos_pi_div_five]

/-- `g(χ_{−20}) = 2i √5`: the eight units mod `20` pair `k ↔ 20 − k` (oddness), and
`4(sin(π/10) + sin(3π/10)) = 2√5`. -/
lemma gauss_χ_neg20ℂ : gaussSum χ_neg20ℂ stdAddChar = 2 * I * (Real.sqrt 5 : ℝ) := by
  unfold gaussSum
  rw [sum_zmod_lcm]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, χ_neg20ℂ_eq_val,
    stdAddChar_lcm_natCast]
  simp only [χ_neg20Val_0, χ_neg20Val_1, χ_neg20Val_2, χ_neg20Val_3, χ_neg20Val_4, χ_neg20Val_5,
    χ_neg20Val_6, χ_neg20Val_7, χ_neg20Val_8, χ_neg20Val_9, χ_neg20Val_10, χ_neg20Val_11,
    χ_neg20Val_12, χ_neg20Val_13, χ_neg20Val_14, χ_neg20Val_15, χ_neg20Val_16, χ_neg20Val_17,
    χ_neg20Val_18, χ_neg20Val_19]
  simp only [Nat.cast_ofNat, Nat.cast_one, one_mul, Int.cast_zero, Int.cast_one, Int.cast_neg,
    zero_mul, zero_add, neg_mul]
  have c7 : Real.cos (7 * (π / 10)) = -Real.cos (3 * (π / 10)) := by
    rw [show 7 * (π / 10) = π - 3 * (π / 10) by ring, Real.cos_pi_sub]
  have s7 : Real.sin (7 * (π / 10)) = Real.sin (3 * (π / 10)) := by
    rw [show 7 * (π / 10) = π - 3 * (π / 10) by ring, Real.sin_pi_sub]
  have c9 : Real.cos (9 * (π / 10)) = -Real.cos (π / 10) := by
    rw [show 9 * (π / 10) = π - π / 10 by ring, Real.cos_pi_sub]
  have s9 : Real.sin (9 * (π / 10)) = Real.sin (π / 10) := by
    rw [show 9 * (π / 10) = π - π / 10 by ring, Real.sin_pi_sub]
  have c11 : Real.cos (11 * (π / 10)) = -Real.cos (π / 10) := by
    rw [show 11 * (π / 10) = π / 10 + π by ring, Real.cos_add_pi]
  have s11 : Real.sin (11 * (π / 10)) = -Real.sin (π / 10) := by
    rw [show 11 * (π / 10) = π / 10 + π by ring, Real.sin_add_pi]
  have c13 : Real.cos (13 * (π / 10)) = -Real.cos (3 * (π / 10)) := by
    rw [show 13 * (π / 10) = 3 * (π / 10) + π by ring, Real.cos_add_pi]
  have s13 : Real.sin (13 * (π / 10)) = -Real.sin (3 * (π / 10)) := by
    rw [show 13 * (π / 10) = 3 * (π / 10) + π by ring, Real.sin_add_pi]
  have c17 : Real.cos (17 * (π / 10)) = Real.cos (3 * (π / 10)) := by
    rw [show 17 * (π / 10) = 2 * π - 3 * (π / 10) by ring, Real.cos_two_pi_sub]
  have s17 : Real.sin (17 * (π / 10)) = -Real.sin (3 * (π / 10)) := by
    rw [show 17 * (π / 10) = 2 * π - 3 * (π / 10) by ring, Real.sin_two_pi_sub]
  have c19 : Real.cos (19 * (π / 10)) = Real.cos (π / 10) := by
    rw [show 19 * (π / 10) = 2 * π - π / 10 by ring, Real.cos_two_pi_sub]
  have s19 : Real.sin (19 * (π / 10)) = -Real.sin (π / 10) := by
    rw [show 19 * (π / 10) = 2 * π - π / 10 by ring, Real.sin_two_pi_sub]
  rw [c7, s7, c9, s9, c11, s11, c13, s13, c17, s17, c19, s19, sin_pi_div_ten,
    sin_three_pi_div_ten]
  push_cast
  ring

/-! ## The root numbers are all `1` -/

lemma natCast_cpow_half (N : ℕ) : ((N : ℕ) : ℂ) ^ (1 / 2 : ℂ) = ((Real.sqrt N : ℝ) : ℂ) := by
  have h := Complex.ofReal_cpow (Nat.cast_nonneg N : (0:ℝ) ≤ N) (1 / 2 : ℝ)
  rw [Real.sqrt_eq_rpow]
  push_cast at h ⊢
  exact h.symm

lemma sqrt_natCast_four : Real.sqrt ((4 : ℕ) : ℝ) = 2 := by
  rw [show ((4 : ℕ) : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

lemma sqrt_natCast_lcm : Real.sqrt ((Nat.lcm 4 5 : ℕ) : ℝ) = 2 * Real.sqrt 5 := by
  rw [lcm_four_five_eq, show ((20 : ℕ) : ℝ) = 2 ^ 2 * 5 by norm_num,
    Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]

lemma sqrt_five_pos : 0 < Real.sqrt 5 := Real.sqrt_pos.2 (by norm_num)

/-- `rootNumber χ_{−4} = 2i / i / 2 = 1`. -/
theorem rootNumber_χ_neg4ℂ : rootNumber χ_neg4ℂ = 1 := by
  unfold rootNumber
  rw [natCast_cpow_half]
  simp only [χ_neg4ℂ_odd.not_even, ↓reduceIte]
  rw [gauss_χ_neg4ℂ, sqrt_natCast_four]
  push_cast
  field_simp

/-- `rootNumber χ₅ = √5 / √5 = 1`. -/
theorem rootNumber_χ₅ℂ : rootNumber χ₅ℂ = 1 := by
  unfold rootNumber
  rw [natCast_cpow_half]
  simp only [χ₅ℂ_even, ↓reduceIte]
  rw [gauss_χ₅ℂ]
  have h5 : ((Real.sqrt 5 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast sqrt_five_pos.ne'
  push_cast
  field_simp

/-- `rootNumber χ_{−20} = 2i√5 / i / (2√5) = 1`. -/
theorem rootNumber_χ_neg20ℂ : rootNumber χ_neg20ℂ = 1 := by
  unfold rootNumber
  rw [natCast_cpow_half]
  simp only [χ_neg20ℂ_odd.not_even, ↓reduceIte]
  rw [gauss_χ_neg20ℂ, sqrt_natCast_lcm]
  have h5 : ((Real.sqrt 5 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast sqrt_five_pos.ne'
  push_cast
  field_simp

/-- The product identity the functional equation needs:
`rootNumber χ_{−4} · rootNumber χ₅ = rootNumber χ_{−20}`. -/
theorem rootNumber_mul : rootNumber χ_neg4ℂ * rootNumber χ₅ℂ = rootNumber χ_neg20ℂ := by
  rw [rootNumber_χ_neg4ℂ, rootNumber_χ₅ℂ, rootNumber_χ_neg20ℂ, mul_one]

/-! ## The completed products and their common functional equation

Mathlib's normalisation: for a primitive `χ` mod `N`,
`Λ(χ, 1 − s) = N^(s − 1/2) · rootNumber χ · Λ(χ⁻¹, s)`, and for the trivial character mod `1`,
`Λ = completedRiemannZeta`, with `Λ(1 − s) = Λ(s)`. Here `Λ(χ) := completedLFunction χ`
(`= L(χ, s) · Γℝ(s)` for even `χ`, `L(χ, s) · Γℝ(s+1)` for odd `χ`). The exponent that comes out
is `20^(s − 1/2)`, the conductor `20 = disc ℚ(√−5)` in absolute value. -/

/-- `Λ_K(s) = Λ(ζ, s) · Λ(χ_{−20}, s)`: the completed `ζ(s) L(s, χ_{−20})` (the completed `ζ_K`). -/
def completedProductK (s : ℂ) : ℂ :=
  completedRiemannZeta s * DirichletCharacter.completedLFunction χ_neg20ℂ s

/-- `Λ_genus(s) = Λ(χ_{−4}, s) · Λ(χ₅, s)`: the completed genus-character product
`L(s, χ_{−4}) L(s, χ₅)`. -/
def completedProductGenus (s : ℂ) : ℂ :=
  DirichletCharacter.completedLFunction χ_neg4ℂ s * DirichletCharacter.completedLFunction χ₅ℂ s

/-- `Λ_Z₁ = ½(Λ_K + Λ_genus)`: the completed principal-class (Epstein) zeta. -/
def completedEpstein (s : ℂ) : ℂ := (completedProductK s + completedProductGenus s) / 2

lemma natCast_lcm_complex : ((Nat.lcm 4 5 : ℕ) : ℂ) = 20 := by
  rw [lcm_four_five_eq]; norm_num

/-- **`ζ_K`'s functional equation:** `Λ_K(1 − s) = 20^(s − 1/2) · Λ_K(s)`. -/
theorem completedProductK_one_sub (s : ℂ) :
    completedProductK (1 - s) = (20 : ℂ) ^ (s - 1 / 2) * completedProductK s := by
  unfold completedProductK
  rw [completedRiemannZeta_one_sub,
    χ_neg20ℂ_isPrimitive.completedLFunction_one_sub s, rootNumber_χ_neg20ℂ, χ_neg20ℂ_inv,
    natCast_lcm_complex]
  ring

/-- **The genus product has the same functional equation:**
`Λ_genus(1 − s) = 20^(s − 1/2) · Λ_genus(s)`, since `4^(s − 1/2) · 5^(s − 1/2) = 20^(s − 1/2)`. -/
theorem completedProductGenus_one_sub (s : ℂ) :
    completedProductGenus (1 - s) = (20 : ℂ) ^ (s - 1 / 2) * completedProductGenus s := by
  unfold completedProductGenus
  rw [χ_neg4ℂ_isPrimitive.completedLFunction_one_sub s,
    χ₅ℂ_isPrimitive.completedLFunction_one_sub s, rootNumber_χ_neg4ℂ, rootNumber_χ₅ℂ,
    χ_neg4ℂ_inv, χ₅ℂ_inv]
  have h : (20 : ℂ) ^ (s - 1 / 2) = ((4 : ℕ) : ℂ) ^ (s - 1 / 2) * ((5 : ℕ) : ℂ) ^ (s - 1 / 2) := by
    have := Complex.mul_cpow_ofReal_nonneg (a := 4) (b := 5) (by norm_num) (by norm_num)
      (s - 1 / 2)
    push_cast at this ⊢
    rw [← this]; norm_num
  rw [h]
  ring

/-- **The Epstein completed form obeys exactly `ζ_K`'s functional equation:** both `Λ_K` and `Λ_Z₁`
satisfy `Λ(1 − s) = 20^(s − 1/2) · Λ(s)`. -/
theorem completedEpstein_one_sub (s : ℂ) :
    completedEpstein (1 - s) = (20 : ℂ) ^ (s - 1 / 2) * completedEpstein s := by
  unfold completedEpstein
  rw [completedProductK_one_sub, completedProductGenus_one_sub]
  ring

/-- `ζ_K` and `Z₁` share the one completed functional equation. -/
theorem epstein_same_functionalEquation_as_K (s : ℂ) :
    completedProductK (1 - s) = (20 : ℂ) ^ (s - 1 / 2) * completedProductK s ∧
      completedEpstein (1 - s) = (20 : ℂ) ^ (s - 1 / 2) * completedEpstein s :=
  ⟨completedProductK_one_sub s, completedEpstein_one_sub s⟩

/-! ## `Z₁` is the function whose completed form that is -/

/-- The principal-class (Epstein) zeta of `x² + 5y²`, written as
`½ [ζ(s) L(s, χ_{−20}) + L(s, χ_{−4}) L(s, χ₅)]`. It has no Euler product. -/
def epsteinPrincipal (s : ℂ) : ℂ :=
  (zetaProduct s + DirichletCharacter.LFunction χ_neg4ℂ s * DirichletCharacter.LFunction χ₅ℂ s) / 2

lemma completedRiemannZeta_eq_mul {s : ℂ} (hs : 0 < s.re) :
    completedRiemannZeta s = riemannZeta s * Gammaℝ s := by
  rw [riemannZeta_def_of_ne_zero (fun h => by simp [h] at hs)]
  field_simp [Gammaℝ_ne_zero_of_re_pos hs]

lemma completedLFunction_eq_mul {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hs : 0 < s.re) :
    DirichletCharacter.completedLFunction χ s =
      DirichletCharacter.LFunction χ s * DirichletCharacter.gammaFactor χ s := by
  have hne : DirichletCharacter.gammaFactor χ s ≠ 0 := by
    rcases χ.even_or_odd with h | h
    · rw [h.gammaFactor_def]; exact Gammaℝ_ne_zero_of_re_pos hs
    · rw [h.gammaFactor_def]
      exact Gammaℝ_ne_zero_of_re_pos (by simp; linarith)
  rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ s
    (Or.inl (fun h => by simp [h] at hs))]
  field_simp

/-- For `0 < Re s`, the completed Epstein zeta is `Γℝ(s) Γℝ(s + 1)` times `epsteinPrincipal`:
both summands carry the same gamma factor (`ζ`: `Γℝ(s)`, `χ_{−20}`: `Γℝ(s+1)`; `χ₅`: `Γℝ(s)`,
`χ_{−4}`: `Γℝ(s+1)`). -/
theorem completedEpstein_eq_gamma_mul {s : ℂ} (hs : 0 < s.re) :
    completedEpstein s = Gammaℝ s * Gammaℝ (s + 1) * epsteinPrincipal s := by
  unfold completedEpstein completedProductK completedProductGenus epsteinPrincipal zetaProduct
  rw [completedRiemannZeta_eq_mul hs, completedLFunction_eq_mul χ_neg20ℂ hs,
    completedLFunction_eq_mul χ_neg4ℂ hs, completedLFunction_eq_mul χ₅ℂ hs,
    χ_neg20ℂ_odd.gammaFactor_def, χ_neg4ℂ_odd.gammaFactor_def, χ₅ℂ_even.gammaFactor_def]
  ring

/-! ## The no-go: the functional equation does not force the zero line

Davenport–Heilbronn (1936), "On the zeros of certain Dirichlet series" (J. London Math. Soc.): the
Epstein zeta function of the binary quadratic form `x² + 5y²` (a form of class-number-2 field
discriminant `−20`) has infinitely many zeros in `Re s > 1`. It is the cited prior art; the analytic
input (almost-periodicity of a Dirichlet series with no Euler product in its half plane of absolute
convergence) is not in Mathlib. It is carried as a named `Prop`, never
proved, never an axiom. We state only the one consequence needed (a single zero). -/

/-- **Davenport–Heilbronn (cited, not proved).** The principal-class (Epstein) zeta of `x² + 5y²`
has a zero with `Re s > 1`. -/
def DavenportHeilbronnEpstein : Prop :=
  ∃ s : ℂ, 1 < s.re ∧ epsteinPrincipal s = 0

/-- **The no-go adapter.** Given Davenport–Heilbronn for `x² + 5y²`, there is a function — the
completed Epstein zeta — that satisfies *exactly* `ζ_K`'s completed functional equation
`Λ(1 − s) = 20^(s − 1/2) Λ(s)` (with `Λ_K` itself obeying the same law) and still has a zero off
`Re = 1/2`. So the functional equation alone cannot force the zero line: any proof for `ζ_K` must
use the Euler product (equivalently, the factorisation `ζ_K = ζ · L`) that `Z₁` lacks. -/
theorem funEq_not_force_zeroLine (h : DavenportHeilbronnEpstein) :
    ∃ F : ℂ → ℂ,
      (∀ s, F (1 - s) = (20 : ℂ) ^ (s - 1 / 2) * F s) ∧
      (∀ s, completedProductK (1 - s) = (20 : ℂ) ^ (s - 1 / 2) * completedProductK s) ∧
      ∃ s : ℂ, F s = 0 ∧ s.re ≠ 1 / 2 ∧ 1 < s.re ∧ epsteinPrincipal s = 0 := by
  obtain ⟨s, hs, hz⟩ := h
  refine ⟨completedEpstein, completedEpstein_one_sub, completedProductK_one_sub,
    s, ?_, (show (1 / 2 : ℝ) < s.re by linarith).ne', hs, hz⟩
  rw [completedEpstein_eq_gamma_mul (by linarith), hz, mul_zero]

end ExistenceSystem.Summit

end

end
