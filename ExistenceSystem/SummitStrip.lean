module

/-
SUMMIT — the reflection `s ↦ 1 − s` and the strip frontier.

`χ_{−20}` is primitive of conductor `20`, so the functional equations of `ζ` and of
`L(s, χ_{−20})` carry a nontrivial zero `s` of the product to the nontrivial zero `1 − s`.
-/

public import ExistenceSystem.Summit
public import Mathlib.NumberTheory.LSeries.DirichletContinuation

@[expose] public section

noncomputable section

open Complex

open scoped Real

namespace ExistenceSystem.Summit

open ExistenceSystem.TheThing NumberField

/-! ## `χ_{−20}` is primitive -/

lemma χ_neg20_int (n : ℤ) : χ_neg20ℂ n = (χ_neg20 n : ℂ) := by
  rw [χ_neg20ℂ, MulChar.ringHomComp_apply]
  simp

lemma χ_neg20_one : χ_neg20 (1 : ℤ) = 1 := by
  simp

lemma χ_neg20_eleven : χ_neg20 (11 : ℤ) = -1 := by
  rw [χ_neg20_eq_mul, ZMod.χ₄_int_three_mod_four (by decide), χ₅_eq_legendre,
    legendreSym.mod 5 11]
  norm_num [legendreSym.at_one]

lemma χ_neg20_thirteen : χ_neg20 (13 : ℤ) = -1 := by
  rw [χ_neg20_eq_mul, ZMod.χ₄_int_one_mod_four (by decide), χ₅_eq_legendre,
    legendreSym.mod 5 13]
  have h3 : legendreSym 5 3 = -1 := by
    rw [legendreSym.eq_neg_one_iff]
    decide
  norm_num [h3]

/-- A character that factors through level `d` agrees on integers congruent mod `d`. -/
lemma FactorsThrough.apply_eq {d : ℕ} (h : χ_neg20ℂ.FactorsThrough d) {a b : ℤ}
    (ha : IsCoprime a (Nat.lcm 4 5 : ℕ)) (hb : IsCoprime b (Nat.lcm 4 5 : ℕ))
    (hab : (a : ZMod d) = (b : ZMod d)) : χ_neg20ℂ a = χ_neg20ℂ b := by
  obtain ⟨hd, χ₀, hχ⟩ := h
  rw [hχ, DirichletCharacter.changeLevel_eq_cast_of_dvd' χ₀ hd ha,
    DirichletCharacter.changeLevel_eq_cast_of_dvd' χ₀ hd hb, hab]

lemma eq_twenty_of_factorsThrough {c : ℕ} (hdvd : c ∣ 20) (hft : χ_neg20ℂ.FactorsThrough c) :
    c = 20 := by
  by_contra hne
  have hcases : c ∣ 10 ∨ c ∣ 4 := by
    have hmem : c ∈ Nat.divisors 20 := Nat.mem_divisors.2 ⟨hdvd, by norm_num⟩
    have : Nat.divisors 20 = {1, 2, 4, 5, 10, 20} := by decide
    rw [this] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h | h | h | h | h <;> subst h <;> first | decide | exact absurd rfl hne
  have hcop : ∀ n : ℤ, Int.gcd n 20 = 1 → IsCoprime n (Nat.lcm 4 5 : ℕ) := by
    intro n hn
    rw [χ_neg20_level]
    exact Int.isCoprime_iff_gcd_eq_one.2 hn
  rcases hcases with h10 | h4
  · have hcong : ((11 : ℤ) : ZMod c) = ((1 : ℤ) : ZMod c) := by
      rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
      exact (Int.natCast_dvd_natCast.2 h10).trans (by norm_num)
    have := FactorsThrough.apply_eq hft (hcop 11 (by norm_num)) (hcop 1 (by norm_num)) hcong
    rw [χ_neg20_int, χ_neg20_int, χ_neg20_eleven, χ_neg20_one] at this
    norm_num at this
  · have hcong : ((13 : ℤ) : ZMod c) = ((1 : ℤ) : ZMod c) := by
      rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
      exact (Int.natCast_dvd_natCast.2 h4).trans (by norm_num)
    have := FactorsThrough.apply_eq hft (hcop 13 (by norm_num)) (hcop 1 (by norm_num)) hcong
    rw [χ_neg20_int, χ_neg20_int, χ_neg20_thirteen, χ_neg20_one] at this
    norm_num at this

/-- `χ_{−20}` has conductor `20`. -/
theorem χ_neg20ℂ_isPrimitive : χ_neg20ℂ.IsPrimitive := by
  rw [DirichletCharacter.isPrimitive_def]
  have hdvd := χ_neg20ℂ.conductor_dvd_level
  have hft := χ_neg20ℂ.factorsThrough_conductor
  generalize χ_neg20ℂ.conductor = c at hdvd hft ⊢
  rw [χ_neg20_level] at hdvd ⊢
  exact eq_twenty_of_factorsThrough hdvd hft

/-! ## The reflection `s ↦ 1 − s` -/

lemma χ_neg20_isQuadratic : (χ_neg20 : MulChar (ZMod (Nat.lcm 4 5)) ℤ).IsQuadratic := by
  intro a
  have ha : (((a.val : ℕ) : ℤ) : ZMod (Nat.lcm 4 5)) = a := by
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  rw [← ha, χ_neg20_eq_mul]
  have h4 : ZMod.χ₄ ((a.val : ℕ) : ℤ) = 0 ∨ ZMod.χ₄ ((a.val : ℕ) : ℤ) = 1 ∨
      ZMod.χ₄ ((a.val : ℕ) : ℤ) = -1 := ZMod.isQuadratic_χ₄ _
  have h5 : χ₅ ((a.val : ℕ) : ℤ) = 0 ∨ χ₅ ((a.val : ℕ) : ℤ) = 1 ∨
      χ₅ ((a.val : ℕ) : ℤ) = -1 := quadraticChar_isQuadratic (ZMod 5) _
  generalize ZMod.χ₄ ((a.val : ℕ) : ℤ) = x at h4 ⊢
  generalize χ₅ ((a.val : ℕ) : ℤ) = y at h5 ⊢
  rcases h4 with rfl | rfl | rfl <;> rcases h5 with rfl | rfl | rfl <;> norm_num

lemma χ_neg20ℂ_inv : χ_neg20ℂ⁻¹ = χ_neg20ℂ :=
  (χ_neg20_isQuadratic.comp (Int.castRingHom ℂ)).inv

lemma riemannZeta_one_sub_eq_zero {s : ℂ} (hz : riemannZeta s = 0) (hs1 : s ≠ 1)
    (hneg : ¬ ∃ n : ℕ, s = -((n : ℂ) + 1)) : riemannZeta (1 - s) = 0 := by
  have hs : ∀ n : ℕ, s ≠ -n := by
    intro n hn
    rcases n with _ | m
    · rw [hn, Nat.cast_zero, neg_zero, riemannZeta_zero] at hz
      norm_num at hz
    · exact hneg ⟨m, by rw [hn]; push_cast; ring⟩
  rw [riemannZeta_one_sub hs hs1, hz, mul_zero]

lemma lcm_four_five_ne_one : Nat.lcm 4 5 ≠ 1 := by decide

lemma LFunction_one_sub_eq_zero {s : ℂ} (hz : DirichletCharacter.LFunction χ_neg20ℂ s = 0)
    (hodd : ¬ ∃ n : ℕ, s = -((2 * (n : ℂ)) + 1)) :
    DirichletCharacter.LFunction χ_neg20ℂ (1 - s) = 0 := by
  have hΓ : Complex.Gammaℝ (s + 1) ≠ 0 := by
    rw [Ne, Complex.Gammaℝ_eq_zero_iff]
    rintro ⟨n, hn⟩
    exact hodd ⟨n, by linear_combination hn⟩
  have hΛ : DirichletCharacter.completedLFunction χ_neg20ℂ s = 0 := by
    have h := DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ_neg20ℂ s
      (Or.inr lcm_four_five_ne_one)
    rw [χ_neg20ℂ_odd.gammaFactor_def, hz, eq_comm, div_eq_zero_iff] at h
    exact h.resolve_right hΓ
  have hΛ' : DirichletCharacter.completedLFunction χ_neg20ℂ (1 - s) = 0 := by
    rw [χ_neg20ℂ_isPrimitive.completedLFunction_one_sub, χ_neg20ℂ_inv, hΛ, mul_zero]
  rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ_neg20ℂ (1 - s)
    (Or.inr lcm_four_five_ne_one), hΛ', zero_div]

/-- The functional equations carry a nontrivial zero `s` of `ζ · L(χ_{−20})` to the
nontrivial zero `1 − s`. -/
theorem nontrivialZero_one_sub {s : ℂ} (h : NontrivialZero s) : NontrivialZero (1 - s) := by
  obtain ⟨hz, hs1, htriv⟩ := h
  have hz' : zetaProduct (1 - s) = 0 := by
    rcases mul_eq_zero.mp hz with hζ | hL
    · exact mul_eq_zero_of_left (riemannZeta_one_sub_eq_zero hζ hs1 htriv) _
    · refine mul_eq_zero_of_right _ (LFunction_one_sub_eq_zero hL ?_)
      rintro ⟨n, hn⟩
      exact htriv ⟨2 * n, by rw [hn]; push_cast; ring⟩
  refine ⟨hz', ?_, ?_⟩
  · intro h1
    rw [h1] at hz'
    exact zetaProduct_ne_zero_of_one_le_re (by simp) hz'
  · rintro ⟨n, hn⟩
    have hs : s = (n : ℂ) + 2 := by linear_combination -hn
    apply zetaProduct_ne_zero_of_one_le_re _ hz
    rw [hs]
    simp only [add_re, natCast_re]
    norm_num
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

/-! ## The strip frontier -/

/-- The product `ζ(s) L(s, χ_{−20})` has no zero in `1/2 < Re s < 1`.

This is the one clause left once the reflection is proved. It is not weaker than RH:
`stripZeroFree_iff` shows it is equivalent to `RiemannHypothesis ∧ dirichletZeroLine`.
What it removes is the left half `0 ≤ Re s < 1/2` of the strip and the outside
`Re s ≥ 1`, which the machine now discharges. -/
def stripZeroFree : Prop :=
  ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 → zetaProduct s ≠ 0

lemma re_eq_half_of_zero {s : ℂ} (hfree : stripZeroFree) (hz : zetaProduct s = 0)
    (hz' : zetaProduct (1 - s) = 0) : s.re = 1 / 2 := by
  have right : ∀ w : ℂ, zetaProduct w = 0 → ¬ 1 / 2 < w.re := by
    intro w hw hlt
    by_cases h1 : w.re < 1
    · exact hfree w hlt h1 hw
    · exact zetaProduct_ne_zero_of_one_le_re (not_lt.mp h1) hw
  rcases lt_trichotomy s.re (1 / 2) with hlt | heq | hgt
  · exact absurd (by simp only [sub_re, one_re]; linarith) (right (1 - s) hz')
  · exact heq
  · exact absurd hgt (right s hz)

/-- Strip frontier → every nontrivial zero of `ζ · L(χ_{−20})` has real part `1/2`. -/
theorem zeroLine_of_stripZeroFree (hfree : stripZeroFree) {s : ℂ} (hs : NontrivialZero s) :
    s.re = 1 / 2 :=
  re_eq_half_of_zero hfree hs.1 (nontrivialZero_one_sub hs).1

lemma riemannZeta_neg_odd_ne_zero (n : ℕ) : riemannZeta (-((2 * (n : ℂ)) + 1)) ≠ 0 := by
  set w : ℂ := 2 * (n : ℂ) + 2 with hw
  have hwre : w.re = 2 * n + 2 := by simp [hw]
  have hw1 : w ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    rw [hwre, one_re] at this
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hwn : ∀ m : ℕ, w ≠ -m := by
    intro m h
    have := congrArg Complex.re h
    rw [hwre, neg_re, natCast_re] at this
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n), (Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have hfe := riemannZeta_one_sub hwn hw1
  rw [show (1 : ℂ) - w = -((2 * (n : ℂ)) + 1) by rw [hw]; ring] at hfe
  rw [hfe]
  have hpos : 0 < w.re := by rw [hwre]; positivity
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero ?_) ?_) ?_)
    (riemannZeta_ne_zero_of_one_le_re (by rw [hwre]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]))
  · exact (cpow_ne_zero_iff_of_exponent_ne_zero (by
      intro h; rw [neg_eq_zero] at h; rw [h, zero_re] at hpos; linarith)).2 (by exact_mod_cast Real.two_pi_pos.ne')
  · exact Complex.Gamma_ne_zero_of_re_pos hpos
  · intro hc
    obtain ⟨k, hk⟩ := Complex.cos_eq_zero_iff.mp hc
    have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have h2 : ((2 * n + 2 : ℤ) : ℂ) = ((2 * k + 1 : ℤ) : ℂ) := by
      push_cast
      have : (π : ℂ) * w = (2 * k + 1) * π := by linear_combination 2 * hk
      rw [hw] at this
      exact mul_right_cancel₀ hπ (by linear_combination this)
    have h2' : (2 * n + 2 : ℤ) = 2 * k + 1 := by exact_mod_cast h2
    omega

/-- The strip clause is exactly RH for `ζ` together with the zero line of `L(χ_{−20})`. -/
theorem stripZeroFree_iff : stripZeroFree ↔ RiemannHypothesis ∧ dirichletZeroLine := by
  constructor
  · intro hfree
    refine ⟨?_, ?_⟩
    · intro s hz htriv hs1
      have hneg : ¬ ∃ n : ℕ, s = -((n : ℂ) + 1) := by
        rintro ⟨n, rfl⟩
        obtain ⟨k, rfl⟩ | ⟨k, rfl⟩ := Nat.even_or_odd n
        · apply riemannZeta_neg_odd_ne_zero k
          rw [← hz]
          push_cast
          ring_nf
        · exact htriv ⟨k, by push_cast; ring⟩
      exact re_eq_half_of_zero hfree (mul_eq_zero_of_left hz _)
        (mul_eq_zero_of_left (riemannZeta_one_sub_eq_zero hz hs1 hneg) _)
    · intro s hz hodd
      exact re_eq_half_of_zero hfree (mul_eq_zero_of_right _ hz)
        (mul_eq_zero_of_right _ (LFunction_one_sub_eq_zero hz hodd))
  · rintro ⟨hRH, hL⟩ s hlo hhi hz
    rcases mul_eq_zero.mp hz with hζ | hLz
    · have hs1 : s ≠ 1 := by
        rintro rfl
        rw [one_re] at hhi
        exact lt_irrefl _ hhi
      have htriv : ¬ ∃ n : ℕ, s = -2 * ((n : ℂ) + 1) := by
        rintro ⟨n, rfl⟩
        simp only [mul_re, neg_re, re_ofNat, add_re, natCast_re, one_re, neg_im, im_ofNat,
          add_im, natCast_im, one_im] at hlo
        linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      have := hRH s hζ htriv hs1
      linarith
    · have hodd : ¬ ∃ n : ℕ, s = -((2 * (n : ℂ)) + 1) := by
        rintro ⟨n, rfl⟩
        simp only [neg_re, add_re, mul_re, re_ofNat, natCast_re, im_ofNat, natCast_im,
          one_re] at hlo
        linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      have := hL s hLz hodd
      linarith

/-! ## Carried into the strip: the continuation is unique -/

/-- On `ℂ ∖ {1}`, any differentiable function that agrees with `dedekindZeta K` on
`Re s > 1` is the product `ζ(s) L(s, χ_{−20})`, provided `halfPlane`. -/
theorem continuation_eq_zetaProduct (hhalf : halfPlane) {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F {1}ᶜ) (hagree : ∀ s : ℂ, 1 < s.re → F s = dedekindZeta K s) :
    ∀ s : ℂ, s ≠ 1 → F s = zetaProduct s := by
  have hU : IsOpen ({1}ᶜ : Set ℂ) := isOpen_compl_singleton
  have hP : DifferentiableOn ℂ zetaProduct {1}ᶜ := fun s hs =>
    (differentiableAt_zetaProduct hs).differentiableWithinAt
  have hconn : IsPreconnected ({1}ᶜ : Set ℂ) :=
    (isConnected_compl_singleton_of_one_lt_rank (by simp) 1).isPreconnected
  have h2 : (2 : ℂ) ∈ ({1}ᶜ : Set ℂ) := by norm_num
  have hev : F =ᶠ[nhds (2 : ℂ)] zetaProduct := by
    have hopen : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const continuous_re
    filter_upwards [hopen.mem_nhds (by norm_num : (1 : ℝ) < (2 : ℂ).re)] with s hs
    rw [hagree s hs, hhalf s hs]
  intro s hs
  exact (hF.analyticOnNhd hU).eqOn_of_preconnected_of_eventuallyEq (hP.analyticOnNhd hU)
    hconn h2 hev hs

end ExistenceSystem.Summit

end

end
