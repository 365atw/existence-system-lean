module

/-
SUMMIT — RH for `K = ℚ(√−5)`, from the arithmetic in `TheThing`.

The summit is not proved. `rh_one_piece` is conditional on `Frontier`.

`dedekindZeta` in Mathlib is the Dirichlet series of ideal counts. Off absolute
convergence that series is `0`, so "every zero of `dedekindZeta K` has real part
`1/2`" is false, and `TheThing.dedekindZeta_factorization_gap` (an equality at
every `s`) is the wrong statement of `ζ_K(s) = ζ(s) L(s, χ_{−20})`. The identity
that can hold is `halfPlane`, the equality for `1 < Re s`. Extending it into the
strip by the identity theorem is not formalized. Nontrivial zeros are zeros of
the product `ζ(s) L(s, χ_{−20})`, excluding `s = 1` and the negative integers.

SUMMIT KEY (captain confirmed, 2026-10-23) — add as ONE CANDIDATE APPROACH, not a given.

Her words: "tangential extrapolation at the entropy-static-face dimension."

Settled sharpening (captain, 2026-10-23). The free direction — the one the flow
cannot change, her KL9/KL10 conservation — is the alpha, the beginning of the
infinite ride along `Re(s) = 1/2`. The omega, the static face, is never reached:
endless by design, no last point. The candidate asks whether that alpha, forced
along `Re(s) = 1/2` with no terminating omega, pins every nontrivial zero to
`Re(s) = 1/2`.

KL9 is not a module in this repository. KL10 (`conserved_coord`, on
`fm/kl10-conservation-g1`) is a linear coordinate constant along a gradient flow
`ẋ = -Γ∇J`. That flow is not this trajectory, so KL10 is not imported and is not
applied. What closes here is the same shape on the critical ride: the real part
is constantly `1/2`, and its derivative is `0`. The ride's imaginary part has no
upper bound. The extrapolation from that pair of facts to the zero line is
`TangentialExtrapolation`. Its antecedent is proved, so the implication is the
zero line itself, not a reduction of `Frontier`, and `rh_one_piece` does not use it.
-/

public import ExistenceSystem.TheThing
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.NumberTheory.LSeries.Nonvanishing

@[expose] public section

noncomputable section

open scoped Real nonZeroDivisors

open Ideal NumberField

namespace ExistenceSystem.Summit

open ExistenceSystem.TheThing

/-! ## The character on odd primes -/

theorem χ_neg20_two : χ_neg20 (2 : ℤ) = 0 := by
  rw [DirichletCharacter.apply_eq_zero_iff, χ_neg20_level]
  intro ⟨a, b, hab⟩
  have hab' : a * 2 + b * 20 = 1 := by simpa using hab
  omega

theorem χ_neg20_five : χ_neg20 (5 : ℤ) = 0 := by
  rw [DirichletCharacter.apply_eq_zero_iff, χ_neg20_level]
  intro ⟨a, b, hab⟩
  have hab' : a * 5 + b * 20 = 1 := by simpa using hab
  omega

theorem χ_neg20_eq_legendre_negFive {p : ℕ} [Fact p.Prime] (hodd : p ≠ 2) :
    χ_neg20 (p : ℤ) = legendreSym p (-5) := by
  by_cases h5 : p = 5
  · have hχ5 : χ_neg20 (p : ℤ) = 0 := by
      rw [show (p : ℤ) = 5 by exact_mod_cast h5]
      exact χ_neg20_five
    rw [hχ5]
    subst h5
    have hz : ((-5 : ℤ) : ZMod 5) = 0 := by
      norm_num
      exact ZMod.natCast_self 5
    exact ((legendreSym.eq_zero_iff 5 (-5)).2 hz).symm
  · rw [χ_neg20_eq_mul, χ₅_eq_legendre, legendreSym.at_neg hodd]
    have hrec : legendreSym p 5 = legendreSym 5 (p : ℤ) :=
      legendreSym.quadratic_reciprocity_one_mod_four (p := 5) (q := p) (by decide) hodd
    rw [hrec]
    congr 1

/-- On a prime, `χ_{−20}` is `0`, `1`, or `-1`. -/
theorem χ_neg20_trichotomy {p : ℕ} [Fact p.Prime] :
    χ_neg20 (p : ℤ) = 0 ∨ χ_neg20 (p : ℤ) = 1 ∨ χ_neg20 (p : ℤ) = -1 := by
  by_cases h0 : χ_neg20 (p : ℤ) = 0
  · exact Or.inl h0
  · right
    have hmul : χ_neg20 (p : ℤ) = ZMod.χ₄ (p : ℤ) * χ₅ (p : ℤ) := χ_neg20_eq_mul (p : ℤ)
    have h4ne : ZMod.χ₄ (p : ℤ) ≠ 0 := by
      intro h
      apply h0
      rw [hmul, h, zero_mul]
    have h5ne : χ₅ (p : ℤ) ≠ 0 := by
      intro h
      apply h0
      rw [hmul, h, mul_zero]
    have h4 : ZMod.χ₄ (p : ℤ) = 1 ∨ ZMod.χ₄ (p : ℤ) = -1 := by
      rcases ZMod.isQuadratic_χ₄ (p : ℤ) with h0' | h1 | hm
      · exact absurd h0' h4ne
      · exact Or.inl h1
      · exact Or.inr hm
    have h5 : χ₅ (p : ℤ) = 1 ∨ χ₅ (p : ℤ) = -1 := by
      rw [χ₅_eq_legendre] at h5ne ⊢
      have hnz : ((p : ℤ) : ZMod 5) ≠ 0 := fun hz =>
        h5ne ((legendreSym.eq_zero_iff 5 (p : ℤ)).2 hz)
      exact legendreSym.eq_one_or_neg_one (p := 5) hnz
    have hval : ZMod.χ₄ (p : ℤ) * χ₅ (p : ℤ) = 1 ∨ ZMod.χ₄ (p : ℤ) * χ₅ (p : ℤ) = -1 := by
      rcases h4 with h4 | h4 <;> rcases h5 with h5 | h5
      · left; rw [h4, h5]; norm_num
      · right; rw [h4, h5]; norm_num
      · right; rw [h4, h5]; norm_num
      · left; rw [h4, h5]; norm_num
    rw [hmul]
    exact hval

theorem χ_neg20ℂ_odd : DirichletCharacter.Odd χ_neg20ℂ := by
  rw [DirichletCharacter.Odd, χ_neg20ℂ, MulChar.ringHomComp_apply]
  have h4 : ZMod.χ₄ (-1 : ℤ) = -1 := ZMod.χ₄_int_three_mod_four (by decide)
  have h5 : χ₅ (-1 : ℤ) = 1 := by
    rw [χ₅_eq_legendre, legendreSym.at_neg_one (p := 5) (by decide)]
    exact ZMod.χ₄_nat_one_mod_four (by decide)
  have hmul : χ_neg20 (-1 : ℤ) = -1 := by
    rw [χ_neg20_eq_mul, h4, h5]
    decide
  have : χ_neg20 (-1 : ZMod (Nat.lcm 4 5)) = χ_neg20 (-1 : ℤ) := rfl
  rw [this, hmul]
  norm_num

theorem χ_neg20ℂ_ne_one : χ_neg20ℂ ≠ 1 := by
  intro h
  have hodd : (1 : DirichletCharacter ℂ (Nat.lcm 4 5)) (-1) = -1 := by
    simpa [DirichletCharacter.Odd, h] using χ_neg20ℂ_odd
  rw [MulChar.one_apply (isUnit_one.neg)] at hodd
  exact absurd hodd (by norm_num)

/-! ## Coordinates used by the splitting law -/

lemma pairO_int (n : ℤ) : pairO n 0 = n := by
  apply RingOfIntegers.ext
  rw [coe_pairO, map_zero, zero_mul, add_zero]
  exact (map_intCast (algebraMap (𝓞 K) K) n).symm

lemma pair_add (a b c d : ℤ) : pairO a b + pairO c d = pairO (a + c) (b + d) := by
  apply RingOfIntegers.ext
  rw [coe_pairO]
  simp only [map_add, coe_pairO]
  ring_nf

lemma pair_smul (n a b : ℤ) : (n : 𝓞 K) * pairO a b = pairO (n * a) (n * b) := by
  apply RingOfIntegers.ext
  rw [coe_pairO]
  simp only [map_mul, coe_pairO, map_intCast]
  have hn : (n : K) = algebraMap ℤ K n := (map_intCast (algebraMap ℤ K) n).symm
  rw [hn]
  ring_nf

lemma pair_nsmul (n : ℕ) (a b : ℤ) :
    (n : 𝓞 K) * pairO a b = pairO ((n : ℤ) * a) ((n : ℤ) * b) := by
  rw [show (n : 𝓞 K) = ((n : ℤ) : 𝓞 K) from (Int.cast_natCast n).symm]
  exact pair_smul (n : ℤ) a b

lemma δO_eq_pair : δO = pairO 0 1 := by
  apply RingOfIntegers.ext
  rw [coe_δO, coe_pairO, map_zero, map_one, one_mul, zero_add]

lemma eq_two_or_five_of_dvd_twenty {p : ℕ} (hp : Nat.Prime p) (h : p ∣ 20) : p = 2 ∨ p = 5 := by
  have h20 : p ∣ 2 * 10 := by simpa using h
  rcases hp.dvd_mul.mp h20 with h2 | h10
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2)
  · rcases hp.dvd_mul.mp (by simpa using h10 : p ∣ 2 * 5) with h2 | h5
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2)
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).1 h5)

/-! ## Ramified primes `2` and `5` -/

theorem two_ramifies :
    χ_neg20 (2 : ℤ) = 0 ∧ p₂.IsPrime ∧ Ideal.absNorm p₂ = 2 ∧ p₂ ^ 2 = Ideal.span {(2 : 𝓞 K)} := by
  refine ⟨χ_neg20_two, ?_, absNorm_p₂, p₂_sq⟩
  exact isPrime_of_irreducible_absNorm (by
    rw [absNorm_p₂]
    exact (Nat.irreducible_iff_nat_prime 2).mpr Nat.prime_two)

theorem five_ramifies :
    χ_neg20 (5 : ℤ) = 0 ∧ (Ideal.span {δO}).IsPrime ∧
      Ideal.absNorm (Ideal.span {δO}) = 5 ∧
      Ideal.span {δO} ^ 2 = Ideal.span {(5 : 𝓞 K)} := by
  refine ⟨χ_neg20_five, ?_, ?_, ?_⟩
  · exact isPrime_of_irreducible_absNorm (by
      rw [absNorm_span_singleton, δO_eq_pair, intNorm_pair]
      have : ((0 : ℤ) ^ 2 + 5 * (1 : ℤ) ^ 2).natAbs = 5 := by decide
      rw [this]
      exact (Nat.irreducible_iff_nat_prime 5).mpr Nat.prime_five)
  · rw [absNorm_span_singleton, δO_eq_pair, intNorm_pair]
    decide
  · rw [pow_two, span_singleton_mul_span_singleton]
    have hsq : δO * δO = -5 := by rw [← pow_two, δO_sq]
    rw [hsq]
    exact span_singleton_neg (x := (5 : 𝓞 K))

/-! ## No ideal of norm `p` when `χ(p) = -1` -/

lemma not_norm_mul_prime {p : ℕ} [Fact p.Prime] (hχ : χ_neg20 (p : ℤ) = -1)
    {k : ℤ} (hk : k = 1 ∨ k = 2) {a b : ℤ} (h : a ^ 2 + 5 * b ^ 2 = k * (p : ℤ)) :
    False := by
  have hp : Nat.Prime p := Fact.out
  have hodd : p ≠ 2 := by
    intro hp2
    have : χ_neg20 (2 : ℤ) = -1 := by simpa [hp2] using hχ
    rw [χ_neg20_two] at this
    exact absurd this (by decide : (0 : ℤ) ≠ -1)
  have hnot5 : p ≠ 5 := by
    intro hp5
    have : χ_neg20 (5 : ℤ) = -1 := by simpa [hp5] using hχ
    rw [χ_neg20_five] at this
    exact absurd this (by decide : (0 : ℤ) ≠ -1)
  have hleg : legendreSym p (-5) = -1 := by
    rw [← χ_neg20_eq_legendre_negFive hodd, hχ]
  by_cases hb : (p : ℤ) ∣ b
  · have hpa : (p : ℤ) ∣ a := by
      have hsum : (p : ℤ) ∣ a ^ 2 + 5 * b ^ 2 := by
        rw [h]
        exact dvd_mul_left _ _
      have hb2 : (p : ℤ) ∣ b ^ 2 := dvd_pow hb two_ne_zero
      have h5b : (p : ℤ) ∣ 5 * b ^ 2 := dvd_mul_of_dvd_right hb2 _
      have hpa2 : (p : ℤ) ∣ a ^ 2 := (dvd_add_right h5b).mp (by simpa [add_comm] using hsum)
      have hnat : p ∣ a.natAbs ^ 2 := by
        obtain ⟨c, hc⟩ := hpa2
        have habs := congrArg Int.natAbs hc
        rw [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast] at habs
        exact ⟨c.natAbs, habs⟩
      have hdiv : p ∣ a.natAbs := hp.dvd_of_dvd_pow hnat
      rcases Int.natAbs_eq a with ha | ha
      · rw [ha]
        exact_mod_cast hdiv
      · rw [ha]
        exact dvd_neg.mpr (by exact_mod_cast hdiv)
    have hsq : (p : ℤ) ^ 2 ∣ a ^ 2 + 5 * b ^ 2 := by
      refine dvd_add ?_ ?_
      · exact pow_dvd_pow_of_dvd hpa 2
      · exact dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd hb 2) _
    rw [h] at hsq
    have hcancel : (p : ℤ) ∣ k := by
      have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
      obtain ⟨t, ht⟩ := hsq
      have : k * p = p * (p * t) := by simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using ht
      have : k = p * t := mul_left_cancel₀ hp0 (by simpa [mul_comm, mul_assoc] using this)
      exact ⟨t, this⟩
    rcases hk with rfl | rfl
    · obtain ⟨t, ht⟩ := hcancel
      rcases Int.eq_one_or_neg_one_of_mul_eq_one ht.symm with hp1 | hp1
      · exact hp.ne_one (by exact_mod_cast hp1)
      · have : (0 : ℤ) < p := by exact_mod_cast hp.pos
        linarith
    · have hp2 : (p : ℤ) ∣ 2 := hcancel
      have : p ∣ 2 := by exact_mod_cast hp2
      exact hodd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 this)
  · have hb0 : (b : ZMod p) ≠ 0 := by
      intro hz
      exact hb ((ZMod.intCast_zmod_eq_zero_iff_dvd b p).1 hz)
    have hcong : (a : ZMod p) ^ 2 + (5 : ZMod p) * (b : ZMod p) ^ 2 = 0 := by
      have : ((a ^ 2 + 5 * b ^ 2 : ℤ) : ZMod p) = 0 := by
        rw [h, Int.cast_mul, Int.cast_natCast]
        simp
      simpa [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_ofNat] using this
    have ha2 : (a : ZMod p) ^ 2 = -((5 : ZMod p) * (b : ZMod p) ^ 2) :=
      eq_neg_of_add_eq_zero_left hcong
    have hsquare : ((-5 : ℤ) : ZMod p) = ((a : ZMod p) * (b : ZMod p)⁻¹) ^ 2 := by
      have hb2 : (b : ZMod p) ^ 2 ≠ 0 := pow_ne_zero 2 hb0
      have hdiv : (a : ZMod p) ^ 2 * ((b : ZMod p) ^ 2)⁻¹ = -((5 : ZMod p)) := by
        rw [ha2, neg_mul, mul_assoc, mul_inv_cancel₀ hb2, mul_one]
      calc
        ((-5 : ℤ) : ZMod p) = -((5 : ZMod p)) := by simp
        _ = (a : ZMod p) ^ 2 * ((b : ZMod p) ^ 2)⁻¹ := by rw [← hdiv]
        _ = ((a : ZMod p) * (b : ZMod p)⁻¹) ^ 2 := by rw [mul_pow, inv_pow]
    have hnz5 : ((-5 : ℤ) : ZMod p) ≠ 0 := by
      intro hz
      have hdvd : (p : ℤ) ∣ -5 := (ZMod.intCast_zmod_eq_zero_iff_dvd (-5) p).1 hz
      have hdvd' : (p : ℤ) ∣ 5 := dvd_neg.mp hdvd
      have : p ∣ 5 := by exact_mod_cast hdvd'
      exact hnot5 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).1 this)
    have hone : legendreSym p (-5) = 1 :=
      (legendreSym.eq_one_iff (p := p) (a := -5) hnz5).2
        ⟨(a : ZMod p) * (b : ZMod p)⁻¹, by simpa [pow_two] using hsquare⟩
    exact absurd (hone.symm.trans hleg) (by decide : (1 : ℤ) ≠ -1)

lemma no_ideal_of_absNorm_eq_p {p : ℕ} [Fact p.Prime] (hχ : χ_neg20 (p : ℤ) = -1)
    (I : Ideal (𝓞 K)) : Ideal.absNorm I ≠ p := by
  intro hN
  have hp : Nat.Prime p := Fact.out
  have hmem : I ∈ (Ideal (𝓞 K))⁰ :=
    absNorm_ne_zero_iff_mem_nonZeroDivisors.mp (by
      rw [hN]
      exact hp.ne_zero)
  rcases class_eq_one_or_p₂ (ClassGroup.mk0 ⟨I, hmem⟩) with h1 | hp₂
  · have hprinc : I.IsPrincipal := (ClassGroup.mk0_eq_one_iff hmem).mp h1
    let α : 𝓞 K := Submodule.IsPrincipal.generator I
    have hspan : Ideal.span {α} = I := Submodule.IsPrincipal.span_singleton_generator I
    have hnat : (Algebra.norm ℤ α).natAbs = p := by
      rw [← hN, ← hspan, absNorm_span_singleton]
    have hnorm : Algebra.norm ℤ α = (p : ℤ) := by
      calc
        Algebra.norm ℤ α = |(Algebra.norm ℤ α)| := (abs_of_nonneg (norm_nonneg α)).symm
        _ = ((Algebra.norm ℤ α).natAbs : ℤ) := (Int.natCast_natAbs _).symm
        _ = p := by exact_mod_cast hnat
    have hnorm' : (intA α) ^ 2 + 5 * (intB α) ^ 2 = (1 : ℤ) * p := by
      rw [← intNorm_pair, ← coe_eq_pair, hnorm, one_mul]
    exact not_norm_mul_prime hχ (Or.inl rfl) hnorm'
  · have hImem : I * p₂ ∈ (Ideal (𝓞 K))⁰ :=
      absNorm_ne_zero_iff_mem_nonZeroDivisors.mp (by
        rw [map_mul, hN, absNorm_p₂]
        exact mul_ne_zero hp.ne_zero (by decide))
    have hclass : ClassGroup.mk0 ⟨I * p₂, hImem⟩ = 1 := by
      have heq : (⟨I, hmem⟩ * ⟨p₂, p₂_mem⟩ : (Ideal (𝓞 K))⁰) = ⟨I * p₂, hImem⟩ := by
        apply Subtype.ext
        rw [Submonoid.coe_mul]
      rw [← heq, map_mul, hp₂, ← pow_two, p₂_class_sq]
    have hprinc : (I * p₂).IsPrincipal := (ClassGroup.mk0_eq_one_iff hImem).mp hclass
    let α : 𝓞 K := Submodule.IsPrincipal.generator (I * p₂)
    have hspan : Ideal.span {α} = I * p₂ :=
      Submodule.IsPrincipal.span_singleton_generator (I * p₂)
    have hnat : (Algebra.norm ℤ α).natAbs = 2 * p := by
      have habs : Ideal.absNorm (I * p₂) = 2 * p := by
        rw [map_mul, hN, absNorm_p₂]
        ring
      rw [← habs, ← hspan, absNorm_span_singleton]
    have hnorm : Algebra.norm ℤ α = (2 * p : ℤ) := by
      calc
        Algebra.norm ℤ α = |(Algebra.norm ℤ α)| := (abs_of_nonneg (norm_nonneg α)).symm
        _ = ((Algebra.norm ℤ α).natAbs : ℤ) := (Int.natCast_natAbs _).symm
        _ = 2 * p := by exact_mod_cast hnat
    have hnorm' : (intA α) ^ 2 + 5 * (intB α) ^ 2 = (2 : ℤ) * p := by
      rw [← intNorm_pair, ← coe_eq_pair, hnorm]
    exact not_norm_mul_prime hχ (Or.inr rfl) hnorm'

lemma span_prime_of_no_norm_p {p : ℕ} [Fact p.Prime]
    (hno : ∀ I : Ideal (𝓞 K), Ideal.absNorm I ≠ p) :
    (Ideal.span {(p : 𝓞 K)}).IsPrime := by
  have hp : Nat.Prime p := Fact.out
  have hnorm : Ideal.absNorm (Ideal.span {(p : 𝓞 K)}) = p ^ 2 := by
    have h := absNorm_span_natCast (S := 𝓞 K) p
    rw [RingOfIntegers.rank, finrank_K] at h
    simpa using h
  have hirr : Irreducible (Ideal.span {(p : 𝓞 K)}) := by
    rw [irreducible_iff]
    refine ⟨?_, ?_⟩
    · intro hu
      rw [_root_.Ideal.isUnit_iff, ← absNorm_eq_one_iff, hnorm] at hu
      have hlt : 1 < p := hp.one_lt
      have : p ^ 2 ≠ 1 := by
        have : 1 < p ^ 2 := Nat.one_lt_pow (by decide) hlt
        omega
      exact this hu
    · intro A B hAB
      have hmul : Ideal.absNorm A * Ideal.absNorm B = p ^ 2 := by
        have := congrArg Ideal.absNorm hAB
        rw [map_mul, hnorm] at this
        exact this.symm
      have hdvd : Ideal.absNorm A ∣ p ^ 2 := ⟨Ideal.absNorm B, hmul.symm⟩
      obtain ⟨k, hk, hkA⟩ := (Nat.dvd_prime_pow hp).1 hdvd
      interval_cases k
      · left
        rw [_root_.Ideal.isUnit_iff, ← absNorm_eq_one_iff]
        simpa [pow_zero] using hkA
      · exfalso
        exact hno A (by simpa using hkA)
      · right
        rw [_root_.Ideal.isUnit_iff, ← absNorm_eq_one_iff]
        have : p ^ 2 * Ideal.absNorm B = p ^ 2 * 1 := by
          simpa [hkA, mul_one] using hmul
        exact Nat.mul_left_cancel (Nat.pow_pos hp.pos) this
  exact isPrime_of_prime (UniqueFactorizationMonoid.irreducible_iff_prime.mp hirr)

/-! ## Split primes -/

lemma exists_small_sqrt {p : ℕ} [Fact p.Prime] (hodd : p ≠ 2) (h5 : p ≠ 5)
    (hleg : legendreSym p (-5) = 1) :
    ∃ t : ℕ, t ≤ (p - 1) / 2 ∧ (t : ZMod p) ^ 2 = ((-5 : ℤ) : ZMod p) ∧ 0 < t := by
  have hp : Nat.Prime p := Fact.out
  have hnz : ((-5 : ℤ) : ZMod p) ≠ 0 := by
    intro hz
    have hdvd : (p : ℤ) ∣ -5 := (ZMod.intCast_zmod_eq_zero_iff_dvd (-5) p).1 hz
    have hdvd' : (p : ℤ) ∣ 5 := dvd_neg.mp hdvd
    have : p ∣ 5 := by exact_mod_cast hdvd'
    exact h5 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).1 this)
  obtain ⟨u, hu⟩ := (legendreSym.eq_one_iff (p := p) (a := -5) hnz).1 hleg
  have hu0 : u ≠ 0 := by
    intro h0
    apply hnz
    simpa [h0] using hu.symm
  have : NeZero u := ⟨hu0⟩
  have hval : (-u).val = p - u.val := ZMod.val_neg_of_ne_zero u
  have hsum : u.val + (-u).val = p := by
    rw [hval]
    have := ZMod.val_lt u
    omega
  have hle : u.val ≤ (p - 1) / 2 ∨ (-u).val ≤ (p - 1) / 2 := by
    by_contra h
    push Not at h
    have : p + 1 ≤ u.val + (-u).val := by
      have h1 : (p - 1) / 2 + 1 ≤ u.val := Nat.succ_le_of_lt h.1
      have h2 : (p - 1) / 2 + 1 ≤ (-u).val := Nat.succ_le_of_lt h.2
      have hadd := Nat.add_le_add h1 h2
      have hodd' : p % 2 = 1 := (hp.mod_two_eq_one_iff_ne_two).2 hodd
      omega
    omega
  rcases hle with hle | hle
  · refine ⟨u.val, hle, ?_, ?_⟩
    · rw [ZMod.natCast_zmod_val, pow_two]
      simpa [pow_two] using hu.symm
    · have : u.val ≠ 0 := by
        intro h0
        apply hu0
        exact (ZMod.val_eq_zero u).mp h0
      omega
  · refine ⟨(-u).val, hle, ?_, ?_⟩
    · calc
        ((-u).val : ZMod p) ^ 2 = (-u) ^ 2 := by rw [ZMod.natCast_zmod_val]
        _ = u ^ 2 := by rw [neg_sq]
        _ = ((-5 : ℤ) : ZMod p) := by simpa [pow_two] using hu.symm
    · have : (-u).val ≠ 0 := by
        intro h0
        apply hu0
        exact neg_eq_zero.mp ((ZMod.val_eq_zero (-u)).mp h0)
      omega

/-- `χ(p) = 1` produces two distinct prime ideals of norm `p` with product `(p)`. -/
theorem split_of_χ_one {p : ℕ} [Fact p.Prime] (hχ : χ_neg20 (p : ℤ) = 1) :
    ∃ 𝔮 𝔮' : Ideal (𝓞 K), 𝔮.IsPrime ∧ 𝔮'.IsPrime ∧ 𝔮 ≠ 𝔮' ∧
      Ideal.absNorm 𝔮 = p ∧ Ideal.absNorm 𝔮' = p ∧ 𝔮 * 𝔮' = Ideal.span {(p : 𝓞 K)} := by
  have hp : Nat.Prime p := Fact.out
  have hodd : p ≠ 2 := by
    intro h
    have : χ_neg20 (2 : ℤ) = 1 := by simpa [h] using hχ
    rw [χ_neg20_two] at this
    exact zero_ne_one this
  have h5 : p ≠ 5 := by
    intro h
    have : χ_neg20 (5 : ℤ) = 1 := by simpa [h] using hχ
    rw [χ_neg20_five] at this
    exact zero_ne_one this
  have hleg : legendreSym p (-5) = 1 := by
    rw [← χ_neg20_eq_legendre_negFive hodd, hχ]
  obtain ⟨t, ht_le, ht_sq, ht_pos⟩ := exists_small_sqrt hodd h5 hleg
  have hdvd : (p : ℤ) ∣ (t : ℤ) ^ 2 + 5 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have : ((t : ZMod p) ^ 2 + 5 : ZMod p) = 0 := by
      rw [ht_sq]
      ring
    simpa [Int.cast_add, Int.cast_pow, Int.cast_natCast, Int.cast_ofNat] using this
  obtain ⟨m, hm⟩ := hdvd
  have hm_pos : 0 < m := by
    have hnum : 0 < (t : ℤ) ^ 2 + 5 := by nlinarith
    have hp0 : 0 < (p : ℤ) := by exact_mod_cast hp.pos
    have : 0 < (p : ℤ) * m := by simpa [hm] using hnum
    exact (mul_pos_iff_of_pos_left hp0).1 this
  have hm_lt : m < (p : ℤ) := by
    have hmod : p % 2 = 1 := (hp.mod_two_eq_one_iff_ne_two).2 hodd
    set q : ℕ := (p - 1) / 2
    have hpq : p = 2 * q + 1 := by omega
    have htq : t ≤ q := ht_le
    have hq1 : 1 ≤ q := by omega
    have hnum : (t : ℤ) ^ 2 + 5 < (p : ℤ) * p := by
      have htq' : (t : ℤ) ≤ q := by exact_mod_cast htq
      have hpq' : (p : ℤ) = 2 * (q : ℤ) + 1 := by exact_mod_cast hpq
      have hq1' : (1 : ℤ) ≤ q := by exact_mod_cast hq1
      nlinarith
    have : (p : ℤ) * m < (p : ℤ) * p := by
      rw [← hm]
      exact hnum
    exact lt_of_mul_lt_mul_left this (by exact_mod_cast hp.pos.le)
  have hm_abs : (m.natAbs : ℤ) = m := by
    rw [Int.natCast_natAbs, abs_of_nonneg hm_pos.le]
  have hnot_m : ¬ (p : ℕ) ∣ m.natAbs := by
    intro hd
    have : (p : ℤ) ≤ m := by
      have hd' : (p : ℤ) ∣ (m.natAbs : ℤ) := by exact_mod_cast hd
      rw [hm_abs] at hd'
      exact Int.le_of_dvd hm_pos hd'
    have : (p : ℤ) < (p : ℤ) := lt_of_le_of_lt this hm_lt
    exact lt_irrefl _ this
  have hcop : IsCoprime (p : ℤ) m := by
    have hnat : Nat.Coprime p m.natAbs :=
      (hp.coprime_iff_not_dvd).2 hnot_m
    have : IsCoprime (p : ℤ) (m.natAbs : ℕ) := hnat.isCoprime
    simpa [hm_abs] using this
  let 𝔮 : Ideal (𝓞 K) := Ideal.span {(p : 𝓞 K), pairO (t : ℤ) 1}
  let 𝔮' : Ideal (𝓞 K) := Ideal.span {(p : 𝓞 K), pairO (t : ℤ) (-1)}
  have hprod_elt : pairO (t : ℤ) 1 * pairO (t : ℤ) (-1) = (p : 𝓞 K) * (m : 𝓞 K) := by
    rw [mul_pair_conj]
    have hm' : (t : ℤ) ^ 2 + 5 * (1 : ℤ) ^ 2 = (p : ℤ) * m := by simpa [one_pow] using hm
    rw [hm']
    apply RingOfIntegers.ext
    change algebraMap ℤ K ((p : ℤ) * m) = ((p : 𝓞 K) : K) * ((m : 𝓞 K) : K)
    have hpK : ((p : 𝓞 K) : K) = algebraMap ℤ K (p : ℤ) := by
      have hpcast : (p : 𝓞 K) = algebraMap ℤ (𝓞 K) (p : ℤ) := by
        rw [← Int.cast_natCast]
        exact (map_intCast (algebraMap ℤ (𝓞 K)) (p : ℤ)).symm
      rw [RingOfIntegers.coe_eq_algebraMap, hpcast]
      exact (IsScalarTower.algebraMap_apply ℤ (𝓞 K) K (p : ℤ)).symm
    have hmK : ((m : 𝓞 K) : K) = algebraMap ℤ K m := by
      rw [RingOfIntegers.coe_eq_algebraMap, (map_intCast (algebraMap ℤ (𝓞 K)) m).symm]
      exact (IsScalarTower.algebraMap_apply ℤ (𝓞 K) K m).symm
    rw [map_mul, hpK, hmK]
  have hle : 𝔮 * 𝔮' ≤ Ideal.span {(p : 𝓞 K)} := by
    unfold 𝔮 𝔮'
    rw [span_pair_mul_span_pair, span_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact mul_mem_right _ _ (mem_span_singleton_self _)
    · exact mul_mem_right _ _ (mem_span_singleton_self _)
    · exact mul_mem_left _ _ (mem_span_singleton_self _)
    · rw [hprod_elt]
      exact mul_mem_right _ _ (mem_span_singleton_self _)
  have hge : Ideal.span {(p : 𝓞 K)} ≤ 𝔮 * 𝔮' := by
    rw [span_singleton_le_iff_mem]
    obtain ⟨a, b, hab⟩ := hcop
    have hpm : (p : 𝓞 K) * (m : 𝓞 K) ∈ 𝔮 * 𝔮' := by
      rw [← hprod_elt]
      exact mul_mem_mul (subset_span (by simp)) (subset_span (by simp))
    have hpp : (p : 𝓞 K) * (p : 𝓞 K) ∈ 𝔮 * 𝔮' :=
      mul_mem_mul (subset_span (by simp)) (subset_span (by simp))
    have hcomb : (p : 𝓞 K) =
        (a : 𝓞 K) * ((p : 𝓞 K) * (p : 𝓞 K)) + (b : 𝓞 K) * ((p : 𝓞 K) * (m : 𝓞 K)) := by
      apply RingOfIntegers.ext
      simp only [RingOfIntegers.coe_eq_algebraMap, map_add, map_mul, map_intCast]
      calc
        algebraMap ℤ K (p : ℤ) = algebraMap ℤ K (p : ℤ) * algebraMap ℤ K (a * p + b * m) := by
          rw [hab, map_one, mul_one]
        _ = algebraMap ℤ K a * (algebraMap ℤ K (p : ℤ) * algebraMap ℤ K (p : ℤ)) +
            algebraMap ℤ K b * (algebraMap ℤ K (p : ℤ) * algebraMap ℤ K m) := by
          rw [map_add, map_mul, map_mul]
          ring
    rw [hcomb]
    exact add_mem (mul_mem_left _ _ hpp) (mul_mem_left _ _ hpm)
  have hprod : 𝔮 * 𝔮' = Ideal.span {(p : 𝓞 K)} := le_antisymm hle hge
  have hnot_top_left : 𝔮 ≠ ⊤ := by
    intro htop
    have hq' : 𝔮' = Ideal.span {(p : 𝓞 K)} := by
      rw [htop, Ideal.top_mul] at hprod
      exact hprod
    have hmem : pairO (t : ℤ) (-1) ∈ Ideal.span {(p : 𝓞 K)} := by
      rw [← hq']
      exact subset_span (by simp)
    rw [mem_span_singleton] at hmem
    obtain ⟨r, hr⟩ := hmem
    rw [coe_eq_pair r, pair_nsmul] at hr
    have hB := congrArg intB hr
    rw [intB_pair, intB_pair] at hB
    have hdvd1 : (p : ℤ) ∣ -1 := ⟨intB r, hB⟩
    have hdvdone : (p : ℤ) ∣ 1 := dvd_neg.mp hdvd1
    obtain ⟨c, hc⟩ := hdvdone
    rcases Int.eq_one_or_neg_one_of_mul_eq_one hc.symm with hp1 | hp1
    · exact hp.ne_one (by exact_mod_cast hp1)
    · have : (0 : ℤ) < p := by exact_mod_cast hp.pos
      linarith
  have hnot_top_right : 𝔮' ≠ ⊤ := by
    intro htop
    have hq : 𝔮 = Ideal.span {(p : 𝓞 K)} := by
      rw [htop, mul_top] at hprod
      exact hprod
    have hmem : pairO (t : ℤ) 1 ∈ Ideal.span {(p : 𝓞 K)} := by
      rw [← hq]
      exact subset_span (by simp)
    rw [mem_span_singleton] at hmem
    obtain ⟨r, hr⟩ := hmem
    rw [coe_eq_pair r, pair_nsmul] at hr
    have hB := congrArg intB hr
    rw [intB_pair, intB_pair] at hB
    have hdvd1 : (p : ℤ) ∣ 1 := ⟨intB r, hB⟩
    obtain ⟨c, hc⟩ := hdvd1
    rcases Int.eq_one_or_neg_one_of_mul_eq_one hc.symm with hp1 | hp1
    · exact hp.ne_one (by exact_mod_cast hp1)
    · have : (0 : ℤ) < p := by exact_mod_cast hp.pos
      linarith
  have hne : 𝔮 ≠ 𝔮' := by
    intro hqq
    have ht_sum : (2 : 𝓞 K) * (t : 𝓞 K) ∈ 𝔮 := by
      have h1 : pairO (t : ℤ) 1 ∈ 𝔮 := subset_span (by simp)
      have h2 : pairO (t : ℤ) (-1) ∈ 𝔮 := by
        rw [hqq]
        exact subset_span (by simp)
      have hadd : pairO (t : ℤ) 1 + pairO (t : ℤ) (-1) ∈ 𝔮 := add_mem h1 h2
      rw [pair_add, show (t : ℤ) + (t : ℤ) = 2 * (t : ℤ) by ring,
        show (1 : ℤ) + -1 = 0 by ring, pairO_int] at hadd
      simpa [map_mul] using hadd
    have hp_mem : (p : 𝓞 K) ∈ 𝔮 := subset_span (by simp)
    have hnot_t : ¬ (p : ℕ) ∣ t := by
      intro hd
      have : (t : ZMod p) = 0 := by
        rw [ZMod.natCast_eq_zero_iff]
        exact hd
      have : ((-5 : ℤ) : ZMod p) = 0 := by simpa [this] using ht_sq
      have hd5 : (p : ℤ) ∣ 5 :=
        dvd_neg.mp ((ZMod.intCast_zmod_eq_zero_iff_dvd (-5) p).1 this)
      have : p ∣ 5 := by exact_mod_cast hd5
      exact h5 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).1 this)
    have hcop2 : IsCoprime (p : ℤ) (2 * (t : ℤ)) := by
      have hnot : ¬ p ∣ 2 * t := by
        intro hd
        rcases hp.dvd_mul.mp hd with h2 | ht
        · exact hodd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2)
        · exact hnot_t ht
      exact (hp.coprime_iff_not_dvd.2 hnot).isCoprime
    obtain ⟨a, b, hab⟩ := hcop2
    have hone : (1 : 𝓞 K) ∈ 𝔮 := by
      have hlift : (1 : 𝓞 K) =
          (a : 𝓞 K) * (p : 𝓞 K) + (b : 𝓞 K) * ((2 : 𝓞 K) * (t : 𝓞 K)) := by
        apply RingOfIntegers.ext
        simp only [RingOfIntegers.coe_eq_algebraMap, map_add, map_mul, map_intCast]
        calc
          algebraMap ℤ K (1 : ℤ) =
              algebraMap ℤ K (a * p + b * (2 * (t : ℤ))) := by
            rw [hab, map_one]
          _ = algebraMap ℤ K a * algebraMap ℤ K (p : ℤ) +
              algebraMap ℤ K b * (algebraMap ℤ K (2 : ℤ) * algebraMap ℤ K (t : ℤ)) := by
            rw [map_add, map_mul, map_mul, map_mul]
      rw [hlift]
      exact add_mem (mul_mem_left _ _ hp_mem) (mul_mem_left _ _ ht_sum)
    rw [← eq_top_iff_one] at hone
    exact hnot_top_left hone
  have hNp : Ideal.absNorm (Ideal.span {(p : 𝓞 K)}) = p ^ 2 := by
    have h := absNorm_span_natCast (S := 𝓞 K) p
    rw [RingOfIntegers.rank, finrank_K] at h
    simpa using h
  have hmulN : Ideal.absNorm 𝔮 * Ideal.absNorm 𝔮' = p ^ 2 := by
    have h := congrArg Ideal.absNorm hprod
    rw [map_mul, hNp] at h
    exact h
  have hdiv : Ideal.absNorm 𝔮 ∣ p ^ 2 := ⟨Ideal.absNorm 𝔮', hmulN.symm⟩
  obtain ⟨k, hk, hkq⟩ := (Nat.dvd_prime_pow hp).1 hdiv
  have hq1 : Ideal.absNorm 𝔮 ≠ 1 := by
    intro h
    exact hnot_top_left ((absNorm_eq_one_iff).1 h)
  have hq'1 : Ideal.absNorm 𝔮' ≠ 1 := by
    intro h
    exact hnot_top_right ((absNorm_eq_one_iff).1 h)
  have hk_one : k = 1 := by
    interval_cases k
    · exact absurd (by simpa using hkq) hq1
    · rfl
    · have : Ideal.absNorm 𝔮' = 1 := by
        have : p ^ 2 * Ideal.absNorm 𝔮' = p ^ 2 := by simpa [hkq] using hmulN
        exact Nat.mul_left_cancel (Nat.pow_pos hp.pos) (by simpa [one_mul] using this)
      exact absurd this hq'1
  have hNq : Ideal.absNorm 𝔮 = p := by simpa [hk_one] using hkq
  have hNq' : Ideal.absNorm 𝔮' = p := by
    have : p * Ideal.absNorm 𝔮' = p ^ 2 := by simpa [hNq] using hmulN
    have : Ideal.absNorm 𝔮' = p := Nat.mul_left_cancel hp.pos (by simpa [pow_two, mul_comm] using this)
    exact this
  have hprime : 𝔮.IsPrime :=
    isPrime_of_irreducible_absNorm (by rw [hNq]; exact (Nat.irreducible_iff_nat_prime p).mpr hp)
  have hprime' : 𝔮'.IsPrime :=
    isPrime_of_irreducible_absNorm (by rw [hNq']; exact (Nat.irreducible_iff_nat_prime p).mpr hp)
  exact ⟨𝔮, 𝔮', hprime, hprime', hne, hNq, hNq', hprod⟩

theorem inert_of_χ_neg {p : ℕ} [Fact p.Prime] (hχ : χ_neg20 (p : ℤ) = -1) :
    (Ideal.span {(p : 𝓞 K)}).IsPrime ∧ ¬ ∃ I : Ideal (𝓞 K), Ideal.absNorm I = p := by
  refine ⟨?_, ?_⟩
  · exact span_prime_of_no_norm_p (no_ideal_of_absNorm_eq_p hχ)
  · intro ⟨I, hI⟩
    exact no_ideal_of_absNorm_eq_p hχ I hI

/-- Odd primes split, stay inert, or ramify with `χ_{−20}`. `2` and `5` are the ramified squares. -/
theorem splitting_of_χ {p : ℕ} [Fact p.Prime] :
    (χ_neg20 (p : ℤ) = 0 ∧ ∃ 𝔭 : Ideal (𝓞 K), 𝔭.IsPrime ∧ Ideal.absNorm 𝔭 = p ∧
      𝔭 ^ 2 = Ideal.span {(p : 𝓞 K)}) ∨
    (χ_neg20 (p : ℤ) = 1 ∧ ∃ 𝔮 𝔮' : Ideal (𝓞 K), 𝔮.IsPrime ∧ 𝔮'.IsPrime ∧ 𝔮 ≠ 𝔮' ∧
      Ideal.absNorm 𝔮 = p ∧ Ideal.absNorm 𝔮' = p ∧ 𝔮 * 𝔮' = Ideal.span {(p : 𝓞 K)}) ∨
    (χ_neg20 (p : ℤ) = -1 ∧ (Ideal.span {(p : 𝓞 K)}).IsPrime ∧
      ¬ ∃ I : Ideal (𝓞 K), Ideal.absNorm I = p) := by
  have hnot : ¬ IsCoprime (p : ℤ) (Nat.lcm 4 5) → p ∣ 20 := by
    intro h
    rw [χ_neg20_level] at h
    have hcop : ¬ Nat.Coprime p 20 := by
      intro hc
      exact h hc.isCoprime
    exact (Nat.Prime.dvd_iff_not_coprime (Fact.out : Nat.Prime p)).2 hcop
  rcases χ_neg20_trichotomy (p := p) with h0 | h1 | hm
  · left
    have hpdiv : p ∣ 20 := hnot ((DirichletCharacter.apply_eq_zero_iff χ_neg20 (p : ℤ)).1 h0)
    rcases eq_two_or_five_of_dvd_twenty (Fact.out) hpdiv with rfl | rfl
    · obtain ⟨hχ, hprime, hnorm, hsq⟩ := two_ramifies
      exact ⟨hχ, ⟨p₂, hprime, hnorm, hsq⟩⟩
    · obtain ⟨hχ, hprime, hnorm, hsq⟩ := five_ramifies
      exact ⟨hχ, ⟨Ideal.span {δO}, hprime, hnorm, hsq⟩⟩
  · right
    left
    exact ⟨h1, split_of_χ_one h1⟩
  · right
    right
    obtain ⟨hprime, hno⟩ := inert_of_χ_neg hm
    exact ⟨hm, hprime, hno⟩

/-! ## The product `ζ(s) L(s, χ_{−20})` -/

/-- The meromorphic product `ζ(s) L(s, χ_{−20})`. On `1 < Re s` this is `ζ_K`
only if `halfPlane` holds. -/
def zetaProduct (s : ℂ) : ℂ :=
  riemannZeta s * DirichletCharacter.LFunction χ_neg20ℂ s

/-- A zero of the product that is not the pole `s = 1` and not a negative integer.
Negative even integers are the trivial zeros of `ζ`; negative odd integers are the
trivial zeros of this odd `L`-function. `s = 0` is not in that list. -/
def NontrivialZero (s : ℂ) : Prop :=
  zetaProduct s = 0 ∧ s ≠ 1 ∧ ¬ ∃ n : ℕ, s = -((n : ℂ) + 1)

theorem zetaProduct_trivialZero {s : ℂ} (h : ∃ n : ℕ, s = -((n : ℂ) + 1)) :
    zetaProduct s = 0 := by
  obtain ⟨n, rfl⟩ := h
  obtain ⟨k, hk⟩ | ⟨k, hk⟩ := Nat.even_or_odd n
  · have hform : -((n : ℂ) + 1) = -(2 * (k : ℂ)) - 1 := by
      rw [hk]
      push_cast
      ring
    rw [hform, zetaProduct, χ_neg20ℂ_odd.LFunction_neg_two_mul_nat_sub_one k, mul_zero]
  · have hform : -((n : ℂ) + 1) = -2 * ((k : ℂ) + 1) := by
      rw [hk]
      push_cast
      ring
    rw [hform, zetaProduct, riemannZeta_neg_two_mul_nat_add_one k, zero_mul]

theorem zetaProduct_ne_zero_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) : zetaProduct s ≠ 0 :=
  mul_ne_zero (riemannZeta_ne_zero_of_one_le_re hs)
    (DirichletCharacter.LFunction_ne_zero_of_one_le_re χ_neg20ℂ (Or.inl χ_neg20ℂ_ne_one) hs)

/-- `ζ_K(s) = ζ(s) L(s, χ_{−20})` for `1 < Re s`.

This is the Mathlib gap. The splitting law gives the Euler factor at each prime and
does not identify Dirichlet-series coefficients for every `n`. `dedekindZeta` has no
Euler-product theorem in this Mathlib. The old `∀ s` gap in `TheThing` is not this
statement: off the half-plane the series definition is `0`. -/
def halfPlane : Prop :=
  ∀ s : ℂ, 1 < s.re → dedekindZeta K s = zetaProduct s

/-- Zeros of `L(s, χ_{−20})` outside the negative odd integers lie on `Re = 1/2`.
Those negative odds are `Odd.LFunction_neg_two_mul_nat_sub_one`. -/
def dirichletZeroLine : Prop :=
  ∀ s : ℂ, DirichletCharacter.LFunction χ_neg20ℂ s = 0 →
    ¬ (∃ n : ℕ, s = -((2 * (n : ℂ)) + 1)) → s.re = 1 / 2

/-- The exact frontier of the summit.
`halfPlane`, `RiemannHypothesis`, and `dirichletZeroLine` are each used by `rh_one_piece`.
`TangentialExtrapolation` is not a clause: it does not reduce this frontier. -/
structure Frontier : Prop where
  half : halfPlane
  riemann : RiemannHypothesis
  dirichlet : dirichletZeroLine

/-- Conditional summit. Not a proof of RH for `K`.

Given `Frontier`, every nontrivial zero of `ζ · L(χ_{−20})` has real part `1/2`,
and on `1 < Re s` the Mathlib `dedekindZeta K` agrees with that product and does not
vanish. A zero of `ζ_K` inside the strip is a zero of this product only after the
half-plane identity is continued, and that continuation is not a theorem here. -/
theorem rh_one_piece (frontier : Frontier) (s : ℂ) :
    (zetaProduct s = 0 → s ≠ 1 → (¬ ∃ n : ℕ, s = -((n : ℂ) + 1)) → s.re = 1 / 2) ∧
      (1 < s.re → dedekindZeta K s = zetaProduct s ∧ dedekindZeta K s ≠ 0) := by
  refine ⟨?_, ?_⟩
  · intro hz hpole htriv
    rcases mul_eq_zero.mp hz with hzζ | hL
    · have hnot : ¬ ∃ n : ℕ, s = -2 * ((n : ℂ) + 1) := by
        intro ⟨n, hn⟩
        apply htriv
        refine ⟨2 * n + 1, ?_⟩
        rw [hn]
        push_cast
        ring_nf
      exact frontier.riemann s hzζ hnot hpole
    · have hnot : ¬ ∃ n : ℕ, s = -((2 * (n : ℂ)) + 1) := by
        intro ⟨n, hn⟩
        apply htriv
        refine ⟨2 * n, ?_⟩
        rw [hn]
        push_cast
        ring_nf
      exact frontier.dirichlet s hL hnot
  · intro hs
    have heq : dedekindZeta K s = zetaProduct s := frontier.half s hs
    refine ⟨heq, ?_⟩
    rw [heq]
    exact zetaProduct_ne_zero_of_one_le_re hs.le

/-! ## Summit key: alpha on the critical line, no terminating omega

The tangent below is the local direction of the zeta trajectory along `1/2 + it`.
Her phrase for the candidate is "tangential extrapolation at the entropy-static-face
dimension." The static face is not a value of this derivative: there is no last `t`.
-/

/-- The critical line, parameterized by the imaginary part. -/
def criticalPoint (t : ℝ) : ℂ := (1 / 2 : ℂ) + (t : ℂ) * Complex.I

/-- Alpha. The free direction of this ride is its real part, constantly `1/2`.

KL10 `conserved_coord` is this shape for a gradient flow. It is not applied: this
path is not a solution of `ẋ = -Γ∇J`. -/
theorem alphaForced (t : ℝ) : (criticalPoint t).re = 1 / 2 := by
  simp [criticalPoint, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    Complex.I_im, Complex.ofReal_im]

/-- The real part is an exactly conserved coordinate of the ride: its derivative is `0`. -/
theorem hasDerivAt_re_criticalPoint (t : ℝ) :
    HasDerivAt (fun s : ℝ => (criticalPoint s).re) 0 t := by
  have hfun : (fun s : ℝ => (criticalPoint s).re) = fun _ => (1 / 2 : ℝ) := by
    funext s
    exact alphaForced s
  rw [hfun]
  exact hasDerivAt_const t (1 / 2)

theorem hasDerivAt_criticalPoint (t : ℝ) : HasDerivAt criticalPoint Complex.I t := by
  have hof : HasDerivAt (fun s : ℝ => (s : ℂ)) (1 : ℂ) t := (hasDerivAt_id t).ofReal_comp
  have hmul : HasDerivAt (fun s : ℝ => (s : ℂ) * Complex.I) (1 * Complex.I) t :=
    hof.mul_const Complex.I
  have h := (hasDerivAt_const t ((1 / 2 : ℂ))).add hmul
  unfold criticalPoint
  convert h using 1
  simp [zero_add, one_mul]

/-- Omega is never reached. The imaginary part of the ride has no last value. -/
theorem noTerminatingOmega : ¬ ∃ B : ℝ, ∀ t : ℝ, (criticalPoint t).im ≤ B := by
  intro ⟨B, hB⟩
  have h := hB (B + 1)
  simp [criticalPoint, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re,
    Complex.I_im] at h
  linarith

/-- The zeta trajectory along the critical line. -/
def criticalTrajectory (t : ℝ) : ℂ := zetaProduct (criticalPoint t)

lemma differentiableAt_zetaProduct {s : ℂ} (hs : s ≠ 1) : DifferentiableAt ℂ zetaProduct s :=
  (differentiableAt_riemannZeta hs).mul
    (DirichletCharacter.differentiableAt_LFunction χ_neg20ℂ s (Or.inr χ_neg20ℂ_ne_one))

lemma criticalPoint_ne_one (t : ℝ) : criticalPoint t ≠ 1 := by
  intro h
  have := congrArg Complex.re h
  rw [alphaForced, Complex.one_re] at this
  exact (by norm_num : (1 / 2 : ℝ) ≠ 1) this

/-- The tangent of the zeta trajectory at each finite `t`. This is the closed part of the
summit key. The factor `I` is the velocity of the critical line. -/
theorem hasDerivAt_criticalTrajectory (t : ℝ) :
    HasDerivAt criticalTrajectory ((deriv zetaProduct (criticalPoint t)) * Complex.I) t := by
  have hζ : HasDerivAt zetaProduct (deriv zetaProduct (criticalPoint t)) (criticalPoint t) :=
    (differentiableAt_zetaProduct (criticalPoint_ne_one t)).hasDerivAt
  unfold criticalTrajectory
  simpa [Function.comp_def] using hζ.comp t (hasDerivAt_criticalPoint t)

theorem criticalTangent_eq (t : ℝ) :
    deriv criticalTrajectory t = deriv zetaProduct (criticalPoint t) * Complex.I :=
  (hasDerivAt_criticalTrajectory t).deriv

/-- Where the summit key stops.

The antecedent is `alphaForced` together with `noTerminatingOmega`, both proved.
The consequent is the zero line. An implication whose antecedent is proved is the
consequent, so this is not a cleaner frontier than `Frontier`, and `rh_one_piece`
does not take it as a hypothesis. -/
def TangentialExtrapolation : Prop :=
  ((∀ t : ℝ, (criticalPoint t).re = 1 / 2) ∧ ¬ ∃ B : ℝ, ∀ t : ℝ, (criticalPoint t).im ≤ B) →
    ∀ s : ℂ, NontrivialZero s → s.re = 1 / 2

end ExistenceSystem.Summit

end

end
