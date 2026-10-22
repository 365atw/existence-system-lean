module

/-
ℚ(√5) and ℤ[φ], with σ, trace, norm, and the two real embeddings.

Taxonomy L214: "**σ** | the nontrivial automorphism of ℚ(√5), √5 ↦ −√5;
σ(φ) = 1 − φ = −1/φ".

Carriers (map, G6 "B-Q5" / "B-TR"): `QuadraticAlgebra ℤ 1 1` is ℤ[φ],
`QuadraticAlgebra ℚ 1 1` is ℚ(√5), `star` is σ, and `QuadraticAlgebra.lift`
at φ and at ψ is the two real embeddings. Trace and norm are Mathlib's.

The coil faces stay over ℝ (KL18). This module does not identify `ωⁿ` inside
ℚ(√5) with the real power `φⁿ`.
-/
public import Mathlib

@[expose] public section

open Real
open scoped goldenRatio QuadraticAlgebra

namespace ExistenceSystem.Quadratic

/-- ℤ[φ], the ring `ω² = 1 + ω`. -/
abbrev Zphi := QuadraticAlgebra ℤ 1 1

/-- ℚ(√5), the algebra `ω² = 1 + ω`. -/
abbrev K := QuadraticAlgebra ℚ 1 1

/-- No rational root of `x² − x − 1`. This is the hypothesis of Mathlib's
`Field (QuadraticAlgebra ℚ 1 1)` instance. -/
theorem no_rational_root : ∀ r : ℚ, r ^ 2 ≠ 1 + 1 * r := by
  intro r hr
  have hr' : (r : ℝ) ^ 2 = (r : ℝ) + 1 := by
    have : (r : ℝ) ^ 2 = 1 + 1 * (r : ℝ) := by exact_mod_cast hr
    linarith
  have hfac : ((r : ℝ) - φ) * ((r : ℝ) - ψ) = 0 := by
    have h1 : φ + ψ = 1 := goldenRatio_add_goldenConj
    have h2 : φ * ψ = -1 := goldenRatio_mul_goldenConj
    linear_combination hr' - (r : ℝ) * h1 + h2
  rcases mul_eq_zero.1 hfac with h | h
  · exact goldenRatio_irrational ⟨r, by linarith⟩
  · exact goldenConj_irrational ⟨r, by linarith⟩

instance factNoRoot : Fact (∀ r : ℚ, r ^ 2 ≠ 1 + 1 * r) := ⟨no_rational_root⟩

/-- σ² = id. Taxonomy L214, the nontrivial automorphism, has order two. -/
theorem sigma_involutive (x : K) : star (star x) = x := star_star x

theorem fold_eq_trace (x : K) :
    x + star x = algebraMap ℚ K (QuadraticAlgebra.trace x) :=
  (QuadraticAlgebra.algebraMap_trace_eq_add_star x).symm

theorem trace_def' (x : K) : QuadraticAlgebra.trace x = 2 * x.re + x.im := by
  rw [QuadraticAlgebra.trace_def]
  simp

theorem norm_def' (x : K) :
    QuadraticAlgebra.norm x = x.re * x.re + x.re * x.im - x.im * x.im := by
  rw [QuadraticAlgebra.norm_def]
  simp

/-- The inclusion ℤ[φ] → ℚ(√5). -/
def coeZphi : Zphi →+* K where
  toFun z := ⟨(z.re : ℚ), (z.im : ℚ)⟩
  map_one' := by ext <;> simp
  map_mul' z w := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' z w := by ext <;> simp

theorem coeZphi_star (z : Zphi) : coeZphi (star z) = star (coeZphi z) := by
  cases z with
  | mk x y =>
    ext <;> simp [coeZphi, QuadraticAlgebra.star_mk]

theorem omega_sq_zphi : (ω : Zphi) * ω = 1 + ω := by
  rw [QuadraticAlgebra.omega_mul_omega_eq_add]
  simp

lemma phi_is_root : φ * φ = (1 : ℚ) • (1 : ℝ) + (1 : ℚ) • φ := by
  simp only [Algebra.smul_def, map_one, one_mul]
  rw [← sq, goldenRatio_sq]
  ring

lemma psi_is_root : ψ * ψ = (1 : ℚ) • (1 : ℝ) + (1 : ℚ) • ψ := by
  simp only [Algebra.smul_def, map_one, one_mul]
  rw [← sq, goldenConj_sq]
  ring

/-- The real embedding `ℚ(√5) → ℝ` sending `ω` to `φ`. -/
noncomputable def embedPhi : K →ₐ[ℚ] ℝ :=
  QuadraticAlgebra.lift ⟨φ, phi_is_root⟩

/-- The real embedding `ℚ(√5) → ℝ` sending `ω` to `ψ = σ(φ)`. -/
noncomputable def embedPsi : K →ₐ[ℚ] ℝ :=
  QuadraticAlgebra.lift ⟨ψ, psi_is_root⟩

theorem embedPhi_mk (x y : ℚ) : embedPhi ⟨x, y⟩ = (x : ℝ) + (y : ℝ) * φ := by
  simp [embedPhi, QuadraticAlgebra.lift_apply_apply, Algebra.smul_def]

theorem embedPsi_mk (x y : ℚ) : embedPsi ⟨x, y⟩ = (x : ℝ) + (y : ℝ) * ψ := by
  simp [embedPsi, QuadraticAlgebra.lift_apply_apply, Algebra.smul_def]

theorem embedPhi_omega : embedPhi ω = φ := by
  rw [show (ω : K) = ⟨0, 1⟩ from rfl, embedPhi_mk]
  simp

theorem embedPsi_omega : embedPsi ω = ψ := by
  rw [show (ω : K) = ⟨0, 1⟩ from rfl, embedPsi_mk]
  simp

/-- The two embeddings are intertwined by σ: `ι_ψ = ι_φ ∘ star`. -/
theorem embedPsi_eq_embedPhi_star (z : K) : embedPsi z = embedPhi (star z) := by
  rw [show z = ⟨z.re, z.im⟩ from by ext <;> rfl, QuadraticAlgebra.star_mk, embedPsi_mk,
    embedPhi_mk]
  rw [show ψ = 1 - φ from one_sub_goldenConj.symm]
  push_cast
  ring

theorem embedPhi_coeZphi (z : Zphi) :
    embedPhi (coeZphi z) = (z.re : ℝ) + (z.im : ℝ) * φ := by
  simp [coeZphi, embedPhi_mk]

theorem embedPsi_coeZphi (z : Zphi) :
    embedPsi (coeZphi z) = (z.re : ℝ) + (z.im : ℝ) * ψ := by
  simp [coeZphi, embedPsi_mk]

/-- `1` and `φ` are linearly independent over ℚ, so `embedPhi` is injective. -/
theorem embedPhi_injective : Function.Injective embedPhi := by
  rw [embedPhi, QuadraticAlgebra.lift_injective_iff]
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have h : (s : ℝ) + (t : ℝ) * φ = 0 := by
    simpa [Algebra.smul_def] using hst
  rcases eq_or_ne t 0 with rfl | ht
  · have hs : (s : ℝ) = 0 := by simpa using h
    exact ⟨by exact_mod_cast hs, rfl⟩
  · exfalso
    have htR : (t : ℝ) ≠ 0 := by exact_mod_cast ht
    have hφ : φ = (-(s : ℝ)) / (t : ℝ) := by
      rw [eq_div_iff htR]
      linarith
    have hφq : ((-(s / t) : ℚ) : ℝ) = φ := by
      calc
        ((-(s / t) : ℚ) : ℝ) = (-(s : ℝ)) / (t : ℝ) := by push_cast; ring
        _ = φ := hφ.symm
    exact goldenRatio_irrational ⟨-(s / t), hφq⟩

end ExistenceSystem.Quadratic

end
