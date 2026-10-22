module

/-
The Landau functional in the uniform sector, at field level.

Note L598–L599: `J = ∫ d³r_∥ {f_L + f_el}`.
Note L602–L605 writes `f_L` with common moduli inside each shell.
Note L609 writes `f_el`. The tensors `T`, `M` and the domain `Ω` are not given entries
or a shape (map, §6a U28); they stay parameters. The reduction she divides by `|Ω|`
is the scalar density at L621, not a measure on an invented domain.

Note L615: "Every term in J is indexed by a relation ∑ G = 0 in ℤ⁶; nothing else may
appear." The carrier of a general term, at every order, is not fixed (map, KL22). A term
of `J` in this module is one summand of the uniform-sector density at L621.

Note L619 contributes `η²μ cos` per signed `T₁` relation. Note L602 writes the same cubic
as `(n_i n_j m_a* + c.c.)`, and `z + conj z = 2 Re z`. Both displays are encoded. They
are not proved equal.

Note L625–L627 puts `μ = |C| η² / a₂` and drops `O(η⁶)` into `D` "at leading order".
The identity proved here keeps that remainder explicit:
`b_eff = (36 b₁ + 6 b₂) − 15 C² / a₂`.
-/
public import Mathlib

@[expose] public section

namespace ExistenceSystem.Landau

/-- Note L613: `a₁(T) = α₁ (T − T₁*) / T₁*`. -/
noncomputable def a1OfTemp (α1 T Tstar : ℝ) : ℝ :=
  α1 * (T - Tstar) / Tstar

/-- Note L602: `z + conj z = 2 Re z`. This is the complex-conjugate display. -/
theorem cc_eq_two_re (z : ℂ) : z + star z = (2 : ℂ) * (z.re : ℂ) := by
  rw [Complex.star_def, Complex.ext_iff]
  refine ⟨?_, ?_⟩
  · simp [Complex.add_re, Complex.conj_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    ring
  · simp [Complex.add_im, Complex.conj_im, Complex.mul_im, Complex.ofReal_im]

/-- Note L619: one signed `T₁` contribution `η² μ cos(θᵢ + θⱼ − χ_a)`. -/
noncomputable def t1Cos (η μ θ : ℝ) : ℝ :=
  η ^ 2 * μ * Real.cos θ

/-- Note L619: one signed `T₂` contribution `μ³ cos(χ_a + χ_b + χ_c)`. -/
noncomputable def t2Cos (μ θ : ℝ) : ℝ :=
  μ ^ 3 * Real.cos θ

/-- Quadratic shell sum, before the common-modulus specialisation. `sn`, `sm` are `|n|²`, `|m|²`. -/
noncomputable def shellQuad (a1 a2 : ℝ) (sn : Fin 6 → ℝ) (sm : Fin 15 → ℝ) : ℝ :=
  a1 * ∑ i, sn i + a2 * ∑ a, sm a

theorem shellQuad_uniform (a1 a2 η μ : ℝ) (sn : Fin 6 → ℝ) (sm : Fin 15 → ℝ)
    (hn : ∀ i, sn i = η ^ 2) (hm : ∀ a, sm a = μ ^ 2) :
    shellQuad a1 a2 sn sm = 6 * a1 * η ^ 2 + 15 * a2 * μ ^ 2 := by
  simp only [shellQuad, hn, hm, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  ring

/-- Quartic shell sum of Note L604. -/
noncomputable def shellQuartic (b1 b2 b3 b4 b5 : ℝ) (sn : Fin 6 → ℝ) (sm : Fin 15 → ℝ) : ℝ :=
  b1 * (∑ i, sn i) ^ 2 + b2 * ∑ i, sn i ^ 2
    + b3 * (∑ i, sn i) * (∑ a, sm a)
    + b4 * (∑ a, sm a) ^ 2 + b5 * ∑ a, sm a ^ 2

theorem shellQuartic_uniform (b1 b2 b3 b4 b5 η μ : ℝ) (sn : Fin 6 → ℝ) (sm : Fin 15 → ℝ)
    (hn : ∀ i, sn i = η ^ 2) (hm : ∀ a, sm a = μ ^ 2) :
    shellQuartic b1 b2 b3 b4 b5 sn sm =
      (36 * b1 + 6 * b2) * η ^ 4 + 90 * b3 * η ^ 2 * μ ^ 2
        + (225 * b4 + 15 * b5) * μ ^ 4 := by
  simp only [shellQuartic, hn, hm, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  ring

/-- Note L619, saturated against the sign of `C`: each cosine satisfies `C cos = −|C|`,
and thirty signed relations sum to `−30 |C| η² μ`. -/
theorem t1_saturated (C η μ : ℝ) (cosθ : Fin 30 → ℝ) (h : ∀ i, C * cosθ i = -|C|) :
    ∑ i : Fin 30, C * (η ^ 2 * μ * cosθ i) = -30 * |C| * η ^ 2 * μ := by
  have h' : ∀ i, C * (η ^ 2 * μ * cosθ i) = -|C| * η ^ 2 * μ := by
    intro i
    calc
      C * (η ^ 2 * μ * cosθ i) = C * cosθ i * η ^ 2 * μ := by ring
      _ = -|C| * η ^ 2 * μ := by rw [h i]
  simp_rw [h', Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  ring

/-- The same saturation for the twenty signed `T₂` relations and `C'`. -/
theorem t2_saturated (C' μ : ℝ) (cosχ : Fin 20 → ℝ) (h : ∀ i, C' * cosχ i = -|C'|) :
    ∑ i : Fin 20, C' * (μ ^ 3 * cosχ i) = -20 * |C'| * μ ^ 3 := by
  have h' : ∀ i, C' * (μ ^ 3 * cosχ i) = -|C'| * μ ^ 3 := by
    intro i
    calc
      C' * (μ ^ 3 * cosχ i) = C' * cosχ i * μ ^ 3 := by ring
      _ = -|C'| * μ ^ 3 := by rw [h i]
  simp_rw [h', Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  ring

/-- One summand of the uniform-sector density at Note L621. -/
inductive JTerm
  | quadN
  | quadM
  | cubicT1
  | cubicT2
  | quartNN
  | quartN4
  | quartNM
  | quartMM
  | quartM4
  | sextic
  deriving DecidableEq

def termEquiv : JTerm ≃ Fin 10 where
  toFun
    | .quadN => 0
    | .quadM => 1
    | .cubicT1 => 2
    | .cubicT2 => 3
    | .quartNN => 4
    | .quartN4 => 5
    | .quartNM => 6
    | .quartMM => 7
    | .quartM4 => 8
    | .sextic => 9
  invFun
    | 0 => .quadN
    | 1 => .quadM
    | 2 => .cubicT1
    | 3 => .cubicT2
    | 4 => .quartNN
    | 5 => .quartN4
    | 6 => .quartNM
    | 7 => .quartMM
    | 8 => .quartM4
    | 9 => .sextic
  left_inv t := by cases t <;> rfl
  right_inv i := by fin_cases i <;> rfl

instance : Fintype JTerm :=
  Fintype.ofEquiv (Fin 10) termEquiv.symm

/-- Note L621, term by term. -/
noncomputable def evalTerm (a1 a2 C C' b1 b2 b3 b4 b5 D η μ : ℝ) : JTerm → ℝ
  | .quadN => 6 * a1 * η ^ 2
  | .quadM => 15 * a2 * μ ^ 2
  | .cubicT1 => -30 * |C| * η ^ 2 * μ
  | .cubicT2 => -20 * |C'| * μ ^ 3
  | .quartNN => 36 * b1 * η ^ 4
  | .quartN4 => 6 * b2 * η ^ 4
  | .quartNM => 90 * b3 * η ^ 2 * μ ^ 2
  | .quartMM => 225 * b4 * μ ^ 4
  | .quartM4 => 15 * b5 * μ ^ 4
  | .sextic => D * η ^ 6

/-- The uniform-sector density `J / |Ω|` at Note L621. -/
noncomputable def uniformDensity
    (a1 a2 C C' b1 b2 b3 b4 b5 D η μ : ℝ) : ℝ :=
  6 * a1 * η ^ 2 + 15 * a2 * μ ^ 2 - 30 * |C| * η ^ 2 * μ - 20 * |C'| * μ ^ 3
    + (36 * b1 + 6 * b2) * η ^ 4 + 90 * b3 * η ^ 2 * μ ^ 2
    + (225 * b4 + 15 * b5) * μ ^ 4 + D * η ^ 6

private lemma sum_terms {M : Type*} [AddCommMonoid M] (f : JTerm → M) :
    ∑ t, f t =
      f .quadN + f .quadM + f .cubicT1 + f .cubicT2 + f .quartNN + f .quartN4 + f .quartNM
        + f .quartMM + f .quartM4 + f .sextic := by
  rw [← termEquiv.symm.sum_comp f]
  repeat rw [Fin.sum_univ_succ]
  simp [termEquiv, add_zero, ← add_assoc]

theorem sum_evalTerm (a1 a2 C C' b1 b2 b3 b4 b5 D η μ : ℝ) :
    ∑ t, evalTerm a1 a2 C C' b1 b2 b3 b4 b5 D η μ t =
      uniformDensity a1 a2 C C' b1 b2 b3 b4 b5 D η μ := by
  rw [sum_terms]
  simp only [evalTerm, uniformDensity]
  ring

/-- `J = |Ω| · (J/|Ω|)`. `Ω` is not given a shape, so `|Ω|` is a scalar parameter. -/
noncomputable def sectorJ (vol dens : ℝ) : ℝ :=
  vol * dens

theorem sectorJ_div_vol (vol dens : ℝ) (h : vol ≠ 0) : sectorJ vol dens / vol = dens := by
  simp [sectorJ]
  field_simp [h]

/-- Note L627: `b_eff = (36 b₁ + 6 b₂) − 15 C² / a₂`. -/
noncomputable def bEff (a2 C b1 b2 : ℝ) : ℝ :=
  (36 * b1 + 6 * b2) - 15 * C ^ 2 / a2

/-- The monomials L621 drops into `D` only "at leading order". They stay here. -/
noncomputable def higherTerms (C' b3 b4 b5 η μ : ℝ) : ℝ :=
  -20 * |C'| * μ ^ 3 + 90 * b3 * η ^ 2 * μ ^ 2 + (225 * b4 + 15 * b5) * μ ^ 4

/-- The exact `η²` / `η⁴` identity under `μ = |C| η² / a₂`. For real `C`, `C² = |C|²`. -/
theorem slave_exact (a1 a2 C b1 b2 η μ : ℝ) (ha2 : a2 ≠ 0) (hμ : μ = |C| * η ^ 2 / a2) :
    6 * a1 * η ^ 2 + 15 * a2 * μ ^ 2 - 30 * |C| * η ^ 2 * μ + (36 * b1 + 6 * b2) * η ^ 4 =
      6 * a1 * η ^ 2 + bEff a2 C b1 b2 * η ^ 4 := by
  rw [hμ, bEff, ← sq_abs]
  field_simp [ha2]
  simp_rw [sq_abs C, sq_abs η]
  ring

theorem uniform_slave (a1 a2 C C' b1 b2 b3 b4 b5 D η μ : ℝ) (ha2 : a2 ≠ 0)
    (hμ : μ = |C| * η ^ 2 / a2) :
    uniformDensity a1 a2 C C' b1 b2 b3 b4 b5 D η μ =
      6 * a1 * η ^ 2 + bEff a2 C b1 b2 * η ^ 4 + D * η ^ 6
        + higherTerms C' b3 b4 b5 η μ := by
  have h := slave_exact a1 a2 C b1 b2 η μ ha2 hμ
  calc
    uniformDensity a1 a2 C C' b1 b2 b3 b4 b5 D η μ
        = (6 * a1 * η ^ 2 + 15 * a2 * μ ^ 2 - 30 * |C| * η ^ 2 * μ + (36 * b1 + 6 * b2) * η ^ 4)
          + higherTerms C' b3 b4 b5 η μ + D * η ^ 6 := by
        simp only [uniformDensity, higherTerms]
        ring
    _ = 6 * a1 * η ^ 2 + bEff a2 C b1 b2 * η ^ 4 + D * η ^ 6
          + higherTerms C' b3 b4 b5 η μ := by
        rw [h]
        ring

end ExistenceSystem.Landau

end
