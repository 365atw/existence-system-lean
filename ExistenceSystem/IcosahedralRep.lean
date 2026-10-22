module

/-
Character data for the two real three-dimensional irreps of the icosahedral group.

Note L510–L514: "Y ≅ A₅ has exactly two inequivalent real three-dimensional irreps,
Γ₃ and Γ₃', interchanged by σ. On the classes (E, 12 C₅, 12 C₅², 20 C₃, 15 C₂):
Γ₃ = (3, φ, 1−φ, 0, −1), Γ₃' = (3, 1−φ, φ, 0, −1)."

The isomorphism `Y ≅ A₅` and the action of `Y` on `ℤ⁶` are named in the Note and not
constructed there (map, §6a U21). This module records the character values she writes,
the interchange by σ, and the character inner products. It does not build the sixty
matrices.
-/
public import ExistenceSystem.Quadratic

@[expose] public section

open scoped QuadraticAlgebra

namespace ExistenceSystem.IcosahedralRep

open ExistenceSystem.Quadratic

/-- Conjugacy classes named at Note L510. `Class` is a Lean keyword, so this is `IcosaClass`. -/
inductive IcosaClass
  | e
  | c5
  | c5sq
  | c3
  | c2
  deriving DecidableEq

def classEquiv : IcosaClass ≃ Fin 5 where
  toFun
    | .e => 0
    | .c5 => 1
    | .c5sq => 2
    | .c3 => 3
    | .c2 => 4
  invFun
    | 0 => .e
    | 1 => .c5
    | 2 => .c5sq
    | 3 => .c3
    | 4 => .c2
  left_inv t := by cases t <;> rfl
  right_inv i := by fin_cases i <;> rfl

instance : Fintype IcosaClass :=
  Fintype.ofEquiv (Fin 5) classEquiv.symm

/-- Class sizes `(1, 12, 12, 20, 15)`. They sum to `|A₅| = 60`. -/
def classSize : IcosaClass → ℕ
  | .e => 1
  | .c5 => 12
  | .c5sq => 12
  | .c3 => 20
  | .c2 => 15

theorem classSize_sum : ∑ c, classSize c = 60 := by
  decide

/-- Note L512: `Γ₃ = (3, φ, 1−φ, 0, −1)`, with `φ` read as `ω` in `ℚ(√5)`. -/
def chi3 : IcosaClass → K
  | .e => 3
  | .c5 => ω
  | .c5sq => 1 - ω
  | .c3 => 0
  | .c2 => -1

/-- Note L512: `Γ₃' = (3, 1−φ, φ, 0, −1)`. -/
def chi3' : IcosaClass → K
  | .e => 3
  | .c5 => 1 - ω
  | .c5sq => ω
  | .c3 => 0
  | .c2 => -1

private lemma sum_classes {M : Type*} [AddCommMonoid M] (f : IcosaClass → M) :
    ∑ c, f c = f .e + f .c5 + f .c5sq + f .c3 + f .c2 := by
  rw [← classEquiv.symm.sum_comp f]
  repeat rw [Fin.sum_univ_succ]
  simp [classEquiv, add_zero, ← add_assoc]

set_option linter.unusedSimpArgs false in
set_option linter.unnecessarySeqFocus false in
/-- Note L510: the two irreps are interchanged by σ. `σ = star` on `ℚ(√5)`. -/
theorem star_chi3 (c : IcosaClass) : star (chi3 c) = chi3' c := by
  cases c <;>
    ext <;>
      simp [chi3, chi3', QuadraticAlgebra.re_star, QuadraticAlgebra.im_star,
        QuadraticAlgebra.re_sub, QuadraticAlgebra.im_sub, QuadraticAlgebra.re_add,
        QuadraticAlgebra.im_add, QuadraticAlgebra.re_neg, QuadraticAlgebra.im_neg,
        QuadraticAlgebra.re_one, QuadraticAlgebra.im_one, QuadraticAlgebra.re_omega,
        QuadraticAlgebra.im_omega, QuadraticAlgebra.re_natCast, QuadraticAlgebra.im_natCast,
        QuadraticAlgebra.re_zero, QuadraticAlgebra.im_zero]

/-- The two real embeddings swap with σ, so `ι_ψ ∘ Γ₃ = ι_φ ∘ Γ₃'`. -/
theorem embedPsi_chi3 (c : IcosaClass) : embedPsi (chi3 c) = embedPhi (chi3' c) := by
  rw [embedPsi_eq_embedPhi_star, star_chi3]

/-- Character inner product `(1/60) ∑ |class| χ ψ` in `ℚ(√5)`. -/
noncomputable def charInner (χ ψ : IcosaClass → K) : K :=
  algebraMap ℚ K (60 : ℚ)⁻¹ *
    ∑ c, algebraMap ℚ K (classSize c : ℚ) * (χ c * ψ c)

lemma omega_sq : (ω : K) * ω = 1 + ω := by
  rw [QuadraticAlgebra.omega_mul_omega_eq_add]
  simp [Algebra.smul_def]

lemma one_sub_omega_sq : ((1 : K) - ω) * (1 - ω) = 2 - ω := by
  calc
    ((1 : K) - ω) * (1 - ω) = 1 - ω - ω + ω * ω := by ring
    _ = 1 - ω - ω + (1 + ω) := by rw [omega_sq]
    _ = 2 - ω := by ring

lemma omega_mul_one_sub : (ω : K) * (1 - ω) = -1 := by
  calc
    (ω : K) * (1 - ω) = ω - ω * ω := by ring
    _ = ω - (1 + ω) := by rw [omega_sq]
    _ = -1 := by ring

set_option linter.unusedSimpArgs false in
set_option linter.unnecessarySeqFocus false in
theorem charInner_chi3_self : charInner chi3 chi3 = 1 := by
  have hsum : ∑ c, algebraMap ℚ K (classSize c : ℚ) * (chi3 c * chi3 c) = algebraMap ℚ K 60 := by
    rw [sum_classes]
    simp only [classSize, chi3, omega_sq, one_sub_omega_sq]
    apply QuadraticAlgebra.ext <;>
      simp [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, QuadraticAlgebra.re_add,
        QuadraticAlgebra.im_add, QuadraticAlgebra.re_sub, QuadraticAlgebra.im_sub,
        QuadraticAlgebra.re_neg, QuadraticAlgebra.im_neg, QuadraticAlgebra.re_one,
        QuadraticAlgebra.im_one, QuadraticAlgebra.re_zero, QuadraticAlgebra.im_zero,
        QuadraticAlgebra.re_omega, QuadraticAlgebra.im_omega, QuadraticAlgebra.re_natCast,
        QuadraticAlgebra.im_natCast, ← QuadraticAlgebra.C_eq_algebraMap, QuadraticAlgebra.re_C,
        QuadraticAlgebra.im_C] <;>
      norm_num
  unfold charInner
  rw [hsum, ← map_mul, inv_mul_cancel₀ (by norm_num : (60 : ℚ) ≠ 0), map_one]

set_option linter.unusedSimpArgs false in
set_option linter.unnecessarySeqFocus false in
theorem charInner_chi3_cross : charInner chi3 chi3' = 0 := by
  have hsum : ∑ c, algebraMap ℚ K (classSize c : ℚ) * (chi3 c * chi3' c) = 0 := by
    rw [sum_classes]
    simp only [classSize, chi3, chi3', omega_mul_one_sub]
    have hcomm : ((1 : K) - ω) * ω = ω * ((1 : K) - ω) := by ring
    rw [hcomm, omega_mul_one_sub]
    apply QuadraticAlgebra.ext <;>
      simp [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, QuadraticAlgebra.re_add,
        QuadraticAlgebra.im_add, QuadraticAlgebra.re_neg, QuadraticAlgebra.im_neg,
        QuadraticAlgebra.re_one, QuadraticAlgebra.im_one, QuadraticAlgebra.re_zero,
        QuadraticAlgebra.im_zero, QuadraticAlgebra.re_natCast, QuadraticAlgebra.im_natCast,
        ← QuadraticAlgebra.C_eq_algebraMap, QuadraticAlgebra.re_C, QuadraticAlgebra.im_C] <;>
      norm_num
  unfold charInner
  rw [hsum, mul_zero]

end ExistenceSystem.IcosahedralRep

end
