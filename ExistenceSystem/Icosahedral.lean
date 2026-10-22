module

/-
The icosahedral star and its lift, over ℤ[φ].

Note L482–L486: "Take the six five-fold axis vectors of the icosahedron — its vertex
star, up to sign: Q₁ = (0, 1, φ), …, Q₆ = (φ, 0, −1), each divided by √(2+φ) so that
|Qᵢ| = 1. (Note 1 + φ² = 2 + φ = √5 φ exactly.)"

Note L492: "Qᵢ · Qⱼ = ±1/√5 (i ≠ j)".

Note L498: "Qᵢ^⊥ = σ(Qᵢ) / √(3−φ)", and "|σ(Qᵢ)| / |Qᵢ|_unnorm = 1/φ exactly".
The symbol Qᵢ in that ratio is the unnormalised tuple displayed at L484; σ acts
slot by slot on those coordinates (map, G2, U17).

Note L504–L508: "Gᵢ = 2^{−1/2} (Qᵢ, Qᵢ^⊥)", "A the 6×6 matrix with rows Gᵢ",
"AAᵀ = AᵀA = I", "ℒ := A(ℤ⁶)", and "the determinant of the unnormalized embedding
is 40√5 ≠ 0, so π_∥ ⊕ π_⊥ is a linear isomorphism".

The floating-point residuals on those lines are corroboration. The theorems below
are the exact statements beside them.
-/
public import ExistenceSystem.Quadratic

@[expose] public section

open Real Matrix
open scoped goldenRatio QuadraticAlgebra Matrix

namespace ExistenceSystem.Icosahedral

open ExistenceSystem.Quadratic

/-! ## Unnormalised coordinates in ℤ[φ] -/

/-- Unnormalised five-fold axes. Note L484, before the division by `√(2+φ)`. -/
def qRaw : Fin 6 → Fin 3 → Zphi
  | 0, 0 => 0
  | 0, 1 => 1
  | 0, 2 => ω
  | 1, 0 => 0
  | 1, 1 => -1
  | 1, 2 => ω
  | 2, 0 => 1
  | 2, 1 => ω
  | 2, 2 => 0
  | 3, 0 => -1
  | 3, 1 => ω
  | 3, 2 => 0
  | 4, 0 => ω
  | 4, 1 => 0
  | 4, 2 => 1
  | 5, 0 => ω
  | 5, 1 => 0
  | 5, 2 => -1

/-- Sign of the off-diagonal product `qᵢ · qⱼ = (sign i j) · φ`. Diagonal is unused. -/
def sign (i j : Fin 6) : ℤ :=
  match i.val, j.val with
  | 0, 1 | 1, 0 => 1
  | 0, 2 | 2, 0 => 1
  | 0, 3 | 3, 0 => 1
  | 0, 4 | 4, 0 => 1
  | 0, 5 | 5, 0 => -1
  | 1, 2 | 2, 1 => -1
  | 1, 3 | 3, 1 => -1
  | 1, 4 | 4, 1 => 1
  | 1, 5 | 5, 1 => -1
  | 2, 3 | 3, 2 => 1
  | 2, 4 | 4, 2 => 1
  | 2, 5 | 5, 2 => 1
  | 3, 4 | 4, 3 => -1
  | 3, 5 | 5, 3 => -1
  | 4, 5 | 5, 4 => 1
  | _, _ => 0

def qDot (i j : Fin 6) : Zphi :=
  qRaw i 0 * qRaw j 0 + qRaw i 1 * qRaw j 1 + qRaw i 2 * qRaw j 2

/-- `2 + ω`, the squared length `1 + φ² = 2 + φ` inside ℤ[φ]. -/
def sqLen : Zphi := ⟨2, 1⟩

def qExpected (i j : Fin 6) : Zphi :=
  if i = j then sqLen else ⟨0, sign i j⟩

theorem qDot_eq (i j : Fin 6) : qDot i j = qExpected i j := by
  fin_cases i <;> fin_cases j <;> rfl

theorem qDot_self (i : Fin 6) : qDot i i = sqLen := by
  simpa [qExpected] using qDot_eq i i

theorem qDot_off (i j : Fin 6) (hij : i ≠ j) : qDot i j = ⟨0, sign i j⟩ := by
  simpa [qExpected, hij] using qDot_eq i j

theorem sign_ne_zero_off (i j : Fin 6) (hij : i ≠ j) : sign i j = 1 ∨ sign i j = -1 := by
  fin_cases i <;> fin_cases j <;> simp_all [sign]

/-! ## The two real images -/

noncomputable def qVec (i : Fin 6) : Fin 3 → ℝ :=
  fun k => embedPhi (coeZphi (qRaw i k))

noncomputable def qVecPerp (i : Fin 6) : Fin 3 → ℝ :=
  fun k => embedPsi (coeZphi (qRaw i k))

theorem qVec_dot (i j : Fin 6) :
    dotProduct (qVec i) (qVec j) = embedPhi (coeZphi (qDot i j)) := by
  have hmul (x y : Zphi) :
      embedPhi (coeZphi x) * embedPhi (coeZphi y) = embedPhi (coeZphi (x * y)) := by
    rw [← map_mul, ← map_mul]
  have hadd (x y : Zphi) :
      embedPhi (coeZphi x) + embedPhi (coeZphi y) = embedPhi (coeZphi (x + y)) := by
    rw [← map_add, ← map_add]
  rw [dotProduct, Fin.sum_univ_three, qVec, qVec, qVec, qVec, qVec, qVec, hmul, hmul, hmul,
    hadd, hadd]
  rfl

theorem qVecPerp_dot (i j : Fin 6) :
    dotProduct (qVecPerp i) (qVecPerp j) = embedPsi (coeZphi (qDot i j)) := by
  have hmul (x y : Zphi) :
      embedPsi (coeZphi x) * embedPsi (coeZphi y) = embedPsi (coeZphi (x * y)) := by
    rw [← map_mul, ← map_mul]
  have hadd (x y : Zphi) :
      embedPsi (coeZphi x) + embedPsi (coeZphi y) = embedPsi (coeZphi (x + y)) := by
    rw [← map_add, ← map_add]
  rw [dotProduct, Fin.sum_univ_three, qVecPerp, qVecPerp, qVecPerp, qVecPerp, qVecPerp,
    qVecPerp, hmul, hmul, hmul, hadd, hadd]
  rfl

private theorem embed_sqLen : embedPhi (coeZphi sqLen) = 2 + φ := by
  simp [sqLen, embedPhi_coeZphi]

private theorem embedPsi_sqLen : embedPsi (coeZphi sqLen) = 2 + ψ := by
  simp [sqLen, embedPsi_coeZphi]

theorem qVec_norm_sq (i : Fin 6) : dotProduct (qVec i) (qVec i) = 2 + φ := by
  rw [qVec_dot, qDot_self, embed_sqLen]

theorem qVecPerp_norm_sq (i : Fin 6) : dotProduct (qVecPerp i) (qVecPerp i) = 2 + ψ := by
  rw [qVecPerp_dot, qDot_self, embedPsi_sqLen]

theorem two_add_phi_eq_sqrt5_mul_phi : 2 + φ = √5 * φ := by
  have hsub : φ - ψ = √5 := goldenRatio_sub_goldenConj
  have hψ : ψ = 1 - φ := (one_sub_goldenConj).symm
  have hdiff : φ - ψ = 2 * φ - 1 := by rw [hψ]; ring
  have hmul : (2 * φ - 1) * φ = 2 * φ ^ 2 - φ := by ring
  calc
    2 + φ = 2 * (φ + 1) - φ := by ring
    _ = 2 * φ ^ 2 - φ := by rw [goldenRatio_sq]
    _ = (2 * φ - 1) * φ := by rw [hmul]
    _ = (φ - ψ) * φ := by rw [hdiff]
    _ = √5 * φ := by rw [hsub]

theorem phi_div_norm_sq : φ / (2 + φ) = 1 / √5 := by
  rw [two_add_phi_eq_sqrt5_mul_phi]
  have h5 : √5 ≠ 0 := by
    exact (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 5)).ne'
  field_simp [h5, goldenRatio_ne_zero]

theorem psi_div_conj_norm_sq : ψ / (2 + ψ) = -(1 / √5) := by
  have hsub : φ - ψ = √5 := goldenRatio_sub_goldenConj
  have hψ : √5 * ψ = -(2 + ψ) := by
    calc
      √5 * ψ = (φ - ψ) * ψ := by rw [hsub]
      _ = φ * ψ - ψ ^ 2 := by ring
      _ = -1 - (ψ + 1) := by rw [goldenRatio_mul_goldenConj, goldenConj_sq]
      _ = -(2 + ψ) := by ring
  have h5 : √5 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 5)).ne'
  have hden : 2 + ψ ≠ 0 := by
    have hψeq : ψ = 1 - φ := (one_sub_goldenConj).symm
    linarith [hψeq, goldenRatio_lt_two]
  calc
    ψ / (2 + ψ) = (√5 * ψ) / (√5 * (2 + ψ)) := by
      rw [← mul_div_mul_left ψ (2 + ψ) h5]
    _ = (-(2 + ψ)) / (√5 * (2 + ψ)) := by rw [hψ]
    _ = -((2 + ψ) / (√5 * (2 + ψ))) := by rw [neg_div]
    _ = -((2 + ψ) / ((2 + ψ) * √5)) := by rw [mul_comm √5 (2 + ψ)]
    _ = -(√5)⁻¹ := by rw [div_mul_cancel_left₀ hden]
    _ = -(1 / √5) := by rw [inv_eq_one_div]

/-- Note L498: `|σ(Qᵢ)| / |Qᵢ|_unnorm = 1/φ`. Lengths of the two real images of `qᵢ`. -/
theorem length_ratio (i : Fin 6) :
    Real.sqrt (dotProduct (qVecPerp i) (qVecPerp i)) /
        Real.sqrt (dotProduct (qVec i) (qVec i)) = 1 / φ := by
  rw [qVec_norm_sq, qVecPerp_norm_sq]
  have hφpos : 0 < 2 + φ := by linarith [goldenRatio_pos]
  have hψpos : 0 < 2 + ψ := by
    have : ψ = 1 - φ := (one_sub_goldenConj).symm
    linarith [this, goldenRatio_lt_two]
  have hsq : (2 + ψ) / (2 + φ) = 1 / φ ^ 2 := by
    have hcross : (2 + ψ) * φ ^ 2 = 2 + φ := by
      have hψ : ψ = 1 - φ := one_sub_goldenConj.symm
      have hsq : φ ^ 2 = φ + 1 := goldenRatio_sq
      calc
        (2 + ψ) * φ ^ 2 = (3 - φ) * (φ + 1) := by
          rw [hψ, hsq]
          generalize φ = x
          ring
        _ = 3 * (φ + 1) - φ * (φ + 1) := by
          generalize φ = x
          ring
        _ = 3 * φ + 3 - (φ ^ 2 + φ) := by
          generalize φ = x
          ring
        _ = 3 * φ + 3 - (φ + 1 + φ) := by rw [hsq]
        _ = 2 + φ := by
          generalize φ = x
          ring
    rw [div_eq_div_iff hφpos.ne' (pow_ne_zero 2 goldenRatio_ne_zero)]
    linarith
  rw [← Real.sqrt_div hψpos.le, hsq, Real.sqrt_div (by positivity),
    Real.sqrt_sq goldenRatio_pos.le, Real.sqrt_one]

/-! ## Normalised star. Note L486 and the boxed product at L492. -/

noncomputable def Q (i : Fin 6) : Fin 3 → ℝ :=
  (Real.sqrt (2 + φ))⁻¹ • qVec i

noncomputable def Qperp (i : Fin 6) : Fin 3 → ℝ :=
  (Real.sqrt (3 - φ))⁻¹ • qVecPerp i

theorem three_sub_phi_eq : 3 - φ = 2 + ψ := by
  have : ψ = 1 - φ := (one_sub_goldenConj).symm
  linarith

private theorem sqrt_norm_sq_inv :
    (Real.sqrt (2 + φ))⁻¹ * (Real.sqrt (2 + φ))⁻¹ = (2 + φ)⁻¹ := by
  rw [← mul_inv, ← sq, Real.sq_sqrt (by linarith [goldenRatio_pos])]

private theorem sqrt_perp_inv :
    (Real.sqrt (3 - φ))⁻¹ * (Real.sqrt (3 - φ))⁻¹ = (2 + ψ)⁻¹ := by
  have hnonneg : 0 ≤ 2 + ψ := by
    have hψ : ψ = 1 - φ := (one_sub_goldenConj).symm
    linarith [hψ, goldenRatio_lt_two]
  rw [three_sub_phi_eq, ← mul_inv, ← sq, Real.sq_sqrt hnonneg]

theorem Q_dot_self (i : Fin 6) : dotProduct (Q i) (Q i) = 1 := by
  simp only [Q]
  rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc, sqrt_norm_sq_inv,
    qVec_norm_sq]
  exact inv_mul_cancel₀ (by linarith [goldenRatio_pos])

theorem Q_dot_off (i j : Fin 6) (hij : i ≠ j) :
    dotProduct (Q i) (Q j) = (sign i j : ℝ) / √5 := by
  simp only [Q]
  rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc, sqrt_norm_sq_inv,
    qVec_dot, qDot_off i j hij, embedPhi_coeZphi]
  simp only [Int.cast_zero, zero_add]
  have hre : (2 + φ)⁻¹ * ((sign i j : ℝ) * φ) = (sign i j : ℝ) * (φ / (2 + φ)) := by
    ring
  rw [hre, phi_div_norm_sq]
  ring

theorem Qperp_dot_self (i : Fin 6) : dotProduct (Qperp i) (Qperp i) = 1 := by
  simp only [Qperp]
  rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc, sqrt_perp_inv,
    qVecPerp_norm_sq]
  exact inv_mul_cancel₀ (by
    have hψ : ψ = 1 - φ := (one_sub_goldenConj).symm
    linarith [hψ, goldenRatio_lt_two])

theorem Qperp_dot_off (i j : Fin 6) (hij : i ≠ j) :
    dotProduct (Qperp i) (Qperp j) = -((sign i j : ℝ) / √5) := by
  simp only [Qperp]
  rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc, sqrt_perp_inv,
    qVecPerp_dot, qDot_off i j hij, embedPsi_coeZphi]
  simp only [Int.cast_zero, zero_add]
  have hre : (2 + ψ)⁻¹ * ((sign i j : ℝ) * ψ) = (sign i j : ℝ) * (ψ / (2 + ψ)) := by
    ring
  rw [hre, psi_div_conj_norm_sq]
  ring

/-! ## The lift. Note L504. -/

noncomputable def row (i : Fin 6) : Fin 6 → ℝ := fun j =>
  if h : (j.val : ℕ) < 3 then
    Q i ⟨j.val, h⟩ / Real.sqrt 2
  else
    Qperp i ⟨j.val - 3, by omega⟩ / Real.sqrt 2

private lemma row_par (i : Fin 6) (k : Fin 3) :
    row i (Fin.castLE (by omega : 3 ≤ 6) k) = Q i k / Real.sqrt 2 := by
  unfold row
  have hk : ((Fin.castLE (by omega : 3 ≤ 6) k).val : ℕ) < 3 := k.isLt
  exact dite_eq_left hk

private lemma row_perp (i : Fin 6) (k : Fin 3) :
    row i (Fin.natAdd 3 k) = Qperp i k / Real.sqrt 2 := by
  unfold row
  have hk : ¬ ((Fin.natAdd 3 k).val : ℕ) < 3 := by
    simp [Fin.natAdd]
  rw [dite_eq_right hk]
  apply congrArg (fun z : ℝ => z / Real.sqrt 2)
  apply congrArg (Qperp i)
  apply Fin.ext
  simp [Fin.natAdd]

private lemma half_mul (x y : ℝ) : (x / √2) * (y / √2) = (1 / 2) * (x * y) := by
  rw [div_mul_div_comm, ← sq, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  ring

theorem row_dot (i j : Fin 6) :
    dotProduct (row i) (row j) =
      (1 / 2) * (dotProduct (Q i) (Q j) + dotProduct (Qperp i) (Qperp j)) := by
  unfold dotProduct
  rw [Fin.sum_univ_six, Fin.sum_univ_three, Fin.sum_univ_three]
  have e0 : (0 : Fin 6) = Fin.castLE (by omega : 3 ≤ 6) (0 : Fin 3) := by
    apply Fin.ext; simp [Fin.castLE]
  have e1 : (1 : Fin 6) = Fin.castLE (by omega : 3 ≤ 6) (1 : Fin 3) := by
    apply Fin.ext; simp [Fin.castLE]
  have e2 : (2 : Fin 6) = Fin.castLE (by omega : 3 ≤ 6) (2 : Fin 3) := by
    apply Fin.ext; simp [Fin.castLE]
  have e3 : (3 : Fin 6) = Fin.natAdd 3 (0 : Fin 3) := by
    apply Fin.ext; simp [Fin.natAdd]
  have e4 : (4 : Fin 6) = Fin.natAdd 3 (1 : Fin 3) := by
    apply Fin.ext; simp [Fin.natAdd]
  have e5 : (5 : Fin 6) = Fin.natAdd 3 (2 : Fin 3) := by
    apply Fin.ext; simp [Fin.natAdd]
  rw [e0, e1, e2, e3, e4, e5]
  rw [row_par i 0, row_par j 0, row_par i 1, row_par j 1, row_par i 2, row_par j 2,
    row_perp i 0, row_perp j 0, row_perp i 1, row_perp j 1, row_perp i 2, row_perp j 2]
  rw [half_mul, half_mul, half_mul, half_mul, half_mul, half_mul]
  ring

/-- Rows of `Gᵢ` are orthonormal. Note L506: `AAᵀ = I`. -/
theorem row_orthonormal (i j : Fin 6) :
    dotProduct (row i) (row j) = if i = j then 1 else 0 := by
  rw [row_dot]
  by_cases hij : i = j
  · subst hij
    rw [Q_dot_self, Qperp_dot_self]
    norm_num
  · rw [Q_dot_off i j hij, Qperp_dot_off i j hij]
    simp [hij]

noncomputable def A : Matrix (Fin 6) (Fin 6) ℝ :=
  Matrix.of fun i j => row i j

/-- Note L506: `AAᵀ = I`. For a square matrix this is also `AᵀA = I`. -/
theorem A_mul_transpose : A * Aᵀ = 1 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, A, Matrix.of_apply, Matrix.one_apply]
  simpa [dotProduct] using row_orthonormal i j

theorem A_transpose_mul : Aᵀ * A = 1 :=
  mul_eq_one_comm.mp A_mul_transpose

/-- `ℒ := A(ℤ⁶)`, the integer combinations of the rows of `A`. Note L506. -/
noncomputable def lattice : Set (Fin 6 → ℝ) :=
  {v | ∃ n : Fin 6 → ℤ, v = fun j => ∑ i : Fin 6, (n i : ℝ) * row i j}

theorem mem_lattice_rows (n : Fin 6 → ℤ) :
    (fun j => ∑ i : Fin 6, (n i : ℝ) * row i j) ∈ lattice :=
  ⟨n, rfl⟩

/-! ## Unnormalised embedding and its determinant, Note L508. -/

noncomputable def rawM : Matrix (Fin 6) (Fin 6) ℝ :=
  !![0, 1, φ, 0, 1, ψ;
     0, -1, φ, 0, -1, ψ;
     1, φ, 0, 1, ψ, 0;
     -1, φ, 0, -1, ψ, 0;
     φ, 0, 1, ψ, 0, 1;
     φ, 0, -1, ψ, 0, -1]

/-- `π_∥` of a coefficient vector: the parallel block of the unnormalised embedding. -/
noncomputable def piParallel (c : Fin 6 → ℝ) : Fin 3 → ℝ :=
  fun k => ∑ i : Fin 6, c i * qVec i k

/-- `π_⊥` of a coefficient vector. -/
noncomputable def piPerp (c : Fin 6 → ℝ) : Fin 3 → ℝ :=
  fun k => ∑ i : Fin 6, c i * qVecPerp i k

theorem rawM_eq_images (i : Fin 6) (k : Fin 3) :
    rawM i ⟨k.val, by omega⟩ = qVec i k ∧
      rawM i ⟨k.val + 3, by omega⟩ = qVecPerp i k := by
  fin_cases i <;> fin_cases k <;>
    simp [rawM, qVec, qVecPerp, qRaw, embedPhi_coeZphi, embedPsi_coeZphi]

private noncomputable def pairE : Matrix (Fin 6) (Fin 6) ℝ :=
  !![1, 1, 0, 0, 0, 0;
     1, -1, 0, 0, 0, 0;
     0, 0, 1, 1, 0, 0;
     0, 0, 1, -1, 0, 0;
     0, 0, 0, 0, 1, 1;
     0, 0, 0, 0, 1, -1]

private noncomputable def paired : Matrix (Fin 6) (Fin 6) ℝ :=
  !![0, 0, 2 * φ, 0, 0, 2 * ψ;
     0, 2, 0, 0, 2, 0;
     0, 2 * φ, 0, 0, 2 * ψ, 0;
     2, 0, 0, 2, 0, 0;
     2 * φ, 0, 0, 2 * ψ, 0, 0;
     0, 0, 2, 0, 0, 2]

private noncomputable def pairedHalf : Matrix (Fin 6) (Fin 6) ℝ :=
  !![0, 0, φ, 0, 0, ψ;
     0, 1, 0, 0, 1, 0;
     0, φ, 0, 0, ψ, 0;
     1, 0, 0, 1, 0, 0;
     φ, 0, 0, ψ, 0, 0;
     0, 0, 1, 0, 0, 1]

private lemma pairE_mul_raw : pairE * rawM = paired := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pairE, rawM, paired, Matrix.mul_apply, Fin.sum_univ_six] <;> ring

private lemma paired_eq_two_smul : paired = (2 : ℝ) • pairedHalf := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [paired, pairedHalf, smul_eq_mul]

private noncomputable def bA : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1; φ, ψ]

private noncomputable def bC : Matrix (Fin 2) (Fin 2) ℝ := !![φ, ψ; 1, 1]

private lemma det_bA : bA.det = -√5 := by
  simp only [bA, Matrix.det_fin_two_of, one_mul]
  linarith [goldenRatio_sub_goldenConj]

private lemma det_bC : bC.det = √5 := by
  simp only [bC, Matrix.det_fin_two_of, mul_one]
  exact goldenRatio_sub_goldenConj

private def contig : Fin 2 × Fin 3 ≃ Fin 6 where
  toFun := fun p => ⟨p.1.val + 2 * p.2.val, by omega⟩
  invFun := fun n =>
    (⟨n.val % 2, by omega⟩, ⟨n.val / 2, by omega⟩)
  left_inv := by
    intro p
    ext <;> simp <;> omega
  right_inv := by
    intro n
    ext
    simpa using Nat.mod_add_div n.val 2

private noncomputable def blocks : Fin 3 → Matrix (Fin 2) (Fin 2) ℝ
  | 0 => bA
  | 1 => bA
  | 2 => bC

private noncomputable def blocked : Matrix (Fin 6) (Fin 6) ℝ :=
  (blockDiagonal blocks).reindex contig contig

private lemma det_blocked : blocked.det = 5 * √5 := by
  simp only [blocked, Matrix.det_reindex_self, Matrix.det_blockDiagonal]
  simp only [Fin.prod_univ_three, blocks, det_bA, det_bC]
  have hsq : √5 ^ 2 = (5 : ℝ) := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  calc
    (-√5) * (-√5) * √5 = (√5 * √5) * √5 := by ring
    _ = √5 ^ 2 * √5 := by ring
    _ = 5 * √5 := by rw [hsq]

/-- New row index ↦ old row of `pairedHalf`. -/
private def rowFwd : Fin 6 → Fin 6
  | 0 => 3
  | 1 => 4
  | 2 => 1
  | 3 => 2
  | 4 => 0
  | 5 => 5

/-- New column index ↦ old column of `pairedHalf`. -/
private def colFwd : Fin 6 → Fin 6
  | 0 => 0
  | 1 => 3
  | 2 => 1
  | 3 => 4
  | 4 => 2
  | 5 => 5

private noncomputable def rowPerm : Equiv.Perm (Fin 6) :=
  Equiv.ofBijective rowFwd (by decide)

private noncomputable def colPerm : Equiv.Perm (Fin 6) :=
  Equiv.ofBijective colFwd (by decide)

private lemma permuted_eq_blocked :
    ((pairedHalf.submatrix rowPerm id).submatrix id colPerm) = blocked := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blocked, blockDiagonal, blocks, bA, bC, contig, pairedHalf, rowPerm, colPerm,
      rowFwd, colFwd, Matrix.submatrix_apply, Matrix.reindex_apply]

private lemma det_pairE : pairE.det = -8 := by
  let b : Fin 3 → Matrix (Fin 2) (Fin 2) ℝ := fun _ => !![1, 1; 1, -1]
  have hdet : ((blockDiagonal b).reindex contig contig).det = -8 := by
    simp only [Matrix.det_reindex_self, Matrix.det_blockDiagonal, Fin.prod_univ_three, b,
      Matrix.det_fin_two_of]
    norm_num
  have heq : pairE = (blockDiagonal b).reindex contig contig := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pairE, blockDiagonal, b, contig, Matrix.reindex_apply]
  rw [heq, hdet]

/-- Note L508: the determinant of the unnormalised embedding is `40√5`. -/
theorem det_rawM : rawM.det = 40 * √5 := by
  have hmul : pairE.det * rawM.det = paired.det := by
    rw [← Matrix.det_mul, pairE_mul_raw]
  have hscale : paired.det = 64 * pairedHalf.det := by
    rw [paired_eq_two_smul, Matrix.det_smul, Fintype.card_fin]
    norm_num
  have hrow : (pairedHalf.submatrix rowPerm id).det =
      (Equiv.Perm.sign rowPerm : ℝ) * pairedHalf.det :=
    Matrix.det_permute rowPerm pairedHalf
  have hcol : ((pairedHalf.submatrix rowPerm id).submatrix id colPerm).det =
      (Equiv.Perm.sign colPerm : ℝ) * (pairedHalf.submatrix rowPerm id).det :=
    Matrix.det_permute' colPerm (pairedHalf.submatrix rowPerm id)
  rw [permuted_eq_blocked] at hcol
  have hblocked : blocked.det =
      (Equiv.Perm.sign colPerm : ℝ) * (Equiv.Perm.sign rowPerm : ℝ) * pairedHalf.det := by
    rw [hcol, hrow, mul_assoc]
  have hsq (σ : Equiv.Perm (Fin 6)) :
      (Equiv.Perm.sign σ : ℝ) * Equiv.Perm.sign σ = 1 := by
    exact_mod_cast Int.units_coe_mul_self (Equiv.Perm.sign σ)
  have hsigns : (Equiv.Perm.sign rowPerm : ℤ) * (Equiv.Perm.sign colPerm : ℤ) = -1 := by
    decide
  have hsign : (Equiv.Perm.sign rowPerm : ℝ) * (Equiv.Perm.sign colPerm : ℝ) = -1 := by
    exact_mod_cast hsigns
  have hhalf : pairedHalf.det = -blocked.det := by
    calc
      pairedHalf.det = ((Equiv.Perm.sign rowPerm : ℝ) * Equiv.Perm.sign rowPerm) *
          ((Equiv.Perm.sign colPerm : ℝ) * Equiv.Perm.sign colPerm) * pairedHalf.det := by
        rw [hsq rowPerm, hsq colPerm]
        ring
      _ = (Equiv.Perm.sign rowPerm : ℝ) * (Equiv.Perm.sign colPerm : ℝ) *
          ((Equiv.Perm.sign colPerm : ℝ) * (Equiv.Perm.sign rowPerm : ℝ) * pairedHalf.det) := by
        ring
      _ = (Equiv.Perm.sign rowPerm : ℝ) * (Equiv.Perm.sign colPerm : ℝ) * blocked.det := by
        rw [← hblocked]
      _ = -blocked.det := by
        rw [hsign]
        ring
  rw [det_blocked] at hhalf
  have hpairdet : paired.det = 64 * (-5 * √5) := by
    rw [hscale, hhalf]
    ring
  rw [det_pairE] at hmul
  have h8 : (-8 : ℝ) ≠ 0 := by norm_num
  apply (mul_right_inj' h8).mp
  calc
    (-8 : ℝ) * rawM.det = paired.det := hmul
    _ = 64 * (-5 * √5) := hpairdet
    _ = (-8) * (40 * √5) := by ring

theorem det_rawM_ne_zero : rawM.det ≠ 0 := by
  rw [det_rawM]
  positivity

/-- `π_∥ ⊕ π_⊥`, as the linear map whose matrix is the unnormalised embedding, is an isomorphism.
Note L508. -/
theorem piJoin_bijective : Function.Bijective rawM.mulVec := by
  have hU : IsUnit rawM := by
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
    exact det_rawM_ne_zero
  exact ⟨Matrix.mulVec_injective_iff_isUnit.mpr hU,
    Matrix.mulVec_surjective_iff_isUnit.mpr hU⟩

end ExistenceSystem.Icosahedral

end
