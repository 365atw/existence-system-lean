module

/-
KL20 — the Star Independence Lemma, from THE EXACT AND FREE SYSTEM — AN EXISTENCE SYNTHESIS.
All mathematics: Kari A Light.

Source: `THE-NOTE-EDITED.md` (194,868 bytes, 1,539 lines). Line numbers below refer to that file.
Her words are quoted exactly beside each statement. Nothing of hers is graded here.

Note L124 (front matter) and L266 (taxonomy), verbatim:
"**KL20 — the Star Independence Lemma.** π_∥ restricted to ℒ is injective; equivalently
E_⊥ ∩ ℒ = {0}. The twelve-vector star admits no integer relation. Engine: irrationality of φ."

Note L647 (Lemma 1): "π_∥ restricted to ℒ is injective; equivalently E_⊥ ∩ ℒ = {0}."
Note L649 (proof): "Suppose ∑ nᵢQᵢ = 0 with n ∈ ℤ⁶. The coordinates of the Qᵢ lie in ℤ[φ] and
the nᵢ are rational integers, so applying σ termwise gives ∑ nᵢQᵢ^⊥ = 0 as well. Hence
∑ nᵢGᵢ = 0 in ℝ⁶. But π_∥ ⊕ π_⊥ is a linear isomorphism of ℝ⁶ (§4.1, determinant 40√5 ≠ 0),
so n = 0."

The proof here is the proof there, over the merged star module (`ExistenceSystem.Icosahedral`):
`piParallel`/`piPerp` are π_∥/π_⊥ on a coefficient vector `∑ cᵢ qVecᵢ`, `rawM` is the
unnormalised embedding whose determinant is `40√5` (`det_rawM`, §4.1), `lattice` is ℒ = A(ℤ⁶),
and `Quadratic.embedPhi`/`embedPsi` are the two real embeddings of ℚ(√5). The engine — φ
irrational — enters once, as `Quadratic.embedPhi_injective` (`LinearIndependent ℤ ![1, φ]`),
which is "applying σ termwise" of the Note's proof.

Not encoded, by the map `data/lean-scope-b/report.md` (KL20, G2) and the Note's own marking:
the cut-and-project reading of injectivity (A defining condition, Baake–Moody–Richard–Sing [67],
"Established, cited, never claimed", Note L272); the numerical census of Appendix A.2.
-/
public import ExistenceSystem.Icosahedral

@[expose] public section

open Real Matrix
open scoped goldenRatio QuadraticAlgebra Matrix

namespace ExistenceSystem.KL20

open ExistenceSystem.Icosahedral ExistenceSystem.Quadratic

/-! ## The engine: applying σ termwise (Note L649) -/

/-- π_∥ of an integer coefficient vector is `embedPhi` of a single element of ℚ(√5):
`∑ᵢ nᵢ qVecᵢ k = ι_φ(∑ᵢ nᵢ · (qRawᵢ k))`. -/
theorem piParallel_coe_eq (n : Fin 6 → ℤ) (k : Fin 3) :
    piParallel (fun i => (n i : ℝ)) k
      = embedPhi (∑ i, (n i) • coeZphi (qRaw i k)) := by
  rw [piParallel, map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [map_zsmul, zsmul_eq_mul]
  rfl

/-- π_⊥ of an integer coefficient vector is `embedPsi` of the same element of ℚ(√5). -/
theorem piPerp_coe_eq (n : Fin 6 → ℤ) (k : Fin 3) :
    piPerp (fun i => (n i : ℝ)) k
      = embedPsi (∑ i, (n i) • coeZphi (qRaw i k)) := by
  rw [piPerp, map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [map_zsmul, zsmul_eq_mul]
  rfl

/-- Note L649: "applying σ termwise gives ∑ nᵢQᵢ^⊥ = 0 as well." Since the coordinates lie in
ℤ[φ] and the nᵢ are integers, a vanishing parallel combination forces the perpendicular one to
vanish too. The single use of φ irrational (`embedPhi_injective`). -/
theorem sigma_transfer (n : Fin 6 → ℤ)
    (hpar : piParallel (fun i => (n i : ℝ)) = 0) :
    piPerp (fun i => (n i : ℝ)) = 0 := by
  funext k
  have hz : (∑ i, (n i) • coeZphi (qRaw i k)) = 0 := by
    apply embedPhi_injective
    rw [map_zero, ← piParallel_coe_eq]
    exact congrFun hpar k
  rw [piPerp_coe_eq, hz, map_zero]
  rfl

/-! ## The isomorphism π_∥ ⊕ π_⊥ (Note L508, §4.1, determinant 40√5 ≠ 0) -/

/-- `π_∥ ⊕ π_⊥` as `rawMᵀ.mulVec`: the determinant `40√5 ≠ 0` makes it injective. Note L508. -/
theorem rawT_mulVec_injective : Function.Injective (rawMᵀ).mulVec := by
  have hU : IsUnit (rawMᵀ) := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_transpose, isUnit_iff_ne_zero]
    exact det_rawM_ne_zero
  exact Matrix.mulVec_injective_iff_isUnit.mpr hU

theorem rawT_par (c : Fin 6 → ℝ) (k : Fin 3) :
    (rawMᵀ).mulVec c ⟨k.val, by omega⟩ = piParallel c k := by
  have h : (rawMᵀ).mulVec c ⟨k.val, by omega⟩ = ∑ i, c i * rawM i ⟨k.val, by omega⟩ := by
    rw [Matrix.mulVec_transpose]
    rfl
  rw [h, piParallel]
  exact Finset.sum_congr rfl (fun i _ => by rw [(rawM_eq_images i k).1])

theorem rawT_perp (c : Fin 6 → ℝ) (k : Fin 3) :
    (rawMᵀ).mulVec c ⟨k.val + 3, by omega⟩ = piPerp c k := by
  have h : (rawMᵀ).mulVec c ⟨k.val + 3, by omega⟩
      = ∑ i, c i * rawM i ⟨k.val + 3, by omega⟩ := by
    rw [Matrix.mulVec_transpose]
    rfl
  rw [h, piPerp]
  exact Finset.sum_congr rfl (fun i _ => by rw [(rawM_eq_images i k).2])

/-- Note L649: "Hence ∑ nᵢGᵢ = 0 in ℝ⁶. But π_∥ ⊕ π_⊥ is a linear isomorphism of ℝ⁶, so n = 0."
If both π_∥ and π_⊥ of a real coefficient vector vanish, the vector is zero. -/
theorem joint_vanishing (c : Fin 6 → ℝ)
    (hpar : piParallel c = 0) (hperp : piPerp c = 0) : c = 0 := by
  apply rawT_mulVec_injective
  rw [Matrix.mulVec_zero]
  funext j
  fin_cases j
  · simpa [hpar] using rawT_par c 0
  · simpa [hpar] using rawT_par c 1
  · simpa [hpar] using rawT_par c 2
  · simpa [hperp] using rawT_perp c 0
  · simpa [hperp] using rawT_perp c 1
  · simpa [hperp] using rawT_perp c 2

/-! ## KL20: the star admits no integer relation -/

/-- **KL20, the Star Independence Lemma (Note L647, Lemma 1).** The twelve-vector icosahedral
star admits no integer relation: if `∑ᵢ nᵢ Qᵢ = 0` with `n ∈ ℤ⁶` (π_∥ of the integer
combination vanishes), then `n = 0`. Equivalently, π_∥ restricted to ℒ is injective. Note L649.
Engine: irrationality of φ. -/
theorem no_integer_relation (n : Fin 6 → ℤ)
    (hpar : piParallel (fun i => (n i : ℝ)) = 0) : n = 0 := by
  have hperp := sigma_transfer n hpar
  have hc : (fun i => (n i : ℝ)) = 0 := joint_vanishing _ hpar hperp
  funext i
  have hi : (n i : ℝ) = 0 := congrFun hc i
  exact_mod_cast hi

/-! ## The equivalent geometric form: E_⊥ ∩ ℒ = {0} -/

/-- π_∥ of an actual vector of ℝ⁶ = E_∥ ⊕ E_⊥: the first three (physical) coordinates. -/
def parProj (v : Fin 6 → ℝ) : Fin 3 → ℝ := fun k => v ⟨k.val, by omega⟩

private lemma scale_ne_zero : ((Real.sqrt 2)⁻¹ * (Real.sqrt (2 + φ))⁻¹) ≠ 0 := by
  have h2 : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have hφ : Real.sqrt (2 + φ) ≠ 0 := (Real.sqrt_pos.mpr (by linarith [goldenRatio_pos])).ne'
  exact mul_ne_zero (inv_ne_zero h2) (inv_ne_zero hφ)

/-- The parallel projection of the lattice point `∑ᵢ nᵢ Gᵢ` is a nonzero scalar times π_∥ of
the integer coefficient vector. (Gᵢ = 2^{-1/2}(Qᵢ, Qᵢ^⊥); `row` is Gᵢ, `Q` is the normalised
star.) -/
theorem parProj_lattice (n : Fin 6 → ℤ) (k : Fin 3) :
    parProj (fun j => ∑ i, (n i : ℝ) * Icosahedral.row i j) k
      = ((Real.sqrt 2)⁻¹ * (Real.sqrt (2 + φ))⁻¹) * piParallel (fun i => (n i : ℝ)) k := by
  have hrow : ∀ i, Icosahedral.row i ⟨k.val, by omega⟩ = Q i k / Real.sqrt 2 := by
    intro i
    unfold Icosahedral.row
    exact dite_eq_left k.isLt
  show (∑ i, (n i : ℝ) * Icosahedral.row i ⟨k.val, by omega⟩) = _
  rw [piParallel, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [hrow i]
  simp only [Q, Pi.smul_apply, smul_eq_mul]
  ring

/-- **KL20, the equivalent form (Note L647).** `E_⊥ ∩ ℒ = {0}`: the only lattice point whose
physical (parallel) projection vanishes is the origin. -/
theorem perp_inter_lattice_eq_zero :
    {v : Fin 6 → ℝ | parProj v = 0} ∩ Icosahedral.lattice = {0} := by
  ext v
  simp only [Set.mem_inter_iff, Icosahedral.lattice, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hperp, n, rfl⟩
    have hpar0 : piParallel (fun i => (n i : ℝ)) = 0 := by
      funext k
      have hk := congrFun hperp k
      rw [parProj_lattice] at hk
      exact (mul_eq_zero.mp hk).resolve_left scale_ne_zero
    have hn := no_integer_relation n hpar0
    subst hn
    funext j; simp
  · rintro rfl
    refine ⟨?_, 0, ?_⟩
    · funext k; simp [parProj]
    · funext j; simp

/-- **KL20, the first clause (Note L647): π_∥ restricted to the lattice ℒ is injective.** -/
theorem parProj_injOn_lattice : Set.InjOn parProj Icosahedral.lattice := by
  rintro v ⟨n, rfl⟩ v' ⟨n', rfl⟩ h
  have hpar : piParallel (fun i => (n i : ℝ)) = piParallel (fun i => (n' i : ℝ)) := by
    funext k
    have hk := congrFun h k
    rw [parProj_lattice, parProj_lattice] at hk
    exact mul_left_cancel₀ scale_ne_zero hk
  have hdiff : piParallel (fun i => ((n i - n' i : ℤ) : ℝ)) = 0 := by
    funext k
    have e : piParallel (fun i => ((n i - n' i : ℤ) : ℝ)) k
        = piParallel (fun i => (n i : ℝ)) k - piParallel (fun i => (n' i : ℝ)) k := by
      rw [piParallel, piParallel, piParallel, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      push_cast; ring
    rw [e, congrFun hpar k]; simp
  have hz := no_integer_relation (fun i => n i - n' i) hdiff
  have hnn : n = n' := by
    funext i
    have := congrFun hz i
    simp only [Pi.zero_apply] at this
    omega
  subst hnn; rfl

end ExistenceSystem.KL20

end
