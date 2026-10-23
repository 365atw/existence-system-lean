module

/-
KL23 — The Real-Type Two-Rate Theorem, from THE EXACT AND FREE SYSTEM — AN EXISTENCE SYNTHESIS (§6.1).
All mathematics: Kari A Light.

Source: `THE-NOTE-EDITED.md` (194,868 bytes, 1,539 lines). Line numbers below refer to that file.
Her words are quoted exactly beside each statement. Nothing of hers is graded here.

Her statement (Note L805–L809):

  L805: "**Two facts about `Γ`, both from Schur, both free.** They are stated and proved together, as
  one theorem, because it is one lemma applied twice."

  L807: "**The Real-Type Two-Rate Theorem (KL23 — `Γ`a, `Γ`b).** Let `Y=A₅` act on
  `V=E_∥⊕E_⊥`, the summands carrying the two inequivalent real three-dimensional irreps `Γ₃,Γ₃'`.
  Let `Γ` be the kinetic coefficient tensor: a `Y`-equivariant element of `V⊗V`, symmetric by Onsager
  reciprocity [33] — both `u` and `w` are time-even, so the signature is `+1` and `Γ` is symmetric, not
  antisymmetric — and positive semi-definite by the second law. Then
  L808: `Γ=Γ_∥ P_∥ ⊕ Γ_⊥ P_⊥,  Γ_∥,Γ_⊥≥0`.
  L809: **The internal tags `Γ`a and `Γ`b are retained: `Γ`a is `Γ|_{E_⊥}=Γ_⊥·𝟏` — one positive number
  on the perpendicular block; `Γ`b is the vanishing of the mixed block.**"

Her proof (Note L811): "The mixed block intertwines `Γ₃'` with `Γ₃`. Their characters differ on the class
`12C₅` (`φ` against `1−φ`), so they are inequivalent and Schur's lemma gives `Hom_Y(Γ₃',Γ₃)=0`; the block
vanishes, and by symmetry so does its transpose. This half uses equivariance alone — neither Onsager
symmetry nor positivity … For the diagonal blocks, Schur over `ℝ` gives only that `End_Y` is a real
division algebra, hence `ℝ,ℂ` or `ℍ`. The Frobenius–Schur indicator settles which:
`ν(χ)=|Y|⁻¹∑_g χ(g²)=1/60[3+15·3+20·0+12(χ(5A)+χ(5B))]=1/60[48+12]=+1`, the golden ratio cancelling
because only the sum `χ(5A)+χ(5B)=1` enters — so both twins are of real type, and independently so, since
a real irreducible module of complex type has even dimension and one of quaternionic type dimension
divisible by four, while `dim E_⊥=3`. Real type means a unique invariant symmetric bilinear form up to
scale; each diagonal block is therefore a scalar. ∎"

Reading choices and scope:

* The representations `Γ₃, Γ₃'` and the action of `Y≅A₅` on `ℝ⁶` are, in her Note and in this
  formalisation, "named … and not constructed" (map §6a; `ExistenceSystem.IcosahedralRep` header). This
  module reuses that merged character module — the class data, the character values `Γ₃=(3,φ,1−φ,0,−1)`
  and `Γ₃'=(3,1−φ,φ,0,−1)` (Note L512), and the two character inner products — and adds the
  Frobenius–Schur indicator computation `ν=+1` that her L811 proof turns on. The concrete orthogonal
  projections `P_∥=π_∥`, `P_⊥=π_⊥` are built in `ExistenceSystem.Icosahedral`.

* The borrowed results are cited, never claimed, and enter as **explicit named hypotheses**:
    - **Schur's lemma, A7 (Note L1130):** "A homomorphism between irreducible representations is zero or
      an isomorphism; an equivariant endomorphism of a real irreducible representation of real type is a
      scalar. Schur [7]; … Serre [8]." It carries two uses here (Note L516, "One lemma, four doors"): the
      mixed block vanishes because `Γ₃'≇Γ₃`, and each diagonal block is a scalar because of real type.
    - **Onsager reciprocity and the second law, A13 (Note L1142):** "The kinetic tensor is symmetric and
      positive semi-definite …". Positive semi-definiteness of the diagonal blocks is the hypothesis
      (`secondLaw…`) from which `Γ_∥,Γ_⊥≥0` is discharged. Onsager *symmetry* frames the setup — it is why
      `Γ` is symmetric, not antisymmetric — but, as her L811 proof notes, the block structure itself "uses
      equivariance alone — neither Onsager symmetry nor positivity"; the diagonal blocks are scalars by
      Schur over `ℝ` (real type) with no appeal to symmetry, so symmetry is not carried as a load-bearing
      hypothesis here. (Its role is her counterfactual L813, which is prose and is not encoded.)

* On the positivity wording, the map (`G3`, §1b(v)) records that "`Γ_∥,Γ_⊥≥0`" (L808) and "one positive
  number" (L809) are two readings; following the boxed statement L808, this module states `≥ 0` and
  derives it from the second-law hypothesis. The uniform-sector scope (Note L815: "The statement holds in
  the uniform sector") is where the equivariance is exact; the counterfactual sentence (L813) is prose and
  is not encoded. KL17 (L819, same computation) is a separate item.
-/
public import Mathlib
public import ExistenceSystem.IcosahedralRep

@[expose] public section

namespace ExistenceSystem.KL23

open ExistenceSystem.IcosahedralRep
open ExistenceSystem.Quadratic
open scoped QuadraticAlgebra InnerProductSpace

/-! ## Part A — the Frobenius–Schur indicator `ν = +1` (Note L811)

The new content her L811 proof turns on: the real-type criterion for the two twins. Everything else in
Part A/B reuses the merged character module `ExistenceSystem.IcosahedralRep`. -/

/-- The five conjugacy classes written out, so sums over `IcosaClass` reduce to the five summands.
Mirror of the (private) helper in `IcosahedralRep`, rebuilt from the public `classEquiv`. -/
private lemma sum_over_classes {M : Type*} [AddCommMonoid M] (f : IcosaClass → M) :
    ∑ c, f c = f .e + f .c5 + f .c5sq + f .c3 + f .c2 := by
  rw [← classEquiv.symm.sum_comp f]
  repeat rw [Fin.sum_univ_succ]
  simp [classEquiv, add_zero, ← add_assoc]

/-- Note L811: the class of `g²`, read off her indicator computation
`ν(χ)=1/60[3+15·3+20·0+12(χ(5A)+χ(5B))]`. The identity squares to the identity; the 15 involutions
(`15C₂`) square to the identity; the 20 three-cycles (`20C₃`) square within their class; and the two
five-fold classes `12C₅`, `12C₅²` square into each other (so `12(χ(5A)+χ(5B))` is their joint
contribution). -/
def sqClass : IcosaClass → IcosaClass
  | .e => .e
  | .c5 => .c5sq
  | .c5sq => .c5
  | .c3 => .c3
  | .c2 => .e

/-- Note L811: the Frobenius–Schur indicator `ν(χ)=|Y|⁻¹∑_g χ(g²)`, grouped by conjugacy class as
`(1/60)∑_c |c|·χ(g²)` with `g²` in class `sqClass c`. -/
noncomputable def fsIndicator (χ : IcosaClass → K) : K :=
  algebraMap ℚ K (60 : ℚ)⁻¹ *
    ∑ c, algebraMap ℚ K (classSize c : ℚ) * χ (sqClass c)

set_option linter.unusedSimpArgs false in
set_option linter.unnecessarySeqFocus false in
/-- Note L811: `ν(Γ₃)=+1` — `Γ₃` is of real type. The golden ratio cancels: the two five-fold classes
contribute `12·(1−φ)+12·φ`. -/
theorem fsIndicator_chi3 : fsIndicator chi3 = 1 := by
  have hsum : ∑ c, algebraMap ℚ K (classSize c : ℚ) * chi3 (sqClass c) = algebraMap ℚ K 60 := by
    rw [sum_over_classes]
    simp only [classSize, sqClass, chi3]
    apply QuadraticAlgebra.ext <;>
      simp [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, QuadraticAlgebra.re_add,
        QuadraticAlgebra.im_add, QuadraticAlgebra.re_sub, QuadraticAlgebra.im_sub,
        QuadraticAlgebra.re_neg, QuadraticAlgebra.im_neg, QuadraticAlgebra.re_one,
        QuadraticAlgebra.im_one, QuadraticAlgebra.re_zero, QuadraticAlgebra.im_zero,
        QuadraticAlgebra.re_omega, QuadraticAlgebra.im_omega, QuadraticAlgebra.re_natCast,
        QuadraticAlgebra.im_natCast, ← QuadraticAlgebra.C_eq_algebraMap, QuadraticAlgebra.re_C,
        QuadraticAlgebra.im_C] <;>
      norm_num
  unfold fsIndicator
  rw [hsum, ← map_mul, inv_mul_cancel₀ (by norm_num : (60 : ℚ) ≠ 0), map_one]

set_option linter.unusedSimpArgs false in
set_option linter.unnecessarySeqFocus false in
/-- Note L811: `ν(Γ₃')=+1` — the phason irrep `Γ₃'` is of real type, which is "equivalent to `Γ₃'` having
Frobenius–Schur indicator `+1`" (Note L813) and is what gives a single well-defined positive relaxation
rate. -/
theorem fsIndicator_chi3' : fsIndicator chi3' = 1 := by
  have hsum : ∑ c, algebraMap ℚ K (classSize c : ℚ) * chi3' (sqClass c) = algebraMap ℚ K 60 := by
    rw [sum_over_classes]
    simp only [classSize, sqClass, chi3']
    apply QuadraticAlgebra.ext <;>
      simp [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, QuadraticAlgebra.re_add,
        QuadraticAlgebra.im_add, QuadraticAlgebra.re_sub, QuadraticAlgebra.im_sub,
        QuadraticAlgebra.re_neg, QuadraticAlgebra.im_neg, QuadraticAlgebra.re_one,
        QuadraticAlgebra.im_one, QuadraticAlgebra.re_zero, QuadraticAlgebra.im_zero,
        QuadraticAlgebra.re_omega, QuadraticAlgebra.im_omega, QuadraticAlgebra.re_natCast,
        QuadraticAlgebra.im_natCast, ← QuadraticAlgebra.C_eq_algebraMap, QuadraticAlgebra.re_C,
        QuadraticAlgebra.im_C] <;>
      norm_num
  unfold fsIndicator
  rw [hsum, ← map_mul, inv_mul_cancel₀ (by norm_num : (60 : ℚ) ≠ 0), map_one]

/-- Note L811, corroboration: "a real irreducible module of complex type has even dimension" — `dim E_⊥=3`
is odd, excluding complex type independently of the indicator. -/
theorem dim_perp_not_complex_type : ¬ (2 ∣ (3 : ℕ)) := by decide

/-- Note L811, corroboration: "one of quaternionic type dimension divisible by four" — `dim E_⊥=3`
excludes quaternionic type independently of the indicator. -/
theorem dim_perp_not_quaternionic_type : ¬ (4 ∣ (3 : ℕ)) := by decide

/-! ## Part B — inequivalence and irreducibility (reused from `IcosahedralRep`)

Note L514: "because the summands are **inequivalent**, Schur's lemma … admits no intertwiner between
them." These are the character-level facts that discharge the premises of Schur's lemma below. -/

/-- Note L811/L514: `Γ₃` and `Γ₃'` are inequivalent — their character inner product is `0`. Reuses
`IcosahedralRep.charInner_chi3_cross`. -/
theorem inequivalent : charInner chi3 chi3' = 0 := charInner_chi3_cross

/-- Note L811: "Their characters differ on the class `12C₅` (`φ` against `1−φ`)." -/
theorem chi_ne_on_c5 : chi3 .c5 ≠ chi3' .c5 := by
  intro h
  have him := congrArg QuadraticAlgebra.im h
  simp only [chi3, chi3', QuadraticAlgebra.im_omega, QuadraticAlgebra.im_sub,
    QuadraticAlgebra.im_one] at him
  norm_num at him

/-- `Γ₃` is irreducible: its self character inner product is `1`. Reuses
`IcosahedralRep.charInner_chi3_self`. -/
theorem irreducible_chi3 : charInner chi3 chi3 = 1 := charInner_chi3_self

/-! ## Part C — the two-rate theorem, assembled from the borrowed Schur and Onsager hypotheses

`V = E_∥ ⊕ E_⊥` is carried by its two summands `E_par`, `E_perp` (real inner product spaces standing for
the carriers of `Γ₃`, `Γ₃'`). The kinetic tensor `Γ` is carried by its four blocks between them. The
representation-theoretic implications (Schur A7; the Frobenius–Schur real-type criterion) and the
physical inputs (Onsager symmetry and the second law, A13) enter as **named hypotheses**; this module
supplies the premises they consume (`inequivalent`, `fsIndicator_chi3`, `fsIndicator_chi3'`) and the
positivity `Γ_∥,Γ_⊥≥0`. -/

/-- A positive-semidefinite scalar block has a nonnegative scalar: if `G = c·𝟏` and `⟪G v, v⟫ ≥ 0` for
all `v`, then `0 ≤ c`. This is the second-law step (Note L808, "`Γ_∥,Γ_⊥≥0`"). -/
private theorem scalar_nonneg_of_psd {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Nontrivial E] (G : E →ₗ[ℝ] E) (c : ℝ) (hG : G = c • LinearMap.id)
    (hpsd : ∀ v : E, 0 ≤ ⟪G v, v⟫_ℝ) : 0 ≤ c := by
  obtain ⟨v, hv⟩ := exists_ne (0 : E)
  have h0 := hpsd v
  rw [hG] at h0
  simp only [LinearMap.smul_apply, LinearMap.id_apply] at h0
  rw [real_inner_smul_left] at h0
  have hnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hvv : (0 : ℝ) < ⟪v, v⟫_ℝ := by
    rw [real_inner_self_eq_norm_mul_norm]; exact mul_pos hnorm hnorm
  by_contra hneg
  rw [not_le] at hneg
  exact absurd h0 (not_le.mpr (mul_neg_of_neg_of_pos hneg hvv))

section TwoRate

variable {E_par : Type*} [NormedAddCommGroup E_par] [InnerProductSpace ℝ E_par]
variable {E_perp : Type*} [NormedAddCommGroup E_perp] [InnerProductSpace ℝ E_perp]

/-- **(Γb), Note L809/L811.** "`Γ`b is the vanishing of the mixed block." The mixed blocks `Γ_{⊥∥}` and
`Γ_{∥⊥}` of `Γ` intertwine the inequivalent `Γ₃'` and `Γ₃`; by Schur's lemma (A7, Note L1130) they
vanish. The borrowed Schur implication is the hypothesis `schurMixed`; the premise `charInner Γ₃ Γ₃' = 0`
is discharged here by `inequivalent`. Uses equivariance alone — "neither Onsager symmetry nor
positivity" (Note L811). -/
theorem mixed_block_vanishes
    (Gpm : E_perp →ₗ[ℝ] E_par) (Gmp : E_par →ₗ[ℝ] E_perp)
    (schurMixed : charInner chi3 chi3' = 0 → Gpm = 0 ∧ Gmp = 0) :
    Gpm = 0 ∧ Gmp = 0 :=
  schurMixed inequivalent

/-- **(Γa), Note L809/L811.** "`Γ`a is `Γ|_{E_⊥}=Γ_⊥·𝟏` — one positive number on the perpendicular
block." Schur over `ℝ` with the Frobenius–Schur real-type criterion (A7, Note L1130/L811) makes the
perpendicular diagonal block a scalar; the second law (A13, Note L1142) makes the scalar `≥ 0`. The
borrowed implication is `schurScalarPerp`, whose premise `ν(Γ₃')=+1` is discharged by `fsIndicator_chi3'`;
the second law is `secondLawPerp`. -/
theorem perp_block_scalar [Nontrivial E_perp]
    (Gmm : E_perp →ₗ[ℝ] E_perp)
    (schurScalarPerp : fsIndicator chi3' = 1 → ∃ c : ℝ, Gmm = c • LinearMap.id)
    (secondLawPerp : ∀ v : E_perp, 0 ≤ ⟪Gmm v, v⟫_ℝ) :
    ∃ Γ_perp : ℝ, 0 ≤ Γ_perp ∧ Gmm = Γ_perp • LinearMap.id := by
  obtain ⟨c, hc⟩ := schurScalarPerp fsIndicator_chi3'
  exact ⟨c, scalar_nonneg_of_psd Gmm c hc secondLawPerp, hc⟩

/-- The parallel diagonal block is likewise a nonnegative scalar (Note L808, `Γ_∥≥0`): `Γ₃` is of real
type (`fsIndicator_chi3`) and the second law gives `Γ_∥≥0`. -/
theorem par_block_scalar [Nontrivial E_par]
    (Gpp : E_par →ₗ[ℝ] E_par)
    (schurScalarPar : fsIndicator chi3 = 1 → ∃ c : ℝ, Gpp = c • LinearMap.id)
    (secondLawPar : ∀ u : E_par, 0 ≤ ⟪Gpp u, u⟫_ℝ) :
    ∃ Γ_par : ℝ, 0 ≤ Γ_par ∧ Gpp = Γ_par • LinearMap.id := by
  obtain ⟨c, hc⟩ := schurScalarPar fsIndicator_chi3
  exact ⟨c, scalar_nonneg_of_psd Gpp c hc secondLawPar, hc⟩

/-- **The Real-Type Two-Rate Theorem (KL23), Note L807–L809.** The kinetic tensor, block-decomposed over
`V=E_∥⊕E_⊥`, is `Γ=Γ_∥ P_∥ ⊕ Γ_⊥ P_⊥` with `Γ_∥,Γ_⊥≥0`: the two mixed blocks vanish (Γb), and each
diagonal block is a nonnegative scalar (Γa and its `E_∥` twin). Borrowed as explicit hypotheses: Schur's
lemma A7 (`schurMixed`, `schurScalarPar`, `schurScalarPerp`), with the Frobenius–Schur real-type criterion
folded into the scalar implications; Onsager/second-law positivity A13 (`secondLawPar`, `secondLawPerp`).
What this module proves: the premises those implications consume, and the positivity `Γ_∥,Γ_⊥≥0`. -/
theorem two_rate [Nontrivial E_par] [Nontrivial E_perp]
    (Gpp : E_par →ₗ[ℝ] E_par) (Gpm : E_perp →ₗ[ℝ] E_par)
    (Gmp : E_par →ₗ[ℝ] E_perp) (Gmm : E_perp →ₗ[ℝ] E_perp)
    (schurMixed : charInner chi3 chi3' = 0 → Gpm = 0 ∧ Gmp = 0)
    (schurScalarPar : fsIndicator chi3 = 1 → ∃ c : ℝ, Gpp = c • LinearMap.id)
    (schurScalarPerp : fsIndicator chi3' = 1 → ∃ c : ℝ, Gmm = c • LinearMap.id)
    (secondLawPar : ∀ u : E_par, 0 ≤ ⟪Gpp u, u⟫_ℝ)
    (secondLawPerp : ∀ v : E_perp, 0 ≤ ⟪Gmm v, v⟫_ℝ) :
    (Gpm = 0 ∧ Gmp = 0) ∧
      (∃ Γ_par : ℝ, 0 ≤ Γ_par ∧ Gpp = Γ_par • LinearMap.id) ∧
      (∃ Γ_perp : ℝ, 0 ≤ Γ_perp ∧ Gmm = Γ_perp • LinearMap.id) :=
  ⟨mixed_block_vanishes Gpm Gmp schurMixed,
    par_block_scalar Gpp schurScalarPar secondLawPar,
    perp_block_scalar Gmm schurScalarPerp secondLawPerp⟩

end TwoRate

end ExistenceSystem.KL23

end
