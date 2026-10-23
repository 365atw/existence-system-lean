module

/-
KL5 — the Two-Shell Theorem, from THE EXACT AND FREE SYSTEM — AN EXISTENCE SYNTHESIS.
All mathematics: Kari A Light.

Source: `THE-NOTE-EDITED.md` (194,868 bytes, 1,539 lines). Line numbers below refer to that file.
Her words are quoted exactly beside each statement. Nothing of hers is graded here.

Note L94 (front matter), her statement verbatim:
  "KL5 — The Two-Shell Theorem (two-shell necessity). The twelve-fold icosahedral star
   contains no closed triad at all; hence a single-shell functional has no cubic invariant,
   no first-order transition, and no phase dependence to be flat in. Triads exist only as
   short + short = long, across two shells, and the two second-shell sub-shells stand in
   ratio exactly φ. The two-shell structure is forced, not chosen. Proved in §4.3; verified
   exhaustively, Appendix A items 2, 3, 4."

Note L562 (§4.3), the proof: "Three vectors of equal length sum to zero only if their
pairwise cosines are all −1/2. The icosahedral star offers only ±1/√5 = ±0.4472… and −1
(antipodes). Hence:" — L564: "Over all C(12,3)=220 triples of the twelve vectors ±Qᵢ, the
number satisfying Qₐ+Q_b+Q_c=0 is zero."

Note L570 (§4.3, Forcing 2 / the shell ratio): "|Qᵢ ± Qⱼ|² = 2 ± 2/√5,
  |q_>|/|q_<| = √((2+2/√5)/(2−2/√5)) = √((√5+1)/(√5−1)) = √((3+√5)/2) = φ exactly."
Note L584: "Triads exist only as short + short = long, across the two shells."

What is formalised here is the geometry that is hers and is a theorem: no closed triad in the
twelve-star (App. A item 2), the second-shell ratio φ (App. A item 3, Forcing 2), and that the
long leg of a mixed closure is a second-shell vector, not a first-shell unit (App. A item 4).

What is NOT encoded, by her own markings:
  • "a cubic invariant forces a first-order transition" is borrowed — A10 (Alexander–McTague
    [21–25]), "used in §4.3 and §4.5", "Established, cited, never claimed". The words
    "cubic invariant", "first-order transition" and "phase dependence" name physics objects the
    Note does not define formally, so they are prose here, not Lean (cf. KL3).
  • Her search sentence (L566) — "no paper … has assembled this object by hand … That is a
    search result, not a theorem" — is, by her own words, not a theorem.

This module leverages the shared star module `ExistenceSystem.Icosahedral` (the twelve-vector
star over ℤ[φ], `Qᵢ·Qⱼ = ±1/√5`). No star data is given a second home here.
-/
public import ExistenceSystem.Icosahedral

@[expose] public section

open Real Matrix
open scoped goldenRatio Matrix

namespace ExistenceSystem.KL5

open ExistenceSystem.Icosahedral

/-! ## A √5 fact used throughout

The star's only off-diagonal cosines are `±1/√5`, and `−1/2` is none of them. The content is
that `√5 ≠ 2`: any `±1/√5` equal to `−1/2` would force `√5 = ±2`, impossible. -/

/-- No real of the form `K/√5` with `K = ±1` equals `−1/2` (because `√5 ≠ ±2`). -/
private theorem K_div_sqrt5_ne (K : ℝ) (hK : K = 1 ∨ K = -1) : K / √5 ≠ -1 / 2 := by
  have h5 : √5 * √5 = 5 := Real.mul_self_sqrt (by norm_num)
  have h5pos : (0 : ℝ) < √5 := Real.sqrt_pos.mpr (by norm_num)
  intro h
  rw [div_eq_iff h5pos.ne'] at h
  rcases hK with rfl | rfl
  · linarith [h5pos]
  · have h2 : √5 = 2 := by linarith
    rw [h2] at h5; norm_num at h5

/-! ## The twelve-fold star: the vectors `±Qᵢ`

Note L482/L564: the twelve vectors `±Qᵢ`, indexed by a sign `s : Bool` and an axis `i : Fin 6`.
`starVec true i = Qᵢ`, `starVec false i = −Qᵢ`. The twelve distinct labels are the twelve
vectors of the star; `C(12,3) = 220` triples.
-/

/-- The twelve vectors `±Qᵢ` of the icosahedral star. -/
noncomputable def starVec (s : Bool) (i : Fin 6) : Fin 3 → ℝ :=
  (if s then (1 : ℝ) else -1) • Q i

/-- Pairwise dot product of two star vectors: the sign of the pairing times `Qᵢ·Qⱼ`. -/
theorem starVec_dot (s t : Bool) (i j : Fin 6) :
    dotProduct (starVec s i) (starVec t j)
      = (if s = t then (1 : ℝ) else -1) * dotProduct (Q i) (Q j) := by
  simp only [starVec, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  cases s <;> cases t <;> simp

/-- Each star vector has unit length (Note L486). -/
theorem starVec_dot_self (s : Bool) (i : Fin 6) :
    dotProduct (starVec s i) (starVec s i) = 1 := by
  rw [starVec_dot]
  simp [Q_dot_self]

/-- Note L562: the star "offers only ±1/√5 and −1 (antipodes)". Hence no pair of *distinct*
star vectors has cosine −1/2. -/
theorem starVec_dot_ne_neg_half (s t : Bool) (i j : Fin 6) (h : (s, i) ≠ (t, j)) :
    dotProduct (starVec s i) (starVec t j) ≠ -1 / 2 := by
  rw [starVec_dot]
  by_cases hij : i = j
  · subst hij
    rw [Q_dot_self, mul_one]
    split_ifs <;> norm_num
  · rw [Q_dot_off i j hij, ← mul_div_assoc]
    apply K_div_sqrt5_ne
    rcases sign_ne_zero_off i j hij with hsg | hsg <;> by_cases hst : s = t <;> simp [hsg, hst]

/-! ## No closed triad in the twelve-star (App. A item 2) -/

/-- Note L562–L564 (KL5, the Two-Shell Theorem, item 2): no three distinct vectors of the
twelve-fold star sum to zero. Her proof: three unit vectors summing to zero force every
pairwise cosine to be −1/2, which the star never offers. -/
theorem no_closed_triad (s₁ s₂ s₃ : Bool) (i₁ i₂ i₃ : Fin 6)
    (h12 : (s₁, i₁) ≠ (s₂, i₂)) (_h13 : (s₁, i₁) ≠ (s₃, i₃)) (_h23 : (s₂, i₂) ≠ (s₃, i₃)) :
    starVec s₁ i₁ + starVec s₂ i₂ + starVec s₃ i₃ ≠ 0 := by
  intro hsum
  set v1 := starVec s₁ i₁ with hv1
  set v2 := starVec s₂ i₂ with hv2
  set v3 := starVec s₃ i₃ with hv3
  have h11 : dotProduct v1 v1 = 1 := starVec_dot_self s₁ i₁
  have h22 : dotProduct v2 v2 = 1 := starVec_dot_self s₂ i₂
  have h33 : dotProduct v3 v3 = 1 := starVec_dot_self s₃ i₃
  have e1 : dotProduct v1 v1 + dotProduct v1 v2 + dotProduct v1 v3 = 0 := by
    have := congrArg (dotProduct v1) hsum
    simpa [dotProduct_add, dotProduct_zero] using this
  have e2 : dotProduct v2 v1 + dotProduct v2 v2 + dotProduct v2 v3 = 0 := by
    have := congrArg (dotProduct v2) hsum
    simpa [dotProduct_add, dotProduct_zero] using this
  have e3 : dotProduct v3 v1 + dotProduct v3 v2 + dotProduct v3 v3 = 0 := by
    have := congrArg (dotProduct v3) hsum
    simpa [dotProduct_add, dotProduct_zero] using this
  have c21 : dotProduct v2 v1 = dotProduct v1 v2 := dotProduct_comm _ _
  have c31 : dotProduct v3 v1 = dotProduct v1 v3 := dotProduct_comm _ _
  have c32 : dotProduct v3 v2 = dotProduct v2 v3 := dotProduct_comm _ _
  have hp : dotProduct v1 v2 = -1 / 2 := by
    linarith [e1, e2, e3, c21, c31, c32, h11, h22, h33]
  exact starVec_dot_ne_neg_half s₁ s₂ i₁ i₂ h12 hp

/-! ## The second shell and Forcing 2: the ratio φ (App. A item 3) -/

/-- Note L568–L570: `|Qᵢ + Qⱼ|² = 2 + 2·sign(i,j)/√5`. -/
theorem secondShell_sq_add (i j : Fin 6) (hij : i ≠ j) :
    dotProduct (Q i + Q j) (Q i + Q j) = 2 + 2 * (sign i j : ℝ) / √5 := by
  simp only [dotProduct_add, add_dotProduct]
  rw [Q_dot_self, Q_dot_self, Q_dot_off i j hij, dotProduct_comm (Q j) (Q i), Q_dot_off i j hij]
  ring

/-- Note L568–L570: `|Qᵢ − Qⱼ|² = 2 − 2·sign(i,j)/√5`. -/
theorem secondShell_sq_sub (i j : Fin 6) (hij : i ≠ j) :
    dotProduct (Q i - Q j) (Q i - Q j) = 2 - 2 * (sign i j : ℝ) / √5 := by
  simp only [dotProduct_sub, sub_dotProduct]
  rw [Q_dot_self, Q_dot_self, Q_dot_off i j hij, dotProduct_comm (Q j) (Q i), Q_dot_off i j hij]
  ring

/-- Note L570: the ratio of the two second-shell squared lengths is `φ²`. -/
theorem secondShell_ratio_sq : (2 + 2 / √5) / (2 - 2 / √5) = φ ^ 2 := by
  have h5 : √5 * √5 = 5 := Real.mul_self_sqrt (by norm_num)
  have h5pos : (0 : ℝ) < √5 := Real.sqrt_pos.mpr (by norm_num)
  have hsne : √5 ≠ 0 := h5pos.ne'
  have hgt : (1 : ℝ) < √5 := by
    have := Real.sqrt_lt_sqrt (show (0 : ℝ) ≤ 1 by norm_num) (show (1 : ℝ) < 5 by norm_num)
    rwa [Real.sqrt_one] at this
  have hden : (2 - 2 / √5) ≠ 0 := by
    have hlt : 2 / √5 < 2 := by rw [div_lt_iff₀ h5pos]; linarith [hgt]
    have : 0 < 2 - 2 / √5 := by linarith
    exact this.ne'
  have hφ2 : φ ^ 2 = (3 + √5) / 2 := by
    have hval : 2 * φ - 1 = √5 := by
      have h1 : (1 : ℝ) - φ = ψ := one_sub_goldenConj
      have h2 : φ - ψ = √5 := goldenRatio_sub_goldenConj
      linarith
    rw [goldenRatio_sq]; linarith
  rw [hφ2, div_eq_div_iff hden (by norm_num : (2 : ℝ) ≠ 0)]
  field_simp
  linear_combination -h5

/-- Note L570, Forcing 2 (App. A item 3): the two second-shell sub-shells stand in ratio
exactly `φ`: `√(2 + 2/√5) / √(2 − 2/√5) = φ`. A coefficient-free consequence of
`Qᵢ·Qⱼ = ±1/√5` alone. -/
theorem shell_ratio : Real.sqrt (2 + 2 / √5) / Real.sqrt (2 - 2 / √5) = φ := by
  have hnum : (0 : ℝ) ≤ 2 + 2 / √5 := by positivity
  rw [← Real.sqrt_div hnum, secondShell_ratio_sq, Real.sqrt_sq goldenRatio_pos.le]

/-! ## Triads exist only across two shells (App. A item 4) -/

/-- Note L584 (short + short = long): the closing vector of a mixed triad, `−(Qᵢ + Qⱼ)`, is a
*second-shell* vector — its squared length is `2 ± 2/√5 ≠ 1` — so it is not a first-shell unit
vector. A genuine triad therefore cannot live inside one shell. -/
theorem mixed_triad_long_not_unit (i j : Fin 6) (hij : i ≠ j) :
    dotProduct (Q i + Q j) (Q i + Q j) ≠ 1 := by
  rw [secondShell_sq_add i j hij]
  have h5pos : (0 : ℝ) < √5 := Real.sqrt_pos.mpr (by norm_num)
  have h5 : √5 * √5 = 5 := Real.mul_self_sqrt (by norm_num)
  intro hcon
  rcases sign_ne_zero_off i j hij with hsg | hsg <;> rw [hsg] at hcon <;> push_cast at hcon <;>
      field_simp [h5pos.ne'] at hcon
  · linarith [h5pos]
  · have h2 : √5 = 2 := by linarith
    rw [h2] at h5; norm_num at h5

end ExistenceSystem.KL5

end
