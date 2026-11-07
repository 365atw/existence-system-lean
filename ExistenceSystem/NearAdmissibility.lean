module

/-
NEAR-ADMISSIBILITY — the ε-sibling of the Admissibility Lemma (KL22). All mathematics: Kari A Light.

Her statement, locked 2026-11-06, verbatim:
"A state is admissible to within ε on a window of length T exactly when its twist is no bigger than
about ε/T. The states that pass this test but fail exact invariance are precisely the near-misses."

`KL22.phase_trivial_iff` says `e^{ik·u} = 1` for **every** translation `u` iff `k = 0`, by the single
evaluation `u = π/k_j`. This module changes one thing: "every `u`" becomes "every `u` on a window of
length `T`", and "`= 1`" becomes "within `ε` of `1`". `phase_near_trivial_iff` is that lemma, proved
by the same one-point evaluation, the translation now shortened to fit the window. It is the
imperfect-bifurcation reading of the exact closure: closure is the perfect case, and the near-misses
are what the imperfection lets through.

Reading choices:

* The phase is one real number `L` and the translation is `u ∈ [0, T]`; `phase_trivial_iff_window`
  connects this to her wavevector form, as the `ε = 0` face in every direction.
* The explicit modulus is `2·arcsin(ε/2)` (`windowModulus`). The equivalence needs `0 ≤ ε < 2`: since
  `|e^{iθ} − 1| ≤ 2` always, for `ε ≥ 2` the test passes every `L` while the right side does not.

This module NAMES the near-misses. It does not bound their count, it does not prove SC or AC(β), it
does not lower the ceiling, and it makes no claim about the Riemann hypothesis.
-/
public import Mathlib
public import ExistenceSystem.KL22

@[expose] public section

open Real

namespace ExistenceSystem.NearAdmissibility

/-! ## The modulus -/

/-- The explicit modulus of the exponential on the circle: `|e^{iθ} − 1| ≤ ε` for `|θ| ≤ π` exactly
when `|θ| ≤ windowModulus ε`. -/
noncomputable def windowModulus (ε : ℝ) : ℝ := 2 * arcsin (ε / 2)

/-- For a phase of size at most `π`, being within `ε` of `1` is `|θ| ≤ windowModulus ε`. -/
theorem norm_phase_sub_one_le_iff {x ε : ℝ} (hx : |x| ≤ π) (h0 : 0 ≤ ε) (h2 : ε < 2) :
    ‖Complex.exp (Complex.I * (↑x : ℂ)) - 1‖ ≤ ε ↔ |x| ≤ windowModulus ε := by
  have hnorm : ‖Complex.exp (Complex.I * (↑x : ℂ)) - 1‖ = 2 * Real.sin (|x| / 2) := by
    rw [Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs, abs_mul, abs_two]
    congr 1
    have hhalf : |x / 2| ≤ π := by
      rw [abs_div, abs_two]
      linarith [abs_nonneg x, pi_pos]
    rw [Real.abs_sin_eq_sin_abs_of_abs_le_pi hhalf, abs_div, abs_two]
  have hmem : |x| / 2 ∈ Set.Icc (-(π / 2)) (π / 2) :=
    ⟨by linarith [abs_nonneg x, pi_pos], by linarith⟩
  have hε : ε / 2 ∈ Set.Icc (-1 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have harc := Real.le_arcsin_iff_sin_le hmem hε
  rw [hnorm, windowModulus]
  constructor
  · intro h
    have := harc.mpr (by linarith)
    linarith
  · intro h
    have := harc.mp (by linarith)
    linarith

/-- The modulus stays below `π` on the range `ε < 2`, so the window's end is not a wrap-around. -/
theorem windowModulus_lt_pi {ε : ℝ} (h2 : ε < 2) : windowModulus ε < π := by
  have h : arcsin (ε / 2) < π / 2 := Real.arcsin_lt_pi_div_two.mpr (by linarith)
  unfold windowModulus
  linarith

/-! ## The ε-sibling of `phase_trivial_iff` -/

/-- **The ε-sibling of the Admissibility Lemma's analytic step (`KL22.phase_trivial_iff`).** "A state
is admissible to within ε on a window of length T exactly when its twist is no bigger than about
ε/T." A phase `e^{iuL}` stays within `ε` of `1` for every `u` in a window of length `T` iff
`|L| ≤ 2·arcsin(ε/2)/T`. Her proof evaluates at `u = π/k_j`; this one evaluates at the same point,
cut down to fit the window: `u = min T (π/|L|)`. The states this test passes and `L = 0` fails are
the near-misses, the imperfect bifurcations of an exact closure (`NearMiss`). -/
theorem phase_near_trivial_iff (L T ε : ℝ) (hT : 0 < T) (h0 : 0 ≤ ε) (h2 : ε < 2) :
    (∀ u ∈ Set.Icc (0 : ℝ) T, ‖Complex.exp (Complex.I * (↑(u * L) : ℂ)) - 1‖ ≤ ε)
      ↔ |L| ≤ windowModulus ε / T := by
  have hlt := windowModulus_lt_pi h2
  rw [le_div_iff₀ hT]
  constructor
  · intro h
    by_contra hcon
    have hbig : windowModulus ε < |L| * T := not_le.mp hcon
    have hmod : 0 ≤ windowModulus ε := by
      unfold windowModulus
      have : 0 ≤ arcsin (ε / 2) := Real.arcsin_nonneg.mpr (by linarith)
      linarith
    have hL : 0 < |L| := by
      by_contra hL
      have : |L| = 0 := le_antisymm (not_lt.mp hL) (abs_nonneg L)
      rw [this, zero_mul] at hbig
      linarith
    have hu0 : 0 ≤ min T (π / |L|) := le_min hT.le (div_pos pi_pos hL).le
    have habs : |min T (π / |L|) * L| = min (|L| * T) π := by
      rw [abs_mul, abs_of_nonneg hu0, mul_comm, mul_min_of_nonneg _ _ hL.le,
        mul_div_cancel₀ _ hL.ne']
    have hx : |min T (π / |L|) * L| ≤ π := by
      rw [habs]
      exact min_le_right _ _
    have hle := (norm_phase_sub_one_le_iff hx h0 h2).mp (h _ ⟨hu0, min_le_left _ _⟩)
    rw [habs] at hle
    exact absurd hle (not_le.mpr (lt_min hbig hlt))
  · intro h u hu
    have hul : |u * L| ≤ windowModulus ε := by
      rw [abs_mul, abs_of_nonneg hu.1, mul_comm]
      exact (mul_le_mul_of_nonneg_left hu.2 (abs_nonneg L)).trans h
    exact (norm_phase_sub_one_le_iff (hul.trans hlt.le) h0 h2).mpr hul

/-! ## The near-misses -/

/-- "The states that pass this test but fail exact invariance are precisely the near-misses." A
phase `L` is a near-miss at `(ε, T)` when it is admissible to within `ε` on the window of length `T`
and `L ≠ 0`: the imperfect bifurcations, where the exact closure `L = 0` is the perfect case. -/
def NearMiss (ε T L : ℝ) : Prop :=
  (∀ u ∈ Set.Icc (0 : ℝ) T, ‖Complex.exp (Complex.I * (↑(u * L) : ℂ)) - 1‖ ≤ ε) ∧ L ≠ 0

/-- A near-miss is a nonzero twist no bigger than `windowModulus ε / T`. -/
theorem nearMiss_iff {ε T : ℝ} (L : ℝ) (hT : 0 < T) (h0 : 0 ≤ ε) (h2 : ε < 2) :
    NearMiss ε T L ↔ L ≠ 0 ∧ |L| ≤ windowModulus ε / T := by
  rw [NearMiss, phase_near_trivial_iff L T ε hT h0 h2, and_comm]

/-! ## The near-misses of the plain short sum are the near-closures

A term of the sixth moment of `∑_{M<m≤2M} m^{-1/2-it}` pairs two triple products `A` and `B`, each a
product of three integers in `(M, 2M]`, and carries the phase `(B/A)^{it}`. The sum itself is not
built here: this section works with the pair `(A, B)` and its twist `log(B/A)`. -/

/-- The range of a triple product `A` of the plain short sum at size `M`. -/
def InShortRange (M A : ℕ) : Prop := M ^ 3 ≤ A ∧ A ≤ 8 * M ^ 3

/-- The twist of the pair `(A, B)`: the term carries `e^{it·log(B/A)}`. -/
noncomputable def closurePhase (A B : ℕ) : ℝ := log ((B : ℝ) / A)

/-- Both sides of the logarithm comparison, on the ordered case `a ≤ b`. -/
private theorem log_div_bounds_of_le {m K a b : ℝ} (hm : 0 < m) (hma : m ≤ a) (hbK : b ≤ K)
    (hab : a ≤ b) : (b - a) / K ≤ log (b / a) ∧ log (b / a) ≤ (b - a) / m := by
  have ha : 0 < a := hm.trans_le hma
  have hb : 0 < b := ha.trans_le hab
  have hx : 0 < b / a := div_pos hb ha
  have hd : 0 ≤ b - a := sub_nonneg.mpr hab
  constructor
  · calc (b - a) / K ≤ (b - a) / b := div_le_div_of_nonneg_left hd hb hbK
      _ = 1 - (b / a)⁻¹ := by field_simp
      _ ≤ log (b / a) := Real.one_sub_inv_le_log_of_pos hx
  · calc log (b / a) ≤ b / a - 1 := Real.log_le_sub_one_of_pos hx
      _ = (b - a) / a := by field_simp
      _ ≤ (b - a) / m := div_le_div_of_nonneg_left hd hm hma

/-- The twist compared with the gap `|b − a|`, for `a` and `b` in `[m, K]`. -/
private theorem abs_log_div_bounds {m K a b : ℝ} (hm : 0 < m) (hma : m ≤ a) (haK : a ≤ K)
    (hmb : m ≤ b) (hbK : b ≤ K) :
    |b - a| / K ≤ |log (b / a)| ∧ |log (b / a)| ≤ |b - a| / m := by
  rcases le_total a b with hab | hba
  · obtain ⟨h₁, h₂⟩ := log_div_bounds_of_le hm hma hbK hab
    have hx : 1 ≤ b / a := (one_le_div (hm.trans_le hma)).mpr hab
    rw [abs_of_nonneg (sub_nonneg.mpr hab), abs_of_nonneg (Real.log_nonneg hx)]
    exact ⟨h₁, h₂⟩
  · obtain ⟨h₁, h₂⟩ := log_div_bounds_of_le hm hmb haK hba
    have hx : 1 ≤ a / b := (one_le_div (hm.trans_le hmb)).mpr hba
    have hlog : log (b / a) = -log (a / b) := by rw [← Real.log_inv, inv_div]
    rw [hlog, abs_neg, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hba),
      abs_of_nonneg (Real.log_nonneg hx)]
    exact ⟨h₁, h₂⟩

/-- The range of a triple product, read in `ℝ`. -/
private theorem InShortRange.cast {M A : ℕ} (hA : InShortRange M A) :
    (M : ℝ) ^ 3 ≤ A ∧ (A : ℝ) ≤ 8 * (M : ℝ) ^ 3 :=
  ⟨by exact_mod_cast hA.1, by exact_mod_cast hA.2⟩

/-- The elementary bound (route 5 R3): `|L| ≥ |B − A|/(8·M³)`. -/
theorem gap_div_le_closurePhase (M A B : ℕ) (hM : 0 < M) (hA : InShortRange M A)
    (hB : InShortRange M B) : |(B : ℝ) - A| / (8 * (M : ℝ) ^ 3) ≤ |closurePhase A B| :=
  (abs_log_div_bounds (pow_pos (by exact_mod_cast hM) 3) hA.cast.1 hA.cast.2 hB.cast.1
    hB.cast.2).1

/-- The matching upper comparison: `|L| ≤ |B − A|/M³`. -/
theorem closurePhase_le_gap_div (M A B : ℕ) (hM : 0 < M) (hA : InShortRange M A)
    (hB : InShortRange M B) : |closurePhase A B| ≤ |(B : ℝ) - A| / (M : ℝ) ^ 3 :=
  (abs_log_div_bounds (pow_pos (by exact_mod_cast hM) 3) hA.cast.1 hA.cast.2 hB.cast.1
    hB.cast.2).2

/-- **The near-misses of the plain short sum are the near-closures `1 ≤ |B − A| ≲ M³/T`.** "The
states that pass this test but fail exact invariance are precisely the near-misses." Up to the
factor `8` the `≲` stands for, a pair `(A, B)` is a near-miss exactly when it fails to close and its
gap fits the band: every near-miss has `1 ≤ |B − A| ≤ 8·M³·ε'/T`, and every pair with
`1 ≤ |B − A| ≤ M³·ε'/T` is a near-miss. This names the set. It does not count it. -/
theorem nearMiss_near_closure (M A B : ℕ) (T ε : ℝ) (hM : 0 < M) (hA : InShortRange M A)
    (hB : InShortRange M B) (hT : 0 < T) (h0 : 0 ≤ ε) (h2 : ε < 2) :
    (NearMiss ε T (closurePhase A B) →
        1 ≤ |(B : ℝ) - A| ∧ |(B : ℝ) - A| ≤ 8 * (M : ℝ) ^ 3 * windowModulus ε / T) ∧
      (1 ≤ |(B : ℝ) - A| ∧ |(B : ℝ) - A| ≤ (M : ℝ) ^ 3 * windowModulus ε / T →
        NearMiss ε T (closurePhase A B)) := by
  have hM3 : 0 < (M : ℝ) ^ 3 := pow_pos (by exact_mod_cast hM) 3
  have hlow := gap_div_le_closurePhase M A B hM hA hB
  have hup := closurePhase_le_gap_div M A B hM hA hB
  rw [nearMiss_iff _ hT h0 h2]
  constructor
  · rintro ⟨hne, hle⟩
    constructor
    · have hAB : (B : ℤ) - A ≠ 0 := by
        intro hzero
        have hBA : B = A := by omega
        apply hne
        rw [closurePhase, hBA]
        have hApos : (A : ℝ) ≠ 0 := (hM3.trans_le hA.cast.1).ne'
        rw [div_self hApos, Real.log_one]
      have hint : (1 : ℤ) ≤ |(B : ℤ) - A| := Int.one_le_abs hAB
      exact_mod_cast hint
    · have h8 : 0 < 8 * (M : ℝ) ^ 3 := by positivity
      have := (div_le_iff₀ h8).mp (hlow.trans hle)
      calc |(B : ℝ) - A| ≤ windowModulus ε / T * (8 * (M : ℝ) ^ 3) := this
        _ = 8 * (M : ℝ) ^ 3 * windowModulus ε / T := by ring
  · rintro ⟨hone, hband⟩
    constructor
    · intro hzero
      rw [hzero, abs_zero] at hlow
      have hpos : 0 < |(B : ℝ) - A| / (8 * (M : ℝ) ^ 3) := by
        have : 0 < |(B : ℝ) - A| := by linarith
        positivity
      linarith
    · refine hup.trans ((div_le_iff₀ hM3).mpr ?_)
      calc |(B : ℝ) - A| ≤ (M : ℝ) ^ 3 * windowModulus ε / T := hband
        _ = windowModulus ε / T * (M : ℝ) ^ 3 := by ring

/-- At `τ = 14/5`, that is `T = M^{14/5}`, the band `M³/T` is `X^{1/15}` with `X = M³`. -/
theorem near_band_at_critical (M : ℝ) (hM : 0 < M) :
    M ^ 3 / M ^ (14 / 5 : ℝ) = (M ^ 3) ^ (1 / 15 : ℝ) := by
  rw [← Real.rpow_natCast M 3, ← Real.rpow_sub hM, ← Real.rpow_mul hM.le]
  norm_num

/-! ## Her lemma is the `ε = 0` face -/

/-- **`KL22.phase_trivial_iff` is the `ε = 0` face.** Her hypothesis, `e^{ik·u} = 1` for every
translation, holds iff in every direction the phase passes the `ε = 0` test on one window of any
length `T > 0`. Exact invariance is what the test sees with no imperfection allowed. -/
theorem phase_trivial_iff_window (k : Fin 3 → ℝ) {T : ℝ} (hT : 0 < T) :
    (∀ u : Fin 3 → ℝ, Complex.exp (Complex.I * (↑(k ⬝ᵥ u) : ℂ)) = 1) ↔
      ∀ v : Fin 3 → ℝ, ∀ u ∈ Set.Icc (0 : ℝ) T,
        ‖Complex.exp (Complex.I * (↑(u * (k ⬝ᵥ v)) : ℂ)) - 1‖ ≤ 0 := by
  constructor
  · intro h v u _
    rw [(KL22.phase_trivial_iff k).mp h]
    simp
  · intro h u
    have hle := (phase_near_trivial_iff (k ⬝ᵥ u) T 0 hT le_rfl two_pos).mp (h u)
    have hzero : k ⬝ᵥ u = 0 := by
      simpa [windowModulus] using hle
    simp [hzero]

end ExistenceSystem.NearAdmissibility

end
