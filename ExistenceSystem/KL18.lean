module

/-
KL18 — THE CONJUGATE LANDING THEOREM, from THE EXACT AND FREE SYSTEM — AN EXISTENCE SYNTHESIS.
All mathematics: Kari A Light.

Source: `THE-NOTE-EDITED.md` (194,868 bytes, 1,539 lines). Line numbers below refer to that file.
Her words are quoted exactly beside each statement. Nothing of hers is graded here.

Reading choices (quoting the Lean map `data/lean-scope-b/G6.md`, KL18 points 2 and 5):

* The two conjugate faces are formalised **arithmetically** over ℝ, as the map's lighter route
  ("Defined arithmetically, KL18's content touches no other group"): the coil-`k` faces are
  `φ ^ (3*k)` and `σ(φ) ^ (3*k)`, where `σ(φ) = 1 - φ = ψ` is Mathlib's `Real.goldenConj`
  (Note B.5, L1263: "the coil-`k` face is `φ^{±3k}`"; the identity is stated in the index `n`,
  the coil form is the case `n = 3k`).
* The Lucas identity `φⁿ + σ(φ)ⁿ = Lₙ` (Note L1061, B.5 L1261) needs Lucas numbers, which the map
  records Mathlib lacks ("B-LF: Lucas numbers NOT FOUND"); the minimal definition `lucas` is added
  below with her line reference.
* "The norm of the pair is exactly 1 at every coil" (L1064) has two formal readings the map names
  (`|N| = 1` or `N = (-1)ᵏ`); her ledger (2026-08-20, "THE SIGNED NORM") and Note B.6 L1267
  (`product = (-1)^k`) take `N = (-1)ᵏ`. Both are proved below (`norm_pair`, `norm_pair_abs`).

Part (c) of her theorem ("no coil is distinguished … the identity case cannot be located at one")
is prose at that point by the map's finding (KL18 point 5: *distinguished* and *located at a coil*
are not defined in the Note); its formal residue — that (a) and (b) hold for **every** `k`, so no
`k` is singled out — is exactly what the universally quantified statements below say, and that is all
that is encoded. "None is arrived at" is `residual_pos` (KL13). The limit `r = 0` (L1070) and
KL12's *configuration* type are not encoded (map, KL12 point 5).
-/
public import Mathlib

@[expose] public section

open Real
open scoped goldenRatio

namespace ExistenceSystem.KL18

/-! ## 0. Lucas numbers

Note L1061/L1261 names "the Lucas numbers [Lucas 1878]"; reference [68] (L1407): "The identity
`φⁿ + σ(φ)ⁿ = Lₙ`". The map (G6, "B-LF") records Lucas numbers are not in Mathlib; this is the
minimal definition, `L₀ = 2`, `L₁ = 1`, `Lₙ₊₂ = Lₙ₊₁ + Lₙ`. -/
def lucas : ℕ → ℤ
  | 0 => 2
  | 1 => 1
  | (n + 2) => lucas (n + 1) + lucas n

@[simp] theorem lucas_zero : lucas 0 = 2 := rfl
@[simp] theorem lucas_one : lucas 1 = 1 := rfl
theorem lucas_add_two (n : ℕ) : lucas (n + 2) = lucas (n + 1) + lucas n := rfl

/-! ## 1. The fold of the two conjugate faces is a Lucas number

Note L1061: "The fold of the two conjugate faces is an exact whole number,
$$\varphi^{n}+\sigma(\varphi)^{n}=L_{n},$$ the Lucas numbers [Lucas 1878]."
Here `σ(φ) = ψ = Real.goldenConj` (`Real.one_sub_goldenConj`: `1 - φ = ψ`). -/

/-- `σ(φ) = 1 - φ`, i.e. Mathlib's `ψ` is `1 - φ` (Note Taxonomy L214: `σ(φ) = 1 - φ`). -/
theorem goldenConj_eq_one_sub : ψ = 1 - φ := (one_sub_goldenConj).symm

/-- Note L1061 / B.5 L1261: `φⁿ + σ(φ)ⁿ = Lₙ` for every `n`. -/
theorem goldenRatio_pow_add_goldenConj_pow (n : ℕ) :
    φ ^ n + ψ ^ n = (lucas n : ℝ) := by
  induction n using Nat.twoStepInduction with
  | zero => norm_num
  | one => norm_num
  | more n ih1 ih2 =>
    have eφ : φ ^ (n + 2) = φ ^ (n + 1) + φ ^ n := by
      have h : φ ^ (n + 2) = φ ^ n * φ ^ 2 := by ring
      rw [h, goldenRatio_sq]; ring
    have eψ : ψ ^ (n + 2) = ψ ^ (n + 1) + ψ ^ n := by
      have h : ψ ^ (n + 2) = ψ ^ n * ψ ^ 2 := by ring
      rw [h, goldenConj_sq]; ring
    have hl : (lucas (n + 2) : ℝ) = (lucas (n + 1) : ℝ) + (lucas n : ℝ) := by
      rw [lucas_add_two]; push_cast; ring
    rw [eφ, eψ, hl, ← ih1, ← ih2]; ring

/-! ## 2. The Pisot mechanism

Note L1062: "The mechanism is that `φ` is a Pisot number: its conjugate is negative and shrinking,
so the alternating powers vanish and carry the sum onto an integer [Pisot 1938]." (B.5 L1263 repeats
it.) The map (G6, "B-PIS") records the sentence uses only `σ(φ) < 0` and `|σ(φ)| < 1`, both in
Mathlib; a general Pisot theory is not needed. -/

/-- "its conjugate is negative" — `σ(φ) < 0` (Mathlib `Real.goldenConj_neg`). -/
theorem conj_neg : ψ < 0 := goldenConj_neg

/-- "and shrinking" — `|σ(φ)| < 1`. -/
theorem conj_abs_lt_one : |ψ| < 1 :=
  abs_lt.2 ⟨neg_one_lt_goldenConj, lt_trans goldenConj_neg one_pos⟩

/-- "the alternating powers vanish": `σ(φ)ⁿ → 0`. This is the exact content of the Pisot mechanism
that "carr[ies] the sum onto an integer" — the fold is `Lₙ` exactly for every `n`
(`goldenRatio_pow_add_goldenConj_pow`), while the free face `σ(φ)ⁿ` tends to `0`. -/
theorem goldenConj_pow_tendsto_zero :
    Filter.Tendsto (fun n : ℕ => ψ ^ n) Filter.atTop (nhds 0) :=
  tendsto_pow_atTop_nhds_zero_of_abs_lt_one conj_abs_lt_one

/-! ## 3. The coil faces, the fold at every coil, and the base case

Note B.5 L1263: "the coil-`k` face is `φ^{±3k}` … it must be stated as the every-third"; so the fold
at coil `k` is `L_{3k}`. Note L1062: "At coil 0 both faces equal 1 and the fold is 2, which is `L₀`;
the identity holds there as the base case." -/

/-- "The landing is general: the fold is exact at every coil" (L1070): the fold of the coil-`k`
faces `φ^{3k}` and `σ(φ)^{3k}` is the whole number `L_{3k}`. -/
theorem fold_coil (k : ℕ) : φ ^ (3 * k) + ψ ^ (3 * k) = (lucas (3 * k) : ℝ) :=
  goldenRatio_pow_add_goldenConj_pow (3 * k)

/-- Note L1062: "At coil 0 both faces equal 1 and the fold is 2, which is `L₀`." -/
theorem fold_coil_zero : φ ^ (3 * 0) + ψ ^ (3 * 0) = 2 := by norm_num

/-! ## 4. For every `k ≥ 1` neither face alone is a whole number

Note L1062: "For every `k ≥ 1` neither face alone is a whole number." Formalised as irrationality
(stronger than "not a whole number"), via `φ^{m+1} = φ·F_{m+1} + F_m` and the irrationality of
`φ`, `ψ` (map, KL18(a): `Real.goldenRatio_irrational`, `Real.goldenConj_mul_fib_succ_add_fib`). -/

theorem goldenRatio_pow_succ_irrational (m : ℕ) : Irrational (φ ^ (m + 1)) := by
  rw [← goldenRatio_mul_fib_succ_add_fib m]
  exact (goldenRatio_irrational.mul_natCast (by simp)).add_natCast _

theorem goldenConj_pow_succ_irrational (m : ℕ) : Irrational (ψ ^ (m + 1)) := by
  rw [← goldenConj_mul_fib_succ_add_fib m]
  exact (goldenConj_irrational.mul_natCast (by simp)).add_natCast _

/-- The parallel face `φ^{3k}` is irrational for `k ≥ 1`. -/
theorem face_par_irrational (k : ℕ) (hk : 1 ≤ k) : Irrational (φ ^ (3 * k)) := by
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (show 3 * k ≠ 0 by omega)
  rw [hm]; exact goldenRatio_pow_succ_irrational m

/-- The perpendicular face `σ(φ)^{3k}` is irrational for `k ≥ 1`. -/
theorem face_perp_irrational (k : ℕ) (hk : 1 ≤ k) : Irrational (ψ ^ (3 * k)) := by
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (show 3 * k ≠ 0 by omega)
  rw [hm]; exact goldenConj_pow_succ_irrational m

/-! ## 5. The norm of the pair

Note L1064: "The norm of the pair is exactly 1 at every coil (Appendix B.3, product column)."
B.3 L1251 / B.6 L1267: `N(π∥·π⊥) = (-1)ᵏ` once signs are restored. Engine: `N(φ) = φ·ψ = -1`
(Mathlib `Real.goldenRatio_mul_goldenConj`), so `N(φ^{3k}) = (φψ)^{3k} = (-1)^{3k} = (-1)ᵏ`. -/

/-- `N(φ^{3k}) = φ^{3k}·σ(φ)^{3k} = (-1)ᵏ` (the signed reading, B.3/B.6). -/
theorem norm_pair (k : ℕ) : φ ^ (3 * k) * ψ ^ (3 * k) = (-1) ^ k := by
  rw [← mul_pow, goldenRatio_mul_goldenConj, pow_mul]; norm_num

/-- "The norm of the pair is exactly 1 at every coil" — the absolute-value reading, `|N| = 1`. -/
theorem norm_pair_abs (k : ℕ) : |φ ^ (3 * k) * ψ ^ (3 * k)| = 1 := by
  rw [norm_pair]; simp [abs_pow]

/-! ## 6. "None is arrived at": the residual is strictly positive at every finite coil (KL13)

Note L1058 (headline), L1060, L1070. KL18(a) cites KL13: "At every finite coil the residual is
strictly positive, so no configuration is bound." The coil law is KL12/§7.0 L981, B.4 L1253:
`r₀ > 0`, `r_{k+1} = φ⁻³·r_k`. (The *configuration* type and the limit `r = 0` are not encoded;
see the header and the map, KL12 point 5.) -/

/-- The near-touch residual (Note §7.0 L981, B.4 L1253), `r_{k+1} = φ⁻³·r_k`. -/
noncomputable def residual (r₀ : ℝ) : ℕ → ℝ
  | 0 => r₀
  | (k + 1) => (φ ^ 3)⁻¹ * residual r₀ k

/-- Note L997 (KL13): "`r₀ > 0` and `φ⁻³ > 0`, so `r_k > 0` for every finite coil `k`." -/
theorem residual_pos (r₀ : ℝ) (hr : 0 < r₀) (k : ℕ) : 0 < residual r₀ k := by
  induction k with
  | zero => exact hr
  | succ k ih =>
    have : 0 < (φ ^ 3)⁻¹ := by positivity
    exact mul_pos this ih

/-- Note §7.0 L983: "*The residuals converge to `0`*." The ratio `φ⁻³ ∈ (0,1)`, so `r_k → 0`. -/
theorem residual_tendsto_zero (r₀ : ℝ) :
    Filter.Tendsto (residual r₀) Filter.atTop (nhds 0) := by
  have hclosed : ∀ k, residual r₀ k = (φ ^ 3)⁻¹ ^ k * r₀ := by
    intro k
    induction k with
    | zero => simp [residual]
    | succ k ih => rw [residual, ih, pow_succ]; ring
  have hlt : (φ ^ 3)⁻¹ < 1 := by
    rw [inv_lt_one₀ (by positivity)]
    calc (1 : ℝ) < φ := one_lt_goldenRatio
      _ = φ ^ 1 := (pow_one φ).symm
      _ ≤ φ ^ 3 := pow_le_pow_right₀ one_lt_goldenRatio.le (by norm_num)
  have hpos : 0 ≤ (φ ^ 3)⁻¹ := by positivity
  have := (tendsto_pow_atTop_nhds_zero_of_lt_one hpos hlt).mul_const r₀
  simp only [zero_mul] at this
  exact this.congr (fun k => (hclosed k).symm)

/-! ## 7. Part (b): the operator's determinate reading returns `m` at every coil (KL15, §7.3)

Note L1066: "**(b)** The operator's determinate reading returns `m` at every coil (KL15, §7.3)."
§7.3 L1019/L1040: with `A = mφ`, `B = m·σ(φ) = m(1-φ)`, the fired pair is `(A-δ, B+δ)` and the
trace `A'+B' = m` "as an algebraic identity, for every `δ`". (The map, KL15 point 5, records that
reading `π_swap(m·φ)` as this scalar is a definition the Note supplies at §7.3; `E = mc²` and the
units criterion are not encoded.) -/

/-- Note §7.3 L1040: `π_swap(m·φ) = A' + B' = m`, "as an algebraic identity, for every `δ`",
with `A = mφ`, `B = m(1-φ)`, `A' = A - δ`, `B' = B + δ`. -/
theorem piswap_trace (m δ : ℝ) : (m * φ - δ) + (m * (1 - φ) + δ) = m := by ring

end ExistenceSystem.KL18

end
