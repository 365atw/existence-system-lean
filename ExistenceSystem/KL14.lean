module

/-
KL14 — the fixed-point part of existence and uniqueness of the bound configuration, from
THE EXACT AND FREE SYSTEM — AN EXISTENCE SYNTHESIS.
All mathematics: Kari A Light.

Source: `THE-NOTE-EDITED.md` (194,868 bytes, 1,539 lines). Line numbers below refer to that file.
Her words are quoted exactly beside each statement. Nothing of hers is graded here.

The coil law `r_{k+1} = φ^{-3} * r_k` is taken as given (captain's ruling; KL12 / §7.0) and is
`ExistenceSystem.KL13.residual`. The coil map is `r ↦ φ^{-3} * r` on the metric space
`([0, r₀], |·|)`.

"The bound configuration exists, is unique, and is the limit of the ascent" names KL12's
*configuration*. That type is not given in the Note (map `data/lean-scope-b/G6.md`, KL12 point 5
and KL14 point 5) and is not encoded. Formalised here: `0` is the unique fixed point of the coil
map on `[0, r₀]`, by the Banach fixed-point theorem (`ContractingWith`), and the ascent — the
residual sequence — converges to that fixed point.
-/
public import ExistenceSystem.KL13

@[expose] public section

open Real Filter Function Set
open scoped goldenRatio

namespace ExistenceSystem.KL14

/-- The coil map `r ↦ φ^{-3} * r` (Note L1001). -/
noncomputable def coilMap (r : ℝ) : ℝ := (φ ^ 3)⁻¹ * r

/-- `φ^{-3}` lies in `(0, 1)`, so the coil map is a strict contraction and sends `[0, r₀]` into
itself. Her proof (L1003) uses the self-map without a separate sentence (map, KL14 point 5(i)). -/
lemma coilRatio_mem_Ioo : (φ ^ 3)⁻¹ ∈ Set.Ioo (0 : ℝ) 1 := by
  refine ⟨by positivity, ?_⟩
  rw [inv_lt_one₀ (by positivity : (0 : ℝ) < φ ^ 3)]
  exact one_lt_pow₀ one_lt_goldenRatio (by decide : (3 : ℕ) ≠ 0)

/-- Lipschitz constant of the coil map: `‖φ^{-3}‖₊ < 1`. -/
lemma coilRatio_lt_one : ‖(φ ^ 3)⁻¹‖₊ < 1 := by
  refine NNReal.coe_lt_coe.mp ?_
  rw [NNReal.coe_one]
  calc (‖(φ ^ 3)⁻¹‖₊ : ℝ) = ‖(φ ^ 3)⁻¹‖ := coe_nnnorm _
    _ = |(φ ^ 3)⁻¹| := Real.norm_eq_abs _
    _ = (φ ^ 3)⁻¹ := abs_of_pos coilRatio_mem_Ioo.1
    _ < 1 := coilRatio_mem_Ioo.2

lemma lipschitz_coilMap : LipschitzWith ‖(φ ^ 3)⁻¹‖₊ coilMap := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  have hc : (‖(φ ^ 3)⁻¹‖₊ : ℝ) = (φ ^ 3)⁻¹ := by
    calc (‖(φ ^ 3)⁻¹‖₊ : ℝ) = ‖(φ ^ 3)⁻¹‖ := coe_nnnorm _
      _ = |(φ ^ 3)⁻¹| := Real.norm_eq_abs _
      _ = (φ ^ 3)⁻¹ := abs_of_pos coilRatio_mem_Ioo.1
  rw [hc, dist_eq_norm, dist_eq_norm, Real.norm_eq_abs, Real.norm_eq_abs, coilMap, coilMap,
    ← mul_sub, abs_mul, abs_of_pos coilRatio_mem_Ioo.1]

lemma contracting_coilMap : ContractingWith ‖(φ ^ 3)⁻¹‖₊ coilMap :=
  ⟨coilRatio_lt_one, lipschitz_coilMap⟩

/-- `0 < φ^{-3} < 1` sends `[0, r₀]` into itself. Holds for every `r₀`; the interval is empty
when `r₀ < 0`. -/
lemma coilMap_mapsTo (r₀ : ℝ) :
    MapsTo coilMap (Icc (0 : ℝ) r₀) (Icc (0 : ℝ) r₀) := by
  intro r ⟨hr0, hr1⟩
  refine ⟨mul_nonneg coilRatio_mem_Ioo.1.le hr0, ?_⟩
  exact (mul_le_of_le_one_left hr0 coilRatio_mem_Ioo.2.le).trans hr1

/-- The coil map on the subtype `[0, r₀]`. -/
noncomputable def coilMapIcc (r₀ : ℝ) : Icc (0 : ℝ) r₀ → Icc (0 : ℝ) r₀ :=
  (coilMap_mapsTo r₀).restrict coilMap _ _

lemma coilMapIcc_contracting (r₀ : ℝ) :
    ContractingWith ‖(φ ^ 3)⁻¹‖₊ (coilMapIcc r₀) :=
  contracting_coilMap.restrict (coilMap_mapsTo r₀)

/-- A fixed point of `r ↦ φ^{-3} * r` on `ℝ` is `0`, because `φ^{-3} ≠ 1` (Note L1003, last line). -/
lemma coilMap_fixed_iff {r : ℝ} : coilMap r = r ↔ r = 0 := by
  constructor
  · intro h
    have hne : (φ ^ 3)⁻¹ ≠ 1 := coilRatio_mem_Ioo.2.ne
    have : ((φ ^ 3)⁻¹ - 1) * r = 0 := by
      unfold coilMap at h
      linear_combination h
    rcases mul_eq_zero.mp this with h0 | h0
    · exact absurd (sub_eq_zero.mp h0) hne
    · exact h0
  · rintro rfl
    simp [coilMap]

lemma residual_eq_iterate (r₀ : ℝ) (n : ℕ) : KL13.residual r₀ n = coilMap^[n] r₀ := by
  induction n with
  | zero => simp [KL13.residual]
  | succ n ih =>
    calc KL13.residual r₀ (n + 1)
        = (φ ^ 3)⁻¹ * KL13.residual r₀ n := by simp [KL13.residual]
      _ = (φ ^ 3)⁻¹ * coilMap^[n] r₀ := by rw [ih]
      _ = coilMap (coilMap^[n] r₀) := by simp [coilMap]
      _ = coilMap^[n + 1] r₀ := (iterate_succ_apply' coilMap n r₀).symm

/-- Note line 112: "0 is the unique fixed point of r |-> phi^{-3} r on [0, r_0]; the bound configuration exists, is unique, and is the limit of the ascent."

The fixed-point half, by Banach (`ContractingWith.fixedPoint` on the complete space `[0, r₀]`):
the coil map has a unique fixed point there, and that point is `0`. "bound configuration" is
KL12's undefined type and is not encoded. The limit of the ascent is `ascent_tendsto_zero`. -/
theorem fixedPoint_eq_zero (r₀ : ℝ) (hr : 0 ≤ r₀) :
    (∃! z : Icc (0 : ℝ) r₀, coilMap (z : ℝ) = (z : ℝ)) ∧
      ∀ z : Icc (0 : ℝ) r₀, coilMap (z : ℝ) = (z : ℝ) → (z : ℝ) = 0 := by
  let s : Set ℝ := Icc 0 r₀
  have : Nonempty s := ⟨⟨0, left_mem_Icc.mpr hr⟩⟩
  have : CompleteSpace s := isClosed_Icc.isComplete.completeSpace_coe
  let hs : MapsTo coilMap s s := coilMap_mapsTo r₀
  let f : s → s := coilMapIcc r₀
  have hf : ContractingWith ‖(φ ^ 3)⁻¹‖₊ f := coilMapIcc_contracting r₀
  let z : s := ContractingWith.fixedPoint f hf
  have hz : coilMap (z : ℝ) = (z : ℝ) := by
    have hfz : (f z : ℝ) = coilMap (z : ℝ) := by simp [f, coilMapIcc]
    rw [← hfz]
    exact congrArg Subtype.val hf.fixedPoint_isFixedPt
  refine ⟨⟨z, hz, ?_⟩, ?_⟩
  · intro w hw
    have hw' : IsFixedPt f w := Subtype.ext <| by
      simpa [f, coilMapIcc] using hw
    exact hf.fixedPoint_unique hw'
  · intro w hw
    exact coilMap_fixed_iff.mp hw

/-- Note line 112: "0 is the unique fixed point of r |-> phi^{-3} r on [0, r_0]; the bound configuration exists, is unique, and is the limit of the ascent."

The limit half: iteration of the coil map from `r₀` converges to the Banach fixed point, which
is `0`. That sequence is the ascent (the residual of the coil law). "bound configuration" is
KL12's undefined type and is not encoded. -/
theorem ascent_tendsto_zero (r₀ : ℝ) (hr : 0 ≤ r₀) :
    Tendsto (KL13.residual r₀) atTop (nhds (0 : ℝ)) := by
  let s : Set ℝ := Icc 0 r₀
  have : Nonempty s := ⟨⟨0, left_mem_Icc.mpr hr⟩⟩
  have : CompleteSpace s := isClosed_Icc.isComplete.completeSpace_coe
  let hs : MapsTo coilMap s s := coilMap_mapsTo r₀
  let f : s → s := coilMapIcc r₀
  have hf : ContractingWith ‖(φ ^ 3)⁻¹‖₊ f := coilMapIcc_contracting r₀
  let x0 : s := ⟨r₀, right_mem_Icc.mpr hr⟩
  let z : s := ContractingWith.fixedPoint f hf
  have hfix : coilMap (z : ℝ) = (z : ℝ) := by
    have hfz : (f z : ℝ) = coilMap (z : ℝ) := by simp [f, coilMapIcc]
    rw [← hfz]
    exact congrArg Subtype.val hf.fixedPoint_isFixedPt
  have hzero : (z : ℝ) = 0 := coilMap_fixed_iff.mp hfix
  have htend : Tendsto (fun n : ℕ => (f^[n] x0 : ℝ)) atTop (nhds (z : ℝ)) :=
    (continuous_subtype_val.tendsto z).comp (hf.tendsto_iterate_fixedPoint x0)
  rw [hzero] at htend
  refine htend.congr fun n => ?_
  have hiter : (f^[n] x0 : ℝ) = coilMap^[n] (x0 : ℝ) := by
    simpa [f, coilMapIcc] using hs.coe_iterate_restrict x0 n
  simpa [x0, residual_eq_iterate] using hiter

end ExistenceSystem.KL14

end
