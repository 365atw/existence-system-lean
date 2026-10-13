module

/-
KL3 — the indifference theorem, from THE EXACT AND FREE SYSTEM — AN EXISTENCE SYNTHESIS.
All mathematics: Kari A Light.

Source: `THE-NOTE-EDITED.md` (194,868 bytes, 1,539 lines). Line numbers below refer to that file.
Her words are quoted exactly beside each statement. Nothing of hers is graded here.

Only the mathematics of the potential is formalised: the values at the branches, the stationary
points, and the minimizer set. The prose words "least-action drive", "provably indifferent",
"exogenous", and the cusp step of §3.3 are not encoded.
-/
public import Mathlib

@[expose] public section

namespace ExistenceSystem.KL3

/-- Note L422: "$$V(x)=-\tfrac r2x^{2}+\tfrac14x^{4}.$$" -/
noncomputable def V (r x : ℝ) : ℝ := -(r / 2) * x ^ 2 + (1 / 4) * x ^ 4

/-- The derivative of `V` in `x`, written out: `V′(x) = -r x + x³`. -/
theorem hasDerivAt_V (r x : ℝ) : HasDerivAt (V r) (-r * x + x ^ 3) x := by
  have h := (((hasDerivAt_pow 2 x).const_mul (-(r / 2))).add
    ((hasDerivAt_pow 4 x).const_mul (1 / 4)))
  convert h using 1
  · funext y; simp only [V, Pi.add_apply]
  · push_cast; ring

theorem deriv_V (r x : ℝ) : deriv (V r) x = -r * x + x ^ 3 :=
  (hasDerivAt_V r x).deriv

/-- `V` minus its branch depth is a perfect square: `V r x + r²/4 = (x² - r)² / 4`. -/
theorem V_add_depth (r x : ℝ) : V r x + r ^ 2 / 4 = (x ^ 2 - r) ^ 2 / 4 := by
  unfold V; ring

/-! ## 1. Equal depth at the two branches

Note L424: "For $r>0$ the ordered branches are $x=\pm\sqrt r$, and because $V$ is **even**,"
Note L426: "$$V(+\sqrt r)=V(-\sqrt r)=-\tfrac{r^{2}}4.$$"
Note L90 (KL3): "the ordered branches $x=\pm\sqrt r$ have *exactly* equal depth $-r^{2}/4$"
-/

/-- Note L424: "$V$ is **even**". -/
theorem V_even (r x : ℝ) : V r (-x) = V r x := by
  unfold V; ring

/-- Note L426: "$$V(+\sqrt r)=V(-\sqrt r)=-\tfrac{r^{2}}4.$$" -/
theorem V_branches (r : ℝ) (hr : 0 < r) :
    V r (Real.sqrt r) = -r ^ 2 / 4 ∧ V r (-Real.sqrt r) = -r ^ 2 / 4 := by
  have hs : Real.sqrt r ^ 2 = r := Real.sq_sqrt hr.le
  have h1 : V r (Real.sqrt r) = -r ^ 2 / 4 := by
    have := V_add_depth r (Real.sqrt r)
    rw [hs] at this
    linarith
  exact ⟨h1, by rw [V_even]; exact h1⟩

/-! ## 2. The stationary points

Note L428: "The two branches are stationary points of **exactly equal standing**."
Note L420: "Consider the symmetric normal form $\dot x=rx-x^{3}$, relaxational on the even potential"
-/

/-- The flow of Note L420 is descent on `V`: `r x - x³ = -V′(x)`. -/
theorem flow_eq_neg_deriv (r x : ℝ) : r * x - x ^ 3 = -deriv (V r) x := by
  rw [deriv_V]; ring

/-- `V′` vanishes at exactly three points: `0`, `√r` and `-√r`. -/
theorem deriv_V_eq_zero_iff (r : ℝ) (hr : 0 < r) (x : ℝ) :
    deriv (V r) x = 0 ↔ x = 0 ∨ x = Real.sqrt r ∨ x = -Real.sqrt r := by
  have hs : Real.sqrt r ^ 2 = r := Real.sq_sqrt hr.le
  have key : deriv (V r) x = x * ((x - Real.sqrt r) * (x + Real.sqrt r)) := by
    rw [deriv_V]
    linear_combination x * hs
  rw [key]
  constructor
  · intro h
    rcases mul_eq_zero.1 h with h0 | h'
    · exact Or.inl h0
    · rcases mul_eq_zero.1 h' with h1 | h2
      · exact Or.inr (Or.inl (by linarith))
      · exact Or.inr (Or.inr (by linarith))
  · rintro (h | h | h) <;> subst h <;> ring

/-- The critical set of `V` is `{0, √r, -√r}`. -/
theorem critical_set (r : ℝ) (hr : 0 < r) :
    {x : ℝ | deriv (V r) x = 0} = {0, Real.sqrt r, -Real.sqrt r} := by
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  exact deriv_V_eq_zero_iff r hr x

/-- The three critical points are pairwise distinct, so there are exactly three. -/
theorem critical_points_distinct (r : ℝ) (hr : 0 < r) :
    (0 : ℝ) ≠ Real.sqrt r ∧ (0 : ℝ) ≠ -Real.sqrt r ∧ Real.sqrt r ≠ -Real.sqrt r := by
  have hpos : 0 < Real.sqrt r := Real.sqrt_pos.2 hr
  refine ⟨hpos.ne, ?_, ?_⟩ <;> linarith

theorem critical_set_ncard (r : ℝ) (hr : 0 < r) :
    {x : ℝ | deriv (V r) x = 0}.ncard = 3 := by
  obtain ⟨h01, h02, h12⟩ := critical_points_distinct r hr
  rw [critical_set r hr, Set.ncard_insert_of_notMem, Set.ncard_pair h12]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
  exact ⟨h01, h02⟩

/-! ## 3. The minimizer set

Note L434: "> **The minimizer set has more than one element, so minimizing is not a selection rule.**"
Note L436: "*Not* "the free branch fails to be a minimizer." Both branches **are** minimizers, and that
is exactly why the functional cannot choose."
-/

/-- Every value of `V` is at least the branch depth `-r²/4`. -/
theorem V_ge_depth (r x : ℝ) : -r ^ 2 / 4 ≤ V r x := by
  have := V_add_depth r x
  nlinarith [sq_nonneg (x ^ 2 - r)]

/-- The global minimizers of `V` over `ℝ` are exactly `√r` and `-√r`. -/
theorem minimizers_eq (r : ℝ) (hr : 0 < r) :
    {x : ℝ | ∀ y : ℝ, V r x ≤ V r y} = {Real.sqrt r, -Real.sqrt r} := by
  have hs : Real.sqrt r ^ 2 = r := Real.sq_sqrt hr.le
  obtain ⟨hb1, hb2⟩ := V_branches r hr
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro hmin
    have hle := hmin (Real.sqrt r)
    rw [hb1] at hle
    have hsq : (x ^ 2 - r) ^ 2 = 0 := by
      have := V_add_depth r x
      nlinarith [sq_nonneg (x ^ 2 - r)]
    have hx2 : x ^ 2 = Real.sqrt r ^ 2 := by
      rw [hs]; linarith [pow_eq_zero_iff two_ne_zero |>.1 hsq]
    exact sq_eq_sq_iff_eq_or_eq_neg.1 hx2
  · rintro (h | h) y <;> subst h
    · rw [hb1]; exact V_ge_depth r y
    · rw [hb2]; exact V_ge_depth r y

/-- Note L434: "**The minimizer set has more than one element, so minimizing is not a selection
rule.**" — the mathematical half: the minimizer set has more than one element. -/
theorem minimizers_nontrivial (r : ℝ) (hr : 0 < r) :
    {x : ℝ | ∀ y : ℝ, V r x ≤ V r y}.Nontrivial := by
  rw [minimizers_eq r hr]
  exact ⟨_, Set.mem_insert _ _, _, Set.mem_insert_of_mem _ rfl,
    (critical_points_distinct r hr).2.2⟩

/-- Note L436: "Both branches **are** minimizers" — and the minimizer set has exactly two elements. -/
theorem minimizers_ncard (r : ℝ) (hr : 0 < r) :
    {x : ℝ | ∀ y : ℝ, V r x ≤ V r y}.ncard = 2 := by
  rw [minimizers_eq r hr, Set.ncard_pair (critical_points_distinct r hr).2.2]

end ExistenceSystem.KL3

end
