module

/-
First-order Euler–Lagrange calculus for a density.

Note L829–L831: "δJ/δw_m = −∂_k Π_km", with
`Π_km := ∂f_el/∂(∂_k w_m) = K₁ ∂_k w_m + K₂ T_kmpq ∂_p w_q + K₃ M_kmpq u_pq`.

The higher-order clause "at every order" and the admissible class are prose
(map, G5 §2.5). This module is the first-order operator, the chain rule of the
first variation, the gradient-only divergence, and the quadratic-order formula for `Π`.
`T_kmpq = T_pqkm` is a hypothesis for matching her displayed `Π`, not an asserted fact.
Phonon terms do not depend on `∇w`, so their partial in that slot is zero.
-/
public import Mathlib

@[expose] public section

open MeasureTheory

namespace ExistenceSystem.EulerLagrange

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The first-order operator `∂L/∂u − d/dx (∂L/∂u')`, after the field is substituted. -/
noncomputable def el (partialValue partialDeriv : ℝ → ℝ) (x : ℝ) : ℝ :=
  partialValue x - deriv partialDeriv x

/-- Note L836: a density with no bare-field dependence has Euler–Lagrange derivative a divergence.
In one variable that derivative is `−dΠ/dx`. -/
theorem el_gradientOnly (partialDeriv : ℝ → ℝ) (x : ℝ) :
    el (fun _ => 0) partialDeriv x = -deriv partialDeriv x := by
  simp [el]

/-- Chain rule at `ε = 0`: `d/dε L(u + ε φ, u' + ε φ') = DL (φ, φ')`. -/
theorem variation_at_zero (L : ℝ → ℝ → ℝ) (u v φ ψ : ℝ) (L' : ℝ × ℝ →L[ℝ] ℝ)
    (hL : HasFDerivAt (fun p : ℝ × ℝ => L p.1 p.2) L' (u, v)) :
    HasDerivAt (fun ε => L (u + ε * φ) (v + ε * ψ)) (L' (φ, ψ)) 0 := by
  have h1 : HasDerivAt (fun ε => u + ε * φ) φ 0 := by
    have h := (hasDerivAt_const 0 u).add ((hasDerivAt_id 0).mul_const φ)
    exact (h.congr_deriv (by ring)).congr_of_eventuallyEq
      (Filter.EventuallyEq.of_eq (by funext ε; rfl))
  have h2 : HasDerivAt (fun ε => v + ε * ψ) ψ 0 := by
    have h := (hasDerivAt_const 0 v).add ((hasDerivAt_id 0).mul_const ψ)
    exact (h.congr_deriv (by ring)).congr_of_eventuallyEq
      (Filter.EventuallyEq.of_eq (by funext ε; rfl))
  have hpath := h1.prodMk h2
  have hcomp := HasFDerivAt.comp_hasDerivAt_of_eq (hl := hL) (hf := hpath)
    (hy := by
      show (u, v) = (u + (0 : ℝ) * φ, v + (0 : ℝ) * ψ)
      ext <;> ring)
  exact hcomp.congr_of_eventuallyEq (Filter.EventuallyEq.of_eq (by funext ε; rfl))

/-- Replace the single entry `(a, b)`. -/
def setEntry (g : ι → ι → ℝ) (a b : ι) (t : ℝ) : ι → ι → ℝ :=
  fun k l => if k = a ∧ l = b then t else g k l

omit [Fintype ι] in
lemma setEntry_self (g : ι → ι → ℝ) (a b : ι) : setEntry g a b (g a b) = g := by
  funext k l
  by_cases h : k = a ∧ l = b
  · rcases h with ⟨rfl, rfl⟩
    simp [setEntry]
  · simp [setEntry, h]

omit [Fintype ι] in
lemma hasDerivAt_setEntry (g : ι → ι → ℝ) (a b k l : ι) :
    HasDerivAt (fun t => setEntry g a b t k l) (if k = a ∧ l = b then 1 else 0) (g a b) := by
  by_cases h : k = a ∧ l = b
  · rcases h with ⟨rfl, rfl⟩
    have hid := hasDerivAt_id (g k l)
    refine (hid.congr_deriv (by simp)).congr_of_eventuallyEq
      (Filter.EventuallyEq.of_eq (by funext t; simp [setEntry]))
  · simpa [setEntry, h] using hasDerivAt_const (g a b) (g k l)

private lemma sum_single (f : ι → ι → ℝ) (a b : ι) :
    ∑ k, ∑ l, (if k = a ∧ l = b then f k l else 0) = f a b := by
  rw [Finset.sum_eq_single a]
  · rw [Finset.sum_eq_single b]
    · simp
    · intro l _ hlb
      rw [ite_eq_right (fun h => hlb h.2)]
    · simp
  · intro k _ hka
    refine Finset.sum_eq_zero ?_
    intro l _
    rw [ite_eq_right (fun h => hka h.1)]
  · simp

noncomputable def k1Term (g : ι → ι → ℝ) : ℝ :=
  ∑ k, ∑ l, g k l * g k l

noncomputable def k2Term (T : ι → ι → ι → ι → ℝ) (g : ι → ι → ℝ) : ℝ :=
  ∑ k, ∑ l, ∑ m, ∑ n, T k l m n * g k l * g m n

noncomputable def k3Term (M : ι → ι → ι → ι → ℝ) (u g : ι → ι → ℝ) : ℝ :=
  ∑ k, ∑ l, ∑ m, ∑ n, M k l m n * g k l * u m n

/-- Gradient part of `f_el`. The factor `1/2` sits outside both `K₁` and `K₂`. `K₃` is outside it. -/
noncomputable def gradDensity (K1 K2 K3 : ℝ) (T M : ι → ι → ι → ι → ℝ)
    (u g : ι → ι → ℝ) : ℝ :=
  (1 / 2) * K1 * k1Term g + (1 / 2) * K2 * k2Term T g + K3 * k3Term M u g

/-- Note L831: `Π_km = K₁ ∂_k w_m + K₂ T_kmpq ∂_p w_q + K₃ M_kmpq u_pq`. -/
noncomputable def piStress (K1 K2 K3 : ℝ) (T M : ι → ι → ι → ι → ℝ)
    (u g : ι → ι → ℝ) (k m : ι) : ℝ :=
  K1 * g k m + K2 * ∑ p, ∑ q, T k m p q * g p q + K3 * ∑ p, ∑ q, M k m p q * u p q

omit [Fintype ι] in
private lemma hasDerivAt_sq_entry (g : ι → ι → ℝ) (a b k l : ι) :
    HasDerivAt (fun t => setEntry g a b t k l * setEntry g a b t k l)
      (if k = a ∧ l = b then 2 * g a b else 0) (g a b) := by
  have hs := hasDerivAt_setEntry g a b k l
  have hm := hs.mul hs
  rw [setEntry_self g a b] at hm
  have hd : (if k = a ∧ l = b then (1 : ℝ) else 0) * g k l
      + g k l * (if k = a ∧ l = b then 1 else 0)
      = if k = a ∧ l = b then 2 * g a b else 0 := by
    by_cases h : k = a ∧ l = b
    · rcases h with ⟨rfl, rfl⟩
      simp
      ring
    · simp [h]
  rwa [hd] at hm

private lemma hasDerivAt_k1 (g : ι → ι → ℝ) (a b : ι) :
    HasDerivAt (fun t => k1Term (setEntry g a b t)) (2 * g a b) (g a b) := by
  unfold k1Term
  have h := HasDerivAt.fun_sum (u := (Finset.univ : Finset ι))
    (fun k _ => HasDerivAt.fun_sum (u := (Finset.univ : Finset ι))
      (fun l _ => hasDerivAt_sq_entry g a b k l))
  have hs : ∑ k, ∑ l, (if k = a ∧ l = b then 2 * g a b else 0) = 2 * g a b := by
    simpa using sum_single (fun _ _ => 2 * g a b) a b
  rwa [hs] at h

private lemma hasDerivAt_k2 (T : ι → ι → ι → ι → ℝ) (g : ι → ι → ℝ) (a b : ι) :
    HasDerivAt (fun t => k2Term T (setEntry g a b t))
      (∑ m, ∑ n, T a b m n * g m n + ∑ k, ∑ l, T k l a b * g k l) (g a b) := by
  unfold k2Term
  have hterm : ∀ k l m n,
      HasDerivAt (fun t => T k l m n * (setEntry g a b t k l * setEntry g a b t m n))
        (T k l m n * ((if k = a ∧ l = b then 1 else 0) * g m n
          + g k l * (if m = a ∧ n = b then 1 else 0))) (g a b) := by
    intro k l m n
    have hm := ((hasDerivAt_setEntry g a b k l).mul
      (hasDerivAt_setEntry g a b m n)).const_mul (T k l m n)
    rwa [setEntry_self g a b] at hm
  have h := HasDerivAt.fun_sum (u := (Finset.univ : Finset ι)) (fun k _ =>
    HasDerivAt.fun_sum (u := (Finset.univ : Finset ι)) (fun l _ =>
      HasDerivAt.fun_sum (u := (Finset.univ : Finset ι)) (fun m _ =>
        HasDerivAt.fun_sum (u := (Finset.univ : Finset ι)) (fun n _ =>
          hterm k l m n))))
  have hs1 : ∑ k, ∑ l, ∑ m, ∑ n,
      T k l m n * ((if k = a ∧ l = b then (1 : ℝ) else 0) * g m n)
      = ∑ m, ∑ n, T a b m n * g m n := by
    have hfac : ∀ k l, ∑ m, ∑ n, T k l m n * ((if k = a ∧ l = b then 1 else 0) * g m n)
        = (if k = a ∧ l = b then 1 else 0) * ∑ m, ∑ n, T k l m n * g m n := by
      intro k l
      have hcomm : ∀ m n, T k l m n * ((if k = a ∧ l = b then 1 else 0) * g m n)
          = (if k = a ∧ l = b then 1 else 0) * (T k l m n * g m n) := by
        intro m n
        ring
      simp_rw [hcomm, ← Finset.mul_sum]
    simp_rw [hfac, ite_mul, one_mul, zero_mul]
    exact sum_single (fun k l => ∑ m, ∑ n, T k l m n * g m n) a b
  have hs2 : ∑ k, ∑ l, ∑ m, ∑ n,
      T k l m n * (g k l * (if m = a ∧ n = b then (1 : ℝ) else 0))
      = ∑ k, ∑ l, T k l a b * g k l := by
    have hfac : ∀ k l, ∑ m, ∑ n,
        T k l m n * (g k l * (if m = a ∧ n = b then 1 else 0)) = T k l a b * g k l := by
      intro k l
      have hpull : ∑ m, ∑ n, T k l m n * (g k l * (if m = a ∧ n = b then 1 else 0))
          = g k l * ∑ m, ∑ n, T k l m n * (if m = a ∧ n = b then 1 else 0) := by
        have hcomm : ∀ m n, T k l m n * (g k l * (if m = a ∧ n = b then 1 else 0))
            = g k l * (T k l m n * (if m = a ∧ n = b then 1 else 0)) := by
          intro m n
          ring
        simp_rw [hcomm, ← Finset.mul_sum]
      rw [hpull]
      have hsingle : ∑ m, ∑ n, T k l m n * (if m = a ∧ n = b then 1 else 0) = T k l a b := by
        simp_rw [mul_ite, mul_one, mul_zero]
        exact sum_single (fun m n => T k l m n) a b
      rw [hsingle]
      ring
    simp_rw [hfac]
  have hsum : ∑ k, ∑ l, ∑ m, ∑ n,
      T k l m n * ((if k = a ∧ l = b then (1 : ℝ) else 0) * g m n
        + g k l * (if m = a ∧ n = b then 1 else 0))
      = ∑ m, ∑ n, T a b m n * g m n + ∑ k, ∑ l, T k l a b * g k l := by
    simp_rw [mul_add, Finset.sum_add_distrib, hs1, hs2]
  have hfun : HasDerivAt (fun t => ∑ k, ∑ l, ∑ m, ∑ n,
      T k l m n * setEntry g a b t k l * setEntry g a b t m n)
      (∑ k, ∑ l, ∑ m, ∑ n, T k l m n * ((if k = a ∧ l = b then (1 : ℝ) else 0) * g m n
        + g k l * (if m = a ∧ n = b then 1 else 0))) (g a b) := by
    refine h.congr_of_eventuallyEq (Filter.EventuallyEq.of_eq ?_)
    funext t
    simp_rw [mul_assoc]
  rwa [hsum] at hfun

private lemma hasDerivAt_k3 (M : ι → ι → ι → ι → ℝ) (u g : ι → ι → ℝ) (a b : ι) :
    HasDerivAt (fun t => k3Term M u (setEntry g a b t))
      (∑ m, ∑ n, M a b m n * u m n) (g a b) := by
  unfold k3Term
  have hterm : ∀ k l m n,
      HasDerivAt (fun t => M k l m n * setEntry g a b t k l * u m n)
        (M k l m n * (if k = a ∧ l = b then 1 else 0) * u m n) (g a b) := by
    intro k l m n
    have hm := ((hasDerivAt_setEntry g a b k l).const_mul (M k l m n)).mul
      (hasDerivAt_const (g a b) (u m n))
    rw [setEntry_self g a b] at hm
    have hd : (M k l m n * (if k = a ∧ l = b then 1 else 0)) * u m n
        + (M k l m n * g k l) * 0
        = M k l m n * (if k = a ∧ l = b then 1 else 0) * u m n := by ring
    rwa [hd] at hm
  have h := HasDerivAt.fun_sum (u := (Finset.univ : Finset ι)) (fun k _ =>
    HasDerivAt.fun_sum (u := (Finset.univ : Finset ι)) (fun l _ =>
      HasDerivAt.fun_sum (u := (Finset.univ : Finset ι)) (fun m _ =>
        HasDerivAt.fun_sum (u := (Finset.univ : Finset ι)) (fun n _ =>
          hterm k l m n))))
  have hsum : ∑ k, ∑ l, ∑ m, ∑ n,
      M k l m n * (if k = a ∧ l = b then 1 else 0) * u m n
      = ∑ m, ∑ n, M a b m n * u m n := by
    have hfac : ∀ k l, ∑ m, ∑ n, M k l m n * (if k = a ∧ l = b then 1 else 0) * u m n
        = (if k = a ∧ l = b then 1 else 0) * ∑ m, ∑ n, M k l m n * u m n := by
      intro k l
      have hcomm : ∀ m n, M k l m n * (if k = a ∧ l = b then 1 else 0) * u m n
          = (if k = a ∧ l = b then 1 else 0) * (M k l m n * u m n) := by
        intro m n
        ring
      simp_rw [hcomm, ← Finset.mul_sum]
    simp_rw [hfac, ite_mul, one_mul, zero_mul]
    exact sum_single (fun k l => ∑ m, ∑ n, M k l m n * u m n) a b
  rwa [hsum] at h

/-- Under `T_klmn = T_mnkl`, the partial of the gradient density in the slot `∂_a w_b`
is her `Π_ab`. A constant `phonon` (the terms with no `∇w`) does not contribute. -/
theorem hasDerivAt_gradDensity (K1 K2 K3 : ℝ) (T M : ι → ι → ι → ι → ℝ)
    (u g : ι → ι → ℝ) (a b : ι) (phonon : ℝ)
    (hT : ∀ k l m n, T k l m n = T m n k l) :
    HasDerivAt (fun t => gradDensity K1 K2 K3 T M u (setEntry g a b t) + phonon)
      (piStress K1 K2 K3 T M u g a b) (g a b) := by
  have hk1 := (hasDerivAt_k1 g a b).const_mul ((1 / 2) * K1)
  have hsym : ∑ k, ∑ l, T k l a b * g k l = ∑ m, ∑ n, T a b m n * g m n := by
    simp_rw [hT]
  have hk2raw : HasDerivAt (fun t => k2Term T (setEntry g a b t))
      (2 * ∑ m, ∑ n, T a b m n * g m n) (g a b) := by
    have hk := hasDerivAt_k2 T g a b
    have hd : ∑ m, ∑ n, T a b m n * g m n + ∑ k, ∑ l, T k l a b * g k l
        = 2 * ∑ m, ∑ n, T a b m n * g m n := by
      rw [hsym]
      ring
    rwa [hd] at hk
  have hk2 := hk2raw.const_mul ((1 / 2) * K2)
  have hk3 := (hasDerivAt_k3 M u g a b).const_mul K3
  have hph := hasDerivAt_const (g a b) phonon
  have h := (hk1.add (hk2.add hk3)).add hph
  have hd : (1 / 2) * K1 * (2 * g a b) + ((1 / 2) * K2 * (2 * ∑ m, ∑ n, T a b m n * g m n)
      + K3 * ∑ m, ∑ n, M a b m n * u m n) + 0
      = piStress K1 K2 K3 T M u g a b := by
    simp [piStress]
    ring
  have hfun : (fun t => gradDensity K1 K2 K3 T M u (setEntry g a b t) + phonon) =ᶠ[nhds (g a b)]
      ((fun y => (1 / 2) * K1 * k1Term (setEntry g a b y))
        + ((fun y => (1 / 2) * K2 * k2Term T (setEntry g a b y))
          + fun y => K3 * k3Term M u (setEntry g a b y))
        + fun _ => phonon) :=
    Filter.EventuallyEq.of_eq <| by
      funext t
      simp only [gradDensity, Pi.add_apply]
      ring
  exact (h.congr_of_eventuallyEq hfun).congr_deriv hd

/-- Integration by parts on `ℝ`. Note L829, tested against a compactly supported field,
in one variable: `∫ u v' = −∫ u' v`. -/
theorem ibp_line {u v u' v' : ℝ → ℝ}
    (hu : ∀ x ∈ tsupport v, HasDerivAt u (u' x) x)
    (hv : ∀ x ∈ tsupport u, HasDerivAt v (v' x) x)
    (huv' : Integrable (u * v')) (hu'v : Integrable (u' * v)) (huv : Integrable (u * v)) :
    ∫ x, u x * v' x = -∫ x, u' x * v x :=
  integral_mul_deriv_eq_deriv_mul_of_integrable hu hv huv' hu'v huv

/-- Directional integration by parts. The measure is Haar on a finite-dimensional real space. -/
theorem ibp_frechet {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] [FiniteDimensional ℝ E] {μ : Measure E} [Measure.IsAddHaarMeasure μ]
    {f g : E → ℝ} {v : E}
    (hf'g : Integrable (fun x => fderiv ℝ f x v * g x) μ)
    (hfg' : Integrable (fun x => f x * fderiv ℝ g x v) μ)
    (hfg : Integrable (fun x => f x * g x) μ)
    (hf : ∀ x ∈ tsupport g, DifferentiableAt ℝ f x)
    (hg : ∀ x ∈ tsupport f, DifferentiableAt ℝ g x) :
    ∫ x, f x * fderiv ℝ g x v ∂μ = -∫ x, fderiv ℝ f x v * g x ∂μ :=
  integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hf'g hfg' hfg hf hg

/-- Sum of the directional pairings. This is `∫ φ div Π = −∫ ∇φ · Π` when `φ` is the test field. -/
theorem ibp_sum_directions {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] {μ : Measure E} [Measure.IsAddHaarMeasure μ]
    {κ : Type*} [Fintype κ] {f g : E → ℝ} {v : κ → E}
    (hf'g : ∀ i, Integrable (fun x => fderiv ℝ f x (v i) * g x) μ)
    (hfg' : ∀ i, Integrable (fun x => f x * fderiv ℝ g x (v i)) μ)
    (hfg : Integrable (fun x => f x * g x) μ)
    (hf : ∀ x ∈ tsupport g, DifferentiableAt ℝ f x)
    (hg : ∀ x ∈ tsupport f, DifferentiableAt ℝ g x) :
    ∫ x, f x * ∑ i, fderiv ℝ g x (v i) ∂μ
      = -∫ x, (∑ i, fderiv ℝ f x (v i)) * g x ∂μ := by
  have hterm : ∀ i, ∫ x, f x * fderiv ℝ g x (v i) ∂μ
      = -∫ x, fderiv ℝ f x (v i) * g x ∂μ :=
    fun i => ibp_frechet (hf'g i) (hfg' i) hfg hf hg
  calc
    ∫ x, f x * ∑ i, fderiv ℝ g x (v i) ∂μ
        = ∫ x, ∑ i, f x * fderiv ℝ g x (v i) ∂μ := by
          simp_rw [Finset.mul_sum]
    _ = ∑ i, ∫ x, f x * fderiv ℝ g x (v i) ∂μ := by
          rw [integral_finsetSum (Finset.univ : Finset κ) (fun i _ => hfg' i)]
    _ = ∑ i, -∫ x, fderiv ℝ f x (v i) * g x ∂μ := by
          refine Finset.sum_congr rfl ?_
          intro i _
          exact hterm i
    _ = -(∑ i, ∫ x, fderiv ℝ f x (v i) * g x ∂μ) := by
          rw [Finset.sum_neg_distrib]
    _ = -∫ x, ∑ i, fderiv ℝ f x (v i) * g x ∂μ := by
          rw [integral_finsetSum (Finset.univ : Finset κ) (fun i _ => hf'g i)]
    _ = -∫ x, (∑ i, fderiv ℝ f x (v i)) * g x ∂μ := by
          simp_rw [← Finset.sum_mul]

end ExistenceSystem.EulerLagrange

end
