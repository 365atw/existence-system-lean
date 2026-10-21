module

/-
KL1 — the per-dimension uniqueness result, from THE EXACT AND FREE SYSTEM — AN EXISTENCE SYNTHESIS.
All mathematics: Kari A Light.

Source: `THE-NOTE-EDITED.md` (194,868 bytes, 1,539 lines). Line numbers below refer to that file.
Her words are quoted exactly beside each statement. Nothing of hers is graded here.

Only the mathematics is formalised: for every integer `n ≥ 2`, `f(x) = x^n - x - 1` has exactly one
positive real root and it lies in `(1,2)`; with `rₙ` that root, `rₙ₊₁ < rₙ`, the roots are bounded
below by 1, and `rₙ → 1`; `φ = r₂` is the planar face and the plastic number `ρ = r₃` the spatial
face. The prose on Note L86 after that mathematical sentence is not encoded. The picture in §1.2
is not encoded.
-/
public import Mathlib

@[expose] public section

noncomputable section

open Classical
open Real
open scoped goldenRatio
open Polynomial

namespace ExistenceSystem.KL1

attribute [local instance] Classical.propDecidable

local instance : DecidableEq ℝ := fun a b => Classical.propDecidable (a = b)

local instance : DecidableLT ℝ := fun a b => Classical.propDecidable (a < b)

local instance (p : ℝ → Prop) : DecidablePred p := fun a => Classical.propDecidable (p a)

/-! ## The polynomial

Note L305: "$$x^{n}=x+1\qquad\Longleftrightarrow\qquad x^{n}-x-1=0.$$"
Note L311: "For every integer $n\ge2$, $f(x)=x^{n}-x-1$ has exactly one positive real root, and it lies in $(1,2)$."
-/

/-- Note L311: "$f(x)=x^{n}-x-1$". -/
def f (n : ℕ) (x : ℝ) : ℝ := x ^ n - x - 1

/-- The polynomial `X^n - X - 1` whose positive root is `rₙ`. -/
def poly (n : ℕ) : ℝ[X] := X ^ n - X - 1

lemma eval_poly (n : ℕ) (x : ℝ) : (poly n).eval x = f n x := by
  simp [poly, f]

lemma f_one (n : ℕ) : f n 1 = -1 := by simp [f]

lemma continuous_f (n : ℕ) : Continuous (f n) := by
  unfold f
  continuity

lemma f_two_pos (n : ℕ) (hn : 2 ≤ n) : 0 < f n 2 := by
  have hpow : (2 : ℝ) ^ 2 ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hn
  have hfour : (2 : ℝ) ^ 2 = 4 := by norm_num
  simp only [f]
  linarith

lemma natDegree_X_add_one_lt (n : ℕ) (hn : 2 ≤ n) :
    (X + (1 : ℝ[X])).natDegree < ((X : ℝ[X]) ^ n).natDegree := by
  rw [← C_1, natDegree_X_add_C (1 : ℝ), natDegree_X_pow]
  omega

lemma poly_eq_sub (n : ℕ) : poly n = X ^ n - (X + 1) := by
  simpa only [poly] using (sub_sub (X ^ n) (X : ℝ[X]) (1 : ℝ[X]))

lemma poly_ne_zero (n : ℕ) (hn : 2 ≤ n) : poly n ≠ 0 := by
  intro h
  have hnd : (X ^ n - (X + (1 : ℝ[X]))).natDegree = n := by
    rw [natDegree_sub_eq_left_of_natDegree_lt (natDegree_X_add_one_lt n hn), natDegree_X_pow]
  rw [← poly_eq_sub, h, natDegree_zero] at hnd
  omega

lemma leadingCoeff_poly (n : ℕ) (hn : 2 ≤ n) : (poly n).leadingCoeff = 1 := by
  rw [poly_eq_sub, leadingCoeff_sub_of_degree_lt (degree_lt_degree (natDegree_X_add_one_lt n hn)),
    leadingCoeff_X_pow]

lemma eraseLead_X_add_one : (X + (1 : ℝ[X])).eraseLead = 1 := by
  rw [← C_1, ← self_sub_monomial_natDegree_leadingCoeff, natDegree_X_add_C (1 : ℝ),
    leadingCoeff_X_add_C (1 : ℝ), monomial_one_one_eq_X, sub_eq_add_neg, add_assoc,
    add_comm (C (1 : ℝ)) (-X), ← add_assoc, add_neg_cancel, zero_add]

lemma eraseLead_poly (n : ℕ) (hn : 2 ≤ n) : (poly n).eraseLead = -X - 1 := by
  have hlt : (-(X + (1 : ℝ[X]))).natDegree < ((X : ℝ[X]) ^ n).natDegree := by
    rw [natDegree_neg]
    exact natDegree_X_add_one_lt n hn
  have hp : poly n = -(X + 1) + X ^ n := by
    rw [poly_eq_sub, sub_eq_add_neg, add_comm]
  rw [hp, eraseLead_add_of_natDegree_lt_right hlt, eraseLead_X_pow, add_zero, neg_add,
    ← sub_eq_add_neg]

lemma leadingCoeff_negX_sub_one : (-X - (1 : ℝ[X])).leadingCoeff = -1 := by
  have h : -X - (1 : ℝ[X]) = -(X + 1) := by rw [neg_add, ← sub_eq_add_neg]
  rw [h, ← C_1, leadingCoeff_neg, leadingCoeff_X_add_C]

/-- `X + 1` has coefficient signs `+, +`: no sign change. -/
lemma signVariations_X_add_one : (X + (1 : ℝ[X])).signVariations = 0 := by
  have hne : X + (1 : ℝ[X]) ≠ 0 := by simpa using X_add_C_ne_zero (1 : ℝ)
  have hlead : (X + (1 : ℝ[X])).leadingCoeff = 1 := by simpa using leadingCoeff_X_add_C (1 : ℝ)
  have hvar1 : signVariations (1 : ℝ[X]) = 0 := by
    rw [← C_1, ← monomial_zero_left]
    exact signVariations_monomial 0 (1 : ℝ)
  rw [signVariations_eq_eraseLead_add_ite hne, eraseLead_X_add_one, hvar1, hlead, leadingCoeff_one,
    sign_pos (zero_lt_one : (0 : ℝ) < 1), ite_eq_right (by decide : (1 : SignType) ≠ -1), zero_add]

lemma signVariations_negX_sub_one : (-X - (1 : ℝ[X])).signVariations = 0 := by
  have hmul : C (-1 : ℝ) * (X + 1) = -X - 1 := by
    rw [mul_add, C_mul_X_eq_monomial, monomial_neg, monomial_one_one_eq_X, mul_one, C_neg, C_1,
      ← sub_eq_add_neg]
  rw [← hmul, signVariations_C_mul (X + 1) (by norm_num : (-1 : ℝ) ≠ 0), signVariations_X_add_one]

/-- Note L313: "The coefficient sign sequence of $f$ is $+,-,-$: a single sign change." -/
lemma signVariations_poly (n : ℕ) (hn : 2 ≤ n) : (poly n).signVariations = 1 := by
  rw [signVariations_eq_eraseLead_add_ite (poly_ne_zero n hn), eraseLead_poly n hn,
    signVariations_negX_sub_one, leadingCoeff_poly n hn, leadingCoeff_negX_sub_one,
    sign_pos (zero_lt_one : (0 : ℝ) < 1), sign_neg (by norm_num : (-1 : ℝ) < 0),
    ite_eq_left (by decide : (1 : SignType) = -(-1)), zero_add]

/-- Descartes' upper bound: at most one positive real root, counted with multiplicity.
Note L313: "from a single change the only admissible value is **exactly one**" — the upper bound
half, `Polynomial.roots_countP_pos_le_signVariations`. -/
lemma pos_roots_countP_le_one (n : ℕ) (hn : 2 ≤ n) :
    (poly n).roots.countP (fun x : ℝ => 0 < x) ≤ 1 := by
  simpa [signVariations_poly n hn] using
    (Polynomial.roots_countP_pos_le_signVariations (poly n))

/-- Note L315: "$f$ is continuous, $f(1)=-1<0$, and $f(2)=2^{n}-3>0$ for $n\ge2$, so a root lies in $(1,2)$". -/
theorem exists_root_Ioo (n : ℕ) (hn : 2 ≤ n) :
    ∃ x ∈ Set.Ioo (1 : ℝ) 2, f n x = 0 := by
  have hsub := intermediate_value_Ioo (f := f n) (a := (1 : ℝ)) (b := 2)
    (by norm_num : (1 : ℝ) ≤ 2) (continuous_f n).continuousOn
  have h0 : (0 : ℝ) ∈ Set.Ioo (f n 1) (f n 2) := by
    rw [f_one]
    exact ⟨by norm_num, f_two_pos n hn⟩
  obtain ⟨x, hx, he⟩ := hsub h0
  exact ⟨x, hx, he⟩

/-- Note L311: "For every integer $n\ge2$, $f(x)=x^{n}-x-1$ has exactly one positive real root, and it lies in $(1,2)$."
Uniqueness is the Descartes upper bound (one sign change). Existence in `(1,2)` is the intermediate value theorem. -/
theorem existsUnique_pos_root (n : ℕ) (hn : 2 ≤ n) :
    ∃! x : ℝ, 0 < x ∧ f n x = 0 := by
  obtain ⟨x0, hx0, hf0⟩ := exists_root_Ioo n hn
  have hx0pos : 0 < x0 := lt_trans zero_lt_one hx0.1
  refine ⟨x0, ⟨hx0pos, hf0⟩, ?_⟩
  intro y ⟨hypos, hyf⟩
  by_contra hne
  have hmem : ∀ {z : ℝ}, f n z = 0 → z ∈ (poly n).roots := by
    intro z hz
    rw [mem_roots']
    exact ⟨poly_ne_zero n hn, by simpa [IsRoot, eval_poly] using hz⟩
  have hcount := pos_roots_countP_le_one n hn
  have hcard : ((poly n).roots.filter (fun z : ℝ => 0 < z)).card ≤ 1 := by
    simpa [Multiset.countP_eq_card_filter] using hcount
  have hxF : x0 ∈ (poly n).roots.filter (fun z : ℝ => 0 < z) := by
    simp [Multiset.mem_filter, hmem hf0, hx0pos]
  have hyF : y ∈ (poly n).roots.filter (fun z : ℝ => 0 < z) := by
    simp [Multiset.mem_filter, hmem hyf, hypos]
  have hsub : ({x0, y} : Finset ℝ) ⊆
      ((poly n).roots.filter (fun z : ℝ => 0 < z)).toFinset := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · simpa [Multiset.mem_toFinset] using hxF
    · simpa [Multiset.mem_toFinset] using hyF
  have hxy : x0 ≠ y := fun h => hne h.symm
  have htwo : ({x0, y} : Finset ℝ).card = 2 := Finset.card_pair hxy
  have hfin : 2 ≤ ((poly n).roots.filter (fun z : ℝ => 0 < z)).toFinset.card := by
    simpa [htwo] using Finset.card_le_card hsub
  have : 2 ≤ ((poly n).roots.filter (fun z : ℝ => 0 < z)).card :=
    hfin.trans (Multiset.toFinset_card_le _)
  omega

/-- `rₙ`, the positive real root of `x^n = x + 1`. For `n < 2` the value is `1`; every theorem
about the root assumes `2 ≤ n`. -/
def r (n : ℕ) : ℝ :=
  if h : 2 ≤ n then Classical.choose (existsUnique_pos_root n h).exists else 1

theorem r_spec (n : ℕ) (hn : 2 ≤ n) : 0 < r n ∧ f n (r n) = 0 := by
  rw [r, dite_eq_left hn]
  exact Classical.choose_spec (existsUnique_pos_root n hn).exists

theorem r_eq_of_pos_root (n : ℕ) (hn : 2 ≤ n) {x : ℝ} (hx : 0 < x) (hf : f n x = 0) :
    x = r n :=
  (existsUnique_pos_root n hn).unique ⟨hx, hf⟩ (r_spec n hn)

/-- Note L311: the positive root "lies in $(1,2)$". -/
theorem r_mem_Ioo (n : ℕ) (hn : 2 ≤ n) : r n ∈ Set.Ioo (1 : ℝ) 2 := by
  obtain ⟨x, hx, hf⟩ := exists_root_Ioo n hn
  have hxpos : 0 < x := lt_trans zero_lt_one hx.1
  have heq : x = r n := r_eq_of_pos_root n hn hxpos hf
  simpa [heq] using hx

/-- Note L305 / L319: "$r_n^{\,n}=r_n+1$". -/
theorem r_pow (n : ℕ) (hn : 2 ≤ n) : (r n) ^ n = r n + 1 := by
  have h := (r_spec n hn).2
  simp only [f] at h
  linarith

/-- Note L321: "Hence $r_{n+1}<r_n$: the roots descend monotonically".
Evaluated as in L319: `g(rₙ) = rₙ² - 1 > 0`, so `rₙ₊₁ ∈ (1, rₙ)`. -/
theorem r_succ_lt (n : ℕ) (hn : 2 ≤ n) : r (n + 1) < r n := by
  have hr := r_mem_Ioo n hn
  have hpow := r_pow n hn
  have hg : f (n + 1) (r n) = (r n) ^ 2 - 1 := by
    simp only [f]
    calc
      (r n) ^ (n + 1) - r n - 1 = r n * (r n) ^ n - r n - 1 := by rw [pow_succ']
      _ = r n * (r n + 1) - r n - 1 := by rw [hpow]
      _ = (r n) ^ 2 - 1 := by ring
  have hgpos : 0 < f (n + 1) (r n) := by
    rw [hg]
    nlinarith [hr.1]
  have hcont : ContinuousOn (f (n + 1)) (Set.Icc 1 (r n)) := (continuous_f _).continuousOn
  have h0 : (0 : ℝ) ∈ Set.Ioo (f (n + 1) 1) (f (n + 1) (r n)) := by
    rw [f_one]
    exact ⟨by norm_num, hgpos⟩
  obtain ⟨y, hy, hyf⟩ := (intermediate_value_Ioo hr.1.le hcont) h0
  have hypos : 0 < y := lt_trans zero_lt_one hy.1
  have heq : y = r (n + 1) := r_eq_of_pos_root (n + 1) (by omega) hypos hyf
  rw [← heq]
  exact hy.2

/-- Note L321: "bounded below by 1". The root lies in `(1,2)`, so the bound is strict. -/
theorem one_lt_r (n : ℕ) (hn : 2 ≤ n) : 1 < r n :=
  (r_mem_Ioo n hn).1

/-- Note L321: "And $L=1$: were $L>1$, then $r_n^{\,n}\ge L^{\,n}\to\infty$, contradicting $r_n^{\,n}=r_n+1\le3$. Hence $r_n\to1^{+}$." -/
theorem tendsto_r : Filter.Tendsto r Filter.atTop (nhds (1 : ℝ)) := by
  let s : ℕ → ℝ := fun k => r (k + 2)
  have hanti : Antitone s :=
    antitone_nat_of_succ_le fun k => (r_succ_lt (k + 2) (by omega)).le
  have hbdd : BddBelow (Set.range s) := by
    refine ⟨1, ?_⟩
    rintro y ⟨k, rfl⟩
    exact (one_lt_r (k + 2) (by omega)).le
  have hlim : Filter.Tendsto s Filter.atTop (nhds (⨅ k, s k)) :=
    tendsto_atTop_ciInf hanti hbdd
  have hL : ⨅ k, s k = 1 := by
    set L : ℝ := ⨅ k, s k
    have hle : (1 : ℝ) ≤ L := le_ciInf fun k => (one_lt_r (k + 2) (by omega)).le
    refine le_antisymm ?_ hle
    by_contra h
    have hgt : (1 : ℝ) < L := not_le.mp h
    have hpow : Filter.Tendsto (fun k : ℕ => L ^ (k + 2)) Filter.atTop Filter.atTop :=
      (tendsto_pow_atTop_atTop_of_one_lt hgt).comp (Filter.tendsto_add_atTop_nat 2)
    have hlt : ∀ k, L ^ (k + 2) < 3 := by
      intro k
      have hk : 2 ≤ k + 2 := by omega
      have hr := r_mem_Ioo (k + 2) hk
      have heq : s k ^ (k + 2) = s k + 1 := by
        have hf := (r_spec (k + 2) hk).2
        simp only [f] at hf
        linarith
      have hLs : L ≤ s k := ciInf_le hbdd k
      calc
        L ^ (k + 2) ≤ s k ^ (k + 2) :=
          pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ L) hLs _
        _ = s k + 1 := heq
        _ < 3 := by linarith [hr.2]
    obtain ⟨k, hk⟩ := (hpow.eventually_gt_atTop (3 : ℝ)).exists
    linarith [hlt k, hk]
  have htail : Filter.Tendsto s Filter.atTop (nhds (1 : ℝ)) := by simpa [hL] using hlim
  exact (Filter.tendsto_add_atTop_iff_nat 2).1 htail

/-! ## The two faces

Note L86: "φ is its planar face and the plastic number ρ its spatial face."
Note L331: "One constant per dimension: $\varphi$ the planar face, $\rho$ the spatial face."
-/

/-- Note L86 / L331: "$\varphi$ is its planar face" — the `n = 2` root, Mathlib's golden ratio,
the unique positive root of `x^2 = x + 1`. -/
theorem planar_face : φ = r 2 := by
  have hpos : 0 < φ := lt_trans zero_lt_one one_lt_goldenRatio
  have hf : f 2 φ = 0 := by
    have hsq : φ ^ 2 = φ + 1 := goldenRatio_sq
    simp only [f]
    linarith
  exact r_eq_of_pos_root 2 le_rfl hpos hf

/-- The spatial face: the plastic number `ρ = r₃`. -/
def ρ : ℝ := r 3

/-- Note L86 / L331: "the plastic number $\rho$ its spatial face" — the `n = 3` member. -/
theorem spatial_face : ρ = r 3 := rfl

/-- Note L325: the condition at `n = 3` is "$x^{3}=x+1$". -/
theorem rho_cube : ρ ^ 3 = ρ + 1 := by
  have h := (r_spec 3 (by omega)).2
  simp only [f] at h
  unfold ρ
  linarith

/-- `ρ` is the unique positive real root of `x^3 = x + 1`. -/
theorem rho_unique {x : ℝ} (hx : 0 < x) (h : x ^ 3 = x + 1) : x = ρ := by
  have hf : f 3 x = 0 := by simp only [f]; linarith
  simpa [ρ] using r_eq_of_pos_root 3 (by omega) hx hf

end ExistenceSystem.KL1

end

end
