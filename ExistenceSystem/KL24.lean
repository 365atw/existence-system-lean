module

/-
KL24 — Lemma 3, the Gradient-Only Divergence Lemma (§6.2), from THE EXACT AND FREE SYSTEM —
AN EXISTENCE SYNTHESIS. All mathematics: Kari A Light.

Source: `THE-NOTE-EDITED.md` (194,868 bytes, 1,539 lines). Line numbers below refer to that file.
Her words are quoted exactly beside each statement. Nothing of hers is graded here.

Note L132 (front-matter list form):
"**KL24 — the Gradient-Only Divergence Lemma.** *J* depends on the phason field only through its
gradient, pointwise; so its Euler–Lagrange derivative is a divergence."

Note L829–L831 (Lemma 3, body), verbatim:
"**Lemma 3 — The Gradient-Only Divergence Lemma (KL24).** J depends on the phason field only
through its gradient, *pointwise*, and therefore
  δJ/δw_m = −∂_k Π_km,  Π_km := ∂f_el/∂(∂_k w_m) = K₁ ∂_k w_m + K₂ T_kmpq ∂_p w_q + K₃ M_kmpq u_pq,
exactly, at every order in both the amplitude expansion and the gradient expansion."

Note L833–L836 (her proof, two steps), verbatim:
"1. **The Landau part is pointwise w-independent.** By Lemma 2 (§4.6), every term of f_L is a
monomial indexed by a closure ∑G=0 in ℤ⁶. Such a term carries the phase factor
exp[i π_⊥(∑G)·w(x)] evaluated at the single point x. By the Closure Transfer Lemma, π_⊥(∑G)=0. The
factor is exp(i·0)=1 **at every point x separately**. … 2. **The elastic part contains only
gradients.** No term linear in ∇w exists (Γ₃⊗Γ₃' contains no identity, §4.8(3)); no term in bare w
exists by step 1; so f_el=f_el(∇w,u_kl,…). Any higher-gradient term admissible at higher order is
likewise a function of ∂w,∂∂w,…, because step 1 forbids bare w at every order. The Euler–Lagrange
derivative of any such functional is a divergence. ∎"

Reading choices and scope (map `data/lean-scope-b/G5.md` §2, `report.md` l.146, l.489):

* **Dependencies, leaves-first.** The proof rests on her **KL22** (Lemma 2, the Admissibility
  Lemma) and **KL21** (the Closure Transfer Lemma), both merged on `main` and imported, not
  rebuilt; and on §4.8(3) = KL7 reason 3 (representation content, borrowed). The first-order
  Euler–Lagrange calculus is the shared layer-0 module `ExistenceSystem.EulerLagrange`, likewise
  imported and reused: its `el_gradientOnly`, `gradDensity`, `piStress` and
  `hasDerivAt_gradDensity` are step 2 at the displayed (quadratic) order.

* **Step 1 is the genuinely new content here, and it is proved at every order in the amplitude
  expansion.** A term of f_L is a monomial `∏_m n_{G_m}` carried, exactly as in KL22, by a finite
  family `c : Fin M → (Fin 6 → ℤ)` of reciprocal indices upstairs (any order = any M). Its
  reciprocal lattice vectors are `G_m = A·(c m) ∈ ℒ` (`recipVec`); the **perpendicular** phase the
  monomial carries at the field value `w(x) ∈ E_⊥` is `exp[i π_⊥(∑_m G_m)·w]` (`monoPhasePerp`,
  the π_⊥-mirror of KL22's translation phase `monoPhase`). Her step 1 is `landau_term_phase_trivial`:
  a closure `∑_m c m = 0` (KL22's admissibility output) forces `∑_m π_⊥(G_m)=0` **by the Closure
  Transfer Lemma** (`KL21.closure_transfer`, the "dragged along" direction), so the factor is
  `exp(i·0)=1` at every point x separately. `landau_pointwise_w_independent` reads off the
  consequence: a density that is a finite sum of admissible terms is constant in `w` — the Landau
  part is pointwise w-independent — so its bare-field partial vanishes (`landau_bare_partial_zero`).

* **Step 2 is reused from `EulerLagrange`.** `displayed_piStress` is her displayed `Π_km` at
  quadratic order (`hasDerivAt_gradDensity`, with the pair symmetry `T_klmn = T_mnkl` carried as a
  hypothesis — §2.5: the Note does not state it, a formaliser takes it from [30] or assumes it).
  `gradient_only_divergence` is the capstone: step 1 kills the bare-field partial, and then the
  Euler–Lagrange derivative is the pure divergence `−∂_k Π_km` (`EulerLagrange.el` with a zero bare
  slot). The one-variable reduction is what the shared module supports; the general functional
  derivative over 3-D fields is the deepest, library-scale frontier (`report.md` l.442: "a project
  as general library"), carried, not built.

* **Not formalisable as written (`data/lean-scope-b/G5.md` §2.5), carried as prose, never a `sorry`:**
  "the Euler–Lagrange derivative of any such functional is a divergence" for the higher-gradient
  "every order" class — the admissible class at every gradient order is not defined in the Note;
  the general `Π` beyond the displayed quadratic one; and the tensors `T,M` (borrowed [30]). Step 1
  here is at every amplitude order; the displayed `Π` and the divergence are the quadratic-order
  instance.
-/
public import ExistenceSystem.KL21
public import ExistenceSystem.KL22
public import ExistenceSystem.EulerLagrange

@[expose] public section

open Real Matrix

namespace ExistenceSystem.KL24

open ExistenceSystem.Icosahedral ExistenceSystem.KL21 ExistenceSystem.KL22

/-! ## Step 1 — a term of f_L, its reciprocal lattice vectors, and their perpendicular phase

Note L833–L834: "every term of f_L is a monomial indexed by a closure ∑G=0 in ℤ⁶. Such a term
carries the phase factor exp[i π_⊥(∑G)·w(x)]." The carrier is KL22's: a monomial `∏_m n_{G_m}` is a
finite family `c : Fin M → (Fin 6 → ℤ)` of reciprocal indices upstairs. -/

/-- The reciprocal lattice vector `G = A·c ∈ ℒ` of a single amplitude with integer coordinates `c`
upstairs: the integer combination of the rows of `A` (Note L506, `Icosahedral.lattice`). -/
noncomputable def recipVec (c : Fin 6 → ℤ) : Fin 6 → ℝ :=
  fun j => ∑ i : Fin 6, (c i : ℝ) * Icosahedral.row i j

/-- `recipVec c ∈ ℒ`: the reciprocal vector of any amplitude is a lattice point. -/
theorem recipVec_mem_lattice (c : Fin 6 → ℤ) : recipVec c ∈ Icosahedral.lattice :=
  Icosahedral.mem_lattice_rows c

/-- `recipVec 0 = 0`. -/
theorem recipVec_zero : recipVec (0 : Fin 6 → ℤ) = 0 := by
  funext j
  simp [recipVec]

/-- `recipVec` is additive on reciprocal indices across a finite family: the total reciprocal
vector `∑_m G_m` is the reciprocal vector of the total index `∑_m c m`. -/
theorem recipVec_sum {M : ℕ} (c : Fin M → (Fin 6 → ℤ)) :
    (∑ m, recipVec (c m)) = recipVec (∑ m, c m) := by
  funext j
  simp only [recipVec, Finset.sum_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  push_cast
  rw [Finset.sum_mul]

/-- Note L834: "Such a term carries the phase factor exp[i π_⊥(∑G)·w(x)]." The perpendicular phase a
single amplitude `n_G` acquires at the field value `w = w(x) ∈ E_⊥`: `exp[i π_⊥(G)·w]`, with
`π_⊥(G) = perpProj (recipVec c)` the perpendicular-space projection of its lattice vector (KL21). -/
noncomputable def ampPhasePerp (c : Fin 6 → ℤ) (w : Fin 3 → ℝ) : ℂ :=
  Complex.exp (Complex.I * (↑(perpProj (recipVec c) ⬝ᵥ w) : ℂ))

/-- Note L834: the monomial `∏_m n_{G_m}`, carried by the finite family `c`, carries at the field
value `w` the product of its amplitudes' perpendicular phase factors — the π_⊥-mirror of KL22's
translation phase `monoPhase`. -/
noncomputable def monoPhasePerp {M : ℕ} (c : Fin M → (Fin 6 → ℤ)) (w : Fin 3 → ℝ) : ℂ :=
  ∏ m, ampPhasePerp (c m) w

/-- π_⊥ (`perpProj`) is additive across a finite family (it reads off three coordinates). -/
private lemma perpProj_sum {M : ℕ} (G : Fin M → (Fin 6 → ℝ)) :
    perpProj (∑ m, G m) = ∑ m, perpProj (G m) := by
  funext k
  simp only [perpProj, Finset.sum_apply]

/-- **Note L834.** "a term carries the phase factor exp[i π_⊥(∑G)·w(x)]." The product of the
single-amplitude perpendicular phases collapses to one phase driven by the total perpendicular
projection `∑_m π_⊥(G_m)`. -/
theorem monoPhasePerp_eq {M : ℕ} (c : Fin M → (Fin 6 → ℤ)) (w : Fin 3 → ℝ) :
    monoPhasePerp c w
      = Complex.exp (Complex.I * (↑((∑ m, perpProj (recipVec (c m))) ⬝ᵥ w) : ℂ)) := by
  unfold monoPhasePerp ampPhasePerp
  rw [← Complex.exp_sum, ← Finset.mul_sum, ← Complex.ofReal_sum, sum_dotProduct]

/-! ## Step 1 — the Landau part is pointwise w-independent (Note L833–L834) -/

/-- **KL24 step 1 (Note L833–L834).** A term of f_L indexed by an exact closure `∑_m c m = 0` in ℤ⁶
(KL22's admissibility output) carries, at every point `x`, the trivial phase factor: `monoPhasePerp
c w = 1` for every field value `w`. The engine is her sentence "By the Closure Transfer Lemma,
π_⊥(∑G)=0": the six-dimensional closure drags the perpendicular closure along
(`KL21.closure_transfer`), so `∑_m π_⊥(G_m)=0` and the factor is `exp(i·0)=1` at every point x
separately. -/
theorem landau_term_phase_trivial {M : ℕ} (c : Fin M → (Fin 6 → ℤ))
    (hclosure : (∑ m, c m) = 0) (w : Fin 3 → ℝ) : monoPhasePerp c w = 1 := by
  -- The reciprocal vectors `G_m = A·(c m)` are lattice points, and their sum vanishes.
  have hG : ∀ m ∈ (Finset.univ : Finset (Fin M)), recipVec (c m) ∈ Icosahedral.lattice :=
    fun m _ => recipVec_mem_lattice (c m)
  have hsum0 : (∑ m, recipVec (c m)) = 0 := by
    rw [recipVec_sum, hclosure, recipVec_zero]
  -- "By the Closure Transfer Lemma, π_⊥(∑G)=0": the dragged-along perpendicular closure.
  have hperp0 : (∑ m, perpProj (recipVec (c m))) = 0 :=
    ((closure_transfer Finset.univ (fun m => recipVec (c m)) hG).2).mp hsum0
  rw [monoPhasePerp_eq, hperp0]
  simp

/-! ## Step 1 — the whole Landau density is constant in the field; its bare partial vanishes

Her step 1 conclusion (Note L833): "The Landau part is pointwise w-independent." Model the Landau
density's dependence on the field value as a finite sum of admissible terms with complex
coefficients, each term `a_j · (its phase factor)`. A term of varying amplitude order is carried by
a dependent pair `⟨M, c⟩`; the order is `M`. -/

/-- The Landau density, as a real function of the field value `w` taken constant over the sample (a
one-parameter slice `fun _ => w` of the field value `w(x) ∈ E_⊥`). It is a finite sum of admissible
terms `a_j · (phase factor of term j)`, each term `c j` carried at its own amplitude order. -/
noncomputable def landauScalar {N : ℕ} (a : Fin N → ℂ)
    (c : Fin N → Σ M : ℕ, Fin M → (Fin 6 → ℤ)) (w : ℝ) : ℝ :=
  (∑ j, a j * monoPhasePerp (c j).2 (fun _ => w)).re

/-- **KL24 step 1 (Note L833), the Landau part is pointwise w-independent.** When every term is
admissible (`∑_m c j m = 0`), the Landau density does not depend on the field at all: it equals the
constant `(∑_j a_j).re`. Each term's phase factor is `1` at every point (`landau_term_phase_trivial`). -/
theorem landau_pointwise_w_independent {N : ℕ} (a : Fin N → ℂ)
    (c : Fin N → Σ M : ℕ, Fin M → (Fin 6 → ℤ))
    (hadm : ∀ j, (∑ m, (c j).2 m) = 0) :
    landauScalar a c = fun _ => (∑ j, a j).re := by
  funext w
  unfold landauScalar
  have hterm : ∀ j, a j * monoPhasePerp (c j).2 (fun _ => w) = a j := by
    intro j
    rw [landau_term_phase_trivial (c j).2 (hadm j), mul_one]
  rw [Finset.sum_congr rfl (fun j _ => hterm j)]

/-- **The bare-field partial of the Landau density vanishes (Note L833).** Because the Landau part
is pointwise w-independent (`landau_pointwise_w_independent`), its derivative in the field value is
zero at every point — exactly "step 1 forbids bare w". This is the zero that feeds the
Euler–Lagrange operator's bare-field slot. -/
theorem landau_bare_partial_zero {N : ℕ} (a : Fin N → ℂ)
    (c : Fin N → Σ M : ℕ, Fin M → (Fin 6 → ℤ))
    (hadm : ∀ j, (∑ m, (c j).2 m) = 0) (w₀ : ℝ) :
    deriv (landauScalar a c) w₀ = 0 := by
  rw [landau_pointwise_w_independent a c hadm]
  simp

/-! ## Step 2 — the displayed Π at quadratic order, and the gradient-only divergence

Reused from the shared `EulerLagrange` module. The elastic density has no term linear in ∇w
(Γ₃⊗Γ₃' contains no identity, §4.8(3), borrowed), so `EulerLagrange.gradDensity` — purely quadratic
plus the strain coupling — is its form at the displayed order. -/

open ExistenceSystem.EulerLagrange in
/-- **Note L831, her displayed `Π_km` at quadratic order.** The partial of the elastic gradient
density in the slot `∂_a w_b` is `Π_ab = K₁ ∂_a w_b + K₂ T_abpq ∂_p w_q + K₃ M_abpq u_pq`
(`EulerLagrange.piStress`). The pair symmetry `T_klmn = T_mnkl` (hypothesis `hT`) is what the Note
does not state and a formaliser takes from [30] (§2.5); a `phonon` term with no ∇w does not
contribute. Reuses `EulerLagrange.hasDerivAt_gradDensity`; nothing is rebuilt. -/
theorem displayed_piStress {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K1 K2 K3 : ℝ) (T M : ι → ι → ι → ι → ℝ) (u g : ι → ι → ℝ) (a b : ι) (phonon : ℝ)
    (hT : ∀ k l m n, T k l m n = T m n k l) :
    HasDerivAt (fun t => gradDensity K1 K2 K3 T M u (setEntry g a b t) + phonon)
      (piStress K1 K2 K3 T M u g a b) (g a b) :=
  hasDerivAt_gradDensity K1 K2 K3 T M u g a b phonon hT

/-- **KL24, the Gradient-Only Divergence Lemma (Note L829–L836), capstone at the displayed order.**
Because the Landau part is pointwise w-independent (step 1, `landau_bare_partial_zero`) and the
elastic part contains only gradients (step 2), the full density has **no bare-field term**: its
Euler–Lagrange derivative carries no `∂f/∂w` contribution and is the pure divergence
`δJ/δw_m = −∂_k Π_km`. Here, in the one-variable reduction the shared `EulerLagrange` module
supports, that is `−dΠ/dx`. Step 1 supplies the vanishing bare slot `deriv (landauScalar a c)`;
`EulerLagrange.el` then returns exactly the divergence. -/
theorem gradient_only_divergence {N : ℕ} (a : Fin N → ℂ)
    (c : Fin N → Σ M : ℕ, Fin M → (Fin 6 → ℤ))
    (hadm : ∀ j, (∑ m, (c j).2 m) = 0) (stress : ℝ → ℝ) (x : ℝ) :
    EulerLagrange.el (deriv (landauScalar a c)) stress x = -deriv stress x := by
  have hzero : deriv (landauScalar a c) x = 0 := landau_bare_partial_zero a c hadm x
  simp only [EulerLagrange.el, hzero, zero_sub]

end ExistenceSystem.KL24

end
