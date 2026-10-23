module

/-
KL6 — The No-Pinning Theorem (phason flatness, §4.6), from THE EXACT AND FREE SYSTEM —
AN EXISTENCE SYNTHESIS. All mathematics: Kari A Light.

Source: `THE-NOTE-EDITED.md` (194,868 bytes, 1,539 lines). Line numbers below refer to that file.
Her words are quoted exactly beside each statement. Nothing of hers is graded here.

Note L96 (front-matter list form), verbatim:
"J is identically independent of the uniform phason — J(w+w₀)=J(w) for every w₀∈E_⊥, hence every
derivative in w vanishes identically, at every order, amplitude and temperature — because every
admissible term is indexed by a ℤ⁶ closure and the irrationality of φ lifts every physical closure
to a six-dimensional one. **The phason is exactly free because φ is irrational** — with the
irrationality supplying the injectivity and the quadratic algebraicity of φ supplying the conjugate
embedding E_⊥ into which the closure lifts. *Proved in §4.6–§4.7; verified, Appendix A item 6.*
*Rests on the Star Independence Lemma (KL20), the Closure Transfer Lemma (KL21) and the
Admissibility Lemma (KL22).*"

Note L661 (Theorem, the No-Pinning Theorem, KL6, body), verbatim:
"Apply a uniform phason shift w ↦ w+w₀, w₀∈E_⊥ constant. Then n_i ↦ n_i e^{iQ_i^⊥·w₀} and
m_a ↦ m_a e^{iS_a^⊥·w₀}. Term by term:
 1. **Quadratic** a₁∑|n_i|², a₂∑|m_a|²: moduli are untouched by pure phase factors. **Unchanged.**
 2. **All quartics** b₁…b₅: built from |n_i|² and |m_a|² only. **Unchanged.**
 3. **Mixed cubic** C∑_{T₁}(n_i n_j m_a^* + c.c.): acquires exp[i(Q_i^⊥+Q_j^⊥−S_a^⊥)·w₀]. By the
    Closure Transfer Lemma, (i,j,a)∈T₁ means Q_i+Q_j−S_a=0 in E_∥, hence the same relation holds in
    E_⊥ — for all 60 signed mixed triads, residual exactly 0. Factor = e^{i0}=1. **Unchanged.**
 4. **Pure cubic** C'∑_{T₂}(m_a m_b m_c + c.c.): acquires exp[i(S_a^⊥+S_b^⊥+S_c^⊥)·w₀]=1 by the
    same corollary — for all 20 signed triads per sub-shell, maximum residual 1.6×10⁻¹⁶. **Unchanged.**
 5. **Elastic sector.** f_el contains only *gradients* of w. For constant w₀, ∂_k w₀=0: every phason
    term **and the K₃ phonon–phason coupling** vanish identically. **Unchanged.**"

Note L669 (boxed), verbatim:
"J(w+w₀)=J(w) ⟹ ∂J/∂w|_uniform ≡ 0, ∂^k J/∂w^k|_uniform ≡ 0 ∀k≥1."

Note L675 (the calculation in one line), verbatim:
"∂J₃/∂w = 2C ∑_T η₁η₂η₃ sin(Θ_T)·π_⊥(∑_{G∈T} G) = ∑_T(···)·π_⊥(0) = 0."
Note L677: "Every summand carries the **zero vector** as its coefficient — *before* any evaluation of
sin(·), *before* any stationarity condition, *before* any temperature is chosen."

Reading choices and scope (map `data/lean-scope-b/G2.md`, KL6, §4.6–§4.7, l.269–345):

* This is the **π_⊥ adapter** of the one character-action **seam** KL22 built on the π_∥ side: "a
  character action on a weight-graded polynomial ring; invariant iff weight 0", with the phonon
  translation (weight π_∥, KL22) and the phason shift (weight π_⊥, here) as its two adapters (map §2,
  the architecture note). The deep step is **reused, not rebuilt**: `KL22.phase_trivial_iff`
  (e^{ik·u}=1 ∀u ⟺ k=0) is fully general in the wavevector and serves both sides; the π_⊥ arithmetic
  is KL21's `no_integer_relation_perp`. Nothing of KL20–KL22 is rebuilt here.

* **The carrier is KL22's.** A *term* is a monomial `∏_m n_{G_m}` carried by a finite family
  `c : Fin M → (Fin 6 → ℤ)` of reciprocal indices (each `G_m ∈ ℒ = A(ℤ⁶)`, named by its integer
  coordinates upstairs; a conjugate amplitude `n_G^*` is the index `-G`; "any order" is any `M`).
  Both shells' amplitudes `n_i` and `m_a` are indices of this one carrier, so items 3 and 4 are one
  statement over all signed triads. The Note's `J` itself (its amplitude variables, whether "any
  order" is every degree or a power series) is U28/G4 and is **not built here**, exactly as in KL22.

* The phason shift acts on an amplitude by `n_G ↦ n_G e^{iπ_⊥(G)·w₀}` (`ampPhasePerp`), the π_⊥
  mirror of `KL22.ampPhase`; the monomial's acquired factor is the product (`monoPhasePerp`), which
  `monoPhasePerp_eq` collapses to `exp[iπ_⊥(∑_m G_m)·w₀]`. **Items 1–2** ("moduli untouched by pure
  phase factors") are `ampPhasePerp_norm` (`‖e^{ix·I}‖=1`). **Items 3–4** are
  `admissible_phason_invariant` / `phason_invariant_iff_closure`: the factor is 1 for every `w₀` iff
  the indices close in ℤ⁶ — the perpendicular closure dragged along by the physical one (KL21).
  **Item 5** ("for constant w₀, ∂_k w₀=0") is `uniform_shift_grad_zero` / `elastic_uniform_invariant`:
  a uniform shift leaves every gradient of `w`, hence `f_el`, untouched. The **boxed derivative
  corollary** (L669) is `no_pinning_fderiv` / `no_pinning_iteratedFDeriv`: `w₀ ↦ (admissible term)`
  is strictly constant (`phasonTerm_const`, J(w+w₀)=J(w)), so every Fréchet derivative of order `≥ 1`
  vanishes. The **one-line calculation** (L675, L677) is `perp_coefficient_zero` / `summand_zero`:
  each summand carries `π_⊥(∑G)=π_⊥(0)=0` as its coefficient, before any `sin(·)`.

Not encoded (map G2.md §5, her own markings quoted, no verdict on her work):
* "It therefore survives … **beyond mean field** (it is a Ward identity of a continuous symmetry)"
  (L679) — a statement about a statistical field theory the Note does not set up; nothing in the Note
  defines the measure or the fluctuation theory it would hold in.
* "*verified, Appendix A item 6*" — a finite numerical census (A.2/A.4), corroboration at finitely
  many closures; the general statement rests on KL20–KL22.
* **Borrowed, hers-marked (I-088, protection paragraph L679).** "w is the Goldstone coordinate of the
  broken E_⊥ translational symmetry, by Goldstone's theorem [26,27,28,29] (A11). … The
  phason-as-Goldstone fact is theirs and is not claimed here; what is constructed here is the
  functional in which it becomes a term-by-term identity indexed by ℤ⁶ closure." (L679). Prior
  uniform-phason flatness: Zeyher & Finger, PRL 49, 1833 (1982) [61], "Established, cited, never
  claimed". The protection reading — "symmetry, not fine-tuning" — is her interpretation of the same
  identity, not a further proposition; it is recorded here, not graded.
-/
public import Mathlib
public import ExistenceSystem.KL21
public import ExistenceSystem.KL22

@[expose] public section

open Real Matrix

namespace ExistenceSystem.KL6

open ExistenceSystem.Icosahedral ExistenceSystem.KL21 ExistenceSystem.KL22

/-! ## The phason shift as a unit-modulus phase on the amplitudes (Note L661, items 1–2) -/

/-- Note L661: "n_i ↦ n_i e^{iQ_i^⊥·w₀}." The phase factor a single amplitude `n_G`, with `G` the
lattice vector of integer coordinates `c`, acquires under a uniform phason shift `w ↦ w+w₀`,
`w₀ ∈ E_⊥`. The π_⊥ mirror of `KL22.ampPhase`. -/
noncomputable def ampPhasePerp (c : Fin 6 → ℤ) (w₀ : Fin 3 → ℝ) : ℂ :=
  Complex.exp (Complex.I * (↑(piPerp (fun i => (c i : ℝ)) ⬝ᵥ w₀) : ℂ))

/-- **Note L661, items 1–2.** "moduli are untouched by pure phase factors." The phason factor has
modulus one, so the quadratic terms a₁∑|n_i|², a₂∑|m_a|² and the quartics b₁…b₅ built from |n_i|²,
|m_a|² only are unchanged. -/
theorem ampPhasePerp_norm (c : Fin 6 → ℤ) (w₀ : Fin 3 → ℝ) : ‖ampPhasePerp c w₀‖ = 1 := by
  unfold ampPhasePerp
  rw [mul_comm]
  exact Complex.norm_exp_ofReal_mul_I _

/-- Items 1–2, product form: an amplitude scaled by the phason factor keeps its modulus — the
quadratic/quartic data `|n_G|` is invariant under the shift. -/
theorem norm_mul_ampPhasePerp (c : Fin 6 → ℤ) (w₀ : Fin 3 → ℝ) (z : ℂ) :
    ‖ampPhasePerp c w₀ * z‖ = ‖z‖ := by
  rw [norm_mul, ampPhasePerp_norm, one_mul]

/-! ## The monomial acquires the product factor (Note L666) -/

/-- Note L666: a monomial `∏_m n_{G_m}`, carried by the finite family `c` of reciprocal indices,
acquires the product of its amplitudes' phason factors under the uniform shift. π_⊥ mirror of
`KL22.monoPhase`. -/
noncomputable def monoPhasePerp {M : ℕ} (c : Fin M → (Fin 6 → ℤ)) (w₀ : Fin 3 → ℝ) : ℂ :=
  ∏ m, ampPhasePerp (c m) w₀

/-- π_⊥ of the summed integer coordinates is the sum of the π_⊥ images: additivity of `piPerp` over
a finite family. π_⊥ mirror of `KL22.piParallel_sum`. -/
theorem piPerp_sum {M : ℕ} (c : Fin M → (Fin 6 → ℤ)) :
    piPerp (fun i => ((∑ m, c m) i : ℝ)) = ∑ m, piPerp (fun i => (c m i : ℝ)) := by
  funext k
  simp only [piPerp, Finset.sum_apply]
  push_cast
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.sum_mul]

/-- **Note L665.** "acquires exp[i(Q_i^⊥+Q_j^⊥−S_a^⊥)·w₀]." The product of single-amplitude phason
factors collapses to one phase, driven by the total reciprocal index `∑_m G_m`. π_⊥ mirror of
`KL22.monoPhase_eq`. -/
theorem monoPhasePerp_eq {M : ℕ} (c : Fin M → (Fin 6 → ℤ)) (w₀ : Fin 3 → ℝ) :
    monoPhasePerp c w₀
      = Complex.exp (Complex.I * (↑(piPerp (fun i => ((∑ m, c m) i : ℝ)) ⬝ᵥ w₀) : ℂ)) := by
  unfold monoPhasePerp ampPhasePerp
  rw [← Complex.exp_sum, ← Finset.mul_sum, ← Complex.ofReal_sum, piPerp_sum, sum_dotProduct]

/-! ## The arithmetic step: π_⊥(∑ G_m)=0 ⟺ ∑ G_m=0 in ℤ⁶ (Note L665, via KL21) -/

/-- **Note L665, "the same relation holds in E_⊥".** The perpendicular projection of the total
reciprocal index vanishes iff the integer closure holds: physical closure is dragged to perpendicular
closure (KL21, `no_integer_relation_perp`). π_⊥ mirror of `KL22.piParallel_zero_iff_closure`. -/
theorem piPerp_zero_iff_closure {M : ℕ} (c : Fin M → (Fin 6 → ℤ)) :
    piPerp (fun i => ((∑ m, c m) i : ℝ)) = 0 ↔ (∑ m, c m) = 0 := by
  constructor
  · intro h
    exact no_integer_relation_perp _ h
  · intro h
    funext k
    rw [h]
    simp [piPerp]

/-! ## Items 3–4: the admissible cubics are left strictly invariant (Note L665–666) -/

/-- **Note L665–666, items 3–4.** "Factor = e^{i0}=1. **Unchanged.**" A monomial term whose
reciprocal indices close exactly in ℤ⁶ (`∑_m G_m = 0`, KL22's admissibility criterion) is left
strictly invariant by *every* uniform phason shift: its acquired factor is 1. The 60 signed mixed
triads (T₁) and the 20-per-sub-shell pure triads (T₂) are admissible, hence unchanged. -/
theorem admissible_phason_invariant {M : ℕ} (c : Fin M → (Fin 6 → ℤ)) (h : (∑ m, c m) = 0)
    (w₀ : Fin 3 → ℝ) : monoPhasePerp c w₀ = 1 := by
  rw [monoPhasePerp_eq]
  exact (KL22.phase_trivial_iff _).mpr ((piPerp_zero_iff_closure c).mpr h) w₀

/-- **KL6, items 3–4 (the full equivalence).** A monomial term `∏_m n_{G_m}` is invariant under
*every* uniform phason shift `w ↦ w+w₀`, `w₀ ∈ E_⊥`, iff its reciprocal indices close exactly in ℤ⁶.
The π_⊥ mirror of `KL22.admissible_iff_closure`: one character-action seam, the phason adapter. -/
theorem phason_invariant_iff_closure {M : ℕ} (c : Fin M → (Fin 6 → ℤ)) :
    (∀ w₀ : Fin 3 → ℝ, monoPhasePerp c w₀ = 1) ↔ (∑ m, c m) = 0 := by
  constructor
  · intro hw
    apply (piPerp_zero_iff_closure c).mp
    apply (KL22.phase_trivial_iff _).mp
    intro w₀
    rw [← monoPhasePerp_eq]
    exact hw w₀
  · intro h w₀
    exact admissible_phason_invariant c h w₀

/-! ## Item 5: the elastic sector sees only gradients, and a uniform shift has none (Note L667) -/

/-- **Note L667, item 5.** "For constant w₀, ∂_k w₀=0." The gradient of a uniform phason value is the
zero map: a constant field has no gradient, so every phason term of `f_el` and the K₃ phonon–phason
coupling — built from gradients of `w` only — vanish identically for a uniform shift. -/
theorem uniform_shift_grad_zero (w₀ : Fin 3 → ℝ) (r : Fin 3 → ℝ) :
    fderiv ℝ (fun _ : Fin 3 → ℝ => w₀) r = 0 :=
  fderiv_const_apply w₀

/-- **Note L667, item 5 (invariance form).** A uniform phason shift `w ↦ w+w₀` leaves every gradient
of the phason field untouched — `∇(w+w₀)=∇w` — so every elastic density built from those gradients,
and the K₃ coupling, is **unchanged**. Here `wfield : ℝ³ → ℝ³` is the phason field in position. -/
theorem elastic_uniform_invariant (wfield : (Fin 3 → ℝ) → (Fin 3 → ℝ)) (w₀ : Fin 3 → ℝ)
    (r : Fin 3 → ℝ) :
    fderiv ℝ (fun x => wfield x + w₀) r = fderiv ℝ wfield r :=
  fderiv_add_const w₀

/-! ## The boxed derivative corollary: every derivative in w vanishes (Note L669–671) -/

/-- The uniform-shift energy of an admissible term: its base value `A` (the monomial `∏_m n_{G_m}` at
`w`) carried by the phason factor, as a function of the uniform shift `w₀ ∈ E_⊥`. This is `J`
restricted to the uniform (q=0) phason sector, written as a function of `w₀`. -/
noncomputable def phasonTerm {M : ℕ} (c : Fin M → (Fin 6 → ℤ)) (A : ℂ) (w₀ : Fin 3 → ℝ) : ℂ :=
  A * monoPhasePerp c w₀

/-- **Note L669, "J(w+w₀)=J(w)".** An admissible term is *strictly* constant in the uniform phason
shift: equal to its base value `A` for every `w₀`. -/
theorem phasonTerm_const {M : ℕ} (c : Fin M → (Fin 6 → ℤ)) (h : (∑ m, c m) = 0) (A : ℂ)
    (w₀ : Fin 3 → ℝ) : phasonTerm c A w₀ = A := by
  rw [phasonTerm, admissible_phason_invariant c h w₀, mul_one]

/-- **Note L669–671, boxed, k=1: ∂J/∂w|_uniform ≡ 0.** The Fréchet derivative of an admissible term
in the uniform phason shift vanishes everywhere. -/
theorem no_pinning_fderiv {M : ℕ} (c : Fin M → (Fin 6 → ℤ)) (h : (∑ m, c m) = 0) (A : ℂ)
    (w₀ : Fin 3 → ℝ) : fderiv ℝ (phasonTerm c A) w₀ = 0 := by
  have hconst : phasonTerm c A = fun _ => A := by
    funext x; exact phasonTerm_const c h A x
  rw [hconst]
  exact fderiv_const_apply A

/-- **Note L669–671, boxed, all k≥1: ∂^k J/∂w^k|_uniform ≡ 0.** Every iterated Fréchet derivative of
order `k ≥ 1` of an admissible term in the uniform phason shift vanishes identically — "at every
order". -/
theorem no_pinning_iteratedFDeriv {M : ℕ} (c : Fin M → (Fin 6 → ℤ)) (h : (∑ m, c m) = 0) (A : ℂ)
    {k : ℕ} (hk : k ≠ 0) : iteratedFDeriv ℝ k (phasonTerm c A) = 0 := by
  have hconst : phasonTerm c A = fun _ => A := by
    funext x; exact phasonTerm_const c h A x
  rw [hconst]
  exact iteratedFDeriv_const_of_ne hk A

/-! ## The one-line calculation: every summand carries the zero vector (Note L675, L677) -/

/-- **Note L675.** "π_⊥(∑_{G∈T} G) = … π_⊥(0) = 0." For an admissible closure the perpendicular
coefficient vector that the derivative brings down is exactly the zero vector. -/
theorem perp_coefficient_zero {M : ℕ} (c : Fin M → (Fin 6 → ℤ)) (h : (∑ m, c m) = 0) :
    piPerp (fun i => ((∑ m, c m) i : ℝ)) = 0 :=
  (piPerp_zero_iff_closure c).mpr h

/-- **Note L677.** "Every summand carries the **zero vector** as its coefficient — *before* any
evaluation of sin(·), *before* any stationarity condition, *before* any temperature is chosen."
Whatever real scalar amplitude/phase `2C η₁η₂η₃ sin Θ_T` multiplies the perpendicular coefficient of
an admissible summand, that summand is zero. -/
theorem summand_zero {M : ℕ} (c : Fin M → (Fin 6 → ℤ)) (h : (∑ m, c m) = 0) (coeff : ℝ) :
    coeff • piPerp (fun i => ((∑ m, c m) i : ℝ)) = 0 := by
  rw [perp_coefficient_zero c h, smul_zero]

/-! ## KL6 — The No-Pinning Theorem (Note L661–671, the boxed statement) -/

/-- **KL6 — The No-Pinning Theorem (Note L661–671).** For an admissible term — reciprocal indices
closing exactly in ℤ⁶ (`∑_m G_m = 0`), which by KL22 is *every* term `J` may contain at any order —
and every uniform phason shift `w₀ ∈ E_⊥`:

* `J(w+w₀)=J(w)`: the term is strictly unchanged (first component);
* hence `∂J/∂w|_uniform ≡ 0` (second component) and `∂^k J/∂w^k|_uniform ≡ 0` for every `k ≥ 1`
  (third component) — "every derivative in w vanishes identically, at every order, amplitude and
  temperature".

The phason moves every wave's phase (`ampPhasePerp`) and moves no energy: the perpendicular closure
is dragged along by the physical one (KL21), so the acquired factor is exactly 1. -/
theorem no_pinning {M : ℕ} (c : Fin M → (Fin 6 → ℤ)) (h : (∑ m, c m) = 0) (A : ℂ) :
    (∀ w₀, phasonTerm c A w₀ = A) ∧
      (∀ w₀, fderiv ℝ (phasonTerm c A) w₀ = 0) ∧
      (∀ k : ℕ, k ≠ 0 → iteratedFDeriv ℝ k (phasonTerm c A) = 0) :=
  ⟨fun w₀ => phasonTerm_const c h A w₀,
   fun w₀ => no_pinning_fderiv c h A w₀,
   fun _ hk => no_pinning_iteratedFDeriv c h A hk⟩

end ExistenceSystem.KL6

end
