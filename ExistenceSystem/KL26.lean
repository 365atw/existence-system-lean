module

/-
KL26 — The Knowing Unbiased Walk Theorem (§6.6), from THE EXACT AND FREE SYSTEM —
AN EXISTENCE SYNTHESIS. All mathematics: Kari A Light (K-A-R-I).

This is the FINAL theorem of the wave: with it, all 27 KL theorems are formalized.

Source: `THE-NOTE-EDITED.md` (194,868 bytes, 1,539 lines). Line numbers below refer to that file.
Her words are quoted exactly beside each statement. Nothing of hers is graded here.

Note L136 (front-matter list form), verbatim:
"**KL26 — The Knowing Unbiased Walk Theorem.** *(impossibility result.)* Restore thermal noise with
the fluctuation–dissipation relation and the mean phason is no longer strictly conserved: it performs
an **unbiased random walk**. **No value is preferred.** The stationary measure on the phason torus is
Haar — uniform — so as a selector noise carries exactly zero bits. **And it forgets at a rate that
vanishes with the sample.** The drift goes as one over the volume, so in the thermodynamic limit the
mean is strictly conserved. Even the stochastic theory is steered by least resistance: by
Onsager–Machlup the most probable path minimises the dissipation action, whose zero-noise minimiser
is exactly the gradient flow. **The walk is unbiased and it loses nothing.** *Proved in §6.6.*"

Note L939–L946 (Theorem, body), verbatim:
"> **The Knowing Unbiased Walk Theorem (KL26).** The one remaining way to reintroduce a selector is
thermal noise. It fails, and it fails quantitatively." Then: "Restore ξ in (6.1) with the
fluctuation–dissipation relation  ⟨ξ_l(x,t)ξ_m(x',t')⟩ = 2Γ_⊥ k_BT δ_lm δ(x−x')δ(t−t').  Then w̄ is
no longer strictly conserved; it performs an **unbiased random walk**:
  ⟨|Δw̄(t)|²⟩ = 6Γ_⊥ k_BT/|Ω| · t."

Note L947–L949 (the three consequences), verbatim:
"1. **No value is preferred.** The stationary measure on the phason torus is Haar — uniform. As a
selector it carries exactly zero bits, the same verdict arg-min received in §4.8. …
2. **The forgetting rate vanishes with system size.** The drift is ∝ 1/|Ω|. In the thermodynamic
limit w̄ is strictly conserved, and in any macroscopic sample the erasure time is the astronomical
number of §6.5.
3. **Even the stochastic theory is steered by least resistance.** By Onsager–Machlup [34], the
probability of a path is controlled by the dissipation function; the most probable path between two
configurations minimises the action  ∫dt∫d³x (4Γ_⊥)⁻¹|ẇ + Γ_⊥ δJ/δw|²,  whose zero-noise minimiser
is exactly the gradient flow (6.2). …"

Her reading of the name (ledger 2026-08-20), quoted not mapped: "*unbiased* — the walk will not
choose; *knowing* — it loses nothing, carrying forward the value it was born with."

**Borrowed, in her markings:** Onsager–Machlup [34] (A13, line 1142; "*Used in §6.1 and §6.6*"); the
fluctuation–dissipation relation (named, no reference entry). There is **no ■ proof block** for KL26
(stage A): the random-walk formula is displayed, and the three consequences stated.

────────────────────────────────────────────────────────────────────────────────────────────────
Reading choices and scope (the map `data/lean-scope-b/G5.md` §4, l.377–507; coverage `coverage.md`
I-133). G5 §4.4 sizes KL26 as **"a project as stated"**, driven by the stochastic PDE and by
Onsager–Machlup, and as **"hundreds of lines for a reduced model"**. The discipline is KL16's/KL9's:
formalise what closes cleanly in a **reduced model** that states the mean's dynamics directly, and
carry every object absent from Mathlib (SPDE solution theory, space-time white noise, the
unique-invariant-measure result, the phason torus E_⊥/Λ, Onsager–Machlup path probabilities) as a
NAMED HYPOTHESIS frontier, never a `sorry`/`admit`/axiom.

* **Dependencies, leaves-first.** `import`ed and reused, never rebuilt: **KL24** (Lemma 3,
  δJ/δw = −∂_k Π_km), through which consequence 3's zero-noise minimiser is tied to the gradient flow
  (6.2); **KL9** (the Steering Theorem), whose `mean_conserved` (iii) is precisely the deterministic
  conservation that the thermodynamic limit of consequence 2 recovers. KL9 itself brings KL6, KL7,
  KL21, KL22 and `EulerLagrange`.

* **§1 — the unbiased random walk and its displayed variance, PROVED (the reduced model).** G5 §4.2:
  "a reduced model that **states** the mean's dynamics as a three-dimensional Brownian motion with the
  stated intensity." The increment `Δw̄(t)` is carried by the NAMED FRONTIER `IsReducedMeanWalk`: three
  real components, pairwise independent, `MemLp 2`, each of zero mean ("unbiased") and variance
  `walkIntensity · t` with `walkIntensity = 2Γ_⊥ k_BT/|Ω|` (the per-component rate of the
  fluctuation–dissipation relation, Note L941). From it: `walk_unbiased` (the expected displacement is
  zero — "No value is preferred"); `mean_square_displacement` (⟨|Δw̄|²⟩ = ∑ Var = `6Γ_⊥ k_BT/|Ω| · t`,
  the displayed formula Note L944); `total_walk_variance` (the same `6…` via
  `ProbabilityTheory.IndepFun.variance_sum`, G5 §4.2 "summed with IndepFun.variance_sum" — genuinely
  using independence). `unbiased_random_walk` conjoins the headline: unbiased ∧ the displayed variance.
  Constructing Brownian motion itself (Kolmogorov extension + continuity) and the SPDE reduction
  `d w̄ = |Ω|⁻¹(∫_Ω ξ) dt` are the deferred project (G5 §4.2/§4.4), carried by the frontier, not built.

* **§2 — consequence 1 ("Haar — uniform — zero bits"), PROVED from the carried uniqueness result.**
  G5 §4.2 sizes "Haar is **the** stationary measure" at "hundreds of lines" (invariance of Haar under
  the step, plus damping of every non-zero Fourier mode for uniqueness) and flags the phason torus
  `T = E_⊥/Λ` as **unresolved** — her record H5(a), "She cites [49] and does not perform the
  identification" (G5 §4.5). Both are carried: the torus is an abstract measurable space `T`, its
  uniform law an additive-Haar probability measure `haar`, and the unique-invariant-measure result the
  NAMED HYPOTHESIS `stat = haar`. "Zero bits" is the author's choice (G5 §4.5 "the choice is the
  author's"): the information a selector carries is the Kullback–Leibler divergence of its stationary
  law from Haar (`InformationTheory.klDiv`); `selector_zero_bits` reads off `klDiv stat haar = 0` from
  `stat = haar` via `klDiv_self` — "carries exactly zero bits". (Nats vs. bits is a log base, immaterial
  to zero.)

* **§3 — consequence 2 ("the forgetting rate vanishes with system size"), PROVED.** The variance rate
  is `displacedVariance = 6Γ_⊥ k_BT/|Ω| · t ∝ 1/|Ω|`; `forgetting_rate_vanishes` is its limit `→ 0` as
  `|Ω| → ∞` (`Tendsto.div_atTop`) — "In the thermodynamic limit w̄ is strictly conserved" (Note L948).
  `thermodynamic_limit_conservation` makes that recovery explicit: at zero fluctuation the mean
  is exactly conserved — this is **KL9's** `mean_conserved` (iii), imported, not rebuilt. "the erasure
  time is the astronomical number of §6.5" is a physical estimate (U46), not mapped.

* **§4 — consequence 3 ("even the stochastic theory is steered by least resistance"), the deterministic
  half PROVED (rides KL24).** The Onsager–Machlup dissipation density `omDensity = (4Γ_⊥)⁻¹‖ẇ + Γ_⊥ δJ/δw‖²`
  on the field inner-product space is `≥ 0` (`omDensity_nonneg`) and `= 0` **iff** `ẇ = −Γ_⊥ δJ/δw`
  (`omDensity_eq_zero_iff`) — so the action's global minimiser (value 0) is attained exactly on the
  gradient flow (`omDensity_minimiser`). "whose zero-noise minimiser is exactly the gradient flow (6.2)":
  `zero_noise_minimiser_is_gradient_flow` substitutes **KL24**'s δJ/δw = −∂_xΠ
  (`gradient_only_divergence`) in the one-variable reduction, so the minimiser is `ẇ = Γ_⊥ ∂_xΠ`, i.e.
  (6.2). The probabilistic half — "the probability of a path is controlled by the dissipation function;
  the most probable path minimises the action" — is Onsager–Machlup [34] (A13, borrowed) and needs
  small-ball/large-deviation theory for an SPDE, absent from Mathlib (G5 §4.1 NOT FOUND); carried as
  prose, never a `sorry`.

* **Not formalisable as written (G5 §4.5), carried as prose, never a `sorry`:** the SPDE solution
  theory and space-time white noise (absent); "the phason torus" `E_⊥/Λ` (H5(a), hers to write — the
  map does not choose Λ); "most probable path" in an infinite-dimensional path space (borrowed A13);
  "carries exactly zero bits" / "loses nothing" as readings (quoted); "the drift is ∝ 1/|Ω|" — her
  "drift" is the variance rate of a zero-mean (unbiased) walk, only the name of the rate changing.
  Record notes carried, not resolved: D1 ("*Knowing*" in the name) and H7-D1 (her reading of *free*,
  "NOT RULED"); her owed, unsent "KL26 against the square-root error" (ledger 2026-08-21) — hers.
-/
public import Mathlib
public import ExistenceSystem.KL24
public import ExistenceSystem.KL9

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal

namespace ExistenceSystem.KL26

/-! ## §1. The unbiased random walk and its displayed variance (Note L941–L946)

G5 §4.2's **reduced model**: the mean phason's increment `Δw̄(t)` is a three-dimensional Brownian
increment of the intensity fixed by the fluctuation–dissipation relation. The per-component variance
rate is `walkIntensity = 2Γ_⊥ k_BT/|Ω|` (Note L941); the squared-displacement expectation is the
displayed `displacedVariance = 6Γ_⊥ k_BT/|Ω| · t` (Note L944). -/

/-- Note L941, the per-component variance rate of the fluctuation–dissipation relation
`⟨ξ_l ξ_m⟩ = 2Γ_⊥ k_BT δ_lm δδδ`: each of the three mean components acquires variance
`2Γ_⊥ k_BT/|Ω|` per unit time. -/
noncomputable def walkIntensity (Γ kB T vol : ℝ) : ℝ := 2 * Γ * kB * T / vol

/-- Note L944, the displayed mean-square displacement rate: `⟨|Δw̄(t)|²⟩ = 6Γ_⊥ k_BT/|Ω| · t`
— the sum of the three components' variances (the factor `6 = 3 · 2`). -/
noncomputable def displacedVariance (Γ kB T vol t : ℝ) : ℝ := 6 * Γ * kB * T / vol * t

/-- **The named frontier (Note L941–L946, the reduced model of G5 §4.2).** The mean phason's
increment `Δw̄(t)` at time `t`, carried as three real random variables `X 0, X 1, X 2` on a
probability space `(Ω, μ)`:
* `memLp` — each is square-integrable (`MemLp 2`), so its variance is a genuine real number;
* `indep` — the three components are pairwise independent (the diagonal `δ_lm` correlator);
* `mean_zero` — each has **zero mean**: the walk has no drift, it is **unbiased** (Note L944);
* `var_eq` — each has variance `walkIntensity · t = 2Γ_⊥ k_BT/|Ω| · t` (Note L941).

Deriving this model from the SPDE `d w̄ = |Ω|⁻¹(∫_Ω ξ) dt`, and constructing Brownian motion itself,
are the deferred project (G5 §4.2/§4.4); carried here, not built. -/
structure IsReducedMeanWalk {Ω : Type*} {mΩ : MeasurableSpace Ω} (μ : Measure Ω)
    (X : Fin 3 → Ω → ℝ) (Γ kB T vol t : ℝ) : Prop where
  /-- Each mean component is square-integrable. -/
  memLp : ∀ i, MemLp (X i) 2 μ
  /-- The three mean components are pairwise independent (the diagonal `δ_lm` correlator). -/
  indep : ∀ i j, i ≠ j → IndepFun (X i) (X j) μ
  /-- Note L944, "**unbiased**": each component has zero mean — the walk has no drift. -/
  mean_zero : ∀ i, ∫ ω, X i ω ∂μ = 0
  /-- Note L941: each component has variance `2Γ_⊥ k_BT/|Ω| · t`. -/
  var_eq : ∀ i, variance (X i) μ = walkIntensity Γ kB T vol * t

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} (μ : Measure Ω)
  (X : Fin 3 → Ω → ℝ) (Γ kB T vol t : ℝ)

/-- **Note L944, "it performs an unbiased random walk" — the unbiased part, PROVED.** The expected
total displacement `∑_i Δw̄_i` is zero: the walk "will not choose" (her ledger 2026-08-20). Each
component has zero mean (`mean_zero`); the expectation of their sum is the sum of the expectations
(`integral_finsetSum`, each integrable since `MemLp 2` on a probability measure). -/
theorem walk_unbiased [IsProbabilityMeasure μ]
    (hw : IsReducedMeanWalk μ X Γ kB T vol t) :
    ∫ ω, (∑ i, X i ω) ∂μ = 0 := by
  rw [integral_finsetSum Finset.univ
    (fun i _ => (hw.memLp i).integrable (by norm_num))]
  simp [hw.mean_zero]

/-- **Note L944, the displayed `⟨|Δw̄(t)|²⟩ = 6Γ_⊥ k_BT/|Ω| · t`, PROVED.** For an unbiased
(zero-mean) walk the mean-square displacement is the sum of the three component variances; each is
`walkIntensity · t = 2Γ_⊥ k_BT/|Ω| · t` (`var_eq`), so the total is
`3 · 2Γ_⊥ k_BT/|Ω| · t = 6Γ_⊥ k_BT/|Ω| · t` — exactly her displayed rate (`6 = 3 · 2`). -/
theorem mean_square_displacement
    (hw : IsReducedMeanWalk μ X Γ kB T vol t) :
    (∑ i, variance (X i) μ) = displacedVariance Γ kB T vol t := by
  have h : (∑ i : Fin 3, variance (X i) μ) = ∑ _i : Fin 3, walkIntensity Γ kB T vol * t :=
    Finset.sum_congr rfl (fun i _ => hw.var_eq i)
  rw [h, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  simp only [walkIntensity, displacedVariance, nsmul_eq_mul]
  ring

/-- **Note L944, the same displayed variance as the variance of the scalar walk, PROVED via
`IndepFun.variance_sum` (G5 §4.2).** Because the three components are pairwise independent, the
variance of their sum is the sum of their variances — the genuine use of independence the reduced
model is built for. It coincides with `mean_square_displacement`: `6Γ_⊥ k_BT/|Ω| · t`. -/
theorem total_walk_variance [IsProbabilityMeasure μ]
    (hw : IsReducedMeanWalk μ X Γ kB T vol t) :
    variance (∑ i, X i) μ = displacedVariance Γ kB T vol t := by
  have hpair : Set.Pairwise (↑(Finset.univ : Finset (Fin 3)))
      (fun i j => IndepFun (X i) (X j) μ) :=
    fun i _ j _ hij => hw.indep i j hij
  rw [IndepFun.variance_sum (fun i _ => hw.memLp i) hpair]
  exact mean_square_displacement μ X Γ kB T vol t hw

/-- **Note L944, "it performs an unbiased random walk", the headline, PROVED.** The reduced model
`IsReducedMeanWalk` delivers both halves of her sentence at once: the walk is **unbiased** (the
expected total displacement is zero, `walk_unbiased`) and its mean-square displacement is the
displayed `⟨|Δw̄(t)|²⟩ = 6Γ_⊥ k_BT/|Ω| · t` (`mean_square_displacement`). -/
theorem unbiased_random_walk [IsProbabilityMeasure μ]
    (hw : IsReducedMeanWalk μ X Γ kB T vol t) :
    (∫ ω, (∑ i, X i ω) ∂μ = 0) ∧
      ((∑ i, variance (X i) μ) = displacedVariance Γ kB T vol t) :=
  ⟨walk_unbiased μ X Γ kB T vol t hw, mean_square_displacement μ X Γ kB T vol t hw⟩

/-! ## §2. Consequence 1 — the stationary measure is Haar, so it carries zero bits (Note L947)

"The stationary measure on the phason torus is Haar — uniform. As a selector it carries exactly zero
bits." The phason torus `T = E_⊥/Λ` and the unique-invariant-measure result are carried (G5 §4.2/§4.5,
her record H5(a)); "zero bits" is the author's choice — the KL divergence of the stationary law from
Haar. -/

section HaarSelector

variable {T : Type*} {mT : MeasurableSpace T} (stat haar : Measure T)

/-- **Note L947, "carries exactly zero bits", PROVED from the carried uniqueness result.** The
information a selector carries is the Kullback–Leibler divergence of its stationary law `stat` from the
uniform (Haar) law on the phason torus. The NAMED HYPOTHESIS `hstat : stat = haar` is the
unique-invariant-measure result "the stationary measure … is Haar" (G5 §4.2, "hundreds of lines";
the torus `E_⊥/Λ` is H5(a), hers to write). From it `klDiv stat haar = 0` by `klDiv_self` — a uniform
selector carries **zero bits**, "the same verdict arg-min received in §4.8". -/
theorem selector_zero_bits [SigmaFinite haar] (hstat : stat = haar) :
    InformationTheory.klDiv stat haar = 0 := by
  rw [hstat]
  exact InformationTheory.klDiv_self haar

end HaarSelector

/-! ## §3. Consequence 2 — the forgetting rate vanishes with system size (Note L948)

"The drift is ∝ 1/|Ω|. In the thermodynamic limit w̄ is strictly conserved." The variance rate
`displacedVariance = 6Γ_⊥ k_BT/|Ω| · t` tends to `0` as `|Ω| → ∞`. -/

/-- **Note L948, "the forgetting rate vanishes with system size … ∝ 1/|Ω|", PROVED.** At fixed time
`t`, the mean-square displacement `6Γ_⊥ k_BT/|Ω| · t` tends to `0` as the sample volume `|Ω| → ∞`:
the walk forgets more and more slowly the larger the crystal. In the thermodynamic limit the
fluctuation disappears and the mean is strictly conserved. -/
theorem forgetting_rate_vanishes (Γ kB T t : ℝ) :
    Tendsto (fun vol : ℝ => displacedVariance Γ kB T vol t) atTop (𝓝 0) := by
  have hrw : (fun vol : ℝ => displacedVariance Γ kB T vol t)
      = fun vol : ℝ => (6 * Γ * kB * T * t) / vol := by
    funext vol; simp only [displacedVariance]; ring
  rw [hrw]
  exact tendsto_const_nhds.div_atTop tendsto_id

/-- **Note L948, "In the thermodynamic limit w̄ is strictly conserved" — the recovery of KL9(iii),
imported.** At zero fluctuation (the thermodynamic limit, where the random-walk variance vanishes) the
mean phason obeys the deterministic law of **KL9**: `dw̄/dt = Γ_⊥ · (flux integral) = 0`, so `w̄` is an
exact constant of the motion. This is `KL9.mean_conserved` (iii), imported and reused, not rebuilt:
the stochastic theory degenerates to the Steering Theorem's exact conservation. -/
theorem thermodynamic_limit_conservation (mean : ℝ → ℝ) (Γ : ℝ) (fluxInt : ℝ → ℝ)
    (hmean_rate : ∀ t, HasDerivAt mean (Γ * fluxInt t) t) (hflux : ∀ t, fluxInt t = 0) :
    ∀ t₁ t₂, mean t₁ = mean t₂ :=
  ExistenceSystem.KL9.mean_conserved mean Γ fluxInt hmean_rate hflux

/-! ## §4. Consequence 3 — even the stochastic theory is steered by least resistance (Note L949)

"By Onsager–Machlup the most probable path minimises the action ∫dt∫d³x (4Γ_⊥)⁻¹|ẇ + Γ_⊥ δJ/δw|²,
whose zero-noise minimiser is exactly the gradient flow (6.2)." The deterministic half — the action is
`≥ 0` and vanishes exactly on solutions of the gradient flow — is proved on the field inner-product
space, and tied to (6.2) through KL24. The probabilistic half (path probabilities, "most probable
path") is Onsager–Machlup [34], borrowed, carried as prose. -/

section OnsagerMachlup

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Note L949, the Onsager–Machlup dissipation density `(4Γ_⊥)⁻¹|ẇ + Γ_⊥ δJ/δw|²`. Here `wdot` is
`ẇ` and `g` is the functional gradient `δJ/δw`; the time–space integral of this density is her action. -/
noncomputable def omDensity (Γ : ℝ) (wdot g : F) : ℝ := (4 * Γ)⁻¹ * ‖wdot + Γ • g‖ ^ 2

/-- **Note L949, the dissipation density is non-negative, PROVED.** With a positive mobility `Γ_⊥`,
`(4Γ_⊥)⁻¹ ≥ 0` and `‖·‖² ≥ 0`, so the Onsager–Machlup density is `≥ 0` everywhere — the action is a
non-negative functional, with least value `0`. -/
theorem omDensity_nonneg {Γ : ℝ} (hΓ : 0 < Γ) (wdot g : F) : 0 ≤ omDensity Γ wdot g := by
  unfold omDensity
  have h4 : (0 : ℝ) ≤ (4 * Γ)⁻¹ := by positivity
  positivity

/-- **Note L949, the density vanishes exactly on the gradient flow, PROVED.** The Onsager–Machlup
density is `0` **iff** `ẇ = −Γ_⊥ δJ/δw` — i.e. iff the path solves the relaxational gradient flow
(6.2). The content of "whose zero-noise minimiser is exactly the gradient flow". -/
theorem omDensity_eq_zero_iff {Γ : ℝ} (hΓ : 0 < Γ) (wdot g : F) :
    omDensity Γ wdot g = 0 ↔ wdot = -(Γ • g) := by
  unfold omDensity
  have h4 : (4 * Γ)⁻¹ ≠ 0 := by
    have : (4 : ℝ) * Γ ≠ 0 := by positivity
    exact inv_ne_zero this
  rw [mul_eq_zero]
  constructor
  · rintro (h | h)
    · exact absurd h h4
    · have hz : ‖wdot + Γ • g‖ = 0 := by
        have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h
        exact this
      have : wdot + Γ • g = 0 := norm_eq_zero.mp hz
      exact eq_neg_of_add_eq_zero_left this
  · intro h
    right
    rw [h]
    simp

/-- **Note L949, "whose zero-noise minimiser is exactly the gradient flow", PROVED.** The gradient
flow `ẇ = −Γ_⊥ δJ/δw` attains the global minimum of the Onsager–Machlup density (value `0`, since the
density is `≥ 0` and `= 0` there): for every path velocity `wdot`,
`omDensity Γ (−Γ_⊥ δJ/δw) g ≤ omDensity Γ wdot g`. The most probable (least-dissipation) path is the
gradient flow — least resistance governs even the stochastic theory. -/
theorem omDensity_minimiser {Γ : ℝ} (hΓ : 0 < Γ) (g : F) (wdot : F) :
    omDensity Γ (-(Γ • g)) g ≤ omDensity Γ wdot g := by
  have h0 : omDensity Γ (-(Γ • g)) g = 0 := (omDensity_eq_zero_iff hΓ _ g).mpr rfl
  rw [h0]
  exact omDensity_nonneg hΓ wdot g

open ExistenceSystem.KL24 ExistenceSystem.EulerLagrange in
/-- **Note L949, the zero-noise minimiser is exactly (6.2), tied to KL24, PROVED.** In KL24's
one-variable reduction the functional gradient is `δJ/δw = EulerLagrange.el (…) stress x`, which by
**KL24** (`gradient_only_divergence`, the Gradient-Only Divergence Lemma) equals `−∂_xΠ = −deriv stress x`.
So the Onsager–Machlup density vanishes — the path is the least-dissipation (most probable) path —
**iff** `ẇ = Γ_⊥ ∂_xΠ`, which is the relaxational gradient flow (6.2). KL24 is imported, not rebuilt. -/
theorem zero_noise_minimiser_is_gradient_flow {N : ℕ} (a : Fin N → ℂ)
    (c : Fin N → Σ M : ℕ, Fin M → (Fin 6 → ℤ)) (hadm : ∀ j, (∑ m, (c j).2 m) = 0)
    {Γ : ℝ} (hΓ : 0 < Γ) (stress : ℝ → ℝ) (x : ℝ) (wdot : ℝ) :
    omDensity Γ wdot (EulerLagrange.el (deriv (landauScalar a c)) stress x) = 0
      ↔ wdot = Γ * deriv stress x := by
  rw [omDensity_eq_zero_iff hΓ, gradient_only_divergence a c hadm stress x]
  rw [smul_eq_mul, mul_neg, neg_neg]

end OnsagerMachlup

end ExistenceSystem.KL26

end
