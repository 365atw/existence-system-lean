module

/-
KL25 — The Staircase Bounded-Barrier Theorem (§4.9/§4.10), from THE EXACT AND FREE SYSTEM —
AN EXISTENCE SYNTHESIS. All mathematics: Kari A Light.

Source: `THE-NOTE-EDITED.md` (194,868 bytes, 1,539 lines). Line numbers below refer to that file.
Her words are quoted exactly beside each statement. Nothing of hers is graded here.

Note L134 (front-matter list form), verbatim:
"**KL25 — The Staircase Bounded-Barrier Theorem.** The shift from one uniform phason value to
another executes as `N` sweeps of a wall carrying `δ/N` — a staircase, not a single step. Every
intermediate is a perfect member of the family at bulk energy and the wall tension vanishes linearly,
so choosing `N` with the sample size gives **a barrier of order one, independent of sample size.**
The members of the degenerate family are therefore not merely equal in free energy but freely
reachable from one another: **no wall between them grows with the crystal.** *Proved in §4.10.*"

Note L741 (Theorem, body), verbatim:
"> **The Staircase Bounded-Barrier Theorem (KL25).** The staircase construction executes the shift
`w ↦ w+δ` as `N` sweeps of a `δ/N` wall; every intermediate is a perfect member of the family at
bulk energy; wall tension vanishes linearly; choosing `N` with the sample size gives **a barrier of
order one, independent of sample size**. The members of the degenerate family are therefore not
merely equal in free energy but freely reachable from one another: **no wall between them grows with
the crystal.**"

Note L743, verbatim:
"> *The closure argument certifies that there is no pinning potential to be overcome — a statement
about the landscape, not about the kinetics.*"

Note L745 (Scope on K₃ and q; coverage.md I-108), verbatim:
"**Scope on `K_3` and `q`.** Icosahedral symmetry permits exactly one mixed phonon–phason elastic
constant, `K_3`, generically nonzero at finite wavevector and entering at `O(q²)` (Socolar, Lubensky
and Steinhardt [30]; Ding et al., Phys. Rev. B 48, 7003 (1993), Eq. 68 [62]). It is carried openly in
`f_el` and vanishes identically for uniform fields. The identically-vanishing mixed Hessian block, and
the No-Pinning Theorem with it, are statements about the **uniform (`q=0`) sector only**."

Record note, carried not resolved (map `data/lean-scope-b/G4.md`, KL25; her ledger 2026-08-10):
the letter `δ` here is a **uniform phason shift** `w ↦ w+δ`, `δ ∈ E_⊥` — her ruling: "**δ is NOT the
free phason of §4.9 — the separation STAYS.**" §7's `δ = t√5` is a different object and is not touched.

## What is proved here, what is imported, and what is the named frontier (map `data/lean-scope-b/G4.md`).

Her §4.10 names "**the staircase construction**" with a definite article and does **not** write it out
(stage A: "no separate construction paragraph appears in §4.10, lines 732–745"). The map sizes KL25 as
*a project*: the wall profile, the sweep, the function space of phason fields on a growing sample, and
the energy model of the wall are **not fixed in the Note** — "the energy model of the wall is not
fixed" (G4.md §2). What the Note *does* assert about the wall is exactly three facts: the shift is cut
into `N` sweeps of strength `δ/N`; the tension **vanishes linearly** in the strength; and the wall
spans the sample, so its energy is extensive in the sample's wall area, which grows with the crystal.

Following the house discipline (the KL16 / KL19 pattern), those undefined-in-Note objects are carried
as the **named frontier** `WallModel` — a structure bundling exactly her three asserted facts, never a
`sorry`, never an axiom. Everything the theorem claims is then proved **from** that model, gap-free:

* `WallModel` (the **named frontier**): the wall area `area : ℕ → ℝ` in a sample of linear size `L`
  (`area_nonneg`; `area_atTop`: the span "grows with the crystal", Note L741), and the tension
  coefficient `tension ≥ 0`. `wallEnergy h L := tension * h * area L` encodes "wall tension vanishes
  linearly" (linear in the strength `h`) and "a wall … across the sample" (extensive in `area L`).
  Deriving this model from U28's gradient energy `f_el` (`K₁, K₂, K₃`) is the deferred frontier
  (U28/G4), carried here, not built.

* PROVED, gap-free, over `ℝ`:
  - `stepStrength_nsmul`: the `N` sweeps of strength `δ/N` reconstitute the full shift `δ`
    ("a staircase, not a single step", Note L134);
  - `barrier_eq`, `barrier_nonneg`: the barrier (max energy excess along the path) in closed form;
  - `barrier_le_of_area_le`, `staircase_barrier_bounded`: **choosing `N` with the sample size**
    (`area L ≤ N L`) gives `barrier ≤ tension·δ` for **every** `L` — "a barrier of order one,
    independent of sample size";
  - `staircase_barrier_isBigO`: the barrier is `O(1)` on `atTop` — "a barrier of order one";
  - `single_step_wall_grows`: the **contrast** — a single step (`N = 1`) is a wall whose barrier
    `→ ∞` as the sample grows; the staircase defeats exactly this. Together: "**no wall between them
    grows with the crystal**";
  - `staircase_bounded_barrier`: the capstone conjunction (reconstitution ∧ uniform bound ∧ `O(1)`).

* IMPORTED, not rebuilt (leaves-first; dependencies KL6, KL24 merged on `main`):
  - **KL6** (the No-Pinning Theorem): "every intermediate is a perfect member of the family at bulk
    energy." Between sweeps the field is uniform; `intermediate_at_bulk_energy` is `KL6.phasonTerm_const`
    (an admissible Landau term is unchanged from its bulk value — zero excess) and
    `intermediate_no_gradient` is `KL6.uniform_shift_grad_zero` (a uniform field has no gradient, so the
    elastic/`K₃` part sees nothing — the Note L745 "`q=0` sector").
  - **KL24** (the Gradient-Only Divergence Lemma): `energy_through_gradient` is
    `KL24.landau_pointwise_w_independent` — the energy sees the field only through its gradient, so the
    barrier is localized to the moving wall and uniform intermediates cost nothing.

* NOT built (map G4.md §2, §5; carried as prose, never a `sorry`): the phason field space on a growing
  sample, the actual functional `J`, the wall profile and the sweep, the rate `N = N(L)` beyond "with
  the sample size", and U28's derivation that `f_el` yields a linearly-vanishing tension. Note L743 ("a
  statement about the landscape, not about the kinetics") is a scope sentence; nothing to map.
-/
public import Mathlib
public import ExistenceSystem.KL6
public import ExistenceSystem.KL24

@[expose] public section

open Filter Asymptotics

namespace ExistenceSystem.KL25

/-! ## The named frontier: the wall-energy model the Note asserts but does not write out

Note L741 names "the staircase construction" and asserts three facts about its wall; the model itself
is not fixed in the Note (map G4.md §2). The KL16 / KL19 pattern: carry exactly those facts as a named
structure, prove everything from it, never a `sorry`. -/

/-- **The named frontier (Note L741, the KL16 pattern).** The wall-energy model of §4.10. The Note
asserts three facts about the wall and leaves the model itself open (deriving it from U28's `f_el` is
deferred, U28/G4): the wall **spans the sample**, so its energy is extensive in the wall area `area L`
of a sample of linear size `L`; that area **grows with the crystal** (`area_atTop`); and the wall
**tension vanishes linearly** in the strength, with coefficient `tension ≥ 0`. -/
structure WallModel where
  /-- The wall area in a sample of linear size `L`: the area a wall must span to cross the sample. -/
  area : ℕ → ℝ
  /-- A wall area is nonnegative. -/
  area_nonneg : ∀ L, 0 ≤ area L
  /-- Note L741, "**no wall … grows with the crystal**": the area a single wall must span grows
  without bound as the sample size `L → ∞`. This is what makes a *single* step's barrier diverge. -/
  area_atTop : Tendsto area atTop atTop
  /-- The wall tension coefficient `τ ≥ 0`: energy per unit area per unit wall strength. -/
  tension : ℝ
  /-- The tension coefficient is nonnegative. -/
  tension_nonneg : 0 ≤ tension

/-- Note L741, "**wall tension vanishes linearly**": a wall of strength `h` carries tension `τ·h` per
unit area — **linear** in `h`, so it vanishes linearly as `h → 0` — hence energy `τ·h·(area L)` across
a sample of linear size `L`, extensive in the wall area it spans. -/
noncomputable def WallModel.wallEnergy (m : WallModel) (h : ℝ) (L : ℕ) : ℝ :=
  m.tension * h * m.area L

/-! ## The staircase: `N` sweeps of a `δ/N` wall (Note L134, L741) -/

/-- Note L741: the shift `w ↦ w+δ` executed as `N` sweeps, each a wall of strength `δ/N`. -/
noncomputable def stepStrength (δ : ℝ) (N : ℕ) : ℝ := δ / N

/-- Note L134, "a staircase, not a single step": the `N` sweeps, each of strength `δ/N`, reconstitute
the full shift `δ`. -/
theorem stepStrength_nsmul (δ : ℝ) {N : ℕ} (hN : N ≠ 0) : (N : ℝ) * stepStrength δ N = δ := by
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  unfold stepStrength
  rw [mul_comm, div_mul_cancel₀ δ hN']

/-- **The staircase barrier** in a sample of linear size `L`: the maximum energy excess along the
`N`-sweep path. Note L741: "every intermediate is a perfect member of the family at bulk energy" — the
uniform states *between* sweeps have zero excess (KL6, `intermediate_at_bulk_energy`); the energy sees
the field only through its gradient (KL24, `energy_through_gradient`). So the maximum over the path is
the energy of **one** wall of strength `δ/N` crossing the sample. -/
noncomputable def WallModel.barrier (m : WallModel) (δ : ℝ) (N L : ℕ) : ℝ :=
  m.wallEnergy (stepStrength δ N) L

/-- The barrier in closed form: `τ · δ · (area L) / N`. -/
theorem barrier_eq (m : WallModel) (δ : ℝ) (N L : ℕ) :
    m.barrier δ N L = m.tension * δ * m.area L / N := by
  simp only [WallModel.barrier, WallModel.wallEnergy, stepStrength]
  ring

/-- The barrier is nonnegative (`τ, δ, area L ≥ 0`). -/
theorem barrier_nonneg (m : WallModel) {δ : ℝ} (hδ : 0 ≤ δ) (N L : ℕ) :
    0 ≤ m.barrier δ N L := by
  rw [barrier_eq]
  exact div_nonneg (mul_nonneg (mul_nonneg m.tension_nonneg hδ) (m.area_nonneg L))
    (Nat.cast_nonneg N)

/-! ## Choosing `N` with the sample size: a barrier of order one (Note L741) -/

/-- **Note L741, the heart: "choosing `N` with the sample size gives a barrier of order one".** When
the number of sweeps is chosen to keep up with the sample's wall area (`area L ≤ N`), the barrier is
bounded by `τ·δ` — a constant, independent of `L`. The `area L / N ≤ 1` cancellation is exactly the
staircase's point: `N` sweeps of `δ/N` each spread the fixed `τ·δ` over `N` walls. -/
theorem barrier_le_of_area_le (m : WallModel) {δ : ℝ} (hδ : 0 ≤ δ) {N L : ℕ}
    (hN : m.area L ≤ (N : ℝ)) : m.barrier δ N L ≤ m.tension * δ := by
  rw [barrier_eq, mul_div_assoc]
  refine mul_le_of_le_one_right (mul_nonneg m.tension_nonneg hδ) ?_
  rcases Nat.eq_zero_or_pos N with hN0 | hNpos
  · subst hN0
    have hle : m.area L ≤ 0 := by exact_mod_cast hN
    have : m.area L = 0 := le_antisymm hle (m.area_nonneg L)
    simp [this]
  · rw [div_le_one (by exact_mod_cast hNpos)]
    exact hN

/-- **Note L741: "a barrier of order one, independent of sample size".** With a sweep schedule
`N = N(L)` chosen to keep up with the sample's wall area (`area L ≤ N L`), the barrier is `≤ τ·δ` for
**every** sample size `L` at once — it does not grow with the crystal. -/
theorem staircase_barrier_bounded (m : WallModel) {δ : ℝ} (hδ : 0 ≤ δ)
    (N : ℕ → ℕ) (hN : ∀ L, m.area L ≤ (N L : ℝ)) :
    ∀ L, m.barrier δ (N L) L ≤ m.tension * δ :=
  fun L => barrier_le_of_area_le m hδ (hN L)

/-- **Note L741: "a barrier of order one".** The barrier, as a function of the sample size `L`, is
`O(1)` on `atTop` — bounded by a constant multiple of `1`. -/
theorem staircase_barrier_isBigO (m : WallModel) {δ : ℝ} (hδ : 0 ≤ δ)
    (N : ℕ → ℕ) (hN : ∀ L, m.area L ≤ (N L : ℝ)) :
    (fun L => m.barrier δ (N L) L) =O[atTop] fun _ => (1 : ℝ) := by
  refine isBigO_of_le' atTop (c := m.tension * δ) (fun L => ?_)
  rw [norm_one, mul_one, Real.norm_of_nonneg (barrier_nonneg m hδ (N L) L)]
  exact barrier_le_of_area_le m hδ (hN L)

/-! ## The contrast: a single step is a wall that grows with the crystal (Note L741) -/

/-- **Note L741, the contrast the staircase defeats: a single step is "a wall [that] grows with the
crystal".** Executing the whole shift in one sweep (`N = 1`) gives barrier `τ·δ·(area L)`, which — since
the wall area grows with the sample (`area_atTop`) and `τ·δ > 0` — **diverges** as `L → ∞`. The
staircase replaces this diverging single wall with `N` vanishing ones. -/
theorem single_step_wall_grows (m : WallModel) {δ : ℝ} (hτδ : 0 < m.tension * δ) :
    Tendsto (fun L => m.barrier δ 1 L) atTop atTop := by
  have hrw : (fun L => m.barrier δ 1 L) = fun L => m.tension * δ * m.area L := by
    funext L; rw [barrier_eq]; push_cast; ring
  rw [hrw]
  exact Tendsto.const_mul_atTop hτδ m.area_atTop

/-! ## Imported, not rebuilt: every intermediate is at bulk energy (KL6, KL24)

Note L741: "every intermediate is a perfect member of the family at bulk energy." Between sweeps the
staircase field is **uniform**; the facts that a uniform state has zero energy excess are KL6's and
KL24's, imported and reused, not rebuilt (leaves-first). -/

/-- **Note L741, "every intermediate is a perfect member of the family at bulk energy" (via KL6).**
Between sweeps the field is a uniform phason shift `w ↦ w + w₀`, `w₀ ∈ E_⊥`; by KL6 (the No-Pinning
Theorem) every admissible Landau term is then unchanged from its bulk value `A` — zero energy excess.
This is `KL6.phasonTerm_const`, imported. -/
theorem intermediate_at_bulk_energy {M : ℕ} (c : Fin M → (Fin 6 → ℤ))
    (h : (∑ k, c k) = 0) (A : ℂ) (w₀ : Fin 3 → ℝ) :
    KL6.phasonTerm c A w₀ = A :=
  KL6.phasonTerm_const c h A w₀

/-- **Note L745, the `q=0` scope (via KL6).** A uniform intermediate has **no gradient**, so the
elastic sector — and the mixed `K₃` phonon–phason coupling, which "vanishes identically for uniform
fields" (Note L745) — sees nothing. This is `KL6.uniform_shift_grad_zero`, imported: the gradient of a
constant field is the zero map. -/
theorem intermediate_no_gradient (w₀ : Fin 3 → ℝ) (r : Fin 3 → ℝ) :
    fderiv ℝ (fun _ : Fin 3 → ℝ => w₀) r = 0 :=
  KL6.uniform_shift_grad_zero w₀ r

/-- **The energy sees the field only through its gradient (via KL24).** By KL24 (the Gradient-Only
Divergence Lemma) the Landau part is pointwise `w`-independent; so a uniform intermediate carries no
Landau excess, and — having no gradient (`intermediate_no_gradient`) — no elastic excess either. This
is why the barrier is localized to the moving wall and the intermediates are at bulk energy. This is
`KL24.landau_pointwise_w_independent`, imported. -/
theorem energy_through_gradient {Nf : ℕ} (a : Fin Nf → ℂ)
    (c : Fin Nf → Σ M : ℕ, Fin M → (Fin 6 → ℤ)) (hadm : ∀ j, (∑ k, (c j).2 k) = 0) :
    KL24.landauScalar a c = fun _ => (∑ j, a j).re :=
  KL24.landau_pointwise_w_independent a c hadm

/-! ## KL25 — The Staircase Bounded-Barrier Theorem (Note L741, the capstone) -/

/-- **KL25 — The Staircase Bounded-Barrier Theorem (Note L741).** Given the wall-energy model the Note
asserts (the named frontier `WallModel`), a nonnegative shift `δ ≥ 0`, and a sweep schedule `N = N(L)`
that keeps at least one sweep (`hNpos`) and keeps up with the sample's wall area (`hN : area L ≤ N L` —
"**choosing `N` with the sample size**"):

* `(1)` the `N L` sweeps of strength `δ/N L` reconstitute the full shift `δ` ("a staircase, not a
  single step");
* `(2)` the barrier is `≤ τ·δ` for **every** sample size `L` — "**a barrier of order one, independent
  of sample size**"; and
* `(3)` as a function of `L` the barrier is `O(1)` on `atTop`.

Contrast `single_step_wall_grows`: the one-sweep barrier **diverges** with the sample. So the degenerate
family's members are "**freely reachable from one another: no wall between them grows with the
crystal.**" The uniform intermediates are at bulk energy by KL6 (`intermediate_at_bulk_energy`), the
energy seeing the field only through its gradient by KL24 (`energy_through_gradient`). -/
theorem staircase_bounded_barrier (m : WallModel) {δ : ℝ} (hδ : 0 ≤ δ)
    (N : ℕ → ℕ) (hNpos : ∀ L, N L ≠ 0) (hN : ∀ L, m.area L ≤ (N L : ℝ)) :
    (∀ L, (N L : ℝ) * stepStrength δ (N L) = δ) ∧
      (∀ L, m.barrier δ (N L) L ≤ m.tension * δ) ∧
      ((fun L => m.barrier δ (N L) L) =O[atTop] fun _ => (1 : ℝ)) :=
  ⟨fun L => stepStrength_nsmul δ (hNpos L),
   staircase_barrier_bounded m hδ N hN,
   staircase_barrier_isBigO m hδ N hN⟩

end ExistenceSystem.KL25

end
