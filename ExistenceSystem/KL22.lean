module

/-
KL22 — The Admissibility Lemma (Lemma 2, §4.6), from THE EXACT AND FREE SYSTEM —
AN EXISTENCE SYNTHESIS. All mathematics: Kari A Light.

Source: `THE-NOTE-EDITED.md` (194,868 bytes, 1,539 lines). Line numbers below refer to that
file. Her words are quoted exactly beside each statement. Nothing of hers is graded here.

Note L128 (front-matter list form), verbatim:
"**KL22 — The Admissibility Lemma.** Under a physical-space translation every monomial acquires a
phase factor, so invariance under *every* translation forces its wavevectors to close in ℤ⁶.
**Every term J may contain, at any order, is therefore indexed by an exact integer relation
upstairs — and nothing else may appear.** The admissible terms are counted in the six-dimensional
lattice, where the counting is finite and exact; that is what makes the No-Pinning Theorem an
identity at every order rather than a property of a truncation. *Proved in §4.6.*"

Note L659 (Lemma 2, body and proof), verbatim:
"**Lemma 2 — The Admissibility Lemma (KL22).** Under a physical translation r ↦ r+u,
n_G ↦ n_G e^{iπ_∥(G)·u}, so a monomial ∏_m n_{G_m} acquires the factor exp[iπ_∥(∑_m G_m)·u].
Invariance for **all** u ⟺ π_∥(∑ G_m)=0 ⟺ (Lemma 1) ∑_m G_m=0 in ℤ⁶. **So every term in J, at
every order, is indexed by an exact integer relation in ℤ⁶. Nothing else can appear.** ∎"

Note L615 (the boxed restatement), verbatim:
"**Every term in J is indexed by a relation ∑ G=0 in ℤ⁶; nothing else may appear.** This is
Lemma 2 of §4.6, and it is why the theorem there is exhaustive rather than a property of a
truncation."

Reading choices and scope (map `data/lean-scope-b/G2.md`, KL22, §"KL22", l.204–266):

* "Lemma 1" of her proof is **KL20**, the Star Independence Lemma (π_∥ restricted to ℒ is
  injective). This module rests on it — the single step "π_∥(∑ G_m)=0 ⟺ ∑_m G_m=0 in ℤ⁶" is
  `ExistenceSystem.KL20.no_integer_relation`, reused. The Note names KL6 (No-Pinning) as this
  lemma's *consumer* (L96); KL6 is not a dependency and is not pulled in.

* **The carrier.** The Note's `J` (L598–L609) is a polynomial in the shell amplitudes `n_i, m_a`
  plus an elastic density in gradients of `u, w`; the map records (G2 §5) that the definition of
  "a term J may contain, at any order" — the variable set and whether "any order" is every
  polynomial degree or a power series — is not fixed in the Note and is U28/G4 territory. This
  module therefore does not build `J`. It formalises the lemma's argument at the generality her
  proof is written in: a **term** is a monomial `∏_m n_{G_m}` carried by a finite family
  `G : Fin M → (Fin 6 → ℤ)` of reciprocal indices — each `G_m` a lattice vector of ℒ = A(ℤ⁶),
  named by its integer coordinates upstairs (so a conjugate amplitude `n_{G}^*` is the index `-G`,
  and "any order" is any `M`). The map notes the gradient terms of `f_el` "fall outside this
  lemma's argument"; they are not monomials in `n_G` and are not in scope here.

* `π_∥` is `ExistenceSystem.Icosahedral.piParallel`, π_∥ on a coefficient vector `c` (a point of
  E_∥ ≅ ℝ³). The translation `r ↦ r+u` acts on an amplitude by `n_G ↦ n_G e^{iπ_∥(G)·u}`
  (`ampPhase`); the monomial's acquired factor is their product (`monoPhase`), which `monoPhase_eq`
  identifies with `exp[iπ_∥(∑_m G_m)·u]` — her "a monomial ∏_m n_{G_m} acquires the factor". The
  analytic step "invariance for all u ⟺ π_∥(∑ G_m)=0" is `phase_trivial_iff`
  (`e^{ik·u}=1 ∀u ⟺ k=0`). The arithmetic step is KL20.
-/
public import Mathlib
public import ExistenceSystem.KL20

@[expose] public section

open Real Matrix

namespace ExistenceSystem.KL22

open ExistenceSystem.Icosahedral ExistenceSystem.KL20

/-! ## A term as a monomial in the amplitudes, and its phase under a translation (Note L659) -/

/-- Note L659: "n_G ↦ n_G e^{iπ_∥(G)·u}." The phase factor a single amplitude `n_G`, with `G` the
lattice vector of integer coordinates `c`, acquires under the physical translation `r ↦ r+u`. -/
noncomputable def ampPhase (c : Fin 6 → ℤ) (u : Fin 3 → ℝ) : ℂ :=
  Complex.exp (Complex.I * (↑(piParallel (fun i => (c i : ℝ)) ⬝ᵥ u) : ℂ))

/-- Note L659: a monomial `∏_m n_{G_m}`, carried by the finite family `c` of reciprocal indices,
acquires the product of its amplitudes' phase factors under the translation `r ↦ r+u`. -/
noncomputable def monoPhase {M : ℕ} (c : Fin M → (Fin 6 → ℤ)) (u : Fin 3 → ℝ) : ℂ :=
  ∏ m, ampPhase (c m) u

/-! ## π_∥ is additive on the reciprocal indices -/

/-- π_∥ of the summed integer coordinates is the sum of the π_∥ images: additivity of
`piParallel` over a finite family, the linearity behind "acquires the factor exp[iπ_∥(∑_m G_m)·u]". -/
theorem piParallel_sum {M : ℕ} (c : Fin M → (Fin 6 → ℤ)) :
    piParallel (fun i => ((∑ m, c m) i : ℝ)) = ∑ m, piParallel (fun i => (c m i : ℝ)) := by
  funext k
  simp only [piParallel, Finset.sum_apply]
  push_cast
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.sum_mul]

/-! ## The monomial acquires the factor exp[iπ_∥(∑_m G_m)·u] (Note L659) -/

/-- **Note L659.** "a monomial ∏_m n_{G_m} acquires the factor exp[iπ_∥(∑_m G_m)·u]." The product of
the single-amplitude phase factors collapses to one phase, driven by the total reciprocal index
`∑_m G_m`. -/
theorem monoPhase_eq {M : ℕ} (c : Fin M → (Fin 6 → ℤ)) (u : Fin 3 → ℝ) :
    monoPhase c u
      = Complex.exp (Complex.I * (↑(piParallel (fun i => ((∑ m, c m) i : ℝ)) ⬝ᵥ u) : ℂ)) := by
  unfold monoPhase ampPhase
  rw [← Complex.exp_sum, ← Finset.mul_sum, ← Complex.ofReal_sum,
    piParallel_sum, sum_dotProduct]

/-! ## The analytic step: a phase trivial for every translation has zero wavevector (Note L659) -/

/-- **Note L659, "Invariance for all u ⟺ π_∥(∑ G_m)=0".** A plane-wave phase `e^{ik·u}` is `1` for
every physical translation `u` iff its wavevector `k` vanishes. The forward direction is the
engine: scaling `u` along a coordinate forces each component of `k` to zero. -/
theorem phase_trivial_iff (k : Fin 3 → ℝ) :
    (∀ u : Fin 3 → ℝ, Complex.exp (Complex.I * (↑(k ⬝ᵥ u) : ℂ)) = 1) ↔ k = 0 := by
  constructor
  · intro h
    funext j
    simp only [Pi.zero_apply]
    by_contra hj
    have hdot : k ⬝ᵥ (Pi.single j (π / k j)) = π := by
      rw [dotProduct, Finset.sum_eq_single j
        (fun i _ hij => by rw [Pi.single_eq_of_ne hij, mul_zero])
        (fun hj' => absurd (Finset.mem_univ j) hj')]
      rw [Pi.single_eq_same, mul_div_cancel₀ _ hj]
    have hone := h (Pi.single j (π / k j))
    rw [hdot, mul_comm, Complex.exp_pi_mul_I] at hone
    norm_num at hone
  · intro h u
    subst h
    simp [zero_dotProduct]

/-! ## The arithmetic step: π_∥(∑ G_m)=0 ⟺ ∑ G_m=0 in ℤ⁶ (Note L659, "(Lemma 1)" = KL20) -/

/-- **Note L659, "π_∥(∑ G_m)=0 ⟺ (Lemma 1) ∑_m G_m=0 in ℤ⁶".** The parallel projection of the total
reciprocal index vanishes iff the integer closure holds — the Star Independence Lemma (KL20),
`no_integer_relation`, is exactly this step. -/
theorem piParallel_zero_iff_closure {M : ℕ} (c : Fin M → (Fin 6 → ℤ)) :
    piParallel (fun i => ((∑ m, c m) i : ℝ)) = 0 ↔ (∑ m, c m) = 0 := by
  constructor
  · intro h
    exact no_integer_relation _ h
  · intro h
    funext k
    rw [h]
    simp [piParallel]

/-! ## KL22 — The Admissibility Lemma (Lemma 2, Note L659) -/

/-- **KL22, The Admissibility Lemma (Lemma 2, Note L659/L615).** A monomial term `∏_m n_{G_m}` is
invariant under *every* physical translation `r ↦ r+u` iff its reciprocal indices close exactly in
ℤ⁶: `∑_m G_m = 0`. "So every term in J, at every order, is indexed by an exact integer relation in
ℤ⁶. Nothing else can appear." The proof is her two-step chain: the monomial acquires
`exp[iπ_∥(∑_m G_m)·u]` (`monoPhase_eq`); this is trivial for all `u` iff `π_∥(∑_m G_m)=0`
(`phase_trivial_iff`); and that holds iff `∑_m G_m=0` in ℤ⁶ by KL20 (`piParallel_zero_iff_closure`). -/
theorem admissible_iff_closure {M : ℕ} (c : Fin M → (Fin 6 → ℤ)) :
    (∀ u : Fin 3 → ℝ, monoPhase c u = 1) ↔ (∑ m, c m) = 0 := by
  constructor
  · intro h
    apply (piParallel_zero_iff_closure c).mp
    apply (phase_trivial_iff _).mp
    intro u
    rw [← monoPhase_eq]
    exact h u
  · intro h u
    rw [monoPhase_eq]
    exact (phase_trivial_iff _).mpr ((piParallel_zero_iff_closure c).mpr h) u

end ExistenceSystem.KL22

end
