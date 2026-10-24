module

/-
KL7 — The non-collapse / under-determination theorem (§4.8), from THE EXACT AND FREE SYSTEM —
AN EXISTENCE SYNTHESIS. All mathematics: Kari A Light (K-A-R-I).

Source: `THE-NOTE-EDITED.md` (194,868 bytes, 1,539 lines). Line numbers below refer to that
file. Her words are quoted exactly beside each statement. Nothing of hers is graded here.

Note L98 (front-matter list form), verbatim:
"**KL7 — The non-collapse theorem.** The free direction cannot be recovered as a disguised
optimum: arg min_w J is all of E_⊥, the mixed Hessian block vanishes identically *as a function*
and not merely at a point, so no implicit-function route runs from the determined variable to the
free one — and no admissible perturbation can create one without making φ rational. *Proved in
§4.8. Rests on the Closure Transfer Lemma (KL21) and the Admissibility Lemma (KL22).*"

Note L697 (§4.8, the collapse diagnosis), verbatim:
"Every prior attempt at co-instantiating a free selection with a least-action descent put the free
quantity and the optimized quantity **in the same space**. Then any candidate free value f lies in
the domain of J; J(f) varies; any nonzero coupling makes f an implicit function of the determined
variable, f=f*(η); and the "freedom" evaporates into an arg-extremum in disguise. That is what
collapsing into optimisation means, and it is what killed every previous route."

Note L701 (the exact statement), verbatim:
"> Every uniform w **is** a global minimizer of J. The whole three-torus is argmin: arg min_w J=E_⊥.
Minimization does not select w; it **under-determines** w by three continuous parameters. As a
selector, "arg min" here carries **exactly zero bits.**"

Note L703, verbatim:
"This is precisely the structure of the indifference theorem of §3. There, V(+√r)=V(−√r)=−r²/4 and
arg min={+,−}: *both* branches are minimizers … *the minimizer set has more than one element, so
minimizing is not a selection rule.* The construction reproduces that faithfully, with the
two-element set replaced by a three-torus."

Note L705–L710 (the FOUR independent reasons it cannot collapse, KL7), verbatim:
"**Four independent reasons it cannot collapse (KL7).**
1. **Linear-algebraic.** E_∥ and E_⊥ are literal orthogonal complements in ℝ⁶: AAᵀ=I, P_∥P_⊥ᵀ=0
   exactly.
2. **Arithmetic — the decisive one.** By the Closure Transfer Lemma the phason phase factor cancels
   *identically* in every invariant of J, at every order. Consequently ∂²J/∂η∂w≡0, ∂²J/∂μ∂w≡0,
   ∂²J/∂w_k∂w_l≡0 — **everywhere on configuration space, not merely at the critical point.** The
   Hessian at the ordered state is block diagonal: positive-definite in (η,μ,the 15 stiff relative
   phases) and **exactly zero** in the 3×3 phason block. Because the mixed block is zero *as a
   function* and not *as a value at a point*, **there is no implicit-function-theorem route from η
   to w; w cannot be solved for.** Equivalently and more strongly: J factors as
   J(|n|,|m|,stiff relative phases,∇w), with uniform w simply **absent** from its domain of
   dependence. … **It is indifferent because it cannot see the variable.** That is a projection,
   not a degenerate Hessian eigendirection.
3. **Representation-theoretic.** Γ₃⊗Γ₃' has character (9,−1,−1,0,1), since φ(1−φ)=φ−φ²=−1. Its inner
   product with the trivial character is (1/60)[9−12−12+0+15]=0: **no identity component**, and
   Γ₃⊗Γ₃'=Γ₄⊕Γ₅. So no invariant bilinear coupling of a parallel vector to a perpendicular vector
   exists. **Because E_∥ and E_⊥ carry the two *inequivalent* three-dimensional irreps, the free
   direction cannot be an arg-extremum of the least-action functional.** …
4. **No perturbation can reintroduce it.** Any admissible term added to J must be invariant under
   physical-space translation, hence built from monomials with ∑π_∥(G)=0, hence (Lemma 1) with
   ∑G=0, hence perpendicular-closed, hence w-independent. To write a w-dependent local term one
   would need a physical-space closure that is *not* a lattice closure. There is none. **The only
   way to make the phason selectable is to make φ rational — that is, to destroy the quasicrystal.**"

────────────────────────────────────────────────────────────────────────────────────────────────
Reading choices and scope (the map `data/lean-scope-b/G4.md`, §"KL7 — The non-collapse theorem",
l.110–224; coverage `coverage.md` I-092 … I-098).

The module is deep in the architecture sense: a small interface — the under-determination theorems
and the four reasons — with the heavy machinery (the ℤ⁶ lattice arithmetic, the A₅ character table,
Mathlib's calculus and orthogonal-complement theory) sitting behind it in the imported modules. It
leverages them; it does not rebuild them (leaves-first).

* **J is not built here.** The Note's energy `J` (U28/U29, §4.4–§4.5) — its field content, its
  moduli, its 21 phases, its 15 stiff relative-phase combinations — is out of scope (the map, G4
  §"KL7" item 2; it is "the heavier alternative … U28 territory"). The geometry of reason 2 is
  therefore stated at the generality the argument lives at: an abstract energy `J : E → ℝ` on a real
  normed space, with the free directions carried as a subspace `Eperp : Submodule ℝ E`, and KL6's
  invariance `J(x+w)=J(x)` for `w ∈ Eperp` carried as the EXPLICIT HYPOTHESIS `hInv` (never proved,
  never an axiom) — exactly as KL19 carries its borrowed local-isomorphism premise. KL6 (No-Pinning)
  is an *inferred* dependency (the map, G4 §"KL7" item 3) and is not pulled in; `hInv` is the one
  fact about `J` the geometry consumes, and §4 below shows term-by-term why it holds.

* **The positive-definite (η,μ,15 stiff) block is NOT built** (reason 2, l.708). The map records
  (G4 §"KL7" items 2, 5) that the (η,μ) second derivative "is not shown on the page … a fact about
  layout", hundreds of lines on top of U29/U30. Only the *phason* block — "**exactly zero** … as a
  function" — is in scope; it is what the collapse argument turns on.

* **"make φ rational" (l.710) is prose, not built** (the map, G4 §"KL7" item 5, "Not formalisable as
  written"): no family in which the star's ratio varies is defined in the Note. Reason 4's
  formalisable kernel is KL21/KL22 for the *actual* star, and that is what §4 proves: an admissible
  (physical-translation-invariant) term closes in ℤ⁶ (KL22, `admissible_iff_closure`), so its
  perpendicular/phason phase is dragged to the trivial one (the π_⊥-mirror of KL20, carried on main
  as `KL21.no_integer_relation_perp`), hence the term is w-independent.

* **Record notes, hers, carried and NOT resolved** (the map, G4 §"KL7" item 5): **H5(a)** (l.701's
  "arg min_w J = E_⊥" beside the compact-torus reading §6.6 needs — here the free locus is `Eperp`,
  a subspace, not the torus `T³`); **D3** (reason 4's "No perturbation can reintroduce it." against
  §8 item 6); **D1 / H7-D1** ("free direction", "selector"). The ledger lists KL7 in the
  impossibility family ("the disguised optimum").

* **Borrowed, her marking (A7, l.1130):** Schur's lemma, which reason 3 invokes to turn "no identity
  component" into "no invariant coupling". Reason 3 here states the character arithmetic
  (1/60)[9−12−12+0+15]=0 and reuses the merged `IcosahedralRep` (`charInner_chi3_cross`); the Schur
  step is borrowed prose, not reproved here.

Structure. §1 the under-determination geometry (reason 2's engine), abstract on `hInv`; §2 reason 1
(orthogonal complements); §3 reason 3 (the character); §4 reasons 2 & 4 (the closure engine on
KL21/KL22).
-/
public import Mathlib
public import ExistenceSystem.KL21
public import ExistenceSystem.KL22
public import ExistenceSystem.IcosahedralRep

@[expose] public section

open Real

namespace ExistenceSystem.KL7

/-! ## §1. The under-determination geometry (Note L701, reason 2, l.708)

`J : E → ℝ` is an abstract energy on a real normed space; `Eperp` is the free subspace `E_⊥`; and
`hInv` is KL6's invariance `J(x+w)=J(x)` for `w ∈ Eperp` (carried, not proved — §4 shows why it
holds term by term). Everything in this section is a consequence of `hInv` alone. -/

section Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (Eperp : Submodule ℝ E) (J : E → ℝ)
  (hInv : ∀ x : E, ∀ w ∈ Eperp, J (x + w) = J x)

include hInv

/-- **Note L701 ("exactly zero bits"; L703, the §3 structure reproduced).** Over the free
directions, with every other variable held fixed, `J` is *constant*: `w₀ ↦ J (x + w₀)` takes one
value on `Eperp`. "Minimization does not select w; it **under-determines** w." As a selector it
carries exactly zero bits — the minimizer set is the whole subspace, not one point. -/
theorem constant_on_free (x : E) {w₀ w₁ : E} (h₀ : w₀ ∈ Eperp) (h₁ : w₁ ∈ Eperp) :
    J (x + w₀) = J (x + w₁) := by
  rw [hInv x w₀ h₀, hInv x w₁ h₁]

/-- **Note L701 ("Every uniform w *is* a global minimizer of J … arg min_w J = E_⊥").** Fixing every
other variable (the basepoint `x`), *every* `w₀ ∈ Eperp` minimizes `w ↦ J (x + w)` over `Eperp`: the
function is constant there (`constant_on_free`), so the whole free subspace is the arg-min. This is
the §3 indifference theorem with the two-element set `{+√r,−√r}` replaced by `E_⊥` (L703). -/
theorem isMinOn_free (x : E) {w₀ : E} (h₀ : w₀ ∈ Eperp) :
    IsMinOn (fun w => J (x + w)) (Eperp : Set E) w₀ := by
  rw [isMinOn_iff]
  intro w hw
  rw [constant_on_free Eperp J hInv x h₀ hw]

/-- **Note L708 ("∂²J/∂η∂w ≡ 0 … everywhere on configuration space").** First the first-order
engine: along any free direction `w ∈ Eperp` the directional derivative of `J` vanishes at *every*
point `x`. (`t ↦ J (x + t•w)` is constant by `hInv`, so its derivative, `fderiv ℝ J x w`, is 0.) -/
theorem fderiv_free_eq_zero (hdiff : Differentiable ℝ J) (x : E) {w : E} (hw : w ∈ Eperp) :
    fderiv ℝ J x w = 0 := by
  -- `γ t = x + t • w` has derivative `w` at `0`, and `J ∘ γ` is constant (= `J x`).
  have hγ : HasDerivAt (fun t : ℝ => x + t • w) w 0 := by
    have h := ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add x
    simpa using h
  have hcomp : HasDerivAt (fun t : ℝ => J (x + t • w)) (fderiv ℝ J x w) 0 := by
    have hf : HasFDerivAt J (fderiv ℝ J x) ((fun t : ℝ => x + t • w) 0) := by
      simpa using (hdiff x).hasFDerivAt
    exact hf.comp_hasDerivAt (0 : ℝ) hγ
  have hconst : HasDerivAt (fun t : ℝ => J (x + t • w)) 0 0 := by
    have hfun : (fun t : ℝ => J (x + t • w)) = fun _ : ℝ => J x := by
      funext t
      exact hInv x (t • w) (Eperp.smul_mem t hw)
    rw [hfun]
    exact hasDerivAt_const 0 (J x)
  exact hcomp.unique hconst

/-- **Note L708 ("the mixed block is zero *as a function* and not *as a value at a point*").** For a
free direction `w ∈ Eperp`, the map `x ↦ ∂_w J (x)` is identically the zero function. This is the
"as a function" half: not "it is zero at the critical point" but "it is the zero map on all of
configuration space". -/
theorem free_deriv_is_zero_fun (hdiff : Differentiable ℝ J) {w : E} (hw : w ∈ Eperp) :
    (fun x => fderiv ℝ J x w) = (0 : E → ℝ) := by
  funext x
  exact fderiv_free_eq_zero Eperp J hInv hdiff x hw

/-- **Note L708 ("∂²J/∂η∂w ≡ 0 … everywhere, not merely at the critical point").** The mixed Hessian
block with one slot in the free subspace vanishes identically: the derivative of `x ↦ ∂_w J (x)` is
the zero map at *every* `x`. Because `x ↦ ∂_w J (x)` is already the zero function
(`free_deriv_is_zero_fun`), all of its derivatives vanish — the block is zero "as a function". -/
theorem mixed_hessian_block_vanishes (hdiff : Differentiable ℝ J) (x : E) {w : E} (hw : w ∈ Eperp) :
    fderiv ℝ (fun y => fderiv ℝ J y w) x = 0 := by
  rw [free_deriv_is_zero_fun Eperp J hInv hdiff hw]
  exact fderiv_const_apply 0

/-- **Note L697 / L708 ("there is no implicit-function-theorem route from η to w; w cannot be solved
for").** The map `x ↦ ∂_w J (x)` has zero derivative everywhere (`mixed_hessian_block_vanishes`), so
the continuous linear map whose surjectivity Mathlib's implicit-function theorem would require (its
`range = ⊤` hypothesis) is the zero map, and the zero map into `ℝ` is not surjective. There is no
block to invert: the determined variable cannot be used to solve for the free one. -/
theorem no_implicit_function_route (hdiff : Differentiable ℝ J) (x : E) {w : E} (hw : w ∈ Eperp) :
    ¬ Function.Surjective (fderiv ℝ (fun y => fderiv ℝ J y w) x) := by
  rw [mixed_hessian_block_vanishes Eperp J hInv hdiff x hw]
  intro hsurj
  obtain ⟨y, hy⟩ := hsurj 1
  simp at hy

/-- **Note L708 ("J factors as J(|n|,|m|,stiff relative phases,∇w), with uniform w simply absent
from its domain of dependence").** `J` factors through the quotient `E ⧸ E_⊥`: configurations that
differ only by a free (uniform phason) vector get the same energy. The free coordinate is absent
from `J`'s domain of dependence — "it cannot see the variable." -/
theorem factorsThrough_quotient : Function.FactorsThrough J (fun x => Eperp.mkQ x) := by
  intro a b hab
  have hmem : a - b ∈ Eperp := by
    have hab' : Eperp.mkQ a = Eperp.mkQ b := hab
    rwa [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq] at hab'
  have hba : b + (a - b) = a := by abel
  rw [← hba]
  exact hInv b (a - b) hmem

end Geometry

/-! ## §2. Reason 1 — linear-algebraic (Note L707)

"E_∥ and E_⊥ are literal orthogonal complements in ℝ⁶: AAᵀ=I, P_∥P_⊥ᵀ=0 exactly." Stated at the
generality it lives at: a subspace `Epar` of a real inner-product space and its orthogonal
complement `Eparᗮ = E_⊥`. (The merged `Icosahedral` module carries the concrete `AAᵀ=I` —
`A_mul_transpose` — for the actual star; that is U18/G2, not rebuilt here.) -/

section Reason1

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] (Epar : Submodule ℝ F)

/-- **Note L707 ("P_∥P_⊥ᵀ=0 exactly").** A determined (parallel) vector and a free (perpendicular)
vector are orthogonal: the two subspaces do not couple. -/
theorem par_perp_inner_zero {v w : F} (hv : v ∈ Epar) (hw : w ∈ Eparᗮ) :
    (inner ℝ v w) = 0 :=
  Submodule.inner_right_of_mem_orthogonal hv hw

/-- **Note L707 ("literal orthogonal complements").** The determined and free subspaces meet only in
`0`: no nonzero vector is both parallel and perpendicular. -/
theorem par_inf_perp_eq_bot : Epar ⊓ Eparᗮ = ⊥ :=
  Submodule.inf_orthogonal_eq_bot Epar

end Reason1

/-! ## §3. Reason 3 — representation-theoretic (Note L709)

"Γ₃⊗Γ₃' has character (9,−1,−1,0,1), since φ(1−φ)=φ−φ²=−1. Its inner product with the trivial
character is (1/60)[9−12−12+0+15]=0: **no identity component** … So no invariant bilinear coupling
of a parallel vector to a perpendicular vector exists."

Reuses the merged `IcosahedralRep` (its `chi3`/`chi3'` are Γ₃/Γ₃' on A₅'s five classes, `charInner`
is the (1/60)∑|class|χψ inner product). The tensor character is the product `chi3·chi3'`. -/

section Reason3

open ExistenceSystem.IcosahedralRep ExistenceSystem.Quadratic
open scoped QuadraticAlgebra

/-- The tensor character of `Γ₃⊗Γ₃'`: on each class it is the product of the two characters. -/
noncomputable def tensorChar (c : IcosaClass) : K := chi3 c * chi3' c

/-- **Note L709 ("Γ₃⊗Γ₃' has character (9,−1,−1,0,1), since φ(1−φ)=φ−φ²=−1").** The five values of
the tensor character, class by class: `3·3=9`, `ω(1−ω)=−1` (her φ(1−φ)=−1, via
`omega_mul_one_sub`), `(1−ω)ω=−1`, `0·0=0`, `(−1)(−1)=1`. -/
theorem tensorChar_values :
    tensorChar .e = 9 ∧ tensorChar .c5 = -1 ∧ tensorChar .c5sq = -1 ∧
      tensorChar .c3 = 0 ∧ tensorChar .c2 = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · show (3 : K) * 3 = 9; norm_num
  · exact omega_mul_one_sub
  · show ((1 : K) - ω) * ω = -1; rw [mul_comm]; exact omega_mul_one_sub
  · show (0 : K) * 0 = 0; ring
  · show (-1 : K) * -1 = 1; ring

/-- **Note L709 ("Its inner product with the trivial character is (1/60)[9−12−12+0+15]=0: no
identity component").** The multiplicity of the trivial representation in `Γ₃⊗Γ₃'` is zero — the
tensor product contains no identity component. It is `⟨χ₃·χ₃', 1⟩ = ⟨χ₃, χ₃'⟩`, which the merged
`IcosahedralRep.charInner_chi3_cross` computes as `0`; concretely `(1/60)[9−12−12+0+15]=0`. Since
`E_∥` and `E_⊥` carry the *inequivalent* irreps `Γ₃`, `Γ₃'`, no invariant bilinear coupling exists
(the Schur step, A7, borrowed). -/
theorem no_identity_component : charInner tensorChar (fun _ => 1) = 0 := by
  have h : charInner tensorChar (fun _ => (1 : K)) = charInner chi3 chi3' := by
    unfold charInner tensorChar
    simp [mul_one]
  rw [h, charInner_chi3_cross]

end Reason3

/-! ## §4. Reasons 2 & 4 — the closure engine (Note L708, L710)

Reason 2: "By the Closure Transfer Lemma the phason phase factor cancels *identically* in every
invariant of J." Reason 4: "Any admissible term … hence (Lemma 1) ∑G=0, hence perpendicular-closed,
hence w-independent."

The uniform phason shift acts on an amplitude by `n_G ↦ n_G e^{iπ_⊥(G)·w}` — the π_⊥-mirror of the
physical translation of KL22. This section builds the phason phase factor and proves: a monomial is
phason-invariant for *every* `w` iff its reciprocal indices close in ℤ⁶ (`∑ G = 0`), using the
π_⊥-mirror of the Star Independence Lemma carried on main as `KL21.no_integer_relation_perp` (as
KL22 uses the π_∥ version `KL20.no_integer_relation`). Admissibility (physical-translation
invariance, KL22's `admissible_iff_closure`) therefore drags phason invariance along: every
admissible term is w-independent, so no admissible perturbation can make the phason selectable. -/

section Reason2and4

open ExistenceSystem.Icosahedral ExistenceSystem.KL22 Matrix

/-- The phason phase factor a single amplitude `n_G` (with `G` the lattice vector of integer
coordinates `c`) acquires under the uniform phason shift `w`: `n_G ↦ n_G e^{iπ_⊥(G)·w}`. The
π_⊥-mirror of `KL22.ampPhase`. -/
noncomputable def phasonAmpPhase (c : Fin 6 → ℤ) (w : Fin 3 → ℝ) : ℂ :=
  Complex.exp (Complex.I * (↑(piPerp (fun i => (c i : ℝ)) ⬝ᵥ w) : ℂ))

/-- The phason phase factor a monomial `∏_m n_{G_m}` acquires under the phason shift `w`: the product
of its amplitudes' phason phase factors. The π_⊥-mirror of `KL22.monoPhase`. -/
noncomputable def phasonPhase {M : ℕ} (c : Fin M → (Fin 6 → ℤ)) (w : Fin 3 → ℝ) : ℂ :=
  ∏ m, phasonAmpPhase (c m) w

/-- π_⊥ of the summed integer coordinates is the sum of the π_⊥ images: additivity of `piPerp` over
a finite family (the π_⊥-mirror of `KL22.piParallel_sum`). -/
theorem piPerp_sum {M : ℕ} (c : Fin M → (Fin 6 → ℤ)) :
    piPerp (fun i => ((∑ m, c m) i : ℝ)) = ∑ m, piPerp (fun i => (c m i : ℝ)) := by
  funext k
  simp only [piPerp, Finset.sum_apply]
  push_cast
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.sum_mul]

/-- **Note L708 ("the phason phase factor cancels identically").** The product of the single-amplitude
phason phase factors collapses to one phase, driven by the total reciprocal index `∑_m G_m`. The
π_⊥-mirror of `KL22.monoPhase_eq`. -/
theorem phasonPhase_eq {M : ℕ} (c : Fin M → (Fin 6 → ℤ)) (w : Fin 3 → ℝ) :
    phasonPhase c w
      = Complex.exp (Complex.I * (↑(piPerp (fun i => ((∑ m, c m) i : ℝ)) ⬝ᵥ w) : ℂ)) := by
  unfold phasonPhase phasonAmpPhase
  rw [← Complex.exp_sum, ← Finset.mul_sum, ← Complex.ofReal_sum,
    piPerp_sum, sum_dotProduct]

/-- **Note L710 ("perpendicular-closed, hence w-independent"), and reason 2 ("cancels identically").**
A monomial's phason phase factor is trivial for *every* uniform phason shift `w` iff its reciprocal
indices close exactly in ℤ⁶ (`∑_m G_m = 0`). The analytic step is `KL22.phase_trivial_iff`
(`e^{ik·w}=1 ∀w ⟺ k=0`); the arithmetic step `π_⊥(∑G)=0 ⟺ ∑G=0` is the π_⊥-mirror of KL20, carried
on main as `KL21.no_integer_relation_perp`. -/
theorem phasonPhase_trivial_iff_closure {M : ℕ} (c : Fin M → (Fin 6 → ℤ)) :
    (∀ w : Fin 3 → ℝ, phasonPhase c w = 1) ↔ (∑ m, c m) = 0 := by
  constructor
  · intro h
    have hperp : piPerp (fun i => ((∑ m, c m) i : ℝ)) = 0 := by
      apply (phase_trivial_iff _).mp
      intro w
      rw [← phasonPhase_eq]
      exact h w
    exact ExistenceSystem.KL21.no_integer_relation_perp _ hperp
  · intro h w
    rw [phasonPhase_eq]
    have hz : piPerp (fun i => ((∑ m, c m) i : ℝ)) = 0 := by
      rw [h]; funext k; simp [piPerp]
    exact (phase_trivial_iff _).mpr hz w

/-- **KL7 reason 2 (Note L708), the Closure Transfer Lemma at the level of the phase factors.**
Physical-translation invariance (admissibility) and phason invariance are equivalent — both are the
single closure `∑_m G_m = 0`. This is `KL21`'s "the perpendicular closure is not an extra
hypothesis; it is dragged along by the physical one", read on the monomial's two phase factors:
`KL22.admissible_iff_closure` for the physical side, `phasonPhase_trivial_iff_closure` for the
phason side. -/
theorem physical_iff_phason {M : ℕ} (c : Fin M → (Fin 6 → ℤ)) :
    (∀ u : Fin 3 → ℝ, monoPhase c u = 1) ↔ (∀ w : Fin 3 → ℝ, phasonPhase c w = 1) := by
  rw [admissible_iff_closure, phasonPhase_trivial_iff_closure]

/-- **KL7 reason 4 (Note L710): "No perturbation can reintroduce it."** Any admissible term — one
invariant under *every* physical-space translation (`KL22.admissible_iff_closure`: `∑G=0`) — is
*w-independent*: its phason phase factor is trivial for every uniform phason shift `w`. So no
admissible perturbation of `J` can depend on the uniform phason, and none can make it selectable.
The free direction cannot be reintroduced without a physical-space closure that is not a lattice
closure — and (KL20/KL21) there is none. -/
theorem no_admissible_perturbation_selects {M : ℕ} (c : Fin M → (Fin 6 → ℤ))
    (hadm : ∀ u : Fin 3 → ℝ, monoPhase c u = 1) :
    ∀ w : Fin 3 → ℝ, phasonPhase c w = 1 :=
  (physical_iff_phason c).mp hadm

end Reason2and4

end ExistenceSystem.KL7

end
