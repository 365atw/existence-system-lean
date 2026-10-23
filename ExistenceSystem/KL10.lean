module

/-
KL10 — Lemma 4, the conservation statement, from THE EXACT AND FREE SYSTEM — AN EXISTENCE SYNTHESIS.
All mathematics: Kari A Light.

Source: `THE-NOTE-EDITED.md` (194,868 bytes, 1,539 lines). Line numbers below refer to that file.
Her words are quoted exactly beside each statement. Nothing of hers is graded here.

The statement is known (A14/A18 — Kunin et al. — reached independently); what is new is its USE,
not the statement. This module does not claim the statement as novel.

Note L104: "Every continuous symmetry of a potential is an exactly conserved quantity of the
gradient flow that potential generates."
Note L1144 (A14): "The statement itself is known: the earliest clean named form is Kunin et al.
(A18) … What is new here is its use …"
Note L1152 (A18): "This is the statement of Lemma 4, §6.4, which was reached here independently."

Only the body's mathematics is formalised (Note L909). A continuous symmetry is her one-parameter
translation `x ↦ x + s • v` on a real inner-product space; the conserved quantity is the linear
coordinate `v · x` along a solution of `ẋ = -Γ ∇J`. The list form's words "every continuous
symmetry", read as a general group action, are not encoded: the Note defines no such action, and
A19 marks that case as a different object (the map, `data/lean-scope-b/G5.md` §1.5). The gradient
flow is a hypothesis on a curve. Existence of solutions is not claimed. The prose after L911 —
the Noether contrast, the table, and "the direction the functional cannot see" — is not encoded.
-/
public import Mathlib

@[expose] public section

noncomputable section

open InnerProductSpace
open scoped RealInnerProductSpace

namespace ExistenceSystem.KL10

/-! ## The null direction of the potential

Note L909: "Let $J$ be $C^{1}$ on a configuration space carrying an inner product, invariant under
a one-parameter translation $x\mapsto x+sv$. Then $v\cdot\nabla J\equiv0$ everywhere."
Her $C^{1}$ is `ContDiff ℝ 1`. The configuration space is a real inner-product space, complete
because Mathlib's `gradient` asks for `CompleteSpace`.
-/

/-- Note L909: invariance under `x ↦ x + s v` gives "$v\cdot\nabla J\equiv0$ everywhere". -/
theorem inner_gradient_eq_zero
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {J : E → ℝ} {v : E} (hJ : ContDiff ℝ 1 J)
    (hinv : ∀ x : E, ∀ s : ℝ, J (x + s • v) = J x) (x : E) :
    ⟪v, gradient J x⟫ = 0 := by
  -- `s ↦ J(x + s • v)` is constant, so its derivative at `0` is `0`. The chain rule
  -- says that derivative is `⟨∇J(x), v⟩`.
  have hFd : HasFDerivAt J (toDual ℝ E (gradient J x)) x :=
    (hJ.differentiable_one x).hasGradientAt.hasFDerivAt
  have hline : HasDerivAt (fun s : ℝ => J (x + s • v)) ((toDual ℝ E (gradient J x)) v) 0 :=
    hFd.hasLineDerivAt v
  have hconst : HasDerivAt (fun s : ℝ => J (x + s • v)) (0 : ℝ) 0 := by
    have heq : (fun s : ℝ => J (x + s • v)) = fun _ : ℝ => J x := by
      funext s
      exact hinv x s
    rw [heq]
    exact hasDerivAt_const (0 : ℝ) (J x)
  have hz : ⟪gradient J x, v⟫ = 0 := by
    simpa only [toDual_apply_apply] using hline.unique hconst
  rw [real_inner_comm (gradient J x) v]
  exact hz

/-! ## The conserved coordinate of the flow

Note L909: "If further $\Gamma$ is **constant**, symmetric, with $\Gamma v\parallel v$, then along
any solution of $\dot x=-\Gamma\nabla J$,
$\frac{d}{dt}(v\cdot x)=-v\cdot\Gamma\nabla J=-(\Gamma v)\cdot\nabla J=-\Gamma_v(v\cdot\nabla J)=0$."
`Γ` constant is one continuous linear map. `Γ v ∥ v` is `Γ v = Γv • v`, and `Γv` is her `Γ_v`.
-/

/-- Note L909, the displayed line: along a solution, `d/dt (v · x) = 0`. -/
theorem hasDerivAt_coord
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {J : E → ℝ} {v : E} {Γ : E →L[ℝ] E} {Γv : ℝ}
    (hJ : ContDiff ℝ 1 J) (hinv : ∀ x : E, ∀ s : ℝ, J (x + s • v) = J x)
    (hsym : LinearMap.IsSymmetric (Γ : E →ₗ[ℝ] E)) (heig : Γ v = Γv • v)
    {γ : ℝ → E} {t : ℝ} (hγ : HasDerivAt γ (-(Γ (gradient J (γ t)))) t) :
    HasDerivAt (fun s => ⟪v, γ s⟫) 0 t := by
  -- Note L909: `d/dt (v · x) = -v · Γ ∇J = -(Γ v) · ∇J = -Γᵥ (v · ∇J) = 0`.
  have hzero : ⟪v, gradient J (γ t)⟫ = 0 := inner_gradient_eq_zero hJ hinv (γ t)
  have hv : HasDerivAt (fun _ : ℝ => v) 0 t := hasDerivAt_const t v
  have hinner := hv.inner ℝ hγ
  simp only [inner_zero_left, add_zero] at hinner
  have hcalc : ⟪v, -(Γ (gradient J (γ t)))⟫ = 0 := by
    rw [inner_neg_right, ← LinearMap.IsSymmetric.apply_clm hsym v (gradient J (γ t)),
      heig, real_inner_smul_left, hzero]
    ring
  simpa [hcalc] using hinner

/-- Note L909 / L104. The linear coordinate `v · x` is an exactly conserved quantity of any
solution of `ẋ = -Γ ∇J`.

"Every continuous symmetry of a potential is an exactly conserved quantity of the gradient flow
that potential generates."

The statement is known (A14/A18 — Kunin et al. — reached independently); what is new is its USE,
not the statement. -/
theorem conserved_coord
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {J : E → ℝ} {v : E} {Γ : E →L[ℝ] E} {Γv : ℝ}
    (hJ : ContDiff ℝ 1 J) (hinv : ∀ x : E, ∀ s : ℝ, J (x + s • v) = J x)
    (hsym : LinearMap.IsSymmetric (Γ : E →ₗ[ℝ] E)) (heig : Γ v = Γv • v)
    {γ : ℝ → E} (hγ : ∀ t, HasDerivAt γ (-(Γ (gradient J (γ t)))) t) :
    ∀ t₁ t₂, ⟪v, γ t₁⟫ = ⟪v, γ t₂⟫ := by
  have hdiff : Differentiable ℝ (fun t => ⟪v, γ t⟫) := fun t =>
    (hasDerivAt_coord hJ hinv hsym heig (hγ t)).differentiableAt
  have hzero : ∀ t, deriv (fun s => ⟪v, γ s⟫) t = 0 := fun t =>
    (hasDerivAt_coord hJ hinv hsym heig (hγ t)).deriv
  intro t₁ t₂
  exact is_const_of_deriv_eq_zero hdiff hzero t₁ t₂

/-- The gradient flow `ẋ = -∇J` (`Γ = id` in Note L909). A translation symmetry of `J` is a first
integral of that flow: `t ↦ v · γ(t)` is constant. -/
theorem conserved_along_neg_gradient
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {J : E → ℝ} {v : E} (hJ : ContDiff ℝ 1 J)
    (hinv : ∀ x : E, ∀ s : ℝ, J (x + s • v) = J x)
    {γ : ℝ → E} (hγ : ∀ t, HasDerivAt γ (-(gradient J (γ t))) t) :
    ∀ t₁ t₂, ⟪v, γ t₁⟫ = ⟪v, γ t₂⟫ := by
  -- `Γ = id` is constant and symmetric, and `id v = 1 • v`, so L909 applies.
  have hsym : LinearMap.IsSymmetric (ContinuousLinearMap.id ℝ E : E →ₗ[ℝ] E) :=
    fun x y => rfl
  have heig : (ContinuousLinearMap.id ℝ E) v = (1 : ℝ) • v := by simp
  exact conserved_coord hJ hinv hsym heig fun t => by simpa using hγ t

end ExistenceSystem.KL10

end

end
