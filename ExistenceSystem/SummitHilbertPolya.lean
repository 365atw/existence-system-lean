module

/-
SUMMIT HILBERT–PÓLYA — the operator face is an equivalence, and why that is a warning.

All mathematics: Kari A Light. Grades nothing; claims no RH; proves no RH.

`SummitFrontiers` proves one direction of the operator face: a symmetric `T` whose eigenvalues carry
the nontrivial zeros forces every zero onto `Re = 1/2` (`stripZeroFree_of_hilbertPolya`). This module
proves the converse, so the face is an equivalence:

    stripZeroFree ↔ HilbertPolyaExists                      (`stripZeroFree_iff_hilbertPolyaExists`)

The converse is cheap, and that is its content. Given the zero line, the operator is built **from the
zeros**: on the finitely supported vectors of `ℓ²(zeros)`, multiply the basis vector at the zero
`1/2 + γ i` by the real number `γ`. So the bare existence of a Hilbert–Pólya operator is exactly the
summit and nothing lighter. The operator route can only be a lever if `T` is constructed without the
zeros (from the carrier, a geometry, a dynamics), with the correspondence proved afterwards. The
existence statement does not supply that independence.
-/

public import ExistenceSystem.SummitFrontiers
public import Mathlib

@[expose] public section

noncomputable section

open Complex

namespace ExistenceSystem.Summit

/-- The Hilbert–Pólya existence statement: some complex inner-product space carries a symmetric
operator whose eigenvalues realize every nontrivial zero as `1/2 + γ i`. -/
def HilbertPolyaExists : Prop :=
  ∃ (E : Type) (_ : NormedAddCommGroup E) (_ : InnerProductSpace ℂ E) (T : E →ₗ[ℂ] E),
    T.IsSymmetric ∧ HilbertPolyaCorrespondence T

/-! ## The diagonal model on `ℓ²` -/

namespace Diagonal

open scoped Classical

variable {Z : Type} (γ : Z → ℝ)

/-- `ℓ²(Z)`, complex-valued. -/
abbrev H (Z : Type) := lp (fun _ : Z => ℂ) 2

/-- The finitely supported vectors of `ℓ²(Z)`. -/
def finSupp (Z : Type) : Submodule ℂ (H Z) where
  carrier := {f | (Function.support (⇑f : Z → ℂ)).Finite}
  add_mem' {f g} hf hg := by
    refine (Set.Finite.union hf hg).subset ?_
    intro z hz
    rw [Function.mem_support, lp.coeFn_add, Pi.add_apply] at hz
    by_contra h
    rw [Set.mem_union, Function.mem_support, Function.mem_support, not_or, not_not,
      not_not] at h
    exact hz (by rw [h.1, h.2, add_zero])
  zero_mem' := by
    show (Function.support (⇑(0 : H Z) : Z → ℂ)).Finite
    rw [lp.coeFn_zero]
    simp
  smul_mem' c {f} hf := by
    refine Set.Finite.subset hf ?_
    intro z hz
    rw [Function.mem_support, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul] at hz
    exact right_ne_zero_of_mul hz

lemma mem_finSupp {f : H Z} : f ∈ finSupp Z ↔ (Function.support (⇑f : Z → ℂ)).Finite := Iff.rfl

lemma support_mul_subset (f : finSupp Z) :
    Function.support (fun z => (γ z : ℂ) * (f : H Z) z) ⊆ Function.support (⇑(f : H Z)) := by
  intro z hz
  rw [Function.mem_support] at hz ⊢
  exact right_ne_zero_of_mul hz

lemma memℓp_mul (f : finSupp Z) : Memℓp (fun z => (γ z : ℂ) * (f : H Z) z) 2 := by
  apply memℓp_gen
  have hfin : (Function.support (fun z => (γ z : ℂ) * (f : H Z) z)).Finite :=
    (mem_finSupp.1 f.2).subset (support_mul_subset γ f)
  refine summable_of_ne_finset_zero (s := hfin.toFinset) ?_
  intro z hz
  rw [Set.Finite.mem_toFinset, Function.notMem_support] at hz
  simp [hz]

/-- The vector `z ↦ γ z · f z`, as an element of `ℓ²`. -/
def mulVec (f : finSupp Z) : H Z := ⟨fun z => (γ z : ℂ) * (f : H Z) z, memℓp_mul γ f⟩

lemma mulVec_apply (f : finSupp Z) (z : Z) : mulVec γ f z = (γ z : ℂ) * (f : H Z) z := rfl

lemma mulVec_mem (f : finSupp Z) : mulVec γ f ∈ finSupp Z :=
  (mem_finSupp.1 f.2).subset (support_mul_subset γ f)

/-- Multiplication by the real weights `γ`. -/
def mulOp : finSupp Z →ₗ[ℂ] finSupp Z where
  toFun f := ⟨mulVec γ f, mulVec_mem γ f⟩
  map_add' f g := by
    refine Subtype.ext (lp.ext (funext fun z => ?_))
    show mulVec γ (f + g) z = (mulVec γ f + mulVec γ g : H Z) z
    rw [lp.coeFn_add, Pi.add_apply, mulVec_apply, mulVec_apply, mulVec_apply,
      Submodule.coe_add, lp.coeFn_add, Pi.add_apply, mul_add]
  map_smul' c f := by
    refine Subtype.ext (lp.ext (funext fun z => ?_))
    show mulVec γ (c • f) z = (c • mulVec γ f : H Z) z
    rw [lp.coeFn_smul, Pi.smul_apply, mulVec_apply, mulVec_apply, Submodule.coe_smul,
      lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
    ring

lemma mulOp_apply (f : finSupp Z) (z : Z) :
    ((mulOp γ f : finSupp Z) : H Z) z = (γ z : ℂ) * (f : H Z) z := rfl

/-- Real weights make the multiplication operator symmetric. -/
theorem mulOp_isSymmetric : (mulOp γ).IsSymmetric := by
  intro f g
  rw [Submodule.coe_inner, Submodule.coe_inner, lp.inner_eq_tsum, lp.inner_eq_tsum]
  congr 1
  funext z
  rw [mulOp_apply, mulOp_apply]
  simp only [RCLike.inner_apply, map_mul, Complex.conj_ofReal]
  ring

/-- The basis vector at `z` is finitely supported. -/
lemma single_mem (z : Z) : lp.single (E := fun _ : Z => ℂ) 2 z (1 : ℂ) ∈ finSupp Z := by
  rw [mem_finSupp]
  refine (Set.finite_singleton z).subset ?_
  intro w hw
  rw [Function.mem_support] at hw
  by_contra hne
  exact hw (lp.single_apply_ne (E := fun _ : Z => ℂ) 2 z (1 : ℂ) hne)

/-- The basis vector at `z`, in the finitely supported subspace. -/
def basisVec (z : Z) : finSupp Z := ⟨lp.single (E := fun _ : Z => ℂ) 2 z (1 : ℂ), single_mem z⟩

/-- The basis vector at `z` is an eigenvector with eigenvalue `γ z`. -/
theorem mulOp_basisVec (z : Z) : mulOp γ (basisVec z) = (γ z : ℂ) • basisVec z := by
  refine Subtype.ext (lp.ext (funext fun w => ?_))
  show (γ w : ℂ) * lp.single (E := fun _ : Z => ℂ) 2 z (1 : ℂ) w = ((γ z : ℂ) • lp.single (E := fun _ : Z => ℂ) 2 z (1 : ℂ) : H Z) w
  rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  by_cases h : w = z
  · subst h
    rfl
  · rw [lp.single_apply_ne (E := fun _ : Z => ℂ) 2 z (1 : ℂ) h, mul_zero, mul_zero]

lemma basisVec_ne_zero (z : Z) : basisVec z ≠ 0 := by
  intro h
  have := congrArg (fun f : finSupp Z => (f : H Z) z) h
  simp only [basisVec, ZeroMemClass.coe_zero,
    lp.single_apply_self] at this
  exact one_ne_zero this

end Diagonal

/-! ## The equivalence -/

/-- **The converse, PROVED.** On the zero line, the diagonal operator on `ℓ²(zeros)` with weight
`Im s` is a symmetric Hilbert–Pólya operator. It is built from the zeros themselves. -/
theorem hilbertPolyaExists_of_zeroLine (h : ZeroLine) : HilbertPolyaExists := by
  let Z : Type := {s : ℂ // NontrivialZero s}
  let γ : Z → ℝ := fun z => (z : ℂ).im
  refine ⟨Diagonal.finSupp Z, inferInstance, inferInstance, Diagonal.mulOp γ,
    Diagonal.mulOp_isSymmetric γ, ?_⟩
  intro s hs
  refine ⟨((s.im : ℝ) : ℂ), Diagonal.basisVec (⟨s, hs⟩ : Z),
    Diagonal.basisVec_ne_zero _, Diagonal.mulOp_basisVec γ _, ?_⟩
  apply Complex.ext
  · simp [h s hs]
  · simp

/-- **The operator face is an equivalence.** A symmetric Hilbert–Pólya operator exists iff
`stripZeroFree`. Forward builds the diagonal operator from the zeros; backward is
`stripZeroFree_of_hilbertPolya`. The existence form is therefore exactly the summit; only an
independent construction of `T` could be a lever. -/
theorem stripZeroFree_iff_hilbertPolyaExists : stripZeroFree ↔ HilbertPolyaExists := by
  constructor
  · intro h
    exact hilbertPolyaExists_of_zeroLine (stripZeroFree_iff_zeroLine.1 h)
  · rintro ⟨E, _, _, T, hT, hcorr⟩
    exact stripZeroFree_of_hilbertPolya hT hcorr

end ExistenceSystem.Summit

end

end
