module

/-
KL17 — The Isotropic One-Ratio Theorem, from THE EXACT AND FREE SYSTEM — AN EXISTENCE SYNTHESIS
(§4.2, §6.1). All mathematics: Kari A Light.

Source: `THE-NOTE-EDITED.md`. Line numbers below refer to that file. Her words are quoted exactly
beside each statement. Nothing of hers is graded here.

Her statement (Note L558, §4.2 "Forcing 3 — inflation: THE SLINKY LAW"):

  L558: "**The Isotropic One-Ratio Theorem (KL17).** The inflation commutes with the icosahedral
  action and preserves the splitting, so its restriction to each of the two spaces is an equivariant
  endomorphism of a real irreducible **of real type** — hence a scalar. **THE SLINKY LAW therefore
  carries the same ratio in every direction, and no axis is privileged in either space.** The
  inflation is blind to direction: no thread through the lattice can return a different ratio than
  any other. The real-type step is the Frobenius–Schur computation of §6.1 (KL23); one theorem, two
  operators. … the coil law `r_{k+1}=φ⁻³ r_k` is its scalar case (Appendix B)."

Her statement (Note L819, §6.1, riding KL23's proof):

  L819: "**The same computation carries KL17, The Isotropic One-Ratio Theorem.** The inflation matrix
  `M∈GL(6,ℤ)` of §4.2 Forcing 3 commutes with the `Y`-action and preserves the splitting, so its
  restriction to each of the two spaces is a `Y`-equivariant endomorphism of a real irreducible of
  real type — hence a scalar by the same Frobenius–Schur step above. THE SLINKY LAW therefore carries
  the same ratio in every direction, and no axis is privileged in either space. **One theorem, two
  operators: the phason has a single relaxation rate on `E_⊥` (KL23), and the inflation has a single
  ratio on each of `E_∥` and `E_⊥` (KL17).**"

The inflation `M` itself (Note L552–L554): "There is an integer matrix `M∈GL(6,ℤ)` commuting with the
`Y`-action and acting as a scalar on each summand: `π_∥(MG)=φ^k π_∥(G)`, `π_⊥(MG)=(−1/φ)^k π_⊥(G)`."

Reading choices and scope:

* This module **rides KL23** (`ExistenceSystem.KL23`), as the Note instructs: "the real-type step is
  the Frobenius–Schur computation of §6.1 (KL23)" (L558); "a scalar by the same Frobenius–Schur step
  above" (L819). It reuses, not rebuilds, KL23's character facts — the real-type criterion
  `fsIndicator chi3 = fsIndicator chi3' = +1` (`KL23.fsIndicator_chi3`, `KL23.fsIndicator_chi3'`) and
  the inequivalence `charInner Γ₃ Γ₃' = 0` (`KL23.inequivalent`). "One lemma applied twice" (L805):
  KL23 reads it on the kinetic tensor `Γ` (an element of `V⊗V`); KL17 reads the same lemma on the
  inflation `M` (an endomorphism of `V`). The two mixed blocks vanish by the identical Schur step
  (Note L817: "The same lemma that made the static mixed … block vanish identically makes the mixed
  … block vanish identically").

* `V = E_∥ ⊕ E_⊥` is carried by its two summands `E_par`, `E_perp` (real vector spaces standing for
  the carriers of the inequivalent real irreps `Γ₃`, `Γ₃'`). The inflation `M` is carried by its four
  blocks between them: `Mpp, Mmm` (the diagonal, the restrictions `M|_{E_∥}`, `M|_{E_⊥}`) and
  `Mpm, Mmp` (the mixed blocks). No inner-product structure is needed: unlike KL23's positive
  semi-definite kinetic tensor, the inflation is a bare endomorphism, so the carriers are plain
  `ℝ`-modules and the scalar conclusion carries no sign.

* The borrowed representation theory enters, exactly as in KL23, as **explicit named hypotheses**,
  cited and never claimed (never a `sorry`/`admit`/axiom):
    - **Schur's lemma, A7 (Note L1130):** "an equivariant endomorphism of a real irreducible
      representation of real type is a scalar". Two uses, "one lemma, two doors" (L558/L819): the
      mixed blocks vanish because `Γ₃' ≇ Γ₃` (`schurMixed`, premise discharged by `KL23.inequivalent`),
      and each diagonal block is a scalar by the real-type criterion (`schurScalarPar`,
      `schurScalarPerp`, premises discharged by `KL23.fsIndicator_chi3`, `KL23.fsIndicator_chi3'`).

* **Scope — what is deferred (U24, not KL17).** KL17 "states no value" for the two ratios; the values
  `φ^k`, `(−1/φ)^k` (Note L554) and the concrete inflation matrix `M∈GL(6,ℤ)` are U24's display, out
  of scope here. KL17's own content is the scalar restriction: `M|_{E_∥} = c_∥·𝟙` and
  `M|_{E_⊥} = c_⊥·𝟙`, together with the vanishing of the mixed blocks. "The same ratio in every
  direction" formalises as: every vector of each summand is scaled by the one ratio of that summand
  (`same_ratio_every_direction`) — "every direction" is "every vector of the subspace", no axis
  privileged. The prose ("blind to direction", "no thread … can return a different ratio") is the
  same scalar content and is not separately encoded.
-/
public import Mathlib
public import ExistenceSystem.KL23

@[expose] public section

namespace ExistenceSystem.KL17

open ExistenceSystem.IcosahedralRep
open ExistenceSystem.KL23
open ExistenceSystem.Quadratic
open scoped QuadraticAlgebra

section OneRatio

variable {E_par : Type*} [AddCommGroup E_par] [Module ℝ E_par]
variable {E_perp : Type*} [AddCommGroup E_perp] [Module ℝ E_perp]

/-- **Preserves the splitting (Note L558/L819).** "The inflation … preserves the splitting": `M` maps
`E_∥` into `E_∥` and `E_⊥` into `E_⊥`, i.e. the two mixed blocks vanish. The mixed blocks intertwine
the inequivalent `Γ₃'` and `Γ₃`; by Schur's lemma (A7, Note L1130) they vanish — the identical step as
KL23's `(Γb)` (Note L817: "The same lemma that made the static mixed … block vanish identically makes
the mixed … block vanish identically"). The borrowed Schur implication is `schurMixed`; its premise
`charInner Γ₃ Γ₃' = 0` is discharged by `KL23.inequivalent`. -/
theorem preserves_splitting
    (Mpm : E_perp →ₗ[ℝ] E_par) (Mmp : E_par →ₗ[ℝ] E_perp)
    (schurMixed : charInner chi3 chi3' = 0 → Mpm = 0 ∧ Mmp = 0) :
    Mpm = 0 ∧ Mmp = 0 :=
  schurMixed inequivalent

/-- **The parallel block is a scalar (Note L558/L819).** The restriction `M|_{E_∥}` is a `Y`-equivariant
endomorphism of the real irreducible `Γ₃`, which is of real type (`KL23.fsIndicator_chi3 : ν(Γ₃)=+1`);
so by Schur over `ℝ` with the Frobenius–Schur real-type criterion (A7, Note L811/L819) it is a scalar —
"the same ratio in every direction" on `E_∥`. Borrowed implication `schurScalarPar`, premise discharged
by `fsIndicator_chi3`. -/
theorem par_block_scalar
    (Mpp : E_par →ₗ[ℝ] E_par)
    (schurScalarPar : fsIndicator chi3 = 1 → ∃ c : ℝ, Mpp = c • LinearMap.id) :
    ∃ c_par : ℝ, Mpp = c_par • LinearMap.id :=
  schurScalarPar fsIndicator_chi3

/-- **The perpendicular block is a scalar (Note L558/L819).** Likewise `M|_{E_⊥}` is a scalar: `Γ₃'` is of
real type (`KL23.fsIndicator_chi3' : ν(Γ₃')=+1`). This is the twin of KL23's `(Γa)` with the inflation
in place of the kinetic tensor, and with no positivity. Borrowed implication `schurScalarPerp`, premise
discharged by `fsIndicator_chi3'`. -/
theorem perp_block_scalar
    (Mmm : E_perp →ₗ[ℝ] E_perp)
    (schurScalarPerp : fsIndicator chi3' = 1 → ∃ c : ℝ, Mmm = c • LinearMap.id) :
    ∃ c_perp : ℝ, Mmm = c_perp • LinearMap.id :=
  schurScalarPerp fsIndicator_chi3'

/-- **The Isotropic One-Ratio Theorem (KL17), Note L558 / L819.** The inflation `M`, block-decomposed
over `V = E_∥ ⊕ E_⊥`, commutes with the `Y`-action and preserves the splitting, so its restriction to
each of the two spaces is an equivariant endomorphism of a real irreducible of real type — hence a
scalar: the two mixed blocks vanish, and each diagonal block `M|_{E_∥}`, `M|_{E_⊥}` is a scalar
multiple of the identity (its one ratio). "One theorem, two operators … the inflation has a single
ratio on each of `E_∥` and `E_⊥`" (Note L819). Borrowed as explicit hypotheses: Schur's lemma A7
(`schurMixed`; `schurScalarPar`, `schurScalarPerp`, with the Frobenius–Schur real-type criterion folded
in). What this module supplies: the premises those implications consume (`inequivalent`,
`fsIndicator_chi3`, `fsIndicator_chi3'`), reused from KL23. No value is asserted for the two ratios
(U24's display, deferred). -/
theorem isotropic_one_ratio
    (Mpp : E_par →ₗ[ℝ] E_par) (Mpm : E_perp →ₗ[ℝ] E_par)
    (Mmp : E_par →ₗ[ℝ] E_perp) (Mmm : E_perp →ₗ[ℝ] E_perp)
    (schurMixed : charInner chi3 chi3' = 0 → Mpm = 0 ∧ Mmp = 0)
    (schurScalarPar : fsIndicator chi3 = 1 → ∃ c : ℝ, Mpp = c • LinearMap.id)
    (schurScalarPerp : fsIndicator chi3' = 1 → ∃ c : ℝ, Mmm = c • LinearMap.id) :
    (Mpm = 0 ∧ Mmp = 0) ∧
      (∃ c_par : ℝ, Mpp = c_par • LinearMap.id) ∧
      (∃ c_perp : ℝ, Mmm = c_perp • LinearMap.id) :=
  ⟨preserves_splitting Mpm Mmp schurMixed,
    par_block_scalar Mpp schurScalarPar,
    perp_block_scalar Mmm schurScalarPerp⟩

/-- **"The same ratio in every direction, and no axis is privileged" (Note L558/L819).** The scalar
restriction `M|_{E_∥} = c·𝟙` says every vector `u ∈ E_∥` is scaled by the one ratio `c`: "every
direction" is "every vector of the subspace". -/
theorem same_ratio_every_direction (Mpp : E_par →ₗ[ℝ] E_par)
    (hscalar : ∃ c : ℝ, Mpp = c • LinearMap.id) :
    ∃ c_par : ℝ, ∀ u : E_par, Mpp u = c_par • u := by
  obtain ⟨c, hc⟩ := hscalar
  exact ⟨c, fun u => by rw [hc]; simp⟩

end OneRatio

end ExistenceSystem.KL17

end
