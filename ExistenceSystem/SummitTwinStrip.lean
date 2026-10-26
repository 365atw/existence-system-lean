module

/-
SUMMIT TWIN STRIP — the twin fails the strip clause the One Piece needs.

All mathematics: Kari A Light. Grades nothing; claims no RH; proves no RH.

`SummitEpstein` and `SummitEuler` prove that the Epstein twin `Z₁` of the norm form `x² + 5y²`
satisfies exactly `ζ_K`'s completed functional equation, is a Dirichlet series on `Re s > 1`, and
differs from `ζ_K` only in that its coefficients are not multiplicative. This module states the
strip-level no-go. The twin's version of `stripZeroFree` is false as soon as `Z₁` has one zero in
`1/2 < Re s < 1`.

That zero is carried as the named hypothesis `EpsteinStripZero`, never a `sorry`, never an axiom. It is
supplied OUTSIDE Lean by an interval-arithmetic (Arb ball arithmetic) argument-principle certificate
(rh-hunt-a1 report): `Z₁` has exactly one zero in the square of half-side `2⁻⁴⁰` centred at
`0.9329696974854141 + 15.668249531278473 i`, certified winding number `1 ± 5e-43`; its real part
lies in `(0.93, 0.94)`. The certificate trusts Arb's rigorous enclosures of the Hurwitz zeta function;
it is not checked by Lean. Unlike the cited Davenport–Heilbronn hypothesis (`Re s > 1`, proved in
1936 but not located), this zero is explicit and sits inside the critical strip itself.
-/

public import ExistenceSystem.SummitEuler

@[expose] public section

noncomputable section

open Complex

namespace ExistenceSystem.Summit

/-- The twin's strip clause: `Z₁` has no zero in `1/2 < Re s < 1` (the shape of `stripZeroFree`). -/
def twinStripZeroFree : Prop :=
  ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 → epsteinPrincipal s ≠ 0

/-- **Certified outside Lean, carried here.** `Z₁` has a zero with real part in `(0.93, 0.94)`.
Interval-arithmetic certificate: rh-hunt-a1 report, `/root/certify/certify.py` on the compute box. -/
def EpsteinStripZero : Prop :=
  ∃ s : ℂ, 93 / 100 < s.re ∧ s.re < 94 / 100 ∧ epsteinPrincipal s = 0

/-- Given the certified zero, the twin's strip clause is false. -/
theorem not_twinStripZeroFree (h : EpsteinStripZero) : ¬ twinStripZeroFree := by
  obtain ⟨s, h1, h2, hz⟩ := h
  intro hfree
  exact hfree s (by linarith) (by linarith) hz

/-- **The strip-level no-go.** Given the certified zero: `ζ_K` and its twin share the completed
functional equation and are Dirichlet series on `Re s > 1`; `ζ_K`'s coefficients are multiplicative
and the twin's are not; and the twin's strip clause is FALSE. So no argument that uses only what the
two share can prove `stripZeroFree`. This proves no RH and does not show multiplicativity suffices. -/
theorem strip_no_go (h : EpsteinStripZero) :
    coeffKAF.IsMultiplicative ∧ ¬ coeffEpsteinAF.IsMultiplicative ∧
      (∀ s : ℂ, completedProductK (1 - s) = (20 : ℂ) ^ (s - 1 / 2) * completedProductK s) ∧
      (∀ s : ℂ, completedEpstein (1 - s) = (20 : ℂ) ^ (s - 1 / 2) * completedEpstein s) ∧
      ¬ twinStripZeroFree :=
  ⟨euler_product_discriminates.1, euler_product_discriminates.2.1,
    euler_product_discriminates.2.2.1, euler_product_discriminates.2.2.2.1,
    not_twinStripZeroFree h⟩

end ExistenceSystem.Summit

end

end
