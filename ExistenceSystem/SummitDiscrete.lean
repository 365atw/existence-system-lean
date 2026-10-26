module

/-
SUMMIT DISCRETE — the zeros of `ζ(s) L(s, χ_{−20})` are discrete: finitely many up to each height.

All mathematics: Kari A Light. Grades nothing; claims no RH; proves no RH.

`SummitFrontiers` carried the discreteness of the nontrivial zeros as the named structure
`ZeroCount`. This module PROVES it, so the carried hypothesis is removed and the counting adapter
becomes unconditional:

    countsAgree_iff_stripZeroFree' : zeroCount.CountsAgree ↔ stripZeroFree

What is proved, from Mathlib and the summit chain only:

1. The critical strip: a nontrivial zero has `0 < Re s < 1` (`nontrivialZero_re_pos`,
   `nontrivialZero_re_lt_one`) — the right edge is `zetaProduct_ne_zero_of_one_le_re`, the left
   edge is the reflection `nontrivialZero_one_sub`.
2. No zeros near the pole: `s = 1` is not an accumulation point of zeros
   (`zetaProduct_ne_zero_near_one`) — the residue `(s−1) ζ(s) → 1` and `L(1, χ) ≠ 0`.
3. Finiteness (`nontrivialZero_finite`): the zeros of height `≤ T` lie in the compact ball of
   radius `T + 1`; an infinite set there would have an accumulation point `x`; `x = 1` is excluded
   by (2), and `x ≠ 1` forces `zetaProduct ≡ 0` on the connected set `ℂ ∖ {1}` by the identity
   theorem, contradicting `zetaProduct 2 ≠ 0`.
4. `zeroCount : ZeroCount` built from (3), and the unconditional adapter above.

The functional-equation symmetry, the Riemann–von Mangoldt count and RH itself are untouched.
-/

public import ExistenceSystem.SummitFrontiers
public import Mathlib

@[expose] public section

noncomputable section

open Complex Filter Topology
open ExistenceSystem.TheThing

namespace ExistenceSystem.Summit

/-! ## 1. Confinement to the critical strip -/

/-- A nontrivial zero lies strictly left of `Re = 1`. -/
theorem nontrivialZero_re_lt_one {s : ℂ} (h : NontrivialZero s) : s.re < 1 := by
  by_contra hs
  exact zetaProduct_ne_zero_of_one_le_re (not_lt.1 hs) h.1

/-- A nontrivial zero lies strictly right of `Re = 0`: reflect through `s ↦ 1 − s`. -/
theorem nontrivialZero_re_pos {s : ℂ} (h : NontrivialZero s) : 0 < s.re := by
  have := nontrivialZero_re_lt_one (nontrivialZero_one_sub h)
  rw [sub_re, one_re] at this
  linarith

/-! ## 2. No zeros accumulate at the pole -/

/-- Near the pole `s = 1`, off it, `ζ(s) L(s, χ_{−20})` has no zeros. -/
theorem zetaProduct_ne_zero_near_one :
    ∀ᶠ s in 𝓝[≠] (1 : ℂ), zetaProduct s ≠ 0 := by
  have hζ : ∀ᶠ s in 𝓝[≠] (1 : ℂ), riemannZeta s ≠ 0 := by
    filter_upwards [riemannZeta_residue_one.eventually_ne one_ne_zero] with s hs hz
    exact hs (by rw [hz, mul_zero])
  have hLc : ContinuousAt (DirichletCharacter.LFunction χ_neg20ℂ) 1 :=
    (DirichletCharacter.differentiableAt_LFunction χ_neg20ℂ 1
      (Or.inr χ_neg20ℂ_ne_one)).continuousAt
  have hL : ∀ᶠ s in 𝓝 (1 : ℂ), DirichletCharacter.LFunction χ_neg20ℂ s ≠ 0 :=
    hLc.eventually_ne (DirichletCharacter.LFunction_apply_one_ne_zero χ_neg20ℂ_ne_one)
  filter_upwards [hζ, nhdsWithin_le_nhds hL] with s h1 h2
  exact mul_ne_zero h1 h2

/-! ## 3. Finiteness of the zeros below any height -/

/-- `zetaProduct` is not identically zero off the pole: it is nonzero at `s = 2`. -/
theorem zetaProduct_two_ne_zero : zetaProduct 2 ≠ 0 :=
  zetaProduct_ne_zero_of_one_le_re (by norm_num)

/-- The nontrivial zeros of height `≤ T` form a finite set. -/
theorem nontrivialZero_finite (T : ℝ) : {s : ℂ | NontrivialZero s ∧ |s.im| ≤ T}.Finite := by
  set S : Set ℂ := {s : ℂ | NontrivialZero s ∧ |s.im| ≤ T} with hS
  by_contra hinf
  have hsub : S ⊆ Metric.closedBall (0 : ℂ) (T + 1) := by
    intro s hs
    rw [Metric.mem_closedBall, dist_zero_right]
    have h1 := nontrivialZero_re_lt_one hs.1
    have h2 := nontrivialZero_re_pos hs.1
    have h3 : ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
    rw [abs_of_pos h2] at h3
    linarith [hs.2]
  obtain ⟨x, -, hx⟩ :=
    Set.Infinite.exists_accPt_of_subset_isCompact hinf (isCompact_closedBall _ _) hsub
  have hfreq : ∃ᶠ y in 𝓝[≠] x, y ∈ S := by
    rw [accPt_iff_frequently_nhdsNE] at hx
    exact hx
  by_cases hx1 : x = 1
  · subst hx1
    have := (zetaProduct_ne_zero_near_one.and_frequently hfreq)
    obtain ⟨y, hy1, hy2⟩ := this.exists
    exact hy1 hy2.1.1
  · have hU : IsOpen ({1}ᶜ : Set ℂ) := isOpen_compl_singleton
    have hP : DifferentiableOn ℂ zetaProduct {1}ᶜ := fun s hs =>
      (differentiableAt_zetaProduct hs).differentiableWithinAt
    have hA : AnalyticOnNhd ℂ zetaProduct {1}ᶜ := hP.analyticOnNhd hU
    have hconn : IsPreconnected ({1}ᶜ : Set ℂ) :=
      (isConnected_compl_singleton_of_one_lt_rank (by simp) 1).isPreconnected
    have hzero : ∃ᶠ y in 𝓝[≠] x, zetaProduct y = 0 :=
      hfreq.mono fun y hy => hy.1.1
    have h0 := hA.eqOn_zero_of_preconnected_of_frequently_eq_zero hconn hx1 hzero
    have h2 : (2 : ℂ) ∈ ({1}ᶜ : Set ℂ) := by norm_num
    exact zetaProduct_two_ne_zero (h0 h2)

/-! ## 4. The zero count, unconditionally -/

/-- The discreteness structure of `SummitFrontiers`, built rather than carried. -/
def zeroCount : ZeroCount where
  zeros T := (nontrivialZero_finite T).toFinset
  mem_zeros T s := by simp

/-- The counting adapter with no carried hypothesis:
`N₀(T) = N(T)` for all `T` iff `stripZeroFree`. -/
theorem countsAgree_iff_stripZeroFree' : zeroCount.CountsAgree ↔ stripZeroFree :=
  countsAgree_iff_stripZeroFree zeroCount

/-- The counting face is RH-strength, unconditionally. -/
theorem countsAgree_iff_RH' :
    zeroCount.CountsAgree ↔ RiemannHypothesis ∧ dirichletZeroLine :=
  countsAgree_iff_RH zeroCount

end ExistenceSystem.Summit

end

end
