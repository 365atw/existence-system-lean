module

/-
SUMMIT FRONTIERS — the one lock, seen from three sides.

All mathematics: Kari A Light. Grades nothing; claims no RH; proves no RH.

The summit chain reduces the whole open problem for the One Piece `K = ℚ(√−5)` to the single
named proposition `stripZeroFree` (`SummitStrip`), and proves

    stripZeroFree ↔ RiemannHypothesis ∧ dirichletZeroLine                (`stripZeroFree_iff`)

so any proposition strong enough to force every nontrivial zero onto `Re = 1/2` is exactly
RH-strength (`data/summit-force-s1/report.md`, §2). This module records, in the repo's own
named-frontier discipline (the pattern of KL16's `ExhaustiveToBound` and KL19's `LIClassEqualFreq`:
a named `Prop`, a PROVED adapter, NEVER a `sorry`, never a false "reduction"), the captain's two
routes from the scout report as three faces of that one lock.

`stripZeroFree` is the summit's single undischarged **seam** — a deep module whose one-line interface
carries the entire open problem. Each face below is an **adapter** at that seam: a named `Prop` plus a
proved equivalence (or implication) to `stripZeroFree`. Two adapters make a hypothetical seam a real
one; here there are three, so the record shows all three faces are the same lock, RH-strength, and
exactly where it sits.

- Route 1, positivity (Li / Bombieri–Lagarias). `LiPositive` — every Keiper–Li coefficient `λ_n^K`
  of the completed `ξ_K` is `≥ 0`. The Li criterion `λ_n ≥ 0 ∀n ⟺ RH for K` is the open prior art
  (Li 1997; Bombieri–Lagarias 1999; the Hadamard/explicit-formula link is not in Mathlib): it is
  carried as the named cited hypothesis `LiCriterion`, never proved, never an axiom. The adapter
  `liPositive_iff_stripZeroFree` composes it with `stripZeroFree_iff`. (Report §3.1, §6.1.)
- Route 1, operator (Hilbert–Pólya / de Branges). `HilbertPolyaCorrespondence` — a symmetric operator
  `T` on a complex inner-product space whose spectrum carries the zeros (each nontrivial zero is
  `1/2 + γ·i` with `γ` an eigenvalue of `T`). The construction of `T` is the open problem and is never
  built; the genuine content is PROVED: a symmetric operator has real spectrum
  (`conj_eigenvalue_eq_self`), so `γ ∈ ℝ` forces `Re = 1/2`. Adapter `stripZeroFree_of_hilbertPolya`.
  (Report §3, §6.2.)
- Route 2, counting (method of carrying). `ZeroCount` carries the discreteness of the zeros (finitely
  many up to each height — a genuine theorem, not in Mathlib for this product; carried as a named
  structure, the KL16 `SplittingData` pattern). From it the on-line count `N₀(T)`, total count
  `N(T)`, and the `Prop` `CountsAgree` (`N₀(T) = N(T) ∀T`) are defined and the adapter
  `countsAgree_iff_stripZeroFree` is PROVED:
  `N₀(T) = N(T) ∀T ⟺ stripZeroFree`. The functional-equation symmetry gives `N(T)` as a global
  invariant but is blind to on/off-line, because off-line zeros occur in line-symmetric pairs that
  contribute to `N(T)` identically to on-line ones (report §4) — that blindness is why the counting
  face is the lock, not a lever, and it is recorded here in prose, not graded.

The summit chain and `stripZeroFree` are untouched; this is added alongside.
-/

public import ExistenceSystem.SummitStrip
public import Mathlib

@[expose] public section

noncomputable section

open Complex

open scoped Classical

namespace ExistenceSystem.Summit

/-! ## The backbone adapter: the strip clause is "every nontrivial zero on the line"

`zeroLine_of_stripZeroFree` is the proved forward direction (`SummitStrip`). The converse is clean:
a zero in the open strip `1/2 < Re s < 1` is a nontrivial zero with `Re ≠ 1/2`. So the strip clause
and the zero line are one proposition. All three faces route through this. -/

/-- The report's "local rule": every nontrivial zero of `ζ(s) L(s, χ_{−20})` lies on `Re = 1/2`.
Distinct from `dirichletZeroLine`, which is the zero line of the `L`-factor alone. -/
def ZeroLine : Prop := ∀ s : ℂ, NontrivialZero s → s.re = 1 / 2

/-- The strip clause is exactly "every nontrivial zero on the line". Fully proved. -/
theorem stripZeroFree_iff_zeroLine : stripZeroFree ↔ ZeroLine := by
  constructor
  · intro hfree s hs
    exact zeroLine_of_stripZeroFree hfree hs
  · intro h s hlo hhi hz
    have hs1 : s ≠ 1 := by
      rintro rfl
      rw [one_re] at hhi
      exact absurd hhi (lt_irrefl 1)
    have htriv : ¬ ∃ n : ℕ, s = -((n : ℂ) + 1) := by
      rintro ⟨n, rfl⟩
      simp only [neg_re, add_re, natCast_re, one_re] at hlo
      linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have hre : s.re = 1 / 2 := h s ⟨hz, hs1, htriv⟩
    linarith

/-! ## Route 1 — the positivity seam (Li / Bombieri–Lagarias)

Report §3.1 / §6.1. The Keiper–Li coefficients `λ_n^K` of the completed `ξ_K = ξ · Λ(χ_{−20})` are
carried as an abstract real sequence `lam : ℕ → ℝ` (Mathlib has no Keiper–Li coefficients; by the
zero-sum representation `λ_n = ∑_ρ (1 − (1 − 1/ρ)^n)` their positivity is exactly "the turn-back
angle always closes"). The scout computed `λ_n^K > 0` for `n = 1..8` (report §7); that is the
empirical down-payment, not a proof, and nothing empirical enters the Lean. -/

/-- Route 1, the positivity face: every Keiper–Li coefficient `λ_n^K` is non-negative. -/
def LiPositive (lam : ℕ → ℝ) : Prop := ∀ n : ℕ, 1 ≤ n → 0 ≤ lam n

/-- The Li / Bombieri–Lagarias criterion for `ζ_K`, carried as a named cited hypothesis (Li 1997;
Bombieri–Lagarias 1999) — NEVER proved, NEVER an axiom, exactly the `LIClassEqualFreq` discipline:
positivity of all Keiper–Li coefficients is equivalent to RH for `K`. The deep content (the Hadamard
product / explicit-formula link between the `λ_n` and the zeros, for the completed Dedekind `ζ_K`) is
the open prior art and is not in Mathlib. -/
def LiCriterion (lam : ℕ → ℝ) : Prop :=
  LiPositive lam ↔ RiemannHypothesis ∧ dirichletZeroLine

/-- **Route 1 (positivity) adapter.** Given the Li / Bombieri–Lagarias criterion, Li-positivity is
exactly `stripZeroFree` — the one lock. Proved by composing the carried criterion with
`stripZeroFree_iff`; the record is that this positivity face is RH-strength, not lighter. -/
theorem liPositive_iff_stripZeroFree {lam : ℕ → ℝ} (hBL : LiCriterion lam) :
    LiPositive lam ↔ stripZeroFree :=
  hBL.trans stripZeroFree_iff.symm

/-- Hence Li-positivity forces every nontrivial zero onto the line. -/
theorem zeroLine_of_liPositive {lam : ℕ → ℝ} (hBL : LiCriterion lam) (h : LiPositive lam) :
    ZeroLine :=
  stripZeroFree_iff_zeroLine.1 ((liPositive_iff_stripZeroFree hBL).1 h)

/-! ## Route 1 — the operator seam (Hilbert–Pólya / de Branges)

Report §3 / §6.2. The open object is a self-adjoint operator (or a de Branges / Hermite–Biehler
structure function with the phase-always-increasing property) whose spectrum is the nontrivial
zeros. Its construction is the open problem and is never built here. What is genuinely PROVED is the
mechanism it would supply: the spectrum of a symmetric operator is real, and a real spectral
parameter `γ` puts `1/2 + γ·i` on the line. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The Hilbert–Pólya correspondence for an operator `T` on a complex inner-product space `E`: every
nontrivial zero `s` is `1/2 + γ·i` where `γ` is an eigenvalue of `T` (a complex spectral parameter,
**not assumed real** — its reality is what self-adjointness delivers). The existence of `T` together
with this correspondence is the Hilbert–Pólya / de Branges hypothesis; it is carried, never built. -/
def HilbertPolyaCorrespondence (T : E →ₗ[ℂ] E) : Prop :=
  ∀ s : ℂ, NontrivialZero s →
    ∃ (γ : ℂ) (v : E), v ≠ 0 ∧ T v = γ • v ∧ s = (1 / 2 : ℂ) + γ * Complex.I

/-- **Route 1 (operator) — the genuine content, PROVED.** If `T` is symmetric (self-adjoint) and
realizes the zeros through the correspondence, every nontrivial zero lies on the line: a symmetric
operator has real eigenvalues (`conj_eigenvalue_eq_self`), so `γ` is real and `(1/2 + γ·i).re = 1/2`.
The missing object is the pair `(T, correspondence)`, the open Hilbert–Pólya problem. -/
theorem zeroLine_of_hilbertPolya {T : E →ₗ[ℂ] E} (hT : T.IsSymmetric)
    (hcorr : HilbertPolyaCorrespondence T) : ZeroLine := by
  intro s hs
  obtain ⟨γ, v, hv, hTv, hs_eq⟩ := hcorr s hs
  have hev : Module.End.HasEigenvalue T γ :=
    Module.End.hasEigenvalue_of_hasEigenvector
      (⟨Module.End.mem_eigenspace_iff.2 hTv, hv⟩ : Module.End.HasEigenvector T γ v)
  have him : γ.im = 0 := Complex.conj_eq_iff_im.1 (hT.conj_eigenvalue_eq_self hev)
  have hhalf : (1 / 2 : ℂ).re = 1 / 2 := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring]
    exact Complex.ofReal_re _
  rw [hs_eq, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, him, hhalf]
  ring

/-- **Route 1 (operator) adapter.** A symmetric Hilbert–Pólya model implies `stripZeroFree`. An
implication, not an equivalence (the operator is one sufficient object; the report records the route
as a program with one hard object, report §6.2). -/
theorem stripZeroFree_of_hilbertPolya {T : E →ₗ[ℂ] E} (hT : T.IsSymmetric)
    (hcorr : HilbertPolyaCorrespondence T) : stripZeroFree :=
  stripZeroFree_iff_zeroLine.2 (zeroLine_of_hilbertPolya hT hcorr)

/-! ## Route 2 — the counting seam (method of carrying)

Report §4 / §6.3. Global invariant: the zero-count `N(T)` (Riemann–von Mangoldt, from the functional
equation's archimedean phase). Local rule: each counted zero on `Re = 1/2`. RH ⟺ `N₀(T) = N(T)` for
all `T`. The functional-equation symmetry hands over `N(T)` but is **blind** to on/off-line: off-line
zeros come in line-symmetric pairs that wind the contour exactly as on-line pairs do, so the global
invariant cannot discriminate. That blindness is recorded in prose; it is why counting is the lock,
not a lever.

Discreteness of the zeros (finitely many up to each height) is a genuine theorem — zeros of a nonzero
holomorphic function are isolated — not available in Mathlib for this product. It is carried as the
named structure `ZeroCount`, the KL16 `SplittingData` pattern: never a `sorry`, never an axiom. Given
it, the counting adapter is fully PROVED. -/

/-- The carried discreteness frontier: a family of finite sets of the nontrivial zeros, `zeros T`
being exactly the nontrivial zeros of height `|Im s| ≤ T`. The existence of these `Finset`s is the
discreteness/finiteness theorem, carried here, not built. -/
structure ZeroCount where
  /-- The nontrivial zeros of height `≤ T`, as a finite set. -/
  zeros : ℝ → Finset ℂ
  /-- `zeros T` is exactly the nontrivial zeros `s` with `|Im s| ≤ T`. -/
  mem_zeros : ∀ (T : ℝ) (s : ℂ), s ∈ zeros T ↔ (NontrivialZero s ∧ |s.im| ≤ T)

namespace ZeroCount

variable (zc : ZeroCount)

/-- `N(T)` — the global invariant: the total count of nontrivial zeros of height `≤ T`. The
Riemann–von Mangoldt law would compute this from the functional equation; that symmetry is blind to
whether a counted zero is on the line (report §4). -/
def N (T : ℝ) : ℕ := (zc.zeros T).card

/-- `N₀(T)` — the local count: nontrivial zeros of height `≤ T` that lie on `Re = 1/2`. The on-line
zeros the sign changes of the Hardy `Z`-function locate (report §4). -/
def N₀ (T : ℝ) : ℕ := ((zc.zeros T).filter (fun s => s.re = 1 / 2)).card

/-- Route 2, the counting criterion (method of carrying): the on-line count equals the total count
at every height, `N₀(T) = N(T)` for all `T`. This is the named `Prop` the adapter puts at the lock. -/
def CountsAgree : Prop := ∀ T : ℝ, zc.N₀ T = zc.N T

/-- The local count never exceeds the global one: the on-line zeros are a subset. This `≤` is the
honest content of "positive proportion on the line"; pushing it to equality for all `T` is the lock. -/
theorem N₀_le_N (T : ℝ) : zc.N₀ T ≤ zc.N T :=
  Finset.card_filter_le _ _

end ZeroCount

/-- The on-line count equals the total count at every height iff every nontrivial zero is on the
line. Fully proved from the carried discreteness. -/
theorem countsAgree_iff_zeroLine (zc : ZeroCount) : zc.CountsAgree ↔ ZeroLine := by
  show (∀ T, zc.N₀ T = zc.N T) ↔ ZeroLine
  constructor
  · intro h s hs
    by_contra hne
    set T : ℝ := |s.im| with hT
    have hmem : s ∈ zc.zeros T := (zc.mem_zeros T s).2 ⟨hs, le_refl _⟩
    have hsub : (zc.zeros T).filter (fun w => w.re = 1 / 2) ⊂ zc.zeros T :=
      Finset.filter_ssubset.2 ⟨s, hmem, hne⟩
    have hlt : zc.N₀ T < zc.N T := Finset.card_lt_card hsub
    rw [h T] at hlt
    exact lt_irrefl _ hlt
  · intro h T
    apply congrArg Finset.card
    apply Finset.filter_true_of_mem
    intro s hsmem
    exact h s ((zc.mem_zeros T s).1 hsmem).1

/-- **Route 2 (counting) adapter.** `CountsAgree` — `N₀(T) = N(T)` for all `T` — is exactly
`stripZeroFree`, the one lock. Fully proved (given the carried discreteness) by composing with the
backbone adapter. -/
theorem countsAgree_iff_stripZeroFree (zc : ZeroCount) : zc.CountsAgree ↔ stripZeroFree :=
  (countsAgree_iff_zeroLine zc).trans stripZeroFree_iff_zeroLine.symm

/-- The counting face is RH-strength: `CountsAgree ↔ RiemannHypothesis ∧ dirichletZeroLine`. -/
theorem countsAgree_iff_RH (zc : ZeroCount) :
    zc.CountsAgree ↔ RiemannHypothesis ∧ dirichletZeroLine :=
  (countsAgree_iff_stripZeroFree zc).trans stripZeroFree_iff

end ExistenceSystem.Summit

end

end
