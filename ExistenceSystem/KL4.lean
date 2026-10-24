module

/-
KL4 — The never-closing identification (§4.7), from THE EXACT AND FREE SYSTEM —
AN EXISTENCE SYNTHESIS. All mathematics: Kari A Light.

Source: `THE-NOTE-EDITED.md` (194,868 bytes, 1,539 lines). Line numbers below refer to that file.
Her words are quoted exactly beside each statement. Nothing of hers is graded here.

Note L92 (front-matter list form), verbatim:
"**KL4 — The never-closing identification.** *Irrational-never-lands*, *helix-never-closes* and
*five-fold-never-tiles* are **one** structure, not three: they are the single statement that the
icosahedral star admits no integer relation. *Proved as one statement in §4.7.*"

Note L683 (lead-in, §4.7), verbatim:
"The proof used irrationality exactly once, and everything turns on it. Lemma 1 says the star admits
no integer relation. That is *the same* statement as the crystallographic restriction forbidding
five-fold periodic order (§2.2), which is *the same* statement as 2cos(2π/5)=1/φ being irrational."

Note L685 (Theorem, the joint label KL4, KL6), verbatim:
"**Theorem (The never-closing identification, the No-Pinning Theorem, KL4, KL6).** Physical-space
closure lifts to six-dimensional closure only because the star is rationally independent. That
independence is exactly what makes five-fold symmetry non-crystallographic, and exactly what makes
the phason phase cancel out of every term of J. **The never-closing and the zero cost are one
theorem.**"

Note L687, verbatim:
"The irrational that never lands on a whole number, the helix that never closes, and the five-fold
symmetry that never tiles are not three facts with a family resemblance. They are one fact stated
three times — and the free energy that cannot see the phason is the fourth face of it."

Note L689 (the mechanism stated precisely), verbatim:
"**The mechanism stated precisely: two arithmetic facts, each doing its own job.** *Irrationality*
supplies the **injectivity**. It is the hypothesis of Lemma 1 and it is what empties the kernel: the
star admits no integer relation, π_∥ has no kernel on ℒ, and no closure on this rung can be a false
one. *Quadratic algebraicity* supplies the **space in which the cancellation happens at all**. φ is a
totally real quadratic integer, and the second embedding of ℤ[φ] — the Galois conjugate σ(φ)=1−φ —
is exactly what produces Q_i^⊥, hence E_⊥, hence the lift to ℤ⁶ … Lemma 1's proof uses both in one
line and in this order: σ carries ∑ n_iQ_i=0 to ∑ n_iQ_i^⊥=0 — that is the algebraicity — and only
then does the isomorphism π_∥⊕π_⊥ force n=0."

Note L691 (the discriminator), verbatim:
"**The discriminator.** Replace φ by a transcendental winding. Every part of the never-closing
survives untouched: the ratio still lands on no whole number, the helix still never closes, and no
periodic lattice admits the symmetry. The lift dies. There is no Galois conjugate, hence no E_⊥, no
ℤ⁶ parent, no cut-and-project, no inflation — and therefore no six-dimensional closure for a
perpendicular phase to cancel into. Never-closing is shared by *every* irrational; the Ascent is the
property of being algebraic of degree two. **The phason is exactly free because φ is irrational**."

Reading choices and scope (map `data/lean-scope-b/G2.md`, KL4, §4.7, l.348–406; report.md layer 5):

* This is a **leaf**: the two arithmetic facts of L689 are each already a merged theorem, imported
  from `main` and **reused, not rebuilt** (leaves-first).
  - **Arithmetic fact 1 — "irrationality supplies the injectivity."** "The star admits no integer
    relation, π_∥ has no kernel on ℒ" is `KL20.no_integer_relation` (engine: `embedPhi_injective`,
    φ irrational). The never-closing itself — "the ratio lands on no whole number" (L691) — is here
    the abstract `NeverCloses`/`neverCloses_iff_irrational`: a real winding admits no nontrivial
    integer relation iff it is irrational. L683's "2cos(2π/5)=1/φ being irrational" is the concrete
    face (`two_cos_eq_inv_goldenRatio`, `irrational_two_cos_two_pi_div_five`).
  - **Arithmetic fact 2 — "quadratic algebraicity supplies the space."** The Galois conjugate
    σ(φ)=1−φ that "produces Q_i^⊥, hence E_⊥, hence the lift to ℤ⁶" is `embedPsi` in `Quadratic`;
    the σ-transfer step is `KL20.sigma_transfer`. Here the *lift as such* is `AdmitsLift`: a winding
    is a root of a monic integer quadratic together with a distinct second root — its conjugate.
  - **The zero-cost half** — "the phason phase cancels out of every term of J" — is `KL6.no_pinning`.

* **The discriminator (L691) is the genuinely new content.** `discriminator` exhibits a transcendental
  winding (a Liouville number) that never-closes yet admits no lift: "Never-closing is shared by
  *every* irrational; the Ascent is the property of being algebraic of degree two." `goldenRatio`
  sits on both sides (`goldenRatio_neverCloses_and_admitsLift`), which is why "the never-closing and
  the zero cost are one theorem" *at φ* — `never_closing_and_zero_cost` delivers both halves (KL20,
  KL6) from the one engine for every admissible term.

Not formalisable as written (map G2.md §5, her own markings quoted, no verdict on her work):
* "**one** structure, not three", "*the same* statement", "one fact stated three times", "the fourth
  face of it", "**The never-closing and the zero cost are one theorem.**" (L92, L685, L687) — these
  are identifications *at the level of reading*. In Lean every proved proposition is logically
  equivalent to every other, so "the same statement" carries no formal content beyond the separate
  implications; what is stated here is each implication with its hypothesis exposed. A fact about
  formal logic, not about her text. `never_closing_and_zero_cost` therefore packages the two halves
  as a conjunction riding the one engine, not as a fabricated logical identity.
* *helix-never-closes* (L92, L687, L691) — no helix is defined in §4.7; a formal statement would need
  the helix defined. Carried as prose.
* **Borrowed, hers to cite, not claimed (G1 rows U10, U11; G2 §5).** The crystallographic restriction
  — "[9] (A8), *Used in §2.2 and §4.7*" — would need A8 (finite-order integer matrices, cyclotomic
  degree), **not** Mathlib's `IsCrystallographic`; out of scope here (hundreds of lines, report.md).
  Hurwitz's approximation theorem — A5, "*Used in §1.5*" — "φ's extremal irrationality" (L687); also
  borrowed. Neither is rebuilt; the link to them is recorded as prose.
* The body label carries two numbers (KL4, KL6); KL6's own body theorem is at L661. Recorded as
  layout.
-/
public import Mathlib
public import ExistenceSystem.KL20
public import ExistenceSystem.KL6

@[expose] public section

open Real Polynomial

open scoped goldenRatio

namespace ExistenceSystem.KL4

open ExistenceSystem.Icosahedral ExistenceSystem.Quadratic

/-! ## Arithmetic fact 1: the never-closing is irrationality (Note L689, L691)

"*Irrationality* supplies the **injectivity** … the ratio lands on no whole number" (L689, L691). A
real winding `x` **never closes** when it admits no nontrivial integer relation `a + b x = 0`. -/

/-- Note L691: "the ratio still lands on no whole number." A real winding `x` **never closes** if the
only integer relation `a + b x = 0` it satisfies is the trivial one. -/
def NeverCloses (x : ℝ) : Prop := ∀ a b : ℤ, (a : ℝ) + b * x = 0 → a = 0 ∧ b = 0

/-- **Note L691: "Never-closing is shared by *every* irrational."** A winding never closes iff it is
irrational — the single arithmetic fact behind *irrational-never-lands*. -/
theorem neverCloses_iff_irrational (x : ℝ) : NeverCloses x ↔ Irrational x := by
  constructor
  · intro h hmem
    obtain ⟨q, hq⟩ := hmem
    have hxval : ((q.den : ℤ) : ℝ) * x = ((q.num : ℤ) : ℝ) := by
      rw [← hq, Rat.cast_def]
      have hdR : (q.den : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Rat.den_ne_zero q)
      push_cast
      field_simp
    have hrel : ((-q.num : ℤ) : ℝ) + ((q.den : ℤ) : ℝ) * x = 0 := by
      rw [hxval]; push_cast; ring
    have hb0 := (h (-q.num) (q.den : ℤ) hrel).2
    exact (Rat.den_ne_zero q) (by exact_mod_cast hb0)
  · intro hirr a b hab
    rcases eq_or_ne b 0 with hb | hb
    · subst hb
      simp only [Int.cast_zero, zero_mul, add_zero] at hab
      exact ⟨by exact_mod_cast hab, rfl⟩
    · exfalso
      have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hb
      apply hirr
      refine ⟨(-a : ℚ) / (b : ℚ), ?_⟩
      push_cast
      rw [div_eq_iff hbR]
      linear_combination -hab

/-- The golden ratio never closes (it is irrational). The never-closing at the discriminator value. -/
theorem goldenRatio_neverCloses : NeverCloses φ :=
  (neverCloses_iff_irrational φ).mpr goldenRatio_irrational

/-! ## The concrete face: 2cos(2π/5) = 1/φ, irrational (Note L683) -/

/-- **Note L683: "2cos(2π/5)=1/φ".** The five-fold cosine equals the inverse golden ratio — the same
value whose irrationality is "*the same* statement" as the star admitting no integer relation. -/
theorem two_cos_eq_inv_goldenRatio : 2 * Real.cos (2 * π / 5) = φ⁻¹ := by
  have hinv : φ⁻¹ = φ - 1 := by rw [inv_goldenRatio, ← one_sub_goldenConj]; ring
  rw [hinv, show (2 * π / 5 : ℝ) = 2 * (π / 5) by ring, Real.cos_two_mul, Real.cos_pi_div_five]
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hgold : φ = (1 + Real.sqrt 5) / 2 := rfl
  rw [hgold]
  linear_combination (1 / 4 : ℝ) * h5

/-- **Note L683, the irrationality.** `2cos(2π/5)` is irrational: *irrational-never-lands* at the
geometric value. -/
theorem irrational_two_cos_two_pi_div_five : Irrational (2 * Real.cos (2 * π / 5)) := by
  rw [two_cos_eq_inv_goldenRatio, inv_goldenRatio]
  exact goldenConj_irrational.neg

/-- **Note L683, as never-closing.** The five-fold cosine never lands on a whole number. -/
theorem two_cos_neverCloses : NeverCloses (2 * Real.cos (2 * π / 5)) :=
  (neverCloses_iff_irrational _).mpr irrational_two_cos_two_pi_div_five

/-! ## Arithmetic fact 2: the lift needs a Galois conjugate (Note L689, L691)

"*Quadratic algebraicity* supplies the **space** … the Galois conjugate σ(φ)=1−φ is exactly what
produces Q_i^⊥, hence E_⊥, hence the lift to ℤ⁶" (L689). "The Ascent is the property of being
algebraic of degree two" (L691). A winding **admits the lift** when it is a root of a monic integer
quadratic together with a distinct second root — its conjugate (`embedPsi` in `Quadratic`). -/

/-- Note L689, L691: the **Ascent / the lift**. A winding `x` *admits the lift* when it and a distinct
`y` are the two roots of one monic integer quadratic `t² = b t + c` — `y` the Galois conjugate that
the second embedding of `ℤ[φ]` realises as `E_⊥`. -/
def AdmitsLift (x : ℝ) : Prop :=
  ∃ (b c : ℤ) (y : ℝ), y ≠ x ∧ x ^ 2 = (b : ℝ) * x + (c : ℝ) ∧ y ^ 2 = (b : ℝ) * y + (c : ℝ)

/-- **Note L689: "σ(φ)=1−φ".** The golden ratio admits the lift: `φ` and its Galois conjugate
`ψ = 1 − φ` are the two roots of the monic integer quadratic `t² = t + 1`. -/
theorem goldenRatio_admitsLift : AdmitsLift φ := by
  refine ⟨1, 1, ψ, (goldenConj_neg.trans goldenRatio_pos).ne, ?_, ?_⟩
  · push_cast; rw [goldenRatio_sq]; ring
  · push_cast; rw [goldenConj_sq]; ring

/-- **Note L691: "The lift dies. There is no Galois conjugate."** A transcendental winding admits no
lift: it is a root of no integer quadratic at all, so it has no conjugate. -/
theorem not_admitsLift_of_transcendental {x : ℝ} (hx : Transcendental ℤ x) : ¬ AdmitsLift x := by
  rintro ⟨b, c, _, -, hx2, -⟩
  apply hx
  refine ⟨X ^ 2 - (C b * X + C c), ?_, ?_⟩
  · exact (monic_X_pow_sub (lt_of_le_of_lt degree_linear_le (by decide))).ne_zero
  · have hae : (aeval x) (X ^ 2 - (C b * X + C c)) = x ^ 2 - ((b : ℝ) * x + (c : ℝ)) := by
      simp only [map_sub, map_add, map_mul, map_pow, aeval_X, map_intCast, eq_intCast]
    rw [hae, hx2]; ring

/-! ## The discriminator (Note L691) -/

/-- **Note L691, "The discriminator."** A transcendental winding `never-closes` (shared by *every*
irrational) yet admits **no lift** (the Ascent needs algebraic degree two): replacing φ by a
transcendental winding keeps the never-closing but kills the lift. A Liouville number witnesses it. -/
theorem discriminator : ∃ x : ℝ, NeverCloses x ∧ ¬ AdmitsLift x := by
  have hL : Liouville (liouvilleNumber 2) := liouville_liouvilleNumber (le_refl 2)
  exact ⟨liouvilleNumber 2,
    (neverCloses_iff_irrational _).mpr hL.irrational,
    not_admitsLift_of_transcendental hL.transcendental⟩

/-- **Note L689–L691, at the discriminator value.** The golden ratio sits on *both* sides: it never
closes (irrational) **and** admits the lift (quadratic integer). That both halves hold at φ is why
the never-closing and the zero cost are one theorem at φ. -/
theorem goldenRatio_neverCloses_and_admitsLift : NeverCloses φ ∧ AdmitsLift φ :=
  ⟨goldenRatio_neverCloses, goldenRatio_admitsLift⟩

/-! ## KL4 — the never-closing and the zero cost are one theorem (Note L685, the joint label KL4, KL6)

Her "*the same* statement" / "one theorem" (L92, L685, L687) carries no formal content beyond the
separate implications (G2.md §5); so the two halves are packaged as a conjunction, both delivered for
every admissible term from the one engine — KL20 (no integer relation) and KL6 (phason flatness). -/

/-- **KL4, KL6 — the never-closing identification (Note L685).** For every admissible term
(reciprocal indices closing in ℤ⁶, `∑ c = 0`), from the one engine — φ irrational, quadratically
algebraic — follow together:

* **the never-closing** — the star admits no integer relation (`KL20.no_integer_relation`:
  π_∥ has no kernel on ℒ); and
* **the zero cost** — the term is strictly phason-flat, `J(w+w₀)=J(w)` (`KL6.no_pinning`).

"The never-closing and the zero cost are one theorem." -/
theorem never_closing_and_zero_cost {M : ℕ} (c : Fin M → (Fin 6 → ℤ)) (h : ∑ m, c m = 0) (A : ℂ) :
    (∀ n : Fin 6 → ℤ, piParallel (fun i => (n i : ℝ)) = 0 → n = 0)
      ∧ (∀ w₀, KL6.phasonTerm c A w₀ = A) :=
  ⟨fun n hn => KL20.no_integer_relation n hn, (KL6.no_pinning c h A).1⟩

end ExistenceSystem.KL4

end
