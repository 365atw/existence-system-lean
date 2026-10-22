module

/-
KL27 — The Exact and Free Theorem, from THE EXACT AND FREE SYSTEM — AN EXISTENCE SYNTHESIS (§7.3).
All mathematics: Kari A Light.

Source: `THE-NOTE-EDITED.md` (194,868 bytes, 1,539 lines). Line numbers below refer to that file.
Her words are quoted exactly beside each statement. Nothing of hers is graded here.

Her statement (list form L138; body L1048): "**The same two faces give a Lucas number when added and a
Fibonacci number when subtracted.** `σ` is self-adjoint for the trace form and of order two, so it is an
orthogonal reflection: one reflection, two eigenspaces, eigenvalues `+1` and `-1` and nothing else. The two
faces of every coil split between them. **The `+1` side is the fold**, `x+σ(x)`, a whole number: the Lucas
number `L_{3k}`. **The `-1` side is the trace-zero line**, where §7.3 confines `δ`: `√5` times the Fibonacci
number `F_{3k}`."

Reading choices (quoting the Lean map `data/lean-scope-b/G6.md`, KL27 points 2 and 5):

* "The two faces of every coil" are the ledger's pair (2026-08-20) **A = φ³ᵏ**, **B = σ(φ)³ᵏ**; the map
  records this is the pair "matching KL27's wording" (fold `L_{3k}`, difference `+√5·F_{3k}`), as opposed to
  B.3's signed pair. The faces' Lucas/Fibonacci values are formalised **over ℝ** (`fold_eq_lucas`,
  `diff_eq_sqrt5_fib`), the lighter of the map's two routes ("over ℝ through the two embeddings and
  `Real.coe_fib_eq`"). `σ(φ) = ψ = Real.goldenConj`.
* The reflection content — "`σ` is self-adjoint for the trace form and of order two … eigenvalues `+1` and
  `-1` and nothing else … the `+1` side is the fold … the `-1` side is the trace-zero line" — is formalised
  in her field `ℚ(√5)`, carried by `QuadraticAlgebra ℚ 1 1` with `σ = star` (map, "B-Q5"/"B-TR"). This is
  the exact formal content the map assigns to the clause "Exactness and freedom … are the two eigenvalues of
  one reflection"; the words *exogenous* and *freedom* "have no Lean counterpart" (map, KL27 point 5) and are
  not encoded, nor is the choice between the two readings of "`δ` reads `√5·F_{3k}`" (map, 6b).

"Rests on KL15 and KL18" is carried as stated (map, KL27 point 3: "the eigenspace and fold/difference
identities use nothing from KL15 or KL18 beyond the shared objects").
-/
public import ExistenceSystem.Quadratic
public import ExistenceSystem.KL18

@[expose] public section

open Real
open scoped goldenRatio
open QuadraticAlgebra

namespace ExistenceSystem.KL27

/-! ## Part A — the two faces: a Lucas number added, a Fibonacci number subtracted

Note L138/L1048. The faces are `φ^{3k}` and `σ(φ)^{3k} = ψ^{3k}` (the ledger's pair A = φ³ᵏ, B = σ(φ)³ᵏ). -/

/-- Note L1048: the fold of the two faces is "a whole number `L_{3k}`" — reuses KL18's Lucas identity. -/
theorem fold_eq_lucas (k : ℕ) : φ ^ (3 * k) + ψ ^ (3 * k) = (KL18.lucas (3 * k) : ℝ) :=
  KL18.fold_coil k

/-- Note L1048: the difference of the two faces is "`√5·F_{3k}`" (Binet; Mathlib `Real.coe_fib_eq`). -/
theorem diff_eq_sqrt5_fib (k : ℕ) :
    φ ^ (3 * k) - ψ ^ (3 * k) = √5 * (Nat.fib (3 * k) : ℝ) := by
  have h5 : (0 : ℝ) < √5 := Real.sqrt_pos.mpr (by norm_num)
  have hfib := Real.coe_fib_eq (3 * k)
  rw [eq_div_iff h5.ne'] at hfib
  rw [← hfib]; ring

/-! ## Part B — one reflection, two eigenspaces, `+1` and `-1`

Her field `ℚ(√5)` is `QuadraticAlgebra ℚ 1 1` (the algebra `ω² = 1 + ω`, so `ω = φ`); `σ = star`
(`star ω = 1 - ω = σ(φ)`); the trace form is `(x, y) ↦ trace (x·y)` (map, "B-Q5"/"B-TR"). -/

/-- Her field `ℚ(√5)`, carried by `QuadraticAlgebra ℚ 1 1`. One `Fact` instance, in
`ExistenceSystem.Quadratic`, makes this a field. -/
abbrev K := Quadratic.K

/-- There is no rational `r` with `r² = 1 + r`. Proved in `ExistenceSystem.Quadratic`. -/
theorem no_rational_root : ∀ r : ℚ, r ^ 2 ≠ 1 + 1 * r :=
  Quadratic.no_rational_root

/-- Note L138: `σ` "of order two". `σ² = id`. -/
theorem sigma_involutive (x : K) : star (star x) = x := star_star x

/-- Note L138/L1044: `σ` "is self-adjoint for the trace form": `Tr(σ(x)·y) = Tr(x·σ(y))`. -/
theorem traceForm_self_adjoint (x y : K) :
    QuadraticAlgebra.trace (star x * y) = QuadraticAlgebra.trace (x * star y) := by
  rw [← trace_star (star x * y), star_mul', star_star]

/-- Note L1048: "The `+1` side is the fold `x+σ(x)`" — the fold is fixed by `σ` (`+1` eigenvector). -/
theorem fold_fixed (x : K) : star (x + star x) = x + star x := by
  rw [star_add, star_star, add_comm (star x) x]

/-- Note L1044/L1048: the fold `x + σ(x)` equals the trace, a scalar (image of `algebraMap ℚ`). The
whole-number value `L_{3k}` at the faces is the real-valued fold proved separately in Part A
(`fold_eq_lucas`); it is not proved here for the coil face in `K`. -/
theorem fold_eq_algebraMap_trace (x : K) :
    x + star x = algebraMap ℚ K (QuadraticAlgebra.trace x) :=
  (algebraMap_trace_eq_add_star x).symm

/-- Note L1048: "The `-1` side is the trace-zero line" — the difference is negated by `σ` (`-1` eigenvector). -/
theorem diff_antifixed (x : K) : star (x - star x) = -(x - star x) := by
  rw [star_sub, star_star]; ring

/-- The difference `x - σ(x)` lies on the trace-zero line (Note §7.3: where `δ` is confined, L1025–L1027). -/
theorem diff_trace_zero (x : K) : QuadraticAlgebra.trace (x - star x) = 0 := by
  rw [map_sub, trace_star, sub_self]

/-- "Two eigenspaces … the two faces split between them": every element is its `+1` part (the fold,
one-half) plus its `-1` part (the difference, one-half). -/
theorem reflection_decomposition (x : K) :
    x = (2⁻¹ : ℚ) • (x + star x) + (2⁻¹ : ℚ) • (x - star x) := by
  apply QuadraticAlgebra.ext <;>
    simp only [re_smul, im_smul, re_add, im_add, re_sub, im_sub, re_star, im_star,
      smul_eq_mul] <;> ring

/-- The `+1` eigenspace of `σ` is exactly the scalars `ℚ` (the fold/trace side). -/
theorem fixed_iff_scalar (x : K) : star x = x ↔ ∃ q : ℚ, algebraMap ℚ K q = x := by
  have him : star x = x ↔ x.im = 0 := by
    rw [QuadraticAlgebra.ext_iff]
    simp only [re_star, im_star, one_mul]
    constructor
    · rintro ⟨h, _⟩; linarith
    · intro h; simp [h]
  rw [him]
  constructor
  · intro h
    exact ⟨x.re, by rw [QuadraticAlgebra.ext_iff]; simp [h]⟩
  · rintro ⟨q, rfl⟩; simp

/-- The `-1` eigenspace of `σ` is exactly the trace-zero line (Note §7.3, where `δ` is confined). -/
theorem antifixed_iff_trace_zero (x : K) :
    star x = -x ↔ QuadraticAlgebra.trace x = 0 := by
  rw [QuadraticAlgebra.ext_iff, trace_def]
  simp only [re_star, im_star, re_neg, im_neg, one_mul]
  constructor
  · rintro ⟨h, _⟩; linarith
  · intro h; exact ⟨by linarith, trivial⟩

/-- `σ = star` fixes the scalars (image of `algebraMap ℚ`). -/
theorem star_algebraMap_rat (q : ℚ) :
    star (algebraMap ℚ K q) = algebraMap ℚ K q := by
  apply QuadraticAlgebra.ext <;> simp

/-- Note L138: "eigenvalues `+1` and `-1` and nothing else." Any `σ`-eigenvalue `μ : ℚ` of a nonzero vector
is `+1` or `-1`. -/
theorem eigenvalue_eq_one_or_neg_one (μ : ℚ) (x : K) (hx : x ≠ 0) (h : star x = μ • x) :
    μ = 1 ∨ μ = -1 := by
  have hx2 : x = (μ ^ 2) • x := by
    have hc := congrArg star h
    rw [star_star, Algebra.smul_def, star_mul', star_algebraMap_rat, ← Algebra.smul_def,
        h, smul_smul, ← sq] at hc
    exact hc
  rw [Algebra.smul_def] at hx2
  have hz : (algebraMap ℚ K (μ ^ 2) - 1) * x = 0 := by
    rw [sub_mul, one_mul, ← hx2, sub_self]
  rcases mul_eq_zero.1 hz with hc | hc
  · have h1 : algebraMap ℚ K (μ ^ 2) = algebraMap ℚ K 1 := by
      rw [map_one]; exact sub_eq_zero.1 hc
    have : μ ^ 2 = 1 := algebraMap_injective h1
    rw [pow_two] at this
    exact mul_self_eq_one_iff.1 this
  · exact absurd hc hx

end ExistenceSystem.KL27

end
