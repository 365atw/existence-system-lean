# existence-system-lean

Lean 4 + Mathlib formalisation of results from THE EXACT AND FREE SYSTEM — AN EXISTENCE SYNTHESIS.

All mathematics: Kari A Light.

## KL1 — the per-dimension uniqueness result (`ExistenceSystem/KL1.lean`)

For every integer `n ≥ 2`, `f(x) = x^n - x - 1` has exactly one positive real root, in `(1, 2)`.
Proved with no `sorry`, `admit`, or new axioms:

- `existsUnique_pos_root`, `r_mem_Ioo`: exactly one positive root, and `rₙ ∈ (1, 2)` (Descartes' upper bound `Polynomial.roots_countP_pos_le_signVariations`; existence by `intermediate_value_Ioo`)
- `r_pow`, `r_succ_lt`, `one_lt_r`, `tendsto_r`: `rₙ^n = rₙ + 1`, `rₙ₊₁ < rₙ`, bounded below by 1, and `rₙ → 1`
- `planar_face`: `φ = r₂` (Mathlib's `Real.goldenRatio`)
- `spatial_face`, `rho_cube`, `rho_unique`: the plastic number `ρ = r₃`, the unique positive root of `x^3 = x + 1`

Her words are quoted beside each statement with line numbers from the Note.
Only that mathematics is formalised; the prose on Note L86 after the mathematical sentence, and the picture in §1.2, are not encoded.

## KL3 — the indifference theorem (`ExistenceSystem/KL3.lean`)

For `V(x) = -(r/2)x² + ¼x⁴` with `r > 0`, proved with no `sorry`, `admit`, or new axioms:

- `V_branches`: `V(√r) = V(-√r) = -r²/4`
- `critical_set`, `critical_set_ncard`: `V′` vanishes at exactly `0`, `√r`, `-√r`
- `minimizers_eq`, `minimizers_nontrivial`, `minimizers_ncard`: the minimizers of `V` over `ℝ` are exactly `√r` and `-√r`
- Supporting lemmas: `V_even` (`V(-x) = V(x)`), `hasDerivAt_V` / `deriv_V` (`V′(x) = -r x + x³`), `flow_eq_neg_deriv` (`r x - x³ = -V′(x)`)

Her words are quoted beside each statement with line numbers from the Note.
Only the mathematics of the potential is formalised; the prose concepts ("least-action drive", "provably indifferent", "exogenous", the cusp step of §3.3) are not encoded.

## KL13 — positivity of the residual (`ExistenceSystem/KL13.lean`)

The coil law `r_{k+1} = φ^{-3} r_k` is taken as given. For `r₀ > 0` and `φ^{-3} > 0`,
`residual_pos`: `r_k > 0` for every finite `k`. Her list-form clause "no configuration is bound at
any finite coil" names KL12's *configuration*, whose type the Note does not give; that type is not
encoded.

## KL14 — fixed point of the coil map (`ExistenceSystem/KL14.lean`)

On `[0, r₀]` with `0 ≤ r₀`, by Banach (`ContractingWith` with constant `φ^{-3}`):

- `fixedPoint_eq_zero`: `0` is the unique fixed point of `r ↦ φ^{-3} r`
- `ascent_tendsto_zero`: the residual sequence (the ascent) converges to `0`

Her clause "the bound configuration exists, is unique, and is the limit of the ascent" uses that
same undefined *configuration* type; only the fixed point and the limit are encoded.

## KL15 — the trace identity (`ExistenceSystem/KL15.lean`)

`piSwap_eq_m`: the §7.3 trace reading `π_swap(m·φ) = A' + B' = m` for every `δ`. The identity does
not depend on the coil. The "only determinate reading" past the trace, the units criterion, the
word *total*, and `E = mc²` are not encoded.

## KL18 — THE CONJUGATE LANDING THEOREM (`ExistenceSystem/KL18.lean`)

Her title (Note L120). Formalised over ℝ with Mathlib's `Real.goldenRatio` (`φ`) and `Real.goldenConj`
(`ψ = σ(φ) = 1 - φ`), proved with no `sorry`, `admit`, or new axioms:

- `lucas`: the Lucas numbers `L₀ = 2`, `L₁ = 1`, `Lₙ₊₂ = Lₙ₊₁ + Lₙ` (Mathlib lacks them; added with her
  line reference, per the map's "B-LF")
- `goldenRatio_pow_add_goldenConj_pow`: `φⁿ + σ(φ)ⁿ = Lₙ` — "the fold of the two conjugate faces is an exact
  whole number" (L1061), with the coil form `fold_coil` (`L_{3k}`) and base case `fold_coil_zero` (`= 2 = L₀`)
- `conj_neg`, `conj_abs_lt_one`, `goldenConj_pow_tendsto_zero`: the Pisot mechanism — `σ(φ) < 0`, `|σ(φ)| < 1`,
  so `σ(φ)ⁿ → 0` ("the alternating powers vanish", L1062)
- `face_par_irrational`, `face_perp_irrational`: for `k ≥ 1` neither face `φ^{3k}`, `σ(φ)^{3k}` is a whole
  number (L1062)
- `norm_pair` (`= (-1)ᵏ`), `norm_pair_abs` (`= 1`): "the norm of the pair is exactly 1 at every coil" (L1064)
- `residual_pos` (KL13), `residual_tendsto_zero`: the residual is strictly positive at every finite coil and
  converges to `0` ("none is arrived at", L983/L997)
- `piswap_trace`: part (b), `π_swap(m·φ) = A' + B' = m` for every `δ` (L1066/L1040, KL15)

**Reading choices** (quoting the Lean map `data/lean-scope-b/G6.md`, KL18 points 2, 5). The faces are defined
arithmetically as `φ^{3k}`, `σ(φ)^{3k}` ("Defined arithmetically, KL18's content touches no other group");
the identity is stated in the index `n`, the coil form is the case `n = 3k` (B.5 L1263). "The norm is exactly
1" has two formal readings the map names (`|N| = 1` or `N = (-1)ᵏ`); both are proved. Part (c) ("no coil is
distinguished … the identity case cannot be located at one") is prose at that point by the map's finding
(*distinguished* and *located at a coil* are undefined in the Note); its formal residue is that (a) and (b)
hold for **every** `k`, which is exactly how the theorems are quantified, and that alone is encoded. The limit
`r = 0` and KL12's *configuration* type (undefined in the Note) are not encoded.

## KL27 — The Exact and Free Theorem (`ExistenceSystem/KL27.lean`, §7.3)

Her title (Note L138). Two parts, proved with no `sorry`, `admit`, or new axioms:

**Part A — the two faces (over ℝ).** "The same two faces give a Lucas number when added and a Fibonacci number
when subtracted" (L138):

- `fold_eq_lucas`: `φ^{3k} + σ(φ)^{3k} = L_{3k}` (reuses KL18)
- `diff_eq_sqrt5_fib`: `φ^{3k} - σ(φ)^{3k} = √5·F_{3k}` (Binet; Mathlib `Real.coe_fib_eq`)

**Part B — one reflection, two eigenspaces (in her field `ℚ(√5) = QuadraticAlgebra ℚ 1 1`, `σ = star`).**
"`σ` is self-adjoint for the trace form and of order two, so it is an orthogonal reflection … eigenvalues `+1`
and `-1` and nothing else" (L138):

- `no_rational_root` / `factNoRoot`: `r² ≠ 1 + r` for every rational `r`, so `QuadraticAlgebra ℚ 1 1` is a
  field (her `ℚ(√5)`)
- `sigma_involutive` (`σ² = id`, order two), `traceForm_self_adjoint` (`Tr(σ(x)·y) = Tr(x·σ(y))`)
- `fold_fixed`, `fold_eq_algebraMap_trace`: the `+1` side is the fold `x + σ(x)`, which is the trace — a scalar
- `diff_antifixed`, `diff_trace_zero`: the `-1` side is `x - σ(x)`, on the trace-zero line (where §7.3 confines `δ`)
- `fixed_iff_scalar`, `antifixed_iff_trace_zero`: the `+1` eigenspace is exactly `ℚ`, the `-1` eigenspace
  exactly the trace-zero line
- `reflection_decomposition`: every element splits as its `+1` half (the fold) plus its `-1` half (the difference)
- `eigenvalue_eq_one_or_neg_one`: any `σ`-eigenvalue of a nonzero vector is `+1` or `-1` ("nothing else")

**Reading choices** (quoting the map, KL27 points 2, 5, and §6b). "The two faces of every coil" are the
ledger's pair `A = φ^{3k}`, `B = σ(φ)^{3k}`, "matching KL27's wording" (fold `L_{3k}`, difference `+√5·F_{3k}`)
rather than B.3's signed pair; the faces' values are taken over ℝ ("the lighter of the two routes"). The
reflection content is the exact formal content the map assigns to "Exactness and freedom … are the two
eigenvalues of one reflection"; the words *exogenous* and *freedom* "have no Lean counterpart" and are not
encoded, nor is the choice between the two readings of "`δ` reads `√5·F_{3k}`". "Rests on KL15 and KL18" is
carried as stated (the eigenspace and fold/difference identities use nothing from them beyond the shared
objects).

Build: `lake exe cache get && lake build` (Lean `v4.35.0-rc4`, Mathlib `v4.35.0-rc4`).
Axiom check: `lake env lean checks/PrintAxioms.lean` (standalone script, not part of the build target); every
audited theorem depends only on `propext`, `Classical.choice`, `Quot.sound` (the Lucas definition depends on
no axioms). Logs in `logs/`.

## TheThing — the arithmetic of `ℚ(√−5)` (`ExistenceSystem/TheThing.lean`)

Report `qsqrt5-rep-s1`: "ℚ(√−5) is the imaginary quadratic field of discriminant −20.
Its ring of integers is ℤ[√−5], with unit group {±1}. The ideal class group is cyclic of
order 2, generated by the class of 𝔭₂ = (2, 1+√−5)." Proved with no `sorry`, `admit`, or new axioms:

- `discr_eq_neg_twenty`, `isUnit_iff`: discriminant `−20`, units `{±1}`
- `classNumber_eq_two`, `classGroup_isCyclic`, `classGroup_card_eq_two`: class number 2, `Cl ≅ ℤ/2ℤ`,
  generated by `[𝔭₂]` (`p₂_order`, `class_eq_one_or_p₂`)
- `p₂_sq`, `p₃_mul_p₃'`, `six_factorizations`: `(2) = 𝔭₂²`, `(3) = 𝔭₃·𝔭₃′`,
  `(6) = 𝔭₂²·𝔭₃·𝔭₃′ = (1+√−5)(1−√−5)`
- `not_uniqueFactorization_elements`, `uniqueFactorization_ideals`, `factorizations_not_associated`:
  unique factorization of elements fails; unique factorization of ideals holds
- `χ_neg20_eq_mul`: `χ_{−20} = χ_{−4} · χ₅`, with `χ₅ := quadraticChar (ZMod 5)` (Mathlib does not name `χ₅`)
- `seven_home`, `sixtySeven_home`, `oneHundredSeven_home`: `7`, `67`, and `107` are inert in `ℚ(i)` and
  in `ℚ(√5)`, and split in `ℚ(√−5)` into the class of `𝔭₂`

`dedekindZeta_factorization_gap` is the statement `ζ_K(s) = ζ(s) · L(s, χ_{−20})`. Mathlib defines
`dedekindZeta` and `DirichletCharacter.LFunction` and does not prove this identity. The definition is
that missing statement: a proposition, not an axiom, and not a proof. It is not in `checks/PrintAxioms.lean`.

Sacred hold. The module states what the field is. "What the Pit is made of," and whether Portal / Pit /
THE THING are the same, is her open question — not answered, not adjudicated. Report §7: those questions
"are untouched by the theorems in §1–§5."
