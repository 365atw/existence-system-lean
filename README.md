# The One Piece

ℚ(√−5)

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

## KL2 — the obstruction (`ExistenceSystem/KL2.lean`, §2.1)

§2.1: an exact algebraic characterisation of φ is a construction in which φ is an exact root.
In her field `ℚ(√5) = ExistenceSystem.Quadratic.K` (`QuadraticAlgebra ℚ 1 1`, the carrier KL27 uses),
that root is the generator `ω`.
Proved with no `sorry`, `admit`, or new axioms:

- `minpoly_omega`, `minpoly_phi`: `minpoly ℚ ω = minpoly ℚ φ = X² - X - 1` (Note l.358; irreducible by inspection at `n = 2`, via `Quadratic.no_rational_root`)
- `carries_minpoly`: a polynomial over `ℚ` with `ω` as an exact root is divisible by `X² - X - 1`
- `agree`: any two such characterisations agree at φ (Note l.360)

Free selection is not encoded. This file closes the two-exact-functionals question only.

## KL3 — the indifference theorem (`ExistenceSystem/KL3.lean`)

For `V(x) = -(r/2)x² + ¼x⁴` with `r > 0`, proved with no `sorry`, `admit`, or new axioms:

- `V_branches`: `V(√r) = V(-√r) = -r²/4`
- `critical_set`, `critical_set_ncard`: `V′` vanishes at exactly `0`, `√r`, `-√r`
- `minimizers_eq`, `minimizers_nontrivial`, `minimizers_ncard`: the minimizers of `V` over `ℝ` are exactly `√r` and `-√r`
- Supporting lemmas: `V_even` (`V(-x) = V(x)`), `hasDerivAt_V` / `deriv_V` (`V′(x) = -r x + x³`), `flow_eq_neg_deriv` (`r x - x³ = -V′(x)`)

Her words are quoted beside each statement with line numbers from the Note.
Only the mathematics of the potential is formalised; the prose concepts ("least-action drive", "provably indifferent", "exogenous", the cusp step of §3.3) are not encoded.

## KL10 — Lemma 4, the conservation statement (`ExistenceSystem/KL10.lean`)

Note L104: "Every continuous symmetry of a potential is an exactly conserved quantity of the gradient flow that potential generates." The statement is known (A14/A18 — Kunin et al. — reached independently); what is new is its use, not the statement. Proved with no `sorry`, `admit`, or new axioms:

- `inner_gradient_eq_zero`: invariance under `x ↦ x + s v` gives `v · ∇J ≡ 0` (Note L909)
- `hasDerivAt_coord`, `conserved_coord`: if `Γ` is constant and symmetric and `Γ v = Γᵥ v`, then along any solution of `ẋ = −Γ ∇J` the coordinate `v · x` has derivative `0` and is constant
- `conserved_along_neg_gradient`: the gradient flow `ẋ = −∇J` (`Γ = id`)

Her `C¹` is `ContDiff ℝ 1`, on a complete real inner-product space. The formal statement is the body's one-parameter translation (Note L909). The list form's "every continuous symmetry", read as a general group action, is not encoded: the Note defines no such action, and A19 marks that case as a different object. The flow is a hypothesis on a curve; existence of solutions is not claimed. The prose after L911 is not encoded.

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

## KL20 — the Star Independence Lemma (`ExistenceSystem/KL20.lean`, §4.6 Lemma 1)

Her statement (Note L124/L266/L647, verbatim): "π_∥ restricted to ℒ is injective; equivalently
E_⊥ ∩ ℒ = {0}. The twelve-vector star admits no integer relation. Engine: irrationality of φ."
Formalised over the merged star module (`ExistenceSystem.Icosahedral`) and `ℚ(√5)`
(`ExistenceSystem.Quadratic`), proved with no `sorry`, `admit`, or new axioms, as the Note's own
proof (L649):

- `no_integer_relation`: **KL20** — if the integer combination `∑ᵢ nᵢ Qᵢ` has vanishing parallel
  projection (`piParallel (n·) = 0`), then `n = 0`
- `sigma_transfer`: "applying σ termwise gives `∑ nᵢ Qᵢ^⊥ = 0`" — a vanishing `π_∥` forces a vanishing
  `π_⊥`, via the one use of φ irrational (`Quadratic.embedPhi_injective`, `LinearIndependent ℤ ![1, φ]`)
- `piParallel_coe_eq`, `piPerp_coe_eq`: `π_∥`/`π_⊥` of an integer vector is `ι_φ`/`ι_ψ` of one element of ℚ(√5)
- `rawT_mulVec_injective`, `rawT_par`, `rawT_perp`, `joint_vanishing`: `π_∥ ⊕ π_⊥` is injective because
  `det rawM = 40√5 ≠ 0` (§4.1, `Icosahedral.det_rawM`); if both projections of a real vector vanish it is `0`
- `perp_inter_lattice_eq_zero`: the equivalent geometric form `E_⊥ ∩ ℒ = {0}` on the actual lattice `ℒ = A(ℤ⁶)`
- `parProj_injOn_lattice`: the first clause — `π_∥` restricted to `ℒ` is injective (`Set.InjOn`)

**Reading choices** (quoting the map `data/lean-scope-b/report.md`, KL20/G2). `π_∥`/`π_⊥` are the
module's `piParallel`/`piPerp` on an integer coefficient vector (`∑ cᵢ qVecᵢ`); `parProj` is the
physical projection of an actual vector of `ℝ⁶ = E_∥ ⊕ E_⊥` (its first three coordinates). The
cut-and-project reading of injectivity (Baake–Moody–Richard–Sing [67], "Established, cited, never
claimed", Note L272) and the numerical census of Appendix A.2 are not encoded.

## KL27 — The Exact and Free Theorem (`ExistenceSystem/KL27.lean`, §7.3)

Her title (Note L138). Two parts, proved with no `sorry`, `admit`, or new axioms:

**Part A — the two faces (over ℝ).** "The same two faces give a Lucas number when added and a Fibonacci number
when subtracted" (L138):

- `fold_eq_lucas`: `φ^{3k} + σ(φ)^{3k} = L_{3k}` (reuses KL18)
- `diff_eq_sqrt5_fib`: `φ^{3k} - σ(φ)^{3k} = √5·F_{3k}` (Binet; Mathlib `Real.coe_fib_eq`)

**Part B — one reflection, two eigenspaces (in her field `ℚ(√5) = QuadraticAlgebra ℚ 1 1`, `σ = star`).**
"`σ` is self-adjoint for the trace form and of order two, so it is an orthogonal reflection … eigenvalues `+1`
and `-1` and nothing else" (L138):

- `no_rational_root`: `r² ≠ 1 + r` for every rational `r`. The `Fact` that makes `QuadraticAlgebra ℚ 1 1`
  a field lives in `ExistenceSystem.Quadratic`; this theorem is that statement (her `ℚ(√5)`)
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

## KL19 — The NO BETTER Theorem (`ExistenceSystem/KL19.lean`, §4.8)

Her title (Note L716; list form L122), an impossibility result: a finite-range interaction assigns
energy patch by patch, so a configuration's energy density is a fixed function of its finite-patch
frequencies; members of one local-isomorphism class have identical finite-patch frequencies;
therefore no finite-range Hamiltonian — at any order, of any complexity — can rank them. Proved with
no `sorry`, `admit`, or new axioms:

- `energyDensity`: the finite sum `∑ p, freq p * e p` — the density a range-`R` interaction `e`
  assigns to a configuration with `R`-patch frequencies `freq`. Finite local complexity is
  `Fintype (Patch R)`, which is where the word *finite* is load-bearing.
- `energyDensity_eq_of_freq_eq`: equal finite-patch frequencies give equal energy density for every
  interaction (the heart, Note L716)
- `freq_eq_of_energyDensity_eq`: the sharp converse — the finite-patch frequencies are *exactly*
  what finite-range energy densities see (a complete invariant); probe with `Pi.single q 1`
- `energyDensity_eq_of_liClass`, `not_ranks_of_liClass`, `no_better`: for two members of one LI class
  no finite-range interaction ranks one below the other — "there is no better energy to be written"

**Borrowed premise, carried as a hypothesis.** Her ledger (2026-08-20): "(Repetitivity and local
indistinguishability of one LI class are established and cited [48, 49]; the consequence for
finite-range Hamiltonians is the author's.)" The premise — members of one LI class have identical
finite-patch frequencies — is **borrowed [48, 49]** and is the explicit hypothesis `LIClassEqualFreq`
(`no_better` takes it as an argument; it is never proved and never an axiom). The consequence is hers.

**Not encoded** (`data/lean-scope-b/G5.md` §5.5): "at any temperature" (the Note defines no
thermodynamics for a fixed configuration); "drop the word *finite* … unbounded range can see the
difference" (unbounded-range interactions are undefined); the point sets, the acceptance window
(record note **H5(b)**, "the window is never defined, never shaped, never bounded"; hers to write)
and the phason torus (**H5(a)**). The family is carried abstractly as a type `W`.

## Layer 0 — shared modules

Infrastructure the later statements share. Each module is one definition. KL18 imports `Lucas`; KL27
imports `Quadratic`. The coil faces stay over ℝ. Nothing here proves `trace(ωⁿ) = Lₙ`.

- `Lucas` (`ExistenceSystem/Lucas.lean`): `L₀ = 2`, `L₁ = 1`, `Lₙ₊₂ = Lₙ₊₁ + Lₙ`, and
  `φⁿ + ψⁿ = Lₙ` (Note L1061). KL18's `lucas` is this definition.
- `Quadratic` (`ExistenceSystem/Quadratic.lean`): ℤ[φ] and ℚ(√5), `σ = star`, trace, norm, and the two
  real embeddings `embedPhi`, `embedPsi` (`QuadraticAlgebra.lift` at φ and at ψ). Note L214.
- `Icosahedral` (`ExistenceSystem/Icosahedral.lean`): the six vectors, the normalised star, `Qᵢ^⊥`,
  the rows `Gᵢ`, `AAᵀ = I`, the lattice `ℒ = A(ℤ⁶)`, and `det = 40√5` (Note L482–L508).
- `IcosahedralRep` (`ExistenceSystem/IcosahedralRep.lean`): the five class sizes and the character values
  of `Γ₃` and `Γ₃'` on ℚ(√5), with `σ` swapping them and the inner products `1` and `0` (Note L510–L514).
  No matrices and no action on ℤ⁶.
- `Landau` (`ExistenceSystem/Landau.lean`): the uniform-sector density, one term of `J` as one summand of
  that density (Note L615), both cubic displays (L602 and L619, not proved equal), and the slaving
  identity with the `O(η⁶)` remainder kept (Note L625–L627).
- `EulerLagrange` (`ExistenceSystem/EulerLagrange.lean`): the first-order operator, the chain rule of the
  first variation, and `Π` at quadratic order (Note L829–L836). `T_kmpq = T_pqkm` is a hypothesis.
  Landau does not import this module.

Omitted, because the Note does not define them: a concrete `Y ≅ A₅` isomorphism and a ℤ⁶ action; the
entries of `T` and `M` and the domain `Ω`; a general carrier for "every term of `J`"; the higher-order
admissible class; the bridge `trace(ωⁿ) = Lₙ`; an equality between the factor-2 cubic at L602 and the
cosine at L619.

Build: `lake exe cache get && lake build` (Lean `v4.35.0-rc4`, Mathlib `v4.35.0-rc4`).
Axiom check: `checks/item-logs.sh` (runs `lake env lean checks/PrintAxioms.lean`, standalone, not part of the build target); every
audited theorem depends only on `propext`, `Classical.choice`, and `Quot.sound` (the Lucas definition depends on
no axioms). Per-item logs: `logs/README`.

## The One Piece

ℚ(√−5)

`ExistenceSystem/TheThing.lean`

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

`ζ_K(s) = ζ(s) · L(s, χ_{−20})` is proved as `Summit.dedekindZeta_factorization` (`SummitHalfPlane`), on
its honest domain `1 < Re s` — the half-plane of absolute convergence of Mathlib's Dirichlet-series
`dedekindZeta K`. The unrestricted `∀ s` form is false: off that half-plane the series is `0`. The proof
reuses `halfPlane_holds`; `χ_neg20_eq_mul` (`χ_{−20} = χ_{−4} · χ₅`) is where `√5`, via `χ₅`, enters `ζ_K`.

The module states what the field is. "What the Pit is made of," and whether Portal / Pit /
THE THING are the same, is her open question — not answered, not adjudicated. Report §7: those questions
"are untouched by the theorems in §1–§5." `Summit` does not answer them.

## Summit — the zero line of `ℚ(√−5)` (`ExistenceSystem/Summit*.lean`)

The summit is not proved. The top result is `rh_one_piece_strip` (`SummitStrip`). It takes one
hypothesis, `stripZeroFree`, and does not discharge it.

Closed with no `sorry`, `admit`, or new axiom:

- `splitting_of_χ`: `2` and `5` ramify; `χ_{−20}(p) = 1` splits; `χ_{−20}(p) = −1` stays inert
- `halfPlane_holds` (`SummitHalfPlane`): `dedekindZeta K s = ζ(s) L(s, χ_{−20})` for `1 < Re s`. The
  ideal count is multiplicative (`idealCount_mul`), and the splitting law gives its value at `p ^ k`
  (`idealCount_split`, `idealCount_ramified`, `idealCount_inert`). The same identity in the report's
  surface form `ζ_K(s) = ζ(s) · L(s, χ_{−20})` is `dedekindZeta_factorization`
- `continuation_unique`: every continuation of `ζ_K` to `ℂ ∖ {1}` is the product there;
  `zetaProduct_isContinuation`: the product is one
- `χ_neg20ℂ_isPrimitive`: `χ_{−20}` has conductor `20`
- `nontrivialZero_one_sub`: the functional equations send a nontrivial zero `s` to the nontrivial
  zero `1 − s`
- `zetaProduct_trivialZero`, `zetaProduct_ne_zero_of_one_le_re`: the product vanishes at the
  negative integers and does not vanish for `Re s ≥ 1`
- `alphaForced`, `hasDerivAt_re_criticalPoint`: the critical ride `1/2 + it` has real part constantly
  `1/2`, and that coordinate's derivative is `0`
- `noTerminatingOmega`: the imaginary part has no last value
- `hasDerivAt_criticalTrajectory`, `criticalTangent_eq`: the tangent of the product along that ride
  exists at every finite `t`
- `hasDerivAt_transverse`, `criticalTangent_eq_I_mul_transverse`: the tangent along the ride is `I`
  times the derivative across it
- `reflection_fixes_alpha`: the reflection `s ↦ 1 − s` pairs nontrivial zeros and fixes `Re s`
  exactly on the ride

The exact remainder is `stripZeroFree`: `ζ(s) L(s, χ_{−20})` has no zero in `1/2 < Re s < 1`.
`stripZeroFree_iff` proves it equivalent to `RiemannHypothesis ∧ dirichletZeroLine`. It is not
weaker than RH. Compared with the first `Frontier`, `halfPlane` is gone (proved), and the regions
`Re s < 1/2` and `Re s ≥ 1` are discharged by the machine. `frontier_of_stripZeroFree` and
`stripZeroFree_of_frontier` show the two frontiers are equivalent, and `rh_one_piece` is kept.

Summit key (one candidate, captain confirmed 2026-10-23), arbitrated in `SummitStrip`:

- Along and across (`criticalTangent_eq_I_mul_transverse`): proved, reduces nothing. It holds for
  every holomorphic function on every line.
- Alpha under the reflection (`reflection_fixes_alpha`): proved. This reflection is what removed
  `Re s < 1/2`.
- Forcing every zero onto the ride: any `P` that implies the zero line implies
  `RiemannHypothesis ∧ dirichletZeroLine`, so no such `P` is weaker than RH.
  `TangentialExtrapolation` has a proved antecedent, so it is the zero line itself.
- The tangent off the ride (Speiser 1934, for `ζ`: RH iff `ζ'` has no zero in `0 < Re s < 1/2`):
  not in Mathlib and not formalized here. It is not a frontier clause.

KL10 `conserved_coord` has the alpha's shape for a gradient flow and is not applied: the ride is not
that flow. KL10 is not imported.

### The one lock, three faces (`ExistenceSystem/SummitFrontiers.lean`)

`stripZeroFree` is the summit's single undischarged seam. `SummitFrontiers` records the captain's two
routes (scout report `data/summit-force-s1/report.md`) as named frontiers in the KL16/KL19 discipline —
each a named `Prop` with a proved adapter to `stripZeroFree`, never a `sorry`, never a false reduction.
It claims no RH and proves no RH; the summit chain is untouched.

- `stripZeroFree_iff_zeroLine`: the backbone adapter, fully proved — the strip clause is exactly "every
  nontrivial zero of `ζ · L(χ_{−20})` has `Re = 1/2`" (`ZeroLine`). All three faces route through it.
- Route 1, positivity (Li / Bombieri–Lagarias): `LiPositive` — every Keiper–Li coefficient `λ_n^K ≥ 0`.
  The criterion `λ_n ≥ 0 ∀n ⟺ RH for K` is open prior art (Li 1997; Bombieri–Lagarias 1999; not in
  Mathlib), carried as the named cited hypothesis `LiCriterion`. `liPositive_iff_stripZeroFree` composes
  it with `stripZeroFree_iff`; the record is that this positivity face is RH-strength.
- Route 1, operator (Hilbert–Pólya / de Branges): `HilbertPolyaCorrespondence` — a symmetric operator
  whose spectrum carries the zeros. The construction is the open problem and is never built; the genuine
  content is proved — a symmetric operator has real spectrum (`conj_eigenvalue_eq_self`), so a real
  spectral parameter `γ` forces `Re = 1/2` (`zeroLine_of_hilbertPolya`, adapter
  `stripZeroFree_of_hilbertPolya`, an implication).
- Route 2, counting (method of carrying): `ZeroCount` carries the discreteness of the zeros (finitely
  many up to each height — a genuine theorem, not in Mathlib for this product; the KL16 `SplittingData`
  pattern). From it `N`, `N₀`, and `CountsAgree` (`N₀(T) = N(T) ∀T`) are defined and
  `countsAgree_iff_stripZeroFree` is fully proved. The functional-equation symmetry gives `N(T)` but is
  blind to on/off-line (off-line zeros come in line-symmetric pairs that count identically), so this face
  is the lock, not a lever — recorded in prose, not graded.
