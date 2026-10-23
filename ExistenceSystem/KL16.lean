module

/-
KL16 — THE FOUR PERFECT IDEALS OF ℤ[φ], from THE EXACT AND FREE SYSTEM — AN EXISTENCE SYNTHESIS.
All mathematics: Kari A Light, except the perfect-ideal definition, which is borrowed and marked.

Source: `THE-NOTE-EDITED.md` (194,868 bytes, 1,539 lines); line numbers below refer to it.
Her §2.4 statement, quoted verbatim in `four_perfect_ideals` below.

Her words (Note L385, §2.4, quoted exactly):
  "Theorem (The four perfect ideals of ℤ[φ], KL16). Exhaustive to norm 10¹⁰, there are exactly
   four perfect ideals in ℤ[φ]. All four have N(𝔞)=3,928,320, and they form two σ-orbits of length
   two. σ moves every one of them; not one is fixed."

Definition (Note L383, §2.4, Hausman and Shapiro [53]; NOT claimed here):
  "For an ideal 𝔞 of ℤ[φ] write Σ(𝔞)=∑_{𝔟∣𝔞} N(𝔟) and I(𝔞)=Σ(𝔞)/N(𝔞). An ideal with
   Σ(𝔞)=2N(𝔞) is a *perfect ideal*." (Hausman, Shapiro, Comm. Pure Appl. Math. 29 (1976), 323–341.)

The four, as she records them (Note L389):
  𝔞₁=(2)⁴(3)(√5)𝔭₁₁𝔭₃₁,  𝔞₂=(2)⁴(3)(√5)p̄₁₁p̄₃₁,
  𝔞₃=(2)⁴(3)(√5)𝔭₁₁p̄₃₁,  𝔞₄=(2)⁴(3)(√5)p̄₁₁𝔭₃₁.
  Aligned: σ:𝔞₁↔𝔞₂. Crossed: σ:𝔞₃↔𝔞₄. (Note L396.)
  N = 4⁴·9·5·11·31 = 3,928,320, Σ = 341·10·6·12·32 = 7,856,640, I = 2 exactly (Note L398).

The mechanism (Note L402): "It closes because 2¹⁰−1=1023=3·11·31, and 11 and 31 both split in ℤ[φ]
  since both are ≡1 (mod 5). Σ((2)⁴)=(4⁵−1)/3=341=11·31; taking one prime above each asymmetrically
  is what breaks the σ-symmetry and produces the orbit of two."

The classical perfect numbers do not lift (Note L404): "6, 28, 496 and 8128 all have abundancy index
  ≠2 in this ring, because 2, 3 and 7 are inert." See `classical_perfect_numbers_do_not_lift`.

## What is proved here, and what is a displayed hypothesis — the reading, per the captain's ruling.

The captain's ruling (a): work over Mathlib's ring of integers `𝓞` of ℚ(√5) — which Mathlib carries as
a Dedekind domain — not over `QuadraticAlgebra ℤ 1 1` (the shared `ExistenceSystem.Quadratic` carrier,
which Mathlib does not know as a Dedekind domain). So `K = ℚ(√5)` is built here as `AdjoinRoot (X²−X−1)`
(root `φ`), and `𝓞 K = ℤ[φ]`; `σ` is its Galois conjugation `φ ↦ 1−φ`.

* PROVED, gap-free, over `𝓞 K`:
  - the Hausman–Shapiro divisor-sum `Σ = sigmaIdeal` (`§1`), its value on a prime power
    (`sigmaIdeal_prime_pow`, the geometric sum) and its multiplicativity on coprime ideals
    (`sigmaIdeal_mul_coprime`) — this is the arithmetic engine;
  - each of the four explicit ideals is perfect (`four_perfect_ideals`), with `N(𝔞ᵢ)=3,928,320`;
  - the two σ-orbits of length two: σ swaps within each pair, none is fixed, the four are distinct
    (`sigma_orbits`);
  - the classical perfect numbers 6, 28, 496, 8128 do not lift (`classical_perfect_numbers_do_not_lift`).

* DISPLAYED HYPOTHESIS (borrowed number theory, not claimed): the structure `SplittingData` bundles the
  Kummer–Dedekind splitting of the rational primes in ℤ[φ] — that 2, 3, 7, 127 are inert, 5 ramifies,
  and 11, 31 split into distinct conjugate primes, with their ideal norms, and that σ swaps the split
  conjugates. These are the factorisations the Note states (L402); Mathlib does not hand them to us, and
  the elementary route needs the indefinite norm form `a²+ab−b²` and Kummer–Dedekind, so they are carried
  as named inputs, exactly the house convention for content from outside. Everything above is proved FROM
  this structure, gap-free, with no `sorry`/`admit`/axiom.

* THE FRONTIER (Note L385/L412): "exactly four / exhaustive to 10¹⁰." Her Note gives NO search procedure
  ("No theorem asserts that more exist", L412). This is the unproven frontier `ExhaustiveToBound` — a
  `Prop`-valued hypothesis, clearly labelled, NEVER a `sorry`/axiom. Exhibiting and proving the four,
  with exhaustiveness as a named hypothesis, is the deliverable (the 10¹⁰ search is deferred work).
-/
public import Mathlib

@[expose] public section

noncomputable section

open Polynomial NumberField Ideal Module Finset

namespace ExistenceSystem.KL16

/-! ## 0. The field `K = ℚ(√5)` and its ring of integers `𝓞 K = ℤ[φ]`

`K = ℚ[X]/(X²−X−1)`; the root is `φ`, with `φ² = φ + 1`. The ring of integers `𝓞 K` is `ℤ[φ]`, a
Dedekind domain (Mathlib). `σ` is the Galois conjugation `φ ↦ 1−φ` (Note Taxonomy L214: the nontrivial
automorphism of ℚ(√5)). -/

/-- The minimal polynomial of `φ`, `X² − X − 1`. -/
def poly : ℚ[X] := X ^ 2 - X - 1

lemma poly_natDegree : poly.natDegree = 2 := by
  unfold poly
  compute_degree!

lemma poly_monic : poly.Monic := by
  unfold poly
  monicity!

lemma poly_ne_zero : poly ≠ 0 := poly_monic.ne_zero

/-- `X² − X − 1` is irreducible over ℚ: its roots `φ, ψ` are irrational. -/
lemma poly_irreducible : Irreducible poly := by
  refine irreducible_of_degree_le_three_of_not_isRoot ?_ ?_
  · rw [Finset.mem_Icc, poly_natDegree]; omega
  · intro r hr
    have hr' : r ^ 2 - r - 1 = 0 := by
      simpa [poly, IsRoot.def, eval_sub, eval_pow, eval_X, eval_one] using hr
    -- `r² = r + 1` has no rational solution: the two real roots `φ, ψ` are irrational.
    have hrR : (r : ℝ) ^ 2 = (r : ℝ) + 1 := by
      have : (r : ℝ) ^ 2 - (r : ℝ) - 1 = 0 := by exact_mod_cast hr'
      linarith
    have hfac : ((r : ℝ) - Real.goldenRatio) * ((r : ℝ) - Real.goldenConj) = 0 := by
      have h1 : Real.goldenRatio + Real.goldenConj = 1 := Real.goldenRatio_add_goldenConj
      have h2 : Real.goldenRatio * Real.goldenConj = -1 := Real.goldenRatio_mul_goldenConj
      nlinarith [hrR, h1, h2]
    rcases mul_eq_zero.1 hfac with h | h
    · exact Real.goldenRatio_irrational ⟨r, by linarith⟩
    · exact Real.goldenConj_irrational ⟨r, by linarith⟩

instance : Fact (Irreducible poly) := ⟨poly_irreducible⟩

/-- `K = ℚ(√5)`, as `ℚ[X]/(X²−X−1)`. -/
abbrev K : Type := AdjoinRoot poly

/-- `φ`, the adjoined root. -/
def phi : K := AdjoinRoot.root poly

/-- `φ² = φ + 1` (Note Taxonomy: `ω² = 1 + ω`). -/
lemma phi_sq : phi ^ 2 = phi + 1 := by
  have key : phi ^ 2 - phi - 1 = 0 := by
    have e : (AdjoinRoot.mk poly) (X ^ 2 - X - 1) = phi ^ 2 - phi - 1 := by
      simp only [map_sub, map_pow, map_one, AdjoinRoot.mk_X, phi]
    rw [← e]
    exact AdjoinRoot.mk_self
  linear_combination key

lemma finrank_K : Module.finrank ℚ K = 2 := by
  have h := (AdjoinRoot.powerBasis poly_ne_zero).finrank
  rwa [AdjoinRoot.powerBasis_dim, poly_natDegree] at h

/-- The conjugate automorphism `φ ↦ 1 − φ`. The other root of `X²−X−1` is `1−φ`. -/
def conjHom : K →ₐ[ℚ] K :=
  AdjoinRoot.liftAlgHom poly (Algebra.ofId ℚ K) (1 - phi) <| by
    have h : phi ^ 2 = phi + 1 := phi_sq
    simp only [poly, eval₂_sub, eval₂_pow, eval₂_X, eval₂_one]
    linear_combination h

@[simp] lemma conjHom_phi : conjHom phi = 1 - phi :=
  AdjoinRoot.liftAlgHom_root poly (Algebra.ofId ℚ K) (1 - phi) _

lemma conjHom_conjHom (x : K) : conjHom (conjHom x) = x := by
  have hcomp : conjHom.comp conjHom = AlgHom.id ℚ K := by
    apply AdjoinRoot.algHom_ext
    show conjHom (conjHom phi) = phi
    rw [conjHom_phi, map_sub, map_one, conjHom_phi]
    ring
  exact AlgHom.congr_fun hcomp x

/-- The conjugation as a ring equivalence of `K` (an involution). -/
def conjEquiv : K ≃+* K :=
  RingEquiv.ofRingHom conjHom.toRingHom conjHom.toRingHom
    (RingHom.ext conjHom_conjHom) (RingHom.ext conjHom_conjHom)

/-- `σ`, the conjugation on `𝓞 K = ℤ[φ]` (Note L214). -/
def sigma : 𝓞 K ≃+* 𝓞 K := RingOfIntegers.mapRingEquiv conjEquiv

/-- `σ` acting on ideals: `𝔞 ↦ σ(𝔞)`. -/
def conjIdeal (I : Ideal (𝓞 K)) : Ideal (𝓞 K) := Ideal.map (sigma : 𝓞 K →+* 𝓞 K) I

lemma conjIdeal_mul (I J : Ideal (𝓞 K)) : conjIdeal (I * J) = conjIdeal I * conjIdeal J := by
  unfold conjIdeal
  exact Ideal.map_mul _ I J

lemma conjIdeal_pow (I : Ideal (𝓞 K)) (k : ℕ) : conjIdeal (I ^ k) = conjIdeal I ^ k := by
  induction k with
  | zero => simp [conjIdeal, Ideal.map_top]
  | succ k ih => rw [pow_succ, pow_succ, conjIdeal_mul, ih]

lemma sigma_sigma (x : 𝓞 K) : sigma (sigma x) = x := by
  apply RingOfIntegers.ext
  have h : ((sigma (sigma x) : 𝓞 K) : K) = conjEquiv (conjEquiv (x : K)) := by
    simp [sigma, RingOfIntegers.mapRingEquiv_apply]
  rw [h]
  show conjHom (conjHom (x : K)) = (x : K)
  exact conjHom_conjHom _

lemma conjIdeal_conjIdeal (I : Ideal (𝓞 K)) : conjIdeal (conjIdeal I) = I := by
  unfold conjIdeal
  rw [Ideal.map_map]
  have hid : (sigma : 𝓞 K →+* 𝓞 K).comp (sigma : 𝓞 K →+* 𝓞 K) = RingHom.id (𝓞 K) :=
    RingHom.ext fun x => sigma_sigma x
  rw [hid, Ideal.map_id]

/-- `σ` fixes the ideal generated by any `σ`-fixed element. -/
lemma conjIdeal_span_fixed {x : 𝓞 K} (h : (sigma : 𝓞 K →+* 𝓞 K) x = x) :
    conjIdeal (span {x}) = span {x} := by
  unfold conjIdeal
  rw [Ideal.map_span, Set.image_singleton, h]

/-- `σ` fixes `(2)` and `(3)` (it fixes the rational integers `2, 3`). -/
lemma sigma_ofNat_fixed (n : ℕ) [n.AtLeastTwo] :
    (sigma : 𝓞 K →+* 𝓞 K) (OfNat.ofNat n) = OfNat.ofNat n := map_ofNat _ n

/-! ## 1. The Hausman–Shapiro divisor-sum `Σ = sigmaIdeal`, over the Dedekind domain `𝓞 K`

`Σ(𝔞) = ∑_{𝔟 ∣ 𝔞} N(𝔟)` (Note L383). The monoid of ideals of a Dedekind domain is a
`UniqueFactorizationMonoid` with finitely many units, so a nonzero ideal has finitely many divisors
(`UniqueFactorizationMonoid.fintypeSubtypeDvd`). We prove the two facts the computation needs: the
value on a prime power is the geometric sum (`sigmaIdeal_prime_pow`), and `Σ` is multiplicative on
coprime ideals (`sigmaIdeal_mul_coprime`). -/

/-- The finset of divisors of a nonzero ideal; `∅` at `⊥`. -/
noncomputable def divisors (I : Ideal (𝓞 K)) : Finset (Ideal (𝓞 K)) :=
  open Classical in
  if h : I = ⊥ then ∅
  else (@Finset.univ {d : Ideal (𝓞 K) // d ∣ I}
    (UniqueFactorizationMonoid.fintypeSubtypeDvd I h)).image Subtype.val

lemma mem_divisors {I J : Ideal (𝓞 K)} (hI : I ≠ ⊥) : J ∈ divisors I ↔ J ∣ I := by
  classical
  unfold divisors
  rw [dif_neg hI]
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Subtype.exists]
  constructor
  · rintro ⟨d, hd, rfl⟩; exact hd
  · intro h; exact ⟨J, h, rfl⟩

/-- `Σ(𝔞) = ∑_{𝔟 ∣ 𝔞} N(𝔟)` (Hausman–Shapiro, Note L383). -/
def sigmaIdeal (I : Ideal (𝓞 K)) : ℕ := ∑ J ∈ divisors I, Ideal.absNorm J

/-- An ideal is *perfect* when `Σ(𝔞) = 2 N(𝔞)` (Hausman–Shapiro; Note L383). -/
def IsPerfect (I : Ideal (𝓞 K)) : Prop := sigmaIdeal I = 2 * Ideal.absNorm I

/-- The divisors of a prime power `p^k` are exactly `p^0, …, p^k`. -/
lemma divisors_prime_pow {p : Ideal (𝓞 K)} (hp : Prime p) (k : ℕ) :
    divisors (p ^ k) = (Finset.range (k + 1)).image (p ^ ·) := by
  classical
  have hpne : p ^ k ≠ ⊥ := pow_ne_zero k hp.ne_zero
  ext J
  rw [mem_divisors hpne, Finset.mem_image]
  constructor
  · intro hJ
    rw [dvd_prime_pow hp] at hJ
    obtain ⟨i, hik, hassoc⟩ := hJ
    exact ⟨i, Finset.mem_range.mpr (by omega), (associated_iff_eq.mp hassoc.symm)⟩
  · rintro ⟨i, hi, rfl⟩
    rw [dvd_prime_pow hp]
    exact ⟨i, by simpa using Nat.lt_succ_iff.mp (Finset.mem_range.mp hi), Associated.refl _⟩

lemma pow_injective_of_prime {p : Ideal (𝓞 K)} (hp : Prime p) :
    Function.Injective (p ^ ·) := by
  intro i j hij
  by_contra hne
  wlog h : i < j generalizing i j
  · exact this hij.symm (Ne.symm hne) (by omega)
  · have hij' : p ^ i = p ^ j := hij
    have hdvd : p ^ j ∣ p ^ i := ⟨1, by rw [hij', mul_one]⟩
    have : p ^ (i + 1) ∣ p ^ j := pow_dvd_pow p (by omega)
    have hd2 : p ^ (i + 1) ∣ p ^ i := this.trans hdvd
    have := (pow_dvd_pow_iff hp.ne_zero hp.not_isUnit).mp hd2
    omega

/-- The geometric sum: `Σ(p^k) = ∑_{i=0}^{k} N(p)^i`. (Note L402 for `(2)⁴`: `341=(4⁵−1)/3`.) -/
lemma sigmaIdeal_prime_pow {p : Ideal (𝓞 K)} (hp : Prime p) (k : ℕ) :
    sigmaIdeal (p ^ k) = ∑ i ∈ Finset.range (k + 1), (Ideal.absNorm p) ^ i := by
  unfold sigmaIdeal
  rw [divisors_prime_pow hp k, Finset.sum_image (pow_injective_of_prime hp).injOn]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_pow]

/-- Antisymmetry of divisibility for ideals, via `I ∣ J ↔ J ≤ I`. -/
lemma ideal_dvd_antisymm {I J : Ideal (𝓞 K)} (h1 : I ∣ J) (h2 : J ∣ I) : I = J := by
  rw [Ideal.dvd_iff_le] at h1 h2
  exact le_antisymm h2 h1

/-- `gcd(a·b, I) = a` when `a ∣ I` and `b` is coprime to `I`. -/
lemma gcd_mul_coprime_eq {a b I : Ideal (𝓞 K)} (ha : a ∣ I) (hcop : IsCoprime b I) :
    gcd (a * b) I = a := by
  apply ideal_dvd_antisymm
  · -- `gcd(a·b, I) ∣ a`: it divides `a·b` and is coprime to `b` (dividing `I`).
    have hd1 : gcd (a * b) I ∣ a * b := gcd_dvd_left _ _
    have hd2 : gcd (a * b) I ∣ I := gcd_dvd_right _ _
    have hcop' : IsCoprime (gcd (a * b) I) b := hcop.symm.of_isCoprime_of_dvd_left hd2
    exact hcop'.dvd_of_dvd_mul_right hd1
  · exact dvd_gcd (dvd_mul_right a b) ha

/-- For coprime `I, J`, a divisor `d` of `I·J` splits as `gcd(d,I) · gcd(d,J)`. -/
lemma dvd_mul_eq_gcd_mul {I J d : Ideal (𝓞 K)} (hcop : IsCoprime I J) (hd : d ∣ I * J) :
    gcd d I * gcd d J = d := by
  apply ideal_dvd_antisymm
  · -- `gcd d I` and `gcd d J` are coprime divisors of `d`, so their product divides `d`.
    have h1 : gcd d I ∣ d := gcd_dvd_left d I
    have h2 : gcd d J ∣ d := gcd_dvd_left d J
    have hcop' : IsCoprime (gcd d I) (gcd d J) :=
      (hcop.of_isCoprime_of_dvd_left (gcd_dvd_right d I)).of_isCoprime_of_dvd_right
        (gcd_dvd_right d J)
    exact hcop'.mul_dvd h1 h2
  · -- `d ∣ gcd d I * gcd d J`, pulling a gcd out of each factor in turn (no `normalize`).
    have s1 : d ∣ gcd d I * J := dvd_gcd_mul_of_dvd_mul hd
    have s2 : d ∣ gcd d J * gcd d I := by
      have hc : d ∣ J * gcd d I := by rw [mul_comm]; exact s1
      exact dvd_gcd_mul_of_dvd_mul hc
    rwa [mul_comm] at s2

/-- The multiplication map is injective on a product of coprime divisor-finsets. -/
lemma mul_injOn_divisors {I J : Ideal (𝓞 K)} (hI : I ≠ ⊥) (hJ : J ≠ ⊥) (hcop : IsCoprime I J) :
    Set.InjOn (fun p : Ideal (𝓞 K) × Ideal (𝓞 K) => p.1 * p.2)
      (divisors I ×ˢ divisors J : Finset (_ × _)) := by
  intro p hp q hq hpq
  simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, mem_divisors hI,
    mem_divisors hJ] at hp hq
  have hcp : IsCoprime p.2 I := (hcop.symm.of_isCoprime_of_dvd_left hp.2)
  have hcq : IsCoprime q.2 I := (hcop.symm.of_isCoprime_of_dvd_left hq.2)
  have hcp' : IsCoprime p.1 J := (hcop.of_isCoprime_of_dvd_left hp.1)
  have hcq' : IsCoprime q.1 J := (hcop.of_isCoprime_of_dvd_left hq.1)
  have e1 : p.1 = q.1 := by
    have h1 : gcd (p.1 * p.2) I = p.1 := gcd_mul_coprime_eq hp.1 hcp
    have h2 : gcd (q.1 * q.2) I = q.1 := gcd_mul_coprime_eq hq.1 hcq
    rw [← h1, ← h2]; exact congrArg (gcd · I) hpq
  have e2 : p.2 = q.2 := by
    have h1 : gcd (p.2 * p.1) J = p.2 := gcd_mul_coprime_eq hp.2 hcp'
    have h2 : gcd (q.2 * q.1) J = q.2 := gcd_mul_coprime_eq hq.2 hcq'
    rw [← h1, ← h2, mul_comm p.2 p.1, mul_comm q.2 q.1]; exact congrArg (gcd · J) hpq
  exact Prod.ext e1 e2

/-- The divisors of `I·J` (coprime) are exactly the products of a divisor of `I` and one of `J`. -/
lemma divisors_mul_coprime {I J : Ideal (𝓞 K)} (hI : I ≠ ⊥) (hJ : J ≠ ⊥) (hcop : IsCoprime I J) :
    divisors (I * J) = (divisors I ×ˢ divisors J).image (fun p => p.1 * p.2) := by
  have hIJ : I * J ≠ ⊥ := mul_ne_zero hI hJ
  ext d
  simp only [Finset.mem_image, Finset.mem_product, mem_divisors hIJ, mem_divisors hI,
    mem_divisors hJ]
  constructor
  · intro hd
    exact ⟨(gcd d I, gcd d J), ⟨gcd_dvd_right d I, gcd_dvd_right d J⟩, dvd_mul_eq_gcd_mul hcop hd⟩
  · rintro ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩
    exact mul_dvd_mul ha hb

/-- `Σ` is multiplicative on coprime ideals: `Σ(I·J) = Σ(I)·Σ(J)`. -/
lemma sigmaIdeal_mul_coprime {I J : Ideal (𝓞 K)} (hI : I ≠ ⊥) (hJ : J ≠ ⊥)
    (hcop : IsCoprime I J) : sigmaIdeal (I * J) = sigmaIdeal I * sigmaIdeal J := by
  classical
  unfold sigmaIdeal
  rw [divisors_mul_coprime hI hJ hcop, Finset.sum_image (mul_injOn_divisors hI hJ hcop),
    Finset.sum_product, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [map_mul]

/-! ## 2. The splitting data of the rational primes in ℤ[φ] (Kummer–Dedekind; borrowed, not claimed)

Note L402: "11 and 31 both split in ℤ[φ] since both are ≡1 (mod 5)"; `(2)⁴` has `Σ=341=11·31`; the
non-lifting (Note L404) is "because 2, 3 and 7 are inert." This bundles those factorisations — which
Mathlib does not hand us — as a displayed hypothesis, the house convention for borrowed content. -/

/-- The Kummer–Dedekind splitting of the rational primes used in §2.4, as a named hypothesis.
Each field is a factorisation / norm / primality that Kummer–Dedekind provides for ℤ[φ]. -/
structure SplittingData where
  /-- `5` ramifies: `(√5)` is a prime above `5`. -/
  p5 : Ideal (𝓞 K)
  /-- `11` splits: `𝔭₁₁`, a prime above `11`. -/
  p11 : Ideal (𝓞 K)
  /-- the conjugate `p̄₁₁` above `11`. -/
  q11 : Ideal (𝓞 K)
  /-- `31` splits: `𝔭₃₁`, a prime above `31`. -/
  p31 : Ideal (𝓞 K)
  /-- the conjugate `p̄₃₁` above `31`. -/
  q31 : Ideal (𝓞 K)
  two_inert : Prime (span {(2 : 𝓞 K)})
  three_inert : Prime (span {(3 : 𝓞 K)})
  seven_inert : Prime (span {(7 : 𝓞 K)})
  onetwoseven_inert : Prime (span {(127 : 𝓞 K)})
  p5_prime : Prime p5
  p5_norm : Ideal.absNorm p5 = 5
  five_ramifies : span {(5 : 𝓞 K)} = p5 ^ 2
  p11_prime : Prime p11
  q11_prime : Prime q11
  p11_norm : Ideal.absNorm p11 = 11
  q11_norm : Ideal.absNorm q11 = 11
  eleven_splits : span {(11 : 𝓞 K)} = p11 * q11
  p11_ne_q11 : p11 ≠ q11
  p31_prime : Prime p31
  q31_prime : Prime q31
  p31_norm : Ideal.absNorm p31 = 31
  q31_norm : Ideal.absNorm q31 = 31
  thirtyone_splits : span {(31 : 𝓞 K)} = p31 * q31
  p31_ne_q31 : p31 ≠ q31
  conj_p11 : conjIdeal p11 = q11
  conj_p31 : conjIdeal p31 = q31
  conj_p5 : conjIdeal p5 = p5

variable (sd : SplittingData)

/-- `N((2)) = 4`: `2` is inert, norm `2² = 4`. -/
lemma absNorm_span_two : Ideal.absNorm (span {(2 : 𝓞 K)}) = 4 := by
  have h := Ideal.absNorm_span_natCast (S := 𝓞 K) 2
  rw [RingOfIntegers.rank, finrank_K] at h
  simpa using h

lemma absNorm_span_three : Ideal.absNorm (span {(3 : 𝓞 K)}) = 9 := by
  have h := Ideal.absNorm_span_natCast (S := 𝓞 K) 3
  rw [RingOfIntegers.rank, finrank_K] at h
  simpa using h

lemma absNorm_span_seven : Ideal.absNorm (span {(7 : 𝓞 K)}) = 49 := by
  have h := Ideal.absNorm_span_natCast (S := 𝓞 K) 7
  rw [RingOfIntegers.rank, finrank_K] at h
  simpa using h

lemma absNorm_span_onetwoseven : Ideal.absNorm (span {(127 : 𝓞 K)}) = 16129 := by
  have h := Ideal.absNorm_span_natCast (S := 𝓞 K) 127
  rw [RingOfIntegers.rank, finrank_K] at h
  simpa using h

/-! ## Primes are nonzero and coprime when distinct -/

lemma prime_ne_bot {p : Ideal (𝓞 K)} (hp : Prime p) : p ≠ ⊥ := hp.ne_zero

/-- Distinct nonzero primes of `𝓞 K` are coprime (they are maximal). -/
lemma isCoprime_of_prime_ne {p q : Ideal (𝓞 K)} (hp : Prime p) (hq : Prime q) (hne : p ≠ q) :
    IsCoprime p q := by
  have hpm : p.IsMaximal := (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero
  have hqm : q.IsMaximal := (Ideal.isPrime_of_prime hq).isMaximal hq.ne_zero
  exact Ideal.isCoprime_iff_sup_eq.mpr (Ideal.IsMaximal.coprime_of_ne hpm hqm hne)

/-- Primes with different norms are distinct. -/
lemma prime_ne_of_absNorm_ne {p q : Ideal (𝓞 K)}
    (h : Ideal.absNorm p ≠ Ideal.absNorm q) : p ≠ q := fun he => h (he ▸ rfl)

/-- Coprimality from distinct norms. -/
lemma coprime_of_absNorm_ne {p q : Ideal (𝓞 K)} (hp : Prime p) (hq : Prime q)
    (h : Ideal.absNorm p ≠ Ideal.absNorm q) : IsCoprime p q :=
  isCoprime_of_prime_ne hp hq (prime_ne_of_absNorm_ne h)

/-- `Σ(p) = 1 + N(p)` for a prime `p`. -/
lemma sigmaIdeal_prime {p : Ideal (𝓞 K)} (hp : Prime p) :
    sigmaIdeal p = 1 + Ideal.absNorm p := by
  have h := sigmaIdeal_prime_pow hp 1
  rw [pow_one] at h
  rw [h]
  simp [Finset.sum_range_succ]

/-! ## 3. The four perfect ideals (Note L385, L389)

Her theorem (Note L385), quoted verbatim:
"**Theorem (The four perfect ideals of ℤ[φ], KL16).** Exhaustive to norm 10¹⁰, there are exactly four
perfect ideals in ℤ[φ]. All four have N(𝔞)=3,928,320, and they form two σ-orbits of length two. σ moves
every one of them; not one is fixed."

The four (Note L389): `𝔞₁=(2)⁴(3)(√5)𝔭₁₁𝔭₃₁`, `𝔞₂=(2)⁴(3)(√5)p̄₁₁p̄₃₁`, `𝔞₃=(2)⁴(3)(√5)𝔭₁₁p̄₃₁`,
`𝔞₄=(2)⁴(3)(√5)p̄₁₁𝔭₃₁`. We prove each is perfect with `N=3,928,320`; exhaustiveness is §6. -/

/-- The common part `(2)⁴·(3)·(√5)` of all four ideals. -/
def base : Ideal (𝓞 K) := span {(2 : 𝓞 K)} ^ 4 * span {(3 : 𝓞 K)} * sd.p5

/-- `𝔞₁ = (2)⁴(3)(√5)𝔭₁₁𝔭₃₁` (Note L390). -/
def a₁ : Ideal (𝓞 K) := base sd * sd.p11 * sd.p31
/-- `𝔞₂ = (2)⁴(3)(√5)p̄₁₁p̄₃₁` (Note L391). -/
def a₂ : Ideal (𝓞 K) := base sd * sd.q11 * sd.q31
/-- `𝔞₃ = (2)⁴(3)(√5)𝔭₁₁p̄₃₁` (Note L392). -/
def a₃ : Ideal (𝓞 K) := base sd * sd.p11 * sd.q31
/-- `𝔞₄ = (2)⁴(3)(√5)p̄₁₁𝔭₃₁` (Note L393). -/
def a₄ : Ideal (𝓞 K) := base sd * sd.q11 * sd.p31

lemma base_ne_bot : base sd ≠ ⊥ := by
  refine mul_ne_zero (mul_ne_zero (pow_ne_zero _ sd.two_inert.ne_zero) sd.three_inert.ne_zero)
    sd.p5_prime.ne_zero

/-- `Σ((2)⁴·(3)·(√5)) = 341·10·6 = 20460`. -/
lemma sigmaIdeal_base : sigmaIdeal (base sd) = 20460 := by
  have hcop23 : IsCoprime (span {(2 : 𝓞 K)} ^ 4) (span {(3 : 𝓞 K)}) :=
    (coprime_of_absNorm_ne sd.two_inert sd.three_inert
      (by rw [absNorm_span_two, absNorm_span_three]; decide)).pow_left
  have hcop2_5 : IsCoprime (span {(2 : 𝓞 K)}) sd.p5 :=
    coprime_of_absNorm_ne sd.two_inert sd.p5_prime (by rw [absNorm_span_two, sd.p5_norm]; decide)
  have hcop3_5 : IsCoprime (span {(3 : 𝓞 K)}) sd.p5 :=
    coprime_of_absNorm_ne sd.three_inert sd.p5_prime (by rw [absNorm_span_three, sd.p5_norm]; decide)
  have hcop_base5 : IsCoprime (span {(2 : 𝓞 K)} ^ 4 * span {(3 : 𝓞 K)}) sd.p5 :=
    IsCoprime.mul_left hcop2_5.pow_left hcop3_5
  have h23ne : span {(2 : 𝓞 K)} ^ 4 * span {(3 : 𝓞 K)} ≠ ⊥ :=
    mul_ne_zero (pow_ne_zero _ sd.two_inert.ne_zero) sd.three_inert.ne_zero
  unfold base
  rw [sigmaIdeal_mul_coprime h23ne sd.p5_prime.ne_zero hcop_base5,
    sigmaIdeal_mul_coprime (pow_ne_zero _ sd.two_inert.ne_zero) sd.three_inert.ne_zero hcop23,
    sigmaIdeal_prime_pow sd.two_inert, sigmaIdeal_prime sd.three_inert, sigmaIdeal_prime sd.p5_prime,
    absNorm_span_two, absNorm_span_three, sd.p5_norm]
  norm_num [Finset.sum_range_succ]

/-- `N((2)⁴·(3)·(√5)) = 4⁴·9·5 = 11520`. -/
lemma absNorm_base : Ideal.absNorm (base sd) = 11520 := by
  unfold base
  rw [map_mul, map_mul, map_pow, absNorm_span_two, absNorm_span_three, sd.p5_norm]
  norm_num

/-- The abstract perfect ideal: for primes `x` of norm `11` and `y` of norm `31`, both distinct from
the base primes `2, 3, 5` and from each other, `base·x·y` is perfect with norm `3,928,320`. This is the
engine behind all four of `𝔞₁..𝔞₄` (Note L398: `N=3,928,320`, `Σ=7,856,640`, `I=2`). -/
lemma perfect_base_mul {x y : Ideal (𝓞 K)} (hx : Prime x) (hxn : Ideal.absNorm x = 11)
    (hy : Prime y) (hyn : Ideal.absNorm y = 31) :
    sigmaIdeal (base sd * x * y) = 7856640 ∧ Ideal.absNorm (base sd * x * y) = 3928320 := by
  -- coprimality of `x` and `y` with the base and each other, from distinct norms
  have hb2 : IsCoprime (span {(2 : 𝓞 K)}) x :=
    coprime_of_absNorm_ne sd.two_inert hx (by rw [absNorm_span_two, hxn]; decide)
  have hb3 : IsCoprime (span {(3 : 𝓞 K)}) x :=
    coprime_of_absNorm_ne sd.three_inert hx (by rw [absNorm_span_three, hxn]; decide)
  have hb5 : IsCoprime sd.p5 x :=
    coprime_of_absNorm_ne sd.p5_prime hx (by rw [sd.p5_norm, hxn]; decide)
  have hby2 : IsCoprime (span {(2 : 𝓞 K)}) y :=
    coprime_of_absNorm_ne sd.two_inert hy (by rw [absNorm_span_two, hyn]; decide)
  have hby3 : IsCoprime (span {(3 : 𝓞 K)}) y :=
    coprime_of_absNorm_ne sd.three_inert hy (by rw [absNorm_span_three, hyn]; decide)
  have hby5 : IsCoprime sd.p5 y :=
    coprime_of_absNorm_ne sd.p5_prime hy (by rw [sd.p5_norm, hyn]; decide)
  have hxy : IsCoprime x y := coprime_of_absNorm_ne hx hy (by rw [hxn, hyn]; decide)
  have hbasex : IsCoprime (base sd) x := by
    unfold base
    exact IsCoprime.mul_left (IsCoprime.mul_left hb2.pow_left hb3) hb5
  have hbasey : IsCoprime (base sd) y := by
    unfold base
    exact IsCoprime.mul_left (IsCoprime.mul_left hby2.pow_left hby3) hby5
  have hbasexy : IsCoprime (base sd * x) y := IsCoprime.mul_left hbasey hxy
  have hbx_ne : base sd * x ≠ ⊥ := mul_ne_zero (base_ne_bot sd) hx.ne_zero
  refine ⟨?_, ?_⟩
  · rw [sigmaIdeal_mul_coprime hbx_ne hy.ne_zero hbasexy,
      sigmaIdeal_mul_coprime (base_ne_bot sd) hx.ne_zero hbasex,
      sigmaIdeal_base sd, sigmaIdeal_prime hx, sigmaIdeal_prime hy, hxn, hyn]
  · rw [map_mul, map_mul, absNorm_base sd, hxn, hyn]

lemma a₁_perfect : IsPerfect (a₁ sd) := by
  have h := perfect_base_mul sd sd.p11_prime sd.p11_norm sd.p31_prime sd.p31_norm
  unfold IsPerfect a₁
  rw [h.1, h.2]

lemma a₂_perfect : IsPerfect (a₂ sd) := by
  have h := perfect_base_mul sd sd.q11_prime sd.q11_norm sd.q31_prime sd.q31_norm
  unfold IsPerfect a₂
  rw [h.1, h.2]

lemma a₃_perfect : IsPerfect (a₃ sd) := by
  have h := perfect_base_mul sd sd.p11_prime sd.p11_norm sd.q31_prime sd.q31_norm
  unfold IsPerfect a₃
  rw [h.1, h.2]

lemma a₄_perfect : IsPerfect (a₄ sd) := by
  have h := perfect_base_mul sd sd.q11_prime sd.q11_norm sd.p31_prime sd.p31_norm
  unfold IsPerfect a₄
  rw [h.1, h.2]

lemma a₁_norm : Ideal.absNorm (a₁ sd) = 3928320 :=
  (perfect_base_mul sd sd.p11_prime sd.p11_norm sd.p31_prime sd.p31_norm).2
lemma a₂_norm : Ideal.absNorm (a₂ sd) = 3928320 :=
  (perfect_base_mul sd sd.q11_prime sd.q11_norm sd.q31_prime sd.q31_norm).2
lemma a₃_norm : Ideal.absNorm (a₃ sd) = 3928320 :=
  (perfect_base_mul sd sd.p11_prime sd.p11_norm sd.q31_prime sd.q31_norm).2
lemma a₄_norm : Ideal.absNorm (a₄ sd) = 3928320 :=
  (perfect_base_mul sd sd.q11_prime sd.q11_norm sd.p31_prime sd.p31_norm).2

/-- **KL16, part 1 (Note L385).** The four explicit ideals of §2.4 are all perfect, each of norm
`3,928,320` (`N = 4⁴·9·5·11·31`, `Σ = 341·10·6·12·32 = 7,856,640 = 2N`). -/
theorem four_perfect_ideals :
    (IsPerfect (a₁ sd) ∧ IsPerfect (a₂ sd) ∧ IsPerfect (a₃ sd) ∧ IsPerfect (a₄ sd)) ∧
    (Ideal.absNorm (a₁ sd) = 3928320 ∧ Ideal.absNorm (a₂ sd) = 3928320 ∧
      Ideal.absNorm (a₃ sd) = 3928320 ∧ Ideal.absNorm (a₄ sd) = 3928320) :=
  ⟨⟨a₁_perfect sd, a₂_perfect sd, a₃_perfect sd, a₄_perfect sd⟩,
    ⟨a₁_norm sd, a₂_norm sd, a₃_norm sd, a₄_norm sd⟩⟩

/-! ## 4. The two σ-orbits of length two (Note L385, L396)

Note L396: "Aligned: σ:𝔞₁↔𝔞₂. Crossed: σ:𝔞₃↔𝔞₄." `σ` fixes `(2), (3), (√5)` and swaps the split
conjugates `𝔭₁₁↔p̄₁₁`, `𝔭₃₁↔p̄₃₁` (`SplittingData.conj_*`). So the four fall into two orbits of length
two; `σ` moves every one of them, and none is fixed. -/

/-- `σ` fixes the common base `(2)⁴·(3)·(√5)`. -/
lemma conjIdeal_base : conjIdeal (base sd) = base sd := by
  unfold base
  rw [conjIdeal_mul, conjIdeal_mul, conjIdeal_pow,
    conjIdeal_span_fixed (sigma_ofNat_fixed 2), conjIdeal_span_fixed (sigma_ofNat_fixed 3),
    sd.conj_p5]

/-- `σ` swaps the split conjugates back: `σ(p̄₁₁) = 𝔭₁₁` (the inverse of `conj_p11`). -/
lemma conjIdeal_q11 : conjIdeal sd.q11 = sd.p11 := by
  rw [← sd.conj_p11, conjIdeal_conjIdeal]

lemma conjIdeal_q31 : conjIdeal sd.q31 = sd.p31 := by
  rw [← sd.conj_p31, conjIdeal_conjIdeal]

lemma conjIdeal_a₁ : conjIdeal (a₁ sd) = a₂ sd := by
  unfold a₁ a₂
  rw [conjIdeal_mul, conjIdeal_mul, conjIdeal_base, sd.conj_p11, sd.conj_p31]

lemma conjIdeal_a₃ : conjIdeal (a₃ sd) = a₄ sd := by
  unfold a₃ a₄
  rw [conjIdeal_mul, conjIdeal_mul, conjIdeal_base, sd.conj_p11, conjIdeal_q31 sd]

lemma conjIdeal_a₂ : conjIdeal (a₂ sd) = a₁ sd := by
  have := conjIdeal_a₁ sd
  rw [← this, conjIdeal_conjIdeal]

lemma conjIdeal_a₄ : conjIdeal (a₄ sd) = a₃ sd := by
  have := conjIdeal_a₃ sd
  rw [← this, conjIdeal_conjIdeal]

/-- A prime dividing a prime equals it: two nonzero primes are maximal, so `q ≤ r` forces `r = q`. -/
lemma prime_dvd_prime_eq {r q : Ideal (𝓞 K)} (hr : Prime r) (hq : Prime q) (h : r ∣ q) : r = q :=
  (((Ideal.isPrime_of_prime hq).isMaximal hq.ne_zero).eq_of_le
    (Ideal.isPrime_of_prime hr).ne_top (Ideal.dvd_iff_le.mp h)).symm

/-- A prime of norm `∉ {4, 9, 5}` does not divide the base `(2)⁴·(3)·(√5)`. -/
lemma not_dvd_base {r : Ideal (𝓞 K)} (hr : Prime r) (h2 : Ideal.absNorm r ≠ 4)
    (h3 : Ideal.absNorm r ≠ 9) (h5 : Ideal.absNorm r ≠ 5) : ¬ r ∣ base sd := by
  intro h
  unfold base at h
  rcases hr.dvd_mul.mp h with h' | h'
  · rcases hr.dvd_mul.mp h' with h'' | h''
    · exact h2 (by rw [prime_dvd_prime_eq hr sd.two_inert (hr.dvd_of_dvd_pow h''),
        absNorm_span_two])
    · exact h3 (by rw [prime_dvd_prime_eq hr sd.three_inert h'', absNorm_span_three])
  · exact h5 (by rw [prime_dvd_prime_eq hr sd.p5_prime h', sd.p5_norm])

/-- A prime `r ∉ base` with `r ≠ x` and `r ≠ y` (all prime) does not divide `base·x·y`. -/
lemma not_dvd_base_mul {r x y : Ideal (𝓞 K)} (hr : Prime r) (hnb : ¬ r ∣ base sd)
    (hx : Prime x) (hy : Prime y) (hrx : r ≠ x) (hry : r ≠ y) : ¬ r ∣ base sd * x * y := by
  intro h
  rcases hr.dvd_mul.mp h with h' | h'
  · rcases hr.dvd_mul.mp h' with h'' | h''
    · exact hnb h''
    · exact hrx (prime_dvd_prime_eq hr hx h'')
  · exact hry (prime_dvd_prime_eq hr hy h')

/-- `𝔭₁₁` does not divide the base (its norm is `11 ∉ {4,9,5}`). -/
lemma p11_not_dvd_base : ¬ sd.p11 ∣ base sd :=
  not_dvd_base sd sd.p11_prime (by rw [sd.p11_norm]; decide) (by rw [sd.p11_norm]; decide)
    (by rw [sd.p11_norm]; decide)
lemma q11_not_dvd_base : ¬ sd.q11 ∣ base sd :=
  not_dvd_base sd sd.q11_prime (by rw [sd.q11_norm]; decide) (by rw [sd.q11_norm]; decide)
    (by rw [sd.q11_norm]; decide)
lemma p31_not_dvd_base : ¬ sd.p31 ∣ base sd :=
  not_dvd_base sd sd.p31_prime (by rw [sd.p31_norm]; decide) (by rw [sd.p31_norm]; decide)
    (by rw [sd.p31_norm]; decide)
lemma q31_not_dvd_base : ¬ sd.q31 ∣ base sd :=
  not_dvd_base sd sd.q31_prime (by rw [sd.q31_norm]; decide) (by rw [sd.q31_norm]; decide)
    (by rw [sd.q31_norm]; decide)

/-- `𝔭₁₁ ≠ 𝔭₃₁` (distinct norms `11 ≠ 31`), etc. -/
lemma p11_ne_p31 : sd.p11 ≠ sd.p31 := prime_ne_of_absNorm_ne (by rw [sd.p11_norm, sd.p31_norm]; decide)
lemma p11_ne_q31 : sd.p11 ≠ sd.q31 := prime_ne_of_absNorm_ne (by rw [sd.p11_norm, sd.q31_norm]; decide)
lemma q11_ne_p31 : sd.q11 ≠ sd.p31 := prime_ne_of_absNorm_ne (by rw [sd.q11_norm, sd.p31_norm]; decide)
lemma q11_ne_p11 : sd.q11 ≠ sd.p11 := (sd.p11_ne_q11).symm
lemma q11_ne_q31 : sd.q11 ≠ sd.q31 := prime_ne_of_absNorm_ne (by rw [sd.q11_norm, sd.q31_norm]; decide)
lemma q31_ne_p31 : sd.q31 ≠ sd.p31 := (sd.p31_ne_q31).symm

/-- `𝔞₁ ≠ 𝔞₂`: `𝔭₁₁ ∣ 𝔞₁` but `𝔭₁₁ ∤ 𝔞₂`. -/
lemma a₁_ne_a₂ : a₁ sd ≠ a₂ sd := by
  intro he
  have hd : sd.p11 ∣ a₁ sd := (dvd_mul_left sd.p11 (base sd)).mul_right sd.p31
  rw [he] at hd
  exact not_dvd_base_mul sd sd.p11_prime (p11_not_dvd_base sd) sd.q11_prime sd.q31_prime
    sd.p11_ne_q11 (p11_ne_q31 sd) hd

/-- `𝔞₃ ≠ 𝔞₄`: `𝔭₁₁ ∣ 𝔞₃` but `𝔭₁₁ ∤ 𝔞₄`. -/
lemma a₃_ne_a₄ : a₃ sd ≠ a₄ sd := by
  intro he
  have hd : sd.p11 ∣ a₃ sd := (dvd_mul_left sd.p11 (base sd)).mul_right sd.q31
  rw [he] at hd
  exact not_dvd_base_mul sd sd.p11_prime (p11_not_dvd_base sd) sd.q11_prime sd.p31_prime
    sd.p11_ne_q11 (p11_ne_p31 sd) hd

/-- `𝔞₁ ≠ 𝔞₃`: `𝔭₃₁ ∣ 𝔞₁` but `𝔭₃₁ ∤ 𝔞₃`. -/
lemma a₁_ne_a₃ : a₁ sd ≠ a₃ sd := by
  intro he
  have hd : sd.p31 ∣ a₁ sd := dvd_mul_left sd.p31 (base sd * sd.p11)
  rw [he] at hd
  exact not_dvd_base_mul sd sd.p31_prime (p31_not_dvd_base sd) sd.p11_prime sd.q31_prime
    (p11_ne_p31 sd).symm sd.p31_ne_q31 hd

/-- `𝔞₁ ≠ 𝔞₄`: `𝔭₁₁ ∣ 𝔞₁` but `𝔭₁₁ ∤ 𝔞₄ = base·p̄₁₁·𝔭₃₁`. -/
lemma a₁_ne_a₄ : a₁ sd ≠ a₄ sd := by
  intro he
  have hd : sd.p11 ∣ a₁ sd := (dvd_mul_left sd.p11 (base sd)).mul_right sd.p31
  rw [he] at hd
  exact not_dvd_base_mul sd sd.p11_prime (p11_not_dvd_base sd) sd.q11_prime sd.p31_prime
    sd.p11_ne_q11 (p11_ne_p31 sd) hd

/-- `𝔞₂ ≠ 𝔞₃`: `p̄₁₁ ∣ 𝔞₂` but `p̄₁₁ ∤ 𝔞₃`. -/
lemma a₂_ne_a₃ : a₂ sd ≠ a₃ sd := by
  intro he
  have hd : sd.q11 ∣ a₂ sd := (dvd_mul_left sd.q11 (base sd)).mul_right sd.q31
  rw [he] at hd
  exact not_dvd_base_mul sd sd.q11_prime (q11_not_dvd_base sd) sd.p11_prime sd.q31_prime
    (q11_ne_p11 sd) (q11_ne_q31 sd) hd

/-- `𝔞₂ ≠ 𝔞₄`: `p̄₃₁ ∣ 𝔞₂` but `p̄₃₁ ∤ 𝔞₄ = base·p̄₁₁·𝔭₃₁`. -/
lemma a₂_ne_a₄ : a₂ sd ≠ a₄ sd := by
  intro he
  have hd : sd.q31 ∣ a₂ sd := dvd_mul_left sd.q31 (base sd * sd.q11)
  rw [he] at hd
  exact not_dvd_base_mul sd sd.q31_prime (q31_not_dvd_base sd) sd.q11_prime sd.p31_prime
    ((q11_ne_q31 sd).symm) (q31_ne_p31 sd) hd

/-- **KL16, part 2 (Note L385, L396).** The four ideals form two σ-orbits of length two: `σ` swaps
`𝔞₁ ↔ 𝔞₂` (aligned) and `𝔞₃ ↔ 𝔞₄` (crossed), the four are pairwise distinct, and `σ` moves every one
of them — not one is fixed. -/
theorem sigma_orbits :
    -- orbit 1: `σ : 𝔞₁ ↔ 𝔞₂`, length two
    (conjIdeal (a₁ sd) = a₂ sd ∧ conjIdeal (a₂ sd) = a₁ sd ∧ a₁ sd ≠ a₂ sd) ∧
    -- orbit 2: `σ : 𝔞₃ ↔ 𝔞₄`, length two
    (conjIdeal (a₃ sd) = a₄ sd ∧ conjIdeal (a₄ sd) = a₃ sd ∧ a₃ sd ≠ a₄ sd) ∧
    -- the two orbits are distinct (the four are pairwise distinct)
    (a₁ sd ≠ a₃ sd ∧ a₁ sd ≠ a₄ sd ∧ a₂ sd ≠ a₃ sd ∧ a₂ sd ≠ a₄ sd) ∧
    -- σ moves every one of them: none is fixed
    (conjIdeal (a₁ sd) ≠ a₁ sd ∧ conjIdeal (a₂ sd) ≠ a₂ sd ∧
      conjIdeal (a₃ sd) ≠ a₃ sd ∧ conjIdeal (a₄ sd) ≠ a₄ sd) := by
  refine ⟨⟨conjIdeal_a₁ sd, conjIdeal_a₂ sd, a₁_ne_a₂ sd⟩,
    ⟨conjIdeal_a₃ sd, conjIdeal_a₄ sd, a₃_ne_a₄ sd⟩,
    ⟨a₁_ne_a₃ sd, a₁_ne_a₄ sd, a₂_ne_a₃ sd, a₂_ne_a₄ sd⟩, ?_, ?_, ?_, ?_⟩
  · rw [conjIdeal_a₁]; exact (a₁_ne_a₂ sd).symm
  · rw [conjIdeal_a₂]; exact a₁_ne_a₂ sd
  · rw [conjIdeal_a₃]; exact (a₃_ne_a₄ sd).symm
  · rw [conjIdeal_a₄]; exact a₃_ne_a₄ sd

/-! ## 5. The classical perfect numbers do not lift (Note L404)

Note L404: "6, 28, 496 and 8128 all have abundancy index ≠2 in this ring, because 2, 3 and 7 are
inert." We compute `Σ((n))` and `N((n))` for `n = 6, 28, 496, 8128` and check `Σ ≠ 2N` in each case
(Note L406 records the exact fractions). `496 = 2⁴·31` uses the splitting of `31`; the others use
inert `2, 3, 7, 127`. -/

-- The remaining results all consume the splitting data `sd` only in their proofs, so include it.
include sd

/-- `(6) = (2)·(3)`, `Σ = 50`, `N = 36`, so `I = 25/18 ≠ 2` (Note L406). -/
theorem six_not_perfect : ¬ IsPerfect (span {(6 : 𝓞 K)}) := by
  have hsplit : span {(6 : 𝓞 K)} = span {(2 : 𝓞 K)} * span {(3 : 𝓞 K)} := by
    rw [Ideal.span_singleton_mul_span_singleton]; norm_num
  have hcop : IsCoprime (span {(2 : 𝓞 K)}) (span {(3 : 𝓞 K)}) :=
    coprime_of_absNorm_ne sd.two_inert sd.three_inert
      (by rw [absNorm_span_two, absNorm_span_three]; decide)
  unfold IsPerfect
  rw [hsplit, sigmaIdeal_mul_coprime sd.two_inert.ne_zero sd.three_inert.ne_zero hcop,
    sigmaIdeal_prime sd.two_inert, sigmaIdeal_prime sd.three_inert, map_mul,
    absNorm_span_two, absNorm_span_three]
  decide

/-- `(28) = (2)²·(7)`, `Σ = 1050`, `N = 784`, so `I = 75/56 ≠ 2` (Note L406). -/
theorem twentyeight_not_perfect : ¬ IsPerfect (span {(28 : 𝓞 K)}) := by
  have hsplit : span {(28 : 𝓞 K)} = span {(2 : 𝓞 K)} ^ 2 * span {(7 : 𝓞 K)} := by
    rw [Ideal.span_singleton_pow, Ideal.span_singleton_mul_span_singleton]; norm_num
  have hcop : IsCoprime (span {(2 : 𝓞 K)} ^ 2) (span {(7 : 𝓞 K)}) :=
    (coprime_of_absNorm_ne sd.two_inert sd.seven_inert
      (by rw [absNorm_span_two, absNorm_span_seven]; decide)).pow_left
  unfold IsPerfect
  rw [hsplit,
    sigmaIdeal_mul_coprime (pow_ne_zero _ sd.two_inert.ne_zero) sd.seven_inert.ne_zero hcop,
    sigmaIdeal_prime_pow sd.two_inert, sigmaIdeal_prime sd.seven_inert, map_mul, map_pow,
    absNorm_span_two, absNorm_span_seven]
  norm_num [Finset.sum_range_succ]

/-- `(496) = (2)⁴·𝔭₃₁·p̄₃₁` (31 splits), `Σ = 349184`, `N = 246016`, `I = 44/31 ≠ 2` (Note L406). -/
theorem fourninetysix_not_perfect : ¬ IsPerfect (span {(496 : 𝓞 K)}) := by
  have hsplit : span {(496 : 𝓞 K)} = span {(2 : 𝓞 K)} ^ 4 * (sd.p31 * sd.q31) := by
    rw [← sd.thirtyone_splits, Ideal.span_singleton_pow, Ideal.span_singleton_mul_span_singleton]
    norm_num
  have h31ne : sd.p31 * sd.q31 ≠ ⊥ := mul_ne_zero sd.p31_prime.ne_zero sd.q31_prime.ne_zero
  have hcop2_31 : IsCoprime (span {(2 : 𝓞 K)} ^ 4) (sd.p31 * sd.q31) :=
    (IsCoprime.mul_right
      (coprime_of_absNorm_ne sd.two_inert sd.p31_prime (by rw [absNorm_span_two, sd.p31_norm]; decide))
      (coprime_of_absNorm_ne sd.two_inert sd.q31_prime
        (by rw [absNorm_span_two, sd.q31_norm]; decide))).pow_left
  have hcop31 : IsCoprime sd.p31 sd.q31 :=
    isCoprime_of_prime_ne sd.p31_prime sd.q31_prime sd.p31_ne_q31
  unfold IsPerfect
  rw [hsplit,
    sigmaIdeal_mul_coprime (pow_ne_zero _ sd.two_inert.ne_zero) h31ne hcop2_31,
    sigmaIdeal_mul_coprime sd.p31_prime.ne_zero sd.q31_prime.ne_zero hcop31,
    sigmaIdeal_prime_pow sd.two_inert, sigmaIdeal_prime sd.p31_prime, sigmaIdeal_prime sd.q31_prime,
    map_mul, map_mul, map_pow, absNorm_span_two, sd.p31_norm, sd.q31_norm]
  norm_num [Finset.sum_range_succ]

/-- `(8128) = (2)⁶·(127)`, `Σ = 88085930`, `N = 66064384`, `I ≠ 2` (Note L406). -/
theorem eightonetwoeight_not_perfect : ¬ IsPerfect (span {(8128 : 𝓞 K)}) := by
  have hsplit : span {(8128 : 𝓞 K)} = span {(2 : 𝓞 K)} ^ 6 * span {(127 : 𝓞 K)} := by
    rw [Ideal.span_singleton_pow, Ideal.span_singleton_mul_span_singleton]; norm_num
  have hcop : IsCoprime (span {(2 : 𝓞 K)} ^ 6) (span {(127 : 𝓞 K)}) :=
    (coprime_of_absNorm_ne sd.two_inert sd.onetwoseven_inert
      (by rw [absNorm_span_two, absNorm_span_onetwoseven]; decide)).pow_left
  unfold IsPerfect
  rw [hsplit,
    sigmaIdeal_mul_coprime (pow_ne_zero _ sd.two_inert.ne_zero) sd.onetwoseven_inert.ne_zero hcop,
    sigmaIdeal_prime_pow sd.two_inert, sigmaIdeal_prime sd.onetwoseven_inert, map_mul, map_pow,
    absNorm_span_two, absNorm_span_onetwoseven]
  norm_num [Finset.sum_range_succ]

/-- **KL16, part 3 (Note L404).** The classical perfect numbers `6, 28, 496, 8128` do not lift: none
of `(6), (28), (496), (8128)` is a perfect ideal of ℤ[φ]. -/
theorem classical_perfect_numbers_do_not_lift :
    ¬ IsPerfect (span {(6 : 𝓞 K)}) ∧ ¬ IsPerfect (span {(28 : 𝓞 K)}) ∧
    ¬ IsPerfect (span {(496 : 𝓞 K)}) ∧ ¬ IsPerfect (span {(8128 : 𝓞 K)}) :=
  ⟨six_not_perfect sd, twentyeight_not_perfect sd, fourninetysix_not_perfect sd,
    eightonetwoeight_not_perfect sd⟩

/-! ## 6. The frontier: "exactly four / exhaustive to 10¹⁰" (Note L385, L412)

Note L412 ("What is not established"): "The search reached norm 10¹⁰ and no further. Only k=4 closes
across the bases tested. No theorem asserts that more exist." Her Note gives **no search procedure**, so
"exactly four" is the unproven frontier. It is stated here as a `Prop`-valued hypothesis — NEVER a
`sorry`/`admit`/axiom — clearly labelled. Exhibiting and proving the four (above), with exhaustiveness
as this named hypothesis, is the deliverable; the `10¹⁰` search is deferred work (`kl16-exhaustive-b`). -/

/-- The unproven frontier (Note L385/L412): exhaustive to norm `10¹⁰`, the four exhibited ideals are
**all** the perfect ideals of ℤ[φ] at norm `≤ B`. A displayed hypothesis, not a theorem: her Note gives
no search procedure. -/
def ExhaustiveToBound (B : ℕ) : Prop :=
  ∀ I : Ideal (𝓞 K), I ≠ ⊥ → Ideal.absNorm I ≤ B → IsPerfect I →
    I = a₁ sd ∨ I = a₂ sd ∨ I = a₃ sd ∨ I = a₄ sd

/-- **KL16 (Note L385), assembled.** Conditional on the exhaustiveness frontier
`ExhaustiveToBound (10¹⁰)` (which the Note states without a search procedure), the perfect ideals of
ℤ[φ] of norm `≤ 10¹⁰` are exactly the four exhibited, all of norm `3,928,320`, forming two σ-orbits of
length two with none fixed; and the classical perfect numbers do not lift. The four and their structure
are proved unconditionally above (`four_perfect_ideals`, `sigma_orbits`,
`classical_perfect_numbers_do_not_lift`); only "exactly these four" rests on the frontier. -/
theorem KL16_four_perfect_ideals (hExh : ExhaustiveToBound sd (10 ^ 10)) :
    -- the four are perfect, of norm 3,928,320
    (IsPerfect (a₁ sd) ∧ IsPerfect (a₂ sd) ∧ IsPerfect (a₃ sd) ∧ IsPerfect (a₄ sd)) ∧
    -- they are exactly the perfect ideals of norm ≤ 10¹⁰ (conditional on the frontier)
    (∀ I : Ideal (𝓞 K), I ≠ ⊥ → Ideal.absNorm I ≤ 10 ^ 10 → IsPerfect I →
      I = a₁ sd ∨ I = a₂ sd ∨ I = a₃ sd ∨ I = a₄ sd) ∧
    -- two σ-orbits of length two, none fixed
    (conjIdeal (a₁ sd) = a₂ sd ∧ conjIdeal (a₃ sd) = a₄ sd ∧
      a₁ sd ≠ a₂ sd ∧ a₃ sd ≠ a₄ sd) :=
  ⟨(four_perfect_ideals sd).1, hExh,
    ⟨conjIdeal_a₁ sd, conjIdeal_a₃ sd, a₁_ne_a₂ sd, a₃_ne_a₄ sd⟩⟩

end ExistenceSystem.KL16

end
