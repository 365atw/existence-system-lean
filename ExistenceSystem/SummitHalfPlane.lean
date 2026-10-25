module

/-
SUMMIT — `halfPlane`: `ζ_K(s) = ζ(s) L(s, χ_{−20})` for `1 < Re s`.

`dedekindZeta K` is the L-series of `n ↦ #{I : absNorm I = n}`. That count is
multiplicative, and the splitting law gives its value at `p ^ k`: `k + 1` for a split
prime, `1` or `0` (as `k` is even or odd) for an inert prime, `1` for `2` and `5`. Those
are the values of `ζ * χ_{−20}` (Mathlib's `zetaMul`), so the two L-series agree.
-/

public import ExistenceSystem.Summit
public import Mathlib.NumberTheory.LSeries.Nonvanishing

@[expose] public section

noncomputable section

open Ideal NumberField

namespace ExistenceSystem.Summit

open ExistenceSystem.TheThing

/-! ## The ideal count is multiplicative -/

/-- `#{I : absNorm I = n}`. -/
def idealCount (n : ℕ) : ℕ := Nat.card {I : Ideal (𝓞 K) // absNorm I = n}

lemma absNorm_natSpan (n : ℕ) : absNorm (span {(n : 𝓞 K)}) = n ^ 2 := by
  have h := absNorm_span_natCast (S := 𝓞 K) n
  rw [RingOfIntegers.rank, finrank_K] at h
  simpa using h

lemma natCast_mem_of_absNorm {I : Ideal (𝓞 K)} {n : ℕ} (h : absNorm I = n) :
    (n : 𝓞 K) ∈ I := h ▸ absNorm_mem I

lemma sup_eq_top_of_coprime {A B : Ideal (𝓞 K)} (h : Nat.Coprime (absNorm A) (absNorm B)) :
    A ⊔ B = ⊤ := by
  have hA : absNorm (A ⊔ B) ∣ absNorm A := absNorm_dvd_absNorm_of_le (le_sup_left : A ≤ A ⊔ B)
  have hB : absNorm (A ⊔ B) ∣ absNorm B := absNorm_dvd_absNorm_of_le (le_sup_right : B ≤ A ⊔ B)
  exact absNorm_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes h hA hB)

lemma natSpan_le {I : Ideal (𝓞 K)} {n : ℕ} (h : absNorm I = n) : span {(n : 𝓞 K)} ≤ I :=
  (span_singleton_le_iff_mem I).2 (natCast_mem_of_absNorm h)

/-- `I J ⊔ (m) = I` when `absNorm I = m`, `absNorm J = n`, `m` and `n` coprime. -/
lemma mul_sup_natSpan {I J : Ideal (𝓞 K)} {m n : ℕ} (hmn : Nat.Coprime m n)
    (hI : absNorm I = m) (hJ : absNorm J = n) : I * J ⊔ span {(m : 𝓞 K)} = I := by
  apply le_antisymm (sup_le Ideal.mul_le_left (natSpan_le hI))
  have htop : J ⊔ span {(m : 𝓞 K)} = ⊤ := by
    apply sup_eq_top_of_coprime
    rw [hJ, absNorm_natSpan]
    exact (Nat.Coprime.pow_right 2 hmn.symm)
  calc I = I * (J ⊔ span {(m : 𝓞 K)}) := by rw [htop, mul_top]
    _ = I * J ⊔ I * span {(m : 𝓞 K)} := Ideal.mul_sup _ _ _
    _ ≤ I * J ⊔ span {(m : 𝓞 K)} := sup_le_sup_left Ideal.mul_le_right _

lemma natSpan_sup_eq_top {m n : ℕ} (hmn : Nat.Coprime m n) :
    span {(m : 𝓞 K)} ⊔ span {(n : 𝓞 K)} = ⊤ := by
  apply sup_eq_top_of_coprime
  rw [absNorm_natSpan, absNorm_natSpan]
  exact Nat.Coprime.pow 2 2 hmn

/-- `(K ⊔ (m)) (K ⊔ (n)) = K` when `absNorm K = m n` with `m`, `n` coprime. -/
lemma sup_mul_sup_eq {L : Ideal (𝓞 K)} {m n : ℕ} (hmn : Nat.Coprime m n)
    (hL : absNorm L = m * n) :
    (L ⊔ span {(m : 𝓞 K)}) * (L ⊔ span {(n : 𝓞 K)}) = L := by
  apply le_antisymm
  · rw [Ideal.sup_mul, Ideal.mul_sup, Ideal.mul_sup]
    refine sup_le (sup_le Ideal.mul_le_left Ideal.mul_le_left) (sup_le Ideal.mul_le_right ?_)
    rw [span_singleton_mul_span_singleton, span_singleton_le_iff_mem]
    have := natCast_mem_of_absNorm hL
    simpa using this
  · calc L = L * (span {(m : 𝓞 K)} ⊔ span {(n : 𝓞 K)}) := by
          rw [natSpan_sup_eq_top hmn, mul_top]
      _ = L * span {(m : 𝓞 K)} ⊔ L * span {(n : 𝓞 K)} := Ideal.mul_sup _ _ _
      _ ≤ _ := by
          refine sup_le ?_ ?_
          · rw [mul_comm]
            exact mul_mono le_sup_right le_sup_left
          · exact mul_mono le_sup_left le_sup_right

lemma absNorm_sup_natSpan {L : Ideal (𝓞 K)} {m n : ℕ} (hmn : Nat.Coprime m n)
    (hm : m ≠ 0) (hn : n ≠ 0) (hL : absNorm L = m * n) :
    absNorm (L ⊔ span {(m : 𝓞 K)}) = m ∧ absNorm (L ⊔ span {(n : 𝓞 K)}) = n := by
  set a := absNorm (L ⊔ span {(m : 𝓞 K)})
  set b := absNorm (L ⊔ span {(n : 𝓞 K)})
  have hab : a * b = m * n := by
    rw [← hL, ← map_mul, sup_mul_sup_eq hmn hL]
  have ha2 : a ∣ m ^ 2 := by
    rw [← absNorm_natSpan]
    exact absNorm_dvd_absNorm_of_le le_sup_right
  have hb2 : b ∣ n ^ 2 := by
    rw [← absNorm_natSpan]
    exact absNorm_dvd_absNorm_of_le le_sup_right
  have ha : a ∣ m := by
    have hcop : Nat.Coprime a n :=
      Nat.Coprime.coprime_dvd_left ha2 (Nat.Coprime.pow_left 2 hmn)
    exact hcop.dvd_of_dvd_mul_right ⟨b, by rw [hab]⟩
  have hb : b ∣ n := by
    have hcop : Nat.Coprime b m :=
      Nat.Coprime.coprime_dvd_left hb2 (Nat.Coprime.pow_left 2 hmn.symm)
    exact hcop.dvd_of_dvd_mul_left ⟨a, by rw [mul_comm b a, hab]⟩
  obtain ⟨c, hc⟩ := ha
  obtain ⟨d, hd⟩ := hb
  have hab0 : a * b ≠ 0 := by rw [hab]; exact mul_ne_zero hm hn
  have hcd : c * d = 1 := by
    have : a * b * (c * d) = a * b * 1 := by
      rw [mul_one]
      calc a * b * (c * d) = (a * c) * (b * d) := by ring
        _ = a * b := by rw [← hc, ← hd, hab]
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hab0) this
  have hc1 : c = 1 := Nat.eq_one_of_mul_eq_one_right hcd
  have hd1 : d = 1 := Nat.eq_one_of_mul_eq_one_left hcd
  exact ⟨by rw [hc, hc1, mul_one], by rw [hd, hd1, mul_one]⟩

/-- Ideals of norm `m n` are products of ideals of norms `m` and `n`, uniquely. -/
def idealMulEquiv {m n : ℕ} (hmn : Nat.Coprime m n) (hm : m ≠ 0) (hn : n ≠ 0) :
    {I : Ideal (𝓞 K) // absNorm I = m} × {J : Ideal (𝓞 K) // absNorm J = n} ≃
      {L : Ideal (𝓞 K) // absNorm L = m * n} where
  toFun IJ := ⟨IJ.1.1 * IJ.2.1, by rw [map_mul, IJ.1.2, IJ.2.2]⟩
  invFun L := (⟨L.1 ⊔ span {(m : 𝓞 K)}, (absNorm_sup_natSpan hmn hm hn L.2).1⟩,
    ⟨L.1 ⊔ span {(n : 𝓞 K)}, (absNorm_sup_natSpan hmn hm hn L.2).2⟩)
  left_inv IJ := by
    obtain ⟨⟨I, hI⟩, ⟨J, hJ⟩⟩ := IJ
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · exact mul_sup_natSpan hmn hI hJ
    · change I * J ⊔ span {(n : 𝓞 K)} = J
      rw [mul_comm]
      exact mul_sup_natSpan hmn.symm hJ hI
  right_inv L := by
    obtain ⟨L, hL⟩ := L
    exact Subtype.ext (sup_mul_sup_eq hmn hL)

theorem idealCount_mul {m n : ℕ} (hmn : Nat.Coprime m n) (hm : m ≠ 0) (hn : n ≠ 0) :
    idealCount (m * n) = idealCount m * idealCount n := by
  rw [idealCount, idealCount, idealCount, ← Nat.card_prod]
  exact (Nat.card_congr (idealMulEquiv hmn hm hn)).symm

/-! ## Ideals of prime-power norm -/

lemma ne_top_of_absNorm_prime_pow {I : Ideal (𝓞 K)} {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0)
    (hI : absNorm I = p ^ k) : I ≠ ⊤ := by
  intro h
  rw [h, absNorm_top] at hI
  exact (Nat.one_lt_pow hk hp.one_lt).ne hI

/-- An ideal of norm `p ^ k`, `k ≠ 0`, is `𝔐 I'` for a maximal ideal `𝔐 ∋ p`. -/
lemma exists_maximal_factor {I : Ideal (𝓞 K)} {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0)
    (hI : absNorm I = p ^ k) :
    ∃ 𝔐 : Ideal (𝓞 K), 𝔐.IsMaximal ∧ span {(p : 𝓞 K)} ≤ 𝔐 ∧ ∃ I', I = 𝔐 * I' := by
  obtain ⟨𝔐, hmax, hle⟩ := exists_le_maximal I (ne_top_of_absNorm_prime_pow hp hk hI)
  refine ⟨𝔐, hmax, ?_, Ideal.dvd_iff_le.2 hle⟩
  rw [span_singleton_le_iff_mem]
  have hmem : ((p ^ k : ℕ) : 𝓞 K) ∈ 𝔐 := hle (natCast_mem_of_absNorm hI)
  rw [Nat.cast_pow] at hmem
  exact hmax.isPrime.mem_of_pow_mem k hmem

lemma isMaximal_of_prime_absNorm {𝔮 : Ideal (𝓞 K)} (hq : 𝔮.IsPrime) {n : ℕ} (hn : n ≠ 0)
    (hN : absNorm 𝔮 = n) : 𝔮.IsMaximal := by
  refine hq.isMaximal ?_
  intro h
  rw [h, absNorm_bot] at hN
  exact hn hN.symm

lemma absNorm_cofactor {𝔐 I' : Ideal (𝓞 K)} {p k : ℕ} (hp : p.Prime)
    (h : absNorm (𝔐 * I') = p ^ (k + 1)) (hM : absNorm 𝔐 = p) : absNorm I' = p ^ k := by
  rw [map_mul, hM, pow_succ, mul_comm (p ^ k)] at h
  exact Nat.eq_of_mul_eq_mul_left hp.pos h

/-- Split prime: ideals of norm `p ^ k` are `𝔮 ^ i 𝔮' ^ (k − i)`. -/
lemma split_classify {p : ℕ} (hp : p.Prime) {𝔮 𝔮' : Ideal (𝓞 K)} (hq : 𝔮.IsPrime)
    (hq' : 𝔮'.IsPrime) (hN : absNorm 𝔮 = p) (hN' : absNorm 𝔮' = p)
    (hprod : 𝔮 * 𝔮' = span {(p : 𝓞 K)}) :
    ∀ (k : ℕ) (I : Ideal (𝓞 K)), absNorm I = p ^ k → ∃ i ≤ k, I = 𝔮 ^ i * 𝔮' ^ (k - i) := by
  have hqm := isMaximal_of_prime_absNorm hq hp.ne_zero hN
  have hqm' := isMaximal_of_prime_absNorm hq' hp.ne_zero hN'
  intro k
  induction k with
  | zero =>
    intro I hI
    refine ⟨0, le_rfl, ?_⟩
    rw [pow_zero, absNorm_eq_one_iff] at hI
    rw [hI, pow_zero, pow_zero, mul_one, Ideal.one_eq_top]
  | succ k ih =>
    intro I hI
    obtain ⟨𝔐, hmax, hle, I', rfl⟩ := exists_maximal_factor hp k.succ_ne_zero hI
    rw [← hprod, hmax.isPrime.mul_le] at hle
    rcases hle with hle | hle
    · have h𝔐 : 𝔮 = 𝔐 := hqm.eq_of_le hmax.ne_top hle
      subst h𝔐
      obtain ⟨i, hik, hI'⟩ := ih I' (absNorm_cofactor hp hI hN)
      refine ⟨i + 1, by omega, ?_⟩
      rw [hI', show k + 1 - (i + 1) = k - i by omega, pow_succ, mul_comm (𝔮 ^ i) 𝔮, mul_assoc]
    · have h𝔐 : 𝔮' = 𝔐 := hqm'.eq_of_le hmax.ne_top hle
      subst h𝔐
      obtain ⟨i, hik, hI'⟩ := ih I' (absNorm_cofactor hp hI hN')
      refine ⟨i, by omega, ?_⟩
      rw [hI', show k + 1 - i = k - i + 1 by omega, pow_succ]
      ring

lemma split_injective {p : ℕ} (hp : p.Prime) {𝔮 𝔮' : Ideal (𝓞 K)} (hq : 𝔮.IsPrime)
    (hq' : 𝔮'.IsPrime) (hne : 𝔮 ≠ 𝔮') (hN : absNorm 𝔮 = p) (hN' : absNorm 𝔮' = p)
    {k i j : ℕ} (hij : i < j) (hj : j ≤ k) :
    𝔮 ^ i * 𝔮' ^ (k - i) ≠ 𝔮 ^ j * 𝔮' ^ (k - j) := by
  intro h
  have hq0 : 𝔮 ≠ ⊥ := fun h0 => by rw [h0, absNorm_bot] at hN; exact hp.ne_zero hN.symm
  have hq0' : 𝔮' ≠ ⊥ := fun h0 => by rw [h0, absNorm_bot] at hN'; exact hp.ne_zero hN'.symm
  obtain ⟨d, rfl⟩ : ∃ d, j = i + d := ⟨j - i, by omega⟩
  have hk : k - i = (k - (i + d)) + d := by omega
  rw [hk, pow_add, pow_add, mul_assoc] at h
  have h1 := mul_left_cancel₀ (pow_ne_zero i hq0) h
  rw [mul_comm (𝔮' ^ (k - (i + d)))] at h1
  have h2 := mul_right_cancel₀ (pow_ne_zero _ hq0') h1
  have hd : d ≠ 0 := by omega
  have hle : 𝔮' ^ d ≤ 𝔮 := h2 ▸ Ideal.pow_le_self hd
  have := (isMaximal_of_prime_absNorm hq' hp.ne_zero hN').eq_of_le
    (isMaximal_of_prime_absNorm hq hp.ne_zero hN).ne_top (hq.le_of_pow_le hle)
  exact hne this.symm

theorem idealCount_split {p : ℕ} (hp : p.Prime) {𝔮 𝔮' : Ideal (𝓞 K)} (hq : 𝔮.IsPrime)
    (hq' : 𝔮'.IsPrime) (hne : 𝔮 ≠ 𝔮') (hN : absNorm 𝔮 = p) (hN' : absNorm 𝔮' = p)
    (hprod : 𝔮 * 𝔮' = span {(p : 𝓞 K)}) (k : ℕ) : idealCount (p ^ k) = k + 1 := by
  let f : Fin (k + 1) → {I : Ideal (𝓞 K) // absNorm I = p ^ k} := fun i =>
    ⟨𝔮 ^ (i : ℕ) * 𝔮' ^ (k - i), by
      rw [map_mul, map_pow, map_pow, hN, hN', ← pow_add]
      congr 1
      omega⟩
  have hf : Function.Bijective f := by
    refine ⟨fun a b hab => ?_, fun I => ?_⟩
    · have hab' : 𝔮 ^ (a : ℕ) * 𝔮' ^ (k - a) = 𝔮 ^ (b : ℕ) * 𝔮' ^ (k - b) :=
        congrArg Subtype.val hab
      rcases lt_trichotomy (a : ℕ) b with h | h | h
      · exact absurd hab' (split_injective hp hq hq' hne hN hN' h (by omega))
      · exact Fin.ext h
      · exact absurd hab'.symm (split_injective hp hq hq' hne hN hN' h (by omega))
    · obtain ⟨i, hik, hi⟩ := split_classify hp hq hq' hN hN' hprod k I.1 I.2
      exact ⟨⟨i, by omega⟩, Subtype.ext hi.symm⟩
  rw [idealCount, ← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_eq_fintype_card,
    Fintype.card_fin]

/-- Ramified prime: the only ideal of norm `p ^ k` is `𝔭 ^ k`. -/
lemma ramified_classify {p : ℕ} (hp : p.Prime) {𝔭 : Ideal (𝓞 K)} (hP : 𝔭.IsPrime)
    (hN : absNorm 𝔭 = p) (hsq : 𝔭 ^ 2 = span {(p : 𝓞 K)}) :
    ∀ (k : ℕ) (I : Ideal (𝓞 K)), absNorm I = p ^ k → I = 𝔭 ^ k := by
  have hPm := isMaximal_of_prime_absNorm hP hp.ne_zero hN
  intro k
  induction k with
  | zero =>
    intro I hI
    rw [pow_zero, absNorm_eq_one_iff] at hI
    rw [hI, pow_zero, Ideal.one_eq_top]
  | succ k ih =>
    intro I hI
    obtain ⟨𝔐, hmax, hle, I', rfl⟩ := exists_maximal_factor hp k.succ_ne_zero hI
    rw [← hsq] at hle
    have h𝔐 : 𝔭 = 𝔐 := hPm.eq_of_le hmax.ne_top (hmax.isPrime.le_of_pow_le hle)
    subst h𝔐
    rw [ih I' (absNorm_cofactor hp hI hN), pow_succ, mul_comm]

theorem idealCount_ramified {p : ℕ} (hp : p.Prime) {𝔭 : Ideal (𝓞 K)} (hP : 𝔭.IsPrime)
    (hN : absNorm 𝔭 = p) (hsq : 𝔭 ^ 2 = span {(p : 𝓞 K)}) (k : ℕ) :
    idealCount (p ^ k) = 1 := by
  rw [idealCount, Nat.card_eq_one_iff_exists]
  refine ⟨⟨𝔭 ^ k, by rw [map_pow, hN]⟩, fun I => Subtype.ext ?_⟩
  exact ramified_classify hp hP hN hsq k I.1 I.2

/-- Inert prime: an ideal of norm `p ^ k` exists only for even `k`, and it is `(p) ^ (k/2)`. -/
lemma inert_classify {p : ℕ} (hp : p.Prime) (hP : (span {(p : 𝓞 K)}).IsPrime) :
    ∀ (k : ℕ) (I : Ideal (𝓞 K)), absNorm I = p ^ k →
      ∃ j, k = 2 * j ∧ I = span {(p : 𝓞 K)} ^ j := by
  have hN : absNorm (span {(p : 𝓞 K)}) = p ^ 2 := absNorm_natSpan p
  have hPm := isMaximal_of_prime_absNorm hP (pow_ne_zero 2 hp.ne_zero) hN
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro I hI
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · refine ⟨0, rfl, ?_⟩
      rw [pow_zero, absNorm_eq_one_iff] at hI
      rw [hI, pow_zero, Ideal.one_eq_top]
    obtain ⟨𝔐, hmax, hle, I', rfl⟩ := exists_maximal_factor hp hk.ne' hI
    have h𝔐 : span {(p : 𝓞 K)} = 𝔐 := hPm.eq_of_le hmax.ne_top hle
    subst h𝔐
    rw [map_mul, hN] at hI
    have hk2 : 2 ≤ k := by
      by_contra hlt
      have hk1 : k = 1 := by omega
      subst hk1
      have hle : p ^ 2 ≤ p ^ 1 := Nat.le_of_dvd (by simpa using hp.pos) ⟨_, hI.symm⟩
      have : p ≤ 1 := by nlinarith [hp.two_le]
      exact absurd hp.two_le (by omega)
    have hI' : absNorm I' = p ^ (k - 2) := by
      rw [show k = 2 + (k - 2) by omega, pow_add] at hI
      exact Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos 2) hI
    obtain ⟨j, hj, hIj⟩ := ih (k - 2) (by omega) I' hI'
    exact ⟨j + 1, by omega, by rw [hIj, pow_succ, mul_comm]⟩

theorem idealCount_inert {p : ℕ} (hp : p.Prime) (hP : (span {(p : 𝓞 K)}).IsPrime) (k : ℕ) :
    idealCount (p ^ k) = if Even k then 1 else 0 := by
  rw [idealCount]
  split_ifs with hk
  · obtain ⟨j, rfl⟩ := hk
    rw [Nat.card_eq_one_iff_exists]
    refine ⟨⟨span {(p : 𝓞 K)} ^ j, by rw [map_pow, absNorm_natSpan, ← pow_mul]; ring_nf⟩,
      fun I => Subtype.ext ?_⟩
    obtain ⟨j', hj', hI⟩ := inert_classify hp hP (j + j) I.1 I.2
    rw [hI, show j' = j by omega]
  · rw [Nat.card_eq_zero]
    left
    refine ⟨fun I => ?_⟩
    obtain ⟨j, hj, -⟩ := inert_classify hp hP k I.1 I.2
    exact hk ⟨j, by omega⟩

/-! ## The coefficients of `ζ_K` are those of `ζ * χ_{−20}` -/

/-- The ideal count as a complex arithmetic function. -/
def idealCountA : ArithmeticFunction ℂ := toArithmeticFunction (fun n => (idealCount n : ℂ))

lemma idealCountA_apply {n : ℕ} (hn : n ≠ 0) : idealCountA n = idealCount n := by
  simp [idealCountA, toArithmeticFunction, hn]

lemma idealCount_one : idealCount 1 = 1 := by
  rw [idealCount, Nat.card_eq_one_iff_exists]
  exact ⟨⟨⊤, absNorm_top⟩, fun I => Subtype.ext (absNorm_eq_one_iff.1 I.2)⟩

lemma isMultiplicative_idealCountA : idealCountA.IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  refine ⟨by rw [idealCountA_apply one_ne_zero, idealCount_one, Nat.cast_one], ?_⟩
  intro m n hm hn hmn
  rw [idealCountA_apply (mul_ne_zero hm hn), idealCountA_apply hm, idealCountA_apply hn,
    idealCount_mul hmn hm hn, Nat.cast_mul]

lemma χ_neg20ℂ_natCast (p : ℕ) : χ_neg20ℂ (p : ZMod (Nat.lcm 4 5)) = (χ_neg20 (p : ℤ) : ℂ) := by
  rw [← χ_neg20_int, Int.cast_natCast]

set_option backward.isDefEq.respectTransparency.types false in
lemma zetaMul_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    χ_neg20ℂ.zetaMul (p ^ k) = ∑ i ∈ Finset.range (k + 1), (χ_neg20ℂ (p : ZMod _)) ^ i := by
  simp only [DirichletCharacter.zetaMul, toArithmeticFunction, ArithmeticFunction.coe_zeta_mul_apply,
    ArithmeticFunction.coe_mk, Nat.sum_divisors_prime_pow hp, pow_eq_zero_iff', hp.ne_zero, ne_eq,
    false_and, ↓reduceIte, Nat.cast_pow, map_pow]

/-- The splitting law, read as the count of ideals of norm `p ^ k`. -/
lemma idealCount_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (idealCount (p ^ k) : ℂ) = ∑ i ∈ Finset.range (k + 1), (χ_neg20ℂ (p : ZMod _)) ^ i := by
  have := Fact.mk hp
  rw [χ_neg20ℂ_natCast]
  rcases splitting_of_χ (p := p) with ⟨h0, 𝔭, hP, hN, hsq⟩ |
    ⟨h1, 𝔮, 𝔮', hq, hq', hne, hN, hN', hprod⟩ | ⟨hm, hP, -⟩
  · rw [idealCount_ramified hp hP hN hsq, h0, Finset.sum_range_succ']
    simp
  · rw [idealCount_split hp hq hq' hne hN hN' hprod, h1]
    simp
  · rw [idealCount_inert hp hP, hm, Int.cast_neg, Int.cast_one, neg_one_geom_sum]
    by_cases hk : Even k <;> simp [hk, Nat.even_add_one]

theorem idealCountA_eq_zetaMul : idealCountA = χ_neg20ℂ.zetaMul := by
  rw [ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers _ isMultiplicative_idealCountA
    _ (DirichletCharacter.isMultiplicative_zetaMul _)]
  intro p k hp
  rw [zetaMul_prime_pow hp, ← idealCount_prime_pow hp,
    idealCountA_apply (pow_ne_zero k hp.ne_zero)]

/-- `ζ_K(s) = ζ(s) L(s, χ_{−20})` for `1 < Re s`. -/
theorem halfPlane_holds : halfPlane := by
  intro s hs
  have hζK : dedekindZeta K s = LSeries (fun n => idealCountA n) s := by
    rw [dedekindZeta]
    refine LSeries_congr (fun {n} hn => ?_) s
    rw [idealCountA_apply hn, idealCount]
  have hχ : LSeriesSummable (fun n => toArithmeticFunction (fun m : ℕ => χ_neg20ℂ m) n) s :=
    LSeriesSummable_of_bounded_of_one_lt_re (m := 1) (fun n hn => by
      simpa only [toArithmeticFunction, ArithmeticFunction.coe_mk, hn, ↓reduceIte]
        using χ_neg20ℂ.norm_le_one _) hs
  have hζ : LSeriesSummable (fun n => ((ArithmeticFunction.zeta : ArithmeticFunction ℂ) n)) s := by
    refine (LSeriesSummable_congr s (fun {n} hn => ?_)).1
      (ArithmeticFunction.LSeriesSummable_zeta_iff.mpr hs)
    simp [ArithmeticFunction.natCoe_apply]
  rw [hζK, idealCountA_eq_zetaMul, DirichletCharacter.zetaMul,
    ArithmeticFunction.LSeries_mul' hζ hχ, zetaProduct,
    DirichletCharacter.LFunction_eq_LSeries _ hs, ← ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs]
  congr 1
  refine LSeries_congr (fun {n} hn => ?_) s
  simp [toArithmeticFunction, hn]

/-- Report §4 / The One Piece: `ζ_K(s) = ζ(s) · L(s, χ_{−20})` for `1 < Re s`.

The honest factorization. Mathlib's `dedekindZeta K` is the Dirichlet series of ideal
counts; it equals the product exactly on the half-plane of absolute convergence
`1 < Re s`. Off that half-plane the series is `0`, so the unrestricted `∀ s` form is
false — this is why the domain hypothesis is the honest one. The proof reuses
`halfPlane_holds` (the splitting law and the multiplicativity of the ideal count) and
rebuilds nothing. The character identity `χ_{−20} = χ_{−4} · χ₅`
(`TheThing.χ_neg20_eq_mul`) is the exact spot where `√5`, through `χ₅`, enters `ζ_K`. -/
theorem dedekindZeta_factorization (s : ℂ) (hs : 1 < s.re) :
    dedekindZeta K s = riemannZeta s * DirichletCharacter.LFunction χ_neg20ℂ s := by
  have h := halfPlane_holds s hs
  rwa [zetaProduct] at h

end ExistenceSystem.Summit

end

end
