module

/-
KL21 — the Closure Transfer Lemma, from THE EXACT AND FREE SYSTEM — AN EXISTENCE SYNTHESIS.
All mathematics: Kari A Light.

Source: `THE-NOTE-EDITED.md` (194,868 bytes, 1,539 lines). Line numbers below refer to that file.
Her words are quoted exactly beside each statement. Nothing of hers is graded here.

Note L126 (front matter), verbatim:
"**KL21 — the Closure Transfer Lemma.** Physical closure $\Leftrightarrow$ six-dimensional closure
$\Leftrightarrow$ perpendicular closure. The perpendicular closure is not an extra hypothesis; it is
dragged along by the physical one. *Proved in §4.6.*"

Note L655–L657 (§4.6), verbatim:
"> **The Closure Transfer Lemma (KL21).** For any $G_1\dots G_n\in\mathcal L$,
> $$\sum_m\pi_\parallel(G_m)=0\iff\sum_mG_m=0\iff\sum_m\pi_\perp(G_m)=0.$$
> The perpendicular closure is **not an extra hypothesis**. It is dragged along by the physical
> closure."

Note L255 (taxonomy, the star map), verbatim:
"$(\cdot)^{\star}:=\pi_\perp\circ(\pi_\parallel|_{\mathcal L})^{-1}:\pi_\parallel(\mathcal L)\to
E_\perp$; a group homomorphism, so it carries closures to closures (equivalent form of the Closure
Transfer Lemma)"

Note L267 (taxonomy, named results), verbatim:
"Four aspects carried *in the statement*: lifting, transfer, cancellation, homomorphism (star map).
| **The author's.**"

No proof block follows L655–L657. The argument here is KL20's (`ExistenceSystem.KL20`, imported,
not rebuilt) for the first `⇔`, and the π_⊥-mirror of KL20 for the second: the same argument with
the two embeddings of ℚ(√5) exchanged by σ (`embedPsi = embedPhi ∘ σ`,
`Quadratic.embedPsi_eq_embedPhi_star`). The Note states injectivity on ℒ only for π_∥ (L647); the
mirror `E_∥ ∩ ℒ = {0}` is proved here because the third clause needs it.

Reading (the map `data/lean-scope-b/G2.md`, KL21). ℒ is the merged `Icosahedral.lattice = A(ℤ⁶)`;
a lattice point's π_∥/π_⊥ are its physical/perpendicular coordinates (`KL20.parProj`, and
`perpProj` here: the first/last three coordinates of `ℝ⁶ = E_∥ ⊕ E_⊥`). The headline three-way
equivalence L655–L657 is assembled as `closure_transfer` over a finite family `Gₘ ∈ ℒ`: linearity
of the two projections across the sum, ℒ closed under finite sums, and the two intersection forms
`{π_∥ = 0} ∩ ℒ = {0}` (KL20) and `{π_⊥ = 0} ∩ ℒ = {0}` (the mirror). The star map L255 is built on
π_∥(ℒ) as the range of π_∥ restricted to ℒ, its inverse given by KL20's injectivity (`starMap`,
`starMap_apply`); `starMap_add`/`starMap_zero` are "a group homomorphism, so it carries closures to
closures". Her word at L666 is "corollary" ("by the same corollary") where L655 and the taxonomy say
Lemma; a naming fact only, not encoded.
-/
public import ExistenceSystem.KL20

@[expose] public section

open Real
open scoped goldenRatio QuadraticAlgebra

namespace ExistenceSystem.KL21

open ExistenceSystem.Icosahedral ExistenceSystem.Quadratic ExistenceSystem.KL20

/-! ## The π_⊥-mirror of KL20: σ exchanges the two embeddings -/

/-- σ exchanges the two real embeddings (`embedPsi = embedPhi ∘ σ`), so `embedPsi` is injective
too: the mirror of KL20's single use of φ irrational. -/
theorem embedPsi_injective : Function.Injective embedPsi := by
  intro a b hab
  have h : embedPhi (star a) = embedPhi (star b) := by
    rw [← embedPsi_eq_embedPhi_star, ← embedPsi_eq_embedPhi_star]; exact hab
  have hs : star a = star b := embedPhi_injective h
  have hss := congrArg (star : K → K) hs
  simpa only [star_star] using hss

/-- The mirror of Note L649's "applying σ termwise": a vanishing perpendicular combination of the
star forces the parallel one to vanish. -/
theorem sigma_transfer_perp (n : Fin 6 → ℤ)
    (hperp : piPerp (fun i => (n i : ℝ)) = 0) :
    piParallel (fun i => (n i : ℝ)) = 0 := by
  funext k
  have hz : (∑ i, (n i) • coeZphi (qRaw i k)) = 0 := by
    apply embedPsi_injective
    rw [map_zero, ← piPerp_coe_eq]
    exact congrFun hperp k
  rw [piParallel_coe_eq, hz, map_zero]
  rfl

/-- The mirror of KL20 (`no_integer_relation`): the perpendicular star `Qᵢ^⊥` admits no integer
relation. -/
theorem no_integer_relation_perp (n : Fin 6 → ℤ)
    (hperp : piPerp (fun i => (n i : ℝ)) = 0) : n = 0 := by
  have hpar := sigma_transfer_perp n hperp
  have hc : (fun i => (n i : ℝ)) = 0 := joint_vanishing _ hpar hperp
  funext i
  have hi : (n i : ℝ) = 0 := congrFun hc i
  exact_mod_cast hi

/-- π_⊥ of an actual vector of ℝ⁶ = E_∥ ⊕ E_⊥: the last three (perpendicular) coordinates. -/
def perpProj (v : Fin 6 → ℝ) : Fin 3 → ℝ := fun k => v ⟨k.val + 3, by omega⟩

private lemma scale_perp_ne_zero : ((Real.sqrt 2)⁻¹ * (Real.sqrt (3 - φ))⁻¹) ≠ 0 := by
  have h2 : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have hφ : Real.sqrt (3 - φ) ≠ 0 :=
    (Real.sqrt_pos.mpr (by linarith [goldenRatio_lt_two])).ne'
  exact mul_ne_zero (inv_ne_zero h2) (inv_ne_zero hφ)

/-- The perpendicular projection of the lattice point `∑ᵢ nᵢ Gᵢ` is a nonzero scalar times π_⊥ of
the integer coefficient vector. (Gᵢ = 2^{-1/2}(Qᵢ, Qᵢ^⊥), `Qᵢ^⊥ = σ(Qᵢ)/√(3−φ)`.) -/
theorem perpProj_lattice (n : Fin 6 → ℤ) (k : Fin 3) :
    perpProj (fun j => ∑ i, (n i : ℝ) * Icosahedral.row i j) k
      = ((Real.sqrt 2)⁻¹ * (Real.sqrt (3 - φ))⁻¹) * piPerp (fun i => (n i : ℝ)) k := by
  have hrow : ∀ i, Icosahedral.row i ⟨k.val + 3, by omega⟩ = Qperp i k / Real.sqrt 2 := by
    intro i
    unfold Icosahedral.row
    rw [dif_neg (by omega : ¬ ((k.val + 3 : ℕ) < 3))]
    congr 1
  show (∑ i, (n i : ℝ) * Icosahedral.row i ⟨k.val + 3, by omega⟩) = _
  rw [piPerp, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [hrow i]
  simp only [Qperp, Pi.smul_apply, smul_eq_mul]
  ring

/-- **The mirror of KL20's equivalent form.** `E_∥ ∩ ℒ = {0}`: the only lattice point whose
perpendicular projection vanishes is the origin. -/
theorem par_inter_lattice_eq_zero :
    {v : Fin 6 → ℝ | perpProj v = 0} ∩ Icosahedral.lattice = {0} := by
  ext v
  simp only [Set.mem_inter_iff, Icosahedral.lattice, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hpar, n, rfl⟩
    have hperp0 : piPerp (fun i => (n i : ℝ)) = 0 := by
      funext k
      have hk := congrFun hpar k
      rw [perpProj_lattice] at hk
      exact (mul_eq_zero.mp hk).resolve_left scale_perp_ne_zero
    have hn := no_integer_relation_perp n hperp0
    subst hn
    funext j; simp
  · rintro rfl
    refine ⟨?_, 0, ?_⟩
    · funext k; simp [perpProj]
    · funext j; simp

/-- **The mirror of KL20's first clause: π_⊥ restricted to the lattice ℒ is injective.** -/
theorem perpProj_injOn_lattice : Set.InjOn perpProj Icosahedral.lattice := by
  rintro v ⟨n, rfl⟩ v' ⟨n', rfl⟩ h
  have hperp : piPerp (fun i => (n i : ℝ)) = piPerp (fun i => (n' i : ℝ)) := by
    funext k
    have hk := congrFun h k
    rw [perpProj_lattice, perpProj_lattice] at hk
    exact mul_left_cancel₀ scale_perp_ne_zero hk
  have hdiff : piPerp (fun i => ((n i - n' i : ℤ) : ℝ)) = 0 := by
    funext k
    have e : piPerp (fun i => ((n i - n' i : ℤ) : ℝ)) k
        = piPerp (fun i => (n i : ℝ)) k - piPerp (fun i => (n' i : ℝ)) k := by
      rw [piPerp, piPerp, piPerp, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      push_cast; ring
    rw [e, congrFun hperp k]; simp
  have hz := no_integer_relation_perp (fun i => n i - n' i) hdiff
  have hnn : n = n' := by
    funext i
    have := congrFun hz i
    simp only [Pi.zero_apply] at this
    omega
  subst hnn; rfl

/-! ## The headline: physical ⇔ six-dimensional ⇔ perpendicular closure (Note L655–L657) -/

/-- π_∥ is additive across a finite family (it reads off three coordinates). -/
private lemma parProj_sum {ι : Type*} (s : Finset ι) (G : ι → (Fin 6 → ℝ)) :
    parProj (∑ m ∈ s, G m) = ∑ m ∈ s, parProj (G m) := by
  funext k
  simp only [parProj, Finset.sum_apply]

/-- π_⊥ is additive across a finite family. -/
private lemma perpProj_sum {ι : Type*} (s : Finset ι) (G : ι → (Fin 6 → ℝ)) :
    perpProj (∑ m ∈ s, G m) = ∑ m ∈ s, perpProj (G m) := by
  funext k
  simp only [perpProj, Finset.sum_apply]

/-- ℒ is closed under `+`: the lattice is the integer span of the rows of `A`. -/
private lemma add_mem_lattice {u v : Fin 6 → ℝ} (hu : u ∈ Icosahedral.lattice)
    (hv : v ∈ Icosahedral.lattice) : u + v ∈ Icosahedral.lattice := by
  obtain ⟨n, rfl⟩ := hu
  obtain ⟨n', rfl⟩ := hv
  refine ⟨n + n', ?_⟩
  funext j
  simp only [Pi.add_apply, Int.cast_add]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i _ => by ring)

/-- ℒ as an additive submonoid of ℝ⁶, so that `∑ₘ Gₘ ∈ ℒ` for a finite family in ℒ. -/
private def latticeSubmonoid : AddSubmonoid (Fin 6 → ℝ) where
  carrier := Icosahedral.lattice
  zero_mem' := ⟨0, by funext j; simp⟩
  add_mem' := fun ha hb => add_mem_lattice ha hb

/-- ℒ is closed under finite sums: `∑ₘ Gₘ ∈ ℒ` whenever every `Gₘ ∈ ℒ`. Note L655, "for any
`G₁…Gₙ ∈ ℒ`", the sum `∑ₘ Gₘ` is itself a lattice point. -/
private lemma sum_mem_lattice {ι : Type*} (s : Finset ι) (G : ι → (Fin 6 → ℝ))
    (hG : ∀ m ∈ s, G m ∈ Icosahedral.lattice) :
    (∑ m ∈ s, G m) ∈ Icosahedral.lattice := by
  have h : (∑ m ∈ s, G m) ∈ latticeSubmonoid :=
    AddSubmonoid.sum_mem latticeSubmonoid (fun m hm => hG m hm)
  exact h

/-- **KL21, the Closure Transfer Lemma (Note L655–L657).** For any finite family `Gₘ ∈ ℒ`,
`∑ₘ π_∥(Gₘ) = 0 ⟺ ∑ₘ Gₘ = 0 ⟺ ∑ₘ π_⊥(Gₘ) = 0`. The perpendicular closure is not an extra
hypothesis; it is dragged along by the physical one. The first `⇔` is KL20
(`perp_inter_lattice_eq_zero`), the second its π_⊥-mirror (`par_inter_lattice_eq_zero`); both read
the sum `∑ₘ Gₘ` as the single lattice point it is. -/
theorem closure_transfer {ι : Type*} (s : Finset ι) (G : ι → (Fin 6 → ℝ))
    (hG : ∀ m ∈ s, G m ∈ Icosahedral.lattice) :
    ((∑ m ∈ s, parProj (G m)) = 0 ↔ (∑ m ∈ s, G m) = 0) ∧
      ((∑ m ∈ s, G m) = 0 ↔ (∑ m ∈ s, perpProj (G m)) = 0) := by
  have hsum : (∑ m ∈ s, G m) ∈ Icosahedral.lattice := sum_mem_lattice s G hG
  refine ⟨?_, ?_⟩
  · rw [← parProj_sum]
    refine ⟨fun hpar => ?_, fun h6 => ?_⟩
    · have hmem : (∑ m ∈ s, G m) ∈ ({v : Fin 6 → ℝ | parProj v = 0} ∩ Icosahedral.lattice) :=
        ⟨hpar, hsum⟩
      rw [perp_inter_lattice_eq_zero] at hmem
      simpa using hmem
    · rw [h6]; funext k; simp [parProj]
  · rw [← perpProj_sum]
    refine ⟨fun h6 => ?_, fun hperp => ?_⟩
    · rw [h6]; funext k; simp [perpProj]
    · have hmem : (∑ m ∈ s, G m) ∈ ({v : Fin 6 → ℝ | perpProj v = 0} ∩ Icosahedral.lattice) :=
        ⟨hperp, hsum⟩
      rw [par_inter_lattice_eq_zero] at hmem
      simpa using hmem

/-! ## The star map (Note L255): `(·)^⋆ = π_⊥ ∘ (π_∥|_ℒ)⁻¹` -/

/-- The star map `(·)^⋆ := π_⊥ ∘ (π_∥|_ℒ)⁻¹` (Note L255). On π_∥(ℒ) it sends the physical
projection of a lattice point to that point's perpendicular projection; the inverse of `π_∥|_ℒ`
exists by KL20's injectivity (`parProj_injOn_lattice`). -/
noncomputable def starMap (p : Fin 3 → ℝ) : Fin 3 → ℝ :=
  perpProj (Function.invFunOn parProj Icosahedral.lattice p)

/-- The defining property of the star map: for a lattice point `v`, `(π_∥ v)^⋆ = π_⊥ v`. -/
theorem starMap_apply {v : Fin 6 → ℝ} (hv : v ∈ Icosahedral.lattice) :
    starMap (parProj v) = perpProj v := by
  have hex : ∃ a ∈ Icosahedral.lattice, parProj a = parProj v := ⟨v, hv, rfl⟩
  have hmem : Function.invFunOn parProj Icosahedral.lattice (parProj v) ∈ Icosahedral.lattice :=
    Function.invFunOn_mem hex
  have heq : parProj (Function.invFunOn parProj Icosahedral.lattice (parProj v)) = parProj v :=
    Function.invFunOn_eq hex
  have hpre : Function.invFunOn parProj Icosahedral.lattice (parProj v) = v :=
    parProj_injOn_lattice hmem hv heq
  simp only [starMap, hpre]

/-- The star map is a group homomorphism (Note L255): it respects addition on π_∥(ℒ), so it
"carries closures to closures". -/
theorem starMap_add {u v : Fin 6 → ℝ} (hu : u ∈ Icosahedral.lattice)
    (hv : v ∈ Icosahedral.lattice) :
    starMap (parProj u + parProj v) = starMap (parProj u) + starMap (parProj v) := by
  have huv : u + v ∈ Icosahedral.lattice := add_mem_lattice hu hv
  have hsum : parProj u + parProj v = parProj (u + v) := by
    funext k; simp only [parProj, Pi.add_apply]
  rw [hsum, starMap_apply huv, starMap_apply hu, starMap_apply hv]
  funext k; simp only [perpProj, Pi.add_apply]

/-- The star map sends `0` to `0`: the identity element of the homomorphism (Note L255). -/
theorem starMap_zero : starMap 0 = 0 := by
  have h0 : (0 : Fin 6 → ℝ) ∈ Icosahedral.lattice := latticeSubmonoid.zero_mem
  have hp : parProj (0 : Fin 6 → ℝ) = 0 := by funext k; simp [parProj]
  have hstar : starMap (parProj (0 : Fin 6 → ℝ)) = perpProj (0 : Fin 6 → ℝ) := starMap_apply h0
  rw [hp] at hstar
  rw [hstar]; funext k; simp [perpProj]

end ExistenceSystem.KL21

end
