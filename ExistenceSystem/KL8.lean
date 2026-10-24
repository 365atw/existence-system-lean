module

/-
KL8 — The symmetry-protection upgrade (§5), from THE EXACT AND FREE SYSTEM —
AN EXISTENCE SYNTHESIS. All mathematics: Kari A Light (K-A-R-I).

Source: `THE-NOTE-EDITED.md` (194,868 bytes, 1,539 lines). Line numbers below refer to that
file. Her words are quoted exactly beside each statement. Nothing of hers is graded here.

Note L100 (front-matter list form), verbatim:
"**KL8 — The symmetry-protection upgrade.** The indifferent locus is carried from measure-zero and
fine-tuned (in the normal form) to full-dimensional, symmetry-protected, generic, and realized in
stable matter at room temperature. *Established in §5.*" (Her verb is *established*.)

Note L754 (§5.1 opening), verbatim:
"Set the two indifferences side by side — the one the normal form of §3 delivers, and the one the
construction of §4 delivers."

Note L756–L765 (the comparison table, her rows), verbatim cells:
"| indifference locus | $\{h=0,\ r>0\}$ | the entire phason 3-torus, all $w\in E_\perp$ |
 | dimension in its own space | measure zero in the $(r,h)$ plane | full dimension |
 | status | fine-tuned; destroyed by any bias $h\ne0$ | protected by a continuous (Goldstone)
   symmetry of $J$ |
 | stability under perturbation | none | total: no admissible term can break it (§4.8(4)) |
 | order of the statement | exact at one order | an identity at **every** order (Lemma 2) |
 | degenerate set | 2 points, $\{+\sqrt r,-\sqrt r\}$ | a 3-parameter continuum of non-congruent
   structures |
 | $\varphi$ present? | no | yes, forced three times, three ways (§4.2, §4.3) |
 | realized? | a normal-form observation | i-Al$_{70}$Pd$_{20}$Mn$_{10}$,
   i-Al$_{65}$Cu$_{20}$Fe$_{15}$, stable at room temperature [10,13,14,15]; icosahedrite, found in
   nature [12] |"

Note L767 (KL8, the body), verbatim:
"**KL8.** In the normal form, the indifference of the least-action functional held on a measure-zero
locus and was destroyed by any perturbation. In the icosahedral system the corresponding locus is of
full dimension in $E_\perp$, protected by a symmetry, unbreakable by any admissible perturbation, and
instantiated in matter that sits stably on a laboratory bench and, as icosahedrite, in a meteorite.
**Measure-zero → symmetry-protected → generic → realized.** The theorem of §3 is unchanged; what has
changed is where it lives."

Note L769 (the co-instantiation statement and the imported comparison), verbatim:
"Both halves are now in one system: a $\varphi$-scaled ordered branch, with $\varphi$ forced rather
than inserted, and a free selector that is generic rather than fine-tuned. **The comparison against
bcc, fcc and competing decagonal orderings is carried out in the Landau literature [21–25] and
settled empirically by the stable icosahedral phases [10, 13, 14]** (see also §8, item 5)."

────────────────────────────────────────────────────────────────────────────────────────────────
Reading choices and scope (map `data/lean-scope-b/G4.md`, §"KL8 — The symmetry-protection upgrade",
l.228–306; coverage `coverage.md` I-109/I-110/I-111).

KL8 is a **packaging theorem**: "no new mathematics beyond its constituents" (the map, G4 §"KL8"
item 2). It sets §3's indifference beside §4's and names the upgrade — nothing of KL3, KL6, KL7, KL22
is rebuilt (leaves-first). It is deep in the architecture sense: a small interface — the two
indifferences, side by side — with each constituent's heavy machinery sitting behind the modules it
imports. It leverages them; it does not reprove them.

The map splits KL8 into parts of different kinds (G4 §"KL8", the side-by-side table). Only the
**mathematics** of her comparison is encoded here; the two non-mathematical rows are recorded, not
mapped — exactly the discipline of KL19's borrowed premise and KL7's "make φ rational" prose:

* **The normal-form side (§3), `normalFormLocus …`, `normalForm_degenerate_card`,
  `bias_breaks_branches` (Note L758–L765, column 1).** "indifference locus $\{h=0,\ r>0\}$ …
  measure zero in the $(r,h)$ plane" is `normalFormLocus_volume_zero`; "degenerate set 2 points,
  $\{+\sqrt r,-\sqrt r\}$" is `normalForm_degenerate_card`, reusing `KL3.minimizers_ncard`;
  "fine-tuned; destroyed by any bias $h\ne0$" is `bias_breaks_branches` — for `h ≠ 0` the two
  branches `±√r` lose their equal depth, the elementary kernel of §3.3's universal-unfolding step
  (A16, borrowed: Golubitsky–Schaeffer [41], Thom [42]; the unfolding *theory* is not built, only
  the equal-depth-is-broken fact her table states).

* **The icosahedral side (§4), geometric — `icosahedral_indifferent_full`, `symmetry_protected`
  (Note L758–L760, column 2).** "the entire phason 3-torus, all $w\in E_\perp$ … full dimension" is
  `icosahedral_indifferent_full`: *every* free vector is a global minimizer over `E_⊥`, so the
  arg-min is all of `E_⊥` — `KL7.isMinOn_free`. "protected by a continuous (Goldstone) symmetry of
  $J$" is `symmetry_protected`: `J (x+w) = J x` for `w ∈ E_⊥`, which is KL6's invariance, carried
  here (as in KL7) as the explicit hypothesis `hInv` — never proved, never an axiom; the word
  *Goldstone* names it via A11 (borrowed, her marking l.1138), not reproved.

* **The icosahedral side (§4), perturbative — `unbreakable`, `identity_at_every_order` (Note
  L761–L762, column 2).** "total: no admissible term can break it (§4.8(4))" is `unbreakable` =
  `KL7.no_admissible_perturbation_selects`: an admissible term (physical-translation invariant,
  `KL22.admissible_iff_closure`) is w-independent. "an identity at **every** order (Lemma 2)" is
  `identity_at_every_order` = `KL6.no_pinning` fed by `KL22.admissible_iff_closure`: the term is
  strictly constant in the uniform phason shift and every one of its w-derivatives vanishes, at
  every order.

* **The headline, `symmetry_protection_upgrade` (Note L767, the icosahedral conjunction).** "of full
  dimension in $E_\perp$, protected by a symmetry, unbreakable by any admissible perturbation … an
  identity at every order" — the four mathematical rows of column 2 in one statement, each discharged
  by its constituent. "The theorem of §3 is unchanged; what has changed is where it lives": §3's side
  is the companion `normalForm_*` above.

Not encoded (the map, G4 §"KL8" item 5, her markings quoted; **no verdict on her work**):
* **"generic"** — "the Note gives no definition (no topology or measure on a space of functionals is
  fixed in which *generic* would be read)" (the map). Recorded, not mapped.
* **"realized in stable matter at room temperature"; "instantiated in matter … as icosahedrite, in a
  meteorite"** — empirical, resting on cited experiment (A15; [10,12,13,14,15]). "What experiment has
  established." (her l.1146). Not mathematics; recorded, not mapped.
* **The "3-parameter continuum of non-congruent structures" row (L763, column 2)** — needs U34's
  locally-inequivalent part (G5's LI-class material), deferred; the degenerate-set contrast encoded
  here is her own "2 points" against KL7's "all of E_⊥".
* **"$\varphi$ … forced three times, three ways (§4.2, §4.3)"** (L764) — the forcings are G2/G3
  (KL17/KL23/…), not restated here.
* **The imported comparison (L769, I-111)** — "carried out in the Landau literature [21–25] and
  settled empirically" (her l.769), "imported, not derived here" (§8 item 5, N5). Borrowed; recorded,
  not mapped.
* **The verb on the list form is "*Established in §5*", not "Proved"** — the map's note, carried.

Structure. §1 the normal-form side (§3): the measure-zero locus, the two-point degenerate set, the
bias that breaks the equal depth. §2 the icosahedral side, geometric (abstract on `hInv`, as KL7).
§3 the icosahedral side, perturbative (the concrete ℤ⁶ carrier, on KL6/KL7/KL22). §4 the headline.
-/
public import Mathlib
public import ExistenceSystem.KL3
public import ExistenceSystem.KL6
public import ExistenceSystem.KL7
public import ExistenceSystem.KL22

@[expose] public section

open Real MeasureTheory

namespace ExistenceSystem.KL8

/-! ## §1. The normal-form side (§3): "where it came from" (Note L758–L765, column 1)

The indifference §3 delivers: a locus `{h=0, r>0}` of measure zero in the `(r,h)` plane, a
two-point degenerate set `{+√r,-√r}`, fine-tuned and destroyed by any bias `h ≠ 0`. Reuses the
merged `KL3` (the §3 potential `V` and its minimizers); nothing of §3 is rebuilt. -/

/-- **Note L758, column 1.** "indifference locus $\{h=0,\ r>0\}$." The genuinely indifferent locus of
the symmetric normal form, as a subset of the `(r,h)` plane (first coordinate `r`, second `h`). -/
def normalFormLocus : Set (ℝ × ℝ) := {p | p.2 = 0 ∧ 0 < p.1}

/-- **Note L759, column 1.** "measure zero in the $(r,h)$ plane." The indifferent locus `{h=0, r>0}`
is Lebesgue-null in `ℝ²`: it lies in the line `{h=0} = ℝ × {0}`, whose plane measure is `∞ · 0 = 0`.
This is the *non-generic* side of her table — in the bare normal form the indifferent case is
fine-tuned. -/
theorem normalFormLocus_volume_zero : volume normalFormLocus = 0 := by
  have hsub : normalFormLocus ⊆ (Set.univ : Set ℝ) ×ˢ ({0} : Set ℝ) := by
    intro p hp
    simp only [Set.mem_prod, Set.mem_univ, Set.mem_singleton_iff, true_and]
    exact hp.1
  refine measure_mono_null hsub ?_
  rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_singleton, mul_zero]

/-- **Note L763, column 1.** "degenerate set 2 points, $\{+\sqrt r,-\sqrt r\}$." The §3 degenerate
set has exactly two elements, the two branches `±√r`. Reuses `KL3.minimizers_ncard`. -/
theorem normalForm_degenerate_card (r : ℝ) (hr : 0 < r) :
    {x : ℝ | ∀ y : ℝ, KL3.V r x ≤ KL3.V r y}.ncard = 2 :=
  KL3.minimizers_ncard r hr

/-- Note L760, column 1 (A16, borrowed): the biased potential `V_h(x) = V(x) − h·x`, the cusp
unfolding `V − h x`. Only the elementary equal-depth-is-broken fact below is used; the
universal-unfolding theory (Golubitsky–Schaeffer [41], Thom [42]) is not built. -/
noncomputable def Vbias (r h x : ℝ) : ℝ := KL3.V r x - h * x

/-- **Note L760, column 1.** "status: fine-tuned; destroyed by any bias $h\ne0$." For any nonzero
bias `h` (and `r > 0`) the two ordered branches `±√r` lose their equal depth: `V_h(√r) ≠ V_h(−√r)`.
The `ℤ₂` symmetry `x ↦ −x` that made the branches equal (`KL3.V_branches`) is broken by the
exogenous term, so the indifference of §3 does not survive a perturbation — the fine-tuned side of
the upgrade. -/
theorem bias_breaks_branches (r h : ℝ) (hr : 0 < r) (hh : h ≠ 0) :
    Vbias r h (Real.sqrt r) ≠ Vbias r h (-Real.sqrt r) := by
  obtain ⟨hb1, hb2⟩ := KL3.V_branches r hr
  have hsqrt : 0 < Real.sqrt r := Real.sqrt_pos.2 hr
  have key : Vbias r h (Real.sqrt r) - Vbias r h (-Real.sqrt r) = -2 * (h * Real.sqrt r) := by
    simp only [Vbias, hb1, hb2]; ring
  intro heq
  rw [heq, sub_self] at key
  have hz : h * Real.sqrt r = 0 := by linarith
  rcases mul_eq_zero.1 hz with hh0 | hs
  · exact hh hh0
  · exact hsqrt.ne' hs

/-! ## §2. The icosahedral side (§4), geometric (Note L758–L760, column 2)

The indifference §4 delivers, at the generality KL7's argument lives at: an abstract energy
`J : E → ℝ` on a real normed space, the free directions a subspace `Eperp = E_⊥`, and KL6's
invariance `J(x+w)=J(x)` for `w ∈ Eperp` carried as the explicit hypothesis `hInv` (never proved;
KL7's discipline). -/

section Icosahedral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (Eperp : Submodule ℝ E) (J : E → ℝ)
  (hInv : ∀ x : E, ∀ w ∈ Eperp, J (x + w) = J x)

include hInv

/-- **Note L758, column 2.** "the entire phason 3-torus, all $w\in E_\perp$"; **L759:** "full
dimension." The indifferent locus is *all* of `E_⊥`: every free vector `w₀ ∈ E_⊥` is a global
minimizer of `w ↦ J (x + w)` over `E_⊥`, so the arg-min is the whole free subspace — not a
measure-zero finite set, as in §3, but the full free direction. This is `KL7.isMinOn_free`. -/
theorem icosahedral_indifferent_full (x : E) {w₀ : E} (hw₀ : w₀ ∈ Eperp) :
    IsMinOn (fun w => J (x + w)) (Eperp : Set E) w₀ :=
  KL7.isMinOn_free Eperp J hInv x hw₀

/-- **Note L760, column 2.** "protected by a continuous (Goldstone) symmetry of $J$." The energy is
invariant under the `E_⊥` translation action: `J (x + w) = J x` for every `w ∈ E_⊥`. This is KL6's
No-Pinning invariance, carried here as `hInv`; the word *Goldstone* names the uniform phason as the
coordinate of the broken `E_⊥` translation (A11, borrowed), not reproved. -/
theorem symmetry_protected (x : E) {w : E} (hw : w ∈ Eperp) : J (x + w) = J x :=
  hInv x w hw

end Icosahedral

/-! ## §3. The icosahedral side (§4), perturbative (Note L761–L762, column 2)

On the concrete carrier of KL6/KL7/KL22: a term is a monomial `∏_m n_{G_m}` carried by a finite
family `c : Fin M → (Fin 6 → ℤ)` of reciprocal indices, admissible iff it is invariant under every
physical translation (`KL22.monoPhase c u = 1` for all `u`). -/

/-- **Note L761, column 2.** "stability under perturbation: total: no admissible term can break it
(§4.8(4))." No admissible perturbation can make the uniform phason selectable: an admissible term
(invariant under every physical translation) is *w-independent* — its phason phase factor is trivial
for every uniform phason shift. This is `KL7.no_admissible_perturbation_selects` (§4.8 reason 4). -/
theorem unbreakable {M : ℕ} (c : Fin M → (Fin 6 → ℤ))
    (hadm : ∀ u : Fin 3 → ℝ, KL22.monoPhase c u = 1) :
    ∀ w : Fin 3 → ℝ, KL7.phasonPhase c w = 1 :=
  KL7.no_admissible_perturbation_selects c hadm

/-- **Note L762, column 2.** "order of the statement: an identity at **every** order (Lemma 2)." For
an admissible term, with amplitude `A`, the uniform-phason energy `w₀ ↦ A · (phason factor)` is
*strictly constant* (equal to `A` for every shift) and every iterated `w`-derivative of order `k ≥ 1`
vanishes — the No-Pinning identity holds at every order, not merely for a truncation. Admissibility
closes the indices in ℤ⁶ (`KL22.admissible_iff_closure`); `KL6.no_pinning` then applies. -/
theorem identity_at_every_order {M : ℕ} (c : Fin M → (Fin 6 → ℤ))
    (hadm : ∀ u : Fin 3 → ℝ, KL22.monoPhase c u = 1) (A : ℂ) :
    (∀ w₀ : Fin 3 → ℝ, KL6.phasonTerm c A w₀ = A)
      ∧ (∀ k : ℕ, k ≠ 0 → iteratedFDeriv ℝ k (KL6.phasonTerm c A) = 0) := by
  have h0 : (∑ m, c m) = 0 := (KL22.admissible_iff_closure c).mp hadm
  exact ⟨fun w₀ => KL6.phasonTerm_const c h0 A w₀,
         fun k hk => KL6.no_pinning_iteratedFDeriv c h0 A hk⟩

/-! ## §4. KL8 — The symmetry-protection upgrade (Note L767, the icosahedral conjunction)

"the corresponding locus is of full dimension in $E_\perp$, protected by a symmetry, unbreakable by
any admissible perturbation … an identity at every order." The four mathematical rows of column 2 in
one statement; §3's side (`normalFormLocus_volume_zero`, `normalForm_degenerate_card`,
`bias_breaks_branches`) is set beside it. -/

/-- **KL8 — The symmetry-protection upgrade (Note L767).** The indifference of §4, in one statement,
each conjunct her column-2 row:

* **full dimension in `E_⊥`** — every free vector `w₀ ∈ E_⊥` is a global minimizer over `E_⊥`
  (`KL7.isMinOn_free`): the indifferent locus is the whole free subspace, not a measure-zero set;
* **protected by a symmetry** — `J (x + w) = J x` for every `w ∈ E_⊥` (KL6's invariance, carried as
  `hInv`; the Goldstone naming is A11, borrowed);
* **unbreakable by any admissible perturbation** — an admissible term is w-independent
  (`KL7.no_admissible_perturbation_selects` / §4.8 reason 4);
* **an identity at every order** — an admissible term is strictly constant in the uniform phason
  shift and every `w`-derivative of order `k ≥ 1` vanishes (`KL6.no_pinning`, fed by
  `KL22.admissible_iff_closure`).

"The theorem of §3 is unchanged; what has changed is where it lives": §3's measure-zero, two-point,
bias-destroyed indifference is the companion `normalForm_*`. "generic" and "realized" are her
non-mathematical rows (recorded in the header, not mapped). No new mathematics beyond its
constituents. -/
theorem symmetry_protection_upgrade
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Eperp : Submodule ℝ E) (J : E → ℝ)
    (hInv : ∀ x : E, ∀ w ∈ Eperp, J (x + w) = J x) (x : E)
    {M : ℕ} (c : Fin M → (Fin 6 → ℤ))
    (hadm : ∀ u : Fin 3 → ℝ, KL22.monoPhase c u = 1) (A : ℂ) :
    (∀ w₀ ∈ Eperp, IsMinOn (fun w => J (x + w)) (Eperp : Set E) w₀)
      ∧ (∀ w ∈ Eperp, J (x + w) = J x)
      ∧ (∀ w : Fin 3 → ℝ, KL7.phasonPhase c w = 1)
      ∧ (∀ w₀ : Fin 3 → ℝ, KL6.phasonTerm c A w₀ = A)
      ∧ (∀ k : ℕ, k ≠ 0 → iteratedFDeriv ℝ k (KL6.phasonTerm c A) = 0) := by
  have h0 : (∑ m, c m) = 0 := (KL22.admissible_iff_closure c).mp hadm
  exact ⟨fun w₀ hw₀ => KL7.isMinOn_free Eperp J hInv x hw₀,
         fun w hw => hInv x w hw,
         KL7.no_admissible_perturbation_selects c hadm,
         fun w₀ => KL6.phasonTerm_const c h0 A w₀,
         fun k hk => KL6.no_pinning_iteratedFDeriv c h0 A hk⟩

end ExistenceSystem.KL8

end
