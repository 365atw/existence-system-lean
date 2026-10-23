module

/-
KL19 — The NO BETTER Theorem (an impossibility result), from THE EXACT AND FREE SYSTEM —
AN EXISTENCE SYNTHESIS.
All mathematics: Kari A Light.

Source: `THE-NOTE-EDITED.md` (194,868 bytes, 1,539 lines). Line numbers below refer to that file.
Her words are quoted exactly beside each statement. Nothing of hers is graded here.

Note L716 (§4.8), the exact statement:
"**The NO BETTER Theorem (KL19).** The word *finite* is load-bearing, and it is what turns the
geometry into a statement about Hamiltonians. A finite-range interaction assigns energy patch by
patch, so the energy **density** of a configuration is a fixed function of its **finite**-patch
frequencies. Equal finite-patch frequencies therefore force equal energy density: **no finite-range
Hamiltonian — at any order, of any complexity, at any temperature — can rank the members of the
family.** That is protection against a whole *class* of Hamiltonians, not the protection of one
Hamiltonian by one symmetry, and it is the reason the degeneracy of §4.8 cannot be removed by
writing down a better energy. Drop the word *finite* and the claim is simply false: distinct $w$
give genuinely distinct **infinite** structures, and an interaction of unbounded range can see the
difference. *Rests on cited prior art [48, 49].*"

Note L122 (list form):
"**KL19 — The NO BETTER Theorem.** *(impossibility result.)* A finite-range interaction assigns
energy patch by patch, so a configuration's energy density is a fixed function of its finite-patch
frequencies — and the members of one local-isomorphism class have identical finite-patch
frequencies. **Therefore no finite-range Hamiltonian, at any order, of any complexity, at any
temperature, can rank them: there is no better energy to be written.** The word *finite* is
load-bearing: distinct uniform phason values give genuinely distinct *infinite* structures, and an
interaction of unbounded range can tell them apart. *Proved in §4.8. Rests on cited prior
art [48, 49].*"

Attribution (her ledger, 2026-08-20, quoted in `data/lean-scope-b/report.md` §6d and
`data/lean-scope-b/G5.md` §5): "(Repetitivity and local indistinguishability of one LI class are
established and cited [48, 49]; the consequence for finite-range Hamiltonians is the author's.)"
So the premise — the members of one local-isomorphism class have identical finite-patch
frequencies ([48] Baake–Grimm, *Aperiodic Order* vol. 1; [49] Baake–Hermisson–Pleasants) — is
**borrowed, not hers**. It is carried below as the EXPLICIT HYPOTHESIS `LIClassEqualFreq`, never
proved, never an axiom. The consequence for finite-range Hamiltonians is hers and is what the
theorems here prove.

What is modelled, and what is left as prose (`data/lean-scope-b/G5.md` §5.2, §5.5):
- Finite local complexity — "finitely many `R`-patches up to translation" — is `Fintype (Patch R)`.
  It is what makes the energy density a *finite* sum, and it is where the word *finite* is
  load-bearing.
- "a configuration's energy density is a fixed function of its finite-patch frequencies" is
  `energyDensity`: the finite sum `∑ p, freq p * e p` of the interaction's per-patch energies `e`
  weighted by the configuration's patch frequencies `freq`. `freq_eq_of_energyDensity_eq` makes the
  "fixed function" sharp — the finite-patch frequencies are exactly what finite-range energy
  densities see.
- "at any order, of any complexity" reads as the two quantifiers ∀ range `R`, ∀ interaction
  `e : Patch R → ℝ`: every many-body order (the `R`-patch already carries every point within
  range `R`) and every assignment of per-patch energies is included.
- "at any temperature" is NOT encoded: the Note gives no definition of how temperature enters for a
  fixed configuration — an ensemble, a free-energy density (`G5.md` §5.5, "the text is prose rather
  than proof"). No thermodynamics is built; the statement is the athermal (energy-density) core.
- "Drop the word *finite* … an interaction of unbounded range can see the difference" is NOT
  encoded: unbounded-range interactions and their energy density are not defined in the Note
  (`G5.md` §5.5). It stands as the reading of the theorem's scope.
- The point sets, the acceptance window (record note **H5(b)**: "the window is never defined, never
  shaped, never bounded"; hers to write) and the phason torus (**H5(a)**) are NOT built; the family
  is carried abstractly as a type `W` with the borrowed LI-class premise above (the inferred edge to
  U33 / KL11 / A9, `G5.md` §5.3).
-/
public import Mathlib

@[expose] public section

namespace ExistenceSystem.KL19

open Finset

/- `Patch R` is the type of `R`-patches up to translation. **Finite local complexity** — the fact
that a configuration has only finitely many distinct `R`-patches up to translation — is carried as
`[∀ R, Fintype (Patch R)]`; it is what makes the energy density a *finite* sum (Note L716, the word
*finite*). -/
variable {Patch : ℕ → Type*} [∀ R, Fintype (Patch R)]

/-- The energy density a finite-range interaction of range `R` assigns to a configuration.

Note L716: "A finite-range interaction assigns energy **patch by patch**, so the energy **density**
of a configuration is a fixed function of its **finite**-patch frequencies." The interaction
`e : Patch R → ℝ` is its energy per `R`-patch (every many-body order of range `R` is such a
function); `freq : Patch R → ℝ` is the configuration's `R`-patch frequencies. Finite local
complexity (`Fintype (Patch R)`) makes this the finite sum `∑ p, freq p * e p`. -/
noncomputable def energyDensity {R : ℕ} (e freq : Patch R → ℝ) : ℝ :=
  ∑ p, freq p * e p

/-- Note L716, the heart: the energy density is "a fixed function of its finite-patch frequencies".
Configurations with equal finite-patch frequencies get equal energy density from every finite-range
interaction `e`. -/
theorem energyDensity_eq_of_freq_eq {R : ℕ} (e : Patch R → ℝ) {freq₁ freq₂ : Patch R → ℝ}
    (h : freq₁ = freq₂) : energyDensity e freq₁ = energyDensity e freq₂ := by
  rw [h]

/-- The sharp form of "a fixed function of its finite-patch frequencies": the finite-patch
frequencies are *exactly* what finite-range energy densities see. If two configurations are assigned
the same energy density by **every** finite-range interaction of range `R`, their `R`-patch
frequencies coincide. Hence the energy-density map does not merely factor through the frequencies —
the frequencies are a complete invariant for it. -/
theorem freq_eq_of_energyDensity_eq {R : ℕ} {freq₁ freq₂ : Patch R → ℝ}
    (h : ∀ e : Patch R → ℝ, energyDensity e freq₁ = energyDensity e freq₂) : freq₁ = freq₂ := by
  classical
  funext q
  -- Probe with the interaction `Pi.single q 1` (energy 1 on patch `q`, 0 elsewhere): its energy
  -- density on a configuration reads off that configuration's frequency of patch `q`.
  have key : ∀ f : Patch R → ℝ, energyDensity (Pi.single q (1 : ℝ)) f = f q := by
    intro f
    simp only [energyDensity]
    rw [Finset.sum_eq_single q]
    · rw [Pi.single_eq_same, mul_one]
    · intro p _ hpq; rw [Pi.single_eq_of_ne hpq, mul_zero]
    · intro hq; exact absurd (Finset.mem_univ q) hq
  have hq := h (Pi.single q (1 : ℝ))
  rw [key freq₁, key freq₂] at hq
  exact hq

/-- The borrowed premise [48, 49], carried as a hypothesis and **never proved**: members of one
local-isomorphism class have identical finite-patch frequencies at every range.

Note L714: "**every *finite* patch of one occurs in the other with identical frequency**"
(repetitivity, equivalently the local indistinguishability of members of one LI class). Her ledger
(2026-08-20) credits this to [48, 49] and keeps only the consequence for finite-range Hamiltonians as
her own. `sameLIClass` (the LI-class relation) and `freq` (each member's patch frequencies) are the
objects of that borrowed theory; neither the window (H5(b)) nor the torus (H5(a)) is built here. -/
def LIClassEqualFreq {W : Type*} (sameLIClass : W → W → Prop)
    (freq : W → ∀ R, Patch R → ℝ) : Prop :=
  ∀ ⦃w w' : W⦄, sameLIClass w w' → ∀ R, freq w R = freq w' R

/-- A finite-range interaction of range `R` **ranks** member `w` strictly below `w'` when it assigns
`w` the strictly smaller energy density. Note L716 / L122: "can rank the members of the family". -/
def Ranks {W : Type*} (freq : W → ∀ R, Patch R → ℝ) (R : ℕ) (e : Patch R → ℝ) (w w' : W) : Prop :=
  energyDensity e (freq w R) < energyDensity e (freq w' R)

/-- Note L716: "Equal finite-patch frequencies therefore force equal energy density." For two
members of one LI class (equal frequencies at every range, via the borrowed premise), every
finite-range interaction assigns them equal energy density. -/
theorem energyDensity_eq_of_liClass {W : Type*} {freq : W → ∀ R, Patch R → ℝ} {w w' : W}
    (hfreq : ∀ R, freq w R = freq w' R) (R : ℕ) (e : Patch R → ℝ) :
    energyDensity e (freq w R) = energyDensity e (freq w' R) :=
  energyDensity_eq_of_freq_eq e (hfreq R)

/-- Note L716 / L122: "**no finite-range Hamiltonian … can rank the members of the family … there
is no better energy to be written.**" No finite-range interaction ranks one LI-class member below
another, either way. -/
theorem not_ranks_of_liClass {W : Type*} {freq : W → ∀ R, Patch R → ℝ} {w w' : W}
    (hfreq : ∀ R, freq w R = freq w' R) (R : ℕ) (e : Patch R → ℝ) :
    ¬ Ranks freq R e w w' := by
  intro hr
  -- `Ranks …` is `energyDensity e (freq w R) < energyDensity e (freq w' R)` by definition.
  have hlt : energyDensity e (freq w R) < energyDensity e (freq w' R) := hr
  rw [energyDensity_eq_of_liClass hfreq R e] at hlt
  exact lt_irrefl _ hlt

/-- **The NO BETTER Theorem (KL19), Note L716 / L122.** Given the borrowed local-isomorphism premise
`hLI` ([48, 49], carried, never proved) and two members `w`, `w'` of one LI class (`hmem`), **no
finite-range Hamiltonian — at any range `R`, of any complexity `e` — can rank one below the
other**: each such interaction assigns them equal energy density, so neither is ranked below the
other.

"Equal finite-patch frequencies therefore force equal energy density: no finite-range Hamiltonian —
at any order, of any complexity, at any temperature — can rank the members of the family." The
premise `hLI` is the borrowed content of [48, 49]; the consequence below is hers. -/
theorem no_better {W : Type*} {sameLIClass : W → W → Prop} {freq : W → ∀ R, Patch R → ℝ}
    (hLI : LIClassEqualFreq sameLIClass freq) {w w' : W} (hmem : sameLIClass w w')
    (R : ℕ) (e : Patch R → ℝ) :
    energyDensity e (freq w R) = energyDensity e (freq w' R) ∧ ¬ Ranks freq R e w w' :=
  ⟨energyDensity_eq_of_liClass (hLI hmem) R e, not_ranks_of_liClass (hLI hmem) R e⟩

end ExistenceSystem.KL19

end
