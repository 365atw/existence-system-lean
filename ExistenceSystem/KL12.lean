module

/-
KL12 — the definition of free and bound, from THE EXACT AND FREE SYSTEM —
AN EXISTENCE SYNTHESIS.
All mathematics: Kari A Light.

Source: `THE-NOTE-EDITED.md` (194,868 bytes, 1,539 lines). Line numbers below refer to that file.
Her words are quoted exactly beside each statement. Nothing of hers is graded here.

The coil law `r_{k+1} = φ^{-3} * r_k` is taken as the hypothesis (captain's ruling; §7.1), and is
`ExistenceSystem.KL13.residual` — the merged coil-law sequence, reused here so the law keeps one home
(cf. the KL13 header; the coil faces are not given a second home). KL12 is the definition KL13 and
KL14 rest on; it is placed on top of that residual so the finite-coil corollary can be read in its own
words with no second copy of the law.

Captain's ruling: `free` and `bound` are predicates on the near-touch residual `r : ℝ` directly. The
fuller "configuration" object (the conjugate face-pair φ^{3k}/σ(φ)^{3k} at coil `k`, with `r` its
scalar measure, and its place on the ascent) is deferred to later work and is out of scope here; the
scalar residual `r` is the carrier.
-/
public import ExistenceSystem.KL13

@[expose] public section

open Real
open scoped goldenRatio

namespace ExistenceSystem.KL12

/-- Note line 108 (list form): "A configuration is **free** while the near-touch residual `r > 0` and
**bound** when `r = 0`."

Note lines 993–995 (body): "**Definition (KL12 — free and bound).** Let `r_k` be the near-touch
residual at coil `k`, with `r_0 > 0` and `r_{k+1} = φ^{-3} r_k` (the coil law; Appendix B). A
configuration is **free** while `r > 0` and **bound** when `r = 0`."

Per the captain's ruling the predicate is taken on the residual `r : ℝ` directly; the fuller
configuration object is deferred. This is the **free** half: a configuration is free while `r > 0`. -/
def free (r : ℝ) : Prop := 0 < r

/-- Note line 108 / lines 993–995: a configuration is **bound** when `r = 0`. The **bound** half of
KL12's definition, taken on the residual `r : ℝ` directly (captain's ruling). -/
def bound (r : ℝ) : Prop := r = 0

/-- On the ascent (`0 ≤ r`) the two halves of the definition are exclusive and exhaustive: a residual
is `free` exactly when it is not `bound`. This is the sense in which her "free while `r > 0`" and
"bound when `r = 0`" partition the non-negative residuals. -/
theorem free_iff_not_bound_of_nonneg {r : ℝ} (hr : 0 ≤ r) : free r ↔ ¬ bound r :=
  ⟨fun h => ne_of_gt h, fun h => lt_of_le_of_ne hr (Ne.symm h)⟩

/-- The coil residual is `free` at every finite coil. With `r_0 > 0` the near-touch residual stays
positive, by KL13's positivity (`ExistenceSystem.KL13.residual_pos`), read through `free`. -/
theorem residual_free (r₀ : ℝ) (hr : 0 < r₀) (k : ℕ) : free (KL13.residual r₀ k) :=
  KL13.residual_pos r₀ hr (by positivity) k

/-- Note line 110 and the Corollary at Note line 999: "No configuration is bound at any finite coil."
Read through KL12's predicates: with `r_0 > 0` the coil residual is `free`, hence not `bound`, at
every finite coil `k`. -/
theorem not_bound_residual (r₀ : ℝ) (hr : 0 < r₀) (k : ℕ) : ¬ bound (KL13.residual r₀ k) := by
  have h : free (KL13.residual r₀ k) := residual_free r₀ hr k
  exact (free_iff_not_bound_of_nonneg (le_of_lt h)).mp h

end ExistenceSystem.KL12

end
