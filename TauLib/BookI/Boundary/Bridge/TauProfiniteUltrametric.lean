import TauLib.BookI.Boundary.Bridge.TauProfiniteSeparation
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# TauLib.BookI.Boundary.Bridge.TauProfiniteUltrametric

**Workstream B1.3.5 — canonical ultrametric distance on `TauProfinite`**.

This module ships the **named anchor** for the canonical ultrametric
topology + Tarski geometry on `TauProfinite`, defined per Book II of
the Panta Rhei monograph (Part 02 ch10, registry `[II.D12]` + `[II.D13]`,
ultrametric inequality `[II.T05]`).

Future Mathlib `Topology` and `Geometry` typeclass instances on
`TauProfinite` MUST instantiate against the functions defined here,
NOT against any contingent boundary scalar readout (`OrthodoxBridge`,
`DefectInverseSystem`, `den : τ³ → ℝ⁴`, etc.).

See the binding spec dossier
[`atlas/audits/taulib/2026-05-04-canonical-topology-geometry-spec.md`](https://github.com/Panta-Rhei-Research/atlas/blob/main/audits/taulib/2026-05-04-canonical-topology-geometry-spec.md)
for the full anchoring discipline (Part 6 anti-spec; Part 7
verification handles).

## Mathematical content

Manuscript Book II Part 02 ch10:

- **First disagreement depth** (`[II.D12]`):
  `δ(x,y) := max{k ≥ 0 | π_k(x) = π_k(y)}` (or `∞` if `x = y`).
- **Canonical ultrametric distance** (`[II.D13]`):
  `d(x,y) := 2^(-δ(x,y))` with `2^(-∞) = 0`.
- **Ultrametric inequality** (`[II.T05]`):
  `d(x,z) ≤ max(d(x,y), d(y,z))`.

This module ships the explicit Lean definitions of `δ` and `d` (as
named functions on `TauProfinite × TauProfinite`) plus a small set of
basic well-formedness lemmas (`_self`, `_symm`, `_nonneg`).
The full metric-axiom proofs and the `MetricSpace TauProfinite`
instance land in **B1.4**.

**Convention note**: manuscript `[II.D12]` defines `δ` as the depth
of the *last agreement* (so `δ ≥ 0`). This Lean encoding uses
`firstDisagreementDepth`, the depth of the *first disagreement*
(so `firstDisagreementDepth ≥ 0` likewise, but offset by one from
manuscript's `δ`). The two encodings are interconvertible; the
resulting `ultrametricDistance = 2^(-firstDisagreementDepth)` differs
from manuscript's `d = 2^(-δ)` by a constant factor of 2 — both
generate the same metric topology and ultrametric structure (the
inequality `[II.T05]` is preserved by any positive scaling).

## Registry Cross-References

- [I.D14]                Instruction / Program (substrate)
- [II.D10]               Stage-k cylinder (already wired in `TauProfiniteTopology.lean`)
- [II.D12]               First disagreement depth `δ` (this module)
- [II.D13]               Ultrametric distance `d = 2^(-δ)` (this module)
- [II.T05]               Ultrametric inequality (B1.4 will prove)
- [II.T08]               Hausdorff (already proven in `TauProfiniteSeparation.lean`)
- [II.T10]               Topology Uniqueness Theorem (canonicity anchor;
                          formal proof out of scope, cited in B1.4 docstring)
- [II.T42]               Categoricity Theorem (global canonicity warrant;
                          formal proof out of scope)

## Cross-references

- `atlas/audits/taulib/2026-05-04-canonical-topology-geometry-spec.md`
  — the binding anchoring spec for B1.4 / B1.5
- `atlas/audits/taulib/2026-05-03-foundations-bridges-state-of-the-union.md`
  — parent A1 dossier with the 9-wave Workstream B1 roadmap
- `BookI/Boundary/Bridge/TauProfiniteTopology.lean` (Wave 50) —
  cylinder topology
- `BookI/Boundary/Bridge/TauProfiniteSeparation.lean` (Wave 51) —
  Hausdorff + totally disconnected, plus the
  `exists_separating_depth` lemma we use to ensure
  `firstDisagreementDepth` is well-defined for `x ≠ y`.
-/

set_option autoImplicit false

namespace Tau.Boundary

open Tau.Denotation

namespace TauProfinite

-- ============================================================
-- PART 1: First disagreement depth `δ` (II.D12)
-- ============================================================

/-- **First disagreement depth** between two `TauProfinite` elements.

    Returns:
    - `none` if `x = y` (formally `δ = ∞`),
    - `some k` if `x ≠ y` and `k` is the smallest depth at which
      `x.proj k ≠ y.proj k`.

    The existence of `k` for `x ≠ y` is guaranteed by
    `exists_separating_depth` (Wave 51). The smallest such `k`
    is selected via `Nat.find`.

    Manuscript convention note: this `firstDisagreementDepth` differs
    from manuscript `[II.D12]`'s `δ` (depth of *last* agreement) by an
    offset; the two are interconvertible. See module docstring. -/
noncomputable def firstDisagreementDepth (x y : TauProfinite) : Option ℕ :=
  open Classical in
  if h : ∃ k : ℕ, x.proj k ≠ y.proj k then
    some (Nat.find h)
  else
    none

/-- A point has no first-disagreement depth with itself. -/
theorem firstDisagreementDepth_self (x : TauProfinite) :
    firstDisagreementDepth x x = none := by
  unfold firstDisagreementDepth
  rw [dif_neg]
  push_neg
  intro k
  rfl

/-- The first-disagreement depth is symmetric in its two arguments. -/
theorem firstDisagreementDepth_symm (x y : TauProfinite) :
    firstDisagreementDepth x y = firstDisagreementDepth y x := by
  unfold firstDisagreementDepth
  by_cases h_xy : ∃ k : ℕ, x.proj k ≠ y.proj k
  · -- Case x ≠ y at some depth: the symmetric witness exists for y x
    have h_yx : ∃ k : ℕ, y.proj k ≠ x.proj k := by
      obtain ⟨k, hk⟩ := h_xy
      exact ⟨k, fun h => hk h.symm⟩
    rw [dif_pos h_xy, dif_pos h_yx]
    -- Both Nat.find values agree because the disagreement-at-k predicate
    -- is symmetric in x ↔ y modulo Eq.symm
    have h_eq : (fun k => x.proj k ≠ y.proj k) = (fun k => y.proj k ≠ x.proj k) := by
      funext k
      exact propext ⟨fun h h' => h h'.symm, fun h h' => h h'.symm⟩
    simp only [h_eq]
  · -- Case x = y at all depths: both sides are `none`
    have h_yx : ¬ ∃ k : ℕ, y.proj k ≠ x.proj k := by
      push_neg at h_xy ⊢
      intro k
      exact (h_xy k).symm
    rw [dif_neg h_xy, dif_neg h_yx]

-- ============================================================
-- PART 2: Canonical ultrametric distance `d = 2^(-δ)` (II.D13)
-- ============================================================

/-- **Canonical ultrametric distance** on `TauProfinite`.

    `d(x, y) := 2^(-firstDisagreementDepth x y)` with the convention
    `2^(-∞) = 0` (i.e. `d(x, x) = 0`).

    Concretely:
    - `d(x, x) = 0`
    - `d(x, y) = 1 / 2^k` when `firstDisagreementDepth x y = some k`

    Distance values lie in the discrete set `{0} ∪ {1/2^k : k ≥ 0}`,
    matching manuscript `[II.D13]` up to a constant factor of 2 (see
    module docstring on convention).

    This is the **canonical and unique** ultrametric on `TauProfinite`
    per the Topology Uniqueness Theorem `[II.T10]`; future Mathlib
    `MetricSpace TauProfinite` (B1.4) instances must wrap this
    function. -/
noncomputable def ultrametricDistance (x y : TauProfinite) : ℚ :=
  match firstDisagreementDepth x y with
  | none   => 0
  | some k => (1 : ℚ) / (2 ^ k)

/-- The ultrametric distance from a point to itself is zero. -/
theorem ultrametricDistance_self (x : TauProfinite) :
    ultrametricDistance x x = 0 := by
  unfold ultrametricDistance
  rw [firstDisagreementDepth_self]

/-- The ultrametric distance is symmetric. -/
theorem ultrametricDistance_symm (x y : TauProfinite) :
    ultrametricDistance x y = ultrametricDistance y x := by
  unfold ultrametricDistance
  rw [firstDisagreementDepth_symm]

/-- The ultrametric distance is non-negative. -/
theorem ultrametricDistance_nonneg (x y : TauProfinite) :
    0 ≤ ultrametricDistance x y := by
  unfold ultrametricDistance
  cases firstDisagreementDepth x y with
  | none => exact le_refl 0
  | some k =>
    have h_pow_pos : (0 : ℚ) < 2 ^ k := by positivity
    exact div_nonneg (by norm_num) (le_of_lt h_pow_pos)

/-- The ultrametric distance is strictly bounded above by 2. -/
theorem ultrametricDistance_lt_two (x y : TauProfinite) :
    ultrametricDistance x y < 2 := by
  unfold ultrametricDistance
  cases firstDisagreementDepth x y with
  | none => norm_num
  | some k =>
    have h_pow_pos : (0 : ℚ) < 2 ^ k := by positivity
    have h_pow_ge_one : (1 : ℚ) ≤ 2 ^ k := by
      have : (1 : ℚ) = (1 : ℚ) ^ k := by simp
      rw [this]
      exact pow_le_pow_left₀ (by norm_num) (by norm_num) k
    have h_div_le : (1 : ℚ) / (2 ^ k) ≤ 1 := by
      rw [div_le_iff₀ h_pow_pos, one_mul]
      exact h_pow_ge_one
    linarith

end TauProfinite

end Tau.Boundary
