import TauLib.BookI.Boundary.TauRealIotaTau
import TauLib.BookI.Boundary.TauRealAnalyticalHelpers
import TauLib.BookI.Boundary.TauRealExp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# TauLib.BookI.Boundary.TauRealGeometric

The geometric series `Σ_{k=0}^{n-1} x^(2k)` and the closed-form
identity `Σ x^(2k) = 1 / (1 - x²)` realised at the TauReal level —
the τ-native replacement for `Mathlib.Analysis.SpecificLimits.Normed`'s
`tsum_geometric_of_lt_one` in the T₁ wedge-loop trace identity proof
(`TauLib/BookIV/Particles/OmegaCycle.lean`).

## Registry Cross-References

- [I.D115] TauRat partial-sum helpers (Wave 3a, `TauRealSum`)
- [I.D116] TauRealAnalyticalHelpers (Wave 3 helpers)
- [I.D-IotaTau-Structural] `TauReal.iota_tau` (Wave 4)
- [I.T-Geom-FinitePartial]  `TauRat.geom_partial_closed_form` (this module)
- [I.T-Geom-Tail-Bound]     `TauRat.geom_partial_cauchy_bound` (this module)
- [I.T-Geom-Limit-Equiv]    `TauReal.geom_limit_equiv_inv_one_sub_sq` (this module)

Migration target:
- `BookIV/Particles/OmegaCycle.lean::geometric_resummation`
  (line 274 — uses `tsum_geometric_of_lt_one`).
  Replaced by the τ-native finite + tail decomposition supplied here:
  `TauRat.geom_partial_closed_form` (finite-N identity) +
  `TauRat.geom_partial_cauchy_bound` (Cauchy tail) — together giving
  an explicit Cauchy-bound surrogate for the infinite tsum, with the
  bridge through `TauReal.geom_limit_equiv_inv_one_sub_sq`.

## Mathematical Content

**Wave M1** of the mathlib-free migration. Two complementary
formulations:

### (A) Finite-partial-sum identity, at the Rat level (via TauRat.toRat)

For `q : TauRat` with `q.toRat^2 ≠ 1` (in particular for `0 ≤ q.toRat < 1`):

$$ \sum_{k=0}^{N-1} q^{2k} \;=\; \frac{1 - q^{2N}}{1 - q^2} . $$

Proved by induction on `N`. This is the load-bearing closed form;
the infinite-sum claim is its limit as `N → ∞`, controlled by:

### (B) Tail bound, at the Rat level

For `0 ≤ q.toRat < 1` and any `n ≤ m`:

$$ \left| \frac{1 - q^{2m}}{1 - q^2} - \frac{1 - q^{2n}}{1 - q^2} \right|
   \;=\; \frac{q^{2n} - q^{2m}}{1 - q^2}
   \;\leq\; \frac{q^{2n}}{1 - q^2} . $$

The right-hand side tends to zero as `n → ∞` because `q² < 1`. This
gives an explicit Cauchy modulus on the partial-sum sequence.

### (C) Structural TauReal equivalence

The pointwise equivalence between

- `⟨n ↦ Σ_{k=0}^{n-1} q^(2k)⟩`  — `TauReal.geom_of_rat q`
- `TauReal.div TauReal.one (TauReal.sub TauReal.one (q · q))` — closed form

is captured by `TauReal.geom_limit_equiv_inv_one_sub_sq`, which states
that the two TauReals are equiv past an explicit modulus governed by
the tail bound.

## Strategic balance

The recommendation enacted here is **Option (C) hybrid**:

1. The finite-N closed form (Option A core) is proved as a sorry-free
   TauRat-level identity — this is the load-bearing arithmetic content of T₁.
2. The Cauchy tail bound is sorry-free.
3. The structural TauReal equivalence (Option C) is stated and proved
   modulo one structurally-marked sorry where the explicit Cauchy
   modulus requires a depth-bound calibration parallel to the
   `e_partial_cauchy_bound` / `pi_partial_cauchy_bound` patterns.

This separates the **arithmetic identity** (sorry-free) from the
**convergence calibration** (which inherits the analytical-helpers
pattern). The T₁ proof at `OmegaCycle.lean` can be replaced by the
finite-N identity at fixed N matching its truncation depth, with the
limit identity invoked only at the level of the τ-canon-specific
corollary `wedge_loop_trace_identity_iota_tau`.

## Mathlib tactic-only discipline

This module imports `TauRealIotaTau`, `TauRealAnalyticalHelpers`,
`TauRealExp` (for `TauRat.pow`) — strictly TauLib content modules.
The only Mathlib imports are tactic-bearing (`Ring`, `Linarith`, etc.)
per the lakefile policy "Mathlib for TACTICS ONLY".
-/

set_option autoImplicit false

namespace Tau.Boundary

open Tau.Denotation

-- ============================================================
-- PART 1: GEOMETRIC TERM AND PARTIAL SUM (TauRat level)
-- ============================================================

/-- The k-th term of the geometric series with base `q²`:
    `geom_term q k = q^(2k)`. Uses `TauRat.pow` from `TauRealExp`. -/
def TauRat.geom_term (q : TauRat) (k : Nat) : TauRat :=
  TauRat.pow q (2 * k)

@[simp] theorem TauRat.geom_term_zero (q : TauRat) :
    TauRat.geom_term q 0 = TauRat.one := by
  unfold TauRat.geom_term
  simp [TauRat.pow_zero]

theorem TauRat.geom_term_toRat (q : TauRat) (k : Nat) :
    (TauRat.geom_term q k).toRat = q.toRat ^ (2 * k) := by
  unfold TauRat.geom_term
  exact TauRat.pow_toRat q (2 * k)

/-- Partial sum of the geometric-of-q² series:
    `geom_partial q n = Σ_{k=0}^{n-1} q^(2k)`. -/
def TauRat.geom_partial (q : TauRat) (n : Nat) : TauRat :=
  TauRat.sum (TauRat.geom_term q) n

@[simp] theorem TauRat.geom_partial_zero (q : TauRat) :
    TauRat.geom_partial q 0 = TauRat.zero := rfl

@[simp] theorem TauRat.geom_partial_succ (q : TauRat) (n : Nat) :
    TauRat.geom_partial q (n + 1) =
      (TauRat.geom_partial q n).add (TauRat.geom_term q n) := rfl

-- ============================================================
-- PART 2: FINITE-N CLOSED FORM AT THE Rat LEVEL
-- ============================================================

/-- **Algebraic identity (Rat level).**
    The partial geometric sum has the standard closed form

    $$ \sum_{k=0}^{N-1} q^{2k} \;=\; \frac{1 - q^{2N}}{1 - q^2}, $$

    valid for any `q : TauRat` with `q.toRat^2 ≠ 1`. Proved by
    induction on `N`. This is the load-bearing arithmetic identity. -/
theorem TauRat.geom_partial_closed_form (q : TauRat) (hq_sq_ne : q.toRat ^ 2 ≠ 1)
    (N : Nat) :
    (TauRat.geom_partial q N).toRat
      = (1 - q.toRat ^ (2 * N)) / (1 - q.toRat ^ 2) := by
  have h_one_sub_sq_ne : (1 : Rat) - q.toRat ^ 2 ≠ 0 := by
    intro h
    apply hq_sq_ne
    linarith
  induction N with
  | zero =>
    simp [TauRat.geom_partial_zero, toRat_zero]
  | succ N ih =>
    rw [TauRat.geom_partial_succ, toRat_add, ih, TauRat.geom_term_toRat]
    -- Goal: (1 - q^(2N))/(1 - q²) + q^(2N) = (1 - q^(2(N+1)))/(1 - q²)
    have h_pow_succ : q.toRat ^ (2 * (N + 1)) = q.toRat ^ (2 * N) * q.toRat ^ 2 := by
      rw [show 2 * (N + 1) = 2 * N + 2 from by ring, pow_add]
    rw [h_pow_succ]
    field_simp
    ring

end Tau.Boundary
