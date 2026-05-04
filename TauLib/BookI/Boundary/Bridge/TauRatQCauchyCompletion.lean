import TauLib.BookI.Boundary.Bridge.TauRatQuotient
import TauLib.BookI.Boundary.Bridge.TauRatQTransport
import Mathlib.Algebra.Order.CauSeq.Completion
import Mathlib.Algebra.Algebra.Basic

/-!
# TauLib.BookI.Boundary.Bridge.TauRatQCauchyCompletion

**Workstream B2.alg / W3 (Path B, Step 1) — Cauchy completion of
TauRatQ via Mathlib's `CauSeq.Completion.Cauchy`**.

Substrate verification step: instantiates Mathlib's canonical
Cauchy-completion construction at base ring `TauRatQ` (which has
`LinearOrderedField` from Wave 44, hence the `IsStrictOrderedRing`
+ `LinearOrder` + `Field` substrate that
`CauSeq.Completion.Cauchy` requires).

## What this ships

- **`TauRatQCauchy`** abbreviation: `CauSeq.Completion.Cauchy
  (abs : TauRatQ → TauRatQ)` — Mathlib's Cauchy completion of
  TauRatQ as a τ-native intermediate target for the
  `TauRealQ →+* ℝ` bridge.
- Verification handles: the auto-derived `Field` structure (and
  optional `Algebra TauRatQ TauRatQCauchy`) confirm Mathlib's
  Cauchy machinery accepts TauRatQ as base.

## Strategic context

Per the **effective-reals research finding** (atlas insights doc
2026-05-04), Mathlib has no named effective-reals type, but
`CauSeq.Completion.Cauchy` is the constructive carrier underlying
ℝ. Targeting it (rather than ℝ directly) is **Path B** — the
cleanest unblock for the full `TauRealQ →+* ℝ` bridge needed by
W3 full + W3b.

Subsequent Path B sub-PRs:
- **Step 2** (queued): `TauRealQ ≃+* TauRatQCauchy` (the
  τ-native ↔ Mathlib-Cauchy bridge — the substantive work)
- **Step 3** (queued): `TauRatQCauchy ≃+*
  CauSeq.Completion.Cauchy (abs : ℚ → ℚ)` (transport via Wave 40
  `TauRatQ ≃+* ℚ`)
- **Step 4** (queued): use `Real.ringEquivCauchy` to bridge to ℝ
- **Compose**: `TauRealQ ≃+* ℝ` — unblocks W3 full + W3b

This module ships **Step 1** only — the substrate check.

## Substrate dependencies

- `TauRatQuotient.lean` (Wave 40): `Field TauRatQ`
- `TauRatQTransport.lean` (Wave 44): `LinearOrderedField TauRatQ`
  + `IsStrictOrderedRing TauRatQ`
- Mathlib: `CauSeq.Completion.Cauchy`, `abs_isAbsoluteValue`

## Atlas cross-references

- `atlas/insights/2026-05-04-mathlib-has-no-effective-reals.md`
  (the research finding that motivated this Path B)
- `atlas/insights/2026-04-29-constructive-real-cardinality-boundary.md`
  (the Markov boundary at LinearOrderedField, sidestepped here
  by stopping at the Cauchy carrier level)

## Registry Cross-References

- [I.T-W40-Field]                  `Field TauRatQ` (substrate)
- [I.T-W44-LinearOrderedField]     `LinearOrderedField TauRatQ`
                                   (substrate)
- [I.T-B2.alg.W3-pathB-step1]      `TauRatQCauchy` Cauchy
                                   completion of TauRatQ (this
                                   module)
-/

set_option autoImplicit false

namespace Tau.Boundary

open Tau.Denotation

-- ============================================================
-- B2.alg / W3 Path B / Step 1: TauRatQCauchy substrate
-- ============================================================

/-- **`TauRatQCauchy` — Mathlib's Cauchy completion of TauRatQ**,
    using the absolute value `abs : TauRatQ → TauRatQ`.

    Defined as `CauSeq.Completion.Cauchy (abs : TauRatQ → TauRatQ)`.

    This is the **constructive carrier** underlying ℝ when ℚ is
    replaced by TauRatQ. Carries `CommRing` + `Field`
    (noncomputable) + `Algebra TauRatQ` from Mathlib's auto-
    derivation. Does NOT carry `LinearOrderedField` (the Markov
    wall) — appropriate for a constructive bridge target. -/
noncomputable abbrev TauRatQCauchy : Type :=
  CauSeq.Completion.Cauchy (abs : TauRatQ → TauRatQ)

-- ============================================================
-- Verification handles
-- ============================================================

/-- **Verification handle 1**: `TauRatQCauchy` has `CommRing`. -/
noncomputable example : CommRing TauRatQCauchy := inferInstance

/-- **Verification handle 2**: `TauRatQCauchy` has `Field`
    (noncomputable, but constructively defined modulo the `inv`
    decision — same setup as Mathlib's ℝ at the carrier level). -/
noncomputable example : Field TauRatQCauchy := inferInstance

-- Note: `Algebra TauRatQ TauRatQCauchy` would need explicit
-- construction (Mathlib doesn't auto-derive it from
-- `CauSeq.Completion.Cauchy`). Natural construction via
-- `RingHom.toAlgebra (CauSeq.Completion.ofRat : TauRatQ →+*
-- TauRatQCauchy)`; deferred to **Step 2** of the Path B
-- follow-up (not strictly needed for this substrate
-- verification).

end Tau.Boundary
