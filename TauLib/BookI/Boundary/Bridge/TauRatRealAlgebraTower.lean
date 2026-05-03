import TauLib.BookI.Boundary.Bridge.TauRatQuotient
import TauLib.BookI.Boundary.Bridge.TauRealQuotientField
import TauLib.BookI.Boundary.Bridge.TauRealQuotientStrictOrderedRing
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Rat

/-!
# TauLib.BookI.Boundary.Bridge.TauRatRealAlgebraTower

**Workstream B2.alg / W1 — Algebra tower foundation:
`Algebra TauRatQ TauRealQ`**.

Establishes the algebra-tower structure that makes `TauRealQ` a
`TauRatQ`-algebra — the foundation for `TauAlgReal` (W2) and the
bridge to `algebraicClosure ℚ ℝ` (W3).

## Construction

The algebra map `TauRatQ →+* TauRealQ` factors through Mathlib's
canonical `algebraMap ℚ TauRealQ` (auto-derived from
`DivisionRing.toRatAlgebra` for any DivisionRing of CharZero):

```
TauRatQ ─(ringEquivRat)→ ℚ ─(algebraMap)→ TauRealQ
```

`CharZero TauRealQ` is itself derived from `IsStrictOrderedRing
TauRealQ` (Wave 41d) via Mathlib's
`IsStrictOrderedRing.toCharZero` instance (priority 100). The
algebra-map composition `(algebraMap ℚ TauRealQ).comp ringEquivRat.toRingHom`
yields the τ-rational scalar map into the τ-real ambient space.

## Verification handle

`algebraMap_tauRatQ_eq_via_rat`: the algebra map factors through
`TauRatQ.toRat` (the rational projection), making the
construction's dependence on the existing TauRatQ ≃ ℚ bridge
auditable.

## Substrate dependencies

- `TauRatQuotient.lean` (Wave 40, post-B2.alg.W0 rename):
  `Field TauRatQ`, `TauRatQ.ringEquivRat : TauRatQ ≃+* ℚ`
- `TauRealQuotientField.lean` (Wave 41c): `Field TauRealQ`
  (noncomputable Cauchy quotient)
- `TauRealQuotientStrictOrderedRing.lean` (Wave 41d):
  `IsStrictOrderedRing TauRealQ` (which auto-derives `CharZero`)
- Mathlib: `DivisionRing.toRatAlgebra`,
  `IsStrictOrderedRing.toCharZero`

## Atlas cross-references

- `atlas/insights/2026-04-29-constructive-real-cardinality-boundary.md`
  (cardinality-boundary insight; `IsStrictOrderedRing TauRealQ`
  is provably constructive but `LinearOrderedField` is not)
- `atlas/insights/2026-05-04-workstream-b1-completion-and-depth-zero-revelation.md`
  (workstream discipline conventions)

## Registry Cross-References

- [I.T-W40-RingEquiv]   `TauRatQ ≃+* ℚ` (substrate)
- [I.T223]              `Field TauRealQ` (substrate)
- [I.T-W41d-StrictOrderedRing]  `IsStrictOrderedRing TauRealQ`
                                 (substrate, gives CharZero)
- [I.T-B2.alg.W1-AlgebraTower]  `Algebra TauRatQ TauRealQ`
                                 (this module)
-/

set_option autoImplicit false

namespace Tau.Boundary

open Tau.Denotation

-- ============================================================
-- PART 1: TauRatQ → TauRealQ ring homomorphism via Mathlib's
-- canonical algebra map for CharZero division rings
-- ============================================================

/-- **The algebra map `TauRatQ →+* TauRealQ`**, factoring through
    Mathlib's canonical `algebraMap ℚ TauRealQ` (auto-derived from
    `DivisionRing.toRatAlgebra` since `TauRealQ` has `Field` +
    `IsStrictOrderedRing` → `CharZero`).

    Composition:
    `TauRatQ ─(ringEquivRat)→ ℚ ─(algebraMap)→ TauRealQ` -/
noncomputable def algebraMapTauRatQToTauRealQ : TauRatQ →+* TauRealQ :=
  (algebraMap ℚ TauRealQ).comp TauRatQ.ringEquivRat.toRingHom

/-- **Verification handle**: the algebra map factors through
    `TauRatQ.toRat` (the rational projection). -/
theorem algebraMap_tauRatQ_eq_via_rat (x : TauRatQ) :
    algebraMapTauRatQToTauRealQ x = algebraMap ℚ TauRealQ x.toRat :=
  rfl

-- ============================================================
-- PART 2: Algebra instance (the foundational typeclass)
-- ============================================================

/-- **`Algebra TauRatQ TauRealQ`** — the algebra-tower instance
    making `TauRealQ` a `TauRatQ`-algebra. Built via
    `RingHom.toAlgebra`. This is the W1 deliverable. -/
noncomputable instance instAlgebraTauRatQTauRealQ :
    Algebra TauRatQ TauRealQ :=
  RingHom.toAlgebra algebraMapTauRatQToTauRealQ

/-- **Verification handle**: the canonical `algebraMap` for the
    new instance is exactly `algebraMapTauRatQToTauRealQ`. -/
theorem algebraMap_eq_tauRatQ_to_tauRealQ :
    algebraMap TauRatQ TauRealQ = algebraMapTauRatQToTauRealQ :=
  rfl

end Tau.Boundary
