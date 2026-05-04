import TauLib.BookI.Boundary.Bridge.TauRatQuotient
import TauLib.BookI.Boundary.Bridge.TauRatQTransport

/-!
# TauLib.BookI.Boundary.Bridge.TauRatQRingEquivConversions

**Workstream B2.alg / W3 (Path B, Step 2-pre-2) — `TauRatQ.toRat`
ring-hom preservation lemmas (NatCast, division, etc.)**.

Ships the **second substrate sub-PR** unblocking Path B Step 2.
While Step 2-pre (PR #149) shipped 4 abs/lt/Archimedean
conversion lemmas, Step 2's forward function additionally
requires `TauRatQ.toRat` to preserve **NatCast** and
**division** when translating bounds like `(1 : TauRatQ) / (N + 1 : ℕ)`.

These follow from Wave 40's `TauRatQ.ringEquivRat : TauRatQ ≃+* ℚ`
being a `RingEquiv` — Mathlib's auto `RingHom`-class instances
provide NatCast / div preservation. We just need to express them
in terms of `TauRatQ.toRat` (the underlying function of
`ringEquivRat`).

## What this ships

Three small lemmas (~5-10 lines each):

- **`TauRatQ.toRat_eq_ringEquivRat`** — the underlying-function
  identity: `TauRatQ.toRat = ringEquivRat.toFun` (essentially
  `rfl`, makes downstream rewrites clean)
- **`TauRatQ.toRat_natCast`** — `((n : ℕ) : TauRatQ).toRat =
  (n : ℚ)` via Mathlib's `map_natCast` on the ring iso
- **`TauRatQ.toRat_div`** — `(x / y).toRat = x.toRat / y.toRat`
  for `x y : TauRatQ` via `RingEquiv.map_div` on ringEquivRat

## Substrate dependencies

- `TauRatQuotient.lean` (Wave 40): `Field TauRatQ`,
  `TauRatQ.ringEquivRat : TauRatQ ≃+* ℚ`, `TauRatQ.toRat`
- `TauRatQTransport.lean` (Wave 44): `LinearOrderedField TauRatQ`
  + transport preserves the underlying ring structure
- Mathlib: `RingEquiv.toRingHom`, `map_natCast`,
  `RingEquiv.map_div`

## What this unlocks

Path B Step 2 (the forward function `cauSeqOfCauchyTauReal :
CauchyTauReal → CauSeq TauRatQ abs`) becomes tractable: with
NatCast + division preserved, the chain `((1 : TauRatQ) / (N + 1
: ℕ)).toRat = (1 : ℚ) / (N + 1 : ℕ)` closes cleanly, allowing
the IsCauSeq witness translation to complete without sorry.

## Atlas cross-references

- `atlas/insights/2026-05-04-mathlib-has-no-effective-reals.md`

## Registry Cross-References

- [I.T-W40-RingEquiv]               `TauRatQ ≃+* ℚ` (substrate)
- [I.T-B2.alg.W3-pathB-step2pre]    Step 2-pre (abs/lt/Archimedean)
- [I.T-B2.alg.W3-pathB-step2pre2]   Step 2-pre-2 (NatCast/div)
                                    (this module)
-/

set_option autoImplicit false

namespace Tau.Boundary

open Tau.Denotation

-- ============================================================
-- B2.alg / W3 Path B / Step 2-pre-2: NatCast + division preservation
-- ============================================================

/-- **`TauRatQ.toRat` is the underlying function of `ringEquivRat`**.
    Definitional identity making downstream rewrites via Mathlib's
    `RingHom` / `RingEquiv` classes clean. -/
theorem TauRatQ.toRat_eq_ringEquivRat (x : TauRatQ) :
    x.toRat = TauRatQ.ringEquivRat x := rfl

/-- **`TauRatQ.toRat` preserves NatCast**: `((n : ℕ) : TauRatQ).toRat
    = (n : ℚ)`.

    Follows from Mathlib's `map_natCast` on the
    `RingEquiv TauRatQ ℚ`. -/
@[simp] theorem TauRatQ.toRat_natCast (n : ℕ) :
    ((n : TauRatQ) : TauRatQ).toRat = (n : ℚ) := by
  rw [TauRatQ.toRat_eq_ringEquivRat]
  exact map_natCast TauRatQ.ringEquivRat n

/-- **`TauRatQ.toRat` preserves division**: `(x / y).toRat =
    x.toRat / y.toRat` for `x y : TauRatQ`.

    Follows from `RingEquiv.map_div` on the `Field` structure of
    TauRatQ ≃+* ℚ. -/
@[simp] theorem TauRatQ.toRat_div (x y : TauRatQ) :
    (x / y).toRat = x.toRat / y.toRat := by
  rw [TauRatQ.toRat_eq_ringEquivRat,
      TauRatQ.toRat_eq_ringEquivRat,
      TauRatQ.toRat_eq_ringEquivRat]
  exact map_div₀ TauRatQ.ringEquivRat x y

end Tau.Boundary
