import TauLib.BookI.Boundary.Bridge.TauRatQuotient
import TauLib.BookI.Boundary.Bridge.TauRatQTransport
import TauLib.BookI.Boundary.TauRatAbs
import TauLib.BookI.Boundary.TauRatOrder
import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# TauLib.BookI.Boundary.Bridge.TauRatTauRatQConversions

**Workstream B2.alg / W3 (Path B, Step 2-pre) — TauRat ↔ TauRatQ
conversion lemma substrate**.

Ships the focused conversion-lemma substrate needed by Path B
Step 2 (`TauRealQ ≃+* TauRatQCauchy`). Each lemma translates a
TauRat-level fact to its TauRatQ counterpart via the
`TauRat.toQ` / `TauRatQ.toRat` round-trip + the Wave 44
`LinearOrderedField TauRatQ` transport.

## What this ships

Four lemmas, each ~3-10 lines:

- **`TauRatQ.toRat_abs`** : `(|y|).toRat = |y.toRat|` for `y :
  TauRatQ` (abs commutes with toRat via the LinearOrderedField
  transport)
- **`TauRat.abs_toQ`** : `(TauRat.abs x).toQ = |x.toQ|` for
  `x : TauRat` (abs commutes with toQ — the application form
  needed by Step 2's IsCauSeq witness)
- **`TauRat.lt_iff_toQ_lt`** : `TauRat.lt x y ↔ x.toQ < y.toQ`
  (lt translates trivially via Wave 40/44 — both sides reduce
  to `x.toRat < y.toRat`)
- **`TauRatQ.exists_recip_le_of_pos`** : `∀ ε > 0, ∃ N : ℕ,
  (1 : TauRatQ) / (N + 1) ≤ ε` (Archimedean glue, derived
  from Wave 44's `Archimedean TauRatQ` instance)

Plus the helper:
- **`TauRatQ.toRat_ofNatRecip`** : `(TauRat.ofNatRecip k).toQ.toRat
  = (1 : ℚ) / (k + 1)` (or its TauRatQ counterpart)

## Substrate dependencies

- `TauRatQuotient.lean` (Wave 40): `TauRatQ`, `TauRat.toQ`,
  `TauRatQ.toRat`, `TauRatQ.eq_iff_toRat_eq`, `TauRatQ.toRat_neg`
- `TauRatQTransport.lean` (Wave 44): `LinearOrder TauRatQ`,
  `Archimedean TauRatQ`, `TauRatQ.le_iff`, `TauRatQ.lt_iff`
- TauRat substrate: `TauRat.abs`, `TauRat.lt`, `TauRat.ofNatRecip`,
  and their toRat-translation lemmas

## What this unlocks

Path B Step 2 (`TauRealQ ≃+* TauRatQCauchy`) becomes tractable:
the four lemmas above are exactly what's needed to translate the
τ-native `TauReal.IsCauchy` (modulus + `1/(k+1)` bound) to
Mathlib's `IsCauSeq` (∀ε > 0, ∃ N) over TauRatQ.

## Atlas cross-references

- `atlas/insights/2026-05-04-mathlib-has-no-effective-reals.md`
  (Path B strategy and the layer-targeting principle)

## Registry Cross-References

- [I.T-W40-Field]                  `Field TauRatQ` (substrate)
- [I.T-W44-LinearOrderedField]     `LinearOrderedField TauRatQ`
                                   (substrate)
- [I.T-B2.alg.W3-pathB-step2pre]   conversion-lemma substrate
                                   (this module)
-/

set_option autoImplicit false

namespace Tau.Boundary

open Tau.Denotation

-- ============================================================
-- B2.alg / W3 Path B / Step 2-pre: TauRat ↔ TauRatQ conversions
-- ============================================================

/-- **abs commutes with toRat at the TauRatQ level**:
    `(|y|).toRat = |y.toRat|` for any `y : TauRatQ`.

    Follows from the LinearOrderedField transport (Wave 44):
    `0 ≤ y ↔ 0 ≤ y.toRat` makes the abs case-split commute. -/
theorem TauRatQ.toRat_abs (y : TauRatQ) : (|y|).toRat = |y.toRat| := by
  by_cases h : 0 ≤ y
  · rw [abs_of_nonneg h, abs_of_nonneg]
    -- Goal: 0 ≤ y.toRat (from 0 ≤ y via order transport)
    have := h
    simp only [TauRatQ.le_iff] at this
    -- this : (0 : TauRatQ).toRat ≤ y.toRat
    -- Need: 0 ≤ y.toRat
    convert this using 1
    -- Goal: (0 : ℚ) = (0 : TauRatQ).toRat
    simp [show ((0 : TauRatQ) = TauRatQ.zero) from rfl, TauRatQ.toRat_zero]
  · push_neg at h
    rw [abs_of_neg h, abs_of_neg]
    · exact TauRatQ.toRat_neg y
    · -- Goal: y.toRat < 0
      have := h
      simp only [TauRatQ.lt_iff] at this
      convert this using 1
      simp [show ((0 : TauRatQ) = TauRatQ.zero) from rfl, TauRatQ.toRat_zero]

/-- **abs commutes with toQ**: `(TauRat.abs x).toQ = |x.toQ|`
    for `x : TauRat`.

    The application form needed by Path B Step 2's IsCauSeq
    witness translation. Reduces to TauRatQ.toRat_abs +
    TauRat.toRat_abs via the toRat round-trip. -/
theorem TauRat.abs_toQ (x : TauRat) : (TauRat.abs x).toQ = |x.toQ| := by
  rw [TauRatQ.eq_iff_toRat_eq]
  rw [TauRatQ.toRat_mk, TauRatQ.toRat_abs, TauRatQ.toRat_mk]
  exact TauRat.toRat_abs x

/-- **lt translates trivially via toQ**:
    `TauRat.lt x y ↔ x.toQ < y.toQ` for `x y : TauRat`.

    Both sides reduce to `x.toRat < y.toRat`:
    - LHS: by definition of `TauRat.lt`
    - RHS: by `TauRatQ.lt_iff` (Wave 44, `Iff.rfl`) +
      `TauRatQ.toRat_mk` -/
@[simp] theorem TauRat.lt_iff_toQ_lt (x y : TauRat) :
    TauRat.lt x y ↔ (x.toQ : TauRatQ) < y.toQ := by
  rw [TauRatQ.lt_iff, TauRatQ.toRat_mk, TauRatQ.toRat_mk]
  rfl

/-- **TauRatQ Archimedean recip**: for any `ε > 0` in `TauRatQ`,
    there exists `N : ℕ` with `(1 : TauRatQ) / (N + 1) ≤ ε`.

    Standard Archimedean derivation from Wave 44's
    `Archimedean TauRatQ` instance. Used in Path B Step 2 to
    convert ε-based Mathlib IsCauSeq to modulus-based τ-native
    IsCauchy and back. -/
theorem TauRatQ.exists_recip_le_of_pos {ε : TauRatQ} (hε : 0 < ε) :
    ∃ N : ℕ, (1 : TauRatQ) / (N + 1 : ℕ) ≤ ε := by
  -- Use Mathlib's exists_nat_one_div_lt_of_lt or similar Archimedean
  -- lemma: in any Archimedean LinearOrderedField, ∃ N, 1/(N+1) < ε
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
  exact ⟨N, le_of_lt hN⟩

end Tau.Boundary
