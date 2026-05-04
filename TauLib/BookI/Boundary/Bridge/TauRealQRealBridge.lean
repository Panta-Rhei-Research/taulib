import TauLib.BookI.Boundary.Bridge.TauRealQCauSeqBridge
import Mathlib.Data.Real.Basic

/-!
# TauLib.BookI.Boundary.Bridge.TauRealQRealBridge

**Workstream B2.alg / W3 (Path B, Steps 3+4) — TauRatQCauchy ↔ ℝ
bridge via Wave 40's `TauRatQ ≃+* ℚ`**.

Builds on Step 2 KEYSTONE (`TauRealQ ≃+* TauRatQCauchy`, PR #157) to
extend the chain all the way to `ℝ`:

```
TauRealQ                        (τ-native Cauchy quotient)
  ≃+* TauRatQCauchy             (Step 2, PR #157)
  ≃+* CauSeq.Completion.Cauchy  (Step 3, this module)
        (abs : ℚ → ℚ)
  ≃+* ℝ                          (Step 4, via Real.ringEquivCauchy)
```

The middle bridge (Step 3) transports the Cauchy completion via
Wave 40's `TauRatQ.ringEquivRat : TauRatQ ≃+* ℚ` (which is
order-preserving by Wave 44's `LinearOrderedField` transport, so
`abs` is preserved).

## What this ships (first sub-PR)

**Step 3a — per-rep forward CauSeq translation**:

```lean
noncomputable def cauSeqQOfCauSeqTauRatQ
    (f : CauSeq TauRatQ (abs : TauRatQ → TauRatQ)) :
    CauSeq ℚ (abs : ℚ → ℚ)
```

Pointwise translation `n ↦ (f n).toRat` with the `IsCauSeq` proof
re-derived using:
- `TauRatQ.lt_iff` (Wave 44 transport, `Iff.rfl`)
- `TauRatQ.toRat_abs` (Step 2-pre)
- `TauRatQ.ringEquivRat.apply_symm_apply` (Wave 40)
- A small substrate helper `TauRatQ.toRat_sub`

## Sub-PR cascade for Steps 3+4

- **3a** (this PR): per-rep forward CauSeq translation
- **3b**: per-rep backward (`CauSeq ℚ → CauSeq TauRatQ`)
- **3c**: lift forward + ring-hom preservation
- **3d**: lift backward + round-trip + RingEquiv assembly
- **4**: compose with `Real.ringEquivCauchy` to bridge to ℝ

## Substrate dependencies

- `TauRealQCauSeqBridge.lean` (Step 2 KEYSTONE, PR #157):
  `TauRealQ ≃+* TauRatQCauchy`
- Wave 40 `TauRatQ.ringEquivRat : TauRatQ ≃+* ℚ`
- Wave 44 `LinearOrderedField TauRatQ` (transport via toRat)
- Mathlib `Real.ringEquivCauchy : ℝ ≃+* CauSeq.Completion.Cauchy
  (abs : ℚ → ℚ)`

## Atlas cross-references

- `atlas/insights/2026-05-04-mathlib-has-no-effective-reals.md`
  (Path B strategy)

## Registry Cross-References

- [I.T-W40-RingEquiv]                `TauRatQ ≃+* ℚ` (substrate)
- [I.T-B2.alg.W3-pathB-step2-RingEquiv]  Step 2 KEYSTONE (substrate)
- [I.T-B2.alg.W3-pathB-step3a]       per-rep forward CauSeq trans
                                     (this module)
-/

set_option autoImplicit false

namespace Tau.Boundary

open Tau.Denotation

-- ============================================================
-- Helper substrate: TauRatQ.toRat preserves subtraction
-- ============================================================

/-- **`TauRatQ.toRat` preserves subtraction**: `(x - y).toRat =
    x.toRat - y.toRat`. Follows from `toRat_add` + `toRat_neg`
    (or directly from the underlying `RingEquiv`). -/
@[simp] theorem TauRatQ.toRat_sub (x y : TauRatQ) :
    (x - y).toRat = x.toRat - y.toRat := by
  rw [TauRatQ.toRat_eq_ringEquivRat, TauRatQ.toRat_eq_ringEquivRat,
      TauRatQ.toRat_eq_ringEquivRat]
  exact map_sub TauRatQ.ringEquivRat x y

/-- **`ringEquivRat.symm` round-trip**: `(ringEquivRat.symm q).toRat
    = q` for `q : ℚ`. The right inverse identity of the Wave 40
    ring iso, expressed via `toRat`. -/
@[simp] theorem TauRatQ.symm_toRat (q : ℚ) :
    (TauRatQ.ringEquivRat.symm q).toRat = q := by
  rw [TauRatQ.toRat_eq_ringEquivRat]
  exact RingEquiv.apply_symm_apply _ _

-- ============================================================
-- B2.alg / W3 Path B / Step 3a: per-rep forward CauSeq translation
-- ============================================================

/-- **Per-rep forward CauSeq translation** `CauSeq TauRatQ abs →
    CauSeq ℚ abs`.

    Pointwise: `n ↦ (f n).toRat` (which is `ringEquivRat (f n)`).
    The `IsCauSeq` property carries through because:
    - `ringEquivRat` is a ring iso (preserves `-`, `0`)
    - It's also order-preserving (Wave 44 transport: `lt_iff`)
    - Hence `abs` is preserved (Step 2-pre `toRat_abs`)

    Strategy: given ε > 0 in ℚ, translate to ε' := `ringEquivRat.symm
    ε > 0` in TauRatQ, apply `f.property` for the modulus, then
    translate the bound back via `toRat_abs` + `toRat_sub` +
    `lt_iff`. -/
noncomputable def cauSeqQOfCauSeqTauRatQ
    (f : CauSeq TauRatQ (abs : TauRatQ → TauRatQ)) :
    CauSeq ℚ (abs : ℚ → ℚ) := by
  refine ⟨fun n => (f n).toRat, ?_⟩
  intro ε hε_pos

  -- Step 1: lift ε to TauRatQ via ringEquivRat.symm
  have hε'_pos : (0 : TauRatQ) < TauRatQ.ringEquivRat.symm ε := by
    rw [TauRatQ.lt_iff, TauRatQ.toRat_zero', TauRatQ.symm_toRat]
    exact hε_pos

  -- Step 2: apply IsCauSeq f at ε'
  obtain ⟨N, hN⟩ := f.property _ hε'_pos
  refine ⟨N, ?_⟩
  intro j hj

  -- Step 3: translate the bound
  have h := hN j hj
  -- h : abs (f j - f N) < ringEquivRat.symm ε in TauRatQ
  rw [TauRatQ.lt_iff] at h
  -- h : (abs (f j - f N)).toRat < (ringEquivRat.symm ε).toRat
  rw [TauRatQ.toRat_abs, TauRatQ.toRat_sub, TauRatQ.symm_toRat] at h
  -- h : |((f j).toRat - (f N).toRat)| < ε
  exact h

/-- **Coercion handle**: the underlying function of
    `cauSeqQOfCauSeqTauRatQ f` at `n` is `(f n).toRat`. -/
@[simp] theorem cauSeqQOfCauSeqTauRatQ_apply
    (f : CauSeq TauRatQ (abs : TauRatQ → TauRatQ)) (n : ℕ) :
    (cauSeqQOfCauSeqTauRatQ f) n = (f n).toRat := rfl

end Tau.Boundary
