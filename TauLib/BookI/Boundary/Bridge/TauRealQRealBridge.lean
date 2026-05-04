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

-- ============================================================
-- Helper substrate (additional): toRat_symm round-trip + ringEquivRat
-- ============================================================

/-- **`ringEquivRat` round-trip the other way**: `(x).toRat`
    composed with `ringEquivRat.symm` recovers `x`. Equivalent
    statement to `RingEquiv.symm_apply_apply`. -/
@[simp] theorem TauRatQ.symm_apply_toRat (x : TauRatQ) :
    TauRatQ.ringEquivRat.symm x.toRat = x := by
  rw [TauRatQ.toRat_eq_ringEquivRat]
  exact RingEquiv.symm_apply_apply _ _

-- ============================================================
-- B2.alg / W3 Path B / Step 3b: per-rep backward CauSeq translation
-- ============================================================

/-- **Per-rep backward CauSeq translation** `CauSeq ℚ abs →
    CauSeq TauRatQ abs`.

    Pointwise: `n ↦ ringEquivRat.symm (g n)`. The inverse direction
    of `cauSeqQOfCauSeqTauRatQ`. Uses the same order-preservation
    machinery (Wave 44 `lt_iff`) translated through `ringEquivRat.symm`.

    Strategy: given ε > 0 in TauRatQ, get the analogous ε.toRat > 0
    in ℚ, apply `g.property` for the modulus, then translate the
    bound back to TauRatQ via `lt_iff` + `toRat_abs` + `toRat_sub`
    + `symm_toRat`. -/
noncomputable def cauSeqTauRatQOfCauSeqQ
    (g : CauSeq ℚ (abs : ℚ → ℚ)) :
    CauSeq TauRatQ (abs : TauRatQ → TauRatQ) := by
  refine ⟨fun n => TauRatQ.ringEquivRat.symm (g n), ?_⟩
  intro ε hε_pos

  -- Step 1: lift ε to ℚ via toRat (= ringEquivRat)
  have hε'_pos : (0 : ℚ) < ε.toRat := by
    rw [← TauRatQ.toRat_zero']
    rw [← TauRatQ.lt_iff]
    exact hε_pos

  -- Step 2: apply IsCauSeq g at ε.toRat
  obtain ⟨N, hN⟩ := g.property _ hε'_pos
  refine ⟨N, ?_⟩
  intro j hj

  -- Step 3: translate the bound back
  have h := hN j hj
  -- h : |g j - g N| < ε.toRat in ℚ
  -- Goal: abs (ringEquivRat.symm (g j) - ringEquivRat.symm (g N)) < ε in TauRatQ
  rw [TauRatQ.lt_iff]
  -- Goal: (abs (...)).toRat < ε.toRat
  rw [TauRatQ.toRat_abs, TauRatQ.toRat_sub,
      TauRatQ.symm_toRat, TauRatQ.symm_toRat]
  -- Goal: |g j - g N| < ε.toRat
  exact h

/-- **Coercion handle**: the underlying function of
    `cauSeqTauRatQOfCauSeqQ g` at `n` is `ringEquivRat.symm (g n)`. -/
@[simp] theorem cauSeqTauRatQOfCauSeqQ_apply
    (g : CauSeq ℚ (abs : ℚ → ℚ)) (n : ℕ) :
    (cauSeqTauRatQOfCauSeqQ g) n = TauRatQ.ringEquivRat.symm (g n) := rfl

-- ============================================================
-- B2.alg / W3 Path B / Step 3c-pre: per-rep CauSeq ring-op preservation (forward)
-- ============================================================

/-- **Per-rep zero preservation**: forward of `(0 : CauSeq TauRatQ abs)`
    is `(0 : CauSeq ℚ abs)`. -/
theorem cauSeqQOfCauSeqTauRatQ_zero :
    cauSeqQOfCauSeqTauRatQ (0 : CauSeq TauRatQ (abs : TauRatQ → TauRatQ)) =
    (0 : CauSeq ℚ (abs : ℚ → ℚ)) := by
  apply Subtype.ext
  funext n
  show ((0 : TauRatQ).toRat : ℚ) = 0
  exact TauRatQ.toRat_zero'

/-- **Per-rep one preservation**: forward of `(1 : CauSeq TauRatQ abs)`
    is `(1 : CauSeq ℚ abs)`. -/
theorem cauSeqQOfCauSeqTauRatQ_one :
    cauSeqQOfCauSeqTauRatQ (1 : CauSeq TauRatQ (abs : TauRatQ → TauRatQ)) =
    (1 : CauSeq ℚ (abs : ℚ → ℚ)) := by
  apply Subtype.ext
  funext n
  show ((1 : TauRatQ).toRat : ℚ) = 1
  exact TauRatQ.toRat_one'

/-- **Per-rep add preservation**: forward distributes over `(+)`. -/
theorem cauSeqQOfCauSeqTauRatQ_add
    (f g : CauSeq TauRatQ (abs : TauRatQ → TauRatQ)) :
    cauSeqQOfCauSeqTauRatQ (f + g) =
    cauSeqQOfCauSeqTauRatQ f + cauSeqQOfCauSeqTauRatQ g := by
  apply Subtype.ext
  funext n
  show ((f n + g n).toRat : ℚ) = (f n).toRat + (g n).toRat
  exact TauRatQ.toRat_add' (f n) (g n)

/-- **Per-rep neg preservation**: forward distributes over `(-_)`. -/
theorem cauSeqQOfCauSeqTauRatQ_neg
    (f : CauSeq TauRatQ (abs : TauRatQ → TauRatQ)) :
    cauSeqQOfCauSeqTauRatQ (-f) = -(cauSeqQOfCauSeqTauRatQ f) := by
  apply Subtype.ext
  funext n
  show ((-f n).toRat : ℚ) = -((f n).toRat)
  exact TauRatQ.toRat_neg (f n)

/-- **Per-rep mul preservation**: forward distributes over `(*)`. -/
theorem cauSeqQOfCauSeqTauRatQ_mul
    (f g : CauSeq TauRatQ (abs : TauRatQ → TauRatQ)) :
    cauSeqQOfCauSeqTauRatQ (f * g) =
    cauSeqQOfCauSeqTauRatQ f * cauSeqQOfCauSeqTauRatQ g := by
  apply Subtype.ext
  funext n
  show ((f n * g n).toRat : ℚ) = (f n).toRat * (g n).toRat
  exact TauRatQ.toRat_mul' (f n) (g n)

-- ============================================================
-- B2.alg / W3 Path B / Step 3c: forward respects equiv + lift to quotient
-- ============================================================

/-- **Forward CauSeq translation respects equivalence**: if `f ≈ g`
    in `CauSeq TauRatQ abs`, then `cauSeqQOfCauSeqTauRatQ f ≈
    cauSeqQOfCauSeqTauRatQ g` in `CauSeq ℚ abs`.

    Mirror of `cauSeqOfCauchyTauReal_respects_equiv` (Step 2-equiv-fwd)
    for the Cauchy-completion bridge layer. The proof translates the
    `LimZero (f - g)` witness through `ringEquivRat`'s order
    preservation. -/
theorem cauSeqQOfCauSeqTauRatQ_respects_equiv
    (f g : CauSeq TauRatQ (abs : TauRatQ → TauRatQ)) (h : f ≈ g) :
    cauSeqQOfCauSeqTauRatQ f ≈ cauSeqQOfCauSeqTauRatQ g := by
  -- ≈ unfolds to LimZero (· - ·)
  show CauSeq.LimZero (cauSeqQOfCauSeqTauRatQ f - cauSeqQOfCauSeqTauRatQ g)
  intro ε hε_pos

  -- Step 1: lift ε to TauRatQ
  have hε'_pos : (0 : TauRatQ) < TauRatQ.ringEquivRat.symm ε := by
    rw [TauRatQ.lt_iff, TauRatQ.toRat_zero', TauRatQ.symm_toRat]
    exact hε_pos

  -- Step 2: apply LimZero of f - g at ε'
  obtain ⟨N, hN⟩ := h _ hε'_pos
  refine ⟨N, ?_⟩
  intro j hj

  -- Step 3: translate the bound
  have hb := hN j hj
  -- hb : abs ((f - g) j) < ringEquivRat.symm ε in TauRatQ
  rw [show ((f - g) j : TauRatQ) = f j - g j from rfl] at hb
  rw [TauRatQ.lt_iff, TauRatQ.toRat_abs, TauRatQ.toRat_sub,
      TauRatQ.symm_toRat] at hb
  -- hb : |((f j).toRat - (g j).toRat)| < ε
  -- Goal: abs ((cauSeqQ f - cauSeqQ g) j) < ε
  show abs ((cauSeqQOfCauSeqTauRatQ f - cauSeqQOfCauSeqTauRatQ g) j) < ε
  rw [show ((cauSeqQOfCauSeqTauRatQ f - cauSeqQOfCauSeqTauRatQ g) j : ℚ) =
        (cauSeqQOfCauSeqTauRatQ f) j - (cauSeqQOfCauSeqTauRatQ g) j from rfl]
  show |(f j).toRat - (g j).toRat| < ε
  exact hb

/-- **Composed forward map** `TauRatQCauchy → Cauchy_ℚ` (per-rep
    form). Composes `cauSeqQOfCauSeqTauRatQ` with
    `CauSeq.Completion.mk`. -/
noncomputable def cauchyQOfCauSeqTauRatQ
    (f : CauSeq TauRatQ (abs : TauRatQ → TauRatQ)) :
    CauSeq.Completion.Cauchy (abs : ℚ → ℚ) :=
  CauSeq.Completion.mk (cauSeqQOfCauSeqTauRatQ f)

/-- **Composed map respects equivalence**: equivalent CauSeqs map to
    the same Cauchy-class. -/
theorem cauchyQOfCauSeqTauRatQ_respects_equiv
    (f g : CauSeq TauRatQ (abs : TauRatQ → TauRatQ)) (h : f ≈ g) :
    cauchyQOfCauSeqTauRatQ f = cauchyQOfCauSeqTauRatQ g := by
  unfold cauchyQOfCauSeqTauRatQ
  exact CauSeq.Completion.mk_eq.mpr
    (cauSeqQOfCauSeqTauRatQ_respects_equiv f g h)

/-- **B2.alg / W3 Path B / Step 3c — the lifted forward map**
    `TauRatQCauchy → CauSeq.Completion.Cauchy (abs : ℚ → ℚ)`.

    Lifts `cauchyQOfCauSeqTauRatQ` to `TauRatQCauchy` via
    `Quotient.lift`. -/
noncomputable def tauRatQCauchyToCauchyQ :
    TauRatQCauchy → CauSeq.Completion.Cauchy (abs : ℚ → ℚ) :=
  Quotient.lift cauchyQOfCauSeqTauRatQ
    cauchyQOfCauSeqTauRatQ_respects_equiv

/-- **Verification handle**: lifted map agrees with per-rep on `mk`. -/
@[simp] theorem tauRatQCauchyToCauchyQ_mk
    (f : CauSeq TauRatQ (abs : TauRatQ → TauRatQ)) :
    tauRatQCauchyToCauchyQ (CauSeq.Completion.mk f) =
    CauSeq.Completion.mk (cauSeqQOfCauSeqTauRatQ f) := rfl

-- ============================================================
-- B2.alg / W3 Path B / Step 3c-ring: ring-hom preservation at quotient
-- ============================================================

/-- **`tauRatQCauchyToCauchyQ` preserves zero**. -/
theorem tauRatQCauchyToCauchyQ_zero :
    tauRatQCauchyToCauchyQ 0 = 0 := by
  show tauRatQCauchyToCauchyQ (CauSeq.Completion.mk 0) = 0
  rw [tauRatQCauchyToCauchyQ_mk, cauSeqQOfCauSeqTauRatQ_zero]
  rfl

/-- **`tauRatQCauchyToCauchyQ` preserves one**. -/
theorem tauRatQCauchyToCauchyQ_one :
    tauRatQCauchyToCauchyQ 1 = 1 := by
  show tauRatQCauchyToCauchyQ (CauSeq.Completion.mk 1) = 1
  rw [tauRatQCauchyToCauchyQ_mk, cauSeqQOfCauSeqTauRatQ_one]
  rfl

/-- **`tauRatQCauchyToCauchyQ` preserves addition**. -/
theorem tauRatQCauchyToCauchyQ_add (x y : TauRatQCauchy) :
    tauRatQCauchyToCauchyQ (x + y) =
    tauRatQCauchyToCauchyQ x + tauRatQCauchyToCauchyQ y := by
  refine Quotient.inductionOn₂ x y (fun f g => ?_)
  show tauRatQCauchyToCauchyQ (CauSeq.Completion.mk (f + g)) =
       tauRatQCauchyToCauchyQ (CauSeq.Completion.mk f) +
       tauRatQCauchyToCauchyQ (CauSeq.Completion.mk g)
  rw [tauRatQCauchyToCauchyQ_mk, tauRatQCauchyToCauchyQ_mk,
      tauRatQCauchyToCauchyQ_mk, cauSeqQOfCauSeqTauRatQ_add,
      ← CauSeq.Completion.mk_add]

/-- **`tauRatQCauchyToCauchyQ` preserves multiplication**. -/
theorem tauRatQCauchyToCauchyQ_mul (x y : TauRatQCauchy) :
    tauRatQCauchyToCauchyQ (x * y) =
    tauRatQCauchyToCauchyQ x * tauRatQCauchyToCauchyQ y := by
  refine Quotient.inductionOn₂ x y (fun f g => ?_)
  show tauRatQCauchyToCauchyQ (CauSeq.Completion.mk (f * g)) =
       tauRatQCauchyToCauchyQ (CauSeq.Completion.mk f) *
       tauRatQCauchyToCauchyQ (CauSeq.Completion.mk g)
  rw [tauRatQCauchyToCauchyQ_mk, tauRatQCauchyToCauchyQ_mk,
      tauRatQCauchyToCauchyQ_mk, cauSeqQOfCauSeqTauRatQ_mul,
      ← CauSeq.Completion.mk_mul]

-- ============================================================
-- B2.alg / W3 Path B / Step 3c-RingHom: forward as RingHom
-- ============================================================

/-- **`tauRatQCauchyToCauchyQRingHom`** — the lifted forward map
    packaged as a `RingHom`. Forward half of the eventual
    `TauRatQCauchy ≃+* CauSeq.Completion.Cauchy (abs : ℚ → ℚ)`
    (Step 3 KEYSTONE). -/
noncomputable def tauRatQCauchyToCauchyQRingHom :
    TauRatQCauchy →+* CauSeq.Completion.Cauchy (abs : ℚ → ℚ) where
  toFun     := tauRatQCauchyToCauchyQ
  map_zero' := tauRatQCauchyToCauchyQ_zero
  map_one'  := tauRatQCauchyToCauchyQ_one
  map_add'  := tauRatQCauchyToCauchyQ_add
  map_mul'  := tauRatQCauchyToCauchyQ_mul

@[simp] theorem tauRatQCauchyToCauchyQRingHom_apply (x : TauRatQCauchy) :
    tauRatQCauchyToCauchyQRingHom x = tauRatQCauchyToCauchyQ x := rfl

end Tau.Boundary
