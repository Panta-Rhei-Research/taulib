import TauLib.BookI.Boundary.Bridge.TauRealQCauSeqBridge
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Analysis.Real.Cardinality
import Mathlib.SetTheory.Cardinal.Continuum

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

-- ============================================================
-- B2.alg / W3 Path B / Step 3d-back-equiv: backward respects ≈
-- ============================================================

/-- **Backward CauSeq translation respects equivalence**: if `f ≈ g`
    in `CauSeq ℚ abs`, then `cauSeqTauRatQOfCauSeqQ f ≈
    cauSeqTauRatQOfCauSeqQ g` in `CauSeq TauRatQ abs`.

    Mirror of `cauSeqQOfCauSeqTauRatQ_respects_equiv` (Step 3c) for
    the inverse direction. -/
theorem cauSeqTauRatQOfCauSeqQ_respects_equiv
    (f g : CauSeq ℚ (abs : ℚ → ℚ)) (h : f ≈ g) :
    cauSeqTauRatQOfCauSeqQ f ≈ cauSeqTauRatQOfCauSeqQ g := by
  show CauSeq.LimZero (cauSeqTauRatQOfCauSeqQ f - cauSeqTauRatQOfCauSeqQ g)
  intro ε hε_pos

  -- Step 1: lift ε to ℚ via toRat
  have hε'_pos : (0 : ℚ) < ε.toRat := by
    rw [← TauRatQ.toRat_zero', ← TauRatQ.lt_iff]
    exact hε_pos

  -- Step 2: apply LimZero of f - g at ε.toRat
  obtain ⟨N, hN⟩ := h _ hε'_pos
  refine ⟨N, ?_⟩
  intro j hj

  -- Step 3: translate the bound
  have hb := hN j hj
  -- hb : |((f - g) j)| < ε.toRat in ℚ
  rw [show ((f - g) j : ℚ) = f j - g j from rfl] at hb
  -- Goal: abs ((cauSeqTauRatQ f - cauSeqTauRatQ g) j) < ε in TauRatQ
  show abs ((cauSeqTauRatQOfCauSeqQ f - cauSeqTauRatQOfCauSeqQ g) j) < ε
  rw [show ((cauSeqTauRatQOfCauSeqQ f - cauSeqTauRatQOfCauSeqQ g) j : TauRatQ) =
        TauRatQ.ringEquivRat.symm (f j) -
          TauRatQ.ringEquivRat.symm (g j) from rfl]
  rw [TauRatQ.lt_iff, TauRatQ.toRat_abs, TauRatQ.toRat_sub,
      TauRatQ.symm_toRat, TauRatQ.symm_toRat]
  exact hb

-- ============================================================
-- B2.alg / W3 Path B / Step 3d-back-quotient: lift backward to TauRatQCauchy
-- ============================================================

/-- **Composed backward map** `Cauchy_ℚ → TauRatQCauchy` (per-rep
    form). -/
noncomputable def tauRatQCauchyOfCauSeqQ
    (f : CauSeq ℚ (abs : ℚ → ℚ)) : TauRatQCauchy :=
  CauSeq.Completion.mk (cauSeqTauRatQOfCauSeqQ f)

/-- **Composed backward respects equivalence**. -/
theorem tauRatQCauchyOfCauSeqQ_respects_equiv
    (f g : CauSeq ℚ (abs : ℚ → ℚ)) (h : f ≈ g) :
    tauRatQCauchyOfCauSeqQ f = tauRatQCauchyOfCauSeqQ g := by
  unfold tauRatQCauchyOfCauSeqQ
  exact CauSeq.Completion.mk_eq.mpr
    (cauSeqTauRatQOfCauSeqQ_respects_equiv f g h)

/-- **Lifted backward map** `CauSeq.Completion.Cauchy (abs : ℚ → ℚ)
    → TauRatQCauchy`. -/
noncomputable def cauchyQToTauRatQCauchy :
    CauSeq.Completion.Cauchy (abs : ℚ → ℚ) → TauRatQCauchy :=
  Quotient.lift tauRatQCauchyOfCauSeqQ tauRatQCauchyOfCauSeqQ_respects_equiv

@[simp] theorem cauchyQToTauRatQCauchy_mk
    (f : CauSeq ℚ (abs : ℚ → ℚ)) :
    cauchyQToTauRatQCauchy (CauSeq.Completion.mk f) =
    CauSeq.Completion.mk (cauSeqTauRatQOfCauSeqQ f) := rfl

-- ============================================================
-- B2.alg / W3 Path B / Step 3d-roundtrip: round-trip identities
-- ============================================================

/-- **CauSeq-level round-trip (forward∘backward)**:
    `cauSeqQOfCauSeqTauRatQ (cauSeqTauRatQOfCauSeqQ g) = g`. -/
theorem cauSeqQOfCauSeqTauRatQ_cauSeqTauRatQOfCauSeqQ
    (g : CauSeq ℚ (abs : ℚ → ℚ)) :
    cauSeqQOfCauSeqTauRatQ (cauSeqTauRatQOfCauSeqQ g) = g := by
  apply Subtype.ext
  funext n
  show ((TauRatQ.ringEquivRat.symm (g n)).toRat : ℚ) = g n
  exact TauRatQ.symm_toRat (g n)

/-- **CauSeq-level round-trip (backward∘forward)**:
    `cauSeqTauRatQOfCauSeqQ (cauSeqQOfCauSeqTauRatQ f) = f`. -/
theorem cauSeqTauRatQOfCauSeqQ_cauSeqQOfCauSeqTauRatQ
    (f : CauSeq TauRatQ (abs : TauRatQ → TauRatQ)) :
    cauSeqTauRatQOfCauSeqQ (cauSeqQOfCauSeqTauRatQ f) = f := by
  apply Subtype.ext
  funext n
  show TauRatQ.ringEquivRat.symm ((f n).toRat) = f n
  exact TauRatQ.symm_apply_toRat (f n)

/-- **Quotient-level forward∘backward = id**. -/
theorem tauRatQCauchyToCauchyQ_cauchyQToTauRatQCauchy
    (x : CauSeq.Completion.Cauchy (abs : ℚ → ℚ)) :
    tauRatQCauchyToCauchyQ (cauchyQToTauRatQCauchy x) = x := by
  refine Quotient.inductionOn x (fun g => ?_)
  show tauRatQCauchyToCauchyQ
        (cauchyQToTauRatQCauchy (CauSeq.Completion.mk g)) =
        CauSeq.Completion.mk g
  rw [cauchyQToTauRatQCauchy_mk, tauRatQCauchyToCauchyQ_mk,
      cauSeqQOfCauSeqTauRatQ_cauSeqTauRatQOfCauSeqQ]

/-- **Quotient-level backward∘forward = id**. -/
theorem cauchyQToTauRatQCauchy_tauRatQCauchyToCauchyQ
    (y : TauRatQCauchy) :
    cauchyQToTauRatQCauchy (tauRatQCauchyToCauchyQ y) = y := by
  refine Quotient.inductionOn y (fun f => ?_)
  show cauchyQToTauRatQCauchy
        (tauRatQCauchyToCauchyQ (CauSeq.Completion.mk f)) =
        CauSeq.Completion.mk f
  rw [tauRatQCauchyToCauchyQ_mk, cauchyQToTauRatQCauchy_mk,
      cauSeqTauRatQOfCauSeqQ_cauSeqQOfCauSeqTauRatQ]

-- ============================================================
-- B2.alg / W3 Path B / Step 3 KEYSTONE: TauRatQCauchy ≃+* Cauchy_ℚ
-- ============================================================

/-- **🎉 Path B Step 3 KEYSTONE — `TauRatQCauchy ≃+* CauSeq.Completion.
    Cauchy (abs : ℚ → ℚ)`**.

    Assembles the Cauchy-completion ring-equivalence from the
    forward `RingHom` (Step 3c) plus the backward function (Step 3d
    above) and round-trip identities. Together with PR #157 (Step 2
    KEYSTONE), this builds `TauRealQ ≃+* CauSeq.Completion.Cauchy
    (abs : ℚ → ℚ)`, which composes with `Real.ringEquivCauchy.symm`
    to yield the **final `TauRealQ ≃+* ℝ`** (Step 4, queued). -/
noncomputable def tauRatQCauchyRingEquivCauchyQ :
    TauRatQCauchy ≃+* CauSeq.Completion.Cauchy (abs : ℚ → ℚ) :=
  { tauRatQCauchyToCauchyQRingHom with
    invFun    := cauchyQToTauRatQCauchy
    left_inv  := cauchyQToTauRatQCauchy_tauRatQCauchyToCauchyQ
    right_inv := tauRatQCauchyToCauchyQ_cauchyQToTauRatQCauchy }

/-- **Coercion handle (forward)**. -/
@[simp] theorem tauRatQCauchyRingEquivCauchyQ_apply (x : TauRatQCauchy) :
    tauRatQCauchyRingEquivCauchyQ x = tauRatQCauchyToCauchyQ x := rfl

/-- **Coercion handle (backward)**. -/
@[simp] theorem tauRatQCauchyRingEquivCauchyQ_symm_apply
    (y : CauSeq.Completion.Cauchy (abs : ℚ → ℚ)) :
    tauRatQCauchyRingEquivCauchyQ.symm y = cauchyQToTauRatQCauchy y := rfl

-- ============================================================
-- B2.alg / W3 Path B / Step 4 KEYSTONE: TauRealQ ≃+* ℝ 🎉🎉🎉
-- ============================================================

/-- **🎉🎉🎉 PATH B FINAL KEYSTONE — `TauRealQ ≃+* ℝ`** 🎉🎉🎉

    Composes the three Path B ring-equivalences:

    ```
    TauRealQ                           (τ-native Cauchy quotient)
      ≃+* TauRatQCauchy                (Step 2 KEYSTONE, PR #157)
      ≃+* CauSeq.Completion.Cauchy ℚ   (Step 3 KEYSTONE, this module above)
      ≃+* ℝ                             (Step 4, via Real.ringEquivCauchy.symm)
    ```

    This is **the full bridge from τ-native reals to Mathlib's `ℝ`**,
    completing the Path B program. With this in place:

    - **W3 (full)**: `TauAlgReal ≃ₐ[TauRatQ] algebraicClosure ℚ ℝ`
      becomes tractable (composes through this bridge)
    - **W3b**: `LinearOrderedField TauAlgReal` via this transport
    - **Downstream**: any Mathlib theorem about ℝ (analysis, topology,
      measure theory, etc.) can be transported back to TauRealQ via
      this iso

    The full chain achieves what the **constructive-real cardinality
    boundary** said was structurally blocked at the LinearOrderedField
    level (atlas/insights/2026-04-29-constructive-real-cardinality-boundary.md):
    we sidestep the Markov wall by bridging at the *Cauchy carrier
    level* (Cauchy completion) rather than at the LinearOrderedField
    level. Mathematics ⇄ τ-mathematics fully connected. 🎉 -/
noncomputable def tauRealQRingEquivReal : TauRealQ ≃+* ℝ :=
  (tauRealQRingEquivTauRatQCauchy.trans
    tauRatQCauchyRingEquivCauchyQ).trans
    Real.ringEquivCauchy.symm

/-- **Coercion handle (forward)**: the underlying function of
    `tauRealQRingEquivReal` is the composition. -/
theorem tauRealQRingEquivReal_apply (x : TauRealQ) :
    tauRealQRingEquivReal x =
    Real.ringEquivCauchy.symm
      (tauRatQCauchyToCauchyQ (tauRealQToTauRatQCauchy x)) := rfl

/-- **Coercion handle (backward)**: the inverse. -/
theorem tauRealQRingEquivReal_symm_apply (r : ℝ) :
    tauRealQRingEquivReal.symm r =
    tauRatQCauchyToTauRealQ
      (cauchyQToTauRatQCauchy (Real.ringEquivCauchy r)) := rfl

-- ============================================================
-- B2.alg / W3 Path B / Cantor-transport: Uncountable TauRealQ
-- ============================================================

/-- **🎉 Cardinality of TauRealQ via the Path B bridge**:
    `#TauRealQ = 𝔠 = 2^ℵ₀`.

    Direct transport from Mathlib's `Cardinal.mk_real` through the
    Path B FINAL KEYSTONE. The proof factors through the `RingEquiv`'s
    underlying `Equiv`, applying `Equiv.cardinal_eq` and then
    rewriting `#ℝ = 𝔠` via `Cardinal.mk_real`.

    **Where Cantor's diagonal lives in this proof**: not directly!
    The diagonal content is buried inside `Cardinal.mk_real`, which
    in turn factors through `cantorFunction_injective` (the geometric-
    series Cantor function `(ℕ → Bool) → ℝ`) at
    `Mathlib/Analysis/Real/Cardinality.lean:185`. That injectivity
    proof requires `LinearOrder ℝ` — the constructively-blocked piece
    for TauRealQ-without-bridge. Path B's classical bridge transports
    the result, side-stepping the Markov barrier.

    See companion research note `cantor-bridge-categorical` for the
    full structural analysis. -/
theorem TauRealQ.mk_eq_continuum :
    Cardinal.mk TauRealQ = Cardinal.continuum := by
  rw [tauRealQRingEquivReal.toEquiv.cardinal_eq, Cardinal.mk_real]

/-- **🎉 TauRealQ is uncountable** — Cantor's diagonal applied via
    the Path B bridge.

    The classical reading of TauRealQ (post-bridge, with Choice via
    `Quotient.out`): `Uncountable TauRealQ` follows in three lines
    from `TauRealQ.mk_eq_continuum` + `Cardinal.aleph0_lt_continuum`
    + `Cardinal.aleph0_lt_mk_iff`.

    **Companion to TauLib's existing CantorRefutation** (`BookI/Sets/
    CantorRefutation.lean` registry [I.T35]): that result is the
    *internal* (constructive, framework-internal) statement showing no
    diagonal completes within Category τ alone. This theorem is the
    *external* (classical, post-bridge) statement showing the carrier
    type IS uncountable when transported into Mathlib's classical
    universe. The two readings coexist via the Löwenheim-Skolem-like
    framing developed in the companion research note. -/
instance : Uncountable TauRealQ := by
  rw [← Cardinal.aleph0_lt_mk_iff, TauRealQ.mk_eq_continuum]
  exact Cardinal.aleph0_lt_continuum

-- ============================================================
-- B2.alg / W3 Path B / Cantor-diagonal-as-constructor:
-- the diagonal as an addressing operation, not an entity creator
-- ============================================================

/-! ## Cantor's diagonal as an addressing operation

The constructive-foundations reading developed in companion research note
`cantor-bridge-categorical` (Panta-Rhei-Research) interprets Cantor's
diagonal procedure as a **constructor** of `TauRealQ` elements rather
than a **creator** of new entities. The diagonal real is, by the
no-ghost reading, an **existing** `TauRealQ` element addressed by a
non-internal selection function (Choice via `Classical.choose`); the
classical content is in the *separation* (proving the addressed element
is outside the input enumeration's image), not in the *existence* of a
hidden entity beyond the carrier type.

This section formalises the reading as a Lean function. The Choice
content is concentrated in a single `Classical.choose` on the
existential delivered by `Uncountable TauRealQ` (PR \#162); the
separation proof is the non-trivial classical content; the corollary
`cantor_no_surjection` is the standard impossibility-of-bijection
statement.

The construction makes manifest that **AC is an addressing mechanism,
not a creation mechanism**: the chosen element was a `TauRealQ` value
all along; `Classical.choose` just points at one in the complement of
the image. -/

/-- **Existence: the complement of any countable image in `TauRealQ` is
    non-empty.** Combines `Uncountable TauRealQ` (PR \#162) with
    countability of `Set.range f` for any `f : ℕ → TauRealQ`.

    Per the no-ghost reading: the witnessed element is an *existing*
    `TauRealQ` value; the existential statement is about the carrier
    type's classical cardinality being strictly larger than the
    countable image. -/
theorem TauRealQ.exists_not_mem_range (f : ℕ → TauRealQ) :
    ∃ d : TauRealQ, d ∉ Set.range f := by
  by_contra h
  push_neg at h
  have h_univ : Set.range f = Set.univ := Set.eq_univ_of_forall h
  have h_count_univ : (Set.univ : Set TauRealQ).Countable := h_univ ▸ Set.countable_range f
  have h_count : Countable TauRealQ := Set.countable_univ_iff.mp h_count_univ
  exact (not_countable : ¬ Countable TauRealQ) h_count

/-- **🎉 Cantor's diagonal as a `TauRealQ`-valued constructor**.

    The function `TauRealQ.cantorDiagonal : (ℕ → TauRealQ) → TauRealQ`
    addresses, via `Classical.choose`, an *existing* `TauRealQ` element
    in the complement of the input enumeration's image. The element
    was a perfectly normal `TauRealQ` value all along (`TauRealQ` is
    `Quotient CauchyTauReal.setoid` by definition; every element is the
    equivalence class of an explicit Cauchy sequence). What `Classical.
    choose` does is **point at** one such element non-internally, which
    is exactly the "addressing-not-creating" role of AC.

    `noncomputable` because `Classical.choose` is. The Choice content
    factors through `TauRealQ.exists_not_mem_range`, which itself uses
    the `Uncountable TauRealQ` instance (PR \#162, transport via Path B
    bridge from `Cardinal.mk_real`). The diagonal is therefore the
    composition of three classical moves:
    1. Path B bridge (Choice via `Quotient.out` in `tauRealQRingEquivReal`),
    2. `Cardinal.mk_real`'s lower bound (LEM via `cantorFunction_injective`),
    3. `Classical.choose` on the resulting non-emptiness (AC, addressing).

    The constructive content (no Choice, no LEM) is in the type itself:
    every `TauRealQ` element is by construction an equivalence class of
    Cauchy sequences with explicit moduli. The diagonal *constructs* one
    such element by pointing at it. -/
noncomputable def TauRealQ.cantorDiagonal (f : ℕ → TauRealQ) : TauRealQ :=
  (TauRealQ.exists_not_mem_range f).choose

/-- **The diagonal is not in the image of `f`** — by `Classical.choose_spec`. -/
theorem TauRealQ.cantorDiagonal_not_mem_range (f : ℕ → TauRealQ) :
    TauRealQ.cantorDiagonal f ∉ Set.range f :=
  (TauRealQ.exists_not_mem_range f).choose_spec

/-- **Separation** (the standard form of Cantor's diagonal conclusion):
    the diagonal differs from `f n` for every `n`. Per the no-ghost
    reading, this is *not* a statement about the existence of a new
    entity outside the carrier; it is a statement about the
    *bijection-impossibility* — `f` cannot enumerate all `TauRealQ`
    values. The diagonal *witnesses* this impossibility by exhibiting a
    `TauRealQ` element outside `f`'s image. -/
theorem TauRealQ.cantorDiagonal_ne_apply (f : ℕ → TauRealQ) (n : ℕ) :
    TauRealQ.cantorDiagonal f ≠ f n := fun h =>
  TauRealQ.cantorDiagonal_not_mem_range f ⟨n, h.symm⟩

/-- **🎉 Cantor's theorem for `TauRealQ`**: no surjection `ℕ → TauRealQ`
    exists.

    This is the **bijection-impossibility** reading of Cantor's diagonal,
    in line with the no-ghost interpretation: the theorem says that no
    enumeration of `TauRealQ` exists, *not* that there are entities
    beyond any enumeration. The `TauRealQ` carrier type is a
    `Quotient` of explicit Cauchy sequences; every element has a
    Cauchy-modulus name. What fails classically is the existence of an
    `ℕ`-indexed enumeration of all such names modulo equivalence. -/
theorem TauRealQ.cantor_no_surjection (f : ℕ → TauRealQ) :
    ¬ Function.Surjective f := fun hf =>
  TauRealQ.cantorDiagonal_not_mem_range f
    (hf (TauRealQ.cantorDiagonal f))

/-- **Stronger restatement**: there is no surjection `ℕ → TauRealQ`,
    expressed as the negation of the existence of such a surjection. -/
theorem TauRealQ.no_surjection_from_nat :
    ¬ ∃ f : ℕ → TauRealQ, Function.Surjective f := fun ⟨f, hf⟩ =>
  TauRealQ.cantor_no_surjection f hf

end Tau.Boundary
