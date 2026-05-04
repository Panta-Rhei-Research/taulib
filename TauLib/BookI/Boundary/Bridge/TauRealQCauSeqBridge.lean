import TauLib.BookI.Boundary.Bridge.TauRatQCauchyCompletion
import TauLib.BookI.Boundary.Bridge.TauRatTauRatQConversions
import TauLib.BookI.Boundary.Bridge.TauRatQRingEquivConversions
import TauLib.BookI.Boundary.Bridge.TauRealQuotientField

/-!
# TauLib.BookI.Boundary.Bridge.TauRealQCauSeqBridge

**Workstream B2.alg / W3 (Path B, Step 2) — Forward function
`CauchyTauReal → CauSeq TauRatQ abs`**.

Step 2 of the Path B chain: builds the τ-native → Mathlib-CauSeq
forward direction. Given a τ-native Cauchy sequence (a
`CauchyTauReal`), produces the corresponding Mathlib `CauSeq`
over `TauRatQ` with the absolute value `abs : TauRatQ → TauRatQ`.

## Construction

For `a : CauchyTauReal`:

- **Sequence**: `n ↦ (a.val.approx n).toQ : ℕ → TauRatQ`
- **`IsCauSeq` witness**: translate the τ-native modulus-based
  `TauReal.IsCauchy` (`1/(k+1)` bound) to Mathlib's `IsCauSeq`
  (∀ ε > 0, ∃ N) using:
  - `TauRatQ.exists_recip_le_of_pos` (Step 2-pre): ε > 0 ⟹
    ∃ N, 1/(N+1) ≤ ε
  - `TauRat.lt_iff_toQ_lt`, `TauRat.abs_toQ` (Step 2-pre):
    translate the inequality and absolute value to TauRatQ
  - `TauRatQ.toRat_natCast`, `TauRatQ.toRat_div`,
    `TauRatQ.toRat_eq_ringEquivRat` (Step 2-pre-2):
    bridge `(1/(N+1) : TauRatQ)` to `(1/(N+1) : ℚ)` for
    transitivity with `hN`

## Substrate dependencies (all shipped)

- Step 1 (PR #148): `TauRatQCauchy` substrate
- Step 2-pre (PR #149): abs/lt/Archimedean conversions
- Step 2-pre-2 (PR #150): NatCast/div ring-hom preservation
- Wave 41c: `CauchyTauReal`, `TauReal.IsCauchy`

## Path B follow-ups (queued)

- **Step 2 inverse + RingEquiv**: backward map + `TauRealQ ≃+*
  TauRatQCauchy` (next sub-PR)
- **Step 3**: transport via Wave 40 (TauRatQ ≃+* ℚ)
- **Step 4**: compose with Mathlib's `Real.ringEquivCauchy` to
  bridge to ℝ
-/

set_option autoImplicit false

namespace Tau.Boundary

open Tau.Denotation

-- ============================================================
-- B2.alg / W3 Path B / Step 2: Forward function
-- ============================================================

/-- **Forward function `CauchyTauReal → CauSeq TauRatQ abs`**.

    Translates a τ-native Cauchy sequence (modulus-based with
    `1/(k+1)` bound) to a Mathlib `CauSeq` over `TauRatQ` (with
    the classical `∀ ε > 0, ∃ N` formulation). -/
noncomputable def cauSeqOfCauchyTauReal (a : CauchyTauReal) :
    CauSeq TauRatQ (abs : TauRatQ → TauRatQ) := by
  refine ⟨fun n => ((a.val.approx n).toQ : TauRatQ), ?_⟩
  -- Goal: IsCauSeq abs (fun n => (a.val.approx n).toQ)
  intro ε hε_pos
  -- Step A: get Archimedean witness N with 1/(N+1) ≤ ε
  obtain ⟨N, hN⟩ := TauRatQ.exists_recip_le_of_pos hε_pos
  -- Step B: apply τ-native Cauchy modulus
  obtain ⟨μ, hμ⟩ := a.isCauchy
  refine ⟨μ N, ?_⟩
  intro j hj
  -- Step C: τ-native witness at indices j ≥ μ N
  have h_tauRat : TauRat.lt
      ((a.val.approx j).sub (a.val.approx (μ N))).abs
      (TauRat.ofNatRecip N) := hμ N j (μ N) hj (le_refl _)
  -- Step D: translate TauRat.lt → TauRatQ.lt via Step 2-pre
  rw [TauRat.lt_iff_toQ_lt] at h_tauRat
  -- Step E: abs commutes with toQ (Step 2-pre)
  rw [TauRat.abs_toQ] at h_tauRat
  -- Step F: expand .sub.toQ = .toQ - .toQ via TauRat.sub def
  have h_sub : ((a.val.approx j).sub (a.val.approx (μ N))).toQ =
      ((a.val.approx j).toQ - (a.val.approx (μ N)).toQ : TauRatQ) := by
    show ((a.val.approx j).add (a.val.approx (μ N)).negate).toQ = _
    -- LHS unfolds via TauRatQ.add_mk and TauRatQ.neg_mk to:
    -- (a.val.approx j).toQ + ((a.val.approx (μ N)).negate).toQ
    -- = a_j.toQ + (-aμ.toQ) = a_j.toQ - aμ.toQ
    show ((a.val.approx j).toQ + ((a.val.approx (μ N)).negate).toQ : TauRatQ) =
        ((a.val.approx j).toQ - (a.val.approx (μ N)).toQ)
    show ((a.val.approx j).toQ + (-(a.val.approx (μ N)).toQ) : TauRatQ) =
        ((a.val.approx j).toQ - (a.val.approx (μ N)).toQ)
    ring
  rw [h_sub] at h_tauRat
  -- Step G: (TauRat.ofNatRecip N).toQ = (1 : TauRatQ) / (N + 1)
  have h_ofNR : (TauRat.ofNatRecip N).toQ = (1 : TauRatQ) / (N + 1 : ℕ) := by
    rw [TauRatQ.eq_iff_toRat_eq, TauRatQ.toRat_mk,
        TauRat.ofNatRecip_toRat, TauRatQ.toRat_div,
        TauRatQ.toRat_natCast,
        show (1 : TauRatQ).toRat = 1 from TauRatQ.toRat_one]
    push_cast
    rfl
  rw [h_ofNR] at h_tauRat
  -- Step H: chain h_tauRat < ... ≤ ε via hN
  exact lt_of_lt_of_le h_tauRat hN

-- ============================================================
-- B2.alg / W3 Path B / Step 2-equiv-fwd: forward respects ≈
-- ============================================================

/-- **Forward function respects equivalence**: if two
    `CauchyTauReal` values are τ-equivalent (in the sense of
    `CauchyTauReal.equiv`), then their forward images under
    `cauSeqOfCauchyTauReal` are equivalent in Mathlib's `CauSeq`
    sense (`f ≈ g ↔ LimZero (f - g)`).

    Uses the same Archimedean + modulus + abs/lt translation
    chain as `cauSeqOfCauchyTauReal` itself, adapted for the
    pairwise-difference modulus from `TauReal.equiv`. -/
theorem cauSeqOfCauchyTauReal_respects_equiv (a b : CauchyTauReal)
    (h : CauchyTauReal.equiv a b) :
    cauSeqOfCauchyTauReal a ≈ cauSeqOfCauchyTauReal b := by
  -- Unfold ≈ to LimZero (f - g)
  show CauSeq.LimZero (cauSeqOfCauchyTauReal a - cauSeqOfCauchyTauReal b)
  intro ε hε_pos
  -- Step A: Archimedean N with 1/(N+1) ≤ ε
  obtain ⟨N, hN⟩ := TauRatQ.exists_recip_le_of_pos hε_pos
  -- Step B: TauReal.equiv modulus (single-index form)
  obtain ⟨μ, hμ⟩ := h
  refine ⟨μ N, ?_⟩
  intro j hj
  -- Step C: τ-native witness at index j ≥ μ N
  have h_tauRat : TauRat.lt
      ((a.val.approx j).sub (b.val.approx j)).abs
      (TauRat.ofNatRecip N) := hμ N j hj
  -- Step D: TauRat.lt → TauRatQ.lt
  rw [TauRat.lt_iff_toQ_lt] at h_tauRat
  -- Step E: abs commutes with toQ
  rw [TauRat.abs_toQ] at h_tauRat
  -- Step F: expand .sub.toQ
  have h_sub : ((a.val.approx j).sub (b.val.approx j)).toQ =
      ((a.val.approx j).toQ - (b.val.approx j).toQ : TauRatQ) := by
    show ((a.val.approx j).add (b.val.approx j).negate).toQ = _
    show ((a.val.approx j).toQ + ((b.val.approx j).negate).toQ : TauRatQ) =
        ((a.val.approx j).toQ - (b.val.approx j).toQ)
    show ((a.val.approx j).toQ + (-(b.val.approx j).toQ) : TauRatQ) =
        ((a.val.approx j).toQ - (b.val.approx j).toQ)
    ring
  rw [h_sub] at h_tauRat
  -- Step G: (TauRat.ofNatRecip N).toQ = (1 : TauRatQ) / (N + 1)
  have h_ofNR : (TauRat.ofNatRecip N).toQ = (1 : TauRatQ) / (N + 1 : ℕ) := by
    rw [TauRatQ.eq_iff_toRat_eq, TauRatQ.toRat_mk,
        TauRat.ofNatRecip_toRat, TauRatQ.toRat_div,
        TauRatQ.toRat_natCast,
        show (1 : TauRatQ).toRat = 1 from TauRatQ.toRat_one]
    push_cast
    rfl
  rw [h_ofNR] at h_tauRat
  -- Step H: chain to < ε via hN
  -- Goal: abs ((cauSeqOfCauchyTauReal a - cauSeqOfCauchyTauReal b) j) < ε
  -- After CauSeq sub coercion: abs (cauSeq_a.val j - cauSeq_b.val j) < ε
  -- = abs ((a.val.approx j).toQ - (b.val.approx j).toQ) < ε
  -- Which matches h_tauRat after combination with hN
  show abs ((cauSeqOfCauchyTauReal a - cauSeqOfCauchyTauReal b) j) < ε
  rw [show ((cauSeqOfCauchyTauReal a - cauSeqOfCauchyTauReal b) j : TauRatQ) =
        (cauSeqOfCauchyTauReal a) j - (cauSeqOfCauchyTauReal b) j from rfl]
  show abs ((a.val.approx j).toQ - (b.val.approx j).toQ) < ε
  exact lt_of_lt_of_le h_tauRat hN

-- ============================================================
-- B2.alg / W3 Path B / Step 2-fwd-quotient: lift to TauRealQ
-- ============================================================

/-- **Composition with `CauSeq.Completion.mk`**: package the
    `CauSeq` produced by `cauSeqOfCauchyTauReal` into a
    `TauRatQCauchy` (= `CauSeq.Completion.Cauchy abs`) value.

    This is the per-`CauchyTauReal`-representative form of the
    forward map; the next step lifts it to `TauRealQ` via
    `Quotient.lift`. -/
noncomputable def tauRatQCauchyOfCauchyTauReal (a : CauchyTauReal) :
    TauRatQCauchy :=
  CauSeq.Completion.mk (cauSeqOfCauchyTauReal a)

/-- **Composed map respects equivalence**: equivalent
    `CauchyTauReal` values map to the same `TauRatQCauchy` class.

    Combines `cauSeqOfCauchyTauReal_respects_equiv`
    (Step 2-equiv-fwd) with Mathlib's `CauSeq.Completion.mk_eq`
    (which says `mk f = mk g ↔ LimZero (f - g) ↔ f ≈ g`). -/
theorem tauRatQCauchyOfCauchyTauReal_respects_equiv
    (a b : CauchyTauReal) (h : CauchyTauReal.equiv a b) :
    tauRatQCauchyOfCauchyTauReal a = tauRatQCauchyOfCauchyTauReal b := by
  unfold tauRatQCauchyOfCauchyTauReal
  exact CauSeq.Completion.mk_eq.mpr
    (cauSeqOfCauchyTauReal_respects_equiv a b h)

/-- **B2.alg / W3 Path B / Step 2-fwd-quotient — the lifted
    forward map** `TauRealQ → TauRatQCauchy`.

    Lifts `tauRatQCauchyOfCauchyTauReal` (per-representative form)
    to the `TauRealQ` quotient via `Quotient.lift`, using
    `tauRatQCauchyOfCauchyTauReal_respects_equiv` as the
    equivalence-respect witness. -/
noncomputable def tauRealQToTauRatQCauchy : TauRealQ → TauRatQCauchy :=
  Quotient.lift tauRatQCauchyOfCauchyTauReal
    tauRatQCauchyOfCauchyTauReal_respects_equiv

/-- **Verification handle**: the lifted map agrees with the
    per-representative form on `CauchyTauReal.toQ` images. By
    `Quotient.lift`'s defining equation. -/
@[simp] theorem tauRealQToTauRatQCauchy_mk (a : CauchyTauReal) :
    tauRealQToTauRatQCauchy a.toQ = tauRatQCauchyOfCauchyTauReal a := rfl

-- ============================================================
-- B2.alg / W3 Path B / Step 2-fwd-ring-zero-one: zero & one preservation
-- ============================================================

/-- **`cauSeqOfCauchyTauReal CauchyTauReal.zero` has all-zero values**.

    Helper for `tauRealQToTauRatQCauchy_zero` — the underlying
    sequence of the forward image of `CauchyTauReal.zero` is the
    constant-zero sequence in `TauRatQ`. -/
theorem cauSeqOfCauchyTauReal_zero_apply (n : ℕ) :
    (cauSeqOfCauchyTauReal CauchyTauReal.zero) n = 0 := by
  show ((CauchyTauReal.zero.val.approx n).toQ : TauRatQ) = 0
  show ((TauReal.zero.approx n).toQ : TauRatQ) = 0
  show (TauRat.zero.toQ : TauRatQ) = 0
  rfl

/-- **`tauRealQToTauRatQCauchy` preserves zero**:
    `tauRealQToTauRatQCauchy 0 = 0`. -/
theorem tauRealQToTauRatQCauchy_zero :
    tauRealQToTauRatQCauchy 0 = 0 := by
  show tauRealQToTauRatQCauchy CauchyTauReal.zero.toQ = 0
  rw [tauRealQToTauRatQCauchy_mk]
  show CauSeq.Completion.mk (cauSeqOfCauchyTauReal CauchyTauReal.zero) = 0
  -- Show CauSeq is equal to the zero CauSeq
  have h_eq : cauSeqOfCauchyTauReal CauchyTauReal.zero = 0 := by
    apply Subtype.ext
    funext n
    exact cauSeqOfCauchyTauReal_zero_apply n
  rw [h_eq]
  rfl

/-- **`cauSeqOfCauchyTauReal CauchyTauReal.one` has all-one values**.

    Helper for `tauRealQToTauRatQCauchy_one`. -/
theorem cauSeqOfCauchyTauReal_one_apply (n : ℕ) :
    (cauSeqOfCauchyTauReal CauchyTauReal.one) n = 1 := by
  show ((CauchyTauReal.one.val.approx n).toQ : TauRatQ) = 1
  show ((TauReal.one.approx n).toQ : TauRatQ) = 1
  show (TauRat.one.toQ : TauRatQ) = 1
  rfl

/-- **`tauRealQToTauRatQCauchy` preserves one**:
    `tauRealQToTauRatQCauchy 1 = 1`. -/
theorem tauRealQToTauRatQCauchy_one :
    tauRealQToTauRatQCauchy 1 = 1 := by
  show tauRealQToTauRatQCauchy CauchyTauReal.one.toQ = 1
  rw [tauRealQToTauRatQCauchy_mk]
  show CauSeq.Completion.mk (cauSeqOfCauchyTauReal CauchyTauReal.one) = 1
  have h_eq : cauSeqOfCauchyTauReal CauchyTauReal.one = 1 := by
    apply Subtype.ext
    funext n
    exact cauSeqOfCauchyTauReal_one_apply n
  rw [h_eq]
  rfl

-- ============================================================
-- B2.alg / W3 Path B / Step 2-fwd-ring-add-neg-mul: add/neg/mul preservation
-- ============================================================

/-- **Pointwise add equation**: `cauSeqOfCauchyTauReal (a.add b)`
    has the same values as `cauSeqOfCauchyTauReal a +
    cauSeqOfCauchyTauReal b` at every index `n`.

    Pointwise rfl chain: `((a.add b).val.approx n).toQ` unfolds via
    `CauchyTauReal.add` and `TauReal.add` to
    `(TauRat.add (a.val.approx n) (b.val.approx n)).toQ`, which
    equals `(a.val.approx n).toQ + (b.val.approx n).toQ` by
    `TauRatQ.add_mk` (rfl). -/
theorem cauSeqOfCauchyTauReal_add_apply (a b : CauchyTauReal) (n : ℕ) :
    (cauSeqOfCauchyTauReal (a.add b)) n =
    (cauSeqOfCauchyTauReal a) n + (cauSeqOfCauchyTauReal b) n := by
  show (((a.val.add b.val).approx n).toQ : TauRatQ) =
    (a.val.approx n).toQ + (b.val.approx n).toQ
  show ((TauRat.add (a.val.approx n) (b.val.approx n)).toQ : TauRatQ) =
    (a.val.approx n).toQ + (b.val.approx n).toQ
  rfl

/-- **CauSeq-level add equation**: bundle the pointwise equation
    into a `CauSeq` equality via `Subtype.ext` + `funext`. -/
theorem cauSeqOfCauchyTauReal_add (a b : CauchyTauReal) :
    cauSeqOfCauchyTauReal (a.add b) =
    cauSeqOfCauchyTauReal a + cauSeqOfCauchyTauReal b := by
  apply Subtype.ext
  funext n
  exact cauSeqOfCauchyTauReal_add_apply a b n

/-- **`tauRealQToTauRatQCauchy` preserves addition**:
    `tauRealQToTauRatQCauchy (x + y) = tauRealQToTauRatQCauchy x +
    tauRealQToTauRatQCauchy y`.

    Combines `cauSeqOfCauchyTauReal_add` with Mathlib's
    `CauSeq.Completion.mk_add` (a `rfl`). -/
theorem tauRealQToTauRatQCauchy_add (x y : TauRealQ) :
    tauRealQToTauRatQCauchy (x + y) =
    tauRealQToTauRatQCauchy x + tauRealQToTauRatQCauchy y := by
  refine Quotient.inductionOn₂ x y (fun a b => ?_)
  show tauRealQToTauRatQCauchy ((a.add b).toQ) =
    tauRealQToTauRatQCauchy a.toQ + tauRealQToTauRatQCauchy b.toQ
  rw [tauRealQToTauRatQCauchy_mk, tauRealQToTauRatQCauchy_mk,
      tauRealQToTauRatQCauchy_mk]
  unfold tauRatQCauchyOfCauchyTauReal
  rw [cauSeqOfCauchyTauReal_add, ← CauSeq.Completion.mk_add]

/-- **Pointwise neg equation**: `cauSeqOfCauchyTauReal (a.neg)`
    has values `-(cauSeqOfCauchyTauReal a) n` at every index. -/
theorem cauSeqOfCauchyTauReal_neg_apply (a : CauchyTauReal) (n : ℕ) :
    (cauSeqOfCauchyTauReal a.neg) n =
    -((cauSeqOfCauchyTauReal a) n) := by
  show ((a.val.negate.approx n).toQ : TauRatQ) =
    -(a.val.approx n).toQ
  show ((TauRat.negate (a.val.approx n)).toQ : TauRatQ) =
    -(a.val.approx n).toQ
  rfl

/-- **CauSeq-level neg equation**: bundle pointwise into `CauSeq`. -/
theorem cauSeqOfCauchyTauReal_neg (a : CauchyTauReal) :
    cauSeqOfCauchyTauReal a.neg = -(cauSeqOfCauchyTauReal a) := by
  apply Subtype.ext
  funext n
  exact cauSeqOfCauchyTauReal_neg_apply a n

/-- **`tauRealQToTauRatQCauchy` preserves negation**:
    `tauRealQToTauRatQCauchy (-x) = -(tauRealQToTauRatQCauchy x)`. -/
theorem tauRealQToTauRatQCauchy_neg (x : TauRealQ) :
    tauRealQToTauRatQCauchy (-x) =
    -(tauRealQToTauRatQCauchy x) := by
  refine Quotient.inductionOn x (fun a => ?_)
  show tauRealQToTauRatQCauchy a.neg.toQ =
    -(tauRealQToTauRatQCauchy a.toQ)
  rw [tauRealQToTauRatQCauchy_mk, tauRealQToTauRatQCauchy_mk]
  unfold tauRatQCauchyOfCauchyTauReal
  rw [cauSeqOfCauchyTauReal_neg, ← CauSeq.Completion.mk_neg]

/-- **Pointwise mul equation**: `cauSeqOfCauchyTauReal (a.mul b)`
    has values `(cauSeqOfCauchyTauReal a) n * (cauSeqOfCauchyTauReal
    b) n` at every index. -/
theorem cauSeqOfCauchyTauReal_mul_apply (a b : CauchyTauReal) (n : ℕ) :
    (cauSeqOfCauchyTauReal (a.mul b)) n =
    (cauSeqOfCauchyTauReal a) n * (cauSeqOfCauchyTauReal b) n := by
  show (((a.val.mul b.val).approx n).toQ : TauRatQ) =
    (a.val.approx n).toQ * (b.val.approx n).toQ
  show ((TauRat.mul (a.val.approx n) (b.val.approx n)).toQ : TauRatQ) =
    (a.val.approx n).toQ * (b.val.approx n).toQ
  rfl

/-- **CauSeq-level mul equation**: bundle pointwise into `CauSeq`. -/
theorem cauSeqOfCauchyTauReal_mul (a b : CauchyTauReal) :
    cauSeqOfCauchyTauReal (a.mul b) =
    cauSeqOfCauchyTauReal a * cauSeqOfCauchyTauReal b := by
  apply Subtype.ext
  funext n
  exact cauSeqOfCauchyTauReal_mul_apply a b n

/-- **`tauRealQToTauRatQCauchy` preserves multiplication**:
    `tauRealQToTauRatQCauchy (x * y) = tauRealQToTauRatQCauchy x *
    tauRealQToTauRatQCauchy y`. -/
theorem tauRealQToTauRatQCauchy_mul (x y : TauRealQ) :
    tauRealQToTauRatQCauchy (x * y) =
    tauRealQToTauRatQCauchy x * tauRealQToTauRatQCauchy y := by
  refine Quotient.inductionOn₂ x y (fun a b => ?_)
  show tauRealQToTauRatQCauchy ((a.mul b).toQ) =
    tauRealQToTauRatQCauchy a.toQ * tauRealQToTauRatQCauchy b.toQ
  rw [tauRealQToTauRatQCauchy_mk, tauRealQToTauRatQCauchy_mk,
      tauRealQToTauRatQCauchy_mk]
  unfold tauRatQCauchyOfCauchyTauReal
  rw [cauSeqOfCauchyTauReal_mul, ← CauSeq.Completion.mk_mul]

-- ============================================================
-- B2.alg / W3 Path B / Step 2-fwd-RingHom: package as RingHom
-- ============================================================

/-- **`tauRealQToTauRatQCauchyRingHom : TauRealQ →+* TauRatQCauchy`** —
    the lifted forward map packaged as a Mathlib `RingHom`.

    Bundles `tauRealQToTauRatQCauchy` together with its five
    preservation witnesses (`_zero`, `_one`, `_add`, `_mul`) into
    Mathlib's `RingHom` structure. Negation preservation follows
    automatically from `RingHom`'s additive-group structure (proved
    separately as `tauRealQToTauRatQCauchy_neg`).

    This is the **forward-direction RingHom** half of the eventual
    `RingEquiv TauRealQ TauRatQCauchy` (Path B Step 2 KEYSTONE);
    the inverse direction + RingEquiv assembly are queued. -/
noncomputable def tauRealQToTauRatQCauchyRingHom :
    TauRealQ →+* TauRatQCauchy where
  toFun     := tauRealQToTauRatQCauchy
  map_zero' := tauRealQToTauRatQCauchy_zero
  map_one'  := tauRealQToTauRatQCauchy_one
  map_add'  := tauRealQToTauRatQCauchy_add
  map_mul'  := tauRealQToTauRatQCauchy_mul

/-- **Coercion handle**: the underlying function of
    `tauRealQToTauRatQCauchyRingHom` is `tauRealQToTauRatQCauchy`. -/
@[simp] theorem tauRealQToTauRatQCauchyRingHom_apply (x : TauRealQ) :
    tauRealQToTauRatQCauchyRingHom x = tauRealQToTauRatQCauchy x := rfl

-- ============================================================
-- B2.alg / W3 Path B / Step 2-back-func: backward function
-- ============================================================

/-- **Helper — `(TauRat.ofNatRecip k).toQ = 1/(k+1)` in TauRatQ**.

    Same identity used in the forward proof, factored out for
    reuse in the backward direction. Combines Step 2-pre-2's
    NatCast/div ring-hom preservation lemmas. -/
theorem TauRat.ofNatRecip_toQ (k : ℕ) :
    (TauRat.ofNatRecip k).toQ = (1 : TauRatQ) / ((k + 1 : ℕ) : TauRatQ) := by
  rw [TauRatQ.eq_iff_toRat_eq, TauRatQ.toRat_mk,
      TauRat.ofNatRecip_toRat, TauRatQ.toRat_div,
      TauRatQ.toRat_natCast,
      show (1 : TauRatQ).toRat = 1 from TauRatQ.toRat_one]
  push_cast
  rfl

/-- **Backward function `CauSeq TauRatQ abs → CauchyTauReal`**.

    Given a Mathlib `CauSeq` over `TauRatQ`, produces a
    `CauchyTauReal` via:

    - **Sequence**: `n ↦ Quotient.out (f n) : ℕ → TauRat` (uses
      `Quotient.out` to pick a representative for each `f n :
      TauRatQ`)
    - **`IsCauchy` witness**: translate Mathlib's `IsCauSeq` (∀
      ε > 0, ∃ N) to τ-native `TauReal.IsCauchy` (modulus + `1/(k+1)`
      bound) using `IsCauSeq.cauchy₂` (pairwise bound) for cleaner
      triangle-inequality handling.

    This is the **inverse direction** of `cauSeqOfCauchyTauReal`;
    together they assemble `TauRealQ ≃+* TauRatQCauchy` (Path B
    Step 2 KEYSTONE). -/
noncomputable def cauchyTauRealOfCauSeq
    (f : CauSeq TauRatQ (abs : TauRatQ → TauRatQ)) :
    CauchyTauReal := by
  refine ⟨⟨fun n => Quotient.out (f n)⟩, ?_⟩
  -- Goal: TauReal.IsCauchy ⟨fun n => Quotient.out (f n)⟩
  -- IsCauchy: ∃ μ, ∀ k m n, μ k ≤ m → μ k ≤ n →
  --   TauRat.lt (((f m).out).sub ((f n).out)).abs (TauRat.ofNatRecip k)

  -- Step 1: positivity of 1/(k+1) in TauRatQ
  have recip_pos : ∀ k : ℕ, (0 : TauRatQ) < (1 : TauRatQ) / ((k + 1 : ℕ) : TauRatQ) := by
    intro k
    apply div_pos one_pos
    exact_mod_cast Nat.succ_pos k

  -- Step 2: extract modulus via IsCauSeq.cauchy₂ (pairwise bound)
  refine ⟨fun k => Classical.choose (f.property.cauchy₂ (recip_pos k)), ?_⟩
  intro k m n hm hn

  -- Step 3: pairwise bound from cauchy₂
  have h_bound : abs (f m - f n) < (1 : TauRatQ) / ((k + 1 : ℕ) : TauRatQ) :=
    Classical.choose_spec (f.property.cauchy₂ (recip_pos k)) m hm n hn

  -- Step 4: Translate goal TauRat.lt → TauRatQ.<
  show TauRat.lt _ _
  rw [TauRat.lt_iff_toQ_lt]
  -- Goal: (((f m).out).sub ((f n).out)).abs.toQ < (TauRat.ofNatRecip k).toQ

  -- Step 5: rewrite TauRat.abs.toQ → |.toQ|, sub.toQ → toQ - toQ
  rw [TauRat.abs_toQ]
  -- Goal: |(((f m).out).sub ((f n).out)).toQ| < (TauRat.ofNatRecip k).toQ

  -- Step 6: expand (sub).toQ = .toQ - .toQ
  have h_sub : (((f m).out).sub ((f n).out)).toQ =
      ((f m).out).toQ - ((f n).out).toQ := by
    show (((f m).out).add ((f n).out).negate).toQ = _
    show (((f m).out).toQ + ((f n).out).negate.toQ : TauRatQ) =
        ((f m).out).toQ - ((f n).out).toQ
    show (((f m).out).toQ + (-((f n).out).toQ) : TauRatQ) =
        ((f m).out).toQ - ((f n).out).toQ
    ring
  rw [h_sub]

  -- Step 7: Quotient.out_eq for both representatives
  rw [show ((f m).out).toQ = f m from Quotient.out_eq (f m),
      show ((f n).out).toQ = f n from Quotient.out_eq (f n)]
  -- Goal: |f m - f n| < (TauRat.ofNatRecip k).toQ

  -- Step 8: rewrite RHS via h_ofNR helper
  rw [TauRat.ofNatRecip_toQ]
  -- Goal: |f m - f n| < (1 : TauRatQ) / ((k + 1 : ℕ) : TauRatQ)

  exact h_bound

-- ============================================================
-- B2.alg / W3 Path B / Step 2-back-equiv: backward respects ≈
-- ============================================================

/-- **Backward function respects equivalence**: if two `CauSeq` values
    are equivalent (in Mathlib's `≈` sense, i.e., `LimZero (f - g)`),
    then their backward images under `cauchyTauRealOfCauSeq` are
    `CauchyTauReal`-equivalent.

    Mirror of `cauSeqOfCauchyTauReal_respects_equiv` (forward
    direction). Uses the same Archimedean + LimZero + abs/lt
    translation chain, adapted for the `Quotient.out`-based
    representative selection. -/
theorem cauchyTauRealOfCauSeq_respects_equiv
    (f g : CauSeq TauRatQ (abs : TauRatQ → TauRatQ))
    (h : f ≈ g) :
    CauchyTauReal.equiv
      (cauchyTauRealOfCauSeq f) (cauchyTauRealOfCauSeq g) := by
  -- CauchyTauReal.equiv unfolds to TauReal.equiv on .val parts
  show TauReal.equiv (cauchyTauRealOfCauSeq f).val
                     (cauchyTauRealOfCauSeq g).val

  -- Step 1: positivity of 1/(k+1) in TauRatQ
  have recip_pos : ∀ k : ℕ, (0 : TauRatQ) < (1 : TauRatQ) / ((k + 1 : ℕ) : TauRatQ) := by
    intro k
    apply div_pos one_pos
    exact_mod_cast Nat.succ_pos k

  -- Step 2: apply `f ≈ g` (= LimZero (f - g)) at ε_k = 1/(k+1)
  refine ⟨fun k => Classical.choose (h _ (recip_pos k)), ?_⟩
  intro k n hn

  -- Step 3: LimZero bound at index n
  have h_bound : abs ((f - g) n) < (1 : TauRatQ) / ((k + 1 : ℕ) : TauRatQ) :=
    Classical.choose_spec (h _ (recip_pos k)) n hn

  -- Step 4: `(f - g) n = f n - g n` (CauSeq sub is pointwise rfl)
  rw [show ((f - g) n : TauRatQ) = f n - g n from rfl] at h_bound

  -- Step 5: translate goal TauRat.lt → TauRatQ.<, abs → |·|
  show TauRat.lt _ _
  rw [TauRat.lt_iff_toQ_lt, TauRat.abs_toQ]

  -- Step 5.5: definitionally fold .val.approx n = Quotient.out (f n)
  show |((Quotient.out (f n)).sub (Quotient.out (g n))).toQ|
        < (TauRat.ofNatRecip k).toQ

  -- Step 6: expand (sub).toQ = .toQ - .toQ
  have h_sub : (((Quotient.out (f n))).sub (Quotient.out (g n))).toQ =
      (Quotient.out (f n)).toQ - (Quotient.out (g n)).toQ := by
    show ((Quotient.out (f n)).add (Quotient.out (g n)).negate).toQ = _
    show ((Quotient.out (f n)).toQ + (Quotient.out (g n)).negate.toQ
            : TauRatQ) = _
    show ((Quotient.out (f n)).toQ + (-(Quotient.out (g n)).toQ)
            : TauRatQ) = _
    ring
  rw [h_sub]

  -- Step 7: Quotient.out_eq + ofNatRecip_toQ
  rw [show (Quotient.out (f n)).toQ = f n from Quotient.out_eq (f n),
      show (Quotient.out (g n)).toQ = g n from Quotient.out_eq (g n),
      TauRat.ofNatRecip_toQ]

  -- Goal: |f n - g n| < 1/(k+1)
  exact h_bound

-- ============================================================
-- B2.alg / W3 Path B / Step 2-back-quotient: lift to TauRatQCauchy
-- ============================================================

/-- **Composition with `CauchyTauReal.toQ`**: package the
    `CauchyTauReal` produced by `cauchyTauRealOfCauSeq` into a
    `TauRealQ` value (the quotient).

    Per-`CauSeq`-representative form of the backward map; the next
    step lifts to `TauRatQCauchy` via `Quotient.lift`. -/
noncomputable def tauRealQOfCauSeq
    (f : CauSeq TauRatQ (abs : TauRatQ → TauRatQ)) : TauRealQ :=
  (cauchyTauRealOfCauSeq f).toQ

/-- **Composed map respects equivalence**: equivalent CauSeqs map
    to the same `TauRealQ` class. Combines
    `cauchyTauRealOfCauSeq_respects_equiv` (Step 2-back-equiv) with
    `Quotient.sound`. -/
theorem tauRealQOfCauSeq_respects_equiv
    (f g : CauSeq TauRatQ (abs : TauRatQ → TauRatQ)) (h : f ≈ g) :
    tauRealQOfCauSeq f = tauRealQOfCauSeq g := by
  unfold tauRealQOfCauSeq
  exact Quotient.sound (cauchyTauRealOfCauSeq_respects_equiv f g h)

/-- **B2.alg / W3 Path B / Step 2-back-quotient — the lifted
    backward map** `TauRatQCauchy → TauRealQ`.

    Inverse-direction counterpart to `tauRealQToTauRatQCauchy` (PR
    #153). Lifts `tauRealQOfCauSeq` (per-rep) to the `TauRatQCauchy`
    quotient via `Quotient.lift`, using `tauRealQOfCauSeq_respects_equiv`
    as the equivalence-respect witness. -/
noncomputable def tauRatQCauchyToTauRealQ : TauRatQCauchy → TauRealQ :=
  Quotient.lift tauRealQOfCauSeq tauRealQOfCauSeq_respects_equiv

/-- **Verification handle**: the lifted map agrees with the
    per-representative form on `CauSeq.Completion.mk` images. By
    `Quotient.lift`'s defining equation. -/
@[simp] theorem tauRatQCauchyToTauRealQ_mk
    (f : CauSeq TauRatQ (abs : TauRatQ → TauRatQ)) :
    tauRatQCauchyToTauRealQ (CauSeq.Completion.mk f) =
    (cauchyTauRealOfCauSeq f).toQ := rfl

end Tau.Boundary
