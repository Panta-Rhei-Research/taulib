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

end Tau.Boundary
