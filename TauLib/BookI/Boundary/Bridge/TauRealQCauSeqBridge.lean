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

end Tau.Boundary
