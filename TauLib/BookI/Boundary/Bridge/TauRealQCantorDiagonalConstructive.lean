import TauLib.BookI.Boundary.Bridge.TauRealQuotient
import TauLib.BookI.Boundary.ConstructiveReals
import TauLib.BookI.Boundary.TauRatField
import TauLib.BookI.Boundary.TauRatOrder
import TauLib.BookI.Boundary.TauRatAbs

/-!
# TauLib.BookI.Boundary.Bridge.TauRealQCantorDiagonalConstructive

**Workstream B2.alg / W3 (Path B, Option β cascade) — constructive
Cantor's diagonal for `TauRealQ` via bare-metal substrate.**

This module shipped Cantor's diagonal as a *truly constructive*
procedure for `TauRealQ`, completing the no-ghost reading developed in
companion research note `cantor-bridge-categorical`. The strategic
insight: the Axiom of Choice is an *addressing mechanism*, not a
*creation mechanism*. The diagonal real is an existing `TauRealQ`
element; the construction should be constructive, with the *only*
classical content concentrated at **representative selection** (input
boundary, `Quotient.out` + `Classical.choose` for modulus extraction).

## What this module ultimately ships (across 7 phases, this file
   evolves over the cascade)

- **`DataCauchyTauReal`** (Phase 1): a parallel modulus-in-data type
  alongside the existing `CauchyTauReal`. The modulus is *data*, not a
  `Prop`-level existential, so constructive procedures can access it
  without `Classical.choose`.
- **`bisectStep`** (Phase 2): one-step rational interval bisection,
  fully constructive, with explicit margin and shrink rate.
- **`diagonalIntervalSeq` / `diagonalSeq`** (Phase 3): iterated bisection
  producing the constructive diagonal Cauchy sequence in `TauRat`.
- **`diagonalData`** (Phase 4): packages the sequence into
  `DataCauchyTauReal` with explicit Cauchy modulus.
- **Constructive separation** (Phase 5): `¬ TauReal.equiv (diagonalData
  f).val (f n).val` proved directly from explicit lower bounds + the
  Archimedean property — *no LEM, no Choice in this proof*.
- **TauRealQ-level lift** (Phase 6): `TauRealQ.cantorDiagonalConstructive`
  with constructive separation theorem; the only classical move is at
  the input boundary.
- **Comparison with PR #163** (Phase 7): both `TauRealQ.cantorDiagonal`
  (PR #163, abstract via `Classical.choose` on existence) and
  `TauRealQ.cantorDiagonalConstructive` (this cascade) coexist; both
  satisfy the bijection-impossibility separation.

## This phase (Phase 1) ships

The parallel type and the bridge functions:

- `DataCauchyTauReal` structure with `(val, modulus, witness)` as data
- `DataCauchyTauReal.toCauchy` (constructive forward map: data → Prop)
- `CauchyTauReal.toData` (noncomputable backward map: Prop → data via
  `Classical.choose`)
- `DataCauchyTauReal.toQ` (composition to `TauRealQ`)
- `@[simp]` round-trip lemmas for `.val`

## Strategic context

Path B's bridge `tauRealQRingEquivReal : TauRealQ ≃+* ℝ` (PR #161) and
the abstract Cantor diagonal `TauRealQ.cantorDiagonal` (PR #163) provide
the *classical* picture of `TauRealQ`'s uncountability. This cascade
provides the *constructive* picture: the diagonal is a constructor of
existing `TauRealQ` elements, not a creator of new entities.

The two pictures coexist via the Löwenheim-Skolem-like internal-vs-
external framing developed in the companion research note. This file
implements the constructive (internal) side at the bare-metal level.

## Atlas cross-references

- `atlas/insights/2026-04-29-constructive-real-cardinality-boundary.md`
  (the Bishop-school constructivity boundary — this file lives within it)
- companion research note `papers/research-notes/cantor-bridge-categorical/`
  (the philosophical analysis — this file is the formal payoff)

## Registry Cross-References

- [I.T-B2.alg.W3-pathB-cantor-constructive-phase1] DataCauchyTauReal
                                                   substrate (this phase)
-/

set_option autoImplicit false

namespace Tau.Boundary

open Tau.Denotation

-- ============================================================
-- Phase 1: DataCauchyTauReal — modulus-in-data parallel type
-- ============================================================

/-- **`DataCauchyTauReal`**: a parallel modulus-in-data Cauchy real.

    Unlike the existing `CauchyTauReal` (which carries `isCauchy : Prop`
    as an existential `IsCauchy`), this structure carries the Cauchy
    modulus *as data* alongside its witness. This enables constructive
    procedures (bisection, separation arguments) that need *direct
    access* to the modulus without `Classical.choose`.

    Ships in Phase 1 of the constructive Cantor diagonal cascade. -/
structure DataCauchyTauReal where
  val : TauReal
  modulus : Nat → Nat
  cauchy_witness : ∀ k m n : Nat, modulus k ≤ m → modulus k ≤ n →
    TauRat.lt ((val.approx m).sub (val.approx n)).abs (TauRat.ofNatRecip k)

/-- **Constructive forward map**: a `DataCauchyTauReal` provides
    everything needed for a `CauchyTauReal`. The Prop-level existential
    `IsCauchy` is witnessed by the data-level `(modulus, witness)` pair. -/
def DataCauchyTauReal.toCauchy (d : DataCauchyTauReal) : CauchyTauReal :=
  ⟨d.val, ⟨d.modulus, d.cauchy_witness⟩⟩

/-- **Backward map**: every `CauchyTauReal` can be cast to
    `DataCauchyTauReal` by extracting its modulus via `Classical.choose`.

    This map is **noncomputable** — Choice enters here. The forward map
    above is fully constructive; this backward map is the explicit place
    where Choice content is added when going from Prop-level to
    data-level. -/
noncomputable def CauchyTauReal.toData (c : CauchyTauReal) : DataCauchyTauReal :=
  ⟨c.val, Classical.choose c.isCauchy, Classical.choose_spec c.isCauchy⟩

/-- **Composition to `TauRealQ`**: send a `DataCauchyTauReal` to its
    quotient class. Constructive (composition of constructive
    `toCauchy` and `Quotient.mk`). -/
def DataCauchyTauReal.toQ (d : DataCauchyTauReal) : TauRealQ :=
  d.toCauchy.toQ

-- ============================================================
-- Phase 1: round-trip @[simp] lemmas for .val
-- ============================================================

/-- The `val` projection is preserved by the forward map (definitional). -/
@[simp] theorem DataCauchyTauReal.toCauchy_val (d : DataCauchyTauReal) :
    d.toCauchy.val = d.val := rfl

/-- The `val` projection is preserved by the backward map (Choice
    affects only the modulus, not the underlying TauReal). -/
@[simp] theorem CauchyTauReal.toData_val (c : CauchyTauReal) :
    c.toData.val = c.val := rfl

/-- The `modulus` of `toData` is the `Classical.choose` of `isCauchy`. -/
theorem CauchyTauReal.toData_modulus (c : CauchyTauReal) :
    c.toData.modulus = Classical.choose c.isCauchy := rfl

/-- Forward map is the identity on `val`-and-modulus extracted from
    `toData`: composing `toData` then `toCauchy` recovers the same
    underlying TauReal. -/
@[simp] theorem CauchyTauReal.toData_toCauchy_val (c : CauchyTauReal) :
    c.toData.toCauchy.val = c.val := rfl

/-- Composing `toCauchy` then `toData` returns a `DataCauchyTauReal`
    with the same `val` (the modulus may differ from the original `d`'s,
    since `Classical.choose` extracts *some* modulus). -/
@[simp] theorem DataCauchyTauReal.toCauchy_toData_val (d : DataCauchyTauReal) :
    d.toCauchy.toData.val = d.val := rfl

-- ============================================================
-- Phase 2: bisectStep — constructive interval bisection
-- ============================================================

/-! ## Phase 2: bisection step

Given an interval `[a, b]` and a probe value `probe`, return a sub-
interval that EXCLUDES the probe with explicit margin and width.

Design:
- Width shrinks by factor 4 per step (clean recursion)
- Probe is excluded by margin ≥ (b − a) / 4 on either side
- Decidable bisection via `TauRat.lt`'s underlying `Rat` order

To avoid `TauRat.div`'s nonzero-proof obligation in the body, we use a
helper `TauRat.scaleDownByPos` that scales a TauRat by a positive
natural divisor by multiplying the denominator. This is more
constructive (no Prop-level hypotheses inside the body of `bisectStep`). -/

/-- Scale a `TauRat` by `1/n` for a positive natural `n`: multiplies the
    denominator. Constructive (no `is_nonzero` Prop required). -/
def TauRat.scaleDownByPos (a : TauRat) (n : Nat) (hn : 0 < n) : TauRat :=
  ⟨a.num, a.den * n, Nat.mul_pos a.den_pos hn⟩

/-- Halving a TauRat: scale by 1/2. -/
def TauRat.half (a : TauRat) : TauRat :=
  TauRat.scaleDownByPos a 2 (by decide)

/-- Quartering a TauRat: scale by 1/4. -/
def TauRat.quarter (a : TauRat) : TauRat :=
  TauRat.scaleDownByPos a 4 (by decide)

/-- Decidability of `TauRat.lt` (routes through `Rat.lt` via `toRat`). -/
instance TauRat.decidableLt (a b : TauRat) : Decidable (TauRat.lt a b) :=
  inferInstanceAs (Decidable (a.toRat < b.toRat))

/-- Decidability of `TauRat.le` (routes through `Rat.le` via `toRat`). -/
instance TauRat.decidableLe (a b : TauRat) : Decidable (TauRat.le a b) :=
  inferInstanceAs (Decidable (a.toRat ≤ b.toRat))

/-- **`bisectStep`**: one bisection step for the constructive Cantor
    diagonal. Given an interval `[a, b]` and a probe value `probe`,
    return a sub-interval `[a', b']` such that:

    - **Width**: `b' − a' = (b − a) / 4` (cleanly shrinking by factor 4)
    - **Separation from probe**: every `x ∈ [a', b']` satisfies
      `|x − probe| ≥ (b − a) / 4`
    - **Subset**: `[a', b'] ⊆ [a, b]`

    Logic: split `[a, b]` into halves at `mid := (a + b) / 2`. If `probe`
    is in the lower half (`probe ≤ mid`), pick the upper "shifted half"
    `[mid + (b − a) / 4, b]`; otherwise pick the lower shifted half
    `[a, mid − (b − a) / 4]`. The shift creates a margin of `(b − a) / 4`
    between probe and the new interval. -/
def bisectStep (a b probe : TauRat) : TauRat × TauRat :=
  let mid := (a.add b).half
  let q := (b.sub a).quarter
  if probe.le mid then (mid.add q, b) else (a, mid.sub q)

-- ============================================================
-- Phase 2: structural lemmas about bisectStep at the toRat level
-- ============================================================

/-! Phase 5 (constructive separation) and Phase 3 (Cauchy proof for the
diagonal sequence) need to reason about widths and bounds at the `Rat`
level (where `linarith` and `field_simp` are available). The lemmas
below state the key structural facts about `bisectStep` after passing
through `TauRat.toRat`. -/

/-- `scaleDownByPos` corresponds to `Rat`-level division. -/
theorem TauRat.scaleDownByPos_toRat (a : TauRat) (n : Nat) (hn : 0 < n) :
    (TauRat.scaleDownByPos a n hn).toRat = a.toRat / (n : Rat) := by
  simp only [TauRat.toRat, TauRat.scaleDownByPos]
  push_cast
  have ha : (a.den : Rat) ≠ 0 := a.den_ne_zero_rat
  have hn' : (n : Rat) ≠ 0 := by exact_mod_cast Nat.pos_iff_ne_zero.mp hn
  field_simp

/-- `half` corresponds to `Rat`-level division by 2. -/
theorem TauRat.half_toRat (a : TauRat) : a.half.toRat = a.toRat / 2 := by
  unfold TauRat.half
  rw [TauRat.scaleDownByPos_toRat]
  norm_num

/-- `quarter` corresponds to `Rat`-level division by 4. -/
theorem TauRat.quarter_toRat (a : TauRat) : a.quarter.toRat = a.toRat / 4 := by
  unfold TauRat.quarter
  rw [TauRat.scaleDownByPos_toRat]
  norm_num

/-- **bisectStep_subset (toRat form)**: the new interval is contained
    in the old. Proved by case analysis on the bisection branch and
    `linarith` after passing through `toRat`. -/
theorem bisectStep_subset (a b probe : TauRat) (hab : a.toRat ≤ b.toRat) :
    let p := bisectStep a b probe
    a.toRat ≤ p.1.toRat ∧ p.2.toRat ≤ b.toRat := by
  unfold bisectStep
  by_cases h : probe.le ((a.add b).half)
  · simp only [h, if_true]
    refine ⟨?_, le_refl _⟩
    rw [toRat_add, TauRat.half_toRat, TauRat.quarter_toRat,
        toRat_add, toRat_sub]
    linarith
  · simp only [h, if_false]
    refine ⟨le_refl _, ?_⟩
    rw [toRat_sub, TauRat.half_toRat, TauRat.quarter_toRat,
        toRat_add, toRat_sub]
    linarith

/-- **bisectStep_width (toRat form)**: the new interval has width
    `(b − a) / 4` in `Rat`. -/
theorem bisectStep_width (a b probe : TauRat) :
    let p := bisectStep a b probe
    p.2.toRat - p.1.toRat = (b.toRat - a.toRat) / 4 := by
  unfold bisectStep
  by_cases h : probe.le ((a.add b).half)
  · simp only [h, if_true]
    rw [toRat_add, TauRat.half_toRat, TauRat.quarter_toRat,
        toRat_add, toRat_sub]
    ring
  · simp only [h, if_false]
    rw [toRat_sub, TauRat.half_toRat, TauRat.quarter_toRat,
        toRat_add, toRat_sub]
    ring

/-- **bisectStep_separation (toRat form)**: every point in the new
    interval is separated from the probe by at least `(b − a) / 4`. -/
theorem bisectStep_separation (a b probe : TauRat) (hab : a.toRat ≤ b.toRat) :
    let p := bisectStep a b probe
    ∀ x : TauRat, p.1.toRat ≤ x.toRat → x.toRat ≤ p.2.toRat →
      |x.toRat - probe.toRat| ≥ (b.toRat - a.toRat) / 4 := by
  unfold bisectStep
  by_cases h : probe.le ((a.add b).half)
  · -- probe ≤ mid: new interval is [mid + q, b]; probe is to the left,
    -- separation = x - probe ≥ (mid + q) - mid = q = (b-a)/4
    simp only [h, if_true]
    intro x hx_lo _
    rw [toRat_add, TauRat.half_toRat, TauRat.quarter_toRat,
        toRat_add, toRat_sub] at hx_lo
    have h_probe : probe.toRat ≤ (a.toRat + b.toRat) / 2 := by
      have h' := h
      simp only [TauRat.le, toRat_add, TauRat.half_toRat] at h'
      linarith
    have hpos : (0 : Rat) ≤ x.toRat - probe.toRat := by linarith
    rw [ge_iff_le, abs_of_nonneg hpos]
    linarith
  · -- probe > mid: new interval is [a, mid - q]; probe is to the right,
    -- separation = probe - x ≥ mid - (mid - q) = q = (b-a)/4
    simp only [h, if_false]
    intro x _ hx_hi
    rw [toRat_sub, TauRat.half_toRat, TauRat.quarter_toRat,
        toRat_add, toRat_sub] at hx_hi
    have h_probe : probe.toRat > (a.toRat + b.toRat) / 2 := by
      have h' := h
      simp only [TauRat.le, toRat_add, TauRat.half_toRat] at h'
      push_neg at h'
      linarith
    have hneg : x.toRat - probe.toRat ≤ 0 := by linarith
    rw [ge_iff_le, abs_of_nonpos hneg]
    linarith

-- ============================================================
-- Phase 3: diagonal interval + midpoint sequences
-- ============================================================

/-! Iterated bisection produces a sequence of nested rational intervals
that shrink by factor 4 per step. The midpoint sequence is the
constructive Cantor diagonal as a TauRat-valued ℕ-indexed sequence. -/

/-- Precision level used when probing `f n` at step `n`. The value
    `4 ^ (n + 2)` is chosen so that `(f n)`'s approximation error,
    bounded by `1 / (4 ^ (n + 2) + 1)`, is smaller than the new
    interval's quarter-width `(1 / 4) ^ (n + 1)` at step `n + 1`.
    Phase 5 will use this precision margin. -/
def diagonalProbeLevel (n : Nat) : Nat := 4 ^ (n + 2)

/-- The probe value: `f n`'s approximation at the chosen precision
    level, using `f n`'s explicit modulus (no `Classical.choose`
    needed — modulus is `data` in `DataCauchyTauReal`). -/
def diagonalProbe (f : Nat → DataCauchyTauReal) (n : Nat) : TauRat :=
  (f n).val.approx ((f n).modulus (diagonalProbeLevel n))

/-- **Iterated bisection — the interval sequence**. Starts at `[0, 1]`
    and bisects against `f n`'s probe at each step, producing a
    sub-interval that excludes the probe with margin. -/
def diagonalIntervalSeq (f : Nat → DataCauchyTauReal) : Nat → TauRat × TauRat
  | 0 => (TauRat.zero, TauRat.one)
  | n+1 =>
      let p := diagonalIntervalSeq f n
      bisectStep p.1 p.2 (diagonalProbe f n)

/-- **The midpoint sequence — the constructive diagonal**.
    The midpoint of each bisected interval. -/
def diagonalSeq (f : Nat → DataCauchyTauReal) (n : Nat) : TauRat :=
  let p := diagonalIntervalSeq f n
  (p.1.add p.2).half

-- ============================================================
-- Phase 3: width and subset properties at the toRat level
-- ============================================================

/-- **Width recursion**: at step n, the interval has width `1 / 4^n` in Rat. -/
theorem diagonalIntervalSeq_width_toRat (f : Nat → DataCauchyTauReal) (n : Nat) :
    let p := diagonalIntervalSeq f n
    p.2.toRat - p.1.toRat = (1 : Rat) / (4 ^ n : Nat) := by
  induction n with
  | zero =>
    -- Step 0: interval is (0, 1), width = 1 - 0 = 1 = 1/4^0 = 1/1
    show TauRat.one.toRat - TauRat.zero.toRat = (1 : Rat) / ((4 ^ 0 : Nat) : Rat)
    rw [toRat_one, toRat_zero]
    norm_num
  | succ n ih =>
    -- Step n+1: bisectStep, width shrinks by factor 4
    have hbw := bisectStep_width
      (diagonalIntervalSeq f n).1 (diagonalIntervalSeq f n).2
      (diagonalProbe f n)
    show (bisectStep _ _ _).2.toRat - (bisectStep _ _ _).1.toRat
        = (1 : Rat) / ((4 ^ (n + 1) : Nat) : Rat)
    rw [hbw]
    have ih' : (diagonalIntervalSeq f n).2.toRat -
               (diagonalIntervalSeq f n).1.toRat
             = (1 : Rat) / ((4 ^ n : Nat) : Rat) := ih
    rw [ih']
    push_cast
    field_simp
    ring

/-- **Subset (one step)**: the new interval is contained in the old. -/
theorem diagonalIntervalSeq_subset_step (f : Nat → DataCauchyTauReal) (n : Nat) :
    let p := diagonalIntervalSeq f n
    let p' := diagonalIntervalSeq f (n + 1)
    p.1.toRat ≤ p'.1.toRat ∧ p'.2.toRat ≤ p.2.toRat := by
  -- Note: requires a ≤ b at step n; provable from width recursion.
  have hwn := diagonalIntervalSeq_width_toRat f n
  have hwn' : (1 : Rat) / ((4 ^ n : Nat) : Rat) ≥ 0 := by positivity
  have hab : (diagonalIntervalSeq f n).1.toRat ≤ (diagonalIntervalSeq f n).2.toRat := by
    linarith
  show let p := diagonalIntervalSeq f n
       let p' := bisectStep p.1 p.2 (diagonalProbe f n)
       p.1.toRat ≤ p'.1.toRat ∧ p'.2.toRat ≤ p.2.toRat
  exact bisectStep_subset _ _ _ hab

/-- **Width is non-negative** in Rat (consequence of width recursion). -/
theorem diagonalIntervalSeq_left_le_right (f : Nat → DataCauchyTauReal) (n : Nat) :
    let p := diagonalIntervalSeq f n
    p.1.toRat ≤ p.2.toRat := by
  have h := diagonalIntervalSeq_width_toRat f n
  have hpos : (0 : Rat) < ((4 ^ n : Nat) : Rat) := by positivity
  have : (0 : Rat) ≤ (1 : Rat) / ((4 ^ n : Nat) : Rat) := by positivity
  linarith

end Tau.Boundary
