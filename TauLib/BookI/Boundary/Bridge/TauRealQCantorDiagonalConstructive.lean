import TauLib.BookI.Boundary.Bridge.TauRealQuotient
import TauLib.BookI.Boundary.ConstructiveReals

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

end Tau.Boundary
