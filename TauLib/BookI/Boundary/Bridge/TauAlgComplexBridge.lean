import TauLib.BookI.Boundary.Bridge.TauAlgComplex
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Algebraic.Integral

/-!
# TauLib.BookI.Boundary.Bridge.TauAlgComplexBridge

**Workstream B2.alg / W5 — Bridge `TauAlgComplex ≃ₐ[TauRatQ]
AlgebraicClosure ℚ`**.

Provides the **canonical-anchoring verification handle** for
`TauAlgComplex` (W4) by constructing the `AlgEquiv` to Mathlib's
`AlgebraicClosure ℚ` over the existing `TauRatQ ≃+* ℚ` (Wave 40)
bridge.

This is the analogue of B1.4c.5b (the II.T10 cross-check for
topology equality): the τ-native ℚ̄ is provably isomorphic to
Mathlib's canonical ℚ̄, cross-validating the canonical anchoring
across two independent constructions.

## Construction

By Mathlib's `IsAlgClosure.equiv R L M`: any two algebraic closures
of the same base ring `R` are AlgEquiv via `IsAlgClosed.lift` in
both directions.

For us with `R := TauRatQ`, `L := TauAlgComplex`,
`M := AlgebraicClosure ℚ`:
- `TauAlgComplex` is `IsAlgClosure TauRatQ` by W4
- `AlgebraicClosure ℚ` becomes `IsAlgClosure TauRatQ` once we set
  up the right algebra-tower instances:
  1. `Algebra TauRatQ ℚ` (via `ringEquivRat`)
  2. `Algebra TauRatQ (AlgebraicClosure ℚ)` (composition through ℚ)
  3. `IsScalarTower TauRatQ ℚ (AlgebraicClosure ℚ)` (`rfl`-level
     via `IsScalarTower.of_algebraMap_eq'`)
  4. `Algebra.IsAlgebraic TauRatQ ℚ` (every `q : ℚ` is algebraic
     via `isAlgebraic_algebraMap` since `ringEquivRat` is surjective)
  5. `Algebra.IsAlgebraic TauRatQ (AlgebraicClosure ℚ)` via
     `IsAlgebraic.trans` (transitivity of algebraic extensions)

Then `IsAlgClosure.equiv` ships the `AlgEquiv`.

## Verification handle (dossier Part 7.2)

This module provides the **dual-path verification handle for
TauAlgComplex** (analogous to B1.4c.5b for the topology equality).
The τ-native ℚ̄ corresponds bijectively to Mathlib's canonical ℚ̄
over the algebra structure; both constructions agree.

## Substrate dependencies

- `TauAlgComplex.lean` (W4): `TauAlgComplex := AlgebraicClosure
  TauRatQ` with `Field` + `Algebra TauRatQ` + `IsAlgClosed` (and
  hence `IsAlgClosure TauRatQ TauAlgComplex` via Mathlib instance)
- `TauRatQuotient.lean` (Wave 40): `TauRatQ.ringEquivRat`
- Mathlib: `IsAlgClosure`, `IsAlgClosure.equiv`,
  `IsScalarTower.of_algebraMap_eq'`, `IsAlgebraic.trans`,
  `isAlgebraic_algebraMap`

## Atlas cross-references

- `atlas/insights/2026-04-29-constructive-real-cardinality-boundary.md`
- `atlas/insights/2026-05-04-workstream-b1-completion-and-depth-zero-revelation.md`
  (Insight 3 "The dual-path verification handle" — same pattern)

## Registry Cross-References

- [I.T-W40-RingEquiv]            `TauRatQ ≃+* ℚ` (substrate)
- [I.T-B2.alg.W4-TauAlgComplex]  `TauAlgComplex` (substrate)
- [I.T-B2.alg.W5-CanonicalBridge] `TauAlgComplex ≃ₐ[TauRatQ]
                                    AlgebraicClosure ℚ` (this module)
-/

set_option autoImplicit false

namespace Tau.Boundary

open Tau.Denotation

-- ============================================================
-- PART 1: Algebra-tower setup
-- ============================================================

/-- **`Algebra TauRatQ ℚ`** via the existing Wave 40 bridge
    `TauRatQ.ringEquivRat : TauRatQ ≃+* ℚ`. The algebra map IS
    the underlying ring hom of the ring equiv. -/
noncomputable instance instAlgebraTauRatQRat : Algebra TauRatQ ℚ :=
  RingHom.toAlgebra TauRatQ.ringEquivRat.toRingHom

-- Note: Mathlib's `AlgebraicClosure.instAlgebra` auto-derives
-- `Algebra TauRatQ (AlgebraicClosure ℚ)` from `Algebra TauRatQ ℚ`
-- (above). Similarly `IsScalarTower TauRatQ ℚ (AlgebraicClosure ℚ)`
-- is auto-derived. So we don't define them manually here — that
-- would create instance diamonds with Mathlib's auto-instances.

-- ============================================================
-- PART 2: Algebraicity transports up the tower
-- ============================================================

/-- **Every `q : ℚ` is algebraic over `TauRatQ`**. Since
    `ringEquivRat` is surjective (it's a `RingEquiv`), every
    `q : ℚ` equals `algebraMap TauRatQ ℚ (ringEquivRat.symm q)`,
    and `isAlgebraic_algebraMap` gives algebraicity of any
    image of the algebra map. -/
noncomputable instance instIsAlgebraicTauRatQRat :
    Algebra.IsAlgebraic TauRatQ ℚ where
  isAlgebraic q := by
    have h : q = algebraMap TauRatQ ℚ (TauRatQ.ringEquivRat.symm q) := by
      show q = TauRatQ.ringEquivRat.toRingHom (TauRatQ.ringEquivRat.symm q)
      exact (TauRatQ.ringEquivRat.apply_symm_apply q).symm
    rw [h]
    exact isAlgebraic_algebraMap _

/-- **Every element of `AlgebraicClosure ℚ` is algebraic over
    `TauRatQ`**. By transitivity (`IsAlgebraic.trans`):
    `Algebra.IsAlgebraic TauRatQ ℚ` (just shipped) +
    `Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ)` (Mathlib auto).
    Requires the `IsScalarTower` set up above. -/
noncomputable instance instIsAlgebraicTauRatQAlgebraicClosureQ :
    Algebra.IsAlgebraic TauRatQ (AlgebraicClosure ℚ) :=
  Algebra.IsAlgebraic.trans TauRatQ ℚ (AlgebraicClosure ℚ)

-- ============================================================
-- PART 3: IsAlgClosure synthesis + the AlgEquiv
-- ============================================================

/-- **`AlgebraicClosure ℚ` is an algebraic closure of `TauRatQ`**,
    with the algebra-tower structure set up above. Combines
    `IsAlgClosed` (Mathlib auto) + `Algebra.IsAlgebraic TauRatQ`
    (just shipped). -/
noncomputable instance instIsAlgClosureTauRatQAlgebraicClosureQ :
    IsAlgClosure TauRatQ (AlgebraicClosure ℚ) where
  isAlgClosed := inferInstance
  isAlgebraic := inferInstance

/-- **B2.alg.W5 — The canonical bridge**:
    `TauAlgComplex ≃ₐ[TauRatQ] AlgebraicClosure ℚ`.

    Constructed via Mathlib's `IsAlgClosure.equiv`: any two
    algebraic closures of the same base ring `TauRatQ` are
    AlgEquiv via `IsAlgClosed.lift` in both directions.

    This is the **dossier Part 7.2 verification handle** for
    `TauAlgComplex`: the τ-native ℚ̄ is provably isomorphic to
    Mathlib's canonical `AlgebraicClosure ℚ`, cross-validating
    the canonical anchoring. -/
noncomputable def tauAlgComplexEquivAlgClosureQ :
    TauAlgComplex ≃ₐ[TauRatQ] AlgebraicClosure ℚ :=
  IsAlgClosure.equiv TauRatQ TauAlgComplex (AlgebraicClosure ℚ)

end Tau.Boundary
