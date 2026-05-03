import TauLib.BookI.Boundary.Bridge.TauRatQuotient
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.Algebraic.Defs

/-!
# TauLib.BookI.Boundary.Bridge.TauAlgComplex

**Workstream B2.alg / W4 — `TauAlgComplex`: the τ-native
algebraic complex numbers (ℚ̄)**.

Ships **`TauAlgComplex`** as the canonical algebraic closure of
`TauRatQ` (the τ-rational field, ≅ ℚ via Wave 40), realising the
τ-native ℚ̄ — the algebraic closure of ℚ in ℂ.

## Mathematical content

By Mathlib's canonical `AlgebraicClosure k` construction (for any
field `k`):
- `AlgebraicClosure k` is a Field
- `Algebra k (AlgebraicClosure k)` (the canonical algebra
  embedding)
- `Algebra.IsAlgebraic k (AlgebraicClosure k)` (every element
  is algebraic over k)
- **`IsAlgClosed (AlgebraicClosure k)`** — the killer feature:
  every nonzero polynomial over `AlgebraicClosure k` has a root.

Applied to `k := TauRatQ`, this yields **`TauAlgComplex :=
AlgebraicClosure TauRatQ`**, the τ-native algebraic closure of
the τ-rational field. By the existing `TauRatQ ≃+* ℚ` (Wave 40),
this is canonically isomorphic to Mathlib's `AlgebraicClosure ℚ`
(the bridge is queued as W5 follow-up).

## Why this works (and Cauchy completion didn't)

Per `atlas/insights/2026-04-29-constructive-real-cardinality-boundary.md`:
- **Cauchy completion** (the Wave 41 path to ℝ) is constructively
  blocked at `LinearOrderedField` (Markov-principle wall).
- **Algebraic completion** (this module's path to ℚ̄) is
  constructively tractable: ℚ̄ = ⋃_n {monic irreducibles of
  degree ≤ n over ℚ}, a countable union of finite root sets.

`TauAlgComplex` thus realizes the **largest constructively-clean
field extension of `TauRatQ`** — the algebraic closure tier,
strictly between ℚ and ℂ.

## Substrate dependencies

- `TauRatQuotient.lean` (Wave 40): `Field TauRatQ`,
  `TauRatQ.ringEquivRat : TauRatQ ≃+* ℚ`
- Mathlib: `AlgebraicClosure k` (canonical construction with
  Field, Algebra, IsAlgebraic, IsAlgClosed instances)

## Atlas cross-references

- `atlas/insights/2026-04-29-constructive-real-cardinality-boundary.md`
  (the cardinality-boundary insight motivating the algebraic-tier
  approach)
- `atlas/insights/2026-05-04-workstream-b1-completion-and-depth-zero-revelation.md`
  (workstream discipline conventions)

## Registry Cross-References

- [I.T-W40-Field]               `Field TauRatQ` (substrate)
- [I.T-W40-RingEquiv]           `TauRatQ ≃+* ℚ` (substrate)
- [I.T-B2.alg.W4-TauAlgComplex] `TauAlgComplex` and its
                                 `Field` + `IsAlgClosed`
                                 (this module)

## What's queued (post-W4)

- **W5**: bridge `TauAlgComplex ≃ₐ[TauRatQ] AlgebraicClosure ℚ`
  for canonical-anchoring verification handle
- **W1+W2+W3**: `Algebra TauRatQ TauRealQ` algebra tower +
  `TauAlgReal` (real algebraic numbers as a subfield of
  `TauRealQ`) + bridge to Mathlib's `algebraicClosure ℚ ℝ`.
  **BLOCKED** on pre-existing namespace collision between
  `TauRatQuotient.lean` and `TauRatInv.lean` (both define
  `Tau.Boundary.toRat_inv`); requires a focused tech-debt
  rename PR before W1 can land.
-/

set_option autoImplicit false

namespace Tau.Boundary

open Tau.Denotation

-- ============================================================
-- B2.alg / W4: TauAlgComplex (the τ-native ℚ̄)
-- ============================================================

/-- **`TauAlgComplex` — the τ-native algebraic complex numbers
    (ℚ̄)**.

    Defined as `AlgebraicClosure TauRatQ`, the canonical algebraic
    closure of the τ-rational field. By the canonical Mathlib
    construction, this carries:
    - A `Field` instance
    - An `Algebra TauRatQ TauAlgComplex` instance (the canonical
      embedding)
    - An `Algebra.IsAlgebraic TauRatQ TauAlgComplex` instance
      (every element is algebraic over `TauRatQ`)
    - An `IsAlgClosed` instance (every nonzero polynomial has a
      root)

    All four are inherited from Mathlib's `AlgebraicClosure k`
    construction (`Mathlib/FieldTheory/IsAlgClosed/AlgebraicClosure.lean`),
    instantiated at `k := TauRatQ`. -/
noncomputable abbrev TauAlgComplex : Type := AlgebraicClosure TauRatQ

-- ============================================================
-- Verification handles: the inherited typeclass instances
-- ============================================================

/-- **Verification handle 1**: `TauAlgComplex` is a `Field`. -/
noncomputable example : Field TauAlgComplex := inferInstance

/-- **Verification handle 2**: `TauAlgComplex` carries the
    canonical `Algebra TauRatQ TauAlgComplex` embedding. -/
noncomputable example : Algebra TauRatQ TauAlgComplex := inferInstance

/-- **Verification handle 3**: every element of `TauAlgComplex`
    is algebraic over `TauRatQ` (the algebraicity property
    that defines the closure). -/
example : Algebra.IsAlgebraic TauRatQ TauAlgComplex := inferInstance

/-- **Verification handle 4**: `TauAlgComplex` is algebraically
    closed — every nonzero polynomial over `TauAlgComplex` has a
    root. This is the **defining property of ℚ̄**. -/
example : IsAlgClosed TauAlgComplex := inferInstance

end Tau.Boundary
