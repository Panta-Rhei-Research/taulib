import TauLib.BookI.Boundary.Bridge.TauRatRealAlgebraTower
import Mathlib.FieldTheory.AlgebraicClosure

/-!
# TauLib.BookI.Boundary.Bridge.TauAlgReal

**Workstream B2.alg / W2 — `TauAlgReal`: the τ-native real
algebraic numbers**.

Ships **`TauAlgReal`** as the algebraic closure of `TauRatQ`
inside `TauRealQ` — the τ-native real algebraic numbers. By
Mathlib's canonical `algebraicClosure F E : IntermediateField F E`
construction, this gives the largest subfield of `TauRealQ`
algebraic over `TauRatQ`.

## Mathematical content

For any field tower `F → E`, Mathlib's
`algebraicClosure F E : IntermediateField F E` is the
intermediate field consisting of all `E`-elements algebraic over
`F`. Applied to `F := TauRatQ`, `E := TauRealQ` (with the algebra
tower from W1), this yields:

- `TauAlgReal : IntermediateField TauRatQ TauRealQ`
- Inherited `Field TauAlgReal` (from `IntermediateField` over a
  field)
- `mem_tauAlgReal {x : TauRealQ} : x ∈ TauAlgReal ↔ IsAlgebraic
  TauRatQ x` (the characterization)

`TauAlgReal` is **constructively cleaner than full TauRealQ**: it
sits strictly between `TauRatQ` and `TauRealQ`, and its elements
are countably specifiable (each algebraic real is determined by
a polynomial over `TauRatQ` plus a root specification).

## What this unlocks (vs. blocks)

**Available immediately**:
- `Field TauAlgReal`
- `Algebra TauRatQ TauAlgReal` (the canonical embedding)
- `Algebra.IsAlgebraic TauRatQ TauAlgReal`

**Queued (via W3)**:
- `LinearOrderedField TauAlgReal` — algebraic reals are
  classically real-closed (hence ordered), but the τ-native
  derivation requires either bridging to Mathlib's
  `algebraicClosure ℚ ℝ` (which IS ordered) OR proving
  decidability of comparison directly via Sturm-sequence
  machinery. Queued as W3b.

## Substrate dependencies

- `TauRatRealAlgebraTower.lean` (W1):
  `Algebra TauRatQ TauRealQ` — the foundational algebra-tower
  instance
- Mathlib: `algebraicClosure F E : IntermediateField F E`
  (`Mathlib/FieldTheory/AlgebraicClosure.lean`)
- All inherited `Field`, `Algebra`, `IsAlgebraic` from the
  Mathlib construction

## Atlas cross-references

- `atlas/insights/2026-04-29-constructive-real-cardinality-boundary.md`
  (algebraic reals are countable, sidestepping the Markov wall)
- `atlas/insights/2026-05-04-workstream-b1-completion-and-depth-zero-revelation.md`
  (workstream discipline conventions)

## Registry Cross-References

- [I.T-W41c-Field]              `Field TauRealQ` (substrate)
- [I.T-B2.alg.W1-AlgebraTower]  `Algebra TauRatQ TauRealQ`
                                 (substrate)
- [I.T-B2.alg.W2-TauAlgReal]    `TauAlgReal` IntermediateField
                                 (this module)
-/

set_option autoImplicit false

namespace Tau.Boundary

open Tau.Denotation

-- ============================================================
-- B2.alg / W2: TauAlgReal (the τ-native real algebraic numbers)
-- ============================================================

/-- **`TauAlgReal` — the τ-native real algebraic numbers**.

    Defined as `algebraicClosure TauRatQ TauRealQ`, the
    intermediate field of `TauRealQ`-elements algebraic over
    `TauRatQ`. By the canonical Mathlib construction
    (`Mathlib/FieldTheory/AlgebraicClosure.lean`), this carries:
    - A `Field` instance (inherited from `IntermediateField` over
      a field)
    - The canonical `Algebra TauRatQ TauAlgReal` embedding
    - `Algebra.IsAlgebraic TauRatQ TauAlgReal` (every element is
      algebraic over `TauRatQ`)

    Sits strictly between `TauRatQ` and `TauRealQ` in the algebra
    tower. -/
noncomputable def TauAlgReal : IntermediateField TauRatQ TauRealQ :=
  algebraicClosure TauRatQ TauRealQ

-- ============================================================
-- Verification handles: the inherited typeclass instances
-- ============================================================

/-- **Verification handle 1**: `TauAlgReal` is a `Field`. -/
noncomputable example : Field TauAlgReal := inferInstance

/-- **Verification handle 2**: `TauAlgReal` carries the canonical
    `Algebra TauRatQ TauAlgReal` embedding. -/
noncomputable example : Algebra TauRatQ TauAlgReal := inferInstance

/-- **Verification handle 3**: every element of `TauAlgReal` is
    algebraic over `TauRatQ` — the **defining property of the
    real algebraic numbers**. -/
example : Algebra.IsAlgebraic TauRatQ TauAlgReal := by
  unfold TauAlgReal
  exact algebraicClosure.isAlgebraic TauRatQ TauRealQ

end Tau.Boundary
