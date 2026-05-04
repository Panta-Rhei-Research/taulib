import TauLib.BookI.Boundary.Bridge.TauAlgReal
import TauLib.BookI.Boundary.Bridge.TauAlgComplexBridge

/-!
# TauLib.BookI.Boundary.Bridge.TauAlgRealEmbedding

**Workstream B2.alg / W3 (soft form) — `TauAlgReal` embedding into
Mathlib's canonical algebraic closure of ℚ**.

Provides the **partial canonical-anchoring verification handle** for
`TauAlgReal` (W2): a τ-native algebra embedding

```lean
TauAlgReal →ₐ[TauRatQ] AlgebraicClosure ℚ
```

constructed via `IsAlgClosed.lift` (embedding into the τ-native
algebraic closure `TauAlgComplex`) composed with the W5 bridge
(`TauAlgComplex ≃ₐ[TauRatQ] AlgebraicClosure ℚ`).

## Soft W3 vs. full W3

The originally-spec'd **W3 full bridge**

```
TauAlgReal ≃ₐ[TauRatQ] algebraicClosure ℚ ℝ
```

requires the missing substrate `TauRealQ →+* ℝ` (the τ-Cauchy
quotient bridge to Mathlib's ℝ via the Cauchy completion universal
property). That's a substantive separate workstream (~100-300 LOC,
involving CauSeq.Completion universality).

This module ships the **available weakening**: an embedding (an
`AlgHom`, not an `≃ₐ`) of `TauAlgReal` into Mathlib's canonical
algebraic closure of ℚ. The image lands in some real-closed
subfield of `AlgebraicClosure ℚ` — abstractly the same as
`algebraicClosure ℚ ℝ`, but the explicit identification awaits the
TauRealQ →+* ℝ bridge.

## Construction

```
TauAlgReal --[IsAlgClosed.lift]--> TauAlgComplex --[W5]--> AlgebraicClosure ℚ
```

Both arrows are τ-native (no Mathlib ℝ involved):
- `IsAlgClosed.lift` works because `TauAlgReal` is algebraic over
  `TauRatQ` (W2) and `TauAlgComplex` is algebraically closed (W4)
- The W5 bridge `tauAlgComplexEquivAlgClosureQ` is a bijective
  AlgEquiv, used here as an AlgHom via `.toAlgHom`

## Substrate dependencies (all shipped)

- W2 (PR #142): `TauAlgReal` IntermediateField + `Algebra
  TauRatQ TauAlgReal` + `Algebra.IsAlgebraic TauRatQ TauAlgReal`
- W4 (PR #139): `TauAlgComplex` + `IsAlgClosed`
- W5 (PR #144): `tauAlgComplexEquivAlgClosureQ : TauAlgComplex
  ≃ₐ[TauRatQ] AlgebraicClosure ℚ`
- Mathlib: `IsAlgClosed.lift`, `AlgEquiv.toAlgHom`, `AlgHom.comp`

## What's queued (full W3 + W3b)

- **W3 (full)**: `TauAlgReal ≃ₐ[TauRatQ] algebraicClosure ℚ ℝ` —
  requires `TauRealQ →+* ℝ` Cauchy bridge (separate substantive
  sub-PR)
- **W3b**: `LinearOrderedField TauAlgReal` — requires either
  Sturm-sequence machinery (substantial) or transport via the full
  W3 bridge (which itself is queued)

## Atlas cross-references

- `atlas/insights/2026-04-29-constructive-real-cardinality-boundary.md`
- `atlas/insights/2026-05-04-workstream-b1-completion-and-depth-zero-revelation.md`

## Registry Cross-References

- [I.T-B2.alg.W2-TauAlgReal]      `TauAlgReal` (substrate)
- [I.T-B2.alg.W4-TauAlgComplex]   `TauAlgComplex` (substrate)
- [I.T-B2.alg.W5-CanonicalBridge] W5 bridge (substrate)
- [I.T-B2.alg.W3-soft-Embedding]  `tauAlgRealEmbedAlgClosureQ`
                                    (this module — soft W3)
-/

set_option autoImplicit false

namespace Tau.Boundary

open Tau.Denotation

-- ============================================================
-- B2.alg / W3 (soft): TauAlgReal embedding via TauAlgComplex
-- ============================================================

/-- **`Algebra.IsAlgebraic TauRatQ TauAlgReal` instance** —
    explicitly registered so that downstream `IsAlgClosed.lift`
    can synthesize it. The underlying fact comes from Mathlib's
    `algebraicClosure.isAlgebraic`, but instance synthesis
    doesn't unfold `TauAlgReal` automatically — so we provide an
    explicit hint. -/
noncomputable instance instIsAlgebraicTauRatQTauAlgReal :
    Algebra.IsAlgebraic TauRatQ TauAlgReal := by
  unfold TauAlgReal
  exact algebraicClosure.isAlgebraic TauRatQ TauRealQ

/-- **τ-native embedding of real algebraics into complex
    algebraics**: `TauAlgReal →ₐ[TauRatQ] TauAlgComplex` via
    Mathlib's `IsAlgClosed.lift`.

    Exists because:
    - `TauAlgReal` is algebraic over `TauRatQ` (W2 instance)
    - `TauAlgComplex` is algebraically closed (W4 instance)
    - Both are `TauRatQ`-algebras

    The embedding is "a (random) homomorphism" per Mathlib's
    `lift` doc — there's typically more than one (Galois action),
    but `IsAlgClosed.lift` provides a canonical `Classical.choice`. -/
noncomputable def tauAlgRealEmbedTauAlgComplex :
    TauAlgReal →ₐ[TauRatQ] TauAlgComplex :=
  IsAlgClosed.lift

/-- **W3 (soft) — `TauAlgReal` embeds into `AlgebraicClosure ℚ`**.

    Composition:
    `TauAlgReal --[lift]--> TauAlgComplex --[W5 bridge]--> AlgebraicClosure ℚ`

    This realizes the **partial canonical-anchoring verification
    handle** for TauAlgReal: every τ-native real algebraic number
    is identified with a Mathlib-canonical algebraic number (in ℚ̄).

    The full bridge `TauAlgReal ≃ₐ[TauRatQ] algebraicClosure ℚ ℝ`
    requires the `TauRealQ →+* ℝ` Cauchy substrate, which is
    queued. -/
noncomputable def tauAlgRealEmbedAlgClosureQ :
    TauAlgReal →ₐ[TauRatQ] AlgebraicClosure ℚ :=
  tauAlgComplexEquivAlgClosureQ.toAlgHom.comp tauAlgRealEmbedTauAlgComplex

end Tau.Boundary
