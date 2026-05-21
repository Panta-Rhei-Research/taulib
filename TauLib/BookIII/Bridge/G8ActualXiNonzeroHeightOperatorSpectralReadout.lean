import TauLib.BookIII.Bridge.G8ActualXiNonzeroHeightSpectralCore
import TauLib.BookIII.Bridge.LemniscateOperatorSpine

/-!
# TauLib.BookIII.Bridge.G8ActualXiNonzeroHeightOperatorSpectralReadout

Operator-facing source contract for the nonzero-height Lane-A spectral payload.

The module states the exact non-circular input needed from future Book III
operator work:

```text
actual nonzero-height xi carrier
  -> declared operator spectral value
  -> exact centered-quadratic alignment
  -> real-valuedness from an accepted self-adjoint readout
```

Finite self-adjoint and spectral-correspondence checks remain diagnostics.
They are not consumed as proofs of the global real-valued readout.
-/

set_option autoImplicit false

noncomputable section

namespace Tau.BookIII.Bridge

-- ============================================================
-- OPERATOR-SOURCE READOUT
-- ============================================================

/-- Diagnostic evidence attached to an operator readout source.

These fields are intentionally non-load-bearing: the proof of nonzero-height
spectral reality below consumes only exact centered-quadratic alignment and
exact real-valuedness. -/
structure G8ActualXiNonzeroHeightOperatorReadoutDiagnostics where
  finiteSelfAdjointDiagnostic : Prop := True
  finiteK5DiagonalDiagnostic : Prop := True
  finiteSpectralCorrespondenceDiagnostic : Prop := True
  status : SpineStatus := .conditional_interface

/-- Operator-facing readout contract for nonzero-height actual `xi` carriers.

`operatorReady` records the Book III operator obligations.  The load-bearing
fields are still the two exact readout facts: equality with the centered
quadratic value and real-valuedness of the declared spectral value. -/
structure G8ActualXiNonzeroHeightOperatorSpectralReadoutContext where
  operatorCtx : LemniscateOperatorContext
  operatorReady : LemniscateOperatorReady operatorCtx
  spectralValue : G8ActualXiNonzeroHeightCarrier → ℂ
  spectralValue_eq_centeredQuadratic :
    ∀ z : G8ActualXiNonzeroHeightCarrier,
      spectralValue z = orthodoxXiCarrierCenteredQuadratic z.1
  spectralValue_real :
    ∀ z : G8ActualXiNonzeroHeightCarrier,
      (spectralValue z).im = 0
  diagnostics : G8ActualXiNonzeroHeightOperatorReadoutDiagnostics := {}

/-- Exact operator readout alignment plus real-valuedness supplies the clean
    nonzero-height spectral payload. -/
theorem
    G8ActualXiNonzeroHeightOperatorSpectralReadoutContext.toSpectralParameterReal
    (ctx : G8ActualXiNonzeroHeightOperatorSpectralReadoutContext) :
    G8ActualXiNonzeroHeightSpectralParameterReal := by
  intro z
  rw [← ctx.spectralValue_eq_centeredQuadratic z]
  exact ctx.spectralValue_real z

/-- The operator readout context forces nonzero-height carriers onto the
    critical axis through the clean centered-quadratic core. -/
theorem
    G8ActualXiNonzeroHeightOperatorSpectralReadoutContext.carrierRe_eq_half
    (ctx : G8ActualXiNonzeroHeightOperatorSpectralReadoutContext)
    (z : G8ActualXiNonzeroHeightCarrier) :
    z.1.toZero.point.re = (1 / 2 : ℝ) :=
  g8NonzeroHeightSpectralParameterReal_forces_re_eq_half
    ctx.toSpectralParameterReal z

/-- The operator readout context excludes nonzero-height carrier
    off-criticality, without using any downstream RH-facing machinery. -/
theorem
    G8ActualXiNonzeroHeightOperatorSpectralReadoutContext.noOffCritical
    (ctx : G8ActualXiNonzeroHeightOperatorSpectralReadoutContext)
    (z : G8ActualXiNonzeroHeightCarrier) :
    ¬ OrthodoxXiCarrierOffCritical z.1 :=
  g8NonzeroHeightSpectralParameterReal_noOffCritical
    ctx.toSpectralParameterReal z

-- ============================================================
-- RED-TEAM FALSIFIERS
-- ============================================================

/-- A claim that the selected operator package is not ready refutes an
    operator readout context using that package. -/
structure G8ActualXiNonzeroHeightOperatorReadoutNotReady
    (ctx : G8ActualXiNonzeroHeightOperatorSpectralReadoutContext) where
  notReady : ¬ LemniscateOperatorReady ctx.operatorCtx

/-- Operator-readiness mismatch is fatal for the readout context. -/
theorem G8ActualXiNonzeroHeightOperatorReadoutNotReady.refutes
    {ctx : G8ActualXiNonzeroHeightOperatorSpectralReadoutContext}
    (w : G8ActualXiNonzeroHeightOperatorReadoutNotReady ctx) :
    False :=
  w.notReady ctx.operatorReady

/-- A mismatch between the operator spectral value and the centered quadratic
    value refutes the source context. -/
structure G8ActualXiNonzeroHeightOperatorSpectralValueMismatch
    (ctx : G8ActualXiNonzeroHeightOperatorSpectralReadoutContext) where
  z : G8ActualXiNonzeroHeightCarrier
  mismatch :
    ctx.spectralValue z ≠ orthodoxXiCarrierCenteredQuadratic z.1

/-- Operator spectral-value mismatch is fatal for the source context. -/
theorem G8ActualXiNonzeroHeightOperatorSpectralValueMismatch.refutes
    {ctx : G8ActualXiNonzeroHeightOperatorSpectralReadoutContext}
    (w : G8ActualXiNonzeroHeightOperatorSpectralValueMismatch ctx) :
    False :=
  w.mismatch (ctx.spectralValue_eq_centeredQuadratic w.z)

/-- A non-real declared operator spectral value refutes the source context. -/
structure G8ActualXiNonzeroHeightOperatorSpectralValueNonreal
    (ctx : G8ActualXiNonzeroHeightOperatorSpectralReadoutContext) where
  z : G8ActualXiNonzeroHeightCarrier
  nonreal : (ctx.spectralValue z).im ≠ 0

/-- Non-real operator spectral values are fatal for the source context. -/
theorem G8ActualXiNonzeroHeightOperatorSpectralValueNonreal.refutes
    {ctx : G8ActualXiNonzeroHeightOperatorSpectralReadoutContext}
    (w : G8ActualXiNonzeroHeightOperatorSpectralValueNonreal ctx) :
    False :=
  w.nonreal (ctx.spectralValue_real w.z)

/-- Finite self-adjoint diagnostics without exact real-valuedness do not
    instantiate the operator source theorem. -/
structure G8ActualXiNonzeroHeightOperatorDiagnosticOnly where
  z : G8ActualXiNonzeroHeightCarrier
  spectralValue : ℂ
  finiteSelfAdjointDiagnostic : Prop
  finiteK5DiagonalDiagnostic : Prop
  finiteSpectralCorrespondenceDiagnostic : Prop
  selfAdjointEvidence : finiteSelfAdjointDiagnostic
  k5Evidence : finiteK5DiagonalDiagnostic
  correspondenceEvidence : finiteSpectralCorrespondenceDiagnostic
  spectralValue_nonreal : spectralValue.im ≠ 0

/-- A diagnostic-only record with the same declared value as an operator
    context refutes that context through exact real-valuedness. -/
theorem G8ActualXiNonzeroHeightOperatorDiagnosticOnly.refutesContext
    (w : G8ActualXiNonzeroHeightOperatorDiagnosticOnly)
    (ctx : G8ActualXiNonzeroHeightOperatorSpectralReadoutContext)
    (hSame : ctx.spectralValue w.z = w.spectralValue) :
    False := by
  apply w.spectralValue_nonreal
  rw [← hSame]
  exact ctx.spectralValue_real w.z

end Tau.BookIII.Bridge
