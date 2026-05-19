import TauLib.BookIII.Bridge.G8FinalRHSpine

/-!
# TauLib.BookIII.Bridge.G8FinalRHSpineDischarge

Minimal discharge surface for the final G8f RH spine.

The existing `G8FinalRHSpine` is the checked handoff into Mathlib's
`RiemannHypothesis` target.  This module factors its remaining obligations into
the smallest current package:

* a transfer/chart context;
* G3 and G4 receiving-side chart readouts;
* theorem-backed actual centered-shadow address correctness;
* a still-open tau-purity target.

Full zero-divisor transfer remains a stronger downstream route.  This module
uses it only as an optional compatibility source for the G3/G4 readouts.
-/

set_option autoImplicit false

noncomputable section

namespace Tau.BookIII.Bridge

open Tau.BookIII.Spectral

-- ============================================================
-- MINIMAL TRANSFER / CHART READOUT
-- ============================================================

/-- Minimal chart-readout bundle needed by the final RH spine.

This deliberately records only the G3 and G4 readouts consumed by the current
one-sided actual-`xi` corridor. -/
structure G8FinalRHTransferChartReadout
    (transfer : G8dZeroDivisorTransferContext) where
  g3ZetaChartReadout :
    transfer.completion.chart.g3ZetaBridge
  g4CompletedXiReadout :
    transfer.completion.chart.g4AnalyticContinuation

/-- Full G8d admissibility can supply the minimal final-spine readout, but the
    readout itself is the smaller live dependency. -/
def G8FinalRHTransferChartReadout.from_g8dAdmissible
    (transfer : G8dZeroDivisorTransferContext)
    (h : G8dZeroDivisorTransferAdmissible transfer) :
    G8FinalRHTransferChartReadout transfer where
  g3ZetaChartReadout :=
    g8d_transfer_requires_g3ZetaBridge transfer h
  g4CompletedXiReadout :=
    g8d_transfer_requires_g4AnalyticContinuation transfer h

/-- The canonical-boundary thin actual `xi` source selected by a minimal
    readout. -/
def G8FinalRHTransferChartReadout.thinSource
    {transfer : G8dZeroDivisorTransferContext}
    (readout : G8FinalRHTransferChartReadout transfer) :
    G8ActualXiZetaThinSourceContext :=
  g8ActualXiZetaCanonicalBoundaryThinSource
    transfer.completion.chart
    readout.g3ZetaChartReadout
    readout.g4CompletedXiReadout

/-- The full actual `xi` source selected by a minimal readout and the same
    transfer context. -/
def G8FinalRHTransferChartReadout.source
    {transfer : G8dZeroDivisorTransferContext}
    (readout : G8FinalRHTransferChartReadout transfer) :
    G8ActualXiZetaSourceContext :=
  g8ActualXiZetaThin_to_fullSource
    readout.thinSource transfer rfl

/-- The theorem-backed explicit centered-shadow address correctness selected
    by a minimal readout. -/
def G8FinalRHTransferChartReadout.addressCorrect
    {transfer : G8dZeroDivisorTransferContext}
    (readout : G8FinalRHTransferChartReadout transfer) :
    G8ActualXiZetaShadowAddressCorrectness readout.thinSource :=
  g8ActualXiZetaExplicitShadowAddressCorrectness readout.thinSource

/-- The tau-purity target left open by the minimal readout. -/
def G8FinalRHTransferChartReadout.tauPurityTarget
    {transfer : G8dZeroDivisorTransferContext}
    (readout : G8FinalRHTransferChartReadout transfer) : Prop :=
  G8eTauPurityExcludesOffCritical
    (g8ActualXiZeta_base readout.source)

-- ============================================================
-- EXISTING FINAL SPINE CONSTRUCTOR
-- ============================================================

/-- Build the existing final spine from the minimal readout surface.

The address-correctness package is kept explicit so callers may use the
canonical theorem-backed package or a stricter future package with the same
target type. -/
def G8FinalRHSpine.fromReadout
    (transfer : G8dZeroDivisorTransferContext)
    (readout : G8FinalRHTransferChartReadout transfer)
    (addressCorrect :
      G8ActualXiZetaShadowAddressCorrectness readout.thinSource)
    (tauPurity : readout.tauPurityTarget) :
    G8FinalRHSpine where
  transfer := transfer
  g3ZetaChartReadout := readout.g3ZetaChartReadout
  g4CompletedXiReadout := readout.g4CompletedXiReadout
  addressCorrect := addressCorrect
  tauPurity := tauPurity

/-- Build the existing final spine using the explicit centered-shadow address
    correctness package. -/
def G8FinalRHSpine.fromReadoutWithExplicitAddress
    (transfer : G8dZeroDivisorTransferContext)
    (readout : G8FinalRHTransferChartReadout transfer)
    (tauPurity : readout.tauPurityTarget) :
    G8FinalRHSpine :=
  G8FinalRHSpine.fromReadout
    transfer readout readout.addressCorrect tauPurity

-- ============================================================
-- ALMOST-FINAL SPINE
-- ============================================================

/-- The final RH spine with every current field discharged except tau purity.

This is the next proof-engineering gauge: a term of this structure fixes the
transfer/chart readout and actual address-correctness path, leaving only the
tau-purity target exposed. -/
structure G8AlmostFinalRHSpine where
  transfer : G8dZeroDivisorTransferContext
  readout : G8FinalRHTransferChartReadout transfer
  addressCorrect :
    G8ActualXiZetaShadowAddressCorrectness readout.thinSource :=
      readout.addressCorrect

/-- Build the almost-final spine with the explicit theorem-backed address
    correctness package. -/
def G8AlmostFinalRHSpine.fromReadout
    (transfer : G8dZeroDivisorTransferContext)
    (readout : G8FinalRHTransferChartReadout transfer) :
    G8AlmostFinalRHSpine where
  transfer := transfer
  readout := readout
  addressCorrect := readout.addressCorrect

/-- The canonical-boundary thin source selected by an almost-final spine. -/
def G8AlmostFinalRHSpine.thinSource
    (almost : G8AlmostFinalRHSpine) :
    G8ActualXiZetaThinSourceContext :=
  almost.readout.thinSource

/-- The full actual `xi` source selected by an almost-final spine. -/
def G8AlmostFinalRHSpine.source
    (almost : G8AlmostFinalRHSpine) :
    G8ActualXiZetaSourceContext :=
  almost.readout.source

/-- The address-resolved source selected by an almost-final spine. -/
def G8AlmostFinalRHSpine.resolvedSource
    (almost : G8AlmostFinalRHSpine) :
    G8ActualXiZetaThinBoundaryAddressResolvedPreimageSource
      almost.thinSource :=
  g8ActualXiZetaCanonicalBoundaryCorrectAddressResolvedSource
    almost.addressCorrect

/-- The almost-final spine exposes the G3 readout. -/
theorem G8AlmostFinalRHSpine.requires_g3ZetaBridge
    (almost : G8AlmostFinalRHSpine) :
    almost.transfer.completion.chart.g3ZetaBridge :=
  almost.readout.g3ZetaChartReadout

/-- The almost-final spine exposes the G4 readout. -/
theorem G8AlmostFinalRHSpine.requires_g4AnalyticContinuation
    (almost : G8AlmostFinalRHSpine) :
    almost.transfer.completion.chart.g4AnalyticContinuation :=
  almost.readout.g4CompletedXiReadout

/-- The almost-final spine exposes theorem-backed actual address correctness. -/
def G8AlmostFinalRHSpine.address_correctness
    (almost : G8AlmostFinalRHSpine) :
    G8ActualXiZetaShadowAddressCorrectness almost.thinSource :=
  almost.addressCorrect

/-- The almost-final spine supplies pointwise tau-imbalance preimages for
    actual off-axis `xi` shadows. -/
theorem G8AlmostFinalRHSpine.pointwisePreimages
    (almost : G8AlmostFinalRHSpine) :
    G8ActualXiZetaThinPointwiseTauImbalancePreimagesExist
      almost.thinSource :=
  almost.addressCorrect.to_pointwisePreimages
    (g8ActualXiZetaCanonicalBoundaryWitnessAdapter
      almost.addressCorrect.toAddressMap)

/-- The almost-final spine assembles the actual `xi`/`zeta` corridor. -/
def G8AlmostFinalRHSpine.corridor
    (almost : G8AlmostFinalRHSpine) :
    G8ActualXiZetaCorridor almost.source :=
  almost.resolvedSource.to_corridor almost.transfer rfl

/-- The only remaining target exposed by the almost-final spine. -/
def G8AlmostFinalRHSpine.tauPurityTarget
    (almost : G8AlmostFinalRHSpine) : Prop :=
  G8eTauPurityExcludesOffCritical
    (g8ActualXiZeta_base almost.source)

/-- Supplying the tau-purity target upgrades an almost-final spine to the
    existing final spine. -/
def G8AlmostFinalRHSpine.toFinalRHSpine
    (almost : G8AlmostFinalRHSpine)
    (tauPurity : almost.tauPurityTarget) :
    G8FinalRHSpine :=
  G8FinalRHSpine.fromReadout
    almost.transfer
    almost.readout
    almost.addressCorrect
    tauPurity

/-- Once tau purity is supplied, the almost-final spine yields Mathlib's RH
    target through the existing final handoff. -/
theorem G8AlmostFinalRHSpine.mathlibRiemannHypothesis
    (almost : G8AlmostFinalRHSpine)
    (tauPurity : almost.tauPurityTarget) :
    RiemannHypothesis :=
  (almost.toFinalRHSpine tauPurity).mathlibRiemannHypothesis

end Tau.BookIII.Bridge
