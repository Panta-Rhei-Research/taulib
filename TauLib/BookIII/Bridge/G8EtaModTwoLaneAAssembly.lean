import TauLib.BookIII.Bridge.G8ActualXiZeroHeightAxisGuard
import TauLib.BookIII.Bridge.G8EtaModTwoExpZetaBoundaryDischarge

/-!
# TauLib.BookIII.Bridge.G8EtaModTwoLaneAAssembly

Downstream assembly adapters for the Lane-A eta corridor.

The eta/Abel modules are kept upstream-clean and import only the low-level
zero-height core.  This module restores the height-split and final-live-hinge
forwarders after the height-split layer is already in scope.
-/

set_option autoImplicit false

noncomputable section

namespace Tau.BookIII.Bridge

/-- With a supplied spectral-parameter reality theorem, the open-unit package
    feeds the existing height-split Lane-A input object. -/
def G8EtaModTwoOpenUnitContinuationData.toHeightSplitInputs
    (data : G8EtaModTwoOpenUnitContinuationData)
    (spectralParameterReal :
      ∀ z : OrthodoxXiZeroCarrier,
        (orthodoxXiCarrierCenteredQuadratic z).im = 0) :
    G8ActualXiHeightSplitSpectralRealityInputs :=
  data.zeroHeightDischarge.toHeightSplitInputs spectralParameterReal

/-- The continuation data plus spectral-parameter reality and accepted
    sigma-fixed realization forwards through the existing final live hinge. -/
def G8EtaModTwoOpenUnitContinuationData.toFinalLiveHinge
    {model : G8BookIIITowerAcceptedSpectralWitnessModel}
    (data : G8EtaModTwoOpenUnitContinuationData)
    (spectralParameterReal :
      ∀ z : OrthodoxXiZeroCarrier,
        (orthodoxXiCarrierCenteredQuadratic z).im = 0)
    (realization :
      G8BookIIIAcceptedTowerRealizationFromSigmaFixed model) :
    G8FinalLiveHinge model :=
  (data.toHeightSplitInputs spectralParameterReal).toFinalLiveHinge realization

/-- With spectral-parameter reality, closure data supplies the height-split
    Lane-A input object. -/
def G8EtaModTwoOpenUnitEtaClosureData.toHeightSplitInputs
    (data : G8EtaModTwoOpenUnitEtaClosureData)
    (spectralParameterReal :
      ∀ z : OrthodoxXiZeroCarrier,
        (orthodoxXiCarrierCenteredQuadratic z).im = 0) :
    G8ActualXiHeightSplitSpectralRealityInputs :=
  data.toContinuationData.toHeightSplitInputs spectralParameterReal

/-- With spectral-parameter reality, Abel boundary-value identification
    supplies the height-split Lane-A input object. -/
def G8ActualXiHeightSplitSpectralRealityInputs.ofEtaModTwoAbelBoundary
    (hBoundary : G8EtaModTwoLFunctionAbelBoundaryValueOnOpenUnit)
    (spectralParameterReal :
      ∀ z : OrthodoxXiZeroCarrier,
        (orthodoxXiCarrierCenteredQuadratic z).im = 0) :
    G8ActualXiHeightSplitSpectralRealityInputs :=
  (G8ActualXiZeroHeightAxisGuardDischarge.ofEtaModTwoAbelBoundary
    hBoundary).toHeightSplitInputs spectralParameterReal

/-- With spectral-parameter reality, the additive-character Abel boundary
    theorem supplies the height-split Lane-A input object. -/
def G8ActualXiHeightSplitSpectralRealityInputs.ofEtaModTwoExpZetaAbelBoundary
    (hBoundary : G8EtaModTwoExpZetaAbelBoundaryValueOnOpenUnit)
    (spectralParameterReal :
      ∀ z : OrthodoxXiZeroCarrier,
        (orthodoxXiCarrierCenteredQuadratic z).im = 0) :
    G8ActualXiHeightSplitSpectralRealityInputs :=
  (G8ActualXiZeroHeightAxisGuardDischarge.ofEtaModTwoExpZetaAbelBoundary
    hBoundary).toHeightSplitInputs spectralParameterReal

/-- With spectral-parameter reality, the pointwise ExpZeta/concrete-eta
    equality supplies the height-split Lane-A input object. -/
def G8ActualXiHeightSplitSpectralRealityInputs.ofEtaModTwoExpZetaConcreteEta
    (hConcrete : G8EtaModTwoExpZetaConcreteEtaOnOpenUnit)
    (spectralParameterReal :
      ∀ z : OrthodoxXiZeroCarrier,
        (orthodoxXiCarrierCenteredQuadratic z).im = 0) :
    G8ActualXiHeightSplitSpectralRealityInputs :=
  (G8ActualXiZeroHeightAxisGuardDischarge.ofEtaModTwoExpZetaConcreteEta
    hConcrete).toHeightSplitInputs spectralParameterReal

end Tau.BookIII.Bridge
