import TauLib.BookIII.Bridge.G8ActualXiHeightSplitSpectralReality
import TauLib.BookIII.Bridge.G8ActualXiZeroHeightAxisGuardCore

/-!
# TauLib.BookIII.Bridge.G8ActualXiZeroHeightAxisGuard

Height-split assembly for the Lane-A zero-height guard.

The low-level real-axis nonvanishing corridor lives in
`G8ActualXiZeroHeightAxisGuardCore`.  This module is intentionally downstream:
it only connects the low-level discharge package to the height-split spectral
reality input object.
-/

set_option autoImplicit false

noncomputable section

namespace Tau.BookIII.Bridge

/-- The discharge package plus spectral-parameter reality supplies the
    existing height-split Lane-A inputs. -/
def G8ActualXiZeroHeightAxisGuardDischarge.toHeightSplitInputs
    (discharge : G8ActualXiZeroHeightAxisGuardDischarge)
    (spectralParameterReal :
      ∀ z : OrthodoxXiZeroCarrier,
        (orthodoxXiCarrierCenteredQuadratic z).im = 0) :
    G8ActualXiHeightSplitSpectralRealityInputs where
  spectralParameterReal := spectralParameterReal
  zeroHeightAxis := discharge.zeroHeightAxisGuard

/-- A zero-height off-critical carrier refutes the discharge package. -/
theorem G8ActualXiZeroHeightOffCriticalFalsifier.refutesZeroHeightDischarge
    (w : G8ActualXiZeroHeightOffCriticalFalsifier)
    (discharge : G8ActualXiZeroHeightAxisGuardDischarge) :
    False :=
  w.refutesZeroHeightAxis discharge.zeroHeightAxisGuard

end Tau.BookIII.Bridge
