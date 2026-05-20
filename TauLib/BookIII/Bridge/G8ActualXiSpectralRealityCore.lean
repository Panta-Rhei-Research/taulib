import TauLib.BookIII.Bridge.G8ActualXiOrthodoxCore

/-!
# TauLib.BookIII.Bridge.G8ActualXiSpectralRealityCore

Low-level centered-quadratic algebra for Lane A.

This module closes the purely algebraic readout step:

```text
Im (s * (1 - s) - 1/4) = Im(s) * (1 - 2 * Re(s)).
```

It deliberately leaves the two real spectral inputs explicit: reality of the
centered spectral parameter and nonzero height.  Those are the next
mathematical gates and are not constructed here.
-/

set_option autoImplicit false

noncomputable section

namespace Tau.BookIII.Bridge

-- ============================================================
-- CENTERED QUADRATIC READOUT
-- ============================================================

/-- The first-edition central quadratic parameter attached to an actual
    orthodox `xi` carrier. -/
def orthodoxXiCarrierCenteredQuadratic
    (z : OrthodoxXiZeroCarrier) : ℂ :=
  z.toZero.point * (1 - z.toZero.point) - (1 / 4 : ℂ)

/-- The localization-bearing imaginary readout of the central quadratic. -/
def orthodoxXiCarrierCenteredQuadraticImagReadout
    (z : OrthodoxXiZeroCarrier) : ℝ :=
  z.toZero.point.im * (1 - 2 * z.toZero.point.re)

/-- Pure complex algebra for the centered quadratic readout. -/
theorem orthodoxXiCarrierCenteredQuadratic_im
    (z : OrthodoxXiZeroCarrier) :
    (orthodoxXiCarrierCenteredQuadratic z).im =
      orthodoxXiCarrierCenteredQuadraticImagReadout z := by
  unfold orthodoxXiCarrierCenteredQuadratic
    orthodoxXiCarrierCenteredQuadraticImagReadout
  simp [Complex.mul_im]
  ring

-- ============================================================
-- SPECTRAL INPUTS
-- ============================================================

/-- The two genuine spectral inputs needed by Lane A.

The algebraic imaginary-part readout is theorem-backed above, so this package
keeps only the real mathematical obligations: reality of the centered spectral
parameter and nonzero height. -/
structure G8ActualXiSpectralRealityInputs where
  spectralParameterReal :
    ∀ z : OrthodoxXiZeroCarrier,
      (orthodoxXiCarrierCenteredQuadratic z).im = 0
  nontrivialHeight :
    ∀ z : OrthodoxXiZeroCarrier,
      z.toZero.point.im ≠ 0

/-- A zero-height carrier refutes the nonzero-height spectral input. -/
structure G8ActualXiZeroHeightFalsifier where
  z : OrthodoxXiZeroCarrier
  zeroHeight : z.toZero.point.im = 0

/-- A non-real centered quadratic carrier refutes the spectral-parameter
    reality input. -/
structure G8ActualXiCenteredQuadraticNonrealFalsifier where
  z : OrthodoxXiZeroCarrier
  nonreal :
    (orthodoxXiCarrierCenteredQuadratic z).im ≠ 0

/-- A mismatch in the centered-quadratic imaginary readout refutes the
    theorem-backed algebraic identity. -/
structure G8ActualXiCenteredQuadraticReadoutMismatchFalsifier where
  z : OrthodoxXiZeroCarrier
  mismatch :
    (orthodoxXiCarrierCenteredQuadratic z).im ≠
      orthodoxXiCarrierCenteredQuadraticImagReadout z

/-- Zero height refutes spectral-reality inputs. -/
theorem G8ActualXiZeroHeightFalsifier.refutesInputs
    (w : G8ActualXiZeroHeightFalsifier)
    (inputs : G8ActualXiSpectralRealityInputs) :
    False :=
  inputs.nontrivialHeight w.z w.zeroHeight

/-- Non-real centered quadratic parameter refutes spectral-reality inputs. -/
theorem G8ActualXiCenteredQuadraticNonrealFalsifier.refutesInputs
    (w : G8ActualXiCenteredQuadraticNonrealFalsifier)
    (inputs : G8ActualXiSpectralRealityInputs) :
    False :=
  w.nonreal (inputs.spectralParameterReal w.z)

/-- The readout-mismatch falsifier is impossible by the algebraic identity. -/
theorem G8ActualXiCenteredQuadraticReadoutMismatchFalsifier.refutes
    (w : G8ActualXiCenteredQuadraticReadoutMismatchFalsifier) :
    False :=
  w.mismatch (orthodoxXiCarrierCenteredQuadratic_im w.z)

end Tau.BookIII.Bridge
