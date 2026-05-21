import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.Linearity
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.Analysis.Complex.AbelLimit
import Mathlib.Analysis.Complex.SummableUniformlyOn
import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.MeanValue

/-!
# TauLib.BookIII.Bridge.G8ActualXiOrthodoxCore

Low-level orthodox `xi` carrier core for the G8f/Lane-A corridor.

This is the sole bridge-zone module in the Lane-A core split that directly
imports Mathlib's orthodox zeta and classical-analysis support.  It defines
only the orthodox completed-`xi` wrapper, its zero carrier, and the
carrier-level off-critical predicate.  Centered shadows, boundary addresses,
spectral-reality forcing, and final RH handoffs live in higher modules.
-/

set_option autoImplicit false

noncomputable section

namespace Tau.BookIII.Bridge

open Complex

-- ============================================================
-- ORTHODOX XI CORE
-- ============================================================

/-- Orthodox completed-`xi` wrapper built from Mathlib's entire
    `completedRiemannZeta₀`.

Mathlib's `completedRiemannZeta` is the completed zeta function with poles at
`0` and `1`; `completedRiemannZeta₀` is the pole-removed entire object.  The
formula below is the standard entire normalization
`xi(s) = 1/2 * (s * (s - 1) * Lambda₀(s) + 1)`. -/
def orthodoxXi (s : ℂ) : ℂ :=
  (1 / 2 : ℂ) *
    (s * (s - 1) * completedRiemannZeta₀ s + 1)

/-- The orthodox `xi` functional-equation shadow inherited from Mathlib's
    completed-zeta functional equation. -/
theorem orthodoxXi_one_sub (s : ℂ) :
    orthodoxXi (1 - s) = orthodoxXi s := by
  unfold orthodoxXi
  rw [completedRiemannZeta₀_one_sub]
  ring

/-- Receiving-side zero object for the orthodox `xi` wrapper.

This is an orthodox object.  It is not a tau zero and carries no tau preimage
claim. -/
structure OrthodoxXiZero where
  point : ℂ
  isZero : orthodoxXi point = 0

/-- The orthodox zero is off the critical line when its real coordinate is not
    `1/2`. -/
def OrthodoxXiOffCritical (z : OrthodoxXiZero) : Prop :=
  z.point.re ≠ (1 / 2 : ℝ)

-- ============================================================
-- UNIVERSE-LIFTED CORRIDOR CARRIER
-- ============================================================

/-- Universe-lifted carrier for existing G8 bridge interfaces.

The mathematical object remains `OrthodoxXiZero`; this carrier only adapts it
to the current `OffCriticalZeroPullbackContext`, whose zero carrier is
universe-polymorphic at `Type 2`. -/
abbrev OrthodoxXiZeroCarrier : Type 2 :=
  ULift.{2, 0} OrthodoxXiZero

/-- Lift an orthodox `xi` zero into the bridge-interface carrier. -/
def OrthodoxXiZero.toCarrier (z : OrthodoxXiZero) :
    OrthodoxXiZeroCarrier :=
  ULift.up z

/-- Project a bridge-interface carrier back to the orthodox `xi` zero record. -/
def OrthodoxXiZeroCarrier.toZero (z : OrthodoxXiZeroCarrier) :
    OrthodoxXiZero :=
  z.down

/-- Off-criticality for the universe-lifted orthodox `xi` carrier. -/
def OrthodoxXiCarrierOffCritical (z : OrthodoxXiZeroCarrier) : Prop :=
  OrthodoxXiOffCritical z.toZero

end Tau.BookIII.Bridge
