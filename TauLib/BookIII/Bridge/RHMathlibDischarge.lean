import Mathlib.NumberTheory.LSeries.RiemannZeta
import TauLib.BookIII.Bridge.G8FinalLiveHinge

/-!
# TauLib.BookIII.Bridge.RHMathlibDischarge

Quarantined Mathlib-facing discharge surface for `RiemannHypothesis`.

This module is intentionally not imported by `TauLib.BookIII`.  It exists as a
dedicated audit target for the final handoff into Mathlib's
`RiemannHypothesis` statement.  The theorem below is conditional on the exact
accepted-realization proof package isolated by the G8 final spine reduction;
it does not manufacture that package.
-/

set_option autoImplicit false

noncomputable section

namespace Tau.BookIII.Bridge

/-- Quarantined final handoff from the explicit G8 accepted-realization proof
package to Mathlib's `RiemannHypothesis`.

The remaining mathematical work is precisely the construction of `pkg`, or
equivalently pointwise accepted centered-address coverage from the Book III
character/tower machinery. -/
theorem tau_mathlib_riemann_hypothesis
    {model : G8BookIIITowerAcceptedSpectralWitnessModel}
    (pkg : G8BookIIICharacterAcceptedRealizationProofPackage model) :
    RiemannHypothesis := by
  exact pkg.mathlibRiemannHypothesis

/-- Same quarantined handoff, phrased through the reduction module's pointwise
accepted centered-address coverage target. -/
theorem tau_mathlib_riemann_hypothesis_from_pointwise_coverage
    {model : G8BookIIITowerAcceptedSpectralWitnessModel}
    (coverage : G8BookIIIPointwiseAcceptedCenteredAddressCoverage model) :
    RiemannHypothesis := by
  exact
    tau_mathlib_riemann_hypothesis
      (G8BookIIICharacterAcceptedRealizationProofPackage.ofPointwiseTowerCoverage
        coverage)

/-- Same quarantined handoff, phrased through the final live-hinge package:
actual `xi` sigma-fixedness plus sigma-fixed accepted tower realization. -/
theorem tau_mathlib_riemann_hypothesis_from_final_live_hinge
    {model : G8BookIIITowerAcceptedSpectralWitnessModel}
    (hinge : G8FinalLiveHinge model) :
    RiemannHypothesis := by
  exact hinge.mathlibRiemannHypothesis

/-- Closed-package variant: the accepted tower model and its final live hinge
are carried by one object. -/
theorem tau_mathlib_riemann_hypothesis_from_closed_final_live_hinge
    (closed : G8ClosedFinalLiveHinge) :
    RiemannHypothesis := by
  exact closed.mathlibRiemannHypothesis

#print axioms tau_mathlib_riemann_hypothesis
#print axioms tau_mathlib_riemann_hypothesis_from_pointwise_coverage
#print axioms tau_mathlib_riemann_hypothesis_from_final_live_hinge
#print axioms tau_mathlib_riemann_hypothesis_from_closed_final_live_hinge

end Tau.BookIII.Bridge
