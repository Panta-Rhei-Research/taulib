# G8 Lane A Eta Open-Unit Closure Map

## What This Wave Closes

- The safe right-half-plane eta product remains theorem-backed by
  `G8EtaModTwoRightHalfPlaneProduct`.
- The product identity now analytically continues across the punctured plane:
  `g8EtaModTwoLFunctionProductIdentityOnPuncturedPlane`.
- Consequently the real open-unit product identity is theorem-backed:
  `g8EtaModTwoLFunction_openUnitProductIdentity`.
- `G8EtaModTwoHurwitzOpenUnitProduct` records the exact Hurwitz-zeta model of
  the mod-two `ZMod.LFunction`.
- The zero-average, zero-residue, and one-residue coefficient facts are
  theorem-backed selectors from the existing mod-two eta coefficient.
- The Hurwitz product evidence can now be built from just the real-valued zeta
  readout by `G8EtaModTwoHurwitzProductContinuationEvidence.ofZetaReal`.
- Abel identification now forces the real-valued zeta readout via
  `g8RiemannZetaRealOnOpenUnit_of_conditionalEtaAbelIdentification`, because
  the theorem-backed product identity writes zeta as a nonzero real multiple of
  the concrete eta value.
- Therefore `G8ActualXiZeroHeightAxisGuardDischarge.ofConditionalEtaAbelIdentification`
  discharges the zero-height guard from the Abel target alone.
- The concrete Abel side is now theorem-backed by
  `g8EtaModTwoAbelPowerSeries_tendsto_concreteEta`: the conditional eta value is
  the radial boundary value of the mod-two Abel power series.
- `g8EtaModTwoConditionalEtaAbelIdentificationOnOpenUnit_of_abelBoundary` shows
  that it is enough to prove the mod-two `ZMod.LFunction` has that same Abel
  boundary value.
- `G8EtaModTwoAbelBoundaryClosure` theorem-backs the coefficient bridge
  `g8EtaModTwoCoeff = -ZMod.stdAddChar` and hence
  `g8EtaModTwoLFunction_eq_neg_expZeta`.
- `G8ActualXiZeroHeightAxisGuardCore` now carries the low-level real-axis
  nonvanishing corridor, so eta/Abel modules no longer need to import the
  height-split or final-live-hinge layers.
- `G8EtaModTwoExpZetaBoundaryDischarge` reduces the remaining Abel boundary
  theorem to the pointwise equality between the concrete conditional eta value
  and `-HurwitzZeta.expZeta`.
- `G8EtaModTwoPairedSeriesBoundary` closes the finite regrouping step:
  `g8EtaModTwoConcretePairedPartial_tendsto_concreteEta` proves that the
  odd/even paired eta partial sums converge to the same concrete conditional
  eta value on `0 < x < 1`.
- The same module proves that a paired ExpZeta boundary theorem,
  `G8EtaModTwoPairedExpZetaBoundaryOnOpenUnit`, is exactly sufficient for the
  pointwise ExpZeta/concrete-eta equality and hence for the zero-height guard.
- `G8EtaModTwoPairedExpZetaBoundaryTheorem` closes the low-level bridge from
  concrete paired terms to the analytic paired series
  `g8EtaModTwoPairedEtaSeries`.
- The remaining positive-half-plane payload is packaged as
  `G8EtaModTwoPairedEtaSeriesEqNegExpZetaOnPositiveHalfPlane`, carrying paired
  summability on `0 < Re(s)` and equality of the paired series with
  `-HurwitzZeta.expZeta`.
- `G8EtaModTwoPairedStripEstimate` and `G8EtaModTwoPairedDerivativeMVT` close
  the MVT derivative majorant needed for paired eta convergence.
- `G8EtaModTwoPairedLocalUniformConvergence` upgrades that strip estimate to
  local-uniform convergence and pointwise summability on `0 < Re(s)`.
- `G8EtaModTwoPairedPositiveHalfPlaneClosure` closes the remaining eta payload:
  it proves safe-half-plane agreement with the mod-two `LSeries`, applies the
  analytic identity theorem across the positive half-plane, specializes to the
  real open unit interval, identifies concrete eta with `-expZeta`, derives
  zeta nonvanishing on `0 < x < 1`, and discharges the zero-height guard.

## What Remains Analytic

- The eta/open-unit zero-height payload is now closed theorem-backed by the
  paired positive-half-plane route.
- The remaining Lane-A analytic payload is no longer the real-axis
  zero-height guard; it is the nonzero-height spectral-parameter reality input:
  `∀ z : OrthodoxXiZeroCarrier,
    (orthodoxXiCarrierCenteredQuadratic z).im = 0`.
- `G8ActualXiNonzeroHeightSpectralReality` sharpens this further to the
  nonzero-height subtype:
  `G8ActualXiNonzeroHeightSpectralParameterReal`.
  This is now the preferred Lane-A payload, because zero-height carriers are
  already handled by the theorem-backed eta guard.
- Together with the now theorem-backed zero-height guard, that spectral reality
  field supplies `G8ActualXiHeightSplitSpectralRealityInputs` through
  `G8ActualXiZeroHeightAxisGuardDischarge.toHeightSplitInputs`.
- The final live hinge still also requires the independent Book III tower
  input `G8BookIIIAcceptedTowerRealizationFromSigmaFixed`; the eta work does
  not construct accepted tower witnesses.

## Non-Circularity Guardrails

- This route does not use `RiemannHypothesis`, accepted coverage, the final live
  hinge, O3, full divisor transfer, or analytic-completion uniqueness.
- The concrete eta series agreement and its analytic identification with
  Mathlib's continued additive-character `expZeta` on `0 < x < 1` are now
  theorem-backed through the paired positive-half-plane closure.
- The product identity theorem uses Mathlib's identity theorem from the safe
  right half-plane and does not use RH, accepted coverage, or any final-spine
  handoff.
- Real-valued zeta on `0 < x < 1` is now a consequence of the Abel
  identification plus the closed product identity, not an independent
  assumption.
- Height-split and final-live-hinge forwarding is intentionally restored only
  downstream in `G8EtaModTwoLaneAAssembly`.
