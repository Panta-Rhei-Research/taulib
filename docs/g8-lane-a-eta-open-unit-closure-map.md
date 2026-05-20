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

## What Remains Analytic

- Boundary-value identification of Mathlib's additive-character `expZeta` with
  the concrete shifted Abel radial limit:
  `G8EtaModTwoExpZetaAbelBoundaryValueOnOpenUnit`.
- This implies the older mod-two `ZMod.LFunction` boundary target by
  `g8EtaModTwoLFunctionAbelBoundaryValueOnOpenUnit_of_expZetaBoundary`.
- Equivalently, it is enough to prove the sharper pointwise target
  `G8EtaModTwoExpZetaConcreteEtaOnOpenUnit`.

Together these form `G8EtaModTwoOpenUnitEtaClosureData`, which forwards through
the existing zero-height discharge path.

## Non-Circularity Guardrails

- This route does not use `RiemannHypothesis`, accepted coverage, the final live
  hinge, O3, full divisor transfer, or analytic-completion uniqueness.
- The concrete eta series agreement is already theorem-backed; what remains is
  the analytic identification of Mathlib's continued `ZMod.LFunction` with the
  Abel boundary value of that conditional series on `0 < x < 1`.
- The product identity theorem uses Mathlib's identity theorem from the safe
  right half-plane and does not use RH, accepted coverage, or any final-spine
  handoff.
- Real-valued zeta on `0 < x < 1` is now a consequence of the Abel
  identification plus the closed product identity, not an independent
  assumption.
- If Mathlib's Abel-continuation APIs are expanded later, the named Abel target
  above is the exact place to instantiate them.  Current Mathlib exposes the
  additive-character analytic-continuation equality
  `ZMod.LFunction_stdAddChar_eq_expZeta`, but not the corresponding radial
  Abel-boundary theorem for `expZeta` on `0 < x < 1`.
- Height-split and final-live-hinge forwarding is intentionally restored only
  downstream in `G8EtaModTwoLaneAAssembly`.
