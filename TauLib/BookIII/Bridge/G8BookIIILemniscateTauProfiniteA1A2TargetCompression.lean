import TauLib.BookIII.Bridge.G8BookIIILemniscateTauProfiniteHilbertDomainTransfer

/-!
# TauLib.BookIII.Bridge.G8BookIIILemniscateTauProfiniteA1A2TargetCompression

Compression and coherence layer for the next three A1.1/A1.2 constructor
targets:

1. tau-circle/profinite lobe identification;
2. profinite lobe wedge and compact metric graph transfer;
3. graph measure, Hilbert/L2, trace, and Kirchhoff-domain transfer.

The previous module names each proof-carrying source separately.  This module
proves the bookkeeping theorem that the third source is a coherent package
containing the first two, and that it is exactly sufficient for the A1.1 metric
graph source plus the A1.2 Hilbert/domain source.

It does not construct the three targets from finite diagnostics or from the
current τ-circle trigonometric scaffold.  The remaining mathematical theorem is
still the actual τ-circle/profinite lobe equivalence, wedge graph metric
transfer, and graph Hilbert/Kirchhoff analysis.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

-- ============================================================
-- COHERENT THREE-TARGET PACKAGE
-- ============================================================

/-- Coherent package containing the three next A1.1/A1.2 constructor targets.

The coherence equalities prevent the three targets from being filled by
unrelated objects.  The Hilbert/domain transfer must use the same wedge transfer
source, and that wedge transfer must use the same lobe-identification source. -/
structure G8BookIIILemniscateTauProfiniteA1A2ThreeTargetPackage where
  lobeIdentification :
    G8BookIIILemniscateTauProfiniteLobeIdentificationSource
  wedgeTransfer :
    G8BookIIILemniscateTauProfiniteWedgeTransferSource
  wedgeUsesLobe :
    wedgeTransfer.lobeIdentification = lobeIdentification
  hilbertDomainTransfer :
    G8BookIIILemniscateTauProfiniteHilbertDomainTransferSource
  domainUsesWedge :
    hilbertDomainTransfer.graphTransfer = wedgeTransfer
  status : SpineStatus := .conditional_interface

/-- Compact target for the coherent three-target package. -/
def G8BookIIILemniscateTauProfiniteA1A2ThreeTarget : Prop :=
  Nonempty G8BookIIILemniscateTauProfiniteA1A2ThreeTargetPackage

/-- Any Hilbert/domain transfer source already contains the lobe and wedge
    sources coherently. -/
def
    G8BookIIILemniscateTauProfiniteHilbertDomainTransferSource.toThreeTargetPackage
    (source : G8BookIIILemniscateTauProfiniteHilbertDomainTransferSource) :
    G8BookIIILemniscateTauProfiniteA1A2ThreeTargetPackage where
  lobeIdentification := source.graphTransfer.lobeIdentification
  wedgeTransfer := source.graphTransfer
  wedgeUsesLobe := rfl
  hilbertDomainTransfer := source
  domainUsesWedge := rfl
  status := source.status

/-- The coherent three-target package is equivalent to the Hilbert/domain
    transfer target, because the third source carries the first two. -/
theorem g8BookIIILemniscateTauProfiniteA1A2ThreeTarget_iff_domainTransferTarget :
    G8BookIIILemniscateTauProfiniteA1A2ThreeTarget ↔
      G8BookIIILemniscateTauProfiniteHilbertDomainTransferTarget := by
  constructor
  · rintro ⟨pkg⟩
    exact ⟨pkg.hilbertDomainTransfer⟩
  · rintro ⟨source⟩
    exact ⟨source.toThreeTargetPackage⟩

/-- The coherent package supplies the lobe-identification target. -/
theorem G8BookIIILemniscateTauProfiniteA1A2ThreeTargetPackage.toLobeIdentificationTarget
    (pkg : G8BookIIILemniscateTauProfiniteA1A2ThreeTargetPackage) :
    G8BookIIILemniscateTauProfiniteLobeIdentificationTarget :=
  ⟨pkg.lobeIdentification⟩

/-- The coherent package supplies the wedge-transfer target. -/
theorem G8BookIIILemniscateTauProfiniteA1A2ThreeTargetPackage.toWedgeTransferTarget
    (pkg : G8BookIIILemniscateTauProfiniteA1A2ThreeTargetPackage) :
    G8BookIIILemniscateTauProfiniteWedgeTransferTarget :=
  ⟨pkg.wedgeTransfer⟩

/-- The coherent package supplies the Hilbert/domain transfer target. -/
theorem
    G8BookIIILemniscateTauProfiniteA1A2ThreeTargetPackage.toHilbertDomainTransferTarget
    (pkg : G8BookIIILemniscateTauProfiniteA1A2ThreeTargetPackage) :
    G8BookIIILemniscateTauProfiniteHilbertDomainTransferTarget :=
  ⟨pkg.hilbertDomainTransfer⟩

/-- The Hilbert/domain transfer target alone implies the first two targets. -/
theorem
    g8BookIIILemniscateTauProfiniteHilbertDomainTransferTarget.toFirstTwoTargets
    (target : G8BookIIILemniscateTauProfiniteHilbertDomainTransferTarget) :
    G8BookIIILemniscateTauProfiniteLobeIdentificationTarget ∧
      G8BookIIILemniscateTauProfiniteWedgeTransferTarget := by
  rcases target with ⟨source⟩
  exact ⟨⟨source.graphTransfer.lobeIdentification⟩,
    ⟨source.graphTransfer⟩⟩

-- ============================================================
-- A1.1/A1.2 DOWNSTREAM SELECTORS
-- ============================================================

/-- A coherent three-target package supplies the A1.1 metric graph source. -/
def G8BookIIILemniscateTauProfiniteA1A2ThreeTargetPackage.toMetricGraphSource
    (pkg : G8BookIIILemniscateTauProfiniteA1A2ThreeTargetPackage) :
    G8BookIIILemniscateMetricGraphSource :=
  pkg.wedgeTransfer.toMetricGraphSource

/-- A coherent three-target package supplies the A1.2 Hilbert/domain source. -/
def G8BookIIILemniscateTauProfiniteA1A2ThreeTargetPackage.toHilbertDomainSource
    (pkg : G8BookIIILemniscateTauProfiniteA1A2ThreeTargetPackage) :
    G8BookIIILemniscateHilbertDomainSource :=
  pkg.hilbertDomainTransfer.toHilbertDomainSource

/-- The coherent three-target package supplies the low-level Kirchhoff-domain
    readiness target. -/
theorem
    G8BookIIILemniscateTauProfiniteA1A2ThreeTargetPackage.toKirchhoffDomainReadinessTarget
    (pkg : G8BookIIILemniscateTauProfiniteA1A2ThreeTargetPackage) :
    G8BookIIILemniscateKirchhoffDomainReadinessTarget :=
  pkg.hilbertDomainTransfer.toKirchhoffDomainReadinessTarget

/-- The coherent three-target package supplies both proof-map sources needed
    for A1.1 and A1.2. -/
theorem
    G8BookIIILemniscateTauProfiniteA1A2ThreeTargetPackage.toMetricGraphAndDomainSources
    (pkg : G8BookIIILemniscateTauProfiniteA1A2ThreeTargetPackage) :
    Nonempty G8BookIIILemniscateMetricGraphSource ∧
      Nonempty G8BookIIILemniscateHilbertDomainSource :=
  ⟨⟨pkg.toMetricGraphSource⟩, ⟨pkg.toHilbertDomainSource⟩⟩

-- ============================================================
-- GUARDRAILS
-- ============================================================

/-- Absence of the lobe-identification target refutes the coherent three-target
    package. -/
structure G8BookIIILemniscateTauProfiniteLobeIdentificationGap where
  noLobeIdentification :
    ¬ G8BookIIILemniscateTauProfiniteLobeIdentificationTarget

/-- The coherent package cannot exist without lobe identification. -/
theorem G8BookIIILemniscateTauProfiniteLobeIdentificationGap.refutesThreeTarget
    (gap : G8BookIIILemniscateTauProfiniteLobeIdentificationGap) :
    ¬ G8BookIIILemniscateTauProfiniteA1A2ThreeTarget := by
  rintro ⟨pkg⟩
  exact gap.noLobeIdentification pkg.toLobeIdentificationTarget

/-- Absence of the wedge-transfer target refutes the coherent three-target
    package. -/
structure G8BookIIILemniscateTauProfiniteWedgeTransferGap where
  noWedgeTransfer :
    ¬ G8BookIIILemniscateTauProfiniteWedgeTransferTarget

/-- The coherent package cannot exist without wedge transfer. -/
theorem G8BookIIILemniscateTauProfiniteWedgeTransferGap.refutesThreeTarget
    (gap : G8BookIIILemniscateTauProfiniteWedgeTransferGap) :
    ¬ G8BookIIILemniscateTauProfiniteA1A2ThreeTarget := by
  rintro ⟨pkg⟩
  exact gap.noWedgeTransfer pkg.toWedgeTransferTarget

/-- Absence of the Hilbert/domain transfer target refutes the coherent
    three-target package. -/
structure G8BookIIILemniscateTauProfiniteHilbertDomainTransferGap where
  noHilbertDomainTransfer :
    ¬ G8BookIIILemniscateTauProfiniteHilbertDomainTransferTarget

/-- The coherent package cannot exist without Hilbert/domain transfer. -/
theorem G8BookIIILemniscateTauProfiniteHilbertDomainTransferGap.refutesThreeTarget
    (gap : G8BookIIILemniscateTauProfiniteHilbertDomainTransferGap) :
    ¬ G8BookIIILemniscateTauProfiniteA1A2ThreeTarget := by
  rintro ⟨pkg⟩
  exact gap.noHilbertDomainTransfer pkg.toHilbertDomainTransferTarget

/-- Unrelated lobe and wedge witnesses do not form the coherent target unless
    the wedge source uses exactly the selected lobe-identification source. -/
structure G8BookIIILemniscateTauProfiniteIncoherentLobeWedgePair where
  lobeIdentification :
    G8BookIIILemniscateTauProfiniteLobeIdentificationSource
  wedgeTransfer :
    G8BookIIILemniscateTauProfiniteWedgeTransferSource
  notCoherent :
    wedgeTransfer.lobeIdentification ≠ lobeIdentification

/-- Coherence is an exact equality, not a diagnostic compatibility check. -/
theorem G8BookIIILemniscateTauProfiniteIncoherentLobeWedgePair.refutesPackage
    {pkg : G8BookIIILemniscateTauProfiniteA1A2ThreeTargetPackage}
    (gap : G8BookIIILemniscateTauProfiniteIncoherentLobeWedgePair)
    (hLobe : pkg.lobeIdentification = gap.lobeIdentification)
    (hWedge : pkg.wedgeTransfer = gap.wedgeTransfer) :
    False := by
  apply gap.notCoherent
  rw [← hWedge, ← hLobe]
  exact pkg.wedgeUsesLobe

end Tau.BookIII.Bridge
