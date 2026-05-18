import TauLib.BookIII.Bridge.G8ChartRelation
import TauLib.BookII.Domains.Ultrametric
import TauLib.BookIII.Spectral.PrimorialLadder
import TauLib.BookIII.Sectors.ParityBridge
import TauLib.BookI.Polarity.H2H3ClassifierBridge

/-!
# TauLib.BookIII.Bridge.G8MasterSwitches

G8e.4 master-switch discipline for the RH bridge proof program.

This module records the three structural projections that make the tau route
different from a generic spectral attack on the classical zeta function:

1. split/hyperbolic geometry rather than only Gaussian/elliptic geometry;
2. ultrametric/profinite substrate rather than only Archimedean topology;
3. canonical prime-polarity boundary spectrum rather than an externally chosen
   operator.

The module deliberately stays at the discipline/interface level.  It does not
prove zero-divisor transfer, O3, analytic-completion uniqueness, or the
classical Riemann Hypothesis.  It only makes the three switches explicit so
future chart-relation work must pass through them rather than smuggling them in
as prose.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

-- ============================================================
-- MASTER-SWITCH LABELS
-- ============================================================

/-- The three structural projections used by the current G8 strategy. -/
inductive G8MasterSwitch where
  | hyperbolicLightCone
  | ultrametricSubstrate
  | canonicalPrimePolarity
  deriving Repr, DecidableEq

/-- Status labels for a master switch in the bridge program. -/
inductive G8MasterSwitchStatus where
  | sourceRecognized
  | bridgeObligation
  | finiteCheckOnly
  | contextHypothesis
  | notYetExternalized
  deriving Repr, DecidableEq

/-- The ultrametric/profinite substrate is visible through existing finite and
    structural anchors: ultrametric triangle/cylinder-ball checks plus
    primorial ladder/cofinality checks.

This is not a locally-uniform analytic convergence theorem.  It is the source
side substrate discipline that later G8 completion work must preserve. -/
def UltrametricSubstrateRecognized : Prop :=
  Tau.BookII.Domains.triangle_check 8 5 = true ∧
  Tau.BookII.Domains.cyl_eq_ball_check 1 3 20 5 = true ∧
  Tau.BookIII.Spectral.primorial_ladder_check 8 = true ∧
  Tau.BookIII.Spectral.primorial_cofinal_check 50 = true ∧
  Tau.BookIII.Spectral.prime_cofinal_check 30 = true

/-- Existing theorem-backed anchors recognize the ultrametric/profinite
    substrate at the finite-check level used elsewhere in TauLib. -/
theorem ultrametricSubstrate_recognized :
    UltrametricSubstrateRecognized := by
  exact ⟨Tau.BookII.Domains.triangle_8_5,
    Tau.BookII.Domains.cyl_ball_k1,
    Tau.BookIII.Spectral.primorial_ladder_8,
    Tau.BookIII.Spectral.primorial_cofinal_50,
    Tau.BookIII.Spectral.prime_cofinal_30⟩

/-- The canonical prime-polarity source truth is visible through the Book I
    / prime-polarity paper bridge: the abstract χ, concrete Pol, and
    Label_∞ agree over the standard small-prime audit range.

This is the anti-"external operator choice" discipline: the boundary spectrum
is supplied by prime polarity inside the tau construction.  Turning it into an
orthodox xi-divisor theorem remains a downstream G6/G8 obligation. -/
def PrimePolaritySourceTruthRecognized : Prop :=
  Tau.Polarity.chi Tau.Polarity.legendreBClass 2  = Tau.Polarity.Pol 2  ∧
  Tau.Polarity.chi Tau.Polarity.legendreBClass 3  = Tau.Polarity.Pol 3  ∧
  Tau.Polarity.chi Tau.Polarity.legendreBClass 5  = Tau.Polarity.Pol 5  ∧
  Tau.Polarity.chi Tau.Polarity.legendreBClass 7  = Tau.Polarity.Pol 7  ∧
  Tau.Polarity.chi Tau.Polarity.legendreBClass 11 = Tau.Polarity.Pol 11 ∧
  Tau.Polarity.chi Tau.Polarity.legendreBClass 13 = Tau.Polarity.Pol 13 ∧
  Tau.Polarity.chi Tau.Polarity.legendreBClass 17 = Tau.Polarity.Pol 17 ∧
  Tau.Polarity.chi Tau.Polarity.legendreBClass 19 = Tau.Polarity.Pol 19 ∧
  Tau.Polarity.chi Tau.Polarity.legendreBClass 23 = Tau.Polarity.Pol 23

/-- Existing theorem-backed anchors recognize the source-truth classifier. -/
theorem primePolaritySourceTruth_recognized :
    PrimePolaritySourceTruthRecognized :=
  Tau.Polarity.chi_legendre_eq_Pol_at_first_nine_primes

/-- Book III sector-level finite checks remain useful boundary-spectrum
    discipline, but they are downstream checks, not the classifier source
    truth itself. -/
def BoundarySectorPolarityRecognized : Prop :=
  Tau.BookIII.Sectors.spectral_polarity_check 5 = true ∧
  Tau.BookIII.Sectors.balanced_uniqueness_check 5 = true ∧
  Tau.BookIII.Sectors.parity_bridge_check 5 3 = true ∧
  Tau.BookIII.Sectors.no_knobs_check 5 3 = true

/-- The canonical prime-polarity switch combines the source-truth classifier
    bridge with the existing Book III boundary-sector finite checks. -/
def CanonicalPrimePolarityRecognized : Prop :=
  PrimePolaritySourceTruthRecognized ∧ BoundarySectorPolarityRecognized

/-- Existing theorem-backed anchors recognize the prime-polarity switch at the
    current finite-check level. -/
theorem canonicalPrimePolarity_recognized :
    CanonicalPrimePolarityRecognized := by
  exact ⟨primePolaritySourceTruth_recognized,
    ⟨Tau.BookIII.Sectors.spectral_polarity_5,
      Tau.BookIII.Sectors.balanced_uniqueness_5,
      Tau.BookIII.Sectors.parity_bridge_5_3,
      Tau.BookIII.Sectors.no_knobs_5_3⟩⟩

/-- All three master switches are recognized by existing TauLib source anchors. -/
def G8MasterSwitchesRecognized : Prop :=
  HyperbolicEllipticGeometryRecognized ∧
  UltrametricSubstrateRecognized ∧
  CanonicalPrimePolarityRecognized

/-- Existing TauLib anchors recognize the three-switch discipline. -/
theorem g8MasterSwitches_recognized :
    G8MasterSwitchesRecognized := by
  exact ⟨hyperbolicEllipticGeometry_recognized,
    ultrametricSubstrate_recognized,
    canonicalPrimePolarity_recognized⟩

-- ============================================================
-- THREE-SWITCH CHART CONTEXT
-- ============================================================

/-- A G8 chart context disciplined by the three master switches.

The switches are kept as fields so later work may replace finite-check anchors
with stronger theorem-backed constructions without changing the downstream
shape. -/
structure G8MasterSwitchContext where
  chart : HyperbolicEllipticChartRelationContext
  hyperbolicSwitch : Prop := HyperbolicEllipticGeometryRecognized
  ultrametricSwitch : Prop := UltrametricSubstrateRecognized
  primePolaritySwitch : Prop := CanonicalPrimePolarityRecognized
  hyperbolicStatus : G8MasterSwitchStatus := .sourceRecognized
  ultrametricStatus : G8MasterSwitchStatus := .sourceRecognized
  primePolarityStatus : G8MasterSwitchStatus := .sourceRecognized
  switchesJointlyConstrainChart : Prop
  primePolarityNotExternalOperatorChoice : Prop

/-- The three master switches are available in this context. -/
def G8MasterSwitchesAvailable
    (ctx : G8MasterSwitchContext) : Prop :=
  ctx.hyperbolicSwitch ∧
  ctx.ultrametricSwitch ∧
  ctx.primePolaritySwitch

/-- The chart relation is disciplined by all three master switches. -/
def G8MasterSwitchChartDisciplined
    (ctx : G8MasterSwitchContext) : Prop :=
  G8MasterSwitchesAvailable ctx ∧
  ctx.switchesJointlyConstrainChart ∧
  ctx.primePolarityNotExternalOperatorChoice

/-- The default source-recognized context has all three switches available. -/
theorem g8MasterSwitches_available_from_recognized
    (ctx : G8MasterSwitchContext)
    (hHyp : ctx.hyperbolicSwitch = HyperbolicEllipticGeometryRecognized)
    (hUltra : ctx.ultrametricSwitch = UltrametricSubstrateRecognized)
    (hPrime :
      ctx.primePolaritySwitch = CanonicalPrimePolarityRecognized) :
    G8MasterSwitchesAvailable ctx := by
  unfold G8MasterSwitchesAvailable
  rw [hHyp, hUltra, hPrime]
  exact g8MasterSwitches_recognized

/-- A master-switch disciplined context exposes the underlying G8e.3 chart
    relation context. -/
def g8MasterSwitchChartDisciplined_exposes_chart
    (ctx : G8MasterSwitchContext)
    (_h : G8MasterSwitchChartDisciplined ctx) :
    HyperbolicEllipticChartRelationContext :=
  ctx.chart

-- ============================================================
-- MASTER-SWITCH OBLIGATIONS AND HANDOFF
-- ============================================================

/-- G8e.4 obligations: the three switches discipline the chart relation, and
    the underlying G8e.3 chart-relation obligations still hold explicitly. -/
structure G8e4MasterSwitchObligations
    (ctx : G8MasterSwitchContext) where
  switches : G8MasterSwitchChartDisciplined ctx
  chartRelation : G8e3ChartRelationObligations ctx.chart

/-- The G8e.4 master-switch package recovers the G8e.3 chart relation. -/
theorem g8e4_masterSwitches_yield_g8e3
    (ctx : G8MasterSwitchContext)
    (h : G8e4MasterSwitchObligations ctx) :
    G8e3ChartRelationObligations ctx.chart :=
  h.chartRelation

/-- The G8e.4 package recovers the G8e.2 chart-faithfulness predicate. -/
theorem g8e4_masterSwitches_yield_chartFaithfulness
    (ctx : G8MasterSwitchContext)
    (h : G8e4MasterSwitchObligations ctx) :
    G8e1ChartFaithfulToTauImbalance ctx.chart.faithfulness.test :=
  g8e3_chartRelation_yields_g8e2ChartFaithfulness
    ctx.chart h.chartRelation

/-- The master-switch package keeps the meromorphic-artifact guardrail from
    G8e.3. -/
theorem g8e4_masterSwitches_ruleOut_artifactFalsifier
    (ctx : G8MasterSwitchContext)
    (h : G8e4MasterSwitchObligations ctx) :
    ¬ Nonempty (MeromorphicChartArtifactFalsifier ctx.chart) :=
  g8e3_meromorphicControl_rulesOut_artifactFalsifier
    ctx.chart h.chartRelation.meromorphic

/-- G8e.4 pullback package: the master-switch layer plus all remaining G8e.3
    pullback obligations. -/
structure G8e4PullbackSubobligations
    (ctx : G8MasterSwitchContext) where
  masterSwitches : G8e4MasterSwitchObligations ctx
  transfer :
    G8dZeroDivisorTransferAdmissible
      ctx.chart.faithfulness.test.base.transfer
  localFold : G8e1LocalFoldReadable ctx.chart.faithfulness.test
  tauWitness : G8e1TauImbalanceRealizesWitness ctx.chart.faithfulness.test
  noChartOnly : G8e1NoChartOnlyOffCriticalZero ctx.chart.faithfulness.test

/-- The G8e.4 pullback package rebuilds the G8e.3 pullback package. -/
theorem g8e4_subobligations_yield_g8e3
    (ctx : G8MasterSwitchContext)
    (h : G8e4PullbackSubobligations ctx) :
    G8e3PullbackSubobligations ctx.chart :=
  { chartRelation := h.masterSwitches.chartRelation
    transfer := h.transfer
    localFold := h.localFold
    tauWitness := h.tauWitness
    noChartOnly := h.noChartOnly }

/-- The G8e.4 package still depends on the G3 zeta bridge obligation. -/
theorem g8e4_subobligations_require_g3ZetaBridge
    (ctx : G8MasterSwitchContext)
    (h : G8e4PullbackSubobligations ctx) :
    ctx.chart.faithfulness.test.base.transfer.completion.chart.g3ZetaBridge :=
  g8e3_subobligations_require_g3ZetaBridge ctx.chart
    (g8e4_subobligations_yield_g8e3 ctx h)

/-- The G8e.4 package still depends on the G4 analytic-continuation obligation. -/
theorem g8e4_subobligations_require_g4AnalyticContinuation
    (ctx : G8MasterSwitchContext)
    (h : G8e4PullbackSubobligations ctx) :
    ctx.chart.faithfulness.test.base.transfer.completion.chart.g4AnalyticContinuation :=
  g8e3_subobligations_require_g4AnalyticContinuation ctx.chart
    (g8e4_subobligations_yield_g8e3 ctx h)

/-- The G8e.4 package still depends on the G5 operator-carrier obligation. -/
theorem g8e4_subobligations_require_g5OperatorCarrier
    (ctx : G8MasterSwitchContext)
    (h : G8e4PullbackSubobligations ctx) :
    ctx.chart.faithfulness.test.base.transfer.completion.chart.g5OperatorCarrier :=
  g8e3_subobligations_require_g5OperatorCarrier ctx.chart
    (g8e4_subobligations_yield_g8e3 ctx h)

/-- The G8e.4 package still depends on the G6 determinant/O3 bridge obligation. -/
theorem g8e4_subobligations_require_g6O3DeterminantBridge
    (ctx : G8MasterSwitchContext)
    (h : G8e4PullbackSubobligations ctx) :
    ctx.chart.faithfulness.test.base.transfer.completion.chart.g6O3DeterminantBridge :=
  g8e3_subobligations_require_g6O3DeterminantBridge ctx.chart
    (g8e4_subobligations_yield_g8e3 ctx h)

/-- The G8e.4 package still depends on analytic-completion uniqueness. -/
theorem g8e4_subobligations_require_completionUnique
    (ctx : G8MasterSwitchContext)
    (h : G8e4PullbackSubobligations ctx) :
    tauTower_analyticCompletion_unique
      ctx.chart.faithfulness.test.base.transfer.completion.chart :=
  g8e3_subobligations_require_completionUnique ctx.chart
    (g8e4_subobligations_yield_g8e3 ctx h)

/-- The G8e.4 package still depends on same-xi-divisor discipline. -/
theorem g8e4_subobligations_require_sameXiDivisor
    (ctx : G8MasterSwitchContext)
    (h : G8e4PullbackSubobligations ctx) :
    ctx.chart.faithfulness.test.base.transfer.completion.chart.sameXiDivisor :=
  g8e3_subobligations_require_sameXiDivisor ctx.chart
    (g8e4_subobligations_yield_g8e3 ctx h)

/-- The G8e.4 package still depends on no-lost-zero transfer. -/
theorem g8e4_subobligations_require_noLost
    (ctx : G8MasterSwitchContext)
    (h : G8e4PullbackSubobligations ctx) :
    ctx.chart.faithfulness.test.base.transfer.noLostZeros :=
  g8e3_subobligations_require_noLost ctx.chart
    (g8e4_subobligations_yield_g8e3 ctx h)

/-- The G8e.4 package still depends on no-spurious-zero transfer. -/
theorem g8e4_subobligations_require_noSpurious
    (ctx : G8MasterSwitchContext)
    (h : G8e4PullbackSubobligations ctx) :
    ctx.chart.faithfulness.test.base.transfer.noSpuriousZeros :=
  g8e3_subobligations_require_noSpurious ctx.chart
    (g8e4_subobligations_yield_g8e3 ctx h)

/-- The G8e.4 package still depends on multiplicity preservation. -/
theorem g8e4_subobligations_require_multiplicityPreserved
    (ctx : G8MasterSwitchContext)
    (h : G8e4PullbackSubobligations ctx) :
    ctx.chart.faithfulness.test.base.transfer.multiplicityPreserved :=
  g8e3_subobligations_require_multiplicityPreserved ctx.chart
    (g8e4_subobligations_yield_g8e3 ctx h)

/-- The G8e.4 package carries the non-uniqueness falsifier guardrail. -/
theorem g8e4_subobligations_require_noTwoCompletionsGuard
    (ctx : G8MasterSwitchContext)
    (h : G8e4PullbackSubobligations ctx) :
    noTwoCompletions_sameTauTower_differentDivisor
      ctx.chart.faithfulness.test.base.transfer.completion.chart :=
  g8e3_subobligations_require_noTwoCompletionsGuard ctx.chart
    (g8e4_subobligations_yield_g8e3 ctx h)

/-- G8e.4 test-level admissibility. -/
def G8e4ContradictionTestAdmissible
    (ctx : G8MasterSwitchContext) : Prop :=
  G8e4PullbackSubobligations ctx ∧
  G8eTauPurityExcludesOffCritical ctx.chart.faithfulness.test.base

/-- G8e.4 admissibility recovers the G8e.3 admissibility interface. -/
theorem g8e4_testAdmissible_to_g8e3TestAdmissible
    (ctx : G8MasterSwitchContext)
    (h : G8e4ContradictionTestAdmissible ctx) :
    G8e3ContradictionTestAdmissible ctx.chart :=
  ⟨g8e4_subobligations_yield_g8e3 ctx h.left, h.right⟩

/-- Conditional no-off-critical-zero conclusion at the G8e.4 master-switch
    level.  This remains entirely hypothesis-driven; it is not an unconditional
    classical RH theorem. -/
theorem g8e4_noOffCriticalZeros_from_testAdmissible
    (ctx : G8MasterSwitchContext)
    (h : G8e4ContradictionTestAdmissible ctx) :
    G8eNoOrthodoxOffCriticalZeros ctx.chart.faithfulness.test.base :=
  g8e3_noOffCriticalZeros_from_testAdmissible ctx.chart
    (g8e4_testAdmissible_to_g8e3TestAdmissible ctx h)

end Tau.BookIII.Bridge
