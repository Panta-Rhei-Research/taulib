import TauLib.BookIII.Bridge.G8FinalLiveHinge

/-!
# TauLib.BookIII.Bridge.G8ActualXiSigmaFixedReduction

Reduction surface for the final actual-`xi` sigma-fixed hinge.

The final live hinge consumes `G8ActualXiBoundaryCharacterSigmaFixed`.  This
module records exactly what that means in the current centered-address model:
it is equivalent to B/C balance of every normalized centered `xi` boundary
address, and it excludes carrier-level off-criticality because off-axis
centered addresses are already theorem-backed as B/C imbalanced.

The converse direction is also exposed as a theorem-backed reduction in the
current binary centered-address model.  This is a reduction, not a new proof of
RH: proving the premise `∀ z, ¬ OrthodoxXiCarrierOffCritical z` is itself the
localization-strength target.
-/

set_option autoImplicit false

noncomputable section

namespace Tau.BookIII.Bridge

-- ============================================================
-- ACTUAL SIGMA-FIXED AS CENTERED-ADDRESS BALANCE
-- ============================================================

/-- Every actual centered `xi` boundary address normalizes to the B/C balance
    hyperplane. -/
def G8ActualXiCenteredAddressBalanced : Prop :=
  ∀ z : OrthodoxXiZeroCarrier,
    BCBalanced
      (orthodoxXiCarrierCenteredBoundaryPointAddress z).normalize.nf

/-- Actual centered-address balance is equivalent to actual sigma-fixedness of
    the canonical `xi` boundary character. -/
theorem g8ActualXiCenteredAddressBalanced_iff_actualSigmaFixed :
    G8ActualXiCenteredAddressBalanced ↔
      G8ActualXiBoundaryCharacterSigmaFixed := by
  constructor
  · intro hBalanced z
    exact
      G8XiBoundaryCharacterSigmaFixed.of_centeredAddress_bcBalanced
        (hBalanced z)
  · intro hSigma z
    exact (hSigma z).centeredAddress_bcBalanced

/-- Actual centered-address balance supplies the final actual sigma-fixed target. -/
theorem G8ActualXiBoundaryCharacterSigmaFixed.of_centeredAddressBalanced
    (hBalanced : G8ActualXiCenteredAddressBalanced) :
    G8ActualXiBoundaryCharacterSigmaFixed :=
  g8ActualXiCenteredAddressBalanced_iff_actualSigmaFixed.mp hBalanced

/-- Actual sigma-fixedness supplies actual centered-address balance. -/
theorem G8ActualXiBoundaryCharacterSigmaFixed.centeredAddressBalanced
    (hSigma : G8ActualXiBoundaryCharacterSigmaFixed) :
    G8ActualXiCenteredAddressBalanced :=
  g8ActualXiCenteredAddressBalanced_iff_actualSigmaFixed.mpr hSigma

-- ============================================================
-- OFF-CRITICAL EXCLUSION REDUCTIONS
-- ============================================================

/-- Actual sigma-fixedness rejects carrier-level off-criticality pointwise.

The proof is the direct balance/imbalance contradiction:
an off-critical carrier is an off-axis centered shadow, and the centered address
construction maps off-axis shadows to B/C imbalance. -/
theorem G8ActualXiBoundaryCharacterSigmaFixed.noCarrierOffCritical
    (hSigma : G8ActualXiBoundaryCharacterSigmaFixed)
    (z : OrthodoxXiZeroCarrier) :
    ¬ OrthodoxXiCarrierOffCritical z := by
  intro hOffCritical
  have hOffAxis :
      ShadowOffAxis (orthodoxXiCarrierCenteredShadow z) :=
    (orthodoxXiCarrierOffCritical_iff_shadowOffAxis z).mp hOffCritical
  have hImbalance :
      TauBCImbalance
        (orthodoxXiCarrierCenteredBoundaryPointAddress z).normalize.nf :=
    orthodoxXiCarrierCenteredBoundaryPointAddress_bcImbalance z hOffAxis
  exact hImbalance ((hSigma z).centeredAddress_bcBalanced)

/-- Carrier-level off-critical exclusion forces actual centered-address balance
    in the current binary centered-address model. -/
theorem g8ActualXiCenteredAddressBalanced_of_noCarrierOffCritical
    (hNoOff :
      ∀ z : OrthodoxXiZeroCarrier, ¬ OrthodoxXiCarrierOffCritical z) :
    G8ActualXiCenteredAddressBalanced := by
  intro z
  have hNotOffAxis :
      ¬ ShadowOffAxis (orthodoxXiCarrierCenteredShadow z) := by
    intro hOffAxis
    exact hNoOff z
      ((orthodoxXiCarrierOffCritical_iff_shadowOffAxis z).mpr hOffAxis)
  have hOnAxis :
      OnCriticalAxis (orthodoxXiCarrierCenteredShadow z) := by
    by_contra hAxis
    exact hNotOffAxis hAxis
  have hAddress :
      orthodoxXiCarrierCenteredBoundaryPointAddress z =
        { sourceValue := 0, stage := 3 } :=
    orthodoxXiCarrierCenteredBoundaryPointAddress_onAxis z hOnAxis
  rw [hAddress]
  simpa [
    G8BoundaryPointAddress.normalize,
    g8CanonicalBoundaryWitnessOfStage,
    g8TauSampleOnAxisBoundaryNF
  ] using g8TauSampleOnAxisBoundaryNF_bcBalanced

/-- In the current centered-address model, no carrier off-criticality supplies
    the actual sigma-fixed target. -/
theorem G8ActualXiBoundaryCharacterSigmaFixed.of_noCarrierOffCritical
    (hNoOff :
      ∀ z : OrthodoxXiZeroCarrier, ¬ OrthodoxXiCarrierOffCritical z) :
    G8ActualXiBoundaryCharacterSigmaFixed :=
  G8ActualXiBoundaryCharacterSigmaFixed.of_centeredAddressBalanced
    (g8ActualXiCenteredAddressBalanced_of_noCarrierOffCritical hNoOff)

/-- Actual sigma-fixedness is equivalent to carrier-level off-critical
    exclusion in the current binary centered-address model. -/
theorem g8ActualXiBoundaryCharacterSigmaFixed_iff_noCarrierOffCritical :
    G8ActualXiBoundaryCharacterSigmaFixed ↔
      ∀ z : OrthodoxXiZeroCarrier, ¬ OrthodoxXiCarrierOffCritical z := by
  constructor
  · intro hSigma z
    exact hSigma.noCarrierOffCritical z
  · intro hNoOff
    exact G8ActualXiBoundaryCharacterSigmaFixed.of_noCarrierOffCritical hNoOff

-- ============================================================
-- FALSIFIERS
-- ============================================================

/-- A carrier-level off-critical `xi` zero refutes actual sigma-fixedness. -/
structure G8ActualXiOffCriticalCarrierFalsifier where
  z : OrthodoxXiZeroCarrier
  offCritical : OrthodoxXiCarrierOffCritical z

/-- Off-critical carrier evidence refutes actual sigma-fixedness. -/
theorem G8ActualXiOffCriticalCarrierFalsifier.refutesActualSigmaFixed
    (w : G8ActualXiOffCriticalCarrierFalsifier) :
    ¬ G8ActualXiBoundaryCharacterSigmaFixed := by
  intro hSigma
  exact hSigma.noCarrierOffCritical w.z w.offCritical

/-- A B/C-imbalanced centered address refutes actual centered-address balance. -/
structure G8ActualXiCenteredAddressImbalanceFalsifier where
  z : OrthodoxXiZeroCarrier
  imbalance :
    TauBCImbalance
      (orthodoxXiCarrierCenteredBoundaryPointAddress z).normalize.nf

/-- A B/C-imbalanced centered address refutes the balance reduction target. -/
theorem G8ActualXiCenteredAddressImbalanceFalsifier.refutesCenteredAddressBalanced
    (w : G8ActualXiCenteredAddressImbalanceFalsifier) :
    ¬ G8ActualXiCenteredAddressBalanced := by
  intro hBalanced
  exact w.imbalance (hBalanced w.z)

/-- A B/C-imbalanced centered address refutes actual sigma-fixedness. -/
theorem G8ActualXiCenteredAddressImbalanceFalsifier.refutesActualSigmaFixed
    (w : G8ActualXiCenteredAddressImbalanceFalsifier) :
    ¬ G8ActualXiBoundaryCharacterSigmaFixed := by
  intro hSigma
  exact w.refutesCenteredAddressBalanced hSigma.centeredAddressBalanced

/-- A non-sigma-fixed canonical character refutes the centered-address balance
    reduction target. -/
theorem G8TwoChannelButNotSigmaFixedWitness.refutesCenteredAddressBalanced
    (w : G8TwoChannelButNotSigmaFixedWitness) :
    ¬ G8ActualXiCenteredAddressBalanced := by
  intro hBalanced
  exact w.notSigmaFixed
    (G8XiBoundaryCharacterSigmaFixed.of_centeredAddress_bcBalanced
      (hBalanced w.z))

end Tau.BookIII.Bridge
