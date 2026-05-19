import TauLib.BookIII.Bridge.G8ActualXiZetaStrictGeometryDiscipline

/-!
# TauLib.BookIII.Bridge.G8PointSensitiveBoundarySelector

Point-sensitive boundary selector interface for the G8f actual `xi` corridor.

The research-paper reread sharpened the next proof target.  A real selector
must be address-realizing and NF-canonical: an orthodox centered shadow should
lead to a finite-provenance boundary witness whose normal form preserves the
localization-bearing B/C axis class.  It must not be hidden classical choice,
and it must not confuse the current binary off-axis sample with genuine
point-sensitive tau geometry.

This module therefore splits the layer into three pieces:

* a theorem-facing selector core, indexed by `CriticalAxisShadow`;
* the present binary/sample selector, explicitly diagnosed as sample-class;
* a future point-sensitive target that records the address-resolution,
  sector-splitting, tail-stability, and no-uneared-diagonal obligations.

No O3 theorem, analytic-completion uniqueness, full divisor transfer,
tau-side purity theorem, or classical RH theorem is proved here.
-/

set_option autoImplicit false

noncomputable section

namespace Tau.BookIII.Bridge

open Tau.BookIII.Spectral

-- ============================================================
-- SELECTOR CORE
-- ============================================================

/-- A boundary selector for centered receiving shadows.

The single theorem-bearing law is the localization law: the selected tau
boundary normal form has the same normalized axis class as the receiving
shadow.  Since the output is a `G8CanonicalBoundaryWitness`, finite-stage
provenance is carried by the value itself. -/
structure G8BoundarySelectorCore where
  select : CriticalAxisShadow → G8CanonicalBoundaryWitness
  axisClass_agrees :
    ∀ p : CriticalAxisShadow,
      primePolarityAxisOffset (select p).nf = normalizedAxisOffset p

/-- Every selector output is finite-stage realizable. -/
theorem g8BoundarySelectorCore_realizable
    (selector : G8BoundarySelectorCore)
    (p : CriticalAxisShadow) :
    BoundaryNFRealizable (selector.select p).nf :=
  g8CanonicalBoundaryWitness_realizable (selector.select p)

/-- A selector whose axis class agrees with an on-axis shadow selects a
    B/C-balanced tau normal form. -/
theorem g8BoundarySelectorCore_onAxis_bcBalanced
    (selector : G8BoundarySelectorCore)
    {p : CriticalAxisShadow}
    (hAxis : OnCriticalAxis p) :
    BCBalanced (selector.select p).nf := by
  have hPrime :
      primePolarityAxisOffset (selector.select p).nf = 0 := by
    rw [selector.axisClass_agrees p]
    exact normalizedAxisOffset_eq_zero_of_onAxis hAxis
  exact
    (primePolarityAxisOffset_eq_zero_iff_bcBalanced
      (selector.select p).nf).mp hPrime

/-- A selector whose axis class agrees with an off-axis shadow selects a
    B/C-imbalanced tau normal form. -/
theorem g8BoundarySelectorCore_offAxis_bcImbalance
    (selector : G8BoundarySelectorCore)
    {p : CriticalAxisShadow}
    (hOffAxis : ShadowOffAxis p) :
    TauBCImbalance (selector.select p).nf := by
  have hPrime :
      primePolarityAxisOffset (selector.select p).nf = 1 := by
    rw [selector.axisClass_agrees p]
    exact normalizedAxisOffset_eq_one_of_offAxis hOffAxis
  exact
    (primePolarityAxisOffset_eq_one_iff_bcImbalance
      (selector.select p).nf).mp hPrime

/-- Off-axis selector outputs are tau critical-imbalanced. -/
theorem g8BoundarySelectorCore_offAxis_criticalImbalance
    (selector : G8BoundarySelectorCore)
    {p : CriticalAxisShadow}
    (hOffAxis : ShadowOffAxis p) :
    TauCriticalImbalance (selector.select p).nf :=
  (tauCriticalImbalance_iff_bcImbalance
    (selector.select p).nf).mpr
    (g8BoundarySelectorCore_offAxis_bcImbalance
      selector hOffAxis)

/-- Off-axis selector outputs have unit prime-polarity axis class. -/
theorem g8BoundarySelectorCore_offAxis_unitAxis
    (selector : G8BoundarySelectorCore)
    {p : CriticalAxisShadow}
    (hOffAxis : ShadowOffAxis p) :
    primePolarityAxisOffset (selector.select p).nf = 1 := by
  rw [selector.axisClass_agrees p]
  exact normalizedAxisOffset_eq_one_of_offAxis hOffAxis

-- ============================================================
-- SAMPLE-CLASS FALLBACK
-- ============================================================

/-- The current binary/sample selector.

This is useful as the existing corridor fallback, but it is intentionally not
claimed to be genuinely point-sensitive: every off-axis shadow is sent to the
same finite off-axis sample witness. -/
def g8BinarySampleBoundarySelector_select
    (p : CriticalAxisShadow) : G8CanonicalBoundaryWitness :=
  if p.axisOffset = 0 then
    g8TauSampleOnAxisCanonicalBoundaryWitness
  else
    g8TauSampleOffAxisCanonicalBoundaryWitness

/-- The current binary/sample selector satisfies the axis-class selector law. -/
def g8BinarySampleBoundarySelector : G8BoundarySelectorCore where
  select := g8BinarySampleBoundarySelector_select
  axisClass_agrees := by
    intro p
    by_cases hRaw : p.axisOffset = 0
    · have hAxis : OnCriticalAxis p := by
        exact hRaw
      have hNorm :
          normalizedAxisOffset p = 0 :=
        normalizedAxisOffset_eq_zero_of_onAxis hAxis
      have hPrime :
          primePolarityAxisOffset
              (g8BinarySampleBoundarySelector_select p).nf = 0 := by
        have hSample :
            primePolarityAxisOffset g8TauSampleOnAxisBoundaryNF = 0 :=
          (primePolarityAxisOffset_eq_zero_iff_bcBalanced
            g8TauSampleOnAxisBoundaryNF).mpr
              g8TauSampleOnAxisBoundaryNF_bcBalanced
        simpa [
          g8BinarySampleBoundarySelector_select,
          hRaw,
          g8TauSampleOnAxisCanonicalBoundaryWitness
        ] using hSample
      rw [hPrime, hNorm]
    · have hOffAxis : ShadowOffAxis p := by
        simpa [ShadowOffAxis, OnCriticalAxis] using hRaw
      have hNorm :
          normalizedAxisOffset p = 1 :=
        normalizedAxisOffset_eq_one_of_offAxis hOffAxis
      have hPrime :
          primePolarityAxisOffset
              (g8BinarySampleBoundarySelector_select p).nf = 1 := by
        simpa [
          g8BinarySampleBoundarySelector_select,
          hRaw,
          g8TauSampleOffAxisCanonicalBoundaryWitness
        ] using
          g8TauSampleOffAxisBoundaryNF_unitAxis
      rw [hPrime, hNorm]

/-- On-axis shadows are sent to the on-axis sample witness by the current
    binary selector. -/
theorem g8BinarySampleBoundarySelector_onAxis_sample
    {p : CriticalAxisShadow}
    (hAxis : OnCriticalAxis p) :
    g8BinarySampleBoundarySelector.select p =
      g8TauSampleOnAxisCanonicalBoundaryWitness := by
  have hRaw : p.axisOffset = 0 := by
    simpa [OnCriticalAxis] using hAxis
  simp [
    g8BinarySampleBoundarySelector,
    g8BinarySampleBoundarySelector_select,
    hRaw
  ]

/-- Off-axis shadows are sent to the off-axis sample witness by the current
    binary selector. -/
theorem g8BinarySampleBoundarySelector_offAxis_sample
    {p : CriticalAxisShadow}
    (hOffAxis : ShadowOffAxis p) :
    g8BinarySampleBoundarySelector.select p =
      g8TauSampleOffAxisCanonicalBoundaryWitness := by
  have hRaw : p.axisOffset ≠ 0 := by
    simpa [ShadowOffAxis, OnCriticalAxis] using hOffAxis
  simp [
    g8BinarySampleBoundarySelector,
    g8BinarySampleBoundarySelector_select,
    hRaw
  ]

-- ============================================================
-- POINT-SENSITIVE TARGET AND DIAGNOSTICS
-- ============================================================

/-- A selector is off-axis sample-class when all off-axis shadows collapse to
    the same current sample witness. -/
def G8BoundarySelectorOffAxisSampleClass
    (selector : G8BoundarySelectorCore) : Prop :=
  ∀ p : CriticalAxisShadow,
    ShadowOffAxis p →
      selector.select p = g8TauSampleOffAxisCanonicalBoundaryWitness

/-- A selector is genuinely point-sensitive when two off-axis shadows can lead
    to distinct canonical boundary witnesses. -/
def G8BoundarySelectorGenuinelyPointSensitive
    (selector : G8BoundarySelectorCore) : Prop :=
  ∃ p q : CriticalAxisShadow,
    ShadowOffAxis p ∧
    ShadowOffAxis q ∧
    selector.select p ≠ selector.select q

/-- The current binary selector is off-axis sample-class. -/
theorem g8BinarySampleBoundarySelector_sampleClass :
    G8BoundarySelectorOffAxisSampleClass
      g8BinarySampleBoundarySelector := by
  intro p hOffAxis
  exact g8BinarySampleBoundarySelector_offAxis_sample hOffAxis

/-- The current binary selector is not genuinely point-sensitive. -/
theorem g8BinarySampleBoundarySelector_not_genuinelyPointSensitive :
    ¬ G8BoundarySelectorGenuinelyPointSensitive
      g8BinarySampleBoundarySelector := by
  intro h
  rcases h with ⟨p, q, hP, hQ, hNe⟩
  have hPeq :
      g8BinarySampleBoundarySelector.select p =
        g8TauSampleOffAxisCanonicalBoundaryWitness :=
    g8BinarySampleBoundarySelector_offAxis_sample hP
  have hQeq :
      g8BinarySampleBoundarySelector.select q =
        g8TauSampleOffAxisCanonicalBoundaryWitness :=
    g8BinarySampleBoundarySelector_offAxis_sample hQ
  exact hNe (hPeq.trans hQeq.symm)

/-- Future point-sensitive selector target.

The proposition fields are deliberately explicit obligations extracted from
address-resolution, boundary-algebra, holomorphy-first, and kernel-foundation
sources: canonical NF/address resolution, finite-depth/tail stability,
sector-split compatibility, and no unearned diagonal/choice shortcut. -/
structure G8PointSensitiveBoundarySelectorTarget where
  core : G8BoundarySelectorCore
  addressResolutionCanonical : Prop
  nfPathIndependent : Prop
  finiteDepthStable : Prop
  sectorSplitCompatible : Prop
  noUnearnedDiagonal : Prop
  genuinelyPointSensitive :
    G8BoundarySelectorGenuinelyPointSensitive core

-- ============================================================
-- COMPATIBILITY WITH THE CURRENT SELECTED-NF CORRIDOR
-- ============================================================

/-- Binary-compatible selectors are selector cores whose selected normal form
    is the current chart-selected binary normal form.

Future genuinely point-sensitive selectors should not be forced through this
adapter unless the old binary corridor has been generalized. -/
structure G8BinaryCompatibleBoundarySelector where
  core : G8BoundarySelectorCore
  selected_nf_eq :
    ∀ p : CriticalAxisShadow,
      (core.select p).nf = g8TauShadowSelectedNormalForm p

/-- The current sample selector is compatible with the existing selected-NF
    corridor. -/
def g8BinarySampleBoundarySelector_binaryCompatible :
    G8BinaryCompatibleBoundarySelector where
  core := g8BinarySampleBoundarySelector
  selected_nf_eq := by
    intro p
    by_cases hRaw : p.axisOffset = 0
    · have hAxis : OnCriticalAxis p := by
        exact hRaw
      simp [
        g8BinarySampleBoundarySelector,
        g8BinarySampleBoundarySelector_select,
        g8TauShadowSelectedNormalForm,
        hRaw,
        g8TauSampleOnAxisCanonicalBoundaryWitness
      ]
    · have hAxis : ¬ OnCriticalAxis p := by
        intro h
        exact hRaw (by simpa [OnCriticalAxis] using h)
      simp [
        g8BinarySampleBoundarySelector,
        g8BinarySampleBoundarySelector_select,
        g8TauShadowSelectedNormalForm,
        hRaw,
        g8TauSampleOffAxisCanonicalBoundaryWitness
      ]

/-- A binary-compatible selector can feed the existing thin boundary-address
    handoff. -/
def G8BinaryCompatibleBoundarySelector.to_thinBoundaryAddressHandoff
    (selector : G8BinaryCompatibleBoundarySelector)
    (source : G8ActualXiZetaThinSourceContext) :
    G8ActualXiZetaThinBoundaryAddressHandoff source where
  address :=
    fun z _hOffAxis =>
      selector.core.select
        (g8ActualXiZetaThinCenteredShadow source z)
  address_selected := by
    intro z _hOffAxis
    exact
      selector.selected_nf_eq
        (g8ActualXiZetaThinCenteredShadow source z)
  address_realizable := by
    intro z _hOffAxis
    exact
      g8BoundarySelectorCore_realizable
        selector.core
        (g8ActualXiZetaThinCenteredShadow source z)
  address_unitAxis := by
    intro z hOffAxis
    exact
      g8BoundarySelectorCore_offAxis_unitAxis
        selector.core
        hOffAxis
  address_criticalImbalance := by
    intro z hOffAxis
    exact
      g8BoundarySelectorCore_offAxis_criticalImbalance
        selector.core
        hOffAxis

/-- The binary sample selector recovers the current thin boundary-address
    handoff. -/
def g8BinarySampleBoundarySelector_to_thinBoundaryAddressHandoff
    (source : G8ActualXiZetaThinSourceContext) :
    G8ActualXiZetaThinBoundaryAddressHandoff source :=
  g8BinarySampleBoundarySelector_binaryCompatible
    |>.to_thinBoundaryAddressHandoff source

end Tau.BookIII.Bridge
