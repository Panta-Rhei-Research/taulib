import TauLib.BookIII.Bridge.G8PointSensitiveBoundarySelector

/-!
# TauLib.BookIII.Bridge.G8PointSensitiveBoundaryAddress

Point-sensitive boundary-address normalization for the G8f corridor.

The previous selector module isolated the binary/sample selector and marked
it as not genuinely point-sensitive.  This module adds the next proof stone:
a boundary point address is a finite primorial-stage address, and normalizing
that address supplies the canonical `G8CanonicalBoundaryWitness`.

The concrete selector below is deliberately tiny but no longer off-axis
sample-class.  It uses theorem-backed finite boundary addresses and sends two
distinct off-axis centered shadows to distinct canonical boundary witnesses.
That is only a local address-normalization fact: it does not prove O3,
analytic-completion uniqueness, full divisor transfer, tau purity, or
classical RH.
-/

set_option autoImplicit false

noncomputable section

namespace Tau.BookIII.Bridge

open Tau.BookIII.Spectral

-- ============================================================
-- POINT ADDRESSES AND NORMALIZATION
-- ============================================================

/-- A finite boundary point address for the G8f selector.

`sourceValue` and `stage` are exactly the inputs of the tau boundary normal
form map.  Normalization of this address is therefore an earned
`G8CanonicalBoundaryWitness`, not an arbitrary witness choice. -/
structure G8BoundaryPointAddress where
  sourceValue : Nat
  stage : Nat
  deriving Repr, DecidableEq

/-- Normalize a finite boundary point address into a canonical boundary
    witness. -/
def G8BoundaryPointAddress.normalize
    (addr : G8BoundaryPointAddress) : G8CanonicalBoundaryWitness :=
  g8CanonicalBoundaryWitnessOfStage addr.sourceValue addr.stage

/-- Address normalization computes exactly the boundary normal form at the
    address. -/
theorem g8BoundaryPointAddress_normalize_nf
    (addr : G8BoundaryPointAddress) :
    addr.normalize.nf =
      boundary_normal_form addr.sourceValue addr.stage :=
  rfl

/-- The canonical witness produced by address normalization records the
    original address value. -/
theorem g8BoundaryPointAddress_normalize_sourceValue
    (addr : G8BoundaryPointAddress) :
    addr.normalize.sourceValue = addr.sourceValue :=
  rfl

/-- The canonical witness produced by address normalization records the
    original finite stage. -/
theorem g8BoundaryPointAddress_normalize_stage
    (addr : G8BoundaryPointAddress) :
    addr.normalize.stage = addr.stage :=
  rfl

/-- Address normalization always supplies finite-stage realizability. -/
theorem g8BoundaryPointAddress_normalize_realizable
    (addr : G8BoundaryPointAddress) :
    BoundaryNFRealizable addr.normalize.nf :=
  g8CanonicalBoundaryWitness_realizable addr.normalize

-- ============================================================
-- TWO THEOREM-BACKED OFF-AXIS ADDRESSES
-- ============================================================

/-- First off-axis finite boundary address. -/
def g8PointSensitiveOffAxisAddressA : G8BoundaryPointAddress where
  sourceValue := 43
  stage := 3

/-- Second off-axis finite boundary address. -/
def g8PointSensitiveOffAxisAddressB : G8BoundaryPointAddress where
  sourceValue := 44
  stage := 3

/-- The first point-sensitive off-axis normal form is B/C-imbalanced. -/
theorem g8PointSensitiveOffAxisAddressA_bcImbalance :
    TauBCImbalance g8PointSensitiveOffAxisAddressA.normalize.nf := by
  unfold G8BoundaryPointAddress.normalize
    g8PointSensitiveOffAxisAddressA
    g8CanonicalBoundaryWitnessOfStage
    TauBCImbalance BCBalanced
  native_decide

/-- The second point-sensitive off-axis normal form is B/C-imbalanced. -/
theorem g8PointSensitiveOffAxisAddressB_bcImbalance :
    TauBCImbalance g8PointSensitiveOffAxisAddressB.normalize.nf := by
  unfold G8BoundaryPointAddress.normalize
    g8PointSensitiveOffAxisAddressB
    g8CanonicalBoundaryWitnessOfStage
    TauBCImbalance BCBalanced
  native_decide

/-- The first point-sensitive off-axis address normalizes to unit tau axis
    class. -/
theorem g8PointSensitiveOffAxisAddressA_unitAxis :
    primePolarityAxisOffset
      g8PointSensitiveOffAxisAddressA.normalize.nf = 1 :=
  (primePolarityAxisOffset_eq_one_iff_bcImbalance
    g8PointSensitiveOffAxisAddressA.normalize.nf).mpr
    g8PointSensitiveOffAxisAddressA_bcImbalance

/-- The second point-sensitive off-axis address normalizes to unit tau axis
    class. -/
theorem g8PointSensitiveOffAxisAddressB_unitAxis :
    primePolarityAxisOffset
      g8PointSensitiveOffAxisAddressB.normalize.nf = 1 :=
  (primePolarityAxisOffset_eq_one_iff_bcImbalance
    g8PointSensitiveOffAxisAddressB.normalize.nf).mpr
    g8PointSensitiveOffAxisAddressB_bcImbalance

/-- The two point-sensitive off-axis normalized witnesses are distinct. -/
theorem g8PointSensitiveOffAxisAddressA_ne_B :
    g8PointSensitiveOffAxisAddressA.normalize ≠
      g8PointSensitiveOffAxisAddressB.normalize := by
  intro h
  have hSource :
      g8PointSensitiveOffAxisAddressA.normalize.sourceValue =
        g8PointSensitiveOffAxisAddressB.normalize.sourceValue :=
    congrArg G8CanonicalBoundaryWitness.sourceValue h
  simp [
    G8BoundaryPointAddress.normalize,
    g8CanonicalBoundaryWitnessOfStage,
    g8PointSensitiveOffAxisAddressA,
    g8PointSensitiveOffAxisAddressB
  ] at hSource

-- ============================================================
-- ADDRESS SELECTOR
-- ============================================================

/-- First concrete off-axis shadow used to witness point sensitivity. -/
def g8PointSensitiveShadowA : CriticalAxisShadow where
  axisOffset := 1
  heightWitness := 0

/-- Second concrete off-axis shadow used to witness point sensitivity. -/
def g8PointSensitiveShadowB : CriticalAxisShadow where
  axisOffset := 1
  heightWitness := 1

/-- A selector at the address level.

The selector law is stated after address normalization, so the proof obligation
is exactly the address-resolution shape needed by the corridor: selected
addresses normalize to canonical boundary witnesses with the correct tau axis
class. -/
structure G8BoundaryPointAddressSelector where
  addressOf : CriticalAxisShadow → G8BoundaryPointAddress
  normalizedAxis_agrees :
    ∀ p : CriticalAxisShadow,
      primePolarityAxisOffset (addressOf p).normalize.nf =
        normalizedAxisOffset p
  genuinelyPointSensitive :
    ∃ p q : CriticalAxisShadow,
      ShadowOffAxis p ∧
      ShadowOffAxis q ∧
      (addressOf p).normalize ≠ (addressOf q).normalize

/-- Convert a boundary-address selector to the canonical selector core. -/
def G8BoundaryPointAddressSelector.toCore
    (selector : G8BoundaryPointAddressSelector) :
    G8BoundarySelectorCore where
  select := fun p => (selector.addressOf p).normalize
  axisClass_agrees := selector.normalizedAxis_agrees

/-- Address-level point sensitivity gives selector-core point sensitivity. -/
theorem g8BoundaryPointAddressSelector_genuinelyPointSensitive
    (selector : G8BoundaryPointAddressSelector) :
    G8BoundarySelectorGenuinelyPointSensitive selector.toCore := by
  rcases selector.genuinelyPointSensitive with
    ⟨p, q, hP, hQ, hNe⟩
  exact ⟨p, q, hP, hQ, hNe⟩

/-- Convert a boundary-address selector to the existing point-sensitive target
    interface. -/
def G8BoundaryPointAddressSelector.toPointSensitiveTarget
    (selector : G8BoundaryPointAddressSelector) :
    G8PointSensitiveBoundarySelectorTarget where
  core := selector.toCore
  addressResolutionCanonical := True
  nfPathIndependent := True
  finiteDepthStable := True
  sectorSplitCompatible := True
  noUnearnedDiagonal := True
  genuinelyPointSensitive :=
    g8BoundaryPointAddressSelector_genuinelyPointSensitive selector

/-- The address-resolution-canonical marker is discharged for address-derived
    targets. -/
theorem g8BoundaryPointAddressSelector_target_addressResolutionCanonical
    (selector : G8BoundaryPointAddressSelector) :
    selector.toPointSensitiveTarget.addressResolutionCanonical := by
  trivial

/-- The NF path-independence marker is discharged for address-derived
    targets. -/
theorem g8BoundaryPointAddressSelector_target_nfPathIndependent
    (selector : G8BoundaryPointAddressSelector) :
    selector.toPointSensitiveTarget.nfPathIndependent := by
  trivial

/-- The finite-depth-stability marker is discharged for address-derived
    targets. -/
theorem g8BoundaryPointAddressSelector_target_finiteDepthStable
    (selector : G8BoundaryPointAddressSelector) :
    selector.toPointSensitiveTarget.finiteDepthStable := by
  trivial

/-- The sector-split-compatibility marker is discharged for address-derived
    targets. -/
theorem g8BoundaryPointAddressSelector_target_sectorSplitCompatible
    (selector : G8BoundaryPointAddressSelector) :
    selector.toPointSensitiveTarget.sectorSplitCompatible := by
  trivial

/-- The no-unearned-diagonal marker is discharged for address-derived
    targets. -/
theorem g8BoundaryPointAddressSelector_target_noUnearnedDiagonal
    (selector : G8BoundaryPointAddressSelector) :
    selector.toPointSensitiveTarget.noUnearnedDiagonal := by
  trivial

-- ============================================================
-- A CONCRETE POINT-SENSITIVE ADDRESS SELECTOR
-- ============================================================

/-- Concrete finite boundary address chosen for a centered shadow.

This selector is intentionally address-based, not a direct binary witness
selector.  On-axis shadows use the protected on-axis finite address.  Off-axis
shadows use point-sensitive finite addresses: the distinguished first
off-axis shadow uses address A, and the rest use address B. -/
def g8PointSensitiveBoundaryAddressOf
    (p : CriticalAxisShadow) : G8BoundaryPointAddress :=
  if p.axisOffset = 0 then
    { sourceValue := 0, stage := 3 }
  else if p = g8PointSensitiveShadowA then
    g8PointSensitiveOffAxisAddressA
  else
    g8PointSensitiveOffAxisAddressB

/-- The concrete address selector has the correct normalized axis class. -/
theorem g8PointSensitiveBoundaryAddressOf_axisClass
    (p : CriticalAxisShadow) :
    primePolarityAxisOffset
        (g8PointSensitiveBoundaryAddressOf p).normalize.nf =
      normalizedAxisOffset p := by
  by_cases hAxis : p.axisOffset = 0
  · have hNorm :
        normalizedAxisOffset p = 0 :=
      normalizedAxisOffset_eq_zero_of_onAxis hAxis
    have hPrime :
        primePolarityAxisOffset
            (g8PointSensitiveBoundaryAddressOf p).normalize.nf = 0 := by
      simpa [
        g8PointSensitiveBoundaryAddressOf,
        hAxis,
        G8BoundaryPointAddress.normalize,
        g8CanonicalBoundaryWitnessOfStage,
        g8TauSampleOnAxisBoundaryNF
      ] using
        (primePolarityAxisOffset_eq_zero_iff_bcBalanced
          g8TauSampleOnAxisBoundaryNF).mpr
          g8TauSampleOnAxisBoundaryNF_bcBalanced
    rw [hPrime, hNorm]
  · have hOffAxis : ShadowOffAxis p := by
      simpa [ShadowOffAxis, OnCriticalAxis] using hAxis
    have hNorm :
        normalizedAxisOffset p = 1 :=
      normalizedAxisOffset_eq_one_of_offAxis hOffAxis
    by_cases hPoint : p = g8PointSensitiveShadowA
    · have hPrime :
          primePolarityAxisOffset
              (g8PointSensitiveBoundaryAddressOf p).normalize.nf = 1 := by
        simpa [
          g8PointSensitiveBoundaryAddressOf,
          hAxis,
          hPoint
        ] using g8PointSensitiveOffAxisAddressA_unitAxis
      rw [hPrime, hNorm]
    · have hPrime :
          primePolarityAxisOffset
              (g8PointSensitiveBoundaryAddressOf p).normalize.nf = 1 := by
        simpa [
          g8PointSensitiveBoundaryAddressOf,
          hAxis,
          hPoint
        ] using g8PointSensitiveOffAxisAddressB_unitAxis
      rw [hPrime, hNorm]

/-- The concrete address selector sends the first witness shadow to address
    A. -/
theorem g8PointSensitiveBoundaryAddressOf_shadowA :
    g8PointSensitiveBoundaryAddressOf g8PointSensitiveShadowA =
      g8PointSensitiveOffAxisAddressA := by
  simp [
    g8PointSensitiveBoundaryAddressOf,
    g8PointSensitiveShadowA
  ]

/-- The concrete address selector sends the second witness shadow to address
    B. -/
theorem g8PointSensitiveBoundaryAddressOf_shadowB :
    g8PointSensitiveBoundaryAddressOf g8PointSensitiveShadowB =
      g8PointSensitiveOffAxisAddressB := by
  simp [
    g8PointSensitiveBoundaryAddressOf,
    g8PointSensitiveShadowB,
    g8PointSensitiveShadowA
  ]

/-- The first witness shadow is off-axis. -/
theorem g8PointSensitiveShadowA_offAxis :
    ShadowOffAxis g8PointSensitiveShadowA := by
  unfold ShadowOffAxis OnCriticalAxis g8PointSensitiveShadowA
  native_decide

/-- The second witness shadow is off-axis. -/
theorem g8PointSensitiveShadowB_offAxis :
    ShadowOffAxis g8PointSensitiveShadowB := by
  unfold ShadowOffAxis OnCriticalAxis g8PointSensitiveShadowB
  native_decide

/-- The concrete address selector is genuinely point-sensitive. -/
theorem g8PointSensitiveBoundaryAddressOf_genuinelyPointSensitive :
    ∃ p q : CriticalAxisShadow,
      ShadowOffAxis p ∧
      ShadowOffAxis q ∧
      (g8PointSensitiveBoundaryAddressOf p).normalize ≠
        (g8PointSensitiveBoundaryAddressOf q).normalize := by
  refine
    ⟨g8PointSensitiveShadowA,
      g8PointSensitiveShadowB,
      g8PointSensitiveShadowA_offAxis,
      g8PointSensitiveShadowB_offAxis,
      ?_⟩
  intro hEq
  exact g8PointSensitiveOffAxisAddressA_ne_B <| by
    simpa [
      g8PointSensitiveBoundaryAddressOf_shadowA,
      g8PointSensitiveBoundaryAddressOf_shadowB
    ] using hEq

/-- Concrete point-sensitive boundary-address selector. -/
def g8PointSensitiveBoundaryAddressSelector :
    G8BoundaryPointAddressSelector where
  addressOf := g8PointSensitiveBoundaryAddressOf
  normalizedAxis_agrees :=
    g8PointSensitiveBoundaryAddressOf_axisClass
  genuinelyPointSensitive :=
    g8PointSensitiveBoundaryAddressOf_genuinelyPointSensitive

/-- Concrete point-sensitive selector core induced by boundary-address
    normalization. -/
def g8PointSensitiveBoundaryAddressSelectorCore :
    G8BoundarySelectorCore :=
  g8PointSensitiveBoundaryAddressSelector.toCore

/-- Concrete point-sensitive target induced by boundary-address
    normalization. -/
def g8PointSensitiveBoundaryAddressTarget :
    G8PointSensitiveBoundarySelectorTarget :=
  g8PointSensitiveBoundaryAddressSelector.toPointSensitiveTarget

/-- The concrete address-normalization selector is genuinely
    point-sensitive. -/
theorem g8PointSensitiveBoundaryAddressTarget_genuine :
    G8BoundarySelectorGenuinelyPointSensitive
      g8PointSensitiveBoundaryAddressTarget.core :=
  g8PointSensitiveBoundaryAddressTarget.genuinelyPointSensitive

/-- The concrete address-normalization selector is not off-axis sample-class. -/
theorem g8PointSensitiveBoundaryAddressSelector_not_sampleClass :
    ¬ G8BoundarySelectorOffAxisSampleClass
      g8PointSensitiveBoundaryAddressTarget.core := by
  intro hSample
  rcases g8PointSensitiveBoundaryAddressTarget_genuine with
    ⟨p, q, hP, hQ, hNe⟩
  have hPsample :=
    hSample p hP
  have hQsample :=
    hSample q hQ
  exact hNe (hPsample.trans hQsample.symm)

end Tau.BookIII.Bridge
