import TauLib.BookIII.Bridge.G8ActualXiOrthodoxCore
import TauLib.BookIII.Bridge.G8ActualOrthodoxCenteredChart

/-!
# TauLib.BookIII.Bridge.G8ActualXiZetaCore

Receiving-side orthodox `xi`/`zeta` chart core for the G8f corridor.

`G8ActualXiOrthodoxCore` is the sole direct Mathlib import point for the
orthodox `xi` carrier.  This module builds the centered shadow and receiving
RH handoff on top of that lower core.

The definitions below do not identify tau zeros with orthodox zeros, do not
prove O3, and do not establish any global target.  They only prove the local
chart-hygiene fact that off-criticality is exactly off-axis readability in the
centered shadow.
-/

set_option autoImplicit false

noncomputable section

namespace Tau.BookIII.Bridge

/-- Localization-bearing centered axis offset for an orthodox `xi` zero.

The corridor needs only the binary off-axis coordinate.  Height and provenance
remain downstream analytic bookkeeping and are deliberately not used here. -/
def orthodoxXiAxisOffset (z : OrthodoxXiZero) : Nat :=
  if z.point.re = (1 / 2 : ℝ) then 0 else 1

/-- Placeholder height/provenance coordinate for the centered shadow.

This module proves localization hygiene only; it does not classify height on
the critical axis. -/
def orthodoxXiHeightWitness (_z : OrthodoxXiZero) : Nat :=
  0

/-- Centered critical-axis shadow attached to an orthodox `xi` zero. -/
def orthodoxXiCenteredShadow (z : OrthodoxXiZero) :
    CriticalAxisShadow where
  axisOffset := orthodoxXiAxisOffset z
  heightWitness := orthodoxXiHeightWitness z

/-- The centered shadow is on-axis exactly when the orthodox zero has real part
    `1/2`. -/
theorem orthodoxXiAxisOffset_eq_zero_iff
    (z : OrthodoxXiZero) :
    orthodoxXiAxisOffset z = 0 ↔ z.point.re = (1 / 2 : ℝ) := by
  unfold orthodoxXiAxisOffset
  by_cases h : z.point.re = (1 / 2 : ℝ)
  · rw [if_pos h]
    simp [h]
  · rw [if_neg h]
    constructor
    · intro hOneZero
      cases hOneZero
    · intro hAxis
      exact False.elim (h hAxis)

/-- Orthodox off-criticality is exactly failure of the centered shadow axis. -/
theorem orthodoxXiOffCritical_iff_notOnAxis
    (z : OrthodoxXiZero) :
    OrthodoxXiOffCritical z ↔
      ¬ OnCriticalAxis (orthodoxXiCenteredShadow z) := by
  unfold OrthodoxXiOffCritical OnCriticalAxis orthodoxXiCenteredShadow
  rw [orthodoxXiAxisOffset_eq_zero_iff]

/-- Orthodox off-criticality is exactly off-axis readability in the centered
    shadow. -/
theorem orthodoxXiOffCritical_iff_shadowOffAxis
    (z : OrthodoxXiZero) :
    OrthodoxXiOffCritical z ↔
      ShadowOffAxis (orthodoxXiCenteredShadow z) :=
  orthodoxXiOffCritical_iff_notOnAxis z

/-- Off-axis readability in the actual `xi` shadow reflects back to the local
    off-critical predicate. -/
theorem orthodoxXiShadowOffAxis_to_offCritical
    (z : OrthodoxXiZero)
    (h : ShadowOffAxis (orthodoxXiCenteredShadow z)) :
    OrthodoxXiOffCritical z :=
  (orthodoxXiOffCritical_iff_shadowOffAxis z).mpr h

/-- Orthodox off-criticality yields off-axis readability in the actual `xi`
    shadow. -/
theorem orthodoxXiOffCritical_to_shadowOffAxis
    (z : OrthodoxXiZero)
    (h : OrthodoxXiOffCritical z) :
    ShadowOffAxis (orthodoxXiCenteredShadow z) :=
  (orthodoxXiOffCritical_iff_shadowOffAxis z).mp h

/-- Centered shadow for the universe-lifted orthodox `xi` carrier. -/
def orthodoxXiCarrierCenteredShadow (z : OrthodoxXiZeroCarrier) :
    CriticalAxisShadow :=
  orthodoxXiCenteredShadow z.toZero

/-- Carrier off-criticality is exactly failure of the centered shadow axis. -/
theorem orthodoxXiCarrierOffCritical_iff_notOnAxis
    (z : OrthodoxXiZeroCarrier) :
    OrthodoxXiCarrierOffCritical z ↔
      ¬ OnCriticalAxis (orthodoxXiCarrierCenteredShadow z) :=
  orthodoxXiOffCritical_iff_notOnAxis z.toZero

/-- Carrier off-criticality is exactly off-axis readability. -/
theorem orthodoxXiCarrierOffCritical_iff_shadowOffAxis
    (z : OrthodoxXiZeroCarrier) :
    OrthodoxXiCarrierOffCritical z ↔
      ShadowOffAxis (orthodoxXiCarrierCenteredShadow z) :=
  orthodoxXiOffCritical_iff_shadowOffAxis z.toZero

-- ============================================================
-- MATHLIB RH HANDOFF
-- ============================================================

/-- Coverage obligation from Mathlib's nontrivial zeta-zero target to the
    orthodox `xi` zero object used by this bridge corridor.

This is intentionally a named obligation.  The present module does not prove
that every Mathlib nontrivial zeta zero is represented by `OrthodoxXiZero`. -/
def G8XiCoversMathlibNontrivialZetaZeros : Prop :=
  ∀ (s : ℂ),
    riemannZeta s = 0 →
    (¬ ∃ n : ℕ, s = -2 * (n + 1)) →
    s ≠ 1 →
      ∃ z : OrthodoxXiZero, z.point = s

/-- If the orthodox `xi` zero object covers Mathlib's nontrivial zeta zeros and
    has no off-critical zeros, then Mathlib's `RiemannHypothesis` target follows.

This is a receiving-side adapter theorem, not a tau proof. -/
theorem mathlibRiemannHypothesis_from_noOffCriticalXiZeros
    (coverage : G8XiCoversMathlibNontrivialZetaZeros)
    (hNoOff : ∀ z : OrthodoxXiZero, ¬ OrthodoxXiOffCritical z) :
    RiemannHypothesis := by
  intro s hz htrivial hpole
  obtain ⟨z, hPoint⟩ := coverage s hz htrivial hpole
  have hAxis : z.point.re = (1 / 2 : ℝ) := by
    by_contra hOff
    exact hNoOff z hOff
  simpa [hPoint] using hAxis

end Tau.BookIII.Bridge
