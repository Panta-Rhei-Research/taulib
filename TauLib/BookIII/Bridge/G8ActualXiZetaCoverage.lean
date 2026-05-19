import TauLib.BookIII.Bridge.G8ActualXiZetaCorridor

/-!
# TauLib.BookIII.Bridge.G8ActualXiZetaCoverage

Receiving-side coverage from Mathlib's nontrivial `riemannZeta` zeros into the
orthodox `xi` zero object used by the G8f corridor.

This module is intentionally orthodox-facing: it uses Mathlib's zeta,
completed-zeta, gamma-factor, and `RiemannHypothesis` interfaces to discharge
the local coverage obligation introduced in `G8ActualXiZetaCore`.  It does not
prove any tau preimage theorem, O3, no-ghost theorem, analytic-completion
uniqueness, or classical RH by itself.
-/

set_option autoImplicit false

noncomputable section

namespace Tau.BookIII.Bridge

open Complex

-- ============================================================
-- ORTHODOX ZETA-TO-XI COVERAGE
-- ============================================================

/-- A Mathlib nontrivial zeta zero is not at `s = 0`.

The `RiemannHypothesis` target already excludes the negative even trivial
zeros and the pole at `1`; the value `ζ(0) = -1/2` rules out `0` from the
zero side. -/
theorem riemannZeta_zero_ne_zero_of_zero
    {s : ℂ}
    (hz : riemannZeta s = 0) :
    s ≠ 0 := by
  intro hs
  have hz0 : riemannZeta 0 = 0 := by
    simpa [hs] using hz
  norm_num [riemannZeta_zero] at hz0

/-- A Mathlib nontrivial zeta zero avoids the zeros of the completed
`Gammaℝ` factor.

The only `Gammaℝ` zeros are the nonpositive even integers.  The `ζ(0)` value
excludes `0`; the RiemannHypothesis nontrivial-zero hypothesis excludes the
negative even branch. -/
theorem gammaReal_ne_zero_of_nontrivial_riemannZeta_zero
    {s : ℂ}
    (hz : riemannZeta s = 0)
    (htrivial : ¬ ∃ n : ℕ, s = -2 * (n + 1)) :
    Gammaℝ s ≠ 0 := by
  intro hgamma
  have hs0 : s ≠ 0 := riemannZeta_zero_ne_zero_of_zero hz
  rcases (Gammaℝ_eq_zero_iff.mp hgamma) with ⟨n, hn⟩
  cases n with
  | zero =>
      have : s = 0 := by
        simpa using hn
      exact hs0 this
  | succ n =>
      apply htrivial
      refine ⟨n, ?_⟩
      simpa [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one,
        Nat.cast_mul] using hn

/-- A nontrivial Mathlib zeta zero forces the completed zeta factor to vanish.

This is purely a receiving-side Mathlib consequence: away from `s = 0`, zeta
is `completedRiemannZeta / Gammaℝ`, and the nontrivial-zero hypotheses keep the
gamma factor nonzero. -/
theorem completedRiemannZeta_eq_zero_of_nontrivial_riemannZeta_zero
    {s : ℂ}
    (hz : riemannZeta s = 0)
    (htrivial : ¬ ∃ n : ℕ, s = -2 * (n + 1)) :
    completedRiemannZeta s = 0 := by
  have hs0 : s ≠ 0 := riemannZeta_zero_ne_zero_of_zero hz
  have hgamma : Gammaℝ s ≠ 0 :=
    gammaReal_ne_zero_of_nontrivial_riemannZeta_zero hz htrivial
  have hdef : riemannZeta s = completedRiemannZeta s / Gammaℝ s :=
    riemannZeta_def_of_ne_zero hs0
  have hdiv : completedRiemannZeta s / Gammaℝ s = 0 := by
    simpa [hdef] using hz
  exact (div_eq_zero_iff.mp hdiv).resolve_right hgamma

/-- A nontrivial Mathlib zeta zero gives an orthodox `xi` zero.

This proves the coverage bridge used by the G8f corridor.  It is still only the
orthodox receiving-side coverage statement: no tau preimage or off-axis
no-ghost theorem is supplied here. -/
theorem orthodoxXi_eq_zero_of_nontrivial_riemannZeta_zero
    {s : ℂ}
    (hz : riemannZeta s = 0)
    (htrivial : ¬ ∃ n : ℕ, s = -2 * (n + 1))
    (hpole : s ≠ 1) :
    orthodoxXi s = 0 := by
  have hs0 : s ≠ 0 := riemannZeta_zero_ne_zero_of_zero hz
  have hOneSub : (1 - s) ≠ 0 := by
    intro h
    exact hpole (sub_eq_zero.mp h).symm
  have hcompleted :
      completedRiemannZeta s = 0 :=
    completedRiemannZeta_eq_zero_of_nontrivial_riemannZeta_zero
      hz htrivial
  have hregularized :
      completedRiemannZeta₀ s = 1 / s + 1 / (1 - s) := by
    have hrewrite :
        completedRiemannZeta₀ s - 1 / s - 1 / (1 - s) = 0 := by
      have h := completedRiemannZeta_eq s
      rw [hcompleted] at h
      exact h.symm
    calc
      completedRiemannZeta₀ s
          = (completedRiemannZeta₀ s - 1 / s - 1 / (1 - s)) +
              (1 / s + 1 / (1 - s)) := by
                ring
      _ = 0 + (1 / s + 1 / (1 - s)) := by
                rw [hrewrite]
      _ = 1 / s + 1 / (1 - s) := by
                simp
  unfold orthodoxXi
  rw [hregularized]
  field_simp [hs0, hOneSub]
  ring

/-- The named coverage obligation from Mathlib nontrivial zeta zeros to the
orthodox `xi` zero object is theorem-backed on the receiving side. -/
theorem g8XiCoversMathlibNontrivialZetaZeros :
    G8XiCoversMathlibNontrivialZetaZeros := by
  intro s hz htrivial hpole
  refine ⟨{ point := s
            isZero :=
              orthodoxXi_eq_zero_of_nontrivial_riemannZeta_zero
                hz htrivial hpole }, rfl⟩

-- ============================================================
-- CORRIDOR HANDOFF WITHOUT AN EXTERNAL COVERAGE PARAMETER
-- ============================================================

/-- Conditional handoff to Mathlib's formal `RiemannHypothesis` target using
the theorem-backed receiving-side coverage bridge.

All tau-side corridor obligations remain explicit inputs. -/
theorem g8ActualXiZetaCorridor_to_mathlibRiemannHypothesis_fromCoverage
    (source : G8ActualXiZetaSourceContext)
    (corridor : G8ActualXiZetaCorridor source)
    (tauPurity :
      G8eTauPurityExcludesOffCritical
        (g8ActualXiZeta_base source)) :
    RiemannHypothesis :=
  g8ActualXiZetaCorridor_to_mathlibRiemannHypothesis
    source corridor tauPurity
    g8XiCoversMathlibNontrivialZetaZeros

end Tau.BookIII.Bridge
