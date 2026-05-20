import TauLib.BookIII.Bridge.G8EtaModTwoAbelBoundaryIdentification

/-!
# TauLib.BookIII.Bridge.G8EtaModTwoAbelBoundaryClosure

Final Abel-boundary closure surface for the Lane-A zero-height eta bridge.

The concrete Abel limit is already theorem-backed in
`G8EtaModTwoAbelBoundaryIdentification`.  This module closes the algebraic
connection between the mod-two eta coefficient and Mathlib's additive-character
`expZeta` model.  The remaining analytic payload, if not supplied by Mathlib, is
now the single radial-boundary theorem saying that this `expZeta` value is the
Abel boundary value of the shifted positive-index eta power series on
`0 < x < 1`.

No result here uses RH, accepted coverage, the final live hinge, O3, full
divisor transfer, or analytic-completion uniqueness.
-/

set_option autoImplicit false

noncomputable section

namespace Tau.BookIII.Bridge

open Complex Filter

open scoped BigOperators Topology

-- ============================================================
-- MOD-TWO COEFFICIENT AS AN ADDITIVE CHARACTER
-- ============================================================

/-- The mod-two eta coefficient is the negative of Mathlib's standard additive
    character on `ZMod 2`.  This is the sign convention matching positive
    indices: odd `+1`, even `-1`. -/
theorem g8EtaModTwoCoeff_eq_neg_stdAddChar
    (j : ZMod 2) :
    g8EtaModTwoCoeff j =
      - (ZMod.stdAddChar (N := 2) j) := by
  fin_cases j
  · simp [g8EtaModTwoCoeff]
  · change (1 : ℂ) = - (ZMod.stdAddChar (N := 2) (1 : ZMod 2))
    have hStdOne :
        ZMod.stdAddChar (N := 2) (1 : ZMod 2) = (-1 : ℂ) := by
      rw [show (1 : ZMod 2) = ((1 : ℤ) : ZMod 2) by norm_num]
      rw [ZMod.stdAddChar_coe (N := 2) (1 : ℤ)]
      convert Complex.exp_pi_mul_I using 1
      ring_nf
    rw [hStdOne]
    norm_num

/-- Function-level form of the mod-two coefficient bridge. -/
theorem g8EtaModTwoCoeff_funext_neg_stdAddChar :
    g8EtaModTwoCoeff =
      (fun j : ZMod 2 => - (ZMod.stdAddChar (N := 2) j)) := by
  funext j
  exact g8EtaModTwoCoeff_eq_neg_stdAddChar j

/-- Mathlib's mod-two eta `LFunction` is the negative additive-character
    `expZeta` attached to the nontrivial class in `ZMod 2`. -/
theorem g8EtaModTwoLFunction_eq_neg_expZeta
    (s : ℂ) :
    g8EtaModTwoLFunction s =
      - HurwitzZeta.expZeta (ZMod.toAddCircle (1 : ZMod 2)) s := by
  have hOneNe : (1 : ZMod 2) ≠ 0 := by
    norm_num
  have hStd :
      ZMod.LFunction
          (fun k : ZMod 2 =>
            ZMod.stdAddChar (N := 2) ((1 : ZMod 2) * k)) s =
        HurwitzZeta.expZeta (ZMod.toAddCircle (1 : ZMod 2)) s :=
    ZMod.LFunction_stdAddChar_eq_expZeta
      (N := 2) (1 : ZMod 2) s (Or.inl hOneNe)
  have hStd' :
      ZMod.LFunction (ZMod.stdAddChar (N := 2)) s =
        HurwitzZeta.expZeta (ZMod.toAddCircle (1 : ZMod 2)) s := by
    simpa using hStd
  calc
    g8EtaModTwoLFunction s =
        ZMod.LFunction
          (fun j : ZMod 2 => - (ZMod.stdAddChar (N := 2) j)) s := by
      simp [g8EtaModTwoLFunction, g8EtaModTwoCoeff_funext_neg_stdAddChar]
    _ = - ZMod.LFunction (ZMod.stdAddChar (N := 2)) s := by
      simp [ZMod.LFunction, Finset.mul_sum, Finset.sum_neg_distrib]
    _ = - HurwitzZeta.expZeta (ZMod.toAddCircle (1 : ZMod 2)) s := by
      rw [hStd']

-- ============================================================
-- THE EXACT REMAINING ABEL / EXPZETA BOUNDARY TARGET
-- ============================================================

/-- The smallest remaining analytic payload after the coefficient bridge:
    Mathlib's additive-character `expZeta` value is the radial Abel boundary
    value of the shifted eta power series on the real open unit interval. -/
abbrev G8EtaModTwoExpZetaAbelBoundaryValueOnOpenUnit : Prop :=
  ∀ (x : ℝ) (_hx0 : 0 < x) (_hx1 : x < 1),
    Tendsto (fun r : ℂ => g8EtaModTwoAbelPowerSeries x r)
      ((𝓝[<] (1 : ℝ)).map ofReal)
      (𝓝 (- HurwitzZeta.expZeta
        (ZMod.toAddCircle (1 : ZMod 2)) (x : ℂ)))

/-- The additive-character Abel boundary theorem is exactly sufficient for the
    existing mod-two `ZMod.LFunction` Abel boundary target. -/
theorem g8EtaModTwoLFunctionAbelBoundaryValueOnOpenUnit_of_expZetaBoundary
    (hBoundary : G8EtaModTwoExpZetaAbelBoundaryValueOnOpenUnit) :
    G8EtaModTwoLFunctionAbelBoundaryValueOnOpenUnit := by
  intro x hx0 hx1
  simpa [g8EtaModTwoLFunction_eq_neg_expZeta] using
    hBoundary x hx0 hx1

/-- The additive-character Abel boundary theorem is enough to recover the
    open-unit eta-zeta identity. -/
theorem g8DirichletEtaZetaIdentityOnOpenUnit_of_expZetaAbelBoundary
    (hBoundary : G8EtaModTwoExpZetaAbelBoundaryValueOnOpenUnit) :
    G8DirichletEtaZetaIdentityOnOpenUnit :=
  g8DirichletEtaZetaIdentityOnOpenUnit_of_abelBoundary
    (g8EtaModTwoLFunctionAbelBoundaryValueOnOpenUnit_of_expZetaBoundary
      hBoundary)

/-- The additive-character Abel boundary theorem discharges the zero-height
    axis guard through the existing eta corridor. -/
def G8ActualXiZeroHeightAxisGuardDischarge.ofEtaModTwoExpZetaAbelBoundary
    (hBoundary : G8EtaModTwoExpZetaAbelBoundaryValueOnOpenUnit) :
    G8ActualXiZeroHeightAxisGuardDischarge :=
  G8ActualXiZeroHeightAxisGuardDischarge.ofEtaModTwoAbelBoundary
    (g8EtaModTwoLFunctionAbelBoundaryValueOnOpenUnit_of_expZetaBoundary
      hBoundary)

end Tau.BookIII.Bridge
