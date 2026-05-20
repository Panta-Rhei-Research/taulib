import TauLib.BookIII.Bridge.G8EtaModTwoConcreteEtaIdentification

/-!
# TauLib.BookIII.Bridge.G8EtaModTwoAbelBoundaryIdentification

Abel-boundary identification layer for the Lane-A zero-height eta bridge.

The product side is theorem-backed.  This module closes the concrete Abel
limit side: the conditional eta value already used by the zero-height
corridor is the radial boundary value of the mod-two Abel power series.  The
remaining analytic payload is now exactly the boundary-value law saying that
Mathlib's continued mod-two `ZMod.LFunction` has the same radial limit on the
real open unit interval.

No result here uses RH, accepted coverage, the final live hinge, O3, full
divisor transfer, or analytic-completion uniqueness.
-/

set_option autoImplicit false

noncomputable section

namespace Tau.BookIII.Bridge

open Complex Filter

open scoped BigOperators Topology

-- ============================================================
-- ABEL POWER SERIES FOR THE MOD-TWO ETA COEFFICIENT
-- ============================================================

/-- Coefficient of the Abel power series attached to the concrete eta value at
    `x`.  The shift matches the positive-index mod-two coefficient convention:
    odd indices carry `+1`, even indices carry `-1`. -/
def g8EtaModTwoAbelCoeff (x : ℝ) (n : ℕ) : ℂ :=
  g8EtaModTwoNatCoeff (n + 1) *
    (g8DirichletEtaMagnitude x n : ℂ)

/-- The `n`th Abel power-series term at radial parameter `r`. -/
def g8EtaModTwoAbelPowerTerm (x : ℝ) (n : ℕ) (r : ℂ) : ℂ :=
  g8EtaModTwoAbelCoeff x n * r ^ n

/-- Abel-smoothed mod-two eta power series. -/
def g8EtaModTwoAbelPowerSeries (x : ℝ) (r : ℂ) : ℂ :=
  ∑' n : ℕ, g8EtaModTwoAbelPowerTerm x n r

/-- At `r = 1`, the finite Abel partial sums are the existing conditional
    mod-two eta partial sums. -/
theorem g8EtaModTwoAbelCoeff_partial_eq_naive
    (x : ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range n, g8EtaModTwoAbelCoeff x i) =
      g8EtaModTwoNaiveConditionalPartial x n := by
  simp [g8EtaModTwoAbelCoeff,
    g8EtaModTwoNaiveConditionalPartial]

/-- At `r = 1`, the finite Abel partial sums are the concrete real eta
    partial sums, transported to `ℂ`. -/
theorem g8EtaModTwoAbelCoeff_partial_eq_concreteEta
    (x : ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range n, g8EtaModTwoAbelCoeff x i) =
      (g8DirichletEtaPartial x n : ℂ) := by
  rw [g8EtaModTwoAbelCoeff_partial_eq_naive,
    g8EtaModTwoNaiveConditionalPartial_eq_concreteEtaPartial]

/-- The theorem-backed Abel limit: the Abel power series tends to the concrete
    conditional eta value as the radial parameter tends to `1` from the left.

This is the clean formal Abel theorem supplied by
`Mathlib.Analysis.Complex.AbelLimit`; it does not identify the resulting
boundary value with Mathlib's continued `ZMod.LFunction`. -/
theorem g8EtaModTwoAbelPowerSeries_tendsto_concreteEta
    (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    Tendsto (fun r : ℂ => g8EtaModTwoAbelPowerSeries x r)
      ((𝓝[<] (1 : ℝ)).map ofReal)
      (𝓝 ((g8EtaModTwoNaiveLSeries_agreesWithConcreteEtaOnOpenUnit.naiveSeries
        x hx0 hx1).value)) := by
  let series :=
    g8EtaModTwoNaiveLSeries_agreesWithConcreteEtaOnOpenUnit.naiveSeries
      x hx0 hx1
  have hPartial :
      Tendsto
        (fun n : ℕ => ∑ i ∈ Finset.range n,
          g8EtaModTwoAbelCoeff x i)
        atTop (𝓝 series.value) := by
    exact series.partialTendsto.congr'
      (Eventually.of_forall fun n =>
        (g8EtaModTwoAbelCoeff_partial_eq_naive x n).symm)
  have hAbel :=
    Complex.tendsto_tsum_powerSeries_nhdsWithin_lt
      (f := fun n : ℕ => g8EtaModTwoAbelCoeff x n)
      (l := series.value) hPartial
  simpa [g8EtaModTwoAbelPowerSeries,
    g8EtaModTwoAbelPowerTerm] using hAbel

-- ============================================================
-- THE REMAINING L-FUNCTION BOUNDARY-VALUE TARGET
-- ============================================================

/-- The exact remaining analytic boundary-value target: Mathlib's continued
    mod-two `ZMod.LFunction` is the radial Abel boundary value of the concrete
    eta power series on the real open unit interval. -/
abbrev G8EtaModTwoLFunctionAbelBoundaryValueOnOpenUnit : Prop :=
  ∀ (x : ℝ) (_hx0 : 0 < x) (_hx1 : x < 1),
    Tendsto (fun r : ℂ => g8EtaModTwoAbelPowerSeries x r)
      ((𝓝[<] (1 : ℝ)).map ofReal)
      (𝓝 (g8EtaModTwoLFunction (x : ℂ)))

/-- The Abel boundary-value law is sufficient for the existing conditional
    eta/L-function identification target. -/
theorem g8EtaModTwoConditionalEtaAbelIdentificationOnOpenUnit_of_abelBoundary
    (hBoundary : G8EtaModTwoLFunctionAbelBoundaryValueOnOpenUnit) :
    G8EtaModTwoConditionalEtaAbelIdentificationOnOpenUnit := by
  intro x hx0 hx1
  exact tendsto_nhds_unique
    (hBoundary x hx0 hx1)
    (g8EtaModTwoAbelPowerSeries_tendsto_concreteEta x hx0 hx1)

/-- Abel boundary-value identification supplies the open-unit eta-zeta
    identity through the previously closed product side. -/
theorem g8DirichletEtaZetaIdentityOnOpenUnit_of_abelBoundary
    (hBoundary : G8EtaModTwoLFunctionAbelBoundaryValueOnOpenUnit) :
    G8DirichletEtaZetaIdentityOnOpenUnit :=
  g8DirichletEtaZetaIdentityOnOpenUnit_of_conditionalEtaAbelIdentification
    (g8EtaModTwoConditionalEtaAbelIdentificationOnOpenUnit_of_abelBoundary
      hBoundary)

/-- Abel boundary-value identification discharges the zero-height axis guard. -/
def G8ActualXiZeroHeightAxisGuardDischarge.ofEtaModTwoAbelBoundary
    (hBoundary : G8EtaModTwoLFunctionAbelBoundaryValueOnOpenUnit) :
    G8ActualXiZeroHeightAxisGuardDischarge :=
  G8ActualXiZeroHeightAxisGuardDischarge.ofConditionalEtaAbelIdentification
    (g8EtaModTwoConditionalEtaAbelIdentificationOnOpenUnit_of_abelBoundary
      hBoundary)

-- ============================================================
-- RED-TEAM FALSIFIERS
-- ============================================================

/-- A falsifier for the theorem-backed concrete Abel limit. -/
structure G8EtaModTwoConcreteAbelLimitMismatch where
  x : ℝ
  pos : 0 < x
  lt_one : x < 1
  mismatch :
    ¬ Tendsto (fun r : ℂ => g8EtaModTwoAbelPowerSeries x r)
      ((𝓝[<] (1 : ℝ)).map ofReal)
      (𝓝 ((g8EtaModTwoNaiveLSeries_agreesWithConcreteEtaOnOpenUnit.naiveSeries
        x pos lt_one).value))

/-- The theorem-backed Abel limit refutes any concrete Abel-limit mismatch. -/
theorem G8EtaModTwoConcreteAbelLimitMismatch.refutes
    (w : G8EtaModTwoConcreteAbelLimitMismatch) :
    False :=
  w.mismatch
    (g8EtaModTwoAbelPowerSeries_tendsto_concreteEta
      w.x w.pos w.lt_one)

/-- A point where the mod-two `LFunction` is not the Abel boundary value
    refutes the boundary-value target. -/
structure G8EtaModTwoLFunctionAbelBoundaryMismatch where
  x : ℝ
  pos : 0 < x
  lt_one : x < 1
  mismatch :
    ¬ Tendsto (fun r : ℂ => g8EtaModTwoAbelPowerSeries x r)
      ((𝓝[<] (1 : ℝ)).map ofReal)
      (𝓝 (g8EtaModTwoLFunction (x : ℂ)))

/-- A pointwise L-function boundary mismatch refutes the global boundary law. -/
theorem G8EtaModTwoLFunctionAbelBoundaryMismatch.refutes
    (w : G8EtaModTwoLFunctionAbelBoundaryMismatch)
    (hBoundary : G8EtaModTwoLFunctionAbelBoundaryValueOnOpenUnit) :
    False :=
  w.mismatch (hBoundary w.x w.pos w.lt_one)

/-- A point where both boundary limits are supplied but the conditional eta
    identification fails. -/
structure G8EtaModTwoConditionalEtaIdentificationDespiteBoundaryMismatch where
  x : ℝ
  pos : 0 < x
  lt_one : x < 1
  lFunctionBoundary :
    Tendsto (fun r : ℂ => g8EtaModTwoAbelPowerSeries x r)
      ((𝓝[<] (1 : ℝ)).map ofReal)
      (𝓝 (g8EtaModTwoLFunction (x : ℂ)))
  concreteBoundary :
    Tendsto (fun r : ℂ => g8EtaModTwoAbelPowerSeries x r)
      ((𝓝[<] (1 : ℝ)).map ofReal)
      (𝓝 ((g8EtaModTwoNaiveLSeries_agreesWithConcreteEtaOnOpenUnit.naiveSeries
        x pos lt_one).value))
  mismatch :
    g8EtaModTwoLFunction (x : ℂ) ≠
      (g8EtaModTwoNaiveLSeries_agreesWithConcreteEtaOnOpenUnit.naiveSeries
        x pos lt_one).value

/-- Uniqueness of the Abel boundary value refutes any mismatch once both
    boundary limits are supplied. -/
theorem G8EtaModTwoConditionalEtaIdentificationDespiteBoundaryMismatch.refutes
    (w : G8EtaModTwoConditionalEtaIdentificationDespiteBoundaryMismatch) :
    False :=
  w.mismatch (tendsto_nhds_unique w.lFunctionBoundary w.concreteBoundary)

end Tau.BookIII.Bridge
