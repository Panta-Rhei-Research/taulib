import TauLib.BookIII.Bridge.G8EtaModTwoOpenUnitContinuation

/-!
# TauLib.BookIII.Bridge.G8EtaModTwoHurwitzOpenUnitProduct

Hurwitz-normalized open-unit product surface for the Lane-A eta bridge.

The safe right-half-plane product identity is theorem-backed in
`G8EtaModTwoRightHalfPlaneProduct`.  This module records the exact
Hurwitz-zeta model of the mod-two `ZMod.LFunction` and packages the remaining
open-unit product continuation as a proof-carrying Hurwitz evidence object.

No result here uses RH, accepted coverage, the final live hinge, O3, full
divisor transfer, or analytic-completion uniqueness.
-/

set_option autoImplicit false

noncomputable section

namespace Tau.BookIII.Bridge

open Complex Filter

open scoped BigOperators Topology

-- ============================================================
-- HURWITZ NORMAL FORM
-- ============================================================

/-- The explicit Hurwitz-zeta model of the mod-two eta L-function. -/
def g8EtaModTwoHurwitzOpenUnitModel (s : ℂ) : ℂ :=
  (2 : ℂ) ^ (-s) *
    ∑ j : ZMod 2,
      g8EtaModTwoCoeff j *
        HurwitzZeta.hurwitzZeta (ZMod.toAddCircle j) s

/-- The mod-two eta `LFunction` is definitionally the Hurwitz-normalized
    finite residue-class sum. -/
theorem g8EtaModTwoLFunction_eq_hurwitzOpenUnitModel (s : ℂ) :
    g8EtaModTwoLFunction s =
      g8EtaModTwoHurwitzOpenUnitModel s := by
  rfl

/-- The zero residue contributes the negative Hurwitz branch. -/
theorem g8EtaModTwoCoeff_zeroResidue :
    g8EtaModTwoCoeff (0 : ZMod 2) = -1 :=
  g8EtaModTwoCoeff_zero

/-- The one residue contributes the positive Hurwitz branch. -/
theorem g8EtaModTwoCoeff_oneResidue :
    g8EtaModTwoCoeff (1 : ZMod 2) = 1 :=
  g8EtaModTwoCoeff_one

/-- The coefficient has zero average, the differentiability gate for Mathlib's
    mod-two L-function continuation. -/
theorem g8EtaModTwoCoeff_zeroAverage :
    (∑ j : ZMod 2, g8EtaModTwoCoeff j) = 0 :=
  g8EtaModTwoCoeff_sum_zero

/-- The Hurwitz-normalized model inherits the theorem-backed safe-half-plane
    product identity from the mod-two L-function. -/
theorem g8EtaModTwoHurwitzProductIdentityOnRightHalfPlane :
    G8EtaModTwoLFunctionProductIdentityOnRightHalfPlane := by
  intro s hs
  exact {
    productIdentity :=
      (g8EtaModTwoLFunctionProductIdentityOnRightHalfPlane_theorem
        s hs).productIdentity
  }

/-- The Hurwitz-normalized model satisfies the open-unit product identity
    theorem-backed, via analytic continuation of the mod-two `LFunction`
    product identity. -/
theorem g8EtaModTwoHurwitz_openUnitProductIdentity
    (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    g8EtaModTwoHurwitzOpenUnitModel (x : ℂ) =
      (g8DirichletEtaDenominator x : ℂ) * riemannZeta (x : ℂ) := by
  rw [← g8EtaModTwoLFunction_eq_hurwitzOpenUnitModel]
  exact g8EtaModTwoLFunction_openUnitProductIdentity x hx0 hx1

-- ============================================================
-- OPEN-UNIT PRODUCT CONTINUATION EVIDENCE
-- ============================================================

/-- Hurwitz-side evidence needed to continue the theorem-backed right-half-plane
    product identity to the real open unit interval.  The fields are exactly the
    analytic payload: real-valued zeta readout and the Hurwitz model product
    identity on `0 < x < 1`. -/
structure G8EtaModTwoHurwitzProductContinuationEvidence where
  zetaReal :
    ∀ (x : ℝ), 0 < x → x < 1 →
      (riemannZeta (x : ℂ)).im = 0
  hurwitzOpenUnitProduct :
    ∀ (x : ℝ), 0 < x → x < 1 →
      g8EtaModTwoHurwitzOpenUnitModel (x : ℂ) =
        (g8DirichletEtaDenominator x : ℂ) * riemannZeta (x : ℂ)

/-- After closing the product continuation theorem-backed, real-valued zeta
    readout is exactly sufficient for the Hurwitz evidence object. -/
def G8EtaModTwoHurwitzProductContinuationEvidence.ofZetaReal
    (hZetaReal : G8RiemannZetaRealOnOpenUnit) :
    G8EtaModTwoHurwitzProductContinuationEvidence where
  zetaReal := hZetaReal
  hurwitzOpenUnitProduct :=
    g8EtaModTwoHurwitz_openUnitProductIdentity

/-- The Hurwitz evidence object is exactly sufficient for the existing
    open-unit product-continuation target. -/
def G8EtaModTwoHurwitzProductContinuationEvidence.toProductContinuation
    (evidence : G8EtaModTwoHurwitzProductContinuationEvidence) :
    G8EtaModTwoProductContinuationToOpenUnit
      g8EtaModTwoLFunctionProductIdentityOnRightHalfPlane_theorem where
  zetaReal := evidence.zetaReal
  openUnitProduct := by
    intro x hx0 hx1
    rw [g8EtaModTwoLFunction_eq_hurwitzOpenUnitModel]
    exact evidence.hurwitzOpenUnitProduct x hx0 hx1

/-- Hurwitz evidence supplies the existing open-unit product identity. -/
theorem G8EtaModTwoHurwitzProductContinuationEvidence.toOpenUnitProduct
    (evidence : G8EtaModTwoHurwitzProductContinuationEvidence) :
    G8EtaModTwoLFunctionProductIdentityOnOpenUnit :=
  evidence.toProductContinuation.toOpenUnitProduct

/-- Named open-unit product target after Hurwitz normalization. -/
abbrev G8EtaModTwoHurwitzOpenUnitProductTarget : Prop :=
  G8EtaModTwoHurwitzProductContinuationEvidence

-- ============================================================
-- RED-TEAM FALSIFIERS
-- ============================================================

/-- A point where the Hurwitz-normalized model fails the open-unit product
    identity refutes the Hurwitz continuation evidence. -/
structure G8EtaModTwoHurwitzOpenUnitProductMismatch where
  x : ℝ
  pos : 0 < x
  lt_one : x < 1
  mismatch :
    g8EtaModTwoHurwitzOpenUnitModel (x : ℂ) ≠
      (g8DirichletEtaDenominator x : ℂ) * riemannZeta (x : ℂ)

/-- A Hurwitz product mismatch refutes the Hurwitz continuation evidence. -/
theorem G8EtaModTwoHurwitzOpenUnitProductMismatch.refutes
    (w : G8EtaModTwoHurwitzOpenUnitProductMismatch)
    (evidence : G8EtaModTwoHurwitzProductContinuationEvidence) :
    False :=
  w.mismatch (evidence.hurwitzOpenUnitProduct w.x w.pos w.lt_one)

/-- Missing Hurwitz product continuation refutes any Hurwitz evidence object. -/
structure G8EtaModTwoMissingHurwitzOpenUnitProduct where
  missing : ¬ G8EtaModTwoHurwitzOpenUnitProductTarget

/-- Missing Hurwitz product continuation refutes supplied evidence. -/
theorem G8EtaModTwoMissingHurwitzOpenUnitProduct.refutes
    (w : G8EtaModTwoMissingHurwitzOpenUnitProduct)
    (evidence : G8EtaModTwoHurwitzProductContinuationEvidence) :
    False :=
  w.missing evidence

end Tau.BookIII.Bridge
