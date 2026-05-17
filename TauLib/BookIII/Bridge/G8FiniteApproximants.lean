import TauLib.BookIII.Bridge.FiniteSpectralDeterminant
import TauLib.BookIII.Bridge.G8ArithmeticCofinality

/-!
# TauLib.BookIII.Bridge.G8FiniteApproximants

G8b finite-approximant scaffold for the RH bridge proof program.

This module records the first safe approximant discipline after G8a:

* finite determinant approximants are the primary G8b bridge objects;
* primorial Euler-product-style approximants are comparison objects only;
* normalization, zero-mode, multiplicity, and pole/zero conventions are
  explicit data;
* no finite approximant is allowed to claim an orthodox `xi` zero divisor.

Everything here is finite bookkeeping.  There is no Fredholm determinant, no
zeta-regularized determinant, no analytic continuation, and no RH claim.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

open Tau.Polarity

-- ============================================================
-- APPROXIMANT ROLES AND CONVENTIONS
-- ============================================================

/-- Role of a finite approximant in the G8 proof program. -/
inductive G8bApproxRole where
  | primaryFiniteDeterminant
  | comparisonPrimorialEuler
  | diagnosticPlacebo
  deriving Repr, DecidableEq

/-- Finite normalization policy.  Infinite normalization remains a later G6/G8
    obligation. -/
inductive FiniteNormalizationPolicy where
  | finiteRawProduct
  | finiteRenormalizedByDeclaredFactor
  | unspecified
  deriving Repr, DecidableEq

/-- Pole/zero bookkeeping convention for a finite comparison object. -/
inductive PoleZeroConvention where
  | determinantZeroConvention
  | eulerPoleConvention
  | comparisonOnly
  | unspecified
  deriving Repr, DecidableEq

/-- Shared convention record for G8b finite approximants. -/
structure G8bApproxConventions where
  role : G8bApproxRole
  determinantClass : DeterminantClass
  zeroModePolicy : ZeroModePolicy
  multiplicityPolicy : MultiplicityPolicy
  spectralConvention : SpectralConvention
  normalizationPolicy : FiniteNormalizationPolicy
  poleZeroConvention : PoleZeroConvention
  deriving Repr

/-- The primary finite determinant convention selected for G8b. -/
def primaryFiniteDetConventions : G8bApproxConventions where
  role := .primaryFiniteDeterminant
  determinantClass := .finite
  zeroModePolicy := .excluded
  multiplicityPolicy := .boundedOnly
  spectralConvention := .finiteDiagonalProduct
  normalizationPolicy := .finiteRawProduct
  poleZeroConvention := .determinantZeroConvention

/-- Primorial Euler products are comparison objects.  They are not the primary
    determinant bridge and do not carry zero-divisor claims. -/
def primorialEulerComparisonConventions : G8bApproxConventions where
  role := .comparisonPrimorialEuler
  determinantClass := .finite
  zeroModePolicy := .unspecified
  multiplicityPolicy := .unspecified
  spectralConvention := .unspecified
  normalizationPolicy := .finiteRawProduct
  poleZeroConvention := .comparisonOnly

-- ============================================================
-- PRIMARY FINITE DETERMINANT APPROXIMANTS
-- ============================================================

/-- Primary G8b finite determinant family.

The actual determinant value is delegated to the G6 finite scaffold.  This
wrapper adds the G8a arithmetic context and records the finite conventions. -/
structure TauFiniteDetApproxFamily where
  cofinality : G8aArithmeticCofinalityContext := primorialG8aContext
  approx : TauFiniteDetApprox
  conventions : G8bApproxConventions := primaryFiniteDetConventions

/-- Build a primary finite determinant family from a cutoff and diagonal
    factor family. -/
def mkTauFiniteDetApproxFamily (cutoff : Nat) (factor : Nat → Nat) :
    TauFiniteDetApproxFamily where
  approx := mkTauFiniteDetApprox cutoff factor

/-- The primary finite determinant family uses the finite determinant role. -/
theorem mkTauFiniteDetApproxFamily_role (cutoff : Nat) (factor : Nat → Nat) :
    (mkTauFiniteDetApproxFamily cutoff factor).conventions.role =
      .primaryFiniteDeterminant :=
  rfl

/-- The primary finite determinant family uses a finite determinant class. -/
theorem mkTauFiniteDetApproxFamily_determinantClass
    (cutoff : Nat) (factor : Nat → Nat) :
    (mkTauFiniteDetApproxFamily cutoff factor).conventions.determinantClass =
      .finite :=
  rfl

/-- The primary finite determinant family excludes the zero mode at this finite
    scaffold level. -/
theorem mkTauFiniteDetApproxFamily_zeroModePolicy
    (cutoff : Nat) (factor : Nat → Nat) :
    (mkTauFiniteDetApproxFamily cutoff factor).conventions.zeroModePolicy =
      .excluded :=
  rfl

/-- The primary finite determinant family's value is the finite diagonal
    product from the G6 scaffold. -/
theorem mkTauFiniteDetApproxFamily_determinant_eq
    (cutoff : Nat) (factor : Nat → Nat) :
    (mkTauFiniteDetApproxFamily cutoff factor).approx.determinant =
      finiteDiagonalProduct cutoff factor :=
  rfl

-- ============================================================
-- PRIMORIAL EULER COMPARISON APPROXIMANTS
-- ============================================================

/-- The squarefree primorial stage itself as a finite arithmetic support. -/
def primorialStageSupport (stage : Nat) : TauFiniteArithmeticSupport where
  modulus := primorial stage
  stage := stage
  modulus_dvd_stage := dvd_refl (primorial stage)

/-- Finite primorial/Euler-style comparison approximant.

This object is useful for comparing prime-coordinate bookkeeping against the
finite determinant family.  Its role is explicitly `comparisonPrimorialEuler`,
not primary determinant bridge. -/
structure PrimorialEulerComparisonApprox where
  stage : Nat
  factor : Nat → Nat
  value : Nat := finiteDiagonalProduct stage factor
  support : TauFiniteArithmeticSupport := primorialStageSupport stage
  conventions : G8bApproxConventions := primorialEulerComparisonConventions

/-- Constructor for a primorial Euler comparison approximant. -/
def mkPrimorialEulerComparisonApprox (stage : Nat) (factor : Nat → Nat) :
    PrimorialEulerComparisonApprox where
  stage := stage
  factor := factor

/-- Primorial Euler approximants are comparison objects only. -/
theorem mkPrimorialEulerComparisonApprox_role
    (stage : Nat) (factor : Nat → Nat) :
    (mkPrimorialEulerComparisonApprox stage factor).conventions.role =
      .comparisonPrimorialEuler :=
  rfl

/-- Primorial Euler comparison approximants do not use a zero-divisor
    convention. -/
theorem mkPrimorialEulerComparisonApprox_poleZeroConvention
    (stage : Nat) (factor : Nat → Nat) :
    (mkPrimorialEulerComparisonApprox stage factor).conventions.poleZeroConvention =
      .comparisonOnly :=
  rfl

/-- The comparison approximant's support is visible at its own primorial
    stage. -/
theorem primorialEulerComparison_support_projection_compatible
    (A : PrimorialEulerComparisonApprox) (x : Nat) :
    A.support.residue (PrimorialStageProjection x A.support.stage) =
      A.support.residue x :=
  finiteSupport_projection_compatible A.support x

-- ============================================================
-- G8B CONTEXT AND GUARDRAILS
-- ============================================================

/-- Explicit G8b finite-approximant context.

This context is intentionally finite.  Downstream G8 work must still supply
analytic completion uniqueness, no-lost/no-spurious-zero theorems, and
multiplicity preservation before any orthodox `xi` divisor statement. -/
structure G8bFiniteApproximantContext where
  arithmetic : G8aArithmeticCofinalityContext := primorialG8aContext
  primaryFamily : Type 1 := TauFiniteDetApproxFamily
  comparisonFamily : Type := PrimorialEulerComparisonApprox
  primaryConventions : G8bApproxConventions := primaryFiniteDetConventions
  comparisonConventions : G8bApproxConventions := primorialEulerComparisonConventions
  finiteOnly : Prop := True
  noXiDivisorClaim : Prop := True
  noAnalyticCompletionClaim : Prop := True

/-- The theorem-backed G8b finite approximant context. -/
def finiteG8bContext : G8bFiniteApproximantContext where
  finiteOnly := True
  noXiDivisorClaim := True
  noAnalyticCompletionClaim := True

/-- G8b exposes no orthodox `xi` zero-divisor claim. -/
theorem finiteG8bContext_noXiDivisorClaim :
    finiteG8bContext.noXiDivisorClaim :=
  trivial

/-- G8b exposes no analytic-completion uniqueness claim. -/
theorem finiteG8bContext_noAnalyticCompletionClaim :
    finiteG8bContext.noAnalyticCompletionClaim :=
  trivial

end Tau.BookIII.Bridge
