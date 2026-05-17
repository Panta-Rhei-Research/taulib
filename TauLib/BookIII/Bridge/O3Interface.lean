import TauLib.BookIII.Bridge.LemniscateOperatorSpine

/-!
# TauLib.BookIII.Bridge.O3Interface

Experimental G6 hygiene paired with the G5 carrier sprint.

O3 is represented here as an explicit conditional interface.  This file adds no
axioms and proves no determinant representation; it merely names the fields a
future determinant/spectral-correspondence proof must supply.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

/-- Determinant class under discussion for an O3 attempt. -/
inductive DeterminantClass where
  | finite
  | fredholm
  | zetaRegularized
  | abstractConditional
  deriving Repr, DecidableEq

/-- How zero modes are handled in the determinant interface. -/
inductive ZeroModePolicy where
  | excluded
  | renormalized
  | retainedWithCorrection
  | unspecified
  deriving Repr, DecidableEq

/-- How zero/eigenvalue multiplicities are handled by the correspondence. -/
inductive MultiplicityPolicy where
  | preserved
  | ignored
  | boundedOnly
  | unspecified
  deriving Repr, DecidableEq

/-- Context data for a future O3 correspondence statement. -/
structure O3Context where
  operatorPackage : Type
  determinantClass : DeterminantClass
  zeroModePolicy : ZeroModePolicy
  multiplicityPolicy : MultiplicityPolicy
  status : SpineStatus := .conditional_interface

/-- Explicit O3 hypothesis interface.  Each field should eventually become a
    theorem-backed obligation, not a global ambient axiom.  This is a data
    record of named obligations rather than a `Prop`, so downstream code must
    choose explicitly which obligations it assumes. -/
structure O3Hypothesis (ctx : O3Context) where
  normalizationNonzero : Prop
  determinantDefined : Prop
  zeroSetEquivalence : Prop
  multiplicityCompatible : Prop
  zetaBridgeCompatible : Prop
  continuationCompatible : Prop

/-- The finite-first context recommended by the G5/G6 pre-flight addendum. -/
def finiteFirstO3Context : O3Context where
  operatorPackage := LemniscateOperatorDomain
  determinantClass := .finite
  zeroModePolicy := .excluded
  multiplicityPolicy := .boundedOnly

/-- The abstract conditional context used when a result should be stated with
    O3 as an explicit hypothesis rather than imported as ambient truth. -/
def abstractConditionalO3Context : O3Context where
  operatorPackage := LemniscateOperatorDomain
  determinantClass := .abstractConditional
  zeroModePolicy := .unspecified
  multiplicityPolicy := .unspecified

end Tau.BookIII.Bridge
