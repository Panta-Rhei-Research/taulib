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

/-- Spectral determinant convention under discussion.  The regularized target
    is deliberately unresolved at G6.0. -/
inductive SpectralConvention where
  | hMinusLambda
  | identityMinusLambdaInverse
  | sMinusOperator
  | finiteDiagonalProduct
  | unspecified
  deriving Repr, DecidableEq

/-- Context data for a future O3 correspondence statement. -/
structure O3Context where
  operatorPackage : Type
  determinantClass : DeterminantClass
  zeroModePolicy : ZeroModePolicy
  multiplicityPolicy : MultiplicityPolicy
  spectralConvention : SpectralConvention := .unspecified
  normalizationNonzeroPredicate : Prop := False
  determinantDefinedPredicate : Prop := False
  zeroSetEquivalencePredicate : Prop := False
  multiplicityCompatiblePredicate : Prop := False
  zetaBridgeCompatiblePredicate : Prop := False
  continuationCompatiblePredicate : Prop := False
  status : SpineStatus := .conditional_interface

/-- Named O3 obligation: determinant normalization is fixed and nonvanishing
    on the zero-bearing comparison domain. -/
def O3NormalizationNonzero (ctx : O3Context) : Prop :=
  ctx.normalizationNonzeroPredicate

/-- Named O3 obligation: the selected determinant class is actually defined for
    the selected operator package. -/
def O3DeterminantDefined (ctx : O3Context) : Prop :=
  ctx.determinantDefinedPredicate

/-- Named O3 obligation: determinant zeros match the intended spectral zeros. -/
def O3ZeroSetEquivalence (ctx : O3Context) : Prop :=
  ctx.zeroSetEquivalencePredicate

/-- Named O3 obligation: multiplicities are handled according to the declared
    multiplicity policy. -/
def O3MultiplicityCompatible (ctx : O3Context) : Prop :=
  ctx.multiplicityCompatiblePredicate

/-- Named O3 obligation: the determinant comparison is compatible with the G3
    zeta bridge. -/
def O3ZetaBridgeCompatible (ctx : O3Context) : Prop :=
  ctx.zetaBridgeCompatiblePredicate

/-- Named O3 obligation: the determinant comparison is compatible with the G4
    continuation/functional-equation layer. -/
def O3ContinuationCompatible (ctx : O3Context) : Prop :=
  ctx.continuationCompatiblePredicate

/-- Explicit O3 proof-field interface.  A value of this structure is not
    supplied in this sprint; downstream theorem statements may require it as a
    hypothesis instead of importing the legacy ambient O3 axiom. -/
structure O3Obligations (ctx : O3Context) where
  normalizationNonzero : O3NormalizationNonzero ctx
  determinantDefined : O3DeterminantDefined ctx
  zeroSetEquivalence : O3ZeroSetEquivalence ctx
  multiplicityCompatible : O3MultiplicityCompatible ctx
  zetaBridgeCompatible : O3ZetaBridgeCompatible ctx
  continuationCompatible : O3ContinuationCompatible ctx

/-- Backward-compatible name for code that already speaks of an O3 hypothesis. -/
abbrev O3Hypothesis (ctx : O3Context) : Prop :=
  O3Obligations ctx

/-- The spectral-correspondence proposition exposed to downstream consumers.
    This is intentionally conditional and local to a context. -/
def SpectralCorrespondenceO3 (ctx : O3Context) : Prop :=
  O3ZeroSetEquivalence ctx ∧ O3MultiplicityCompatible ctx

/-- Adapter from explicit obligations to the local O3 spectral-correspondence
    proposition. -/
theorem spectral_corr_from_hyp (ctx : O3Context) (h : O3Obligations ctx) :
    SpectralCorrespondenceO3 ctx :=
  ⟨h.zeroSetEquivalence, h.multiplicityCompatible⟩

/-- The finite-first context recommended by the G5/G6 pre-flight addendum. -/
def finiteFirstO3Context : O3Context where
  operatorPackage := LemniscateOperatorDomain
  determinantClass := .finite
  zeroModePolicy := .excluded
  multiplicityPolicy := .boundedOnly
  spectralConvention := .finiteDiagonalProduct

/-- The abstract conditional context used when a result should be stated with
    O3 as an explicit hypothesis rather than imported as ambient truth. -/
def abstractConditionalO3Context : O3Context where
  operatorPackage := LemniscateOperatorDomain
  determinantClass := .abstractConditional
  zeroModePolicy := .unspecified
  multiplicityPolicy := .unspecified

end Tau.BookIII.Bridge
