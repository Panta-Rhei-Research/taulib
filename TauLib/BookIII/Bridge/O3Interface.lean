import TauLib.BookIII.Bridge.FiniteSpectralDeterminant

/-!
# TauLib.BookIII.Bridge.O3Interface

Experimental G6 hygiene paired with the G5 carrier sprint.

O3 is represented here as an explicit conditional interface.  This file adds no
axioms and proves no determinant representation; it merely names the fields a
future determinant/spectral-correspondence proof must supply.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

/-- Context data for a future O3 correspondence statement. -/
structure O3Context where
  operatorPackage : Type
  determinantClass : DeterminantClass
  spectralConvention : SpectralConvention := .unspecified
  zeroModePolicy : ZeroModePolicy
  multiplicityPolicy : MultiplicityPolicy
  operatorStatus : O3ObligationStatus := .scaffoldObligation
  determinantStatus : O3ObligationStatus := .scaffoldObligation
  normalizationStatus : O3ObligationStatus := .deferred
  zeroSetStatus : O3ObligationStatus := .deferred
  zetaBridgeStatus : O3ObligationStatus := .deferred
  continuationStatus : O3ObligationStatus := .deferred

/-- The operator package is at least named in the current O3 context. -/
def LemniscateOperatorReady (ctx : O3Context) : Prop :=
  ctx.operatorStatus = .theoremBacked ∨
    ctx.operatorStatus = .finiteCheck ∨
    ctx.operatorStatus = .definitionOnly ∨
    ctx.operatorStatus = .scaffoldObligation ∨
    ctx.operatorStatus = .hypothesis

/-- The determinant object is at least named at the selected determinant class. -/
def DeterminantDefined (ctx : O3Context) : Prop :=
  ctx.determinantStatus = .theoremBacked ∨
    ctx.determinantStatus = .finiteCheck ∨
    ctx.determinantStatus = .definitionOnly ∨
    ctx.determinantStatus = .scaffoldObligation ∨
    ctx.determinantStatus = .hypothesis

/-- The future normalizing factor has an explicit nonvanishing obligation. -/
def NormalizationNonzero (ctx : O3Context) : Prop :=
  ctx.normalizationStatus = .theoremBacked ∨
    ctx.normalizationStatus = .hypothesis

/-- The zero mode is not silently left unspecified. -/
def ZeroModePolicySatisfied (ctx : O3Context) : Prop :=
  ctx.zeroModePolicy ≠ .unspecified

/-- The zero-set equivalence is a named bridge obligation. -/
def ZeroSetEquivalence (ctx : O3Context) : Prop :=
  ctx.zeroSetStatus = .theoremBacked ∨
    ctx.zeroSetStatus = .hypothesis

/-- Multiplicity handling is not silently left unspecified. -/
def MultiplicityCompatible (ctx : O3Context) : Prop :=
  ctx.multiplicityPolicy ≠ .unspecified

/-- The τ-zeta bridge is a named prerequisite for O3. -/
def ZetaBridgeCompatible (ctx : O3Context) : Prop :=
  ctx.zetaBridgeStatus = .theoremBacked ∨
    ctx.zetaBridgeStatus = .hypothesis

/-- The analytic continuation bridge is a named prerequisite for O3. -/
def ContinuationCompatible (ctx : O3Context) : Prop :=
  ctx.continuationStatus = .theoremBacked ∨
    ctx.continuationStatus = .hypothesis

/-- The finite determinant scaffold is the first finite correspondence target. -/
def FiniteCorrespondenceBridge (ctx : O3Context) : Prop :=
  ctx.determinantClass = .finite ∧ ctx.zeroModePolicy = .excluded

/-- Explicit O3 obligation package.  This structure is a `Prop`: to use O3,
    downstream code must carry proofs of named obligations instead of receiving
    an ambient determinant-correspondence axiom. -/
structure O3Obligations (ctx : O3Context) : Prop where
  operatorReady : LemniscateOperatorReady ctx
  determinantDefined : DeterminantDefined ctx
  normalizationNonzero : NormalizationNonzero ctx
  zeroModeHandled : ZeroModePolicySatisfied ctx
  zeroSetEquivalence : ZeroSetEquivalence ctx
  multiplicityCompatible : MultiplicityCompatible ctx
  zetaBridgeCompatible : ZetaBridgeCompatible ctx
  continuationCompatible : ContinuationCompatible ctx
  finiteCorrespondence : FiniteCorrespondenceBridge ctx

/-- Backwards-compatible name for the explicit obligation package. -/
abbrev O3Hypothesis (ctx : O3Context) : Prop :=
  O3Obligations ctx

/-- The finite-first context recommended by the G5/G6 pre-flight addendum. -/
def finiteFirstO3Context : O3Context where
  operatorPackage := LemniscateOperatorDomain
  determinantClass := .finite
  spectralConvention := .identityMinusLambdaInverse
  zeroModePolicy := .excluded
  multiplicityPolicy := .boundedOnly
  operatorStatus := .scaffoldObligation
  determinantStatus := .finiteCheck
  normalizationStatus := .deferred
  zeroSetStatus := .deferred
  zetaBridgeStatus := .deferred
  continuationStatus := .deferred

/-- The abstract conditional context used when a result should be stated with
    O3 as an explicit hypothesis rather than imported as ambient truth. -/
def abstractConditionalO3Context : O3Context where
  operatorPackage := LemniscateOperatorDomain
  determinantClass := .abstractConditional
  spectralConvention := .unspecified
  zeroModePolicy := .unspecified
  multiplicityPolicy := .unspecified
  operatorStatus := .hypothesis
  determinantStatus := .hypothesis
  normalizationStatus := .hypothesis
  zeroSetStatus := .hypothesis
  zetaBridgeStatus := .hypothesis
  continuationStatus := .hypothesis

end Tau.BookIII.Bridge
