/-!
# TauLib.BookIII.Bridge.O3Status

Neutral status labels for the G6 O3 interface.

This module is intentionally small and τ-native.  It records obligation labels
and policy choices without importing mathematical determinant infrastructure
or asserting the O3 correspondence.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

/-- Source/proof status for an O3 obligation. -/
inductive O3ObligationStatus where
  | theoremBacked
  | finiteCheck
  | definitionOnly
  | scaffoldObligation
  | hypothesis
  | docstringOnly
  | deferred
  deriving Repr, DecidableEq

/-- Determinant class under discussion for an O3 attempt. -/
inductive DeterminantClass where
  | finite
  | fredholm
  | zetaRegularized
  | abstractConditional
  deriving Repr, DecidableEq

/-- Spectral variable convention for a determinant-correspondence statement. -/
inductive SpectralConvention where
  | operatorMinusLambda
  | identityMinusLambdaInverse
  | scalarMinusOperator
  | unspecified
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
  | ramifiedAtCenter
  | boundedOnly
  | ignored
  | unspecified
  deriving Repr, DecidableEq

/-- Role of a dependency relative to the O3 bridge. -/
inductive DependencyRole where
  | prerequisite
  | finiteScaffold
  | downstreamConsumer
  | compatibilityObligation
  | deferred
  deriving Repr, DecidableEq

end Tau.BookIII.Bridge
