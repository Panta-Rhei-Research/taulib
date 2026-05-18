import TauLib.BookIII.Bridge.G8FiniteApproximants
import TauLib.BookIII.Bridge.ZetaAsChart

/-!
# TauLib.BookIII.Bridge.G8CompletionUniqueness

G8c analytic-completion uniqueness scaffold for the RH bridge proof program.

G8a records arithmetic cofinality.  G8b records finite approximant discipline.
This module names the next obstruction: a finite tau tower and its finite
approximants must determine a unique normalized receiving-side analytic
completion before any orthodox `xi` divisor statement can be transported.

Everything here is an interface or a guardrail.  There is no analytic
continuation proof, no determinant correspondence proof, no zero-divisor
transfer theorem, and no RH claim.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

-- ============================================================
-- COMPLETION CANDIDATES AND POLICIES
-- ============================================================

/-- Normalization policy for a candidate analytic completion.

The G8 obstruction is partly a normalization problem: two completions are not
comparable until pole/zero and scaling conventions have been fixed. -/
inductive AnalyticCompletionNormalization where
  | normalizedXiChart
  | normalizedDeterminantChart
  | finiteApproximationOnly
  | unspecified
  deriving Repr, DecidableEq

/-- Status label for the uniqueness problem. -/
inductive CompletionUniquenessStatus where
  | openObligation
  | conditionalInterface
  | countermodelPressure
  | uniquenessHypothesisAvailable
  deriving Repr, DecidableEq

/-- Candidate analytic completion record.

The payload types are deliberately abstract.  A future implementation may
instantiate them with completed zeta/xi charts, determinant limits, or another
receiving-side invariant, but this scaffold does not choose one. -/
structure TauAnalyticCompletionCandidate where
  tauTowerData : Type 1
  finiteApproximationData : Type 1 := TauFiniteDetApproxFamily
  receivingAnalyticObject : Type 1
  receivingDivisorObject : Type 1
  normalization : AnalyticCompletionNormalization := .unspecified
  finiteCompatible : Prop := False
  chartCompatible : Prop := False
  determinantCompatible : Prop := False
  deriving Repr

/-- A candidate is normalized when it no longer uses the intentionally
    unresolved normalization label. -/
def CompletionCandidateNormalized
    (C : TauAnalyticCompletionCandidate) : Prop :=
  C.normalization ≠ .unspecified

/-- A candidate is compatible with the already-scaffolded finite layer. -/
def CompletionCandidateFiniteCompatible
    (C : TauAnalyticCompletionCandidate) : Prop :=
  C.finiteCompatible

/-- A candidate is compatible with the receiving zeta/xi chart layer. -/
def CompletionCandidateChartCompatible
    (C : TauAnalyticCompletionCandidate) : Prop :=
  C.chartCompatible

/-- A candidate is compatible with the determinant/O3 layer. -/
def CompletionCandidateDeterminantCompatible
    (C : TauAnalyticCompletionCandidate) : Prop :=
  C.determinantCompatible

/-- Minimal admissibility for a completion candidate at G8c.

This is not enough for an RH argument.  It only says the candidate has passed
the local bookkeeping gates that make a uniqueness question meaningful. -/
def CompletionCandidateAdmissible
    (C : TauAnalyticCompletionCandidate) : Prop :=
  CompletionCandidateNormalized C ∧
  CompletionCandidateFiniteCompatible C ∧
  CompletionCandidateChartCompatible C ∧
  CompletionCandidateDeterminantCompatible C

/-- A finite-only candidate is normalized but remains deliberately below the
    analytic-completion threshold. -/
def finiteOnlyCompletionCandidate
    (receivingAnalyticObject receivingDivisorObject : Type 1) :
    TauAnalyticCompletionCandidate where
  tauTowerData := TauFiniteDetApproxFamily
  receivingAnalyticObject := receivingAnalyticObject
  receivingDivisorObject := receivingDivisorObject
  normalization := .finiteApproximationOnly
  finiteCompatible := True
  chartCompatible := False
  determinantCompatible := False

/-- Finite-only candidates are normalized as finite approximants, not as
    completed analytic objects. -/
theorem finiteOnlyCompletionCandidate_normalized
    (A D : Type 1) :
    CompletionCandidateNormalized (finiteOnlyCompletionCandidate A D) := by
  intro h
  cases h

/-- Finite-only candidates expose finite compatibility. -/
theorem finiteOnlyCompletionCandidate_finiteCompatible
    (A D : Type 1) :
    CompletionCandidateFiniteCompatible (finiteOnlyCompletionCandidate A D) :=
  trivial

/-- Finite-only candidates do not provide the receiving zeta/xi chart
    compatibility required by G8c. -/
theorem finiteOnlyCompletionCandidate_not_chartCompatible
    (A D : Type 1) :
    ¬ CompletionCandidateChartCompatible (finiteOnlyCompletionCandidate A D) := by
  intro h
  exact h

/-- Finite-only candidates do not provide the determinant/O3 compatibility
    required by G8c. -/
theorem finiteOnlyCompletionCandidate_not_determinantCompatible
    (A D : Type 1) :
    ¬ CompletionCandidateDeterminantCompatible
      (finiteOnlyCompletionCandidate A D) := by
  intro h
  exact h

/-- Finite-only candidates cannot be promoted to G8c-admissible analytic
    completions without additional chart and determinant bridge data. -/
theorem finiteOnlyCompletionCandidate_not_admissible
    (A D : Type 1) :
    ¬ CompletionCandidateAdmissible (finiteOnlyCompletionCandidate A D) := by
  intro h
  exact finiteOnlyCompletionCandidate_not_chartCompatible A D h.right.right.left

-- ============================================================
-- G8C UNIQUENESS CONTEXT
-- ============================================================

/-- G8c context: the local shape of analytic-completion uniqueness.

The relation fields define what it means for two candidate completions to have
the same tau tower, same finite approximants, and different receiving divisors.
The `chart` field imports the already-explicit G3/G4/G5/G6/G8 obligations from
`ZetaAsChart`; this module adds the non-uniqueness falsifier discipline around
those obligations. -/
structure G8cCompletionUniquenessContext where
  finiteContext : G8bFiniteApproximantContext := finiteG8bContext
  chart : ZetaAsCoordinateChartContext
  candidateType : Type 2 := TauAnalyticCompletionCandidate
  sameTauTower : candidateType → candidateType → Prop
  sameFiniteApproximants : candidateType → candidateType → Prop
  differentReceivingDivisor : candidateType → candidateType → Prop
  candidateAdmissible : candidateType → Prop
  completionUnique : Prop
  status : CompletionUniquenessStatus := .openObligation

/-- A concrete non-uniqueness witness for the standing G8c red-team test. -/
structure G8cNonuniqueCompletionWitness
    (ctx : G8cCompletionUniquenessContext) where
  left : ctx.candidateType
  right : ctx.candidateType
  leftAdmissible : ctx.candidateAdmissible left
  rightAdmissible : ctx.candidateAdmissible right
  sameTower : ctx.sameTauTower left right
  sameFinite : ctx.sameFiniteApproximants left right
  differentDivisor : ctx.differentReceivingDivisor left right

/-- The standing G8c falsifier is absent exactly when no non-unique completion
    witness exists in the declared context. -/
def G8cNoNonuniqueCompletion
    (ctx : G8cCompletionUniquenessContext) : Prop :=
  ¬ Nonempty (G8cNonuniqueCompletionWitness ctx)

/-- A found non-uniqueness witness refutes the no-countermodel guardrail. -/
theorem g8c_witness_refutes_noNonuniqueCompletion
    (ctx : G8cCompletionUniquenessContext)
    (w : G8cNonuniqueCompletionWitness ctx) :
    ¬ G8cNoNonuniqueCompletion ctx := by
  intro h
  exact h ⟨w⟩

/-- Zero-divisor transfer is admissible only when the zeta-as-chart hypotheses
    and the G8c non-uniqueness guardrail are both present. -/
def G8cZeroDivisorTransferAdmissible
    (ctx : G8cCompletionUniquenessContext) : Prop :=
  ZeroDivisorClaimsAdmissible ctx.chart ∧
  G8cNoNonuniqueCompletion ctx

/-- Any G8c-admissible zero-divisor transfer exposes analytic-completion
    uniqueness from the zeta-as-chart context. -/
theorem g8c_transfer_requires_completionUnique
    (ctx : G8cCompletionUniquenessContext)
    (h : G8cZeroDivisorTransferAdmissible ctx) :
    tauTower_analyticCompletion_unique ctx.chart :=
  zeroDivisorClaimsAdmissible_completionUnique ctx.chart h.left

/-- Any G8c-admissible zero-divisor transfer exposes the standing
    non-uniqueness falsifier guardrail. -/
theorem g8c_transfer_requires_noNonuniqueCompletion
    (ctx : G8cCompletionUniquenessContext)
    (h : G8cZeroDivisorTransferAdmissible ctx) :
    G8cNoNonuniqueCompletion ctx :=
  h.right

/-- The context's local uniqueness field is a named obligation, not a proof
    manufactured by this module. -/
def G8cLocalCompletionUnique
    (ctx : G8cCompletionUniquenessContext) : Prop :=
  ctx.completionUnique

end Tau.BookIII.Bridge
