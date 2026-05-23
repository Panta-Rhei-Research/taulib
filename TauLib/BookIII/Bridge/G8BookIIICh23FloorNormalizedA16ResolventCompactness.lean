import TauLib.BookIII.Bridge.G8BookIIICh23FloorNormalizedA16CompactEmbedding

/-!
# G8 Book III Ch.23 Floor-Normalized A1.6 Resolvent Compactness

This module packages the second A1.6 analytic stone:

```text
compact operator-domain embedding
  + coercive resolvent regularity at -1
  -> compact resolvent
```

The actual coercive/Lax-Milgram and elliptic-regularity theorem is kept as an
explicit source field unless a later Mathlib-backed proof supplies it.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

-- ============================================================
-- COERCIVE RESOLVENT REGULARITY
-- ============================================================

/-- Proof-facing regularity source for the safe resolvent point `-1`.

For the nonnegative Kirchhoff Laplacian, this is the usual `(H_L + 1)^{-1}`
route: solve the weak equation, upgrade to the selected operator domain, and
obtain a graph-norm bound. -/
structure
    G8BookIIICh23FloorNormalizedA16CoerciveResolventRegularitySource
    where
  embedding :
    G8BookIIICh23FloorNormalizedA16RellichCompactEmbeddingSource
  safeResolventPoint : ℂ := (-1 : ℂ)
  nonnegativeSelfAdjointInput : Prop
  nonnegativeSelfAdjointInputWitness :
    nonnegativeSelfAdjointInput
  resolventExistsAtSafePoint : Prop
  resolventExistsAtSafePointWitness :
    resolventExistsAtSafePoint
  resolventMapsL2ToSelectedOperatorDomain : Prop
  resolventMapsL2ToSelectedOperatorDomainWitness :
    resolventMapsL2ToSelectedOperatorDomain
  resolventBoundedForGraphNorm : Prop
  resolventBoundedForGraphNormWitness :
    resolventBoundedForGraphNorm
  weakSolutionCoercivity : Prop
  weakSolutionCoercivityWitness :
    weakSolutionCoercivity
  edgewiseEllipticRegularity : Prop
  edgewiseEllipticRegularityWitness :
    edgewiseEllipticRegularity
  status : SpineStatus := .conditional_interface

/-- Exact regularity target if the coercive resolvent proof is the remaining
    analytic payload. -/
def
    G8BookIIICh23FloorNormalizedA16CoerciveResolventRegularityTarget :
    Prop :=
  Nonempty
    G8BookIIICh23FloorNormalizedA16CoerciveResolventRegularitySource

/-- A regularity source proves its target. -/
theorem
    G8BookIIICh23FloorNormalizedA16CoerciveResolventRegularitySource.toTarget
    (source :
      G8BookIIICh23FloorNormalizedA16CoerciveResolventRegularitySource) :
    G8BookIIICh23FloorNormalizedA16CoerciveResolventRegularityTarget :=
  ⟨source⟩

-- ============================================================
-- COMPACT RESOLVENT SOURCE
-- ============================================================

/-- Compact-resolvent source for the selected floor-normalized Ch.23
    Kirchhoff operator. -/
structure G8BookIIICh23FloorNormalizedA16ResolventCompactnessSource
    where
  regularity :
    G8BookIIICh23FloorNormalizedA16CoerciveResolventRegularitySource
  compactEmbeddingWitness :
    regularity.embedding.compactEmbedding
  resolventFactorsThroughCompactEmbedding : Prop
  resolventFactorsThroughCompactEmbeddingWitness :
    resolventFactorsThroughCompactEmbedding
  compactResolvent : Prop
  compactResolventWitness : compactResolvent
  compactResolventUsesMinusOneNotFiniteDiagnostics : Prop
  compactResolventUsesMinusOneNotFiniteDiagnosticsWitness :
    compactResolventUsesMinusOneNotFiniteDiagnostics
  status : SpineStatus := .conditional_interface

/-- Selected compact-resolvent target. -/
def G8BookIIICh23FloorNormalizedA16ResolventCompactnessTarget :
    Prop :=
  Nonempty G8BookIIICh23FloorNormalizedA16ResolventCompactnessSource

/-- A compact-resolvent source proves its target. -/
theorem
    G8BookIIICh23FloorNormalizedA16ResolventCompactnessSource.toTarget
    (source :
      G8BookIIICh23FloorNormalizedA16ResolventCompactnessSource) :
    G8BookIIICh23FloorNormalizedA16ResolventCompactnessTarget :=
  ⟨source⟩

/-- Build compact resolvent from coercive regularity once the factorization
    through the compact embedding is supplied. -/
def
    G8BookIIICh23FloorNormalizedA16CoerciveResolventRegularitySource.toResolventCompactnessSource
    (source :
      G8BookIIICh23FloorNormalizedA16CoerciveResolventRegularitySource)
    (resolventFactorsThroughCompactEmbedding : Prop)
    (resolventFactorsThroughCompactEmbeddingWitness :
      resolventFactorsThroughCompactEmbedding)
    (compactResolvent : Prop)
    (compactResolventWitness : compactResolvent)
    (compactResolventUsesMinusOneNotFiniteDiagnostics : Prop)
    (compactResolventUsesMinusOneNotFiniteDiagnosticsWitness :
      compactResolventUsesMinusOneNotFiniteDiagnostics) :
    G8BookIIICh23FloorNormalizedA16ResolventCompactnessSource where
  regularity := source
  compactEmbeddingWitness := source.embedding.compactEmbeddingEvidence
  resolventFactorsThroughCompactEmbedding :=
    resolventFactorsThroughCompactEmbedding
  resolventFactorsThroughCompactEmbeddingWitness :=
    resolventFactorsThroughCompactEmbeddingWitness
  compactResolvent := compactResolvent
  compactResolventWitness := compactResolventWitness
  compactResolventUsesMinusOneNotFiniteDiagnostics :=
    compactResolventUsesMinusOneNotFiniteDiagnostics
  compactResolventUsesMinusOneNotFiniteDiagnosticsWitness :=
    compactResolventUsesMinusOneNotFiniteDiagnosticsWitness
  status := source.status

-- ============================================================
-- GUARDRAILS
-- ============================================================

/-- Resolvent existence without compact embedding does not prove compact
    resolvent. -/
structure
    G8BookIIICh23FloorNormalizedA16ResolventWithoutCompactEmbedding
    (source :
      G8BookIIICh23FloorNormalizedA16CoerciveResolventRegularitySource)
    where
  missingCompactEmbedding :
    ¬ source.embedding.compactEmbedding

theorem
    G8BookIIICh23FloorNormalizedA16ResolventWithoutCompactEmbedding.refutes
    {source :
      G8BookIIICh23FloorNormalizedA16CoerciveResolventRegularitySource}
    (gap :
      G8BookIIICh23FloorNormalizedA16ResolventWithoutCompactEmbedding
        source) :
    False :=
  gap.missingCompactEmbedding
    source.embedding.compactEmbeddingEvidence

/-- A finite eigenvalue check is not a compact-resolvent factorization. -/
structure
    G8BookIIICh23FloorNormalizedA16FiniteCheckWithoutResolventFactorization
    where
  finiteCheck : Prop
  finiteCheckWitness : finiteCheck
  noResolventFactorization :
    ¬ G8BookIIICh23FloorNormalizedA16ResolventCompactnessTarget

theorem
    G8BookIIICh23FloorNormalizedA16FiniteCheckWithoutResolventFactorization.refutes
    (gap :
      G8BookIIICh23FloorNormalizedA16FiniteCheckWithoutResolventFactorization)
    (target :
      G8BookIIICh23FloorNormalizedA16ResolventCompactnessTarget) :
    False :=
  gap.noResolventFactorization target

end Tau.BookIII.Bridge
