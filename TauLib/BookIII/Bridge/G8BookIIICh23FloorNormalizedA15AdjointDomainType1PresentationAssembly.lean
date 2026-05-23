import TauLib.BookIII.Bridge.G8BookIIICh23FloorNormalizedA15Type1PresentationEngine

/-!
# G8 Book III Ch.23 Floor-Normalized A1.5 Adjoint-Domain Type-1 Presentation Assembly

This module constructs the next exact A1.5 stepping stone.

The previous layer isolated the target

```text
G8BookIIICh23FloorNormalizedA15AdjointDomainType1PresentationSource
```

as the source needed by the concrete adjoint-calculus engine.  This file
assembles that source from precisely the two load-bearing inputs now visible
in the proof map:

```text
exhaustive Type-1 presentation of the selected Kirchhoff domain
  + adjoint-domain reverse-inclusion proof stones
  -> adjoint-domain Type-1 presentation source
```

The construction is deliberately not a proof of either input.  It is the
strict adapter saying that once the small presentation and reverse-inclusion
proof stones are supplied, the A1.5 concrete engine receives exactly the
candidate/test universe it asked for.

No compact resolvent, A2 point spectrum, A3 actual-`xi`, accepted coverage, or
RH-facing statement is imported or proved here.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

-- ============================================================
-- REVERSE-INCLUSION TARGET EXPOSED AT THE TYPE-1 PRESENTATION LEVEL
-- ============================================================

/-- The reverse-inclusion target needed by the Type-1 adjoint-domain
    presentation layer. -/
def
    G8BookIIICh23FloorNormalizedA15AdjointDomainReverseInclusionTarget :
    Prop :=
  Nonempty
    G8BookIIICh23FloorNormalizedA15AdjointDomainContainedInKirchhoffDomainSource

/-- A full adjoint-domain Type-1 presentation source contains the
    reverse-inclusion source. -/
theorem
    G8BookIIICh23FloorNormalizedA15AdjointDomainType1PresentationSource.toReverseInclusionTarget
    (source :
      G8BookIIICh23FloorNormalizedA15AdjointDomainType1PresentationSource) :
    G8BookIIICh23FloorNormalizedA15AdjointDomainReverseInclusionTarget :=
  ⟨source.reverseInclusion⟩

/-- A proof-stone source supplies the reverse-inclusion target. -/
theorem
    G8BookIIICh23FloorNormalizedA15AdjointDomainExhaustionProofStoneSource.toReverseInclusionTarget
    (source :
      G8BookIIICh23FloorNormalizedA15AdjointDomainExhaustionProofStoneSource) :
    G8BookIIICh23FloorNormalizedA15AdjointDomainReverseInclusionTarget :=
  ⟨source.reverseInclusion⟩

-- ============================================================
-- EXACT ALIGNMENT BETWEEN SMALL PRESENTATION AND REVERSE INCLUSION
-- ============================================================

/-- The exact alignment assertion used when the reverse-inclusion proof stones
    are consumed through a small Type-1 presentation.

This is not an additional analytic theorem.  It records the three facts that
the assembled source actually uses:

* the Type-1 presentation exhausts the selected Kirchhoff domain;
* the reverse inclusion gives exact domain equality with the closed A1.4
  forward inclusion;
* graph-`H2` recovery has been supplied by the reverse-inclusion proof stones.
-/
def
    G8BookIIICh23FloorNormalizedA15ReverseInclusionUsesType1Presentation
    (presentation :
      G8BookIIICh23FloorNormalizedA15SelectedKirchhoffType1Presentation)
    (proofStones :
      G8BookIIICh23FloorNormalizedA15AdjointDomainExhaustionProofStoneSource) :
    Prop :=
  G8BookIIICh23FloorNormalizedA15Type1PresentationExhaustsSelectedKirchhoffDomain
      presentation ∧
    G8BookIIICh23FloorNormalizedA15AdjointDomainEqualsKirchhoffDomain
      proofStones.reverseInclusion ∧
      proofStones.reverseInclusion.graphH2RegularityRecoveredFromAdjointEquation

/-- The alignment assertion follows from the fields already carried by the
    Type-1 presentation and proof-stone source. -/
theorem
    g8BookIIICh23FloorNormalizedA15ReverseInclusionUsesType1Presentation
    (presentation :
      G8BookIIICh23FloorNormalizedA15SelectedKirchhoffType1Presentation)
    (proofStones :
      G8BookIIICh23FloorNormalizedA15AdjointDomainExhaustionProofStoneSource) :
    G8BookIIICh23FloorNormalizedA15ReverseInclusionUsesType1Presentation
      presentation
      proofStones :=
  ⟨presentation.exhaustsSelectedKirchhoffDomain,
    proofStones.reverseInclusion.domainEquality,
    proofStones.reverseInclusion.graphH2RegularityRecoveredWitness⟩

-- ============================================================
-- ASSEMBLY OF THE ADJOINT-DOMAIN TYPE-1 PRESENTATION SOURCE
-- ============================================================

/-- A bundled assembly source: the small presentation and the proof stones that
    supply reverse inclusion. -/
structure
    G8BookIIICh23FloorNormalizedA15AdjointDomainType1PresentationAssemblySource where
  presentation :
    G8BookIIICh23FloorNormalizedA15SelectedKirchhoffType1Presentation
  proofStones :
    G8BookIIICh23FloorNormalizedA15AdjointDomainExhaustionProofStoneSource
  status : SpineStatus := .conditional_interface

/-- Target for the assembled A1.5 Type-1 presentation source. -/
def
    G8BookIIICh23FloorNormalizedA15AdjointDomainType1PresentationAssemblyTarget :
    Prop :=
  Nonempty
    G8BookIIICh23FloorNormalizedA15AdjointDomainType1PresentationAssemblySource

/-- The assembly source constructs the exact adjoint-domain Type-1
    presentation source consumed by the concrete engine. -/
noncomputable def
    G8BookIIICh23FloorNormalizedA15AdjointDomainType1PresentationAssemblySource.toType1PresentationSource
    (source :
      G8BookIIICh23FloorNormalizedA15AdjointDomainType1PresentationAssemblySource) :
    G8BookIIICh23FloorNormalizedA15AdjointDomainType1PresentationSource where
  presentation := source.presentation
  reverseInclusion := source.proofStones.reverseInclusion
  reverseInclusionUsesPresentation :=
    G8BookIIICh23FloorNormalizedA15ReverseInclusionUsesType1Presentation
      source.presentation
      source.proofStones
  reverseInclusionUsesPresentationWitness :=
    g8BookIIICh23FloorNormalizedA15ReverseInclusionUsesType1Presentation
      source.presentation
      source.proofStones
  status := .conditional_interface

/-- An assembly source proves the adjoint-domain Type-1 presentation target. -/
theorem
    G8BookIIICh23FloorNormalizedA15AdjointDomainType1PresentationAssemblySource.toType1PresentationTarget
    (source :
      G8BookIIICh23FloorNormalizedA15AdjointDomainType1PresentationAssemblySource) :
    G8BookIIICh23FloorNormalizedA15AdjointDomainType1PresentationTarget :=
  ⟨source.toType1PresentationSource⟩

/-- A small presentation source and proof-stone source assemble the target
    directly. -/
noncomputable def
    g8BookIIICh23FloorNormalizedA15AdjointDomainType1PresentationAssemblySource_of
    (presentation :
      G8BookIIICh23FloorNormalizedA15SelectedKirchhoffType1Presentation)
    (proofStones :
      G8BookIIICh23FloorNormalizedA15AdjointDomainExhaustionProofStoneSource) :
    G8BookIIICh23FloorNormalizedA15AdjointDomainType1PresentationAssemblySource where
  presentation := presentation
  proofStones := proofStones
  status := .conditional_interface

/-- Target-level assembly from the two currently visible A1.5 obligations:
    small Type-1 presentation and reverse-inclusion proof stones. -/
theorem
    g8BookIIICh23FloorNormalizedA15AdjointDomainType1PresentationTarget_ofPresentationAndProofStones
    (presentationTarget :
      G8BookIIICh23FloorNormalizedA15SelectedKirchhoffType1PresentationTarget)
    (proofStoneTarget :
      G8BookIIICh23FloorNormalizedA15AdjointDomainExhaustionProofStoneTarget) :
    G8BookIIICh23FloorNormalizedA15AdjointDomainType1PresentationTarget :=
  presentationTarget.elim fun presentation =>
    proofStoneTarget.elim fun proofStones =>
      (g8BookIIICh23FloorNormalizedA15AdjointDomainType1PresentationAssemblySource_of
        presentation
        proofStones).toType1PresentationTarget

/-- Assembly-target form of the same result. -/
theorem
    g8BookIIICh23FloorNormalizedA15AdjointDomainType1PresentationTarget_ofAssembly
    (target :
      G8BookIIICh23FloorNormalizedA15AdjointDomainType1PresentationAssemblyTarget) :
    G8BookIIICh23FloorNormalizedA15AdjointDomainType1PresentationTarget :=
  target.elim fun source => source.toType1PresentationTarget

-- ============================================================
-- DOWNSTREAM A1.5 ENGINE ADAPTERS
-- ============================================================

/-- The two A1.5 obligations are enough for the concrete adjoint-calculus
    engine. -/
theorem
    g8BookIIICh23FloorNormalizedA15AdjointCalculusEngineTarget_ofPresentationAndProofStones
    (presentationTarget :
      G8BookIIICh23FloorNormalizedA15SelectedKirchhoffType1PresentationTarget)
    (proofStoneTarget :
      G8BookIIICh23FloorNormalizedA15AdjointDomainExhaustionProofStoneTarget) :
    G8BookIIICh23FloorNormalizedA15AdjointCalculusEngineTarget :=
  g8BookIIICh23FloorNormalizedA15AdjointCalculusEngineTarget_ofType1Presentation
    (g8BookIIICh23FloorNormalizedA15AdjointDomainType1PresentationTarget_ofPresentationAndProofStones
      presentationTarget
      proofStoneTarget)

/-- The two A1.5 obligations are enough for the two analytic-law targets
    consumed by the reverse-inclusion proof path. -/
theorem
    g8BookIIICh23FloorNormalizedA15TwoAnalyticLawTargets_ofPresentationAndProofStones
    (presentationTarget :
      G8BookIIICh23FloorNormalizedA15SelectedKirchhoffType1PresentationTarget)
    (proofStoneTarget :
      G8BookIIICh23FloorNormalizedA15AdjointDomainExhaustionProofStoneTarget) :
    G8BookIIICh23FloorNormalizedA15GraphH2TraceRecoveryFromAdjointEquationTarget ∧
      G8BookIIICh23FloorNormalizedA15AdjointPairingGreenIdentityAgainstKirchhoffTestsTarget :=
  g8BookIIICh23FloorNormalizedA15TwoAnalyticLawTargets_ofType1Presentation
    (g8BookIIICh23FloorNormalizedA15AdjointDomainType1PresentationTarget_ofPresentationAndProofStones
      presentationTarget
      proofStoneTarget)

-- ============================================================
-- GUARDRAILS
-- ============================================================

/-- Reverse-inclusion proof stones alone do not provide the small Type-1
    presentation. -/
structure
    G8BookIIICh23FloorNormalizedA15ProofStonesWithoutType1Presentation
    where
  proofStoneTarget :
    G8BookIIICh23FloorNormalizedA15AdjointDomainExhaustionProofStoneTarget
  missingPresentation :
    ¬ G8BookIIICh23FloorNormalizedA15SelectedKirchhoffType1PresentationTarget

theorem
    G8BookIIICh23FloorNormalizedA15ProofStonesWithoutType1Presentation.refutes
    (gap :
      G8BookIIICh23FloorNormalizedA15ProofStonesWithoutType1Presentation)
    (source :
      G8BookIIICh23FloorNormalizedA15AdjointDomainType1PresentationSource) :
    False :=
  gap.missingPresentation ⟨source.presentation⟩

/-- A small Type-1 presentation alone does not provide reverse adjoint-domain
    inclusion. -/
structure
    G8BookIIICh23FloorNormalizedA15Type1PresentationWithoutReverseInclusionTarget
    where
  presentationTarget :
    G8BookIIICh23FloorNormalizedA15SelectedKirchhoffType1PresentationTarget
  missingReverseInclusion :
    ¬ G8BookIIICh23FloorNormalizedA15AdjointDomainReverseInclusionTarget

theorem
    G8BookIIICh23FloorNormalizedA15Type1PresentationWithoutReverseInclusionTarget.refutes
    (gap :
      G8BookIIICh23FloorNormalizedA15Type1PresentationWithoutReverseInclusionTarget)
    (source :
      G8BookIIICh23FloorNormalizedA15AdjointDomainType1PresentationSource) :
    False :=
  gap.missingReverseInclusion source.toReverseInclusionTarget

/-- Losing graph-`H2` recovery from the reverse-inclusion proof stones refutes
    the assembly source. -/
structure
    G8BookIIICh23FloorNormalizedA15Type1AssemblyWithoutGraphH2Recovery
    where
  source :
    G8BookIIICh23FloorNormalizedA15AdjointDomainType1PresentationAssemblySource
  missingGraphH2 :
    ¬ source.proofStones.reverseInclusion.graphH2RegularityRecoveredFromAdjointEquation

theorem
    G8BookIIICh23FloorNormalizedA15Type1AssemblyWithoutGraphH2Recovery.refutes
    (gap :
      G8BookIIICh23FloorNormalizedA15Type1AssemblyWithoutGraphH2Recovery) :
    False :=
  gap.missingGraphH2
    gap.source.proofStones.reverseInclusion.graphH2RegularityRecoveredWitness

end Tau.BookIII.Bridge
