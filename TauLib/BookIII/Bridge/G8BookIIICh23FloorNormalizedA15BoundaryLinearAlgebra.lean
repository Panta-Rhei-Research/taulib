import TauLib.BookIII.Bridge.G8BookIIICh23FloorNormalizedA15AdjointDomainExhaustionPayloadConstruction

/-!
# G8 Book III Ch.23 Floor-Normalized A1.5 Boundary Linear Algebra

This module discharges the finite boundary-linear-algebra part of A1.5.

For a two-lobe wedge graph, the boundary trace has four value coordinates and
four outgoing derivative coordinates at the crossing.  The Kirchhoff boundary
subspace is:

```text
all four values agree
sum of all outgoing derivatives is zero
```

With the standard boundary symplectic form

```text
Omega((v,d),(w,e)) = d dot w - v dot e
```

this Kirchhoff subspace is its own annihilator.  This is the finite-dimensional
maximal-isotropic boundary theorem needed by the A1.5 payload.  It does not
prove the analytic adjoint-domain lift or reverse inclusion.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

-- ============================================================
-- FOUR ENDPOINT COORDINATES
-- ============================================================

/-- Four endpoint coordinates for the two-loop wedge boundary.  The coordinate
    order is B-left, B-right, C-left, C-right. -/
structure G8BookIIICh23FloorNormalizedA15BoundaryCoord where
  b0 : Int
  b1 : Int
  c0 : Int
  c1 : Int
  deriving Repr, DecidableEq

namespace G8BookIIICh23FloorNormalizedA15BoundaryCoord

/-- The zero four-coordinate vector. -/
def zero : G8BookIIICh23FloorNormalizedA15BoundaryCoord where
  b0 := 0
  b1 := 0
  c0 := 0
  c1 := 0

/-- The constant-one four-coordinate vector. -/
def one : G8BookIIICh23FloorNormalizedA15BoundaryCoord where
  b0 := 1
  b1 := 1
  c0 := 1
  c1 := 1

/-- Test derivative vector forcing equality of the B endpoints. -/
def testB : G8BookIIICh23FloorNormalizedA15BoundaryCoord where
  b0 := -1
  b1 := 1
  c0 := 0
  c1 := 0

/-- Test derivative vector forcing equality between the B base and C-left. -/
def testC0 : G8BookIIICh23FloorNormalizedA15BoundaryCoord where
  b0 := -1
  b1 := 0
  c0 := 1
  c1 := 0

/-- Test derivative vector forcing equality between the B base and C-right. -/
def testC1 : G8BookIIICh23FloorNormalizedA15BoundaryCoord where
  b0 := -1
  b1 := 0
  c0 := 0
  c1 := 1

/-- Coordinate sum, used for Kirchhoff outgoing-derivative balance. -/
def sum (x : G8BookIIICh23FloorNormalizedA15BoundaryCoord) : Int :=
  x.b0 + x.b1 + x.c0 + x.c1

/-- Integer dot product for the finite boundary model. -/
def dot
    (x y : G8BookIIICh23FloorNormalizedA15BoundaryCoord) :
    Int :=
  x.b0 * y.b0 + x.b1 * y.b1 + x.c0 * y.c0 + x.c1 * y.c1

/-- Crossing value agreement: all endpoint values coincide. -/
def balanced
    (x : G8BookIIICh23FloorNormalizedA15BoundaryCoord) :
    Prop :=
  x.b0 = x.b1 ∧ x.b0 = x.c0 ∧ x.b0 = x.c1

theorem zero_balanced :
    balanced zero := by
  simp [balanced, zero]

theorem one_balanced :
    balanced one := by
  simp [balanced, one]

theorem zero_sum :
    sum zero = 0 := by
  norm_num [sum, zero]

theorem testB_sum :
    sum testB = 0 := by
  norm_num [sum, testB]

theorem testC0_sum :
    sum testC0 = 0 := by
  norm_num [sum, testC0]

theorem testC1_sum :
    sum testC1 = 0 := by
  norm_num [sum, testC1]

end G8BookIIICh23FloorNormalizedA15BoundaryCoord

-- ============================================================
-- BOUNDARY TRACES AND KIRCHHOFF SUBSPACE
-- ============================================================

/-- Finite boundary trace: endpoint values plus outgoing derivatives. -/
structure G8BookIIICh23FloorNormalizedA15BoundaryTrace where
  value : G8BookIIICh23FloorNormalizedA15BoundaryCoord
  deriv : G8BookIIICh23FloorNormalizedA15BoundaryCoord
  deriving Repr, DecidableEq

namespace G8BookIIICh23FloorNormalizedA15BoundaryTrace

abbrev Coord :=
  G8BookIIICh23FloorNormalizedA15BoundaryCoord

namespace Coord

export G8BookIIICh23FloorNormalizedA15BoundaryCoord
  (zero one testB testC0 testC1 sum dot balanced zero_balanced one_balanced
    zero_sum testB_sum testC0_sum testC1_sum)

end Coord

/-- The zero boundary trace. -/
def zero : G8BookIIICh23FloorNormalizedA15BoundaryTrace where
  value := Coord.zero
  deriv := Coord.zero

/-- A boundary trace with constant unit value and zero derivative. -/
def constantValueOne :
    G8BookIIICh23FloorNormalizedA15BoundaryTrace where
  value := Coord.one
  deriv := Coord.zero

/-- A boundary trace with zero value and B-endpoint derivative test. -/
def derivativeTestB :
    G8BookIIICh23FloorNormalizedA15BoundaryTrace where
  value := Coord.zero
  deriv := Coord.testB

/-- A boundary trace with zero value and C-left derivative test. -/
def derivativeTestC0 :
    G8BookIIICh23FloorNormalizedA15BoundaryTrace where
  value := Coord.zero
  deriv := Coord.testC0

/-- A boundary trace with zero value and C-right derivative test. -/
def derivativeTestC1 :
    G8BookIIICh23FloorNormalizedA15BoundaryTrace where
  value := Coord.zero
  deriv := Coord.testC1

/-- Kirchhoff boundary condition: crossing value agreement plus derivative
    balance. -/
def Kirchhoff
    (x : G8BookIIICh23FloorNormalizedA15BoundaryTrace) :
    Prop :=
  Coord.balanced x.value ∧ Coord.sum x.deriv = 0

/-- Boundary symplectic form from Green's identity. -/
def boundaryForm
    (x y : G8BookIIICh23FloorNormalizedA15BoundaryTrace) :
    Int :=
  Coord.dot x.deriv y.value - Coord.dot x.value y.deriv

/-- A boundary trace annihilates all Kirchhoff boundary traces. -/
def annihilatesKirchhoff
    (x : G8BookIIICh23FloorNormalizedA15BoundaryTrace) :
    Prop :=
  ∀ y : G8BookIIICh23FloorNormalizedA15BoundaryTrace,
    Kirchhoff y → boundaryForm x y = 0

theorem zero_kirchhoff :
    Kirchhoff zero := by
  exact ⟨Coord.zero_balanced, Coord.zero_sum⟩

theorem constantValueOne_kirchhoff :
    Kirchhoff constantValueOne := by
  exact ⟨Coord.one_balanced, Coord.zero_sum⟩

theorem derivativeTestB_kirchhoff :
    Kirchhoff derivativeTestB := by
  exact ⟨Coord.zero_balanced, Coord.testB_sum⟩

theorem derivativeTestC0_kirchhoff :
    Kirchhoff derivativeTestC0 := by
  exact ⟨Coord.zero_balanced, Coord.testC0_sum⟩

theorem derivativeTestC1_kirchhoff :
    Kirchhoff derivativeTestC1 := by
  exact ⟨Coord.zero_balanced, Coord.testC1_sum⟩

/-- Kirchhoff boundary traces annihilate all Kirchhoff boundary traces. -/
theorem boundaryForm_eq_zero_of_kirchhoff
    {x y : G8BookIIICh23FloorNormalizedA15BoundaryTrace}
    (hx : Kirchhoff x)
    (hy : Kirchhoff y) :
    boundaryForm x y = 0 := by
  rcases hx with ⟨⟨hx01, hx0c0, hx0c1⟩, hdx⟩
  rcases hy with ⟨⟨hy01, hy0c0, hy0c1⟩, hdy⟩
  dsimp [Coord.sum] at hdx hdy
  dsimp [boundaryForm, Coord.dot]
  rw [← hx01, ← hx0c0, ← hx0c1, ← hy01, ← hy0c0, ← hy0c1]
  calc
    x.deriv.b0 * y.value.b0 + x.deriv.b1 * y.value.b0 +
          x.deriv.c0 * y.value.b0 + x.deriv.c1 * y.value.b0 -
        (x.value.b0 * y.deriv.b0 + x.value.b0 * y.deriv.b1 +
          x.value.b0 * y.deriv.c0 + x.value.b0 * y.deriv.c1) =
        (x.deriv.b0 + x.deriv.b1 + x.deriv.c0 + x.deriv.c1) *
            y.value.b0 -
          x.value.b0 *
            (y.deriv.b0 + y.deriv.b1 + y.deriv.c0 + y.deriv.c1) := by
      ring
    _ = 0 := by
      rw [hdx, hdy]
      ring

/-- Kirchhoff traces are contained in their annihilator. -/
theorem annihilatesKirchhoff_of_kirchhoff
    {x : G8BookIIICh23FloorNormalizedA15BoundaryTrace}
    (hx : Kirchhoff x) :
    annihilatesKirchhoff x := by
  intro y hy
  exact boundaryForm_eq_zero_of_kirchhoff hx hy

/-- An annihilator trace has balanced values, forced by the three derivative
    test traces. -/
theorem balanced_of_annihilatesKirchhoff
    {x : G8BookIIICh23FloorNormalizedA15BoundaryTrace}
    (hx : annihilatesKirchhoff x) :
    Coord.balanced x.value := by
  have hB :=
    hx derivativeTestB derivativeTestB_kirchhoff
  have hC0 :=
    hx derivativeTestC0 derivativeTestC0_kirchhoff
  have hC1 :=
    hx derivativeTestC1 derivativeTestC1_kirchhoff
  constructor
  · dsimp [boundaryForm, Coord.dot, derivativeTestB, Coord.zero,
      Coord.testB] at hB
    omega
  constructor
  · dsimp [boundaryForm, Coord.dot, derivativeTestC0, Coord.zero,
      Coord.testC0] at hC0
    omega
  · dsimp [boundaryForm, Coord.dot, derivativeTestC1, Coord.zero,
      Coord.testC1] at hC1
    omega

/-- An annihilator trace satisfies outgoing derivative balance, forced by the
    constant-value Kirchhoff test trace. -/
theorem derivative_sum_eq_zero_of_annihilatesKirchhoff
    {x : G8BookIIICh23FloorNormalizedA15BoundaryTrace}
    (hx : annihilatesKirchhoff x) :
    Coord.sum x.deriv = 0 := by
  have h :=
    hx constantValueOne constantValueOne_kirchhoff
  dsimp [boundaryForm, Coord.dot, constantValueOne, Coord.one,
    Coord.zero] at h
  ring_nf at h
  simpa [Coord.sum] using h

/-- The annihilator of the Kirchhoff boundary subspace is contained in the
    Kirchhoff boundary subspace. -/
theorem kirchhoff_of_annihilatesKirchhoff
    {x : G8BookIIICh23FloorNormalizedA15BoundaryTrace}
    (hx : annihilatesKirchhoff x) :
    Kirchhoff x :=
  ⟨balanced_of_annihilatesKirchhoff hx,
    derivative_sum_eq_zero_of_annihilatesKirchhoff hx⟩

/-- The Kirchhoff boundary subspace is exactly its boundary-form annihilator. -/
theorem annihilatesKirchhoff_iff_kirchhoff
    (x : G8BookIIICh23FloorNormalizedA15BoundaryTrace) :
    annihilatesKirchhoff x ↔ Kirchhoff x :=
  ⟨kirchhoff_of_annihilatesKirchhoff,
    annihilatesKirchhoff_of_kirchhoff⟩

end G8BookIIICh23FloorNormalizedA15BoundaryTrace

-- ============================================================
-- MAXIMAL KIRCHHOFF BOUNDARY SOURCE
-- ============================================================

/-- Finite-dimensional maximal-isotropic Kirchhoff boundary theorem for the
    selected two-lobe boundary trace model. -/
def
    G8BookIIICh23FloorNormalizedA15FiniteBoundaryMaximalIsotropicKirchhoff :
    Prop :=
  (∀ x y : G8BookIIICh23FloorNormalizedA15BoundaryTrace,
      G8BookIIICh23FloorNormalizedA15BoundaryTrace.Kirchhoff x →
        G8BookIIICh23FloorNormalizedA15BoundaryTrace.Kirchhoff y →
          G8BookIIICh23FloorNormalizedA15BoundaryTrace.boundaryForm x y = 0) ∧
    (∀ x : G8BookIIICh23FloorNormalizedA15BoundaryTrace,
      G8BookIIICh23FloorNormalizedA15BoundaryTrace.annihilatesKirchhoff x ↔
        G8BookIIICh23FloorNormalizedA15BoundaryTrace.Kirchhoff x)

/-- The finite-dimensional Kirchhoff boundary theorem is closed by the
    explicit endpoint-coordinate calculation. -/
theorem
    g8BookIIICh23FloorNormalizedA15FiniteBoundaryMaximalIsotropicKirchhoff_closed :
    G8BookIIICh23FloorNormalizedA15FiniteBoundaryMaximalIsotropicKirchhoff :=
  ⟨fun _ _ hx hy =>
      G8BookIIICh23FloorNormalizedA15BoundaryTrace.boundaryForm_eq_zero_of_kirchhoff
        hx hy,
    fun x =>
      G8BookIIICh23FloorNormalizedA15BoundaryTrace.annihilatesKirchhoff_iff_kirchhoff
        x⟩

/-- No larger symmetric boundary condition remains in the finite boundary
    model: every annihilator trace is already Kirchhoff. -/
def
    G8BookIIICh23FloorNormalizedA15FiniteBoundaryNoLargerSymmetricCondition :
    Prop :=
  ∀ x : G8BookIIICh23FloorNormalizedA15BoundaryTrace,
    G8BookIIICh23FloorNormalizedA15BoundaryTrace.annihilatesKirchhoff x →
      G8BookIIICh23FloorNormalizedA15BoundaryTrace.Kirchhoff x

/-- The no-larger-symmetric-boundary-condition law follows from the same
    annihilator equality. -/
theorem
    g8BookIIICh23FloorNormalizedA15FiniteBoundaryNoLargerSymmetricCondition_closed :
    G8BookIIICh23FloorNormalizedA15FiniteBoundaryNoLargerSymmetricCondition := by
  intro x hx
  exact
    (G8BookIIICh23FloorNormalizedA15BoundaryTrace.annihilatesKirchhoff_iff_kirchhoff
      x).1 hx

/-- The A1.5 maximal-isotropic Kirchhoff boundary source is theorem-backed by
    the finite endpoint-coordinate calculation. -/
def
    g8BookIIICh23FloorNormalizedA15MaximalIsotropicKirchhoffBoundarySource_fromBoundaryLinearAlgebra :
    G8BookIIICh23FloorNormalizedA15MaximalIsotropicKirchhoffBoundarySource where
  maximalIsotropicKirchhoffBoundaryCondition :=
    G8BookIIICh23FloorNormalizedA15FiniteBoundaryMaximalIsotropicKirchhoff
  maximalIsotropicKirchhoffBoundaryConditionWitness :=
    g8BookIIICh23FloorNormalizedA15FiniteBoundaryMaximalIsotropicKirchhoff_closed
  noLargerSymmetricBoundaryCondition :=
    G8BookIIICh23FloorNormalizedA15FiniteBoundaryNoLargerSymmetricCondition
  noLargerSymmetricBoundaryConditionWitness :=
    g8BookIIICh23FloorNormalizedA15FiniteBoundaryNoLargerSymmetricCondition_closed
  status := .conditional_interface

/-- Target form of the finite-dimensional maximal Kirchhoff boundary source. -/
def
    G8BookIIICh23FloorNormalizedA15MaximalIsotropicKirchhoffBoundaryTarget :
    Prop :=
  Nonempty
    G8BookIIICh23FloorNormalizedA15MaximalIsotropicKirchhoffBoundarySource

/-- The maximal Kirchhoff boundary source target is theorem-backed by the
    finite boundary-linear-algebra calculation. -/
theorem
    g8BookIIICh23FloorNormalizedA15MaximalIsotropicKirchhoffBoundaryTarget_fromBoundaryLinearAlgebra :
    G8BookIIICh23FloorNormalizedA15MaximalIsotropicKirchhoffBoundaryTarget :=
  ⟨g8BookIIICh23FloorNormalizedA15MaximalIsotropicKirchhoffBoundarySource_fromBoundaryLinearAlgebra⟩

-- ============================================================
-- RESIDUAL A1.5 PAYLOAD AFTER BOUNDARY LINEAR ALGEBRA
-- ============================================================

/-- After maximal boundary linear algebra is closed, the residual A1.5 source
    consists of the adjoint lift plus the reverse inclusion aligned with that
    lifted boundary forcing. -/
structure
    G8BookIIICh23FloorNormalizedA15AdjointLiftReverseInclusionSource where
  lift :
    G8BookIIICh23FloorNormalizedA15SelectedBoundaryKernelAdjointLiftSource
  reverseInclusion :
    G8BookIIICh23FloorNormalizedA15AdjointDomainContainedInKirchhoffDomainSource
  reverseUsesCrossing :
    reverseInclusion.crossingSource = lift.boundaryForcing.crossingAgreement
  reverseUsesKirchhoff :
    reverseInclusion.kirchhoffSource = lift.boundaryForcing.kirchhoffBalance
  graphH2RecoveryComesFromAdjointEquation : Prop
  graphH2RecoveryComesFromAdjointEquationWitness :
    graphH2RecoveryComesFromAdjointEquation
  reverseInclusionUsesBoundaryLinearAlgebra : Prop
  reverseInclusionUsesBoundaryLinearAlgebraWitness :
    reverseInclusionUsesBoundaryLinearAlgebra
  status : SpineStatus := .conditional_interface

/-- Target for the residual adjoint-lift plus reverse-inclusion payload after
    finite boundary linear algebra has been discharged. -/
def
    G8BookIIICh23FloorNormalizedA15AdjointLiftReverseInclusionTarget :
    Prop :=
  Nonempty
    G8BookIIICh23FloorNormalizedA15AdjointLiftReverseInclusionSource

/-- The residual source after boundary linear algebra supplies the previous
    maximal-boundary/reverse-inclusion source by inserting the closed maximal
    boundary theorem. -/
noncomputable def
    G8BookIIICh23FloorNormalizedA15AdjointLiftReverseInclusionSource.toMaximalBoundaryReverseInclusionSource
    (source :
      G8BookIIICh23FloorNormalizedA15AdjointLiftReverseInclusionSource) :
    G8BookIIICh23FloorNormalizedA15MaximalBoundaryReverseInclusionSource where
  lift := source.lift
  maximalBoundary :=
    g8BookIIICh23FloorNormalizedA15MaximalIsotropicKirchhoffBoundarySource_fromBoundaryLinearAlgebra
  reverseInclusion := source.reverseInclusion
  reverseUsesCrossing := source.reverseUsesCrossing
  reverseUsesKirchhoff := source.reverseUsesKirchhoff
  graphH2RecoveryComesFromAdjointEquation :=
    source.graphH2RecoveryComesFromAdjointEquation
  graphH2RecoveryComesFromAdjointEquationWitness :=
    source.graphH2RecoveryComesFromAdjointEquationWitness
  maximalBoundaryUsedForNoLargerSymmetricExtension :=
    G8BookIIICh23FloorNormalizedA15FiniteBoundaryNoLargerSymmetricCondition ∧
      source.reverseInclusionUsesBoundaryLinearAlgebra
  maximalBoundaryUsedForNoLargerSymmetricExtensionWitness :=
    ⟨g8BookIIICh23FloorNormalizedA15FiniteBoundaryNoLargerSymmetricCondition_closed,
      source.reverseInclusionUsesBoundaryLinearAlgebraWitness⟩
  status := .conditional_interface

/-- Target-level adapter from the residual post-boundary-linear-algebra source
    to the previous residual target. -/
theorem
    g8BookIIICh23FloorNormalizedA15MaximalBoundaryReverseInclusionTarget_ofAdjointLiftReverseInclusion
    (target :
      G8BookIIICh23FloorNormalizedA15AdjointLiftReverseInclusionTarget) :
    G8BookIIICh23FloorNormalizedA15MaximalBoundaryReverseInclusionTarget :=
  target.elim fun source =>
    ⟨source.toMaximalBoundaryReverseInclusionSource⟩

/-- After finite boundary linear algebra, the remaining adjoint-lift/reverse
    payload is sufficient for the full A1.5 adjoint-domain exhaustion route. -/
theorem
    g8BookIIICh23FloorNormalizedA15AdjointDomainExhaustionPayloadRouteTarget_ofAdjointLiftReverseInclusion
    (target :
      G8BookIIICh23FloorNormalizedA15AdjointLiftReverseInclusionTarget) :
    G8BookIIICh23FloorNormalizedA15AdjointDomainExhaustionPayloadRouteTarget :=
  g8BookIIICh23FloorNormalizedA15AdjointDomainExhaustionPayloadRouteTarget_ofMaximalBoundaryReverseInclusion
    (g8BookIIICh23FloorNormalizedA15MaximalBoundaryReverseInclusionTarget_ofAdjointLiftReverseInclusion
      target)

/-- After finite boundary linear algebra, the remaining adjoint-lift/reverse
    payload is sufficient for the selected-carrier maximal Kirchhoff extension
    target. -/
theorem
    g8BookIIICh23FloorNormalizedA15MaximalKirchhoffSelfAdjointExtensionTarget_ofAdjointLiftReverseInclusion
    (target :
      G8BookIIICh23FloorNormalizedA15AdjointLiftReverseInclusionTarget) :
    G8BookIIICh23FloorNormalizedA15MaximalKirchhoffSelfAdjointExtensionTarget :=
  g8BookIIICh23FloorNormalizedA15MaximalKirchhoffSelfAdjointExtensionTarget_ofMaximalBoundaryReverseInclusion
    (g8BookIIICh23FloorNormalizedA15MaximalBoundaryReverseInclusionTarget_ofAdjointLiftReverseInclusion
      target)

-- ============================================================
-- GUARDRAILS
-- ============================================================

/-- A boundary trace in the annihilator but outside Kirchhoff is impossible in
    the finite boundary model. -/
structure
    G8BookIIICh23FloorNormalizedA15BoundaryAnnihilatorStrictlyLargerGap where
  trace :
    G8BookIIICh23FloorNormalizedA15BoundaryTrace
  annihilates :
    G8BookIIICh23FloorNormalizedA15BoundaryTrace.annihilatesKirchhoff trace
  notKirchhoff :
    ¬ G8BookIIICh23FloorNormalizedA15BoundaryTrace.Kirchhoff trace

theorem
    G8BookIIICh23FloorNormalizedA15BoundaryAnnihilatorStrictlyLargerGap.refutes
    (gap :
      G8BookIIICh23FloorNormalizedA15BoundaryAnnihilatorStrictlyLargerGap) :
    False :=
  gap.notKirchhoff
    (G8BookIIICh23FloorNormalizedA15BoundaryTrace.kirchhoff_of_annihilatesKirchhoff
      gap.annihilates)

/-- Finite boundary linear algebra alone still does not provide the analytic
    adjoint-domain lift. -/
structure
    G8BookIIICh23FloorNormalizedA15BoundaryLinearAlgebraWithoutAdjointLift
    where
  maximalBoundary :
    G8BookIIICh23FloorNormalizedA15MaximalIsotropicKirchhoffBoundarySource
  missingLift :
    ¬ G8BookIIICh23FloorNormalizedA15SelectedBoundaryKernelAdjointLiftTarget

theorem
    G8BookIIICh23FloorNormalizedA15BoundaryLinearAlgebraWithoutAdjointLift.refutes
    (gap :
      G8BookIIICh23FloorNormalizedA15BoundaryLinearAlgebraWithoutAdjointLift)
    (lift :
      G8BookIIICh23FloorNormalizedA15SelectedBoundaryKernelAdjointLiftSource) :
    False :=
  gap.missingLift ⟨lift⟩

end Tau.BookIII.Bridge
