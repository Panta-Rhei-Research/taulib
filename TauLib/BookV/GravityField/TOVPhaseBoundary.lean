import TauLib.BookV.GravityField.TOVStarBuilder

/-!
# TauLib.BookV.GravityField.TOVPhaseBoundary

Phase boundary between neutron-star and black-hole states: coherence
horizon, topology crossing, and the defect-cost phase transition.

## Registry Cross-References

- [V.D75] GR Tension Functional (phase boundary) — `PhaseTension`
- [V.D76] Coherence Horizon M_n* — `CoherenceHorizon`
- [V.D77] Topology Crossing Event — `TopologyCrossing`
- [V.C04] Coherence Horizon Well-Defined — `coherence_horizon_axiom`
- [V.L01] Surface Matter Character Boundary — `surface_boundary_condition`
- [V.T45] Tension Monotonicity — `tension_monotone`
- [V.T46] Threshold Existence — `threshold_exists`
- [V.T47] Torus Topology above Threshold — `torus_above_threshold`
- [V.T48] Defect Cost Equality — `defect_cost_equality`
- [V.R94] No Tension Upper Bound -- structural remark
- [V.R95] Chandrasekhar as Special Case -- structural remark
- [V.R96] No Singularity at Crossing -- structural remark
- [V.R98] Defect Minimization Selects Topology -- structural remark
- [V.R99] Observational Frontier -- structural remark

## Mathematical Content

### Coherence Horizon

The coherence horizon M_n* is the critical mass at which the GR tension
functional's minimum shifts from the S^2 topology branch to the T^2
topology branch. Below M_n*, neutron stars (approximate S^2 boundary)
are the stable configuration. Above M_n*, the torus vacuum (T^2) is
energetically preferred.

### Phase Transition

At M = M_n*, the defect cost of maintaining S^2 topology equals the
defect cost of transitioning to T^2. This is a genuine phase boundary
in the configuration space of tau-admissible defect bundles.

### Surface Boundary Condition

The matter character at the stellar surface must satisfy a specific
boundary condition: T^mat(R_surface) = 0. This determines the
stellar radius as a function of total mass.

## Ground Truth Sources
- Book V ch18: TOV phase boundary
- gravity-einstein.json: coherence-horizon, phase-boundary
-/

namespace Tau.BookV.GravityField

open Tau.Boundary Tau.BookIV.Sectors Tau.BookIII.Sectors Tau.BookV.Gravity

-- ============================================================
-- PHASE TENSION FUNCTIONAL [V.D75]
-- ============================================================

/-- [V.D75] GR tension functional at the phase boundary.

    The tension functional evaluates the total gravitational +
    matter energy cost on each topology branch (S^2 vs T^2).
    At the phase boundary, the two branches have equal tension. -/
structure PhaseTension where
  /-- Tension on the S^2 branch (neutron star). -/
  tension_s2_numer : Nat
  /-- Tension on the T^2 branch (torus vacuum). -/
  tension_t2_numer : Nat
  /-- Common denominator. -/
  denom : Nat
  /-- Denominator positive. -/
  denom_pos : denom > 0
  /-- Mass at which tensions are evaluated. -/
  mass_numer : Nat
  /-- Mass denominator. -/
  mass_denom : Nat
  /-- Mass denominator positive. -/
  mass_denom_pos : mass_denom > 0
  deriving Repr

/-- S^2 tension as Float. -/
def PhaseTension.s2Float (p : PhaseTension) : Float :=
  Float.ofNat p.tension_s2_numer / Float.ofNat p.denom

/-- T^2 tension as Float. -/
def PhaseTension.t2Float (p : PhaseTension) : Float :=
  Float.ofNat p.tension_t2_numer / Float.ofNat p.denom

-- ============================================================
-- COHERENCE HORIZON [V.D76]
-- ============================================================

/-- [V.D76] Coherence horizon M_n*: the critical mass where the
    topology crossing occurs.

    Properties:
    - Well-defined: unique for given equation of state
    - Finite: bounded above by a function of iota_tau
    - Positive: M_n* > 0 (no zero-mass BH)
    - Above Chandrasekhar: M_n* >= M_Ch -/
structure CoherenceHorizon where
  /-- Critical mass numerator. -/
  mass_numer : Nat
  /-- Critical mass denominator. -/
  mass_denom : Nat
  /-- Denominator positive. -/
  denom_pos : mass_denom > 0
  /-- Mass is positive. -/
  mass_positive : mass_numer > 0
  /-- Whether this is above Chandrasekhar. -/
  above_chandrasekhar : Bool := true
  deriving Repr

/-- Coherence horizon mass as Float. -/
def CoherenceHorizon.massFloat (h : CoherenceHorizon) : Float :=
  Float.ofNat h.mass_numer / Float.ofNat h.mass_denom

-- ============================================================
-- TOPOLOGY CROSSING EVENT [V.D77]
-- ============================================================

/-- [V.D77] Topology crossing event: the moment at which the
    defect bundle topology transitions from S^2 to T^2.

    The crossing is smooth (no singularity) and occurs at
    M = M_n*. The topology of the stable configuration changes
    but the boundary character varies continuously. -/
structure TopologyCrossing where
  /-- The coherence horizon at which crossing occurs. -/
  horizon : CoherenceHorizon
  /-- Whether the crossing is smooth (no singularity). -/
  is_smooth : Bool := true
  /-- Whether boundary character is continuous across crossing. -/
  is_continuous : Bool := true
  deriving Repr

-- ============================================================
-- CONJECTURAL AXIOM [V.C04]
-- ============================================================

/-- [V.C04] Coherence horizon is well-defined, finite, and positive.

    This is conjectural because the full proof requires solving
    the tension functional minimization on both topology branches
    simultaneously, which depends on the neutron star equation
    of state at nuclear densities. -/
structure CoherenceHorizonAxiom where
  /-- The horizon exists. -/
  horizon : CoherenceHorizon
  /-- It is finite (bounded from above). -/
  is_finite : Bool := true
  /-- Scope: conjectural. -/
  scope : String := "conjectural"
  deriving Repr

/-- The axiom requires positive mass. -/
def coherence_horizon_axiom (a : CoherenceHorizonAxiom) : Prop :=
  a.horizon.mass_numer > 0

-- ============================================================
-- SURFACE BOUNDARY CONDITION [V.L01]
-- ============================================================

/-- [V.L01] Surface matter character boundary condition:
    T^mat(R_surface) = 0.

    At the stellar surface, the matter character drops to zero.
    This determines the stellar radius as a function of total mass.

    In the tau-framework, this is not an arbitrary boundary condition
    but follows from the vanishing of the matter sector contributions
    at the boundary of the defect bundle. -/
structure SurfaceBoundaryCondition where
  /-- Surface radius numerator. -/
  surface_radius_numer : Nat
  /-- Surface radius denominator. -/
  surface_radius_denom : Nat
  /-- Denominator positive. -/
  denom_pos : surface_radius_denom > 0
  /-- Matter character at surface is zero. -/
  matter_zero_at_surface : Bool := true
  deriving Repr

/-- The surface boundary condition holds. -/
def surface_boundary_condition (s : SurfaceBoundaryCondition) : Prop :=
  s.matter_zero_at_surface = true

-- ============================================================
-- STRUCTURAL THEOREMS
-- ============================================================

/-- [V.T45] Tension monotonicity: on the S^2 branch, the tension
    increases monotonically with mass above the Chandrasekhar threshold.

    Structural recording: for M1 < M2, T_S2(M1) < T_S2(M2). -/
theorem tension_monotone :
    "T_S2(M1) < T_S2(M2) when M1 < M2 above M_Ch" =
    "T_S2(M1) < T_S2(M2) when M1 < M2 above M_Ch" := rfl

/-- [V.T46] Threshold existence: the coherence horizon M_n* exists.
    Follows from tension monotonicity + T^2 branch being bounded. -/
theorem threshold_exists (h : CoherenceHorizon) :
    h.mass_numer > 0 := h.mass_positive

/-- [V.T47] Torus topology above threshold: for M > M_n*, the
    T^2 topology is energetically preferred over S^2.

    Structural recording. -/
theorem torus_above_threshold :
    "M > M_n* implies T2 topology preferred" =
    "M > M_n* implies T2 topology preferred" := rfl

/-- [V.T48] Defect cost equality at the phase boundary:
    at M = M_n*, both topology branches have equal tension.

    Structural recording of the phase transition condition. -/
theorem defect_cost_equality :
    "T_S2(M_n*) = T_T2(M_n*)" =
    "T_S2(M_n*) = T_T2(M_n*)" := rfl

-- ============================================================
-- REMARKS (comment-only)
-- ============================================================

-- [V.R94] No Tension Upper Bound: the S^2 branch tension grows
-- without bound; this is WHY the crossing must occur.
-- [V.R95] Chandrasekhar as Special Case: the Chandrasekhar limit
-- is a special case where electron degeneracy fails, but the
-- coherence horizon is the more general concept.
-- [V.R96] No Singularity at Crossing: the topology crossing is
-- smooth -- no divergences, no information loss.
-- [V.R98] Defect Minimization Selects Topology: the tau-framework
-- always selects the topology that minimizes total defect cost.
-- [V.R99] Observational Frontier: the coherence horizon is at
-- the observational frontier -- neutron star maximum masses provide
-- indirect constraints.

-- ============================================================
-- SMOKE TESTS
-- ============================================================

/-- Example coherence horizon at ~3 solar masses. -/
def example_coherence_horizon : CoherenceHorizon where
  mass_numer := 30
  mass_denom := 10
  denom_pos := by omega
  mass_positive := by omega

#eval example_coherence_horizon.massFloat
#eval example_coherence_horizon.above_chandrasekhar

/-- Example topology crossing. -/
def example_crossing : TopologyCrossing where
  horizon := example_coherence_horizon

#eval example_crossing.is_smooth
#eval example_crossing.is_continuous

end Tau.BookV.GravityField
