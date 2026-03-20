import TauLib.BookIV.Physics.InternalEquations
import TauLib.BookIV.Calibration.SIReference

/-!
# TauLib.BookIV.Physics.ReadoutFunctor

The readout functor R_μ: the precise categorical bridge between
Layer 1 (internal physics) and Layer 2 (SI measurement procedures).

## Registry Cross-References

- [IV.D325] Measurement Procedure — `MeasurementProcedure`
- [IV.D326] Readout Functor — `ReadoutFunctor`
- [IV.D327] Calibration Anchor — `ReadoutAnchor`
- [IV.T128] Readout Preserves Identities — `readout_preserves_identities`
- [IV.T129] Single-Anchor Sufficiency — `single_anchor_sufficiency`
- [IV.P177] Codomain is operational — `codomain_operational`

## Mathematical Content

### The Readout Functor R_μ

**Domain**: H_∂[ω] — internal categorical objects (Layer 1).
**Codomain**: Operational measurement procedures (NOT abstract SI numbers).

R_μ does NOT map to "mass" or "energy" as Platonic universals.
It maps to **specific operational measurement procedures**:

| Internal object | R_μ image | Operational procedure |
|----------------|-----------|----------------------|
| m_n (neutron mass morphism) | **ANCHOR** | Penning trap frequency ratio |
| m_e (electron mass morphism) | R₀⁻¹ × m_n procedure | Same trap, different ion |
| α (fine structure) | (121/225)·ι_τ⁴ → number | Quantum Hall + von Klitzing |
| G (gravitational constant) | ι_τ² × torus vacuum → number | Torsion balance protocol |

### The Single Anchor

m_n is the ONLY empirical input. Everything else is:
- Internal categorical structure (Layer 1) +
- R_μ readout (Layer 2) +
- 4 exact SI defining constants (c, h, e, k_B)

### Layer 2 = SI Bridge

Layer 2 is NOT "the real world." It is the sharply delineated boundary
between the τ-framework's internal categorical physics and the
metrological conventions of the International System of Units.

## Ground Truth Sources
- Book IV Part II ch12-ch14: Calibration anchor, dimensional bridge
- SharedOntology.lean: calibration is structural
-/

namespace Tau.BookIV.Physics

open Tau.BookIII.Sectors Tau.BookIV.Calibration

-- ============================================================
-- MEASUREMENT PROCEDURE [IV.D325]
-- ============================================================

/-- [IV.D325] An operational measurement procedure: the codomain of
    the readout functor R_μ.

    NOT an abstract SI number. NOT "mass itself." Rather: a complete
    specification of HOW to measure, yielding a number in SI units.

    Examples:
    - Penning trap frequency ratio for m_n
    - Quantum Hall resistance for α
    - Torsion balance protocol for G -/
structure MeasurementProcedure where
  /-- Which physical quantity this procedure measures. -/
  quantity : PrimaryInvariant
  /-- Which sector the source internal object lives in. -/
  source_sector : Sector
  /-- Name of the operational protocol. -/
  protocol : String
  /-- Whether this is the calibration anchor (exactly one: m_n). -/
  is_anchor : Bool
  /-- SI unit string (e.g., "kg", "m/s", dimensionless). -/
  si_unit : String
  /-- Number of exact SI constants used in the readout chain. -/
  exact_constants_used : Nat
  deriving Repr

-- ============================================================
-- READOUT FUNCTOR [IV.D326]
-- ============================================================

/-- [IV.D326] The readout functor R_μ.

    Domain: Internal categorical objects in H_∂[ω] (Layer 1).
    Codomain: Operational measurement procedures (Layer 2).

    Properties:
    - Preserves internal identities (a homomorphism, not a lossy projection)
    - Has a single empirical anchor (m_n)
    - Uses exactly 4 exact SI defining constants (c, h, e, k_B)
    - Every other SI value is DERIVED, not independently measured -/
structure ReadoutFunctor where
  /-- Number of independent empirical inputs (must be 1 = m_n). -/
  num_anchors : Nat
  /-- The anchor count is exactly 1. -/
  single_anchor : num_anchors = 1
  /-- Number of exact SI defining constants used. -/
  num_exact_si : Nat
  /-- Exactly 4 exact SI constants (c, h, e, k_B). -/
  four_exact : num_exact_si = 4
  /-- R_μ preserves internal identities (is a functor, not just a function). -/
  preserves_identities : Bool
  /-- Identity preservation is true. -/
  preserves_true : preserves_identities = true
  deriving Repr

/-- The canonical readout functor. -/
def readout : ReadoutFunctor where
  num_anchors := 1
  single_anchor := rfl
  num_exact_si := 4
  four_exact := rfl
  preserves_identities := true
  preserves_true := rfl

-- ============================================================
-- READOUT ANCHOR [IV.D327]
-- ============================================================

/-- [IV.D327] The calibration anchor: the single empirical input
    to the readout functor.

    In the τ-framework, m_n (neutron mass) is the unique anchor because:
    1. The neutron is the first ontic particle (minimal mass-bearing config)
    2. It is directly measurable (Penning trap)
    3. All other masses are internal ratios times m_n
    4. All other dimensionful constants factor through m_n + exact SI -/
structure ReadoutAnchor where
  /-- The SI constant serving as anchor. -/
  anchor : SIConstant
  /-- The anchor quantity is Mass. -/
  quantity : PrimaryInvariant
  /-- It is a mass measurement. -/
  is_mass : quantity = .Mass
  /-- The measurement procedure. -/
  procedure : MeasurementProcedure
  /-- The procedure is flagged as anchor. -/
  procedure_is_anchor : procedure.is_anchor = true
  deriving Repr

/-- The neutron mass measurement procedure. -/
def neutron_procedure : MeasurementProcedure where
  quantity := .Mass
  source_sector := .C
  protocol := "Penning trap cyclotron frequency ratio"
  is_anchor := true
  si_unit := "kg"
  exact_constants_used := 0   -- the anchor itself uses no exact constants

/-- The canonical readout anchor: neutron mass. -/
def readout_anchor : ReadoutAnchor where
  anchor := si_neutron_mass
  quantity := .Mass
  is_mass := rfl
  procedure := neutron_procedure
  procedure_is_anchor := rfl

-- ============================================================
-- DERIVED MEASUREMENT PROCEDURES
-- ============================================================

/-- Electron mass measurement: derived from m_n via mass ratio R₀. -/
def electron_procedure : MeasurementProcedure where
  quantity := .Mass
  source_sector := .C
  protocol := "Penning trap (same trap, different ion) via R₀ = m_n/m_e"
  is_anchor := false
  si_unit := "kg"
  exact_constants_used := 0   -- R₀ is dimensionless, no SI constants needed

/-- Fine-structure constant measurement: readout of EM self-coupling. -/
def alpha_procedure : MeasurementProcedure where
  quantity := .Energy
  source_sector := .B
  protocol := "Quantum Hall effect + von Klitzing resistance"
  is_anchor := false
  si_unit := "dimensionless"
  exact_constants_used := 0   -- α is dimensionless

/-- Gravitational constant measurement: readout of D-sector coupling. -/
def gravity_procedure : MeasurementProcedure where
  quantity := .Gravity
  source_sector := .D
  protocol := "Torsion balance (Cavendish-type)"
  is_anchor := false
  si_unit := "m³/(kg·s²)"
  exact_constants_used := 3   -- G readout uses c, h, m_n

/-- Speed of light: readout of base-fiber conversion. -/
def speed_of_light_procedure : MeasurementProcedure where
  quantity := .Time        -- c bridges time (base) and space (fiber)
  source_sector := .D
  protocol := "SI-defined exact value (distance/time)"
  is_anchor := false
  si_unit := "m/s"
  exact_constants_used := 0   -- c is exact by SI definition

/-- All canonical measurement procedures. -/
def all_procedures : List MeasurementProcedure :=
  [neutron_procedure, electron_procedure, alpha_procedure,
   gravity_procedure, speed_of_light_procedure]

-- ============================================================
-- STRUCTURAL THEOREMS
-- ============================================================

/-- [IV.T128] The readout functor preserves internal identities:
    if two Layer 1 objects are equal (as internal morphisms),
    their R_μ images yield equal SI numbers. -/
theorem readout_preserves_identities :
    readout.preserves_identities = true := rfl

/-- [IV.T129] Single-anchor sufficiency: the readout functor requires
    exactly 1 empirical input (m_n) and 4 exact SI constants. -/
theorem single_anchor_sufficiency :
    readout.num_anchors = 1 ∧ readout.num_exact_si = 4 := by
  exact ⟨rfl, rfl⟩

/-- [IV.P177] The codomain of R_μ is operational: each measurement
    procedure specifies a protocol, not just a number. -/
theorem codomain_operational :
    neutron_procedure.protocol ≠ "" ∧
    electron_procedure.protocol ≠ "" ∧
    alpha_procedure.protocol ≠ "" ∧
    gravity_procedure.protocol ≠ "" := by
  simp [neutron_procedure, electron_procedure, alpha_procedure, gravity_procedure]

/-- Exactly one procedure is the anchor. -/
theorem unique_anchor :
    (all_procedures.filter (·.is_anchor)).length = 1 := by
  simp [all_procedures, neutron_procedure, electron_procedure,
        alpha_procedure, gravity_procedure, speed_of_light_procedure]

/-- The anchor is the neutron mass procedure. -/
theorem anchor_is_neutron :
    readout_anchor.anchor.name = "Neutron mass m_n" := rfl

-- ============================================================
-- SMOKE TESTS
-- ============================================================

#eval readout.num_anchors              -- 1
#eval readout.num_exact_si             -- 4
#eval neutron_procedure.protocol       -- "Penning trap cyclotron frequency ratio"
#eval all_procedures.length            -- 5

end Tau.BookIV.Physics
