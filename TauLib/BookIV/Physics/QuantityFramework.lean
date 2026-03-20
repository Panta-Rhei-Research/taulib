import TauLib.BookIII.Sectors.Decomposition
import TauLib.BookI.Boundary.Iota

/-!
# TauLib.BookIV.Physics.QuantityFramework

Core structural types for τ-native physical quantities: the 5 primary
physical invariants, carrier types, and particle ontology.

## Registry Cross-References

- [IV.D09] Primary Invariant — `PrimaryInvariant`
- [IV.D10] Carrier Type — `CarrierType`
- [IV.D11] Physical Quantity Template — `PhysicalQuantity`
- [IV.D12] Particle Kind — `ParticleKind`

## Mathematical Content

The τ-framework replaces orthodox physics' independent postulated quantities
with **coherence invariants of defect dynamics** on τ¹ × T². Five primary
invariants exhaust the independent physical degrees of freedom:

| Invariant | τ-Definition | Carrier |
|-----------|-------------|---------|
| Entropy | Coherence defect novelty measure (S_def + S_ref) | Crossing |
| Time | Defect novelty event sequence parameter (ρ-iteration) | Base τ¹ |
| Energy | Coherence cost of maintaining localized defect bundle | Fiber T² |
| Mass | Inertial invariant of persistent T² defect bundle | Fiber T² |
| Gravity | Frame holonomy sector coupling (GR sector) | Base τ¹ |

All five are determined by ι_τ = 2/(π+e) via sector lift functors.

## Ground Truth Sources
- particle-physics-defects.json: five-physical-invariants
- quantum-mechanics.json: sector lift functors
- holonomy-sectors.json: sector-carrier correspondence
-/

namespace Tau.BookIV.Physics

open Tau.Kernel Tau.Denotation Tau.Boundary Tau.BookIII.Sectors

-- ============================================================
-- PRIMARY PHYSICAL INVARIANTS [IV.D09]
-- ============================================================

/-- [IV.D09] The 5 primary physical invariants of the τ-framework.
    These exhaust the independent physical degrees of freedom;
    all other physical quantities are derived from these five. -/
inductive PrimaryInvariant where
  /-- Coherence defect novelty measure: S = S_def + S_ref.
      S_def → 0 at coherence horizon; S_ref unbounded. -/
  | Entropy
  /-- Defect novelty event sequence parameter (ρ-iteration depth).
      Time emerges from defect dynamics ordering, NOT from spacetime. -/
  | Time
  /-- Coherence cost of maintaining localized defect bundle structure.
      Energy ∝ defect-tuple magnitude & stability degree. -/
  | Energy
  /-- Inertial invariant of persistent T² defect bundle.
      Mass = boundary-fixed-point of defect bundle's coherence functional. -/
  | Mass
  /-- Frame holonomy sector coupling (GR sector).
      Curvature = holonomy defect on frame transport. -/
  | Gravity
  deriving Repr, DecidableEq, BEq, Inhabited

-- ============================================================
-- CARRIER TYPE [IV.D10]
-- ============================================================

/-- [IV.D10] Carrier type for physical quantities in the τ³ = τ¹ ×_f T² fibration.
    Every physical quantity lives on exactly one of three carriers. -/
inductive CarrierType where
  /-- Lives on the fiber T² (spatial/microcosm = Book IV). -/
  | Fiber
  /-- Lives on the base τ¹ (temporal/macrocosm = Book V). -/
  | Base
  /-- Lives at the lemniscate crossing point L = S¹ ∨ S¹ (unpolarized). -/
  | Crossing
  deriving Repr, DecidableEq, BEq, Inhabited

-- ============================================================
-- PHYSICAL QUANTITY TEMPLATE [IV.D11]
-- ============================================================

/-- [IV.D11] Physical quantity template: a τ-native physical observable
    characterized by its primary invariant, carrier, governing sector,
    and structural properties. -/
structure PhysicalQuantity where
  /-- Display name. -/
  name : String
  /-- Which primary invariant this quantity belongs to. -/
  invariant : PrimaryInvariant
  /-- Where the quantity lives in τ³. -/
  carrier : CarrierType
  /-- Which holonomy sector governs this quantity. -/
  sector : Sector
  /-- Whether the quantity is σ-fixed (unpolarized, at crossing point). -/
  is_sigma_fixed : Bool
  /-- Whether the quantity is conserved under τ-admissible evolution. -/
  is_conserved : Bool
  deriving Repr

-- ============================================================
-- PARTICLE ONTOLOGY [IV.D12]
-- ============================================================

/-- [IV.D12] Particle classification in the τ-framework.
    The τ-kernel distinguishes three kinds of carriers. -/
inductive ParticleKind where
  /-- Persistent localized defect bundle with stable T² fiber.
      Example: neutron (first ontic particle = minimal mass-bearing config). -/
  | Ontic
  /-- Null transport along τ¹ with degenerate S¹ fiber (not T²).
      Example: photon (null transport with degenerate circular fiber). -/
  | Radiation
  /-- Intermediate exchange carrier (not persistent).
      Example: virtual photon in Feynman diagrams. -/
  | Virtual
  deriving Repr, DecidableEq, BEq, Inhabited

-- ============================================================
-- CANONICAL PRIMARY-INVARIANT → CARRIER ASSIGNMENT
-- ============================================================

/-- Canonical carrier assignment for each primary invariant. -/
def PrimaryInvariant.carrier : PrimaryInvariant → CarrierType
  | .Entropy => .Crossing   -- entropy is unpolarized (crossing point)
  | .Time    => .Base        -- time lives on base τ¹
  | .Energy  => .Fiber       -- energy lives on fiber T²
  | .Mass    => .Fiber       -- mass lives on fiber T²
  | .Gravity => .Base        -- gravity lives on base τ¹

/-- Canonical sector assignment for each primary invariant. -/
def PrimaryInvariant.sector : PrimaryInvariant → Sector
  | .Entropy => .Omega       -- entropy involves all sectors (crossing)
  | .Time    => .A           -- time = weak sector (temporal arrow)
  | .Energy  => .B           -- energy = EM sector (excitation cost)
  | .Mass    => .C           -- mass = strong sector (confinement)
  | .Gravity => .D           -- gravity = GR sector (frame holonomy)

-- ============================================================
-- THE 5 CANONICAL PHYSICAL QUANTITIES
-- ============================================================

/-- Entropy as physical quantity. -/
def entropy_quantity : PhysicalQuantity where
  name := "Entropy"
  invariant := .Entropy
  carrier := .Crossing
  sector := .Omega
  is_sigma_fixed := true    -- entropy is σ-fixed (unpolarized)
  is_conserved := false     -- S_ref grows unboundedly

/-- Time as physical quantity. -/
def time_quantity : PhysicalQuantity where
  name := "Time"
  invariant := .Time
  carrier := .Base
  sector := .A
  is_sigma_fixed := false   -- time has direction (arrow)
  is_conserved := false     -- time parameter increases monotonically

/-- Energy as physical quantity. -/
def energy_quantity : PhysicalQuantity where
  name := "Energy"
  invariant := .Energy
  carrier := .Fiber
  sector := .B
  is_sigma_fixed := true    -- energy is σ-fixed
  is_conserved := true      -- energy conserved under τ-admissible evolution

/-- Mass as physical quantity. -/
def mass_quantity : PhysicalQuantity where
  name := "Mass"
  invariant := .Mass
  carrier := .Fiber
  sector := .C
  is_sigma_fixed := true    -- mass is σ-fixed
  is_conserved := true      -- mass conserved (No-Shrink for BH)

/-- Gravity as physical quantity. -/
def gravity_quantity : PhysicalQuantity where
  name := "Gravity"
  invariant := .Gravity
  carrier := .Base
  sector := .D
  is_sigma_fixed := true    -- gravitational coupling is σ-fixed
  is_conserved := true      -- gravitational constant is fixed

/-- All 5 canonical physical quantities. -/
def all_quantities : List PhysicalQuantity :=
  [entropy_quantity, time_quantity, energy_quantity, mass_quantity, gravity_quantity]

-- ============================================================
-- STRUCTURAL THEOREMS
-- ============================================================

/-- Exactly 5 primary invariants. -/
theorem five_invariants_exhaust (p : PrimaryInvariant) :
    p = .Entropy ∨ p = .Time ∨ p = .Energy ∨ p = .Mass ∨ p = .Gravity := by
  cases p <;> simp

/-- Exactly 3 carrier types. -/
theorem three_carriers_exhaust (c : CarrierType) :
    c = .Fiber ∨ c = .Base ∨ c = .Crossing := by
  cases c <;> simp

/-- Exactly 3 particle kinds. -/
theorem three_particle_kinds (k : ParticleKind) :
    k = .Ontic ∨ k = .Radiation ∨ k = .Virtual := by
  cases k <;> simp

/-- Gravity is the unique base-carrier primary invariant
    among those with σ-fixed property. -/
theorem gravity_unique_sigma_fixed_base :
    gravity_quantity.carrier = .Base ∧
    gravity_quantity.is_sigma_fixed = true ∧
    time_quantity.is_sigma_fixed = false := by
  exact ⟨rfl, rfl, rfl⟩

/-- Energy and Mass both live on the fiber T². -/
theorem energy_mass_fiber :
    energy_quantity.carrier = .Fiber ∧ mass_quantity.carrier = .Fiber := by
  exact ⟨rfl, rfl⟩

/-- All 5 canonical quantities use distinct primary invariants. -/
theorem all_quantities_distinct :
    entropy_quantity.invariant ≠ time_quantity.invariant ∧
    entropy_quantity.invariant ≠ energy_quantity.invariant ∧
    entropy_quantity.invariant ≠ mass_quantity.invariant ∧
    entropy_quantity.invariant ≠ gravity_quantity.invariant ∧
    time_quantity.invariant ≠ energy_quantity.invariant ∧
    time_quantity.invariant ≠ mass_quantity.invariant ∧
    time_quantity.invariant ≠ gravity_quantity.invariant ∧
    energy_quantity.invariant ≠ mass_quantity.invariant ∧
    energy_quantity.invariant ≠ gravity_quantity.invariant ∧
    mass_quantity.invariant ≠ gravity_quantity.invariant := by
  simp [entropy_quantity, time_quantity, energy_quantity, mass_quantity, gravity_quantity]

-- ============================================================
-- SMOKE TESTS
-- ============================================================

#eval all_quantities.length          -- 5
#eval entropy_quantity.carrier       -- Crossing
#eval time_quantity.sector           -- A (Weak)
#eval energy_quantity.is_conserved   -- true
#eval mass_quantity.is_sigma_fixed   -- true

-- ============================================================
-- CATEGORICAL ONTOLOGY LAYER [IV.D321a-e]
-- ============================================================

/-- [IV.D321a] An internal quantity as a categorical object.
    Each quantity IS its generator action — a functor from a sector
    subcategory of τ³ to its internal hom. This replaces the metadata-level
    PhysicalQuantity with a definitional categorical characterization.

    The `generator` field names the τ-generator whose minimal endomorphism
    defines this quantity. The `carrier_space` identifies whether the
    endomorphism acts on base τ¹, fiber T², or the crossing L. -/
structure InternalQuantity where
  /-- The primary invariant this quantity instantiates. -/
  invariant : PrimaryInvariant
  /-- The τ-generator whose action defines this quantity.
      α=gravity, π=time, γ=energy, η=mass, ω=entropy. -/
  generator : String
  /-- Where the generator acts: "End(τ¹)" for base, "End(T²)" for fiber,
      "Aut(L)" for crossing. -/
  endomorphism_type : String
  /-- Governing sector. -/
  sector : Sector
  /-- Carrier type. -/
  carrier : CarrierType
  /-- Whether the quantity is conserved. -/
  is_conserved : Bool
  deriving Repr

/-- Time as generator action: π-endomorphism of base τ¹. -/
def time_internal : InternalQuantity where
  invariant := .Time
  generator := "π"
  endomorphism_type := "End(τ¹)_A"
  sector := .A
  carrier := .Base
  is_conserved := false

/-- Energy as generator action: γ-endomorphism of fiber T². -/
def energy_internal : InternalQuantity where
  invariant := .Energy
  generator := "γ"
  endomorphism_type := "End(T²)_B"
  sector := .B
  carrier := .Fiber
  is_conserved := true

/-- Mass as generator action: η-fixed point on fiber T². -/
def mass_internal : InternalQuantity where
  invariant := .Mass
  generator := "η"
  endomorphism_type := "End(T²)_C"
  sector := .C
  carrier := .Fiber
  is_conserved := true

/-- Gravity as generator action: α-endomorphism of base τ¹. -/
def gravity_internal : InternalQuantity where
  invariant := .Gravity
  generator := "α"
  endomorphism_type := "End(τ¹)_D"
  sector := .D
  carrier := .Base
  is_conserved := true

/-- Entropy as generator action: ω-crossing automorphism of L. -/
def entropy_internal : InternalQuantity where
  invariant := .Entropy
  generator := "ω"
  endomorphism_type := "Aut(L)_{B∩C}"
  sector := .Omega
  carrier := .Crossing
  is_conserved := false

/-- All 5 internal quantities. -/
def all_internal_quantities : List InternalQuantity :=
  [time_internal, energy_internal, mass_internal, gravity_internal, entropy_internal]

/-- The categorical layer is consistent with the metadata layer:
    same sector assignment for each invariant. -/
theorem categorical_consistent_with_metadata :
    time_internal.sector = time_quantity.sector ∧
    energy_internal.sector = energy_quantity.sector ∧
    mass_internal.sector = mass_quantity.sector ∧
    gravity_internal.sector = gravity_quantity.sector ∧
    entropy_internal.sector = entropy_quantity.sector := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Each internal quantity has a distinct generator. -/
theorem internal_generators_distinct :
    time_internal.generator ≠ energy_internal.generator ∧
    time_internal.generator ≠ mass_internal.generator ∧
    time_internal.generator ≠ gravity_internal.generator ∧
    time_internal.generator ≠ entropy_internal.generator ∧
    energy_internal.generator ≠ mass_internal.generator ∧
    energy_internal.generator ≠ gravity_internal.generator ∧
    energy_internal.generator ≠ entropy_internal.generator ∧
    mass_internal.generator ≠ gravity_internal.generator ∧
    mass_internal.generator ≠ entropy_internal.generator ∧
    gravity_internal.generator ≠ entropy_internal.generator := by
  simp [time_internal, energy_internal, mass_internal, gravity_internal, entropy_internal]

end Tau.BookIV.Physics
