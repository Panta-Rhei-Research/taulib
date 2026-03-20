import TauLib.BookIV.Physics.QuantityFramework
import TauLib.BookIV.Sectors.CouplingFormulas

/-!
# TauLib.BookIV.Physics.MassEnergy

Mass, energy, and the mass-energy structural relation in the τ-framework.

## Registry Cross-References

- [IV.D20] Mass Index — `MassIndex`
- [IV.D21] Energy Index — `EnergyIndex`
- [IV.D22] Speed Constant — `SpeedConstant`
- [IV.D23] Mass-Energy Relation — `MassEnergyRelation`
- [IV.R04] Neutron as first ontic particle — structural remark

## Mathematical Content

### Mass in the τ-Framework

Mass is the **inertial invariant of a persistent localized defect bundle**
with stable 2-torus T² fiber. It is NOT a postulated scalar but a
**boundary fixed-point** of the defect bundle's coherence functional:

    M_n(x) := MassIdx(NF_ω(x))

= α-Idx readout from normal-form stabilized configuration.

The **neutron** is the first ontic particle (minimal mass-bearing
defect bundle in τ). Beta decay is the shedding of subsidiary defect modes.

### Energy in the τ-Framework

Energy is the **coherence cost of maintaining a localized defect bundle
structure**. It is proportional to the defect-tuple magnitude and
stability degree.

### Mass-Energy Relation

    E = m_τ · c²_τ

where c_τ is the τ-derived speed-of-light constant. This relation
holds as a structural identity between the mass and energy indices.

### Particle Ontology

- **Ontic particles**: Persistent defect bundles with stable T² fiber (neutron, proton, ...)
- **Radiation**: Null transport with degenerate S¹ fiber (photon)
- **E = ℏω_τ**: Photon energy from transport frequency

## Ground Truth Sources
- particle-physics-defects.json: particle-ontology, mass definition
- quantum-mechanics.json: mass-energy equivalence
- gravity-einstein.json: BH mass index
-/

namespace Tau.BookIV.Physics

open Tau.Kernel Tau.Denotation Tau.Boundary Tau.BookIII.Sectors Tau.BookIV.Sectors

-- ============================================================
-- MASS INDEX [IV.D20]
-- ============================================================

/-- [IV.D20] Mass index: the inertial invariant of a persistent
    localized defect bundle.

    Mass = boundary fixed-point of the defect bundle's coherence
    functional = α-Idx readout from NF-stabilized configuration.

    Properties:
    - Not a primitive scalar but a resistance/scale index
    - Comes with minimal carrier that can host it
    - Monotone under admissible evolution (No-Shrink for BH) -/
structure MassIndex where
  /-- Mass value numerator (scaled). -/
  numer : Nat
  /-- Mass value denominator. -/
  denom : Nat
  /-- Denominator is positive. -/
  denom_pos : denom > 0
  /-- Carrier type (must be Fiber for ontic particles). -/
  carrier : CarrierType
  /-- Whether the defect bundle is persistent (stable T² fiber). -/
  is_persistent : Bool
  deriving Repr

/-- Float display for mass index. -/
def MassIndex.toFloat (m : MassIndex) : Float :=
  Float.ofNat m.numer / Float.ofNat m.denom

-- ============================================================
-- ENERGY INDEX [IV.D21]
-- ============================================================

/-- [IV.D21] Energy index: the coherence cost of maintaining a
    localized defect bundle structure.

    Energy ∝ defect-tuple magnitude × stability degree.
    Each sector provides its own excitation cost scale. -/
structure EnergyIndex where
  /-- Energy value numerator (scaled). -/
  numer : Nat
  /-- Energy value denominator. -/
  denom : Nat
  /-- Denominator is positive. -/
  denom_pos : denom > 0
  /-- Which sector provides the excitation. -/
  sector : Sector
  deriving Repr

/-- Float display for energy index. -/
def EnergyIndex.toFloat (e : EnergyIndex) : Float :=
  Float.ofNat e.numer / Float.ofNat e.denom

-- ============================================================
-- SPEED CONSTANT [IV.D22]
-- ============================================================

/-- [IV.D22] Speed-of-light constant c²_τ: the τ-derived structural
    constant relating mass and energy indices.

    c²_τ is not postulated but earned from the τ-kernel as the
    canonical conversion factor between defect-bundle mass indices
    and coherence cost indices. -/
structure SpeedConstant where
  /-- c² numerator (scaled). -/
  c_sq_numer : Nat
  /-- c² denominator. -/
  c_sq_denom : Nat
  /-- Denominator is positive. -/
  denom_pos : c_sq_denom > 0
  deriving Repr

/-- Float display for speed constant. -/
def SpeedConstant.toFloat (s : SpeedConstant) : Float :=
  Float.ofNat s.c_sq_numer / Float.ofNat s.c_sq_denom

-- ============================================================
-- MASS-ENERGY RELATION [IV.D23]
-- ============================================================

/-- [IV.D23] Mass-energy relation template: E = m · c²_τ.

    This is a structural identity relating the mass index to the
    energy index via the τ-derived speed constant. The relation
    holds as a cross-multiplication equality on scaled rationals:

    energy/1 = mass × c² means:
    E_numer · m_denom · c_denom = m_numer · E_denom · c_numer -/
structure MassEnergyRelation where
  /-- Mass index. -/
  mass : MassIndex
  /-- Energy index. -/
  energy : EnergyIndex
  /-- Speed constant c²_τ. -/
  speed : SpeedConstant
  /-- The structural identity: E = m · c². -/
  relation :
    energy.numer * mass.denom * speed.c_sq_denom =
    mass.numer * energy.denom * speed.c_sq_numer
  deriving Repr

-- ============================================================
-- PARTICLE PROPERTIES
-- ============================================================

/-- Ontic particles have fiber carrier (stable T² topology). -/
structure OnticParticle where
  /-- Mass of the particle. -/
  mass : MassIndex
  /-- Ontic particles are persistent. -/
  persistent_proof : mass.is_persistent = true
  /-- Ontic particles live on the fiber T². -/
  fiber_proof : mass.carrier = .Fiber
  deriving Repr

/-- Radiation has degenerate fiber (S¹, not T²). -/
structure RadiationCarrier where
  /-- Energy of the radiation. -/
  energy : EnergyIndex
  /-- Which sector (typically EM for photon). -/
  sector_proof : energy.sector = .B ∨ energy.sector = .D
  deriving Repr

-- ============================================================
-- NEUTRON AS FIRST ONTIC PARTICLE [IV.R04]
-- ============================================================

/-- [IV.R04] The neutron is the first ontic particle: the minimal
    mass-bearing defect bundle in τ.

    Properties:
    - Toroidal defect bundle on τ¹ (the "micro-donut")
    - Beta decay: neutron → proton + electron + ν_e
      (shedding subsidiary defect modes)
    - Stable in bound states; β-decay only when free

    This structure records the neutron's structural role.
    The numerical mass comes from the calibration cascade (Part VII). -/
structure NeutronRole where
  /-- Neutron mass index (first/minimal). -/
  mass : MassIndex
  /-- The neutron is ontic (persistent T² fiber). -/
  is_ontic : mass.is_persistent = true ∧ mass.carrier = .Fiber
  /-- The neutron mass is positive. -/
  mass_positive : mass.numer > 0
  deriving Repr

-- ============================================================
-- STRUCTURAL THEOREMS
-- ============================================================

/-- Ontic particles have Fiber carrier type. -/
theorem ontic_has_fiber (p : OnticParticle) :
    p.mass.carrier = .Fiber := p.fiber_proof

/-- Ontic particles are persistent. -/
theorem ontic_is_persistent (p : OnticParticle) :
    p.mass.is_persistent = true := p.persistent_proof

/-- The mass-energy relation implies energy > 0 when mass > 0
    and speed > 0 (structural). -/
theorem mass_energy_positive (r : MassEnergyRelation)
    (hm : r.mass.numer > 0) (hc : r.speed.c_sq_numer > 0) :
    r.energy.numer * r.mass.denom * r.speed.c_sq_denom > 0 := by
  rw [r.relation]
  exact Nat.mul_pos (Nat.mul_pos hm r.energy.denom_pos) hc

-- ============================================================
-- SMOKE TESTS
-- ============================================================

-- Example mass index (placeholder values)
#eval (MassIndex.mk 939565 1000000 (by omega) .Fiber true).toFloat  -- ~0.94 (scaled)

-- Example energy index
#eval (EnergyIndex.mk 939565 1000000 (by omega) .B).toFloat         -- ~0.94 (scaled)

end Tau.BookIV.Physics
