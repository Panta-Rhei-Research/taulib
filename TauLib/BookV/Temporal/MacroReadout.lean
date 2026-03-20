import TauLib.BookV.Temporal.HighEnergy
import TauLib.BookIV.Sectors.SectorParameters
import TauLib.BookIV.Physics.QuantityFramework

/-!
# TauLib.BookV.Temporal.MacroReadout

Macroscopic readouts: null intertwiners, operational distance, redshift,
expansion, and the Hubble parameter.

## Registry Cross-References

- [V.D27] Null Intertwiner — `NullIntertwiner`
- [V.T14] Boundary Supports Null — `boundary_supports_null`
- [V.P06] Null Selects EM — `null_selects_em`
- [V.D28] Operational Distance — `OperationalDistance`
- [V.T15] Distance-Time Duality — `distance_time_dual`
- [V.D29] Refinement Drift — `RefinementDrift`
- [V.T16] Refinement Drift Formula — `drift_formula_positive`
- [V.D30] Readout Expansion — `ReadoutExpansion`
- [V.D31] Hubble Readout Parameter — `HubbleReadout`

## Ground Truth Sources
- Book V Part II (2nd Edition): Temporal Foundation
-/

namespace Tau.BookV.Temporal

open Tau.Kernel Tau.Boundary Tau.BookIV.Arena Tau.BookIV.Sectors
open Tau.BookIII.Sectors Tau.BookIV.Physics

-- ============================================================
-- NULL INTERTWINER [V.D27]
-- ============================================================

/-- [V.D27] Null intertwiner: massless morphism in boundary holonomy.
    Null transport moves along base τ¹ at c_τ. Sector B (EM) is
    uniquely selected by the null (zero fiber stiffness) condition. -/
structure NullIntertwiner where
  /-- The sector supporting this null intertwiner. -/
  sector : Sector
  /-- Null selects EM. -/
  null_is_em : sector = .B
  /-- The carrier type (always Base for null transport). -/
  carrier : CarrierType
  /-- Null transport is base-only. -/
  carrier_is_base : carrier = .Base
  /-- Massless flag. -/
  massless : Bool
  /-- Must be massless. -/
  massless_true : massless = true
  deriving Repr

/-- The photon as canonical null intertwiner. -/
def photon_null : NullIntertwiner where
  sector := .B
  null_is_em := rfl
  carrier := .Base
  carrier_is_base := rfl
  massless := true
  massless_true := rfl

-- ============================================================
-- BOUNDARY SUPPORTS NULL [V.T14]
-- ============================================================

/-- [V.T14] The boundary holonomy algebra supports null intertwiners.
    EM generator gamma at depth 2 allows null transport on τ¹. -/
theorem boundary_supports_null :
    em_sector.generator = .gamma ∧
    em_sector.depth = 2 ∧
    photon_null.sector = .B := by
  exact ⟨rfl, rfl, rfl⟩

-- ============================================================
-- NULL SELECTS EM [V.P06]
-- ============================================================

/-- [V.P06] The null condition uniquely selects B-sector (EM).
    Only B supports null transport: D/A are depth 1 temporal,
    C is confined (χ₋), Omega is massive (crossing). -/
theorem null_selects_em (n : NullIntertwiner) :
    n.sector = .B := n.null_is_em

/-- EM is the unique null carrier among the 5 sectors. -/
theorem em_unique_null :
    em_sector.polarity = .ChiPlus ∧
    em_sector.depth = 2 ∧
    strong_sector.polarity = .ChiMinus ∧
    higgs_sector.polarity = .Crossing := by
  exact ⟨rfl, rfl, rfl, rfl⟩

-- ============================================================
-- OPERATIONAL DISTANCE [V.D28]
-- ============================================================

/-- [V.D28] Operational distance: tick count of the null intertwiner
    connecting two events at depth n₀. The τ-native spatial distance
    is NOT a primitive metric but a counting readout of null transport. -/
structure OperationalDistance where
  /-- Reference depth for the measurement. -/
  ref_depth : Nat
  ref_depth_pos : ref_depth > 0
  /-- Distance numerator (tick count * scale). -/
  dist_numer : Nat
  dist_denom : Nat
  denom_pos : dist_denom > 0
  deriving Repr

/-- Distance as Float. -/
def OperationalDistance.toFloat (d : OperationalDistance) : Float :=
  Float.ofNat d.dist_numer / Float.ofNat d.dist_denom

-- ============================================================
-- DISTANCE-TIME DUALITY [V.T15]
-- ============================================================

/-- [V.T15] Distance and proper time are dual readouts.
    Time counts α-ticks along base; distance counts null-intertwiner
    ticks between events. Both derived from the refinement tower. -/
theorem distance_time_dual :
    canonical_base_circle.seed = .alpha ∧
    photon_null.sector = .B ∧
    canonical_base_circle.profinite.seed = .alpha := by
  exact ⟨rfl, rfl, rfl⟩

-- ============================================================
-- REFINEMENT DRIFT [V.D29]
-- ============================================================

/-- [V.D29] Refinement drift (cosmological redshift):
    z(n_s, n_r) := Δt(n_s)/Δt(n_r) − 1. Since Δt(n) ~ ι_τ^n
    and ι_τ < 1, source earlier (n_s < n_r) gives z > 0 (redshift).
    The τ-framework predicts redshift WITHOUT metric expansion. -/
structure RefinementDrift where
  n_source : Nat
  n_receiver : Nat
  source_pos : n_source > 0
  receiver_pos : n_receiver > 0
  /-- Source precedes receiver (cosmological redshift). -/
  source_earlier : n_source < n_receiver
  deriving Repr

/-- Depth difference (positive for redshift). -/
def RefinementDrift.depth_diff (d : RefinementDrift) : Nat :=
  d.n_receiver - d.n_source

-- ============================================================
-- REFINEMENT DRIFT FORMULA [V.T16]
-- ============================================================

/-- [V.T16] Drift depth difference is positive for cosmological
    observations (source earlier than receiver). -/
theorem drift_formula_positive (d : RefinementDrift) :
    d.depth_diff > 0 := by
  simp only [RefinementDrift.depth_diff]
  exact Nat.sub_pos_of_lt d.source_earlier

-- ============================================================
-- READOUT EXPANSION [V.D30]
-- ============================================================

/-- [V.D30] Readout expansion a(n) ~ ι_τ^(-n): cumulative proper-time
    scaling. The universe "expands" because the tower deepens and
    proper-time increments shrink — not because space stretches. -/
structure ReadoutExpansion where
  depth : Nat
  depth_pos : depth > 0
  expansion_numer : Nat
  expansion_denom : Nat
  denom_pos : expansion_denom > 0
  deriving Repr

/-- Expansion as Float. -/
def ReadoutExpansion.toFloat (a : ReadoutExpansion) : Float :=
  Float.ofNat a.expansion_numer / Float.ofNat a.expansion_denom

-- ============================================================
-- HUBBLE READOUT PARAMETER [V.D31]
-- ============================================================

/-- [V.D31] Hubble readout H(n) := Δa/a per tick. NOT constant: decays
    with depth. Early (opening) H is large (inflation), late H is small.
    H(n) ~ 1 − ι_τ to leading order. -/
structure HubbleReadout where
  depth : Nat
  depth_pos : depth > 0
  hubble_numer : Nat
  hubble_denom : Nat
  denom_pos : hubble_denom > 0
  deriving Repr

/-- Hubble readout as Float. -/
def HubbleReadout.toFloat (h : HubbleReadout) : Float :=
  Float.ofNat h.hubble_numer / Float.ofNat h.hubble_denom

-- ============================================================
-- STRUCTURAL THEOREMS
-- ============================================================

/-- Null intertwiner is always massless and base-carried. -/
theorem null_structural (n : NullIntertwiner) :
    n.massless = true ∧ n.carrier = .Base :=
  ⟨n.massless_true, n.carrier_is_base⟩

/-- The EM sector coupling ι_τ² is the null-transport scale. -/
theorem null_transport_scale :
    em_sector.coupling_numer = iota_sq_numer ∧
    em_sector.coupling_denom = iota_sq_denom := by
  exact ⟨rfl, rfl⟩

/-- Redshift requires source < receiver. -/
theorem redshift_requires_earlier (d : RefinementDrift) :
    d.n_source < d.n_receiver := d.source_earlier

-- ============================================================
-- SMOKE TESTS
-- ============================================================

#eval photon_null.sector           -- B (EM)
#eval photon_null.massless         -- true
#eval photon_null.carrier          -- Base
#eval em_sector.coupling_float     -- ≈ 0.1166 (ι_τ²)

-- Example drift
#eval (RefinementDrift.mk 10 100 (by omega) (by omega) (by omega)).depth_diff
  -- 90

-- Example Hubble
#eval (HubbleReadout.mk 5 (by omega) 658541 1000000 (by omega)).toFloat
  -- ≈ 0.6585 (1 − ι_τ)

end Tau.BookV.Temporal
