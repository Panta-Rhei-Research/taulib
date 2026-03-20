import TauLib.BookIV.Physics.QuantityFramework

/-!
# TauLib.BookIV.Physics.DefectFunctional

The 4-component defect functional and fluid regime classification.

## Registry Cross-References

- [IV.D16] Defect Component — `DefectComponent`
- [IV.D17] Defect Tuple — `DefectTuple`
- [IV.D18] Fluid Regime — `FluidRegime`
- [IV.D19] Regime Signature — `RegimeSignature`

## Mathematical Content

### 4-Component Defect Functional

Every fluid state is classified by a 4-component defect tuple:

| Component | Description | Computation |
|-----------|-------------|-------------|
| Mobility | Local transport capability | Adjacency-graph diffusion rate |
| Vorticity | Rotational signature (Kelvin) | ∮ u·dl on boundary cycles |
| Compression | Volumetric density change | ∇·u on clopen adjacency |
| Topological | Winding/defect count | Defects on clopen tower |

All four are computed on **clopen adjacency graphs** WITHOUT importing the reals.

### 8 Fluid Regimes

The defect tuple's inequality pattern classifies 8 canonical fluid regimes:

| Regime | Key Signature |
|--------|---------------|
| Crystal | Periodic NF-code + arrested transport |
| Glass | Aperiodic + mobility < k_glass |
| Euler | Kelvin-invariant + defect-budget preserved (inviscid) |
| Navier-Stokes | Viscous shear-defect + dissipation normalizer |
| MHD | Coupled fluid+EM holonomy + frozen flux |
| Plasma | EM-active + boundary-obstruction transport |
| Superfluid | Quantized circulation (hard lattice) |
| Superconductor | EM-superfluid + quantized flux Φ_τ |

## Ground Truth Sources
- fluid-condensed-matter.json: defect-functional-spectrum, defect-functionals
- fluid-condensed-matter.json: regime classification, tau-superfluidity
-/

namespace Tau.BookIV.Physics

-- ============================================================
-- DEFECT COMPONENTS [IV.D16]
-- ============================================================

/-- [IV.D16] The 4 canonical defect components.
    These are the independent degrees of freedom in the defect functional,
    computed on clopen adjacency graphs without importing the reals. -/
inductive DefectComponent where
  /-- Local transport capability (diffusion rate on adjacency graph). -/
  | Mobility
  /-- Rotational motion signature (Kelvin-type circulation invariant). -/
  | Vorticity
  /-- Volumetric density change (∇·u incompressibility measure). -/
  | Compression
  /-- Winding/defect count on clopen tower (topological charge). -/
  | Topological
  deriving Repr, DecidableEq, BEq, Inhabited

-- ============================================================
-- DEFECT TUPLE [IV.D17]
-- ============================================================

/-- [IV.D17] Defect tuple: the 4-component functional that classifies
    fluid states and drives regularity.

    All components are non-negative scaled integers (representing
    defect magnitudes computed on finite clopen lattices). -/
structure DefectTuple where
  /-- Mobility defect value (scaled). -/
  mobility : Nat
  /-- Vorticity defect value (scaled). -/
  vorticity : Nat
  /-- Compression defect value (scaled). -/
  compression : Nat
  /-- Topological defect value (scaled). -/
  topological : Nat
  deriving Repr, DecidableEq, BEq

/-- Total defect budget: sum of all 4 components. -/
def DefectTuple.total (d : DefectTuple) : Nat :=
  d.mobility + d.vorticity + d.compression + d.topological

-- ============================================================
-- FLUID REGIMES [IV.D18]
-- ============================================================

/-- [IV.D18] The 8 canonical fluid regimes, classified by
    defect-tuple inequality patterns.

    Each regime is a τ-native formulation of a classical fluid type,
    defined WITHOUT importing the reals. -/
inductive FluidRegime where
  /-- Periodic NF-code + arrested transport.
      Physical: crystalline solid with periodic lattice. -/
  | Crystal
  /-- Aperiodic NF-code + mobility below glass threshold k_glass.
      Physical: amorphous solid (thermal aging). -/
  | Glass
  /-- Kelvin-invariant + defect-budget preserved (inviscid).
      Physical: ideal fluid with circulation conservation. -/
  | Euler
  /-- Viscous shear-defect dominant + dissipation normalizer.
      Physical: viscous fluid with energy dissipation. -/
  | NavierStokes
  /-- Coupled fluid + EM holonomy with frozen-flux axiom.
      Physical: magnetohydrodynamic flow (Alfvén modes). -/
  | MHD
  /-- EM-active fluid with boundary-obstruction transport.
      Physical: ionized gas with Debye screening. -/
  | Plasma
  /-- Quantized circulation constraint (hard lattice on plaquettes).
      Physical: superfluid with protected vortex defects. -/
  | Superfluid
  /-- EM-superfluid with quantized flux Φ_τ.
      Physical: superconductor (Meissner effect, Abrikosov vortices). -/
  | Superconductor
  deriving Repr, DecidableEq, BEq, Inhabited

-- ============================================================
-- REGIME SIGNATURE [IV.D19]
-- ============================================================

/-- [IV.D19] Regime signature: the structural properties that
    distinguish each fluid regime.

    Each regime is characterized by a combination of boolean flags
    and optional bounds on defect components. -/
structure RegimeSignature where
  /-- Which regime this signature describes. -/
  regime : FluidRegime
  /-- Upper bound on mobility (Some k = mobility ≤ k, None = no bound). -/
  mobility_bound : Option Nat
  /-- Whether Kelvin circulation invariant holds (∮ u·dl conserved). -/
  kelvin_invariant : Bool
  /-- Whether energy dissipation is present. -/
  dissipation : Bool
  /-- Whether coupled to EM holonomy sector. -/
  em_coupled : Bool
  /-- Whether circulation is quantized (hard lattice constraint). -/
  quantized_circulation : Bool
  /-- Whether compression defect must vanish (incompressibility). -/
  incompressible : Bool
  deriving Repr

-- ============================================================
-- CANONICAL REGIME SIGNATURES
-- ============================================================

/-- Crystal regime signature: arrested, no circulation, no dissipation. -/
def crystal_signature : RegimeSignature where
  regime := .Crystal
  mobility_bound := some 0           -- arrested transport
  kelvin_invariant := false
  dissipation := false
  em_coupled := false
  quantized_circulation := false
  incompressible := false

/-- Glass regime signature: arrested below threshold, aperiodic. -/
def glass_signature : RegimeSignature where
  regime := .Glass
  mobility_bound := some 1           -- below k_glass threshold
  kelvin_invariant := false
  dissipation := false
  em_coupled := false
  quantized_circulation := false
  incompressible := false

/-- Euler regime: inviscid, Kelvin-invariant, budget-preserving. -/
def euler_signature : RegimeSignature where
  regime := .Euler
  mobility_bound := none
  kelvin_invariant := true            -- circulation conserved
  dissipation := false                -- no energy dissipation
  em_coupled := false
  quantized_circulation := false
  incompressible := true              -- ∇·u = 0

/-- Navier-Stokes regime: viscous, dissipative. -/
def ns_signature : RegimeSignature where
  regime := .NavierStokes
  mobility_bound := none
  kelvin_invariant := false           -- viscosity breaks Kelvin
  dissipation := true                 -- energy dissipation present
  em_coupled := false
  quantized_circulation := false
  incompressible := true              -- ∇·u = 0 (incompressible NS)

/-- MHD regime: coupled fluid+EM, frozen flux. -/
def mhd_signature : RegimeSignature where
  regime := .MHD
  mobility_bound := none
  kelvin_invariant := false
  dissipation := true
  em_coupled := true                  -- EM holonomy coupled
  quantized_circulation := false
  incompressible := false

/-- Plasma regime: EM-active, mobile charges. -/
def plasma_signature : RegimeSignature where
  regime := .Plasma
  mobility_bound := none
  kelvin_invariant := false
  dissipation := true
  em_coupled := true                  -- EM sector active
  quantized_circulation := false
  incompressible := false

/-- Superfluid regime: quantized circulation, dissipation gap. -/
def superfluid_signature : RegimeSignature where
  regime := .Superfluid
  mobility_bound := none
  kelvin_invariant := true            -- quantized Kelvin invariant
  dissipation := false                -- dissipation suppressed by gap
  em_coupled := false
  quantized_circulation := true       -- ∮ u·dl ∈ {n·ℏ_τ}
  incompressible := true

/-- Superconductor regime: EM-superfluid, quantized flux. -/
def superconductor_signature : RegimeSignature where
  regime := .Superconductor
  mobility_bound := none
  kelvin_invariant := true
  dissipation := false                -- zero resistance
  em_coupled := true                  -- EM sector (Meissner effect)
  quantized_circulation := true       -- quantized flux tubes
  incompressible := true

/-- All 8 canonical regime signatures. -/
def all_regime_signatures : List RegimeSignature :=
  [crystal_signature, glass_signature, euler_signature, ns_signature,
   mhd_signature, plasma_signature, superfluid_signature, superconductor_signature]

/-- Regime signature lookup. -/
def regime_signature (r : FluidRegime) : RegimeSignature :=
  match r with
  | .Crystal => crystal_signature
  | .Glass => glass_signature
  | .Euler => euler_signature
  | .NavierStokes => ns_signature
  | .MHD => mhd_signature
  | .Plasma => plasma_signature
  | .Superfluid => superfluid_signature
  | .Superconductor => superconductor_signature

-- ============================================================
-- STRUCTURAL THEOREMS
-- ============================================================

/-- Exactly 4 defect components. -/
theorem four_components_exhaust (c : DefectComponent) :
    c = .Mobility ∨ c = .Vorticity ∨ c = .Compression ∨ c = .Topological := by
  cases c <;> simp

/-- Exactly 8 fluid regimes. -/
theorem eight_regimes_exhaust (r : FluidRegime) :
    r = .Crystal ∨ r = .Glass ∨ r = .Euler ∨ r = .NavierStokes ∨
    r = .MHD ∨ r = .Plasma ∨ r = .Superfluid ∨ r = .Superconductor := by
  cases r <;> simp

/-- Euler regime has no dissipation (inviscid). -/
theorem euler_no_dissipation :
    (regime_signature .Euler).dissipation = false := by rfl

/-- Euler regime preserves Kelvin circulation invariant. -/
theorem euler_kelvin_invariant :
    (regime_signature .Euler).kelvin_invariant = true := by rfl

/-- Navier-Stokes regime has dissipation. -/
theorem ns_has_dissipation :
    (regime_signature .NavierStokes).dissipation = true := by rfl

/-- Superfluid has quantized circulation. -/
theorem superfluid_quantized :
    (regime_signature .Superfluid).quantized_circulation = true := by rfl

/-- Superfluid has no dissipation (dissipation gap). -/
theorem superfluid_no_dissipation :
    (regime_signature .Superfluid).dissipation = false := by rfl

/-- Superconductor is EM-coupled (Meissner effect). -/
theorem superconductor_em_coupled :
    (regime_signature .Superconductor).em_coupled = true := by rfl

/-- Crystal regime has arrested transport (mobility bound = 0). -/
theorem crystal_arrested :
    (regime_signature .Crystal).mobility_bound = some 0 := by rfl

/-- MHD is EM-coupled (frozen flux). -/
theorem mhd_em_coupled :
    (regime_signature .MHD).em_coupled = true := by rfl

/-- Defect tuple total is sum of all components. -/
theorem defect_total_sum (d : DefectTuple) :
    d.total = d.mobility + d.vorticity + d.compression + d.topological := rfl

/-- All 8 regime signatures are present. -/
theorem all_signatures_count : all_regime_signatures.length = 8 := by rfl

-- ============================================================
-- SMOKE TESTS
-- ============================================================

#eval all_regime_signatures.length                          -- 8
#eval (regime_signature .Euler).dissipation                 -- false
#eval (regime_signature .NavierStokes).dissipation          -- true
#eval (regime_signature .Superfluid).quantized_circulation  -- true
#eval (regime_signature .Superconductor).em_coupled         -- true

-- Example defect tuple
#eval (DefectTuple.mk 100 50 0 3).total                    -- 153

end Tau.BookIV.Physics
