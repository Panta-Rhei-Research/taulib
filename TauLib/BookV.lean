-- Gravity (Part I)
import TauLib.BookV.Gravity.GravitationalConstant
import TauLib.BookV.Gravity.EinsteinEquation
import TauLib.BookV.Gravity.Schwarzschild
import TauLib.BookV.Gravity.CoRotorCoupling
import TauLib.BookV.Gravity.BHTopoModes

-- GravityField Scale (Part III addition)
import TauLib.BookV.GravityField.TauSchwarzschildScale

-- Prologue
import TauLib.BookV.Prologue.HermeticPrinciple
import TauLib.BookV.Prologue.ExportContract

-- Temporal (Part II first half)
import TauLib.BookV.Temporal.BaseCircle
import TauLib.BookV.Temporal.TemporalIgnition
import TauLib.BookV.Temporal.HighEnergy
import TauLib.BookV.Temporal.MacroReadout
-- Temporal (Part II second half)
import TauLib.BookV.Temporal.DistanceLadder
import TauLib.BookV.Temporal.BoundaryData
import TauLib.BookV.Temporal.CosmicAPI

-- GravityField (Part III: Frame Holonomy to Closing Identity, ch11-ch20)
import TauLib.BookV.GravityField.FrameHolonomy
import TauLib.BookV.GravityField.LorentzNoMinkowski
import TauLib.BookV.GravityField.TauEinsteinEq
import TauLib.BookV.GravityField.LinearEinstein
import TauLib.BookV.GravityField.NonlinearEinstein
import TauLib.BookV.GravityField.TauSchwarzschild
import TauLib.BookV.GravityField.TOVStarBuilder
import TauLib.BookV.GravityField.TOVPhaseBoundary
import TauLib.BookV.GravityField.CalibrationTriangle
import TauLib.BookV.GravityField.ClosingIdentity
import TauLib.BookV.GravityField.ExponentDerivation
import TauLib.BookV.GravityField.BipolarHolonomy

-- Thermodynamics (Part IV: Entropy, Heat, Vacuum, ch21-ch26)
import TauLib.BookV.Thermodynamics.Inversion
import TauLib.BookV.Thermodynamics.EntropySplitting
import TauLib.BookV.Thermodynamics.DefectExhaustion
import TauLib.BookV.Thermodynamics.HeatEM
import TauLib.BookV.Thermodynamics.VacuumNoVoid
import TauLib.BookV.Thermodynamics.DarkEnergyArtifact

-- FluidMacro (Part V: Navier-Stokes, Turbulence, Plasma, ch27-ch33)
import TauLib.BookV.FluidMacro.NavierStokesMacro
import TauLib.BookV.FluidMacro.Turbulence
import TauLib.BookV.FluidMacro.ChargeObstruction
import TauLib.BookV.FluidMacro.TauPlasma
import TauLib.BookV.FluidMacro.TauMHD
import TauLib.BookV.FluidMacro.TauAlfven
import TauLib.BookV.FluidMacro.PhaseTransitions

-- Astrophysics (Part V/VI: Classical to Large-Scale Structure, ch34-ch45)
import TauLib.BookV.Astrophysics.ClassicalIllusion
import TauLib.BookV.Astrophysics.KeplerSolarSystem
import TauLib.BookV.Astrophysics.GalaxyRelational
import TauLib.BookV.Astrophysics.RotationCurves
import TauLib.BookV.Astrophysics.CompactObjects
import TauLib.BookV.Astrophysics.Supernovae
import TauLib.BookV.Astrophysics.AccretionJets
import TauLib.BookV.Astrophysics.BinaryMergersGW
import TauLib.BookV.Astrophysics.EHTReread
import TauLib.BookV.Astrophysics.BulletClusterLSS
import TauLib.BookV.Astrophysics.SectorExhaustion
import TauLib.BookV.Astrophysics.H0TensionLCDM

-- Cosmology (Part VI/VII: Big Bang to Boundary Unification, ch46-ch56)
import TauLib.BookV.Cosmology.BigBangRegime
import TauLib.BookV.Cosmology.InflationRegime
import TauLib.BookV.Cosmology.ThresholdLadder
import TauLib.BookV.Cosmology.HeliumFraction
import TauLib.BookV.Cosmology.BBNBaryogenesis
import TauLib.BookV.Cosmology.BaryogenesisAsymmetry
import TauLib.BookV.Cosmology.BBNNuclearNetwork
import TauLib.BookV.Cosmology.BHBirthTopology
import TauLib.BookV.Cosmology.BHBipolarFusion
import TauLib.BookV.Cosmology.NoShrinkExtended
import TauLib.BookV.Cosmology.MergerNormalForm
import TauLib.BookV.Cosmology.GlobalFiniteness
import TauLib.BookV.Cosmology.CosmologicalEndstate
import TauLib.BookV.Cosmology.FalsificationPack
import TauLib.BookV.Cosmology.CMBSpectrum
import TauLib.BookV.Cosmology.NeutrinoBackground
import TauLib.BookV.Cosmology.Reionization
import TauLib.BookV.Cosmology.BoundaryUnification

-- Orthodox (Part VII: Orthodox Correspondence, ch58-66)
import TauLib.BookV.Orthodox.CorrespondenceMap
import TauLib.BookV.Orthodox.EmergentGeometry
import TauLib.BookV.Orthodox.OtherApproaches
import TauLib.BookV.Orthodox.MeasurementUnification
import TauLib.BookV.Orthodox.FalsifiableSeams

-- Coda (Part VIII: Bridge to Life, ch66-72)
import TauLib.BookV.Coda.ConstantsLedger
import TauLib.BookV.Coda.BridgeToLife
import TauLib.BookV.Coda.GAlphaBridge
import TauLib.BookV.Coda.CalibrationChain
import TauLib.BookV.Coda.HermeticClosure

/-!
# TauLib.BookV — Categorical Macrocosm

Master import file for Book V (Categorical Macrocosm) Lean modules.

Book V = base τ¹ of τ³ = τ¹ ×_f T² = temporal physics:
gravity, cosmology, black holes, thermodynamics, life.

## Module Organization

### Gravity (Part I: Gravitational Foundation)
- `GravitationalConstant`: G_τ from torus vacuum geometry, shape ratio r/R = ι_τ
- `EinsteinEquation`: τ-Einstein as boundary-character identity, κ_τ coupling
- `Schwarzschild`: R = 2G_τM, BH mass index, No-Shrink theorem
- `CoRotorCoupling`: co-rotor coupling κ_n, c₁ = 3/π, closing identity α_G = α¹⁸·(χκ_n/2)
- `BHTopoModes`: T² QNM modes, echo times, entropy ratio, no-Hawking argument

### Prologue
- `HermeticPrinciple`: fiber completeness (3 fiber + 2 base = 5), temporal complement recap
- `ExportContract`: 10-item export from Book IV (arena, sectors, couplings, invariants, R formula)

### Temporal (Part II: Temporal Structure, ch04-ch10)
- `BaseCircle`: base circle τ¹, alpha-ticks, proper time, causal ordering, geodesic duration
- `TemporalIgnition`: 3 temporal epochs, ignition depth, now-hypersurface, coherence horizon
- `HighEnergy`: maximal coupling, opening regime, unique τ-Einstein solutions, progression rate
- `MacroReadout`: null intertwiners, operational distance, redshift, expansion, Hubble parameter
- `DistanceLadder`: 5-rung distance ladder, Cepheid calibrator, BAO ruler, dark energy artifact
- `BoundaryData`: CMB surface, neutrino decoupling, recombination depth, CnuB surface
- `CosmicAPI`: 21-item cosmic stack API, scope distribution (19 τ-effective + 2 conjectural)

### GravityField (Part III: Frame Holonomy to Closing Identity, ch11-ch20)
- `FrameHolonomy`: Clopen frame, gravitational coupling, frame holonomy sector
- `LorentzNoMinkowski`: Null intertwiner, Lorentz from readout (no Minkowski)
- `TauEinsteinEq`: Curvature character, τ-Einstein equation derivation
- `LinearEinstein`: Newtonian limit, classical gravitational tests
- `NonlinearEinstein`: NF iteration, density saturation, nonlinear solutions
- `TauSchwarzschild`: Schwarzschild relation, BH evolution modes
- `TOVStarBuilder`: Stellar structure, Chandrasekhar limit, TOV equation
- `TOVPhaseBoundary`: Coherence horizon, topology crossing, phase boundary
- `CalibrationTriangle`: Calibration triangle, 3 vertices (G, κ_n, α_G)
- `ClosingIdentity`: α_G closing identity, 10-link gravitational chain

### Thermodynamics (Part IV: Entropy, Heat, Vacuum, ch21-ch26)
- `Inversion`: Classical second law inversion, holomorphic vs defect entropy
- `EntropySplitting`: S = S_def + S_ref decomposition, defect entropy decreasing
- `DefectExhaustion`: Defect functional minimization, exhaustion of defect types
- `HeatEM`: Heat as B-sector phenomenon, Planck distribution, Stefan-Boltzmann
- `VacuumNoVoid`: No true void, vacuum character, pair production, Unruh effect
- `DarkEnergyArtifact`: Dark energy as ΛCDM artifact, vacuum energy resolution

### FluidMacro (Part V: Navier-Stokes, Turbulence, Plasma, ch27-ch33)
- `NavierStokesMacro`: NS as τ-coarse-graining, viscous flow, Reynolds number
- `Turbulence`: Turbulence onset, Kolmogorov 5/3 law, inertial range
- `ChargeObstruction`: Charge-flux constraint, magnetic obstruction, Lorentz force
- `TauPlasma`: Plasma, Debye screening, plasma frequency, dispersion
- `TauMHD`: Magnetohydrodynamics, Alfvén waves, dynamo, reconnection
- `TauAlfven`: Alfvén wave modes, dispersion, damping, magnetoacoustic
- `PhaseTransitions`: Phase transitions, critical exponents, order parameters

### Astrophysics (Part V/VI: Classical to Large-Scale Structure, ch34-ch45)
- `ClassicalIllusion`: Classical mechanics as τ-readout limit, force-free ontology
- `KeplerSolarSystem`: Kepler laws, solar system, planetary orbits
- `GalaxyRelational`: Galaxy formation, relational structure, morphology
- `RotationCurves`: Rotation curves, no dark matter, boundary characters
- `CompactObjects`: White dwarfs, neutron stars, black holes, Chandrasekhar limit
- `Supernovae`: Type Ia/II supernovae, nucleosynthesis, remnants
- `AccretionJets`: Accretion disks, relativistic jets, AGN
- `BinaryMergersGW`: Binary mergers, gravitational waves, LIGO/Virgo
- `EHTReread`: Event Horizon Telescope reread, shadow predictions
- `BulletClusterLSS`: Bullet cluster, large-scale structure, no dark matter
- `SectorExhaustion`: Astrophysical sector exhaustion, all phenomena covered
- `H0TensionLCDM`: Hubble tension, LCDM artifacts, τ-resolution

### Cosmology (Part VI/VII: Big Bang to Boundary Unification, ch46-ch56)
- `BigBangRegime`: Big bang as opening regime, temporal opening, no singularity
- `InflationRegime`: Inflation as regime invariance, inflaton no-go, flatness, horizon
- `ThresholdLadder`: Six canonical thresholds EW→B→N→nuc→H→γ, nucleosynthesis, CMB
- `BaryogenesisAsymmetry`: η_B = α·ι_τ¹⁵·(5/6) = (121/270)·ι_τ¹⁹ upgrade to τ-effective; exponent 15 = dim(τ³)×|gen|
- `BHBirthTopology`: BH birth as topology crossing S²→T², linking class, information preservation
- `BHBipolarFusion`: Bipolar BHs, polarity imbalance, blueprint monoid, fusion closure
- `NoShrinkExtended`: No-shrink theorem, Hawking readout, no evaporation, permanence hallmark
- `MergerNormalForm`: Merger normal form, ringdown, primorial mass gap, Wilson loops, GW bound
- `GlobalFiniteness`: Finite motifs, saturation radius, absorbing pattern, global finiteness chain
- `CosmologicalEndstate`: Eternal circulation, two cosmic phases, no heat death, complexity
- `FalsificationPack`: 10 testable predictions across 3 falsification levels
- `BoundaryUnification`: 6 Hartogs squares, cross-coupling naturality, ι_τ mediates all 10

### Orthodox (Part VII: Orthodox Correspondence, ch58-66)
- `CorrespondenceMap`: Correspondence functor Phi, structural artifacts, readout protocol
- `EmergentGeometry`: GR as chart shadow, no singularities, sector exhaustion, native holography
- `OtherApproaches`: String theory, LQG, CDT, causal sets, twistors, NCG comparisons
- `MeasurementUnification`: VM quantum states, measurement dissolution, Bell inequality, decoherence
- `FalsifiableSeams`: No singularities, no UV, no dark sectors, vacuum zero, E1 full

### Coda (Part VIII: Bridge to Life, ch66-72)
- `ConstantsLedger`: 10-entry ledger, No Shrink restatement, testable seams, honest scope
- `BridgeToLife`: Export contracts VI/VII, Hermetic Truth, profinite ergodicity, EW bridge

## Current Count: 78 modules
-/
