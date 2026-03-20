-- Prologue
import TauLib.BookIII.Prologue.HartogsBulk

-- Part I: Enrichment
import TauLib.BookIII.Enrichment.LayerTemplate
import TauLib.BookIII.Enrichment.Functor
import TauLib.BookIII.Enrichment.CanonicalLadder

-- Part II: Sectors
import TauLib.BookIII.Sectors.BoundaryCharacters
import TauLib.BookIII.Sectors.Decomposition
import TauLib.BookIII.Sectors.LanglandsReflection
import TauLib.BookIII.Sectors.ParityBridge

-- Part III: Spectral Algebra
import TauLib.BookIII.Spectral.PrimorialLadder
import TauLib.BookIII.Spectral.CRT
import TauLib.BookIII.Spectral.HenselLifting
import TauLib.BookIII.Spectral.LocalFields
import TauLib.BookIII.Spectral.Adeles
import TauLib.BookIII.Spectral.BipolarClassifier
import TauLib.BookIII.Spectral.Trichotomy
import TauLib.BookIII.Spectral.ModularForms
import TauLib.BookIII.Spectral.ConfinementBridge
import TauLib.BookIII.Spectral.AdditiveConjectures
import TauLib.BookIII.Spectral.SieveInfrastructure
import TauLib.BookIII.Spectral.GoldbachDeep
import TauLib.BookIII.Spectral.TwinPrimeDeep

-- Part IV: Spectral Doors
import TauLib.BookIII.Doors.MutualDetermination
import TauLib.BookIII.Doors.SplitComplexZeta
import TauLib.BookIII.Doors.LemniscateOperator
import TauLib.BookIII.Doors.SpectralCorrespondence
import TauLib.BookIII.Doors.CriticalLine
import TauLib.BookIII.Doors.GrandGRH
import TauLib.BookIII.Doors.Poincare
import TauLib.BookIII.Doors.MasterSchema
import TauLib.BookIII.Doors.SpectralDecomp
import TauLib.BookIII.Doors.BridgeTightening

-- Part V: Physics Layer
import TauLib.BookIII.Physics.FluidData
import TauLib.BookIII.Physics.HartogsFlow
import TauLib.BookIII.Physics.PositiveRegularity
import TauLib.BookIII.Physics.StrongSector
import TauLib.BookIII.Physics.GapTheorem
import TauLib.BookIII.Physics.Hodge
import TauLib.BookIII.Physics.PhysicsAssembly

-- Part VI: Arithmetic Mirror
import TauLib.BookIII.Arithmetic.EnrFunctor01
import TauLib.BookIII.Arithmetic.RationalPoints
import TauLib.BookIII.Arithmetic.ProtoCodes
import TauLib.BookIII.Arithmetic.BSD
import TauLib.BookIII.Arithmetic.Langlands
import TauLib.BookIII.Arithmetic.EnrichedBiSquare
import TauLib.BookIII.Arithmetic.TowerAssembly
import TauLib.BookIII.Arithmetic.ABCConjecture
import TauLib.BookIII.Arithmetic.ABCDeep

-- Part VII: Computation
import TauLib.BookIII.Computation.E2Agent
import TauLib.BookIII.Computation.TowerMachine
import TauLib.BookIII.Computation.Admissibility
import TauLib.BookIII.Computation.WitnessSearch
import TauLib.BookIII.Computation.CompBiSquare
import TauLib.BookIII.Computation.E2Witness

-- Part VIII: Hinge Theorem
import TauLib.BookIII.Hinge.DependencyChain
import TauLib.BookIII.Hinge.HingeTheorem

-- Part IX: Orthodox Bridge
import TauLib.BookIII.Bridge.ZFCasVM
import TauLib.BookIII.Bridge.ForbiddenMoves
import TauLib.BookIII.Bridge.Incompleteness
import TauLib.BookIII.Bridge.BridgeAxiom
import TauLib.BookIII.Bridge.TranslationArith
import TauLib.BookIII.Bridge.TranslationTopo
import TauLib.BookIII.Bridge.TranslationObstruction
import TauLib.BookIII.Bridge.ConjectureGaps

-- Part X: Mirror
import TauLib.BookIII.Mirror.ProofTheoryE3
import TauLib.BookIII.Mirror.Saturation
import TauLib.BookIII.Mirror.E3Witness

-- Part XI: Spectrum (τ-Turing Machine, Complexity Bridge)
import TauLib.BookIII.Spectrum.TTM
import TauLib.BookIII.Spectrum.InterfaceWidth
import TauLib.BookIII.Spectrum.ThreeSAT
import TauLib.BookIII.Spectrum.KernelHinge

/-!
# TauLib.BookIII — Categorical Spectrum

Master import file for Book III (Categorical Spectrum): The Eight Spectral
Forces of Mathematics. 50 modules covering the enrichment ladder (E₀⊊E₁⊊E₂⊊E₃),
spectral algebra, all 8 Millennium Problem treatments, computation layer,
orthodox bridge, and reflective coda.

## Module Count: 66

## Key Results
- III.T04: Canonical Ladder (E₀⊊E₁⊊E₂⊊E₃ unique and saturated)
- III.T23: Master Schema (8 Millennium Problems as Mutual Determination)
- III.T40: Tower Assembly (coherent bi-square scaling chain)
- III.T41: Hinge Theorem (Books IV-VII are sector instantiations)
- III.T47: Honest Claim (scope discipline verified)
- III.T49: Applied Saturation (E₃ terminal)

## Conjectural Axioms (3)
- `spectral_correspondence_O3` (III.T18): O₃ spectral gap
- `grand_grh_adelic` (III.T20): adelic GRH lift
- `bridge_functor_exists` (III.D71): bridge functor existence
-/
