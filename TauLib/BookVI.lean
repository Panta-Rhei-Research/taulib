-- LifeCore (Part 1: Parity Bridge, Distinction, SelfDesc, Layer Separation)
import TauLib.BookVI.LifeCore.ParityBridge
import TauLib.BookVI.LifeCore.Distinction
import TauLib.BookVI.LifeCore.SelfDesc
import TauLib.BookVI.LifeCore.LayerSep

-- Sectors (Part 1 cont: Life Loops, 4+1 Sectors, Hallmarks, Absence)
import TauLib.BookVI.Sectors.LifeLoop
import TauLib.BookVI.Sectors.FourPlusOne
import TauLib.BookVI.Sectors.Hallmarks
import TauLib.BookVI.Sectors.Absence

-- Persistence (Part 2: Temporal Stability, Circadian Rhythms, Homochirality)
import TauLib.BookVI.Persistence.PersistenceSector
import TauLib.BookVI.Persistence.TemporalLemniscate

-- Agency (Part 3: Spatial Motility, ATP, Membranes)
import TauLib.BookVI.Agency.AgencySector
import TauLib.BookVI.Agency.MetabolicEnergy

-- Source (Part 4: Structure Generation, Photosynthesis, Genetic Code)
import TauLib.BookVI.Source.SourceSector
import TauLib.BookVI.Source.GeneticCode
import TauLib.BookVI.Source.Epigenetics

-- Closure (Part 5: Structure Recycling, Death/Aging, Ecosystems)
import TauLib.BookVI.Closure.ClosureSector
import TauLib.BookVI.Closure.Ecosystem

-- Consumer (Part 6: Mixed Sector, Fiber Regime, Reproduction, Evolution, Immunity, Neural, Identity)
import TauLib.BookVI.Consumer.ConsumerMixer
import TauLib.BookVI.Consumer.FiberRegime
import TauLib.BookVI.Consumer.Reproduction
import TauLib.BookVI.Consumer.Evolution
import TauLib.BookVI.Consumer.Immune
import TauLib.BookVI.Consumer.Neural
import TauLib.BookVI.Consumer.Identity

-- CosmicLife (Part 7: BH Distinction, BH SelfDesc, Crossing Limit, Galaxy Basins)
import TauLib.BookVI.CosmicLife.BHDist
import TauLib.BookVI.CosmicLife.BHSelfDesc
import TauLib.BookVI.CosmicLife.CrossLimit
import TauLib.BookVI.CosmicLife.GalaxyBasin

-- Mind (Part 8: Consciousness, Language, Bridge to Book VII)
import TauLib.BookVI.Mind.Consciousness
import TauLib.BookVI.Mind.Bridge

/-!
# TauLib.BookVI — Categorical Life

Master import file for Book VI (Categorical Life) Lean modules.

Book VI = E₂ enrichment layer: from categorical structure to living systems.
Life = τ-Distinction AND SelfDesc. Five life sectors from π₁(τ³).

## Module Organization

### LifeCore (Part 1: Foundations of Life)
- `ParityBridge`: Polarity functional, weak-sector uniqueness, Parity Bridge Theorem
- `Distinction`: τ-Distinction predicate (5 conditions), carrier types, well-definedness
- `SelfDesc`: SelfDesc predicate, internal evaluator, closure theorem
- `LayerSep`: Layer Separation Lemma, NS-TOV counterexample, loop factorization

### Sectors (Parts 1-2: Life Sectors and Hallmarks)
- `LifeLoop`: Life Loop class, DecodeTarget/Horizon, Metabolic Fiber Theorem
- `FourPlusOne`: 5 life sectors (persistence, agency, source, closure, consumer)
- `Hallmarks`: 7 hallmarks derived from Distinction+SelfDesc
- `Absence`: NoDist/NoSelfDesc failure modes, virus/neutron/NS counterexamples

### Persistence (Part 2: Temporal Stability)
- `PersistenceSector`: Persistence sector (α-base), temporal stability, abiogenesis
- `TemporalLemniscate`: Temporal lemniscate L_T, circadian rhythms, homochirality

### Agency (Part 3: Spatial Motility)
- `AgencySector`: Agency sector (π-base), spatial motility, chemotaxis
- `MetabolicEnergy`: ATP uniqueness, membrane as L, Krebs cycle, self-assembly

### Source (Part 4: Structure Generation)
- `SourceSector`: Source sector (π'-fiber), structure generation, photosynthesis
- `GeneticCode`: BSD genetic code, codon error correction, Turing/Hodge, central dogma
- `Epigenetics`: Chromatin partition, epigenetic state, Waddington landscape, cell fate, drift

### Closure (Part 5: Structure Recycling)
- `ClosureSector`: Closure sector (π''-fiber), structure recycling, aging/death
- `Ecosystem`: Inter-sector web, ecosystem Poincaré circulation, repair budget

### Consumer (Part 6: Mixed Sector and Animal Life)
- `ConsumerMixer`: Consumer mixer (π',π''), signature rigidity, bridge-head to E₃
- `FiberRegime`: Eukaryotic innovations, multicellularity as colimit, development
- `Reproduction`: Recombination functor, sex as second distinction
- `Evolution`: PPAS fitness, evolution as optimization, fitness landscape topology
- `Immune`: Cellular distinction (MHC), autoimmunity as five failure modes
- `Neural`: Neural architecture as τ³ computer, sleep as lemniscate second lobe
- `Identity`: SelfDesc over code not carrier, substrate replacement preserves life

### CosmicLife (Part 7: Black Holes as Living Systems)
- `BHDist`: Macro-torus carrier, lexicographic defect, BH Distinction Theorem
- `BHSelfDesc`: BH DecodeTarget/Horizon, uniqueness, BH SelfDesc Theorem
- `CrossLimit`: ω-representative, Lift_ω, Crossing-Limit Theorem, universal BH
- `GalaxyBasin`: Life basins, carrier ladder, basin predicate, Anchor Lemma

### Mind (Part 8: Consciousness, Language, Bridge)
- `Consciousness`: Structural self-model, minimal conscious agent, VI.T38 crown jewel
- `Bridge`: Enrichment saturation, extended lemniscate, language, six exports, ω-germ boundary

## Current Count: 30 modules
-/
