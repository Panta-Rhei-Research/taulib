-- ========== KERNEL (Parts I–II) ==========
import TauLib.BookI.Kernel.Signature
import TauLib.BookI.Kernel.Axioms
import TauLib.BookI.Kernel.Diagonal
import TauLib.BookI.Kernel.ActionQuantum

-- ========== ORBIT (Part III) ==========
import TauLib.BookI.Orbit.Generation
import TauLib.BookI.Orbit.Countability
import TauLib.BookI.Orbit.Closure
import TauLib.BookI.Orbit.Ladder
import TauLib.BookI.Orbit.Rigidity
import TauLib.BookI.Orbit.TooMany
import TauLib.BookI.Orbit.TooFew
import TauLib.BookI.Orbit.Saturation

-- ========== DENOTATION (Part IV) ==========
import TauLib.BookI.Denotation.TauIdx
import TauLib.BookI.Denotation.RankTransfer
import TauLib.BookI.Denotation.Arithmetic
import TauLib.BookI.Denotation.ProgramMonoid
import TauLib.BookI.Denotation.Equality
import TauLib.BookI.Denotation.Order
import TauLib.BookI.Denotation.Structural
import TauLib.BookI.Denotation.GrowthEscape
import TauLib.BookI.Denotation.SolenoidPitch

-- ========== COORDINATES (Part V) ==========
import TauLib.BookI.Coordinates.Primes
import TauLib.BookI.Coordinates.PrimeEnumeration
import TauLib.BookI.Coordinates.TowerAtoms
import TauLib.BookI.Coordinates.NormalForm
import TauLib.BookI.Coordinates.ABCD
import TauLib.BookI.Coordinates.NoTie
import TauLib.BookI.Coordinates.Descent
import TauLib.BookI.Coordinates.Hyperfact
import TauLib.BookI.Coordinates.ChebyshevBias

-- ========== POLARITY (Parts VI–VII) ==========
import TauLib.BookI.Polarity.Spectral
import TauLib.BookI.Polarity.Polarity
import TauLib.BookI.Polarity.ModArith
import TauLib.BookI.Polarity.OmegaGerms
import TauLib.BookI.Polarity.OmegaRing
import TauLib.BookI.Polarity.PrimeBridge
import TauLib.BookI.Polarity.ExtGCD
import TauLib.BookI.Polarity.ChineseRemainder
import TauLib.BookI.Polarity.NthPrime
import TauLib.BookI.Polarity.CRTBasis
import TauLib.BookI.Polarity.TeichmuellerLift
import TauLib.BookI.Polarity.PolarizedGerms
import TauLib.BookI.Polarity.BipolarAlgebra
import TauLib.BookI.Polarity.Lemniscate

-- ========== SETS (Part XIII) ==========
import TauLib.BookI.Sets.Membership
import TauLib.BookI.Sets.Operations
import TauLib.BookI.Sets.Powerset
import TauLib.BookI.Sets.Universe
import TauLib.BookI.Sets.Counting
import TauLib.BookI.Sets.CantorRefutation
import TauLib.BookI.Sets.UniqueInfinity
import TauLib.BookI.Sets.OrbitSets

-- ========== BOUNDARY (Parts VIII–X) ==========
import TauLib.BookI.Boundary.Ring
import TauLib.BookI.Boundary.SplitComplex
import TauLib.BookI.Boundary.Iota
import TauLib.BookI.Boundary.NumberTower
import TauLib.BookI.Boundary.Characters
import TauLib.BookI.Boundary.Spectral
import TauLib.BookI.Boundary.Fourier
import TauLib.BookI.Boundary.ConstructiveReals
import TauLib.BookI.Boundary.ComplexField
import TauLib.BookI.Boundary.Quaternions
import TauLib.BookI.Boundary.Cyclotomic
import TauLib.BookI.Boundary.Measure
import TauLib.BookI.Boundary.Integration
import TauLib.BookI.Boundary.Galois

-- ========== LOGIC (Part XI) ==========
import TauLib.BookI.Logic.Truth4
import TauLib.BookI.Logic.Explosion
import TauLib.BookI.Logic.BooleanRecovery

-- ========== HOLOMORPHY (Parts XII, XV–XVI) ==========
import TauLib.BookI.Holomorphy.DHolomorphic
import TauLib.BookI.Holomorphy.TauHolomorphic
import TauLib.BookI.Holomorphy.DiagonalProtection
import TauLib.BookI.Holomorphy.IdentityTheorem
import TauLib.BookI.Holomorphy.SpectralCoefficients
import TauLib.BookI.Holomorphy.Thinness
import TauLib.BookI.Holomorphy.GlobalHartogs
import TauLib.BookI.Holomorphy.BoundaryInterior
import TauLib.BookI.Holomorphy.PresheafEssence

-- ========== TOPOS (Part XIV) ==========
import TauLib.BookI.Topos.EarnedArrows
import TauLib.BookI.Topos.Functors
import TauLib.BookI.Topos.LimitsSites
import TauLib.BookI.Topos.EarnedTopos
import TauLib.BookI.Topos.CartesianProduct
import TauLib.BookI.Topos.WedgeProduct
import TauLib.BookI.Topos.InternalHom

-- ========== META-LOGIC (Part XVII) ==========
import TauLib.BookI.MetaLogic.Substrate
import TauLib.BookI.MetaLogic.LinearDiscipline
import TauLib.BookI.MetaLogic.LinearityAudit
import TauLib.BookI.MetaLogic.StructuralExclusion
import TauLib.BookI.MetaLogic.DiagonalResonance
import TauLib.BookI.MetaLogic.OnticInvariance
import TauLib.BookI.MetaLogic.ReceptionCriterion

-- ========== CONTINUED FRACTIONS ==========
import TauLib.BookI.CF.WindowAlgebra

/-!
# TauLib Book I — Categorical Foundations

All Lean 4 modules corresponding to Book I (Parts I–XVII).
79 chapters, 218 registry entries, 91 modules, zero sorry.

## Structure

- **Kernel** (Parts I–II): 5 generators, K0–K6 axioms, ρ operator
- **Orbit** (Part III): Generation, closure, iterator ladder
- **Denotation** (Part IV): τ-Idx, arithmetic, program monoid
- **Coordinates** (Part V): Normal form, ABCD chart, hyperfactorization
- **Polarity** (Parts VI–VII): Primes, lemniscate, bipolar algebra
- **Boundary** (Parts VIII–X): Ring, scalars, number systems, characters
- **Logic** (Part XI): Truth4, explosion, Boolean recovery
- **Holomorphy** (Parts XII, XV–XVI): D-holomorphic, Global Hartogs, presheaf essence
- **Sets** (Part XIII): Internal set theory, Cantor refutation
- **Topos** (Part XIV): Earned arrows, functors, sites, topos, bi-monoidal
- **MetaLogic** (Part XVII): Proof-theoretic mirror, structural exclusion, diagonal resonance, ontic invariance, reception criterion
- **CF**: Continued fraction window algebra
-/
