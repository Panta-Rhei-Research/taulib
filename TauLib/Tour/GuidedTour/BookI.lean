import TauLib.BookI.Kernel.Signature
import TauLib.BookI.Kernel.Axioms
import TauLib.BookI.Coordinates.Hyperfact
import TauLib.BookI.Coordinates.NoTie
import TauLib.BookI.Polarity.Polarity
import TauLib.BookI.Boundary.Characters
import TauLib.BookI.Boundary.SplitComplex
import TauLib.BookI.Holomorphy.DHolomorphic
import TauLib.BookI.Holomorphy.GlobalHartogs
import TauLib.BookI.Logic.Truth4
import TauLib.BookI.Logic.Explosion
import TauLib.BookI.Topos.EarnedTopos
import TauLib.BookIII.Spectrum.KernelHinge

open Tau.Kernel Tau.Orbit Tau.Denotation Tau.Boundary Tau.Polarity
open Tau.Coordinates Tau.Holomorphy
open Tau.Logic Tau.Topos
open Tau.Spectrum

/-!
# Guided Tour Companion: Book I — How Mathematics Is Earned

**Companion to**: `launch/guided-tours/guided-tour-book-I.pdf`

This Lean module walks through the 7 structural hinges of Book I,
letting you verify each one by stepping through the actual formalization.
Each section corresponds to a hinge in the whitepaper.
-/

-- ================================================================
-- HINGE 1: Five Generators and Seven Axioms [I.D01, K0–K6]
-- ================================================================

/-
The coherence kernel: 5 generators, 1 operator, 7 axioms.
Everything in the series traces back to these primitives.
-/

-- The five generators as an inductive type
#check Generator
-- Generator : Type
-- Constructors: alpha, pi, gamma, eta, omega

-- The strict order K1
#check K1_strict_order
-- K1: alpha < pi < gamma < eta < omega

-- The progression operator and its axioms
#check rho
-- rho : TauObj → TauObj

#check K2_omega_fixed
-- K2: ρ fixes omega (the beacon)

#check K3_orbit_seeded
-- K3: orbit-seeded generation

#check K4_no_jump
-- K4: the no-jump / cover axiom

#check K5_beacon_non_succ
-- K5: omega is not a successor

-- Generator distinctness (consequence of K1)
#check gen_distinct
-- All five generators are pairwise distinct


-- ================================================================
-- HINGE 2: Hyperfactorization Theorem [I.T04]
-- ================================================================

/-
Every integer X ≥ 2 admits a unique ABCD decomposition.
The No-Tie Lemma ensures uniqueness; the greedy peel gives existence.
-/

-- The ABCD validity predicate
#check ValidABCD

-- The No-Tie Lemma: different (B,C) pairs cannot produce equal products
#check no_tie

-- Computational verification of hyperfactorization
#check hyperfact_check


-- ================================================================
-- HINGE 3: Prime Polarity and the Lemniscate [I.T09]
-- ================================================================

/-
Primes induce bipolar polarizations via CRT. The ensemble yields
the algebraic lemniscate L = S¹ ∨ S¹.
-/

-- The fundamental characters χ₊ and χ₋
#check chi_plus
#check chi_minus

-- Character completeness: χ₊(x) + χ₋(x) = x
#check chi_complete

-- Character orthogonality: χ₊(x) · χ₋(y) = 0
#check chi_orthogonal

-- Sigma swaps characters: χ₊^σ = χ₋
#check sigma_swaps_chi_plus
#check sigma_swaps_chi_minus


-- ================================================================
-- HINGE 4: Split-Complex Holomorphy [I.D42–I.T21]
-- ================================================================

/-
j² = +1 (not i² = -1). Zero divisors are sector selectors,
not pathologies. The diagonal discipline K6 tames them.
-/

-- The split-complex ring structure
#check SplitComplex

-- D-holomorphic functions: sector independence
#check is_sector_independent

-- The sector form: ∂F₊/∂v = 0 and ∂F₋/∂u = 0
#check sector_fun_independent


-- ================================================================
-- HINGE 5: Global Hartogs Extension [I.T31]
-- ================================================================

/-
Boundary determines interior. Every holomorphic function on the
boundary extends uniquely to the interior.
-/

#check HartogsData


-- ================================================================
-- HINGE 6: Earned Topos and Paraconsistent Logic [I.D59, I.P27]
-- ================================================================

/-
Four truth values: True, False, Both, Neither.
Explosion is blocked (B ⇒ F = N ≠ T), but the lattice is Boolean.
-/

-- The four truth values
#check Truth4
-- Inductive type with: T, F, B, N

-- The explosion barrier
#check explosion_barrier
-- B ⇒ F = N (not T)

-- The earned topos
#check EarnedTopos


-- ================================================================
-- HINGE 7: Kernel Hinge Diagram [I.D74]
-- ================================================================

/-
The complete dependency DAG from axioms to Book II export.
The bridge is proved complete: all exports are earned.
-/

-- The Book II bridge structure
#check KernelHinge

-- Bridge completeness: all fields instantiated from earned structures
#check book_ii_bridge_complete


-- ================================================================
-- VERIFICATION SUMMARY
-- ================================================================

/-
All 7 hinges of Book I are machine-checked:

  H1: Generator, K1–K5, gen_distinct          ✓ (Kernel)
  H2: ValidABCD, no_tie, hyperfact_check      ✓ (Coordinates)
  H3: chi_plus, chi_minus, chi_complete        ✓ (Polarity/Boundary)
  H4: SplitComplex, is_sector_independent      ✓ (Holomorphy)
  H5: HartogsData                              ✓ (Holomorphy)
  H6: Truth4, explosion_barrier, EarnedTopos   ✓ (Logic/Topos)
  H7: KernelHinge, book_ii_bridge_complete     ✓ (Bridge)

Zero sorry. Every hinge compiles. The code is the proof.
-/
