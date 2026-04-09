import TauLib.BookIII.Enrichment.CanonicalLadder
import TauLib.BookIII.Sectors.Decomposition
import TauLib.BookIII.Sectors.ParityBridge
import TauLib.BookIII.Hinge.HingeTheorem
import TauLib.BookIII.Hinge.DependencyChain
import TauLib.BookIII.Doors.MasterSchema
import TauLib.BookIII.Doors.GrandGRH
import TauLib.BookIII.Doors.SpectralCorrespondence
import TauLib.BookIII.Bridge.BridgeAxiom

open Tau.BookIII.Enrichment Tau.BookIII.Sectors Tau.BookIII.Hinge
open Tau.BookIII.Doors Tau.BookIII.Bridge

/-!
# Guided Tour Companion: Book III — Where Physics Lives

**Companion to**: `launch/guided-tours/guided-tour-book-III.pdf`

This Lean module walks through the 6 structural hinges of Book III —
the constitutional volume that legislates the architecture of Books IV–VII.
-/

-- ================================================================
-- HINGE 1: The Canonical Ladder Theorem [III.T04]
-- ================================================================

/-
Exactly four enrichment layers: E₀ ⊊ E₁ ⊊ E₂ ⊊ E₃.
Non-emptiness, strictness, saturation, uniqueness.
-/

#check non_emptiness_check
#check strictness_check
#check saturation_e3_check
#check canonical_ladder_check


-- ================================================================
-- HINGE 2: The 4+1 Sector Template [III.D13]
-- ================================================================

/-
Boundary characters partition into 4 primitive sectors + 1 coupling.
At E₁: four forces + Higgs. At E₂: five life sectors.
-/

#check Sector
#check sector_of
#check sector_decomposition_check
#check sector_preservation_check


-- ================================================================
-- HINGE 3: The Hinge Theorem [III.T41]
-- ================================================================

/-
Books IV–VII = sector instantiations of the enrichment ladder.
The 7-book architecture is derived, not chosen.
-/

#check hinge_theorem_check
#check dependency_chain_check


-- ================================================================
-- HINGE 4: The Master Schema [III.T23]
-- ================================================================

/-
All 8 Millennium Problems are instances of Mutual Determination
at different enrichment levels.
-/

#check MasterSchemaEntry
#check master_schema_check


-- ================================================================
-- HINGE 5: The Bridge Axiom [III.D71]
-- ================================================================

/-
The ONE conjectural postulate in the entire framework.
Finite checks pass; the axiom asserts the infinite extension.
This is the compute-then-axiomatize pattern.
-/

-- The axiom itself
#check bridge_functor_exists

-- The finite check that precedes it
#check bridge_functor_check
#check bridge_functor_8_3

-- The scope ledger: what is proved vs conjectured
#check bridge_ledger_check
#check bridge_ledger_consistent

-- Honest claims: every τ-effective claim passes its check
#check honest_claim_8_3


-- ================================================================
-- HINGE 6: The 4-Tier Scope Discipline
-- ================================================================

/-
Every claim carries a scope label: established, τ-effective,
conjectural, or metaphorical. Conflation is a type error.
-/

#check ScopeLabel
-- Inductive: established, tau_effective, conjectural, metaphorical

#check conjectural_properly_marked


-- ================================================================
-- VERIFICATION SUMMARY
-- ================================================================

/-
All 6 hinges of Book III are machine-checked:

  H1: canonical_ladder_check (non-empty + strict + saturated) ✓
  H2: sector_decomposition_check, sector_preservation_check    ✓
  H3: hinge_theorem_check, dependency_chain_check              ✓
  H4: master_schema_check, MasterSchemaEntry                   ✓
  H5: bridge_functor_exists (1 axiom), bridge_ledger_consistent ✓
  H6: ScopeLabel, conjectural_properly_marked                  ✓

One axiom (bridge_functor_exists). Zero sorry. The hinge compiles.
-/
