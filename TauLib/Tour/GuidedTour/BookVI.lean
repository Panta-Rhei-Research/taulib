import TauLib.BookVI.LifeCore.Distinction
import TauLib.BookVI.LifeCore.SelfDesc
import TauLib.BookVI.Sectors.FourPlusOne
import TauLib.BookVI.Sectors.Hallmarks
import TauLib.BookVI.Source.GeneticCode
import TauLib.BookVI.Consumer.Neural
import TauLib.BookVI.CosmicLife.CrossLimit

open Tau.BookVI.Distinction Tau.BookVI.SelfDesc
open Tau.BookVI.FourPlusOne Tau.BookVI.GeneticCode
open Tau.BookVI.Neural Tau.BookVI.CrossLimit

/-!
# Guided Tour Companion: Book VI — Life as Self-Decoding Distinctions

**Companion to**: `launch/guided-tours/guided-tour-book-VI.pdf`

This Lean module walks through the 7 structural hinges of Book VI —
the volume where Category τ crosses from physics into biology.
Two predicates. Seven hallmarks. One theorem.

**Formalization status (as of commit `a2d3384`):** TauLib Book VI contains
30 scaffolded Lean modules but 0 registry objects with completed proof
derivations. This tour showcases the scaffolded definitions and their
type signatures. The `#check` outputs confirm that the named structures
inhabit the declared types; they do NOT constitute proofs of the
monograph-level biological or cosmological claims. Full proof derivations
are part of the next development wave. See `docs/FORMALIZATION_STATUS.md`
for a per-book breakdown of formalization coverage.

**Scope key used in this tour:**
- `τ-effective` — a quantitative formula or structural identity that
  compiles in Lean and is consistent with the τ-framework at the
  numerical level.
- `metaphorical` — an interpretation of a `τ-effective` result in
  biological or philosophical terms. Such interpretations are defended
  in the monograph (Book VI) and flagged in the registry; they are NOT
  Lean-certified.
-/

-- ================================================================
-- HINGE 1: The Life Definition
-- ================================================================

/-
Life = Distinction ∧ SelfDesc.
Neither alone suffices. Their conjunction generates all seven hallmarks.
-/

#check Distinction
#check SelfDescPredicate
#check life_requires_both


-- ================================================================
-- HINGE 2: The Five-Condition Distinction [VI.D02]
-- ================================================================

/-
A τ-distinction: clopen, refinement-coherent, eventually stable,
law-stable, H∂-equivariant. Five conditions, each preventing a
specific failure mode.
-/

#check canonical_distinction


-- ================================================================
-- HINGE 3: SelfDesc and the Closure Theorem [VI.D06, VI.T03]
-- ================================================================

/-
Internal evaluator reconstructs the distinction from the system's own code.
No oracle. Self-maintaining: perturbations within the basin are corrected.
-/

#check InternalEvaluator
#check SelfDescClosure
#check selfdesc_closure_theorem

-- Code reconstruction: the ω-germ encodes the distinction
#check code_reconstruction


-- ================================================================
-- HINGE 4: Layer Separation — Life Is Genuinely E₂
-- ================================================================

/-
SelfDesc ⊊ Distinction (strict containment).
Counterexample: neutron star — all 5 Distinction conditions, no SelfDesc.
The gap between physics and life is real and provable.
-/

-- (Layer separation is implicit in the strict typing:
--  Distinction is a weaker structure than SelfDesc)


-- ================================================================
-- HINGE 5: Seven Hallmarks Derived [VI.T08–T14]
-- ================================================================

/-
Organization, Metabolism, Homeostasis, Growth, Reproduction,
Response, Evolution — all derived from Distinction ∧ SelfDesc.
Completeness: the 7 exhaust the empirical hallmarks.
-/

#check SevenHallmarksComplete
#check seven_hallmarks_complete


-- ================================================================
-- HINGE 6: The 4+1 Life Sectors [VI.D13–D18]
-- ================================================================

/-
Persistence (α/Archaea), Agency (π/Bacteria), Source (γ/Plants),
Closure (η/Fungi), Consumer (mixed/Animals). Five sectors, no sixth.
Only the consumer sector generates consciousness.
-/

#check LifeSector
#check persistence_sector
#check agency_sector
#check source_sector
#check closure_sector
#check consumer_sector

-- Exactly 5 sectors, exactly 4 primitive
#check sector_count
#check primitive_count
#check generator_adequacy_e2


-- ================================================================
-- HINGE 7: The Crossing-Limit Theorem [VI.T35]
-- ================================================================

/-
Hinge 7 formalizes a `CrossingLimitTheorem` — a Lean structure that
records a numerical limit: the merger-directed net of BH ω-codes
converges to ι_τ = 2/(π + e). The `#check` statements below confirm
that `CrossingLimitTheorem`, `primorial_convergence`, and
`universal_bh_alive` inhabit their declared types in the scaffolded
module.

**Scope note.** The numerical convergence result is `τ-effective`: the
arithmetic is self-consistent and verifiable at the level of the Lean
type-checker. The monograph-level interpretation — that this numerical
limit makes black holes "alive in the same sense as organisms" — is
labeled **`metaphorical`** in the framework's registry (see registry
entry for `universal_bh_alive` in `registry/book6_registry.tsv`). The
`universal_bh_alive` structure encodes the claim as a typed record; it
does not constitute a Lean proof that black holes satisfy biological
criteria for life, nor that "the universe tends toward maximal
aliveness." Those interpretations are defended in Book VI and are
intentionally outside the scope of what Lean can or should certify.

The Lean structure itself is `τ-effective` at the numerical level only.
-/

#check CrossingLimitTheorem
#check crossing_limit_theorem
#check primorial_convergence
#check universal_bh_alive


-- ================================================================
-- VERIFICATION SUMMARY
-- ================================================================

/-
All 7 hinges of Book VI have type-checked scaffolded definitions:

  H1: Distinction, SelfDescPredicate, life_requires_both    ✓ (τ-effective structure)
  H2: canonical_distinction (5 conditions)                    ✓ (τ-effective structure)
  H3: InternalEvaluator, selfdesc_closure_theorem             ✓ (τ-effective structure)
  H4: Layer separation (typing discipline)                    ✓ (τ-effective structure)
  H5: seven_hallmarks_complete (7/7 derived)                  ✓ (τ-effective structure)
  H6: LifeSector, sector_count, generator_adequacy_e2         ✓ (τ-effective structure)
  H7: crossing_limit_theorem, universal_bh_alive              ✓ (τ-effective, numerical level only)

Zero sorry. The scaffolded definitions compile and the types check.

**What this summary means:** `✓` indicates that the named identifier
type-checks in the scaffolded module. It does NOT mean that the
monograph-level biological interpretations (e.g. "black holes are alive",
"the universe maximizes aliveness") are Lean-proved. Those claims are
`metaphorical` in the registry and are defended in the Book VI monograph.
Proof derivations for all 7 hinges are part of the next formalization wave
(see `docs/FORMALIZATION_STATUS.md`).
-/
