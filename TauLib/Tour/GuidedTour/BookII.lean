import TauLib.BookI.Boundary.SplitComplex
import TauLib.BookI.Boundary.Characters
import TauLib.BookI.Boundary.Fourier
import TauLib.BookI.Boundary.Spectral
import TauLib.BookII.Hartogs.MutualDetermination
import TauLib.BookII.CentralTheorem.CentralTheorem
import TauLib.BookII.CentralTheorem.Categoricity
import TauLib.BookII.Enrichment.SelfEnrichment
import TauLib.BookII.Enrichment.YonedaTheorem

open Tau.Boundary Tau.Polarity Tau.BookII.Hartogs
open Tau.BookII.CentralTheorem Tau.BookII.Enrichment

/-!
# Guided Tour Companion: Book II — Finite Readouts of Infinity

**Companion to**: `launch/guided-tours/guided-tour-book-II.pdf`

This Lean module walks through the 7 structural hinges of Book II.
The Central Theorem — O(τ³) ≅ A_spec(L) — is the structural heart
of the entire series. Every hinge below feeds into it.
-/

-- ================================================================
-- HINGE 1: Boundary-First Paradigm [II.R01]
-- ================================================================

/-
The boundary is primary; the interior is constructed from it.
This is implicit in Book I's exports — the lemniscate characters
earned there power everything in Book II.
-/

-- Book I's boundary characters are the starting data
#check chi_plus
#check chi_minus
#check chi_complete
-- These ARE the finite readouts. Everything below extends them.


-- ================================================================
-- HINGE 2: The Split-Complex Shift [II.D32, II.T24]
-- ================================================================

/-
j² = +1 (hyperbolic), not i² = -1 (elliptic).
This avoids Liouville and enables non-constant bounded holomorphic functions.
-/

#check SplitComplex

-- The bipolar idempotents: e₊ = (1+j)/2, e₋ = (1-j)/2
#check chi_plus_of_e_plus
#check chi_minus_of_e_minus

-- Idempotent orthogonality: e₊ · e₋ = 0
#check chi_orthogonal


-- ================================================================
-- HINGE 3: Omega-Germ Construction [II.D04, II.T02]
-- ================================================================

/-
Finite residue towers read out infinity. The crossing point
on the lemniscate is where both sectors meet.
-/

#check crossing_point
#check crossing_iff_chi_equal

-- Fourier transform: bipolar decomposition of boundary data
#check fourier
#check fourier_invertible


-- ================================================================
-- HINGE 4: Mutual Determination [II.T27]
-- ================================================================

/-
Five descriptions of holomorphic structure are the same object:
Refinement ↔ Spectral ↔ ω-Germ ↔ Character ↔ Hartogs.
-/

#check mutual_determination_check


-- ================================================================
-- HINGE 5: The Central Theorem [II.T40]
-- ================================================================

/-
O(τ³) ≅ A_spec(L) — the ring of holomorphic functions on τ³
equals the spectral algebra of the lemniscate boundary.
Four chained isomorphisms build the identification.
-/

#check central_theorem_check
#check central_theorem_forward_check
#check central_theorem_inverse_check


-- ================================================================
-- HINGE 6: Liouville Dodge and Categoricity [II.T41, II.T42]
-- ================================================================

/-
Liouville's theorem does not apply: j² = +1 gives a wave-type
operator, not an elliptic Laplacian. Non-constant bounded
holomorphic functions exist. τ³ is unique (moduli = point).
-/

#check categoricity_check
#check liouville_dodge_check
#check moduli_singleton_check


-- ================================================================
-- HINGE 7: Self-Enrichment Bridge [II.D53, II.D54]
-- ================================================================

/-
τ enriches over itself: Hom objects are themselves τ-objects.
This is the E₀ → E₁ transition that enables Book III.
-/

#check self_enrichment_check

-- Yoneda embedding: fully faithful and bipolar-preserving
#check probe_yoneda_check
#check yoneda_faithful_check
#check yoneda_full_check
#check yoneda_bipolar_check
#check full_yoneda_check


-- ================================================================
-- VERIFICATION SUMMARY
-- ================================================================

/-
All 7 hinges of Book II are machine-checked:

  H1: chi_plus, chi_minus, chi_complete        ✓ (Boundary exports)
  H2: SplitComplex, chi_orthogonal             ✓ (Split-complex)
  H3: crossing_point, fourier_invertible        ✓ (Omega-germ)
  H4: mutual_determination_check               ✓ (5-way equivalence)
  H5: central_theorem_check (forward + inverse) ✓ (Central Theorem)
  H6: categoricity_check, moduli_singleton      ✓ (Liouville/Categoricity)
  H7: self_enrichment_check, full_yoneda_check  ✓ (Self-enrichment)

Zero sorry. The Central Theorem compiles. Boundary determines interior.
-/
