import TauLib.BookIII.Doors.SpectralCorrespondenceFinite

/-!
# TauLib.BookIII.Doors.SpectralCorrespondence

Spectral Correspondence Theorem (legacy O3 axiom wrapper).

Finite spectral-parameter and correspondence definitions live in the
axiom-free module `TauLib.BookIII.Doors.SpectralCorrespondenceFinite`.  This
module contains only the legacy universal O3 postulate and compatibility
selector, so axiom-free proof slices can avoid importing it.
-/

namespace Tau.BookIII.Doors

-- ============================================================
-- SPECTRAL CORRESPONDENCE [III.T18] — O3 AXIOM
-- ============================================================

/-- [III.T18] **CONJECTURE-AXIOM — CONDITIONAL RESULTS DOWNSTREAM**

    The O(3) spectral correspondence holds at all levels. This is one
    of exactly three conjecture-axioms in TauLib; see also
    `bridge_functor_exists` (`BookIII.Bridge.BridgeAxiom`) and
    `grand_grh_adelic` (`BookIII.Doors.GrandGRH`).

    The finite predicate `spectral_correspondence_finite` is defined in
    `SpectralCorrespondenceFinite`.  This axiom asserts its universal
    extension and should not be imported by axiom-free proof slices. -/
axiom spectral_correspondence_O3 :
  ∀ k : Nat, spectral_correspondence_finite k = true

/-- [III.T18] Structural: O3 implies finite correspondence at any level. -/
theorem spectral_corr_from_O3 (k : Nat) :
    spectral_correspondence_finite k = true :=
  spectral_correspondence_O3 k

end Tau.BookIII.Doors
