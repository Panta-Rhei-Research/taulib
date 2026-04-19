import TauLib.BookI.Orbit.Rigidity
import TauLib.BookII.CentralTheorem.CentralTheorem
import TauLib.BookIII.Bridge.BridgeAxiom
import TauLib.BookIII.Doors.GrandGRH
import TauLib.BookIII.Doors.SpectralCorrespondence
import TauLib.BookIV.Electroweak.WeinbergNLO
import TauLib.BookV.Cosmology.CMBSpectrum
import TauLib.BookVII.Ethics.CIProof

/-!
# TauLib.Meta.PrintAxioms

Per-theorem `#print axioms` driver for CI-generated TCB classification.

## Purpose

Round 2 of the Breitner peer review (peer-review-fixes-v2, 2026-04-19) noted
that the site's `/verify/tcb.md` partition of theorems by TCB extension
(kernel-only vs. `native_decide`-extended vs. project-axiom-dependent) was
author-attested rather than machine-attested. This module closes that gap:
each `#print axioms` call below emits, at Lean elaboration time, the
complete transitive axiom closure for a headline theorem. A CI step then
parses those elaboration messages into a structured artifact
(`.github/workflows/output/print_axioms.json`) and a human-readable
Markdown report (`docs/print_axioms_report.md`).

## Contract with the harvester

- Each `#print axioms` line below is preceded by a marker comment of the
  form `-- HARVEST: <name> | <module relative path>` so the harvester can
  associate each axiom-listing message with its originating theorem
  without having to re-parse Lean's full message stream.
- The harvester expects Lean to emit `#print axioms` output as
  informational messages on stdout during `lake build` (or `lake env
  lean`) of this file. The output format is the standard
  `'<name>' depends on axioms: [...]` form that Lean 4 has emitted since
  core version `v4.0.0`.

## Scope: the eight headline theorems

These are the theorems Round 2 named by hand as the ones whose TCB cost
a reviewer most likely wants to audit. The list is intentionally small
and curated; expanding to every theorem in TauLib is possible but not
necessary for the narrow claim the site makes.

All three project axioms are also emitted so that their self-witnessing
(axiom `X` trivially depends on axiom `X`) is visible in the artifact
alongside the derived theorems that pull them in transitively.

## Namespace note

Book I's rigidity/categoricity theorems live under `Tau.Orbit` rather
than `Tau.BookI.Orbit` for historical reasons (the namespace predates
the book-level reorganization). The harvester records the fully
qualified name Lean reports, not the path-derived one.
-/

namespace Tau.Meta.PrintAxioms

open Tau.Orbit
open Tau.BookII.CentralTheorem
open Tau.BookIII.Bridge
open Tau.BookIII.Doors
open Tau.BookIV.Electroweak
open Tau.BookV.Cosmology
open Tau.BookVII.Ethics.CIProof

-- ============================================================
-- Book I — kernel-only (structural) theorems
-- ============================================================

-- HARVEST: Tau.Orbit.rigidity_non_omega | BookI/Orbit/Rigidity.lean
#print axioms Tau.Orbit.rigidity_non_omega

-- HARVEST: Tau.Orbit.categoricity_non_omega | BookI/Orbit/Rigidity.lean
#print axioms Tau.Orbit.categoricity_non_omega

-- ============================================================
-- Book II — Central Theorem (uses native_decide)
-- ============================================================

-- HARVEST: Tau.BookII.CentralTheorem.central_theorem_3_15 | BookII/CentralTheorem/CentralTheorem.lean
#print axioms Tau.BookII.CentralTheorem.central_theorem_3_15

-- ============================================================
-- Book III — Bridge (project-axiom-dependent + native_decide)
-- ============================================================

-- HARVEST: Tau.BookIII.Bridge.bridge_ledger_consistent | BookIII/Bridge/BridgeAxiom.lean
#print axioms Tau.BookIII.Bridge.bridge_ledger_consistent

-- ============================================================
-- Book IV — Electroweak window-integer identities (native_decide)
-- ============================================================

-- HARVEST: Tau.BookIV.Electroweak.consecutive_window_integers | BookIV/Electroweak/WeinbergNLO.lean
#print axioms Tau.BookIV.Electroweak.consecutive_window_integers

-- ============================================================
-- Book V — CMB first-peak holonomy (structural, kernel-only)
--
-- NOTE: The Round 2 brief lists `first_peak_holonomy` and
-- `structural_hubble` under the (aspirational) `BookIV.Arena` /
-- `BookV.Cosmology` names. In the current repository both live in
-- `TauLib/BookV/Cosmology/CMBSpectrum.lean`; `first_peak_holonomy` is
-- a `Float` definition (whose axiom-closure is emittable but trivial)
-- and `first_peak_holonomy_thm` is the associated content theorem.
-- The harvester records both.
-- ============================================================

-- HARVEST: Tau.BookV.Cosmology.first_peak_holonomy_thm | BookV/Cosmology/CMBSpectrum.lean
#print axioms Tau.BookV.Cosmology.first_peak_holonomy_thm

-- HARVEST: Tau.BookV.Cosmology.structural_hubble | BookV/Cosmology/CMBSpectrum.lean
#print axioms Tau.BookV.Cosmology.structural_hubble

-- ============================================================
-- Book VII — Ethics j-closed fixed point
-- ============================================================

-- HARVEST: Tau.BookVII.Ethics.CIProof.ci_j_closed_fixed_point | BookVII/Ethics/CIProof.lean
#print axioms Tau.BookVII.Ethics.CIProof.ci_j_closed_fixed_point

-- ============================================================
-- The three project axioms — self-witnessing
--
-- Each of these is declared by the `axiom` keyword in Book III.
-- Running `#print axioms` on the axiom itself yields a listing whose
-- transitive closure is `{X}` — the axiom witnesses only itself. This
-- is informationally useful because it documents the axiom's fully
-- qualified name, fixes its module of origin, and lets the harvester
-- produce a three-row "project axioms" section in the report without
-- needing a separate code path.
-- ============================================================

-- HARVEST: Tau.BookIII.Bridge.bridge_functor_exists | BookIII/Bridge/BridgeAxiom.lean
#print axioms Tau.BookIII.Bridge.bridge_functor_exists

-- HARVEST: Tau.BookIII.Doors.spectral_correspondence_O3 | BookIII/Doors/SpectralCorrespondence.lean
#print axioms Tau.BookIII.Doors.spectral_correspondence_O3

-- HARVEST: Tau.BookIII.Doors.grand_grh_adelic | BookIII/Doors/GrandGRH.lean
#print axioms Tau.BookIII.Doors.grand_grh_adelic

end Tau.Meta.PrintAxioms
