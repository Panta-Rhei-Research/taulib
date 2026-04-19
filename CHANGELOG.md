# Changelog

All notable changes to TauLib are documented in this file.

## [2.0.0] - 2026-04-19

### Peer-review-driven corrections

Pre-publication simulated peer review (four frontier-expert reviewers plus a synthesis chair) identified three process failures in v1.0.0. `peer-review-fixes-v1` (PR #1, merged at commit `a2d3384`) and the follow-on `ci-python-sorry-checker` (PR #2, merged at commit `b743f4c`) address them.

#### Axioms: 4 → 3

The fourth axiom `central_theorem_physical : True` in `BookIV/Arena/BoundaryHolonomy.lean` was retired. An `axiom` of type `True` is a no-op (`True` is inhabited by `trivial`), so the declaration added nothing to the theory while inflating the axiom count. The three remaining axioms are all conjectural, all in Book III, all following the compute-then-axiomatize pattern:

- `bridge_functor_exists` (`BookIII/Bridge/BridgeAxiom.lean`)
- `spectral_correspondence_O3` (`BookIII/Doors/SpectralCorrespondence.lean`)
- `grand_grh_adelic` (`BookIII/Doors/GrandGRH.lean`)

#### Sorry: 3 → 0 (all seven books sorry-free)

The three previously shipping Book VII `theorem X : True := sorry` declarations (`omega_point_theorem`, `science_faith_boundary`, `no_forced_stance`) were retired and replaced with `def` values of a new `Commitment` structure in `TauLib/BookVII/Meta/Commitment.lean`. Each commitment carries its `statement`, `warrant`, and `registry_id` as inspectable `String` data — readable via `#eval` — rather than as an unprovable `sorry` on a trivially-provable `True` goal.

The original declaration names are preserved; `#check omega_point_theorem` now reports type `Commitment` rather than `True`. The 21 downstream `#check` references in the `Tour/` files resolve unchanged.

#### CI enforcement

Two policies were previously documented but not enforced by CI:

- **Tactics-only Mathlib policy.** A new CI step greps for forbidden imports (`Mathlib.{Order, Algebra, CategoryTheory, Topology, Analysis, Data.Nat, Logic}`) and fails the build on any hit.
- **Axiom and sorry count invariants.** A new Python-based checker (`scripts/check_no_sorry.py`) strips Lean comments and string literals before counting `axiom` and `sorry` occurrences, then asserts exact counts (3 axioms, 0 sorry) on every push to `main`. The earlier grep+awk implementation has a known false-positive on multi-line block comments; the Python checker is exact against TauLib's source.

#### Documentation reconciliation

`README.md`, `RELEASE_NOTES.md`, `CITATION.cff`, `docs/FORMALIZATION_STATUS.md`, `docs/SCOPE_LABELS.md`, `TauLib.lean`, the Tour files, and the website (`site/index.md`) were all updated to the new counts. Earlier commits citing the v1.0.0 state (4 axioms / 3 sorry) are preserved in the git history and branch-name trail (`peer-review-fixes-v1`, `ci-python-sorry-checker`) as a full audit trail.

#### Paper

The companion paper (`papers/taulib/main.tex` in the Panta Rhei monograph repo) was revised in parallel. v3.3 (2026-04-19) ships with 31 pages, 0 undefined refs, and aligns with the pinned repo commit.

### Fixed

- `README.md` line 61: `cd TauLib` → `cd taulib` (clone creates lowercase directory).
- `README.md` line 310: BibTeX `$\tau$` was corrupted by a literal tab character; restored.
- `RELEASE_NOTES.md` top-line version bumped to v2.0.0.
- `CITATION.cff` abstract: "Books I–VI contain zero sorry" → "all seven books are sorry-free".

## [1.0.0] - 2026-04-12

### Initial Public Release

First public release accompanying the Panta Rhei book series (2nd Edition).

#### Codebase

- 450 Lean 4 modules across 7 book namespaces
- 125,771 lines of Lean 4 code
- 4,332 theorems and lemmas
- 3,542 definitions
- 3,721 `#eval` computations
- 4 axioms (3 conjectural in Book III, 1 structural in Book IV)
- 3 sorry (all methodological, Book VII only)
- 0 sorry in Books I-VI
- Mathlib imported for proof tactics only; zero mathematical content imports

#### Guided Tours

8 interactive tours for different audiences:

| Tour | Audience |
|------|----------|
| `Tour/VerifyItYourself.lean` | Skeptics and reviewers |
| `Tour/Foundations.lean` | Mathematicians and Lean users |
| `Tour/CentralTheorem.lean` | Mathematicians |
| `Tour/Physics.lean` | Physicists |
| `Tour/OneConstant.lean` | Physicists and cosmologists |
| `Tour/MillenniumProblems.lean` | Number theorists |
| `Tour/LifeFromPhysics.lean` | Biologists |
| `Tour/MindAndEthics.lean` | Philosophers |

#### Documentation

- README with audience-segmented reading paths
- Architecture guide with dependency graphs
- Formalization status with axiom and sorry inventory
- Glossary of key terms and constants
- Scope labels guide (established / tau-effective / conjectural / metaphorical)
- doc-gen4 documentation generation pipeline
- CI/CD workflows for build and documentation deployment

#### Quality Assurance

- 3 comprehensive audits completed (cross-reference, content, codebase)
- 100% module docstring coverage
- Consistent registry cross-reference format (em-dash separator)
- All namespace headers verified correct
- Zero TODO/FIXME/HACK comments in codebase

#### Build

- Lean 4 v4.28.0-rc1
- Mathlib4 (tactics only)
- Apache 2.0 license
