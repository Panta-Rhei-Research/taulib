# Changelog

All notable changes to TauLib are documented in this file.

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
