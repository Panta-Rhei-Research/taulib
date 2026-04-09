# Contributing to TauLib

TauLib is the official formalization of Category &tau;, maintained by the authors of the [Panta Rhei](https://panta-rhei.site) book series. This document covers issue reporting, code style conventions, and citation guidelines.

---

## Reporting Issues

If you find an error, have a question, or want to suggest an improvement:

1. Open an issue at the [GitHub Issues](https://github.com/panta-rhei-framework/taulib/issues) page
2. Include the **module path** (e.g., `TauLib.BookIV.Electroweak.EWSynthesis`)
3. Quote the specific **theorem or definition name** (e.g., `nine_ew_quantities`)
4. Describe what you expected vs. what you found
5. Include your Lean version (`lean --version`) and platform

### Good issue examples

- "Theorem `X` in module `Y` has a weaker conclusion than the corresponding Book IV result [IV.T140]"
- "`#eval` at line 42 of `Z.lean` produces value V, but the book claims W"
- "The dependency from `BookIII.Bridge` to `BookII.CentralTheorem` seems unnecessary"

---

## Pull Requests

This repository is the **official release** of TauLib. We do not accept external pull requests on this repo.

If you want to:
- **Experiment** &mdash; fork the repo and work freely under the Apache 2.0 license
- **Contribute** &mdash; open a pull request or issue on the [TauLib repository](https://github.com/panta-rhei-framework/taulib)
- **Report fixes** &mdash; open an issue; we will credit you in the changelog

---

## Code Style

These conventions apply to all TauLib code and are recommended for forks.

### Namespaces

```
Tau.{Family}.{Module}
```

Examples: `Tau.Kernel.Axioms`, `Tau.Boundary.SplitComplex`, `Tau.Electroweak.EWSynthesis`

### Naming Conventions

| Element | Convention | Example |
|---------|-----------|---------|
| Theorems | `lowercase_with_underscores` | `rigidity_non_omega` |
| Definitions | `lowercase_with_underscores` | `iota_tau_float` |
| Structures | `PascalCase` | `TauObj`, `SplitComplex` |
| Inductive types | `PascalCase` | `Generator`, `OrbitRay` |
| Instances | Named explicitly | `instAddSplitComplex` |
| Type aliases | `PascalCase` | `TauIdx` |

### Module Docstrings

Every `.lean` file **must** start with a `/-! -/` block containing:

```lean
/-!
# TauLib.BookN.Family.Module

Brief description of this module's mathematical content.

## Registry Cross-References

- [N.DX] DefinitionName -- `lean_identifier`
- [N.TX] TheoremName -- `lean_identifier`

## Mathematical Content

Detailed explanation of the module's purpose, key definitions,
and how it fits into the overall structure.

## Ground Truth Sources

- Chapter X of Book N (section X.Y)
-/
```

**Requirements:**
- Title matches the Lean namespace
- Registry cross-references use `[Book.TypeIndex]` format
- Mathematical content explains the "why," not just the "what"
- Ground truth sources link to the LaTeX book chapters

### Declaration Docstrings

Every `def`, `theorem`, `lemma`, `structure`, `class`, and `inductive` should have a `/-- -/` docstring:

```lean
/-- The master constant ι_τ = 2/(π + e) ≈ 0.341304.
    Governs all quantitative predictions in Category τ.
    Registry: [I.D45] -/
def iota_tau_float : Float := 2.0 / (Float.pi + Float.exp 1.0)
```

### Registry ID Format

Cross-references to the Panta Rhei books use `[Book.TypeIndex]`:

| Prefix | Meaning | Example |
|--------|---------|---------|
| `I.` &ndash; `VII.` | Book number | `IV.T140` = Book IV, Theorem 140 |
| `K` | Axiom | `I.K1` = Axiom K1 |
| `D` | Definition | `V.D317` |
| `T` | Theorem | `IV.T66` |
| `P` | Proposition | `V.P176` |
| `R` | Remark | `IV.R260` |
| `OP` | Open Problem | `V.OP12` |

### Scope Labels

Every module and registry entry has a scope tier:

| Tier | Meaning |
|------|---------|
| **established** | Classical mathematics, independently verified |
| **&tau;-effective** | Quantitative prediction derived within the &tau; framework |
| **conjectural** | Structural claim, computationally verified but not derived from axioms |
| **metaphorical** | Philosophical/analogical extension |

See [docs/SCOPE_LABELS.md](docs/SCOPE_LABELS.md) for full details.

### Dependency Policy

| Rule | Rationale |
|------|-----------|
| Mathlib for tactics **only** | TauLib builds all math from scratch |
| No `import Mathlib.Order.*`, `Mathlib.Algebra.*`, etc. | These would import external mathematical content |
| `import Mathlib.Tactic` is the correct import | Brings in `simp`, `omega`, `ring`, `decide`, etc. |

### Sorry Policy

- **Books I&ndash;VI:** Zero sorry, zero exceptions
- **Book VII:** Sorry permitted only for methodological boundary markers, typed `True := sorry`
- Every sorry must have a docstring explaining why it exists

---

## Building

```bash
# Full build
lake build

# Specific book
lake build TauLib.BookI

# Check Lean toolchain
cat lean-toolchain
```

Requires Lean 4 (see `lean-toolchain` for the pinned version). The first build fetches Mathlib and takes several minutes; subsequent builds are cached.

---

## Citing TauLib

If you use TauLib in academic work, please cite:

```bibtex
@software{taulib2026,
  author    = {Fuchs, Thorsten and Fuchs, Anna-Sophie},
  title     = {{TauLib}: Mechanized Formalization of Category $\tau$},
  year      = {2026},
  version   = {2.0.0},
  url       = {https://github.com/panta-rhei-framework/taulib},
  note      = {450 modules, 125{,}771 lines of Lean 4, 4{,}332 theorems},
  license   = {Apache-2.0}
}
```

Or use the [CITATION.cff](CITATION.cff) file (GitHub's "Cite this repository" feature).

---

## License

Apache 2.0. See [LICENSE](LICENSE).
