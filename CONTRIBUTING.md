# Contributing to TauLib

TauLib is the Lean 4 formalization of the [Panta Rhei Research Program](https://panta-rhei.site) — Category τ built from 7 axioms, 5 generators, and 1 operator, applied across mathematics, physics, biology, and metaphysics. As of April 2026, the project is solo-authored by Thorsten Fuchs, and this is the first time we are opening the door to community engagement.

**External contributions are welcome.** If you have spotted a typo, a missed `simp` simplification, a broken link, or an outright error in a registry entry, please open a PR or issue. Larger changes start with a conversation — see below.

---

## Types of Contributions

### Small PRs — merged liberally

Open a PR directly. No issue required. Expect a review turnaround measured in days, not weeks.

- Typo fixes in docstrings, comments, and Markdown.
- Docstring corrections and clarifications.
- Tactic simplifications using `simp`, `omega`, `decide`, `ring`, `norm_num`, etc. — provided the kernel axiom count and `sorry` count do not change.
- Registry bookkeeping: wrong registry ID cross-reference, missing `[Book.TypeIndex]` tag, mismatched scope label.
- Broken links in docs and README.
- CI hygiene: workflow fixes, `lake-manifest.json` updates, `lean-toolchain` bumps that keep the build green.

### Medium PRs — open an issue first

Describe what you want to do in a short issue, get a nod, then open the PR. This keeps us from colliding on the same work.

- New lemmas that support existing theorems.
- Alternative proofs of existing theorems. Must not add axioms. Must keep the theorem statement intact.
- doc-gen4 improvements: better navigation, cross-linking, tagging.
- New `#eval` checks, especially where they tighten a compute-then-axiomatize pattern.

### Large changes — open a discussion

These are architectural. Use a GitHub issue labelled `discussion`, or raise it on Zulip once the thread is announced (see below).

- Adding new axioms (the current count is 3, and any increase needs a registry entry and explicit sign-off).
- Changing scope labels (`established`, `τ-effective`, `conjectural`, `metaphorical`).
- Refactors inside `BookI/Kernel` — the K0–K6 axioms are load-bearing.
- Proposals to merge `Mathlib` *content* modules (the project is tactics-only-Mathlib; see below).

---

## Out of Scope for PRs

Maintainers will not accept these changes. They will fail CI, or get closed with a pointer here.

- **Adding `sorry`.** CI enforces `sorry = 0` across Books I–VI and the current methodological count in Book VII. If you genuinely need a hole, declare a clearly-labelled `axiom` with (a) a docstring explaining why it is conjectural, (b) a compute-then-axiomatize finite check via `#eval` or `decide`, and (c) a registry entry marking it `conjectural`.
- **Importing Mathlib content modules.** Anything under `Mathlib.Algebra.*`, `Mathlib.CategoryTheory.*`, `Mathlib.Order.*`, `Mathlib.Topology.*`, etc. is out. TauLib builds its mathematics from scratch on the K0–K6 kernel. Only `import Mathlib.Tactic` (and its sub-imports for specific tactics) is permitted. A CI grep-guard enforces this.
- **Changing the K0–K6 kernel axioms** without prior discussion.
- **Increasing the axiom count from 3** without a registry entry and a discussion thread.

---

## PR Conventions

- **Branch from `main`.** Small PRs can be opened directly; medium and large changes should reference their issue.
- **Commit messages:** imperative mood, short title (< 72 chars), body explaining the *why*. No emojis.
- **DCO sign-off required.** End each commit with `Signed-off-by: Your Name <email>`. `git commit -s` does this automatically. There is no separate CLA.
- **CI must be green:**
  - `lake build` passes with zero errors and zero warnings you introduced.
  - `scripts/check_no_sorry.py` reports `axioms=3, sorry=0`.
  - The tactics-only Mathlib grep-guard passes.
- **Registry updates:** if your PR touches a registry-tracked object (any declaration tagged `[Book.TypeIndex]`), update the matching row in `registry/bookN_registry.tsv` in the same PR.

Small, focused PRs are easier to review and get merged faster. If a change grows beyond a few files, consider splitting it.

---

## Issues

Use the [issue tracker](https://github.com/panta-rhei-research/taulib/issues) for:

- Typos too large for a drive-by PR, or scattered across many files.
- Factual errors in registry entries.
- Proof-style feedback.
- Questions about Panta Rhei's conventions (naming, scope tiers, kernel structure).
- Feature requests.

**Issue template:**

- Module path (e.g. `TauLib.BookIV.Electroweak.EWSynthesis`).
- Theorem or definition name (e.g. `nine_ew_quantities`).
- Expected vs. actual behaviour, or the nature of the error.
- Your `lean --version` output.
- A minimal repro if the issue is a build or elaboration failure.

---

## Zulip and Longer Discussion

Longer discussions, design questions, and help requests are best routed to the [leanprover-community Zulip](https://leanprover.zulipchat.com/). The project will open an announcement thread in `#new members` — **URL to be announced** once it lands. Until then, the GitHub issue tracker is the primary async channel.

---

## Licensing

TauLib is licensed under Apache-2.0. See [LICENSE](LICENSE). There is no Contributor License Agreement — a DCO sign-off on each commit is sufficient.

---

## Code of Conduct

We follow the Lean Community standards: https://leanprover-community.github.io/meta.html

---

## Maintainer Responsiveness

- **Issues:** triaged within 7 calendar days.
- **Small PRs:** reviewed within 14 days.
- **Medium and large PRs, and substantive issues:** addressed publicly in the issue or PR thread, with a visible trace of the decision-making. If something is going to take longer than the standard window, the maintainer will say so in-thread.

---

## Code Style (Reference)

The conventions below apply to all TauLib code. A contribution that respects them will move faster through review.

### Namespaces

```
Tau.{Family}.{Module}
```

Examples: `Tau.Kernel.Axioms`, `Tau.Boundary.SplitComplex`, `Tau.Electroweak.EWSynthesis`.

### Naming

| Element | Convention | Example |
|---------|-----------|---------|
| Theorems / lemmas | `lowercase_with_underscores` | `rigidity_non_omega` |
| Definitions | `lowercase_with_underscores` | `iota_tau_float` |
| Structures | `PascalCase` | `TauObj`, `SplitComplex` |
| Inductive types | `PascalCase` | `Generator`, `OrbitRay` |
| Instances | Named explicitly | `instAddSplitComplex` |
| Type aliases | `PascalCase` | `TauIdx` |

### Module Docstrings

Every `.lean` file starts with a `/-! -/` block:

```lean
/-!
# TauLib.BookN.Family.Module

Brief description of the module's mathematical content.

## Registry Cross-References

- [N.DX] DefinitionName -- `lean_identifier`
- [N.TX] TheoremName    -- `lean_identifier`

## Mathematical Content

Why this module exists and how it fits into the larger structure.

## Ground Truth Sources

- Chapter X of Book N (section X.Y)
-/
```

### Declaration Docstrings

Every `def`, `theorem`, `lemma`, `structure`, `class`, and `inductive` has a `/-- -/` docstring that mentions its registry ID where one exists:

```lean
/-- The master constant ι_τ = 2/(π + e) ≈ 0.341304.
    Governs all quantitative predictions in Category τ.
    Registry: [I.D45] -/
def iota_tau_float : Float := 2.0 / (Float.pi + Float.exp 1.0)
```

### Registry IDs

| Prefix | Meaning | Example |
|--------|---------|---------|
| `I.` – `VII.` | Book number | `IV.T140` |
| `K` | Kernel axiom | `I.K1` |
| `D` | Definition | `V.D317` |
| `T` | Theorem | `IV.T66` |
| `P` | Proposition | `V.P176` |
| `R` | Remark | `IV.R260` |
| `OP` | Open Problem | `V.OP12` |

### Scope Labels

| Tier | Meaning |
|------|---------|
| **established** | Classical mathematics, independently verified. |
| **τ-effective** | Quantitative prediction derived within the τ framework. |
| **conjectural** | Structural claim, computationally verified but not derived from axioms. |
| **metaphorical** | Philosophical or analogical extension. |

See [docs/SCOPE_LABELS.md](docs/SCOPE_LABELS.md) for full details.

---

## Building

```bash
lake build                    # full build
lake build TauLib.BookI       # a single book
cat lean-toolchain            # pinned Lean version
```

The first build fetches Mathlib and takes several minutes; subsequent builds are cached.

---

## Citing TauLib

```bibtex
@software{taulib2026,
  author    = {Fuchs, Thorsten and Fuchs, Anna-Sophie},
  title     = {{TauLib}: Mechanized Formalization of Category $\tau$},
  year      = {2026},
  version   = {2.0.0},
  url       = {https://github.com/panta-rhei-research/taulib},
  license   = {Apache-2.0}
}
```

Or use the [CITATION.cff](CITATION.cff) file via GitHub's "Cite this repository" feature.
