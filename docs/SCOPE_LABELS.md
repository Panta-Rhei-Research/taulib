# Scope Labels

TauLib uses a 4-tier scope discipline to classify every mathematical claim. This system, introduced in Book III, ensures transparent epistemic status throughout the formalization.

## The Four Tiers

### Established

Classical mathematics that is independently verified and widely accepted. These results do not depend on Category τ — they are standard theorems formalized within the τ framework.

**Example:** The Chinese Remainder Theorem (`BookI/Polarity/ChineseRemainder.lean`)

### τ-Effective

Quantitative predictions derived within the Category τ framework. These are the core results — formulas that produce specific numerical values from the master constant ι_τ and structural parameters, testable against experimental data.

**Example:** CMB first peak at ℓ₁ = 220.6 with +69 ppm accuracy (`BookV/Cosmology/CMBSpectrum.lean`)

### Conjectural

Structural claims that are not yet derived from the axioms. Computationally verified at all tested finite bounds, but the infinite-limit assertion remains unproven. TauLib marks these with explicit `axiom` declarations.

**Example:** The bridge functor existence axiom (`BookIII/Bridge/BridgeAxiom.lean`) — all finite checks pass; the axiom asserts the infinite extension.

### Metaphorical

Philosophical or analogical extensions where formal mathematics meets lived experience. These mark the boundary between what can be formalized and what requires interpretation.

**Example:** The Categorical Imperative proof programme (`BookVII/Ethics/CIProof.lean`) — formalized as a j-closed fixed point, but its ethical content transcends the formalism.

## How Scope Labels Appear

In the LaTeX books, scope labels appear as colored side-bars around theorem environments. In TauLib, they appear in:

1. **Module docstrings** — each module header notes its dominant scope tier
2. **Registry cross-references** — entries like `[IV.T140]` carry scope in the registry TSV files
3. **Axiom declarations** — the 3 conjectural axioms are explicitly labeled in their docstrings

## The 4 Axioms and 3 Sorry

TauLib contains exactly 4 axioms (3 conjectural, 1 structural) and 3 sorry (all methodological, Book VII only). See the [README](../README.md) for the full list.

The conjectural axioms follow a "compute-then-axiomatize" pattern: a decidable finite check function is verified computationally via `native_decide`, then an axiom asserts the property holds universally. This makes the conjectural boundary maximally transparent.
