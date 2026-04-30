# Formalization Status

This document is a local orientation note for TauLib's formalization status. The authoritative public snapshot for current metrics, trusted-base details, axiom/sorry status, and count reconciliation is the [Panta Rhei Release Manifest](https://panta-rhei.site/verify/release-manifest/).

---

## Summary

- Current public metrics live in the Release Manifest, not in this hand-maintained document.
- TauLib's CI builds the Lean source and enforces the repository's axiom/sorry checks.
- The public verification site separates Lean compilation from empirical truth, bridge adequacy, semantic correspondence, and external acceptance.

---

## Axiom Inventory

TauLib contains exactly **3 axioms**, all conjectural, all in Book III, each explicitly declared and documented.

### Conjectural Axioms (3)

These follow the "compute-then-axiomatize" pattern: a decidable check function is verified computationally via `native_decide` at all tested finite bounds. The axiom asserts that the property holds universally. Every theorem whose proof transitively invokes one of these axioms is a **conditional result**, conditional on the universal extension.

| # | Axiom | Module | What It Asserts |
|---|-------|--------|-----------------|
| 1 | `bridge_functor_exists` | `BookIII.Bridge.BridgeAxiom` | The bridge functor from the canonical enrichment ladder to the spectral decomposition exists for all n |
| 2 | `spectral_correspondence_O3` | `BookIII.Doors.SpectralCorrespondence` | The O(3) spectral correspondence holds universally |
| 3 | `grand_grh_adelic` | `BookIII.Doors.GrandGRH` | The adelic Generalized Riemann Hypothesis (used for spectral completeness) |

### Retired in `peer-review-fixes-v1` (2026-04-19)

A previously shipping fourth axiom, `central_theorem_physical` in `BookIV.Arena.BoundaryHolonomy`, has been retired. Its statement type was the trivial proposition `True`, which is inhabited by `trivial` — so the `axiom` declaration added nothing to the theory while inflating the inventory from 3 to 4. Pre-publication simulated peer review identified this as a null commitment. The architectural intent (pointing the Book IV reader at the Book II Central Theorem) is now carried by documentation comments and the registry cross-reference `[IV.T96]`, not by a formal declaration.

---

## Sorry Inventory

TauLib contains exactly **0 sorry** across all seven books.

Books I–VI have been sorry-free since Wave 12. Book VII previously shipped three `theorem X : True := sorry` declarations — `omega_point_theorem`, `science_faith_boundary`, `no_forced_stance` — encoding what the monograph calls *structural commitments*. Pre-publication simulated peer review identified this encoding as performative: the goal type `True` is provable by `trivial`, so a `sorry` on `True` is a marker with no formal content; additionally, `no_forced_stance : True := sorry` was being justified (in surrounding docstring prose) by citation of registry `VII.T47` — which was itself `no_forced_stance`, i.e.\ self-referentially.

### Commitment encoding (peer-review-fixes-v1)

In `TauLib/BookVII/Meta/Commitment.lean`, a `Commitment` structure is introduced:

```lean
structure Commitment where
  statement : String
  warrant : String
  registry_id : String
  deriving Repr, Inhabited
```

The three previously shipping `theorem` declarations are retired and replaced with `def` values of this structure, carrying inspectable string data for each commitment:

| # | Declaration | Module | Encodes |
|---|-------------|--------|---------|
| 1 | `omega_point_theorem` | `BookVII.Logos.Sector` | [VII.T46] The ω-generator's bridge-functor equivalence at S_L |
| 2 | `science_faith_boundary` | `BookVII.Logos.Sector` | [VII.P29] Four-register convergence at S_L across Reg_{E,P,D,C} |
| 3 | `no_forced_stance` | `BookVII.Final.Boundary` | [VII.T47] The structural framework does not force a stance here |

`#print axioms omega_point_theorem` reports no axioms (it is a `def`, not a theorem or axiom). `rg ':= sorry' TauLib/` returns zero matches. `#eval omega_point_theorem.statement` returns the literal commitment text for inspection.

**Key property:** no mathematical or physical result in Books I–VI depends on any sorry (there are none). The three Book VII commitments are data, not unproven propositions, and cannot be used as premises in any theorem.

---

## Scope Tier Distribution

Every module and registry entry carries a scope label from the [4-tier system](SCOPE_LABELS.md):

| Tier | Meaning | Approximate Coverage |
|------|---------|---------------------|
| **established** | Classical mathematics, independently verifiable | Books I&ndash;II foundations, standard analysis |
| **&tau;-effective** | Quantitative prediction derived from &iota;<sub>&tau;</sub> | Most of Books IV&ndash;V physics |
| **conjectural** | Structural claim, computationally verified | 3 axioms in Book III, select Book V claims |
| **metaphorical** | Philosophical/analogical | Book VII ethics and metaphysics |

---

## Verification Chain

The trust chain from axioms to results:

```
Lean 4 kernel (trusted)
    │
    ├── Lean core library (Nat, Prop, etc.)
    │
    ├── Mathlib tactics (simp, omega, ring, decide, ...)
    │       └── No mathematical content imported
    │
    └── TauLib
            ├── 7 axioms K0–K6 (K0 implicit in Lean's type system)
            │       └── 6 structural axioms → all of Book I
            │
            ├── 3 explicit axioms (all conjectural, all Book III)
            │       └── Isolated in Book III; not needed for Books I–II
            │       └── (4th axiom `central_theorem_physical` retired 2026-04-19 — was a no-op `axiom : True`)
            │
            ├── 0 sorry (all seven books sorry-free since peer-review-fixes-v1, 2026-04-19)
            │       └── 3 Book VII structural commitments encoded as `def : Commitment`, not sorry
            │
            └── Lean declarations and executable checks documented in the Release Manifest
                    └── Verified by Lean's kernel
```

---

## What "Zero Sorry Across All Seven Books" Means

This is the strongest claim a Lean formalization can make short of being fully axiom-free:

1. **Every theorem** in all seven books has a complete proof term verified by Lean's kernel
2. **Every `#eval`** produces a concrete value at compile time
3. **No `sorry`** appears anywhere in the proof terms of any book (`rg ':= sorry' TauLib/` returns zero matches)
4. The 3 `axiom` declarations are explicit, auditable, and isolated (all Book III; the 4th axiom `central_theorem_physical` was retired in `peer-review-fixes-v1` on 2026-04-19 as a no-op)

The three Book VII structural commitments (`omega_point_theorem`, `science_faith_boundary`, `no_forced_stance`) are encoded as `def` values of a `Commitment` structure, not as unproven propositions — they are data, not sorry.
