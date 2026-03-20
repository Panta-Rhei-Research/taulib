# Glossary

Key terms, symbols, and structures used throughout TauLib.

## Constants

| Symbol | Value | Lean Name | Description |
|--------|-------|-----------|-------------|
| ι_τ | 2/(π + e) ≈ 0.341304 | `iota_tau_float` | Master constant; governs all quantitative predictions |
| κ_D | 1 − ι_τ ≈ 0.658696 | — | Complementary constant (D-sector coupling) |
| κ_ω | ι_τ/(1 + ι_τ) ≈ 0.254485 | — | Omega coupling constant |
| W₃(4) | 5 | — | Third Wieferich quotient at 4; governs NLO corrections |
| W₃(3) | 4 | — | Third Wieferich quotient at 3 |

## Generators

| Generator | Symbol | Index | Role |
|-----------|--------|------:|------|
| `alpha` | α | 0 | Radial seed — its orbit becomes TauIdx (natural numbers) |
| `pi` | π | 1 | Prime base / multiplicative spine |
| `gamma` | γ | 2 | Exponent channel |
| `eta` | η | 3 | Tetration channel |
| `omega` | ω | 4 | Fixed-point absorber / closure beacon |

## Core Structures

| Lean Type | Module | Description |
|-----------|--------|-------------|
| `Generator` | `BookI/Kernel/Signature` | The 5-element generator type |
| `TauObj` | `BookI/Kernel/Axioms` | Objects in Category τ (seed + depth) |
| `TauIdx` | `BookI/Denotation/TauIdx` | Internal natural numbers (= `Nat`, earned from O_α) |
| `SplitComplex` | `BookI/Boundary/SplitComplex` | Split-complex numbers (boundary ring) |

## Key Spaces

| Symbol | Description | Lean Module |
|--------|-------------|-------------|
| τ³ | The τ-fibration: τ¹ ×_f T² | `BookII/Interior/Tau3Fibration` |
| τ¹ | Base circle (macrocosm) | `BookV/Temporal/BaseCircle` |
| T² | Fiber torus (microcosm) | `BookIV/Arena/Tau3Arena` |
| L | Lemniscate boundary: S¹ ∨ S¹ | `BookI/Polarity/Lemniscate` |

## Registry ID Format

Cross-references between TauLib and the Panta Rhei books use the format `[Book.TypeIndex]`:

| Prefix | Meaning | Example |
|--------|---------|---------|
| `I.` – `VII.` | Book number | `IV.T140` = Book IV |
| `K` | Axiom | `I.K1` = Axiom K1 |
| `D` | Definition | `V.D317` = Definition 317 |
| `T` | Theorem | `IV.T66` = Theorem 66 |
| `P` | Proposition | `V.P176` = Proposition 176 |
| `R` | Remark | `IV.R260` = Remark 260 |
| `OP` | Open Problem | `V.OP12` = Open Problem 12 |

## Axioms (K0–K6)

| Axiom | Name | One-Line Description |
|-------|------|---------------------|
| K0 | Universe Postulate | τ exists as a universe of discourse (implicit in Lean's type system) |
| K1 | Strict Order | The 5 generators are strictly totally ordered: α < π < γ < η < ω |
| K2 | Omega Fixed Point | ρ(ω) = ω — omega is the unique fixed point |
| K3 | Orbit-Seeded | ρ(g) is seeded by g for all non-ω generators |
| K4 | No-Jump (Cover) | ρ advances depth by exactly 1 |
| K5 | Beacon Non-Successor | ω is never reached by iterating ρ |
| K6 | Object Closure | Every TauObj is a generator or ρ-generated |
