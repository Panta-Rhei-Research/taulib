# TauLib Refactoring Roadmap — Three Hinge Theorems

**Status:** Strategic planning phase
**Version:** v1.0 (2026-04-21)
**Authors:** Thorsten Fuchs & Anna-Sophie Fuchs (via collaborative planning session)

---

## 1. Executive Summary

This document plans the porting of the three hinge theorems of the Panta
Rhei τ-framework from their LaTeX proof form (three research papers,
completed April 2026) into Lean 4 / TauLib formal proofs:

1. **Hyperfactorization** (Book I Theorem I.T04)
   — unique tower-atom decomposition
2. **Prime Polarity** (Book I Theorem I.T05)
   — B/C prime split and Dirichlet density $R_B = 1/2$
3. **Master Constant** (Book I Chapter 41, corrected via ERRATUM-004)
   — structural derivation of $\iota_\tau = 2/(\pi + e)$

The overarching goal: **replace fiat definitions with structural ones**.
Most critically, $\iota_\tau$ should cease to be a hardcoded
`Nat/Nat` pair in `BookI/Boundary/Iota.lean` and instead be defined
as the scalar readout of the crossing-point defect $\omega$-germ,
with the numerical identity $\iota_\tau = 2/(\pi+e) \approx 0.341304$
appearing as a theorem.

Estimated total effort: **~3000-4000 Lean lines, ~18 weeks elapsed
(or 6-8 weeks with 3 engineers in parallel)**.

---

## 2. Current State Assessment

### 2.1 TauLib overall state

- **125,771 LOC, 450 modules, 4,332 theorems, 3,542 definitions**
- **Only 3 `sorry`** — all in Book VII (methodological, not structural)
- Books I–VI: **zero `sorry`**
- Build system: Lake; mathlib allowed for **tactics only** (no
  mathematical content)
- `autoImplicit = false` — every variable explicit

### 2.2 Three hinge theorems — current state

All three exist as **computable Boolean verifiers with narrative
docstrings**, but the Prop-level structural theorems the papers
prove are **not yet present**.

| Theorem | Current state | Gap |
|---|---|---|
| **ι_τ master constant** | `iota_tau_numer : Nat := 341304` (fiat, `Iota.lean:41`) | No link to π, e; no formal theorem of the identity |
| **Prime Polarity** | `partition_check : Bool` (L220 Polarity.lean) | No density theorem, no Legendre-symbol classifier |
| **Hyperfactorization** | `hyperfact_check : Bool` (L61 Hyperfact.lean) | No Prop-level `∃!` theorem |

### 2.3 Substrate readiness

The **foundation is sufficient**:

| Substrate | Module | Status |
|---|---|---|
| `SplitComplex` (j² = +1) | `BookI/Polarity/BipolarAlgebra.lean` + `Boundary/SplitComplex.lean` | **Complete** — full ring axioms proved |
| `AlgebraicLemniscate` | `BookI/Polarity/Lemniscate.lean` | **Complete structurally** — σ-involution, canonical construction |
| σ involution / polarity swap | `BookI/Polarity/BipolarAlgebra.lean` | Proved |
| `OmegaTail` (finite-depth ω-germs) | `BookI/Polarity/OmegaGerms.lean` | **Present but computational** — needs `InverseLimit` extension |
| `TauReal` (Cauchy-style reals) | `BookI/Boundary/ConstructiveReals.lean` | **Partial** — see §2.4 below |

### 2.4 TauReal audit finding (critical for Phase 0)

TauReal **exists** but is a simplified "sequence of TauRat
approximations" wrapper (structure with `approx : Nat → TauRat`),
**not a true Cauchy-quotient completion**.

**Present:**
- `TauReal.add, mul, sub, negate, fromTauRat, fromNat`
- Ring axioms (proved as `taureal_*` theorems, bundled in
  `taureal_ring_axioms`)
- `taureal_archimedean_embedding` (injective embedding from ℕ)

**Missing (critical for refactor):**
- `TauReal.inv`, `TauReal.div` — **cannot form `2/(π+e)` today**
- `TauReal.lt, le, abs` (ordering, absolute value)
- `TauReal.lim` / `Cauchy.toReal` / any limit-taking operation
- `TauReal.pi` — does not exist
- `TauReal.exp 1` — does not exist
- No mathlib bridge (by design — TauLib's policy is
  mathlib tactics only, not content)

---

## 3. Strategic Approach

### 3.1 Phase map

| Phase | Scope | Lines | Weeks | Parallel? |
|---|---|---:|---:|:-:|
| **Phase 0** | TauReal extensions + structural ι_τ refactor | ~200 | 2 | No (blocks all) |
| **Phase 1** | Shared foundations (Lemniscate, ω-germs, Read, PolarityLattice, BipolarSwap) | 400-500 | 2 | No |
| **Phase 2A** | Hyperfactorization uniqueness | 500-700 | 3-4 | Yes |
| **Phase 2B** | Prime Polarity (Route B) | 500-600 | 3-4 | Yes |
| **Phase 2C** | iota-tau Steps 1-10 | ~1280 | 6-8 | Yes |
| **Phase 3** | Integration + iota-tau Step 11 (split-complex lift) | 200-300 | 2 | No |
| **Phase 3'** | iota-tau Step 12 (Saturation, Enrich^4=Enrich^3) | 120-400 | 2-4 | Gated |
| **Phase 4** | Numerical evaluation + `#eval` certificate | 50-100 | 0.5 | No |

### 3.2 Dependency analysis

**iota-tau is the capstone paper** (1280 core lines + extensions) but
**does NOT structurally depend** on Hyperfactorization or Prime Polarity
as completed theorems. Cross-paper references are thematic only.
Consequence: Phases 2A, 2B, 2C can run in parallel after Phase 1
foundations.

**Hyperfactorization is the lowest-risk starter** — most pieces already
in `BookI/Coordinates/*.lean` (`no_tie`, `Descent`, `ABCD`); needs only
elevation from Boolean verifier to Prop-level uniqueness via strong
induction.

**Prime Polarity Route B is explicitly independent of Hyperfactorization
I.T04** (paper §1760, "Route B's entire pipeline lives at the
CRT-idempotent level without invoking hyperfactorization"). This
breaks a potential circular dependency.

---

## 4. Phase 0 — Detailed Plan (based on TauReal audit)

### 4.1 Goal

Replace `iota_tau : Nat/Nat` fiat definition with a structural
`iota_tau : TauReal` derived from the defect-germ scalar readout, and
prove `iota_tau = 2/(π + e)` as a theorem in TauReal.

### 4.2 Sub-tasks

**P0.1 — Extend ConstructiveReals.lean with pi, e constants** (~45 lines)

Add two standalone definitions of TauReal constants using the
*direct-sequence* idiom (no quotient, no Cauchy machinery):

```lean
-- In BookII/Transcendentals/PiEarned.lean (extend)
-- Leibniz / Archimedes-polygon series (already scaled integer in pi_scaled)
noncomputable def TauReal.pi : TauReal where
  approx n := ⟨⟨pi_scaled n, 0⟩, 10^n, pow_pos_of_two ..⟩

-- In BookII/Transcendentals/EEarned.lean (extend)
noncomputable def TauReal.e : TauReal where
  approx n := ⟨⟨e_factorial_scaled n, 0⟩, fact_denom n, fact_denom_pos ..⟩
```

Estimated: **~20 lines per constant + 5 lines for the denominator
positivity lemmas = ~45 lines total**.

**P0.2 — Add TauReal.two** (~1 line)

```lean
noncomputable def TauReal.two : TauReal := TauReal.fromNat 2
```

**P0.3 — Direct-sequence definition of ι_τ avoiding division** (~10 lines)

Since `TauReal.inv` / `TauReal.div` don't exist yet, define ι_τ as a
direct sequence matching `2 * 10^n / (pi_scaled n + e_scaled n)`:

```lean
-- In BookI/Boundary/Iota.lean (rewrite)
noncomputable def iota_tau : TauReal where
  approx n := ⟨⟨2 * 10^n, 0⟩, pi_scaled n + e_scaled n, pi_plus_e_pos ..⟩
```

This is the **structural** definition: a canonical sequence
earned from the paper's construction. The Nat/Nat fiat becomes a
**derived bound**:

```lean
-- Preserved for backward compatibility (~50 downstream callsites)
def iota_tau_numer : Nat := 341304  -- now: derived bound
def iota_tau_denom : Nat := 1000000
lemma iota_tau_bound :
  TauReal.approx iota_tau 7 = ⟨⟨iota_tau_numer * 10, 0⟩, iota_tau_denom * 10, _⟩ := by
  native_decide
```

**P0.4 — The numerical identity theorem** (~40 lines, the hard step)

Prove the pointwise-TauRat identity linking the ι_τ sequence to
the 2/(π+e) sequence. This requires adding `TauRat.inv` with a
nonzero hypothesis:

```lean
-- New in TauRat.lean (~30 lines)
noncomputable def TauRat.inv (q : TauRat) (h : q.num ≠ 0) : TauRat := ...
-- Prove basic properties: inv_mul_self, inv_nonzero, etc.

-- In Iota.lean
theorem iota_tau_eq_two_over_pi_plus_e_pointwise :
  ∀ n, TauRat.equiv
    (iota_tau.approx n)
    (TauRat.two.mul (TauRat.inv ((TauReal.pi.approx n).add (TauReal.e.approx n)) _)) := by
  intro n
  -- direct algebraic manipulation on TauRat
  ...
```

From this pointwise identity, `iota_tau = 2/(π_τ + e_τ)` at the
TauReal-equiv level follows by `TauReal.equiv` unfolding.

**P0.5 — Reconcile backward compatibility** (~20 lines, audit-driven)

Audit the ~50 downstream callsites of `iota_tau_numer` /
`iota_tau_denom` (identified in `BookIV/MassDerivation/BreathingModes.lean:92`,
`BookV/GravityField/NonlinearEinstein.lean:435`, etc.). Ensure the
new structural definition preserves these as derived bounds so no
callsite proof breaks.

### 4.3 Phase 0 deliverables

At the end of Phase 0:

1. `TauReal.pi` and `TauReal.e` exist as canonical sequences (not via
   Cauchy quotient, but as direct sequence approximants — sufficient
   for current needs).
2. `TauReal.two` is a named constant.
3. `TauRat.inv` with nonzero hypothesis is implemented with basic
   properties.
4. `iota_tau : TauReal` is the structural definition in `Iota.lean`.
5. `iota_tau_eq_two_over_pi_plus_e` is a proven theorem.
6. `iota_tau_numer` / `iota_tau_denom` remain as derived bounds;
   downstream callsites continue to compile.
7. `BookI/Boundary/Iota.lean` docstring updated:
   old: *"iota_tau is NOT defined as a real number (deferred to Book II)"*
   → new: *"iota_tau is the canonical scalar readout of the
   crossing-point defect germ; the numerical identity
   `iota_tau = 2/(π + e)` is Theorem `iota_tau_eq_two_over_pi_plus_e`."*

### 4.4 Phase 0 estimated effort

**~200 Lean lines** (45 + 1 + 10 + 40 + 30 + 20 + proofs), **2 weeks
for one engineer**. No mathlib bridge required. No full Cauchy-quotient
TauReal rewrite required (that's a separate wave if desired).

### 4.5 Phase 0 risks

**R0.1 — TauRat.inv complexity.** If `TauRat` lacks a `num_ne_zero`
witness field, adding `inv` may require restructuring TauRat itself.
Mitigation: spot-check TauRat.lean first (before starting P0.4) and
scope the inv extension.

**R0.2 — pi_scaled / e_factorial_scaled numerical precision.** The
existing Leibniz / factorial series produce *integer approximations*
— need to verify they converge accurately enough for the identity
theorem's pointwise bound to hold. Mitigation: if precision is
insufficient, add improved series (e.g., Machin-like π formula,
faster-converging e series) — estimated +50 lines.

**R0.3 — Downstream callsite breakage.** ~50 files reference
`iota_tau_numer` / `iota_tau_denom`. Mitigation: preserve these as
derived bounds with same Nat values (Phase 0 maintains exact
numerical compatibility).

---

## 5. Phases 1-4 — High-Level Plan

### 5.1 Phase 1 — Shared Foundations (~400-500 lines, 2 weeks)

Build once, reuse three times:

- `BookI/Polarity/Lemniscate.lean` extension — σ-involution on
  $\mathbb{L} = S^1 \vee S^1$ as wedge, crossing point $\omega_\times$
- `BookI/Polarity/OmegaGerms.lean` — full `InverseLimit` type
  (upgrade from finite-depth tuples)
- `BookI/Boundary/Read.lean` (**new**) — `ReadF_n`, `ReadF = invLim`,
  `ReadOrth` functor (using Phase 0's TauReal.pi, TauReal.e)
- `BookI/Polarity/PolarityLattice.lean` — $\Lambda[n]$ with labeled
  classes (B / C / ×)
- `BookI/Polarity/BipolarSwap.lean` — universal lobe-swap API

### 5.2 Phase 2 — Per-paper cores (parallelisable)

Each phase delivers the Prop-level theorems replacing the current
Boolean verifiers.

**Phase 2A — Hyperfactorization** (~500-700 lines):
- `theorem hyperfactorization : ∀ x ≥ 2, ∃! abcd, ValidABCD x abcd`
- Uses existing `no_tie` + `Descent` + strong induction
- Deliverable module: `BookI/Coordinates/Hyperfact.lean` upgrade

**Phase 2B — Prime Polarity Route B** (~500-600 lines):
- New `BookI/Polarity/LegendreClassifier.lean` (mod-8 classifier)
- Dichotomy theorem (Prop-level, replacing `partition_check` Bool)
- Density theorem (partial — density = 1/2 via Dirichlet-in-AP from
  mathlib; density→ι_τ identification deferred to Phase 3)

**Phase 2C — iota-tau Steps 1-10** (~1280 lines):
- Crossing-point defect germ construction (Steps 4-5)
- Non-polarity + ω-approach halves (Steps 6a-6b)
- Intersection + universality (Steps 6c-7)
- Coupling identity (Step 9 — depends on Phase 0's TauReal.pi, e)
- Numerical readout (Step 10 — this promotes Phase 0's
  pointwise-TauRat identity to the full scalar-algebra theorem)

### 5.3 Phase 3 — Integration (~200-300 lines, 2 weeks)

- **Step 11**: split-complex lift via Book II ch.47 idempotent
  decomposition — `BookI/IotaTau/SplitComplex.lean` or equivalent
- Cross-paper consistency: Prime Polarity's χ character agrees with
  iota-tau's split-complex χ̃ lift
- Capstone theorem module `BookI/IotaTau/NumericalIdentity.lean`:
  the final `iota_tau_eq_two_over_pi_plus_e` with full chain

### 5.4 Phase 3' — Saturation (gated on Book VII ch.48)

- iota-tau Step 12: `Enrich^4(τ) = Enrich^3(τ)` saturation theorem
- Blocked until Book VII chapter 48 (self-enrichment tower)
  is formalised
- **Recommendation**: ship 3-hinge refactor WITHOUT Phase 3', add
  later when Book VII matures

### 5.5 Phase 4 — Numerical evaluation (~50-100 lines, 0.5 week)

- Interval-arithmetic proof: `|ReadOrth iota_tau - 0.341304238875| < 10^{-12}`
- Optional `#eval` certificate via `native_decide` on bounded
  rational approximation
- Verification against the 2nd-Ed locked constant
  (CLAUDE.md: 0.341304238875... as of 2026-02-18)

---

## 6. Key Open Decisions

### D1. Mathlib content policy

**Current**: Lakefile allows mathlib **tactics only**, not content.

**Question**: Can we import `Mathlib.Data.Real.Basic` + `Real.pi` +
`Real.exp` for the Phase 4 numerical cross-verification? This would
enable a bridge theorem `TauReal.pi ≈ Real.pi` to within
proven error bounds.

**Impact**: If **yes**, Phase 4 is straightforward (~50 lines).
If **no**, Phase 4 requires native TauReal interval arithmetic
(~100 lines, more work but keeps mathlib-free purity).

**Recommendation**: start with **no mathlib content** policy
(preserves TauLib's purity claim), revisit if Phase 4 blockers
emerge.

### D2. Backward compatibility strategy

**Current plan**: preserve `iota_tau_numer` / `iota_tau_denom` as
derived bounds so ~50 downstream callsites compile unchanged.

**Alternative**: rewrite all callsites to use the new structural
`iota_tau : TauReal` directly, removing the Nat/Nat intermediate.

**Recommendation**: derived-bounds strategy (safer, preserves
momentum, downstream can migrate incrementally).

### D3. Sprint parallelisation

**Sequential** (1 engineer): ~18 weeks total
**Parallel** (3 engineers on Phases 2A/2B/2C after Phase 1): ~6-8
weeks total

**Recommendation**: start sequential (build momentum, confirm
patterns work); parallelise Phase 2 once Phase 1 foundations are
proven.

### D4. Phase 3' (Saturation / Enrich^4 = Enrich^3) gating

**Option A**: Ship 3-hinge refactor without Step 12. Add later as
Book VII matures.
**Option B**: Delay release until Book VII ch.48 is formalised
(unknown timeline).

**Recommendation**: **Option A** — the three hinges stand on their
own; Step 12 is a structural bonus, not a prerequisite.

### D5. Cauchy-quotient TauReal upgrade

Current TauReal is a simplified "sequence wrapper" with pointwise-equiv
semantics. A proper Cauchy-quotient construction would be more
mathematically honest but is a separate ~200-300 line wave.

**Recommendation**: **keep simplified TauReal for now** (Phase 0
works with existing semantics); schedule Cauchy-quotient upgrade as
a separate wave after 3-hinge refactor completes.

---

## 7. Progress Tracking

### 7.1 Milestone ledger

| Milestone | Phase | Status | Target date |
|---|---|---|---|
| M0: TauReal audit complete | 0 | ✅ Done (2026-04-21) | — |
| M1: Strategy doc ratified | — | 🟡 In review | 2026-04-21 |
| M2: TauReal.pi, TauReal.e, TauReal.two | 0 | ⬜ Pending | +2 days |
| M3: TauRat.inv + nonzero hypothesis | 0 | ⬜ Pending | +3 days |
| M4: Structural iota_tau + numerical theorem | 0 | ⬜ Pending | +1 week |
| M5: Phase 0 complete (Iota.lean refactor) | 0 | ⬜ Pending | +2 weeks |
| M6: Phase 1 foundations | 1 | ⬜ Pending | +4 weeks |
| M7: First hinge theorem ported (2A recommended) | 2A | ⬜ Pending | +7-8 weeks |
| M8: All three hinges ported | 2A-2C | ⬜ Pending | +14-16 weeks |
| M9: Numerical evaluation certificate | 4 | ⬜ Pending | +16-18 weeks |

### 7.2 Risk register

| ID | Risk | Severity | Mitigation |
|---|---|---|---|
| R0.1 | TauRat.inv complexity | Medium | Audit TauRat before P0.4 |
| R0.2 | pi_scaled / e_scaled precision | Low | Add improved series if needed |
| R0.3 | Callsite breakage | Low | Preserve derived bounds |
| R1.1 | OmegaGerms InverseLimit type refactor | Medium | Prototype in spike branch first |
| R2C.1 | Novel σ-equivariant holomorphic transformer API | High | Spike early, pair with paper author |
| R3'.1 | Book VII ch.48 dependency | High | Gate Phase 3', ship without if needed |

---

## 8. Appendices

### A. Key file paths (repo-relative)

**Upstream papers (LaTeX source, in the Panta Rhei book repo, not TauLib):**
- `papers/iota-tau/main.tex` (v2.9, 33 pages)
- `papers/prime-polarity/main.tex`
- `papers/hyperfactorization/main.tex`

**TauLib primary refactor targets (paths below are relative to TauLib repo root):**
- `TauLib/BookI/Boundary/Iota.lean`
- `TauLib/BookI/Boundary/ConstructiveReals.lean`
- `TauLib/BookI/Polarity/Polarity.lean`
- `TauLib/BookI/Coordinates/Hyperfact.lean`

**TauLib shared infrastructure:**
- `BookI/Polarity/Lemniscate.lean`, `BipolarAlgebra.lean`, `OmegaGerms.lean`, `PolarizedGerms.lean`, `Spectral.lean`
- `BookI/Coordinates/NoTie.lean`, `Descent.lean`, `ABCD.lean`
- `BookI/Boundary/SplitComplex.lean`
- `BookII/Hartogs/BndLift.lean`, `EvolutionOperator.lean`, `MutualDetermination.lean`
- `BookII/CentralTheorem/CentralTheorem.lean`, `ExtensionsOmegaGerms.lean`

### B. Paper cross-references

| Paper | Lean section label | Line range |
|---|---|---|
| iota-tau | `sec:lean-plan` | 2975-3058 |
| prime-polarity | `sec:lean-plan` | 1694-1795 |
| hyperfactorization | `sec:lean-plan` | 1340-1428 |

### C. Historical context

- **2026-02-18**: ι_τ corrected to 0.341304238875... (was 0.341459 in
  1st Ed) — locked in Book II, not yet reflected in Iota.lean
- **2026-04-21 (this session)**: Three hinge papers completed to
  v2.9 / v1 structural rigour; TauLib refactor roadmap drafted

### D. Companion documents

- `RELEASE_NOTES.md` — TauLib release tracking (will be updated
  per phase)
- `ATLAS.md` — registry-to-Lean cross-reference (to be updated as
  hinge theorems are ported)

---

## Change Log

- **v1.0 (2026-04-21)**: Initial strategy document. Based on parallel
  reconnaissance reports covering (a) Lean roadmaps across all three
  papers and (b) TauLib kernel audit including TauReal substrate
  status. Phase 0 plan detailed; Phases 1-4 high-level.

- **v1.1 (2026-04-21)**: Phase 0 expanded into a **full 4-wave TauReal
  infrastructure build** (replaces minimal `direct-sequence avoidance`
  approach). New scope: ~900 lines instead of ~200. Decision: walk the
  hard way and build proper Cauchy semantics, ordering, field
  operations, and standard constants natively in TauLib.

  | Wave | Scope | Lines | Module |
  |---|---|---:|---|
  | 1 | TauRat field & order (`equiv_trans`, `toRat`, `lt/le/abs/inv/div`) | ~250 | `TauRatField.lean` (new) |
  | 2 | TauReal Cauchy semantics + ordering | ~300 | `TauRealCauchy.lean` (new) |
  | 3 | TauReal constants (π, e via Cauchy series) | ~200 | extend `PiEarned.lean`, `EEarned.lean` |
  | 4 | Structural ι_τ + numerical identity | ~150 | refactor `Iota.lean` |

- **v1.2 (2026-04-21)**: **Tactical-constraint audit complete.**
  Discovered that `Mathlib.Tactic.FieldSimp` and `Mathlib.Tactic.Linarith`
  are **NOT in TauLib's effective tactic budget** because their
  discharger sub-modules pull in `Mathlib.Algebra.Field.*`,
  `Mathlib.Algebra.Order.*`, `Mathlib.Algebra.Group.Nat.Defs`,
  `Mathlib.Logic.Basic` — all mathematical content forbidden by lakefile
  policy.  Effective budget: `ring`, `ring_nf`, `linear_combination`,
  `norm_num`, `push_cast`, `omega`, `decide`, `native_decide`, plus
  Lean core types (`Rat`, `Int`, `Nat`) with their built-in operations.

  **Strategy: Option B1 + selective B3.**  Push through with manual
  tactical work, building TauLib-internal helper lemmas opportunistically
  as patterns recur.  Wave 1 split into 4 sub-waves for compile-time
  isolation:

  | Sub-wave | Scope | Lines | Module | Status |
  |---|---|---:|---|---|
  | 1a | `equiv_trans`, `toRat` bridge, homomorphisms, `is_nonzero` | 223 | `TauRatField.lean` | ✅ DELIVERED |
  | 1b | Ordering (`lt`, `le`, transitivity, trichotomy) | ~80 | `TauRatOrder.lean` | next |
  | 1c | Absolute value (`abs` + properties) | ~100 | `TauRatAbs.lean` | pending |
  | 1d | Inverse + division (`inv`, `div` with nonzero hypotheses) | ~150-200 | `TauRatInv.lean` | pending |

  **Revised estimates** (factoring 2-3× tactical-work overhead):
  Wave 1 ~600 lines, Wave 2 ~600 lines, Wave 3 ~250 lines, Wave 4 ~200
  lines.  Total ~1650 lines (was 900).

- **v1.3 (2026-04-21)**: **Wave 1a delivered and compiling.**  223
  lines.  TauRat now has `equiv_trans` (the missing piece in
  NumberTower), `toRat` semantic bridge, full set of homomorphism
  properties (`toRat_add/mul/negate/sub/zero/one`), and `is_nonzero`
  predicate with equiv preservation.  Smoke tests passing.
