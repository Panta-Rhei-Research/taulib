import TauLib.BookI.Polarity.Polarity
import Mathlib.Tactic.Linarith

/-!
# TauLib.BookI.Polarity.LegendreClassifier

**Legacy Prop-level bridge for bound-dependent spectral diagnostics.**

Despite the historical file name, this module does not implement the canonical
Legendre `(2/p)` classifier from `papers/prime-polarity/main.tex`. It lifts the
older Boolean `partition_check` / `pol_at` diagnostics from `Polarity.lean` to
Prop-level statements.

## Workstream B1.3 deliverable (Phase 2B partial)

This module ships the **finitist, kernel-pure** diagnostic bridge:

1. **Bool ↔ Prop bridges** — `partition_check_iff`,
   `b_class_witness_iff`, `c_class_witness_iff` convert the existing
   `Bool` verifiers into Prop predicates suitable for theorem citation.
2. **Prop-level diagnostic dichotomy** (`prime_polarity_dichotomy`) — every
   prime is either B-dominant or C-dominant at any bound `N`.
3. **Disjointness** (`b_c_dominance_disjoint`,
   `prime_class_dichotomy_disjoint`) — no prime is both B-dominant and
   C-dominant at the same bound.
4. **Exhaustiveness at prime level** (`prime_class_dichotomy_exhaustive`)
   — every prime is classified by exactly one witness.

For the canonical prime-polarity theorem, use
`PrimePolarityClassifier.lean`, `PrimePolarityIsomorphism.lean`, and
`H2H3ClassifierBridge.lean`: B iff `(2/p)=+1`, C iff `(2/p)=-1`, and `p=2`
is the crossing label X.

## Registry Cross-References

- [I.D19e]                Bound-dependent spectral diagnostic verifier in
                          `Polarity.lean`
- [I.T-PP-Dichotomy-Prop] `prime_polarity_dichotomy` (this module)
- [I.T-PP-BoolPropBridge] `partition_check_iff` /
                          `{b,c}_class_witness_iff` (this module)
- [I.T-PP-Disjoint]       `b_c_dominance_disjoint` /
                          `prime_class_dichotomy_disjoint` (this module)
- [I.T-PP-Exhaustive]     `prime_class_dichotomy_exhaustive` (this module)
- [I.T-PP-Density-Half]   `b_density_one_half` — Dirichlet asymptotic
                          1/2 (queued B1.3c, requires Mathlib
                          analytic-NT bridge)

## Cross-references

- `atlas/audits/taulib/2026-05-03-foundations-bridges-state-of-the-union.md`
  §8 wave B1.3 — the A1 dossier's roadmap entry for this wave.
- `ROADMAP-3-HINGES.md` Phase 2B — the original strategic plan; this
  module closes the dichotomy + Bool-Prop-bridge half.
-/

set_option autoImplicit false

namespace Tau.Polarity

open Tau.Denotation Tau.Coordinates

-- ============================================================
-- PART 1: BOOL ↔ PROP BRIDGES
-- ============================================================

/-- **Bool ↔ Prop bridge for `partition_check`.**

    The Boolean check `partition_check n N = true` is logically equivalent
    to the arithmetic identity
    `count_b_dominant n N + count_c_dominant n N = count_primes n`.

    Trivial unfold + `beq_iff_eq`. Useful for citing the existing
    `#eval partition_check 50 1000  -- true` smoke tests as Prop-level
    facts at concrete bounds via `decide` or `native_decide`. -/
theorem partition_check_iff (n N : TauIdx) :
    partition_check n N = true ↔
      count_b_dominant n N + count_c_dominant n N = count_primes n := by
  unfold partition_check
  exact beq_iff_eq

/-- **Bool ↔ Prop bridge for `b_class_witness`.**

    `b_class_witness p N = true` ↔ `p` is prime AND polarity-classified
    as B-dominant. -/
theorem b_class_witness_iff (p N : TauIdx) :
    b_class_witness p N = true ↔
      is_prime_bool p = true ∧ pol_at p N = true := by
  simp [b_class_witness]

/-- **Bool ↔ Prop bridge for `c_class_witness`.**

    `c_class_witness p N = true` ↔ `p` is prime AND polarity-classified
    as C-dominant. -/
theorem c_class_witness_iff (p N : TauIdx) :
    c_class_witness p N = true ↔
      is_prime_bool p = true ∧ pol_at p N = false := by
  simp [c_class_witness]

-- ============================================================
-- PART 2: PROP-LEVEL POLARITY DICHOTOMY
-- ============================================================

/-- **Bound-dependent diagnostic polarity dichotomy (Prop form).**

    For every prime `p` and every bound `N`, the polarity classification
    `pol_at p N : Bool` is either `true` (B-dominant: B_max > C_max in
    the spectral signature) or `false` (C-dominant: B_max ≤ C_max).

    This is the Prop-level lift of the implicit Bool case-split on
    `pol_at p N`, making the dichotomy citable in Prop-level theorems
    (rather than relying on `Bool.eq_dec` at every callsite). -/
theorem prime_polarity_dichotomy (p N : TauIdx) :
    pol_at p N = true ∨ pol_at p N = false := by
  cases h : pol_at p N
  · right; rfl
  · left; rfl

-- ============================================================
-- PART 3: DISJOINTNESS + EXHAUSTIVENESS AT THE PRIME LEVEL
-- ============================================================

/-- **B/C dominance disjointness (Prop form).**

    No prime is simultaneously B-dominant and C-dominant at the same
    bound — the witnesses `b_class_witness` and `c_class_witness` are
    mutually exclusive (modulo the shared `is_prime_bool` precondition). -/
theorem b_c_dominance_disjoint (p N : TauIdx) :
    ¬ (b_class_witness p N = true ∧ c_class_witness p N = true) := by
  intro ⟨hb, hc⟩
  rw [b_class_witness_iff] at hb
  rw [c_class_witness_iff] at hc
  -- hb.2 : pol_at p N = true ; hc.2 : pol_at p N = false
  rw [hb.2] at hc
  exact Bool.noConfusion hc.2

/-- **Prime-level partition exhaustiveness.**

    Every prime is classified by exactly one of `b_class_witness` or
    `c_class_witness` at any bound. Direct consequence of
    `prime_polarity_dichotomy` plus the witness definitions. -/
theorem prime_class_dichotomy_exhaustive (p N : TauIdx)
    (hp : is_prime_bool p = true) :
    b_class_witness p N = true ∨ c_class_witness p N = true := by
  rcases prime_polarity_dichotomy p N with h | h
  · left; rw [b_class_witness_iff]; exact ⟨hp, h⟩
  · right; rw [c_class_witness_iff]; exact ⟨hp, h⟩

/-- **Prime-level partition disjointness.**

    Alias of `b_c_dominance_disjoint`. No prime can be both B-class and
    C-class at the same bound. -/
theorem prime_class_dichotomy_disjoint (p N : TauIdx) :
    ¬ (b_class_witness p N = true ∧ c_class_witness p N = true) :=
  b_c_dominance_disjoint p N

end Tau.Polarity
