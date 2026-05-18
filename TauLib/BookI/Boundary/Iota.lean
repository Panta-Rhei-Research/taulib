import TauLib.BookI.Boundary.Ring
import TauLib.BookI.Boundary.SplitComplex

/-!
# TauLib.BookI.Boundary.Iota

The master constant iota_tau in its **fiat decimal form** —
the Nat-decidable witness representation used by ~35 BookIV/V/Tour
files for `decide` / `native_decide` physics-calibration checks.

## Two coexisting representations of iota_tau

Wave 4 of the TauReal infrastructure refactor (`TauRealIotaTau.lean`)
shipped a **structural** form `TauReal.iota_tau := 2 / (TauReal.pi + TauReal.e)`
with the defining identity `TauReal.iota_tau_mul_pi_plus_e_eq_two`
fully proven. The B1.0a callsite audit at
`atlas/audits/taulib/2026-05-03-iota-tau-callsite-audit.md` confirms
that **the two forms coexist as a documented dual-representation
pattern**, not a fiat-to-replace-with-structural migration:

| Form | Type | Use case | Module |
|---|---|---|---|
| `iota_tau_numer / iota_tau_denom` (this module) | `Nat / Nat` | Nat-decidable finite-witness checks for physics calibrations (162 callsites across 35 files) | this file |
| `TauReal.iota_tau` | `TauReal` | Theorem-cited identities; the Cauchy-completion class | `TauRealIotaTau.lean` |
| `iota_tau_float` (this module) | `Float` | `#eval` demonstrations | this file |

The fiat decimal `0.341304` is a **6-decimal truncation** of the true
ι_τ = 2/(π+e) = 0.341304238875… (numerical error < 3 × 10⁻⁷).
A formal numerical-bridge theorem
(`TauReal.iota_tau_numerical_bridge`) is the Phase 4 / B1.0b
deliverable in `TauRealIotaTau.lean`.

## Registry Cross-References

- [I.D01]    Master Constant — `iota_tau_numer`, `iota_tau_denom`, `iota_tau_float` (this module, fiat form)
- [I.D-IotaTau-Structural] `TauReal.iota_tau` (TauRealIotaTau.lean, structural form)
- [I.D28]    Boundary Local Ring — legacy finite B/C diagnostic counts,
             `bc_ratio`

## Ground Truth Sources
- chunk_0015_M000074: iota_tau = 2/(pi + e), foundational constant
- iota-tau research paper: `iota_tau` is the crossing-germ balance readout,
  not a prime-density ratio
- prime-polarity research paper: canonical B/C prime polarity is the
  Legendre/Kronecker `(2/p)` classifier

## Mathematical Content

The master constant iota_tau = 2/(pi + e) ~ 0.341304 is the structural
crossing-germ balance readout. It is related to the B/C channel split at the
boundary, but it is **not** the asymptotic ratio of B-dominant to C-dominant
primes.

This module provides:

1. **Rational approximation**: iota_tau ~ 341304/1000000 (6 decimal places)
2. **Legacy B/C diagnostic counts**: count_b / count_c computed at various
   bounds using the older spectral-signature diagnostics
3. **Retired convergence-shape predicates**: archived Prop shapes for old
   experiments; they are not axioms and should not be cited as source truth
   for `iota_tau`

For the **structural** Cauchy-completion form of iota_tau (used by
theorem-cited identities rather than Nat-decidable witnesses), see
`TauLib/BookI/Boundary/TauRealIotaTau.lean`.
-/

namespace Tau.Boundary

open Tau.Denotation Tau.Polarity

-- ============================================================
-- MASTER CONSTANT: RATIONAL APPROXIMATION
-- ============================================================

/-- Numerator of iota_tau rational approximation (6 decimal places).

    See `TauReal.iota_tau` in `TauRealIotaTau.lean` for the structural
    Cauchy-completion form. The numerical-bridge theorem
    `TauReal.iota_tau_numerical_bridge` (Phase 4 / B1.0b) formally
    documents that this fiat decimal is within < 3 × 10⁻⁷ of the
    structural form. -/
def iota_tau_numer : Nat := 341304

/-- Denominator of iota_tau rational approximation. See `iota_tau_numer`
    docstring for the cross-reference to the structural form. -/
def iota_tau_denom : Nat := 1000000

/-- iota_tau denominator is positive. -/
theorem iota_tau_denom_pos : iota_tau_denom > 0 := by
  simp [iota_tau_denom]

/-- Float approximation of iota_tau = 2/(pi + e) ~ 0.341304.
    Since Lean 4 Float does not have a built-in pi constant,
    we use the known decimal approximation. -/
def iota_tau_float : Float := 0.341304

/-- Float approximation from the rational approximation. -/
def iota_tau_rat_float : Float :=
  Float.ofNat iota_tau_numer / Float.ofNat iota_tau_denom

-- ============================================================
-- LEGACY B/C DIAGNOSTIC COUNTS
-- ============================================================

/-- Legacy B/C diagnostic count pair (numerator, denominator).
    Returns `(count_b, count_c)` using the older bound-dependent
    spectral-signature diagnostics. This is not a canonical prime-density
    ratio and does not define `iota_tau`. -/
def bc_ratio_pair (n N : TauIdx) : Nat × Nat :=
  (count_b_dominant n N, count_c_dominant n N)

/-- Legacy B/C diagnostic ratio as a Float. Returns 0.0 if there are no
    C-dominant primes. This diagnostic ratio should not be identified with
    `iota_tau`. -/
def bc_ratio_float (n N : TauIdx) : Float :=
  let (b, c) := bc_ratio_pair n N
  if c = 0 then 0.0
  else Float.ofNat b / Float.ofNat c

/-- Scaled legacy B/C diagnostic ratio:
    `(count_b * 1000000) / count_c`, retained for integer comparison in
    older finite checks. -/
def bc_ratio_scaled (n N : TauIdx) : Nat :=
  let (b, c) := bc_ratio_pair n N
  if c = 0 then 0
  else (b * 1000000) / c

-- ============================================================
-- RETIRED CONVERGENCE-SHAPE PREDICATES
-- ============================================================

/-- Retired convergence-shape predicate for the old diagnostic experiment:
    for all epsilon > 0, there exists N₀ such that for all n ≥ N₀,
    |bc_ratio(n, N) - iota_tau| < epsilon.

    This is not an axiom, not a theorem, and not source truth for `iota_tau`.
    The iota-tau paper withdraws the identification of `iota_tau` with a
    B/C prime-density ratio; `iota_tau` is the crossing-germ balance readout. -/
def ConvergenceClaimFloat (N : TauIdx) : Prop :=
  ∀ (eps : Float), eps > 0.0 →
    ∃ (n0 : Nat), ∀ (n : Nat), n ≥ n0 →
      Float.abs (bc_ratio_float n N - iota_tau_float) < eps

/-- Retired convergence-shape predicate in rational form: for all k
    (precision level),
    there exists n0 such that for n ≥ n0,
    |count_b(n,N) * denom - numer * count_c(n,N)| < count_c(n,N) * (denom / 10^k).
    This is the pure Nat formulation avoiding Float for archived diagnostics;
    it should not be cited as an active convergence claim. -/
def ConvergenceClaimRat (N : TauIdx) (k : Nat) : Prop :=
  ∃ (n0 : Nat), ∀ (n : Nat), n ≥ n0 →
    let (b, c) := bc_ratio_pair n N
    c > 0 ∧
    -- |b * denom - numer * c| < c * (denom / 10^k)
    -- i.e., the ratio b/c is within denom/10^k of numer/denom
    (if b * iota_tau_denom ≥ iota_tau_numer * c
     then b * iota_tau_denom - iota_tau_numer * c < c * (iota_tau_denom / 10 ^ k)
     else iota_tau_numer * c - b * iota_tau_denom < c * (iota_tau_denom / 10 ^ k))

-- ============================================================
-- COMPUTABLE CHECKS
-- ============================================================

/-- Check that both B and C counts are positive at bound n, N. -/
def both_channels_active (n N : TauIdx) : Bool :=
  let (b, c) := bc_ratio_pair n N
  b > 0 && c > 0

/-- Legacy diagnostic check that B-count < C-count at the chosen finite
    bounds. This is not justified by `iota_tau` and has no canonical
    density meaning. -/
def b_minority_check (n N : TauIdx) : Bool :=
  let (b, c) := bc_ratio_pair n N
  b < c

-- ============================================================
-- ARCHIVED SMOKE-TEST RECIPES
-- ============================================================

/-!
The old finite diagnostic checks below used to run during every build. They
are intentionally kept as archived recipes rather than compiled `#eval` /
`native_decide` obligations: this module is retained for compatibility with
legacy callsites, while source truth for `iota_tau` now lives in the structural
crossing-germ modules.

Example interactive checks, if a future audit needs them:

```lean
#eval iota_tau_float
#eval iota_tau_rat_float
#eval bc_ratio_pair 50 1000
#eval bc_ratio_pair 100 1000
#eval bc_ratio_float 50 1000
#eval bc_ratio_float 100 1000
#eval bc_ratio_scaled 50 1000
#eval bc_ratio_scaled 100 1000
#eval both_channels_active 50 1000
#eval b_minority_check 100 1000
```
-/

end Tau.Boundary
