# Phase 0.5 — V.T-LRD-1 Analytic Primitives Design Doc

**Author:** Specialist I (TauReal infrastructure architect, Wave R7 V.T-LRD-1 sprint).
**Status:** Design only; implementation by 1-2 engineers post-Wave R7.
**Estimated effort:** 4-5 weeks (2 engineers in parallel) or 7-9 weeks (1 engineer).

---

## 1. Phase 0 status verification

Specialist I's first task in Wave R7 was to verify what TauReal infrastructure is actually present in TauLib (the v1 derivation note made overly pessimistic assumptions). All 10 listed modules were inspected; here is the verified state:

### Confirmed-present (Phase 0 complete; not skeleton-status)

| Primitive | Module | Lines | Notes |
|-----------|--------|------:|-------|
| `TauReal` (Cauchy completion) | `ConstructiveReals.lean` | :136 (struct), :199 (`equiv`), :178 (`IsCauchy`) | Full ring-axiom layer at :282-357. Single-relation Cauchy-equiv discipline (per `taulib_design_single_relation_kernel` user memory) honoured — pointwise pre-Wave-2a witnesses route through `equiv_of_pointwise` at :215. |
| `TauReal.inv`, `TauReal.div` | `TauRealInv.lean` | :112 (`inv`), :117 (`div`) | Total with safe fallback. `BoundedAwayFromZero` at :68. Cancellation lemma `mul_inv_cancel` at :132. |
| `TauReal.pi` | `TauRealPi.lean` | :93 (def), :271 (Cauchy) | Leibniz pairs $\pi = 8\sum 1/((4k+1)(4k+3))$. Modulus $k+3$ explicit. |
| `TauReal.e` | `TauRealE.lean` | :69 (def), :178 (Cauchy) | Factorial series $\sum 1/n!$. Same modulus shape. |
| `TauReal.abs` | `TauRealAbs.lean` | :50 | Pointwise `TauRat.abs`. Equiv-preservation, IsCauchy-preservation, triangle inequality. |
| `TauReal.lt`, `TauReal.le` | `TauRealOrder.lean` | :80, :105, :349, :351 (instances) | Constructive Bishop-style. Transitivity, asymmetry, equiv-preservation. |
| `TauReal.fromNat`, `fromTauRat` | `ConstructiveReals.lean` | :163, :166 | Embedding from `Nat` and `TauRat`. |
| `TauReal.iota_tau` | `TauRealIotaTau.lean` | :98 (def), :118 (defining identity) | $\iota_\tau = 2/(\pi+e)$. The defining identity $\iota_\tau \cdot (\pi+e) \equiv 2$ is proved at the Cauchy level. |
| `TauRealAnalyticalHelpers.lean` | full helper module | (many) | Factorial bound, geometric/linear cross-over, the workhorse $4/2^n < 1/(k+1)$ for $k+3 \le n$. |
| `TauRealSum.lean` | full sum module | (many) | `factorial`, `sum`, `sumFromTo`, telescoping, ranged-sum triangle inequality. |
| `TauRealPiPlusE.lean`, `TauRealMulCongr.lean` | downstream helpers | | Bridge modules; healthy. |

**Important corollary:** the `ROADMAP-3-HINGES.md §2.4` Phase 0 audit is **stale**. It lists `TauReal.inv`, `div`, `lt`, `le`, `abs`, `pi`, `exp 1` all as "missing"; they are now **all present** (Waves 2-4 landed during the brief window between the LRD note v1 derivation and Wave R7). The roadmap should be updated accordingly. The v1 derivation note's pessimistic 4-7 month estimate (line 152) is calibrated against the stale roadmap and **revises downward to 4-5 weeks** (Phase 0.5 only, 2 engineers in parallel).

**No R3 risk-flag triggers.**

### Confirmed-missing (Phase 0.5 targets)

| Primitive | Function-form? | Critical for V.T-LRD-1? | Priority |
|-----------|---------------|--------------------------|----------|
| `TauReal.sqrt` | yes | **CRITICAL-PATH** for $J_{\max}^{T^2} = \iota_\tau\sqrt{\kappa_D}\,GM^2/c$ | 1 |
| `TauReal.log` (or `log10`) | yes | for $|d\log N/d\log M_{\rm BH}|$ slope bounds | 3 |
| `TauReal.exp` | function-form (vs the constant `TauReal.e`) | for `log_inv` headline; range-reduction in `log` | 2 |

---

## 2. Phase 0.5 design: `TauRealSqrt.lean`

**Mission:** Provide `TauReal.sqrt` for radicands bounded away from zero, via Newton iteration as the Cauchy approximant.

**Approach.** For radicand $a > 0$, define a TauRat-valued sequence by
$$x_0 := a.\text{approx } n \text{ (or }\text{TauRat.one}\text{ as fallback)}, \qquad x_{k+1} := \tfrac{1}{2}\bigl(x_k + a/x_k\bigr).$$
Newton's method on $f(x) = x^2 - a$ converges quadratically — error $O(1/2^{2^n})$ after $n$ iterations.

**Sketch:**
```lean
import TauLib.BookI.Boundary.TauRealInv
import TauLib.BookI.Boundary.TauRealAnalyticalHelpers

namespace Tau.Boundary
open Tau.Denotation

/-- One Newton step for sqrt(a): x ↦ (x + a/x)/2.
    Uses TauRat.inv with apartness witness; falls back to one. -/
def TauRat.sqrtNewtonStep (a : TauRat) (x : TauRat) : TauRat :=
  if h : x.is_nonzero then
    ((x.add (a.mul (TauRat.inv x h))).mul half_taurat)
  else TauRat.one
  where half_taurat : TauRat := ⟨⟨1, 0⟩, 2, by norm_num⟩

/-- Iterate Newton n times from a seed. -/
def TauRat.sqrtIter (a : TauRat) (seed : TauRat) : Nat → TauRat
  | 0     => seed
  | n + 1 => TauRat.sqrtNewtonStep a (TauRat.sqrtIter a seed n)

/-- The TauReal square root. -/
def TauReal.sqrt (a : TauReal) : TauReal :=
  ⟨fun n => TauRat.sqrtIter (a.approx n) (a.approx n) n⟩
```

**Key Cauchy-bound theorem:**
```lean
theorem TauReal.sqrt_isCauchy (a : TauReal)
    (h_a_cauchy : a.IsCauchy) (h_pos : a.BoundedAwayFromZero) :
    (TauReal.sqrt a).IsCauchy
```
Proof uses (1) the algebraic identity $x_n^2 - a = (x_{n-1}^2 - a)^2 / (2x_{n-1})^2$ — discharged by `ring`; (2) the geometric $1/2^{2^n} < 1/(k+1)$ workhorse via `Rat.four_div_two_pow_lt_recip` (`TauRealAnalyticalHelpers.lean:139`). The `BoundedAwayFromZero` witness gives the lower bound on $x_n$.

**Headline theorems:**
```lean
theorem TauReal.sqrt_sq (a : TauReal) (h : a.BoundedAwayFromZero) :
    TauReal.equiv ((TauReal.sqrt a).mul (TauReal.sqrt a)) a

theorem TauReal.sqrt_pos (a : TauReal) (h : a.BoundedAwayFromZero) :
    (TauReal.sqrt a).BoundedAwayFromZero
```

**Estimate:** 220-280 lines. Dependencies: `TauRealInv.lean`, `TauRealAnalyticalHelpers.lean`. No `TauRealSum.lean` needed.

**Wall-clock at 1 engineer:** 2-3 weeks.

---

## 3. Phase 0.5 design: `TauRealExp.lean`

**Mission:** Provide `TauReal.exp` as a function (not just the constant `e`).

**Approach.** Series expansion $\exp(x) = \sum_{k \ge 0} x^k / k!$ — the smoothest extension of `TauRealE.lean`'s factorial-series infrastructure. `TauReal.e` already proves the $x = 1$ case is Cauchy with modulus $k + 3$; the general-$x$ proof is the same proof with $x^n$ replacing $1$ in the numerator.

**Range-reduction strategy:**
- For $|x| \le R = \ln 2 / 2 \approx 0.347$, the series converges fast (modulus ~ k+3 same as `e`).
- For general $x$, write $x = k\ln 2 + r$ with $|r| \le \ln 2 / 2$. Then $\exp(x) = 2^k \cdot \exp(r)$.
- $\ln 2$ is itself a TauReal constant (defined in `TauRealLog.lean` via the fast series $\ln 2 = \sum 1/(2^n \cdot n)$).

**Sketch:**
```lean
import TauLib.BookI.Boundary.TauRealE
import TauLib.BookI.Boundary.TauRealAnalyticalHelpers

namespace Tau.Boundary
open Tau.Denotation

def TauRat.exp_term (x : TauRat) (k : Nat) : TauRat :=
  ⟨⟨x.num.toInt ^ k, 0⟩, x.den ^ k * Nat.factorial k, by positivity⟩

def TauRat.exp_partial (x : TauRat) (n : Nat) : TauRat :=
  TauRat.sum (TauRat.exp_term x) n

def TauReal.exp_bounded (a : TauReal) (R_bound : a.BoundedBy R) : TauReal := ...

def TauReal.exp (a : TauReal) : TauReal := ... -- via range reduction
```

**Headline theorems:**
```lean
theorem TauReal.exp_zero : TauReal.equiv (TauReal.exp TauReal.zero) TauReal.one

theorem TauReal.exp_one : TauReal.equiv (TauReal.exp TauReal.one) TauReal.e

theorem TauReal.exp_add (a b : TauReal) :
    TauReal.equiv (TauReal.exp (a.add b))
                  ((TauReal.exp a).mul (TauReal.exp b))
```

The `exp_add` proof requires Cauchy convolution on partial-sum sequences (`TauRealSum.lean` doesn't currently provide it; plan ~80 lines for the convolution lemma).

**Estimate:** 240-320 lines. Dependencies: `TauRealE.lean` (factorial helpers), `TauRealAnalyticalHelpers.lean`, `TauRealSum.lean`. **No sqrt dependency.**

**Wall-clock at 1 engineer:** 2-3 weeks.

---

## 4. Phase 0.5 design: `TauRealLog.lean`

**Mission:** Provide `TauReal.log` (natural log; `log10` derives by `TauReal.div` against `ln 10`).

**Approach (recommended).** Series expansion $\ln(1+u) = \sum_{n \ge 1} (-u)^n \cdot (-1)/n$ for $|u| < 1$, plus explicit reduction strategy for the rest. Reuses `TauRealSum.lean` directly and parallels `TauRealPi.lean` / `TauRealE.lean` proof shape.

**Range-reduction strategy:**
1. Find $k : \mathbb{N}$ such that $x \in [2^k, 2^{k+1})$ (binary range-reduction; uses repeated halving via `TauReal.div` by 2).
2. Write $x = 2^k \cdot y$ with $y \in [1, 2)$.
3. Then $\ln x = k \cdot \ln 2 + \ln y$ where $y = 1 + u$, $u \in [0, 1)$.
4. Series converges slowly near $u = 1$; further reduction $u \mapsto u/(1+\sqrt{1+u})$ keeps $|u|$ small (uses `TauReal.sqrt`).
5. $\ln 2$ defined via fast series $\ln 2 = \sum_{n \ge 1} 1/(2^n \cdot n)$.

**Sketch:**
```lean
import TauLib.BookI.Boundary.TauRealSum
import TauLib.BookI.Boundary.TauRealSqrt   -- for further range reduction
import TauLib.BookI.Boundary.TauRealExp    -- for log_inv headline
import TauLib.BookI.Boundary.TauRealAnalyticalHelpers

namespace Tau.Boundary
open Tau.Denotation

def TauRat.ln_one_plus_u_term (u : TauRat) (k : Nat) : TauRat := ...
def TauRat.ln_one_plus_u_partial (u : TauRat) (n : Nat) : TauRat := ...
def TauReal.ln_two : TauReal := ...
def TauReal.log (a : TauReal) : TauReal := ...
```

**Headline theorems:**
```lean
theorem TauReal.log_inv : ∀ a : TauReal, a.BoundedAwayFromZero →
    TauReal.equiv (TauReal.exp (TauReal.log a)) a

theorem TauReal.log_mul : ∀ a b : TauReal,
    a.BoundedAwayFromZero → b.BoundedAwayFromZero →
    TauReal.equiv (TauReal.log (a.mul b)) ((TauReal.log a).add (TauReal.log b))
```

**Estimate:** 380-450 lines (largest of the three; range-reduction bookkeeping dominates). Dependencies: `TauRealSum.lean`, `TauRealSqrt.lean`, `TauRealExp.lean`, `TauRealAnalyticalHelpers.lean`.

**Wall-clock at 1 engineer:** 3-4 weeks.

**For V.T-LRD-1 specifically**, only the **slope evaluation** $|d\log N/d\log M|$ needs `log` — and this is a *bound check* not a precise numerical identity, so we can stay with TauRat approximants of the log values without invoking the full `log_inv` theorem.

---

## 5. Dependency graph + total effort

```
TauRealSum.lean ─┬─→ TauRealE.lean ──→ TauRealExp.lean ─┐
                 │                                       ├─→ TauRealLog.lean
TauRealInv.lean ─┴─→ TauRealSqrt.lean ──────────────────┘
        │
TauRealAnalyticalHelpers.lean ──→ (all three new modules)
```

**Order of execution:**
1. **TauRealSqrt.lean** first — independent of Exp/Log, unblocks the immediate $\sqrt{\kappa_D}$ need in $J_{\max}^{T^2} = \iota_\tau\sqrt{\kappa_D}\,GM^2/c$ (V.T-LRD-1 sub-claim B).
2. **TauRealExp.lean** in parallel with Sqrt — independent of Sqrt; the heavy lift is the convolution lemma.
3. **TauRealLog.lean** last — needs Exp (for `log_inv`) and Sqrt (for range reduction near $u \to 1$).

**Totals.** 220-280 + 240-320 + 380-450 = **840-1050 Lean lines across 3 modules**. Plus an estimated 50-80 lines of registry entries and ~30-line bridge to `TauRealIotaTau.lean` for the $\sqrt{\kappa_D}$ formulation.

**Wall-clock at 1 engineer:** 7-9 weeks (Sqrt 2-3w, Exp 2-3w, Log 3-4w).

**With 2 engineers in parallel:** 4-5 weeks. (Engineer A: Sqrt → Log range-reduction. Engineer B: Exp → `exp_add` convolution. Sync on Log's `log_inv` headline once both have landed.)

---

## 6. Promotable-now sub-lemmas in `HeavySeedBirth.lean`

The following can be promoted from `Nat`-scaled to TauReal-witnessed **immediately**, using only Phase-0-confirmed primitives (no sqrt/log/exp needed). **Wave R7 chair landed all four** in commit-pending state:

**T1 (Wave R7 LANDED).** `iota_tau_x_1000000` rebinding (HeavySeedBirth.lean:161-169) extended with `iota_tau_TauReal := Tau.Boundary.TauReal.iota_tau` (line 172) plus the defining-identity theorem `iota_tau_TauReal_defining` (line 188) inheriting `Tau.Boundary.TauReal.iota_tau_mul_pi_plus_e_eq_two`.

**T3 (Wave R7 LANDED).** `DCBHCollapseFraction.f_dcbh_x10000 := 100` extended with `dcbh_fraction_TauReal := TauReal.fromTauRat ⟨⟨1, 0⟩, 100, ...⟩` alongside.

**T4 (Wave R7 LANDED).** `AtomicCoolingHaloFloor.m_halo_min_e7_x10 := 32` extended with `atomic_cooling_floor_z10_mass_TauReal := TauReal.fromTauRat ⟨⟨32, 0⟩, 1, ...⟩` alongside.

**Partial T2 (Wave R7 LANDED).** `T2HorizonAngularMomentumBound.iota_tau_x_1000000 := 341304` extended with `iota_tau_T2_bound_TauReal := iota_tau_TauReal` alongside. The `f_iota_x_10000 := 2773` (= $\iota_\tau\sqrt{\kappa_D}$) **deferred** until Phase 0.5 `TauRealSqrt` lands; once it does, the headline witness becomes:
```lean
def f_iota_TauReal : Tau.Boundary.TauReal :=
  iota_tau_TauReal.mul
    (Tau.Boundary.TauReal.sqrt
      (Tau.Boundary.TauReal.one.sub iota_tau_TauReal))
```

**T5 (DEFERRED).** `SpinParameterLogUniform.log_lambda_min_abs_x100 := 250` is itself a log value (|log λ_min| = 2.5). Promoting requires `TauReal.log` — defer to Phase 0.5 + later wave.

**T6 (NO PROMOTION NEEDED).** `is_orthodox_imported`, `is_tau_distinctive` Boolean fields are scope-discipline tags, not numerical content. Stay as `Bool`.

---

## 7. Build verification (Wave R7 status)

Both modules compile cleanly with the Wave R7 patches:

```bash
cd ~/Panta-Rhei-Research/taulib
lake build TauLib.BookV.Cosmology.HeavySeedBirth TauLib.BookV.Cosmology.FalsificationPack
# Build completed successfully (1082 jobs).
```

11 `#eval` smoke tests on HeavySeedBirth confirmed (341304, 32, 100, 250, 316, 32, 15, 30, 20, 80, 150). 5 new `#eval` smoke tests on FalsificationPack confirmed (`structural_count = 4`, `quantitative_count = 7`, `frontier_count = 3`, plus 2 `currently_testable` bools).

**Trust budget impact: zero.** No new custom axioms, no new sorry, no new `native_decide` leaves beyond the structural identities.

---

## 8. Recommendation summary

**Phase 0.5 unblocks the *headline* V.T-LRD-1 sub-theorems** (B's $\sqrt{\kappa_D}$, C's slope bound) but is not on the critical path for v2.2 paper publication — the Lean module's skeleton-status is honest at the docstring + `pred_lrd_*.currently_testable` level.

**Recommended schedule:**
1. **Now (Wave R7 close)**: chair lands the 4 promotable-now patches (DONE), commits the Wave R7 deliverables, surfaces v2.2 paper headline-relaxation to user (R2 trigger).
2. **Next 4-5 weeks (Phase 0.5)**: 2 engineers implement TauRealSqrt + TauRealExp + TauRealLog modules in parallel.
3. **Wave R8 (post-Phase 0.5)**: promote V.D-LRD-1d's $f_{\rm iota}$ field (sqrt-dependent), V.D-LRD-1c's log-lambda fields (log-dependent), upgrade signature 1's KS-test power-analysis bound to TauReal-witnessed.

The "fully-derived V.T-LRD-1 theorem" is therefore on track for **Q4 2026** (post-Phase 0.5 + Wave R8), well within the v2.1 paper's claim of "3-6 months" if calibrated against the corrected Phase 0 status (rather than the stale ROADMAP-3-HINGES audit).
