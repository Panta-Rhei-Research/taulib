import TauLib.BookI.Boundary.ComplexField
import TauLib.BookI.Boundary.TauRealSum
import TauLib.BookI.Boundary.TauRealExp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.FieldSimp

/-!
# TauLib.BookI.Boundary.TauComplexExp

**Wave Γ₇ Phase 3C — the M3 breakthrough: τ-native exp on the
cyclotomic-4 extension `TauComplex = TauReal[X]/(X²+1)`.**

This module is the load-bearing artifact of Wave Γ₇ (May 2026), the
multi-session campaign that established the formal machinery needed to
prove `TauComplex.exp_add : exp(z₁+z₂) ≈ exp(z₁) · exp(z₂)` (the **M3
endpoint**), from which sin/cos addition formulae follow via Euler's
formula `exp(i·x) = cos(x) + i·sin(x)`, and eventually the discharge of
Machin's formula yielding τ-native π formally certified to 50+ digits.

The Taylor series for `exp(z)` on `TauComplex`:
$$ \exp(z) \;=\; \sum_{k=0}^{\infty} \frac{z^k}{k!} . $$

When specialised to purely imaginary arguments `z = i·x` (with the
cyclotomic-4 root `i`), this gives **Euler's formula**:
$$ \exp(i \cdot x) \;=\; \cos(x) + i \cdot \sin(x) . $$

The cyclotomic-4 structure of `i` is what makes this work: powers of `i`
cycle through `{1, i, -1, -i}` with period 4, separating the even-power
real contributions (cos terms) from the odd-power imaginary contributions
(sin terms).

## The M3 trajectory — what this module establishes

The module organizes around the **disciplined-decomposition discipline**
of the τ-canon programme: each sub-result is a focused, sorry-free
addition (~100-200 LOC per commit), composing toward the M3 endpoint
via named-target intermediates.

### Major milestones shipped (UNCONDITIONAL)

| Theorem | Statement |
|---------|-----------|
| `i_unit_pow_4_equiv_one` | The cyclotomic-4 identity `i⁴ ≈ 1` |
| `equiv_add_congr` / `equiv_mul_congr` | Equiv-congruence under add/mul |
| `equiv_pow_congr_strong` | Pow congruence (strengthened with bounds) |
| `mul_BoundedBy_compounds` | Multiplication bound compounding |
| `pow_BoundedBy_compounds` | Power bound compounding |
| `taucomplex_mul_left_comm` | Bound-free ring identity |
| `taucomplex_add_left_comm` | Bound-free add identity |
| `taucomplex_mul_reassoc_right` | Triple-product reassociation (bounded) |
| `pascal_combine_discharge` | The Pascal combinatorial step |
| `right_sum_reindex_discharge` | The right-sum reindex bridge |
| `pascal_LHS_form_bridge_discharge` | Nat-arith bridge `(n+1)-(j+1) = n-j` |
| **`add_pow_equiv_strong`** | **🎯 BINOMIAL THEOREM** (LEFT-assoc form) |
| **`add_pow_equiv_target_strong`** | **🎯 BINOMIAL THEOREM** (named-target form) |
| `scale_by_inv_factorial` infra | Foundation for `exp_term_add_eq_cauchyDiag` |

### Named targets — 6 of 10 unconditionally discharged

The **named-target + later-discharge pattern** (atlas insight:
`named-target-discharge-pattern.md`) was applied 10 times in this
campaign:

| # | Target | Status |
|---|--------|--------|
| 1 | `BBPLeibnizCorrespondence` | queued (Wave Γ₆) |
| 2 | `exp_partial_add_eq_cauchyPStar_target` | queued |
| 3 | `exp_term_add_eq_cauchyDiag_target` | queued (next sprint) |
| 4 | `add_pow_equiv_target` | ✓ strengthened discharge |
| 5 | `equiv_pow_congr_target` | partially (strong form) |
| 6 | `mul_BoundedBy_compounds_target` | ✓ unconditional |
| 7 | `pow_BoundedBy_compounds_target` | ✓ unconditional |
| 8 | `pascal_combine_target` | ✓ unconditional |
| 9 | `right_sum_reindex_target` | ✓ unconditional |
| 10 | `pascal_LHS_form_bridge_target` | ✓ unconditional |

## Module organization (parts 1-32)

The file is organized into 32 numbered sections, each shipped as a
focused commit per the disciplined-decomposition pattern:

* **Parts 1-2**: `TauComplex.pow` + cyclotomic-4 identity `i⁴ ≈ 1`.
* **Parts 3-7**: factorial scaling + `exp_term`, `exp_partial`,
  `cauchyDiag`, `cauchyPStar` definitions.
* **Part 8**: named targets `exp_term_add_eq_cauchyDiag_target` and
  `exp_partial_add_eq_cauchyPStar_target` + the conditional
  `_under_term_hyp` theorem.
* **Parts 9-11**: equiv-congruence lemmas (add, mul, negate, sub).
* **Part 12**: `BoundedBy` predicate + named-target propositions for
  bound compounding.
* **Parts 13-14**: left-identity equivs + binomial base case.
* **Parts 15-17**: sum-mul distributivity + bound compounding
  discharges + helper extraction.
* **Parts 18-19**: pow bound + equiv_pow_congr_strong + binomial
  helpers (`mul_left_comm`, `sum_equiv_congr`, `sum_add_split`,
  `sum_split_first`).
* **Parts 20-21**: term identities + `B_left` left-assoc form +
  `B_left·(z₁+z₂) ≈ Σ_left + Σ_right`.
* **Parts 22-25**: Pascal preliminaries (`fromTauReal_fromNat_add`,
  `fromTauReal_fromNat_zero`) + Pascal term + sum decomposition +
  first-term simplification + B_left split bridge helpers.
* **Parts 26-28**: Σ_right reindex sub-lemmas + composing bridge +
  `@[reducible]` defs (`binomial_right_sum`, `binomial_right_shifted`,
  `binomial_left_sum`, `binomial_sigma_left`).
* **Part 29**: `pascal_combine_target` named target + binomial-left defs.
* **Part 30**: Recursive named target `right_sum_reindex_target` +
  `add_left_comm` + `pascal_LHS_form_bridge_target` and discharge +
  **`pascal_combine_target_under_right_reindex_hyp`** (conditional
  pascal combine, 7-step chain).
* **Part 31**: 🎯🎯🎯 **THE BINOMIAL THEOREM ON TauComplex** —
  unconditional discharges of `right_sum_reindex`,
  `pascal_combine`, and **`add_pow_equiv_strong`** (M3 stepping
  stone) via the `simp only [rfl-facts]` breakthrough.
* **Part 32**: `TauComplex.scale_by_inv_factorial` infrastructure for
  the upcoming `exp_term_add_eq_cauchyDiag` discharge.

## Key structural insights from this campaign

Four atlas insights were authored or extended during this work:

* **`cauchy-bound-template-pattern`** — the 5-step Cauchy-bound proof
  template (validated 5 times across the τ-canon programme).
* **`deep-research-redteam-pattern`** — multi-agent recon sprints
  before structurally-subtle implementation (validated 2 times this
  wave, saving ~6-10 sessions of misaligned work).
* **`named-target-discharge-pattern`** — ship a `Prop` as a named
  target when proof depth exceeds commit scope; discharge in a
  focused later session. 10 targets shipped, 6 unconditionally
  discharged this wave alone.
* **`whnf-elaboration-cost-defer-pattern`** — Lean operational
  pattern for handling expression-tree depth × signature-arity cliffs.
  5 strategies validated including the breakthrough `simp only
  [rfl-facts]` technique that cracked the binomial theorem's
  rfl-cliff at Part 31.

## Why this module is M3-ready

The mathematical content of the binomial theorem on TauComplex is
**structurally complete**:
* `add_pow_equiv_strong` provides `pow (z₁+z₂) n ≈ binomial_left_sum`.
* `add_pow_equiv_target_strong` bridges to the named-target form.
* The bound-tracking machinery (`BoundedBy`, `add_BoundedBy_compounds`,
  `mul_BoundedBy_compounds`, `pow_BoundedBy_compounds`) is in place.
* The cauchyPStar machinery + `under_term_hyp` conditional theorem
  links the per-term identity (queued discharge) to the partial-sum
  identity needed for M3.

What remains for M3 is **mechanical Cauchy-product work**:
1. Discharge `exp_term_add_eq_cauchyDiag_target` via binomial theorem
   + factorial arithmetic (`scale_by_inv_factorial` infrastructure
   shipped Part 32).
2. Discharge `exp_partial_add_eq_cauchyPStar_target` trivially via
   the `under_term_hyp` conditional.
3. Cauchy-product bound at TauComplex (Cauchy-bound-template
   instantiation).
4. `TauComplex.exp` + `IsCauchy` (mechanical).
5. **`TauComplex.exp_add` — M3 ENDPOINT**.

Then sin/cos addition formulae via cyclotomic-4 specialization, and
finally Machin's formula → τ-native π → ι_τ formal certification to
50+ digits.

## Build state

* `sorry` count: 0 (BookI/Boundary remains sorry-free throughout
  Wave Γ₇).
* `axiom` count: 3 (unchanged from pre-campaign baseline; all in
  BookIII Bridge/GRH/Spectral).
* LOC: ~3230.
* Imports: `ComplexField` (TauComplex types + ring axioms),
  `TauRealSum` (cauchy product at TauRat level), `TauRealExp`
  (TauReal.exp + IsCauchy), Mathlib tactic-only imports.

## Cross-references to the τ-canon corpus

* `BookI.Boundary.ComplexField` — `TauComplex` as the cyclotomic-4
  adjunction `TauReal[X]/(X²+1)` (manuscript ch77).
* `BookI.Boundary.TauRealExp` — Wave 3b's `TauReal.exp_add` (the
  TauReal-level template this M3 work lifts to TauComplex).
* `BookI.Boundary.TauRealSin` / `TauRealCos` — Wave Γ₇ Phase 3A/3B
  τ-native sin and cos Taylor series (consumers of the upcoming M3
  + cyclotomic specialization).
* `BookI.Boundary.TauRealArctan` — Wave Γ₇ Phase 1A's arctan + Strategy
  G numerical certificate (consumer of upcoming Machin formula proof).
* `BookIV.Sectors.WilsonProjection` — 50-digit `iotaTau`
  (`ι_τ = 2/(π+e)`) currently hard-coded; M3 + Machin formal proof
  will replace the hard-coded value with a formally-verified one.
-/

set_option autoImplicit false

namespace Tau.Boundary

open Tau.Denotation

-- ============================================================
-- PART 1: TauComplex.pow VIA ITERATED MULTIPLICATION
-- ============================================================

/-- **[I.D-TauComplex-Pow]** TauComplex iterated power: `z^k` by
    repeated `TauComplex.mul`. -/
def TauComplex.pow (z : TauComplex) : Nat → TauComplex
  | 0 => TauComplex.one
  | k + 1 => (TauComplex.pow z k).mul z

@[simp] theorem TauComplex.pow_zero (z : TauComplex) :
    TauComplex.pow z 0 = TauComplex.one := rfl

@[simp] theorem TauComplex.pow_succ (z : TauComplex) (k : Nat) :
    TauComplex.pow z (k + 1) = (TauComplex.pow z k).mul z := rfl

theorem TauComplex.pow_one (z : TauComplex) :
    TauComplex.pow z 1 = TauComplex.one.mul z := rfl

-- ============================================================
-- PART 2: COMPUTING SPECIFIC POWERS OF i (the cyclotomic-4 root)
-- ============================================================

/-- **The cyclotomic-4 identity** `i⁴ ≈ 1` at TauComplex.equiv level.

    This is THE defining relation of the cyclotomic-4 group `μ_4 ⊂ ℂ`
    and the structural confirmation that `TauComplex` correctly
    realises `TauReal[X]/(X²+1) ⊃ μ_4`.

    Proof: pointwise TauRat reduction. After unfolding to the TauRat
    level, `(0+1i)^4 = 1+0i` reduces to an Int identity that `ring`
    closes via `equiv_iff_toInt_eq`. -/
theorem TauComplex.i_unit_pow_4_equiv_one :
    (TauComplex.pow TauComplex.i_unit 4).equiv TauComplex.one := by
  refine ⟨?_, ?_⟩
  · -- Real part: equiv to TauReal.one.
    apply TauReal.equiv_of_pointwise
    intro n
    simp only [TauComplex.pow, TauComplex.mul, TauComplex.i_unit, TauComplex.one,
               TauReal.sub, TauReal.add, TauReal.mul, TauReal.negate, TauReal.zero, TauReal.one]
    simp only [TauRat.equiv, TauRat.add, TauRat.mul, TauRat.negate, TauRat.zero, TauRat.one]
    try rw [equiv_iff_toInt_eq]
    try simp only [toInt_add, toInt_mul, toInt_negate, toInt_fromNat, toInt_zero, toInt_one]
    try push_cast
    try ring
  · -- Imaginary part: equiv to TauReal.zero.
    apply TauReal.equiv_of_pointwise
    intro n
    simp only [TauComplex.pow, TauComplex.mul, TauComplex.i_unit, TauComplex.one,
               TauReal.sub, TauReal.add, TauReal.mul, TauReal.negate, TauReal.zero, TauReal.one]
    simp only [TauRat.equiv, TauRat.add, TauRat.mul, TauRat.negate, TauRat.zero, TauRat.one]
    try rw [equiv_iff_toInt_eq]
    try simp only [toInt_add, toInt_mul, toInt_negate, toInt_fromNat, toInt_zero, toInt_one]
    try push_cast
    try ring

/-- **`i^3 ≈ -i`** — the third power, completing the cyclotomic-4 cycle:
    `{i^0 = 1, i^1 = i, i^2 = -1, i^3 = -i, i^4 = 1, ...}`. -/
theorem TauComplex.i_unit_pow_3_equiv_neg_i :
    (TauComplex.pow TauComplex.i_unit 3).equiv (TauComplex.negate TauComplex.i_unit) := by
  refine ⟨?_, ?_⟩
  · apply TauReal.equiv_of_pointwise
    intro n
    simp only [TauComplex.pow, TauComplex.mul, TauComplex.i_unit, TauComplex.negate, TauComplex.one,
               TauReal.sub, TauReal.add, TauReal.mul, TauReal.negate, TauReal.zero, TauReal.one]
    simp only [TauRat.equiv, TauRat.add, TauRat.mul, TauRat.negate, TauRat.zero, TauRat.one]
    try rw [equiv_iff_toInt_eq]
    try simp only [toInt_add, toInt_mul, toInt_negate, toInt_fromNat, toInt_zero, toInt_one]
    try push_cast
    try ring
  · apply TauReal.equiv_of_pointwise
    intro n
    simp only [TauComplex.pow, TauComplex.mul, TauComplex.i_unit, TauComplex.negate, TauComplex.one,
               TauReal.sub, TauReal.add, TauReal.mul, TauReal.negate, TauReal.zero, TauReal.one]
    simp only [TauRat.equiv, TauRat.add, TauRat.mul, TauRat.negate, TauRat.zero, TauRat.one]
    try rw [equiv_iff_toInt_eq]
    try simp only [toInt_add, toInt_mul, toInt_negate, toInt_fromNat, toInt_zero, toInt_one]
    try push_cast
    try ring

-- ============================================================
-- PART 3: SCALE-BY-INVERSE-FACTORIAL HELPER (TauRat level)
-- ============================================================

/-- **TauRat-level scale-by-inverse-factorial**: divide a TauRat by `k!`
    by multiplying its denominator by `k.factorial`. This is the
    structural primitive needed for the Taylor series `z^k / k!`. -/
def TauRat.scale_by_inv_factorial (q : TauRat) (k : Nat) : TauRat :=
  { num    := q.num,
    den    := q.den * k.factorial,
    den_pos := Nat.mul_pos q.den_pos (Nat.factorial_pos k) }

/-- Bridge theorem: `scale_by_inv_factorial q k` toRat is `q.toRat / k!`. -/
theorem TauRat.scale_by_inv_factorial_toRat (q : TauRat) (k : Nat) :
    (TauRat.scale_by_inv_factorial q k).toRat = q.toRat / (k.factorial : Rat) := by
  unfold TauRat.scale_by_inv_factorial TauRat.toRat
  have h_fac_pos : (0 : Rat) < (k.factorial : Rat) := by
    have := Nat.factorial_pos k; exact_mod_cast this
  push_cast
  field_simp

-- ============================================================
-- PART 4: TauReal.scale_by_inv_factorial (lifted to TauReal)
-- ============================================================

/-- **TauReal-level scale-by-inverse-factorial**: pointwise lift of
    `TauRat.scale_by_inv_factorial`. -/
def TauReal.scale_by_inv_factorial (x : TauReal) (k : Nat) : TauReal :=
  ⟨fun n => TauRat.scale_by_inv_factorial (x.approx n) k⟩

@[simp] theorem TauReal.scale_by_inv_factorial_approx (x : TauReal) (k n : Nat) :
    (TauReal.scale_by_inv_factorial x k).approx n =
      TauRat.scale_by_inv_factorial (x.approx n) k := rfl

-- ============================================================
-- PART 5: TauComplex.exp_term (the k-th Taylor term)
-- ============================================================

/-- **[I.D-TauComplex-ExpTerm]** The k-th Taylor term of `exp(z)`:
    `z^k / k!` as a TauComplex.

    Componentwise: divide both real and imaginary parts of `pow z k`
    by `k!` (via `TauReal.scale_by_inv_factorial`).

    The cyclotomic-4 structure of `i` (proved in Part 2 via
    `i_unit_pow_4_equiv_one`) means that for `z = i·x` (purely imaginary),
    the powers `i^k` cycle through `{1, i, -1, -i}` with period 4, giving
    Euler's formula `exp(i·x) = cos(x) + i·sin(x)` via separation into
    even-power (cos) and odd-power (sin) contributions. -/
def TauComplex.exp_term (z : TauComplex) (k : Nat) : TauComplex :=
  ⟨TauReal.scale_by_inv_factorial (TauComplex.pow z k).re k,
   TauReal.scale_by_inv_factorial (TauComplex.pow z k).im k⟩

@[simp] theorem TauComplex.exp_term_re (z : TauComplex) (k : Nat) :
    (TauComplex.exp_term z k).re =
      TauReal.scale_by_inv_factorial (TauComplex.pow z k).re k := rfl

@[simp] theorem TauComplex.exp_term_im (z : TauComplex) (k : Nat) :
    (TauComplex.exp_term z k).im =
      TauReal.scale_by_inv_factorial (TauComplex.pow z k).im k := rfl

-- ============================================================
-- PART 6: TauComplex.exp_partial (the partial-sum sequence)
-- ============================================================

/-- TauComplex sum: direct Nat-recursion summation. -/
def TauComplex.sum (f : Nat → TauComplex) : Nat → TauComplex
  | 0 => TauComplex.zero
  | n + 1 => (TauComplex.sum f n).add (f n)

@[simp] theorem TauComplex.sum_zero (f : Nat → TauComplex) :
    TauComplex.sum f 0 = TauComplex.zero := rfl

@[simp] theorem TauComplex.sum_succ (f : Nat → TauComplex) (n : Nat) :
    TauComplex.sum f (n + 1) = (TauComplex.sum f n).add (f n) := rfl

/-- **[I.D-TauComplex-ExpPartial]** Partial sum of the exp Taylor series
    at depth `n`:
    `exp_partial z n = Σ_{k=0}^{n-1} z^k / k!`. -/
def TauComplex.exp_partial (z : TauComplex) (n : Nat) : TauComplex :=
  TauComplex.sum (TauComplex.exp_term z) n

@[simp] theorem TauComplex.exp_partial_zero (z : TauComplex) :
    TauComplex.exp_partial z 0 = TauComplex.zero := rfl

@[simp] theorem TauComplex.exp_partial_succ (z : TauComplex) (n : Nat) :
    TauComplex.exp_partial z (n + 1) =
      (TauComplex.exp_partial z n).add (TauComplex.exp_term z n) := rfl

-- ============================================================
-- PART 7: TauComplex Cauchy-product infrastructure (Phase 3C Part 3a)
-- ============================================================

/-- **[I.D-TauComplex-CauchyDiag]** The n-th diagonal of the Cauchy
    product of TauComplex sequences:
    `cauchyDiag a b n = Σ_{i=0}^{n} a(i) · b(n - i)` (TauComplex.mul). -/
def TauComplex.cauchyDiag (a b : Nat → TauComplex) (n : Nat) : TauComplex :=
  TauComplex.sum (fun i => (a i).mul (b (n - i))) (n + 1)

/-- **[I.D-TauComplex-CauchyPStar]** Partial Cauchy product:
    `cauchyPStar a b N = Σ_{k=0}^{N-1} cauchyDiag a b k`.

    This is the τ-native Cauchy-product machinery on TauComplex,
    parallel to `TauRat.cauchyPStar` from `TauRealSum.lean`. The M3
    breakthrough (Phase 3C Part 3b-3e) will use this to express the
    binomial identity `exp_partial(z₁+z₂) ≈ cauchyPStar (exp_term z₁) (exp_term z₂)`
    and lift the `cauchy_product_bound` tail estimate. -/
def TauComplex.cauchyPStar (a b : Nat → TauComplex) (N : Nat) : TauComplex :=
  TauComplex.sum (TauComplex.cauchyDiag a b) N

@[simp] theorem TauComplex.cauchyPStar_zero (a b : Nat → TauComplex) :
    TauComplex.cauchyPStar a b 0 = TauComplex.zero := rfl

@[simp] theorem TauComplex.cauchyPStar_succ (a b : Nat → TauComplex) (n : Nat) :
    TauComplex.cauchyPStar a b (n + 1) =
      (TauComplex.cauchyPStar a b n).add (TauComplex.cauchyDiag a b n) := rfl

/-- `cauchyDiag a b 0 = sum_{i=0}^{0} a(i)·b(0-i) = TauComplex.zero.add ((a 0).mul (b 0))`,
    structural unfolding. The equiv-level identity `cauchyDiag_zero_equiv`
    saying this is equiv to `(a 0).mul (b 0)` follows via `taucomplex_zero_add`
    at the TauReal level (queued for Part 3b). -/
theorem TauComplex.cauchyDiag_zero (a b : Nat → TauComplex) :
    TauComplex.cauchyDiag a b 0 =
      TauComplex.zero.add ((a 0).mul (b 0)) := rfl

-- ============================================================
-- PART 8: M3 TARGETS (statements only — proofs queued for Part 3b-3e)
-- ============================================================

/-! ## Phase 3C Part 3b-3e roadmap — the M3 breakthrough

With `TauComplex.cauchyPStar` defined, the M3 breakthrough decomposes
into four focused sub-deliverables, paralleling the `TauReal.exp_add`
proof structure (Wave 3b R10 in `TauRealExp.lean`):

### Phase 3C Part 3b — The binomial identity at TauComplex level

**Target**: `TauComplex.exp_partial_add_eq_cauchyPStar`:

```
(TauComplex.exp_partial (z₁.add z₂) n).equiv
  (TauComplex.cauchyPStar (TauComplex.exp_term z₁) (TauComplex.exp_term z₂) n)
```

**Proof strategy**: pointwise reduction via `TauReal.equiv_of_pointwise`,
then expanding both sides componentwise. The key arithmetic identity
at each component is the binomial theorem applied to `(z₁ + z₂)^n` in
TauComplex arithmetic.

The TauRat-level analog `exp_partial_add_toRat_eq_cauchyPStar` (in
`TauRealExp.lean`, ~30 LOC) does this for reals. The TauComplex version
adds a layer of complex-multiplication distributivity but follows the
same combinatorial structure.

**Estimated LOC**: ~150-200.

### Phase 3C Part 3c — The Cauchy-product bound at TauComplex level

**Target**: a TauComplex analog of `TauRat.cauchy_product_bound`:

```
|exp_partial(z₁) · exp_partial(z₂) - cauchyPStar(exp_term z₁, exp_term z₂, n)|
  ≤ n · C² / 2^(n-1)
```

(at TauComplex.equiv level, with `C` a per-term bound).

**Proof strategy**: lift the existing `TauRat.cauchy_product_bound`
(~200 LOC in `TauRealSum.lean`) to TauComplex componentwise. Each of
the real and imaginary components is a sum of 4 TauRat-level Cauchy
products with appropriate signs:

  (a·b).re = a.re·b.re - a.im·b.im
  (a·b).im = a.re·b.im + a.im·b.re

The TauComplex bound is at most `2x` the TauRat bound (from triangle
inequality on the 2-term sums).

**Estimated LOC**: ~250-300.

### Phase 3C Part 3d — Full TauComplex.exp

**Target**: define `TauComplex.exp : TauComplex → TauComplex` via the
diagonal construction (parallel to `TauReal.exp`):

```
def TauComplex.exp (z : TauComplex) : TauComplex :=
  -- n-th approximation: exp_partial at the n-th approximation of z, depth n
  ⟨..., ...⟩
```

Plus its `IsCauchy` property for bounded arguments.

**Estimated LOC**: ~100-150.

### Phase 3C Part 3e — TauComplex.exp_add (the M3 target)

**Target**: the M3 breakthrough proper:

```
theorem TauComplex.exp_add (a b : TauComplex) (R : Rat)
    (hR0 : 0 ≤ R) (hR1 : R ≤ 1) (ha : TauComplex.BoundedBy a R)
    (hb : TauComplex.BoundedBy b R) :
    TauComplex.equiv
      (TauComplex.exp (a.add b))
      ((TauComplex.exp a).mul (TauComplex.exp b))
```

**Proof strategy**: directly mirror `TauReal.exp_add`:
1. Use Part 3b's binomial identity to rewrite LHS as `cauchyPStar`.
2. Use Part 3c's Cauchy-product bound to estimate the difference
   `cauchyPStar - exp_partial · exp_partial`.
3. Modulus `λ k => 2k + 6` (or similar) via the chain
   `n · C² / 2^(n-1) < 1/(k+1)`.

**Estimated LOC**: ~100.

### Phase 3C Part 4 — sin/cos addition formula extraction

Once Part 3e lands, specialise `TauComplex.exp_add` to purely imaginary
arguments `z₁ = i·α, z₂ = i·β` and extract real/imag parts via
`TauComplex.equiv`. The cyclotomic-4 structure (`i⁴ ≈ 1` proved in
Part 2) is what cleanly separates the Taylor terms into cos (even
power) and i·sin (odd power) contributions.

**Estimated LOC**: ~150-200.

## Total Wave Γ₇ M3 effort estimate

Phases 3C Part 3b → Phase 4: **~650-1000 LOC across 4-5 focused sessions**.

The structural framework is now fully in place. The remaining work is
substantial Cauchy-product manipulation that closely parallels the
existing `TauReal.exp_add` proof, lifted componentwise to TauComplex.

## What Phase 3C Part 3a added

* `TauComplex.cauchyDiag a b n` — n-th Cauchy product diagonal.
* `TauComplex.cauchyPStar a b N` — partial Cauchy product.
* Simp lemmas: `cauchyPStar_zero`, `cauchyPStar_succ`, `cauchyDiag_zero`.
* Detailed roadmap (this docstring) for Phase 3C Part 3b → 4.

The Cauchy-product infrastructure is the **load-bearing structural
foundation** for the M3 breakthrough proper.

## Phase 3C Part 3b (this commit) adds

* `TauReal.equiv_add_congr` — congruence lemma: equiv is preserved by add.
* `TauComplex.equiv_add_congr` — componentwise lift.
* `TauComplex.exp_term_add_eq_cauchyDiag_target : Prop` — the per-term
  binomial identity as a named target proposition, parallel to
  `BBPLeibnizCorrespondence` (Wave Γ₆).
* `TauComplex.exp_partial_add_eq_cauchyPStar_base` — proof of the base
  case (n=0).
* `TauComplex.exp_partial_add_eq_cauchyPStar_under_term_hyp` —
  conditional theorem: IF the per-term identity holds at all depths,
  THEN the partial-sum identity follows by induction.

Phase 3C Part 3b' (next session) will discharge the per-term identity
via the binomial theorem on TauComplex.

## Trust budget (unchanged)

* sorry = 0
* axioms = 3
* TauLib build: 2695/2695 jobs ✓
-/

-- ============================================================
-- PART 9: TauReal/TauComplex EQUIV CONGRUENCE LEMMAS (Phase 3C Part 3b)
-- ============================================================

/-- **TauReal equiv congruence under addition**: if `a ≈ a'` and
    `b ≈ b'` then `a.add b ≈ a'.add b'`.

    Modulus construction: take `μ(k) := max (μ_a (2k+1)) (μ_b (2k+1))`,
    so at depth `n ≥ μ(k)`, each component is bounded by `1/(2k+2)`,
    and the triangle inequality gives the combined bound `2/(2k+2) = 1/(k+1)`. -/
theorem TauReal.equiv_add_congr {a a' b b' : TauReal}
    (h_a : a.equiv a') (h_b : b.equiv b') :
    (a.add b).equiv (a'.add b') := by
  obtain ⟨μ_a, hμ_a⟩ := h_a
  obtain ⟨μ_b, hμ_b⟩ := h_b
  refine ⟨fun k => max (μ_a (2 * k + 1)) (μ_b (2 * k + 1)), ?_⟩
  intro k n hn
  have h_a_n : μ_a (2 * k + 1) ≤ n := le_of_max_le_left hn
  have h_b_n : μ_b (2 * k + 1) ≤ n := le_of_max_le_right hn
  have h_a_bound := hμ_a (2 * k + 1) n h_a_n
  have h_b_bound := hμ_b (2 * k + 1) n h_b_n
  -- At TauRat.lt level: each |a.approx n - a'.approx n| < 1/(2k+2).
  -- Triangle: |(a+b).approx n - (a'+b').approx n|
  --         ≤ |a.approx n - a'.approx n| + |b.approx n - b'.approx n|
  --         < 1/(2k+2) + 1/(2k+2) = 1/(k+1).
  unfold TauRat.lt at h_a_bound h_b_bound ⊢
  rw [TauRat.toRat_abs, toRat_sub] at h_a_bound h_b_bound
  rw [TauRat.ofNatRecip_toRat] at h_a_bound h_b_bound
  rw [TauRat.toRat_abs, toRat_sub, TauRat.ofNatRecip_toRat]
  -- Unfold (a.add b).approx n = (a.approx n).add (b.approx n).
  show |((TauReal.add a b).approx n).toRat - ((TauReal.add a' b').approx n).toRat|
        < 1 / ((k : Rat) + 1)
  unfold TauReal.add
  simp only
  rw [toRat_add, toRat_add]
  -- Goal: |(a.approx n).toRat + (b.approx n).toRat
  --        - ((a'.approx n).toRat + (b'.approx n).toRat)| < 1/(k+1)
  have h_split :
      ((a.approx n).toRat + (b.approx n).toRat)
        - ((a'.approx n).toRat + (b'.approx n).toRat)
      = ((a.approx n).toRat - (a'.approx n).toRat)
        + ((b.approx n).toRat - (b'.approx n).toRat) := by ring
  rw [h_split]
  have h_tri : |((a.approx n).toRat - (a'.approx n).toRat)
                + ((b.approx n).toRat - (b'.approx n).toRat)|
              ≤ |(a.approx n).toRat - (a'.approx n).toRat|
                + |(b.approx n).toRat - (b'.approx n).toRat| := abs_add_le _ _
  -- Combined: < 1/(2k+2) + 1/(2k+2) = 1/(k+1).
  -- TauRat.ofNatRecip k is 1/(k+1); so .ofNatRecip (2k+1) is 1/(2k+2) = 1/(2(k+1)).
  -- Sum: 2/(2(k+1)) = 1/(k+1). ✓
  have h_two_recip :
      1 / (((2 * k + 1 : Nat) : Rat) + 1) + 1 / (((2 * k + 1 : Nat) : Rat) + 1)
        = 1 / ((k : Rat) + 1) := by
    have h_cast : ((2 * k + 1 : Nat) : Rat) + 1 = 2 * ((k : Rat) + 1) := by
      push_cast; ring
    rw [h_cast]
    have h_k_nn : (0 : Rat) ≤ (k : Rat) := by exact_mod_cast Nat.zero_le k
    have h_k1_pos : (0 : Rat) < (k : Rat) + 1 := by linarith
    field_simp
    ring
  linarith

/-- **TauComplex equiv congruence under addition**: componentwise lift
    of `TauReal.equiv_add_congr`. -/
theorem TauComplex.equiv_add_congr {z z' w w' : TauComplex}
    (h_z : z.equiv z') (h_w : w.equiv w') :
    (z.add w).equiv (z'.add w') :=
  ⟨TauReal.equiv_add_congr h_z.1 h_w.1, TauReal.equiv_add_congr h_z.2 h_w.2⟩

-- ============================================================
-- PART 10: PHASE 3C PART 3b — BASE CASE + CONDITIONAL INDUCTION
-- ============================================================

/-- **[I.D-TauComplex-BinomialTarget]** The per-term binomial identity
    on TauComplex as a named target proposition (Phase 3C Part 3b').

    Asserts that for all TauComplex `z₁, z₂` and Nat `n`:
    `(exp_term (z₁ + z₂) n) ≈ cauchyDiag (exp_term z₁) (exp_term z₂) n`.

    Discharging this requires the binomial theorem on TauComplex —
    essentially proving `(z₁+z₂)^n = Σ_{i=0}^n C(n,i) z₁^i z₂^(n-i)`
    at equiv level. Substantial work (~200-400 LOC) queued for
    Part 3b'. -/
def TauComplex.exp_term_add_eq_cauchyDiag_target : Prop :=
  ∀ (z₁ z₂ : TauComplex) (n : Nat),
    (TauComplex.exp_term (z₁.add z₂) n).equiv
      (TauComplex.cauchyDiag (TauComplex.exp_term z₁) (TauComplex.exp_term z₂) n)

/-- **Base case** (n = 0) of the binomial identity at the
    partial-sum level: both sides are `TauComplex.zero`, hence equiv. -/
theorem TauComplex.exp_partial_add_eq_cauchyPStar_base (z₁ z₂ : TauComplex) :
    (TauComplex.exp_partial (z₁.add z₂) 0).equiv
      (TauComplex.cauchyPStar (TauComplex.exp_term z₁) (TauComplex.exp_term z₂) 0) := by
  -- exp_partial _ 0 = TauComplex.zero (by definition).
  -- cauchyPStar _ _ 0 = TauComplex.zero (by simp lemma).
  -- TauComplex.zero.equiv TauComplex.zero by reflexivity.
  show (TauComplex.zero).equiv (TauComplex.zero)
  exact TauComplex.equiv_refl _

/-- **The partial-sum binomial identity, conditional on the per-term
    identity holding at all depths.**

    If `exp_term_add_eq_cauchyDiag_target` holds, then by induction on `n`,
    the partial-sum identity follows: at each step, use IH to combine
    the partial-sum equiv with the per-term equiv via `equiv_add_congr`.

    Phase 3C Part 3b' will discharge the per-term identity, after which
    this conditional theorem gives the unconditional partial-sum identity. -/
theorem TauComplex.exp_partial_add_eq_cauchyPStar_under_term_hyp
    (h_term : TauComplex.exp_term_add_eq_cauchyDiag_target)
    (z₁ z₂ : TauComplex) (n : Nat) :
    (TauComplex.exp_partial (z₁.add z₂) n).equiv
      (TauComplex.cauchyPStar (TauComplex.exp_term z₁) (TauComplex.exp_term z₂) n) := by
  induction n with
  | zero => exact TauComplex.exp_partial_add_eq_cauchyPStar_base z₁ z₂
  | succ n ih =>
    -- exp_partial (z₁+z₂) (n+1) = exp_partial (z₁+z₂) n + exp_term (z₁+z₂) n
    -- cauchyPStar ... (n+1) = cauchyPStar ... n + cauchyDiag ... n
    -- IH: exp_partial (z₁+z₂) n ≈ cauchyPStar ... n
    -- h_term n: exp_term (z₁+z₂) n ≈ cauchyDiag ... n
    -- Apply equiv_add_congr.
    show (TauComplex.exp_partial (z₁.add z₂) (n + 1)).equiv
          (TauComplex.cauchyPStar (TauComplex.exp_term z₁) (TauComplex.exp_term z₂) (n + 1))
    rw [TauComplex.exp_partial_succ, TauComplex.cauchyPStar_succ]
    exact TauComplex.equiv_add_congr ih (h_term z₁ z₂ n)

/-- **The M3 target** (Phase 3C Part 3e — unconditional). Stated as a
    `def` (proposition) since the per-term identity hasn't yet been
    discharged. Once Part 3b' lands, this becomes a `theorem` via
    the `_under_term_hyp` conditional. -/
def TauComplex.exp_partial_add_eq_cauchyPStar_target : Prop :=
  ∀ (z₁ z₂ : TauComplex) (n : Nat),
    (TauComplex.exp_partial (z₁.add z₂) n).equiv
      (TauComplex.cauchyPStar (TauComplex.exp_term z₁) (TauComplex.exp_term z₂) n)

-- ============================================================
-- PART 11: PHASE 3C PART 3b' — Equiv-Negate/Sub/Mul/Pow CONGRUENCE
-- ============================================================

/-! ## Phase 3C Part 3b' deliverables — congruence infrastructure

The binomial theorem on TauComplex (Phase 3C Part 3b'', queued) requires
**all four** arithmetic operations to preserve equiv:

* Addition: ✓ `TauReal.equiv_add_congr` + `TauComplex.equiv_add_congr` (Part 3b)
* Negation: ✓ this commit — easy (same modulus, since `|−a − −b| = |a − b|`)
* Subtraction: ✓ this commit — derived from add + negate
* Multiplication (with bound): ✓ this commit — via `mul_respects_equiv_right_of_bound`
  twice + commutativity
* Power (with bound): ✓ this commit — induction on the exponent

These foundational lemmas are load-bearing for the binomial theorem.
Once they're in place, the actual binomial expansion proof becomes
mechanical induction with Pascal's rule + distributivity.

The "with bound" qualifier is structurally necessary for multiplication:
unbounded factors can amplify equiv errors arbitrarily, so we need
`BoundedBy`-style hypotheses to control the proof modulus.
-/

/-- **TauReal equiv congruence under negation**: if `a ≈ b` then
    `a.negate ≈ b.negate`. Modulus unchanged. -/
theorem TauReal.equiv_negate_congr {a b : TauReal} (h : a.equiv b) :
    a.negate.equiv b.negate := by
  obtain ⟨μ, hμ⟩ := h
  refine ⟨μ, ?_⟩
  intro k n hkn
  have h_orig := hμ k n hkn
  unfold TauRat.lt at h_orig ⊢
  rw [TauRat.toRat_abs, toRat_sub] at h_orig
  rw [TauRat.toRat_abs, toRat_sub]
  rw [TauRat.ofNatRecip_toRat] at h_orig ⊢
  -- Unfold (a.negate).approx n .toRat = -(a.approx n).toRat
  show |((TauReal.negate a).approx n).toRat - ((TauReal.negate b).approx n).toRat|
        < 1 / ((k : Rat) + 1)
  unfold TauReal.negate
  simp only
  rw [toRat_negate, toRat_negate]
  -- |-a - (-b)| = |b - a| = |a - b|
  have h_flip : -(a.approx n).toRat - -(b.approx n).toRat
                  = -((a.approx n).toRat - (b.approx n).toRat) := by ring
  rw [h_flip, abs_neg]
  exact h_orig

/-- **TauReal equiv congruence under subtraction**: if `a ≈ a'` and
    `b ≈ b'` then `a.sub b ≈ a'.sub b'`. Derived from add + negate. -/
theorem TauReal.equiv_sub_congr {a a' b b' : TauReal}
    (h_a : a.equiv a') (h_b : b.equiv b') :
    (a.sub b).equiv (a'.sub b') := by
  -- sub is defined as add b.negate
  show (a.add b.negate).equiv (a'.add b'.negate)
  exact TauReal.equiv_add_congr h_a (TauReal.equiv_negate_congr h_b)

/-- **TauReal equiv congruence under multiplication** (with bound hypothesis):
    if `a ≈ a'` and `b ≈ b'`, with `a'` bounded by `Ma` and `b` bounded by `Mb`,
    then `a.mul b ≈ a'.mul b'`.

    Proof: chain via `a.mul b ≈ a'.mul b ≈ a'.mul b'` using
    `mul_respects_equiv_right_of_bound` twice (once directly, once after
    commuting via `taureal_mul_comm`). -/
theorem TauReal.equiv_mul_congr {a a' b b' : TauReal}
    (Ma Mb : Nat) (hMa : 1 ≤ Ma) (hMb : 1 ≤ Mb)
    (h_bound_a' : ∀ n, (a'.approx n).abs.toRat ≤ Ma)
    (h_bound_b : ∀ n, (b.approx n).abs.toRat ≤ Mb)
    (h_a : a.equiv a') (h_b : b.equiv b') :
    (a.mul b).equiv (a'.mul b') := by
  -- Step 1: a·b ≈ a'·b (vary left factor, b bounded).
  have step1 : (a.mul b).equiv (a'.mul b) :=
    TauReal.mul_respects_equiv_right_of_bound a a' b Mb hMb h_bound_b h_a
  -- Step 2: a'·b ≈ a'·b' (vary right factor, a' bounded — via commutativity).
  have step2 : (a'.mul b).equiv (a'.mul b') := by
    have h_comm1 : (a'.mul b).equiv (b.mul a') := taureal_mul_comm a' b
    have h_swap : (b.mul a').equiv (b'.mul a') :=
      TauReal.mul_respects_equiv_right_of_bound b b' a' Ma hMa h_bound_a' h_b
    have h_comm2 : (b'.mul a').equiv (a'.mul b') := taureal_mul_comm b' a'
    exact TauReal.equiv_trans (TauReal.equiv_trans h_comm1 h_swap) h_comm2
  exact TauReal.equiv_trans step1 step2

/-- **TauComplex equiv congruence under multiplication** (with bound).

    Lifts `TauReal.equiv_mul_congr` componentwise. TauComplex multiplication
    `(a+bi)(c+di) = (ac − bd) + (ad + bc)i` mixes both components, so the
    bound and equiv hypotheses are required on all four TauReal components.

    The lift uses:
    * `TauReal.equiv_mul_congr` on each of the four products `ac, bd, ad, bc`.
    * `TauReal.equiv_sub_congr` for the real part `ac − bd`.
    * `TauReal.equiv_add_congr` for the imag part `ad + bc`. -/
theorem TauComplex.equiv_mul_congr {z z' w w' : TauComplex}
    (Mre Mim : Nat) (hMre : 1 ≤ Mre) (hMim : 1 ≤ Mim)
    (h_bound_z'_re : ∀ n, (z'.re.approx n).abs.toRat ≤ Mre)
    (h_bound_z'_im : ∀ n, (z'.im.approx n).abs.toRat ≤ Mim)
    (h_bound_w_re : ∀ n, (w.re.approx n).abs.toRat ≤ Mre)
    (h_bound_w_im : ∀ n, (w.im.approx n).abs.toRat ≤ Mim)
    (h_z : z.equiv z') (h_w : w.equiv w') :
    (z.mul w).equiv (z'.mul w') := by
  -- Componentwise:
  -- (z·w).re = z.re·w.re − z.im·w.im
  -- (z·w).im = z.re·w.im + z.im·w.re
  refine ⟨?_, ?_⟩
  · -- Real part: z.re·w.re − z.im·w.im ≈ z'.re·w'.re − z'.im·w'.im
    show ((z.re.mul w.re).sub (z.im.mul w.im)).equiv
          ((z'.re.mul w'.re).sub (z'.im.mul w'.im))
    apply TauReal.equiv_sub_congr
    · -- z.re·w.re ≈ z'.re·w'.re
      exact TauReal.equiv_mul_congr Mre Mre hMre hMre
              h_bound_z'_re h_bound_w_re h_z.1 h_w.1
    · -- z.im·w.im ≈ z'.im·w'.im
      exact TauReal.equiv_mul_congr Mim Mim hMim hMim
              h_bound_z'_im h_bound_w_im h_z.2 h_w.2
  · -- Imag part: z.re·w.im + z.im·w.re ≈ z'.re·w'.im + z'.im·w'.re
    show ((z.re.mul w.im).add (z.im.mul w.re)).equiv
          ((z'.re.mul w'.im).add (z'.im.mul w'.re))
    apply TauReal.equiv_add_congr
    · -- z.re·w.im ≈ z'.re·w'.im
      exact TauReal.equiv_mul_congr Mre Mim hMre hMim
              h_bound_z'_re h_bound_w_im h_z.1 h_w.2
    · -- z.im·w.re ≈ z'.im·w'.re
      exact TauReal.equiv_mul_congr Mim Mre hMim hMre
              h_bound_z'_im h_bound_w_re h_z.2 h_w.1

/-! Note on `TauComplex.equiv_pow_congr`:

The natural next step is `equiv_pow_congr`: if `z ≈ z'` (with z' bounded),
then `pow z k ≈ pow z' k` for all k. By induction on k using
`equiv_mul_congr`.

This requires that `pow z k` stays bounded across k (some power of the
bound on z). The bound compounds: if |z'| ≤ R, then |z'^k| ≤ R^k.

Stating this cleanly requires either:
- A `BoundedBy` predicate on TauComplex (we have it for TauReal componentwise).
- Pre-computed bounds on powers.

Queued for Phase 3C Part 3b'' as part of the binomial-theorem prep. The
foundational `equiv_mul_congr` shipped here is the load-bearing piece;
`equiv_pow_congr` will be a mechanical induction on top.
-/

-- ============================================================
-- PART 12: PHASE 3C PART 3b'' — TauComplex.BoundedBy + target propositions
-- ============================================================

/-! ## Phase 3C Part 3b'' deliverables — BoundedBy + binomial targets

The remaining piece for discharging `exp_term_add_eq_cauchyDiag_target`
is the binomial theorem on TauComplex. Part 3b'' ships the
**bound-tracking infrastructure** + the **named-target propositions**
that decompose the binomial proof into focused next-session work.

The binomial theorem requires bound-tracking because TauReal.equiv_mul_congr
needs `BoundedBy` hypotheses on both factors. As we induct over `pow z k`,
the bound compounds: `|pow z k| ≤ M^k` for `|z| ≤ M`. We need a
`TauComplex.BoundedBy` predicate to manage this cleanly.
-/

/-- **TauComplex BoundedBy predicate**: both real and imaginary
    parts bounded by `M` at every approximation level. Componentwise
    version of `TauReal.BoundedBy`.

    Used as the hypothesis for `equiv_pow_congr` and the binomial
    theorem on TauComplex. -/
def TauComplex.BoundedBy (z : TauComplex) (M : Nat) : Prop :=
  (∀ n, (z.re.approx n).abs.toRat ≤ M) ∧
  (∀ n, (z.im.approx n).abs.toRat ≤ M)

/-- **[I.D-TauComplex-EquivPowCongr-Target]** Named target for the
    pow congruence theorem.

    Asserts: for `z ≈ z'` with `z'` bounded by `M` (in TauComplex.BoundedBy
    sense), `pow z k ≈ pow z' k` for all `k ≤ N` and any bound `Mk`
    appropriate to depth `k`.

    Discharging this requires:
    1. Establishing that `pow z' k` is bounded (with explicit compound bound).
    2. Induction on `k` using `equiv_mul_congr` at each step.

    Phase 3C Part 3b''' (queued) will discharge this. -/
def TauComplex.equiv_pow_congr_target : Prop :=
  ∀ (z z' : TauComplex) (k : Nat),
    z.equiv z' →
    (∀ M : Nat, 1 ≤ M → TauComplex.BoundedBy z' M →
      (TauComplex.pow z k).equiv (TauComplex.pow z' k))

/-- **[I.D-TauComplex-AddPowEquiv-Target]** Named target for the
    binomial theorem on TauComplex.

    Asserts: `pow (z₁ + z₂) n ≈ Σ_{i=0}^n C(n,i) · pow z₁ i · pow z₂ (n-i)`
    at TauComplex.equiv level, where:
    - `C(n,i)` is the binomial coefficient (a natural number).
    - The sum is `TauComplex.sum` (direct Nat recursion).
    - `C(n,i) · z` means `(TauComplex.fromTauReal (TauReal.fromNat C(n,i))).mul z`.

    Discharging this requires:
    1. Induction on `n`.
    2. Pascal's rule `C(n,i) + C(n,i-1) = C(n+1,i)`.
    3. TauComplex distributivity (`taucomplex_left_distrib`).
    4. The congruence lemmas (Parts 3b + 3b').

    Phase 3C Part 3b''' (queued) will discharge this. -/
def TauComplex.add_pow_equiv_target : Prop :=
  ∀ (z₁ z₂ : TauComplex) (n : Nat),
    (TauComplex.pow (z₁.add z₂) n).equiv
      (TauComplex.sum (fun i =>
        (TauComplex.fromTauReal (TauReal.fromNat (Nat.choose n i))).mul
          ((TauComplex.pow z₁ i).mul (TauComplex.pow z₂ (n - i))))
        (n + 1))

-- ============================================================
-- PART 13: WHAT THE BINOMIAL TARGET WOULD UNLOCK
-- ============================================================

/-! ## The discharge chain (Part 3b''' → Part 3c → Part 3e → Part 4)

With `add_pow_equiv_target` discharged in Part 3b''', the path to
the M3 endpoint is mechanical:

### Part 3b''' → discharges `exp_term_add_eq_cauchyDiag_target`

Combine the binomial theorem with division by `n!`:

  pow (z₁+z₂) n / n!
    ≈ Σ_{i=0}^n C(n,i) · pow z₁ i · pow z₂ (n-i) / n!     [by binomial theorem]
    = Σ_{i=0}^n pow z₁ i · pow z₂ (n-i) / (i! · (n-i)!)  [C(n,i) = n!/(i!(n-i)!)]
    = Σ_{i=0}^n (pow z₁ i / i!) · (pow z₂ (n-i) / (n-i)!) [factor reorganisation]
    = Σ_{i=0}^n exp_term z₁ i · exp_term z₂ (n-i)        [by exp_term defn]
    = cauchyDiag (exp_term z₁) (exp_term z₂) n           [by cauchyDiag defn]

This gives `exp_term (z₁+z₂) n ≈ cauchyDiag ...` directly.

### Part 3c → Cauchy-product bound at TauComplex level

Componentwise lift of `TauRat.cauchy_product_bound`. Each TauComplex
Cauchy product decomposes into four TauRat Cauchy products with signs,
each bounded by the existing TauRat tail bound.

### Part 3d → TauComplex.exp (full diagonal construction)

Mirror `TauReal.exp` at TauComplex level:
  exp z := componentwise (diagonal) Cauchy sequence over exp_partial.

### Part 3e → TauComplex.exp_add (the M3 target)

Combine 3b'' + 3c + 3d via the standard structure:
- Binomial identity rewrites exp_partial(z₁+z₂) as cauchyPStar.
- Cauchy-product bound estimates the difference from exp_partial·exp_partial.
- Modulus inequality (parallel to TauReal.exp_add) closes the equiv.

### Part 4 → sin/cos addition formula extraction

Specialise to z₁ = i·α, z₂ = i·β. The cyclotomic-4 cycle of `i^k`
separates Taylor terms into cos (even-power real) and sin (odd-power
imaginary) contributions. Real/imag parts of `exp_add` at imaginary
arguments give the addition formulae.

## What this commit (Part 3b'') adds

* `TauComplex.BoundedBy z M` — bound-tracking predicate.
* `TauComplex.equiv_pow_congr_target : Prop` — pow congruence as named target.
* `TauComplex.add_pow_equiv_target : Prop` — binomial theorem as named target.
* Detailed proof-chain documentation showing how discharge of `add_pow_equiv_target`
  immediately gives `exp_term_add_eq_cauchyDiag_target` (Part 3b's queued target).

## Trust budget (unchanged)

* sorry = 0
* axioms = 3
* Full TauLib build: 2695/2695 jobs ✓
* Part 3b'' is infrastructure + named targets — no new proofs beyond
  the type-level definitions.
-/

-- ============================================================
-- PART 14: PHASE 3C PART 3b''' — Left-identity equivs + binomial base case
-- ============================================================

/-- **TauComplex equivalence is transitive** (componentwise via TauReal). -/
theorem TauComplex.equiv_trans {z w v : TauComplex}
    (h_zw : z.equiv w) (h_wv : w.equiv v) : z.equiv v :=
  ⟨TauReal.equiv_trans h_zw.1 h_wv.1, TauReal.equiv_trans h_zw.2 h_wv.2⟩

/-! ## Phase 3C Part 3b''' deliverables — base case + left-identity equivs

The binomial theorem proof (Part 3b''' through 3b'''') decomposes into
disciplined sub-pieces, mirroring the pattern that's worked through
Parts 3a-3b''. This commit ships:

1. **Left-identity equivs**: `zero.add z ≈ z` and `one.mul z ≈ z` at the
   TauComplex.equiv level. These are needed for sum-simplification steps
   in the binomial proof (sums of the form `zero.add (term)` reduce via
   left-identity).

2. **Base case of binomial theorem** (`n = 0`): explicitly proved as
   a focused theorem. Both sides reduce to `TauComplex.one` (up to equiv).

Phase 3C Part 3b'''' (next session) will handle the inductive step:
- Apply IH via equiv_mul_congr (with bound tracking).
- Distribute (z₁+z₂) over the sum.
- Reindex the resulting two sums.
- Apply Pascal's rule to combine.
-/

/-- **Left-identity for add at TauComplex.equiv level**: `zero.add z ≈ z`.

    Derived via `taucomplex_add_comm` + `taucomplex_add_zero` (the
    right-identity version that already exists in `ComplexField.lean`). -/
theorem TauComplex.zero_add_equiv (z : TauComplex) :
    (TauComplex.zero.add z).equiv z := by
  have h_comm : (TauComplex.zero.add z).equiv (z.add TauComplex.zero) :=
    taucomplex_add_comm TauComplex.zero z
  have h_right_id : (z.add TauComplex.zero).equiv z :=
    taucomplex_add_zero z
  exact TauComplex.equiv_trans h_comm h_right_id

/-- **Left-identity for mul at TauComplex.equiv level**: `one.mul z ≈ z`.

    Derived via `taucomplex_mul_comm` + `taucomplex_mul_one` (the
    right-identity version that already exists in `ComplexField.lean`). -/
theorem TauComplex.one_mul_equiv (z : TauComplex) :
    (TauComplex.one.mul z).equiv z := by
  have h_comm : (TauComplex.one.mul z).equiv (z.mul TauComplex.one) :=
    taucomplex_mul_comm TauComplex.one z
  have h_right_id : (z.mul TauComplex.one).equiv z :=
    taucomplex_mul_one z
  exact TauComplex.equiv_trans h_comm h_right_id

/-- **Phase 3C Part 3b''' core: base case of the binomial theorem**.

    At `n = 0`, the binomial theorem reduces componentwise to TauRat
    identities that close by `ring` at the Int level.

    LHS: `pow (z₁ + z₂) 0 = TauComplex.one` (definitional).
    RHS: `sum (...) 1 = zero.add ((fromTauReal (fromNat 1)).mul (one.mul one))`,
    which is structurally a TauComplex whose components reduce to `1` (re)
    and `0` (im) after componentwise simplification.

    Direct pointwise reduction following the proof pattern of
    `i_unit_pow_4_equiv_one` (Part 2). -/
theorem TauComplex.add_pow_equiv_base (z₁ z₂ : TauComplex) :
    (TauComplex.pow (z₁.add z₂) 0).equiv
      (TauComplex.sum (fun i =>
        (TauComplex.fromTauReal (TauReal.fromNat (Nat.choose 0 i))).mul
          ((TauComplex.pow z₁ i).mul (TauComplex.pow z₂ (0 - i))))
        (0 + 1)) := by
  -- pow z 0 = TauComplex.one (definitional).
  -- sum (...) (0+1) = sum (...) 1 = zero.add (term at i=0).
  -- term at i=0 has C(0,0)=1, pow z₁ 0 = one, pow z₂ 0 = one, so it's
  -- (fromTauReal (fromNat 1)).mul (one.mul one).
  -- Both sides should reduce to TauComplex.one componentwise.
  refine ⟨?_, ?_⟩
  · -- Real part
    apply TauReal.equiv_of_pointwise
    intro n
    simp only [TauComplex.pow, TauComplex.sum, TauComplex.mul, TauComplex.add,
               TauComplex.zero, TauComplex.one, TauComplex.fromTauReal,
               TauReal.sub, TauReal.add, TauReal.mul, TauReal.negate,
               TauReal.fromNat, TauReal.fromTauRat, TauReal.zero, TauReal.one]
    simp only [TauRat.equiv, TauRat.add, TauRat.mul, TauRat.negate,
               TauRat.zero, TauRat.one]
    try rw [equiv_iff_toInt_eq]
    try simp only [toInt_add, toInt_mul, toInt_negate, toInt_fromNat, toInt_zero, toInt_one]
    try push_cast
    try ring
    try decide
  · -- Imaginary part
    apply TauReal.equiv_of_pointwise
    intro n
    simp only [TauComplex.pow, TauComplex.sum, TauComplex.mul, TauComplex.add,
               TauComplex.zero, TauComplex.one, TauComplex.fromTauReal,
               TauReal.sub, TauReal.add, TauReal.mul, TauReal.negate,
               TauReal.fromNat, TauReal.fromTauRat, TauReal.zero, TauReal.one]
    simp only [TauRat.equiv, TauRat.add, TauRat.mul, TauRat.negate,
               TauRat.zero, TauRat.one]
    try rw [equiv_iff_toInt_eq]
    try simp only [toInt_add, toInt_mul, toInt_negate, toInt_fromNat, toInt_zero, toInt_one]
    try push_cast
    try ring
    try decide

/-! ## Phase 3C Part 3 roadmap (next session)

With `TauComplex.exp_partial` defined, the next step is the **M3
breakthrough proper**: prove `TauComplex.exp_add`, i.e.,

  `exp(z₁ + z₂) ≈ exp(z₁) · exp(z₂)` (at the TauComplex.equiv level)

by lifting `TauReal.exp_add` (Wave 3b R10, ~200 LOC of Cauchy-product
manipulation in TauRealExp.lean) to TauComplex.

### The lift strategy

The existing `TauReal.exp_add` proof relies on:
1. `TauRat.cauchyPStar` — Cauchy product at TauRat level (TauRealSum.lean).
2. `TauReal.exp_partial_add_toRat_eq_cauchyPStar` — finite-N Cauchy-product
   identity for exp partial sums.
3. `TauRat.cauchy_product_bound` — tail bound on the Cauchy product.
4. `Rat.four_div_two_pow_lt_recip` — the Cauchy-bound template's
   workhorse.

For TauComplex, the lift adds a layer of complex multiplication on top
of each Cauchy-product step. The combinatorial identity (binomial
theorem applied to `(a + b)^k`) carries over verbatim — the new
content is that complex multiplication `(a+bi)(c+di) = (ac-bd) + (ad+bc)i`
distributes correctly.

### Phase 3C Part 4 (sin/cos addition formula extraction)

Once `TauComplex.exp_add` lands, specialising to purely imaginary
arguments `z₁ = i·α`, `z₂ = i·β` gives:

  exp(i·α) · exp(i·β) ≈ exp(i·(α+β))

Expanding both sides via `TauComplex.mul`:
- LHS = (cos α + i sin α)(cos β + i sin β)
       = (cos α cos β - sin α sin β) + i(cos α sin β + sin α cos β)
- RHS = cos(α+β) + i sin(α+β)

Equating real and imaginary parts via `TauComplex.equiv` yields:
- cos(α+β) ≈ cos α cos β - sin α sin β
- sin(α+β) ≈ cos α sin β + sin α cos β

The cyclotomic-4 structure of `i` (Part 2's `i_unit_pow_4_equiv_one`)
is what makes the LHS expansion clean: powers of `i` cycle through
{1, i, -1, -i}, separating the real exp(i·x) Taylor terms into
cos (even powers) and i·sin (odd powers) contributions.

### What this commit adds

* `TauRat.scale_by_inv_factorial` — divide a TauRat by k!.
* `TauReal.scale_by_inv_factorial` — pointwise TauReal lift.
* `TauComplex.exp_term z k` — `z^k / k!` as a TauComplex.
* `TauComplex.sum` — direct Nat-recursion summation on TauComplex.
* `TauComplex.exp_partial z n` — the partial sum at depth n.
* Componentwise simp lemmas (exp_term_re, exp_term_im, sum_*, exp_partial_*).

This completes Phase 3C Part 2b — the **structural definition** of
exp on TauComplex. Phase 3C Part 3 (the actual exp_add lift) is the
next session's M3 breakthrough work.
-/

-- ============================================================
-- PART 15: PHASE 3C PART 3b'''' — Sum-mul-distributivity at TauComplex
-- ============================================================

/-! ## Phase 3C Part 3b'''' deliverables — sum-manipulation infrastructure

The inductive step of the binomial theorem (Part 3b''''') needs to
distribute `(z₁ + z₂)` over a sum, which requires:

1. **Right-distributivity at equiv**: `(a + b) · c ≈ a·c + b·c`.
2. **Sum-mul distributivity**: `(sum f n) · z ≈ sum (fun i => (f i)·z) n`.

These foundational structural lemmas derive from the existing ring
axioms via the equiv-congruence framework. They unblock Part 3b''''' (the
substantive binomial induction step) without re-deriving structural
manipulations inline.
-/

/-- `zero.mul z ≈ zero` at TauComplex.equiv level.

    Direct componentwise pointwise reduction. -/
theorem TauComplex.zero_mul_equiv (z : TauComplex) :
    (TauComplex.zero.mul z).equiv TauComplex.zero := by
  refine ⟨?_, ?_⟩
  · apply TauReal.equiv_of_pointwise
    intro n
    simp only [TauComplex.mul, TauComplex.zero,
               TauReal.sub, TauReal.add, TauReal.mul, TauReal.negate, TauReal.zero]
    simp only [TauRat.equiv, TauRat.add, TauRat.mul, TauRat.negate, TauRat.zero]
    try rw [equiv_iff_toInt_eq]
    try simp only [toInt_add, toInt_mul, toInt_negate, toInt_fromNat, toInt_zero, toInt_one]
    try push_cast
    try ring
    try decide
  · apply TauReal.equiv_of_pointwise
    intro n
    simp only [TauComplex.mul, TauComplex.zero,
               TauReal.sub, TauReal.add, TauReal.mul, TauReal.negate, TauReal.zero]
    simp only [TauRat.equiv, TauRat.add, TauRat.mul, TauRat.negate, TauRat.zero]
    try rw [equiv_iff_toInt_eq]
    try simp only [toInt_add, toInt_mul, toInt_negate, toInt_fromNat, toInt_zero, toInt_one]
    try push_cast
    try ring
    try decide

/-- **Right-distributivity at equiv**: `(a + b) · c ≈ a·c + b·c`.

    Derived from `taucomplex_left_distrib` (`a · (b + c) ≈ a·b + a·c`)
    via `taucomplex_mul_comm` chains. -/
theorem TauComplex.right_distrib_equiv (a b c : TauComplex) :
    ((a.add b).mul c).equiv ((a.mul c).add (b.mul c)) := by
  -- (a+b)·c ≈ c·(a+b)     [mul_comm]
  --        ≈ c·a + c·b   [left_distrib]
  --        ≈ a·c + b·c   [mul_comm on each term via equiv_add_congr]
  have h1 : ((a.add b).mul c).equiv (c.mul (a.add b)) :=
    taucomplex_mul_comm (a.add b) c
  have h2 : (c.mul (a.add b)).equiv ((c.mul a).add (c.mul b)) :=
    taucomplex_left_distrib c a b
  have h3 : ((c.mul a).add (c.mul b)).equiv ((a.mul c).add (b.mul c)) :=
    TauComplex.equiv_add_congr (taucomplex_mul_comm c a) (taucomplex_mul_comm c b)
  exact TauComplex.equiv_trans (TauComplex.equiv_trans h1 h2) h3

/-- **Sum-mul-distributivity (right)**: `(sum f n) · z ≈ sum (fun i => (f i)·z) n`.

    Foundational lemma for the binomial theorem's inductive step:
    distributing `(z₁+z₂)` over `sum (binomial-terms n)`.

    Proof by induction on `n`:
    - Base (n=0): `sum f 0 = zero`, so LHS = `zero · z ≈ zero` (via
      `zero_mul_equiv`), and RHS = `sum (...) 0 = zero`.
    - Step (n+1): LHS = `(sum f n + f n) · z ≈ (sum f n)·z + (f n)·z`
      (`right_distrib_equiv`), then by IH on the first term + `equiv_add_congr`
      gives `sum (...) n + (f n)·z = RHS`. -/
theorem TauComplex.sum_mul_distrib_right
    (f : Nat → TauComplex) (z : TauComplex) (n : Nat) :
    ((TauComplex.sum f n).mul z).equiv (TauComplex.sum (fun i => (f i).mul z) n) := by
  induction n with
  | zero =>
    show (TauComplex.zero.mul z).equiv TauComplex.zero
    exact TauComplex.zero_mul_equiv z
  | succ n ih =>
    show (((TauComplex.sum f n).add (f n)).mul z).equiv
          ((TauComplex.sum (fun i => (f i).mul z) n).add ((f n).mul z))
    have h_distrib : (((TauComplex.sum f n).add (f n)).mul z).equiv
                      (((TauComplex.sum f n).mul z).add ((f n).mul z)) :=
      TauComplex.right_distrib_equiv (TauComplex.sum f n) (f n) z
    have h_ih : (((TauComplex.sum f n).mul z).add ((f n).mul z)).equiv
                  ((TauComplex.sum (fun i => (f i).mul z) n).add ((f n).mul z)) :=
      TauComplex.equiv_add_congr ih (TauComplex.equiv_refl _)
    exact TauComplex.equiv_trans h_distrib h_ih

/-- Helper: pointwise mul-comm lifts through sum.
    `sum (fun i => (f i).mul z) n ≈ sum (fun i => z.mul (f i)) n`. -/
private theorem TauComplex.sum_mul_swap (f : Nat → TauComplex) (z : TauComplex) (n : Nat) :
    (TauComplex.sum (fun i => (f i).mul z) n).equiv
      (TauComplex.sum (fun i => z.mul (f i)) n) := by
  induction n with
  | zero => exact TauComplex.equiv_refl _
  | succ n ih =>
    show ((TauComplex.sum (fun i => (f i).mul z) n).add ((f n).mul z)).equiv
          ((TauComplex.sum (fun i => z.mul (f i)) n).add (z.mul (f n)))
    exact TauComplex.equiv_add_congr ih (taucomplex_mul_comm (f n) z)

/-- **Sum-mul-distributivity (left)**: `z · (sum f n) ≈ sum (fun i => z·(f i)) n`.

    Derived from the right version via `taucomplex_mul_comm`. -/
theorem TauComplex.sum_mul_distrib_left
    (z : TauComplex) (f : Nat → TauComplex) (n : Nat) :
    (z.mul (TauComplex.sum f n)).equiv (TauComplex.sum (fun i => z.mul (f i)) n) := by
  have h_comm : (z.mul (TauComplex.sum f n)).equiv ((TauComplex.sum f n).mul z) :=
    taucomplex_mul_comm z (TauComplex.sum f n)
  have h_distrib : ((TauComplex.sum f n).mul z).equiv
                    (TauComplex.sum (fun i => (f i).mul z) n) :=
    TauComplex.sum_mul_distrib_right f z n
  have h_swap : (TauComplex.sum (fun i => (f i).mul z) n).equiv
                  (TauComplex.sum (fun i => z.mul (f i)) n) :=
    TauComplex.sum_mul_swap f z n
  exact TauComplex.equiv_trans (TauComplex.equiv_trans h_comm h_distrib) h_swap

-- ============================================================
-- PART 16: PHASE 3C PART 3b''''' — Bound-compounding named targets
-- ============================================================

/-! ## Phase 3C Part 3b''''' deliverables — bound-compounding targets

The binomial theorem's inductive step (Part 3b'''''') needs to apply
`TauComplex.equiv_mul_congr`, which requires `BoundedBy` hypotheses
on the factors. As we induct over `pow z k`, the bound compounds:

* Multiplication: `BoundedBy z M ∧ BoundedBy w M ⟹ BoundedBy (z·w) (2·M·M)`.
* Power (inductive): `BoundedBy z M ⟹ BoundedBy (pow z k) ((2M)^k)` (rough bound).

Component-level reasoning: each component of `z·w` is a sum/difference
of products of bounded components, with the factor of 2 coming from
triangle inequality on the sum.

This commit ships the **named-target propositions** for bound
compounding. Part 3b'''''' (next) will discharge them with the
component-level abs-arithmetic + induction. The actual proofs require
careful TauReal-level unfolding (TauReal.sub ↦ add + negate,
TauReal.mul componentwise) which deserves its own focused session.
-/

/-- **[I.D-TauComplex-MulBoundCompounds-Target]** Named target for
    multiplication bound compounding. -/
def TauComplex.mul_BoundedBy_compounds_target : Prop :=
  ∀ (z w : TauComplex) (M : Nat),
    1 ≤ M → TauComplex.BoundedBy z M → TauComplex.BoundedBy w M →
    TauComplex.BoundedBy (z.mul w) (2 * M * M)

/-- **[I.D-TauComplex-PowBoundCompounds-Target]** Named target for
    pow bound compounding. -/
def TauComplex.pow_BoundedBy_compounds_target : Prop :=
  ∀ (z : TauComplex) (M : Nat) (k : Nat),
    1 ≤ M → TauComplex.BoundedBy z M →
    ∃ Bk : Nat, 1 ≤ Bk ∧ TauComplex.BoundedBy (TauComplex.pow z k) Bk

-- ============================================================
-- PART 17: PHASE 3C PART 3b'''''' — Discharge bound-compounding targets
-- ============================================================

/-- Helper: a fully-unfolded form of `(z.mul w).re.approx n .toRat`. -/
private theorem TauComplex.mul_re_approx_toRat (z w : TauComplex) (n : Nat) :
    (((z.mul w).re).approx n).toRat
      = (z.re.approx n).toRat * (w.re.approx n).toRat
        - (z.im.approx n).toRat * (w.im.approx n).toRat := by
  -- (z.mul w).re = (z.re.mul w.re).sub (z.im.mul w.im)
  -- TauReal.sub a b = a.add b.negate
  -- (.add x y).approx n = (x.approx n).add (y.approx n)
  -- (.negate x).approx n = (x.approx n).negate
  -- toRat_add, toRat_mul, toRat_negate close it.
  show ((((z.re.mul w.re).add (z.im.mul w.im).negate)).approx n).toRat
        = (z.re.approx n).toRat * (w.re.approx n).toRat
          - (z.im.approx n).toRat * (w.im.approx n).toRat
  show (((z.re.mul w.re).approx n).add (((z.im.mul w.im).negate).approx n)).toRat
        = (z.re.approx n).toRat * (w.re.approx n).toRat
          - (z.im.approx n).toRat * (w.im.approx n).toRat
  rw [toRat_add]
  show ((z.re.mul w.re).approx n).toRat + (((z.im.mul w.im).negate).approx n).toRat
        = (z.re.approx n).toRat * (w.re.approx n).toRat
          - (z.im.approx n).toRat * (w.im.approx n).toRat
  show ((z.re.mul w.re).approx n).toRat + (((z.im.mul w.im).approx n).negate).toRat
        = (z.re.approx n).toRat * (w.re.approx n).toRat
          - (z.im.approx n).toRat * (w.im.approx n).toRat
  rw [toRat_negate]
  show ((z.re.mul w.re).approx n).toRat + (- ((z.im.mul w.im).approx n).toRat)
        = (z.re.approx n).toRat * (w.re.approx n).toRat
          - (z.im.approx n).toRat * (w.im.approx n).toRat
  show (((z.re.approx n).mul (w.re.approx n))).toRat
        + (- (((z.im.approx n).mul (w.im.approx n))).toRat)
        = (z.re.approx n).toRat * (w.re.approx n).toRat
          - (z.im.approx n).toRat * (w.im.approx n).toRat
  rw [toRat_mul, toRat_mul]
  ring

/-- Helper: a fully-unfolded form of `(z.mul w).im.approx n .toRat`. -/
private theorem TauComplex.mul_im_approx_toRat (z w : TauComplex) (n : Nat) :
    (((z.mul w).im).approx n).toRat
      = (z.re.approx n).toRat * (w.im.approx n).toRat
        + (z.im.approx n).toRat * (w.re.approx n).toRat := by
  show (((z.re.mul w.im).approx n).add ((z.im.mul w.re).approx n)).toRat
        = (z.re.approx n).toRat * (w.im.approx n).toRat
          + (z.im.approx n).toRat * (w.re.approx n).toRat
  rw [toRat_add]
  show ((z.re.mul w.im).approx n).toRat + ((z.im.mul w.re).approx n).toRat
        = (z.re.approx n).toRat * (w.im.approx n).toRat
          + (z.im.approx n).toRat * (w.re.approx n).toRat
  show (((z.re.approx n).mul (w.im.approx n))).toRat
        + (((z.im.approx n).mul (w.re.approx n))).toRat
        = (z.re.approx n).toRat * (w.im.approx n).toRat
          + (z.im.approx n).toRat * (w.re.approx n).toRat
  rw [toRat_mul, toRat_mul]

/-- **Mul-bound compounding** (discharge of `mul_BoundedBy_compounds_target`):
    if `BoundedBy z M` and `BoundedBy w M` with `1 ≤ M`, then
    `BoundedBy (z·w) (2·M·M)`. -/
theorem TauComplex.mul_BoundedBy_compounds (z w : TauComplex) (M : Nat) (hM : 1 ≤ M)
    (h_bound_z : TauComplex.BoundedBy z M) (h_bound_w : TauComplex.BoundedBy w M) :
    TauComplex.BoundedBy (z.mul w) (2 * M * M) := by
  refine ⟨?_, ?_⟩
  · -- Real part: |(z·w).re| ≤ |z.re·w.re| + |z.im·w.im| ≤ M² + M² = 2M².
    intro n
    have h_zr := h_bound_z.1 n
    have h_zi := h_bound_z.2 n
    have h_wr := h_bound_w.1 n
    have h_wi := h_bound_w.2 n
    rw [TauRat.toRat_abs] at h_zr h_zi h_wr h_wi
    rw [TauRat.toRat_abs]
    rw [TauComplex.mul_re_approx_toRat]
    have h_tri :
        |(z.re.approx n).toRat * (w.re.approx n).toRat
          - (z.im.approx n).toRat * (w.im.approx n).toRat|
        ≤ |(z.re.approx n).toRat * (w.re.approx n).toRat|
          + |(z.im.approx n).toRat * (w.im.approx n).toRat| := abs_sub _ _
    have hM_nn : (0 : Rat) ≤ (M : Rat) := by exact_mod_cast Nat.zero_le M
    have h_pre : |(z.re.approx n).toRat * (w.re.approx n).toRat|
                  ≤ (M : Rat) * (M : Rat) := by
      rw [abs_mul]
      exact mul_le_mul h_zr h_wr (abs_nonneg _) hM_nn
    have h_pim : |(z.im.approx n).toRat * (w.im.approx n).toRat|
                  ≤ (M : Rat) * (M : Rat) := by
      rw [abs_mul]
      exact mul_le_mul h_zi h_wi (abs_nonneg _) hM_nn
    have h_cast : ((2 * M * M : Nat) : Rat) = 2 * (M : Rat) * (M : Rat) := by
      push_cast; ring
    rw [h_cast]
    linarith
  · -- Imag part: |(z·w).im| ≤ |z.re·w.im| + |z.im·w.re| ≤ M² + M² = 2M².
    intro n
    have h_zr := h_bound_z.1 n
    have h_zi := h_bound_z.2 n
    have h_wr := h_bound_w.1 n
    have h_wi := h_bound_w.2 n
    rw [TauRat.toRat_abs] at h_zr h_zi h_wr h_wi
    rw [TauRat.toRat_abs]
    rw [TauComplex.mul_im_approx_toRat]
    have h_tri :
        |(z.re.approx n).toRat * (w.im.approx n).toRat
          + (z.im.approx n).toRat * (w.re.approx n).toRat|
        ≤ |(z.re.approx n).toRat * (w.im.approx n).toRat|
          + |(z.im.approx n).toRat * (w.re.approx n).toRat| := abs_add_le _ _
    have hM_nn : (0 : Rat) ≤ (M : Rat) := by exact_mod_cast Nat.zero_le M
    have h_p1 : |(z.re.approx n).toRat * (w.im.approx n).toRat|
                  ≤ (M : Rat) * (M : Rat) := by
      rw [abs_mul]
      exact mul_le_mul h_zr h_wi (abs_nonneg _) hM_nn
    have h_p2 : |(z.im.approx n).toRat * (w.re.approx n).toRat|
                  ≤ (M : Rat) * (M : Rat) := by
      rw [abs_mul]
      exact mul_le_mul h_zi h_wr (abs_nonneg _) hM_nn
    have h_cast : ((2 * M * M : Nat) : Rat) = 2 * (M : Rat) * (M : Rat) := by
      push_cast; ring
    rw [h_cast]
    linarith

/-- **Mul-bound compounding target discharged.** -/
theorem TauComplex.mul_BoundedBy_compounds_target_discharged :
    TauComplex.mul_BoundedBy_compounds_target :=
  fun z w M hM h_z h_w => TauComplex.mul_BoundedBy_compounds z w M hM h_z h_w

-- ============================================================
-- PART 18: PHASE 3C PART 3b''''''' — pow_BoundedBy_compounds + equiv_pow_congr
-- ============================================================

/-! ## Phase 3C Part 3b''''''' deliverables — pow congruence with bound tracking

With `mul_BoundedBy_compounds` discharged (Part 3b'''''', commit `72d0501`),
this part ships:

* **`TauComplex.one_BoundedBy_one`** — base case bound for `pow z 0 =
  TauComplex.one`.
* **`TauComplex.BoundedBy_mono`** — monotonicity of `BoundedBy` in the
  bound (used to bump bounds to a common `max`).
* **`TauComplex.pow_BoundedBy_compounds`** — discharge of
  `pow_BoundedBy_compounds_target` by induction on `k`, using
  `mul_BoundedBy_compounds` and bound bumping.
* **`TauComplex.equiv_pow_congr_strong`** — pow congruence theorem with
  bounds on BOTH `z` and `z'`. By induction on `k` using
  `equiv_mul_congr` + `pow_BoundedBy_compounds`.

### Why the strengthened form

`TauComplex.equiv_mul_congr` (Part 3b') requires bounds on:
* `z'` (rhs of the first equiv).
* `w` (lhs of the second equiv).

In the pow induction at `k → k+1`, the application of `equiv_mul_congr` to:
* `z := pow z k`, `z' := pow z' k`, `w := z`, `w' := z'`
* hypotheses: `IH : pow z k ≈ pow z' k`, `h_zz : z ≈ z'`

needs:
* bound on `z' = pow z' k` ✓ — from `pow_BoundedBy_compounds` at `z'`.
* bound on `w = z` ✗ — NOT provided by the named target (which only
  gives `BoundedBy z' M`).

`BoundedBy` is a pointwise predicate (at every `n`), and an equivalence
`z ≈ z'` together with `BoundedBy z' M` does NOT imply `BoundedBy z N`
for any fixed `N` — equivalent Cauchy sequences can have arbitrary
pointwise values (only the differences tend to 0). Transferring the
bound would require a "Cauchy bound transfer" lemma that finds an `N₀`
beyond which `z` is bounded by `M+1`, and rephrases the equiv at the
tail. That lemma is non-trivial and is deferred.

The **strengthened form** with bounds on both `z` and `z'` is what the
binomial theorem (Part 3b'''''''', queued) actually consumes. The named
target `equiv_pow_congr_target` remains queued for a later session.

### The named-target + later-discharge pattern (applied)

Per `atlas/insights/2026-05-14-named-target-discharge-pattern.md`, when
mid-discharge a proof reveals depth not anticipated at the
named-target-shipping commit, the disciplined response is to ship the
strengthened-discharge AND keep the original named target queued. This
preserves trust budget (no sorry-laundering) while still delivering the
practically-useful form.
-/

/-- **TauComplex.one bounded by 1.**

    Componentwise: `TauComplex.one.re = TauReal.one` (bounded by 1 trivially)
    and `TauComplex.one.im = TauReal.zero` (bounded by 0 ≤ 1). -/
theorem TauComplex.one_BoundedBy_one : TauComplex.BoundedBy TauComplex.one 1 := by
  refine ⟨?_, ?_⟩
  · -- Real part: |TauRat.one| = 1 ≤ 1.
    intro n
    show (TauRat.one.abs).toRat ≤ ((1 : Nat) : Rat)
    rw [TauRat.toRat_abs, toRat_one]
    norm_num
  · -- Imag part: |TauRat.zero| = 0 ≤ 1.
    intro n
    show (TauRat.zero.abs).toRat ≤ ((1 : Nat) : Rat)
    rw [TauRat.toRat_abs, toRat_zero]
    norm_num

/-- **Monotonicity of `BoundedBy`**: if `BoundedBy z M` and `M ≤ N`,
    then `BoundedBy z N`.

    Used in the pow induction to bring `pow z k` and `z` to a common
    bound `max Bk M` before applying `mul_BoundedBy_compounds`. -/
theorem TauComplex.BoundedBy_mono {z : TauComplex} {M N : Nat} (h : M ≤ N)
    (h_bound : TauComplex.BoundedBy z M) :
    TauComplex.BoundedBy z N := by
  have hMN : ((M : Nat) : Rat) ≤ ((N : Nat) : Rat) := by exact_mod_cast h
  refine ⟨?_, ?_⟩
  · intro n; exact le_trans (h_bound.1 n) hMN
  · intro n; exact le_trans (h_bound.2 n) hMN

/-- **Pow-bound compounding** (discharge of `pow_BoundedBy_compounds_target`):
    if `BoundedBy z M` and `1 ≤ M`, then for every `k`, there exists
    `Bk` with `1 ≤ Bk` and `BoundedBy (pow z k) Bk`.

    Proof: induction on `k`.
    * Base `k = 0`: `pow z 0 = TauComplex.one`, bounded by 1.
    * Step `k → k+1`: by IH, `BoundedBy (pow z k) Bk`. Set `N := max Bk M`,
      bump both `pow z k` and `z` to bound `N` via `BoundedBy_mono`, then
      apply `mul_BoundedBy_compounds` to get bound `2·N·N` on
      `(pow z k).mul z = pow z (k+1)`. -/
theorem TauComplex.pow_BoundedBy_compounds (z : TauComplex) (M : Nat) (k : Nat)
    (hM : 1 ≤ M) (h_bound : TauComplex.BoundedBy z M) :
    ∃ Bk : Nat, 1 ≤ Bk ∧ TauComplex.BoundedBy (TauComplex.pow z k) Bk := by
  induction k with
  | zero =>
    -- pow z 0 = TauComplex.one, bounded by 1.
    exact ⟨1, le_refl 1, TauComplex.one_BoundedBy_one⟩
  | succ k ih =>
    obtain ⟨Bk, hBk_pos, h_pow⟩ := ih
    -- Common bound N = max Bk M, then bump both factors.
    let N : Nat := max Bk M
    have hN_pos : 1 ≤ N := Nat.le_trans hBk_pos (Nat.le_max_left Bk M)
    have h_pow_N : TauComplex.BoundedBy (TauComplex.pow z k) N :=
      TauComplex.BoundedBy_mono (Nat.le_max_left Bk M) h_pow
    have h_z_N : TauComplex.BoundedBy z N :=
      TauComplex.BoundedBy_mono (Nat.le_max_right Bk M) h_bound
    -- mul_BoundedBy_compounds: bound on (pow z k).mul z = pow z (k+1).
    have h_mul := TauComplex.mul_BoundedBy_compounds (TauComplex.pow z k) z N hN_pos h_pow_N h_z_N
    -- 1 ≤ 2*N*N since N ≥ 1.
    have hMul_pos : 1 ≤ 2 * N * N := by
      have hN0 : 0 < N := hN_pos
      have h2N : 0 < 2 * N := by omega
      have : 0 < 2 * N * N := Nat.mul_pos h2N hN0
      omega
    exact ⟨2 * N * N, hMul_pos, h_mul⟩

/-- **Pow-bound compounding target discharged.** -/
theorem TauComplex.pow_BoundedBy_compounds_target_discharged :
    TauComplex.pow_BoundedBy_compounds_target :=
  fun z M k hM h_z => TauComplex.pow_BoundedBy_compounds z M k hM h_z

/-- **Strengthened pow congruence** (with bounds on BOTH `z` and `z'`):
    if `z ≈ z'` with `BoundedBy z M` and `BoundedBy z' M`, then
    `pow z k ≈ pow z' k` for all `k`.

    Proof: induction on `k`.
    * Base `k = 0`: both sides are `TauComplex.one`, reflexive.
    * Step `k → k+1`:
        - IH: `pow z k ≈ pow z' k`.
        - `pow_BoundedBy_compounds` on `z'` gives bound `Bk'` on `pow z' k`.
        - Set common bound `N := max Bk' M`, bump `pow z' k` and `z` to `N`.
        - Apply `equiv_mul_congr` with `(z := pow z k, z' := pow z' k,
          w := z, w' := z')` using IH and `h_zz`.

    The named target `equiv_pow_congr_target` (which requires bound on
    `z'` only) is NOT discharged here — it requires a Cauchy-bound-
    transfer argument that we defer to a later session. The strengthened
    form is what the binomial theorem (Part 3b'''''''' next) actually
    consumes. -/
theorem TauComplex.equiv_pow_congr_strong (z z' : TauComplex) (h_zz : z.equiv z')
    (M : Nat) (hM : 1 ≤ M)
    (h_bound_z : TauComplex.BoundedBy z M)
    (h_bound_z' : TauComplex.BoundedBy z' M) (k : Nat) :
    (TauComplex.pow z k).equiv (TauComplex.pow z' k) := by
  induction k with
  | zero =>
    -- pow z 0 = TauComplex.one = pow z' 0, reflexive.
    show TauComplex.one.equiv TauComplex.one
    exact TauComplex.equiv_refl TauComplex.one
  | succ k ih =>
    -- pow z (k+1) = (pow z k).mul z, pow z' (k+1) = (pow z' k).mul z'.
    show ((TauComplex.pow z k).mul z).equiv ((TauComplex.pow z' k).mul z')
    -- Bound on pow z' k via pow_BoundedBy_compounds at z'.
    obtain ⟨Bk', hBk'_pos, h_pow_z'⟩ :=
      TauComplex.pow_BoundedBy_compounds z' M k hM h_bound_z'
    -- Common bound N = max Bk' M for the multiplication step.
    let N : Nat := max Bk' M
    have hN_pos : 1 ≤ N := Nat.le_trans hBk'_pos (Nat.le_max_left Bk' M)
    have h_pow_z'_N : TauComplex.BoundedBy (TauComplex.pow z' k) N :=
      TauComplex.BoundedBy_mono (Nat.le_max_left Bk' M) h_pow_z'
    have h_z_N : TauComplex.BoundedBy z N :=
      TauComplex.BoundedBy_mono (Nat.le_max_right Bk' M) h_bound_z
    -- Apply equiv_mul_congr: bound on z' = pow z' k ✓, bound on w = z ✓.
    exact TauComplex.equiv_mul_congr (z := TauComplex.pow z k)
            (z' := TauComplex.pow z' k) (w := z) (w' := z')
            N N hN_pos hN_pos
            h_pow_z'_N.1 h_pow_z'_N.2 h_z_N.1 h_z_N.2 ih h_zz

-- ============================================================
-- PART 19: PHASE 3C PART 3b'''''''' — Helpers for binomial theorem
-- ============================================================

/-! ## Phase 3C Part 3b'''''''' deliverables — binomial-theorem helpers

The binomial theorem on TauComplex (`add_pow_equiv_target`, shipped at
`60c1bff`) requires substantial scaffolding. This commit ships the
**bound-free structural helpers** needed by the discharge:

* **`taucomplex_mul_left_comm`** — unconditional `a·(b·c) ≈ b·(a·c)`.
  Proved pointwise at TauRat level (the same way `taucomplex_mul_comm`
  and `taucomplex_left_distrib` are proved). This is the key
  bound-free reorganization tool for triple products.
* **`TauComplex.sum_equiv_congr`** — if `f i ≈ g i` for all i, then
  `sum f n ≈ sum g n`. Foundational for lifting term-level equivs to
  sum-level.
* **`TauComplex.sum_add_split`** — `sum (fun i => (f i).add (g i)) n ≈
  (sum f n).add (sum g n)`. Lets us split a sum of sums-of-pairs into
  a pair of sums.
* **`TauComplex.sum_split_first`** — `sum f (n+1) ≈ f 0 + sum (fun i =>
  f (i+1)) n`. Lets us peel off the first term from a sum (mirror
  of the definitional `sum_succ` which peels the last term).

### Why these are bound-free

All four lemmas use only:
* Componentwise pointwise reduction at the TauRat level (closed by
  `ring` after unfolding) — for `mul_left_comm`.
* `equiv_add_congr` (unconditional — addition respects equiv without
  bounds) + `equiv_refl` + `equiv_trans` — for the sum-level lemmas.

This is critical: the binomial inductive step needs to reorganize
triple products like `(c · z₁^i · z₂^(n-i)) · z₁ → c · z₁^(i+1) · z₂^(n-i)`
without bound bookkeeping on every assoc/comm step. The bound is then
only needed at the **outermost** IH-substitution step (where
`equiv_mul_congr` lifts `pow (z₁+z₂) n ≈ B(n)` into the product
`(pow (z₁+z₂) n) · (z₁+z₂) ≈ B(n) · (z₁+z₂)`).

### What Part 3b''''''''' (next) will use these for

The discharge of `add_pow_equiv_target` (in strengthened form with
bounds on z₁ and z₂):

1. **Term identities** via `mul_left_comm` + `mul_assoc` chains:
   `(c · z₁^i · z₂^(n-i)) · z₁ ≈ c · z₁^(i+1) · z₂^(n-i)`.
2. **Lift to sum level** via `sum_equiv_congr` from term identity.
3. **Split B(n) · (z₁+z₂)** via `taucomplex_left_distrib` →
   `B(n) · z₁ + B(n) · z₂` → via `sum_mul_distrib_right` → two sums.
4. **Combine into B(n+1)** via `sum_split_first` (peel off i=0) +
   `sum_succ` (peel off i=n+1) + Pascal's rule on the middle range.
-/

/-- **TauComplex mul-left-comm** (unconditional ring identity):
    `a · (b · c) ≈ b · (a · c)`.

    Proved by componentwise pointwise reduction at the TauRat level
    using `ring`. Used in Part 3b''''''''' for triple-product
    reorganization in the binomial inductive step. -/
theorem taucomplex_mul_left_comm (a b c : TauComplex) :
    (a.mul (b.mul c)).equiv (b.mul (a.mul c)) := by
  refine ⟨?_, ?_⟩
  · -- Real part
    apply TauReal.equiv_of_pointwise
    intro n
    simp only [TauComplex.mul, TauReal.sub, TauReal.add, TauReal.mul, TauReal.negate]
    simp only [TauRat.equiv, TauRat.add, TauRat.mul, TauRat.negate]
    try rw [equiv_iff_toInt_eq]
    try simp only [toInt_add, toInt_mul, toInt_negate, toInt_fromNat, toInt_zero, toInt_one]
    try push_cast
    try ring
  · -- Imag part
    apply TauReal.equiv_of_pointwise
    intro n
    simp only [TauComplex.mul, TauReal.sub, TauReal.add, TauReal.mul, TauReal.negate]
    simp only [TauRat.equiv, TauRat.add, TauRat.mul, TauRat.negate]
    try rw [equiv_iff_toInt_eq]
    try simp only [toInt_add, toInt_mul, toInt_negate, toInt_fromNat, toInt_zero, toInt_one]
    try push_cast
    try ring

/-- **Sum-equiv-congr**: if `f i ≈ g i` for all `i`, then
    `sum f n ≈ sum g n`.

    Used to lift term-level equivalences (e.g.,
    `(c · z₁^i · z₂^(n-i)) · z₁ ≈ c · z₁^(i+1) · z₂^(n-i)`) to
    sum-level equivalences. -/
theorem TauComplex.sum_equiv_congr (f g : Nat → TauComplex) (n : Nat)
    (h : ∀ i, (f i).equiv (g i)) :
    (TauComplex.sum f n).equiv (TauComplex.sum g n) := by
  induction n with
  | zero => exact TauComplex.equiv_refl _
  | succ n ih =>
    show ((TauComplex.sum f n).add (f n)).equiv ((TauComplex.sum g n).add (g n))
    exact TauComplex.equiv_add_congr ih (h n)

/-- **Sum-add-split**: `sum (fun i => (f i).add (g i)) n ≈
    (sum f n).add (sum g n)`.

    Used to split a sum-of-pairs into a pair-of-sums. In the binomial
    step, this lets us turn `sum (fun i => left_term i + right_term i)`
    into `sum left_term + sum right_term`. -/
theorem TauComplex.sum_add_split (f g : Nat → TauComplex) (n : Nat) :
    (TauComplex.sum (fun i => (f i).add (g i)) n).equiv
      ((TauComplex.sum f n).add (TauComplex.sum g n)) := by
  induction n with
  | zero =>
    -- sum _ 0 = zero; RHS = zero.add zero ≈ zero.
    show TauComplex.zero.equiv (TauComplex.zero.add TauComplex.zero)
    exact TauComplex.equiv_symm (TauComplex.zero_add_equiv TauComplex.zero)
  | succ n ih =>
    -- LHS = sum _ n + (f n + g n)
    -- RHS = (sum f n + sum g n) + (f n + g n) — by sum_succ on each
    --     = (sum f n + f n) + (sum g n + g n) after rearrangement
    show ((TauComplex.sum (fun i => (f i).add (g i)) n).add ((f n).add (g n))).equiv
          (((TauComplex.sum f n).add (f n)).add ((TauComplex.sum g n).add (g n)))
    -- Strategy:
    --   LHS ≈ [by ih] (sum f n + sum g n) + (f n + g n)
    --       ≈ [add reorg] (sum f n + f n) + (sum g n + g n)
    -- The "add reorg" is a pure ring identity, proved pointwise.
    have h_ih_lift :
        ((TauComplex.sum (fun i => (f i).add (g i)) n).add ((f n).add (g n))).equiv
        (((TauComplex.sum f n).add (TauComplex.sum g n)).add ((f n).add (g n))) :=
      TauComplex.equiv_add_congr ih (TauComplex.equiv_refl _)
    -- Pure add reorganization: (A + B) + (X + Y) ≈ (A + X) + (B + Y).
    have h_reorg :
        (((TauComplex.sum f n).add (TauComplex.sum g n)).add ((f n).add (g n))).equiv
        (((TauComplex.sum f n).add (f n)).add ((TauComplex.sum g n).add (g n))) := by
      -- Componentwise pointwise reduction.
      refine ⟨?_, ?_⟩
      · apply TauReal.equiv_of_pointwise
        intro k
        simp only [TauComplex.add, TauReal.add]
        simp only [TauRat.equiv, TauRat.add]
        try rw [equiv_iff_toInt_eq]
        try simp only [toInt_add, toInt_mul, toInt_fromNat, toInt_zero, toInt_one]
        try push_cast
        try ring
      · apply TauReal.equiv_of_pointwise
        intro k
        simp only [TauComplex.add, TauReal.add]
        simp only [TauRat.equiv, TauRat.add]
        try rw [equiv_iff_toInt_eq]
        try simp only [toInt_add, toInt_mul, toInt_fromNat, toInt_zero, toInt_one]
        try push_cast
        try ring
    exact TauComplex.equiv_trans h_ih_lift h_reorg

/-- **Sum-split-first**: `sum f (n+1) ≈ f 0 + sum (fun i => f (i+1)) n`.

    Peels off the FIRST term of a sum (mirror of `sum_succ` which peels
    the last). Used in Part 3b''''''''' to reindex the binomial sum
    `S_{n+1} = sum (...) (n+2)` for matching against `Σ_left + Σ_right`. -/
theorem TauComplex.sum_split_first (f : Nat → TauComplex) (n : Nat) :
    (TauComplex.sum f (n + 1)).equiv ((f 0).add (TauComplex.sum (fun i => f (i+1)) n)) := by
  induction n with
  | zero =>
    -- sum f 1 = zero.add (f 0)
    -- RHS = (f 0).add zero
    show (TauComplex.zero.add (f 0)).equiv ((f 0).add TauComplex.zero)
    exact taucomplex_add_comm TauComplex.zero (f 0)
  | succ n ih =>
    -- LHS = sum f (n+2) = (sum f (n+1)).add (f (n+1))
    --     ≈ [by ih on inner] (f 0 + sum (i+1) n).add (f (n+1))
    --     ≈ [by add_assoc] f 0 + (sum (i+1) n + f (n+1))
    --     = f 0 + sum (i+1) (n+1)  [definitional sum_succ]
    show ((TauComplex.sum f (n+1)).add (f (n+1))).equiv
          ((f 0).add ((TauComplex.sum (fun i => f (i+1)) n).add (f (n+1))))
    have h_ih_lift :
        ((TauComplex.sum f (n+1)).add (f (n+1))).equiv
        (((f 0).add (TauComplex.sum (fun i => f (i+1)) n)).add (f (n+1))) :=
      TauComplex.equiv_add_congr ih (TauComplex.equiv_refl _)
    have h_assoc :
        (((f 0).add (TauComplex.sum (fun i => f (i+1)) n)).add (f (n+1))).equiv
        ((f 0).add ((TauComplex.sum (fun i => f (i+1)) n).add (f (n+1)))) :=
      taucomplex_add_assoc (f 0) (TauComplex.sum (fun i => f (i+1)) n) (f (n+1))
    exact TauComplex.equiv_trans h_ih_lift h_assoc

-- ============================================================
-- PART 20: PHASE 3C PART 3b''''''''' — Bound infrastructure + ring helpers
-- ============================================================

/-! ## Phase 3C Part 3b''''''''' deliverables — IH-substitution + ring helpers

This commit ships the **bound-tracking infrastructure** and **ring-
identity helpers** that the binomial inductive step (Part 3b'''''''''',
next) will consume. Three load-bearing pieces:

### Deliverables

* `TauComplex.add_BoundedBy_compounds` — `BoundedBy z₁ M + BoundedBy z₂ M
  ⟹ BoundedBy (z₁+z₂) (2M)`. Used for the OUTERMOST IH-substitution in
  the binomial induction (where the substitution requires a bound on
  the `(z₁+z₂)` factor).

* `TauComplex.mul_respects_equiv_right_of_bound` — componentwise lift of
  the TauReal version. Requires bound on `w` only (NOT on `z'`,
  unlike the general `equiv_mul_congr`). Used at the OUTERMOST IH-
  substitution step to substitute `pow (z₁+z₂) n ≈ B(n)` into the
  product `_ · (z₁+z₂)`. Bound bookkeeping is minimal: only the bound
  on `(z₁+z₂)` matters, derived via `add_BoundedBy_compounds`.

* `TauComplex.mul_reassoc_right` — 4-variable identity `((c·a)·b)·x ≈
  (c·(a·x))·b`. The natural `ring`-based proof (pointwise reduction)
  TIMES OUT on whnf for this 4-variable identity (8 TauRat re/im
  variables; the expression tree explodes). Instead, this proof chains
  through bound-free outer-level identities (`mul_assoc`, `mul_left_comm`,
  `mul_comm`) and ONE bounded substitution at the end via
  `mul_respects_equiv_right_of_bound`. The bound is on `b` only.

### Why this is foundational

These three lemmas are the **load-bearing equiv-substitution tools**
for the binomial induction:
* `mul_respects_equiv_right_of_bound` handles the outer IH substitution.
* `mul_reassoc_right` will handle term-level reorganization.
* `add_BoundedBy_compounds` provides the bound on `(z₁+z₂)`.

The term-level identities AND the sum decomposition `B(n)·(z₁+z₂) ≈
Σ_left + Σ_right` were ATTEMPTED in this part but hit a **parenthesization
mismatch timeout**: `B(n)` in the named target uses right-assoc inner
`c · (X · Y)`, while `mul_reassoc_right`'s natural shape is left-assoc
`(c · X) · Y`. The whnf cost of bridging these in unification was
prohibitive. The disciplined response: ship the bound-tracking + ring-
identity foundations, defer parenthesization-sensitive work to Part
3b''''''''''.
-/

/-- **TauComplex addition bound compounding**: if `BoundedBy z₁ M` and
    `BoundedBy z₂ M`, then `BoundedBy (z₁+z₂) (2M)`.

    Componentwise via triangle inequality (`abs_add_le`):
    `|z₁.re + z₂.re| ≤ |z₁.re| + |z₂.re| ≤ M + M = 2M`. Same for im. -/
theorem TauComplex.add_BoundedBy_compounds (z₁ z₂ : TauComplex) (M : Nat)
    (h₁ : TauComplex.BoundedBy z₁ M) (h₂ : TauComplex.BoundedBy z₂ M) :
    TauComplex.BoundedBy (z₁.add z₂) (2 * M) := by
  refine ⟨?_, ?_⟩
  · intro n
    show ((z₁.re.approx n).add (z₂.re.approx n)).abs.toRat ≤ ((2*M : Nat) : Rat)
    have h_tri : (((z₁.re.approx n).add (z₂.re.approx n)).abs).toRat
                  ≤ ((z₁.re.approx n).abs).toRat + ((z₂.re.approx n).abs).toRat := by
      rw [TauRat.toRat_abs, TauRat.toRat_abs, TauRat.toRat_abs, toRat_add]
      exact abs_add_le _ _
    have h_cast : ((2*M : Nat) : Rat) = 2 * (M : Rat) := by push_cast; ring
    rw [h_cast]
    linarith [h₁.1 n, h₂.1 n]
  · intro n
    show ((z₁.im.approx n).add (z₂.im.approx n)).abs.toRat ≤ ((2*M : Nat) : Rat)
    have h_tri : (((z₁.im.approx n).add (z₂.im.approx n)).abs).toRat
                  ≤ ((z₁.im.approx n).abs).toRat + ((z₂.im.approx n).abs).toRat := by
      rw [TauRat.toRat_abs, TauRat.toRat_abs, TauRat.toRat_abs, toRat_add]
      exact abs_add_le _ _
    have h_cast : ((2*M : Nat) : Rat) = 2 * (M : Rat) := by push_cast; ring
    rw [h_cast]
    linarith [h₁.2 n, h₂.2 n]

/-- **TauComplex mul respects equiv on the LEFT with bound on the RIGHT**:
    if `z ≈ z'` and `BoundedBy w M`, then `z.mul w ≈ z'.mul w`.

    Componentwise lift of `TauReal.mul_respects_equiv_right_of_bound`.
    The TauComplex multiplication has the form `(z·w).re = z.re·w.re -
    z.im·w.im` and `(z·w).im = z.re·w.im + z.im·w.re`. Each of the four
    TauReal products is a `mul_respects_equiv_right_of_bound` application
    with the appropriate `w.re` or `w.im` bound. -/
theorem TauComplex.mul_respects_equiv_right_of_bound
    (z z' w : TauComplex) (Mw : Nat) (hM : 1 ≤ Mw)
    (h_bound_w_re : ∀ n, (w.re.approx n).abs.toRat ≤ Mw)
    (h_bound_w_im : ∀ n, (w.im.approx n).abs.toRat ≤ Mw)
    (h : z.equiv z') :
    (z.mul w).equiv (z'.mul w) := by
  refine ⟨?_, ?_⟩
  · -- (z·w).re = z.re·w.re - z.im·w.im
    show ((z.re.mul w.re).sub (z.im.mul w.im)).equiv
          ((z'.re.mul w.re).sub (z'.im.mul w.im))
    apply TauReal.equiv_sub_congr
    · exact TauReal.mul_respects_equiv_right_of_bound z.re z'.re w.re Mw hM h_bound_w_re h.1
    · exact TauReal.mul_respects_equiv_right_of_bound z.im z'.im w.im Mw hM h_bound_w_im h.2
  · -- (z·w).im = z.re·w.im + z.im·w.re
    show ((z.re.mul w.im).add (z.im.mul w.re)).equiv
          ((z'.re.mul w.im).add (z'.im.mul w.re))
    apply TauReal.equiv_add_congr
    · exact TauReal.mul_respects_equiv_right_of_bound z.re z'.re w.im Mw hM h_bound_w_im h.1
    · exact TauReal.mul_respects_equiv_right_of_bound z.im z'.im w.re Mw hM h_bound_w_re h.2

/-- **TauComplex mul reassociation right** (with bound on `b`):
    `((c·a)·b)·x ≈ (c·(a·x))·b`.

    The pure 4-variable ring identity at TauComplex level would expand
    to a polynomial in 8 TauRat variables, which times out `ring`'s
    whnf normalization. Instead, we chain through bound-free
    intermediates and ONE bounded substitution at the end:

    1. `((c·a)·b)·x ≈ (c·a)·(b·x)`  [taucomplex_mul_assoc]
    2. `(c·a)·(b·x) ≈ b·((c·a)·x)`  [taucomplex_mul_left_comm]
    3. `b·((c·a)·x) ≈ ((c·a)·x)·b`  [taucomplex_mul_comm]
    4. `((c·a)·x)·b ≈ (c·(a·x))·b`  [substitute mul_assoc into _·b
       via `mul_respects_equiv_right_of_bound`, needs bound on b]

    The bound is on `b` only — in the binomial application, `b = pow z₂
    (n-i)` which is bounded via `pow_BoundedBy_compounds` from a bound
    on `z₂`. -/
theorem TauComplex.mul_reassoc_right (c a b x : TauComplex) (Mb : Nat) (hMb : 1 ≤ Mb)
    (h_bound_b_re : ∀ n, (b.re.approx n).abs.toRat ≤ Mb)
    (h_bound_b_im : ∀ n, (b.im.approx n).abs.toRat ≤ Mb) :
    (((c.mul a).mul b).mul x).equiv ((c.mul (a.mul x)).mul b) := by
  have h1 : (((c.mul a).mul b).mul x).equiv ((c.mul a).mul (b.mul x)) :=
    taucomplex_mul_assoc (c.mul a) b x
  have h2 : ((c.mul a).mul (b.mul x)).equiv (b.mul ((c.mul a).mul x)) :=
    taucomplex_mul_left_comm (c.mul a) b x
  have h3 : (b.mul ((c.mul a).mul x)).equiv (((c.mul a).mul x).mul b) :=
    taucomplex_mul_comm b ((c.mul a).mul x)
  have h4 : (((c.mul a).mul x).mul b).equiv ((c.mul (a.mul x)).mul b) :=
    TauComplex.mul_respects_equiv_right_of_bound
      ((c.mul a).mul x) (c.mul (a.mul x)) b Mb hMb h_bound_b_re h_bound_b_im
      (taucomplex_mul_assoc c a x)
  exact TauComplex.equiv_trans (TauComplex.equiv_trans (TauComplex.equiv_trans h1 h2) h3) h4

-- ============================================================
-- PART 21: PHASE 3C PART 3b'''''''''' — Term identities + B_left decomposition
-- ============================================================

/-! ## Phase 3C Part 3b'''''''''' deliverables — term identities (left-assoc)

This commit ships the **term-level identities** + **`B_left(n)` sum
decomposition** for the binomial inductive step, using a
**left-associated** internal form to match `mul_reassoc_right`'s
natural shape and avoid the parenthesization mismatch that blocked
Part 3b'''''''''.

### B_left vs B_target

The named target `add_pow_equiv_target` uses RIGHT-associated inner:
  `B_target(n) := sum (fun i => c_i · (z₁^i · z₂^(n-i))) (n+1)`

This commit works with the LEFT-associated form:
  `B_left(n) := sum (fun i => (c_i · z₁^i) · z₂^(n-i)) (n+1)`

The two are equivalent via `taucomplex_mul_assoc` term-wise (`(c·X)·Y ≈
c·(X·Y)`) + `sum_equiv_congr`. The equiv-bridge `B_left(n) ≈ B_target(n)`
will be discharged at the end of the full binomial proof (Part
3b''''''''''').

### Why left-assoc internally

`mul_reassoc_right`'s natural shape is `((c·a)·b)·x ≈ (c·(a·x))·b` —
LEFT-assoc throughout. When we multiply `B_left(n)` by `z₁` on the
right via `sum_mul_distrib_right`, each term becomes `(((c·X)·Y)·z₁)`,
which is EXACTLY `mul_reassoc_right`'s LHS shape. No whnf-explosion
on unification, no inner-associativity gymnastics. Clean.

### Deliverables

* `TauComplex.add_pow_term_left` — `((c · z₁^i) · z₂^(n-i)) · z₁ ≈
  (c · z₁^(i+1)) · z₂^(n-i)`. Via `mul_reassoc_right` with bound on
  `b = pow z₂ (n-i)`.

* `TauComplex.add_pow_term_right` — `((c · z₁^i) · z₂^k) · z₂ ≈
  (c · z₁^i) · z₂^(k+1)`. Via `taucomplex_mul_assoc` (bound-free).

* `TauComplex.B_left_n_mul_z1_eq_left_sum` — `B_left(n) · z₁ ≈ Σ_left`.
  Via `sum_mul_distrib_right` + `sum_equiv_congr` + `add_pow_term_left`.

* `TauComplex.B_left_n_mul_z2_eq_right_sum` — `B_left(n) · z₂ ≈ Σ_right`.
  Via `sum_mul_distrib_right` + `sum_equiv_congr` + `add_pow_term_right`.

* `TauComplex.B_left_n_mul_add_eq_sigmas` — `B_left(n) · (z₁+z₂) ≈
  Σ_left + Σ_right`. Via `taucomplex_left_distrib` + `equiv_add_congr`
  + the two above.

The Pascal combinatorial step `Σ_left + Σ_right ≈ B_left(n+1)` and the
final outer induction + equiv-bridge to `B_target` are queued for
Part 3b''''''''''' (next).
-/

/-- **Binomial-term identity (LEFT factor z₁, left-assoc shape)**:
    `((c · z₁^i) · z₂^(n-i)) · z₁ ≈ (c · z₁^(i+1)) · z₂^(n-i)`.

    Direct application of `mul_reassoc_right` (with bound on
    `b = pow z₂ (n-i)`). The definitional `pow_succ` makes
    `(pow z₁ i).mul z₁ = pow z₁ (i+1)`, so the conclusion of
    `mul_reassoc_right` matches the goal shape after `simp only
    [pow_succ]` rewrites the goal's `pow z₁ (i+1)` to `(pow z₁ i).mul z₁`. -/
theorem TauComplex.add_pow_term_left (c z₁ z₂ : TauComplex) (i n : Nat) (Mb : Nat)
    (hMb : 1 ≤ Mb)
    (h_bound_b_re : ∀ m, ((TauComplex.pow z₂ (n - i)).re.approx m).abs.toRat ≤ Mb)
    (h_bound_b_im : ∀ m, ((TauComplex.pow z₂ (n - i)).im.approx m).abs.toRat ≤ Mb) :
    (((c.mul (TauComplex.pow z₁ i)).mul (TauComplex.pow z₂ (n - i))).mul z₁).equiv
      ((c.mul (TauComplex.pow z₁ (i+1))).mul (TauComplex.pow z₂ (n - i))) := by
  simp only [TauComplex.pow_succ]
  exact TauComplex.mul_reassoc_right c (TauComplex.pow z₁ i) (TauComplex.pow z₂ (n - i)) z₁
    Mb hMb h_bound_b_re h_bound_b_im

/-- **Binomial-term identity (RIGHT factor z₂, left-assoc shape)**:
    `((c · z₁^i) · z₂^k) · z₂ ≈ (c · z₁^i) · z₂^(k+1)`.

    Direct application of `taucomplex_mul_assoc`. The definitional
    `pow_succ` makes `(pow z₂ k).mul z₂ = pow z₂ (k+1)`, so the
    conclusion of `mul_assoc` matches the goal shape after `simp only
    [pow_succ]`. Bound-free. -/
theorem TauComplex.add_pow_term_right (c z₁ z₂ : TauComplex) (i k : Nat) :
    (((c.mul (TauComplex.pow z₁ i)).mul (TauComplex.pow z₂ k)).mul z₂).equiv
      ((c.mul (TauComplex.pow z₁ i)).mul (TauComplex.pow z₂ (k+1))) := by
  simp only [TauComplex.pow_succ]
  exact taucomplex_mul_assoc (c.mul (TauComplex.pow z₁ i)) (TauComplex.pow z₂ k) z₂

/-- **`B_left(n) · z₁ ≈ Σ_left`**: distribute z₁ over the left-assoc
    binomial sum at depth n.

    LHS: `B_left(n) · z₁ = (sum (fun i => (c_i · z₁^i) · z₂^(n-i)) (n+1)) · z₁`.
    RHS: `Σ_left := sum (fun i => (c_i · z₁^(i+1)) · z₂^(n-i)) (n+1)`.

    Chain:
    1. `sum_mul_distrib_right`: lift the `· z₁` inside the sum.
    2. `sum_equiv_congr` + `add_pow_term_left`: rewrite each term. -/
theorem TauComplex.B_left_n_mul_z1_eq_left_sum (z₁ z₂ : TauComplex) (M : Nat) (hM : 1 ≤ M)
    (h_bound_z2 : TauComplex.BoundedBy z₂ M) (n : Nat) :
    ((TauComplex.sum (fun i =>
        ((TauComplex.fromTauReal (TauReal.fromNat (Nat.choose n i))).mul
          (TauComplex.pow z₁ i)).mul (TauComplex.pow z₂ (n - i))) (n+1)).mul z₁).equiv
      (TauComplex.sum (fun i =>
        ((TauComplex.fromTauReal (TauReal.fromNat (Nat.choose n i))).mul
          (TauComplex.pow z₁ (i+1))).mul (TauComplex.pow z₂ (n - i))) (n+1)) := by
  have h1 := TauComplex.sum_mul_distrib_right
    (fun i => ((TauComplex.fromTauReal (TauReal.fromNat (Nat.choose n i))).mul
                (TauComplex.pow z₁ i)).mul (TauComplex.pow z₂ (n - i)))
    z₁ (n+1)
  have h2 : (TauComplex.sum (fun i =>
              (((TauComplex.fromTauReal (TauReal.fromNat (Nat.choose n i))).mul
                (TauComplex.pow z₁ i)).mul (TauComplex.pow z₂ (n - i))).mul z₁) (n+1)).equiv
             (TauComplex.sum (fun i =>
              ((TauComplex.fromTauReal (TauReal.fromNat (Nat.choose n i))).mul
                (TauComplex.pow z₁ (i+1))).mul (TauComplex.pow z₂ (n - i))) (n+1)) := by
    apply TauComplex.sum_equiv_congr
    intro i
    obtain ⟨Bk, hBk_pos, h_bound⟩ :=
      TauComplex.pow_BoundedBy_compounds z₂ M (n - i) hM h_bound_z2
    exact TauComplex.add_pow_term_left
      (TauComplex.fromTauReal (TauReal.fromNat (Nat.choose n i)))
      z₁ z₂ i n Bk hBk_pos h_bound.1 h_bound.2
  exact TauComplex.equiv_trans h1 h2

/-- **`B_left(n) · z₂ ≈ Σ_right`**: distribute z₂ over the left-assoc
    binomial sum at depth n. Bound-free (uses bound-free `add_pow_term_right`).

    LHS: `B_left(n) · z₂ = (sum (fun i => (c_i · z₁^i) · z₂^(n-i)) (n+1)) · z₂`.
    RHS: `Σ_right := sum (fun i => (c_i · z₁^i) · z₂^((n-i)+1)) (n+1)`.

    Note: `(n-i)+1 = n+1-i` for `i ≤ n` (the sum's range). The Pascal
    combinatorial step (Part 3b''''''''''') will use this Nat-arithmetic
    fact to align with `B_left(n+1)`'s `z₂^(n+1-j)` indexing. -/
theorem TauComplex.B_left_n_mul_z2_eq_right_sum (z₁ z₂ : TauComplex) (n : Nat) :
    ((TauComplex.sum (fun i =>
        ((TauComplex.fromTauReal (TauReal.fromNat (Nat.choose n i))).mul
          (TauComplex.pow z₁ i)).mul (TauComplex.pow z₂ (n - i))) (n+1)).mul z₂).equiv
      (TauComplex.sum (fun i =>
        ((TauComplex.fromTauReal (TauReal.fromNat (Nat.choose n i))).mul
          (TauComplex.pow z₁ i)).mul (TauComplex.pow z₂ ((n - i) + 1))) (n+1)) := by
  have h1 := TauComplex.sum_mul_distrib_right
    (fun i => ((TauComplex.fromTauReal (TauReal.fromNat (Nat.choose n i))).mul
                (TauComplex.pow z₁ i)).mul (TauComplex.pow z₂ (n - i)))
    z₂ (n+1)
  have h2 : (TauComplex.sum (fun i =>
              (((TauComplex.fromTauReal (TauReal.fromNat (Nat.choose n i))).mul
                (TauComplex.pow z₁ i)).mul (TauComplex.pow z₂ (n - i))).mul z₂) (n+1)).equiv
             (TauComplex.sum (fun i =>
              ((TauComplex.fromTauReal (TauReal.fromNat (Nat.choose n i))).mul
                (TauComplex.pow z₁ i)).mul (TauComplex.pow z₂ ((n - i) + 1))) (n+1)) := by
    apply TauComplex.sum_equiv_congr
    intro i
    exact TauComplex.add_pow_term_right
      (TauComplex.fromTauReal (TauReal.fromNat (Nat.choose n i)))
      z₁ z₂ i (n - i)
  exact TauComplex.equiv_trans h1 h2

/-- **`B_left(n) · (z₁+z₂) ≈ Σ_left + Σ_right`**: full decomposition of
    the binomial-step LHS in left-assoc form.

    Chain:
    1. `taucomplex_left_distrib`: `B_left(n) · (z₁+z₂) ≈ B_left(n)·z₁
       + B_left(n)·z₂`.
    2. `equiv_add_congr` lifts the two sub-equivs (`B_left_n_mul_z1_eq_left_sum`
       and `B_left_n_mul_z2_eq_right_sum`) to the add level.

    This completes the LEFT HALF of the binomial inductive step. The
    Pascal combinatorial step `Σ_left + Σ_right ≈ B_left(n+1)` is
    queued for Part 3b''''''''''' (next). -/
theorem TauComplex.B_left_n_mul_add_eq_sigmas (z₁ z₂ : TauComplex) (M : Nat) (hM : 1 ≤ M)
    (h_bound_z2 : TauComplex.BoundedBy z₂ M) (n : Nat) :
    ((TauComplex.sum (fun i =>
        ((TauComplex.fromTauReal (TauReal.fromNat (Nat.choose n i))).mul
          (TauComplex.pow z₁ i)).mul (TauComplex.pow z₂ (n - i))) (n+1)).mul
      (z₁.add z₂)).equiv
      ((TauComplex.sum (fun i =>
        ((TauComplex.fromTauReal (TauReal.fromNat (Nat.choose n i))).mul
          (TauComplex.pow z₁ (i+1))).mul (TauComplex.pow z₂ (n - i))) (n+1)).add
       (TauComplex.sum (fun i =>
        ((TauComplex.fromTauReal (TauReal.fromNat (Nat.choose n i))).mul
          (TauComplex.pow z₁ i)).mul (TauComplex.pow z₂ ((n - i) + 1))) (n+1))) := by
  have h1 := taucomplex_left_distrib
    (TauComplex.sum (fun i =>
      ((TauComplex.fromTauReal (TauReal.fromNat (Nat.choose n i))).mul
        (TauComplex.pow z₁ i)).mul (TauComplex.pow z₂ (n - i))) (n+1))
    z₁ z₂
  have h2 := TauComplex.equiv_add_congr
    (TauComplex.B_left_n_mul_z1_eq_left_sum z₁ z₂ M hM h_bound_z2 n)
    (TauComplex.B_left_n_mul_z2_eq_right_sum z₁ z₂ n)
  exact TauComplex.equiv_trans h1 h2

-- ============================================================
-- PART 22: PHASE 3C PART 3b''''''''''' — Pascal preliminaries
-- ============================================================

/-! ## Phase 3C Part 3b''''''''''' deliverables — Pascal-lift lemmas

For the Pascal combinatorial step `Σ_left + Σ_right ≈ B_left(n+1)`
(Part 3b'''''''''''', queued), we need to lift the Nat-level Pascal
identity to TauComplex via the coefficient map `fromTauReal ∘ fromNat`:

  `Nat.choose (n+1) (j+1) = Nat.choose n j + Nat.choose n (j+1)`  [Pascal at Nat]
                          ↓ apply `fromTauReal ∘ fromNat` ↓
  `fromTauReal (fromNat (Nat.choose (n+1) (j+1))) ≈
   fromTauReal (fromNat (Nat.choose n j)) + fromTauReal (fromNat (Nat.choose n (j+1)))`  [Pascal at TauComplex]

This commit ships the **additive distributivity** of `fromTauReal ∘
fromNat` and the **zero-coefficient case** (needed for the boundary
term `c_{n,n+1} = 0` when reindexing Σ_right).

### Deliverables

* `TauComplex.fromTauReal_fromNat_add` — `fromTauReal (fromNat (a+b)) ≈
  fromTauReal (fromNat a) + fromTauReal (fromNat b)`. Proved by
  componentwise pointwise reduction at TauRat level with `ring`.

* `TauComplex.fromTauReal_fromNat_zero` — `fromTauReal (fromNat 0) ≈
  TauComplex.zero`. Componentwise: `.re = fromNat 0 ≈ zero` (pointwise
  TauRat) and `.im = zero ≈ zero` (refl).

The combinatorial Pascal step + main outer induction + equiv-bridge to
`B_target` are queued for Part 3b'''''''''''' (next).
-/

/-- **fromTauReal ∘ fromNat distributes over Nat addition** at the
    TauComplex.equiv level: `fromTauReal (fromNat (a+b)) ≈ fromTauReal
    (fromNat a) + fromTauReal (fromNat b)`.

    Used in the Pascal step to lift `Nat.choose_succ_succ` to TauComplex
    coefficients. Proved by componentwise pointwise reduction with `ring`. -/
theorem TauComplex.fromTauReal_fromNat_add (a b : Nat) :
    (TauComplex.fromTauReal (TauReal.fromNat (a + b))).equiv
      ((TauComplex.fromTauReal (TauReal.fromNat a)).add
        (TauComplex.fromTauReal (TauReal.fromNat b))) := by
  refine ⟨?_, ?_⟩
  · -- Real part: fromNat (a+b) ≈ fromNat a + fromNat b
    apply TauReal.equiv_of_pointwise
    intro n
    simp only [TauComplex.fromTauReal, TauComplex.add,
               TauReal.fromNat, TauReal.fromTauRat, TauReal.add]
    simp only [TauRat.equiv, TauRat.add, nat_to_taurat, int_to_taurat]
    try rw [equiv_iff_toInt_eq]
    try simp only [toInt_add, toInt_mul, toInt_nat_to_tauint,
                    toInt_fromNat, toInt_zero, toInt_one]
    try push_cast
    try ring
    try decide
  · -- Imag part: TauReal.zero ≈ TauReal.zero + TauReal.zero (both componentwise zero).
    apply TauReal.equiv_of_pointwise
    intro n
    simp only [TauComplex.fromTauReal, TauComplex.add,
               TauReal.zero, TauReal.fromTauRat, TauReal.add]
    simp only [TauRat.equiv, TauRat.add, TauRat.zero]
    try rw [equiv_iff_toInt_eq]
    try simp only [toInt_add, toInt_mul, toInt_fromNat, toInt_zero, toInt_one]
    try push_cast
    try ring
    try decide

/-- **fromTauReal ∘ fromNat 0 is TauComplex.zero** (at equiv level):
    `fromTauReal (fromNat 0) ≈ TauComplex.zero`.

    Used in the Pascal step to discharge the boundary term `c_{n,n+1}
    = Nat.choose n (n+1) = 0` when reindexing the second Pascal sum
    (which extends one index beyond Σ_right's range; the extra term
    has coefficient 0 and thus contributes equiv-zero). -/
theorem TauComplex.fromTauReal_fromNat_zero :
    (TauComplex.fromTauReal (TauReal.fromNat 0)).equiv TauComplex.zero := by
  refine ⟨?_, ?_⟩
  · -- Real part: fromNat 0 ≈ TauReal.zero pointwise.
    apply TauReal.equiv_of_pointwise
    intro n
    simp only [TauComplex.fromTauReal, TauComplex.zero,
               TauReal.fromNat, TauReal.fromTauRat, TauReal.zero]
    simp only [TauRat.equiv, TauRat.zero]
    try rw [equiv_iff_toInt_eq]
    try simp only [toInt_add, toInt_mul, toInt_fromNat, toInt_zero, toInt_one]
    try push_cast
    try ring
    try decide
  · -- Imag part: TauReal.zero ≈ TauReal.zero (refl).
    exact TauReal.equiv_refl _

-- ============================================================
-- PART 23: PHASE 3C PART 3b'''''''''''' — Pascal term + sum decomposition
-- ============================================================

/-! ## Phase 3C Part 3b'''''''''''' deliverables — Pascal step (first half)

For the Pascal combinatorial identity `Σ_left + Σ_right ≈ B_left(n+1)`,
this commit ships the **first half**: the term-wise and sum-wise Pascal
decomposition. The Σ_right reindex + final assembly are queued for
Part 3b''''''''''''' (next).

### Strategy

The binomial step decomposes:
```
B_left(n+1) ≈ f_{n+1}(0) + sum (fun j => f_{n+1}(j+1)) (n+1)   [sum_split_first]
            ≈ z₂^(n+1) + sum (fun j => f_{n+1}(j+1)) (n+1)
            ≈ z₂^(n+1) + Σ_left + Σ_right_shifted              [THIS COMMIT]
            ≈ Σ_left + (z₂^(n+1) + Σ_right_shifted)
            ≈ Σ_left + Σ_right                                  [Σ_right reindex, queued]
```

Where `Σ_right_shifted := sum (fun j => (c_{n,j+1} · z₁^(j+1)) · z₂^(n-j)) (n+1)`.

This commit proves the THIRD line: that `sum (fun j => f_{n+1}(j+1)) (n+1)
≈ Σ_left + Σ_right_shifted` via term-wise Pascal application.

### Deliverables

* `TauComplex.pascal_helper_A` — bound-free `((a+b)·P)·Q ≈ (a·P)·Q +
  (b·P)·Q`. Bypasses the naive bound-dependent substitution by going
  through `(a+b)·(P·Q)` via `mul_assoc`, applying `right_distrib_equiv`
  (bound-free), then `mul_assoc` backwards on each side via
  `equiv_add_congr` (bound-free).

* `TauComplex.pascal_term_decompose` — term-wise Pascal lift: for each j,
  `f_{n+1}(j+1) ≈ term_a(j) + term_b(j)` where `term_a(j) = (c_{n,j} ·
  z₁^(j+1)) · z₂^(n-j)` and `term_b(j) = (c_{n,j+1} · z₁^(j+1)) ·
  z₂^(n-j)`. Uses `Nat.choose_succ_succ` (Nat-level Pascal),
  `fromTauReal_fromNat_add` (lift to TauComplex), bounded substitution
  through `_·pow z₁ (j+1)` and `_·pow z₂ (n-j)`, then `pascal_helper_A`.

* `TauComplex.pascal_sum_decompose` — sum-wise: `sum (fun j =>
  f_{n+1}(j+1)) (n+1) ≈ Σ_left + Σ_right_shifted`. Via
  `sum_equiv_congr` lifting `pascal_term_decompose` + `sum_add_split`.
-/

/-- **Pascal helper A** (bound-free): `((a+b)·P)·Q ≈ (a·P)·Q + (b·P)·Q`.

    Proved by:
    1. `((a+b)·P)·Q ≈ (a+b)·(P·Q)`  [mul_assoc]
    2. `(a+b)·(P·Q) ≈ a·(P·Q) + b·(P·Q)`  [right_distrib_equiv]
    3. `a·(P·Q) ≈ (a·P)·Q` and `b·(P·Q) ≈ (b·P)·Q`  [mul_assoc backwards via equiv_symm]
    4. Combine via `equiv_add_congr` (bound-free).

    The key insight: going through `(a+b)·(P·Q)` avoids the bounded
    substitution that the naive chain `((a+b)·P)·Q ≈ ((a·P)+(b·P))·Q
    ≈ (a·P)·Q + (b·P)·Q` would need. -/
theorem TauComplex.pascal_helper_A (a b P Q : TauComplex) :
    (((a.add b).mul P).mul Q).equiv (((a.mul P).mul Q).add ((b.mul P).mul Q)) := by
  have h1 : (((a.add b).mul P).mul Q).equiv ((a.add b).mul (P.mul Q)) :=
    taucomplex_mul_assoc (a.add b) P Q
  have h2 : ((a.add b).mul (P.mul Q)).equiv ((a.mul (P.mul Q)).add (b.mul (P.mul Q))) :=
    TauComplex.right_distrib_equiv a b (P.mul Q)
  have h3a : (a.mul (P.mul Q)).equiv ((a.mul P).mul Q) :=
    TauComplex.equiv_symm (taucomplex_mul_assoc a P Q)
  have h3b : (b.mul (P.mul Q)).equiv ((b.mul P).mul Q) :=
    TauComplex.equiv_symm (taucomplex_mul_assoc b P Q)
  have h4 : ((a.mul (P.mul Q)).add (b.mul (P.mul Q))).equiv
              (((a.mul P).mul Q).add ((b.mul P).mul Q)) :=
    TauComplex.equiv_add_congr h3a h3b
  exact TauComplex.equiv_trans (TauComplex.equiv_trans h1 h2) h4

/-- **Pascal term decomposition** (one binomial term at index j+1):
    `((c_{n+1, j+1}) · z₁^(j+1)) · z₂^(n-j) ≈
     ((c_{n,j} · z₁^(j+1)) · z₂^(n-j)) + ((c_{n,j+1} · z₁^(j+1)) · z₂^(n-j))`.

    Chain:
    1. Apply `Nat.choose_succ_succ` (Pascal at Nat level) to rewrite
       the coefficient as `Nat.choose n j + Nat.choose n (j+1)`.
    2. Lift to TauComplex via `fromTauReal_fromNat_add`:
       `fromTauReal (fromNat (a+b)) ≈ fromTauReal (fromNat a) +
        fromTauReal (fromNat b)`.
    3. Substitute through `_·pow z₁ (j+1)` (bound on `pow z₁ (j+1)`
       from `pow_BoundedBy_compounds` at z₁) and `_·pow z₂ (n-j)`
       (bound on `pow z₂ (n-j)` from `pow_BoundedBy_compounds` at z₂).
    4. Apply `pascal_helper_A` (bound-free). -/
theorem TauComplex.pascal_term_decompose
    (z₁ z₂ : TauComplex) (M : Nat) (hM : 1 ≤ M)
    (h_bound_z1 : TauComplex.BoundedBy z₁ M)
    (h_bound_z2 : TauComplex.BoundedBy z₂ M) (n j : Nat) :
    (((TauComplex.fromTauReal (TauReal.fromNat (Nat.choose (n+1) (j+1)))).mul
        (TauComplex.pow z₁ (j+1))).mul (TauComplex.pow z₂ (n-j))).equiv
    ((((TauComplex.fromTauReal (TauReal.fromNat (Nat.choose n j))).mul
        (TauComplex.pow z₁ (j+1))).mul (TauComplex.pow z₂ (n-j))).add
     (((TauComplex.fromTauReal (TauReal.fromNat (Nat.choose n (j+1)))).mul
        (TauComplex.pow z₁ (j+1))).mul (TauComplex.pow z₂ (n-j)))) := by
  -- Step 1: Pascal at Nat level
  rw [Nat.choose_succ_succ]
  -- Step 2: bounds on pow factors
  obtain ⟨B_P, hBP_pos, h_bound_P⟩ :=
    TauComplex.pow_BoundedBy_compounds z₁ M (j+1) hM h_bound_z1
  obtain ⟨B_Q, hBQ_pos, h_bound_Q⟩ :=
    TauComplex.pow_BoundedBy_compounds z₂ M (n-j) hM h_bound_z2
  -- Step 3: lift fromTauReal_fromNat_add through _·P then _·Q
  have h_coef := TauComplex.fromTauReal_fromNat_add (Nat.choose n j) (Nat.choose n (j+1))
  have h_lift_P : ((TauComplex.fromTauReal (TauReal.fromNat
                    (Nat.choose n j + Nat.choose n (j+1)))).mul
                    (TauComplex.pow z₁ (j+1))).equiv
                  (((TauComplex.fromTauReal (TauReal.fromNat (Nat.choose n j))).add
                    (TauComplex.fromTauReal (TauReal.fromNat (Nat.choose n (j+1))))).mul
                    (TauComplex.pow z₁ (j+1))) :=
    TauComplex.mul_respects_equiv_right_of_bound _ _ (TauComplex.pow z₁ (j+1))
      B_P hBP_pos h_bound_P.1 h_bound_P.2 h_coef
  have h_lift_Q := TauComplex.mul_respects_equiv_right_of_bound
    _ _ (TauComplex.pow z₂ (n-j)) B_Q hBQ_pos h_bound_Q.1 h_bound_Q.2 h_lift_P
  -- Step 4: apply pascal_helper_A
  have h_helper := TauComplex.pascal_helper_A
    (TauComplex.fromTauReal (TauReal.fromNat (Nat.choose n j)))
    (TauComplex.fromTauReal (TauReal.fromNat (Nat.choose n (j+1))))
    (TauComplex.pow z₁ (j+1))
    (TauComplex.pow z₂ (n-j))
  exact TauComplex.equiv_trans h_lift_Q h_helper

/-- **Pascal sum decomposition**: `sum (fun j => f_{n+1}(j+1)) (n+1) ≈
    Σ_left + Σ_right_shifted`.

    Where:
    * `f_{n+1}(j+1) = (c_{n+1,j+1} · z₁^(j+1)) · z₂^(n-j)` — the j+1-th
      term of B_left(n+1).
    * `Σ_left = sum (fun j => (c_{n,j} · z₁^(j+1)) · z₂^(n-j)) (n+1)` —
      EXACTLY matches the Σ_left shipped in Part 3b''''''''''.
    * `Σ_right_shifted = sum (fun j => (c_{n,j+1} · z₁^(j+1)) · z₂^(n-j))
      (n+1)` — the reindexed Σ_right (i = j+1 shift).

    Chain: apply `pascal_term_decompose` term-wise via `sum_equiv_congr`,
    then split via `sum_add_split`. -/
theorem TauComplex.pascal_sum_decompose
    (z₁ z₂ : TauComplex) (M : Nat) (hM : 1 ≤ M)
    (h_bound_z1 : TauComplex.BoundedBy z₁ M)
    (h_bound_z2 : TauComplex.BoundedBy z₂ M) (n : Nat) :
    (TauComplex.sum (fun j =>
        ((TauComplex.fromTauReal (TauReal.fromNat (Nat.choose (n+1) (j+1)))).mul
          (TauComplex.pow z₁ (j+1))).mul (TauComplex.pow z₂ (n-j))) (n+1)).equiv
    ((TauComplex.sum (fun j =>
        ((TauComplex.fromTauReal (TauReal.fromNat (Nat.choose n j))).mul
          (TauComplex.pow z₁ (j+1))).mul (TauComplex.pow z₂ (n-j))) (n+1)).add
     (TauComplex.sum (fun j =>
        ((TauComplex.fromTauReal (TauReal.fromNat (Nat.choose n (j+1)))).mul
          (TauComplex.pow z₁ (j+1))).mul (TauComplex.pow z₂ (n-j))) (n+1))) := by
  -- Step 1: apply pascal_term_decompose term-wise
  have h_terms : (TauComplex.sum (fun j =>
                  ((TauComplex.fromTauReal (TauReal.fromNat (Nat.choose (n+1) (j+1)))).mul
                    (TauComplex.pow z₁ (j+1))).mul (TauComplex.pow z₂ (n-j))) (n+1)).equiv
                  (TauComplex.sum (fun j =>
                    (((TauComplex.fromTauReal (TauReal.fromNat (Nat.choose n j))).mul
                      (TauComplex.pow z₁ (j+1))).mul (TauComplex.pow z₂ (n-j))).add
                    (((TauComplex.fromTauReal (TauReal.fromNat (Nat.choose n (j+1)))).mul
                      (TauComplex.pow z₁ (j+1))).mul (TauComplex.pow z₂ (n-j)))) (n+1)) := by
    apply TauComplex.sum_equiv_congr
    intro j
    exact TauComplex.pascal_term_decompose z₁ z₂ M hM h_bound_z1 h_bound_z2 n j
  -- Step 2: split via sum_add_split
  have h_split := TauComplex.sum_add_split
    (fun j => ((TauComplex.fromTauReal (TauReal.fromNat (Nat.choose n j))).mul
                (TauComplex.pow z₁ (j+1))).mul (TauComplex.pow z₂ (n-j)))
    (fun j => ((TauComplex.fromTauReal (TauReal.fromNat (Nat.choose n (j+1)))).mul
                (TauComplex.pow z₁ (j+1))).mul (TauComplex.pow z₂ (n-j)))
    (n+1)
  exact TauComplex.equiv_trans h_terms h_split

-- ============================================================
-- PART 24: PHASE 3C PART 3b''''''''''''' — First-term simplification
-- ============================================================

/-! ## Phase 3C Part 3b''''''''''''' deliverables — first-term reduction

For the Pascal step's final combine (Part 3b'''''''''''''', next), we
need to reduce the i=0/j=0 boundary terms of `Σ_right` and `B_left(n+1)`
to a clean `pow z₂ (n+1)` form. Specifically:

* B_left(n+1) at j=0:
    `((fromTauReal (fromNat (Nat.choose (n+1) 0))).mul (pow z₁ 0)).mul (pow z₂ (n+1-0))`
    = `((fromTauReal (fromNat 1)).mul one).mul (pow z₂ (n+1))`
    ≈ `pow z₂ (n+1)`

* Σ_right at i=0:
    `((fromTauReal (fromNat (Nat.choose n 0))).mul (pow z₁ 0)).mul (pow z₂ ((n-0)+1))`
    = `((fromTauReal (fromNat 1)).mul one).mul (pow z₂ (n+1))`
    ≈ `pow z₂ (n+1)`

Both reduce via the same chain. This commit ships:

### Deliverables

* `TauComplex.fromTauReal_fromNat_one` — `fromTauReal (fromNat 1) ≈
  TauComplex.one`. Via pointwise TauRat-level reduction with `ring`.

* `TauComplex.first_term_simplify` — the unified i=0/j=0 simplification:
    `((fromTauReal (fromNat 1)).mul one).mul (pow z₂ (n+1)) ≈ pow z₂ (n+1)`.
  Chain:
    1. `(fromTauReal (fromNat 1)).mul one ≈ fromTauReal (fromNat 1)`
       via `taucomplex_mul_one` (bound-free).
    2. `fromTauReal (fromNat 1) ≈ one` via `fromTauReal_fromNat_one`
       (bound-free).
    3. Substitute into `_·pow z₂ (n+1)`: bound on `pow z₂ (n+1)` from
       `pow_BoundedBy_compounds` at z₂.
    4. `one.mul (pow z₂ (n+1)) ≈ pow z₂ (n+1)` via `one_mul_equiv`
       (bound-free).

  One bounded substitution + three bound-free ring axioms.
-/

/-- **fromTauReal ∘ fromNat 1 is TauComplex.one** at equiv level:
    `(fromTauReal (fromNat 1)).equiv TauComplex.one`.

    Componentwise via pointwise TauRat-level reduction: `(fromNat 1)
    .approx n = nat_to_taurat 1` which has num=1, den=1, matching
    `TauReal.one.approx n = TauRat.one`. The imag side is `zero ≈
    zero` (refl). -/
theorem TauComplex.fromTauReal_fromNat_one :
    (TauComplex.fromTauReal (TauReal.fromNat 1)).equiv TauComplex.one := by
  refine ⟨?_, ?_⟩
  · -- Real part: fromNat 1 ≈ TauReal.one pointwise.
    apply TauReal.equiv_of_pointwise
    intro n
    simp only [TauComplex.fromTauReal, TauComplex.one,
               TauReal.fromNat, TauReal.fromTauRat, TauReal.one]
    simp only [TauRat.equiv, TauRat.one, nat_to_taurat, int_to_taurat]
    try rw [equiv_iff_toInt_eq]
    try simp only [toInt_add, toInt_mul, toInt_nat_to_tauint,
                    toInt_fromNat, toInt_zero, toInt_one]
    try push_cast
    try ring
    try decide
  · -- Imag part: TauReal.zero ≈ TauReal.zero (refl).
    exact TauReal.equiv_refl _

/-- **First-term simplification**: the i=0 / j=0 boundary term of
    Σ_right and B_left(n+1) reduces to `pow z₂ (n+1)`.

    `((fromTauReal (fromNat 1)).mul one).mul (pow z₂ (n+1)) ≈ pow z₂ (n+1)`.

    Used in Part 3b'''''''''''''' to discharge the first-term boundaries
    of the Pascal combine. -/
theorem TauComplex.first_term_simplify (z₂ : TauComplex) (M : Nat) (hM : 1 ≤ M)
    (h_bound_z2 : TauComplex.BoundedBy z₂ M) (n : Nat) :
    (((TauComplex.fromTauReal (TauReal.fromNat 1)).mul TauComplex.one).mul
      (TauComplex.pow z₂ (n+1))).equiv (TauComplex.pow z₂ (n+1)) := by
  -- Step 1: (fromTauReal (fromNat 1)).mul one ≈ fromTauReal (fromNat 1) [mul_one]
  have h1 : ((TauComplex.fromTauReal (TauReal.fromNat 1)).mul TauComplex.one).equiv
              (TauComplex.fromTauReal (TauReal.fromNat 1)) :=
    taucomplex_mul_one (TauComplex.fromTauReal (TauReal.fromNat 1))
  -- Step 2: fromTauReal (fromNat 1) ≈ one [fromTauReal_fromNat_one]
  have h2 : (TauComplex.fromTauReal (TauReal.fromNat 1)).equiv TauComplex.one :=
    TauComplex.fromTauReal_fromNat_one
  -- Chain to get inner ≈ one
  have h_inner : ((TauComplex.fromTauReal (TauReal.fromNat 1)).mul TauComplex.one).equiv
                  TauComplex.one := TauComplex.equiv_trans h1 h2
  -- Step 3: substitute into _·pow z₂ (n+1) [needs bound on pow z₂ (n+1)]
  obtain ⟨B_Q, hBQ_pos, h_bound_Q⟩ :=
    TauComplex.pow_BoundedBy_compounds z₂ M (n+1) hM h_bound_z2
  have h_step3 : (((TauComplex.fromTauReal (TauReal.fromNat 1)).mul TauComplex.one).mul
                   (TauComplex.pow z₂ (n+1))).equiv
                  (TauComplex.one.mul (TauComplex.pow z₂ (n+1))) :=
    TauComplex.mul_respects_equiv_right_of_bound
      _ _ (TauComplex.pow z₂ (n+1)) B_Q hBQ_pos h_bound_Q.1 h_bound_Q.2 h_inner
  -- Step 4: one.mul X ≈ X [one_mul_equiv]
  have h_step4 : (TauComplex.one.mul (TauComplex.pow z₂ (n+1))).equiv (TauComplex.pow z₂ (n+1)) :=
    TauComplex.one_mul_equiv (TauComplex.pow z₂ (n+1))
  exact TauComplex.equiv_trans h_step3 h_step4

-- ============================================================
-- PART 25: PHASE 3C PART 3b'''''''''''''' — B_left split + bridge helpers
-- ============================================================

/-! ## Phase 3C Part 3b'''''''''''''' deliverables — B_left split + helpers

For the Pascal combine `Σ_left + Σ_right ≈ B_left(n+1)` (Part
3b''''''''''''''', queued), we need:

1. **`B_left_split_first`**: B_left(n+1) reindexed via sum_split_first:
     `B_left(n+1) ≈ pow z₂ (n+1) + sum (fun j => f_{n+1}(j+1)) (n+1)`
   where the shifted-sum form matches pascal_sum_decompose's input.

2. **`sum_equiv_congr_bounded`**: a bounded version of sum_equiv_congr
   that only requires equiv on `i < n` (not all i). Used to bridge two
   sums whose terms agree only on the in-range portion.

3. **`zero_term_equiv_zero`**: if `c ≈ zero`, then `(c · z₁^k) · z₂^l ≈
   zero`. Used to drop the `c_{n,n+1} = 0` boundary term from
   Σ_right_shifted when bridging to Σ_right.

### Deliverables

* `TauComplex.B_left_split_first` — `B_left(n+1) ≈ pow z₂ (n+1) +
  sum_shifted`. Via `sum_split_first` + `first_term_simplify` +
  `equiv_add_congr`. The shifted-sum form matches what
  `pascal_sum_decompose` consumes (the `(n+1) - (j+1) = n - j`
  reduction is `rfl` in Lean 4).

* `TauComplex.sum_equiv_congr_bounded` — `(∀ i < n, f i ≈ g i) → sum
  f n ≈ sum g n`. By induction, using `equiv_add_congr` with the
  bounded hypothesis.

* `TauComplex.zero_term_equiv_zero` — `c ≈ zero → ((c · pow z₁ k)
  · pow z₂ l) ≈ zero`. Chain: substitute c → zero via two bounded
  substitutions, then collapse via `zero_mul_equiv` twice.
-/

/-- **B_left split first**: peel the j=0 term of B_left(n+1) which
    simplifies to `pow z₂ (n+1)`.

    `B_left(n+1) ≈ pow z₂ (n+1) + sum (fun j => f_{n+1}(j+1)) (n+1)`

    Via `sum_split_first` (peels j=0) + `first_term_simplify` (the
    j=0 term reduces to `pow z₂ (n+1)` after `Nat.choose (n+1) 0 = 1`
    and `(n+1)-0 = n+1` definitional reductions).

    The shifted-sum form uses `(n+1) - (j+1)` (matching
    `sum_split_first`'s natural output). The bridge to `n - j` form
    (which `pascal_sum_decompose` consumes) is handled in the next
    part via the `Nat.succ_sub_succ_eq_sub : (n+1) - (j+1) = n - j`
    rfl identity. -/
theorem TauComplex.B_left_split_first (z₁ z₂ : TauComplex) (M : Nat) (hM : 1 ≤ M)
    (h_bound_z2 : TauComplex.BoundedBy z₂ M) (n : Nat) :
    (TauComplex.sum (fun j =>
       ((TauComplex.fromTauReal (TauReal.fromNat (Nat.choose (n+1) j))).mul
         (TauComplex.pow z₁ j)).mul (TauComplex.pow z₂ ((n+1) - j))) (n+2)).equiv
     ((TauComplex.pow z₂ (n+1)).add (TauComplex.sum (fun j =>
       ((TauComplex.fromTauReal (TauReal.fromNat (Nat.choose (n+1) (j+1)))).mul
         (TauComplex.pow z₁ (j+1))).mul (TauComplex.pow z₂ ((n+1) - (j+1)))) (n+1))) := by
  have h1 := TauComplex.sum_split_first (fun j =>
    ((TauComplex.fromTauReal (TauReal.fromNat (Nat.choose (n+1) j))).mul
      (TauComplex.pow z₁ j)).mul (TauComplex.pow z₂ ((n+1) - j))) (n+1)
  have h_first : (((TauComplex.fromTauReal (TauReal.fromNat (Nat.choose (n+1) 0))).mul
                    (TauComplex.pow z₁ 0)).mul (TauComplex.pow z₂ ((n+1) - 0))).equiv
                  (TauComplex.pow z₂ (n+1)) :=
    TauComplex.first_term_simplify z₂ M hM h_bound_z2 n
  exact TauComplex.equiv_trans h1
    (TauComplex.equiv_add_congr h_first (TauComplex.equiv_refl _))

/-- **Bounded sum-equiv-congr**: if `f i ≈ g i` for all `i < n`, then
    `sum f n ≈ sum g n`.

    A weaker hypothesis than `sum_equiv_congr` (which requires `∀ i,
    equiv`). Used to bridge two sums whose terms agree only on the
    in-range portion `[0, n)`. -/
theorem TauComplex.sum_equiv_congr_bounded (f g : Nat → TauComplex) (n : Nat)
    (h : ∀ i, i < n → (f i).equiv (g i)) :
    (TauComplex.sum f n).equiv (TauComplex.sum g n) := by
  induction n with
  | zero => exact TauComplex.equiv_refl _
  | succ n ih =>
    show ((TauComplex.sum f n).add (f n)).equiv ((TauComplex.sum g n).add (g n))
    have h_n : (f n).equiv (g n) := h n (Nat.lt_succ_self n)
    have ih' : (TauComplex.sum f n).equiv (TauComplex.sum g n) :=
      ih (fun i hi => h i (Nat.lt_succ_of_lt hi))
    exact TauComplex.equiv_add_congr ih' h_n

/-- **Zero-coefficient term collapses to zero**: if the coefficient
    `c ≈ zero`, then `((c · pow z₁ k) · pow z₂ l) ≈ zero`.

    Used in the Pascal step to drop the boundary term `(c_{n,n+1} ·
    z₁^(n+1)) · z₂^0` from Σ_right_shifted's last entry (where
    `c_{n,n+1} = Nat.choose n (n+1) = 0`).

    Chain: substitute c → zero through `_·pow z₁ k` (bound on
    `pow z₁ k`) and `_·pow z₂ l` (bound on `pow z₂ l`), then collapse
    via `zero_mul_equiv` twice. -/
theorem TauComplex.zero_term_equiv_zero (c z₁ z₂ : TauComplex) (M : Nat) (hM : 1 ≤ M)
    (h_bound_z1 : TauComplex.BoundedBy z₁ M)
    (h_bound_z2 : TauComplex.BoundedBy z₂ M)
    (h_c_zero : c.equiv TauComplex.zero) (k l : Nat) :
    ((c.mul (TauComplex.pow z₁ k)).mul (TauComplex.pow z₂ l)).equiv TauComplex.zero := by
  -- Step 1: substitute c → zero in _·pow z₁ k (bound on pow z₁ k).
  obtain ⟨B_P, hBP_pos, h_bound_P⟩ :=
    TauComplex.pow_BoundedBy_compounds z₁ M k hM h_bound_z1
  have h_step1 : (c.mul (TauComplex.pow z₁ k)).equiv
                  (TauComplex.zero.mul (TauComplex.pow z₁ k)) :=
    TauComplex.mul_respects_equiv_right_of_bound c TauComplex.zero
      (TauComplex.pow z₁ k) B_P hBP_pos h_bound_P.1 h_bound_P.2 h_c_zero
  -- Step 2: zero · pow z₁ k ≈ zero [zero_mul_equiv].
  have h_step2 : (TauComplex.zero.mul (TauComplex.pow z₁ k)).equiv TauComplex.zero :=
    TauComplex.zero_mul_equiv (TauComplex.pow z₁ k)
  -- Step 3: substitute into _·pow z₂ l (bound on pow z₂ l).
  obtain ⟨B_Q, hBQ_pos, h_bound_Q⟩ :=
    TauComplex.pow_BoundedBy_compounds z₂ M l hM h_bound_z2
  have h_inner : (c.mul (TauComplex.pow z₁ k)).equiv TauComplex.zero :=
    TauComplex.equiv_trans h_step1 h_step2
  have h_step3 : ((c.mul (TauComplex.pow z₁ k)).mul (TauComplex.pow z₂ l)).equiv
                  (TauComplex.zero.mul (TauComplex.pow z₂ l)) :=
    TauComplex.mul_respects_equiv_right_of_bound _ _ (TauComplex.pow z₂ l)
      B_Q hBQ_pos h_bound_Q.1 h_bound_Q.2 h_inner
  -- Step 4: zero · pow z₂ l ≈ zero [zero_mul_equiv].
  have h_step4 : (TauComplex.zero.mul (TauComplex.pow z₂ l)).equiv TauComplex.zero :=
    TauComplex.zero_mul_equiv (TauComplex.pow z₂ l)
  exact TauComplex.equiv_trans h_step3 h_step4

-- ============================================================
-- PART 26: PHASE 3C PART 3b''''''''''''''' — Σ_right reindex
-- ============================================================

/-! ## Phase 3C Part 3b''''''''''''''' deliverables — Σ_right reindex

This commit ships the **Σ_right reindex**:
  `Σ_right ≈ pow z₂ (n+1) + Σ_right_shifted`

This is the second of the two key bridges (the first was
`B_left_split_first` in Part 3b''''''''''''''). The final Pascal
combine (Part 3b'''''''''''''''', queued) will assemble:

```
Σ_left + Σ_right
   ≈ Σ_left + (pow z₂ (n+1) + Σ_right_shifted)   [this commit]
   ≈ pow z₂ (n+1) + (Σ_left + Σ_right_shifted)   [add reorg]
   ≈ pow z₂ (n+1) + sum f_{n+1}(j+1)             [pascal_sum_decompose reverse]
   ≈ B_left(n+1)                                  [B_left_split_first reverse + bridge]
```

### Chain

1. **sum_split_first** on Σ_right peels off i=0 →
   `Σ_right ≈ first_term + sum_after_first`.

2. **first_term ≈ pow z₂ (n+1)** via `first_term_simplify` (since
   `Nat.choose n 0 = 1`, `pow z₁ 0 = one`, `(n-0)+1 = n+1` all reduce).

3. **sum_after_first ≈ Σ_right_shifted** by:
   - **Step a**: bridge sum_after_first to "f_restricted_n" (the first
     n terms of Σ_right_shifted) via `sum_equiv_congr_bounded` with
     the Nat-arith identity `(n-(i+1))+1 = n-i` for `i < n` (proved
     by `omega`).
   - **Step b**: peel the last term off Σ_right_shifted (via
     definitional `sum_succ`) and discharge it as ≈ 0 via
     `zero_term_equiv_zero` (with `Nat.choose n (n+1) = 0` Pascal
     boundary).
   - **Step c**: `add_zero` collapses the boundary contribution.

### Deliverables

* `TauComplex.right_sum_reindex` — the main result above.
-/

/-- **Right-shifted sum boundary discharge**: Σ_right_shifted's last term
    (at index `n`, with coefficient `c_{n,n+1} = 0`) collapses to zero,
    leaving just the first n terms.

    `sum f (n+1) ≈ sum f n` where `f j = ((fromTauReal (fromNat (Nat.choose
    n (j+1)))).mul (pow z₁ (j+1))).mul (pow z₂ (n - j))`. The last term
    `f n` has coefficient `Nat.choose n (n+1) = 0`, hence ≈ zero via
    `zero_term_equiv_zero`, and `taucomplex_add_zero` collapses. -/
theorem TauComplex.right_shifted_peel_last (z₁ z₂ : TauComplex) (M : Nat) (hM : 1 ≤ M)
    (h_bound_z1 : TauComplex.BoundedBy z₁ M)
    (h_bound_z2 : TauComplex.BoundedBy z₂ M) (n : Nat) :
    (TauComplex.sum (fun j =>
      ((TauComplex.fromTauReal (TauReal.fromNat (Nat.choose n (j+1)))).mul
        (TauComplex.pow z₁ (j+1))).mul (TauComplex.pow z₂ (n - j))) (n+1)).equiv
    (TauComplex.sum (fun j =>
      ((TauComplex.fromTauReal (TauReal.fromNat (Nat.choose n (j+1)))).mul
        (TauComplex.pow z₁ (j+1))).mul (TauComplex.pow z₂ (n - j))) n) := by
  have h_choose_zero : Nat.choose n (n+1) = 0 := Nat.choose_eq_zero_of_lt (Nat.lt_succ_self n)
  have h_c_zero : (TauComplex.fromTauReal (TauReal.fromNat (Nat.choose n (n+1)))).equiv
                    TauComplex.zero := by
    rw [h_choose_zero]
    exact TauComplex.fromTauReal_fromNat_zero
  have h_last_zero : (((TauComplex.fromTauReal (TauReal.fromNat (Nat.choose n (n+1)))).mul
                        (TauComplex.pow z₁ (n+1))).mul (TauComplex.pow z₂ (n - n))).equiv
                      TauComplex.zero :=
    TauComplex.zero_term_equiv_zero _ z₁ z₂ M hM h_bound_z1 h_bound_z2 h_c_zero (n+1) (n-n)
  -- sum f (n+1) = (sum f n).add (f n) by sum_succ.
  -- Apply equiv_add_congr (refl) h_last_zero, then taucomplex_add_zero.
  apply TauComplex.equiv_trans
    (TauComplex.equiv_add_congr (TauComplex.equiv_refl _) h_last_zero)
  exact taucomplex_add_zero _

/-- **Right after-first bridge**: the `(n-(i+1))+1`-form sum equals the
    `n-j`-form sum on the first n indices (where they agree in value
    via Nat-arith `(n-(i+1))+1 = n-i` for `i < n`).

    Used to bridge `sum_after_first` (output of `sum_split_first` on
    Σ_right) with the first-n-terms of Σ_right_shifted. -/
theorem TauComplex.right_after_first_bridge (z₁ z₂ : TauComplex) (n : Nat) :
    (TauComplex.sum (fun i =>
      ((TauComplex.fromTauReal (TauReal.fromNat (Nat.choose n (i+1)))).mul
        (TauComplex.pow z₁ (i+1))).mul (TauComplex.pow z₂ ((n - (i+1)) + 1))) n).equiv
    (TauComplex.sum (fun j =>
      ((TauComplex.fromTauReal (TauReal.fromNat (Nat.choose n (j+1)))).mul
        (TauComplex.pow z₁ (j+1))).mul (TauComplex.pow z₂ (n - j))) n) := by
  apply TauComplex.sum_equiv_congr_bounded
  intro i hi
  have h_eq : (n - (i+1)) + 1 = n - i := by omega
  rw [h_eq]
  exact TauComplex.equiv_refl _

-- ============================================================
-- PART 27: PHASE 3C PART 3b'''''''''''''''' — right_after_first composite
-- ============================================================

/-! ## Phase 3C Part 3b'''''''''''''''' deliverables — composing sub-lemma

For the Σ_right reindex `Σ_right ≈ pow z₂ (n+1) + Σ_right_shifted`,
this part ships the **composing sub-lemma** that fuses
`right_after_first_bridge` (sum_after_first ≈ first_n_terms) with
`right_shifted_peel_last` (first_n_terms ≈ Σ_right_shifted, reversed)
to yield directly:

  `sum_after_first ≈ Σ_right_shifted`

This is the cleanest decomposition because it keeps each theorem's
signature within Lean's elaboration budget. The main `right_sum_reindex`
in Part 3b''''''''''''''''' (next) will then chain this sub-lemma
with `sum_split_first` and `first_term_simplify` via term-mode.

### Why this works

The composite `right_after_first_to_shifted` has TWO sums in its
signature (sum_after_first form + Σ_right_shifted form), comparable
complexity to the individual sub-lemmas. The main `right_sum_reindex`
has THREE expressions (Σ_right + pow z₂ (n+1) + Σ_right_shifted), one
more than the sub-lemmas — and the additional expression-tree depth
appears to push it past the heartbeat budget. By keeping
right_after_first_to_shifted at "two sums + chain" we stay within
budget.
-/

/-- **right_after_first to Σ_right_shifted** (composite bridge):
    `sum_after_first ≈ Σ_right_shifted`.

    Fuses `right_after_first_bridge` (sum_after_first ≈ first_n_terms)
    with `right_shifted_peel_last` (Σ_right_shifted ≈ first_n_terms,
    used in reverse via `equiv_symm`). -/
theorem TauComplex.right_after_first_to_shifted
    (z₁ z₂ : TauComplex) (M : Nat) (hM : 1 ≤ M)
    (h_bound_z1 : TauComplex.BoundedBy z₁ M)
    (h_bound_z2 : TauComplex.BoundedBy z₂ M) (n : Nat) :
    (TauComplex.sum (fun i =>
      ((TauComplex.fromTauReal (TauReal.fromNat (Nat.choose n (i+1)))).mul
        (TauComplex.pow z₁ (i+1))).mul (TauComplex.pow z₂ ((n - (i+1)) + 1))) n).equiv
    (TauComplex.sum (fun j =>
      ((TauComplex.fromTauReal (TauReal.fromNat (Nat.choose n (j+1)))).mul
        (TauComplex.pow z₁ (j+1))).mul (TauComplex.pow z₂ (n - j))) (n+1)) :=
  TauComplex.equiv_trans
    (TauComplex.right_after_first_bridge z₁ z₂ n)
    (TauComplex.equiv_symm
      (TauComplex.right_shifted_peel_last z₁ z₂ M hM h_bound_z1 h_bound_z2 n))

-- ============================================================
-- PART 28: PHASE 3C PART 3b''''''''''''''''' — right_sum_reindex via defs
-- ============================================================

/-! ## Phase 3C Part 3b''''''''''''''''' deliverables — defs + right_sum_reindex

This part applies strategy 4 from the
`whnf-elaboration-cost-defer-pattern` atlas insight: hide the heavy
sum/mul/pow expressions behind `@[reducible]` private `def`s to shrink
the printed signature of `right_sum_reindex`.

### The strategy

`@[reducible]` defs:
* Definitionally equal to their bodies (so unification with shipped
  sub-lemmas works).
* Shown as `binomial_right_sum z₁ z₂ n` instead of the full sum
  expression in error messages and inferred types.
* Auto-unfold when Lean's elaborator needs to match the unfolded form
  (e.g., when applying `sum_split_first`).

### Deliverables

* `TauComplex.binomial_right_sum` — `@[reducible]` private def for
  `Σ_right` (the `(n-i)+1`-form binomial sum).

* `TauComplex.binomial_right_shifted` — `@[reducible]` private def
  for `Σ_right_shifted` (the `n-j`-form sum from pascal_sum_decompose).

* `TauComplex.right_sum_reindex` — the main combine, now with simpler
  signature: `(binomial_right_sum z₁ z₂ n).equiv ((pow z₂ (n+1)).add
  (binomial_right_shifted z₁ z₂ n))`.
-/

/-- **Binomial right sum** (Σ_right): the `(n-i)+1`-form binomial sum.

    Defined `@[reducible]` so that:
    * The signature of `right_sum_reindex` is compact.
    * Unification with `sum_split_first`'s output unfolds automatically.

    Concretely: `Σ_right = sum (fun i => (c_{n,i} · z₁^i) · z₂^((n-i)+1)) (n+1)`. -/
@[reducible] def TauComplex.binomial_right_sum (z₁ z₂ : TauComplex) (n : Nat) : TauComplex :=
  TauComplex.sum (fun i =>
    ((TauComplex.fromTauReal (TauReal.fromNat (Nat.choose n i))).mul
      (TauComplex.pow z₁ i)).mul (TauComplex.pow z₂ ((n - i) + 1))) (n+1)

/-- **Binomial right shifted sum** (Σ_right_shifted): the `n-j`-form sum
    that `pascal_sum_decompose` produces as the second summand.

    Concretely: `Σ_right_shifted = sum (fun j => (c_{n,j+1} · z₁^(j+1))
    · z₂^(n-j)) (n+1)`. -/
@[reducible] def TauComplex.binomial_right_shifted (z₁ z₂ : TauComplex) (n : Nat) : TauComplex :=
  TauComplex.sum (fun j =>
    ((TauComplex.fromTauReal (TauReal.fromNat (Nat.choose n (j+1)))).mul
      (TauComplex.pow z₁ (j+1))).mul (TauComplex.pow z₂ (n - j))) (n+1)

-- ============================================================
-- PART 29: PHASE 3C PART 3b'''''''''''''''''' — binomial-left defs + pascal target
-- ============================================================

/-! ## Phase 3C Part 3b'''''''''''''''''' deliverables — pascal_combine named target

This part ships:
1. `@[reducible]` defs for `binomial_left_sum` (B_left) and
   `binomial_sigma_left` (Σ_left), completing the structural skeleton.
2. `pascal_combine_target` as a Prop (named target) — the key
   combinatorial identity `Σ_left + Σ_right ≈ B_left(n+1)`.

This applies the **named-target + later-discharge pattern** (used 7+
times in this campaign). The pascal_combine identity is the deepest
remaining piece — its discharge involves combining `right_sum_reindex`
+ `B_left_split_first` + Nat-arith bridges with cost-distributed
elaboration. Ship the named target now; discharge in a focused future
commit with the right operational tooling.

With all four binomial sums now defined (`binomial_left_sum`,
`binomial_sigma_left`, `binomial_right_sum`, `binomial_right_shifted`),
the named target's signature stays compact: three def-calls + one
add + one equiv.

### Deliverables

* `TauComplex.binomial_left_sum` — `@[reducible]` def for `B_left(n)
  = sum (fun i => (c_{n,i} · z₁^i) · z₂^(n-i)) (n+1)`.

* `TauComplex.binomial_sigma_left` — `@[reducible]` def for `Σ_left
  = sum (fun i => (c_{n,i} · z₁^(i+1)) · z₂^(n-i)) (n+1)`. This is
  what `B_left(n)·z₁` becomes after `add_pow_term_left` lifts each
  term.

* `TauComplex.pascal_combine_target` — named-target Prop for the
  Pascal combinatorial identity:
  `∀ z₁ z₂ M (h_bounds) n,
    (binomial_sigma_left z₁ z₂ n + binomial_right_sum z₁ z₂ n) ≈
    binomial_left_sum z₁ z₂ (n+1)`.
-/

/-- **Binomial left sum** (B_left): the LEFT-assoc internal binomial
    sum form.

    `B_left(n) = sum (fun i => (c_{n,i} · z₁^i) · z₂^(n-i)) (n+1)`. -/
@[reducible] def TauComplex.binomial_left_sum (z₁ z₂ : TauComplex) (n : Nat) : TauComplex :=
  TauComplex.sum (fun i =>
    ((TauComplex.fromTauReal (TauReal.fromNat (Nat.choose n i))).mul
      (TauComplex.pow z₁ i)).mul (TauComplex.pow z₂ (n - i))) (n+1)

/-- **Binomial sigma left** (Σ_left): the result of distributing `z₁` over
    `B_left(n)·z₁` and applying `add_pow_term_left` term-wise.

    `Σ_left = sum (fun i => (c_{n,i} · z₁^(i+1)) · z₂^(n-i)) (n+1)`. -/
@[reducible] def TauComplex.binomial_sigma_left (z₁ z₂ : TauComplex) (n : Nat) : TauComplex :=
  TauComplex.sum (fun i =>
    ((TauComplex.fromTauReal (TauReal.fromNat (Nat.choose n i))).mul
      (TauComplex.pow z₁ (i+1))).mul (TauComplex.pow z₂ (n - i))) (n+1)

/-- **[I.D-TauComplex-PascalCombine-Target]** Named target for the
    Pascal combinatorial identity that closes the binomial inductive
    step.

    Asserts: for any `z₁, z₂` with common bound `M` (1 ≤ M),
    the sum `Σ_left + Σ_right` (each a binomial-style sum at depth n)
    equals `B_left(n+1)` (the binomial sum at depth n+1).

    Discharging this requires combining `right_sum_reindex` (still
    queued due to elaboration-cost cliff), `B_left_split_first`, and
    a Nat-arith bridge `(n+1)-(j+1) = n-j`. Ship as named target; the
    full discharge is queued for Part 3b''''''''''''''''''' (next).

    The named target's signature is compact thanks to the four
    `@[reducible]` defs `binomial_left_sum`, `binomial_sigma_left`,
    `binomial_right_sum`, `binomial_right_shifted` — keeping it within
    elaboration budget while still capturing the full combinatorial
    content. -/
def TauComplex.pascal_combine_target : Prop :=
  ∀ (z₁ z₂ : TauComplex) (M : Nat), 1 ≤ M →
    TauComplex.BoundedBy z₁ M → TauComplex.BoundedBy z₂ M → ∀ (n : Nat),
    ((TauComplex.binomial_sigma_left z₁ z₂ n).add
      (TauComplex.binomial_right_sum z₁ z₂ n)).equiv
    (TauComplex.binomial_left_sum z₁ z₂ (n+1))

/-- **Base case of `add_pow_equiv_strong_left`** at n=0:
    `pow (z₁+z₂) 0 ≈ binomial_left_sum z₁ z₂ 0`.

    Both sides reduce to `TauComplex.one` componentwise; proved by the
    same pointwise reduction pattern as `add_pow_equiv_base` (just with
    left-assoc inner `(c · z₁^i) · z₂^(n-i)` instead of right-assoc
    `c · (z₁^i · z₂^(n-i))`). -/
theorem TauComplex.add_pow_equiv_left_base (z₁ z₂ : TauComplex) :
    (TauComplex.pow (z₁.add z₂) 0).equiv (TauComplex.binomial_left_sum z₁ z₂ 0) := by
  refine ⟨?_, ?_⟩
  · -- Real part
    apply TauReal.equiv_of_pointwise
    intro n
    simp only [TauComplex.pow, TauComplex.binomial_left_sum, TauComplex.sum, TauComplex.mul,
               TauComplex.add, TauComplex.zero, TauComplex.one, TauComplex.fromTauReal,
               TauReal.sub, TauReal.add, TauReal.mul, TauReal.negate,
               TauReal.fromNat, TauReal.fromTauRat, TauReal.zero, TauReal.one]
    simp only [TauRat.equiv, TauRat.add, TauRat.mul, TauRat.negate,
               TauRat.zero, TauRat.one, nat_to_taurat, int_to_taurat]
    try rw [equiv_iff_toInt_eq]
    try simp only [toInt_add, toInt_mul, toInt_negate, toInt_nat_to_tauint,
                    toInt_fromNat, toInt_zero, toInt_one]
    try push_cast
    try ring
    try decide
  · -- Imag part
    apply TauReal.equiv_of_pointwise
    intro n
    simp only [TauComplex.pow, TauComplex.binomial_left_sum, TauComplex.sum, TauComplex.mul,
               TauComplex.add, TauComplex.zero, TauComplex.one, TauComplex.fromTauReal,
               TauReal.sub, TauReal.add, TauReal.mul, TauReal.negate,
               TauReal.fromNat, TauReal.fromTauRat, TauReal.zero, TauReal.one]
    simp only [TauRat.equiv, TauRat.add, TauRat.mul, TauRat.negate,
               TauRat.zero, TauRat.one, nat_to_taurat, int_to_taurat]
    try rw [equiv_iff_toInt_eq]
    try simp only [toInt_add, toInt_mul, toInt_negate, toInt_nat_to_tauint,
                    toInt_fromNat, toInt_zero, toInt_one]
    try push_cast
    try ring
    try decide

/-- **Conditional `add_pow_equiv_strong_left`** (the binomial theorem on
    TauComplex, in left-assoc internal form, conditional on
    `pascal_combine_target`):

    Given the named-target Pascal combine hypothesis, by induction on n:
    * Base n=0: `add_pow_equiv_left_base`.
    * Step n → n+1: chain via `mul_respects_equiv_right_of_bound` (with
      `add_BoundedBy_compounds` for the (z₁+z₂) bound), then
      `B_left_n_mul_add_eq_sigmas` (which gives Σ_left + Σ_right), then
      `h_pascal` (which gives B_left(n+1)).

    Once `pascal_combine_target` is discharged (Part 3b''''''''''''''''''',
    queued), this conditional theorem becomes unconditional via direct
    application — yielding the binomial theorem on TauComplex in
    strengthened form (with bounds on z₁, z₂). -/
theorem TauComplex.add_pow_equiv_strong_under_pascal_hyp
    (h_pascal : TauComplex.pascal_combine_target)
    (z₁ z₂ : TauComplex) (M : Nat) (hM : 1 ≤ M)
    (h_bound_z1 : TauComplex.BoundedBy z₁ M)
    (h_bound_z2 : TauComplex.BoundedBy z₂ M) (n : Nat) :
    (TauComplex.pow (z₁.add z₂) n).equiv (TauComplex.binomial_left_sum z₁ z₂ n) := by
  induction n with
  | zero => exact TauComplex.add_pow_equiv_left_base z₁ z₂
  | succ n ih =>
    -- Bound on (z₁+z₂) via add_BoundedBy_compounds.
    have h_bound_add := TauComplex.add_BoundedBy_compounds z₁ z₂ M h_bound_z1 h_bound_z2
    have h_2M_pos : 1 ≤ 2 * M := by omega
    -- Step 1: pow (z₁+z₂) n .mul (z₁+z₂) ≈ binomial_left_sum z₁ z₂ n .mul (z₁+z₂)
    --   via mul_respects_equiv_right_of_bound (bound on z₁+z₂) + ih.
    have h_step1 : ((TauComplex.pow (z₁.add z₂) n).mul (z₁.add z₂)).equiv
                    ((TauComplex.binomial_left_sum z₁ z₂ n).mul (z₁.add z₂)) :=
      TauComplex.mul_respects_equiv_right_of_bound _ _ (z₁.add z₂) (2*M) h_2M_pos
        h_bound_add.1 h_bound_add.2 ih
    -- Step 2: binomial_left_sum .mul (z₁+z₂) ≈ binomial_sigma_left + binomial_right_sum
    --   via B_left_n_mul_add_eq_sigmas.
    have h_step2 := TauComplex.B_left_n_mul_add_eq_sigmas z₁ z₂ M hM h_bound_z2 n
    -- Step 3: binomial_sigma_left + binomial_right_sum ≈ binomial_left_sum z₁ z₂ (n+1)
    --   via the named-target hypothesis h_pascal.
    have h_step3 := h_pascal z₁ z₂ M hM h_bound_z1 h_bound_z2 n
    -- Goal: pow (z₁+z₂) (n+1) ≈ binomial_left_sum z₁ z₂ (n+1)
    -- pow (z₁+z₂) (n+1) = (pow (z₁+z₂) n).mul (z₁+z₂) by pow_succ definitionally.
    exact TauComplex.equiv_trans h_step1 (TauComplex.equiv_trans h_step2 h_step3)

-- ============================================================
-- PART 30: PHASE 3C — discharge attempt for pascal_combine_target
-- ============================================================

/-! ## Discharge attempt — recursive named-target hierarchy

To discharge `pascal_combine_target`, we need:
1. `right_sum_reindex` content: `binomial_right_sum z₁ z₂ n ≈ pow z₂ (n+1)
   + binomial_right_shifted z₁ z₂ n`. (Couldn't elaborate as standalone.)
2. `B_left_split_first` content (already shipped, with `(n+1)-(j+1)` form).
3. Nat-arith bridge `(n+1)-(j+1) = n-j` for the sum forms.
4. Add reorganization.

Since (1) hits the elaboration cliff, ship it as ANOTHER named target —
applying the **named-target + later-discharge pattern** recursively.

Then `pascal_combine_target` becomes conditional on this new named target.
The discharge of `right_sum_reindex_target` is queued for a focused
future commit with the right operational tooling.
-/

/-- **[I.D-TauComplex-RightSumReindex-Target]** Named target for the
    right-sum reindex identity:
    `binomial_right_sum z₁ z₂ n ≈ pow z₂ (n+1) + binomial_right_shifted z₁ z₂ n`.

    All sub-pieces are shipped: `sum_split_first`, `first_term_simplify`,
    `right_after_first_to_shifted`. The composition into a single
    theorem hits the elaboration cliff (Part 3b''''''''''''''''').
    Ship as named target; the conditional `pascal_combine` can use it
    as a hypothesis. -/
def TauComplex.right_sum_reindex_target : Prop :=
  ∀ (z₁ z₂ : TauComplex) (M : Nat), 1 ≤ M →
    TauComplex.BoundedBy z₁ M → TauComplex.BoundedBy z₂ M → ∀ (n : Nat),
    (TauComplex.binomial_right_sum z₁ z₂ n).equiv
    ((TauComplex.pow z₂ (n+1)).add (TauComplex.binomial_right_shifted z₁ z₂ n))

/-- **First term of `binomial_right_sum`** (def-name for the i=0 term
    after `sum_split_first`):
    `((fromTauReal (fromNat (Nat.choose n 0))).mul (pow z₁ 0)).mul (pow z₂ ((n-0)+1))`. -/
@[reducible] def TauComplex.binomial_right_first_term (z₁ z₂ : TauComplex) (n : Nat) : TauComplex :=
  ((TauComplex.fromTauReal (TauReal.fromNat (Nat.choose n 0))).mul
    (TauComplex.pow z₁ 0)).mul (TauComplex.pow z₂ ((n - 0) + 1))

/-- **After-first-term sum of `binomial_right_sum`** (def-name for the
    i ≥ 1 part after `sum_split_first`):
    `sum (fun i => ((c_{n,i+1}) · z₁^(i+1)) · z₂^((n-(i+1))+1)) n`. -/
@[reducible] def TauComplex.binomial_right_after_first (z₁ z₂ : TauComplex) (n : Nat) : TauComplex :=
  TauComplex.sum (fun i =>
    ((TauComplex.fromTauReal (TauReal.fromNat (Nat.choose n (i+1)))).mul
      (TauComplex.pow z₁ (i+1))).mul (TauComplex.pow z₂ ((n - (i+1)) + 1))) n

/-- **Sum-split decomposition of `binomial_right_sum`** into def-name
    intermediates: `binomial_right_sum z₁ z₂ n ≈ first_term + after_first`.

    Direct application of `sum_split_first` to the unfolded form of
    `binomial_right_sum`. `@[reducible]` unfolding makes the RHS match
    `sum_split_first`'s output. -/
theorem TauComplex.binomial_right_sum_split (z₁ z₂ : TauComplex) (n : Nat) :
    (TauComplex.binomial_right_sum z₁ z₂ n).equiv
    ((TauComplex.binomial_right_first_term z₁ z₂ n).add
      (TauComplex.binomial_right_after_first z₁ z₂ n)) :=
  TauComplex.sum_split_first (fun i =>
    ((TauComplex.fromTauReal (TauReal.fromNat (Nat.choose n i))).mul
      (TauComplex.pow z₁ i)).mul (TauComplex.pow z₂ ((n - i) + 1))) n

/-- **After-first bridge** in def-name form:
    `binomial_right_after_first z₁ z₂ n ≈ binomial_right_shifted z₁ z₂ n`.

    Both sides @[reducible]-unfold to exactly the LHS and RHS of
    `right_after_first_to_shifted`'s signature — no rfl-bridge needed
    (shapes match syntactically). -/
theorem TauComplex.binomial_right_after_first_to_shifted_def
    (z₁ z₂ : TauComplex) (M : Nat) (hM : 1 ≤ M)
    (h_bound_z1 : TauComplex.BoundedBy z₁ M)
    (h_bound_z2 : TauComplex.BoundedBy z₂ M) (n : Nat) :
    (TauComplex.binomial_right_after_first z₁ z₂ n).equiv
    (TauComplex.binomial_right_shifted z₁ z₂ n) :=
  TauComplex.right_after_first_to_shifted z₁ z₂ M hM h_bound_z1 h_bound_z2 n

/-- **First-term bridge** in def-name form (via `simp only` rfl-rewrites):
    `binomial_right_first_term z₁ z₂ n ≈ pow z₂ (n+1)`.

    The @[reducible]-unfolded form has `Nat.choose n 0`, `pow z₁ 0`,
    `(n-0)+1` which need to rfl-reduce to `1`, `one`, `n+1` for
    `first_term_simplify` to apply. Earlier `exact`/`apply` attempts
    hit whnf-cliff under heavy context. The `simp only` approach
    applies the rfl rewrites stepwise as targeted simp args,
    distributing the cost across smaller normalization passes. -/
theorem TauComplex.binomial_right_first_term_to_pow
    (z₁ z₂ : TauComplex) (M : Nat) (hM : 1 ≤ M)
    (h_bound_z2 : TauComplex.BoundedBy z₂ M) (n : Nat) :
    (TauComplex.binomial_right_first_term z₁ z₂ n).equiv (TauComplex.pow z₂ (n+1)) := by
  unfold TauComplex.binomial_right_first_term
  simp only [Nat.choose_zero_right, TauComplex.pow_zero, Nat.sub_zero]
  exact TauComplex.first_term_simplify z₂ M hM h_bound_z2 n

/-- **🎯 `right_sum_reindex_target` DISCHARGED!**

    Composes `binomial_right_sum_split` + `equiv_add_congr` of
    `binomial_right_first_term_to_pow` and
    `binomial_right_after_first_to_shifted_def`. All three sub-lemmas
    are in def-name form (signature stays compact), and the chain
    elaborates within budget.

    This unlocks the cascade:
    1. `pascal_combine_discharge` via
       `pascal_combine_target_under_right_reindex_hyp` applied to this.
    2. `add_pow_equiv_strong` (the binomial theorem on TauComplex,
       unconditional) via `add_pow_equiv_strong_under_pascal_hyp`
       applied to (1).
    3. Final B_left ↔ B_target bridge → `add_pow_equiv_target_discharged`. -/
theorem TauComplex.right_sum_reindex_discharge :
    TauComplex.right_sum_reindex_target := by
  intro z₁ z₂ M hM h_bound_z1 h_bound_z2 n
  exact TauComplex.equiv_trans
    (TauComplex.binomial_right_sum_split z₁ z₂ n)
    (TauComplex.equiv_add_congr
      (TauComplex.binomial_right_first_term_to_pow z₁ z₂ M hM h_bound_z2 n)
      (TauComplex.binomial_right_after_first_to_shifted_def z₁ z₂ M hM h_bound_z1 h_bound_z2 n))



/-! ### Bridge attempts deferred — rfl-cliff observed (for first_term only)

Two natural bridge theorems would close the chain:
* `binomial_right_first_term z₁ z₂ n ≈ pow z₂ (n+1)` via `first_term_simplify`.
* `binomial_right_after_first z₁ z₂ n ≈ binomial_right_shifted z₁ z₂ n`
  via `right_after_first_to_shifted`.

Both hit a **rfl-bridge cliff**: the `@[reducible]` unfolded form of
`binomial_right_first_term` is rfl-equal to `first_term_simplify`'s LHS
(via `Nat.choose n 0 = 1` + `pow z₁ 0 = one` + `(n-0)+1 = n+1`, all rfl
in Lean 4 core), but the chained rfl-reductions during unification of
heavy expressions exhaust the whnf budget (timed out at 200K, even at
400K from the earlier attempt).

The disciplined response: ship `binomial_right_sum_split` (which works
because `sum_split_first`'s output already uses the rfl-unfolded form
that matches the def names), defer the bridges to a future commit
with a more targeted approach — likely:
* Add a `change` tactic to force Lean's whnf to the explicit form
  before applying the sub-lemma, OR
* Add custom `simp` lemmas that explicitly state the rfl-bridges,
  letting `simp only [...]` perform them stepwise rather than via
  one big whnf call.
-/

/-- **TauComplex add-left-comm** (unconditional ring identity):
    `a + (b + c) ≈ b + (a + c)`.

    Componentwise pointwise reduction with `ring`. Used in
    `pascal_combine_target_under_right_reindex_hyp` for the add
    reorganization `Σ_left + (z₂^(n+1) + S) ≈ z₂^(n+1) + (Σ_left + S)`. -/
theorem taucomplex_add_left_comm (a b c : TauComplex) :
    (a.add (b.add c)).equiv (b.add (a.add c)) := by
  refine ⟨?_, ?_⟩
  · -- Real part
    apply TauReal.equiv_of_pointwise
    intro n
    simp only [TauComplex.add, TauReal.add]
    simp only [TauRat.equiv, TauRat.add]
    try rw [equiv_iff_toInt_eq]
    try simp only [toInt_add, toInt_mul, toInt_fromNat, toInt_zero, toInt_one]
    try push_cast
    try ring
  · -- Imag part
    apply TauReal.equiv_of_pointwise
    intro n
    simp only [TauComplex.add, TauReal.add]
    simp only [TauRat.equiv, TauRat.add]
    try rw [equiv_iff_toInt_eq]
    try simp only [toInt_add, toInt_mul, toInt_fromNat, toInt_zero, toInt_one]
    try push_cast
    try ring

/-- **Conditional discharge of `pascal_combine_target`** given
    `right_sum_reindex_target` as a hypothesis.

    The chain (in def-name form, kept compact via @[reducible] defs):
    1. `equiv_add_congr (refl) h_right`: bridges `binomial_right_sum` to
       `pow z₂ (n+1) + binomial_right_shifted` inside the add.
    2. `taucomplex_add_left_comm`: reorganizes `Σ_left + (z₂ + S) ≈
       z₂ + (Σ_left + S)`.
    3. `equiv_add_congr (refl) (pascal_sum_decompose.symm)`: bridges
       `Σ_left + binomial_right_shifted` to `sum_pascal_LHS_form`.
    4. (Nat-arith bridge — deferred to future part; requires
       `sum_equiv_congr` over `(n+1)-(j+1) = n-j`.)
    5. `B_left_split_first.symm`: bridges `pow z₂ + sum_form_via_succ_sub_succ`
       to `binomial_left_sum z₁ z₂ (n+1)`.

    The Nat-arith bridge (step 4) is the last operational obstacle.
    Once it's discharged, this conditional theorem closes pascal_combine
    under the right_sum_reindex hypothesis.

    Ship as a recursive named target for the Nat-arith bridge to keep
    the chain disciplined. -/
def TauComplex.pascal_LHS_form_bridge_target : Prop :=
  ∀ (z₁ z₂ : TauComplex) (n : Nat),
    (TauComplex.sum (fun j =>
       ((TauComplex.fromTauReal (TauReal.fromNat (Nat.choose (n+1) (j+1)))).mul
         (TauComplex.pow z₁ (j+1))).mul (TauComplex.pow z₂ (n - j))) (n+1)).equiv
    (TauComplex.sum (fun j =>
       ((TauComplex.fromTauReal (TauReal.fromNat (Nat.choose (n+1) (j+1)))).mul
         (TauComplex.pow z₁ (j+1))).mul (TauComplex.pow z₂ ((n+1) - (j+1)))) (n+1))

/-- **Discharge `pascal_LHS_form_bridge_target`** via term-wise
    Nat-arith rewrite `n - j = (n+1) - (j+1)`.

    Both sides of the sum have the same body except for the `z₂` Nat
    exponent. By `Nat.succ_sub_succ_eq_sub`, the two exponents are
    equal as Nats — apply via `sum_equiv_congr` lifted with a
    term-wise rewrite. -/
theorem TauComplex.pascal_LHS_form_bridge_discharge :
    TauComplex.pascal_LHS_form_bridge_target := by
  intro z₁ z₂ n
  apply TauComplex.sum_equiv_congr
  intro i
  have h_eq : n - i = (n+1) - (i+1) := (Nat.succ_sub_succ_eq_sub n i).symm
  rw [h_eq]
  exact TauComplex.equiv_refl _

/-- **Conditional discharge of `pascal_combine_target`** under
    `right_sum_reindex_target` as hypothesis.

    The full chain (7 steps), all kept compact via @[reducible] def names:
    1. `equiv_add_congr (refl) h_right` lifts `binomial_right_sum` to
       `pow z₂ (n+1) + binomial_right_shifted` inside the add.
    2. `taucomplex_add_left_comm` reorganizes
       `Σ_L + (z₂ + R) ≈ z₂ + (Σ_L + R)`.
    3. `pascal_sum_decompose.symm` bridges
       `Σ_L + R ≈ pascal_sum_LHS_form_n-j`.
    4. `equiv_add_congr (refl) ...` lifts through `pow z₂ + _`.
    5. `pascal_LHS_form_bridge_discharge` bridges
       `n-j` form to `(n+1)-(j+1)` form.
    6. `equiv_add_congr (refl) ...` lifts through `pow z₂ + _`.
    7. `B_left_split_first.symm` closes to `binomial_left_sum (n+1)`.

    Once `right_sum_reindex_target` is discharged (queued for future
    part), this conditional theorem becomes the unconditional
    `pascal_combine_discharge`. -/
theorem TauComplex.pascal_combine_target_under_right_reindex_hyp
    (h_right_reindex : TauComplex.right_sum_reindex_target) :
    TauComplex.pascal_combine_target := by
  intro z₁ z₂ M hM h_bound_z1 h_bound_z2 n
  -- Step 0: get the right-sum reindex equiv from the hypothesis.
  have h_right := h_right_reindex z₁ z₂ M hM h_bound_z1 h_bound_z2 n
  -- Step 1: lift h_right through binomial_sigma_left + _
  have h_lift1 := TauComplex.equiv_add_congr
    (TauComplex.equiv_refl (TauComplex.binomial_sigma_left z₁ z₂ n)) h_right
  -- Step 2: reorganize Σ_L + (z₂ + R) ≈ z₂ + (Σ_L + R)
  have h_reorg := taucomplex_add_left_comm
    (TauComplex.binomial_sigma_left z₁ z₂ n)
    (TauComplex.pow z₂ (n+1))
    (TauComplex.binomial_right_shifted z₁ z₂ n)
  -- Step 3: bridge Σ_L + R ≈ pascal_sum_LHS_n-j_form via pascal_sum_decompose.symm
  have h_pascal_sym := TauComplex.equiv_symm
    (TauComplex.pascal_sum_decompose z₁ z₂ M hM h_bound_z1 h_bound_z2 n)
  -- Step 4: lift h_pascal_sym through pow z₂ + _
  have h_lift2 := TauComplex.equiv_add_congr
    (TauComplex.equiv_refl (TauComplex.pow z₂ (n+1))) h_pascal_sym
  -- Step 5: bridge n-j to (n+1)-(j+1) via pascal_LHS_form_bridge_discharge
  have h_bridge := TauComplex.pascal_LHS_form_bridge_discharge z₁ z₂ n
  -- Step 6: lift h_bridge through pow z₂ + _
  have h_lift3 := TauComplex.equiv_add_congr
    (TauComplex.equiv_refl (TauComplex.pow z₂ (n+1))) h_bridge
  -- Step 7: B_left_split_first.symm closes to binomial_left_sum (n+1)
  have h_BL_sym := TauComplex.equiv_symm
    (TauComplex.B_left_split_first z₁ z₂ M hM h_bound_z2 n)
  -- Chain everything
  exact TauComplex.equiv_trans h_lift1
    (TauComplex.equiv_trans h_reorg
      (TauComplex.equiv_trans h_lift2
        (TauComplex.equiv_trans h_lift3 h_BL_sym)))

-- ============================================================
-- PART 31: PHASE 3C — 🎯🎯🎯 THE BINOMIAL THEOREM ON TauComplex! 🎯🎯🎯
-- ============================================================

/-- **🎯 `pascal_combine_target` DISCHARGED (unconditional).**

    Direct application of `pascal_combine_target_under_right_reindex_hyp`
    (Part 3b'''''''''''''''''') to the now-shipped
    `right_sum_reindex_discharge`. -/
theorem TauComplex.pascal_combine_discharge : TauComplex.pascal_combine_target :=
  TauComplex.pascal_combine_target_under_right_reindex_hyp
    TauComplex.right_sum_reindex_discharge

/-- **🎯🎯🎯 BINOMIAL THEOREM ON TauComplex — UNCONDITIONAL!**

    `pow (z₁ + z₂) n ≈ binomial_left_sum z₁ z₂ n` for any `z₁, z₂` with
    common bound `M` (1 ≤ M) and all `n : Nat`.

    Direct application of `add_pow_equiv_strong_under_pascal_hyp`
    (Part 3b''''''''''''''''') to the now-discharged
    `pascal_combine_discharge`. The strengthened form (with bound
    hypothesis) is the one needed downstream for `TauComplex.exp_add`
    (M3 endpoint).

    The bridge to the named-target form `add_pow_equiv_target` (using
    right-assoc inner `c · (z₁^i · z₂^(n-i))`) is queued for the next
    part — it's a term-wise application of `taucomplex_mul_assoc`
    lifted via `sum_equiv_congr`, bound-free. -/
theorem TauComplex.add_pow_equiv_strong
    (z₁ z₂ : TauComplex) (M : Nat) (hM : 1 ≤ M)
    (h_bound_z1 : TauComplex.BoundedBy z₁ M)
    (h_bound_z2 : TauComplex.BoundedBy z₂ M) (n : Nat) :
    (TauComplex.pow (z₁.add z₂) n).equiv (TauComplex.binomial_left_sum z₁ z₂ n) :=
  TauComplex.add_pow_equiv_strong_under_pascal_hyp
    TauComplex.pascal_combine_discharge z₁ z₂ M hM h_bound_z1 h_bound_z2 n

/-- **Bridge `binomial_left_sum ≈ B_target`** — converts the LEFT-assoc
    internal binomial form to the RIGHT-assoc form of the named target
    `add_pow_equiv_target`.

    Term-wise application of `taucomplex_mul_assoc` (bound-free ring
    axiom: `(a·b)·c ≈ a·(b·c)`) lifted to sums via `sum_equiv_congr`. -/
theorem TauComplex.binomial_left_sum_eq_B_target (z₁ z₂ : TauComplex) (n : Nat) :
    (TauComplex.binomial_left_sum z₁ z₂ n).equiv
    (TauComplex.sum (fun i =>
      (TauComplex.fromTauReal (TauReal.fromNat (Nat.choose n i))).mul
        ((TauComplex.pow z₁ i).mul (TauComplex.pow z₂ (n - i)))) (n+1)) := by
  apply TauComplex.sum_equiv_congr
  intro i
  exact taucomplex_mul_assoc _ _ _

/-- **🎯 `add_pow_equiv_target` DISCHARGED (strengthened, with bounds).**

    `pow (z₁+z₂) n ≈ sum (fun i => c · (z₁^i · z₂^(n-i))) (n+1)`.

    This is the named-target form (right-assoc inner) of the binomial
    theorem on TauComplex. Composes `add_pow_equiv_strong` (in left-assoc
    form) with `binomial_left_sum_eq_B_target` (the bridge).

    Note: the original `add_pow_equiv_target` (Part 3b'') had NO bound
    hypotheses. This discharge adds the bound hypotheses (which are
    needed for the proof structure). The bound-free form would require
    a Cauchy-bound-transfer lemma we don't have yet (similar to
    `equiv_pow_congr_target` deferred earlier). -/
theorem TauComplex.add_pow_equiv_target_strong
    (z₁ z₂ : TauComplex) (M : Nat) (hM : 1 ≤ M)
    (h_bound_z1 : TauComplex.BoundedBy z₁ M)
    (h_bound_z2 : TauComplex.BoundedBy z₂ M) (n : Nat) :
    (TauComplex.pow (z₁.add z₂) n).equiv
    (TauComplex.sum (fun i =>
      (TauComplex.fromTauReal (TauReal.fromNat (Nat.choose n i))).mul
        ((TauComplex.pow z₁ i).mul (TauComplex.pow z₂ (n - i)))) (n+1)) :=
  TauComplex.equiv_trans
    (TauComplex.add_pow_equiv_strong z₁ z₂ M hM h_bound_z1 h_bound_z2 n)
    (TauComplex.binomial_left_sum_eq_B_target z₁ z₂ n)

-- ============================================================
-- PART 32: PHASE 3C — TauComplex.scale_by_inv_factorial infrastructure
-- ============================================================

/-! ## Toward `exp_term_add_eq_cauchyDiag_target` discharge

The next M3 step is discharging
`exp_term_add_eq_cauchyDiag_target`:
   `exp_term (z₁+z₂) n ≈ cauchyDiag (exp_term z₁) (exp_term z₂) n`

The proof structure (using the now-shipped binomial theorem):
1. `pow (z₁+z₂) n ≈ Σ_{i=0}^n c_{n,i} · pow z₁ i · pow z₂ (n-i)`
   [add_pow_equiv_target_strong, just shipped].
2. Scale both sides by `1/n!` componentwise:
   LHS becomes `exp_term (z₁+z₂) n`.
   RHS becomes `Σ_{i=0}^n (c_{n,i}/n!) · pow z₁ i · pow z₂ (n-i)`.
3. Use `c_{n,i}/n! = 1/(i!·(n-i)!)` via factorial arithmetic.
4. Reorganize RHS into `Σ_{i=0}^n (pow z₁ i / i!) · (pow z₂ (n-i) / (n-i)!)`.
5. Recognize the RHS as `cauchyDiag (exp_term z₁) (exp_term z₂) n`.

This part ships the TauComplex-level `scale_by_inv_factorial`
infrastructure (currently exp_term uses TauReal.scale_by_inv_factorial
componentwise).
-/

/-- **TauComplex scale-by-inverse-factorial** (componentwise lift):
    `scale_by_inv_factorial z k = ⟨scale (z.re) k, scale (z.im) k⟩`.

    This makes `exp_term z k = scale_by_inv_factorial (pow z k) k` by
    definitional rfl. Used in the discharge of
    `exp_term_add_eq_cauchyDiag_target` to factor out the factorial
    scaling. -/
def TauComplex.scale_by_inv_factorial (z : TauComplex) (k : Nat) : TauComplex :=
  ⟨TauReal.scale_by_inv_factorial z.re k, TauReal.scale_by_inv_factorial z.im k⟩

@[simp] theorem TauComplex.scale_by_inv_factorial_re (z : TauComplex) (k : Nat) :
    (TauComplex.scale_by_inv_factorial z k).re = TauReal.scale_by_inv_factorial z.re k := rfl

@[simp] theorem TauComplex.scale_by_inv_factorial_im (z : TauComplex) (k : Nat) :
    (TauComplex.scale_by_inv_factorial z k).im = TauReal.scale_by_inv_factorial z.im k := rfl

/-- **`exp_term` unfolds to `scale_by_inv_factorial (pow z k) k`** —
    definitional rfl. Makes the factorial-scaling structure of exp_term
    explicit, which is needed to compose with the binomial theorem
    discharge. -/
theorem TauComplex.exp_term_eq_scale_pow (z : TauComplex) (k : Nat) :
    TauComplex.exp_term z k = TauComplex.scale_by_inv_factorial (TauComplex.pow z k) k := rfl

/-- **TauReal.scale_by_inv_factorial respects Cauchy equivalence.**

    If `a ≈ b` (Cauchy-equiv at TauReal level), then `scale a k ≈
    scale b k` with the SAME modulus. The proof: at the toRat level,
    `|scale a k .approx n - scale b k .approx n| = |a.approx n -
    b.approx n| / k!`. Since `k! ≥ 1`, dividing only tightens the
    bound — same modulus suffices. -/
theorem TauReal.scale_by_inv_factorial_respects_equiv
    (a b : TauReal) (k : Nat) (h : TauReal.equiv a b) :
    TauReal.equiv (TauReal.scale_by_inv_factorial a k) (TauReal.scale_by_inv_factorial b k) := by
  obtain ⟨μ, hm⟩ := h
  refine ⟨μ, fun k' n hn => ?_⟩
  have h_step := hm k' n hn
  unfold TauRat.lt at h_step ⊢
  rw [TauRat.toRat_abs, toRat_sub] at h_step
  rw [TauRat.toRat_abs, toRat_sub]
  rw [TauRat.ofNatRecip_toRat] at h_step ⊢
  -- Substitute scale.approx n .toRat = (.approx n).toRat / k!
  have h_a : ((TauReal.scale_by_inv_factorial a k).approx n).toRat =
              (a.approx n).toRat / (k.factorial : Rat) :=
    TauRat.scale_by_inv_factorial_toRat (a.approx n) k
  have h_b : ((TauReal.scale_by_inv_factorial b k).approx n).toRat =
              (b.approx n).toRat / (k.factorial : Rat) :=
    TauRat.scale_by_inv_factorial_toRat (b.approx n) k
  rw [h_a, h_b]
  -- Goal: |a.toRat/k! - b.toRat/k!| < 1/(k'+1)
  have hk_fac_pos : (0 : Rat) < (k.factorial : Rat) := by
    have := Nat.factorial_pos k; exact_mod_cast this
  have hk_fac_ge_one : (1 : Rat) ≤ (k.factorial : Rat) := by
    have h1 : 1 ≤ k.factorial := Nat.factorial_pos k
    exact_mod_cast h1
  -- |a/c - b/c| = |a-b|/c when c > 0
  have h_split :
      |(a.approx n).toRat / (k.factorial : Rat) - (b.approx n).toRat / (k.factorial : Rat)|
      = |(a.approx n).toRat - (b.approx n).toRat| / (k.factorial : Rat) := by
    rw [← sub_div, abs_div, abs_of_pos hk_fac_pos]
  rw [h_split]
  -- |...|/k! ≤ |...| since k! ≥ 1
  have h_abs_nn : (0 : Rat) ≤ |(a.approx n).toRat - (b.approx n).toRat| := by positivity
  have h_le : |(a.approx n).toRat - (b.approx n).toRat| / (k.factorial : Rat)
              ≤ |(a.approx n).toRat - (b.approx n).toRat| :=
    div_le_self h_abs_nn hk_fac_ge_one
  linarith

/-- **TauComplex.scale_by_inv_factorial respects equiv** (componentwise
    lift of the TauReal version).

    If `z ≈ z'` (TauComplex.equiv, i.e., componentwise TauReal.equiv on
    re and im), then `scale z k ≈ scale z' k`. Componentwise via
    `TauReal.scale_by_inv_factorial_respects_equiv`. -/
theorem TauComplex.scale_by_inv_factorial_respects_equiv
    (z z' : TauComplex) (k : Nat) (h : z.equiv z') :
    (TauComplex.scale_by_inv_factorial z k).equiv (TauComplex.scale_by_inv_factorial z' k) :=
  ⟨TauReal.scale_by_inv_factorial_respects_equiv z.re z'.re k h.1,
   TauReal.scale_by_inv_factorial_respects_equiv z.im z'.im k h.2⟩

/-- **TauRat-level scale-add distributivity** (via `TauRat.equiv` =
    toRat-equality): `scale (p + q) k ≈ scale p k + scale q k`.

    Both sides have toRat `(p.toRat + q.toRat) / k!`. Proof: unfold
    via `scale_by_inv_factorial_toRat` and `toRat_add`, close by `ring`. -/
theorem TauRat.scale_by_inv_factorial_add_equiv (p q : TauRat) (k : Nat) :
    TauRat.equiv (TauRat.scale_by_inv_factorial (p.add q) k)
                 ((TauRat.scale_by_inv_factorial p k).add (TauRat.scale_by_inv_factorial q k)) := by
  rw [equiv_iff_toRat_eq, TauRat.scale_by_inv_factorial_toRat, toRat_add, toRat_add,
      TauRat.scale_by_inv_factorial_toRat, TauRat.scale_by_inv_factorial_toRat]
  have hk_fac_pos : (0 : Rat) < (k.factorial : Rat) := by
    have := Nat.factorial_pos k; exact_mod_cast this
  field_simp

/-- **TauReal.scale_by_inv_factorial distributes over add**:
    `scale (a + b) k ≈ scale a k + scale b k`.

    Componentwise lift via `equiv_of_pointwise` of the TauRat-level identity. -/
theorem TauReal.scale_by_inv_factorial_distrib_add (a b : TauReal) (k : Nat) :
    (TauReal.scale_by_inv_factorial (a.add b) k).equiv
    ((TauReal.scale_by_inv_factorial a k).add (TauReal.scale_by_inv_factorial b k)) := by
  apply TauReal.equiv_of_pointwise
  intro m
  exact TauRat.scale_by_inv_factorial_add_equiv (a.approx m) (b.approx m) k

/-- **TauComplex.scale_by_inv_factorial distributes over add**:
    `scale (z + w) k ≈ scale z k + scale w k`.

    Componentwise lift of `TauReal.scale_by_inv_factorial_distrib_add`. -/
theorem TauComplex.scale_by_inv_factorial_distrib_add (z w : TauComplex) (k : Nat) :
    (TauComplex.scale_by_inv_factorial (z.add w) k).equiv
    ((TauComplex.scale_by_inv_factorial z k).add (TauComplex.scale_by_inv_factorial w k)) :=
  ⟨TauReal.scale_by_inv_factorial_distrib_add z.re w.re k,
   TauReal.scale_by_inv_factorial_distrib_add z.im w.im k⟩

/-- **scale_by_inv_factorial of zero ≈ zero**.

    At TauRat level, `scale TauRat.zero k` has num=0, den=k!, hence
    toRat = 0/k! = 0. So pointwise toRat-equal to TauRat.zero. -/
theorem TauReal.scale_by_inv_factorial_zero (k : Nat) :
    (TauReal.scale_by_inv_factorial TauReal.zero k).equiv TauReal.zero := by
  apply TauReal.equiv_of_pointwise
  intro m
  rw [equiv_iff_toRat_eq, TauReal.scale_by_inv_factorial_approx,
      TauRat.scale_by_inv_factorial_toRat]
  show ((TauReal.zero.approx m).toRat) / (k.factorial : Rat) = (TauReal.zero.approx m).toRat
  rw [show (TauReal.zero.approx m) = TauRat.zero from rfl, toRat_zero]
  simp

theorem TauComplex.scale_by_inv_factorial_zero (k : Nat) :
    (TauComplex.scale_by_inv_factorial TauComplex.zero k).equiv TauComplex.zero :=
  ⟨TauReal.scale_by_inv_factorial_zero k, TauReal.scale_by_inv_factorial_zero k⟩

/-- **TauComplex.scale_by_inv_factorial distributes over sum**:
    `scale (sum f m) k ≈ sum (fun i => scale (f i) k) m`.

    Proof: induction on `m`. Base case uses `scale_zero ≈ zero`. Step
    uses `scale_distrib_add` + IH via `equiv_trans` + `equiv_add_congr`. -/
theorem TauComplex.scale_by_inv_factorial_distrib_sum
    (f : Nat → TauComplex) (m k : Nat) :
    (TauComplex.scale_by_inv_factorial (TauComplex.sum f m) k).equiv
    (TauComplex.sum (fun i => TauComplex.scale_by_inv_factorial (f i) k) m) := by
  induction m with
  | zero =>
    -- sum f 0 = zero; sum (scale ∘ f) 0 = zero. scale zero k ≈ zero.
    show (TauComplex.scale_by_inv_factorial TauComplex.zero k).equiv TauComplex.zero
    exact TauComplex.scale_by_inv_factorial_zero k
  | succ m ih =>
    -- sum f (m+1) = (sum f m).add (f m) by sum_succ.
    -- Apply scale_distrib_add to bridge scale(sum f m + f m) ≈ scale(sum f m) + scale(f m).
    -- Then ih on the first part + equiv_refl on the second.
    show (TauComplex.scale_by_inv_factorial ((TauComplex.sum f m).add (f m)) k).equiv
          ((TauComplex.sum (fun i => TauComplex.scale_by_inv_factorial (f i) k) m).add
            (TauComplex.scale_by_inv_factorial (f m) k))
    apply TauComplex.equiv_trans
      (TauComplex.scale_by_inv_factorial_distrib_add (TauComplex.sum f m) (f m) k)
    exact TauComplex.equiv_add_congr ih (TauComplex.equiv_refl _)

/-- **Factorial split at choose** (Rat-level): for `i ≤ n`,
    `(C(n,i) : Rat) / n! = 1 / (i! · (n-i)!)`.

    Foundational arithmetic identity for the factorial-split step in
    `exp_term_add_eq_cauchyDiag_target` discharge. Direct consequence
    of the combinatorial identity `C(n,i) · i! · (n-i)! = n!`
    (`Nat.choose_mul_factorial_mul_factorial`) cast to Rat. -/
theorem TauRat.choose_div_factorial_eq (n i : Nat) (h : i ≤ n) :
    ((Nat.choose n i : Rat) / (n.factorial : Rat))
    = 1 / ((i.factorial : Rat) * ((n - i).factorial : Rat)) := by
  -- Nat-level combinatorial identity
  have h_combinatorial : Nat.choose n i * i.factorial * (n - i).factorial = n.factorial :=
    Nat.choose_mul_factorial_mul_factorial h
  have h_rat : (Nat.choose n i : Rat) * (i.factorial : Rat) * ((n - i).factorial : Rat)
             = (n.factorial : Rat) := by exact_mod_cast h_combinatorial
  -- Factorial positivity for field_simp
  have hi_ne : (i.factorial : Rat) ≠ 0 := by
    have := Nat.factorial_pos i; exact_mod_cast this.ne'
  have hni_ne : ((n - i).factorial : Rat) ≠ 0 := by
    have := Nat.factorial_pos (n - i); exact_mod_cast this.ne'
  have hn_ne : (n.factorial : Rat) ≠ 0 := by
    have := Nat.factorial_pos n; exact_mod_cast this.ne'
  field_simp
  linear_combination h_rat

/-- **Term-wise scale-binom equals cauchyDiag-term** (strengthened with
    `i ≤ n` hypothesis to use `choose_div_factorial_eq`):

    `scale (c_{n,i} · (pow z₁ i · pow z₂ (n-i))) n ≈
     exp_term z₁ i · exp_term z₂ (n-i)`

    where `c_{n,i} = fromTauReal (fromNat (Nat.choose n i))`.

    The key arithmetic identity: at TauRat toRat level, both sides
    reduce to `(X.re·Y.re - X.im·Y.im) / (i!·(n-i)!)` for .re, where
    X = pow z₁ i and Y = pow z₂ (n-i). The bridge uses
    `choose_div_factorial_eq`. -/
theorem TauComplex.scale_binom_term_eq_cauchyDiag_term
    (z₁ z₂ : TauComplex) (n i : Nat) (h_le : i ≤ n) :
    (TauComplex.scale_by_inv_factorial
      ((TauComplex.fromTauReal (TauReal.fromNat (Nat.choose n i))).mul
        ((TauComplex.pow z₁ i).mul (TauComplex.pow z₂ (n - i)))) n).equiv
    ((TauComplex.exp_term z₁ i).mul (TauComplex.exp_term z₂ (n - i))) := by
  -- Helper: `(nat_to_taurat k).toRat = k` as a Rat (not a named simp lemma in core).
  have h_nat_to_taurat : ∀ k : Nat, (nat_to_taurat k).toRat = (k : Rat) := by
    intro k
    simp only [nat_to_taurat, int_to_taurat, nat_to_tauint, TauRat.toRat,
               TauInt.toInt, TauInt.fromNat]
    push_cast; ring
  -- Nat-level combinatorial identity, cast to Rat.
  have h_combinatorial : Nat.choose n i * i.factorial * (n - i).factorial = n.factorial :=
    Nat.choose_mul_factorial_mul_factorial h_le
  have h_mul : (Nat.choose n i : Rat) * (i.factorial : Rat) * ((n - i).factorial : Rat)
             = (n.factorial : Rat) := by exact_mod_cast h_combinatorial
  have hn_pos : (0 : Rat) < (n.factorial : Rat) := by
    have := Nat.factorial_pos n; exact_mod_cast this
  have hi_pos : (0 : Rat) < (i.factorial : Rat) := by
    have := Nat.factorial_pos i; exact_mod_cast this
  have hni_pos : (0 : Rat) < ((n - i).factorial : Rat) := by
    have := Nat.factorial_pos (n - i); exact_mod_cast this
  refine ⟨?_, ?_⟩
  · -- Real part: prove via pointwise TauRat toRat equality.
    apply TauReal.equiv_of_pointwise
    intro m
    rw [equiv_iff_toRat_eq]
    simp only [TauComplex.scale_by_inv_factorial_re, TauComplex.exp_term_re,
               TauComplex.exp_term_im, TauComplex.mul, TauComplex.fromTauReal,
               TauReal.sub, TauReal.add, TauReal.mul, TauReal.negate,
               TauReal.zero, TauReal.one,
               TauReal.scale_by_inv_factorial_approx, TauRat.scale_by_inv_factorial_toRat,
               TauReal.fromNat, TauReal.fromTauRat,
               toRat_sub, toRat_add, toRat_mul, toRat_negate, toRat_zero,
               h_nat_to_taurat]
    field_simp
    linear_combination
      (((TauComplex.pow z₁ i).re.approx m).toRat * ((TauComplex.pow z₂ (n - i)).re.approx m).toRat
       - ((TauComplex.pow z₁ i).im.approx m).toRat * ((TauComplex.pow z₂ (n - i)).im.approx m).toRat)
      * h_mul
  · -- Imag part: similar.
    apply TauReal.equiv_of_pointwise
    intro m
    rw [equiv_iff_toRat_eq]
    simp only [TauComplex.scale_by_inv_factorial_im, TauComplex.exp_term_re,
               TauComplex.exp_term_im, TauComplex.mul, TauComplex.fromTauReal,
               TauReal.sub, TauReal.add, TauReal.mul, TauReal.negate,
               TauReal.zero,
               TauReal.scale_by_inv_factorial_approx, TauRat.scale_by_inv_factorial_toRat,
               TauReal.fromNat, TauReal.fromTauRat,
               toRat_sub, toRat_add, toRat_mul, toRat_negate, toRat_zero,
               h_nat_to_taurat]
    simp only [mul_zero, zero_mul, zero_add, add_zero, sub_zero, zero_sub]
    field_simp
    linear_combination
      (((TauComplex.pow z₁ i).re.approx m).toRat * ((TauComplex.pow z₂ (n - i)).im.approx m).toRat
       + ((TauComplex.pow z₁ i).im.approx m).toRat * ((TauComplex.pow z₂ (n - i)).re.approx m).toRat)
      * h_mul

/-- **🎯 `exp_term_add_eq_cauchyDiag_target` DISCHARGED (strengthened with
    bounds).**

    `exp_term (z₁+z₂) n ≈ cauchyDiag (exp_term z₁) (exp_term z₂) n` for
    any `z₁, z₂` with common bound `M ≥ 1` and all `n : Nat`.

    The strengthened form (with bounds) chains:
    1. `add_pow_equiv_target_strong` — `pow (z₁+z₂) n ≈ binomial_sum`.
    2. `scale_by_inv_factorial_respects_equiv` — lift through scaling.
       This converts `exp_term (z₁+z₂) n = scale (pow ...) n` to
       `≈ scale (binomial_sum) n` (the rfl-bridge from
       `exp_term_eq_scale_pow` is implicit).
    3. `scale_by_inv_factorial_distrib_sum` — push scaling inside sum.
    4. `sum_equiv_congr_bounded` + `scale_binom_term_eq_cauchyDiag_term`
       — term-wise bridge to the cauchyDiag form (using `i ≤ n` from
       the sum's `i < n+1` range).
    5. The RHS of `h_terms` is `sum (fun i => (exp_term z₁ i).mul
       (exp_term z₂ (n-i))) (n+1)`, which is `cauchyDiag (exp_term z₁)
       (exp_term z₂) n` by definitional rfl.

    The named target `exp_term_add_eq_cauchyDiag_target` was shipped at
    `072fbbe` (Wave Γ₇ Phase 3C Part 3b) with NO bound hypotheses; this
    strengthened discharge adds bounds (required by the binomial theorem
    chain). The bound-free form would require a Cauchy-bound-transfer
    lemma, deferred. -/
theorem TauComplex.exp_term_add_eq_cauchyDiag_target_strong
    (z₁ z₂ : TauComplex) (M : Nat) (hM : 1 ≤ M)
    (h_bound_z1 : TauComplex.BoundedBy z₁ M)
    (h_bound_z2 : TauComplex.BoundedBy z₂ M) (n : Nat) :
    (TauComplex.exp_term (z₁.add z₂) n).equiv
    (TauComplex.cauchyDiag (TauComplex.exp_term z₁) (TauComplex.exp_term z₂) n) := by
  -- Step 1: binomial theorem.
  have h_binom :=
    TauComplex.add_pow_equiv_target_strong z₁ z₂ M hM h_bound_z1 h_bound_z2 n
  -- Step 2: lift through scaling.
  have h_scale := TauComplex.scale_by_inv_factorial_respects_equiv
    (TauComplex.pow (z₁.add z₂) n)
    (TauComplex.sum (fun i =>
      (TauComplex.fromTauReal (TauReal.fromNat (Nat.choose n i))).mul
        ((TauComplex.pow z₁ i).mul (TauComplex.pow z₂ (n - i)))) (n+1)) n h_binom
  -- Step 3: distribute scaling over the sum.
  have h_distrib := TauComplex.scale_by_inv_factorial_distrib_sum
    (fun i => (TauComplex.fromTauReal (TauReal.fromNat (Nat.choose n i))).mul
                ((TauComplex.pow z₁ i).mul (TauComplex.pow z₂ (n - i))))
    (n+1) n
  -- Step 4: term-wise bridge via sum_equiv_congr_bounded.
  have h_terms :
      (TauComplex.sum (fun i =>
        TauComplex.scale_by_inv_factorial
          ((TauComplex.fromTauReal (TauReal.fromNat (Nat.choose n i))).mul
            ((TauComplex.pow z₁ i).mul (TauComplex.pow z₂ (n - i)))) n) (n+1)).equiv
      (TauComplex.sum (fun i =>
        (TauComplex.exp_term z₁ i).mul (TauComplex.exp_term z₂ (n - i))) (n+1)) := by
    apply TauComplex.sum_equiv_congr_bounded
    intro i hi
    -- hi : i < n + 1, i.e., i ≤ n.
    have h_le : i ≤ n := Nat.le_of_lt_succ hi
    exact TauComplex.scale_binom_term_eq_cauchyDiag_term z₁ z₂ n i h_le
  -- Chain: exp_term = scale ∘ pow (by exp_term_eq_scale_pow, rfl), then h_scale,
  --         then h_distrib, then h_terms. The RHS of h_terms = cauchyDiag by defn.
  exact TauComplex.equiv_trans h_scale
    (TauComplex.equiv_trans h_distrib h_terms)

/-- **🎯 `exp_partial_add_eq_cauchyPStar_target` DISCHARGED (strengthened
    with bounds).**

    `exp_partial (z₁+z₂) n ≈ cauchyPStar (exp_term z₁) (exp_term z₂) n`
    for any `z₁, z₂` with common bound `M ≥ 1` and all `n : Nat`.

    Direct induction on n using:
    * Base case (n=0): `exp_partial_add_eq_cauchyPStar_base`.
    * Step case: `equiv_add_congr` of IH and the term-wise discharge
      `exp_term_add_eq_cauchyDiag_target_strong`.

    This pattern is exactly the one from the conditional theorem
    `exp_partial_add_eq_cauchyPStar_under_term_hyp` (Phase 3C Part 3a),
    but using our strengthened term identity (with bounds) directly. -/
theorem TauComplex.exp_partial_add_eq_cauchyPStar_target_strong
    (z₁ z₂ : TauComplex) (M : Nat) (hM : 1 ≤ M)
    (h_bound_z1 : TauComplex.BoundedBy z₁ M)
    (h_bound_z2 : TauComplex.BoundedBy z₂ M) (n : Nat) :
    (TauComplex.exp_partial (z₁.add z₂) n).equiv
    (TauComplex.cauchyPStar (TauComplex.exp_term z₁) (TauComplex.exp_term z₂) n) := by
  induction n with
  | zero => exact TauComplex.exp_partial_add_eq_cauchyPStar_base z₁ z₂
  | succ n ih =>
    show (TauComplex.exp_partial (z₁.add z₂) (n + 1)).equiv
          (TauComplex.cauchyPStar (TauComplex.exp_term z₁) (TauComplex.exp_term z₂) (n + 1))
    rw [TauComplex.exp_partial_succ, TauComplex.cauchyPStar_succ]
    exact TauComplex.equiv_add_congr ih
      (TauComplex.exp_term_add_eq_cauchyDiag_target_strong z₁ z₂ M hM h_bound_z1 h_bound_z2 n)

-- ============================================================
-- PART 33: PHASE 3C — TauComplex.exp diagonal construction
-- ============================================================

/-! ## TauComplex.exp via diagonal construction

Toward Part 3e (M3 endpoint), we define `TauComplex.exp z` via the
diagonal-sequence construction that mirrors `TauReal.exp` (TauRealExp.lean
line 150).

### The construction

`TauReal.exp a := ⟨fun n => TauRat.exp_partial (a.approx n) n⟩` — the
n-th approximation uses `a`'s n-th value AND truncates the Taylor
series at depth `n`. As both advance, the partial sum converges to
exp(a).

For `TauComplex.exp z`, we lift componentwise:
* `(TauComplex.exp z).re.approx n = (TauComplex.exp_partial z n).re.approx n`.
* `(TauComplex.exp z).im.approx n = (TauComplex.exp_partial z n).im.approx n`.

So each component is a TauReal whose n-th approximation is the
diagonal `(exp_partial z n).{re,im}.approx n`.
-/

/-- **TauComplex exp: diagonal construction.**

    `(exp z).re.approx n = (exp_partial z n).re.approx n`
    `(exp z).im.approx n = (exp_partial z n).im.approx n`

    Mirrors `TauReal.exp` (TauRealExp.lean) componentwise. Both the
    Taylor depth and the TauReal approximation advance with n, giving
    a diagonal sequence that converges to the genuine `exp z`. -/
def TauComplex.exp (z : TauComplex) : TauComplex :=
  ⟨⟨fun n => (TauComplex.exp_partial z n).re.approx n⟩,
   ⟨fun n => (TauComplex.exp_partial z n).im.approx n⟩⟩

@[simp] theorem TauComplex.exp_re_approx (z : TauComplex) (n : Nat) :
    (TauComplex.exp z).re.approx n = (TauComplex.exp_partial z n).re.approx n := rfl

@[simp] theorem TauComplex.exp_im_approx (z : TauComplex) (n : Nat) :
    (TauComplex.exp z).im.approx n = (TauComplex.exp_partial z n).im.approx n := rfl

-- ============================================================
-- PART 34: PHASE 3C PART 3c.1 — TauComplex.sum approx-bridge to TauRat.sum
-- ============================================================

/-! ## Foundation for the Cauchy product bound at TauComplex (Part 3c)

The next M3 milestone is the **Cauchy product bound at TauComplex** —
a componentwise lift of `TauRat.cauchy_product_bound` (TauRealSum.lean
line 339). To make that lift work, we first need a structural bridge:
`TauComplex.sum`'s `.re.approx m` (resp. `.im.approx m`) coincides
pointwise with `TauRat.sum` applied to the componentwise approximation
sequence.

### The bridge

`(TauComplex.sum f n).re.approx m = TauRat.sum (fun i => (f i).re.approx m) n`
`(TauComplex.sum f n).im.approx m = TauRat.sum (fun i => (f i).im.approx m) n`

Both follow by induction on `n`:
* **Base** `n = 0`: both sides are `TauRat.zero` by rfl (TauComplex.zero
  unfolds to `⟨TauReal.zero, TauReal.zero⟩` and `TauReal.zero.approx _
  = TauRat.zero`).
* **Step** `n + 1`: both sides reduce to `TauRat.add (recursive_part)
  ((f n).re.approx m)` by unfolding `TauComplex.add` → `TauReal.add`
  → `TauRat.add`; the recursive parts agree by IH.

### Why this matters

Once we have this bridge, we can chain through:
1. `(TauComplex.exp_partial z₁ n).re.approx m * (TauComplex.exp_partial z₂ n).re.approx m`
   → unfold via `.re.approx`-of-mul → componentwise TauRat products
   → applying `TauRat.cauchy_product_bound` componentwise.
2. The TauRat-level bound transfers back to TauReal-level bound via
   `TauReal.lt_of_approx_bound` and similar magnitude lemmas.
3. The componentwise TauReal bound combines into a `TauComplex.abs`
   bound for the full Cauchy product, which is the structural shape
   of the M3 endpoint.

This is the structural prerequisite for Part 3c.2 (Cauchy-product
approx-bridge) through Part 3c.4 (the full bound). -/

/-- **TauComplex.sum_re_approx**: real-part-of-partial-sum bridge.

    The real-part-then-approximate of a TauComplex partial sum equals
    the TauRat partial sum of the real-part-then-approximate sequence.

    Proof: induction on `n`; both sides reduce to `TauRat.add` of the
    recursive part with `(f n).re.approx m` by unfolding `TauComplex.add`
    → `TauReal.add` → `TauRat.add`. The recursive parts agree by IH. -/
theorem TauComplex.sum_re_approx (f : Nat → TauComplex) (n m : Nat) :
    (TauComplex.sum f n).re.approx m = TauRat.sum (fun i => (f i).re.approx m) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show TauRat.add ((TauComplex.sum f n).re.approx m) ((f n).re.approx m)
       = TauRat.add (TauRat.sum (fun i => (f i).re.approx m) n) ((f n).re.approx m)
    rw [ih]

/-- **TauComplex.sum_im_approx**: imaginary-part-of-partial-sum bridge.

    Symmetric to `sum_re_approx`. Same proof strategy. -/
theorem TauComplex.sum_im_approx (f : Nat → TauComplex) (n m : Nat) :
    (TauComplex.sum f n).im.approx m = TauRat.sum (fun i => (f i).im.approx m) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show TauRat.add ((TauComplex.sum f n).im.approx m) ((f n).im.approx m)
       = TauRat.add (TauRat.sum (fun i => (f i).im.approx m) n) ((f n).im.approx m)
    rw [ih]

-- ============================================================
-- PART 35: PHASE 3C PART 3c.2 — TauComplex.mul approx-bridge to TauRat ops
-- ============================================================

/-! ## Componentwise mul bridges to TauRat arithmetic

The TauComplex multiplication formula `(a+bi)(c+di) = (ac-bd) + (ad+bc)i`
becomes, at the `.approx m` level, a pair of definitional identities
involving `TauRat.sub`, `TauRat.add`, `TauRat.mul` of the componentwise
approximations.

These hold by **rfl** since:
* `TauComplex.mul x y = ⟨TauReal.sub (mul x.re y.re) (mul x.im y.im),
    TauReal.add (mul x.re y.im) (mul x.im y.re)⟩`
* `TauReal.sub a b = a.add b.negate`, so `.approx m` is `TauRat.add ...
  (TauRat.negate ...)` = `TauRat.sub ... ...` (also rfl).
* `TauReal.add` and `TauReal.mul` unfold pointwise to `TauRat.add` and
  `TauRat.mul`.

These will be combined with `sum_re_approx`/`sum_im_approx` in Part 3c.4
to express `(TauComplex.cauchyDiag a b n).{re,im}.approx m` as a TauRat
sum of TauRat sums/sub/mul expressions, then bounded via
`TauRat.cauchy_product_bound` componentwise. -/

/-- **TauComplex.mul_re_approx**: real-part-of-mul as TauRat `sub-of-mul`.

    `(x · y).re.approx m = (x.re · y.re).approx m - (x.im · y.im).approx m`,
    where each `(_ · _).approx m` reduces to `TauRat.mul (_.approx m)
    (_.approx m)` by `TauReal.mul`'s pointwise definition. -/
theorem TauComplex.mul_re_approx (x y : TauComplex) (m : Nat) :
    (TauComplex.mul x y).re.approx m
      = TauRat.sub (TauRat.mul (x.re.approx m) (y.re.approx m))
                   (TauRat.mul (x.im.approx m) (y.im.approx m)) := rfl

/-- **TauComplex.mul_im_approx**: imaginary-part-of-mul as TauRat `add-of-mul`.

    `(x · y).im.approx m = (x.re · y.im).approx m + (x.im · y.re).approx m`. -/
theorem TauComplex.mul_im_approx (x y : TauComplex) (m : Nat) :
    (TauComplex.mul x y).im.approx m
      = TauRat.add (TauRat.mul (x.re.approx m) (y.im.approx m))
                   (TauRat.mul (x.im.approx m) (y.re.approx m)) := rfl

-- ============================================================
-- PART 36: PHASE 3C PART 3c.3 — TauComplex.cauchyDiag componentwise expansion
-- ============================================================

/-! ## Componentwise cauchyDiag expansion

Combining `sum_re_approx` (Part 3c.1) and `mul_re_approx` (Part 3c.2)
expresses `(TauComplex.cauchyDiag a b k).{re,im}.approx m` as a
`TauRat.sum` of the appropriate `TauRat.sub` / `TauRat.add` of cross
products of the componentwise approximations.

These are the "double Cauchy" structural expansions:
* **Real part**: `Σᵢ [(aᵢ.re · b_{k-i}.re) − (aᵢ.im · b_{k-i}.im)]` (real
  part of complex product mixes re·re minus im·im).
* **Imaginary part**: `Σᵢ [(aᵢ.re · b_{k-i}.im) + (aᵢ.im · b_{k-i}.re)]`
  (imaginary part mixes re·im plus im·re).

At the `.toRat` level these split into a difference (resp. sum) of two
genuine `TauRat.cauchyDiag` expressions, but we keep the structural
form here to avoid premature `.toRat`-projection. -/

/-- **TauComplex.cauchyDiag_re_approx**: structural expansion of the
    real part of `cauchyDiag` at `.approx m` level.

    `(TauComplex.cauchyDiag a b k).re.approx m
       = TauRat.sum (fun i => (aᵢ.re · b_{k-i}.re) − (aᵢ.im · b_{k-i}.im)) (k+1)` -/
theorem TauComplex.cauchyDiag_re_approx (a b : Nat → TauComplex) (k m : Nat) :
    (TauComplex.cauchyDiag a b k).re.approx m
      = TauRat.sum (fun i =>
          TauRat.sub
            (TauRat.mul ((a i).re.approx m) ((b (k - i)).re.approx m))
            (TauRat.mul ((a i).im.approx m) ((b (k - i)).im.approx m)))
        (k + 1) := by
  show (TauComplex.sum (fun i => (a i).mul (b (k - i))) (k + 1)).re.approx m
     = _
  rw [TauComplex.sum_re_approx]
  rfl

/-- **TauComplex.cauchyDiag_im_approx**: structural expansion of the
    imaginary part of `cauchyDiag` at `.approx m` level.

    `(TauComplex.cauchyDiag a b k).im.approx m
       = TauRat.sum (fun i => (aᵢ.re · b_{k-i}.im) + (aᵢ.im · b_{k-i}.re)) (k+1)` -/
theorem TauComplex.cauchyDiag_im_approx (a b : Nat → TauComplex) (k m : Nat) :
    (TauComplex.cauchyDiag a b k).im.approx m
      = TauRat.sum (fun i =>
          TauRat.add
            (TauRat.mul ((a i).re.approx m) ((b (k - i)).im.approx m))
            (TauRat.mul ((a i).im.approx m) ((b (k - i)).re.approx m)))
        (k + 1) := by
  show (TauComplex.sum (fun i => (a i).mul (b (k - i))) (k + 1)).im.approx m
     = _
  rw [TauComplex.sum_im_approx]
  rfl

/-- **TauComplex.cauchyPStar_re_approx**: structural expansion of the
    real part of `cauchyPStar` at `.approx m` level.

    `(TauComplex.cauchyPStar a b N).re.approx m
       = TauRat.sum (fun k => (cauchyDiag a b k).re.approx m) N`

    Follows from `sum_re_approx` applied to the outer sum. -/
theorem TauComplex.cauchyPStar_re_approx (a b : Nat → TauComplex) (N m : Nat) :
    (TauComplex.cauchyPStar a b N).re.approx m
      = TauRat.sum (fun k => (TauComplex.cauchyDiag a b k).re.approx m) N := by
  show (TauComplex.sum (TauComplex.cauchyDiag a b) N).re.approx m = _
  rw [TauComplex.sum_re_approx]

/-- **TauComplex.cauchyPStar_im_approx**: structural expansion of the
    imaginary part of `cauchyPStar` at `.approx m` level. -/
theorem TauComplex.cauchyPStar_im_approx (a b : Nat → TauComplex) (N m : Nat) :
    (TauComplex.cauchyPStar a b N).im.approx m
      = TauRat.sum (fun k => (TauComplex.cauchyDiag a b k).im.approx m) N := by
  show (TauComplex.sum (TauComplex.cauchyDiag a b) N).im.approx m = _
  rw [TauComplex.sum_im_approx]

-- ============================================================
-- PART 37: PHASE 3C PART 3c.4 — TauRat.sum distribution at toRat level
-- ============================================================

/-! ## TauRat sum distribution over add/sub at toRat level

To express the `.re.approx m .toRat` (resp. `.im`) of TauComplex's
Cauchy product as a difference (resp. sum) of two genuine TauRat
`cauchyPStar`s, we need basic sum-distribution lemmas at toRat level:

* `TauRat.sum_add_toRat`: `(Σᵢ (fᵢ + gᵢ)).toRat = (Σᵢ fᵢ).toRat + (Σᵢ gᵢ).toRat`
* `TauRat.sum_sub_toRat`: `(Σᵢ (fᵢ − gᵢ)).toRat = (Σᵢ fᵢ).toRat − (Σᵢ gᵢ).toRat`

Both proved by induction on `n`, using `TauRat.sum_succ`,
`TauRat.toRat_add`, `TauRat.toRat_sub`, and `ring`. -/

/-- **TauRat sum add-distribution at toRat level**. -/
theorem TauRat.sum_add_toRat (f g : Nat → TauRat) (n : Nat) :
    (TauRat.sum (fun i => (f i).add (g i)) n).toRat
      = (TauRat.sum f n).toRat + (TauRat.sum g n).toRat := by
  induction n with
  | zero => simp [TauRat.sum_zero, toRat_zero]
  | succ n ih =>
    simp only [TauRat.sum_succ, toRat_add]
    rw [ih]
    ring

/-- **TauRat sum sub-distribution at toRat level**. -/
theorem TauRat.sum_sub_toRat (f g : Nat → TauRat) (n : Nat) :
    (TauRat.sum (fun i => (f i).sub (g i)) n).toRat
      = (TauRat.sum f n).toRat - (TauRat.sum g n).toRat := by
  induction n with
  | zero => simp [TauRat.sum_zero, toRat_zero]
  | succ n ih =>
    simp only [TauRat.sum_succ, toRat_add, toRat_sub]
    rw [ih]
    ring

-- ============================================================
-- PART 38: PHASE 3C PART 3c.5 — TauComplex Cauchy toRat-level splits
-- ============================================================

/-! ## TauComplex cauchyDiag / cauchyPStar toRat-level splits

Combining Part 3c.3 (componentwise expansions) with Part 3c.4
(sum_add/sub_toRat distributivity), we obtain the **toRat-level
structural splits** — the key identities that express the real (resp.
imaginary) part of TauComplex's Cauchy product at `.toRat` level as a
**difference** (resp. **sum**) of two genuine `TauRat.cauchyDiag` /
`cauchyPStar` `.toRat` expressions.

These identities are exactly what allows `TauRat.cauchy_product_bound`
(TauRealSum.lean line 339) to apply componentwise:

* `(TauComplex.cauchyDiag a b k).re.approx m .toRat
    = (TauRat.cauchyDiag re_a re_b k).toRat − (TauRat.cauchyDiag im_a im_b k).toRat`
* `(TauComplex.cauchyDiag a b k).im.approx m .toRat
    = (TauRat.cauchyDiag re_a im_b k).toRat + (TauRat.cauchyDiag im_a re_b k).toRat`
* analogous for `cauchyPStar`.

Where `re_a m i := (a i).re.approx m`, etc. -/

/-- **cauchyDiag real-part toRat split**: the re-part of TauComplex
    cauchyDiag at toRat level is a difference of two TauRat cauchyDiags. -/
theorem TauComplex.cauchyDiag_re_toRat_split (a b : Nat → TauComplex) (k m : Nat) :
    ((TauComplex.cauchyDiag a b k).re.approx m).toRat
      = (TauRat.cauchyDiag (fun i => (a i).re.approx m)
          (fun i => (b i).re.approx m) k).toRat
        - (TauRat.cauchyDiag (fun i => (a i).im.approx m)
            (fun i => (b i).im.approx m) k).toRat := by
  rw [TauComplex.cauchyDiag_re_approx, TauRat.sum_sub_toRat]
  rfl

/-- **cauchyDiag imaginary-part toRat split**: the im-part of TauComplex
    cauchyDiag at toRat level is a sum of two TauRat cauchyDiags. -/
theorem TauComplex.cauchyDiag_im_toRat_split (a b : Nat → TauComplex) (k m : Nat) :
    ((TauComplex.cauchyDiag a b k).im.approx m).toRat
      = (TauRat.cauchyDiag (fun i => (a i).re.approx m)
          (fun i => (b i).im.approx m) k).toRat
        + (TauRat.cauchyDiag (fun i => (a i).im.approx m)
            (fun i => (b i).re.approx m) k).toRat := by
  rw [TauComplex.cauchyDiag_im_approx, TauRat.sum_add_toRat]
  rfl

/-- **cauchyPStar real-part toRat split**: the re-part of TauComplex
    cauchyPStar at toRat level is a difference of two TauRat cauchyPStars. -/
theorem TauComplex.cauchyPStar_re_toRat_split (a b : Nat → TauComplex) (N m : Nat) :
    ((TauComplex.cauchyPStar a b N).re.approx m).toRat
      = (TauRat.cauchyPStar (fun i => (a i).re.approx m)
          (fun i => (b i).re.approx m) N).toRat
        - (TauRat.cauchyPStar (fun i => (a i).im.approx m)
            (fun i => (b i).im.approx m) N).toRat := by
  rw [TauComplex.cauchyPStar_re_approx]
  induction N with
  | zero => simp [TauRat.sum_zero, TauRat.cauchyPStar, toRat_zero]
  | succ N ih =>
    rw [TauRat.sum_succ, toRat_add, ih]
    rw [TauComplex.cauchyDiag_re_toRat_split]
    have h_re_unfold : (TauRat.cauchyPStar (fun i => (a i).re.approx m)
                          (fun i => (b i).re.approx m) (N + 1)).toRat
                    = (TauRat.cauchyPStar (fun i => (a i).re.approx m)
                          (fun i => (b i).re.approx m) N).toRat
                        + (TauRat.cauchyDiag (fun i => (a i).re.approx m)
                            (fun i => (b i).re.approx m) N).toRat := by
      show (TauRat.sum (TauRat.cauchyDiag _ _) (N + 1)).toRat = _
      rw [TauRat.sum_succ, toRat_add]
      rfl
    have h_im_unfold : (TauRat.cauchyPStar (fun i => (a i).im.approx m)
                          (fun i => (b i).im.approx m) (N + 1)).toRat
                    = (TauRat.cauchyPStar (fun i => (a i).im.approx m)
                          (fun i => (b i).im.approx m) N).toRat
                        + (TauRat.cauchyDiag (fun i => (a i).im.approx m)
                            (fun i => (b i).im.approx m) N).toRat := by
      show (TauRat.sum (TauRat.cauchyDiag _ _) (N + 1)).toRat = _
      rw [TauRat.sum_succ, toRat_add]
      rfl
    rw [h_re_unfold, h_im_unfold]
    ring

/-- **cauchyPStar imaginary-part toRat split**: the im-part of TauComplex
    cauchyPStar at toRat level is a sum of two TauRat cauchyPStars. -/
theorem TauComplex.cauchyPStar_im_toRat_split (a b : Nat → TauComplex) (N m : Nat) :
    ((TauComplex.cauchyPStar a b N).im.approx m).toRat
      = (TauRat.cauchyPStar (fun i => (a i).re.approx m)
          (fun i => (b i).im.approx m) N).toRat
        + (TauRat.cauchyPStar (fun i => (a i).im.approx m)
            (fun i => (b i).re.approx m) N).toRat := by
  rw [TauComplex.cauchyPStar_im_approx]
  induction N with
  | zero => simp [TauRat.sum_zero, TauRat.cauchyPStar, toRat_zero]
  | succ N ih =>
    rw [TauRat.sum_succ, toRat_add, ih]
    rw [TauComplex.cauchyDiag_im_toRat_split]
    have h_re_im : (TauRat.cauchyPStar (fun i => (a i).re.approx m)
                          (fun i => (b i).im.approx m) (N + 1)).toRat
                    = (TauRat.cauchyPStar (fun i => (a i).re.approx m)
                          (fun i => (b i).im.approx m) N).toRat
                        + (TauRat.cauchyDiag (fun i => (a i).re.approx m)
                            (fun i => (b i).im.approx m) N).toRat := by
      show (TauRat.sum (TauRat.cauchyDiag _ _) (N + 1)).toRat = _
      rw [TauRat.sum_succ, toRat_add]
      rfl
    have h_im_re : (TauRat.cauchyPStar (fun i => (a i).im.approx m)
                          (fun i => (b i).re.approx m) (N + 1)).toRat
                    = (TauRat.cauchyPStar (fun i => (a i).im.approx m)
                          (fun i => (b i).re.approx m) N).toRat
                        + (TauRat.cauchyDiag (fun i => (a i).im.approx m)
                            (fun i => (b i).re.approx m) N).toRat := by
      show (TauRat.sum (TauRat.cauchyDiag _ _) (N + 1)).toRat = _
      rw [TauRat.sum_succ, toRat_add]
      rfl
    rw [h_re_im, h_im_re]
    ring

-- ============================================================
-- PART 39: PHASE 3C PART 3c.6 — TauComplex Cauchy product bound (re-part)
-- ============================================================

/-! ## TauComplex Cauchy product bound — real part

This is the **componentwise lift** of `TauRat.cauchy_product_bound`
(TauRealSum.lean line 339) to the real part of TauComplex partial
products.

### The statement

Under componentwise geometric bounds `|(a i).re.approx m .toRat|`,
`|(a i).im.approx m .toRat| ≤ C / 2^i` (and same for `b`), we have:

`|((sum a n).mul (sum b n)).re.approx m .toRat − (cauchyPStar a b n).re.approx m .toRat|
   ≤ 2 · n · C² / 2^(n-1)`

The factor of 2 (vs. TauRat's 1) reflects that the real part of the
TauComplex Cauchy product splits into a **difference** of two TauRat
Cauchy products (one for `re·re`, one for `im·im`), each of which
satisfies the TauRat bound `n · C² / 2^(n-1)`. Triangle inequality
gives the doubled constant.

### Proof strategy

1. Expand `((sum a n).mul (sum b n)).re.approx m .toRat` via
   `mul_re_approx` + `sum_re_approx` + `sum_im_approx` + `toRat_mul`.
2. Expand `(cauchyPStar a b n).re.approx m .toRat` via
   `cauchyPStar_re_toRat_split`.
3. Re-group via `ring` into `(re-Cauchy-diff) − (im-Cauchy-diff)`.
4. Triangle inequality + `TauRat.cauchy_product_bound` twice. -/

/-- **TauComplex Cauchy product bound (real part)**.

    Componentwise lift of `TauRat.cauchy_product_bound`. The factor of 2
    comes from the triangle inequality applied to the re-im split. -/
theorem TauComplex.cauchy_product_bound_re
    (a b : Nat → TauComplex) (C : Rat) (hC : 0 < C)
    (h_a_re : ∀ i m, |((a i).re.approx m).toRat| ≤ C / (2 : Rat) ^ i)
    (h_a_im : ∀ i m, |((a i).im.approx m).toRat| ≤ C / (2 : Rat) ^ i)
    (h_b_re : ∀ j m, |((b j).re.approx m).toRat| ≤ C / (2 : Rat) ^ j)
    (h_b_im : ∀ j m, |((b j).im.approx m).toRat| ≤ C / (2 : Rat) ^ j)
    (n : Nat) (hn : 1 ≤ n) (m : Nat) :
    |(((TauComplex.sum a n).mul (TauComplex.sum b n)).re.approx m).toRat
      - ((TauComplex.cauchyPStar a b n).re.approx m).toRat|
      ≤ 2 * (n : Rat) * C ^ 2 / (2 : Rat) ^ (n - 1) := by
  -- Set names for componentwise sequences
  set ra : Nat → TauRat := fun i => (a i).re.approx m with hra_def
  set rb : Nat → TauRat := fun j => (b j).re.approx m with hrb_def
  set ia : Nat → TauRat := fun i => (a i).im.approx m with hia_def
  set ib : Nat → TauRat := fun j => (b j).im.approx m with hib_def
  -- Step 1: expand LHS to a sum/diff of TauRat Cauchy expressions
  have h_expand :
      (((TauComplex.sum a n).mul (TauComplex.sum b n)).re.approx m).toRat
        - ((TauComplex.cauchyPStar a b n).re.approx m).toRat
      = ((TauRat.sum ra n).toRat * (TauRat.sum rb n).toRat
          - (TauRat.cauchyPStar ra rb n).toRat)
        - ((TauRat.sum ia n).toRat * (TauRat.sum ib n).toRat
            - (TauRat.cauchyPStar ia ib n).toRat) := by
    rw [TauComplex.mul_re_approx, toRat_sub, toRat_mul, toRat_mul,
        TauComplex.sum_re_approx, TauComplex.sum_re_approx,
        TauComplex.sum_im_approx, TauComplex.sum_im_approx,
        TauComplex.cauchyPStar_re_toRat_split]
    ring
  rw [h_expand]
  -- Step 2: triangle inequality
  have h_tri := abs_sub
      ((TauRat.sum ra n).toRat * (TauRat.sum rb n).toRat
        - (TauRat.cauchyPStar ra rb n).toRat)
      ((TauRat.sum ia n).toRat * (TauRat.sum ib n).toRat
        - (TauRat.cauchyPStar ia ib n).toRat)
  -- Step 3: TauRat.cauchy_product_bound twice
  have h_re_bound := TauRat.cauchy_product_bound ra rb C hC
                       (fun i => h_a_re i m) (fun j => h_b_re j m) n hn
  have h_im_bound := TauRat.cauchy_product_bound ia ib C hC
                       (fun i => h_a_im i m) (fun j => h_b_im j m) n hn
  -- Step 4: combine via linarith
  have h_2nC2 : 2 * (n : Rat) * C ^ 2 / (2 : Rat) ^ (n - 1)
              = (n : Rat) * C ^ 2 / (2 : Rat) ^ (n - 1)
                + (n : Rat) * C ^ 2 / (2 : Rat) ^ (n - 1) := by ring
  rw [h_2nC2]
  linarith

/-- **TauComplex Cauchy product bound (imaginary part)**.

    Componentwise lift of `TauRat.cauchy_product_bound`. The factor of 2
    comes from the triangle inequality applied to the re·im + im·re split. -/
theorem TauComplex.cauchy_product_bound_im
    (a b : Nat → TauComplex) (C : Rat) (hC : 0 < C)
    (h_a_re : ∀ i m, |((a i).re.approx m).toRat| ≤ C / (2 : Rat) ^ i)
    (h_a_im : ∀ i m, |((a i).im.approx m).toRat| ≤ C / (2 : Rat) ^ i)
    (h_b_re : ∀ j m, |((b j).re.approx m).toRat| ≤ C / (2 : Rat) ^ j)
    (h_b_im : ∀ j m, |((b j).im.approx m).toRat| ≤ C / (2 : Rat) ^ j)
    (n : Nat) (hn : 1 ≤ n) (m : Nat) :
    |(((TauComplex.sum a n).mul (TauComplex.sum b n)).im.approx m).toRat
      - ((TauComplex.cauchyPStar a b n).im.approx m).toRat|
      ≤ 2 * (n : Rat) * C ^ 2 / (2 : Rat) ^ (n - 1) := by
  set ra : Nat → TauRat := fun i => (a i).re.approx m with hra_def
  set rb : Nat → TauRat := fun j => (b j).re.approx m with hrb_def
  set ia : Nat → TauRat := fun i => (a i).im.approx m with hia_def
  set ib : Nat → TauRat := fun j => (b j).im.approx m with hib_def
  -- Step 1: expand LHS to two TauRat Cauchy diffs that sum
  have h_expand :
      (((TauComplex.sum a n).mul (TauComplex.sum b n)).im.approx m).toRat
        - ((TauComplex.cauchyPStar a b n).im.approx m).toRat
      = ((TauRat.sum ra n).toRat * (TauRat.sum ib n).toRat
          - (TauRat.cauchyPStar ra ib n).toRat)
        + ((TauRat.sum ia n).toRat * (TauRat.sum rb n).toRat
            - (TauRat.cauchyPStar ia rb n).toRat) := by
    rw [TauComplex.mul_im_approx, toRat_add, toRat_mul, toRat_mul,
        TauComplex.sum_re_approx, TauComplex.sum_re_approx,
        TauComplex.sum_im_approx, TauComplex.sum_im_approx,
        TauComplex.cauchyPStar_im_toRat_split]
    ring
  rw [h_expand]
  -- Step 2: triangle inequality (abs of sum ≤ sum of abs)
  have h_tri := abs_add_le
      ((TauRat.sum ra n).toRat * (TauRat.sum ib n).toRat
        - (TauRat.cauchyPStar ra ib n).toRat)
      ((TauRat.sum ia n).toRat * (TauRat.sum rb n).toRat
        - (TauRat.cauchyPStar ia rb n).toRat)
  -- Step 3: TauRat.cauchy_product_bound twice
  have h_reim_bound := TauRat.cauchy_product_bound ra ib C hC
                         (fun i => h_a_re i m) (fun j => h_b_im j m) n hn
  have h_imre_bound := TauRat.cauchy_product_bound ia rb C hC
                         (fun i => h_a_im i m) (fun j => h_b_re j m) n hn
  -- Step 4: combine via calc
  calc |(TauRat.sum ra n).toRat * (TauRat.sum ib n).toRat
          - (TauRat.cauchyPStar ra ib n).toRat
        + ((TauRat.sum ia n).toRat * (TauRat.sum rb n).toRat
            - (TauRat.cauchyPStar ia rb n).toRat)|
      ≤ |(TauRat.sum ra n).toRat * (TauRat.sum ib n).toRat
              - (TauRat.cauchyPStar ra ib n).toRat|
          + |(TauRat.sum ia n).toRat * (TauRat.sum rb n).toRat
              - (TauRat.cauchyPStar ia rb n).toRat| := h_tri
    _ ≤ (n : Rat) * C ^ 2 / (2 : Rat) ^ (n - 1)
        + (n : Rat) * C ^ 2 / (2 : Rat) ^ (n - 1) := by
        linarith [h_reim_bound, h_imre_bound]
    _ = 2 * (n : Rat) * C ^ 2 / (2 : Rat) ^ (n - 1) := by ring

-- ============================================================
-- PART 40: PHASE 3C PART 3d — TauComplex.pow componentwise magnitude bound
-- ============================================================

/-! ## TauComplex pow componentwise magnitude bound

For the M3 endpoint, we need to establish geometric magnitude bounds on
`(exp_term z i).re.approx m .toRat` and `(exp_term z i).im.approx m .toRat`,
which feed `cauchy_product_bound_re/im` as the per-term geometric bound
`≤ C / 2^i`.

Since `exp_term z i = scale_by_inv_factorial (pow z i) i` componentwise,
the chain is:
1. **Bound on `pow z i` components** (this Part 3d): given
   `TauComplex.BoundedBy z M`, `|((pow z i).{re,im}.approx m).toRat|
   ≤ (2M)^i`. The factor of 2 vs. M^i comes from the TauComplex.mul cross
   products: each mul step contributes a factor of 2M (sum of two M·M
   cross products). The bound is **tight** under componentwise BoundedBy.
2. **Bound on exp_term** (Part 3e, queued): combine with
   `scale_by_inv_factorial_toRat` to get `|.| ≤ (2M)^i / i!`.
3. **Convert to `C / 2^i` form** (Part 3e): for `M ≤ 1` (Nat), `(2M)^i / i!
   ≤ 2^i / i!`, which is `≤ C / 2^i` iff `4^i ≤ C · i!`. The max of
   `4^i / i!` over all `i` is `~11` (achieved at i=3,4), so `C = 11`
   suffices.

### The inductive structure

Both `re` and `im` bounds prove **simultaneously** by induction on `i`:
* **Base** `i = 0`: `pow z 0 = one`. `one.re.approx m = TauRat.one` (so
  `|1| = 1 ≤ 1 = (2M)^0`); `one.im.approx m = TauRat.zero` (so `0 ≤ 1`).
* **Step** `i + 1`: `pow z (i+1) = (pow z i).mul z`. Both `.re` and `.im`
  satisfy the same bound via the mul cross-product structure + triangle
  inequality + IH. -/

/-- **TauComplex.pow componentwise magnitude bound (simultaneous re+im).**

    Given `TauComplex.BoundedBy z M`, both `.re.approx m .toRat` and
    `.im.approx m .toRat` of `pow z k` are bounded by `(2M)^k`. -/
theorem TauComplex.pow_re_im_abs_le (z : TauComplex) (M : Nat)
    (h : TauComplex.BoundedBy z M) (k m : Nat) :
    |((TauComplex.pow z k).re.approx m).toRat| ≤ ((2 * M : Nat) : Rat) ^ k ∧
    |((TauComplex.pow z k).im.approx m).toRat| ≤ ((2 * M : Nat) : Rat) ^ k := by
  induction k with
  | zero =>
    -- pow z 0 = one. one.re.approx m .toRat = 1, one.im.approx m .toRat = 0.
    refine ⟨?_, ?_⟩
    · show |((TauComplex.one.re.approx m).toRat)| ≤ ((2 * M : Nat) : Rat) ^ 0
      -- one.re = TauReal.one, .approx m = TauRat.one, .toRat = 1, |1| = 1.
      show |((TauReal.one.approx m).toRat)| ≤ 1
      show |TauRat.one.toRat| ≤ 1
      rw [toRat_one]
      simp
    · show |((TauComplex.one.im.approx m).toRat)| ≤ ((2 * M : Nat) : Rat) ^ 0
      show |((TauReal.zero.approx m).toRat)| ≤ 1
      show |TauRat.zero.toRat| ≤ 1
      rw [toRat_zero]
      simp
  | succ k ih =>
    obtain ⟨h_re_k, h_im_k⟩ := ih
    have hM_nn : (0 : Rat) ≤ ((2 * M : Nat) : Rat) := by
      exact_mod_cast Nat.zero_le (2 * M)
    have hM_pow_nn : (0 : Rat) ≤ ((2 * M : Nat) : Rat) ^ k :=
      pow_nonneg hM_nn k
    have h_z_re : |(z.re.approx m).toRat| ≤ (M : Rat) := by
      have := h.1 m
      rwa [TauRat.toRat_abs] at this
    have h_z_im : |(z.im.approx m).toRat| ≤ (M : Rat) := by
      have := h.2 m
      rwa [TauRat.toRat_abs] at this
    have hM_nat_nn : (0 : Rat) ≤ (M : Rat) := by exact_mod_cast Nat.zero_le M
    -- 2 * M cast: ((2 * M : Nat) : Rat) = 2 * (M : Rat)
    have h_cast : ((2 * M : Nat) : Rat) = 2 * (M : Rat) := by push_cast; ring
    refine ⟨?_, ?_⟩
    · -- |(pow z (k+1)).re.approx m .toRat| ≤ (2M)^(k+1)
      rw [TauComplex.pow_succ, TauComplex.mul_re_approx, toRat_sub, toRat_mul, toRat_mul]
      calc |((TauComplex.pow z k).re.approx m).toRat * (z.re.approx m).toRat
              - ((TauComplex.pow z k).im.approx m).toRat * (z.im.approx m).toRat|
          ≤ |((TauComplex.pow z k).re.approx m).toRat * (z.re.approx m).toRat|
            + |((TauComplex.pow z k).im.approx m).toRat * (z.im.approx m).toRat| :=
            abs_sub _ _
        _ = |((TauComplex.pow z k).re.approx m).toRat| * |(z.re.approx m).toRat|
            + |((TauComplex.pow z k).im.approx m).toRat| * |(z.im.approx m).toRat| := by
              rw [abs_mul, abs_mul]
        _ ≤ ((2 * M : Nat) : Rat) ^ k * (M : Rat)
            + ((2 * M : Nat) : Rat) ^ k * (M : Rat) := by
              apply add_le_add
              · exact mul_le_mul h_re_k h_z_re (abs_nonneg _) hM_pow_nn
              · exact mul_le_mul h_im_k h_z_im (abs_nonneg _) hM_pow_nn
        _ = ((2 * M : Nat) : Rat) ^ (k + 1) := by
              rw [h_cast]; ring
    · -- |(pow z (k+1)).im.approx m .toRat| ≤ (2M)^(k+1)
      rw [TauComplex.pow_succ, TauComplex.mul_im_approx, toRat_add, toRat_mul, toRat_mul]
      calc |((TauComplex.pow z k).re.approx m).toRat * (z.im.approx m).toRat
              + ((TauComplex.pow z k).im.approx m).toRat * (z.re.approx m).toRat|
          ≤ |((TauComplex.pow z k).re.approx m).toRat * (z.im.approx m).toRat|
            + |((TauComplex.pow z k).im.approx m).toRat * (z.re.approx m).toRat| :=
            abs_add_le _ _
        _ = |((TauComplex.pow z k).re.approx m).toRat| * |(z.im.approx m).toRat|
            + |((TauComplex.pow z k).im.approx m).toRat| * |(z.re.approx m).toRat| := by
              rw [abs_mul, abs_mul]
        _ ≤ ((2 * M : Nat) : Rat) ^ k * (M : Rat)
            + ((2 * M : Nat) : Rat) ^ k * (M : Rat) := by
              apply add_le_add
              · exact mul_le_mul h_re_k h_z_im (abs_nonneg _) hM_pow_nn
              · exact mul_le_mul h_im_k h_z_re (abs_nonneg _) hM_pow_nn
        _ = ((2 * M : Nat) : Rat) ^ (k + 1) := by
              rw [h_cast]; ring

-- ============================================================
-- PART 41: PHASE 3C PART 3e — TauComplex.exp_term componentwise abs bound
-- ============================================================

/-! ## TauComplex exp_term componentwise abs bound

Combining `pow_re_im_abs_le` (Part 3d) with `scale_by_inv_factorial_toRat`
gives the componentwise magnitude bound on `exp_term z k`:

`|(exp_term z k).{re,im}.approx m .toRat| ≤ (2M)^k / k!`

The conversion to `cauchy_product_bound`-input form `C / 2^k` requires
the auxiliary inequality `(4M)^k ≤ C · k!` for some constant `C`. For
the common case `M = 1` (Nat-BoundedBy 1), `4^k ≤ 11 · k!` works
(max of `4^k / k!` is ~10.67 at k=3,4). -/

/-- **TauComplex.exp_term componentwise magnitude bound (simultaneous re+im).**

    `|(exp_term z k).{re,im}.approx m .toRat| ≤ (2M)^k / k!` given
    `TauComplex.BoundedBy z M`.

    Direct application: pow bound + scale_by_inv_factorial. -/
theorem TauComplex.exp_term_re_im_abs_le (z : TauComplex) (M : Nat)
    (h : TauComplex.BoundedBy z M) (k m : Nat) :
    |((TauComplex.exp_term z k).re.approx m).toRat|
      ≤ ((2 * M : Nat) : Rat) ^ k / (k.factorial : Rat) ∧
    |((TauComplex.exp_term z k).im.approx m).toRat|
      ≤ ((2 * M : Nat) : Rat) ^ k / (k.factorial : Rat) := by
  obtain ⟨h_pow_re, h_pow_im⟩ := TauComplex.pow_re_im_abs_le z M h k m
  have h_fact_pos : (0 : Rat) < (k.factorial : Rat) := by
    exact_mod_cast Nat.factorial_pos k
  refine ⟨?_, ?_⟩
  · -- re part
    show |((TauReal.scale_by_inv_factorial (TauComplex.pow z k).re k).approx m).toRat|
       ≤ ((2 * M : Nat) : Rat) ^ k / (k.factorial : Rat)
    rw [TauReal.scale_by_inv_factorial_approx, TauRat.scale_by_inv_factorial_toRat]
    rw [abs_div]
    have h_fact_abs : |(k.factorial : Rat)| = (k.factorial : Rat) :=
      abs_of_pos h_fact_pos
    rw [h_fact_abs]
    exact div_le_div_of_nonneg_right h_pow_re (le_of_lt h_fact_pos)
  · -- im part
    show |((TauReal.scale_by_inv_factorial (TauComplex.pow z k).im k).approx m).toRat|
       ≤ ((2 * M : Nat) : Rat) ^ k / (k.factorial : Rat)
    rw [TauReal.scale_by_inv_factorial_approx, TauRat.scale_by_inv_factorial_toRat]
    rw [abs_div]
    have h_fact_abs : |(k.factorial : Rat)| = (k.factorial : Rat) :=
      abs_of_pos h_fact_pos
    rw [h_fact_abs]
    exact div_le_div_of_nonneg_right h_pow_im (le_of_lt h_fact_pos)

-- ============================================================
-- PART 42: PHASE 3C PART 3f — Bridge to C/2^k form via 4^k ≤ 11·k!
-- ============================================================

/-! ## Algebraic bridge: 4^k ≤ 11 · k!

The cauchy_product_bound hypothesis requires componentwise bounds in the
geometric form `≤ C / 2^k` with a fixed constant `C`. From Part 3e we
have `|(exp_term z k).{re,im}.approx m .toRat| ≤ (2M)^k / k!`. For the
common τ-canon case `M = 1` (Nat-BoundedBy 1), this is `2^k / k!`, and
converting to `C / 2^k` form requires:

`2^k / k! ≤ C / 2^k  ⟺  4^k ≤ C · k!`

The minimal `C` is `max_k (4^k / k!) ≈ 10.67` (achieved at k=3,4). The
next integer `C = 11` suffices.

### Proof structure for `4^k ≤ 11 · k!`

Case split on `k ≤ 3` vs `k ≥ 4`:
* Small cases (k = 0,1,2,3): direct numerical verification.
  - 1 ≤ 11, 4 ≤ 11, 16 ≤ 22, 64 ≤ 66.
* Inductive step (k ≥ 3): `4^(k+1) = 4 · 4^k ≤ 4 · 11 · k! = 44 · k!`.
  Want `≤ 11 · (k+1)! = 11 · (k+1) · k!`. Suffices `4 ≤ k+1`, i.e., `k ≥ 3`. ✓ -/

/-- **Algebraic bridge**: `4^k ≤ 11 · k!` for all natural `k`. -/
theorem four_pow_le_eleven_factorial (k : Nat) :
    (4 : Rat) ^ k ≤ 11 * (k.factorial : Rat) := by
  induction k with
  | zero => norm_num [Nat.factorial]
  | succ k ih =>
    by_cases hk : k ≥ 3
    · -- Inductive step for k ≥ 3
      have h_succ : ((k + 1).factorial : Rat) = ((k + 1 : Nat) : Rat) * (k.factorial : Rat) := by
        rw [Nat.factorial_succ]; push_cast; ring
      have h_fact_nn : (0 : Rat) ≤ (k.factorial : Rat) := by
        exact_mod_cast Nat.factorial_pos k |>.le
      have h_k1_ge_4 : (4 : Rat) ≤ ((k + 1 : Nat) : Rat) := by
        have : (4 : Nat) ≤ k + 1 := by omega
        exact_mod_cast this
      calc (4 : Rat) ^ (k + 1)
          = 4 * (4 : Rat) ^ k := by ring
        _ ≤ 4 * (11 * (k.factorial : Rat)) :=
            mul_le_mul_of_nonneg_left ih (by norm_num)
        _ = 11 * (4 * (k.factorial : Rat)) := by ring
        _ ≤ 11 * (((k + 1 : Nat) : Rat) * (k.factorial : Rat)) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right h_k1_ge_4 h_fact_nn) (by norm_num)
        _ = 11 * ((k + 1).factorial : Rat) := by rw [h_succ]
    · -- Small cases: k ∈ {0, 1, 2}. Manual case split avoiding `interval_cases`.
      push_neg at hk
      -- k < 3, so k = 0, 1, or 2; k + 1 = 1, 2, or 3.
      match k, hk with
      | 0, _ => norm_num [Nat.factorial]
      | 1, _ => norm_num [Nat.factorial]
      | 2, _ => norm_num [Nat.factorial]

/-- **TauComplex.exp_term geometric magnitude bound (M=1 case)**.

    For `TauComplex.BoundedBy z 1`, both `.re.approx m .toRat` and
    `.im.approx m .toRat` of `exp_term z k` are bounded by `11 / 2^k`.

    This is the exact form `cauchy_product_bound_re/im` accepts as input
    for the per-term geometric bound `C / 2^k` with `C = 11`. -/
theorem TauComplex.exp_term_re_im_geom_bound (z : TauComplex)
    (h : TauComplex.BoundedBy z 1) (k m : Nat) :
    |((TauComplex.exp_term z k).re.approx m).toRat| ≤ (11 : Rat) / (2 : Rat) ^ k ∧
    |((TauComplex.exp_term z k).im.approx m).toRat| ≤ (11 : Rat) / (2 : Rat) ^ k := by
  obtain ⟨h_re, h_im⟩ := TauComplex.exp_term_re_im_abs_le z 1 h k m
  -- Bound: |.| ≤ (2 · 1)^k / k.factorial = 2^k / k.factorial
  -- Convert to 11 / 2^k: 2^k / k.factorial ≤ 11 / 2^k iff 4^k ≤ 11 · k.factorial
  have h_2pow_pos : (0 : Rat) < (2 : Rat) ^ k := by positivity
  have h_fact_pos : (0 : Rat) < (k.factorial : Rat) := by
    exact_mod_cast Nat.factorial_pos k
  have h_4pow_le : (4 : Rat) ^ k ≤ 11 * (k.factorial : Rat) := four_pow_le_eleven_factorial k
  have h_2k_to_rat : ((2 * 1 : Nat) : Rat) = 2 := by norm_num
  have h_bound_2k : ((2 * 1 : Nat) : Rat) ^ k / (k.factorial : Rat) ≤ (11 : Rat) / (2 : Rat) ^ k := by
    rw [h_2k_to_rat]
    -- 2^k / k! ≤ 11 / 2^k ⟺ 2^k · 2^k ≤ 11 · k! (by cross-mul)
    rw [div_le_div_iff₀ h_fact_pos h_2pow_pos]
    have h_pow_two : (2 : Rat) ^ k * (2 : Rat) ^ k = (4 : Rat) ^ k := by
      have h1 : (2 : Rat) ^ k * (2 : Rat) ^ k = (2 : Rat) ^ (k + k) := by rw [pow_add]
      have h2 : (2 : Rat) ^ (k + k) = ((2 : Rat) * 2) ^ k := by
        rw [show k + k = 2 * k from by ring, pow_mul]; ring_nf
      rw [h1, h2]; norm_num
    linarith [h_4pow_le, h_pow_two]
  exact ⟨le_trans h_re h_bound_2k, le_trans h_im h_bound_2k⟩

-- ============================================================
-- PART 43: PHASE 3C PART 3g.1 — Helpers for toRat-level binomial theorem
-- ============================================================

/-! ## Foundational helpers for the toRat-level binomial theorem (Part 3g)

To prove the M3 endpoint, we follow **Approach A**: prove a toRat-level
binomial identity at TauComplex by direct induction, **without** Mathlib's
`add_pow` / `CommRing` infrastructure. This preserves the τ-canon
discipline of using Mathlib only for tactics (`ring`, `linarith`,
`norm_num`, etc.).

This Part ships foundational rfl-level lemmas that the induction will
build on:

* `nat_to_taurat_toRat`: `(nat_to_taurat k).toRat = (k : Rat)` —
  promoted from a local `have` (line ~3529) to a public lemma.
* `TauComplex.fromTauReal_re_approx` / `_im_approx`: rfl-bridges showing
  `(fromTauReal r).re.approx m = r.approx m` and `.im.approx m = TauRat.zero`.
* `TauReal.fromNat_approx`: `(TauReal.fromNat k).approx m = nat_to_taurat k`.

All four are rfl or short proofs. -/

/-- **`nat_to_taurat k .toRat = k` as a Rat.** Promoted from local use to
    a public lemma since it's needed throughout the toRat-level binomial
    proof. -/
theorem nat_to_taurat_toRat (k : Nat) : (nat_to_taurat k).toRat = (k : Rat) := by
  simp only [nat_to_taurat, int_to_taurat, nat_to_tauint, TauRat.toRat,
             TauInt.toInt, TauInt.fromNat]
  push_cast; ring

/-- **`(fromTauReal r).re.approx m = r.approx m`** — rfl-bridge. -/
@[simp] theorem TauComplex.fromTauReal_re_approx (r : TauReal) (m : Nat) :
    (TauComplex.fromTauReal r).re.approx m = r.approx m := rfl

/-- **`(fromTauReal r).im.approx m = TauRat.zero`** — rfl-bridge. -/
@[simp] theorem TauComplex.fromTauReal_im_approx (r : TauReal) (m : Nat) :
    (TauComplex.fromTauReal r).im.approx m = TauRat.zero := rfl

/-- **`(TauReal.fromNat k).approx m = nat_to_taurat k`** — rfl-bridge. -/
@[simp] theorem TauReal.fromNat_approx (k m : Nat) :
    (TauReal.fromNat k).approx m = nat_to_taurat k := rfl

-- ============================================================
-- PART 44: PHASE 3C PART 3g.2a — TauComplex.pow recurrence at toRat level
-- ============================================================

/-! ## TauComplex.pow recurrence at toRat level

Both LHS (`pow (z₁+z₂) n`) and RHS (binomial sum) of the toRat-level
binomial theorem satisfy the same recurrence:

`R(value (n+1)) = R(value n) · R(z₁+z₂) − I(value n) · I(z₁+z₂)`

If we prove this recurrence for BOTH the LHS and the RHS, then by
induction (with matching base case `n=0`), they're toRat-equal at every
depth `n`.

### The LHS recurrence

`(pow (z₁+z₂) (n+1)).re.approx m .toRat
  = (pow (z₁+z₂) n .re.approx m).toRat · ((z₁+z₂).re.approx m).toRat
    − (pow (z₁+z₂) n .im.approx m).toRat · ((z₁+z₂).im.approx m).toRat`

This follows from `pow_succ` + `mul_re_approx` + `toRat_sub/mul`. -/

/-- **`pow.re.approx.toRat` recurrence**: `pow z (n+1) .re.approx m .toRat`
    expressed as Rat-arithmetic on `.re/.im.approx m .toRat` values. -/
theorem TauComplex.pow_succ_re_approx_toRat (z : TauComplex) (n m : Nat) :
    ((TauComplex.pow z (n + 1)).re.approx m).toRat
      = ((TauComplex.pow z n).re.approx m).toRat * ((z.re.approx m).toRat)
        - ((TauComplex.pow z n).im.approx m).toRat * ((z.im.approx m).toRat) := by
  rw [TauComplex.pow_succ, TauComplex.mul_re_approx, toRat_sub, toRat_mul, toRat_mul]

/-- **`pow.im.approx.toRat` recurrence**: `pow z (n+1) .im.approx m .toRat`
    expressed as Rat-arithmetic on `.re/.im.approx m .toRat` values. -/
theorem TauComplex.pow_succ_im_approx_toRat (z : TauComplex) (n m : Nat) :
    ((TauComplex.pow z (n + 1)).im.approx m).toRat
      = ((TauComplex.pow z n).re.approx m).toRat * ((z.im.approx m).toRat)
        + ((TauComplex.pow z n).im.approx m).toRat * ((z.re.approx m).toRat) := by
  rw [TauComplex.pow_succ, TauComplex.mul_im_approx, toRat_add, toRat_mul, toRat_mul]

/-- **`(z₁+z₂).re.approx m .toRat = R z₁ + R z₂`** — `add` componentwise
    bridge at toRat level. -/
theorem TauComplex.add_re_approx_toRat (z₁ z₂ : TauComplex) (m : Nat) :
    ((z₁.add z₂).re.approx m).toRat
      = ((z₁.re.approx m).toRat) + ((z₂.re.approx m).toRat) := by
  show (TauRat.add (z₁.re.approx m) (z₂.re.approx m)).toRat = _
  rw [toRat_add]

/-- **`(z₁+z₂).im.approx m .toRat = I z₁ + I z₂`** — `add` componentwise
    bridge at toRat level. -/
theorem TauComplex.add_im_approx_toRat (z₁ z₂ : TauComplex) (m : Nat) :
    ((z₁.add z₂).im.approx m).toRat
      = ((z₁.im.approx m).toRat) + ((z₂.im.approx m).toRat) := by
  show (TauRat.add (z₁.im.approx m) (z₂.im.approx m)).toRat = _
  rw [toRat_add]

-- ============================================================
-- PART 45: PHASE 3C PART 3g.2b — Binomial sum recurrence (Pascal at toRat)
-- ============================================================

/-! ## Binomial sum recurrence at toRat level

The toRat-level binomial theorem says
`((pow (z₁+z₂) n).re.approx m).toRat = ((binomial_sum n).re.approx m).toRat`
(and `.im` analog), where `binomial_sum n` is the explicit binomial sum
of `(fromTauReal (fromNat C(n,i))) · (pow z₁ i · pow z₂ (n-i))` for
`i = 0..n`.

The proof is by induction on `n`. Both LHS and RHS satisfy the SAME
recurrence at toRat level:
* LHS: `R(pow (z₁+z₂) (n+1)) = R(pow (z₁+z₂) n) · R(z₁+z₂) − I(pow (z₁+z₂) n) · I(z₁+z₂)`
  (Part 3g.2a, `pow_succ_re_approx_toRat`)
* RHS: same recurrence — this is the **Pascal step** (this Part 3g.2b).

The RHS recurrence:
`R(binomial_sum (n+1)) = R(binomial_sum n) · R(z₁+z₂) − I(binomial_sum n) · I(z₁+z₂)`

requires proving that the binomial sum at depth `n+1` equals
(`binomial_sum n` `·` `(z₁+z₂)`) at toRat-level re/im. This is the
Pascal regrouping identity, formalized as a TauRat sum manipulation.

### Helper: the binomial-term sequences as TauRat-valued functions

We work with the explicit binomial sum:
```
binom_sum_re z₁ z₂ n m :=
  TauRat.sum (fun i =>
    (nat_to_taurat (n.choose i)).mul
      (((pow z₁ i).mul (pow z₂ (n - i))).re.approx m)) (n+1)
binom_sum_im z₁ z₂ n m := analog with `.im`
```

The theorem states the Pascal recurrence at `.toRat` level:
`(binom_sum_re z₁ z₂ (n+1) m).toRat = (binom_sum_re z₁ z₂ n m).toRat · ((z₁+z₂).re.approx m).toRat
                                       - (binom_sum_im z₁ z₂ n m).toRat · ((z₁+z₂).im.approx m).toRat`

(and `.im` analog with `+` and swapped components). -/

/-- **TauComplex binomial-term sum (re part)** at `.approx m .toRat` level.

    Definition shorthand for the explicit binomial sum's `.re.approx m`. -/
def TauComplex.binom_sum_re (z₁ z₂ : TauComplex) (n m : Nat) : TauRat :=
  TauRat.sum (fun i =>
    (nat_to_taurat (n.choose i)).mul
      (((TauComplex.pow z₁ i).mul (TauComplex.pow z₂ (n - i))).re.approx m)) (n + 1)

/-- **TauComplex binomial-term sum (im part)** at `.approx m .toRat` level. -/
def TauComplex.binom_sum_im (z₁ z₂ : TauComplex) (n m : Nat) : TauRat :=
  TauRat.sum (fun i =>
    (nat_to_taurat (n.choose i)).mul
      (((TauComplex.pow z₁ i).mul (TauComplex.pow z₂ (n - i))).im.approx m)) (n + 1)

/-- **Base case `n = 0`** of the binomial theorem at toRat level.

    `(pow (z₁+z₂) 0).{re,im}.approx m .toRat = (binom_sum_{re,im} 0).toRat`. -/
theorem TauComplex.add_pow_zero_re_im_approx_toRat (z₁ z₂ : TauComplex) (m : Nat) :
    ((TauComplex.pow (z₁.add z₂) 0).re.approx m).toRat
      = (TauComplex.binom_sum_re z₁ z₂ 0 m).toRat ∧
    ((TauComplex.pow (z₁.add z₂) 0).im.approx m).toRat
      = (TauComplex.binom_sum_im z₁ z₂ 0 m).toRat := by
  refine ⟨?_, ?_⟩
  · -- LHS_re at n=0: (one.re.approx m).toRat = 1
    -- RHS_re at n=0: TauRat.sum (fun i => 1 · (one.mul one).re.approx m) 1 .toRat
    show ((TauComplex.one.re.approx m).toRat) = _
    show TauRat.one.toRat = _
    rw [toRat_one]
    show (1 : Rat) = (TauComplex.binom_sum_re z₁ z₂ 0 m).toRat
    -- Unfold binom_sum_re at n=0
    show (1 : Rat) = (TauRat.sum (fun i =>
            (nat_to_taurat (Nat.choose 0 i)).mul
              (((TauComplex.pow z₁ i).mul (TauComplex.pow z₂ (0 - i))).re.approx m)) 1).toRat
    rw [TauRat.sum_succ, TauRat.sum_zero, toRat_add, toRat_zero, zero_add]
    -- Inner term at i=0: (nat_to_taurat (Nat.choose 0 0)).mul ((pow z₁ 0).mul (pow z₂ 0)).re.approx m
    -- = (nat_to_taurat 1).mul ((one.mul one).re.approx m)
    -- .toRat = 1 · 1 = 1
    rw [toRat_mul, nat_to_taurat_toRat]
    show 1 = (1 : Rat) * (((TauComplex.pow z₁ 0).mul (TauComplex.pow z₂ 0)).re.approx m).toRat
    rw [one_mul]
    -- ((pow z₁ 0).mul (pow z₂ 0)).re.approx m = (one.mul one).re.approx m
    show (1 : Rat) = ((TauComplex.one.mul TauComplex.one).re.approx m).toRat
    rw [TauComplex.mul_re_approx, toRat_sub, toRat_mul, toRat_mul]
    show (1 : Rat) = (TauComplex.one.re.approx m).toRat * (TauComplex.one.re.approx m).toRat
                    - (TauComplex.one.im.approx m).toRat * (TauComplex.one.im.approx m).toRat
    show (1 : Rat) = TauRat.one.toRat * TauRat.one.toRat - TauRat.zero.toRat * TauRat.zero.toRat
    rw [toRat_one, toRat_zero]; ring
  · -- LHS_im at n=0: (one.im.approx m).toRat = 0
    show ((TauComplex.one.im.approx m).toRat) = _
    show TauRat.zero.toRat = _
    rw [toRat_zero]
    -- RHS_im at n=0
    show (0 : Rat) = (TauComplex.binom_sum_im z₁ z₂ 0 m).toRat
    show (0 : Rat) = (TauRat.sum (fun i =>
            (nat_to_taurat (Nat.choose 0 i)).mul
              (((TauComplex.pow z₁ i).mul (TauComplex.pow z₂ (0 - i))).im.approx m)) 1).toRat
    rw [TauRat.sum_succ, TauRat.sum_zero, toRat_add, toRat_zero, zero_add]
    rw [toRat_mul, nat_to_taurat_toRat]
    show 0 = (1 : Rat) * (((TauComplex.pow z₁ 0).mul (TauComplex.pow z₂ 0)).im.approx m).toRat
    rw [one_mul]
    show (0 : Rat) = ((TauComplex.one.mul TauComplex.one).im.approx m).toRat
    rw [TauComplex.mul_im_approx, toRat_add, toRat_mul, toRat_mul]
    show (0 : Rat) = TauRat.one.toRat * TauRat.zero.toRat + TauRat.zero.toRat * TauRat.one.toRat
    rw [toRat_one, toRat_zero]; ring

-- ============================================================
-- PART 46: PHASE 3C PART 3g.2c — Helpers for Pascal step
-- ============================================================

/-! ## Helpers for the Pascal step

Three TauRat helper lemmas:
* `TauRat.sum_split_first_toRat`: peel off the first term `f 0` from
  a sum, exposing the shifted sum `(fun i => f (i+1))`.
* `TauRat.sum_const_mul_toRat`: distribute a fixed scalar multiplication
  across a sum at toRat level.
* `nat_choose_succ_succ_toRat`: Pascal's rule cast to `Rat`. -/

/-- **TauRat sum split-first (toRat)**: peel off `f 0` from the sum's start.

    `(TauRat.sum f (n+1)).toRat = (f 0).toRat + (TauRat.sum (fun i => f (i+1)) n).toRat` -/
theorem TauRat.sum_split_first_toRat (f : Nat → TauRat) (n : Nat) :
    (TauRat.sum f (n + 1)).toRat
      = (f 0).toRat + (TauRat.sum (fun i => f (i + 1)) n).toRat := by
  induction n with
  | zero =>
    show (TauRat.sum f 1).toRat = (f 0).toRat + (TauRat.sum (fun i => f (i + 1)) 0).toRat
    rw [TauRat.sum_succ, TauRat.sum_zero, toRat_add, toRat_zero, zero_add]
    rw [TauRat.sum_zero, toRat_zero, add_zero]
  | succ n ih =>
    -- LHS: TauRat.sum f (n+2) = (TauRat.sum f (n+1)).add (f (n+1))
    -- RHS: (f 0).toRat + (TauRat.sum (fun i => f (i+1)) (n+1)).toRat
    --      = (f 0).toRat + ((TauRat.sum (fun i => f (i+1)) n).add ((fun i => f (i+1)) n)).toRat
    --      = (f 0).toRat + (TauRat.sum (fun i => f (i+1)) n).toRat + (f (n+1)).toRat
    rw [TauRat.sum_succ, toRat_add, ih]
    -- Apply sum_succ to the (n+1)-sized shifted sum on the RHS
    conv_rhs => rw [TauRat.sum_succ, toRat_add]
    ring

/-- **TauRat sum const-mul (toRat)**: distribute a fixed scalar across a sum.

    `((TauRat.sum f n).mul c).toRat = (TauRat.sum f n).toRat * c.toRat`

    Trivial via `toRat_mul`, included as a named lemma for proof clarity. -/
theorem TauRat.sum_mul_const_toRat (f : Nat → TauRat) (c : TauRat) (n : Nat) :
    ((TauRat.sum f n).mul c).toRat = (TauRat.sum f n).toRat * c.toRat :=
  toRat_mul _ _

/-- **Pascal at Rat level**: `C(n+1, k+1) = C(n, k) + C(n, k+1)`. -/
theorem nat_choose_succ_succ_toRat (n k : Nat) :
    ((Nat.choose (n + 1) (k + 1) : Nat) : Rat)
      = ((Nat.choose n k : Nat) : Rat) + ((Nat.choose n (k + 1) : Nat) : Rat) := by
  have h := Nat.choose_succ_succ n k
  exact_mod_cast h

/-- **Auxiliary mul-distrib at sum-size `k`** (generalized over sum size).

    Inductive helper for `binom_sum_re_mul_distrib`. Proves the identity
    for arbitrary sum size `k`, then specialize to `k = n + 1`. -/
private theorem TauComplex.binom_sum_re_mul_distrib_aux
    (z₁ z₂ z : TauComplex) (n m k : Nat) :
    (TauRat.sum (fun i =>
        (nat_to_taurat (Nat.choose n i)).mul
          (((TauComplex.pow z₁ i).mul (TauComplex.pow z₂ (n - i))).re.approx m)) k).toRat
        * ((z.re.approx m).toRat)
      - (TauRat.sum (fun i =>
          (nat_to_taurat (Nat.choose n i)).mul
            (((TauComplex.pow z₁ i).mul (TauComplex.pow z₂ (n - i))).im.approx m)) k).toRat
        * ((z.im.approx m).toRat)
      = (TauRat.sum (fun i =>
          (nat_to_taurat (Nat.choose n i)).mul
            ((((TauComplex.pow z₁ i).mul (TauComplex.pow z₂ (n - i))).mul z).re.approx m)) k).toRat := by
  induction k with
  | zero => simp [TauRat.sum_zero, toRat_zero]
  | succ k ih =>
    rw [TauRat.sum_succ, TauRat.sum_succ, TauRat.sum_succ]
    rw [toRat_add, toRat_add, toRat_add]
    -- Define short-names for clarity
    set S_re := (TauRat.sum (fun i =>
        (nat_to_taurat (Nat.choose n i)).mul
          (((TauComplex.pow z₁ i).mul (TauComplex.pow z₂ (n - i))).re.approx m)) k).toRat
    set S_im := (TauRat.sum (fun i =>
        (nat_to_taurat (Nat.choose n i)).mul
          (((TauComplex.pow z₁ i).mul (TauComplex.pow z₂ (n - i))).im.approx m)) k).toRat
    set S_h := (TauRat.sum (fun i =>
        (nat_to_taurat (Nat.choose n i)).mul
          ((((TauComplex.pow z₁ i).mul (TauComplex.pow z₂ (n - i))).mul z).re.approx m)) k).toRat
    set R_z := (z.re.approx m).toRat
    set I_z := (z.im.approx m).toRat
    set C_k := (nat_to_taurat (Nat.choose n k)).toRat
    set P_re := (((TauComplex.pow z₁ k).mul (TauComplex.pow z₂ (n - k))).re.approx m).toRat
    set P_im := (((TauComplex.pow z₁ k).mul (TauComplex.pow z₂ (n - k))).im.approx m).toRat
    -- ih: S_re * R_z - S_im * I_z = S_h
    -- Express the head term contributions at toRat
    have h_head_re : ((nat_to_taurat (Nat.choose n k)).mul
                       (((TauComplex.pow z₁ k).mul (TauComplex.pow z₂ (n - k))).re.approx m)).toRat
                   = C_k * P_re := by rw [toRat_mul]
    have h_head_im : ((nat_to_taurat (Nat.choose n k)).mul
                       (((TauComplex.pow z₁ k).mul (TauComplex.pow z₂ (n - k))).im.approx m)).toRat
                   = C_k * P_im := by rw [toRat_mul]
    have h_head_pz : ((nat_to_taurat (Nat.choose n k)).mul
                       ((((TauComplex.pow z₁ k).mul (TauComplex.pow z₂ (n - k))).mul z).re.approx m)).toRat
                   = C_k * (((((TauComplex.pow z₁ k).mul (TauComplex.pow z₂ (n - k))).mul z).re.approx m).toRat) := by
      rw [toRat_mul]
    rw [h_head_re, h_head_im, h_head_pz]
    -- Expand the (P · z).re.approx m at toRat to P_re · R z - P_im · I z
    have h_pz_re : ((((TauComplex.pow z₁ k).mul (TauComplex.pow z₂ (n - k))).mul z).re.approx m).toRat
                 = P_re * R_z - P_im * I_z := by
      rw [TauComplex.mul_re_approx, toRat_sub, toRat_mul, toRat_mul]
    rw [h_pz_re]
    -- Goal: (S_re + C_k * P_re) * R_z - (S_im + C_k * P_im) * I_z = S_h + C_k * (P_re * R_z - P_im * I_z)
    -- By ih: S_re * R_z - S_im * I_z = S_h
    linarith [ih]

/-- **Binomial sum mul-distrib (re part)**: multiplying `binom_sum_re_n` by `R z`
    and subtracting `binom_sum_im_n` by `I z` equals the sum with each binom-term
    multiplied by `z` at toRat level.

    `binom_sum_re_n · R z − binom_sum_im_n · I z = Σᵢ C(n,i) · R((pow z₁ i · pow z₂ (n-i)) · z)` -/
theorem TauComplex.binom_sum_re_mul_distrib (z₁ z₂ z : TauComplex) (n m : Nat) :
    (TauComplex.binom_sum_re z₁ z₂ n m).toRat * ((z.re.approx m).toRat)
      - (TauComplex.binom_sum_im z₁ z₂ n m).toRat * ((z.im.approx m).toRat)
    = (TauRat.sum (fun i =>
        (nat_to_taurat (Nat.choose n i)).mul
          ((((TauComplex.pow z₁ i).mul (TauComplex.pow z₂ (n - i))).mul z).re.approx m)) (n + 1)).toRat := by
  unfold TauComplex.binom_sum_re TauComplex.binom_sum_im
  exact TauComplex.binom_sum_re_mul_distrib_aux z₁ z₂ z n m (n + 1)

/-- **Binomial sum mul-distrib (im part)**: aux + main.

    `binom_sum_re_n · I z + binom_sum_im_n · R z = Σᵢ C(n,i) · I((pow z₁ i · pow z₂ (n-i)) · z)` -/
private theorem TauComplex.binom_sum_im_mul_distrib_aux
    (z₁ z₂ z : TauComplex) (n m k : Nat) :
    (TauRat.sum (fun i =>
        (nat_to_taurat (Nat.choose n i)).mul
          (((TauComplex.pow z₁ i).mul (TauComplex.pow z₂ (n - i))).re.approx m)) k).toRat
        * ((z.im.approx m).toRat)
      + (TauRat.sum (fun i =>
          (nat_to_taurat (Nat.choose n i)).mul
            (((TauComplex.pow z₁ i).mul (TauComplex.pow z₂ (n - i))).im.approx m)) k).toRat
        * ((z.re.approx m).toRat)
      = (TauRat.sum (fun i =>
          (nat_to_taurat (Nat.choose n i)).mul
            ((((TauComplex.pow z₁ i).mul (TauComplex.pow z₂ (n - i))).mul z).im.approx m)) k).toRat := by
  induction k with
  | zero => simp [TauRat.sum_zero, toRat_zero]
  | succ k ih =>
    rw [TauRat.sum_succ, TauRat.sum_succ, TauRat.sum_succ]
    rw [toRat_add, toRat_add, toRat_add]
    set S_re := (TauRat.sum (fun i =>
        (nat_to_taurat (Nat.choose n i)).mul
          (((TauComplex.pow z₁ i).mul (TauComplex.pow z₂ (n - i))).re.approx m)) k).toRat
    set S_im := (TauRat.sum (fun i =>
        (nat_to_taurat (Nat.choose n i)).mul
          (((TauComplex.pow z₁ i).mul (TauComplex.pow z₂ (n - i))).im.approx m)) k).toRat
    set S_h := (TauRat.sum (fun i =>
        (nat_to_taurat (Nat.choose n i)).mul
          ((((TauComplex.pow z₁ i).mul (TauComplex.pow z₂ (n - i))).mul z).im.approx m)) k).toRat
    set R_z := (z.re.approx m).toRat
    set I_z := (z.im.approx m).toRat
    set C_k := (nat_to_taurat (Nat.choose n k)).toRat
    set P_re := (((TauComplex.pow z₁ k).mul (TauComplex.pow z₂ (n - k))).re.approx m).toRat
    set P_im := (((TauComplex.pow z₁ k).mul (TauComplex.pow z₂ (n - k))).im.approx m).toRat
    have h_head_re : ((nat_to_taurat (Nat.choose n k)).mul
                       (((TauComplex.pow z₁ k).mul (TauComplex.pow z₂ (n - k))).re.approx m)).toRat
                   = C_k * P_re := by rw [toRat_mul]
    have h_head_im : ((nat_to_taurat (Nat.choose n k)).mul
                       (((TauComplex.pow z₁ k).mul (TauComplex.pow z₂ (n - k))).im.approx m)).toRat
                   = C_k * P_im := by rw [toRat_mul]
    have h_head_pz : ((nat_to_taurat (Nat.choose n k)).mul
                       ((((TauComplex.pow z₁ k).mul (TauComplex.pow z₂ (n - k))).mul z).im.approx m)).toRat
                   = C_k * (((((TauComplex.pow z₁ k).mul (TauComplex.pow z₂ (n - k))).mul z).im.approx m).toRat) := by
      rw [toRat_mul]
    rw [h_head_re, h_head_im, h_head_pz]
    have h_pz_im : ((((TauComplex.pow z₁ k).mul (TauComplex.pow z₂ (n - k))).mul z).im.approx m).toRat
                 = P_re * I_z + P_im * R_z := by
      rw [TauComplex.mul_im_approx, toRat_add, toRat_mul, toRat_mul]
    rw [h_pz_im]
    linarith [ih]

/-- **Binomial sum mul-distrib (im part)**: main statement. -/
theorem TauComplex.binom_sum_im_mul_distrib (z₁ z₂ z : TauComplex) (n m : Nat) :
    (TauComplex.binom_sum_re z₁ z₂ n m).toRat * ((z.im.approx m).toRat)
      + (TauComplex.binom_sum_im z₁ z₂ n m).toRat * ((z.re.approx m).toRat)
    = (TauRat.sum (fun i =>
        (nat_to_taurat (Nat.choose n i)).mul
          ((((TauComplex.pow z₁ i).mul (TauComplex.pow z₂ (n - i))).mul z).im.approx m)) (n + 1)).toRat := by
  unfold TauComplex.binom_sum_re TauComplex.binom_sum_im
  exact TauComplex.binom_sum_im_mul_distrib_aux z₁ z₂ z n m (n + 1)

-- ============================================================
-- PART 47: PHASE 3C PART 3g.2d — Pascal step (the big one)
-- ============================================================

/-! ## Pascal step at toRat level

The climax of the toRat-level binomial proof. Given:
* `mul_distrib_re/im` (Parts 3g.2d-pre*): the algebraic structure
  identities relating `binom_sum_n · z` to a single sum of products.
* `sum_split_first_toRat` (Part 3g.2c): peel first term.
* `nat_choose_succ_succ_toRat` (Part 3g.2c): Pascal's rule at Rat.
* `sum_add_toRat` (Part 3c.4): split sum-of-add into two sums.

The Pascal step:
`(binom_sum_re (n+1)).toRat = binom_sum_re_n.toRat · R(z₁+z₂)
                              − binom_sum_im_n.toRat · I(z₁+z₂)`

(and `.im` analog).

The proof manipulates LHS via `sum_split_first` + Pascal coefficient
identity + congruence at toRat level, then splits into the two
contributions and reindexes via `sum_split_first` (in reverse) to match
the RHS. -/

/-- **Sum-pointwise-equality at toRat**: if `f` and `g` agree at toRat
    pointwise, their sums agree at toRat. -/
theorem TauRat.sum_eq_of_toRat_pointwise (f g : Nat → TauRat) (n : Nat)
    (h : ∀ i, i < n → (f i).toRat = (g i).toRat) :
    (TauRat.sum f n).toRat = (TauRat.sum g n).toRat := by
  induction n with
  | zero => simp [TauRat.sum_zero, toRat_zero]
  | succ n ih =>
    rw [TauRat.sum_succ, TauRat.sum_succ, toRat_add, toRat_add]
    rw [ih (fun i hi => h i (Nat.lt_succ_of_lt hi))]
    rw [h n (Nat.lt_succ_self n)]

/-- **Pascal step Sub-lemma A** (peel `i=0` boundary, simplify Nat-arith
    `(n+1) - (i+1) = n - i` in the shifted sum).

    Mirrors the equiv-level cascade's `B_left_split_first` pattern. -/
theorem TauComplex.binom_sum_re_succ_peel_first (z₁ z₂ : TauComplex) (n m : Nat) :
    (TauComplex.binom_sum_re z₁ z₂ (n + 1) m).toRat
      = ((nat_to_taurat (Nat.choose (n + 1) 0)).mul
          (((TauComplex.pow z₁ 0).mul (TauComplex.pow z₂ (n + 1))).re.approx m)).toRat
        + (TauRat.sum (fun i => (nat_to_taurat (Nat.choose (n + 1) (i + 1))).mul
            (((TauComplex.pow z₁ (i + 1)).mul
              (TauComplex.pow z₂ (n - i))).re.approx m)) (n + 1)).toRat := by
  unfold TauComplex.binom_sum_re
  rw [TauRat.sum_split_first_toRat]
  -- Convert (n+1)-(i+1) to n-i in the shifted sum via pointwise toRat congruence
  congr 1
  apply TauRat.sum_eq_of_toRat_pointwise
  intro i _hi
  rw [show (n + 1 - (i + 1)) = (n - i) from Nat.succ_sub_succ_eq_sub n i]

/-- **Pascal step Sub-lemma B (re part)**: Pascal coefficient regroup.

    Convert `C(n+1, i+1) · X_{i+1}` sum into `(C(n,i) + C(n, i+1)) · X_{i+1}`
    sum via Pascal's rule, then split via `sum_add_toRat`.

    Mirrors the equiv-level cascade's `pascal_term_decompose` + `sum_add_split`
    pattern (TauComplexExp.lean:2269 + 2319). -/
theorem TauComplex.binom_pascal_split_re (z₁ z₂ : TauComplex) (n m : Nat) :
    (TauRat.sum (fun i => (nat_to_taurat (Nat.choose (n + 1) (i + 1))).mul
        (((TauComplex.pow z₁ (i + 1)).mul
          (TauComplex.pow z₂ (n - i))).re.approx m)) (n + 1)).toRat
      = (TauRat.sum (fun i => (nat_to_taurat (Nat.choose n i)).mul
          (((TauComplex.pow z₁ (i + 1)).mul
            (TauComplex.pow z₂ (n - i))).re.approx m)) (n + 1)).toRat
        + (TauRat.sum (fun i => (nat_to_taurat (Nat.choose n (i + 1))).mul
            (((TauComplex.pow z₁ (i + 1)).mul
              (TauComplex.pow z₂ (n - i))).re.approx m)) (n + 1)).toRat := by
  -- Step 1: convert each summand to TauRat.add form via Pascal at toRat
  rw [TauRat.sum_eq_of_toRat_pointwise
      (fun i => (nat_to_taurat (Nat.choose (n + 1) (i + 1))).mul
                  (((TauComplex.pow z₁ (i + 1)).mul
                    (TauComplex.pow z₂ (n - i))).re.approx m))
      (fun i => ((nat_to_taurat (Nat.choose n i)).mul
                  (((TauComplex.pow z₁ (i + 1)).mul
                    (TauComplex.pow z₂ (n - i))).re.approx m)).add
                ((nat_to_taurat (Nat.choose n (i + 1))).mul
                  (((TauComplex.pow z₁ (i + 1)).mul
                    (TauComplex.pow z₂ (n - i))).re.approx m)))
      (n + 1)
      (by
        intro i _hi
        rw [toRat_mul, toRat_add, toRat_mul, toRat_mul]
        rw [nat_to_taurat_toRat, nat_to_taurat_toRat, nat_to_taurat_toRat]
        rw [nat_choose_succ_succ_toRat]
        ring)]
  -- Step 2: split sum-of-add into two sums
  rw [TauRat.sum_add_toRat]

/-- **Pascal step Sub-lemma C (re part)**: boundary + second sum = Sum_B.

    LHS: `boundary_LHS + second_sum_size_(n+1)` (from Sub-lemmas A + B).
    RHS: `Sum_B_size_(n+1)` (from `binom_sum_re_mul_distrib` with `z = z₂`).

    The proof handles the size mismatch (second_sum has an extra 0-term at
    i=n where C(n, n+1) = 0) by first peeling it via `sum_succ`, then
    matching the size-n components via `sum_split_first_toRat` on Sum_B. -/
theorem TauComplex.binom_boundary_plus_second_eq_SumB_re
    (z₁ z₂ : TauComplex) (n m : Nat) :
    ((nat_to_taurat (Nat.choose (n + 1) 0)).mul
        (((TauComplex.pow z₁ 0).mul (TauComplex.pow z₂ (n + 1))).re.approx m)).toRat
      + (TauRat.sum (fun i => (nat_to_taurat (Nat.choose n (i + 1))).mul
          (((TauComplex.pow z₁ (i + 1)).mul
            (TauComplex.pow z₂ (n - i))).re.approx m)) (n + 1)).toRat
    = (TauRat.sum (fun i => (nat_to_taurat (Nat.choose n i)).mul
          ((((TauComplex.pow z₁ i).mul (TauComplex.pow z₂ (n - i))).mul z₂).re.approx m))
        (n + 1)).toRat := by
  -- Step 1: Peel the last term (i=n) of second_sum_size_(n+1) — it's 0 since C(n, n+1) = 0
  have h_peel : (TauRat.sum (fun i => (nat_to_taurat (Nat.choose n (i + 1))).mul
                  (((TauComplex.pow z₁ (i + 1)).mul
                    (TauComplex.pow z₂ (n - i))).re.approx m)) (n + 1)).toRat
              = (TauRat.sum (fun i => (nat_to_taurat (Nat.choose n (i + 1))).mul
                  (((TauComplex.pow z₁ (i + 1)).mul
                    (TauComplex.pow z₂ (n - i))).re.approx m)) n).toRat := by
    rw [TauRat.sum_succ, toRat_add]
    have h_last_zero : ((nat_to_taurat (Nat.choose n (n + 1))).mul
                          (((TauComplex.pow z₁ (n + 1)).mul
                            (TauComplex.pow z₂ (n - n))).re.approx m)).toRat = 0 := by
      rw [toRat_mul, nat_to_taurat_toRat]
      rw [Nat.choose_eq_zero_of_lt (Nat.lt_succ_self n)]
      simp
    linarith
  rw [h_peel]
  -- Step 2: Apply sum_split_first to RHS to peel i=0
  rw [TauRat.sum_split_first_toRat]
  -- Now both sides have boundary + size-n shifted sum.
  -- Avoid `congr 1` on sums (per recon: anti-pattern, hits whnf cliff).
  -- Establish each piece via `have`, then combine via `linarith`.

  -- Sub-claim A: boundaries match at toRat
  have h_bound : ((nat_to_taurat (Nat.choose (n + 1) 0)).mul
                    (((TauComplex.pow z₁ 0).mul (TauComplex.pow z₂ (n + 1))).re.approx m)).toRat
               = ((nat_to_taurat (Nat.choose n 0)).mul
                    ((((TauComplex.pow z₁ 0).mul (TauComplex.pow z₂ (n - 0))).mul z₂).re.approx m)).toRat := by
    rw [toRat_mul, toRat_mul, nat_to_taurat_toRat, nat_to_taurat_toRat]
    simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero]
    -- LHS: unfold (pow z₁ 0)·(pow z₂ (n+1)) .re.approx m .toRat
    rw [TauComplex.mul_re_approx (TauComplex.pow z₁ 0) (TauComplex.pow z₂ (n + 1))]
    rw [toRat_sub, toRat_mul, toRat_mul]
    -- LHS: apply pow_succ to pow z₂ (n+1)
    rw [TauComplex.pow_succ_re_approx_toRat z₂ n m]
    rw [TauComplex.pow_succ_im_approx_toRat z₂ n m]
    -- RHS: unfold outer ((pow z₁ 0)·(pow z₂ n))·z₂ .re.approx m .toRat
    rw [TauComplex.mul_re_approx ((TauComplex.pow z₁ 0).mul (TauComplex.pow z₂ n)) z₂]
    rw [toRat_sub, toRat_mul, toRat_mul]
    -- RHS: unfold inner (pow z₁ 0)·(pow z₂ n) .re.approx m and .im.approx m
    rw [TauComplex.mul_re_approx (TauComplex.pow z₁ 0) (TauComplex.pow z₂ n)]
    rw [TauComplex.mul_im_approx (TauComplex.pow z₁ 0) (TauComplex.pow z₂ n)]
    rw [toRat_sub, toRat_add, toRat_mul, toRat_mul, toRat_mul, toRat_mul]
    ring

  -- Sub-claim B: shifted sums match at toRat (both size n, pointwise via pow_succ for z₂)
  have h_shifted : (TauRat.sum (fun i => (nat_to_taurat (Nat.choose n (i + 1))).mul
                      (((TauComplex.pow z₁ (i + 1)).mul
                        (TauComplex.pow z₂ (n - i))).re.approx m)) n).toRat
                 = (TauRat.sum (fun i => (nat_to_taurat (Nat.choose n (i + 1))).mul
                      ((((TauComplex.pow z₁ (i + 1)).mul
                          (TauComplex.pow z₂ (n - (i + 1)))).mul z₂).re.approx m)) n).toRat := by
    apply TauRat.sum_eq_of_toRat_pointwise
    intro i hi
    -- i < n: pow_succ rearrangement applies
    have h_sub_succ : n - i = (n - (i + 1)) + 1 := by omega
    rw [h_sub_succ]
    simp only [toRat_mul, toRat_sub, toRat_add,
               TauComplex.mul_re_approx, TauComplex.mul_im_approx,
               TauComplex.pow_succ_re_approx_toRat, TauComplex.pow_succ_im_approx_toRat]
    ring

  linarith [h_bound, h_shifted]

/-- **🎯 Pascal step (Main, re part)**: the multiplicative recurrence for
    `binom_sum_re` at toRat level.

    `(binom_sum_re_(n+1)).toRat = binom_sum_re_n.toRat · R(z₁+z₂) − binom_sum_im_n.toRat · I(z₁+z₂)`

    Chains Sub-lemmas A + B + C with `binom_sum_re_mul_distrib` (twice). -/
theorem TauComplex.binom_sum_re_succ_step (z₁ z₂ : TauComplex) (n m : Nat) :
    (TauComplex.binom_sum_re z₁ z₂ (n + 1) m).toRat
      = (TauComplex.binom_sum_re z₁ z₂ n m).toRat * (((z₁.add z₂).re.approx m).toRat)
        - (TauComplex.binom_sum_im z₁ z₂ n m).toRat * (((z₁.add z₂).im.approx m).toRat) := by
  -- Establish the three structural sub-lemmas as `have`s
  have h_A := TauComplex.binom_sum_re_succ_peel_first z₁ z₂ n m
  have h_B := TauComplex.binom_pascal_split_re z₁ z₂ n m
  have h_C := TauComplex.binom_boundary_plus_second_eq_SumB_re z₁ z₂ n m
  -- Transform RHS: distribute add + apply mul_distrib (twice, z=z₁ and z=z₂)
  rw [TauComplex.add_re_approx_toRat, TauComplex.add_im_approx_toRat]
  have h_dist : (TauComplex.binom_sum_re z₁ z₂ n m).toRat
                  * ((z₁.re.approx m).toRat + (z₂.re.approx m).toRat)
                - (TauComplex.binom_sum_im z₁ z₂ n m).toRat
                  * ((z₁.im.approx m).toRat + (z₂.im.approx m).toRat)
              = ((TauComplex.binom_sum_re z₁ z₂ n m).toRat * (z₁.re.approx m).toRat
                  - (TauComplex.binom_sum_im z₁ z₂ n m).toRat * (z₁.im.approx m).toRat)
                + ((TauComplex.binom_sum_re z₁ z₂ n m).toRat * (z₂.re.approx m).toRat
                  - (TauComplex.binom_sum_im z₁ z₂ n m).toRat * (z₂.im.approx m).toRat) := by ring
  rw [h_dist]
  rw [TauComplex.binom_sum_re_mul_distrib z₁ z₂ z₁ n m]
  rw [TauComplex.binom_sum_re_mul_distrib z₁ z₂ z₂ n m]
  -- Match the first-sum (`Sum_A_form` from B's first part) with `Sum_A` from mul_distrib(z=z₁)
  have h_first_match :
      (TauRat.sum (fun i => (nat_to_taurat (Nat.choose n i)).mul
          (((TauComplex.pow z₁ (i + 1)).mul
            (TauComplex.pow z₂ (n - i))).re.approx m)) (n + 1)).toRat
      = (TauRat.sum (fun i => (nat_to_taurat (Nat.choose n i)).mul
          ((((TauComplex.pow z₁ i).mul (TauComplex.pow z₂ (n - i))).mul z₁).re.approx m))
            (n + 1)).toRat := by
    apply TauRat.sum_eq_of_toRat_pointwise
    intro i _hi
    simp only [toRat_mul, toRat_sub, toRat_add,
               TauComplex.mul_re_approx, TauComplex.mul_im_approx,
               TauComplex.pow_succ_re_approx_toRat, TauComplex.pow_succ_im_approx_toRat]
    ring
  -- Combine all four identities via linarith
  linarith [h_A, h_B, h_C, h_first_match]

-- ============================================================
-- PART 47 (continued): Symmetric .im Pascal step (3g.2d-E)
-- ============================================================

/-- **Pascal step Sub-lemma A_im** (peel `i=0` boundary, simplify Nat-arith
    in the shifted sum). Symmetric to `binom_sum_re_succ_peel_first`. -/
theorem TauComplex.binom_sum_im_succ_peel_first (z₁ z₂ : TauComplex) (n m : Nat) :
    (TauComplex.binom_sum_im z₁ z₂ (n + 1) m).toRat
      = ((nat_to_taurat (Nat.choose (n + 1) 0)).mul
          (((TauComplex.pow z₁ 0).mul (TauComplex.pow z₂ (n + 1))).im.approx m)).toRat
        + (TauRat.sum (fun i => (nat_to_taurat (Nat.choose (n + 1) (i + 1))).mul
            (((TauComplex.pow z₁ (i + 1)).mul
              (TauComplex.pow z₂ (n - i))).im.approx m)) (n + 1)).toRat := by
  unfold TauComplex.binom_sum_im
  rw [TauRat.sum_split_first_toRat]
  congr 1
  apply TauRat.sum_eq_of_toRat_pointwise
  intro i _hi
  rw [show (n + 1 - (i + 1)) = (n - i) from Nat.succ_sub_succ_eq_sub n i]

/-- **Pascal step Sub-lemma B_im**: Pascal coefficient regroup for `.im`. -/
theorem TauComplex.binom_pascal_split_im (z₁ z₂ : TauComplex) (n m : Nat) :
    (TauRat.sum (fun i => (nat_to_taurat (Nat.choose (n + 1) (i + 1))).mul
        (((TauComplex.pow z₁ (i + 1)).mul
          (TauComplex.pow z₂ (n - i))).im.approx m)) (n + 1)).toRat
      = (TauRat.sum (fun i => (nat_to_taurat (Nat.choose n i)).mul
          (((TauComplex.pow z₁ (i + 1)).mul
            (TauComplex.pow z₂ (n - i))).im.approx m)) (n + 1)).toRat
        + (TauRat.sum (fun i => (nat_to_taurat (Nat.choose n (i + 1))).mul
            (((TauComplex.pow z₁ (i + 1)).mul
              (TauComplex.pow z₂ (n - i))).im.approx m)) (n + 1)).toRat := by
  rw [TauRat.sum_eq_of_toRat_pointwise
      (fun i => (nat_to_taurat (Nat.choose (n + 1) (i + 1))).mul
                  (((TauComplex.pow z₁ (i + 1)).mul
                    (TauComplex.pow z₂ (n - i))).im.approx m))
      (fun i => ((nat_to_taurat (Nat.choose n i)).mul
                  (((TauComplex.pow z₁ (i + 1)).mul
                    (TauComplex.pow z₂ (n - i))).im.approx m)).add
                ((nat_to_taurat (Nat.choose n (i + 1))).mul
                  (((TauComplex.pow z₁ (i + 1)).mul
                    (TauComplex.pow z₂ (n - i))).im.approx m)))
      (n + 1)
      (by
        intro i _hi
        rw [toRat_mul, toRat_add, toRat_mul, toRat_mul]
        rw [nat_to_taurat_toRat, nat_to_taurat_toRat, nat_to_taurat_toRat]
        rw [nat_choose_succ_succ_toRat]
        ring)]
  rw [TauRat.sum_add_toRat]

/-- **Pascal step Sub-lemma C_im**: boundary + second sum = Sum_B_im. -/
theorem TauComplex.binom_boundary_plus_second_eq_SumB_im
    (z₁ z₂ : TauComplex) (n m : Nat) :
    ((nat_to_taurat (Nat.choose (n + 1) 0)).mul
        (((TauComplex.pow z₁ 0).mul (TauComplex.pow z₂ (n + 1))).im.approx m)).toRat
      + (TauRat.sum (fun i => (nat_to_taurat (Nat.choose n (i + 1))).mul
          (((TauComplex.pow z₁ (i + 1)).mul
            (TauComplex.pow z₂ (n - i))).im.approx m)) (n + 1)).toRat
    = (TauRat.sum (fun i => (nat_to_taurat (Nat.choose n i)).mul
          ((((TauComplex.pow z₁ i).mul (TauComplex.pow z₂ (n - i))).mul z₂).im.approx m))
        (n + 1)).toRat := by
  have h_peel : (TauRat.sum (fun i => (nat_to_taurat (Nat.choose n (i + 1))).mul
                  (((TauComplex.pow z₁ (i + 1)).mul
                    (TauComplex.pow z₂ (n - i))).im.approx m)) (n + 1)).toRat
              = (TauRat.sum (fun i => (nat_to_taurat (Nat.choose n (i + 1))).mul
                  (((TauComplex.pow z₁ (i + 1)).mul
                    (TauComplex.pow z₂ (n - i))).im.approx m)) n).toRat := by
    rw [TauRat.sum_succ, toRat_add]
    have h_last_zero : ((nat_to_taurat (Nat.choose n (n + 1))).mul
                          (((TauComplex.pow z₁ (n + 1)).mul
                            (TauComplex.pow z₂ (n - n))).im.approx m)).toRat = 0 := by
      rw [toRat_mul, nat_to_taurat_toRat]
      rw [Nat.choose_eq_zero_of_lt (Nat.lt_succ_self n)]
      simp
    linarith
  rw [h_peel]
  rw [TauRat.sum_split_first_toRat]

  have h_bound : ((nat_to_taurat (Nat.choose (n + 1) 0)).mul
                    (((TauComplex.pow z₁ 0).mul (TauComplex.pow z₂ (n + 1))).im.approx m)).toRat
               = ((nat_to_taurat (Nat.choose n 0)).mul
                    ((((TauComplex.pow z₁ 0).mul (TauComplex.pow z₂ (n - 0))).mul z₂).im.approx m)).toRat := by
    rw [toRat_mul, toRat_mul, nat_to_taurat_toRat, nat_to_taurat_toRat]
    simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero]
    rw [TauComplex.mul_im_approx (TauComplex.pow z₁ 0) (TauComplex.pow z₂ (n + 1))]
    rw [toRat_add, toRat_mul, toRat_mul]
    rw [TauComplex.pow_succ_re_approx_toRat z₂ n m]
    rw [TauComplex.pow_succ_im_approx_toRat z₂ n m]
    rw [TauComplex.mul_im_approx ((TauComplex.pow z₁ 0).mul (TauComplex.pow z₂ n)) z₂]
    rw [toRat_add, toRat_mul, toRat_mul]
    rw [TauComplex.mul_re_approx (TauComplex.pow z₁ 0) (TauComplex.pow z₂ n)]
    rw [TauComplex.mul_im_approx (TauComplex.pow z₁ 0) (TauComplex.pow z₂ n)]
    rw [toRat_sub, toRat_add, toRat_mul, toRat_mul, toRat_mul, toRat_mul]
    ring

  have h_shifted : (TauRat.sum (fun i => (nat_to_taurat (Nat.choose n (i + 1))).mul
                      (((TauComplex.pow z₁ (i + 1)).mul
                        (TauComplex.pow z₂ (n - i))).im.approx m)) n).toRat
                 = (TauRat.sum (fun i => (nat_to_taurat (Nat.choose n (i + 1))).mul
                      ((((TauComplex.pow z₁ (i + 1)).mul
                          (TauComplex.pow z₂ (n - (i + 1)))).mul z₂).im.approx m)) n).toRat := by
    apply TauRat.sum_eq_of_toRat_pointwise
    intro i hi
    have h_sub_succ : n - i = (n - (i + 1)) + 1 := by omega
    rw [h_sub_succ]
    simp only [toRat_mul, toRat_sub, toRat_add,
               TauComplex.mul_re_approx, TauComplex.mul_im_approx,
               TauComplex.pow_succ_re_approx_toRat, TauComplex.pow_succ_im_approx_toRat]
    ring

  linarith [h_bound, h_shifted]

/-- **🎯 Pascal step (Main, im part)**: the multiplicative recurrence for
    `binom_sum_im` at toRat level. -/
theorem TauComplex.binom_sum_im_succ_step (z₁ z₂ : TauComplex) (n m : Nat) :
    (TauComplex.binom_sum_im z₁ z₂ (n + 1) m).toRat
      = (TauComplex.binom_sum_re z₁ z₂ n m).toRat * (((z₁.add z₂).im.approx m).toRat)
        + (TauComplex.binom_sum_im z₁ z₂ n m).toRat * (((z₁.add z₂).re.approx m).toRat) := by
  have h_A := TauComplex.binom_sum_im_succ_peel_first z₁ z₂ n m
  have h_B := TauComplex.binom_pascal_split_im z₁ z₂ n m
  have h_C := TauComplex.binom_boundary_plus_second_eq_SumB_im z₁ z₂ n m
  rw [TauComplex.add_re_approx_toRat, TauComplex.add_im_approx_toRat]
  have h_dist : (TauComplex.binom_sum_re z₁ z₂ n m).toRat
                  * ((z₁.im.approx m).toRat + (z₂.im.approx m).toRat)
                + (TauComplex.binom_sum_im z₁ z₂ n m).toRat
                  * ((z₁.re.approx m).toRat + (z₂.re.approx m).toRat)
              = ((TauComplex.binom_sum_re z₁ z₂ n m).toRat * (z₁.im.approx m).toRat
                  + (TauComplex.binom_sum_im z₁ z₂ n m).toRat * (z₁.re.approx m).toRat)
                + ((TauComplex.binom_sum_re z₁ z₂ n m).toRat * (z₂.im.approx m).toRat
                  + (TauComplex.binom_sum_im z₁ z₂ n m).toRat * (z₂.re.approx m).toRat) := by ring
  rw [h_dist]
  rw [TauComplex.binom_sum_im_mul_distrib z₁ z₂ z₁ n m]
  rw [TauComplex.binom_sum_im_mul_distrib z₁ z₂ z₂ n m]
  have h_first_match :
      (TauRat.sum (fun i => (nat_to_taurat (Nat.choose n i)).mul
          (((TauComplex.pow z₁ (i + 1)).mul
            (TauComplex.pow z₂ (n - i))).im.approx m)) (n + 1)).toRat
      = (TauRat.sum (fun i => (nat_to_taurat (Nat.choose n i)).mul
          ((((TauComplex.pow z₁ i).mul (TauComplex.pow z₂ (n - i))).mul z₁).im.approx m))
            (n + 1)).toRat := by
    apply TauRat.sum_eq_of_toRat_pointwise
    intro i _hi
    simp only [toRat_mul, toRat_sub, toRat_add,
               TauComplex.mul_re_approx, TauComplex.mul_im_approx,
               TauComplex.pow_succ_re_approx_toRat, TauComplex.pow_succ_im_approx_toRat]
    ring
  linarith [h_A, h_B, h_C, h_first_match]

-- ============================================================
-- PART 48: PHASE 3C PART 3g.2e — Main toRat binomial theorem
-- ============================================================

/-- **🎯🎯🎯 The toRat-level binomial theorem on TauComplex**.

    `((pow (z₁ + z₂) n).{re,im}.approx m).toRat = (binom_sum_{re,im} z₁ z₂ n m).toRat`

    Proved by simultaneous induction on `n` (re + im) using:
    * Base case `n = 0` (Part 3g.2b, `add_pow_zero_re_im_approx_toRat`).
    * Pascal step `n → n+1` (Parts 3g.2d-D and 3g.2d-E,
      `binom_sum_re/im_succ_step`).

    Each inductive step: expand `(pow (z₁+z₂) (n+1)).{re,im}.approx m .toRat`
    via `pow_succ_{re,im}_approx_toRat`, substitute IH (re + im), then
    apply the Pascal step in reverse direction. -/
theorem TauComplex.add_pow_re_im_approx_toRat (z₁ z₂ : TauComplex) (n m : Nat) :
    ((TauComplex.pow (z₁.add z₂) n).re.approx m).toRat
      = (TauComplex.binom_sum_re z₁ z₂ n m).toRat ∧
    ((TauComplex.pow (z₁.add z₂) n).im.approx m).toRat
      = (TauComplex.binom_sum_im z₁ z₂ n m).toRat := by
  induction n with
  | zero => exact TauComplex.add_pow_zero_re_im_approx_toRat z₁ z₂ m
  | succ n ih =>
    obtain ⟨ih_re, ih_im⟩ := ih
    refine ⟨?_, ?_⟩
    · -- .re at n+1
      rw [TauComplex.pow_succ_re_approx_toRat]
      rw [ih_re, ih_im]
      exact (TauComplex.binom_sum_re_succ_step z₁ z₂ n m).symm
    · -- .im at n+1
      rw [TauComplex.pow_succ_im_approx_toRat]
      rw [ih_re, ih_im]
      exact (TauComplex.binom_sum_im_succ_step z₁ z₂ n m).symm

end Tau.Boundary
