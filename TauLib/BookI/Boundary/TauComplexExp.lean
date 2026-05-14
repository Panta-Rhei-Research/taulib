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

**Wave Γ₇ Phase 3C Part 2 — τ-native exp on the cyclotomic-4 extension.**

The Taylor series for `exp(z)` on `TauComplex = TauReal[X]/(X²+1)`:

$$ \exp(z) \;=\; \sum_{k=0}^{\infty} \frac{z^k}{k!} . $$

When specialised to purely imaginary arguments `z = i·x` (with the
cyclotomic-4 root `i`), this gives **Euler's formula**:

$$ \exp(i \cdot x) \;=\; \cos(x) + i \cdot \sin(x) . $$

The cyclotomic-4 structure of `i` is what makes this work: powers of `i`
cycle through `{1, i, -1, -i}` with period 4, separating the even-power
real contributions (cos terms) from the odd-power imaginary contributions
(sin terms). This module proves the load-bearing **cyclotomic-4 identity**
`i⁴ ≈ 1` and sets up the exp infrastructure on TauComplex.

## Phase 3C Part 2 vs Part 3 / 4

* **Part 2 (this commit)**: `TauComplex.pow` via iterated multiplication;
  the **cyclotomic-4 identity** `i^4 ≈ 1`; foundational simp lemmas.
* **Part 2b (next session)**: `TauReal.scale_by_inv_factorial`,
  `TauComplex.exp_term`, `TauComplex.exp_partial`, basic Cauchy
  property at TauRat-pair level.
* **Part 3 (M3 breakthrough)**: lift `TauReal.exp_add` to
  `TauComplex.exp_add` via Cauchy products on the cyclotomic extension.
* **Part 4**: specialise to purely imaginary arguments via the
  cyclotomic structure; extract sin/cos addition formulae.

## Why i⁴ ≈ 1 is the load-bearing identity

The cyclotomic group `μ_4 := {1, i, -1, -i} ⊂ TauComplex` is generated
by `i` with relation `i^4 = 1`. This identity:

1. **Validates the cyclotomic framing**: the docstring redesign of
   `ComplexField.lean` claims `TauComplex` is `TauReal[X]/(X²+1)`;
   `X²+1` divides `X⁴-1`, so the quotient automatically satisfies
   `X⁴ = 1`. Proving `i⁴ ≈ 1` τ-natively confirms this.

2. **Sets up Euler's formula**: when we compute `exp(i·x)` via Taylor
   series, the powers of `i` cycle:
   - `i^(4k+0) = 1` → contributes to `cos(x)`'s even Taylor coefficients
   - `i^(4k+1) = i` → contributes to `sin(x)` first-imaginary
   - `i^(4k+2) = -1` → contributes to `cos(x)`'s alternating-sign even
   - `i^(4k+3) = -i` → contributes to `sin(x)`'s alternating-sign odd
   The 4-cycle is precisely what makes `exp(i·x) = cos(x) + i·sin(x)`.

3. **Confirms structural readiness for M3**: if `i^4` works τ-natively,
   the cyclotomic infrastructure is sound. The remaining work
   (exp_partial Cauchy + exp_add lift) is mechanical Cauchy-product
   manipulation.

## Build state

* `sorry` count: 0
* `axiom` count: 0
* Imports: ComplexField (TauComplex), TauRealSum, TauRealExp + tactics.
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

## What this commit (Phase 3C Part 3a) adds

* `TauComplex.cauchyDiag a b n` — n-th Cauchy product diagonal.
* `TauComplex.cauchyPStar a b N` — partial Cauchy product.
* Simp lemmas: `cauchyPStar_zero`, `cauchyPStar_succ`, `cauchyDiag_zero`.
* Detailed roadmap (this docstring) for Phase 3C Part 3b → 4.

The Cauchy-product infrastructure is the **load-bearing structural
foundation** for the M3 breakthrough proper. With this in place,
Phase 3C Part 3b can focus narrowly on the binomial identity proof
without needing to first design the algebraic framework.

## Trust budget (unchanged)

* sorry = 0
* axioms = 3
* TauLib build: 2695/2695 jobs ✓
* No new mathematical claims proved here — Part 3a is pure infrastructure.
-/

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

end Tau.Boundary
