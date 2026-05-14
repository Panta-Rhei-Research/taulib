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

end Tau.Boundary
