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
-- PART 3: STRUCTURAL FOUNDATION FOR exp_partial (Phase 3C Part 2b)
-- ============================================================

/-! ## Phase 3C Part 2b roadmap (next session)

The `TauComplex.exp_partial z n := Σ_{k=0}^{n-1} z^k / k!` construction
requires:

1. **`TauReal.scale_by_inv_factorial`** (helper at TauReal level):
   ```
   def TauReal.scale_by_inv_factorial (x : TauReal) (k : Nat) : TauReal :=
     ⟨fun n => { num := (x.approx n).num,
                  den := (x.approx n).den * k.factorial,
                  den_pos := ... }⟩
   ```
   Mirrors the `TauRat.exp_term` denominator multiplication.

2. **`TauComplex.exp_term z k := pow z k / k!`** at the TauComplex level:
   ```
   def TauComplex.exp_term (z : TauComplex) (k : Nat) : TauComplex :=
     ⟨TauReal.scale_by_inv_factorial (TauComplex.pow z k).re k,
      TauReal.scale_by_inv_factorial (TauComplex.pow z k).im k⟩
   ```

3. **`TauComplex.exp_partial z n`**: sum of exp_terms.

4. **Cauchy proof**: lift from `TauReal.exp_partial_cauchy_bound`
   (Wave 3b R10). The TauComplex Cauchy property holds componentwise:
   each of `re` and `im` partial sums is Cauchy when |z| is bounded.

## Phase 3C Part 3 (M3 breakthrough proper)

Lift `TauReal.exp_add` (the binomial-Cauchy-product identity, ~200 LOC
in TauRealExp.lean) to `TauComplex.exp_add`. The lift is mechanical
once exp_partial is in place: the Cauchy product on TauComplex
respects the same combinatorial structure as on TauReal, just with
complex multiplication on the products.

## Phase 3C Part 4 (sin/cos addition formula extraction)

Specialise `TauComplex.exp_add` to purely imaginary arguments:
- `exp(i·α) · exp(i·β) ≈ exp(i·(α+β))`
- LHS = `(cos α + i sin α) · (cos β + i sin β)`
       = `(cos α cos β - sin α sin β) + i (cos α sin β + sin α cos β)`
- RHS = `cos(α+β) + i sin(α+β)`
- Equating real / imag parts via `TauComplex.equiv` gives the sin/cos
  addition formulae as τ-native theorems.

The cyclotomic-4 root identity `i^4 ≈ 1` proved in this commit is
the structural anchor for the whole chain — it confirms that the
extension behaves correctly under repeated multiplication.
-/

end Tau.Boundary
