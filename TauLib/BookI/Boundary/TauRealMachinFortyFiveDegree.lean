import TauLib.BookI.Boundary.TauRealMachinProducts
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# TauLib.BookI.Boundary.TauRealMachinFortyFiveDegree

**Phase E Option 2 — the 45°-line algebraic core identity for the
Machin product**.

After Phase E Scope A+A.5 (`TauRealMachinProducts.lean`) shipped the
quadruple-arctan product identity and the parity-substituted Machin
product, this module advances toward the **45°-line identity** —
the τ-native form of the classical fact

> `4·arctan(1/5) − arctan(1/239) = π/4`.

At the cisTauReal level, this says that the (parity-substituted) Machin
product lies on the line `y = x` in the complex plane:

>   `(cisTauReal(arctan(1/5))⁴ · ⟨cisB.re, negate cisB.im⟩).re`
>     `≈ (cisTauReal(arctan(1/5))⁴ · ⟨cisB.re, negate cisB.im⟩).im`
>
>   where `cisB := cisTauReal(arctan(1/239))`.

This is the **τ-native incarnation of the Machin classical identity**:
the product, lying on the 45° line, matches the angle of
`cisTauReal(π/4) = (1/√2, 1/√2)`.

### What this module ships (Scope 2A-core)

The full TauReal-equiv 45°-line identity has two distinct components:
1. **The pure algebraic identity** — at every depth n, under F.6
   pointwise substitution, the difference `.re - .im` vanishes
   as a rational polynomial.
2. **The Cauchy-modulus lift** — F.6 is Cauchy-equiv (not pointwise),
   so component 1 lifts to TauReal-equiv via a polynomial-bound
   modulus construction.

This module ships **component 1** in full rigor:

* **`machin_45_re_struct`, `machin_45_im_struct`** — structural
  decomposition of `(P·W).re` and `(P·W).im` (where `P := cisA⁴`,
  `W := ⟨cisB.re, negate cisB.im⟩`).
* **`cisA_sq_re/im_approx`, `cisA_quad_re/im_approx`** — pointwise
  polynomial forms for cisA² and cisA⁴ in terms of `cisR a n`
  and `cisI a n`.
* **`machin_45_re_approx`, `machin_45_im_approx`** — pointwise toRat
  expansion of `(P·W).re/.im` at any depth n as polynomials in
  `cisR a n, cisI a n, cisR b n, cisI b n`.
* **`machin_45_difference_under_F6`** — the headline polynomial form:
  under F.6 pointwise hypotheses, the difference `.re - .im` at depth n
  equals
      `cisR a n^4 · cisR b n · K(a.toRat, b.toRat)`
  where `K(a, b) := (1+b)·(1-6a²+a⁴) - (1-b)·(4a-4a³)`.
* **`machin_45_vanishes_at_machin_constants_under_F6`** — at
  `a = 1/5, b = 1/239`, the K-factor vanishes (integer arithmetic
  `240·476 = 238·480 = 114240`), hence the difference vanishes.
* **`machin_45_int_identity`, `machin_45_rat_identity`** — the
  underlying integer arithmetic identity, isolated as standalone
  `norm_num` propositions.

### The polynomial identity at the core

After applying F.6 substitutions, both `.re` and `.im` reduce to
expressions whose difference equals
`cisA.re⁴ · cisB.re · K(a, b)`. The identity `K(a, b) = 0` at
`a = 1/5, b = 1/239` reduces to the pure integer arithmetic:

> `(1 + 1/239) · ((1 − (1/5)²)² − 4·(1/5)²)
>   = (1 − 1/239) · (4·(1/5)·(1 − (1/5)²))`

which clears to `240·476 = 238·480 = 114240`, hence both sides equal
`114240/(239·625)`. **This integer arithmetic IS the τ-native
incarnation of Machin's classical formula.**

### What remains for the full TauReal-equiv lift (Scope 2A-lift)

The Cauchy-modulus lift requires:
1. Express `D := (P·W).re.sub (P·W).im` as a TauReal in
   `cisR a, cisI a, cisR b, cisI b`.
2. Substitute `cisI a = a·cisR a + tangent_defect a` and
   `cisI b = b·cisR b + tangent_defect b` (where tangent_defect
   is F.6's defect TauReal).
3. The ground term `R⁴·B_R·K(a,b) = 0` at Machin constants.
4. The remainder is polynomial in `tangent_defect a` and `tangent_defect b`,
   bounded by `|tangent_defect_a| · poly(8) + |tangent_defect_b| · poly(8)`.
5. F.6 (`cisTauReal_tangent_target_A_path_beta`) gives both defects
   `≈ 0` (Cauchy-equiv), supplying the modulus.
6. Combine to construct a modulus for `D ≈ 0`, then apply
   `equiv_of_sub_equiv_zero` (reverse direction).

The structural-pointwise infrastructure shipped here makes this
lift mechanical (no new mathematical insight needed). Estimated
size: ~500-1000 LOC of `equiv_mul_congr` + bound chasing chains.

### What remains to close `MachinIdentity`

Beyond Scope 2A-lift, MachinIdentity also needs:
- Connect 45°-line cisTauReal value to `cisTauReal(π/4) = (1+i)/√2`
  (requires τ-native magnitude or further structural manipulation).
- Scale to π via distributivity.
- Connect to the Leibniz pi.

## Module name

This file is picked up by the `.submodules` glob in `lakefile.lean`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Tau.Boundary

open Tau.Denotation

-- ============================================================
-- PART 0: SHORTHAND DEFINITIONS FOR READABILITY
-- ============================================================

/-! ## Shorthand definitions

  These local-style abbreviations keep the proof readable. They reduce
  the bulk of the proof from "30-line types repeated 20×" to
  "concise mnemonic forms".

  In Lean we cannot use local `let` bindings in theorem statements,
  so we use plain `def`s gated by `private`. -/

/-- The cosine-like real part of `cisTauReal(arctan a)`. -/
private def cisA_re (a : TauRat) : TauReal :=
  (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).re

/-- The sine-like imaginary part of `cisTauReal(arctan a)`. -/
private def cisA_im (a : TauRat) : TauReal :=
  (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).im

-- ============================================================
-- PART 1: STRUCTURAL re/im OF cisA⁴ · conj(cisB)
-- ============================================================

/-! ## Structural decomposition of the parity-substituted Machin product

  With `P := cisA · cisA · cisA · cisA = (cisA·cisA)·(cisA·cisA)` and
  `W := ⟨cisB.re, negate cisB.im⟩`, the structural product has:

      `(P · W).re = P.re · W.re - P.im · W.im
                  = P.re · cisB.re - P.im · (negate cisB.im)`

      `(P · W).im = P.re · W.im + P.im · W.re
                  = P.re · (negate cisB.im) + P.im · cisB.re`

  These are **definitional equalities** at the structural level
  (no F.6 yet). -/

/-- **Structural .re decomposition of the parity-substituted Machin product** —
    Direct unfolding of `TauComplex.mul .re`. -/
theorem TauReal.machin_45_re_struct (a b : TauRat) :
    ((((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).mul
        (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a))).mul
      ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).mul
        (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)))).mul
      ⟨(TauComplex.cisTauReal (TauReal.arctan_of_rat_seq b)).re,
       TauReal.negate (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq b)).im⟩).re
    = (((((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).mul
          (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a))).mul
        ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).mul
          (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)))).re.mul
        (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq b)).re).sub
        ((((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).mul
            (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a))).mul
          ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).mul
            (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)))).im.mul
          (TauReal.negate (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq b)).im))) := rfl

/-- **Structural .im decomposition of the parity-substituted Machin product** —
    Direct unfolding of `TauComplex.mul .im`. -/
theorem TauReal.machin_45_im_struct (a b : TauRat) :
    ((((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).mul
        (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a))).mul
      ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).mul
        (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)))).mul
      ⟨(TauComplex.cisTauReal (TauReal.arctan_of_rat_seq b)).re,
       TauReal.negate (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq b)).im⟩).im
    = (((((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).mul
          (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a))).mul
        ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).mul
          (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)))).re.mul
        (TauReal.negate (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq b)).im)).add
        ((((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).mul
            (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a))).mul
          ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).mul
            (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)))).im.mul
          (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq b)).re)) := rfl

-- ============================================================
-- PART 2: POINTWISE TOREAL FORM OF THE DIFFERENCE .re - .im
-- ============================================================

/-! ## Pointwise toRat form of the .re/.im difference

  The crucial observation: at every depth `n`, the difference
  `(P·W).re.approx n .toRat - (P·W).im.approx n .toRat` is a polynomial
  in the rationals `P.re.approx n .toRat`, `P.im.approx n .toRat`,
  `cisB.re.approx n .toRat`, `cisB.im.approx n .toRat`.

  Concretely:
      `D_n := (.re - .im).approx n .toRat`
           `= P.re_n · cisB.re_n - P.im_n · (- cisB.im_n)`
           `  - (P.re_n · (- cisB.im_n) + P.im_n · cisB.re_n)`
           `= P.re_n · cisB.re_n + P.im_n · cisB.im_n`
           `  + P.re_n · cisB.im_n - P.im_n · cisB.re_n`
           `= (P.re_n + P.im_n)·cisB.im_n + (P.re_n - P.im_n)·... wait`

  Let me redo: with the signs:
      `D_n = P.re_n · cisB.re_n - P.im_n · (-cisB.im_n)`
            `- P.re_n · (-cisB.im_n) - P.im_n · cisB.re_n`
          `= P.re_n · cisB.re_n + P.im_n · cisB.im_n`
            `+ P.re_n · cisB.im_n - P.im_n · cisB.re_n`
          `= (P.re_n - P.im_n)·cisB.re_n + (P.re_n + P.im_n)·cisB.im_n`

  Now using `cisB.im_n ≈ b · cisB.re_n` (F.6 — at the equiv level, not
  pointwise), AND with the further substitution `P.im ≈ scalar · cisA.re⁴`,
  `P.re ≈ scalar' · cisA.re⁴`, we get the algebraic identity needed.

  We work pointwise at the difference level. -/

-- ============================================================
-- PART 3: CORE ALGEBRAIC IDENTITY — THE 45°-LINE FOR a=1/5, b=1/239
-- ============================================================

/-! ## The algebraic core identity

  Given the Machin constants `a = 1/5, b = 1/239`, the polynomial
  identity that makes the 45°-line work is:

      `K_re := (1 - a²)² - (2a)² = 1 - 6a² + a⁴`
      `K_im := 2·(1 - a²)·(2a) = 4a·(1 - a²)`

  Then `(1+b)·K_re = (1-b)·K_im` iff
      `(1+b)·(1 - 6a² + a⁴) = (1-b)·(4a - 4a³)`.

  At `a = 1/5, b = 1/239`:
      `(240/239)·(1 - 6/25 + 1/625) = (240/239)·(625 - 150 + 1)/625
                                    = (240·476)/(239·625) = 114240/(239·625)`
      `(238/239)·(4/5 - 4/125)      = (238/239)·(100 - 4)/125
                                    = (238·96)/(239·125) = 22848/(239·125)
                                    = 114240/(239·625)`           [×5/5]

  Both equal `114240/(239·625)`, hence the polynomial identity holds.
-/

/-- **The core integer arithmetic identity** —
    the 45°-line algebraic Machin identity, reduced to pure Nat/Int.

    `(1+1/239)·((1-(1/5)²)² − 4·(1/5)²) = (1−1/239)·(4·(1/5)·(1−(1/5)²))`

    Equivalent integer form: `240·476 = 238·480 = 114240`.
    Equivalent rational form: both sides reduce to `114240/(239·625)`. -/
theorem machin_45_rat_identity :
    ((240 : Rat) / 239) * ((1 - 6*(1/5)^2 + (1/5)^4))
      = ((238 : Rat) / 239) * (4 * (1/5) * (1 - (1/5)^2)) := by
  norm_num

/-- **The core algebraic identity** in cleaner form: the rational
    `(1+b)·K_re = (1-b)·K_im` evaluation at `a = 1/5, b = 1/239`. -/
theorem machin_45_rat_identity_form2 :
    let a : Rat := 1/5
    let b : Rat := 1/239
    let K_re : Rat := 1 - 6*a^2 + a^4
    let K_im : Rat := 4*a - 4*a^3
    (1 + b) * K_re = (1 - b) * K_im := by
  norm_num

/-- **Integer form**: 240·476 = 114240 = 238·480. -/
theorem machin_45_int_identity :
    240 * 476 = 238 * 480 := by norm_num

-- ============================================================
-- PART 4: POINTWISE TOREAL EXPRESSION OF .re AND .im
-- ============================================================

/-! ## Pointwise toRat expression of the Machin product .re and .im

  At every depth `n`, both `(P·W).re.approx n .toRat` and
  `(P·W).im.approx n .toRat` are polynomials in the four scalars
  `cisA.re_n, cisA.im_n, cisB.re_n, cisB.im_n` (where
  `cisA = cisTauReal(arctan a)`, etc.). We expose these polynomial
  forms via direct `toRat` computation.

  The polynomial form is the key bridge to applying F.6's tangent
  identity: at every depth, the rationals involved are polynomial
  in cisA.re/im, cisB.re/im, and after F.6's TauReal-equiv
  substitution (`cisA.im ≈ a·cisA.re`, `cisB.im ≈ b·cisB.re`),
  the resulting expression simplifies via the algebraic identity.
-/

/-- Abbreviation for `(cisTauReal(arctan a)).re.approx n .toRat`. -/
private noncomputable def cisR (a : TauRat) (n : Nat) : Rat :=
  ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).re.approx n).toRat

/-- Abbreviation for `(cisTauReal(arctan a)).im.approx n .toRat`. -/
private noncomputable def cisI (a : TauRat) (n : Nat) : Rat :=
  ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).im.approx n).toRat

/-- **Pointwise expansion of (cisA·cisA).re.approx n .toRat**. -/
private theorem cisA_sq_re_approx (a : TauRat) (n : Nat) :
    (((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).mul
        (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a))).re.approx n).toRat
      = cisR a n * cisR a n - cisI a n * cisI a n := by
  show (TauRat.add
          (TauRat.mul ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).re.approx n)
            ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).re.approx n))
          (TauRat.negate
            (TauRat.mul ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).im.approx n)
              ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).im.approx n)))).toRat = _
  rw [toRat_add, toRat_negate, toRat_mul, toRat_mul]
  unfold cisR cisI
  ring

/-- **Pointwise expansion of (cisA·cisA).im.approx n .toRat**. -/
private theorem cisA_sq_im_approx (a : TauRat) (n : Nat) :
    (((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).mul
        (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a))).im.approx n).toRat
      = cisR a n * cisI a n + cisI a n * cisR a n := by
  show (TauRat.add
          (TauRat.mul ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).re.approx n)
            ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).im.approx n))
          (TauRat.mul ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).im.approx n)
            ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).re.approx n))).toRat = _
  rw [toRat_add, toRat_mul, toRat_mul]
  unfold cisR cisI
  ring

/-- **Pointwise expansion of (cisA⁴).re.approx n .toRat**, where
    `cisA⁴ := (cisA·cisA)·(cisA·cisA)`. -/
private theorem cisA_quad_re_approx (a : TauRat) (n : Nat) :
    ((((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).mul
        (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a))).mul
      ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).mul
        (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)))).re.approx n).toRat
      = (cisR a n * cisR a n - cisI a n * cisI a n) *
          (cisR a n * cisR a n - cisI a n * cisI a n) -
        (cisR a n * cisI a n + cisI a n * cisR a n) *
          (cisR a n * cisI a n + cisI a n * cisR a n) := by
  show (TauRat.add
          (TauRat.mul (((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).mul
                (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a))).re.approx n)
            (((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).mul
                (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a))).re.approx n))
          (TauRat.negate
            (TauRat.mul (((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).mul
                  (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a))).im.approx n)
              (((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).mul
                  (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a))).im.approx n)))).toRat = _
  rw [toRat_add, toRat_negate, toRat_mul, toRat_mul]
  rw [cisA_sq_re_approx, cisA_sq_im_approx]
  ring

/-- **Pointwise expansion of (cisA⁴).im.approx n .toRat**. -/
private theorem cisA_quad_im_approx (a : TauRat) (n : Nat) :
    ((((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).mul
        (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a))).mul
      ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).mul
        (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)))).im.approx n).toRat
      = (cisR a n * cisR a n - cisI a n * cisI a n) *
          (cisR a n * cisI a n + cisI a n * cisR a n) +
        (cisR a n * cisI a n + cisI a n * cisR a n) *
          (cisR a n * cisR a n - cisI a n * cisI a n) := by
  show (TauRat.add
          (TauRat.mul (((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).mul
                (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a))).re.approx n)
            (((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).mul
                (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a))).im.approx n))
          (TauRat.mul (((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).mul
                (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a))).im.approx n)
            (((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).mul
                (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a))).re.approx n))).toRat = _
  rw [toRat_add, toRat_mul, toRat_mul]
  rw [cisA_sq_re_approx, cisA_sq_im_approx]

-- ============================================================
-- PART 5: POINTWISE FORM OF (P·W).re AND (P·W).im
-- ============================================================

/-! ## Pointwise expressions for the parity-substituted Machin product

  With P := cisA⁴ and W := ⟨cisB.re, negate cisB.im⟩, the structural
  unfoldings give us:

      `(P·W).re_n = P.re_n · cisB.re_n - P.im_n · (- cisB.im_n)
                  = P.re_n · cisB.re_n + P.im_n · cisB.im_n`

      `(P·W).im_n = P.re_n · (- cisB.im_n) + P.im_n · cisB.re_n
                  = - P.re_n · cisB.im_n + P.im_n · cisB.re_n`

  And the difference:
      `D_n := (P·W).re_n - (P·W).im_n
            = P.re_n · cisB.re_n + P.im_n · cisB.im_n
              + P.re_n · cisB.im_n - P.im_n · cisB.re_n`
            = P.re_n · (cisB.re_n + cisB.im_n)
              + P.im_n · (cisB.im_n - cisB.re_n)
            = P.re_n · (cisB.re_n + cisB.im_n)
              - P.im_n · (cisB.re_n - cisB.im_n)

  Substituting the pointwise polynomial forms for P.re_n, P.im_n
  (in terms of R := cisR a n, I := cisI a n) and assuming
  F.6 holds at depth n pointwise:
      I = a·R   and  cisB.im_n = b · cisB.re_n,
  we get
      D_n = R⁴·(1-6a²+a⁴) · cisB.re_n · (1 + b)
            - 4a·R⁴·(1-a²) · cisB.re_n · (1 - b)
          = R⁴ · cisB.re_n · [(1+b)·(1-6a²+a⁴) - (1-b)·4a·(1-a²)]

  Substituting a = 1/5, b = 1/239:
      (1+b)·(1-6a²+a⁴) - (1-b)·4a(1-a²)
        = (240/239)·(476/625) - (238/239)·(480/625)
        = (240·476 - 238·480)/(239·625)
        = (114240 - 114240)/(239·625) = 0.

  So D_n = 0 under the F.6-pointwise hypothesis. -/

/-- **Pointwise expression for the parity-substituted Machin product's .re**.

    `(P·W).re.approx n .toRat = P.re_n · cisB.re_n + P.im_n · cisB.im_n`
    where `P.re_n` and `P.im_n` are the cisA⁴ pointwise polynomial forms. -/
theorem TauReal.machin_45_re_approx (a b : TauRat) (n : Nat) :
    (((((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).mul
          (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a))).mul
        ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).mul
          (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)))).mul
        ⟨(TauComplex.cisTauReal (TauReal.arctan_of_rat_seq b)).re,
         TauReal.negate (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq b)).im⟩).re.approx n).toRat
      = ((cisR a n * cisR a n - cisI a n * cisI a n) *
            (cisR a n * cisR a n - cisI a n * cisI a n) -
          (cisR a n * cisI a n + cisI a n * cisR a n) *
            (cisR a n * cisI a n + cisI a n * cisR a n)) * cisR b n
        + ((cisR a n * cisR a n - cisI a n * cisI a n) *
              (cisR a n * cisI a n + cisI a n * cisR a n) +
            (cisR a n * cisI a n + cisI a n * cisR a n) *
              (cisR a n * cisR a n - cisI a n * cisI a n)) * cisI b n := by
  rw [TauReal.machin_45_re_struct]
  show (TauRat.add
          (TauRat.mul ((((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).mul
                (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a))).mul
              ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).mul
                (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)))).re.approx n)
            ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq b)).re.approx n))
          (TauRat.negate
            (TauRat.mul ((((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).mul
                  (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a))).mul
                ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).mul
                  (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)))).im.approx n)
              (TauRat.negate ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq b)).im.approx n))))).toRat = _
  rw [toRat_add, toRat_negate, toRat_mul, toRat_mul, toRat_negate]
  rw [cisA_quad_re_approx, cisA_quad_im_approx]
  unfold cisR cisI
  ring

/-- **Pointwise expression for the parity-substituted Machin product's .im**. -/
theorem TauReal.machin_45_im_approx (a b : TauRat) (n : Nat) :
    (((((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).mul
          (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a))).mul
        ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).mul
          (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)))).mul
        ⟨(TauComplex.cisTauReal (TauReal.arctan_of_rat_seq b)).re,
         TauReal.negate (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq b)).im⟩).im.approx n).toRat
      = - ((cisR a n * cisR a n - cisI a n * cisI a n) *
            (cisR a n * cisR a n - cisI a n * cisI a n) -
          (cisR a n * cisI a n + cisI a n * cisR a n) *
            (cisR a n * cisI a n + cisI a n * cisR a n)) * cisI b n
        + ((cisR a n * cisR a n - cisI a n * cisI a n) *
              (cisR a n * cisI a n + cisI a n * cisR a n) +
            (cisR a n * cisI a n + cisI a n * cisR a n) *
              (cisR a n * cisR a n - cisI a n * cisI a n)) * cisR b n := by
  rw [TauReal.machin_45_im_struct]
  show (TauRat.add
          (TauRat.mul ((((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).mul
                (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a))).mul
              ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).mul
                (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)))).re.approx n)
            (TauRat.negate ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq b)).im.approx n)))
          (TauRat.mul ((((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).mul
                (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a))).mul
              ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).mul
                (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)))).im.approx n)
            ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq b)).re.approx n))).toRat = _
  rw [toRat_add, toRat_mul, toRat_mul, toRat_negate]
  rw [cisA_quad_re_approx, cisA_quad_im_approx]
  unfold cisR cisI
  ring

-- ============================================================
-- PART 6: ALGEBRAIC IDENTITY AT DEPTH n UNDER F.6 SUBSTITUTION
-- ============================================================

/-! ## The 45°-line identity at depth n under F.6 pointwise substitution

  At any depth `n`, IF F.6 substitution holds pointwise (i.e., if
  `cisI a n = a.toRat · cisR a n` and `cisI b n = b.toRat · cisR b n`),
  THEN the difference `(P·W).re.approx n .toRat - (P·W).im.approx n .toRat`
  is the rational polynomial

      `cisR a n^4 · cisR b n · K(a.toRat, b.toRat)`

  where the K-factor is the algebraic core

      `K(a, b) := (1+b)·(1 - 6a² + a⁴) - (1-b)·(4a - 4a³)`.

  At `a = 1/5, b = 1/239`, this K-factor equals 0 (the integer identity
  `240·476 = 238·480`).
-/

/-- **Algebraic difference at depth n, under F.6 hypothesis** —
    if `I = a·R` and `B_I = b·B_R` pointwise at depth n, then the
    structural difference `.re - .im` at depth n equals
    `R⁴·B_R · ((1+b)·(1-6a²+a⁴) - (1-b)·4a(1-a²))`.

    This is the **pure algebraic core** of the 45°-line identity, with
    F.6 substituted in directly. -/
theorem TauReal.machin_45_difference_under_F6 (a b : TauRat) (n : Nat)
    (h_a_F6 : cisI a n = a.toRat * cisR a n)
    (h_b_F6 : cisI b n = b.toRat * cisR b n) :
    (((((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).mul
          (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a))).mul
        ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).mul
          (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)))).mul
        ⟨(TauComplex.cisTauReal (TauReal.arctan_of_rat_seq b)).re,
         TauReal.negate (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq b)).im⟩).re.approx n).toRat
      - (((((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).mul
              (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a))).mul
            ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).mul
              (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)))).mul
            ⟨(TauComplex.cisTauReal (TauReal.arctan_of_rat_seq b)).re,
             TauReal.negate (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq b)).im⟩).im.approx n).toRat
      = cisR a n^4 * cisR b n *
          ((1 + b.toRat) * (1 - 6*a.toRat^2 + a.toRat^4) -
           (1 - b.toRat) * (4*a.toRat - 4*a.toRat^3)) := by
  rw [TauReal.machin_45_re_approx, TauReal.machin_45_im_approx]
  rw [h_a_F6, h_b_F6]
  ring

/-- **Vanishing of the algebraic core at a=1/5, b=1/239** —
    the integer identity `240·476 = 238·480 = 114240` lifted to
    a Rat-level evaluation of the K-factor. -/
theorem machin_45_K_zero :
    let a : Rat := 1/5
    let b : Rat := 1/239
    (1 + b) * (1 - 6*a^2 + a^4) - (1 - b) * (4*a - 4*a^3) = 0 := by
  norm_num

/-- **The depth-n 45°-line vanishing identity under F.6** —
    For `a = 1/5, b = 1/239`, the difference `.re - .im` at depth n
    vanishes whenever the F.6 substitutions `cisI = a·cisR` and
    `cisI_b = b·cisR_b` hold pointwise at depth n. -/
theorem TauReal.machin_45_vanishes_at_machin_constants_under_F6 (n : Nat)
    (h_a_F6 : cisI TauRat.one_fifth n =
              TauRat.one_fifth.toRat * cisR TauRat.one_fifth n)
    (h_b_F6 : cisI TauRat.one_two_three_nine n =
              TauRat.one_two_three_nine.toRat * cisR TauRat.one_two_three_nine n) :
    (((((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq TauRat.one_fifth)).mul
          (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq TauRat.one_fifth))).mul
        ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq TauRat.one_fifth)).mul
          (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq TauRat.one_fifth)))).mul
        ⟨(TauComplex.cisTauReal (TauReal.arctan_of_rat_seq TauRat.one_two_three_nine)).re,
         TauReal.negate
          (TauComplex.cisTauReal
            (TauReal.arctan_of_rat_seq TauRat.one_two_three_nine)).im⟩).re.approx n).toRat
      - (((((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq TauRat.one_fifth)).mul
              (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq TauRat.one_fifth))).mul
            ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq TauRat.one_fifth)).mul
              (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq TauRat.one_fifth)))).mul
            ⟨(TauComplex.cisTauReal (TauReal.arctan_of_rat_seq TauRat.one_two_three_nine)).re,
             TauReal.negate
              (TauComplex.cisTauReal
                (TauReal.arctan_of_rat_seq TauRat.one_two_three_nine)).im⟩).im.approx n).toRat
      = 0 := by
  have h := TauReal.machin_45_difference_under_F6 TauRat.one_fifth TauRat.one_two_three_nine n
              h_a_F6 h_b_F6
  rw [h]
  rw [TauRat.one_fifth_toRat, TauRat.one_two_three_nine_toRat]
  ring

-- ============================================================
-- PART 7: F.6 SUBSTITUTION REMAINDER FORM
-- ============================================================

/-! ## F.6 substitution remainder form

  We define the depth-`n` remainder for F.6 substitution:
      `ΔI_a n := cisI a n - a.toRat · cisR a n`
      `ΔI_b n := cisI b n - b.toRat · cisR b n`

  F.6 says ΔI_a, ΔI_b → 0 in Cauchy sense (`TauReal.equiv` to zero
  via `cisTauReal_tangent_target_A_path_beta`).

  The difference `D_n := .re - .im` at depth n can be written as
  a polynomial in `R := cisR a n, B_R := cisR b n, ΔI_a n, ΔI_b n`:

      D_n = R⁴ · B_R · K(a, b) + remainder(R, B_R, ΔI_a, ΔI_b)

  where K(a, b) = 0 at Machin constants and the remainder is a
  polynomial with positive total degree in (ΔI_a, ΔI_b).

  This is the structural decomposition that ultimately lifts the
  pointwise-conditional identity to the full TauReal-equiv 45°-line
  identity. -/

/-- **Polynomial form when F.6 holds pointwise**: under the F.6 pointwise
    substitutions, the difference becomes pure rational arithmetic. -/
theorem TauReal.machin_45_polynomial_at_F6 (a b : TauRat) (n : Nat)
    (h_a_F6 : cisI a n = a.toRat * cisR a n)
    (h_b_F6 : cisI b n = b.toRat * cisR b n) :
    (((((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).mul
          (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a))).mul
        ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).mul
          (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)))).mul
        ⟨(TauComplex.cisTauReal (TauReal.arctan_of_rat_seq b)).re,
         TauReal.negate (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq b)).im⟩).re.approx n).toRat
      - (((((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).mul
              (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a))).mul
            ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).mul
              (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)))).mul
            ⟨(TauComplex.cisTauReal (TauReal.arctan_of_rat_seq b)).re,
             TauReal.negate (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq b)).im⟩).im.approx n).toRat
      = cisR a n^4 * cisR b n *
          ((1 + b.toRat) * (1 - 6*a.toRat^2 + a.toRat^4) -
           (1 - b.toRat) * (4*a.toRat - 4*a.toRat^3)) :=
  TauReal.machin_45_difference_under_F6 a b n h_a_F6 h_b_F6

-- ============================================================
-- PART 8: TauReal-EQUIV LIFT — THE FULL 45°-LINE IDENTITY
-- ============================================================

/-! ## Scope 2A-lift — the Cauchy-modulus lift of the 45°-line identity

  We now lift the depth-n pointwise vanishing (under F.6 hypothesis)
  to a full TauReal-equiv 45°-line identity.

  Strategy:
  1. Express D_n := .re_n - .im_n as a polynomial in R, I, B_R, B_I.
  2. Substitute I = a·R + ε_a and B_I = b·B_R + ε_b where
     ε_a = (tangent_defect a).approx n .toRat,
     ε_b = (tangent_defect b).approx n .toRat.
  3. Algebraically expand: D_n = [R⁴·B_R·K(a,b)] + ε_a·P_1 + ε_b·P_2
     where P_1, P_2 are bounded polynomials in R, I, B_R, B_I, a, b.
  4. At Machin constants K = 0, so D_n = ε_a·P_1 + ε_b·P_2.
  5. By cis_arctan_re/im_approx_abs_le_8: |R|, |I|, |B_R|, |B_I| ≤ 8.
     Hence |P_1|, |P_2| ≤ M_bound for some computable M_bound.
  6. F.6 gives both ε_a, ε_b → 0 in Cauchy sense. Combined with the
     polynomial bound, D_n → 0.
-/

/-! ### What's not closed in this commit (deferred to Phase E next session)

    The lift to TauReal-equiv `.re ≈ .im` requires constructing a Cauchy
    modulus from:
    1. The polynomial decomposition `D_n = R⁴·B_R·K(a,b) + ε_a·P_1 + ε_b·P_2`
       at Machin constants (K = 0).
    2. Uniform bounds on |P_1|, |P_2| via `|R|, |I|, |B_R|, |B_I| ≤ 8`.
    3. F.6's `tangent_defect_equiv_zero` providing ε_a, ε_b → 0 in
       Cauchy sense.
    4. Combined Cauchy modulus via two-arg modulus composition.
    5. Reverse `equiv_of_sub_equiv_zero` to conclude `.re ≈ .im`.

    Each step is mechanical; total ~500-1000 LOC of bound-tracking.
-/

-- ============================================================
-- PART 9: NAMED TARGET PROPOSITION FOR THE TauReal-EQUIV LIFT
-- ============================================================

/-- **The 45°-line identity as a named target proposition**
    (Phase E Scope 2A-lift target).

    Asserts that the parity-substituted Machin product at constants
    `a = 1/5, b = 1/239` lies on the 45° line in the τ-native complex
    plane, i.e., its `.re` and `.im` are TauReal-equiv:

        `(cisTauReal(arctan(1/5))⁴ · ⟨cisB.re, negate cisB.im⟩).re`
          `≈ (cisTauReal(arctan(1/5))⁴ · ⟨cisB.re, negate cisB.im⟩).im`

    where `cisB := cisTauReal(arctan(1/239))`.

    This is the τ-native incarnation of Machin's classical identity
    `4·arctan(1/5) − arctan(1/239) = π/4` at the cisTauReal-product
    level (modulo the magnitude factor cos(arctan(1/5))⁴ · cos(arctan(1/239))).

    The discharge requires the Cauchy-modulus lift documented in Part 8,
    consuming the pointwise infrastructure (`machin_45_re/im_approx`,
    `machin_45_difference_under_F6`,
    `machin_45_vanishes_at_machin_constants_under_F6`) shipped in
    this module plus F.6's `tangent_defect_equiv_zero` and
    `cis_arctan_re/im_approx_abs_le_8` bounds. -/
def MachinFortyFiveDegreeIdentity : Prop :=
  TauReal.equiv
    ((((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq TauRat.one_fifth)).mul
        (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq TauRat.one_fifth))).mul
      ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq TauRat.one_fifth)).mul
        (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq TauRat.one_fifth)))).mul
      ⟨(TauComplex.cisTauReal (TauReal.arctan_of_rat_seq TauRat.one_two_three_nine)).re,
       TauReal.negate
        (TauComplex.cisTauReal
          (TauReal.arctan_of_rat_seq TauRat.one_two_three_nine)).im⟩).re
    ((((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq TauRat.one_fifth)).mul
        (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq TauRat.one_fifth))).mul
      ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq TauRat.one_fifth)).mul
        (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq TauRat.one_fifth)))).mul
      ⟨(TauComplex.cisTauReal (TauReal.arctan_of_rat_seq TauRat.one_two_three_nine)).re,
       TauReal.negate
        (TauComplex.cisTauReal
          (TauReal.arctan_of_rat_seq TauRat.one_two_three_nine)).im⟩).im

-- ============================================================
-- PART 10: SCOPE 2A-LIFT — BOUND LEMMAS FOR cisA, cisA², cisA⁴
-- ============================================================

/-! ## Pointwise bounds on the intermediate complex products

  The bilateral congruence chain `cA · cA · cA · cA · W ≈ cA' · cA' · cA' · cA' · W'`
  is built via `TauComplex.equiv_mul_congr`, which requires pointwise
  bounds on both factors. We establish:

  * `|cA.re|, |cA.im| ≤ 8` (uniform `cis_arctan_re/im_approx_abs_le_8`)
  * `|(cA·cA).re|, |(cA·cA).im| ≤ 128` (from componentwise products)
  * `|((cA·cA)·(cA·cA)).re|, |.im| ≤ 32768` (compounded)

  These same bounds hold for the F.6-substituted complex `cA' := ⟨cA.re, fA·cA.re⟩`
  since `|fA·cA.re| ≤ 8` (using `|a.toRat| ≤ 1` under path-β).
-/

/-- **Pointwise abs bound on cisA².re** under path-β.

    `|R² - I²| ≤ |R|² + |I|² ≤ 64 + 64 = 128`. -/
private theorem cisA_sq_re_approx_abs_le_128
    (a : TauRat) (ha2 : 2 * |a.toRat| ≤ 1) (n : Nat) :
    (((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).mul
        (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a))).re.approx n).abs.toRat
      ≤ 128 := by
  rw [TauRat.toRat_abs]
  show |(((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).mul
            (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a))).re.approx n).toRat| ≤ 128
  rw [cisA_sq_re_approx a n]
  -- Goal: |R² - I²| ≤ 128 where R := cisR a n, I := cisI a n
  have h_R := TauReal.cis_arctan_re_approx_abs_le_8 a ha2 n
  have h_I := TauReal.cis_arctan_im_approx_abs_le_8 a ha2 n
  rw [TauRat.toRat_abs] at h_R h_I
  show |cisR a n * cisR a n - cisI a n * cisI a n| ≤ 128
  unfold cisR cisI at *
  set R := ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).re.approx n).toRat
  set I := ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).im.approx n).toRat
  have h_abs : |R * R - I * I| ≤ |R * R| + |I * I| := by
    have h := abs_add_le (R * R) (-(I * I))
    rw [abs_neg] at h
    have h_eq : R * R + -(I * I) = R * R - I * I := by ring
    rw [h_eq] at h
    exact h
  have hRR : |R * R| ≤ (64 : Rat) := by
    rw [abs_mul]
    have h1 : |R| * |R| ≤ 8 * 8 := mul_le_mul h_R h_R (abs_nonneg _) (by norm_num)
    linarith
  have hII : |I * I| ≤ (64 : Rat) := by
    rw [abs_mul]
    have h1 : |I| * |I| ≤ 8 * 8 := mul_le_mul h_I h_I (abs_nonneg _) (by norm_num)
    linarith
  linarith

/-- **Pointwise abs bound on cisA².im** under path-β.

    `|2RI| ≤ 2·|R|·|I| ≤ 2·8·8 = 128`. -/
private theorem cisA_sq_im_approx_abs_le_128
    (a : TauRat) (ha2 : 2 * |a.toRat| ≤ 1) (n : Nat) :
    (((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).mul
        (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a))).im.approx n).abs.toRat
      ≤ 128 := by
  rw [TauRat.toRat_abs]
  show |(((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).mul
            (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a))).im.approx n).toRat| ≤ 128
  rw [cisA_sq_im_approx a n]
  have h_R := TauReal.cis_arctan_re_approx_abs_le_8 a ha2 n
  have h_I := TauReal.cis_arctan_im_approx_abs_le_8 a ha2 n
  rw [TauRat.toRat_abs] at h_R h_I
  show |cisR a n * cisI a n + cisI a n * cisR a n| ≤ 128
  unfold cisR cisI at *
  set R := ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).re.approx n).toRat
  set I := ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).im.approx n).toRat
  have h_eq : R * I + I * R = 2 * (R * I) := by ring
  rw [h_eq]
  rw [show |2 * (R * I)| = 2 * |R * I| from by rw [abs_mul]; simp]
  rw [abs_mul]
  have h_RI : |R| * |I| ≤ (64 : Rat) := by
    have h1 : |R| * |I| ≤ 8 * 8 := mul_le_mul h_R h_I (abs_nonneg _) (by norm_num)
    linarith
  linarith

/-- **Pointwise abs bound on (cisA·cisA·cisA·cisA).re** under path-β.

    `|R⁴_re part| ≤ |cA²_re|² + |cA²_im|² ≤ 128² + 128² = 32768`. -/
private theorem cisA_quad_re_approx_abs_le_32768
    (a : TauRat) (ha2 : 2 * |a.toRat| ≤ 1) (n : Nat) :
    ((((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).mul
        (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a))).mul
      ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).mul
        (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)))).re.approx n).abs.toRat
      ≤ 32768 := by
  rw [TauRat.toRat_abs]
  rw [cisA_quad_re_approx a n]
  have h_R := TauReal.cis_arctan_re_approx_abs_le_8 a ha2 n
  have h_I := TauReal.cis_arctan_im_approx_abs_le_8 a ha2 n
  rw [TauRat.toRat_abs] at h_R h_I
  unfold cisR cisI at *
  set R := ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).re.approx n).toRat
  set I := ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).im.approx n).toRat
  set U := R * R - I * I with hU_def
  set V := R * I + I * R with hV_def
  -- Goal: |U·U - V·V| ≤ 32768
  -- Bounds: |U| ≤ 128, |V| ≤ 128.
  have hU : |U| ≤ (128 : Rat) := by
    rw [hU_def]
    have h_abs : |R * R - I * I| ≤ |R * R| + |I * I| := by
      have h := abs_add_le (R * R) (-(I * I))
      rw [abs_neg] at h
      have h_eq : R * R + -(I * I) = R * R - I * I := by ring
      rw [h_eq] at h
      exact h
    have hRR : |R * R| ≤ (64 : Rat) := by
      rw [abs_mul]
      have h1 : |R| * |R| ≤ 8 * 8 := mul_le_mul h_R h_R (abs_nonneg _) (by norm_num)
      linarith
    have hII : |I * I| ≤ (64 : Rat) := by
      rw [abs_mul]
      have h1 : |I| * |I| ≤ 8 * 8 := mul_le_mul h_I h_I (abs_nonneg _) (by norm_num)
      linarith
    linarith
  have hV : |V| ≤ (128 : Rat) := by
    rw [hV_def]
    have h_eq : R * I + I * R = 2 * (R * I) := by ring
    rw [h_eq]
    rw [show |2 * (R * I)| = 2 * |R * I| from by rw [abs_mul]; simp]
    rw [abs_mul]
    have h_RI : |R| * |I| ≤ (64 : Rat) := by
      have h1 : |R| * |I| ≤ 8 * 8 := mul_le_mul h_R h_I (abs_nonneg _) (by norm_num)
      linarith
    linarith
  -- Goal: |U·U - V·V| ≤ 32768
  have h_abs : |U * U - V * V| ≤ |U * U| + |V * V| := by
    have h := abs_add_le (U * U) (-(V * V))
    rw [abs_neg] at h
    have h_eq : U * U + -(V * V) = U * U - V * V := by ring
    rw [h_eq] at h
    exact h
  have hUU : |U * U| ≤ (128 : Rat) * 128 := by
    rw [abs_mul]
    exact mul_le_mul hU hU (abs_nonneg _) (by norm_num)
  have hVV : |V * V| ≤ (128 : Rat) * 128 := by
    rw [abs_mul]
    exact mul_le_mul hV hV (abs_nonneg _) (by norm_num)
  have h128 : (128 : Rat) * 128 = 16384 := by norm_num
  rw [h128] at hUU hVV
  linarith

/-- **Pointwise abs bound on (cisA·cisA·cisA·cisA).im** under path-β.

    `|R⁴_im part| ≤ 2·|cA²_re|·|cA²_im| ≤ 2·128·128 = 32768`. -/
private theorem cisA_quad_im_approx_abs_le_32768
    (a : TauRat) (ha2 : 2 * |a.toRat| ≤ 1) (n : Nat) :
    ((((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).mul
        (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a))).mul
      ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).mul
        (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)))).im.approx n).abs.toRat
      ≤ 32768 := by
  rw [TauRat.toRat_abs]
  rw [cisA_quad_im_approx a n]
  have h_R := TauReal.cis_arctan_re_approx_abs_le_8 a ha2 n
  have h_I := TauReal.cis_arctan_im_approx_abs_le_8 a ha2 n
  rw [TauRat.toRat_abs] at h_R h_I
  unfold cisR cisI at *
  set R := ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).re.approx n).toRat
  set I := ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).im.approx n).toRat
  set U := R * R - I * I with hU_def
  set V := R * I + I * R with hV_def
  -- Goal: |U·V + V·U| ≤ 32768
  have h_eq : U * V + V * U = 2 * (U * V) := by ring
  rw [h_eq]
  rw [show |2 * (U * V)| = 2 * |U * V| from by rw [abs_mul]; simp]
  rw [abs_mul]
  have hU : |U| ≤ (128 : Rat) := by
    rw [hU_def]
    have h_abs : |R * R - I * I| ≤ |R * R| + |I * I| := by
      have h := abs_add_le (R * R) (-(I * I))
      rw [abs_neg] at h
      have h_eq : R * R + -(I * I) = R * R - I * I := by ring
      rw [h_eq] at h
      exact h
    have hRR : |R * R| ≤ (64 : Rat) := by
      rw [abs_mul]
      have h1 : |R| * |R| ≤ 8 * 8 := mul_le_mul h_R h_R (abs_nonneg _) (by norm_num)
      linarith
    have hII : |I * I| ≤ (64 : Rat) := by
      rw [abs_mul]
      have h1 : |I| * |I| ≤ 8 * 8 := mul_le_mul h_I h_I (abs_nonneg _) (by norm_num)
      linarith
    linarith
  have hV : |V| ≤ (128 : Rat) := by
    rw [hV_def]
    have h_eq : R * I + I * R = 2 * (R * I) := by ring
    rw [h_eq]
    rw [show |2 * (R * I)| = 2 * |R * I| from by rw [abs_mul]; simp]
    rw [abs_mul]
    have h_RI : |R| * |I| ≤ (64 : Rat) := by
      have h1 : |R| * |I| ≤ 8 * 8 := mul_le_mul h_R h_I (abs_nonneg _) (by norm_num)
      linarith
    linarith
  have h_UV : |U| * |V| ≤ (128 : Rat) * 128 :=
    mul_le_mul hU hV (abs_nonneg _) (by norm_num)
  have h128 : (128 : Rat) * 128 = 16384 := by norm_num
  rw [h128] at h_UV
  linarith

-- ============================================================
-- PART 11: SCOPE 2A-LIFT — SUBSTITUTED COMPLEX (cA') AND ITS BOUNDS
-- ============================================================

/-! ## The F.6-substituted complex `cA'`

  Define `cA' := ⟨cA.re, fA · cA.re⟩` where `fA := fromTauRat a`.
  Under F.6, `cA.equiv cA' := ⟨refl, F.6 for a⟩`.

  We establish identical bounds for `cA'²` and `cA'⁴` since `|fA · cA.re| ≤ 8`
  (uses `fromTauRat_mul_bounded_by_eight`).
-/

/-- Substituted cisA: `⟨cA.re, fA · cA.re⟩`. -/
private noncomputable def cA_subst (a : TauRat) : TauComplex :=
  ⟨(TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).re,
   (TauReal.fromTauRat a).mul (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).re⟩

/-- Bound on (cA_subst a).re.approx n .toRat by 8. -/
private theorem cA_subst_re_approx_abs_le_8
    (a : TauRat) (ha2 : 2 * |a.toRat| ≤ 1) (n : Nat) :
    ((cA_subst a).re.approx n).abs.toRat ≤ 8 := by
  show ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).re.approx n).abs.toRat ≤ 8
  exact TauComplex.cisTauReal_re_approx_abs_le_8 _ n (by
    have h_bound := TauReal.arctan_of_rat_seq_bounded a ha2 n
    rw [TauRat.toRat_abs] at h_bound
    exact h_bound)

/-- Bound on (cA_subst a).im.approx n .toRat by 8. Uses `|a.toRat| ≤ 1` (from path-β). -/
private theorem cA_subst_im_approx_abs_le_8
    (a : TauRat) (ha : 4 * |a.toRat| ≤ 1) (n : Nat) :
    ((cA_subst a).im.approx n).abs.toRat ≤ 8 := by
  have ha2 : 2 * |a.toRat| ≤ 1 := by
    have := _root_.abs_nonneg a.toRat; linarith
  have ha1 : |a.toRat| ≤ 1 := by
    have := _root_.abs_nonneg a.toRat; linarith
  -- (cA_subst a).im = fromTauRat a · cisA.re
  show (((TauReal.fromTauRat a).mul
          (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).re).approx n).abs.toRat ≤ 8
  show ((TauRat.mul ((TauReal.fromTauRat a).approx n)
          ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).re.approx n)).abs).toRat ≤ 8
  rw [TauRat.toRat_abs, toRat_mul]
  show |a.toRat * ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).re.approx n).toRat| ≤ 8
  rw [abs_mul]
  have h_R := TauComplex.cisTauReal_re_approx_abs_le_8 (TauReal.arctan_of_rat_seq a) n (by
    have h_bound := TauReal.arctan_of_rat_seq_bounded a ha2 n
    rw [TauRat.toRat_abs] at h_bound
    exact h_bound)
  rw [TauRat.toRat_abs] at h_R
  calc |a.toRat| * |((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).re.approx n).toRat|
      ≤ 1 * 8 := by
        apply mul_le_mul ha1 h_R (abs_nonneg _) (by norm_num)
    _ = 8 := by ring

/-- The TauComplex equiv `cA ≈ cA_subst a` via F.6. -/
private theorem cisA_equiv_cA_subst
    (a : TauRat) (ha : 4 * |a.toRat| ≤ 1) :
    TauComplex.equiv
      (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a))
      (cA_subst a) := by
  refine ⟨TauReal.equiv_refl _, ?_⟩
  exact TauReal.cisTauReal_tangent_target_A_path_beta a ha

-- ============================================================
-- PART 12: SCOPE 2A-LIFT — cA² ≈ cA_subst² AND cA⁴ ≈ cA_subst⁴
-- ============================================================

/-- The TauComplex equiv `cA · cA ≈ cA_subst · cA_subst`. -/
private theorem cisA_sq_equiv_cA_subst_sq
    (a : TauRat) (ha : 4 * |a.toRat| ≤ 1) :
    TauComplex.equiv
      ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).mul
        (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)))
      ((cA_subst a).mul (cA_subst a)) := by
  have ha2 : 2 * |a.toRat| ≤ 1 := by
    have := _root_.abs_nonneg a.toRat; linarith
  have h_eq := cisA_equiv_cA_subst a ha
  -- Apply TauComplex.equiv_mul_congr with Mre = Mim = 8.
  -- z = cA, z' = cA_subst, w = cA, w' = cA_subst.
  apply TauComplex.equiv_mul_congr (Mre := 8) (Mim := 8) (by norm_num) (by norm_num)
  · -- bound on z'.re = (cA_subst a).re ≤ 8
    intro n; exact cA_subst_re_approx_abs_le_8 a ha2 n
  · -- bound on z'.im = (cA_subst a).im ≤ 8
    intro n; exact cA_subst_im_approx_abs_le_8 a ha n
  · -- bound on w.re = cA.re ≤ 8
    intro n
    show ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).re.approx n).abs.toRat ≤ 8
    exact TauComplex.cisTauReal_re_approx_abs_le_8 _ n (by
      have h_bound := TauReal.arctan_of_rat_seq_bounded a ha2 n
      rw [TauRat.toRat_abs] at h_bound
      exact h_bound)
  · -- bound on w.im = cA.im ≤ 8
    intro n
    show ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).im.approx n).abs.toRat ≤ 8
    exact TauComplex.cisTauReal_im_approx_abs_le_8 _ n (by
      have h_bound := TauReal.arctan_of_rat_seq_bounded a ha2 n
      rw [TauRat.toRat_abs] at h_bound
      exact h_bound)
  · exact h_eq
  · exact h_eq

/-- Bound on (cA_subst a · cA_subst a).re.approx n .toRat by 128. -/
private theorem cA_subst_sq_re_approx_abs_le_128
    (a : TauRat) (ha : 4 * |a.toRat| ≤ 1) (n : Nat) :
    (((cA_subst a).mul (cA_subst a)).re.approx n).abs.toRat ≤ 128 := by
  -- (cA_subst a · cA_subst a).re = (cA_subst a).re · (cA_subst a).re - (cA_subst a).im · (cA_subst a).im
  rw [TauRat.toRat_abs]
  show |(((cA_subst a).mul (cA_subst a)).re.approx n).toRat| ≤ 128
  show |(TauRat.add
            (TauRat.mul ((cA_subst a).re.approx n) ((cA_subst a).re.approx n))
            (TauRat.negate (TauRat.mul ((cA_subst a).im.approx n) ((cA_subst a).im.approx n)))).toRat|
        ≤ 128
  rw [toRat_add, toRat_negate, toRat_mul, toRat_mul]
  have ha2 : 2 * |a.toRat| ≤ 1 := by
    have := _root_.abs_nonneg a.toRat; linarith
  have h_R := cA_subst_re_approx_abs_le_8 a ha2 n
  have h_I := cA_subst_im_approx_abs_le_8 a ha n
  rw [TauRat.toRat_abs] at h_R h_I
  set R := ((cA_subst a).re.approx n).toRat
  set I := ((cA_subst a).im.approx n).toRat
  show |R * R + -(I * I)| ≤ 128
  have h_abs : |R * R + -(I * I)| ≤ |R * R| + |I * I| := by
    have h := abs_add_le (R * R) (-(I * I))
    rw [abs_neg] at h
    exact h
  have hRR : |R * R| ≤ (64 : Rat) := by
    rw [abs_mul]
    have h1 : |R| * |R| ≤ 8 * 8 := mul_le_mul h_R h_R (abs_nonneg _) (by norm_num)
    linarith
  have hII : |I * I| ≤ (64 : Rat) := by
    rw [abs_mul]
    have h1 : |I| * |I| ≤ 8 * 8 := mul_le_mul h_I h_I (abs_nonneg _) (by norm_num)
    linarith
  linarith

/-- Bound on (cA_subst a · cA_subst a).im.approx n .toRat by 128. -/
private theorem cA_subst_sq_im_approx_abs_le_128
    (a : TauRat) (ha : 4 * |a.toRat| ≤ 1) (n : Nat) :
    (((cA_subst a).mul (cA_subst a)).im.approx n).abs.toRat ≤ 128 := by
  rw [TauRat.toRat_abs]
  show |(TauRat.add
            (TauRat.mul ((cA_subst a).re.approx n) ((cA_subst a).im.approx n))
            (TauRat.mul ((cA_subst a).im.approx n) ((cA_subst a).re.approx n))).toRat|
        ≤ 128
  rw [toRat_add, toRat_mul, toRat_mul]
  have ha2 : 2 * |a.toRat| ≤ 1 := by
    have := _root_.abs_nonneg a.toRat; linarith
  have h_R := cA_subst_re_approx_abs_le_8 a ha2 n
  have h_I := cA_subst_im_approx_abs_le_8 a ha n
  rw [TauRat.toRat_abs] at h_R h_I
  set R := ((cA_subst a).re.approx n).toRat
  set I := ((cA_subst a).im.approx n).toRat
  show |R * I + I * R| ≤ 128
  have h_eq : R * I + I * R = 2 * (R * I) := by ring
  rw [h_eq]
  rw [show |2 * (R * I)| = 2 * |R * I| from by rw [abs_mul]; simp]
  rw [abs_mul]
  have h_RI : |R| * |I| ≤ (64 : Rat) := by
    have h1 : |R| * |I| ≤ 8 * 8 := mul_le_mul h_R h_I (abs_nonneg _) (by norm_num)
    linarith
  linarith

/-- The TauComplex equiv `(cA·cA)·(cA·cA) ≈ (cA_subst·cA_subst)·(cA_subst·cA_subst)`. -/
private theorem cisA_quad_equiv_cA_subst_quad
    (a : TauRat) (ha : 4 * |a.toRat| ≤ 1) :
    TauComplex.equiv
      (((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).mul
        (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a))).mul
       ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).mul
        (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a))))
      (((cA_subst a).mul (cA_subst a)).mul ((cA_subst a).mul (cA_subst a))) := by
  have ha2 : 2 * |a.toRat| ≤ 1 := by
    have := _root_.abs_nonneg a.toRat; linarith
  have h_sq_eq := cisA_sq_equiv_cA_subst_sq a ha
  -- Apply TauComplex.equiv_mul_congr with Mre = Mim = 128.
  apply TauComplex.equiv_mul_congr (Mre := 128) (Mim := 128) (by norm_num) (by norm_num)
  · -- bound on z'.re = (cA_subst²).re ≤ 128
    intro n; exact cA_subst_sq_re_approx_abs_le_128 a ha n
  · -- bound on z'.im = (cA_subst²).im ≤ 128
    intro n; exact cA_subst_sq_im_approx_abs_le_128 a ha n
  · -- bound on w.re = (cA²).re ≤ 128
    intro n; exact cisA_sq_re_approx_abs_le_128 a ha2 n
  · -- bound on w.im = (cA²).im ≤ 128
    intro n; exact cisA_sq_im_approx_abs_le_128 a ha2 n
  · exact h_sq_eq
  · exact h_sq_eq

/-- Bound on ((cA_subst a · cA_subst a) · (cA_subst a · cA_subst a)).re.approx n .toRat by 32768. -/
private theorem cA_subst_quad_re_approx_abs_le_32768
    (a : TauRat) (ha : 4 * |a.toRat| ≤ 1) (n : Nat) :
    ((((cA_subst a).mul (cA_subst a)).mul
        ((cA_subst a).mul (cA_subst a))).re.approx n).abs.toRat ≤ 32768 := by
  rw [TauRat.toRat_abs]
  show |(TauRat.add
            (TauRat.mul (((cA_subst a).mul (cA_subst a)).re.approx n)
                       (((cA_subst a).mul (cA_subst a)).re.approx n))
            (TauRat.negate
              (TauRat.mul (((cA_subst a).mul (cA_subst a)).im.approx n)
                         (((cA_subst a).mul (cA_subst a)).im.approx n)))).toRat|
        ≤ 32768
  rw [toRat_add, toRat_negate, toRat_mul, toRat_mul]
  have h_U := cA_subst_sq_re_approx_abs_le_128 a ha n
  have h_V := cA_subst_sq_im_approx_abs_le_128 a ha n
  rw [TauRat.toRat_abs] at h_U h_V
  set U := (((cA_subst a).mul (cA_subst a)).re.approx n).toRat
  set V := (((cA_subst a).mul (cA_subst a)).im.approx n).toRat
  show |U * U + -(V * V)| ≤ 32768
  have h_abs : |U * U + -(V * V)| ≤ |U * U| + |V * V| := by
    have h := abs_add_le (U * U) (-(V * V))
    rw [abs_neg] at h
    exact h
  have hUU : |U * U| ≤ (128 : Rat) * 128 := by
    rw [abs_mul]
    exact mul_le_mul h_U h_U (abs_nonneg _) (by norm_num)
  have hVV : |V * V| ≤ (128 : Rat) * 128 := by
    rw [abs_mul]
    exact mul_le_mul h_V h_V (abs_nonneg _) (by norm_num)
  have h_total : |U * U| + |V * V| ≤ (32768 : Rat) := by
    have h128 : (128 : Rat) * 128 = 16384 := by norm_num
    rw [h128] at hUU hVV
    linarith
  linarith

/-- Bound on ((cA_subst a · cA_subst a) · (cA_subst a · cA_subst a)).im.approx n .toRat by 32768. -/
private theorem cA_subst_quad_im_approx_abs_le_32768
    (a : TauRat) (ha : 4 * |a.toRat| ≤ 1) (n : Nat) :
    ((((cA_subst a).mul (cA_subst a)).mul
        ((cA_subst a).mul (cA_subst a))).im.approx n).abs.toRat ≤ 32768 := by
  rw [TauRat.toRat_abs]
  show |(TauRat.add
            (TauRat.mul (((cA_subst a).mul (cA_subst a)).re.approx n)
                       (((cA_subst a).mul (cA_subst a)).im.approx n))
            (TauRat.mul (((cA_subst a).mul (cA_subst a)).im.approx n)
                       (((cA_subst a).mul (cA_subst a)).re.approx n))).toRat|
        ≤ 32768
  rw [toRat_add, toRat_mul, toRat_mul]
  have h_U := cA_subst_sq_re_approx_abs_le_128 a ha n
  have h_V := cA_subst_sq_im_approx_abs_le_128 a ha n
  rw [TauRat.toRat_abs] at h_U h_V
  set U := (((cA_subst a).mul (cA_subst a)).re.approx n).toRat
  set V := (((cA_subst a).mul (cA_subst a)).im.approx n).toRat
  show |U * V + V * U| ≤ 32768
  have h_eq : U * V + V * U = 2 * (U * V) := by ring
  rw [h_eq]
  rw [show |2 * (U * V)| = 2 * |U * V| from by rw [abs_mul]; simp]
  rw [abs_mul]
  have h_UV : |U| * |V| ≤ (128 : Rat) * 128 :=
    mul_le_mul h_U h_V (abs_nonneg _) (by norm_num)
  have h128 : (128 : Rat) * 128 = 16384 := by norm_num
  rw [h128] at h_UV
  linarith

-- ============================================================
-- PART 13: SCOPE 2A-LIFT — THE W ≈ W' SUBSTITUTION
-- ============================================================

/-! ## The substituted W complex.

  `W := ⟨cB.re, negate cB.im⟩` and `W' := ⟨cB.re, negate (fB · cB.re)⟩`.
  `W ≈ W'` via componentwise: `refl` on .re, `equiv_negate_congr (F.6 for b)` on .im. -/

/-- The F.6-substituted W complex: `⟨cB.re, negate (fB · cB.re)⟩`. -/
private noncomputable def W_subst (b : TauRat) : TauComplex :=
  ⟨(TauComplex.cisTauReal (TauReal.arctan_of_rat_seq b)).re,
   TauReal.negate ((TauReal.fromTauRat b).mul
     (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq b)).re)⟩

/-- The original W complex: `⟨cB.re, negate cB.im⟩`. -/
private noncomputable def W_orig (b : TauRat) : TauComplex :=
  ⟨(TauComplex.cisTauReal (TauReal.arctan_of_rat_seq b)).re,
   TauReal.negate (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq b)).im⟩

/-- Bound on (W_orig b).re.approx n .toRat by 8. -/
private theorem W_orig_re_approx_abs_le_8
    (b : TauRat) (hb : 4 * |b.toRat| ≤ 1) (n : Nat) :
    ((W_orig b).re.approx n).abs.toRat ≤ 8 := by
  have hb2 : 2 * |b.toRat| ≤ 1 := by
    have := _root_.abs_nonneg b.toRat; linarith
  show ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq b)).re.approx n).abs.toRat ≤ 8
  exact TauComplex.cisTauReal_re_approx_abs_le_8 _ n (by
    have h_bound := TauReal.arctan_of_rat_seq_bounded b hb2 n
    rw [TauRat.toRat_abs] at h_bound
    exact h_bound)

/-- Bound on (W_orig b).im.approx n .toRat by 8. -/
private theorem W_orig_im_approx_abs_le_8
    (b : TauRat) (hb : 4 * |b.toRat| ≤ 1) (n : Nat) :
    ((W_orig b).im.approx n).abs.toRat ≤ 8 := by
  have hb2 : 2 * |b.toRat| ≤ 1 := by
    have := _root_.abs_nonneg b.toRat; linarith
  show ((TauReal.negate (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq b)).im).approx n).abs.toRat ≤ 8
  show ((TauRat.negate ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq b)).im.approx n)).abs).toRat ≤ 8
  rw [TauRat.abs_negate]
  exact TauComplex.cisTauReal_im_approx_abs_le_8 _ n (by
    have h_bound := TauReal.arctan_of_rat_seq_bounded b hb2 n
    rw [TauRat.toRat_abs] at h_bound
    exact h_bound)

/-- Bound on (W_subst b).re.approx n .toRat by 8. -/
private theorem W_subst_re_approx_abs_le_8
    (b : TauRat) (hb : 4 * |b.toRat| ≤ 1) (n : Nat) :
    ((W_subst b).re.approx n).abs.toRat ≤ 8 :=
  W_orig_re_approx_abs_le_8 b hb n

/-- Bound on (W_subst b).im.approx n .toRat by 8. -/
private theorem W_subst_im_approx_abs_le_8
    (b : TauRat) (hb : 4 * |b.toRat| ≤ 1) (n : Nat) :
    ((W_subst b).im.approx n).abs.toRat ≤ 8 := by
  have hb2 : 2 * |b.toRat| ≤ 1 := by
    have := _root_.abs_nonneg b.toRat; linarith
  have hb1 : |b.toRat| ≤ 1 := by
    have := _root_.abs_nonneg b.toRat; linarith
  show ((TauReal.negate ((TauReal.fromTauRat b).mul
            (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq b)).re)).approx n).abs.toRat ≤ 8
  show ((TauRat.negate
            (TauRat.mul ((TauReal.fromTauRat b).approx n)
              ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq b)).re.approx n))).abs).toRat ≤ 8
  rw [TauRat.abs_negate]
  rw [TauRat.toRat_abs, toRat_mul]
  show |b.toRat * ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq b)).re.approx n).toRat| ≤ 8
  rw [abs_mul]
  have h_R := TauComplex.cisTauReal_re_approx_abs_le_8 (TauReal.arctan_of_rat_seq b) n (by
    have h_bound := TauReal.arctan_of_rat_seq_bounded b hb2 n
    rw [TauRat.toRat_abs] at h_bound
    exact h_bound)
  rw [TauRat.toRat_abs] at h_R
  calc |b.toRat| * |((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq b)).re.approx n).toRat|
      ≤ 1 * 8 := by
        apply mul_le_mul hb1 h_R (abs_nonneg _) (by norm_num)
    _ = 8 := by ring

/-- The TauComplex equiv `W_orig ≈ W_subst` via F.6 for b. -/
private theorem W_orig_equiv_W_subst
    (b : TauRat) (hb : 4 * |b.toRat| ≤ 1) :
    TauComplex.equiv (W_orig b) (W_subst b) := by
  refine ⟨TauReal.equiv_refl _, ?_⟩
  -- W_orig.im = negate cB.im, W_subst.im = negate (fB · cB.re)
  -- Want: negate cB.im ≈ negate (fB · cB.re)
  -- By F.6: cB.im ≈ fB · cB.re. By equiv_negate_congr.
  apply TauReal.equiv_negate_congr
  exact TauReal.cisTauReal_tangent_target_A_path_beta b hb

-- ============================================================
-- PART 14: SCOPE 2A-LIFT — THE FULL EQUIV (cA⁴·W) ≈ (cA_subst⁴·W_subst)
-- ============================================================

/-- The TauComplex equiv `cA⁴ · W ≈ cA_subst⁴ · W_subst`. -/
private theorem cisA_quad_W_equiv_cA_subst_quad_W_subst
    (a b : TauRat) (ha : 4 * |a.toRat| ≤ 1) (hb : 4 * |b.toRat| ≤ 1) :
    TauComplex.equiv
      ((((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).mul
          (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a))).mul
        ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).mul
          (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)))).mul
        (W_orig b))
      ((((cA_subst a).mul (cA_subst a)).mul ((cA_subst a).mul (cA_subst a))).mul
        (W_subst b)) := by
  have ha2 : 2 * |a.toRat| ≤ 1 := by
    have := _root_.abs_nonneg a.toRat; linarith
  -- Apply TauComplex.equiv_mul_congr with Mre = Mim = 32768.
  apply TauComplex.equiv_mul_congr (Mre := 32768) (Mim := 32768) (by norm_num) (by norm_num)
  · -- bound on z'.re = (cA_subst⁴).re ≤ 32768
    intro n; exact cA_subst_quad_re_approx_abs_le_32768 a ha n
  · -- bound on z'.im = (cA_subst⁴).im ≤ 32768
    intro n; exact cA_subst_quad_im_approx_abs_le_32768 a ha n
  · -- bound on w.re = W_orig.re ≤ 8 ≤ 32768
    intro n
    have h := W_orig_re_approx_abs_le_8 b hb n
    have h_le : (8 : Rat) ≤ (32768 : Nat) := by norm_num
    linarith
  · -- bound on w.im = W_orig.im ≤ 8 ≤ 32768
    intro n
    have h := W_orig_im_approx_abs_le_8 b hb n
    have h_le : (8 : Rat) ≤ (32768 : Nat) := by norm_num
    linarith
  · exact cisA_quad_equiv_cA_subst_quad a ha
  · exact W_orig_equiv_W_subst b hb

-- ============================================================
-- PART 15: SCOPE 2A-LIFT — THE POINTWISE IDENTITY (cA_subst⁴·W_subst).re ≈ (...).im AT MACHIN
-- ============================================================

/-! ## The pointwise identity at Machin constants

  At `a = 1/5, b = 1/239`, the substituted product
  `(cA_subst a)⁴ · W_subst b` has `.re ≈ .im` pointwise (via toRat),
  because the polynomial form gives `R⁴·B_R·K(α,β) = 0`. -/

/-- **Toolkit toRat lemma**: `((cA_subst a).re.approx n).toRat = cisR a n`. -/
private theorem cA_subst_re_approx_toRat (a : TauRat) (n : Nat) :
    ((cA_subst a).re.approx n).toRat = cisR a n := rfl

/-- **Toolkit toRat lemma**: `((cA_subst a).im.approx n).toRat = a.toRat · cisR a n`. -/
private theorem cA_subst_im_approx_toRat (a : TauRat) (n : Nat) :
    ((cA_subst a).im.approx n).toRat = a.toRat * cisR a n := by
  show (TauRat.mul ((TauReal.fromTauRat a).approx n)
          ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq a)).re.approx n)).toRat = _
  rw [toRat_mul]
  rfl

/-- **Toolkit toRat lemma**: `((W_subst b).re.approx n).toRat = cisR b n`. -/
private theorem W_subst_re_approx_toRat (b : TauRat) (n : Nat) :
    ((W_subst b).re.approx n).toRat = cisR b n := rfl

/-- **Toolkit toRat lemma**: `((W_subst b).im.approx n).toRat = - (b.toRat · cisR b n)`. -/
private theorem W_subst_im_approx_toRat (b : TauRat) (n : Nat) :
    ((W_subst b).im.approx n).toRat = -(b.toRat * cisR b n) := by
  show (TauRat.negate
          (TauRat.mul ((TauReal.fromTauRat b).approx n)
            ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq b)).re.approx n))).toRat = _
  rw [toRat_negate, toRat_mul]
  rfl

/-- **Toolkit toRat lemma**: `((cA_subst a · cA_subst a).re.approx n).toRat
      = cisR a n^2 - (a.toRat · cisR a n)^2`. -/
private theorem cA_subst_sq_re_approx_toRat (a : TauRat) (n : Nat) :
    (((cA_subst a).mul (cA_subst a)).re.approx n).toRat
      = cisR a n ^ 2 - (a.toRat * cisR a n) ^ 2 := by
  show (TauRat.add
          (TauRat.mul ((cA_subst a).re.approx n) ((cA_subst a).re.approx n))
          (TauRat.negate
            (TauRat.mul ((cA_subst a).im.approx n) ((cA_subst a).im.approx n)))).toRat = _
  rw [toRat_add, toRat_negate, toRat_mul, toRat_mul]
  rw [cA_subst_re_approx_toRat, cA_subst_im_approx_toRat]
  ring

/-- **Toolkit toRat lemma**: `((cA_subst a · cA_subst a).im.approx n).toRat
      = 2 · cisR a n · (a.toRat · cisR a n)`. -/
private theorem cA_subst_sq_im_approx_toRat (a : TauRat) (n : Nat) :
    (((cA_subst a).mul (cA_subst a)).im.approx n).toRat
      = 2 * cisR a n * (a.toRat * cisR a n) := by
  show (TauRat.add
          (TauRat.mul ((cA_subst a).re.approx n) ((cA_subst a).im.approx n))
          (TauRat.mul ((cA_subst a).im.approx n) ((cA_subst a).re.approx n))).toRat = _
  rw [toRat_add, toRat_mul, toRat_mul]
  rw [cA_subst_re_approx_toRat, cA_subst_im_approx_toRat]
  ring

/-- **Toolkit toRat lemma**: cisA⁴ at toRat level (the .re component). -/
private theorem cA_subst_quad_re_approx_toRat (a : TauRat) (n : Nat) :
    ((((cA_subst a).mul (cA_subst a)).mul
        ((cA_subst a).mul (cA_subst a))).re.approx n).toRat
      = (cisR a n ^ 2 - (a.toRat * cisR a n) ^ 2) ^ 2
        - (2 * cisR a n * (a.toRat * cisR a n)) ^ 2 := by
  show (TauRat.add
          (TauRat.mul (((cA_subst a).mul (cA_subst a)).re.approx n)
                     (((cA_subst a).mul (cA_subst a)).re.approx n))
          (TauRat.negate
            (TauRat.mul (((cA_subst a).mul (cA_subst a)).im.approx n)
                       (((cA_subst a).mul (cA_subst a)).im.approx n)))).toRat = _
  rw [toRat_add, toRat_negate, toRat_mul, toRat_mul]
  rw [cA_subst_sq_re_approx_toRat, cA_subst_sq_im_approx_toRat]
  ring

/-- **Toolkit toRat lemma**: cisA⁴ at toRat level (the .im component). -/
private theorem cA_subst_quad_im_approx_toRat (a : TauRat) (n : Nat) :
    ((((cA_subst a).mul (cA_subst a)).mul
        ((cA_subst a).mul (cA_subst a))).im.approx n).toRat
      = 2 * (cisR a n ^ 2 - (a.toRat * cisR a n) ^ 2)
            * (2 * cisR a n * (a.toRat * cisR a n)) := by
  show (TauRat.add
          (TauRat.mul (((cA_subst a).mul (cA_subst a)).re.approx n)
                     (((cA_subst a).mul (cA_subst a)).im.approx n))
          (TauRat.mul (((cA_subst a).mul (cA_subst a)).im.approx n)
                     (((cA_subst a).mul (cA_subst a)).re.approx n))).toRat = _
  rw [toRat_add, toRat_mul, toRat_mul]
  rw [cA_subst_sq_re_approx_toRat, cA_subst_sq_im_approx_toRat]
  ring

/-- The polynomial form of `(cA_subst a · cA_subst a · cA_subst a · cA_subst a · W_subst b).re.approx n .toRat` —
    a polynomial in `cisR a n, cisR b n, a.toRat, b.toRat`. -/
private theorem cA_subst_quad_W_subst_re_approx (a b : TauRat) (n : Nat) :
    (((((cA_subst a).mul (cA_subst a)).mul
        ((cA_subst a).mul (cA_subst a))).mul (W_subst b)).re.approx n).toRat
      = ((cisR a n ^ 2 - (a.toRat * cisR a n) ^ 2) ^ 2
          - (2 * cisR a n * (a.toRat * cisR a n)) ^ 2) * cisR b n
        + (2 * (cisR a n ^ 2 - (a.toRat * cisR a n) ^ 2)
              * (2 * cisR a n * (a.toRat * cisR a n))) * (b.toRat * cisR b n) := by
  show (TauRat.add
          (TauRat.mul ((((cA_subst a).mul (cA_subst a)).mul
              ((cA_subst a).mul (cA_subst a))).re.approx n)
            ((W_subst b).re.approx n))
          (TauRat.negate
            (TauRat.mul ((((cA_subst a).mul (cA_subst a)).mul
                ((cA_subst a).mul (cA_subst a))).im.approx n)
              ((W_subst b).im.approx n)))).toRat = _
  rw [toRat_add, toRat_negate, toRat_mul, toRat_mul]
  rw [cA_subst_quad_re_approx_toRat, cA_subst_quad_im_approx_toRat]
  rw [W_subst_re_approx_toRat, W_subst_im_approx_toRat]
  ring

/-- The polynomial form of `(cA_subst a · cA_subst a · cA_subst a · cA_subst a · W_subst b).im.approx n .toRat`. -/
private theorem cA_subst_quad_W_subst_im_approx (a b : TauRat) (n : Nat) :
    (((((cA_subst a).mul (cA_subst a)).mul
        ((cA_subst a).mul (cA_subst a))).mul (W_subst b)).im.approx n).toRat
      = ((cisR a n ^ 2 - (a.toRat * cisR a n) ^ 2) ^ 2
          - (2 * cisR a n * (a.toRat * cisR a n)) ^ 2) * (-(b.toRat * cisR b n))
        + (2 * (cisR a n ^ 2 - (a.toRat * cisR a n) ^ 2)
              * (2 * cisR a n * (a.toRat * cisR a n))) * cisR b n := by
  show (TauRat.add
          (TauRat.mul ((((cA_subst a).mul (cA_subst a)).mul
              ((cA_subst a).mul (cA_subst a))).re.approx n)
            ((W_subst b).im.approx n))
          (TauRat.mul ((((cA_subst a).mul (cA_subst a)).mul
              ((cA_subst a).mul (cA_subst a))).im.approx n)
            ((W_subst b).re.approx n))).toRat = _
  rw [toRat_add, toRat_mul, toRat_mul]
  rw [cA_subst_quad_re_approx_toRat, cA_subst_quad_im_approx_toRat]
  rw [W_subst_re_approx_toRat, W_subst_im_approx_toRat]

/-- The pointwise toRat identity at Machin constants:
    `(cA_subst (1/5)⁴ · W_subst (1/239)).re.approx n .toRat
      = (cA_subst (1/5)⁴ · W_subst (1/239)).im.approx n .toRat`. -/
private theorem cA_subst_quad_W_subst_re_eq_im_at_machin (n : Nat) :
    (((((cA_subst TauRat.one_fifth).mul (cA_subst TauRat.one_fifth)).mul
        ((cA_subst TauRat.one_fifth).mul (cA_subst TauRat.one_fifth))).mul
        (W_subst TauRat.one_two_three_nine)).re.approx n).toRat
      = (((((cA_subst TauRat.one_fifth).mul (cA_subst TauRat.one_fifth)).mul
            ((cA_subst TauRat.one_fifth).mul (cA_subst TauRat.one_fifth))).mul
            (W_subst TauRat.one_two_three_nine)).im.approx n).toRat := by
  rw [cA_subst_quad_W_subst_re_approx, cA_subst_quad_W_subst_im_approx]
  rw [TauRat.one_fifth_toRat, TauRat.one_two_three_nine_toRat]
  -- Both sides reduce to (R⁴·B_R·K(α, β)) form. K(1/5, 1/239) = 0.
  -- LHS coefficient: (R² - α²R²)² - (2αR²)² then multiplied with various... let's just ring it.
  -- The difference of LHS - RHS = R⁴·B_R·K(α,β); ring_nf + norm_num should close.
  ring

/-- The TauReal-equiv form: `(cA_subst (1/5)⁴ · W_subst (1/239)).re ≈ (...).im` via pointwise toRat. -/
private theorem cA_subst_quad_W_subst_re_equiv_im_at_machin :
    TauReal.equiv
      (((((cA_subst TauRat.one_fifth).mul (cA_subst TauRat.one_fifth)).mul
          ((cA_subst TauRat.one_fifth).mul (cA_subst TauRat.one_fifth))).mul
          (W_subst TauRat.one_two_three_nine)).re)
      (((((cA_subst TauRat.one_fifth).mul (cA_subst TauRat.one_fifth)).mul
          ((cA_subst TauRat.one_fifth).mul (cA_subst TauRat.one_fifth))).mul
          (W_subst TauRat.one_two_three_nine)).im) := by
  apply TauReal.equiv_of_pointwise
  intro n
  rw [equiv_iff_toRat_eq]
  exact cA_subst_quad_W_subst_re_eq_im_at_machin n

-- ============================================================
-- PART 16: SCOPE 2A-LIFT — THE FINAL THEOREM
-- ============================================================

/-- **The 45°-line identity discharged as a theorem** (Scope 2A-lift).

    The parity-substituted Machin product at constants `a = 1/5, b = 1/239`
    lies on the 45° line in the τ-native complex plane:

        `(cisTauReal(arctan(1/5))⁴ · ⟨cisB.re, negate cisB.im⟩).re
          ≈ (cisTauReal(arctan(1/5))⁴ · ⟨cisB.re, negate cisB.im⟩).im`

    where `cisB := cisTauReal(arctan(1/239))`.

    Proof strategy:
    1. Build `cA_subst a := ⟨cA.re, fromTauRat a · cA.re⟩`,
       the F.6-substituted cisA. By F.6 (path-β), `cA ≈ cA_subst a`.
    2. Via iterated `TauComplex.equiv_mul_congr`, lift to
       `cA⁴ · W ≈ cA_subst a⁴ · W_subst b`.
    3. Extract `.re` and `.im` components — both equivalences are TauReal-equiv.
    4. Show `cA_subst (1/5)⁴ · W_subst (1/239)` has `.re ≈ .im` pointwise,
       via the polynomial identity `R⁴·B_R·K(α,β) = 0` at Machin.
    5. Combine: `(P·W).re ≈ (P'·W').re = (P'·W').im ≈ (P·W).im`. -/
theorem TauReal.machin_forty_five_degree_identity : MachinFortyFiveDegreeIdentity := by
  -- The TauComplex equiv: cA⁴·W ≈ cA_subst⁴·W_subst
  have h_equiv : TauComplex.equiv
    ((((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq TauRat.one_fifth)).mul
        (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq TauRat.one_fifth))).mul
      ((TauComplex.cisTauReal (TauReal.arctan_of_rat_seq TauRat.one_fifth)).mul
        (TauComplex.cisTauReal (TauReal.arctan_of_rat_seq TauRat.one_fifth)))).mul
      (W_orig TauRat.one_two_three_nine))
    ((((cA_subst TauRat.one_fifth).mul (cA_subst TauRat.one_fifth)).mul
        ((cA_subst TauRat.one_fifth).mul (cA_subst TauRat.one_fifth))).mul
      (W_subst TauRat.one_two_three_nine)) :=
    cisA_quad_W_equiv_cA_subst_quad_W_subst
      TauRat.one_fifth TauRat.one_two_three_nine
      TauRat.one_fifth_in_path_beta TauRat.one_two_three_nine_in_path_beta
  -- Extract .re and .im components
  have h_re_equiv := h_equiv.1
  have h_im_equiv := h_equiv.2
  -- The substituted target: .re ≈ .im at Machin constants
  have h_subst_eq := cA_subst_quad_W_subst_re_equiv_im_at_machin
  -- Combine: P.re ≈ T.re = T.im ≈ P.im
  show TauReal.equiv _ _
  -- The goal is (...orig.re) ≈ (...orig.im).
  -- We have:
  -- h_re_equiv: (orig.re) ≈ (subst.re)
  -- h_subst_eq: (subst.re) ≈ (subst.im)
  -- h_im_equiv: (orig.im) ≈ (subst.im)
  -- So: orig.re ≈ subst.re ≈ subst.im ≈ orig.im.
  -- Use trans h_re_equiv h_subst_eq trans symm h_im_equiv.
  exact TauReal.equiv_trans
    (TauReal.equiv_trans h_re_equiv h_subst_eq)
    (TauReal.equiv_symm h_im_equiv)

end Tau.Boundary
