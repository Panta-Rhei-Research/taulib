import TauLib.BookI.Boundary.Measure

/-!
# TauLib.BookI.Boundary.Integration

Constructive integration on the primorial tower.

## Registry Cross-References

- [I.D99] τ-Integral — `tau_integral`, `integral_check`
- [I.T51] Linearity of Integration — `integral_linearity_check`
- [I.P45] Monotone Convergence — `monotone_convergence_check`

## Mathematical Content

**I.D99 (τ-Integral):** The integral of a function f: Z/M_k Z → ℤ at stage k
is the normalized sum: ∫_k f = (1/M_k) Σ_{x=0}^{M_k-1} f(x). This is the
expectation under the counting measure μ_k.

**I.T51 (Linearity):** ∫_k (af + bg) = a ∫_k f + b ∫_k g. Verified as an
equality of rational pairs (numerator/denominator).

**I.P45 (Monotone Convergence):** For a tower-compatible family of functions
f_k: Z/M_k Z → ℤ with f_k ≤ f_{k+1} (appropriately defined), the integrals
∫_k f_k form a non-decreasing sequence.
-/

set_option autoImplicit false

namespace Tau.Boundary

open Tau.Denotation Tau.Polarity

-- ============================================================
-- τ-INTEGRAL [I.D99]
-- ============================================================

/-- [I.D99] Sum a function over Z/M_k Z. -/
def stage_sum (f : Nat → Int) (k : Nat) : Int :=
  go 0 (primorial k) (0 : Int)
where
  go (x bound : Nat) (acc : Int) : Int :=
    if x >= bound then acc
    else go (x + 1) bound (acc + f x)
  termination_by bound - x

/-- [I.D99] The τ-integral as a rational pair:
    ∫_k f = (Σ f(x), M_k). -/
structure TauIntegral where
  numerator : Int
  denominator : Nat
  deriving Repr

/-- [I.D99] Compute the integral of f at stage k. -/
def tau_integral (f : Nat → Int) (k : Nat) : TauIntegral :=
  { numerator := stage_sum f k
  , denominator := primorial k }

/-- [I.D99] Two integrals are equivalent (same rational value):
    a/b = c/d iff a*d = c*b. -/
def integral_equiv (i j : TauIntegral) : Bool :=
  i.numerator * j.denominator == j.numerator * i.denominator

-- ============================================================
-- LINEARITY [I.T51]
-- ============================================================

/-- [I.T51] Check linearity: ∫(af + bg) = a∫f + b∫g at stage k. -/
def integral_linearity_check (a b : Int) (f g : Nat → Int) (k : Nat) : Bool :=
  let intf := tau_integral f k
  let intg := tau_integral g k
  let intfg := tau_integral (fun x => a * f x + b * g x) k
  let pk := primorial k
  -- ∫(af + bg) = a∫f + b∫g as rationals:
  -- intfg.num / pk = a * intf.num / pk + b * intg.num / pk
  -- i.e., intfg.num = a * intf.num + b * intg.num
  intfg.numerator == a * intf.numerator + b * intg.numerator

-- ============================================================
-- MONOTONE CONVERGENCE [I.P45]
-- ============================================================

/-- [I.P45] Check that integrals increase from stage k to stage k+1
    for a given function family. -/
def monotone_convergence_check_step (f : Nat → Nat → Int)
    (k : Nat) : Bool :=
  let ik := tau_integral (f k) k
  let ik1 := tau_integral (f (k + 1)) (k + 1)
  -- Compare ik.num / ik.den ≤ ik1.num / ik1.den
  -- i.e., ik.num * ik1.den ≤ ik1.num * ik.den
  ik.numerator * ik1.denominator ≤ ik1.numerator * ik.denominator

-- ============================================================
-- EXAMPLES
-- ============================================================

/-- The constant function f(x) = 1. -/
def const_one : Nat → Int := fun _ => 1

/-- The identity function f(x) = x. -/
def ident_fn : Nat → Int := fun x => x

/-- The indicator of even numbers. -/
def even_indicator : Nat → Int := fun x => if x % 2 == 0 then 1 else 0

-- ============================================================
-- THEOREMS
-- ============================================================

/-- [I.D99] Integral of constant 1 at stage 3: ∫_3 1 = 30/30 = 1. -/
theorem integral_const_one_3 :
    (tau_integral const_one 3).numerator = 30 := by native_decide

/-- [I.T51] Linearity for (2f + 3g) at stage 2. -/
theorem linearity_2f_3g_stage2 :
    integral_linearity_check 2 3 ident_fn const_one 2 = true := by native_decide

/-- [I.T51] Linearity for (1f + 0g) at stage 2 (identity). -/
theorem linearity_identity_stage2 :
    integral_linearity_check 1 0 ident_fn const_one 2 = true := by native_decide

/-- [I.D99] Integral of even indicator at stage 2: 3/6 = 1/2. -/
theorem integral_even_2 :
    (tau_integral even_indicator 2).numerator = 3 := by native_decide

-- ============================================================
-- SMOKE TESTS
-- ============================================================

#eval stage_sum const_one 2          -- 6
#eval stage_sum const_one 3          -- 30
#eval stage_sum ident_fn 2           -- 0+1+2+3+4+5 = 15
#eval stage_sum even_indicator 2     -- 3 (x=0,2,4)
#eval (tau_integral const_one 3).numerator  -- 30
#eval integral_linearity_check 2 3 ident_fn const_one 2  -- true

end Tau.Boundary
