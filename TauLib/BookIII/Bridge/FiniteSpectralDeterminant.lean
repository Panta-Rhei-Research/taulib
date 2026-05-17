import TauLib.BookIII.Bridge.O3Interface

/-!
# TauLib.BookIII.Bridge.FiniteSpectralDeterminant

G6.0 finite determinant scaffold.

This module is deliberately finite.  It provides a τ-native product-style
bookkeeping layer for diagonal nonzero-mode approximants.  It is not a
Fredholm determinant, not a zeta-regularized determinant, and not O3.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

/-- Finite mode labels for the first G6 determinant scaffold.

The mode index is shifted by one so the scaffold represents the nonzero-mode
policy selected by `finiteFirstO3Context`. -/
structure NonzeroFiniteMode (cutoff : Nat) where
  index : Nat
  withinCutoff : index < cutoff
  deriving Repr

/-- The nonzero-mode number represented by a finite mode label. -/
def NonzeroFiniteMode.modeNumber {cutoff : Nat}
    (m : NonzeroFiniteMode cutoff) : Nat :=
  m.index + 1

/-- Product over the first `cutoff` nonzero diagonal factors. -/
def finiteDiagonalProduct : Nat → (Nat → Nat) → Nat
  | 0, _factor => 1
  | n + 1, factor => finiteDiagonalProduct n factor * factor (n + 1)

/-- Definitional step for the finite diagonal product. -/
theorem finiteDiagonalProduct_succ (n : Nat) (factor : Nat → Nat) :
    finiteDiagonalProduct (n + 1) factor =
      finiteDiagonalProduct n factor * factor (n + 1) :=
  rfl

/-- G6 finite-first approximant.  The determinant value is a product of finite
    diagonal factors only; all infinite and regularized determinant content
    remains outside this structure. -/
structure TauFiniteDetApprox where
  cutoff : Nat
  factor : Nat → Nat
  determinant : Nat := finiteDiagonalProduct cutoff factor
  determinant_eq : determinant = finiteDiagonalProduct cutoff factor := by rfl
  context : O3Context := finiteFirstO3Context

/-- Build the finite determinant approximant from a cutoff and diagonal factor
    family. -/
def mkTauFiniteDetApprox (cutoff : Nat) (factor : Nat → Nat) :
    TauFiniteDetApprox where
  cutoff := cutoff
  factor := factor

/-- The finite determinant field is exactly the finite diagonal product. -/
theorem tauFiniteDetApprox_determinant_eq
    (A : TauFiniteDetApprox) :
    A.determinant = finiteDiagonalProduct A.cutoff A.factor :=
  A.determinant_eq

/-- The constructor supplied by this module uses the finite-first context. -/
theorem mkTauFiniteDetApprox_context (cutoff : Nat) (factor : Nat → Nat) :
    (mkTauFiniteDetApprox cutoff factor).context = finiteFirstO3Context :=
  rfl

/-- The constructor supplied by this module excludes the zero mode. -/
theorem mkTauFiniteDetApprox_zeroModePolicy (cutoff : Nat) (factor : Nat → Nat) :
    (mkTauFiniteDetApprox cutoff factor).context.zeroModePolicy = .excluded :=
  rfl

/-- Constant-factor finite scaffold used by smoke tests and downstream
    examples. -/
def constantTauFiniteDetApprox (cutoff c : Nat) : TauFiniteDetApprox :=
  mkTauFiniteDetApprox cutoff (fun _ => c)

/-- The zero-cutoff determinant is the empty product. -/
theorem finiteDiagonalProduct_zero (factor : Nat → Nat) :
    finiteDiagonalProduct 0 factor = 1 :=
  rfl

end Tau.BookIII.Bridge
